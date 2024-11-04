use ark_ec::pairing::Pairing;
use ark_ec::{AffineRepr, CurveGroup, VariableBaseMSM};
use ark_ec::Group;
use ark_ff::{Field, One, Zero};
use ark_poly::univariate::DensePolynomial;
use ark_poly::DenseUVPolynomial;
use ark_poly::EvaluationDomain;
use ark_std::rand::Rng;
use ark_std::{end_timer, start_timer, UniformRand};
use derivative::Derivative;

use crate::{koe, single_base_msm};
use crate::utils::BarycentricDomain;

// TODO: integration test
// TODO: bench for logn = 16, 20
// TODO: Fiat-Shamir
// TODO: cofactors/subgroup checks

/// Aggregatable Publicly Verifiable Secret Sharing Scheme (aPVSS) for sharing a secret key `f(0).g1` in G1,
/// corresponding to the public key `f(0).g2` in G2.
///
/// There are 2 types of participants:
/// 1. a fixed list of signers, identified with their BLS public keys in G2, and
/// 2. any number of dealers, whose authentication is the problem of a higher-level protocol.
/// A dealer samples a secret and produces a transcript containing shares of the secret, each encrypted to the corresponding signer,
/// together with a publicly verifiable proof of validity of the ciphertexts.
/// Transcripts with contributions from different dealers can be aggregated into a single verifiable transcript.
/// The scheme is secure (vaguely that means the parameters produced are secure),
/// if the final aggregated transcript is valid, and contains a contribution from a single honest dealer.
///
/// *A fun property* of the scheme is that signers don't have to use (or even decrypt) their shares in any way.
/// Instead, anyone can blindly use the ciphertexts to produce proofs that the threshold number of signers have signed.
///
/// The implementation follows the notes by Alistair Stewart:
/// 1. https://hackmd.io/3968Gr5hSSmef-nptg2GRw
/// 2. https://hackmd.io/xqYBrigYQwyKM_0Sn5Xf4w

/// Parameters of an aPVSS instantiation.
struct
Ceremony<'a, C: Pairing, D: EvaluationDomain<C::ScalarField>> {
    /// The number of signers.
    n: usize,
    /// The threshold, i.e. the minimal number of signers required to reconstruct the shared secret.
    t: usize,
    /// The signers' bls public keys in G2.
    /// **It's critical that proofs of possession are checked for these keys.**
    bls_pks: &'a [C::G2Affine],
    /// An FFT-friendly multiplicative subgroup of the field of size not less than `n`.
    /// The evaluation points are the first `n` elements of the subgroup: `x_j = w^j, j = 0,...,n-1`,
    /// where `w` is the generator of the subgroup.
    domain: D,
    /// Generator of G1.
    g1: C::G1,
    /// Generator of G2.
    g2: C::G2,
}

/// Useful data produced by the protocol:
/// - encrypted shares of the secret key,
/// - the corresponding threshold public key, and
/// - a pair of points with the same discrete logarithm.
///
/// The secret key being shared among the signers is `f(0).g2` for some polynomial `f`.
/// `f(0).g1` is the public key, corresponding to the shared secret key. The share of the signer `j` is `f(w^j).g2`.
/// `(h1, h2)` are points in G1xG2 with the same discrete logarithm, i.e. `h1 = sh.g1` and `h2 = sh.g2` for some `sh`.
/// `bgpk_j = f(w^j).g2 + sh.pk_j, j = 0,...,n-1`.
/// Then `(bgpk_j, h2)` is the ElGamal encryption of the point `f(w^j).g2` with `pk_j` for the ephemeral secret `sh`.
#[derive(Derivative)]
#[derivative(Clone)]
struct SharesAndMore<C: Pairing> {
    /// The public key corresponding to the shared secret key.
    /// `c = f(0).g1`
    c: C::G1Affine,
    /// Shares of the secret, encrypted to the signers.
    /// `bgpk_j = f(w^j).g2 + sh.pk_j, j = 0,...,n-1`
    bgpk: Vec<C::G2Affine>,
    /// `h1 = sh.g1`
    h1: C::G1Affine,
    /// `h2 = sh.g2`
    h2: C::G2Affine,
}

/// Standalone or aggregated transcript with the witness.
// TODO: add weights?
#[derive(Derivative)]
#[derivative(Clone)]
struct Transcript<C: Pairing> {
    shares: SharesAndMore<C>,

    // witness data
    /// Commitment to the secret polynomial `A_j = f(w^j).g1, j = 0,...,n-1`
    a: Vec<C::G1Affine>,
    /// Proofs of knowledge of the exponents `(f_i(0), sh_i)`
    /// such that `C_i=f_i(0).g1` and `h1_i=sh_i.g1` for every dealer `i = 1,...,k`.
    koe_proofs: Vec<KoeProof<C>>,
}

/// Precomputed barycentric weights to facilitate interpolation.
/// Depend only on `(t,n)` so can be reused between the ceremonies.
/// `Ceremony::verifier()` creates the object.
/// TODO: 1. can be computed faster
/// TODO: 2. can keep lis_at_0
/// TODO: 3. lis_at_0 can be computed faster
struct TranscriptVerifier<C: Pairing> {
    domain_size_n: BarycentricDomain<C::ScalarField>,
    domain_size_t: BarycentricDomain<C::ScalarField>,
}

/// Proof that the dealer `i` knows her secrets.
#[derive(Derivative)]
#[derivative(Clone)]
struct KoeProof<C: Pairing> {
    /// `C_i = f_i(0).g1`
    c_i: C::G1Affine,
    /// `h1_i = sh_i.g1`
    h1_i: C::G1Affine,
    /// `s_i` is a proof of knowledge of the discrete logs of `(C_i, h1_i)` with respect to `g1`.
    koe_proof: koe::Proof<C::G1>,
}

impl<C: Pairing> SharesAndMore<C> {
    fn merge_with(self, mut others: Vec<Self>) -> Self {
        others.push(self);
        Self::merge(&others)
    }

    fn merge(keys: &[Self]) -> Self {
        let n = keys[0].bgpk.len();
        Self {
            c: (keys.iter().map(|key| key.c).sum::<C::G1>()).into_affine(),
            // TODO: affine conversions
            bgpk: (0..n).map(|j| {
                keys.iter()
                    .map(|key| key.bgpk[j])
                    .sum::<C::G2>()
                    .into_affine()
            }).collect(),
            h1: keys.iter().map(|key| key.h1).sum::<C::G1>().into_affine(),
            h2: keys.iter().map(|key| key.h2).sum::<C::G2>().into_affine(),
        }
    }
}

impl<C: Pairing> Transcript<C> {
    fn merge_with(self, others: &[Self]) -> Self {
        let mut others = others.to_vec();
        others.push(self);
        Self::merge(&others)
    }

    fn merge(transcripts: &[Self]) -> Self {
        let n = transcripts[0].a.len();
        let a = (0..n).map(|j| {
            transcripts.iter()
                .map(|t| t.a[j])
                .sum::<C::G1>().into_affine()
        }).collect();

        let shares = transcripts.iter()
            .map(|t| t.shares.clone())
            .collect::<Vec<_>>();
        let shares = SharesAndMore::merge(&shares);

        let koe_proofs = transcripts.iter()
            .flat_map(|t| t.koe_proofs.clone())
            .collect::<Vec<_>>();

        Self {
            shares,
            a,
            koe_proofs,
        }
    }
}

impl<'a, C: Pairing, D: EvaluationDomain<C::ScalarField>> Ceremony<'a, C, D> {
    fn setup(t: usize, bls_pks: &'a [C::G2Affine]) -> Self {
        let n = bls_pks.len();
        assert!(t <= n);
        //todo: test t = 1, t = n
        Self {
            n,
            t,
            bls_pks,
            domain: D::new(n).unwrap(),
            g1: C::G1::generator(),
            g2: C::G2::generator(),
        }
    }

    fn deal<R: Rng>(&self, rng: &mut R) -> Transcript<C> {
        // dealer's secrets
        let (f_mon, sh) = (DensePolynomial::rand(self.t - 1, rng), C::ScalarField::rand(rng));
        let ssk = f_mon[0];
        let f_lag: Vec<C::ScalarField> = f_mon.evaluate_over_domain(self.domain).evals.into_iter()
            .take(self.n)
            .collect();

        let _t = start_timer!(|| "Commitment to the secret polynomial in G1 and G2");
        let f_lag_g1 = single_base_msm(&f_lag, self.g1);
        let f_lag_g2 = single_base_msm(&f_lag, self.g2);
        end_timer!(_t);

        let _t = start_timer!(|| "Key exchange");
        let shared_keys: Vec<_> = self.bls_pks.iter()
            .map(|&pk_j| pk_j * sh)
            .collect();
        end_timer!(_t);

        let bgpk: Vec<_> = f_lag_g2.into_iter()
            .zip(shared_keys)
            .map(|(f_j, sk_j)| f_j + sk_j)
            .collect();
        let bgpk = C::G2::normalize_batch(&bgpk);

        let c = self.g1 * ssk;
        let h1 = self.g1 * sh;
        let h2 = self.g2 * sh;

        let instance = koe::Instance { base: self.g1, points: vec![c, h1] };
        let statement = koe::Statement { instance, dlogs: vec![ssk, sh] };
        let koe_proof = statement.prove(rng);

        // Can be batched, but who cares.
        let c = c.into_affine();
        let h1 = h1.into_affine();
        let h2 = h2.into_affine();
        let shares = SharesAndMore { bgpk, h1, h2, c };
        let koe_proof = KoeProof { c_i: c, h1_i: h1, koe_proof };
        Transcript {
            shares,
            a: f_lag_g1,
            koe_proofs: vec![koe_proof],
        }
    }

    fn verifier(&self) -> TranscriptVerifier<C> {
        let _t = start_timer!(|| "Interpolation");
        let domain_size_n = BarycentricDomain::of_size(self.domain, self.n);
        let domain_size_t = BarycentricDomain::of_size(self.domain, self.t);
        end_timer!(_t);
        TranscriptVerifier {
            domain_size_n,
            domain_size_t,
        }
    }

    #[cfg(test)]
    fn verify_transcript_unoptimized<R: Rng>(&self, t: &Transcript<C>, rng: &mut R) {
        // 2. h2 has the same dlog as h1
        assert_eq!(C::pairing(t.shares.h1, self.g2), C::pairing(self.g1, t.shares.h2));
        // 3. `A`s are the evaluations of a degree `t` polynomial in the exponent
        self.verify_as(&t, rng);
        // 4. `C = f(0).g1`
        self.verify_c(&t);
        // 5. `bgpk`s are well-formed
        self.verify_bgpks(&t, rng);
    }

    #[cfg(test)]
    // Checks that `bgpk_j = f_i(w^j).g2 + sh_i.pk_j, j = 0,...,n-1`.
    // For that we interpolate 3 degree `< n` polynomials in the exponent:
    // 1. `bgpk(w^j).g2 = bgpk_j`,
    // 2. `f(w^j).g1 = A_j`, and
    // 3. `pk(w^j).g2 = pk_j`.
    // Then `bgpk(z) = f(z) + sh.pk(z)`, and, as `h1 = sh_i.g1`,
    // we can check that `e(g1, bgpk(z)) = e(f(z), g2) + e(h1, pk(z))`.
    fn verify_bgpks<R: Rng>(&self, t: &Transcript<C>, rng: &mut R) {
        let z = C::ScalarField::rand(rng);
        let lis_at_z = BarycentricDomain::of_size(self.domain, self.n).lagrange_basis_at(z);
        let f_at_z_g1 = C::G1::msm(&t.a, &lis_at_z).unwrap();
        let bgpk_at_z_g2 = C::G2::msm(&t.shares.bgpk, &lis_at_z).unwrap();
        let pk_at_z_g2 = C::G2::msm(&self.bls_pks, &lis_at_z).unwrap();
        let lhs = C::pairing(self.g1, bgpk_at_z_g2);
        let rhs = C::pairing(f_at_z_g1, self.g2) + C::pairing(t.shares.h1, pk_at_z_g2);
        assert_eq!(lhs, rhs);
    }

    #[cfg(test)]
    fn verify_as<R: Rng>(&self, t: &Transcript<C>, rng: &mut R) {
        let z = C::ScalarField::rand(rng);
        let ls_deg_n_at_z = BarycentricDomain::of_size(self.domain, self.n).lagrange_basis_at(z);
        let ls_deg_t_at_z = BarycentricDomain::of_size(self.domain, self.t).lagrange_basis_at(z);
        let f_deg_n_at_z = C::G1::msm(&t.a, &ls_deg_n_at_z);
        let f_deg_t_at_z = C::G1::msm(&t.a[..self.t], &ls_deg_t_at_z);
        assert_eq!(f_deg_n_at_z, f_deg_t_at_z);
    }

    #[cfg(test)]
    fn verify_c(&self, t: &Transcript<C>) {
        let ls_at_0 = BarycentricDomain::of_size(self.domain, self.t).lagrange_basis_at(C::ScalarField::zero());
        let f_at_0 = C::G1::msm(&t.a[..self.t], &ls_at_0).unwrap();
        assert_eq!(t.shares.c, f_at_0.into_affine());
    }
}


impl<C: Pairing> TranscriptVerifier<C> {
    fn verify<D: EvaluationDomain<C::ScalarField>, R: Rng>(&self, params: &Ceremony<C, D>, t: &Transcript<C>, rng: &mut R) {
        // 1. Proofs of knowledge of the discrete logarithms: C_i = f_i(0).g1` and `h1_i = sh_i.g1`.
        let koes = t.koe_proofs.iter()
            .map(|w| {
                let x = koe::Instance {
                    base: params.g1,
                    points: vec![w.c_i.into_group(), w.h1_i.into_group()],
                };
                (x, w.koe_proof.clone())
            })
            .collect::<Vec<_>>();
        koe::Instance::batch_verify(&koes, rng);

        let sum_c = t.koe_proofs.iter()
            .map(|w| w.c_i)
            .sum::<C::G1>()
            .into_affine();

        let sum_h1 = t.koe_proofs.iter()
            .map(|w| w.h1_i)
            .sum::<C::G1>()
            .into_affine();

        let shares = &t.shares;
        assert_eq!(shares.c, sum_c);
        assert_eq!(shares.h1, sum_h1);

        // Merges the equations from `Self::verify_transcript_unoptimized` with random coefficients `r1, r2, r3`.
        // TODO: Fiat-Shamir
        let (r1, z) = (C::ScalarField::rand(rng), C::ScalarField::rand(rng));
        let r2 = r1.square();
        let r3 = r2 * r1;

        let _t = start_timer!(|| "Interpolation");
        let lis_size_n_at_z = self.domain_size_n.lagrange_basis_at(z);
        let (lis_size_t_at_z, lis_size_t_at_0) = {
            let mut lis_size_t_at_z = self.domain_size_t.lagrange_basis_at(z);
            let mut lis_size_t_at_0 = self.domain_size_t.lagrange_basis_at(C::ScalarField::zero());
            lis_size_t_at_z.resize(params.n, C::ScalarField::zero());
            lis_size_t_at_0.resize(params.n, C::ScalarField::zero());
            (lis_size_t_at_z, lis_size_t_at_0)
        };
        end_timer!(_t);

        let a_coeffs: Vec<_> = lis_size_n_at_z.iter()
            .zip(lis_size_t_at_z)
            .zip(lis_size_t_at_0)
            .map(|((li_n_z, li_t_z), li_t_0)| {
                (C::ScalarField::one() - r1) * li_n_z + r1 * li_t_z - r2 * li_t_0
            })
            .collect();

        let _t = start_timer!(|| "1xG1 + 2xG2 MSMs");
        let a_term = C::G1::msm(&t.a, &a_coeffs).unwrap();
        let bgpk_at_z = C::G2::msm(&shares.bgpk, &lis_size_n_at_z).unwrap();
        let pk_at_z = C::G2::msm(&params.bls_pks, &lis_size_n_at_z).unwrap();
        end_timer!(_t);

        assert!(C::multi_pairing(
            &[a_term + shares.c * r2 + shares.h1 * r3, -params.g1, shares.h1.into()],
            &[params.g2, bgpk_at_z + shares.h2 * r3, pk_at_z],
        ).is_zero());
    }
}

#[cfg(test)]
mod tests {
    use ark_poly::GeneralEvaluationDomain;
    use ark_std::{end_timer, start_timer, test_rng};

    use super::*;

    #[test]
    fn it_works() {
        let rng = &mut test_rng();

        let (n, t) = (7, 5);
        let signers = (0..n)
            .map(|_| ark_bls12_381::G2Affine::rand(rng))
            .collect::<Vec<_>>();
        let params =
            Ceremony::<ark_bls12_381::Bls12_381, GeneralEvaluationDomain<ark_bls12_381::Fr>>::setup(
                t, &signers,
            );
        let tww1 = params.deal(rng);
        let tww2 = params.deal(rng);

        params.verify_transcript_unoptimized(&tww1, rng);

        let transcript_verifier = params.verifier();


        transcript_verifier.verify(&params, &tww1, rng);

        let agg_tww = tww1.merge_with(&vec![tww2]);
        transcript_verifier.verify(&params, &agg_tww, rng);
    }

    fn _bench_dkg<C: Pairing>(f: usize) {
        let rng = &mut test_rng();

        // n = 3f+1 -- number of signers,
        // t = 2f+1 -- threshold number of signers
        // k = f+1 -- number of dealers
        let (n, t, k) = (3 * f + 1, 2 * f + 1, f + 1);
        let signers = (0..n)
            .map(|_| C::G2Affine::rand(rng))
            .collect::<Vec<_>>();
        let params =
            Ceremony::<C, GeneralEvaluationDomain<C::ScalarField>>::setup(
                t, &signers,
            );
        let _t = start_timer!(|| format!("Transcript generation, n = {}, t = {}", n, t));
        let transcript = params.deal(rng);
        end_timer!(_t);

        let _t = start_timer!(|| format!("Precomputation for transcript validation"));
        let transcript_verifier = params.verifier();
        end_timer!(_t);

        let _t = start_timer!(|| format!("Standalone transcript validation"));
        transcript_verifier.verify(&params, &transcript, rng);
        end_timer!(_t);

        let transcripts = vec![transcript; k];
        let _t = start_timer!(|| format!("Merging {} transcripts", k));
        let agg_transcript = Transcript::merge(&transcripts);
        end_timer!(_t);

        let _t = start_timer!(|| format!("Aggregate transcript validation, k = {}", k));
        transcript_verifier.verify(&params, &agg_transcript, rng);
        end_timer!(_t);
    }

    #[test]
    // #[ignore]
    fn bench_dkg_jam() {
        assert_eq!((2usize.pow(10) - 1) / 3, 341);
        _bench_dkg::<ark_bls12_381::Bls12_381>(341);
        assert_eq!((2usize.pow(16) - 1) / 3, 21845);
        // _bench_dkg::<ark_bls12_381::Bls12_381>(21845);
    }
}
