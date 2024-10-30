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

/// Parameters of a DKG ceremony.
/// The shares are dealt to the signers identified by their BLS public keys in G2.
/// It's critical that proofs of possession are checked for these keys.
struct Ceremony<'a, C: Pairing, D: EvaluationDomain<C::ScalarField>> {
    n: usize,
    t: usize,
    bls_pks: &'a [C::G2Affine],
    domain: D,
    g1: C::G1,
    g2: C::G2,
}

/// Represents...
/// `f_i` -- the dealer's secret polynomial,
/// `sh_i` -- a secret known to the dealer, such that `h1 = sh_i.g1` and `h2 = sh_i.g2`
/// `(bgpk_j, h2)` is precisely the El-Gamal encryption of the point `f_i(w^j).g2` with `pk_j`.
#[derive(Derivative)]
#[derivative(Clone)]
struct KeysDistributed<C: Pairing> {
    /// Signers' "threshold public keys". Actually these are El-Gamal
    /// `bgpk_j = f_i(w^j).g2 + sh_i.pk_j, j = 0,...,n-1`,
    bgpk: Vec<C::G2Affine>,
    /// `h1 = sh_i.g1`
    h1: C::G1Affine,
    /// `h2 = sh_i.g2`
    h2: C::G2Affine,
    /// `f_i(0).g1` // can be computed from `A_k` as `C = 1/d.sum(A_k)`,
    c: C::G1Affine,
}

/// Standalone or aggregated transcript with the witness.
// TODO: add ids (and weights
#[derive(Derivative)]
#[derivative(Clone)]
struct TranscriptWithWitness<C: Pairing> {
    keys: KeysDistributed<C>,
    // transcript's consistency evidence
    /// Commitment to the secret polynomial `A_j = f_i(w^j).g1, j = 0,...,n-1`
    a: Vec<C::G1Affine>,
    koe_proofs: Vec<KoeProof<C>>,
}

/// Proof that the dealer `i` knows the secrets dealt.
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

impl<C: Pairing> KeysDistributed<C> {
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

impl<C: Pairing> TranscriptWithWitness<C> {
    fn merge_with(self, others: &[Self])  -> Self {
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

        let keys = transcripts.iter()
            .map(|t| t.keys.clone())
            .collect::<Vec<_>>();
        let keys = KeysDistributed::merge(&keys);

        let koe_proofs = transcripts.iter()
            .flat_map(|t|t.koe_proofs.clone())
            .collect::<Vec<_>>();

        Self {
            keys,
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

    fn deal<R: Rng>(&self, rng: &mut R) -> TranscriptWithWitness<C> {
        // dealer's secrets
        let (f_mon, sh) = (DensePolynomial::rand(self.t - 1, rng), C::ScalarField::rand(rng));
        let ssk = f_mon[0];
        let f_lag: Vec<C::ScalarField> = f_mon.evaluate_over_domain(self.domain).evals.into_iter()
            .take(self.n)
            .collect();

        let _t = start_timer!(|| format!("As, n = {}", self.n));
        let a = single_base_msm(&f_lag, self.g1);
        assert_eq!(a.len(), self.n);
        end_timer!(_t);

        let _t = start_timer!(|| format!("bgpks, n = {}", self.n));
        // TODO: single_base_msm?
        let bgpk: Vec<_> = self.bls_pks.iter()
            .zip(f_lag)
            .map(|(&pk_j, f_lag_j)| self.g2 * f_lag_j + pk_j * sh)
            .collect();
        let bgpk = C::G2::normalize_batch(&bgpk);
        assert_eq!(bgpk.len(), self.bls_pks.len());
        end_timer!(_t);

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
        let keys = KeysDistributed { bgpk, h1, h2, c };
        let koe_proof = KoeProof { c_i: c, h1_i: h1, koe_proof };
        TranscriptWithWitness {
            keys,
            a,
            koe_proofs: vec![koe_proof]
        }
    }

    fn verify<R: Rng>(&self, tww: &TranscriptWithWitness<C>, rng: &mut R) {
        // 1. Proofs of knowledge of the discrete logarithms: C_i = f_i(0).g1` and `h1_i = sh_i.g1`.
        tww.koe_proofs.iter()
            .for_each(|w| {
                koe::Instance {
                    base: self.g1,
                    points: vec![w.c_i.into_group(), w.h1_i.into_group()]
                }.verify(&w.koe_proof);
            });

        let sum_c = tww.koe_proofs.iter()
            .map(|w|w.c_i)
            .sum::<C::G1>()
            .into_affine();

        let sum_h1 = tww.koe_proofs.iter()
            .map(|w|w.h1_i)
            .sum::<C::G1>()
            .into_affine();

        let t = &tww.keys;
        assert_eq!(t.c, sum_c);
        assert_eq!(t.h1, sum_h1);

        // Merges the equations from `Self::verify_transcript_unoptimized` with random coefficients `r1, r2, r3`.
        // TODO: Fiat-Shamir
        let (r1, z) = (C::ScalarField::rand(rng), C::ScalarField::rand(rng));
        let r2 = r1.square();
        let r3 = r2 * r1;

        let _t = start_timer!(|| format!("Interpolation, t = {}, n = {}", self.t, self.n));
        let lis_size_n_at_z = BarycentricDomain::of_size(self.domain, self.n).lagrange_basis_at(z);
        let (lis_size_t_at_z, lis_size_t_at_0) = {
            let domain_size_t = BarycentricDomain::of_size(self.domain, self.t);
            let mut lis_size_t_at_z = domain_size_t.lagrange_basis_at(z);
            let mut lis_size_t_at_0 = domain_size_t.lagrange_basis_at(C::ScalarField::zero());
            lis_size_t_at_z.resize(self.n, C::ScalarField::zero());
            lis_size_t_at_0.resize(self.n, C::ScalarField::zero());
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

        let _t = start_timer!(|| format!("1xG1 + 2xG2 MSMs, n = {}", self.n));
        let a_term = C::G1::msm(&tww.a, &a_coeffs).unwrap();
        let bgpk_at_z = C::G2::msm(&t.bgpk, &lis_size_n_at_z).unwrap();
        let pk_at_z = C::G2::msm(&self.bls_pks, &lis_size_n_at_z).unwrap();
        end_timer!(_t);

        assert!(C::multi_pairing(
            &[a_term + t.c * r2 + t.h1 * r3, -self.g1, t.h1.into()],
            &[self.g2, bgpk_at_z + t.h2 * r3, pk_at_z]
        ).is_zero());
    }

    #[cfg(test)]
    fn verify_transcript_unoptimized<R: Rng>(&self, tww: &TranscriptWithWitness<C>, rng: &mut R)  {
        // 2. h2 has the same dlog as h1
        assert_eq!(C::pairing(tww.keys.h1, self.g2), C::pairing(self.g1, tww.keys.h2));
        // 3. `A`s are the evaluations of a degree `t` polynomial in the exponent
        self.verify_as(&tww, rng);
        // 4. `C = f(0).g1`
        self.verify_c(&tww);
        // 5. `bgpk`s are well-formed
        self.verify_bgpks(&tww, rng);
    }

    #[cfg(test)]
    // Checks that `bgpk_j = f_i(w^j).g2 + sh_i.pk_j, j = 0,...,n-1`.
    // For that we interpolate 3 degree `< n` polynomials in the exponent:
    // 1. `bgpk(w^j).g2 = bgpk_j`,
    // 2. `f(w^j).g1 = A_j`, and
    // 3. `pk(w^j).g2 = pk_j`.
    // Then `bgpk(z) = f(z) + sh.pk(z)`, and, as `h1 = sh_i.g1`,
    // we can check that `e(g1, bgpk(z)) = e(f(z), g2) + e(h1, pk(z))`.
    fn verify_bgpks<R: Rng>(&self, tww: &TranscriptWithWitness<C>, rng: &mut R) {
        let z = C::ScalarField::rand(rng);
        let lis_at_z = BarycentricDomain::of_size(self.domain, self.n).lagrange_basis_at(z);
        let f_at_z_g1 = C::G1::msm(&tww.a, &lis_at_z).unwrap();
        let bgpk_at_z_g2 = C::G2::msm(&tww.keys.bgpk, &lis_at_z).unwrap();
        let pk_at_z_g2 = C::G2::msm(&self.bls_pks, &lis_at_z).unwrap();
        let lhs = C::pairing(self.g1, bgpk_at_z_g2);
        let rhs = C::pairing(f_at_z_g1, self.g2) + C::pairing(tww.keys.h1, pk_at_z_g2);
        assert_eq!(lhs, rhs);
    }

    #[cfg(test)]
    fn verify_as<R: Rng>(&self, tww: &TranscriptWithWitness<C>, rng: &mut R) {
        let z = C::ScalarField::rand(rng);
        let ls_deg_n_at_z = BarycentricDomain::of_size(self.domain, self.n).lagrange_basis_at(z);
        let ls_deg_t_at_z = BarycentricDomain::of_size(self.domain, self.t).lagrange_basis_at(z);
        let f_deg_n_at_z = C::G1::msm(&tww.a, &ls_deg_n_at_z);
        let f_deg_t_at_z = C::G1::msm(&tww.a[..self.t], &ls_deg_t_at_z);
        assert_eq!(f_deg_n_at_z, f_deg_t_at_z);
    }

    #[cfg(test)]
    fn verify_c(&self, tww: &TranscriptWithWitness<C>) {
        let ls_at_0 = BarycentricDomain::of_size(self.domain, self.t).lagrange_basis_at(C::ScalarField::zero());
        let f_at_0 = C::G1::msm(&tww.a[..self.t], &ls_at_0).unwrap();
        assert_eq!(tww.keys.c, f_at_0.into_affine());
    }
}

#[cfg(test)]
mod tests {
    use ark_ff::FftField;
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
        params.verify(&tww1, rng);

        let agg_tww = tww1.merge_with(&vec![tww2]);
        params.verify(&agg_tww, rng);
    }

    fn _bench_dkg<C: Pairing>(t: usize, n: usize) {
        let rng = &mut test_rng();
        let signers = (0..n)
            .map(|_| C::G2Affine::rand(rng))
            .collect::<Vec<_>>();
        let params =
            Ceremony::<C, GeneralEvaluationDomain<C::ScalarField>>::setup(
                t, &signers,
            );
        let _t = start_timer!(|| format!("Transcript generation, n = {}", n));
        let transcript = params.deal(rng);
        end_timer!(_t);

        let _t = start_timer!(|| format!("Standalone transcript validation, n = {}", n));
        params.verify(&transcript, rng);
        end_timer!(_t);
    }

    #[test]
    // #[ignore]
    fn bench_dkg_jam() {
        _bench_dkg::<ark_bls12_381::Bls12_381>(682,1023);
    }
}
