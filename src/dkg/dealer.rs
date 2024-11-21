use std::collections::HashMap;

use ark_ec::{AffineRepr, CurveGroup, PrimeGroup, VariableBaseMSM};
use ark_ec::pairing::Pairing;
use ark_ff::{Field, One, Zero};
use ark_poly::DenseUVPolynomial;
use ark_poly::EvaluationDomain;
use ark_poly::univariate::DensePolynomial;
use ark_std::{end_timer, start_timer, UniformRand};
use ark_std::rand::Rng;
use derivative::Derivative;

use crate::agg::SignatureAggregator;
use crate::bls::threshold::AggThresholdSig;
use crate::bls::vanilla::StandaloneSig;
use crate::dkg::Ceremony;
use crate::dkg::transcript::{KoeProof, Transcript};
use crate::koe;
use crate::utils::BarycentricDomain;

// TODO: integration test
// TODO: bench for logn = 16, 20
// TODO: Fiat-Shamir
// TODO: cofactors/subgroup checks
// TODO: ceremony goes to lib.rs

// `d` -- domain size (`N` in the hackmd), indexed by `k`
// `n <= d` -- signer set size (`n` in the hackmd), indexed by `j`
// `t <= n` -- the threshold, `deg(f) = t-1` for the secret-shared polynomial 'f'
// that gives a `t` out of `n` threshold scheme
// Dealers are indexed by `i`, their number is arbitrary.


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
pub struct SharesAndMore<C: Pairing> {
    /// The public key corresponding to the shared secret key.
    /// `c = f(0).g1`
    pub(crate) c: C::G1Affine,
    /// Shares of the secret, encrypted to the signers.
    /// `bgpk_j = f(w^j).g2 + sh.pk_j, j = 0,...,n-1`
    pub bgpk: Vec<C::G2Affine>,
    /// `h1 = sh.g1`
    pub(crate) h1: C::G1Affine,
    /// `h2 = sh.g2`
    pub(crate) h2: C::G2Affine,
}

impl<C: Pairing> SharesAndMore<C> {
    pub fn merge_with(self, mut others: Vec<Self>) -> Self {
        others.push(self);
        Self::merge(&others)
    }

    pub fn merge(keys: &[Self]) -> Self {
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

impl<'a, C: Pairing, D: EvaluationDomain<C::ScalarField>> Ceremony<'a, C, D> {
    pub fn deal<R: Rng>(&self, rng: &mut R) -> Transcript<C> {
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

    // TODO: args are not any more aggregatable
    pub fn aggregate_augmented_sigs(&self, augmented_sigs: Vec<Option<AggThresholdSig<C>>>) -> AggThresholdSig<C> {
        assert_eq!(augmented_sigs.len(), self.n);
        let mut bitmask: Vec<bool> = augmented_sigs.iter().map(|o| o.is_some()).collect();
        bitmask.resize(self.domain.size(), false);
        let set_bits_count = bitmask.iter().filter(|b| **b).count();
        assert!(set_bits_count >= self.t);
        let lis = BarycentricDomain::from_subset(self.domain, &bitmask)
            .lagrange_basis_at(C::ScalarField::zero());
        let augmented_sigs: Vec<AggThresholdSig<C>> = augmented_sigs.into_iter()
            .flatten()
            .collect();
        let bls_sigs: Vec<_> = augmented_sigs.iter().map(|s| s.bls_sig_with_pk.sig).collect();
        let bls_pks: Vec<_> = augmented_sigs.iter().map(|s| s.bls_sig_with_pk.pk).collect();
        let bgpks: Vec<_> = augmented_sigs.iter().map(|s| s.bgpk).collect();
        let asig = C::G1::msm(&bls_sigs, &lis).unwrap().into_affine();
        let apk = C::G2::msm(&bls_pks, &lis).unwrap().into_affine();
        let abgpk = C::G2::msm(&bgpks, &lis).unwrap().into_affine();
        AggThresholdSig {
            bls_sig_with_pk: StandaloneSig { sig: asig, pk: apk },
            bgpk: abgpk,
        }
    }


    pub fn aggregator(&self, final_share: SharesAndMore<C>) -> SignatureAggregator<C> {
        let pks: HashMap<_, _> = self.bls_pks.iter()
            .cloned()
            .zip(final_share.bgpk)
            .enumerate()
            .map(|(j, (bls_pk_j, bgpk_j))| (bls_pk_j, (bgpk_j, j)))
            .collect();
        SignatureAggregator {
            g2: self.g2.into_affine(),
            pks,
        }
    }

    #[cfg(test)]
    pub fn verify_transcript_unoptimized<R: Rng>(&self, t: &Transcript<C>, rng: &mut R) {
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


// Multiply the same base by each scalar.
pub fn single_base_msm<C: CurveGroup>(scalars: &[C::ScalarField], g: C) -> Vec<C::Affine> {
    g.batch_mul(scalars)
}

#[cfg(test)]
mod tests {
    use ark_poly::GeneralEvaluationDomain;
    use ark_std::{end_timer, start_timer, test_rng};

    use super::*;

    fn _bench_dkg<C: Pairing>(f: usize) {
        let rng = &mut test_rng();

        // n = 3f+1 -- number of signers,
        // t = 2f+1 -- threshold number of signers
        // k = f+1 -- number of dealers
        let (n, t, k) = (3 * f + 1, 2 * f + 1, f + 1);
        let signers = (0..n)
            .map(|_| C::G2Affine::rand(rng))
            .collect::<Vec<_>>();
        let params = Ceremony::<C, GeneralEvaluationDomain<C::ScalarField>>::setup(t, &signers);
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
    #[ignore]
    #[cfg(all(not(debug_assertions), feature = "print-trace"))]
    fn bench_dkg_10() {
        assert_eq!((2usize.pow(10) - 1) / 3, 341);
        _bench_dkg::<ark_bls12_381::Bls12_381>(341);
    }

    #[test]
    #[ignore]
    #[cfg(all(not(debug_assertions), feature = "print-trace"))]
    fn bench_dkg_16() {
        assert_eq!((2usize.pow(16) - 1) / 3, 21845);
        _bench_dkg::<ark_bls12_381::Bls12_381>(21845);
    }
}