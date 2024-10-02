mod signing;

use ark_ec::{CurveGroup, Group, VariableBaseMSM};
use ark_ec::pairing::Pairing;
use ark_ec::scalar_mul::fixed_base::FixedBase;
use ark_ff::{Field, One, PrimeField, Zero};
use ark_poly::{DenseUVPolynomial, EvaluationDomain};
use ark_poly::univariate::DensePolynomial;
use ark_std::iter;
use ark_std::rand::Rng;
use ark_std::UniformRand;
use crate::signing::AggThresholdSig;

// Threshold signature/VUF/VRF scheme.
// Follows https://hackmd.io/3968Gr5hSSmef-nptg2GRw

// There is a set of signers identified by an ordered array of their BLS public keys in G2.
// Each signer knows his BLS secret key and his index in the array.

// There is a set of dealers (that may or may not intersect with the set of signers)


// `d` -- domain size (`N` in the hackmd), indexed by `k`
// `n <= d` -- signer set size (`n` in the hackmd), indexed by `j`
// `t <= n` -- the threshold, `deg(f) = t-1` for the secret-shared polynomial 'f'
// that gives a `t` out of `n` threshold scheme
// Dealers are indexed by `i`, their number is arbitrary.


// Represents a dealing (aka transcript) of the dealer `i`
// to the set of signers identified by an array `[pk_j], 0 <= j < n` of their public keys in `G2`.
//
// For the degree `t-1` polynomial `f_i`:
// - the secret being dealt is `f_i(0).G2`,
// - the corresponding public key is `f_i(0).G1`,
// - the share of the `j`-th signer is `f_i(w^j).G2`.
//
// The dealing contains:
// - `Y_j = f_i(w^j).pk_j, j = 0,...,n-1`,
//    the encryptions in `G2` of the shares to the corresponding signers.
// - `C = f_i(0).G1`
//    the verification key corresponding to the secret share.
// - `A_k = f_i(w^k).G1, k = 0,...,d-1`
//   "Feldman commitment" to `f_i` in the Lagrange form,
//    used as a witness to validate the encryptions `Y_j` against the public keys `pk_j`,
//    and the correctness of `C`.
// - `(H1, H2)`
//    a pair of points with the same dlog `H1=sh.G1, H2=sh.G2`.
//    After summation will supply such a pair with an "unknown" (if there's an honest party) dlog,
//    (similar to a KZG-ceremony of degree `1`).

// The difference to SCRAPE as described in Fig. 1 of https://eprint.iacr.org/2021/005.pdf is:
// - Commitments to the monomial coefficients of the polynomial other than `C = f_i(0).G1` are not used.
// - `u2 = f_i(0).G2'`, where `G2'` is another generator in `G2`, isn't used.
// - `(H1, H2)` is sampled

// Since the aggregation is commutative, can represent either a freshly sampled or an aggregated share.
// TODO: how about duplicates?
struct Shares<C: Pairing> {
    // TODO: keep the agg counter?
    c: C::G1Affine,
    a: Vec<C::G1Affine>,
    y: Vec<C::G2Affine>,
    h1: C::G1Affine,
    h2: C::G2Affine,
}

struct GlobalSetup<C: Pairing, D: EvaluationDomain<C::ScalarField>> {
    domain: D,
    g1: C::G1,
    g2: C::G2,
}

struct VirginBlsSigner<C: Pairing> {
    j: usize, // signer's index in the set, see comments to `GlobalSetup::dealer()`
    sk: C::ScalarField,
    bls_pk_g2: C::G2Affine, //TODO: prepared/proj?
}

struct ChadThresholdSigner<C: Pairing> {
    bls_signer: VirginBlsSigner<C>,
    bgpk: C::G2Affine,
}

impl<C: Pairing> VirginBlsSigner<C> {
    fn burgerize(self, agg: &Shares<C>) -> ChadThresholdSigner<C> {
        let sk_inv = self.sk.inverse().unwrap();
        let y = agg.y[self.j];
        // `gsk = f_agg(w^j).G2`
        // decryption of the aggregate share belonging to the signer
        let gsk = y * sk_inv;
        let bgpk = gsk + agg.h2 * self.sk; // `gsk` re-randomized with the `sk`
        let bgpk = bgpk.into_affine();
        ChadThresholdSigner {
            bls_signer: self,
            bgpk,
        }
    }

    fn sign(&self, m: C::G1) -> StandaloneSig<C> {
        let sig = m * self.sk;
        let sig = sig.into_affine();
        StandaloneSig {
            sig,
            pk: self.bls_pk_g2,
        }
    }
}

impl<C: Pairing> ChadThresholdSigner<C> {
    fn sign(&self, &m: &C::G1) -> ThresholdSig<C> {
        let bls_sig_with_pk = self.bls_signer.sign(m);
        ThresholdSig {
            j: self.bls_signer.j,
            bls_sig_with_pk,
            threshold_pk: self.bgpk,
        }
    }
}

struct StandaloneSig<C: Pairing> {
    sig: C::G1Affine,
    pk: C::G2Affine,
}

struct ThresholdSig<C: Pairing> {
    j: usize, // index of th signer
    bls_sig_with_pk: StandaloneSig<C>,
    threshold_pk: C::G2Affine, // aka bgpk
}

/// Deals shares to the set of signers identified by `bls_pks`
struct Dealer<C: Pairing, D: EvaluationDomain<C::ScalarField>> {
    domain: D,
    g1: C::G1,
    g2: C::G2,
    bls_pks: Vec<C::G2Affine>,
}

impl<C: Pairing, D: EvaluationDomain<C::ScalarField>> Dealer<C, D> {
    fn new(d: usize, bls_pks: Vec<C::G2Affine>) -> Self {
        Self {
            domain: D::new(d).unwrap(),
            g1: C::G1::generator(),
            g2: C::G2::generator(),
            bls_pks,
        }
    }

    /// Generates shares with the specified threshold to its signers.
    // As we aggregate the shares on chain, shares of all the signers are kept in a single struct.
    // TODO: PoP
    fn deal_shares<R: Rng>(&self, t: usize, rng: &mut R) -> Shares<C> {
        let f_mon = DensePolynomial::rand(t - 1, rng);
        let c = self.g1 * f_mon[0];
        let f_lag = f_mon.evaluate_over_domain(self.domain).evals;
        let a = single_base_msm(&f_lag, self.g1);
        assert_eq!(a.len(), self.domain.size());
        let y: Vec<_> = self.bls_pks.iter().zip(f_lag)
            .map(|(&pk, f_lag_i)| pk * f_lag_i)
            .collect();
        assert_eq!(y.len(), self.bls_pks.len());

        // After aggregating h1s and h2s we'll get a fresh pair of points in G1xG2
        // of the same unknown dlog for every dealing.
        let sh = C::ScalarField::rand(rng);
        let h1 = self.g1 * sh;
        let h2 = self.g2 * sh;

        // Convert the points into affine
        let y = C::G2::normalize_batch(&y);
        // TODO: these 2 could be added to the batch above, but who cares
        let c = c.into_affine();
        let h1 = h1.into_affine();
        let h2 = h2.into_affine();

        Shares { c, h1, h2, a, y }
    }
}

impl<C: Pairing, D: EvaluationDomain<C::ScalarField>> GlobalSetup<C, D> {
    //TODO: Default
    fn init(d: usize) -> Self {
        Self {
            domain: D::new(d).unwrap(),
            g1: C::G1::generator(),
            g2: C::G2::generator(),
        }
    }

    fn dealer(&self, bls_pks: Vec<C::G2Affine>) -> Dealer<C, D> {
        Dealer {
            domain: self.domain,
            g1: self.g1,
            g2: self.g2,
            bls_pks,
        }
    }

    fn signer<R: Rng>(&self, j: usize, rng: &mut R) -> VirginBlsSigner<C> {
        let sk = C::ScalarField::rand(rng);
        let bls_pk_g2 = self.g2 * sk;
        let bls_pk_g2 = bls_pk_g2.into_affine();
        VirginBlsSigner { j, sk, bls_pk_g2 }
    }

    // 1. `A_k, k = 0,...,d-1` is a commitment to a polynomial `f` such that `deg(f) < t`.
    // 2. Verification key validity: `C = f(0).G1`.
    // 3. Ciphertexts validity: `e(A_j,pk_j) = e(G1,Y_j), j = 0,...,n-1`.
    // 4. (H1,H2) well-formedness: `e(H1,G2) = e(H2,G1)`.
    // TODO: PoK of `sh` and `f(w^i)`
    // TODO: Return result
    // TODO: Batch verification
    // TODO: move to `Shares`?
    fn verify_share<R: Rng>(&self, t: usize, shares: &Shares<C>, rng: &mut R) {
        let z = C::ScalarField::rand(rng);
        let z_k: Vec<_> = iter::once(C::ScalarField::zero())
            .chain(
                iter::successors(Some(z), move |prev| Some(z * prev))
                    .take(self.domain.size() - t)
            ).collect();
        let q_mon = DensePolynomial::from_coefficients_slice(&z_k);
        let q_lag = q_mon.evaluate_over_domain(self.domain).evals;
        assert!(C::G1::msm(&shares.a, &q_lag).unwrap().is_zero());
        let c: C::G1 = shares.a.iter().sum();
        let c = c * self.domain.size_as_field_element().inverse().unwrap();
        assert_eq!(shares.c, c.into_affine());
    }

    // TODO: impl Sum for Shares
    fn aggregate_shares(&self, shares: &[Shares<C>]) -> Shares<C> {
        let d = self.domain.size();
        let l = shares[0].y.len(); //TODO: check lengths equal
        //TODO: bathconvert to affine
        Shares {
            c: shares.iter().map(|s| s.c).sum::<C::G1>().into_affine(),
            h1: shares.iter().map(|s| s.h1).sum::<C::G1>().into_affine(),
            h2: shares.iter().map(|s| s.h2).sum::<C::G2>().into_affine(),
            a: (0..d).map(|i| {
                shares.iter()
                    .map(|s| s.a[i])
                    .sum::<C::G1>().into_affine()
            }).collect(),
            y: (0..l).map(|i| {
                shares.iter()
                    .map(|s| s.y[i])
                    .sum::<C::G2>().into_affine()
            }).collect(),
        }
    }

    fn aggregate_sigs(&self, sigs_with_pks: &[ThresholdSig<C>]) -> AggThresholdSig<C> {
        let mut b = vec![false; self.domain.size()]; //TODO: n?
        sigs_with_pks.iter()
            .for_each(|sig| b[sig.j] = true);

        println!("{:?}", b);

        let lis = self.lis(&b);
        let bls_sigs: Vec<_> = sigs_with_pks.iter().map(|s| s.bls_sig_with_pk.sig).collect();
        let bls_pks: Vec<_> = sigs_with_pks.iter().map(|s| s.bls_sig_with_pk.pk).collect();
        let threshold_pks: Vec<_> = sigs_with_pks.iter().map(|s| s.threshold_pk).collect();
        let asig = C::G1::msm(&bls_sigs, &lis).unwrap().into_affine();
        let apk = C::G2::msm(&bls_pks, &lis).unwrap().into_affine();
        let abgpk = C::G2::msm(&threshold_pks, &lis).unwrap().into_affine();
        AggThresholdSig {
            bls_sig_with_pk: StandaloneSig { sig: asig, pk: apk },
            bgpk: abgpk,
        }
    }

    fn lis(&self, b: &[bool]) -> Vec<C::ScalarField> {
        let d = self.domain.size();
        assert_eq!(b.len(), d);
        let signers: Vec<_> = b.iter().enumerate().filter_map(|(i, b)| b.then_some(i)).collect();
        let non_signers: Vec<_> = b.iter().enumerate().filter_map(|(i, b)| (!b).then_some(i)).collect();
        let w = self.domain.group_gen();
        let powers_of_w: Vec<_> = iter::successors(Some(C::ScalarField::one()), move |prev| Some(w * prev))
            .take(d)
            .collect();
        let denom_exp = non_signers.iter().sum::<usize>() % d;
        let mut denom = powers_of_w[denom_exp] * self.domain.size_as_field_element();
        if non_signers.len() % 2 == 1 {
            denom = -denom;
        }
        let denom_inv = denom.inverse().unwrap();
        signers.into_iter().map(|i| {
            let num = non_signers.iter().map(|&k| powers_of_w[i] - powers_of_w[k]).product::<C::ScalarField>();
            num * denom_inv
        }).collect()
    }
}

// Multiply the same base by each scalar.
pub fn single_base_msm<C: CurveGroup>(scalars: &[C::ScalarField], g: C) -> Vec<C::Affine> {
    let window_size = FixedBase::get_mul_window_size(scalars.len());
    let bits_in_scalar = C::ScalarField::MODULUS_BIT_SIZE.try_into().unwrap();
    let table = FixedBase::get_window_table(bits_in_scalar, window_size, g);
    let scalars_in_g = FixedBase::msm(bits_in_scalar, window_size, &table, scalars);
    C::normalize_batch(&scalars_in_g)
}

#[cfg(test)]
mod tests {
    use ark_poly::{GeneralEvaluationDomain, Polynomial};
    use ark_std::test_rng;
    use crate::signing::ThresholdVk;
    use super::*;

    #[test]
    fn it_works() {
        let rng = &mut test_rng();
        let d = 16;
        let n = 10;
        let t = 7;
        let setup = GlobalSetup::<ark_bls12_381::Bls12_381, GeneralEvaluationDomain<ark_bls12_381::Fr>>::init(d);

        let signers: Vec<_> = (0..n)
            .map(|j| setup.signer(j, rng))
            .collect();
        let signers_pks: Vec<_> = signers.iter()
            .map(|s| s.bls_pk_g2)
            .collect();

        let dealers: Vec<_> = (0..n)
            .map(|_| setup.dealer(signers_pks.clone()))
            .collect();

        let shares: Vec<_> = dealers.iter()
            .map(|d| d.deal_shares(t, rng))
            .collect();

        // TODO: bad share test
        shares.iter()
            .for_each(|s| setup.verify_share(t, s, rng));

        // TODO: aggregate 1/3 + 1
        let agg = setup.aggregate_shares(&shares);
        let vk = ThresholdVk::from_share(&agg);

        let chads: Vec<_> = signers.into_iter()
            .map(|s| s.burgerize(&agg))
            .collect();

        let m = ark_bls12_381::G1Projective::generator();

        let sigs: Vec<_> = chads.iter()
            .map(|c| c.sign(&m))
            .collect();

        let threshold_sig = setup.aggregate_sigs(&sigs);
        vk.verify(&threshold_sig);
    }

    #[test]
    fn test_lis() {
        let rng = &mut test_rng();
        let setup = GlobalSetup::<ark_bls12_381::Bls12_381, GeneralEvaluationDomain<ark_bls12_381::Fr>>::init(4);

        let b = vec![true; 4];
        let lis = setup.lis(&b);
        assert_eq!(lis, setup.domain.evaluate_all_lagrange_coefficients(ark_bls12_381::Fr::zero()));

        let b = vec![false, true, false, true];
        let lis = setup.lis(&b);
        let p_mon = DensePolynomial::rand(1, rng);
        let p_lag = p_mon.evaluate_over_domain_by_ref(setup.domain).evals;
        assert_eq!(p_mon.evaluate(&ark_bls12_381::Fr::zero()), lis[0] * p_lag[1] + lis[1] * p_lag[3]);

        let b = vec![true, true, false, false];
        let lis = setup.lis(&b);
        let p_mon = DensePolynomial::rand(1, rng);
        let p_lag = p_mon.evaluate_over_domain_by_ref(setup.domain).evals;
        assert_eq!(p_mon.evaluate(&ark_bls12_381::Fr::zero()), lis[0] * p_lag[0] + lis[1] * p_lag[1]);

        let b = vec![true, true, true, false];
        let lis = setup.lis(&b);
        let p_mon = DensePolynomial::rand(2, rng);
        let p_lag = p_mon.evaluate_over_domain_by_ref(setup.domain).evals;
        assert_eq!(p_mon.evaluate(&ark_bls12_381::Fr::zero()), lis.iter().zip(p_lag.iter()).map(|(li, pi)| li * pi).sum());
    }

    // TODO: test single signer, t = 1
    // TODO: test t = n
    // TODO: test multiple dealings
}
