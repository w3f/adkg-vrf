use ark_ec::pairing::Pairing;
use ark_ec::{CurveGroup, VariableBaseMSM};
use ark_ec::Group;
use ark_ff::{Field, One, Zero};
use ark_poly::univariate::DensePolynomial;
use ark_poly::DenseUVPolynomial;
use ark_poly::EvaluationDomain;
use ark_std::rand::Rng;
use ark_std::UniformRand;

use crate::single_base_msm;
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
struct Transcript<C: Pairing> {
    /// `A_k = f_i(w^k).g1, k = 0,...,d-1`
    a: Vec<C::G1Affine>,
    /// `bgpk_j = f_i(w^j).g2 + sh_i.pk_j, j = 0,...,n-1`,
    bgpk: Vec<C::G2Affine>,
    /// `h1 = sh_i.g1`
    h1: C::G1Affine,
    /// `h2 = sh_i.g2`
    h2: C::G2Affine,
    // TODO: witness
    /// `f_i(0).g1` // can be computed from `A_k` as `C = 1/d.sum(A_k)`,
    c: C::G1Affine,
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

        let a = single_base_msm(&f_lag, self.g1);
        assert_eq!(a.len(), self.n);

        // TODO: single_base_msm?
        let bgpk: Vec<_> = self.bls_pks.iter()
            .zip(f_lag)
            .map(|(&pk_j, f_lag_j)| self.g2 * f_lag_j + pk_j * sh)
            .collect();
        let bgpk = C::G2::normalize_batch(&bgpk);
        assert_eq!(bgpk.len(), self.bls_pks.len());

        // Can be batched, but who cares.
        let c = (self.g1 * ssk).into_affine();
        let h1 = (self.g1 * sh).into_affine();
        let h2 = (self.g2 * sh).into_affine();

        Transcript { a, bgpk, h1, h2, c }
    }

    fn verify<R: Rng>(&self, t: &Transcript<C>, rng: &mut R) {
        let (a, z) = (C::ScalarField::rand(rng), C::ScalarField::rand(rng));
        let a2 = a.square();
        let ls_deg_n_at_z = BarycentricDomain::of_size(self.domain, self.n).lagrange_basis_at(z);
        let (ls_deg_t_at_z, ls_deg_t_at_0) = {
            let domain_size_t = BarycentricDomain::of_size(self.domain, self.t);
            let mut ls_deg_t_at_z = domain_size_t.lagrange_basis_at(z);
            let mut ls_deg_t_at_0 = domain_size_t.lagrange_basis_at(C::ScalarField::zero());
            ls_deg_t_at_z.resize(self.n, C::ScalarField::zero());
            ls_deg_t_at_0.resize(self.n, C::ScalarField::zero());
            (ls_deg_t_at_z, ls_deg_t_at_0)
        };

        let a_coeffs: Vec<_> = ls_deg_n_at_z.iter().zip(ls_deg_t_at_z).zip(ls_deg_t_at_0)
            .map(|((n_z, t_z), t_0)| (C::ScalarField::one() - a) * n_z + a * t_z - a2 * t_0)
            .collect();

        let a_term = C::G1::msm(&t.a[..self.n], &a_coeffs).unwrap();
        let bgpk_at_z = C::G2::msm(&t.bgpk, &ls_deg_n_at_z).unwrap();
        let pk_at_z = C::G2::msm(&self.bls_pks, &ls_deg_n_at_z).unwrap();

        assert!(C::multi_pairing(
            &[t.c * a2 + a_term, -self.g1, t.h1.into()],
            &[self.g2, bgpk_at_z, pk_at_z]
        ).is_zero());
    }

    #[cfg(test)]
    fn verify_bgpks<R: Rng>(&self, t: &Transcript<C>, rng: &mut R) {
        let z = C::ScalarField::rand(rng);
        let ls_at_z = BarycentricDomain::of_size(self.domain, self.n).lagrange_basis_at(z);
        let f_at_z = C::G1::msm(&t.a[..self.n], &ls_at_z).unwrap();
        let bgpk_at_z = C::G2::msm(&t.bgpk, &ls_at_z).unwrap();
        let pk_at_z = C::G2::msm(&self.bls_pks, &ls_at_z).unwrap();
        let lhs = C::pairing(self.g1, bgpk_at_z);
        let rhs = C::pairing(f_at_z, self.g2) + C::pairing(t.h1, pk_at_z);
        assert_eq!(lhs, rhs);
    }

    #[cfg(test)]
    fn verify_as<R: Rng>(&self, t: &Transcript<C>, rng: &mut R) {
        let z = C::ScalarField::rand(rng);
        let ls_deg_n_at_z = BarycentricDomain::of_size(self.domain, self.n).lagrange_basis_at(z);
        let ls_deg_t_at_z = BarycentricDomain::of_size(self.domain, self.t).lagrange_basis_at(z);
        let f_deg_n_at_z = C::G1::msm(&t.a[..self.n], &ls_deg_n_at_z);
        let f_deg_t_at_z = C::G1::msm(&t.a[..self.t], &ls_deg_t_at_z);
        assert_eq!(f_deg_n_at_z, f_deg_t_at_z);
    }

    #[cfg(test)]
    fn verify_c(&self, t: &Transcript<C>) {
        let ls_at_0 = BarycentricDomain::of_size(self.domain, self.t).lagrange_basis_at(C::ScalarField::zero());
        let f_at_0 = C::G1::msm(&t.a[..self.t], &ls_at_0).unwrap();
        assert_eq!(t.c, f_at_0.into_affine());
    }
}

#[cfg(test)]
mod tests {
    use ark_poly::GeneralEvaluationDomain;
    use ark_std::test_rng;

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
        let t = params.deal(rng);
        params.verify(&t, rng);
        params.verify_bgpks(&t, rng);
        params.verify_as(&t, rng);
        params.verify_c(&t);
    }
}
