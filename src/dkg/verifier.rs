use ark_ec::{AffineRepr, CurveGroup, VariableBaseMSM};
use ark_ec::pairing::Pairing;
use ark_ff::{Field, One, Zero};
use ark_poly::EvaluationDomain;
use ark_std::{end_timer, start_timer, UniformRand};
use ark_std::rand::Rng;

use crate::dkg::Ceremony;
use crate::dkg::transcript::Transcript;
use crate::koe;
use crate::utils::BarycentricDomain;

/// Precomputed barycentric weights to facilitate interpolation.
/// Depend only on `(t,n)` so can be reused between the ceremonies.
/// `Ceremony::verifier()` creates the object.
/// TODO: 1. can be computed faster
/// TODO: 2. can keep lis_at_0
/// TODO: 3. lis_at_0 can be computed faster
pub struct TranscriptVerifier<C: Pairing> {
    pub(crate) domain_size_n: BarycentricDomain<C::ScalarField>,
    pub(crate) domain_size_t: BarycentricDomain<C::ScalarField>,
}

impl<C: Pairing> TranscriptVerifier<C> {

    // TODO: check params
    pub fn verify<D: EvaluationDomain<C::ScalarField>, R: Rng>(&self, params: &Ceremony<C, D>, t: &Transcript<C>, rng: &mut R) {
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