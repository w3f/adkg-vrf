use ark_ec::pairing::Pairing;
use ark_ec::{AffineRepr, CurveGroup, VariableBaseMSM};
use ark_ff::{Field, One, Zero};
use ark_poly::{EvaluationDomain, GeneralEvaluationDomain};
use ark_std::rand::Rng;
use ark_std::{end_timer, start_timer, UniformRand};
use ark_std::{vec, vec::Vec};

use crate::dkg::transcript::DkgTranscript;
use crate::dkg::{Ceremony, DkgResult};
use crate::koe;
use crate::utils::BarycentricDomain;

/// Precomputed barycentric weights to facilitate interpolation.
/// Depend only on `(t,n)` so can be reused between the ceremonies.
/// `Ceremony::verifier()` creates the object.
pub struct TranscriptVerifier<C: Pairing> {
    domain_size_n: BarycentricDomain<C::ScalarField>,
    domain_size_t: BarycentricDomain<C::ScalarField>,
}

impl<C: Pairing> TranscriptVerifier<C> {
    pub fn new(n: usize, t: usize) -> Self {
        let fft_domain = GeneralEvaluationDomain::new(n).unwrap();
        Self::new_with_domain(fft_domain, n, t)
    }

    /// TODO: 1. can be computed faster
    /// TODO: 2. can keep lis_at_0
    /// TODO: 3. lis_at_0 can be computed faster
    pub fn new_with_domain<D: EvaluationDomain<C::ScalarField>>(fft_domain: D, n: usize, t: usize) -> Self {
        assert!(fft_domain.size() >= n);
        assert!(n >= t);
        assert!(t > 0);
        let _t = start_timer!(|| "Interpolation");
        let domain_size_n = BarycentricDomain::of_size(fft_domain, n);
        let domain_size_t = BarycentricDomain::of_size(fft_domain, t);
        end_timer!(_t);
        Self {
            domain_size_n,
            domain_size_t,
        }
    }

    /// Uses Fiat-Shamir randomness to verify the DKG `transcript`, and returns the payload, if valid.
    /// Is useful for on-chain verification of transcripts, when instead of aggregating transcripts,
    /// valid payloads are aggregated.
    pub fn verify_with_fs<D: EvaluationDomain<C::ScalarField>>(&self, params: &Ceremony<C, D>, transcript: DkgTranscript<C>) -> Result<DkgResult<C>, ()> {
        let mut fs = ark_transcript::Transcript::new_labeled(b"adkg_vrf::dkg::verifier");
        // TODO: hash the pks
        // fs.append(params);
        fs.append(&transcript);
        let rng = &mut fs.challenge(b"rng");
        if self.verify(params, &transcript, rng) {
            Ok(transcript.payload)
        } else {
            Err(())
        }
    }

    // TODO: check params
    #[must_use]
    pub fn verify<D: EvaluationDomain<C::ScalarField>, R: Rng>(&self, params: &Ceremony<C, D>, t: &DkgTranscript<C>, rng: &mut R) -> bool {
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
        if !koe::Instance::batch_verify(&koes, rng) {
            return false;
        }

        let payload = &t.payload;

        let sum_c = t.koe_proofs.iter()
            .map(|w| w.c_i)
            .sum::<C::G1>()
            .into_affine();
        let sum_h1 = t.koe_proofs.iter()
            .map(|w| w.h1_i)
            .sum::<C::G1>()
            .into_affine();

        // `C` and `h1` in the payload are consistent with the `C_i`s and `h1_i`s "signed".
        if sum_c != payload.c || sum_h1 != payload.h1 {
            return false;
        }

        // 2, 3, 4, 5
        // Merges the equations from `Ceremony::verify_transcript_unoptimized` with random coefficients `r1, r2, r3`.
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
        let bgpk_at_z = C::G2::msm(&payload.bgpk, &lis_size_n_at_z).unwrap();
        let pk_at_z = C::G2::msm(&params.bls_pks, &lis_size_n_at_z).unwrap();
        end_timer!(_t);

        C::multi_pairing(
            &[a_term + payload.c * r2 + payload.h1 * r3, -params.g1, payload.h1.into()],
            &[params.g2, bgpk_at_z + payload.h2 * r3, pk_at_z],
        ).is_zero()
    }
}

#[cfg(test)]
impl<'a, C: Pairing, D: EvaluationDomain<C::ScalarField>> Ceremony<'a, C, D> {
    pub fn verify_transcript_unoptimized<R: Rng>(&self, t: &DkgTranscript<C>, rng: &mut R) {
        // 2. h2 has the same dlog as h1
        assert_eq!(C::pairing(t.payload.h1, self.g2), C::pairing(self.g1, t.payload.h2));
        // 3. `A`s are the evaluations of a degree `t` polynomial in the exponent
        self.verify_as(&t, rng);
        // 4. `C = f(0).g1`
        self.verify_c(&t);
        // 5. `bgpk`s are well-formed
        self.verify_bgpks(&t, rng);
    }

    // Checks that `bgpk_j = f_i(w^j).g2 + sh_i.pk_j, j = 0,...,n-1`.
    // For that we interpolate 3 degree `< n` polynomials in the exponent:
    // 1. `bgpk(w^j).g2 = bgpk_j`,
    // 2. `f(w^j).g1 = A_j`, and
    // 3. `pk(w^j).g2 = pk_j`.
    // Then `bgpk(z) = f(z) + sh.pk(z)`, and, as `h1 = sh_i.g1`,
    // we can check that `e(g1, bgpk(z)) = e(f(z), g2) + e(h1, pk(z))`.
    fn verify_bgpks<R: Rng>(&self, t: &DkgTranscript<C>, rng: &mut R) {
        let z = C::ScalarField::rand(rng);
        let lis_at_z = BarycentricDomain::of_size(self.domain, self.n).lagrange_basis_at(z);
        let f_at_z_g1 = C::G1::msm(&t.a, &lis_at_z).unwrap();
        let bgpk_at_z_g2 = C::G2::msm(&t.payload.bgpk, &lis_at_z).unwrap();
        let pk_at_z_g2 = C::G2::msm(&self.bls_pks, &lis_at_z).unwrap();
        let lhs = C::pairing(self.g1, bgpk_at_z_g2);
        let rhs = C::pairing(f_at_z_g1, self.g2) + C::pairing(t.payload.h1, pk_at_z_g2);
        assert_eq!(lhs, rhs);
    }

    fn verify_as<R: Rng>(&self, t: &DkgTranscript<C>, rng: &mut R) {
        let z = C::ScalarField::rand(rng);
        let ls_deg_n_at_z = BarycentricDomain::of_size(self.domain, self.n).lagrange_basis_at(z);
        let ls_deg_t_at_z = BarycentricDomain::of_size(self.domain, self.t).lagrange_basis_at(z);
        let f_deg_n_at_z = C::G1::msm(&t.a, &ls_deg_n_at_z);
        let f_deg_t_at_z = C::G1::msm(&t.a[..self.t], &ls_deg_t_at_z);
        assert_eq!(f_deg_n_at_z, f_deg_t_at_z);
    }

    fn verify_c(&self, t: &DkgTranscript<C>) {
        let ls_at_0 = BarycentricDomain::of_size(self.domain, self.t).lagrange_basis_at(C::ScalarField::zero());
        let f_at_0 = C::G1::msm(&t.a[..self.t], &ls_at_0).unwrap();
        assert_eq!(t.payload.c, f_at_0.into_affine());
    }
}
