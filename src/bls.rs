use ark_ec::CurveGroup;
use ark_ec::pairing::Pairing;
use ark_std::rand::Rng;
use ark_std::UniformRand;

use crate::StandaloneSig;

pub struct BlsSigner<C: Pairing> {
    pub sk: C::ScalarField,
    pub bls_pk_g2: C::G2Affine, //TODO: prepared/proj?
}

impl<C: Pairing> BlsSigner<C> {
    #[cfg(test)]
    fn new<R: Rng>(g2: C::G2, rng: &mut R) -> Self {
        let sk = C::ScalarField::rand(rng);
        let bls_pk_g2 = g2 * sk;
        let bls_pk_g2 = bls_pk_g2.into_affine();
        Self { sk, bls_pk_g2 }
    }

    pub fn sign(&self, m: C::G1) -> StandaloneSig<C> {
        let sig = m * self.sk;
        let sig = sig.into_affine();
        StandaloneSig {
            sig,
            pk: self.bls_pk_g2,
        }
    }
}
