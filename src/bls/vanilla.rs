use ark_ec::CurveGroup;
use ark_ec::pairing::Pairing;
use ark_std::rand::Rng;
use ark_std::UniformRand;

pub struct BlsSigner<C: Pairing> {
    sk: C::ScalarField,
    pub bls_pk_g2: C::G2Affine, //TODO: prepared/proj?
}

#[derive(Clone, Debug, PartialEq)]
pub struct StandaloneSig<C: Pairing> {
    pub sig: C::G1Affine,
    pub pk: C::G2Affine,
}

impl<C: Pairing> BlsSigner<C> {
    pub fn new<R: Rng>(g2: C::G2, rng: &mut R) -> Self {
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

impl<C: Pairing> StandaloneSig<C> {
    pub fn verify_unoptimized(&self, m: C::G1, g2: C::G2Affine) {
        assert_eq!(
            C::pairing(self.sig, g2),
            C::pairing(m.into(), self.pk)
        );
    }
}

