use ark_ec::Group;
use ark_ec::pairing::Pairing;
use crate::{Shares, StandaloneSig};



// Used to verify aggregated threshold signatures.
// `c = f(0).g1` is the public key associated with the dealing.
// `(h1, h2)` bind signers to the dealing via `bgpk_j = gsk_j + sk_j.h2`.
pub struct ThresholdVk<C: Pairing> {
    c: C::G1Affine,
    h1: C::G1Affine,
    h2: C::G2Affine,
    // todo: skip serialization
    g1: C::G1,
    g2: C::G2,
}

pub struct AggThresholdSig<C: Pairing> {
    pub(crate) bls_sig_with_pk: StandaloneSig<C>,
    pub(crate) bgpk: C::G2Affine,
}

impl<C: Pairing> ThresholdVk<C> {

    pub fn from_share(share: &Shares<C>) -> Self { //TODO: consume?
        Self {
            c: share.c,
            h1: share.h1,
            h2: share.h2,
            g1: C::G1::generator(),
            g2: C::G2::generator(),
        }
    }
    pub fn verify(&self, sig: &AggThresholdSig<C>) {
        assert_eq!(
            C::pairing(self.g1.into(), sig.bgpk),
            C::multi_pairing(&[self.c, self.h1], &[self.g2.into(), sig.bls_sig_with_pk.pk])
        );
    }
}