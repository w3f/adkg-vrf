use ark_ec::CurveGroup;
use ark_serialize::CanonicalSerialize;
use ark_std::rand::Rng;
use ark_std::UniformRand;
use derivative::Derivative;

use crate::utils::powers;

/// Batch-verifiable proofs of knowledge of discrete logarithms
/// of a number of `points` with respect with the same `base`.
#[derive(CanonicalSerialize)]
pub struct Instance<G: CurveGroup> {
    pub base: G,
    pub points: Vec<G>,
}

pub struct Statement<G: CurveGroup> {
    pub instance: Instance<G>,
    pub dlogs: Vec<G::ScalarField>,
}

#[derive(Derivative)]
#[derivative(Clone)]
pub struct Proof<G: CurveGroup> {
    r: G,
    s: G::ScalarField,
}

impl<G: CurveGroup> Statement<G> {
    pub fn prove<R: Rng>(&self, rng: &mut R) -> Proof<G> {
        let r = G::ScalarField::rand(rng);
        let r_big = self.instance.base * r;
        let mut tr = ark_transcript::Transcript::new_blank();
        tr.append(&self.instance);
        tr.append(&r_big);
        let c: G::ScalarField = tr.challenge(b"whatever").read_reduce();
        let s: G::ScalarField = self.dlogs.iter()
            .zip(powers(c).skip(1))
            .map(|(exp, c)| c * exp)
            .sum();
        let s = r - s;
        Proof { r: r_big, s }
    }
}

impl<G: CurveGroup> Instance<G> {
    pub fn verify(&self, proof: &Proof<G>) {
        let mut tr = ark_transcript::Transcript::new_blank();
        tr.append(self);
        tr.append(&proof.r);
        let c: G::ScalarField = tr.challenge(b"whatever").read_reduce();
        let p: G = self.points.iter()
            .zip(powers(c).skip(1))
            .map(|(&r, ci)| r * ci)
            .sum();
        assert_eq!(proof.r, self.base * proof.s + p)
    }
}


#[cfg(test)]
mod tests {
    use ark_ec::Group;
    use ark_std::{test_rng, UniformRand};

    use crate::koe::{Instance, Statement};

    #[test]
    fn koe() {
        let rng = &mut test_rng();

        let k = 10;
        let base = ark_bls12_381::G1Projective::generator();
        let exponents = (0..k).map(|_| ark_bls12_381::Fr::rand(rng)).collect::<Vec<_>>();
        let results = exponents.iter().map(|exp| base * exp).collect::<Vec<_>>();

        let instance = Instance { base, points: results };
        let statement = Statement { instance, dlogs: exponents };

        let proof = statement.prove(rng);
        statement.instance.verify(&proof);
    }
}