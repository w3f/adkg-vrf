use std::iter;

use ark_ec::{AffineRepr, CurveGroup};
use ark_ec::scalar_mul::glv::GLVConfig;
use ark_ec::short_weierstrass::{Affine, Projective};
use ark_ff::{AdditiveGroup, BigInteger, PrimeField, Zero};
use ark_std::{end_timer, start_timer};

fn table<C: AffineRepr>(bases: &[C]) -> Vec<C> {
    let mut table = vec![C::Group::zero()];
    for b in bases {
        let new_rows: Vec<C::Group> = table.iter()
            .map(|&prev_row| prev_row + b)
            .collect();
        table.extend(new_rows)
    }
    C::Group::normalize_batch(&table)
}

fn indices<F: PrimeField>(scalars: &[F]) -> Vec<usize> {
    let powers_of_2 = iter::successors(Some(1usize), move |prev| Some(prev << 1))
        .take(scalars.len())
        .collect::<Vec<_>>();

    let scalars: Vec<Vec<bool>> = scalars.iter()
        .map(|s| s.into_bigint().to_bits_be())
        .collect();

    let repr_bit_len = F::BigInt::NUM_LIMBS * 64;
    (0..repr_bit_len).map(|i| {
        scalars.iter()
            .zip(powers_of_2.iter())
            .filter_map(|(bits, power)| bits[i].then_some(power))
            .sum()
    }).collect()
}

pub fn short_msm<C: AffineRepr>(bases: &[C], scalars: &[C::ScalarField]) -> C::Group {
    let table = table(&bases);
    let indices = indices(scalars); // TODO: filter trailing zeroes?
    let mut acc = C::Group::zero();
    for idx in indices {
        acc.double_in_place();
        acc += table[idx]
    }
    acc
}
 fn glv_decomposition<C: GLVConfig>(b: Affine<C>, s: C::ScalarField) -> Vec<(Affine<C>, C::ScalarField)> {
    let ((sgn_k1, k1), (sgn_k2, k2)) = C::scalar_decomposition(s);
    let mut b1 = b;
    let mut b2 = C::endomorphism_affine(&b);
    if !sgn_k1 {
        b1 = -b1;
    }
    if !sgn_k2 {
        b2 = -b2;
    }
    vec![(b1, k1), (b2, k2)]
}

pub fn short_msm_glv<C: GLVConfig>(bases: &[Affine<C>], scalars: &[C::ScalarField]) -> Projective<C> {
    assert_eq!(bases.len(), scalars.len());
    let _t_glv = start_timer!(|| format!("{} GLV decompositions", bases.len()));
    let (glv_bases, glv_scalars): (Vec<Affine<C>>, Vec<C::ScalarField>) = bases.iter()
        .zip(scalars)
        .flat_map(|(b, s)| glv_decomposition(*b, *s))
        .unzip();
    end_timer!(_t_glv);
    let _t_msm = start_timer!(|| format!("Strauss {}-msm", glv_bases.len()));
    let res = short_msm(&glv_bases, &glv_scalars);
    end_timer!(_t_msm);
    res
}

#[cfg(test)]
mod tests {
    use ark_ec::CurveGroup;
    use ark_ec::scalar_mul::glv::GLVConfig;
    use ark_ec::short_weierstrass::{Affine, Projective};
    use ark_std::{end_timer, start_timer, test_rng, UniformRand};

    use crate::strauss::{short_msm, short_msm_glv};

    fn _test_short_msm<C: GLVConfig>(n: usize) {
        let rng = &mut test_rng();

        let scalars = (0..n)
            .map(|_| C::ScalarField::rand(rng))
            .collect::<Vec<_>>();
        let bases = (0..n)
            .map(|_| Affine::<C>::rand(rng))
            .collect::<Vec<_>>();

        let _t_naive = start_timer!(|| format!("Naive {}-msm", n));
        let res1: Projective<C> = bases.iter()
            .zip(scalars.iter())
            .map(|(&b, s)| b * s)
            .sum();
        end_timer!(_t_naive);

        let _t_strauss = start_timer!(|| format!("Strauss {}-msm", n));
        let res2 = short_msm(&bases, &scalars);
        end_timer!(_t_strauss);

        assert_eq!(res1, res2);

        let _t_glv = start_timer!(|| format!("GLV {}-msm", n));
        let res3 = short_msm_glv(&bases, &scalars);
        end_timer!(_t_glv);

        assert_eq!(res1, res3);
    }

    #[test]
    fn test_short_msm() {
        _test_short_msm::<ark_bls12_381::g1::Config>(2);
        println!();
        _test_short_msm::<ark_bls12_381::g1::Config>(5);
    }
}