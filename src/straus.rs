use std::iter;

use ark_ec::{AffineRepr, CurveGroup};
use ark_ec::scalar_mul::glv::GLVConfig;
use ark_ec::short_weierstrass::{Affine, Projective};
use ark_ff::{AdditiveGroup, BigInteger, PrimeField, Zero};
use ark_std::{end_timer, start_timer};

/// Simplest form of Straus' multi-scalar multiplication.
/// See the Handbook of Elliptic and Hyperelliptic Curve Cryptography, [Algorithm 9.23](https://hyperelliptic.org/HEHCC/chapters/chap09.pdf)

/// Precomputes sums of all subsets of the list of points.
// See `Self::bits_to_index` for the order.
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

/// Converts `bits` highlighting a subset of the points to the index in the table where the sum of the subset is located.
// The powers of `2` start from `1`, so the least significant bit goes first.
fn bits_to_index<I: Iterator<Item=bool>>(bits: I, powers_of_2: &[u32]) -> usize {
    bits.zip(powers_of_2.iter())
        .filter_map(|(bit, power)| bit.then_some(power))
        .sum::<u32>() as usize
}

/// Converts a list of scalars into a list of lookup indices.
fn indices<F: PrimeField>(scalars: &[F]) -> Vec<usize> {
    let powers_of_2 = iter::successors(Some(1u32), move |prev| Some(prev << 1))
        .take(scalars.len())
        .collect::<Vec<_>>();

    let scalars: Vec<Vec<bool>> = scalars.iter()
        .map(|s| s.into_bigint().to_bits_be())
        .collect();

    let repr_bit_len = F::BigInt::NUM_LIMBS * 64;
    let scalar_bit_len = F::MODULUS_BIT_SIZE as usize;
    let skip = repr_bit_len - scalar_bit_len;
    (skip..repr_bit_len).map(|i| {
        let slice = scalars.iter()
            .map(|s| s[i]);
        bits_to_index(slice, &powers_of_2)
    }).collect()
}

pub fn short_msm<C: AffineRepr>(bases: &[C], scalars: &[C::ScalarField]) -> C::Group {
    let table = table(&bases);
    let indices = indices(scalars);
    let mut acc = C::Group::zero();
    for idx in indices.into_iter().skip_while(|&idx| idx == 0)
    {
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
    let _t_msm = start_timer!(|| format!("straus {}-msm", glv_bases.len()));
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

    use crate::straus::{short_msm, short_msm_glv};

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

        let _t_straus = start_timer!(|| format!("straus {}-msm", n));
        let res2 = short_msm(&bases, &scalars);
        end_timer!(_t_straus);

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