use std::iter;

use ark_ec::{AffineRepr, CurveGroup};
use ark_ec::scalar_mul::glv::GLVConfig;
use ark_ec::short_weierstrass::{Affine, Projective};
use ark_ff::{AdditiveGroup, BigInteger, PrimeField, Zero};
use ark_std::{end_timer, start_timer};

/// Simplest form of Straus' multi-scalar multiplication.
/// See the Handbook of Elliptic and Hyperelliptic Curve Cryptography, [Algorithm 9.23](https://hyperelliptic.org/HEHCC/chapters/chap09.pdf)

/// Precomputes sums of all subsets of the list of `points`.
// The ordering is as in `Self::bits_to_index`.
fn table<C: AffineRepr>(points: &[C]) -> Vec<C> {
    let mut table = vec![C::Group::zero()];
    for p in points {
        let new_rows: Vec<C::Group> = table.iter()
            .map(|&prev_row| prev_row + p)
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

    let scalars_as_bits: Vec<Vec<bool>> = scalars.iter()
        .map(|s| s.into_bigint().to_bits_be())
        .collect();

    let repr_bit_len = F::BigInt::NUM_LIMBS * 64;
    let scalar_bit_len = F::MODULUS_BIT_SIZE as usize;
    let skip = repr_bit_len - scalar_bit_len;
    (skip..repr_bit_len).map(|i| {
        let slice = scalars_as_bits.iter()
            .map(|s| s[i]);
        bits_to_index(slice, &powers_of_2)
    }).collect()
}

pub fn short_msm<C: AffineRepr>(points: &[C], scalars: &[C::ScalarField]) -> C::Group {
    let table = table(&points);
    let indices = indices(scalars);
    let mut acc = C::Group::zero();
    for idx in indices.into_iter().skip_while(|&idx| idx == 0)
    {
        acc.double_in_place();
        acc += table[idx]
    }
    acc
}

fn glv_decomposition<C: GLVConfig>(p: Affine<C>, s: C::ScalarField) -> Vec<(Affine<C>, C::ScalarField)> {
    let ((sgn_s1, s1), (sgn_s2, s2)) = C::scalar_decomposition(s);
    let mut p2 = C::endomorphism_affine(&p);
    let mut p1 = p;
    if !sgn_s1 {
        p1 = -p1;
    }
    if !sgn_s2 {
        p2 = -p2;
    }
    vec![(p1, s1), (p2, s2)]
}

pub fn short_msm_glv<C: GLVConfig>(points: &[Affine<C>], scalars: &[C::ScalarField]) -> Projective<C> {
    assert_eq!(points.len(), scalars.len());
    let _t_glv = start_timer!(|| format!("{} GLV decompositions", points.len()));
    let (glv_points, glv_scalars): (Vec<Affine<C>>, Vec<C::ScalarField>) = points.iter()
        .zip(scalars)
        .flat_map(|(p, s)| glv_decomposition(*p, *s))
        .unzip();
    end_timer!(_t_glv);
    let _t_msm = start_timer!(|| format!("straus {}-msm", glv_points.len()));
    let res = short_msm(&glv_points, &glv_scalars);
    end_timer!(_t_msm);
    res
}

#[cfg(test)]
mod tests {
    use ark_std::{test_rng, UniformRand};

    use super::*;

    fn _test_short_msm<C: GLVConfig>(n: usize) {
        let rng = &mut test_rng();

        let scalars = (0..n)
            .map(|_| C::ScalarField::rand(rng))
            .collect::<Vec<_>>();
        let points = (0..n)
            .map(|_| Affine::<C>::rand(rng))
            .collect::<Vec<_>>();

        let _t_naive = start_timer!(|| format!("Naive {}-msm", n));
        let res1: Projective<C> = points.iter()
            .zip(scalars.iter())
            .map(|(&p, s)| p * s)
            .sum();
        end_timer!(_t_naive);

        let _t_straus = start_timer!(|| format!("straus {}-msm", n));
        let res2 = short_msm(&points, &scalars);
        end_timer!(_t_straus);

        assert_eq!(res1, res2);

        let _t_glv = start_timer!(|| format!("GLV {}-msm", n));
        let res3 = short_msm_glv(&points, &scalars);
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