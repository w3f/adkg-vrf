use std::iter;

use ark_ec::{AffineRepr, CurveGroup};
use ark_ff::{AdditiveGroup, BigInteger, PrimeField, Zero};

pub fn table<C: AffineRepr>(bases: &[C]) -> Vec<C> {
    let mut table = vec![C::Group::zero()];
    for b in bases {
        let new_rows: Vec<C::Group> = table.iter()
            .map(|&prev_row| prev_row + b)
            .collect();
        table.extend(new_rows)
    }
    C::Group::normalize_batch(&table)
}

fn bit_slices<F: PrimeField>(scalars: &[F]) -> Vec<usize> {
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
    let table: Vec<C> = table(&bases);
    let slices = bit_slices(scalars);

    let mut acc = C::Group::zero();
    for idx in slices {
        acc.double_in_place();
        acc += table[idx]
    }
    acc
}

#[cfg(test)]
mod tests {
    use ark_ec::CurveGroup;
    use ark_std::{end_timer, start_timer, test_rng, UniformRand};

    use crate::strauss::short_msm;

    fn _test_short_msm<C: CurveGroup>(n: usize) {
        let rng = &mut test_rng();

        let scalars = (0..n)
            .map(|_| C::ScalarField::rand(rng))
            .collect::<Vec<_>>();
        let bases = (0..n)
            .map(|_| C::rand(rng))
            .collect::<Vec<_>>();
        let bases = C::normalize_batch(&bases);

        let _t_strauss = start_timer!(|| format!("Strauss {}-msm", n));
        let res1 = short_msm(&bases, &scalars);
        end_timer!(_t_strauss);

        let _t_naive = start_timer!(|| format!("Naive {}-msm", n));
        let res2 = bases.into_iter()
            .zip(scalars.iter())
            .map(|(b, s)| b * s)
            .sum();
        end_timer!(_t_naive);

        assert_eq!(res1, res2);
    }

    #[test]
    fn test_short_msm() {
        _test_short_msm::<ark_bls12_381::G1Projective>(4);
    }
}