use ark_ec::CurveGroup;
use ark_ec::pairing::Pairing;
use ark_ec::scalar_mul::fixed_base::FixedBase;
use ark_ff::PrimeField;

use bls::StandaloneSig;

pub mod deal;
mod signing;
mod utils;
pub mod koe;
mod agg;
mod bls;

/// Threshold Verifiable Unpredictable Function (VUF) scheme.
/// Produces an unpredictable output by aggregating a threshold number of vanilla BLS signatures on the input.

// Follows https://hackmd.io/3968Gr5hSSmef-nptg2GRw

// There is a set of signers identified by an ordered array of their BLS public keys in G2.
// Each signer knows his BLS secret key and his index in the array.

// There is a set of dealers (that may or may not intersect with the set of signers)


// `d` -- domain size (`N` in the hackmd), indexed by `k`
// `n <= d` -- signer set size (`n` in the hackmd), indexed by `j`
// `t <= n` -- the threshold, `deg(f) = t-1` for the secret-shared polynomial 'f'
// that gives a `t` out of `n` threshold scheme
// Dealers are indexed by `i`, their number is arbitrary.

struct ThresholdSig<C: Pairing> {
    j: usize, // index of th signer
    bls_sig_with_pk: StandaloneSig<C>,
    threshold_pk: C::G2Affine, // aka bgpk
}

// Multiply the same base by each scalar.
pub fn single_base_msm<C: CurveGroup>(scalars: &[C::ScalarField], g: C) -> Vec<C::Affine> {
    let window_size = FixedBase::get_mul_window_size(scalars.len());
    let bits_in_scalar = C::ScalarField::MODULUS_BIT_SIZE.try_into().unwrap();
    let table = FixedBase::get_window_table(bits_in_scalar, window_size, g);
    let scalars_in_g = FixedBase::msm(bits_in_scalar, window_size, &table, scalars);
    C::normalize_batch(&scalars_in_g)
}

#[cfg(test)]
mod tests {
    // TODO: test single signer, t = 1
    // TODO: test t = n
    // TODO: test multiple dealings
}
