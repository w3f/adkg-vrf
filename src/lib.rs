use ark_ec::{CurveGroup, Group};
use ark_ec::pairing::Pairing;
use ark_ff::PrimeField;

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

pub mod deal;
mod signing;
mod utils;
pub mod koe;
mod agg;
mod bls;

#[cfg(test)]
mod tests {
    // TODO: test single signer, t = 1
    // TODO: test t = n
    // TODO: test multiple dealings

    use ark_ec::{CurveGroup, Group};
    use ark_ec::pairing::Pairing;
    use ark_poly::GeneralEvaluationDomain;
    use ark_std::test_rng;

    use crate::bls::BlsSigner;
    use crate::deal::Ceremony;
    use crate::signing::ThresholdVk;

    fn _it_works<C: Pairing>() {
        let rng = &mut test_rng();

        let (n, t) = (7, 5);
        let signers: Vec<BlsSigner<C>> = (0..n)
            .map(|_| BlsSigner::new(C::G2::generator(), rng))
            .collect();
        let signers_pks: Vec<_> = signers.iter()
            .map(|s| s.bls_pk_g2)
            .collect();
        let params = Ceremony::<C, GeneralEvaluationDomain<C::ScalarField>>::setup(t, &signers_pks);
        let transcript_verifier = params.verifier();

        let transcript = params.deal(rng);
        params.verify_transcript_unoptimized(&transcript, rng);
        transcript_verifier.verify(&params, &transcript, rng);

        let another_transcript = params.deal(rng);
        let agg_transcript = transcript.merge_with(&vec![another_transcript]);
        transcript_verifier.verify(&params, &agg_transcript, rng);

        let message = C::G1::generator();
        let sigs: Vec<_> = signers.iter()
            .map(|s| s.sign(message))
            .collect();

        let threshold_vk = ThresholdVk::from_share(&agg_transcript.shares);
        let sig_aggregator = params.aggregator(agg_transcript.shares);

        let mut sig_agg_session = sig_aggregator.start_session(message.into_affine());
        sig_agg_session.append_verify_sigs(sigs);
        let threshold_sig = sig_agg_session.finalize(&params);
        threshold_vk.verify(&threshold_sig);
    }

    #[test]
    fn it_works() {
        _it_works::<ark_bls12_381::Bls12_381>()
    }
}

