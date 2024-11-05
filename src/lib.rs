/// Threshold Verifiable Unpredictable Function (VUF) scheme.
/// Produces an unpredictable output by aggregating a threshold number of vanilla BLS signatures on the input.
///
/// The scheme comprises 2 parts:
/// 1. a Distributed Key Generation (DKG) protocol that produces some data for a set of BLS signers, and
/// 2. a BLS signature aggregation scheme that leverages the data produced by the DKG
///    to aggregate the signatures from a subset of the signers into a threshold signature,
///    and additionally produce a VUF output.
///
/// An interesting property of the scheme is that the signers are not required to participate
/// in the protocol in any way other than producing vanilla BLS signatures.
/// That allows to transform any deployed BLS signature scheme, where the same message is being signed by multiple signers,
/// into a threshold scheme or a randomness beacon.
///
/// The implementation follows the notes by Alistair Stewart:
/// 1. https://hackmd.io/3968Gr5hSSmef-nptg2GRw
/// 2. https://hackmd.io/xqYBrigYQwyKM_0Sn5Xf4w

/// Aggregatable Publicly Verifiable Secret Sharing Scheme
pub mod dkg;
mod vanilla;
pub mod threshold;
mod utils;
pub mod koe;
mod agg;

#[cfg(test)]
mod tests {
    // TODO: test single signer, t = 1
    // TODO: test t = n
    // TODO: test multiple dealings

    use ark_ec::{CurveGroup, Group};
    use ark_ec::pairing::Pairing;
    use ark_poly::GeneralEvaluationDomain;
    use ark_std::test_rng;

    use crate::vanilla::BlsSigner;
    use crate::dkg::dealer::Ceremony;
    use crate::threshold::ThresholdVk;

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

        let mut sig_agg_session_n = sig_aggregator.start_session(message.into_affine());
        sig_agg_session_n.append_verify_sigs(sigs.clone());
        let threshold_sig_n = sig_agg_session_n.finalize(&params);
        let vuf_n = threshold_vk.vuf_unoptimized(&threshold_sig_n, message);

        let mut sig_agg_session_t = sig_aggregator.start_session(message.into_affine());
        sig_agg_session_t.append_verify_sigs(sigs.into_iter().take(t).collect());
        let threshold_sig_t = sig_agg_session_t.finalize(&params);
        let vuf_t = threshold_vk.vuf_unoptimized(&threshold_sig_t, message);
        assert_eq!(vuf_t, vuf_n);
    }

    #[test]
    fn it_works() {
        _it_works::<ark_bls12_381::Bls12_381>()
    }
}

