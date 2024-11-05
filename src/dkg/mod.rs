/// Aggregatable Publicly Verifiable Secret Sharing scheme (aPVSS) for sharing a secret key `f(0).g1` in G1,
/// corresponding to the public key `f(0).g2` in G2.
///
/// There are 2 types of participants:
/// 1. a fixed list of signers, identified with their BLS public keys in G2, and
/// 2. any number of dealers, whose authentication is the problem of a higher-level protocol.
/// A dealer samples a secret and produces a transcript containing shares of the secret, each encrypted to the corresponding signer,
/// together with a publicly verifiable proof of validity of the ciphertexts.
/// Transcripts with contributions from different dealers can be aggregated into a single verifiable transcript.
/// The scheme is secure (vaguely that means the parameters produced are secure),
/// if the final aggregated transcript is valid, and contains a contribution from a single honest dealer.
///
/// *A fun property* of the scheme is that signers don't have to use (or even decrypt) their shares in any way.
/// Instead, anyone can blindly use the ciphertexts to produce proofs that the threshold number of signers have signed.

pub mod dealer;