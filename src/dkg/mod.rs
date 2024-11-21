use ark_ec::pairing::Pairing;
use ark_poly::EvaluationDomain;

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

/// Parameters of an aPVSS instantiation.
pub struct Ceremony<'a, C: Pairing, D: EvaluationDomain<C::ScalarField>> {
    /// The number of signers.
    pub n: usize,
    /// The threshold, i.e. the minimal number of signers required to reconstruct the shared secret.
    pub t: usize,
    /// The signers' bls public keys in G2.
    /// **It's critical that proofs of possession are checked for these keys.**
    pub bls_pks: &'a [C::G2Affine],
    /// An FFT-friendly multiplicative subgroup of the field of size not less than `n`.
    /// The evaluation points are the first `n` elements of the subgroup: `x_j = w^j, j = 0,...,n-1`,
    /// where `w` is the generator of the subgroup.
    pub domain: D,
    /// Generator of G1.
    pub g1: C::G1,
    /// Generator of G2.
    pub g2: C::G2,
}