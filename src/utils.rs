use ark_ff::PrimeField;
use ark_std::iter;

/// Evaluates the Lagrange basis polynomials over the set `x_1, ..., x_n` at `z`.
/// Returns `L_j(z), j = 1,...,n`, where `deg(L_j) = n - 1`, `L_j(x_j) = 1` and `L_j(x_k) = 0` for `k != j`.
// Follows the formulae from https://people.maths.ox.ac.uk/trefethen/barycentric.pdf, p.3.
// Fails if `x_j = x_k` for `j != k`.
pub fn lagrange_basis_at<F: PrimeField>(xs: &[F], z: &F) -> Vec<F> {
    // 1 / w_j = prod(x_j - x_k, k != j)
    let ws_inv = barycentric_weights_inv(xs);

    // z - x_1, ..., z - x_n
    let z_minus_xs: Vec<F> = iter::repeat(*z).zip(xs)
        .map(|(z, xj)| z - xj)
        .collect();

    // l(z) = (z - x_1) ... (z - x_n)
    let l_at_z: F = z_minus_xs.iter()
        .product();

    // c_j = w_j / (z - x_j)
    let cs = {
        let mut cs_inv: Vec<F> = ws_inv.into_iter().zip(z_minus_xs)
            .map(|(wj_inv, z_minus_xj)| wj_inv * z_minus_xj)
            .collect();
        ark_ff::batch_inversion(&mut cs_inv);
        cs_inv
    };

    // L_j(z) = c_j.l(z)
    cs.iter()
        .map(|cj| l_at_z * cj)
        .collect()
}

/// Inverted barycentric weights of the set `x_1, ..., x_n`.
/// Returns `w_j = prod(x_j - x_k, k != j), j = 1,...,n`.
// Can be computed faster than O(n^2) by evaluating the derivative of the vanishing polynomial.
fn barycentric_weights_inv<F: PrimeField>(xs: &[F]) -> Vec<F> {
    xs.iter().map(|xj| xs.iter()
        .filter_map(|xk| (xk != xj).then_some(*xj - xk))
        .product(),
    ).collect()
}

#[cfg(test)]
mod tests {
    use ark_poly::univariate::DensePolynomial;
    use ark_poly::DenseUVPolynomial;
    use ark_poly::{EvaluationDomain, GeneralEvaluationDomain, Polynomial};
    use ark_std::test_rng;
    use ark_std::UniformRand;

    use super::*;

    #[test]
    // x_j = u^j, where u is a primary root of unity of order n
    fn over_roots_of_unity() {
        let rng = &mut test_rng();

        let n = 16;
        let domain = GeneralEvaluationDomain::new(n).unwrap();
        let xs = domain.elements().collect::<Vec<_>>();
        let z = ark_bls12_381::Fr::rand(rng);
        let ls = lagrange_basis_at(&xs, &z);

        assert_eq!(ls, domain.evaluate_all_lagrange_coefficients(z));
    }

    #[test]
    // p(z) = p(x_1).L_1(z) + ... + p(x_n).L_n(z), if deg(p) < n
    fn over_random_set() {
        let rng = &mut test_rng();

        let n = 7;
        let xs = (0..n)
            .map(|_| ark_bls12_381::Fr::rand(rng))
            .collect::<Vec<_>>();
        let z = ark_bls12_381::Fr::rand(rng);
        let ls = lagrange_basis_at(&xs, &z);

        let p = DensePolynomial::rand(n - 1, rng);
        let p_at_z = xs.iter().zip(ls)
            .map(|(xj, lj_at_z)| lj_at_z * p.evaluate(xj))
            .sum::<ark_bls12_381::Fr>();

        assert_eq!(p_at_z, p.evaluate(&z));
    }
}
