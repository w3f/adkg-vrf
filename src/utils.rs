use ark_ff::{FftField, Field, PrimeField};
use ark_poly::{DenseUVPolynomial, EvaluationDomain};
use ark_poly::univariate::DensePolynomial;
use ark_std::{end_timer, iter, start_timer};

/// Utilities for Lagrange interpolation over a subset of an FFT domain.

/// The vanishing polynomial of `x`.
/// `v(X) = X - x`
fn v<F: Field>(x: F) -> DensePolynomial<F> {
    DensePolynomial::from_coefficients_vec(vec![-x, F::one()]) // -x*0 + 1*X
}

/// The vanishing polynomial of the set `x1,...,xn`.
/// `v(X) = (X - x1) * ... * (X - xn)`
// Runs in `O(nlog^2(n))` when the field `F` contains a radix-2 domain.
// `n` doesn't have to be a power of `2`.
fn v_of<F: FftField>(xs: &[F]) -> DensePolynomial<F> {
    let n = xs.len();
    let mut product_tree = Vec::with_capacity(2 * n - 1);
    product_tree.extend(xs.iter().map(|&xi| v(xi)));
    for i in 0..n - 1 {
        product_tree.push(&product_tree[2 * i] * &product_tree[2 * i + 1])
    }
    product_tree[2 * n - 2].clone()
}

/// Computes `f'`, the formal derivative of 'f'.
fn diff<F: Field>(f: &DensePolynomial<F>) -> DensePolynomial<F> {
    let df_coeffs = f.iter()
        .enumerate()
        .skip(1)
        .map(|(i, ci)| F::from(i as u32) * ci)
        .collect();
    DensePolynomial::from_coefficients_vec(df_coeffs)
}

/// Inverted barycentric weights of the set `x_1, ..., x_n`.
/// Returns `w_j = prod(x_j - x_k, k != j), j = 1,...,n`.
// Runs in O(n^2)
fn barycentric_weights_inv<F: Field>(xs: &[F]) -> Vec<F> {
    xs.iter().map(|xj| xs.iter()
        .filter_map(|xk| (xk != xj).then_some(*xj - xk))
        .product(),
    ).collect()
}

/// Inverted barycentric weights of the subset of the `domain` identified by the bitmask `b`.
/// Runs in O(nlog^2(n)) by evaluating the derivative of the vanishing polynomial of the subset over the whole domain.
fn barycentric_weights_inv_in_domain<F: FftField, D: EvaluationDomain<F>>(domain: D, b: &[bool]) -> Vec<F> {
    assert_eq!(b.len(), domain.size());
    let xs = domain.elements()
        .zip(b)
        .filter_map(|(xi, bi)| bi.then_some(xi))
        .collect::<Vec<_>>();
    let _t = start_timer!(|| "Product tree");
    let v = v_of(&xs);
    end_timer!(_t);
    let dv = diff(&v);
    let dv_over_domain = dv.evaluate_over_domain(domain);
    dv_over_domain.evals.into_iter()
        .zip(b)
        .filter_map(|(xi, bi)| bi.then_some(xi))
        .collect::<Vec<_>>()
}

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

    // c_j = w_j / (z - x_j) = 1 / [(1 / w_j) * (z - x_j)]
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

#[cfg(test)]
mod tests {
    use ark_poly::{DenseUVPolynomial, EvaluationDomain, GeneralEvaluationDomain, Polynomial};
    use ark_poly::univariate::DensePolynomial;
    use ark_std::{end_timer, start_timer, test_rng};
    use ark_std::rand::Rng;
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

    #[test]
    fn test_vanishing_poly() {
        let n = 2usize.pow(10);
        let domain = GeneralEvaluationDomain::<ark_bls12_381::Fr>::new(n).unwrap();
        let xs = domain.elements().collect::<Vec<_>>();

        let _t = start_timer!(|| "Product tree");
        let v = v_of(&xs);
        end_timer!(_t);

        assert_eq!(v, domain.vanishing_polynomial().into());
    }

    #[test]
    fn test_barycentric_weights() {
        let rng = &mut test_rng();

        let (log_n, t) = (9, 2.0 / 3.0);
        let n = 2usize.pow(log_n);
        let domain = GeneralEvaluationDomain::<ark_bls12_381::Fr>::new(n).unwrap();
        let bitmask = _random_bits(n, t, rng);

        let _t = start_timer!(|| format!("Inverted barycentric weights, log(n)={}, t~{}", log_n, t));
        let ws_inv1 = barycentric_weights_inv_in_domain(domain, &bitmask);
        end_timer!(_t);

        let xs = domain.elements()
            .zip(bitmask)
            .filter_map(|(xi, bi)| bi.then_some(xi))
            .collect::<Vec<_>>();

        let _t = start_timer!(|| format!("Naive inverted barycentric weights, log(n)={}, t~{}", log_n, t));
        let ws_inv2 = barycentric_weights_inv(&xs);
        end_timer!(_t);

        assert_eq!(ws_inv1, ws_inv2);
    }

    fn _bench_barycentric_weights<F: FftField>(log_n: u32) {
        let n = 2usize.pow(log_n);
        let domain = GeneralEvaluationDomain::<F>::new(n).unwrap();
        let bitmask = vec![true; n];
        let _t = start_timer!(|| format!("Inverted barycentric weights, log(n)={}", log_n));
        let _ws_inv = barycentric_weights_inv_in_domain(domain, &bitmask);
        end_timer!(_t);
    }

    #[test]
    fn bench_barycentric_weights() {
        _bench_barycentric_weights::<ark_bls12_381::Fr>(10);
        _bench_barycentric_weights::<ark_bls12_381::Fr>(16);
        _bench_barycentric_weights::<ark_bls12_381::Fr>(20);
    }

    fn _random_bits<R: Rng>(n: usize, density: f64, rng: &mut R) -> Vec<bool> {
        (0..n).map(|_| rng.gen_bool(density)).collect()
    }
}
