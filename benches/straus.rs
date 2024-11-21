use ark_ec::CurveGroup;
use ark_ec::scalar_mul::glv::GLVConfig;
use ark_ec::short_weierstrass::Affine;
use ark_std::{test_rng, UniformRand};
use criterion::{BatchSize, BenchmarkId, Criterion, criterion_group, criterion_main};

use adkg_vrf::straus;

fn short_msm<C: CurveGroup>(c: &mut Criterion) {
    let rng = &mut test_rng();
    let n = 4; // msm size
    let m = 100; // pre-generated input size

    let full_scalars = (0..m).map(|_| C::ScalarField::rand(rng)).collect::<Vec<_>>();
    let small_scalars = (0..m).map(|_| C::ScalarField::from(u128::rand(rng))).collect::<Vec<_>>();
    let bases = (0..m).map(|_| C::rand(rng)).collect::<Vec<_>>();
    let bases = C::normalize_batch(&bases);

    let mut i = 0;
    c.bench_with_input(BenchmarkId::new("Straus full scalar MSM", n), &n, |b, n| b.iter_batched(
        || {
            i = (i + 1) % (m - n);
            (&bases[i..i + n], &full_scalars[i..i + n])
        },
        |(bases, scalars)| straus::short_msm(bases, scalars),
        BatchSize::SmallInput,
    ));

    let mut i = 0;
    c.bench_with_input(BenchmarkId::new("Straus 128-bit scalar MSM", n), &n, |b, n| b.iter_batched(
        || {
            i = (i + 1) % (m - n);
            (&bases[i..i + n], &small_scalars[i..i + n])
        },
        |(bases, scalars)| straus::short_msm(bases, scalars),
        BatchSize::SmallInput,
    ));
}

fn glv_vs_straus<C: GLVConfig>(c: &mut Criterion) {
    let rng = &mut test_rng();
    let mut bg = c.benchmark_group("small-multiexp-vs-msm");

    let m = 100; // pre-generated input size
    let full_scalars = (0..m).map(|_| C::ScalarField::rand(rng)).collect::<Vec<_>>();
    let bases = (0..m).map(|_| Affine::<C>::rand(rng)).collect::<Vec<_>>();

    for n in [2, 4] {
        let mut i = 0;
        bg.bench_with_input(BenchmarkId::new("Straus full scalar MSM", n), &n, |b, n| b.iter_batched(
            || {
                i = (i + 1) % (m - n);
                (&bases[i..i + n], &full_scalars[i..i + n])
            },
            |(bases, scalars)| straus::short_msm(bases, scalars),
            BatchSize::SmallInput,
        ));

        let mut i = 0;
        bg.bench_with_input(BenchmarkId::new("GLV-Straus MSM", n), &n, |b, n| b.iter_batched(
            || {
                i = (i + 1) % (m - n);
                (&bases[i..i + n], &full_scalars[i..i + n])
            },
            |(bases, scalars)| straus::short_msm_glv(bases, scalars),
            BatchSize::SmallInput,
        ));
    }
}

criterion_group!(benches,
    short_msm::<ark_bls12_381::G1Projective>,
    glv_vs_straus::<ark_bls12_381::g1::Config>,
);
criterion_main!(benches);