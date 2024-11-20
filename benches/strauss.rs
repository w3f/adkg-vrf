use ark_ec::CurveGroup;
use ark_std::{test_rng, UniformRand};
use criterion::{Criterion, criterion_group, criterion_main};

use adkg_vrf::strauss;

fn short_msm<C: CurveGroup>(c: &mut Criterion) {
    let rng = &mut test_rng();
    let n = 4;

    let scalars = (0..n)
        .map(|_| C::ScalarField::rand(rng))
        .collect::<Vec<_>>();
    let bases = (0..n)
        .map(|_| C::rand(rng))
        .collect::<Vec<_>>();
    let bases = C::normalize_batch(&bases);

    c.bench_function("Strauss 4-msm", |b| b.iter(|| strauss::short_msm(&bases, &scalars)));
    c.bench_function("Precomputation", |b| b.iter(|| strauss::table(&bases)));
}

criterion_group!(benches, short_msm::<ark_bls12_381::G1Projective>);
criterion_main!(benches);