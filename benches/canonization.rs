use criterion::{black_box, criterion_group, criterion_main, Criterion};
use volute::{Lut4, Lut5, Lut6};

/// Benchmark N canonization.
fn bench_n_canonization(c: &mut Criterion) {
    let lut4 = Lut4::threshold(2);
    let lut5 = Lut5::threshold(2);
    let lut6 = Lut6::threshold(2);

    c.bench_function("n_canonization 4", |b| {
        b.iter(|| black_box(lut4).n_canonization())
    });
    c.bench_function("n_canonization 5", |b| {
        b.iter(|| black_box(lut5).n_canonization())
    });
    c.bench_function("n_canonization 6", |b| {
        b.iter(|| black_box(lut6).n_canonization())
    });
}

/// Benchmark P canonization.
fn bench_p_canonization(c: &mut Criterion) {
    let lut4 = Lut4::threshold(2);
    let lut5 = Lut5::threshold(2);
    let lut6 = Lut6::threshold(2);

    c.bench_function("p_canonization 4", |b| {
        b.iter(|| black_box(lut4).p_canonization())
    });
    c.bench_function("p_canonization 5", |b| {
        b.iter(|| black_box(lut5).p_canonization())
    });
    c.bench_function("p_canonization 6", |b| {
        b.iter(|| black_box(lut6).p_canonization())
    });
}

/// Benchmark NPN canonization.
fn bench_npn_canonization(c: &mut Criterion) {
    let lut4 = Lut4::threshold(2);
    let lut5 = Lut5::threshold(2);
    let lut6 = Lut6::threshold(2);

    c.bench_function("npn_canonization 4", |b| {
        b.iter(|| black_box(lut4).npn_canonization())
    });
    c.bench_function("npn_canonization 5", |b| {
        b.iter(|| black_box(lut5).npn_canonization())
    });
    c.bench_function("npn_canonization 6", |b| {
        b.iter(|| black_box(lut6).npn_canonization())
    });
}

criterion_group!(
    benches,
    bench_n_canonization,
    bench_p_canonization,
    bench_npn_canonization
);

criterion_main!(benches);
