use std::hint::black_box;

use criterion::{criterion_group, criterion_main, BenchmarkId, Criterion};
use volute::{Lut, Lut4, Lut5, Lut6};

/// Benchmark N canonization.
fn bench_n_canonization(c: &mut Criterion) {
    let mut group = c.benchmark_group("N Canonization");
    let lut4 = Lut4::threshold(2);
    let lut5 = Lut5::threshold(2);
    let lut6 = Lut6::threshold(2);

    group.bench_function(BenchmarkId::new("Static", 4), |b| {
        b.iter(|| black_box(lut4).n_canonization())
    });
    group.bench_function(BenchmarkId::new("Dynamic", 4), |b| {
        b.iter(|| black_box(Lut::from(lut4)).n_canonization())
    });
    group.bench_function(BenchmarkId::new("Static", 5), |b| {
        b.iter(|| black_box(lut5).n_canonization())
    });
    group.bench_function(BenchmarkId::new("Dynamic", 5), |b| {
        b.iter(|| black_box(Lut::from(lut5)).n_canonization())
    });
    group.bench_function(BenchmarkId::new("Static", 6), |b| {
        b.iter(|| black_box(lut6).n_canonization())
    });
    group.bench_function(BenchmarkId::new("Dynamic", 6), |b| {
        b.iter(|| black_box(Lut::from(lut6)).n_canonization())
    });
}

/// Benchmark P canonization.
fn bench_p_canonization(c: &mut Criterion) {
    let mut group = c.benchmark_group("P Canonization");
    let lut4 = Lut4::threshold(2);
    let lut5 = Lut5::threshold(2);
    let lut6 = Lut6::threshold(2);

    group.bench_function(BenchmarkId::new("Static", 4), |b| {
        b.iter(|| black_box(lut4).p_canonization())
    });
    group.bench_function(BenchmarkId::new("Dynamic", 4), |b| {
        b.iter(|| black_box(Lut::from(lut4)).p_canonization())
    });
    group.bench_function(BenchmarkId::new("Static", 5), |b| {
        b.iter(|| black_box(lut5).p_canonization())
    });
    group.bench_function(BenchmarkId::new("Dynamic", 5), |b| {
        b.iter(|| black_box(Lut::from(lut5)).p_canonization())
    });
    group.bench_function(BenchmarkId::new("Static", 6), |b| {
        b.iter(|| black_box(lut6).p_canonization())
    });
    group.bench_function(BenchmarkId::new("Dynamic", 6), |b| {
        b.iter(|| black_box(Lut::from(lut6)).p_canonization())
    });
}

/// Benchmark NPN canonization.
fn bench_npn_canonization(c: &mut Criterion) {
    let mut group = c.benchmark_group("NPN Canonization");
    let lut4 = Lut4::threshold(2);
    let lut5 = Lut5::threshold(2);
    let lut6 = Lut6::threshold(2);

    group.bench_function(BenchmarkId::new("Static", 4), |b| {
        b.iter(|| black_box(lut4).npn_canonization())
    });
    group.bench_function(BenchmarkId::new("Dynamic", 4), |b| {
        b.iter(|| black_box(Lut::from(lut4)).npn_canonization())
    });
    group.bench_function(BenchmarkId::new("Static", 5), |b| {
        b.iter(|| black_box(lut5).npn_canonization())
    });
    group.bench_function(BenchmarkId::new("Dynamic", 5), |b| {
        b.iter(|| black_box(Lut::from(lut5)).npn_canonization())
    });
    group.bench_function(BenchmarkId::new("Static", 6), |b| {
        b.iter(|| black_box(lut6).npn_canonization())
    });
    group.bench_function(BenchmarkId::new("Dynamic", 6), |b| {
        b.iter(|| black_box(Lut::from(lut6)).npn_canonization())
    });
}

criterion_group!(
    benches,
    bench_n_canonization,
    bench_p_canonization,
    bench_npn_canonization
);

criterion_main!(benches);
