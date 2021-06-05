use criterion::{black_box, criterion_group, criterion_main, BenchmarkId, Criterion};
use hamilton as math;
use math::Vec4;
use rand::prelude::*;

//fn fibonacci(n: u64) -> u64 {
//    match n {
//        0 => 1,
//        1 => 1,
//        n => fibonacci(n - 1) + fibonacci(n - 2),
//    }
//}
//
//fn criterion_benchmark(c: &mut Criterion) { c.bench_function("fib 20", |b| b.iter(|| fibonacci(black_box(20)))); }

fn vec4_addition(c: &mut Criterion) {
    let mut rng = rand::thread_rng();
    let lhs = Vec4::new(
        rng.gen_range(-100..100) as f32,
        rng.gen_range(-100..100) as f32,
        rng.gen_range(-100..100) as f32,
        rng.gen_range(-100..100) as f32,
    );
    let rhs = lhs;

    c.bench_with_input(BenchmarkId::new("addition", lhs), &lhs, |b, i| {
        b.iter(|| {
            let mut lhs = *i;
            for _ in 0..10000 {
                lhs = lhs + rhs
            }
        })
    });
}

criterion_group!(benches, vec4_addition);
criterion_main!(benches);
