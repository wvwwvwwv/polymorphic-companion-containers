use criterion::{Criterion, criterion_group, criterion_main};
use pcc::CompanionStack;
use std::time::Instant;

fn dynamic_stack(c: &mut Criterion) {
    fn recursive<const SIZE: usize>(
        depth: usize,
        max: usize,
        stack: &mut CompanionStack<SIZE>,
    ) -> usize {
        if depth == 0 {
            return max;
        }
        let mut usize_val = stack.push_one(|| Ok::<_, ()>(depth)).unwrap();
        let (usize_val, stack) = usize_val.get_stack();
        assert_ne!(*usize_val, 0);
        *usize_val -= 1;
        let new_max = recursive::<SIZE>(*usize_val, max.max(*usize_val), stack);
        new_max.max(&*usize_val as *const _ as usize)
    }
    c.bench_function("CompanionStack: recursive calls", |b| {
        b.iter_custom(|iters| {
            let depth = 256;
            let mut dynamic_stack: CompanionStack = CompanionStack::default();
            let start = Instant::now();
            for _ in 0..iters {
                assert!(recursive(depth, 0, &mut dynamic_stack) > &depth as *const _ as usize);
            }
            start.elapsed()
        })
    });
}

fn static_stack(c: &mut Criterion) {
    fn recursive(depth: usize, max: usize) -> usize {
        if depth == 0 {
            return max;
        }
        let mut usize_val = depth;
        assert_ne!(usize_val, 0);
        usize_val -= 1;
        let new_max = recursive(usize_val, max.max(usize_val));
        new_max.max(&usize_val as *const _ as usize)
    }

    c.bench_function("StaticStack: recursive calls", |b| {
        b.iter_custom(|iters| {
            let depth = 256;
            let start = Instant::now();
            for _ in 0..iters {
                assert!(recursive(depth, 0) > &depth as *const _ as usize);
            }
            start.elapsed()
        })
    });
}

criterion_group!(companion_stack, dynamic_stack, static_stack);
criterion_main!(companion_stack);
