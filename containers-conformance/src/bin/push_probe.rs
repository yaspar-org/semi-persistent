//! Pinpoint probe: verus untracked push in isolation (release build).
use semi_persistent_containers_verus as verus;
type V = verus::vec::Vec<u64, u32, verus::parallel_store::ParallelStore<u64, u32>, false>;

fn main() {
    let mut total = std::time::Duration::ZERO;
    let mut n = 0usize;
    for _ in 0..500 {
        let t = std::time::Instant::now();
        let mut v: V = V::new();
        for i in 0..100_000u64 {
            v.try_push(i).expect("push: within index word");
        }
        total += t.elapsed();
        n += v.len() as usize;
    }
    println!("push total {total:?} n {n}");
}
