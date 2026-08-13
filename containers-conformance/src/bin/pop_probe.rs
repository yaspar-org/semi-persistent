//! Pinpoint probe: verus untracked pop in isolation (release build) — for
//! disassembly-level attribution of the untracked-gap residue.
use semi_persistent_containers_verus as verus;
type V = verus::vec::Vec<u64, u32, verus::parallel_store::ParallelStore<u64, u32>, false>;

fn main() {
    let mut total = std::time::Duration::ZERO;
    let mut acc = 0u64;
    for _ in 0..500 {
        let mut v: V = V::new();
        for i in 0..100_000u64 {
            v.try_push(i).expect("push: within index word");
        }
        let t = std::time::Instant::now();
        while let Some(x) = v.pop() {
            acc = acc.wrapping_add(x);
        }
        total += t.elapsed();
    }
    println!("pop total {total:?} acc {acc}");
}
