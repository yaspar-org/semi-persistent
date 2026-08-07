//! Attribute (and now confirm the fix for) the map/intern gap:
//!   1. std HashMap with its default `RandomState` (SipHash) — the OLD SpMap
//!   2. hashbrown (foldhash) — what production's `Map` uses
//!   3. std HashMap with `foldhash::fast::RandomState` — what SpMap uses NOW
//!
//! (3) is the verified container (2)'s hasher: it should match (2), not (1),
//! showing the gap was purely the hasher and is now closed.
fn main() {
    const N: u64 = 500_000;
    let t = std::time::Instant::now();
    let mut m1: std::collections::HashMap<u64, usize> = std::collections::HashMap::new();
    for i in 0..N {
        m1.insert(i.wrapping_mul(0x9E3779B97F4A7C15), i as usize);
    }
    let mut hits = 0u64;
    for i in 0..N {
        if m1.contains_key(&i.wrapping_mul(0x9E3779B97F4A7C15)) {
            hits += 1;
        }
    }
    println!("std default (SipHash):     {:?} (hits {hits})", t.elapsed());

    let t = std::time::Instant::now();
    let mut m2: hashbrown::HashMap<u64, usize> = hashbrown::HashMap::new();
    for i in 0..N {
        m2.insert(i.wrapping_mul(0x9E3779B97F4A7C15), i as usize);
    }
    let mut hits2 = 0u64;
    for i in 0..N {
        if m2.contains_key(&i.wrapping_mul(0x9E3779B97F4A7C15)) {
            hits2 += 1;
        }
    }
    println!(
        "prod: hashbrown (foldhash): {:?} (hits {hits2})",
        t.elapsed()
    );

    // Exactly SpMap's index type: std HashMap parameterized by foldhash's
    // BuildHasher (production's default). vstd models this container.
    let t = std::time::Instant::now();
    let mut m3: std::collections::HashMap<u64, usize, foldhash::fast::RandomState> =
        std::collections::HashMap::default();
    for i in 0..N {
        m3.insert(i.wrapping_mul(0x9E3779B97F4A7C15), i as usize);
    }
    let mut hits3 = 0u64;
    for i in 0..N {
        if m3.contains_key(&i.wrapping_mul(0x9E3779B97F4A7C15)) {
            hits3 += 1;
        }
    }
    println!(
        "verus: std<foldhash> (NEW): {:?} (hits {hits3})",
        t.elapsed()
    );
}
