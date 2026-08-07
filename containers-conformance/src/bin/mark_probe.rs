//! Isolate the nested-mark gap: time mark-only, set-only, restore-only
//! separately at N=100k, depth 32, 64 writes/frame — prod vs verus.
use semi_persistent_containers as prod;
use semi_persistent_containers_verus as verus;

const N: usize = 100_000;
const DEPTH: usize = 32;
const W: usize = 64;
const REPS: u32 = 2000;

fn main() {
    // --- production ---
    let mut p: prod::VecP<u64, u32, true> = prod::VecP::new();
    for i in 0..N {
        p.push(i as u64);
    }
    let t = std::time::Instant::now();
    let mut ptoks = Vec::new();
    for _ in 0..REPS {
        ptoks.clear();
        let mut x = 0x9E3779B97F4A7C15u64;
        for _ in 0..DEPTH {
            ptoks.push(p.mark(prod::ShrinkPolicy::Never));
            for _ in 0..W {
                x ^= x << 13;
                x ^= x >> 7;
                x ^= x << 17;
                p.set((x % N as u64) as u32, x);
            }
        }
        p.restore(ptoks[0]);
    }
    println!("prod  full cycle: {:?}", t.elapsed() / REPS);

    // mark-only (no writes): every frame empty, restore trivial
    let t = std::time::Instant::now();
    for _ in 0..REPS {
        ptoks.clear();
        for _ in 0..DEPTH {
            ptoks.push(p.mark(prod::ShrinkPolicy::Never));
        }
        p.restore(ptoks[0]);
    }
    println!("prod  mark-only:  {:?}", t.elapsed() / REPS);

    // --- verus ---
    type V = verus::VecP<u64, u32, true>;
    let mut v: V = V::new();
    for i in 0..N {
        v.push(i as u64);
    }
    let t = std::time::Instant::now();
    let mut vtoks = Vec::new();
    for _ in 0..REPS {
        vtoks.clear();
        let mut x = 0x9E3779B97F4A7C15u64;
        for _ in 0..DEPTH {
            vtoks.push(v.mark(verus::ShrinkPolicy::Never));
            for _ in 0..W {
                x ^= x << 13;
                x ^= x >> 7;
                x ^= x << 17;
                v.set_index((x % N as u64) as u32, x);
            }
        }
        v.restore(vtoks[0]);
    }
    println!("verus full cycle: {:?}", t.elapsed() / REPS);

    let t = std::time::Instant::now();
    for _ in 0..REPS {
        vtoks.clear();
        for _ in 0..DEPTH {
            vtoks.push(v.mark(verus::ShrinkPolicy::Never));
        }
        v.restore(vtoks[0]);
    }
    println!("verus mark-only:  {:?}", t.elapsed() / REPS);

    // set-only under ONE deep frame: isolates tracked set cost.
    let mut x = 0x12345u64;
    let tp = {
        let mut xp = 0u64;
        let t = std::time::Instant::now();
        let tok = p.mark(prod::ShrinkPolicy::Never);
        for _ in 0..REPS {
            for _ in 0..(DEPTH * W) {
                x ^= x << 13;
                x ^= x >> 7;
                x ^= x << 17;
                p.set((x % N as u64) as u32, x);
                xp ^= x;
            }
        }
        p.restore(tok);
        std::hint::black_box(xp);
        t.elapsed() / REPS
    };
    println!("prod  set-only:   {tp:?}");
    let tv = {
        let mut xv = 0u64;
        let t = std::time::Instant::now();
        let tok = v.mark(verus::ShrinkPolicy::Never);
        for _ in 0..REPS {
            for _ in 0..(DEPTH * W) {
                x ^= x << 13;
                x ^= x >> 7;
                x ^= x << 17;
                v.set_index((x % N as u64) as u32, x);
                xv ^= x;
            }
        }
        v.restore(tok);
        std::hint::black_box(xv);
        t.elapsed() / REPS
    };
    println!("verus set-only:   {tv:?}");

    // restore-only: build depth stack with writes OUTSIDE the timer, restore
    // to frame 0 INSIDE it. iter via rebuild each rep.
    let t_build = |p: &mut prod::VecP<u64, u32, true>| {
        let mut x = 0x777u64;
        let mut toks = Vec::new();
        for _ in 0..DEPTH {
            toks.push(p.mark(prod::ShrinkPolicy::Never));
            for _ in 0..W {
                x ^= x << 13;
                x ^= x >> 7;
                x ^= x << 17;
                p.set((x % N as u64) as u32, x);
            }
        }
        toks
    };
    let mut tot = std::time::Duration::ZERO;
    for _ in 0..REPS {
        let toks = t_build(&mut p);
        let t = std::time::Instant::now();
        p.restore(toks[0]);
        tot += t.elapsed();
    }
    println!("prod  restore32:  {:?}", tot / REPS);

    let v_build = |v: &mut V| {
        let mut x = 0x777u64;
        let mut toks = Vec::new();
        for _ in 0..DEPTH {
            toks.push(v.mark(verus::ShrinkPolicy::Never));
            for _ in 0..W {
                x ^= x << 13;
                x ^= x >> 7;
                x ^= x << 17;
                v.set_index((x % N as u64) as u32, x);
            }
        }
        toks
    };
    let mut tot = std::time::Duration::ZERO;
    for _ in 0..REPS {
        let toks = v_build(&mut v);
        let t = std::time::Instant::now();
        v.restore(toks[0]);
        tot += t.elapsed();
    }
    println!("verus restore32:  {:?}", tot / REPS);
}

#[allow(dead_code)]
fn unused() {}
