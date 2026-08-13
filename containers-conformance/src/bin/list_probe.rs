//! Decompose list/append_iter: append-only vs iterate-only, prod vs verus.
use semi_persistent_containers as prod;
use semi_persistent_containers_verus as verus;

prod::define_id31! { pub struct PE / SPE, "e"; }
prod::define_id31! { pub struct PL / SPL, "l"; }
prod::define_id31! { pub struct PN / SPN, "n"; }
verus::define_id31! { pub struct VE / SVE, "e"; }
verus::define_id31! { pub struct VL / SVL, "l"; }
verus::define_id31! { pub struct VN / SVN, "n"; }

const LISTS: usize = 2_000;
const PER: usize = 30;
const REPS: usize = 300;

fn main() {
    // prod build
    let t = std::time::Instant::now();
    let mut pa_final = None;
    for _ in 0..REPS {
        let mut a: prod::ListArena<PE, PL, PN, false> = prod::ListArena::new();
        let ls: Vec<PL> = (0..LISTS).map(|_| a.new_list()).collect();
        for (k, &l) in ls.iter().enumerate() {
            for j in 0..PER {
                a.append(l, PE::new((k * PER + j) as u32 & 0x7FFF_FFFF));
            }
        }
        pa_final = Some((a, ls));
    }
    println!("prod  append: {:?}", t.elapsed() / REPS as u32);
    let (pa, pls) = pa_final.unwrap();
    let t = std::time::Instant::now();
    let mut acc = 0u64;
    for _ in 0..REPS {
        for &l in &pls {
            for e in pa.iter(l) {
                acc = acc.wrapping_add(e.raw() as u64);
            }
        }
    }
    println!("prod  iter:   {:?} (acc {acc})", t.elapsed() / REPS as u32);

    // verus build
    let t = std::time::Instant::now();
    let mut va_final = None;
    for _ in 0..REPS {
        let mut a: verus::ListArena<VE, VL, VN, false> = verus::ListArena::new();
        let ls: Vec<VL> = (0..LISTS)
            .map(|_| a.try_new_list().expect("within id space"))
            .collect();
        for (k, &l) in ls.iter().enumerate() {
            for j in 0..PER {
                a.try_append(l, VE::new((k * PER + j) as u32 & 0x7FFF_FFFF))
                    .expect("within id space");
            }
        }
        va_final = Some((a, ls));
    }
    println!("verus append: {:?}", t.elapsed() / REPS as u32);
    let (va, vls) = va_final.unwrap();
    let t = std::time::Instant::now();
    let mut acc2 = 0u64;
    for _ in 0..REPS {
        for &l in &vls {
            for e in va.iter(l) {
                acc2 = acc2.wrapping_add(e.raw() as u64);
            }
        }
    }
    println!("verus iter:   {:?} (acc {acc2})", t.elapsed() / REPS as u32);
    assert_eq!(acc, acc2);
}

#[cfg(test)]
mod sizes {}
