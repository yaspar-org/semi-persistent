// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0
//! Step 1 of `doc/goal-sequence-patterns.md`: the reference matcher (`seq_ref`)
//! gives the counts and the matches `doc/sequence-patterns.md` states.
//!
//! Children are written as letters: a child `"1q"` is a class with a member `P1()`
//! and a member `Q()`, so it matches the patterns `(P1)` and `(Q)`, each through one
//! member; `"x"` is a class with only `X()`, which no pattern here matches.

mod seq_ref;

use seq_ref::{Env, Graph, Item, Kind, Mult, Pat, Val, match_children, match_node, mult_column};

fn binom(n: u64, k: u64) -> u64 {
    if k > n {
        return 0;
    }
    (0..k).fold(1, |acc, i| acc * (n - i) / (i + 1))
}

/// A graph with one class per child spec, and `Op` of the given kind over them.
fn children(kind: Kind, specs: &[&str]) -> (Graph, Vec<usize>) {
    let mut g = Graph::default();
    g.kinds.insert("Op".into(), kind);
    let kids = specs
        .iter()
        .map(|s| {
            let ms = s
                .chars()
                .map(|c| {
                    let op = match c {
                        '1' => "P1",
                        '2' => "P2",
                        'q' => "Q",
                        'r' => "R",
                        'x' => "X",
                        other => panic!("child letter {other}"),
                    };
                    Graph::node(op, &[])
                })
                .collect();
            g.class(ms)
        })
        .collect();
    (g, kids)
}

fn leaf(op: &str) -> Pat {
    Pat::App(op.into(), vec![])
}
fn one(op: &str) -> Item {
    Item::one(leaf(op))
}
fn run(name: &str, op: &str) -> Item {
    Item::filter(name, leaf(op))
}
fn bare(name: &str) -> Item {
    Item::Bare(name.into())
}
fn count(kind: Kind, specs: &[&str], items: &[Item]) -> usize {
    let (g, kids) = children(kind, specs);
    match_node(&g, "Op", items, &kids, &Env::new()).len()
}

/// The sizes of each sequence binding, in item order, for every match.
fn shapes(kind: Kind, specs: &[&str], items: &[Item]) -> Vec<Vec<usize>> {
    let (g, kids) = children(kind, specs);
    let mut out: Vec<Vec<usize>> = match_node(&g, "Op", items, &kids, &Env::new())
        .iter()
        .map(|e| {
            items
                .iter()
                .filter_map(|i| match i {
                    Item::Bare(n) | Item::Filter { name: n, .. } => match &e[n] {
                        Val::Seq(v) => Some(v.len()),
                        Val::Class(_) | Val::Int(_) => None,
                    },
                    Item::One(..) => Some(1),
                })
                .collect()
        })
        .collect();
    out.sort();
    out
}

// ── A ──────────────────────────────────────────────────────────────────────────

/// k runs over n children, all matching, no gap: the cuts of n into k possibly
/// empty runs, C(n+k−1, k−1) ("§Semantics: a run: zero or more consecutive children").
#[test]
fn a_k_runs_are_the_weak_compositions() {
    for n in 0..=10usize {
        for k in 1..=4usize {
            let items: Vec<Item> = (0..k).map(|i| run(&format!("g{i}"), "P1")).collect();
            let specs = vec!["1"; n];
            assert_eq!(
                count(Kind::Assoc, &specs, &items) as u64,
                binom((n + k - 1) as u64, k as u64 - 1),
                "n={n} k={k}"
            );
        }
    }
}

/// A child matching nothing between two runs, and no gap: no window spans it.
#[test]
fn a_a_non_matching_child_between_runs_blocks_the_match() {
    assert_eq!(
        count(
            Kind::Assoc,
            &["1", "x", "2"],
            &[run("a", "P1"), run("b", "P2")]
        ),
        0
    );
    // With gaps around, the child matching nothing falls in a gap, and runs may be
    // empty: four parses (derived independently of this matcher, from the design text).
    assert_eq!(
        shapes(
            Kind::Assoc,
            &["1", "x", "2"],
            &[bare("p"), run("a", "P1"), run("b", "P2"), bare("s")]
        ),
        vec![
            vec![0, 0, 0, 3],
            vec![0, 1, 0, 2],
            vec![2, 0, 1, 0],
            vec![3, 0, 0, 0]
        ]
    );
}

/// `(op ..a ..b ..c ..d)`: every split into four possibly empty parts, C(n+3, 3).
#[test]
fn a_four_gaps_are_every_split() {
    for n in 0..=8usize {
        let specs = vec!["x"; n];
        let items = [bare("a"), bare("b"), bare("c"), bare("d")];
        assert_eq!(
            count(Kind::Assoc, &specs, &items) as u64,
            binom(n as u64 + 3, 3),
            "n={n}"
        );
    }
}

/// `..pre run one run one ..suf` over n children matching every item: the gap before
/// the first run is empty (every child matches the run), the runs may be empty, so
/// C(n, 2) parses.
#[test]
fn a_run_one_run_one_counts() {
    let items = [
        bare("pre"),
        run("g1", "P1"),
        one("Q"),
        run("g2", "P2"),
        one("R"),
        bare("suf"),
    ];
    for (n, want) in [(4, 6), (6, 15), (8, 28), (10, 45), (12, 66), (16, 120)] {
        let specs = vec!["12qr"; n];
        assert_eq!(count(Kind::Assoc, &specs, &items), want, "n={n}");
    }
}

/// The two-run examples, `..pre (..gs1 P1) (..gs2 P2) ..suf`.
#[test]
fn a_two_run_examples() {
    let items = [bare("pre"), run("g1", "P1"), run("g2", "P2"), bare("suf")];
    // pre, gs1, gs2, suf sizes; derived independently of this matcher.
    assert_eq!(
        shapes(Kind::Assoc, &["1", "12", "12", "2"], &items),
        vec![
            vec![0, 0, 0, 4],
            vec![0, 1, 3, 0],
            vec![0, 2, 2, 0],
            vec![0, 3, 1, 0],
            vec![4, 0, 0, 0]
        ]
    );
    assert_eq!(
        shapes(Kind::Assoc, &["1", "x", "2"], &items),
        vec![
            vec![0, 0, 0, 3],
            vec![0, 1, 0, 2],
            vec![2, 0, 1, 0],
            vec![3, 0, 0, 0]
        ]
    );
    assert_eq!(
        shapes(Kind::Assoc, &["1", "12", "2", "12", "1"], &items),
        vec![
            vec![0, 0, 0, 5],
            vec![0, 1, 3, 1],
            vec![0, 2, 2, 1],
            vec![3, 0, 1, 1],
            vec![3, 1, 0, 1],
            vec![3, 2, 0, 0]
        ]
    );
    assert_eq!(
        shapes(Kind::Assoc, &["12", "12", "12", "12"], &items),
        vec![
            vec![0, 0, 4, 0],
            vec![0, 1, 3, 0],
            vec![0, 2, 2, 0],
            vec![0, 3, 1, 0],
            vec![0, 4, 0, 0]
        ]
    );
    assert_eq!(
        shapes(Kind::Assoc, &["2", "1"], &items),
        vec![vec![0, 0, 1, 1], vec![1, 0, 0, 1], vec![1, 1, 0, 0]]
    );
    // Without the gaps the runs cover the whole sequence: every cut, empty runs included.
    assert_eq!(
        count(
            Kind::Assoc,
            &["12", "12", "12", "12"],
            &[run("g1", "P1"), run("g2", "P2")]
        ),
        5
    );
}

/// The mixed examples, `..pre (..gs1 P1) Q (..gs2 P2) R ..suf`.
#[test]
fn a_mixed_examples() {
    let items = [
        bare("pre"),
        run("g1", "P1"),
        one("Q"),
        run("g2", "P2"),
        one("R"),
        bare("suf"),
    ];
    assert_eq!(
        shapes(Kind::Assoc, &["1", "1", "q", "2", "2", "r", "x"], &items),
        vec![vec![0, 2, 1, 2, 1, 1]]
    );
    assert_eq!(
        shapes(Kind::Assoc, &["1", "1q", "1q", "2", "r"], &items),
        vec![vec![0, 2, 1, 1, 1, 0]]
    );
    assert_eq!(count(Kind::Assoc, &["1", "2", "r"], &items), 0);
    assert_eq!(
        shapes(
            Kind::Assoc,
            &["1", "q", "2", "r", "1", "q", "2", "r"],
            &items
        ),
        vec![vec![0, 1, 1, 1, 1, 4], vec![4, 1, 1, 1, 1, 0]]
    );
}

/// A run beside a gap does not extend into it; an empty gap constrains nothing.
#[test]
fn a_maximality_at_gaps() {
    // `1 1 x`: the run must take both 1s, so the gap is `x` alone.
    assert_eq!(
        shapes(Kind::Assoc, &["1", "1", "x"], &[run("g", "P1"), bare("s")]),
        vec![vec![2, 1]]
    );
    // `x 1 1`: the gap before the run can't end with a 1.
    assert_eq!(
        shapes(Kind::Assoc, &["x", "1", "1"], &[bare("p"), run("g", "P1")]),
        vec![vec![1, 2]]
    );
    // Two runs of the same pattern with the gap between them empty: every cut of 1 1 1.
    assert_eq!(
        count(
            Kind::Assoc,
            &["1", "1", "1"],
            &[run("a", "P1"), bare("m"), run("b", "P1")]
        ),
        4
    );
    // A node with no child matching the run: the splits of the gaps alone, `gs = []`
    // ("§Semantics, Under A: ... matches as `(Cat ..pre ..suf)` does, at every split").
    assert_eq!(
        shapes(
            Kind::Assoc,
            &["x", "x", "x"],
            &[bare("p"), run("g", "P1"), bare("s")]
        ),
        vec![vec![0, 0, 3], vec![1, 0, 2], vec![2, 0, 1], vec![3, 0, 0]]
    );
}

// ── ACI ────────────────────────────────────────────────────────────────────────

/// m children matching two filters: 2^m assignments.
#[test]
fn aci_overlap_is_every_assignment() {
    for m in 0..=8usize {
        let specs = vec!["12"; m];
        assert_eq!(
            count(Kind::Aci, &specs, &[run("a", "P1"), run("b", "P2")]),
            1 << m,
            "m={m}"
        );
    }
}

/// k simple items over n children: n!/(n−k)! assignments, the rest to the bare sequence.
#[test]
fn aci_simple_items_are_every_injection() {
    for n in 0..=6u64 {
        for k in 0..=3u64 {
            let mut items: Vec<Item> = (0..k)
                .map(|i| Item::one(Pat::Var(format!("x{i}"))))
                .collect();
            items.push(bare("rest"));
            let specs = vec!["x"; n as usize];
            let want = if k > n {
                0
            } else {
                (n - k + 1..=n).product::<u64>()
            };
            assert_eq!(count(Kind::Aci, &specs, &items) as u64, want, "n={n} k={k}");
        }
    }
}

/// `:except` removes the other filter's children: one assignment.
#[test]
fn aci_except_gives_one_assignment() {
    let items = [
        run("a", "P1"),
        Item::Filter {
            name: "b".into(),
            base: leaf("P2"),
            except: Some("a".into()),
            mult: None,
        },
    ];
    for m in 0..=6usize {
        assert_eq!(
            shapes(Kind::Aci, &vec!["12"; m], &items),
            vec![vec![m, 0]],
            "m={m}"
        );
    }
    // A child matching only P2 still goes to `b`.
    assert_eq!(shapes(Kind::Aci, &["12", "2"], &items), vec![vec![1, 1]]);
}

/// A child matching no filter goes to the bare sequence; without one, no match.
#[test]
fn aci_unmatched_children_need_a_bare_sequence() {
    assert_eq!(
        shapes(Kind::Aci, &["1", "x"], &[run("a", "P1"), bare("r")]),
        vec![vec![1, 1]]
    );
    assert_eq!(count(Kind::Aci, &["1", "x"], &[run("a", "P1")]), 0);
    // A filter may be empty.
    assert_eq!(
        shapes(Kind::Aci, &["x"], &[run("a", "P1"), bare("r")]),
        vec![vec![0, 1]]
    );
}

/// Simple items take their children before the filters see the rest.
#[test]
fn aci_simple_items_come_first() {
    // `(Op (P1) (..a (P1)) ..r)` over three 1s: the simple item takes any one of them.
    assert_eq!(
        shapes(
            Kind::Aci,
            &["1", "1", "1"],
            &[one("P1"), run("a", "P1"), bare("r")]
        ),
        vec![vec![1, 2, 0]; 3]
    );
}

// ── Member choice and globals ────────────────────────────────────────────────

/// A class with two members matching a filter's pattern doubles the count, under A
/// and under ACI, with the members' bindings distinct.
#[test]
fn member_choice_doubles_the_count() {
    for kind in [Kind::Assoc, Kind::Aci] {
        let mut g = Graph::default();
        g.kinds.insert("Op".into(), kind);
        let (a, b) = (
            g.class(vec![Graph::node("A", &[])]),
            g.class(vec![Graph::node("B", &[])]),
        );
        let c = g.class(vec![Graph::node("Wrap", &[a]), Graph::node("Wrap", &[b])]);
        let d = g.class(vec![Graph::node("Wrap", &[a])]);
        let items = [Item::filter(
            "gs",
            Pat::App("Wrap".into(), vec![Item::one(Pat::Var("x".into()))]),
        )];
        let ms = match_node(&g, "Op", &items, &[c, d], &Env::new());
        assert_eq!(ms.len(), 2, "{kind:?}");
        let xs: Vec<&Val> = ms.iter().map(|e| &e["x"]).collect();
        assert_ne!(xs[0], xs[1], "{kind:?}");
    }
}

/// A global name inside a filter is the global, not a fresh variable.
#[test]
fn a_global_inside_a_filter_is_the_global() {
    let mut g = Graph::default();
    g.kinds.insert("Op".into(), Kind::Aci);
    let (a, b) = (
        g.class(vec![Graph::node("A", &[])]),
        g.class(vec![Graph::node("B", &[])]),
    );
    g.globals.insert("a".into(), a);
    let wa = g.class(vec![Graph::node("Wrap", &[a])]);
    let wb = g.class(vec![Graph::node("Wrap", &[b])]);
    let items = [
        Item::filter(
            "gs",
            Pat::App("Wrap".into(), vec![Item::one(Pat::Var("a".into()))]),
        ),
        bare("rest"),
    ];
    let ms = match_node(&g, "Op", &items, &[wa, wb], &Env::new());
    assert_eq!(ms.len(), 1);
    assert_eq!(ms[0]["gs"], Val::Seq(vec![Val::Class(wa)]));
    assert_eq!(ms[0]["rest"], Val::Seq(vec![Val::Class(wb)]));
    assert!(
        !ms[0].contains_key("a"),
        "a global is not bound as a variable"
    );
}

/// Variables under a filter are sequences, one entry per child, in child order.
#[test]
fn filter_variables_are_sequences_in_child_order() {
    let mut g = Graph::default();
    g.kinds.insert("And".into(), Kind::Aci);
    let (l0, u0, l1, u1) = (
        g.class(vec![Graph::lit("0")]),
        g.class(vec![Graph::lit("5")]),
        g.class(vec![Graph::lit("2")]),
        g.class(vec![Graph::lit("9")]),
    );
    let p = g.class(vec![Graph::node("Var", &[])]);
    let i0 = g.class(vec![Graph::node("Interval", &[l0, u0])]);
    let i1 = g.class(vec![Graph::node("Interval", &[l1, u1])]);
    let g0 = g.class(vec![Graph::node("Global", &[i0, p])]);
    let g1 = g.class(vec![Graph::node("Global", &[i1, p])]);
    let base = Pat::App(
        "Global".into(),
        vec![
            Item::one(Pat::App(
                "Interval".into(),
                vec![
                    Item::one(Pat::Var("l".into())),
                    Item::one(Pat::Var("u".into())),
                ],
            )),
            Item::one(Pat::Var("p".into())),
        ],
    );
    let ms = match_node(
        &g,
        "And",
        &[Item::filter("gs", base), bare("rest")],
        &[g0, g1],
        &Env::new(),
    );
    assert_eq!(ms.len(), 1);
    assert_eq!(ms[0]["l"], Val::Seq(vec![Val::Class(l0), Val::Class(l1)]));
    assert_eq!(ms[0]["u"], Val::Seq(vec![Val::Class(u0), Val::Class(u1)]));
    assert_eq!(ms[0]["p"], Val::Seq(vec![Val::Class(p), Val::Class(p)]));
    assert_eq!(ms[0]["rest"], Val::Seq(vec![]));
}

// ── AC ─────────────────────────────────────────────────────────────────────────

/// An AC graph: `Op` over `(class spec, multiplicity)` children.
fn ac(specs: &[(&str, u64)]) -> (Graph, Vec<(usize, u64)>) {
    let letters: Vec<&str> = specs.iter().map(|s| s.0).collect();
    let (mut g, kids) = children(Kind::Ac, &letters);
    g.kinds.insert("Op".into(), Kind::Ac);
    (g, kids.into_iter().zip(specs.iter().map(|s| s.1)).collect())
}

/// An unannotated AC filter takes only children of multiplicity exactly 1, as every
/// unannotated item under AC does (decision of 2026-09-30, which replaced "every
/// multiplicity" of 2026-09-29); the others go to the rest with their multiplicities.
/// `(..g:k P)` takes every matching child, and binds the multiplicities as `k`.
#[test]
fn ac_filter_default_is_multiplicity_one() {
    let (g, kids) = ac(&[("1", 2), ("1", 1), ("x", 3)]);
    let ms = match_children(&g, "Op", &[run("g", "P1"), bare("r")], &kids, &Env::new());
    assert_eq!(ms.len(), 1);
    let m = &ms[0];
    assert_eq!(m["g"], Val::Seq(vec![Val::Class(kids[1].0)]));
    assert_eq!(m[&mult_column("g")], Val::Seq(vec![Val::Int(1)]));
    assert_eq!(
        m["r"],
        Val::Seq(vec![Val::Class(kids[0].0), Val::Class(kids[2].0)])
    );
    assert_eq!(
        m[&mult_column("r")],
        Val::Seq(vec![Val::Int(2), Val::Int(3)])
    );
    let f = Item::Filter {
        name: "g".into(),
        base: leaf("P1"),
        except: None,
        mult: Some(Mult::var("k")),
    };
    let ms = match_children(&g, "Op", &[f, bare("r")], &kids, &Env::new());
    assert_eq!(ms.len(), 1);
    assert_eq!(
        ms[0]["g"],
        Val::Seq(vec![Val::Class(kids[0].0), Val::Class(kids[1].0)])
    );
    assert_eq!(ms[0]["k"], Val::Seq(vec![Val::Int(2), Val::Int(1)]));
    assert_eq!(ms[0]["r"], Val::Seq(vec![Val::Class(kids[2].0)]));
}

/// `(..g:k>=2 P)` takes only the children whose multiplicity the annotation accepts,
/// binds `k` as a column; the others go to the rest.
#[test]
fn ac_filter_multiplicity_annotation() {
    let (g, kids) = ac(&[("1", 2), ("1", 1), ("1", 3)]);
    let f = Item::Filter {
        name: "g".into(),
        base: leaf("P1"),
        except: None,
        mult: Some(Mult::at_least("k", 2)),
    };
    let ms = match_children(&g, "Op", &[f, bare("r")], &kids, &Env::new());
    assert_eq!(ms.len(), 1);
    assert_eq!(
        ms[0]["g"],
        Val::Seq(vec![Val::Class(kids[0].0), Val::Class(kids[2].0)])
    );
    assert_eq!(ms[0]["k"], Val::Seq(vec![Val::Int(2), Val::Int(3)]));
    assert_eq!(ms[0]["r"], Val::Seq(vec![Val::Class(kids[1].0)]));
    // Without a rest the child of multiplicity 1 has nowhere to go: no match.
    let f = Item::Filter {
        name: "g".into(),
        base: leaf("P1"),
        except: None,
        mult: Some(Mult::at_least("k", 2)),
    };
    assert_eq!(match_children(&g, "Op", &[f], &kids, &Env::new()).len(), 0);
}

/// An unannotated simple item under AC takes a child of multiplicity exactly 1; an
/// annotated one any child its annotation accepts, binding the multiplicity (Semper
/// design §7.5, maximum partition).
#[test]
fn ac_simple_items_follow_maximum_partition() {
    let (g, kids) = ac(&[("1", 2), ("1", 1)]);
    assert_eq!(
        match_children(&g, "Op", &[one("P1"), bare("r")], &kids, &Env::new()).len(),
        1
    );
    let item = Item::One(leaf("P1"), Some(Mult::var("k")));
    let ms = match_children(&g, "Op", &[item, bare("r")], &kids, &Env::new());
    let mut ks: Vec<Val> = ms.iter().map(|m| m["k"].clone()).collect();
    ks.sort();
    assert_eq!(ks, vec![Val::Int(1), Val::Int(2)]);
    // `:3` accepts neither child.
    let item = Item::One(leaf("P1"), Some(Mult::exact(3)));
    assert_eq!(
        match_children(&g, "Op", &[item, bare("r")], &kids, &Env::new()).len(),
        0
    );
}

/// Overlap under AC is as under ACI: m children matching two filters, 2^m. The
/// filters are annotated `:k`, so that children of multiplicity above 1 take part; with
/// the default, such a child matches neither filter and, without a rest, no match exists.
#[test]
fn ac_overlap_is_every_assignment() {
    let any = |name: &str, op: &str, k: &str| Item::Filter {
        name: name.into(),
        base: leaf(op),
        except: None,
        mult: Some(Mult::var(k)),
    };
    for m in 0..=6usize {
        let specs: Vec<(&str, u64)> = (0..m).map(|i| ("12", 1 + i as u64 % 3)).collect();
        let (g, kids) = ac(&specs);
        assert_eq!(
            match_children(
                &g,
                "Op",
                &[any("a", "P1", "ka"), any("b", "P2", "kb")],
                &kids,
                &Env::new()
            )
            .len(),
            1 << m,
            "m={m}"
        );
        let unannotated = match_children(
            &g,
            "Op",
            &[run("a", "P1"), run("b", "P2")],
            &kids,
            &Env::new(),
        )
        .len();
        let want = if m <= 1 { 1 << m } else { 0 };
        assert_eq!(unannotated, want, "m={m}, unannotated");
    }
}

/// "§Edge cases 2: Filter rows are deduplicated by their bindings, not by member": two
/// members of one class that match the filter's pattern with the same bindings give
/// one match, under A, ACI, and AC.
#[test]
fn equal_bindings_are_one_match() {
    for kind in [Kind::Assoc, Kind::Aci, Kind::Ac] {
        let mut g = Graph::default();
        g.kinds.insert("Op".into(), kind);
        let a1 = g.class(vec![Graph::node("A", &[])]);
        let a2 = g.class(vec![Graph::node("A", &[]), Graph::node("B", &[])]);
        // Both members match `(W (A))`, which binds nothing.
        let c = g.class(vec![Graph::node("W", &[a1]), Graph::node("W", &[a2])]);
        let base = Pat::App("W".into(), vec![Item::one(leaf("A"))]);
        let kids = vec![(c, 1)];
        assert_eq!(
            match_children(&g, "Op", &[Item::filter("gs", base)], &kids, &Env::new()).len(),
            1,
            "{kind:?}"
        );
    }
}
