// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0
//! Native AC completion vs. the enumerative encoding (plain binary `add` + commutativity and
//! associativity rewrite rules), on the SAME instance.
//!
//! One generator emits a sequence of declarations, binary `add` applications, and leaf merges.
//! Two `.egg` programs are produced from that single sequence, differing only in how `add` is
//! treated:
//!
//!   - NATIVE: `add` is declared `:assoc-comm` and AC completion is on. Building `add(add(a,b),c)`
//!     with binary applications flattens at build time to the multiset `{a,b,c}` (the inner node
//!     is non-atomic and is inlined, see `EGraph::flatten_ac_children`). No rewrite rules.
//!   - RULES: `add` is a plain 2-ary operator. Associativity and commutativity are supplied as
//!     rewrite rules, so saturation must enumerate the rearrangements that completion gets for
//!     free.
//!
//! Both programs declare the same constants, build the same binary `add` terms, and assert the
//! same leaf merges, so the derived equalities must agree. The point of the comparison is the
//! COST: node count, e-classes, saturation iterations, and e-matching steps. Run with:
//!   cargo test --test ac_vs_rules -- --ignored --nocapture

use semi_persistent_egraph::interpret::Interpreter;
use semi_persistent_egraph::model::{BignumLit, BignumModel};
use semi_persistent_egraph::nodes::DefaultConfig;
use semi_persistent_egraph::saturate::SaturationStrategy;

/// A generated instance: a shared sequence of build actions, rendered to either encoding.
struct Instance {
    /// Number of leaf constants `c0..cN`.
    n_leaves: usize,
    /// Binary `add` terms, each `(name, lhs_name, rhs_name)` where the operands are
    /// previously-named terms (a constant or an earlier `add`). Built in order.
    terms: Vec<(String, String, String)>,
    /// Leaf-pair merges `(lhs_name, rhs_name)`.
    merges: Vec<(String, String)>,
}

impl Instance {
    /// Generate an instance with the same PRNG-driven shape as the AC stress harness, but using
    /// only the `add` operator: a layered DAG of binary sums over `n_leaves` constants, plus
    /// `n_merges` random leaf identifications.
    fn generate(seed: u64, n_leaves: usize, n_layers: usize, n_merges: usize) -> Self {
        let mut rng = seed;
        let mut next = || -> usize {
            rng = rng
                .wrapping_mul(6364136223846793005)
                .wrapping_add(1442695040888963407);
            (rng >> 33) as usize
        };

        let mut terms = Vec::new();
        let mut prev_layer: Vec<String> = (0..n_leaves).map(|i| format!("c{i}")).collect();
        let mut counter = 0usize;
        for _layer in 0..n_layers {
            let n = prev_layer.len();
            let mut new_layer: Vec<String> = Vec::new();
            for _ in 0..(n / 2).max(2) {
                let a = prev_layer[next() % n].clone();
                let b = prev_layer[next() % n].clone();
                let name = format!("t{counter}");
                counter += 1;
                terms.push((name.clone(), a, b));
                new_layer.push(name);
            }
            prev_layer = new_layer;
        }

        let mut merges = Vec::new();
        for _ in 0..n_merges {
            let a = next() % n_leaves;
            let b = next() % n_leaves;
            if a != b {
                merges.push((format!("c{a}"), format!("c{b}")));
            }
        }

        Instance {
            n_leaves,
            terms,
            merges,
        }
    }

    /// Reference syntax for an operand: nullary constants `cN` are operators, written `(cN)`;
    /// `let`-bound `add` terms `tN` are referenced bare.
    fn rref(name: &str) -> String {
        if name.starts_with('c') {
            format!("({name})")
        } else {
            name.to_string()
        }
    }

    /// Shared body: constant declarations, `let` bindings for every `add` term, and the leaf
    /// merges. Identical between the two encodings; only the operator declaration and the
    /// rewrite-rule prelude differ.
    fn body(&self) -> String {
        let mut s = String::new();
        for i in 0..self.n_leaves {
            s.push_str(&format!("(function c{i} () E)\n"));
        }
        for (name, a, b) in &self.terms {
            s.push_str(&format!(
                "(let {name} (add {} {}))\n",
                Self::rref(a),
                Self::rref(b)
            ));
        }
        for (a, b) in &self.merges {
            s.push_str(&format!("(union {} {})\n", Self::rref(a), Self::rref(b)));
        }
        s
    }

    /// NATIVE encoding: `add` is `:assoc-comm`; completion derives the AC consequences.
    fn native_program(&self) -> String {
        let mut s = String::from("(sort E)\n(function add (E) E :assoc-comm)\n");
        // Bindings reference `(add (x) (y))`, i.e. binary applications. The AC build flattens
        // nested same-op children at construction, so these collapse to multisets.
        s.push_str(&self.body());
        s.push_str("(run 30)\n");
        s
    }

    /// RULES encoding: `add` is a plain 2-ary operator; associativity and commutativity are
    /// rewrite rules. Saturation must enumerate the rearrangements.
    fn rules_program(&self) -> String {
        let mut s = String::from("(sort E)\n(function add (E E) E)\n");
        // Commutativity and associativity (both orientations of assoc keep the search closed).
        s.push_str("(rewrite (add a b) (add b a))\n");
        s.push_str("(rewrite (add (add a b) c) (add a (add b c)))\n");
        s.push_str("(rewrite (add a (add b c)) (add (add a b) c))\n");
        s.push_str(&self.body());
        s.push_str("(run 30)\n");
        s
    }
}

/// Outcome of running one encoding.
struct RunStats {
    nodes: usize,
    /// Distinct e-classes among all generated term names (the derived partition).
    classes: usize,
    /// Saturation iterations the last `(run …)` took.
    iterations: usize,
    /// Whether saturation reached a fixpoint within the iteration cap.
    saturated: bool,
    /// E-matching steps (partial-match extensions) across the run.
    match_steps: u64,
}

/// Run an `.egg` program, returning node count, the partition over the named terms, and the
/// saturation outcome. `complete` turns on AC completion (used by the native encoding). Panics
/// on parse/sort/run error so a broken instance is loud rather than silently skewing the
/// comparison.
fn run_program(src: &str, complete: bool, all_names: &[String]) -> RunStats {
    semi_persistent_egraph::ematch::set_match_step_counting(true);
    let cmds = semi_persistent_egraph::parser::parse_program_v2(src)
        .unwrap_or_else(|e| panic!("parse: {e}\n---\n{src}"));
    let mut interp =
        Interpreter::<DefaultConfig, BignumLit, BignumModel, true, false>::new(BignumModel);
    interp.set_strategy(SaturationStrategy::Naive);
    interp.set_cc(complete);
    let mut globals = semi_persistent_egraph::resolve::GlobalCtx::new();
    let checked = semi_persistent_egraph::sortcheck::sortcheck_program(
        cmds,
        &mut interp.eg,
        &interp.model,
        &mut globals,
    )
    .unwrap_or_else(|e| panic!("sort: {e}\n---\n{src}"));
    interp
        .run_checked(&checked)
        .unwrap_or_else(|e| panic!("run: {e}\n---\n{src}"));

    // Partition over the named terms, normalized to dense labels so the two encodings are
    // comparable despite different representative ids.
    let mut label = std::collections::HashMap::new();
    for name in all_names {
        if let Some((id, _)) = interp.global(name) {
            let rep = interp.eg.class_repr(id).to_usize();
            let n = label.len() as u32;
            label.entry(rep).or_insert(n);
        }
    }
    let sat = interp.last_sat();
    RunStats {
        nodes: interp.eg.len(),
        classes: label.len(),
        iterations: sat.map_or(0, |s| s.iterations),
        saturated: sat.is_none_or(|s| s.saturated),
        match_steps: sat.map_or(0, |s| s.match_steps),
    }
}

use semi_persistent_egraph::containers::DenseId;

/// All term names an instance binds (constants + `add` terms), for the partition comparison.
fn all_names(inst: &Instance) -> Vec<String> {
    let mut v: Vec<String> = (0..inst.n_leaves).map(|i| format!("c{i}")).collect();
    v.extend(inst.terms.iter().map(|(n, _, _)| n.clone()));
    v
}

/// Run both encodings of one config and print a comparison row. When the rules encoding
/// reaches a fixpoint, assert the two derived partitions agree (same AC theory + same leaf
/// merges ⟹ same equalities). When it hits the iteration cap it has not finished closing, so a
/// partition mismatch there is expected and not asserted.
fn compare_row(seed: u64, leaves: usize, layers: usize, merges: usize) {
    let inst = Instance::generate(seed, leaves, layers, merges);
    let names = all_names(&inst);

    let native = run_program(&inst.native_program(), true, &names);
    let rules = run_program(&inst.rules_program(), false, &names);

    if rules.saturated {
        assert_eq!(
            native.classes, rules.classes,
            "seed={seed}: partition disagrees despite rules saturating \
             (native {} classes, rules {} classes)",
            native.classes, rules.classes
        );
    }

    eprintln!(
        "({seed},{leaves},{layers},{merges})        | {:>6} | {:>6} | {:>6} | {:>8} | {:>10} | {:>4}",
        native.nodes,
        rules.nodes,
        rules.iterations,
        if rules.saturated { "sat" } else { "CAPPED" },
        rules.match_steps,
        native.classes,
    );
}

fn header() {
    eprintln!(
        "{:<20} | {:>6} | {:>6} | {:>6} | {:>8} | {:>10} | {:>4}",
        "config(s,l,y,m)", "nat_n", "rul_n", "rul_it", "rul_sat", "rul_steps", "cls"
    );
    eprintln!("{}", "-".repeat(78));
}

fn legend() {
    eprintln!(
        "\nnat_n = native AC nodes, rul_n = rules-encoding nodes, rul_it = rules saturation \
         iterations,\nrul_sat = did rules reach a fixpoint (else hit the 30-iteration cap), \
         rul_steps = rules\ne-matching steps, cls = derived e-classes over the named terms \
         (native; rules matches when sat)."
    );
}

/// Side-by-side cost on small CONVERGING instances: both encodings terminate, so every column
/// is a comparable finite number. Shows the constant-factor and growth gap directly.
#[test]
#[ignore = "comparison harness: native AC completion vs enumerative rewrite-rule encoding"]
fn ac_vs_rules_comparison() {
    header();
    for &(seed, leaves, layers, merges) in &[
        (1u64, 4usize, 2usize, 2usize),
        (2, 5, 2, 3),
        (7, 6, 2, 3),
        (3, 6, 3, 4),
    ] {
        compare_row(seed, leaves, layers, merges);
    }
    legend();
}

/// Divergence-onset scan: hold the leaf count fixed and increase term depth (layers). Native
/// completion stays small and finite at every depth; the enumerative encoding's node count and
/// e-matching work blow up super-exponentially. The scan stops at depth 4 because the rules
/// encoding at depth 5 exhausts memory (multi-GB) before finishing even one iteration — which
/// is itself the result: the enumerative method is not merely slower, it stops being runnable
/// at a depth where native completion is still trivial.
#[test]
#[ignore = "comparison harness: depth scan showing the rules encoding's super-exponential blowup"]
fn ac_vs_rules_depth_scan() {
    header();
    // Fixed seed and leaf count; only `layers` (term depth) grows. Capped at 4: depth 5 OOMs
    // the rules encoding (see doc comment).
    for layers in 1..=4 {
        compare_row(42, 5, layers, 3);
    }
    legend();
}
