// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0
//! Criterion benchmark over the saturation corpus.
//!
//! Times our engine in process on the programs of `benches/corpus.toml`, in
//! both encodings and under both scheduling strategies. Criterion supplies
//! warm-up, adaptive iteration counts, bootstrap confidence intervals, and
//! saved-baseline comparisons. There is deliberately no fixed wall-clock or
//! ratio verdict: those proved sensitive to host state.
//!
//! This is our-side only: no egglog, no network, no second engine. The
//! cross-engine comparison lives in `scripts/egglog-compare/compare.py`, which
//! times both engines as separate processes because that is the only protocol
//! both can be held to. Here, in process and without process startup, a
//! regression is not hidden behind that constant overhead. Parsing and
//! sortchecking are deliberately included in each fresh iteration.
//!
//! ```text
//! cargo bench -p semi-persistent-egraph --bench corpus
//! cargo bench -p semi-persistent-egraph --bench corpus -- calc
//! EGRAPH_CORPUS_HEAVY=1 cargo bench -p semi-persistent-egraph --bench corpus -- acgen
//! ```
//!
//! Save a Criterion baseline before a change with `--save-baseline NAME`, then
//! compare the changed tree with `--baseline NAME`. Corpus correctness remains
//! in the ordinary Rust test suite.

use std::hint::black_box;
use std::path::PathBuf;

use criterion::{Criterion, criterion_group, criterion_main};
use semi_persistent_egraph::interpret::Interpreter;
use semi_persistent_egraph::model::{
    AllLit, AllModel, BignumLit, BignumModel, MachineLit, MachineModel,
};
use semi_persistent_egraph::nodes::DefaultConfig;
use semi_persistent_egraph::saturate::SaturationStrategy;

struct Program {
    name: String,
    encoding: String,
    path: PathBuf,
    types: String,
    heavy: bool,
}

fn manifest_dir() -> PathBuf {
    PathBuf::from(env!("CARGO_MANIFEST_DIR"))
}

/// Read the manifest. Only the fields this bench needs are parsed: the
/// per-benchmark `types` and `encodings`, and the `blocked` marker, which
/// excludes a program from timing for the same reason it excludes it from the
/// comparison.
fn load_programs() -> Vec<Program> {
    let manifest = manifest_dir().join("benches/corpus.toml");
    let text = std::fs::read_to_string(&manifest)
        .unwrap_or_else(|e| panic!("cannot read {}: {e}", manifest.display()));

    let mut out = Vec::new();
    let (mut name, mut types, mut encodings, mut blocked, mut heavy) =
        (String::new(), String::new(), Vec::new(), false, false);
    let flush = |name: &str,
                 types: &str,
                 encodings: &[String],
                 blocked: bool,
                 heavy: bool,
                 out: &mut Vec<Program>| {
        if name.is_empty() || blocked {
            return;
        }
        for encoding in encodings {
            let path = manifest_dir()
                .join("tests/egg/bench")
                .join(format!("{name}.{encoding}.egg"));
            assert!(
                path.exists(),
                "manifest lists {}, missing {}",
                name,
                path.display()
            );
            out.push(Program {
                name: name.to_owned(),
                encoding: encoding.clone(),
                path,
                types: types.to_owned(),
                heavy,
            });
        }
    };

    for raw in text.lines() {
        let line = raw.split('#').next().unwrap_or("").trim();
        if line.is_empty() {
            continue;
        }
        if let Some(header) = line
            .strip_prefix("[benchmarks.")
            .and_then(|s| s.strip_suffix(']'))
        {
            flush(&name, &types, &encodings, blocked, heavy, &mut out);
            name = header.to_owned();
            types.clear();
            encodings.clear();
            blocked = false;
            heavy = false;
        } else if line.starts_with('[') {
            flush(&name, &types, &encodings, blocked, heavy, &mut out);
            name.clear();
        } else if let Some((key, value)) = line.split_once('=') {
            let (key, value) = (key.trim(), value.trim());
            match key {
                "types" => types = value.trim_matches('"').to_owned(),
                "blocked" => blocked = true,
                "heavy" => heavy = value.trim() == "true",
                "encodings" => {
                    encodings = value
                        .trim_start_matches('[')
                        .trim_end_matches(']')
                        .split(',')
                        .map(|s| s.trim().trim_matches('"').to_owned())
                        .filter(|s| !s.is_empty())
                        .collect()
                }
                _ => {}
            }
        }
    }
    flush(&name, &types, &encodings, blocked, heavy, &mut out);
    out
}

/// One timed run: parse, sort check, and interpret the program to completion.
/// The e-graph is built fresh each sample, so no run inherits another's caches.
/// `TRACK` is on because corpus programs use `push`/`pop`, and because it is
/// what the shipped binary runs with: timing the untracked configuration would
/// measure an engine nobody uses.
fn run_once(source: &str, types: &str, strategy: SaturationStrategy) -> usize {
    // Same mapping the `.egg` test harness uses: a program that needs more than
    // one literal group runs under the combined model.
    let groups: Vec<&str> = types.split(',').map(str::trim).collect();
    match (groups.contains(&"machine"), groups.contains(&"bignum")) {
        (true, false) => timed::<MachineLit, MachineModel>(source, MachineModel, strategy),
        (false, true) => timed::<BignumLit, BignumModel>(source, BignumModel, strategy),
        _ => timed::<AllLit, AllModel>(source, AllModel, strategy),
    }
}

fn timed<L, M>(source: &str, model: M, strategy: SaturationStrategy) -> usize
where
    L: semi_persistent_egraph::literal::LitVal,
    M: semi_persistent_egraph::lit_model::LitModel<Value = L>,
{
    let cmds = semi_persistent_egraph::parser::parse_program_v2(source).expect("program parses");
    let mut interp = Interpreter::<DefaultConfig, L, M, true, false>::new(model);
    interp.set_strategy(strategy);
    let mut globals = semi_persistent_egraph::resolve::GlobalCtx::new();
    let checked = semi_persistent_egraph::sortcheck::sortcheck_program(
        cmds,
        &mut interp.eg,
        &interp.model,
        &mut globals,
    )
    .expect("program sortchecks");
    interp.run_checked(&checked).expect("program runs");
    interp.eg.len()
}

fn bench_corpus(c: &mut Criterion) {
    let include_heavy = std::env::var_os("EGRAPH_CORPUS_HEAVY").is_some();
    let programs = load_programs();
    for program in &programs {
        if program.heavy && !include_heavy {
            continue;
        }
        let source = std::fs::read_to_string(&program.path).expect("cannot read program");
        let mut group = c.benchmark_group(format!("corpus/{}.{}", program.name, program.encoding));
        for (label, strategy) in [
            ("naive", SaturationStrategy::Naive),
            ("semi", SaturationStrategy::SemiNaive),
        ] {
            group.bench_function(label, |b| {
                b.iter(|| black_box(run_once(&source, &program.types, strategy)));
            });
        }
        group.finish();
    }
}

criterion_group!(benches, bench_corpus);
criterion_main!(benches);
