// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0
use std::process;

use clap::Parser;

use semi_persistent_egraph::model::*;

#[derive(Parser)]
#[command(name = "semi-persistent", about = "Equality saturation engine")]
struct Cli {
    /// Path to an .egg program file
    file: String,

    /// E-class identifier width: 31 or 63 bits
    #[arg(long, default_value = "31", value_parser = parse_id_bits)]
    id_bits: u8,

    /// Push/pop mechanism: "diff" (semi-persistent undo log) or "clone" (deep copy)
    #[arg(long, default_value = "diff", value_parser = parse_push_pop)]
    push_pop: PushPop,

    /// Enable proof extraction (records justifications for every merge)
    #[arg(long, default_value_t = false)]
    proofs: bool,

    /// Comma-separated type groups: machine, bignum
    #[arg(long, default_value = "bignum", value_delimiter = ',')]
    types: Vec<String>,

    /// Use semi-naive saturation (delta-driven rounds). Mutually exclusive with
    /// --use-naive; the default is naive.
    #[arg(long, default_value_t = false, conflicts_with = "use_naive")]
    use_semi_naive: bool,

    /// Use naive saturation (full re-match each round). This is the default; the flag is
    /// accepted for symmetry. Mutually exclusive with --use-semi-naive.
    #[arg(long, default_value_t = false)]
    use_naive: bool,

    /// Derive all AC congruence consequences (superposition + inter-reduction) during
    /// rebuild. Off by default: when off, leapfrog matching still enumerates sub-multisets
    /// of AC nodes, but rebuild does not complete the AC rule set. See AC completion docs.
    #[arg(long, default_value_t = false, conflicts_with = "lazy_ac_eqs")]
    derive_ac_eqs: bool,

    /// Lazy AC completion: saturation runs with completion off; an equality check that
    /// plain congruence cannot decide runs goal-directed completion inside a
    /// semi-persistent transaction shared across consecutive equality checks, with rule
    /// alternation as its second phase; the restore discards everything the checks
    /// derived. `!=` checks are confirmed under completion before they pass. Mutually
    /// exclusive with --derive-ac-eqs.
    #[arg(long, default_value_t = false)]
    lazy_ac_eqs: bool,

    /// Check AC reduced-basis invariants (min_monomial minimality, Kapur-reducedness) each
    /// completion round and print the report. Diagnostic only: superlinear brute-force
    /// checks; needs --derive-ac-eqs to have an effect. Off by default.
    #[arg(long, default_value_t = false)]
    check_ac_basis: bool,

    /// Count and report total e-matching steps (match-work instrumentation).
    /// Off by default; enabling it increments counters on the matching path and needs no
    /// rebuild. Its overhead has not been established by a current Criterion comparison.
    #[arg(long, default_value_t = false)]
    count_match_steps: bool,

    /// Choose each rule's atom order per binding, from the live bucket lengths,
    /// instead of once per round from the index averages. Off by default; the
    /// finite differential tests compare the match sets (design chapter 20).
    #[arg(long, default_value_t = false, conflicts_with = "auto_scheduling")]
    runtime_scheduling: bool,

    /// Choose the scheduling mode per rule per round: a rule whose join meets
    /// a skewed access path (hub-shaped fan-outs) runs with per-binding atom
    /// ordering, flat rules keep the static plan. Off by default; the match
    /// sets are compared across modes by finite differential tests. Mutually exclusive with
    /// --runtime-scheduling.
    #[arg(long, default_value_t = false)]
    auto_scheduling: bool,

    /// Price a bound key by sampling the emitter atom's relation instead of by
    /// the round's size-biased mean fan-out. Off by default; finite differential
    /// tests compare the match sets (design chapter 20).
    #[arg(long, default_value_t = false)]
    sampled_selectivity: bool,

    /// Emitter nodes drawn per sampled estimate. Needs --sampled-selectivity.
    #[arg(long, default_value_t = 32)]
    sampler_k: usize,

    /// Bootstrap resamples guarding each sampled estimate; 0 disables the
    /// guard. Needs --sampled-selectivity.
    #[arg(long, default_value_t = 0)]
    sampler_bootstrap: usize,

    /// Bootstrap coefficient of variation above which a sampled estimate is
    /// discarded for the mean. Needs --sampler-bootstrap.
    #[arg(long, default_value_t = 1.0)]
    sampler_cv: f64,

    /// Merge survivor policy: rank (union-find rank, the default), size
    /// (absorb the smaller class by member count), uses (absorb the side with
    /// the shorter use-list), sum (member count + use-list length). These policies
    /// change representative choice and operational work, not which input equalities are
    /// asserted; differential tests compare observed check outcomes across the modes.
    #[arg(long, default_value = "rank", value_parser = parse_union_by)]
    union_by: semi_persistent_egraph::UnionBy,
}

fn parse_union_by(s: &str) -> Result<semi_persistent_egraph::UnionBy, String> {
    use semi_persistent_egraph::UnionBy;
    match s {
        "rank" => Ok(UnionBy::Rank),
        "size" => Ok(UnionBy::Size),
        "uses" => Ok(UnionBy::Uses),
        "sum" => Ok(UnionBy::Sum),
        _ => Err(format!("expected rank|size|uses|sum, got '{s}'")),
    }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
enum PushPop {
    Diff,
    Clone,
}

fn parse_push_pop(s: &str) -> Result<PushPop, String> {
    match s {
        "diff" => Ok(PushPop::Diff),
        "clone" => Ok(PushPop::Clone),
        _ => Err(format!("expected 'diff' or 'clone', got '{s}'")),
    }
}
fn parse_id_bits(s: &str) -> Result<u8, String> {
    match s {
        "31" => Ok(31),
        "63" => Ok(63),
        _ => Err(format!("expected '31' or '63', got '{s}'")),
    }
}

fn main() {
    use semi_persistent_egraph::saturate::SaturationStrategy;
    let cli = Cli::parse();

    // Default is naive; --use-semi-naive opts in. The two flags conflict (enforced by
    // clap), so at most one is set.
    let strategy = if cli.use_semi_naive {
        SaturationStrategy::SemiNaive
    } else {
        SaturationStrategy::Naive
    };

    // The two scheduling flags conflict (enforced by clap), so at most one is set.
    let sched_mode = if cli.auto_scheduling {
        semi_persistent_egraph::ematch::SchedulingMode::Auto
    } else if cli.runtime_scheduling {
        semi_persistent_egraph::ematch::SchedulingMode::Runtime
    } else {
        semi_persistent_egraph::ematch::SchedulingMode::Static
    };

    // The two completion flags conflict (enforced by clap), so at most one is set.
    let ac_mode = if cli.derive_ac_eqs {
        semi_persistent_egraph::interpret::AcMode::Eager
    } else if cli.lazy_ac_eqs {
        semi_persistent_egraph::interpret::AcMode::Lazy
    } else {
        semi_persistent_egraph::interpret::AcMode::Off
    };

    let src = match std::fs::read_to_string(&cli.file) {
        Ok(s) => s,
        Err(e) => {
            eprintln!("error reading '{}': {e}", cli.file);
            process::exit(1);
        }
    };
    let surface_cmds = match semi_persistent_egraph::parser::parse_program_v2(&src) {
        Ok(c) => c,
        Err(e) => {
            eprintln!("parse error: {e}");
            process::exit(1);
        }
    };

    let groups: Vec<TypeGroup> = cli
        .types
        .iter()
        .map(|s| {
            TypeGroup::parse(s).unwrap_or_else(|| {
                eprintln!("unknown type group: '{s}' (expected: machine, bignum)");
                process::exit(1);
            })
        })
        .collect();

    if cli.push_pop == PushPop::Clone {
        eprintln!("--push-pop clone is not yet implemented");
        process::exit(1);
    }

    let choice = choose_litval(&groups);

    // Set here rather than threaded into `run`: the flag is thread-local and
    // the whole run happens on this thread, as `--runtime-scheduling` does one
    // frame down.
    semi_persistent_egraph::schedule::set_sampled_selectivity(cli.sampled_selectivity.then_some(
        semi_persistent_egraph::schedule::SamplerConfig {
            k: cli.sampler_k,
            bootstrap: cli.sampler_bootstrap,
            cv_threshold: cli.sampler_cv,
        },
    ));

    let opts = EngineOptions {
        strategy,
        ac_mode,
        basis_checks: cli.check_ac_basis,
        count_match_steps: cli.count_match_steps,
        sched_mode,
        union_by: cli.union_by,
    };

    macro_rules! dispatch {
        ($Cfg:ty, $proofs:expr) => {
            match choice {
                LitValChoice::Machine => run::<$Cfg, MachineLit, MachineModel, $proofs>(
                    &surface_cmds,
                    MachineModel,
                    &opts,
                ),
                LitValChoice::Bignum => {
                    run::<$Cfg, BignumLit, BignumModel, $proofs>(&surface_cmds, BignumModel, &opts)
                }
                LitValChoice::All => {
                    run::<$Cfg, AllLit, AllModel, $proofs>(&surface_cmds, AllModel, &opts)
                }
            }
        };
    }

    match (cli.id_bits, cli.proofs) {
        (31, false) => dispatch!(semi_persistent_egraph::nodes::DefaultConfig, false),
        (31, true) => dispatch!(semi_persistent_egraph::nodes::DefaultConfig, true),
        (63, false) => dispatch!(semi_persistent_egraph::nodes::Config64, false),
        (63, true) => dispatch!(semi_persistent_egraph::nodes::Config64, true),
        _ => unreachable!(),
    }

    // Prints only under the `phase-timing` feature with `EGRAPH_PHASE` set; a
    // no-op call otherwise. Placed after the dispatch rather than inside `run`
    // so a program that ends in `(pop)` still reports the rounds it ran.
    semi_persistent_egraph::phase_timing::dump();
    // Same discipline, for the `seek-stats` feature and `EGRAPH_SEEK`.
    semi_persistent_egraph::leapfrog::seek_stats::dump();
}

/// The engine settings the command line resolves before dispatch. Grouped so
/// the three dispatch arms below name them once each instead of repeating the
/// same six values per literal-value choice.
struct EngineOptions {
    strategy: semi_persistent_egraph::saturate::SaturationStrategy,
    ac_mode: semi_persistent_egraph::interpret::AcMode,
    basis_checks: bool,
    count_match_steps: bool,
    sched_mode: semi_persistent_egraph::ematch::SchedulingMode,
    union_by: semi_persistent_egraph::UnionBy,
}

fn run<Cfg, L, M, const PROOFS: bool>(
    surface_cmds: &[semi_persistent_egraph::surface_ast::SurfaceCommand],
    model: M,
    opts: &EngineOptions,
) where
    Cfg: semi_persistent_egraph::config::EGraphConfig,
    Cfg::O: std::hash::Hash,
    L: semi_persistent_egraph::literal::LitVal,
    M: semi_persistent_egraph::lit_model::LitModel<Value = L>,
    semi_persistent_egraph::canon::MSetCanon:
        semi_persistent_egraph::canon::VarCanon<Cfg::G, Cfg::C>,
{
    if opts.count_match_steps {
        semi_persistent_egraph::ematch::set_match_step_counting(true);
    }
    semi_persistent_egraph::ematch::set_scheduling_mode(opts.sched_mode);
    let mut interp =
        semi_persistent_egraph::interpret::Interpreter::<Cfg, L, M, true, PROOFS>::new(model);
    interp.set_strategy(opts.strategy);
    interp.set_ac_mode(opts.ac_mode);
    interp.set_union_by(opts.union_by);
    interp.set_basis_checks(opts.basis_checks);
    let mut globals = semi_persistent_egraph::resolve::GlobalCtx::new();
    let checked = match semi_persistent_egraph::sortcheck::sortcheck_program(
        surface_cmds.to_vec(),
        &mut interp.eg,
        &interp.model,
        &mut globals,
    ) {
        Ok(c) => c,
        Err(e) => {
            eprintln!("sort error: {e}");
            process::exit(1);
        }
    };
    if let Err(e) = interp.run_checked(&checked) {
        eprintln!("error: {e}");
        process::exit(1);
    }
    eprintln!("ok — {} nodes", interp.eg.len());
    if opts.count_match_steps {
        eprintln!(
            "match steps: {}",
            semi_persistent_egraph::ematch::match_steps()
        );
        let (taken, rejected) = semi_persistent_egraph::schedule::sample_tally();
        if taken > 0 {
            eprintln!("sampled estimates: {taken}, guard fallbacks: {rejected}");
        }
    }
}
