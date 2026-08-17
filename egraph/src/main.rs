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
    #[arg(long, default_value_t = false)]
    derive_ac_eqs: bool,

    /// Check AC reduced-basis invariants (min_monomial minimality, Kapur-reducedness) each
    /// completion round and print the report. Diagnostic only: superlinear brute-force
    /// checks; needs --derive-ac-eqs to have an effect. Off by default.
    #[arg(long, default_value_t = false)]
    check_ac_basis: bool,

    /// Count and report total e-matching steps (match-work instrumentation).
    /// Off by default; enabling it has negligible cost and needs no rebuild.
    #[arg(long, default_value_t = false)]
    count_match_steps: bool,

    /// Choose each rule's atom order per binding, from the live bucket lengths,
    /// instead of once per round from the index averages. Off by default; the
    /// match set is the same either way (design chapter 20, S4).
    #[arg(long, default_value_t = false)]
    runtime_scheduling: bool,

    /// Price a bound key by sampling the emitter atom's relation instead of by
    /// the round's size-biased mean fan-out. Off by default; the match set is
    /// the same either way (design chapter 20, S5).
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

    macro_rules! dispatch {
        ($Cfg:ty, $proofs:expr) => {
            match choice {
                LitValChoice::Machine => run::<$Cfg, MachineLit, MachineModel, $proofs>(
                    &surface_cmds,
                    MachineModel,
                    strategy,
                    cli.derive_ac_eqs,
                    cli.check_ac_basis,
                    cli.count_match_steps,
                    cli.runtime_scheduling,
                ),
                LitValChoice::Bignum => run::<$Cfg, BignumLit, BignumModel, $proofs>(
                    &surface_cmds,
                    BignumModel,
                    strategy,
                    cli.derive_ac_eqs,
                    cli.check_ac_basis,
                    cli.count_match_steps,
                    cli.runtime_scheduling,
                ),
                LitValChoice::All => run::<$Cfg, AllLit, AllModel, $proofs>(
                    &surface_cmds,
                    AllModel,
                    strategy,
                    cli.derive_ac_eqs,
                    cli.check_ac_basis,
                    cli.count_match_steps,
                    cli.runtime_scheduling,
                ),
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

fn run<Cfg, L, M, const PROOFS: bool>(
    surface_cmds: &[semi_persistent_egraph::surface_ast::SurfaceCommand],
    model: M,
    strategy: semi_persistent_egraph::saturate::SaturationStrategy,
    cc: bool,
    basis_checks: bool,
    count_match_steps: bool,
    runtime_scheduling: bool,
) where
    Cfg: semi_persistent_egraph::config::EGraphConfig,
    Cfg::O: std::hash::Hash,
    L: semi_persistent_egraph::literal::LitVal,
    M: semi_persistent_egraph::lit_model::LitModel<Value = L>,
    semi_persistent_egraph::canon::MSetCanon:
        semi_persistent_egraph::canon::VarCanon<Cfg::G, Cfg::C>,
{
    if count_match_steps {
        semi_persistent_egraph::ematch::set_match_step_counting(true);
    }
    semi_persistent_egraph::ematch::set_runtime_scheduling(runtime_scheduling);
    let mut interp =
        semi_persistent_egraph::interpret::Interpreter::<Cfg, L, M, true, PROOFS>::new(model);
    interp.set_strategy(strategy);
    interp.set_cc(cc);
    interp.set_basis_checks(basis_checks);
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
    if count_match_steps {
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
