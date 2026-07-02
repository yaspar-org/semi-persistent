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
                ),
                LitValChoice::Bignum => run::<$Cfg, BignumLit, BignumModel, $proofs>(
                    &surface_cmds,
                    BignumModel,
                    strategy,
                    cli.derive_ac_eqs,
                    cli.check_ac_basis,
                    cli.count_match_steps,
                ),
                LitValChoice::All => run::<$Cfg, AllLit, AllModel, $proofs>(
                    &surface_cmds,
                    AllModel,
                    strategy,
                    cli.derive_ac_eqs,
                    cli.check_ac_basis,
                    cli.count_match_steps,
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
}

fn run<Cfg, L, M, const PROOFS: bool>(
    surface_cmds: &[semi_persistent_egraph::surface_ast::SurfaceCommand],
    model: M,
    strategy: semi_persistent_egraph::saturate::SaturationStrategy,
    cc: bool,
    basis_checks: bool,
    count_match_steps: bool,
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
    }
}
