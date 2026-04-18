// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0
//! Test helpers: parse patterns and RHS terms via parser.

use crate::ast::RhsTerm;
use crate::surface_ast::SurfacePattern;

/// Parse multiple surface patterns from a string (for tests).
/// Spans are correct relative to `src`.
pub fn parse_patterns(src: &str) -> Vec<SurfacePattern> {
    crate::parser::parse_patterns(src).unwrap()
}

/// Parse a single surface pattern from a string (for tests).
pub fn parse_pattern(src: &str) -> SurfacePattern {
    let mut pats = parse_patterns(src);
    assert_eq!(
        pats.len(),
        1,
        "expected exactly one pattern, got {}",
        pats.len()
    );
    pats.remove(0)
}

/// Parse an RHS term from a string (for tests).
pub fn parse_rhs(src: &str) -> RhsTerm {
    let wrapped = format!("(rewrite x {src})");
    let cmds = crate::parser::parse_program_v2(&wrapped).unwrap();
    match cmds.into_iter().next().unwrap() {
        crate::surface_ast::SurfaceCommand::Rewrite { rhs, .. } => rhs,
        _ => panic!("expected Rewrite"),
    }
}
