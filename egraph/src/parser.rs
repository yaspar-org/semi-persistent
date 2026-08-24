// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0
//! New parser for the unified surface syntax (§36).
//!
//! Emits `SurfaceCommand`. Pattern parsing is uniform — no `[]`/`{}`
//! dispatch. Everything is `(op pat_child*)`.

use crate::ast::*;
use crate::registry::OpMeta;
use crate::surface_ast::*;
use winnow::ascii::multispace0;
use winnow::combinator::cut_err;
use winnow::error::{ContextError, ErrMode, StrContext, StrContextValue};
use winnow::token::take_while;
use winnow::{ModalResult, Parser};

pub type ParseError = String;

// ── Span helpers ──

fn span_of(base: usize, start_ptr: usize, input: &mut &str) -> Span {
    let end_ptr = input.as_ptr() as usize;
    Span::new((start_ptr - base) as u32, (end_ptr - base) as u32)
}

// ── Lexical helpers (self-contained, no dependency on parser.rs) ──

fn ws(input: &mut &str) -> ModalResult<()> {
    loop {
        multispace0.parse_next(input)?;
        if input.starts_with(';') {
            let _ = take_while(0.., |c: char| c != '\n').parse_next(input)?;
        } else {
            break;
        }
    }
    Ok(())
}

fn ident<'s>(input: &mut &'s str) -> ModalResult<&'s str> {
    ws(input)?;
    let s = *input;
    if s.is_empty() || !s.starts_with(|c: char| c.is_alphabetic() || c == '_') {
        let mut e = ContextError::new();
        e.push(StrContext::Expected(StrContextValue::Description(
            "identifier",
        )));
        return Err(ErrMode::Backtrack(e));
    }
    let len = s
        .find(|c: char| !(c.is_alphanumeric() || c == '_'))
        .unwrap_or(s.len());
    let tok = &s[..len];
    *input = &s[len..];
    Ok(tok)
}

const SYMBOLS: &[&str] = &[
    "<<", ">>", "<=", ">=", "!=", "==", "=>", "+", "-", "*", "/", "%", "<", ">", "&", "|", "^", "~",
];

fn symbol<'s>(input: &mut &'s str) -> ModalResult<&'s str> {
    for &sym in SYMBOLS {
        if input.starts_with(sym) {
            let tok = &input[..sym.len()];
            *input = &input[sym.len()..];
            return Ok(tok);
        }
    }
    let mut e = ContextError::new();
    e.push(StrContext::Expected(StrContextValue::Description("symbol")));
    Err(ErrMode::Backtrack(e))
}

fn op_name<'s>(input: &mut &'s str) -> ModalResult<&'s str> {
    if input.starts_with(|c: char| c.is_alphabetic() || c == '_') {
        return ident(input);
    }
    symbol(input)
}

fn op_token<'s>(input: &mut &'s str) -> ModalResult<&'s str> {
    ws(input)?;
    let s = *input;
    let len = s
        .find(|c: char| {
            c.is_whitespace() || matches!(c, '(' | ')' | '[' | ']' | '{' | '}' | ';' | '"')
        })
        .unwrap_or(s.len());
    if len == 0 {
        let mut e = ContextError::new();
        e.push(StrContext::Expected(StrContextValue::Description(
            "operator",
        )));
        return Err(ErrMode::Backtrack(e));
    }
    let tok = &s[..len];
    *input = &s[len..];
    Ok(tok)
}

/// Command-head keyword. Like [`ident`], but `-` is part of the token, so `print-size`
/// and `print-stats` lex as one word instead of `print` followed by a stray `-size`.
fn kw_token<'s>(input: &mut &'s str) -> ModalResult<&'s str> {
    ws(input)?;
    let s = *input;
    if s.is_empty() || !s.starts_with(|c: char| c.is_alphabetic() || c == '_') {
        let mut e = ContextError::new();
        e.push(StrContext::Expected(StrContextValue::Description(
            "command keyword",
        )));
        return Err(ErrMode::Backtrack(e));
    }
    let len = s
        .find(|c: char| !(c.is_alphanumeric() || c == '_' || c == '-'))
        .unwrap_or(s.len());
    let tok = &s[..len];
    *input = &s[len..];
    Ok(tok)
}

fn op_expr(input: &mut &str) -> ModalResult<String> {
    ws(input)?;
    if input.starts_with(|c: char| c.is_alphabetic() || c == '_') {
        let saved = *input;
        let name = ident(input)?;
        if input.starts_with("::") {
            *input = &input[2..];
            let method = op_name(input)?;
            return Ok(format!("{name}::{method}"));
        }
        *input = saved;
    }
    let tok = op_token(input)?;
    Ok(tok.to_owned())
}

fn num_token<'s>(input: &mut &'s str) -> ModalResult<&'s str> {
    ws(input)?;
    let s = *input;
    let starts_numeric = s.starts_with(|c: char| c.is_ascii_digit())
        || (s.starts_with('-') && s.len() > 1 && s.as_bytes()[1].is_ascii_digit());
    if !starts_numeric {
        let mut e = ContextError::new();
        e.push(StrContext::Expected(StrContextValue::Description("number")));
        return Err(ErrMode::Backtrack(e));
    }
    let len = s
        .find(|c: char| {
            c.is_whitespace() || matches!(c, '(' | ')' | '[' | ']' | '{' | '}' | ';' | '"')
        })
        .unwrap_or(s.len());
    let tok = &s[..len];
    *input = &s[len..];
    Ok(tok)
}

fn number(input: &mut &str) -> ModalResult<u64> {
    let tok = num_token(input)?;
    tok.parse::<u64>().map_err(|_| {
        let mut e = ContextError::new();
        e.push(StrContext::Expected(StrContextValue::Description("number")));
        ErrMode::Cut(e)
    })
}

fn expect_char(input: &mut &str, c: char) -> ModalResult<()> {
    ws(input)?;
    if input.starts_with(c) {
        *input = &input[c.len_utf8()..];
        Ok(())
    } else {
        Err(ErrMode::Backtrack(ContextError::new()))
    }
}

fn cut_char(input: &mut &str, c: char) -> ModalResult<()> {
    ws(input)?;
    if input.starts_with(c) {
        *input = &input[c.len_utf8()..];
        Ok(())
    } else {
        let mut e = ContextError::new();
        e.push(StrContext::Expected(StrContextValue::CharLiteral(c)));
        Err(ErrMode::Cut(e))
    }
}

fn is_literal(s: &str) -> bool {
    s.starts_with(|c: char| c.is_ascii_digit())
        || (s.starts_with('-') && s.len() > 1)
        || s == "true"
        || s == "false"
}

fn parse_quoted_string(input: &mut &str) -> ModalResult<String> {
    ws(input)?;
    if !input.starts_with('"') {
        return Err(ErrMode::Backtrack(ContextError::new()));
    }
    *input = &input[1..];
    let mut buf = String::from('"');
    loop {
        let Some(c) = input.chars().next() else {
            let mut e = ContextError::new();
            e.push(StrContext::Expected(StrContextValue::Description(
                "closing \"",
            )));
            return Err(ErrMode::Cut(e));
        };
        *input = &input[c.len_utf8()..];
        match c {
            '"' => {
                buf.push('"');
                return Ok(buf);
            }
            '\\' => {
                let esc = input.chars().next().ok_or_else(|| {
                    let mut e = ContextError::new();
                    e.push(StrContext::Expected(StrContextValue::Description(
                        "escape character",
                    )));
                    ErrMode::Cut(e)
                })?;
                *input = &input[esc.len_utf8()..];
                match esc {
                    '"' => buf.push('"'),
                    '\\' => buf.push('\\'),
                    'n' => buf.push('\n'),
                    't' => buf.push('\t'),
                    _ => {
                        buf.push('\\');
                        buf.push(esc);
                    }
                }
            }
            _ => buf.push(c),
        }
    }
}

// ── Ground terms ──

fn parse_term_inner(input: &mut &str, base: usize) -> ModalResult<Term> {
    ws(input)?;
    let start = input.as_ptr() as usize;
    if input.starts_with('(') {
        expect_char(input, '(')?;
        let op = cut_err(op_expr)
            .context(StrContext::Label("operator name"))
            .parse_next(input)?;
        let mut children = Vec::new();
        loop {
            ws(input)?;
            if input.starts_with(')') {
                break;
            }
            children.push(parse_term_inner(input, base)?);
        }
        cut_char(input, ')')?;
        Ok(Term::App {
            op,
            children,
            span: span_of(base, start, input),
        })
    } else if input.starts_with('"') {
        let s = parse_quoted_string(input)?;
        Ok(Term::Lit(s, span_of(base, start, input)))
    } else if let Ok(tok) = num_token(input) {
        Ok(Term::Lit(tok.to_owned(), span_of(base, start, input)))
    } else {
        let tok = ident(input)?;
        Ok(Term::Lit(tok.to_owned(), span_of(base, start, input)))
    }
}

#[allow(dead_code)]
fn parse_term(input: &mut &str) -> ModalResult<Term> {
    let base = input.as_ptr() as usize;
    parse_term_inner(input, base)
}

// ── Surface patterns (uniform, no []/{}  dispatch) ──

fn parse_pattern(input: &mut &str, base: usize) -> ModalResult<SurfacePattern> {
    ws(input)?;
    let start = input.as_ptr() as usize;
    if input.starts_with('(') {
        expect_char(input, '(')?;
        let op = cut_err(op_expr)
            .context(StrContext::Label("operator name"))
            .parse_next(input)?;

        // Optional prefix rest: ..name
        ws(input)?;
        let prefix = if input.starts_with("..") {
            let rstart = input.as_ptr() as usize;
            *input = &input[2..];
            let name = ident(input)?;
            let sp = span_of(base, rstart, input);
            Some((name.to_owned(), sp))
        } else {
            None
        };

        // Children (Elem or ElemMult, no Rest)
        let mut children = Vec::new();
        loop {
            ws(input)?;
            if input.starts_with(')') {
                break;
            }
            if input.starts_with("..") {
                break; // suffix rest
            }
            children.push(parse_pat_child(input, base)?);
        }

        // Optional suffix rest: ..name
        ws(input)?;
        let suffix = if input.starts_with("..") {
            let rstart = input.as_ptr() as usize;
            *input = &input[2..];
            let name = ident(input)?;
            let sp = span_of(base, rstart, input);
            Some((name.to_owned(), sp))
        } else {
            None
        };

        cut_char(input, ')')?;
        // If prefix was parsed but there are no children and no suffix,
        // treat it as suffix (e.g. `(union ..rest)` → suffix=rest).
        let (prefix, suffix) = if prefix.is_some() && children.is_empty() && suffix.is_none() {
            (None, prefix)
        } else {
            (prefix, suffix)
        };
        Ok(SurfacePattern::App {
            op,
            prefix,
            children,
            suffix,
            span: span_of(base, start, input),
        })
    } else if input.starts_with('"') {
        let s = parse_quoted_string(input)?;
        let sp = span_of(base, start, input);
        Ok(SurfacePattern::Lit(s, sp))
    } else if let Ok(tok) = num_token(input) {
        let sp = span_of(base, start, input);
        Ok(SurfacePattern::Lit(tok.to_owned(), sp))
    } else {
        let tok = ident(input)?;
        let sp = span_of(base, start, input);
        if is_literal(tok) {
            Ok(SurfacePattern::Lit(tok.to_owned(), sp))
        } else {
            Ok(SurfacePattern::Var(tok.to_owned(), sp))
        }
    }
}

fn parse_pat_child(input: &mut &str, base: usize) -> ModalResult<SurfacePatChild> {
    ws(input)?;
    let pat = parse_pattern(input, base)?;
    // Check for :mult
    ws(input)?;
    if input.starts_with(':') {
        *input = &input[1..];
        let mult = parse_mult_spec(input)?;
        Ok(SurfacePatChild::ElemMult(pat, mult))
    } else {
        Ok(SurfacePatChild::Elem(pat))
    }
}

fn parse_mult_spec(input: &mut &str) -> ModalResult<MultSpec> {
    ws(input)?;
    if input.starts_with(|c: char| c.is_ascii_digit()) {
        let n = number(input)?;
        Ok(MultSpec::Exact(n))
    } else {
        let name = ident(input)?;
        ws(input)?;
        let constraint = parse_cmp_constraint(input)?;
        Ok(MultSpec::Var {
            name: name.to_owned(),
            constraint,
        })
    }
}

fn parse_cmp_constraint(input: &mut &str) -> ModalResult<Option<(CmpOp, u64)>> {
    ws(input)?;
    let op = if input.starts_with(">=") {
        *input = &input[2..];
        Some(CmpOp::Ge)
    } else if input.starts_with("<=") {
        *input = &input[2..];
        Some(CmpOp::Le)
    } else if input.starts_with("==") {
        *input = &input[2..];
        Some(CmpOp::Eq)
    } else if input.starts_with("!=") {
        *input = &input[2..];
        Some(CmpOp::Ne)
    } else if input.starts_with('>') {
        *input = &input[1..];
        Some(CmpOp::Gt)
    } else if input.starts_with('<') {
        *input = &input[1..];
        Some(CmpOp::Lt)
    } else {
        None
    };
    match op {
        Some(cmp) => {
            let n = number(input)?;
            Ok(Some((cmp, n)))
        }
        None => Ok(None),
    }
}

// ── RHS terms ──

fn parse_rhs(input: &mut &str, base: usize) -> ModalResult<RhsTerm> {
    ws(input)?;
    let start = input.as_ptr() as usize;
    if input.starts_with('(') {
        expect_char(input, '(')?;
        let op = cut_err(op_expr)
            .context(StrContext::Label("operator name"))
            .parse_next(input)?;
        let mut children = Vec::new();
        loop {
            ws(input)?;
            if input.starts_with(')') {
                break;
            }
            if input.starts_with("..") {
                children.push(parse_rhs_dotdot(input, base)?);
            } else {
                let child_start = input.as_ptr() as usize;
                let t = parse_rhs(input, base)?;
                ws(input)?;
                // `term:mult` — a multiplicity annotation on an RHS element.
                if input.starts_with(':') {
                    *input = &input[1..];
                    let mult = parse_mult_expr(input)?;
                    children.push(RhsChild::TermMult {
                        term: t,
                        mult,
                        span: span_of(base, child_start, input),
                    });
                } else {
                    children.push(RhsChild::Term(t));
                }
            }
        }
        cut_char(input, ')')?;
        Ok(RhsTerm::App {
            op,
            children,
            span: span_of(base, start, input),
        })
    } else if input.starts_with('"') {
        let s = parse_quoted_string(input)?;
        let sp = span_of(base, start, input);
        Ok(RhsTerm::Lit(s, sp))
    } else if let Ok(tok) = num_token(input) {
        let sp = span_of(base, start, input);
        Ok(RhsTerm::Lit(tok.to_owned(), sp))
    } else {
        let tok = ident(input)?;
        let sp = span_of(base, start, input);
        if is_literal(tok) {
            Ok(RhsTerm::Lit(tok.to_owned(), sp))
        } else {
            Ok(RhsTerm::Var(tok.to_owned(), sp))
        }
    }
}

fn parse_rhs_dotdot(input: &mut &str, base: usize) -> ModalResult<RhsChild> {
    let start = input.as_ptr() as usize;
    assert!(input.starts_with(".."));
    *input = &input[2..];
    ws(input)?;

    if input.starts_with('{') {
        expect_char(input, '{')?;
        let body = parse_rhs(input, base)?;
        ws(input)?;
        let mult = if input.starts_with(':') {
            *input = &input[1..];
            Some(parse_mult_expr(input)?)
        } else {
            None
        };
        ws(input)?;
        expect_kw(input, "for")?;
        let var = ident(input)?.to_owned();
        ws(input)?;
        let mult_var = if input.starts_with(':') {
            *input = &input[1..];
            Some(ident(input)?.to_owned())
        } else {
            None
        };
        ws(input)?;
        expect_kw(input, "in")?;
        let source = ident(input)?.to_owned();
        let filter = parse_optional_if(input, base)?;
        cut_char(input, '}')?;
        match (mult, mult_var) {
            (Some(m), Some(k)) => Ok(RhsChild::MsetComp {
                body: Box::new(body),
                mult: m,
                var,
                mult_var: k,
                source,
                filter,
                span: span_of(base, start, input),
            }),
            (None, None) => Ok(RhsChild::SetComp {
                body: Box::new(body),
                var,
                source,
                filter,
                span: span_of(base, start, input),
            }),
            _ => {
                let mut e = ContextError::new();
                e.push(StrContext::Label(
                    "multiset comp needs both :mult on body and :k on var",
                ));
                Err(ErrMode::Cut(e))
            }
        }
    } else if input.starts_with('[') {
        expect_char(input, '[')?;
        let body = parse_rhs(input, base)?;
        ws(input)?;
        expect_kw(input, "for")?;
        let var = ident(input)?.to_owned();
        ws(input)?;
        expect_kw(input, "in")?;
        let source = ident(input)?.to_owned();
        let filter = parse_optional_if(input, base)?;
        cut_char(input, ']')?;
        Ok(RhsChild::SeqComp {
            body: Box::new(body),
            var,
            source,
            filter,
            span: span_of(base, start, input),
        })
    } else {
        let name = ident(input)?;
        Ok(RhsChild::Splice(
            name.to_owned(),
            span_of(base, start, input),
        ))
    }
}

fn expect_kw(input: &mut &str, kw: &'static str) -> ModalResult<()> {
    let tok = ident(input)?;
    if tok != kw {
        let mut e = ContextError::new();
        e.push(StrContext::Expected(StrContextValue::StringLiteral(kw)));
        return Err(ErrMode::Cut(e));
    }
    Ok(())
}

fn parse_optional_if(input: &mut &str, base: usize) -> ModalResult<Option<Box<RhsTerm>>> {
    ws(input)?;
    if input.starts_with("if") && input[2..].starts_with(|c: char| c.is_whitespace() || c == '(') {
        *input = &input[2..];
        let guard = parse_rhs(input, base)?;
        Ok(Some(Box::new(guard)))
    } else {
        Ok(None)
    }
}

fn parse_mult_expr(input: &mut &str) -> ModalResult<MultExpr> {
    ws(input)?;
    if input.starts_with('(') {
        expect_char(input, '(')?;
        let op = op_expr(input)?;
        let mut args = Vec::new();
        loop {
            ws(input)?;
            if input.starts_with(')') {
                break;
            }
            args.push(parse_mult_expr(input)?);
        }
        cut_char(input, ')')?;
        Ok(MultExpr::Prim { op, args })
    } else if input.starts_with(|c: char| c.is_ascii_digit()) {
        let n = number(input)?;
        Ok(MultExpr::Lit(n))
    } else {
        let name = ident(input)?;
        Ok(MultExpr::Var(name.to_owned()))
    }
}

// ── Actions ──

fn parse_action(input: &mut &str, base: usize) -> ModalResult<Action> {
    let start = input.as_ptr() as usize;
    expect_char(input, '(')?;
    let kw = op_expr(input)?;
    let action = match kw.as_str() {
        "union" => {
            let a = parse_rhs(input, base)?;
            let b = parse_rhs(input, base)?;
            Action::Union(a, b)
        }
        "set" => {
            cut_char(input, '(')?;
            let func = ident(input)?.to_owned();
            let mut args = Vec::new();
            loop {
                ws(input)?;
                if input.starts_with(')') {
                    break;
                }
                args.push(parse_rhs(input, base)?);
            }
            cut_char(input, ')')?;
            let value = parse_rhs(input, base)?;
            Action::Set { func, args, value }
        }
        _ => {
            let mut children = Vec::new();
            loop {
                ws(input)?;
                if input.starts_with(')') {
                    break;
                }
                if input.starts_with("..") {
                    children.push(parse_rhs_dotdot(input, base)?);
                } else {
                    children.push(RhsChild::Term(parse_rhs(input, base)?));
                }
            }
            let action = Action::Insert(RhsTerm::App {
                op: kw,
                children,
                span: span_of(base, start, input),
            });
            cut_char(input, ')')?;
            return Ok(action);
        }
    };
    cut_char(input, ')')?;
    Ok(action)
}

// ── Commands ──

/// Trailing tags recognized after rewrite-like forms. Parsed as a loop, so they may appear
/// in any order. Each command validates the subset it supports after parsing.
struct RuleTags {
    when: Vec<SurfacePattern>,
    subsume: bool,
    ruleset: Option<String>,
}

fn parse_rule_tags(input: &mut &str, base: usize) -> ModalResult<RuleTags> {
    let mut t = RuleTags {
        when: Vec::new(),
        subsume: false,
        ruleset: None,
    };
    loop {
        ws(input)?;
        if input.starts_with(":when") {
            *input = &input[":when".len()..];
            cut_char(input, '(')?;
            loop {
                ws(input)?;
                if input.starts_with(')') {
                    break;
                }
                t.when.push(parse_pattern(input, base)?);
            }
            cut_char(input, ')')?;
        } else if input.starts_with(":subsume") {
            *input = &input[":subsume".len()..];
            t.subsume = true;
        } else if input.starts_with(":ruleset") {
            *input = &input[":ruleset".len()..];
            t.ruleset = Some(ident(input)?.to_owned());
        } else {
            break;
        }
    }
    Ok(t)
}

/// Read a pattern as an RHS term — the conversion `(birewrite …)` needs to use each side as
/// the other direction's right-hand side. A rest variable becomes a splice; a `:mult`
/// annotation has no RHS spelling and is rejected.
fn pattern_as_rhs(p: &SurfacePattern) -> ModalResult<RhsTerm> {
    match p {
        SurfacePattern::Var(n, s) => Ok(RhsTerm::Var(n.clone(), *s)),
        SurfacePattern::Lit(v, s) => Ok(RhsTerm::Lit(v.clone(), *s)),
        SurfacePattern::App {
            op,
            prefix,
            children,
            suffix,
            span,
        } => {
            let mut cs = Vec::with_capacity(children.len() + 2);
            if let Some((n, s)) = prefix {
                cs.push(RhsChild::Splice(n.clone(), *s));
            }
            for c in children {
                match c {
                    SurfacePatChild::Elem(p) => cs.push(RhsChild::Term(pattern_as_rhs(p)?)),
                    SurfacePatChild::ElemMult(..) => {
                        let mut e = ContextError::new();
                        e.push(StrContext::Label(
                            "birewrite side cannot carry a :mult annotation",
                        ));
                        return Err(ErrMode::Cut(e));
                    }
                }
            }
            if let Some((n, s)) = suffix {
                cs.push(RhsChild::Splice(n.clone(), *s));
            }
            Ok(RhsTerm::App {
                op: op.clone(),
                children: cs,
                span: *span,
            })
        }
    }
}

/// `:until (= a b)` / `:until (!= a b)` — two ground terms and the relation that stops the run.
fn parse_run_goal(input: &mut &str, base: usize) -> ModalResult<RunGoal> {
    cut_char(input, '(')?;
    ws(input)?;
    let equal = if input.starts_with("!=") {
        *input = &input[2..];
        false
    } else if input.starts_with('=') {
        *input = &input[1..];
        true
    } else {
        let mut e = ContextError::new();
        e.push(StrContext::Expected(StrContextValue::Description(
            ":until goal must be (= a b) or (!= a b)",
        )));
        return Err(ErrMode::Cut(e));
    };
    let left = parse_term_inner(input, base)?;
    let right = parse_term_inner(input, base)?;
    cut_char(input, ')')?;
    Ok(RunGoal { left, right, equal })
}

/// Parse one command. `desugared` collects the *extra* commands a surface form expands
/// into — today only `(birewrite …)`, which is two rewrites; the caller appends them after
/// the returned command.
fn parse_command(
    input: &mut &str,
    base: usize,
    desugared: &mut Vec<SurfaceCommand>,
) -> ModalResult<SurfaceCommand> {
    ws(input)?;
    let start = input.as_ptr() as usize;
    expect_char(input, '(')?;
    let kw = cut_err(kw_token).parse_next(input)?;
    let cmd = match kw {
        "rewrite" => {
            let lhs = parse_pattern(input, base)?;
            let rhs = parse_rhs(input, base)?;
            let t = parse_rule_tags(input, base)?;
            SurfaceCommand::Rewrite {
                lhs,
                rhs,
                when: t.when,
                subsume: t.subsume,
                ruleset: t.ruleset,
            }
        }
        // `(birewrite a b …)` is exactly the two rewrites `a -> b` and `b -> a`, so it is
        // desugared here rather than carried through the pipeline. Both sides parse as
        // patterns and each is converted to an RHS term for the opposite direction.
        "birewrite" => {
            let lhs = parse_pattern(input, base)?;
            let rhs = parse_pattern(input, base)?;
            let t = parse_rule_tags(input, base)?;
            if t.subsume {
                let mut e = ContextError::new();
                e.push(StrContext::Label(
                    "birewrite cannot be :subsume (it would subsume the node the reverse \
                     direction has to match)",
                ));
                return Err(ErrMode::Cut(e));
            }
            desugared.push(SurfaceCommand::Rewrite {
                lhs: rhs.clone(),
                rhs: pattern_as_rhs(&lhs)?,
                when: t.when.clone(),
                subsume: false,
                ruleset: t.ruleset.clone(),
            });
            SurfaceCommand::Rewrite {
                rhs: pattern_as_rhs(&rhs)?,
                lhs,
                when: t.when,
                subsume: false,
                ruleset: t.ruleset,
            }
        }
        "rule" => {
            cut_char(input, '(')?;
            let mut body = Vec::new();
            loop {
                ws(input)?;
                if input.starts_with(')') {
                    break;
                }
                body.push(parse_pattern(input, base)?);
            }
            cut_char(input, ')')?;
            cut_char(input, '(')?;
            let mut head = Vec::new();
            loop {
                ws(input)?;
                if input.starts_with(')') {
                    break;
                }
                head.push(parse_action(input, base)?);
            }
            cut_char(input, ')')?;
            let t = parse_rule_tags(input, base)?;
            if !t.when.is_empty() {
                let mut e = ContextError::new();
                e.push(StrContext::Label(
                    "rule cannot use :when; put guard patterns in the rule body",
                ));
                return Err(ErrMode::Cut(e));
            }
            if t.subsume {
                let mut e = ContextError::new();
                e.push(StrContext::Label(
                    "rule cannot use :subsume; :subsume applies only to rewrite",
                ));
                return Err(ErrMode::Cut(e));
            }
            SurfaceCommand::Rule {
                body,
                head,
                ruleset: t.ruleset,
            }
        }
        "sort" => {
            let name = ident(input)?.to_owned();
            SurfaceCommand::Pass(Command::Sort(name))
        }
        // `(function …)` and `(constructor …)` share a shape; the keyword decides only
        // whether the declared op is a constructor (a term former, extraction-eligible with
        // a `:cost`) or a plain function.
        "function" | "constructor" => {
            let name = ident(input)?.to_owned();
            cut_char(input, '(')?;
            let mut arg_sorts = Vec::new();
            loop {
                ws(input)?;
                if input.starts_with(')') {
                    break;
                }
                arg_sorts.push(ident(input)?.to_owned());
            }
            cut_char(input, ')')?;
            let ret_sort = ident(input)?.to_owned();
            let (tags, mut meta) = parse_decl_tags(input, base)?;
            meta.is_constructor = kw == "constructor";
            SurfaceCommand::Pass(Command::Function {
                name,
                arg_sorts,
                ret_sort,
                tags,
                meta,
            })
        }
        "datatype" => {
            let name = ident(input)?.to_owned();
            let mut variants = Vec::new();
            loop {
                ws(input)?;
                if input.starts_with(')') {
                    break;
                }
                cut_char(input, '(')?;
                let ctor = ident(input)?.to_owned();
                let mut args = Vec::new();
                loop {
                    ws(input)?;
                    if input.starts_with(')') || input.starts_with(':') {
                        break;
                    }
                    args.push(ident(input)?.to_owned());
                }
                let (tags, mut meta) = parse_decl_tags(input, base)?;
                // A datatype variant is a constructor by construction.
                meta.is_constructor = true;
                cut_char(input, ')')?;
                variants.push(Variant {
                    name: ctor,
                    arg_sorts: args,
                    tags,
                    meta,
                });
            }
            SurfaceCommand::Pass(Command::Datatype { name, variants })
        }
        "union" => {
            let a = parse_term_inner(input, base)?;
            let b = parse_term_inner(input, base)?;
            SurfaceCommand::Pass(Command::Union(a, b))
        }
        "let" => {
            let name = ident(input)?.to_owned();
            let t = parse_term_inner(input, base)?;
            SurfaceCommand::Pass(Command::Let(name, t))
        }
        "ruleset" => {
            let name = ident(input)?.to_owned();
            SurfaceCommand::Pass(Command::Ruleset(name))
        }
        "run" => {
            // `(run N)` / `(run ruleset N)`: the optional leading identifier names the
            // ruleset, so the budget is whichever of the two tokens is a number.
            ws(input)?;
            let ruleset = if input.starts_with(|c: char| c.is_alphabetic() || c == '_') {
                Some(ident(input)?.to_owned())
            } else {
                None
            };
            let limit = number(input)?;
            ws(input)?;
            let until = if input.starts_with(":until") {
                *input = &input[":until".len()..];
                Some(parse_run_goal(input, base)?)
            } else {
                None
            };
            SurfaceCommand::Pass(Command::Run {
                ruleset,
                limit,
                until,
            })
        }
        "print-size" => {
            ws(input)?;
            let op = if input.starts_with(')') {
                None
            } else {
                Some(op_expr(input)?)
            };
            SurfaceCommand::Pass(Command::PrintSize(op))
        }
        "print-stats" => {
            ws(input)?;
            let file = if input.starts_with(":file") {
                *input = &input[":file".len()..];
                let quoted = parse_quoted_string(input)?;
                // `parse_quoted_string` keeps the surrounding quotes; the path does not.
                Some(quoted[1..quoted.len() - 1].to_owned())
            } else {
                None
            };
            SurfaceCommand::Pass(Command::PrintStats(file))
        }
        "check" => {
            ws(input)?;
            let cmd = if input.starts_with("(!=") || input.starts_with("( !=") {
                cut_char(input, '(')?;
                ws(input)?;
                *input = &input[2..];
                let a = parse_term_inner(input, base)?;
                let b = parse_term_inner(input, base)?;
                cut_char(input, ')')?;
                Command::CheckNeq(a, b)
            } else if input.starts_with("(=") || input.starts_with("( =") {
                cut_char(input, '(')?;
                ws(input)?;
                if !input.starts_with('=') {
                    let mut e = ContextError::new();
                    e.push(StrContext::Expected(StrContextValue::CharLiteral('=')));
                    return Err(ErrMode::Cut(e));
                }
                *input = &input[1..];
                let a = parse_term_inner(input, base)?;
                let b = parse_term_inner(input, base)?;
                cut_char(input, ')')?;
                Command::CheckEq(a, b)
            } else {
                let t = parse_term_inner(input, base)?;
                Command::Check(t)
            };
            SurfaceCommand::Pass(cmd)
        }
        "push" => {
            ws.parse_next(input).ok();
            let shrink = input.starts_with(":shrink");
            if shrink {
                *input = &input[7..];
            }
            SurfaceCommand::Pass(Command::Push(shrink))
        }
        "pop" => SurfaceCommand::Pass(Command::Pop),
        "extract" => {
            let t = parse_term_inner(input, base)?;
            SurfaceCommand::Pass(Command::Extract(t))
        }
        "checkau" => {
            ws(input)?;
            let left = parse_term_inner(input, base)?;
            ws(input)?;
            let right = parse_term_inner(input, base)?;
            let mut max_size = u32::MAX;
            let mut playouts = 1000u64;
            let mut algorithm = "uct".to_string();
            let mut cycle_mode = "sides".to_string();
            loop {
                ws(input)?;
                if input.starts_with(')') {
                    break;
                }
                if input.starts_with(":max_size") {
                    *input = &input[":max_size".len()..];
                    let n = number(input)?;
                    max_size = u32::try_from(n).map_err(|_| {
                        let mut e = ContextError::new();
                        e.push(StrContext::Expected(StrContextValue::Description(
                            "checkau :max_size fitting in u32",
                        )));
                        ErrMode::Cut(e)
                    })?;
                } else if input.starts_with(":playouts") {
                    *input = &input[":playouts".len()..];
                    playouts = number(input)?;
                } else if input.starts_with(":algorithm") {
                    *input = &input[":algorithm".len()..];
                    algorithm = ident(input)?.to_string();
                } else if input.starts_with(":cycles") {
                    *input = &input[":cycles".len()..];
                    cycle_mode = kw_token(input)?.to_string();
                } else {
                    break;
                }
            }
            SurfaceCommand::Pass(Command::CheckAu {
                left,
                right,
                max_size,
                playouts,
                algorithm,
                cycle_mode,
            })
        }
        "antiunify" => {
            ws(input)?;
            let left = parse_term_inner(input, base)?;
            ws(input)?;
            let right = parse_term_inner(input, base)?;
            let mut playouts = 1000u64;
            let mut algorithm = "uct".to_string();
            let mut cycle_mode = "sides".to_string();
            loop {
                ws(input)?;
                if input.starts_with(')') {
                    break;
                }
                if input.starts_with(":playouts") {
                    *input = &input[":playouts".len()..];
                    playouts = number(input)?;
                } else if input.starts_with(":algorithm") {
                    *input = &input[":algorithm".len()..];
                    algorithm = ident(input)?.to_string();
                } else if input.starts_with(":cycles") {
                    *input = &input[":cycles".len()..];
                    cycle_mode = kw_token(input)?.to_string();
                } else {
                    break;
                }
            }
            SurfaceCommand::Pass(Command::AntiUnify {
                left,
                right,
                playouts,
                algorithm,
                cycle_mode,
            })
        }
        _ => {
            // Ground term insertion: (op args...)
            let mut children = Vec::new();
            loop {
                ws(input)?;
                if input.starts_with(')') {
                    break;
                }
                children.push(parse_term_inner(input, base)?);
            }
            let cmd = SurfaceCommand::Pass(Command::Insert(Term::App {
                op: kw.to_owned(),
                children,
                span: span_of(base, start, input),
            }));
            cut_char(input, ')')?;
            return Ok(cmd);
        }
    };
    cut_char(input, ')')?;
    Ok(cmd)
}

/// Parse a declaration's tag list: the composable algebra tags plus the two extraction tags
/// (`:cost n`, `:unextractable`). Loops until no tag keyword matches, so tags combine freely
/// and in any order (`:assoc :comm :cost 3`). Longer keywords are tried before their prefixes
/// (`:assoc-comm-idem` before `:assoc-comm` before `:assoc`). The pre-combined `:assoc-comm` /
/// `:assoc-comm-idem` are accepted as aliases that expand into the basic tags. Value-taking tags
/// parse a following argument. `base` is the source-start pointer for `:identity`'s term spans.
///
/// The returned `OpMeta` has `is_constructor: false`; the caller sets it, since that comes from
/// the declaration keyword (`constructor` / `datatype`), not from a tag.
fn parse_decl_tags(input: &mut &str, base: usize) -> ModalResult<(Vec<AlgTag>, OpMeta)> {
    let mut tags = Vec::new();
    let mut meta = OpMeta::default();
    loop {
        ws_inner(input);
        // Extraction tags first: neither prefixes nor is prefixed by an algebra tag.
        if input.starts_with(":cost") {
            *input = &input[":cost".len()..];
            let n = number(input)?;
            meta.cost = u32::try_from(n).map_err(|_| {
                let mut e = ContextError::new();
                e.push(StrContext::Expected(StrContextValue::Description(
                    ":cost must fit in u32",
                )));
                ErrMode::Cut(e)
            })?;
            continue;
        }
        if input.starts_with(":unextractable") {
            *input = &input[":unextractable".len()..];
            meta.unextractable = true;
            continue;
        }
        // Alias expansion first (longest match), then basic tags.
        if input.starts_with(":assoc-comm-idem") {
            *input = &input[":assoc-comm-idem".len()..];
            tags.push(AlgTag::Assoc);
            tags.push(AlgTag::Comm);
            tags.push(AlgTag::Idempotent);
        } else if input.starts_with(":assoc-comm") {
            *input = &input[":assoc-comm".len()..];
            tags.push(AlgTag::Assoc);
            tags.push(AlgTag::Comm);
        } else if input.starts_with(":assoc-left") {
            *input = &input[":assoc-left".len()..];
            tags.push(AlgTag::AssocLeft);
        } else if input.starts_with(":assoc-right") {
            *input = &input[":assoc-right".len()..];
            tags.push(AlgTag::AssocRight);
        } else if input.starts_with(":assoc") {
            *input = &input[":assoc".len()..];
            tags.push(AlgTag::Assoc);
        } else if input.starts_with(":comm") {
            *input = &input[":comm".len()..];
            tags.push(AlgTag::Comm);
        } else if input.starts_with(":idempotent") {
            *input = &input[":idempotent".len()..];
            tags.push(AlgTag::Idempotent);
        } else if input.starts_with(":nilpotent") {
            *input = &input[":nilpotent".len()..];
            // Optional integer order (default 2). Only consume a number if one follows.
            ws_inner(input);
            let order = if input.starts_with(|c: char| c.is_ascii_digit()) {
                let n = number(input)?;
                if !(2..=255).contains(&n) {
                    let mut e = ContextError::new();
                    e.push(StrContext::Expected(StrContextValue::Description(
                        ":nilpotent order must be 2..=255",
                    )));
                    return Err(ErrMode::Cut(e));
                }
                Some(n as u8)
            } else {
                None
            };
            // `Option<u8>`: the ORDER is optional surface syntax — bare `:nilpotent`
            // means order 2 (the resolver's `unwrap_or(2)`); `:nilpotent 3` is explicit.
            // It is a number, not a term: the order is the modulus of the count clamp,
            // never an e-graph entity (see `registry::Clamp::Nilpotent`).
            tags.push(AlgTag::Nilpotent(order));
        } else if input.starts_with(":identity") {
            *input = &input[":identity".len()..];
            // A ground term of the op's return sort (`:identity 0`, `:identity (zero)`).
            let term = parse_term_inner(input, base)?;
            tags.push(AlgTag::Identity(term));
        } else if input.starts_with(":cancellative") {
            *input = &input[":cancellative".len()..];
            tags.push(AlgTag::Cancellative);
        } else if input.starts_with(":inverse") {
            *input = &input[":inverse".len()..];
            let name = ident(input)?.to_owned();
            tags.push(AlgTag::Inverse(name));
        } else {
            break;
        }
    }
    Ok((tags, meta))
}

fn ws_inner(input: &mut &str) {
    while let Some(pos) = input.find(|c: char| !c.is_whitespace()) {
        if input.as_bytes()[pos] == b';' {
            *input = &input[pos..];
            if let Some(nl) = input.find('\n') {
                *input = &input[nl..];
            } else {
                *input = "";
                return;
            }
        } else {
            *input = &input[pos..];
            return;
        }
    }
    *input = "";
}

// ── Entry point ──

pub fn parse_program_v2(input: &str) -> Result<Vec<SurfaceCommand>, ParseError> {
    let base = input.as_ptr() as usize;
    let mut rest = input;
    let mut cmds = Vec::new();
    let mut desugared = Vec::new();
    loop {
        ws(&mut rest).map_err(|e| format!("{e}"))?;
        if rest.is_empty() {
            break;
        }
        desugared.clear();
        let cmd = parse_command(&mut rest, base, &mut desugared).map_err(|e| format!("{e}"))?;
        cmds.push(cmd);
        cmds.append(&mut desugared);
    }
    Ok(cmds)
}

/// Parse one or more patterns from a string. Spans are relative to `input`.
pub fn parse_patterns(input: &str) -> Result<Vec<SurfacePattern>, ParseError> {
    let base = input.as_ptr() as usize;
    let mut rest = input;
    let mut pats = Vec::new();
    loop {
        ws(&mut rest).map_err(|e| format!("{e}"))?;
        if rest.is_empty() {
            break;
        }
        pats.push(parse_pattern(&mut rest, base).map_err(|e| format!("{e}"))?);
    }
    Ok(pats)
}

#[cfg(test)]
mod alg_tag_tests {
    use super::*;

    /// Parse a single `(function ...)` decl and return its tag set.
    fn tags_of(src: &str) -> Vec<AlgTag> {
        let cmds = parse_program_v2(src).expect("parse");
        match &cmds[0] {
            SurfaceCommand::Pass(Command::Function { tags, .. }) => tags.clone(),
            other => panic!("expected function decl, got {other:?}"),
        }
    }

    #[test]
    fn no_tags() {
        assert_eq!(tags_of("(function f (E E) E)"), vec![]);
    }

    #[test]
    fn basic_tags_compose() {
        assert_eq!(
            tags_of("(function add (E) E :assoc :comm)"),
            vec![AlgTag::Assoc, AlgTag::Comm]
        );
        assert_eq!(
            tags_of("(function and (E) E :assoc :comm :idempotent)"),
            vec![AlgTag::Assoc, AlgTag::Comm, AlgTag::Idempotent]
        );
    }

    #[test]
    fn aliases_expand_to_basic_tags() {
        assert_eq!(
            tags_of("(function add (E) E :assoc-comm)"),
            vec![AlgTag::Assoc, AlgTag::Comm]
        );
        assert_eq!(
            tags_of("(function and (E) E :assoc-comm-idem)"),
            vec![AlgTag::Assoc, AlgTag::Comm, AlgTag::Idempotent]
        );
    }

    #[test]
    fn assoc_direction() {
        assert_eq!(
            tags_of("(function sub (E) E :assoc-left)"),
            vec![AlgTag::AssocLeft]
        );
        assert_eq!(
            tags_of("(function sub (E) E :assoc-right)"),
            vec![AlgTag::AssocRight]
        );
    }

    #[test]
    fn nilpotent_optional_order() {
        assert_eq!(
            tags_of("(function xor (E) E :assoc :comm :nilpotent)"),
            vec![AlgTag::Assoc, AlgTag::Comm, AlgTag::Nilpotent(None)]
        );
        assert_eq!(
            tags_of("(function x3 (E) E :assoc :comm :nilpotent 3)"),
            vec![AlgTag::Assoc, AlgTag::Comm, AlgTag::Nilpotent(Some(3))]
        );
    }

    #[test]
    fn identity_literal_and_ctor() {
        // literal unit
        match &tags_of("(function add (E) E :assoc :comm :identity 0)")[2] {
            AlgTag::Identity(Term::Lit(tok, _)) => assert_eq!(tok, "0"),
            other => panic!("expected Identity(Lit), got {other:?}"),
        }
        // constructed unit
        match &tags_of("(function add (E) E :assoc :comm :identity (zero))")[2] {
            AlgTag::Identity(Term::App { op, .. }) => assert_eq!(op, "zero"),
            other => panic!("expected Identity(App), got {other:?}"),
        }
    }

    /// Parse a single declaration and return its `OpMeta`.
    fn meta_of(src: &str) -> OpMeta {
        let cmds = parse_program_v2(src).expect("parse");
        match &cmds[0] {
            SurfaceCommand::Pass(Command::Function { meta, .. }) => *meta,
            other => panic!("expected function/constructor decl, got {other:?}"),
        }
    }

    #[test]
    fn function_is_not_a_constructor() {
        assert_eq!(meta_of("(function f (E E) E)"), OpMeta::default());
    }

    #[test]
    fn constructor_sets_the_flag() {
        let m = meta_of("(constructor f (E E) E)");
        assert!(m.is_constructor);
        assert_eq!(m.cost, 1);
        assert!(!m.unextractable);
    }

    #[test]
    fn extraction_tags_parse_and_mix_with_algebra_tags() {
        let m = meta_of("(constructor add (E) E :cost 7 :assoc :comm :unextractable)");
        assert!(m.is_constructor);
        assert_eq!(m.cost, 7);
        assert!(m.unextractable);
        assert_eq!(
            tags_of("(constructor add (E) E :cost 7 :assoc :comm :unextractable)"),
            vec![AlgTag::Assoc, AlgTag::Comm]
        );
    }

    #[test]
    fn datatype_variants_are_constructors() {
        let cmds = parse_program_v2("(datatype M (Num) (Add M M :cost 4))").expect("parse");
        let SurfaceCommand::Pass(Command::Datatype { variants, .. }) = &cmds[0] else {
            panic!("expected datatype");
        };
        assert!(variants.iter().all(|v| v.meta.is_constructor));
        assert_eq!(variants[0].meta.cost, 1);
        assert_eq!(variants[1].meta.cost, 4);
    }

    #[test]
    fn birewrite_expands_to_two_rewrites() {
        let cmds = parse_program_v2("(birewrite (f x) (g x) :ruleset r)").expect("parse");
        assert_eq!(cmds.len(), 2);
        let ops = |c: &SurfaceCommand| match c {
            SurfaceCommand::Rewrite {
                lhs, rhs, ruleset, ..
            } => {
                let l = match lhs {
                    SurfacePattern::App { op, .. } => op.clone(),
                    other => panic!("expected app lhs, got {other:?}"),
                };
                let r = match rhs {
                    RhsTerm::App { op, .. } => op.clone(),
                    other => panic!("expected app rhs, got {other:?}"),
                };
                (l, r, ruleset.clone())
            }
            other => panic!("expected rewrite, got {other:?}"),
        };
        assert_eq!(
            ops(&cmds[0]),
            ("f".into(), "g".into(), Some("r".to_string()))
        );
        assert_eq!(
            ops(&cmds[1]),
            ("g".into(), "f".into(), Some("r".to_string()))
        );
    }

    #[test]
    fn run_forms() {
        let one = |src: &str| match &parse_program_v2(src).expect("parse")[0] {
            SurfaceCommand::Pass(Command::Run {
                ruleset,
                limit,
                until,
            }) => (ruleset.clone(), *limit, until.clone()),
            other => panic!("expected run, got {other:?}"),
        };
        assert_eq!(one("(run 12)"), (None, 12, None));
        assert_eq!(one("(run fast 3)"), (Some("fast".to_string()), 3, None));
        let (rs, limit, until) = one("(run fast 3 :until (!= a b))");
        assert_eq!((rs, limit), (Some("fast".to_string()), 3));
        assert!(!until.expect("goal").equal);
        assert!(one("(run 5 :until (= a b))").2.expect("goal").equal);
    }

    #[test]
    fn stats_commands_lex_their_hyphenated_keywords() {
        let cmds = parse_program_v2(
            "(print-size) (print-size Add) (print-stats) (print-stats :file \"x.json\")",
        )
        .expect("parse");
        assert!(matches!(
            &cmds[0],
            SurfaceCommand::Pass(Command::PrintSize(None))
        ));
        assert!(
            matches!(&cmds[1], SurfaceCommand::Pass(Command::PrintSize(Some(op))) if op == "Add")
        );
        assert!(matches!(
            &cmds[2],
            SurfaceCommand::Pass(Command::PrintStats(None))
        ));
        assert!(
            matches!(&cmds[3], SurfaceCommand::Pass(Command::PrintStats(Some(p))) if p == "x.json")
        );
    }

    #[test]
    fn inverse_names_op() {
        assert_eq!(
            tags_of("(function add (E) E :assoc :comm :identity 0 :inverse neg)")
                .into_iter()
                .filter(|t| matches!(t, AlgTag::Inverse(_)))
                .collect::<Vec<_>>(),
            vec![AlgTag::Inverse("neg".to_string())]
        );
    }
}
