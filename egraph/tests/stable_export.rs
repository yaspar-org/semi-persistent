// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0
//! Step 2 of `doc/goal-stable-extraction.md`: `dump-egraph` names and orders by content,
//! so one e-graph built in two node orders exports the same bytes.

use semi_persistent_egraph::interpret::Interpreter;
use semi_persistent_egraph::model::{MachineLit, MachineModel};

type Cfg = semi_persistent_egraph::nodes::DefaultConfig;
type Interp = Interpreter<Cfg, MachineLit, MachineModel, true, false>;

const DECLS: &str = "(sort E)
(function a () E)
(function b () E)
(function c () E)
(function P0 () E)
(function P1 () E)
(function F (E) E)
(function G (E) E)
(function K (E E) E)
(function Plus (E) E :assoc-comm)
(function And (E) E :assoc-comm-idem)
(function Cat (E) E :assoc)
";

fn build(body: &str) -> Interp {
    let src = format!("{DECLS}{body}");
    let cmds = semi_persistent_egraph::parser::parse_program_v2(&src).expect("parse");
    let mut it: Interp = Interpreter::new(MachineModel);
    let mut sg = semi_persistent_egraph::resolve::GlobalCtx::new();
    let checked =
        semi_persistent_egraph::sortcheck::sortcheck_program(cmds, &mut it.eg, &it.model, &mut sg)
            .unwrap_or_else(|e| panic!("sortcheck: {e}\n{src}"));
    it.run_checked(&checked)
        .unwrap_or_else(|e| panic!("run: {e}\n{src}"));
    it.eg.rebuild();
    it
}

/// The dump with `root` the class of global `r`.
fn dump(it: &mut Interp) -> (String, semi_persistent_egraph::dump::DumpStats) {
    let (root, _) = it.global("r").expect("a global r");
    it.eg.to_egraph_json(root)
}

struct Rng(u64);
impl Rng {
    fn next(&mut self) -> u64 {
        self.0 = self
            .0
            .wrapping_mul(6364136223846793005)
            .wrapping_add(1442695040888963407);
        self.0 >> 33
    }
    fn below(&mut self, n: usize) -> usize {
        usize::try_from(self.next()).unwrap_or(0) % n
    }
}

const LEAVES: &[&str] = &["(a)", "(b)", "(c)", "p0", "p1"];

/// A random term of depth at most `d`.
fn term(rng: &mut Rng, d: usize) -> String {
    if d == 0 || rng.below(3) == 0 {
        return LEAVES[rng.below(LEAVES.len())].to_string();
    }
    let k = 1 + rng.below(3);
    let kids: Vec<String> = (0..k).map(|_| term(rng, d - 1)).collect();
    match rng.below(6) {
        0 => format!("(F {})", kids[0]),
        1 => format!("(G {})", kids[0]),
        2 => format!("(K {} {})", kids[0], kids.get(1).unwrap_or(&kids[0])),
        3 => format!("(Plus {})", kids.join(" ")),
        4 => format!("(And {})", kids.join(" ")),
        _ => format!("(Cat {})", kids.join(" ")),
    }
}

/// The multiset of class colours: equal for two runs exactly when `dump_canon.py` calls
/// their e-graphs equal (step 1).
fn content(it: &Interp) -> Vec<semi_persistent_egraph::canon_colour::Colour> {
    let mut v = it.eg.canon_colours().class_colour;
    v.sort_unstable();
    v
}

/// One program, built with its `let`s in two orders: every node id differs between the
/// two. Where the two e-graphs have the same content, the dumps are equal byte for byte.
/// (With unions over AC terms, build order can change the content itself: the nested
/// and flat spellings of one ACI content are not merged while AC completion is off.)
#[test]
fn one_egraph_in_two_node_orders_dumps_the_same_bytes() {
    let mut rng = Rng(0x57ab_1e00);
    let (mut same_content, mut differing_ids, mut cases) = (0, 0, 0);
    for _ in 0..300 {
        let n = 3 + rng.below(6);
        let lets: Vec<String> = (0..n)
            .map(|i| format!("(let t{i} {})\n", term(&mut rng, 3)))
            .collect();
        let unions: String = (0..rng.below(3))
            .map(|_| format!("(union t{} t{})\n", rng.below(n), rng.below(n)))
            .collect();
        let head = "(let p0 (P0))\n(let p1 (P1))\n";
        let forward = format!("{head}{}{unions}(let r t0)\n", lets.concat());
        let mut rev = lets.clone();
        rev.reverse();
        let backward = format!("{head}{}{unions}(let r t0)\n", rev.concat());
        let (mut x, mut y) = (build(&forward), build(&backward));
        cases += 1;
        let order = |it: &Interp| -> Vec<String> {
            it.eg
                .node_ids()
                .map(|id| it.eg.node_op_name(id).to_string())
                .collect()
        };
        let ((dx, sx), (dy, sy)) = (dump(&mut x), dump(&mut y));
        assert_eq!(
            sx.symmetric_groups, 0,
            "a rebuilt graph has symmetric classes\n{forward}"
        );
        assert_eq!(sy.symmetric_groups, 0);
        if content(&x) != content(&y) {
            continue;
        }
        same_content += 1;
        if order(&x) != order(&y) {
            differing_ids += 1;
        }
        assert_eq!(dx, dy, "one e-graph, two dumps\n{forward}");
    }
    // The comparison is not vacuous: most cases have one content and different ids.
    assert!(
        same_content > cases / 2,
        "{same_content} of {cases} cases share content"
    );
    assert!(
        differing_ids > same_content / 2,
        "{differing_ids} of {same_content} cases differ in ids"
    );
    eprintln!(
        "{cases} programs: {same_content} with one content, {differing_ids} of them in different ids"
    );
}

/// The node lines of a dump: `(name, op, children, eclass)`. The dump writes one node
/// per line, so a line scan reads it without a JSON parser.
fn node_lines(json: &str) -> Vec<(String, String, Vec<String>, String)> {
    let field = |line: &str, key: &str| -> String {
        let pat = format!("\"{key}\": \"");
        line.find(&pat)
            .map(|i| &line[i + pat.len()..])
            .and_then(|rest| rest.split('"').next())
            .unwrap_or("")
            .to_string()
    };
    json.lines()
        .filter(|l| l.contains("\"eclass\""))
        .map(|l| {
            let name = l
                .trim()
                .trim_start_matches('"')
                .split('"')
                .next()
                .unwrap_or("")
                .to_string();
            let kids = l
                .find("\"children\": [")
                .map(|i| &l[i + 13..])
                .and_then(|rest| rest.split(']').next())
                .unwrap_or("")
                .split(',')
                .map(|k| k.trim().trim_matches('"').to_string())
                .filter(|k| !k.is_empty())
                .collect();
            (name, field(l, "op"), kids, field(l, "eclass"))
        })
        .collect()
}

/// Names are content: the dump names no node or class by its id, and each class is
/// named by the colour `class_data` records for it.
#[test]
fn names_are_colours() {
    let mut it = build("(let r (Plus (a) (b) (F (a))))\n");
    let (json, _) = dump(&mut it);
    let nodes = node_lines(&json);
    assert!(!nodes.is_empty());
    for (name, _, _, class) in &nodes {
        let hex = name
            .strip_prefix('n')
            .and_then(|s| s.split('-').next())
            .expect("a node name");
        assert_eq!(hex.len(), 32, "{name}");
        assert!(hex.chars().all(|c| c.is_ascii_hexdigit()), "{name}");
        let colour = class.rsplit('-').next().unwrap_or("");
        assert!(
            json.contains(&format!(
                "\"{class}\": {{\"type\": \"E\", \"colour\": \"{colour}\"}}"
            )),
            "{class} is not named by its colour"
        );
    }
}

/// An AC node's children are written in name order: `Plus(b, a)` and `Plus(a, b)` are one
/// node, and its children read the same however the classes were numbered.
#[test]
fn ac_children_are_in_name_order() {
    let mut x = build("(let q (b))\n(let p (a))\n(let r (Plus p q))\n");
    let mut y = build("(let p (a))\n(let q (b))\n(let r (Plus q p))\n");
    assert_eq!(dump(&mut x).0, dump(&mut y).0);
    let (json, _) = dump(&mut x);
    let plus: Vec<Vec<String>> = node_lines(&json)
        .into_iter()
        .filter(|(_, op, _, _)| op == "Plus")
        .map(|(_, _, kids, _)| kids)
        .collect();
    assert_eq!(plus.len(), 1);
    for kids in plus {
        assert_eq!(kids.len(), 2);
        let mut sorted = kids.clone();
        sorted.sort_unstable();
        assert_eq!(kids, sorted);
    }
}

/// An AC child is written once with its multiplicity in `"mults"`, parallel to
/// `"children"`: `Plus(a, a, b)` has two children, counted 2 and 1, not three.
#[test]
fn an_ac_child_is_written_once_with_its_count() {
    let mut it = build("(let r (Plus (a) (a) (b)))\n");
    let (json, _) = dump(&mut it);
    let line = json
        .lines()
        .find(|l| l.contains("\"op\": \"Plus\""))
        .expect("a Plus node");
    let (_, _, kids, _) = node_lines(line).into_iter().next().expect("one node line");
    assert_eq!(kids.len(), 2, "{line}");
    let mults = line
        .split("\"mults\": [")
        .nth(1)
        .and_then(|r| r.split(']').next())
        .expect("a mults field");
    let mut counts: Vec<u64> = mults.split(", ").map(|m| m.parse().unwrap()).collect();
    counts.sort_unstable();
    assert_eq!(counts, vec![1, 2], "{line}");
    // A node of another kind carries no counts.
    assert!(
        json.lines()
            .filter(|l| l.contains("\"op\": \"a\""))
            .all(|l| !l.contains("mults")),
        "{json}"
    );
}

/// Bug #9: `DumpStats.nodes` counted the congruent duplicate the dump omits, 4 where the
/// dump wrote 3. After `(union (a) (b))`, `(F (a))` and `(F (b))` are congruent and one
/// is written; the count is the nodes the dump holds.
#[test]
fn the_node_count_is_the_nodes_written() {
    let mut it = build("(let r (K (F (a)) (F (b))))\n(union (a) (b))\n");
    let (json, stats) = dump(&mut it);
    // One `"op":` per node entry (`dump.rs`'s format); classes carry no `op`.
    let written = json.matches("\"op\":").count();
    assert_eq!(stats.nodes, written, "{json}");
    assert!(
        it.eg.len() > written,
        "the e-graph holds the duplicate the dump omits"
    );
}
