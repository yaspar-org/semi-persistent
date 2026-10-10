// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0
//! Print the ASP dump of one AC node of three leaves at a rung: `lpdump RUNG`.
use semi_persistent_egraph::extraction::graph::{Graph, Kind, Node};
use semi_persistent_egraph::extraction::rung::RungKind;
fn main() {
    let rung = RungKind::parse(&std::env::args().nth(1).unwrap_or("selection".into())).unwrap();
    let k = 3;
    let mut g = Graph {
        nodes: Vec::new(),
        classes: vec![Vec::new(); k + 1],
        root: k,
    };
    for c in 0..k {
        g.nodes.push(Node {
            op: "Var".into(),
            ints: vec![],
            strings: vec![],
            children: vec![],
            class: c,
            kind: Kind::Plain,
            mults: Vec::new(),
            subsumed: false,
        });
        g.classes[c].push(c);
    }
    g.nodes.push(Node {
        op: "Op".into(),
        ints: vec![],
        strings: vec![],
        children: (0..k).collect(),
        class: k,
        kind: Kind::MSet,
        mults: Vec::new(),
        subsumed: false,
    });
    g.classes[k].push(k);
    print!("{}", semi_persistent_egraph::extraction::lp::dump(&g, rung));
}
