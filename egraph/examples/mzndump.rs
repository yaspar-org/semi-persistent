// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0
//! Write the MiniZinc dump of a Semper `dump-egraph` file, with a criteria file
//! appended: `mzndump DUMP.json RUNG CRITERIA.mzn > OUT.mzn`.
use semi_persistent_egraph::extraction::graph::{Graph, Kind, Node};
use semi_persistent_egraph::extraction::rung::RungKind;
use std::collections::BTreeMap;
fn load(path: &str) -> Graph {
    let v: serde_json::Value =
        serde_json::from_str(&std::fs::read_to_string(path).unwrap()).unwrap();
    let nodes = v["nodes"].as_object().unwrap();
    let is_e = |c: &str| c.starts_with("E-");
    let mut class_ix: BTreeMap<String, usize> = BTreeMap::new();
    for (_, n) in nodes {
        let c = n["eclass"].as_str().unwrap();
        if is_e(c) {
            let len = class_ix.len();
            class_ix.entry(c.to_string()).or_insert(len);
        }
    }
    let mut g = Graph {
        classes: vec![Vec::new(); class_ix.len()],
        ..Default::default()
    };
    for (_, n) in nodes {
        let c = n["eclass"].as_str().unwrap();
        if !is_e(c) {
            continue;
        }
        let children: Vec<usize> = n["children"]
            .as_array()
            .unwrap()
            .iter()
            .map(|k| nodes[k.as_str().unwrap()]["eclass"].as_str().unwrap())
            .filter(|k| is_e(k))
            .map(|k| class_ix[k])
            .collect();
        let op = n["op"].as_str().unwrap().to_string();
        let kind = if op == "Add" || op == "Mul" {
            Kind::MSet
        } else {
            Kind::Plain
        };
        let class = class_ix[c];
        g.classes[class].push(g.nodes.len());
        g.nodes.push(Node {
            op,
            ints: vec![],
            strings: vec![],
            children,
            mults: Vec::new(),
            class,
            kind,
            subsumed: n["subsumed"].as_bool().unwrap_or(false),
        });
    }
    g.root = class_ix[v["root_eclasses"][0].as_str().unwrap()];
    g
}

fn main() {
    let a: Vec<String> = std::env::args().collect();
    let g = load(&a[1]);
    let rung = RungKind::parse(&a[2]).unwrap();
    let criteria = std::fs::read_to_string(&a[3]).unwrap();
    print!(
        "{}\n{criteria}\n",
        semi_persistent_egraph::extraction::mzn::dump(&g, rung)
    );
}
