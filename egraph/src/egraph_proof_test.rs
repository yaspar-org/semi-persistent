// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0
#[cfg(test)]
mod test {
    use crate::egraph::EGraph31;
    use crate::id::ENodeId;
    use crate::literal::NiraLitVal;
    use crate::union_find::{Justification, ProofBuf};

    #[test]
    fn long_proof_chain() {
        let mut eg = EGraph31::<NiraLitVal, false, true>::new();
        let int = eg.intern_sort("Int");

        let mut ops = Vec::new();
        for i in 0..20 {
            ops.push(eg.register_op0(&format!("c{i}"), int));
        }
        let nodes: Vec<ENodeId> = ops.iter().map(|&op| eg.add(op, &[])).collect();

        for i in 0..19 {
            eg.merge_justified(
                nodes[i],
                nodes[i + 1],
                Justification::Axiom {
                    axiom_id: crate::id::AxiomId::new(i as u16),
                },
            );
        }

        let mut buf = ProofBuf::new();
        eg.explain(nodes[0], nodes[19], &mut buf);
        eprintln!("\nc0 ≡ c19 ({} steps):", buf.steps.len());
        for (from, to, just) in &buf.steps {
            eprintln!("  {:?} ≡ {:?}  by {:?}", from, to, just);
        }
        assert_eq!(buf.steps.len(), 19);
    }

    #[test]
    fn layered_congruence_proof() {
        let mut eg = EGraph31::<NiraLitVal, false, true>::new();
        let int = eg.intern_sort("Int");
        let f = eg.register_op1("f", int, int);
        let g = eg.register_op2("g", int, int, int);

        // Layer 0: 8 constants
        let mut c = Vec::new();
        for i in 0..8 {
            let op = eg.register_op0(&format!("c{i}"), int);
            c.push(eg.add(op, &[]));
        }

        // Layer 1: f(ci)
        let fc: Vec<_> = c.iter().map(|&x| eg.add(f, &[x])).collect();

        // Layer 2: g(f(c2i), f(c2i+1))
        let gfc: Vec<_> = (0..4)
            .map(|i| eg.add(g, &[fc[2 * i], fc[2 * i + 1]]))
            .collect();

        // Merge pairs at layer 0: c0≡c2, c1≡c3, c4≡c6, c5≡c7
        eg.merge_justified(
            c[0],
            c[2],
            Justification::Axiom {
                axiom_id: crate::id::AxiomId::new(0),
            },
        );
        eg.merge_justified(
            c[1],
            c[3],
            Justification::Axiom {
                axiom_id: crate::id::AxiomId::new(1),
            },
        );
        eg.merge_justified(
            c[4],
            c[6],
            Justification::Axiom {
                axiom_id: crate::id::AxiomId::new(2),
            },
        );
        eg.merge_justified(
            c[5],
            c[7],
            Justification::Axiom {
                axiom_id: crate::id::AxiomId::new(3),
            },
        );
        eg.rebuild();

        // Layer 1 congruences
        assert_eq!(eg.find(fc[0]), eg.find(fc[2]));
        assert_eq!(eg.find(fc[1]), eg.find(fc[3]));
        // Layer 2 congruences
        assert_eq!(eg.find(gfc[0]), eg.find(gfc[1]));
        assert_eq!(eg.find(gfc[2]), eg.find(gfc[3]));
        // But left half ≢ right half yet
        assert_ne!(eg.find(gfc[0]), eg.find(gfc[2]));

        // Bridge: c0≡c4, c1≡c5 — cascades all the way up
        eg.merge_justified(
            c[0],
            c[4],
            Justification::Axiom {
                axiom_id: crate::id::AxiomId::new(4),
            },
        );
        eg.merge_justified(
            c[1],
            c[5],
            Justification::Axiom {
                axiom_id: crate::id::AxiomId::new(5),
            },
        );
        eg.rebuild();

        // Now everything collapses
        assert_eq!(eg.find(gfc[0]), eg.find(gfc[2]));

        // Print proofs at each layer
        let mut buf = ProofBuf::new();
        let proofs = [
            ("c0 ≡ c6 (layer 0, chain)", c[0], c[6]),
            ("f(c0) ≡ f(c2) (layer 1, congruence)", fc[0], fc[2]),
            ("f(c1) ≡ f(c7) (layer 1, cross)", fc[1], fc[7]),
            ("g(f(c0),f(c1)) ≡ g(f(c2),f(c3)) (layer 2)", gfc[0], gfc[1]),
            (
                "g(f(c0),f(c1)) ≡ g(f(c4),f(c5)) (layer 2, cross)",
                gfc[0],
                gfc[2],
            ),
            (
                "g(f(c0),f(c1)) ≡ g(f(c6),f(c7)) (layer 2, far)",
                gfc[0],
                gfc[3],
            ),
        ];
        for (label, a, b) in proofs {
            buf.clear();
            eg.explain(a, b, &mut buf);
            eprintln!("\n{label} ({} steps):", buf.steps.len());
            for (from, to, just) in &buf.steps {
                eprintln!("  {:?} ≡ {:?}  by {:?}", from, to, just);
            }
            assert!(!buf.steps.is_empty());
        }
    }
}

#[cfg(test)]
mod deep_proof_test {
    use crate::egraph::EGraph31;
    use crate::id::ENodeId;
    use crate::literal::NiraLitVal;
    use crate::union_find::{Justification, ProofBuf};

    /// Build a 3-layer e-graph, merge leaves, rebuild, extract deep proof.
    ///
    /// Layer 0: constants a, b, c, d
    /// Layer 1: f(a), f(b), f(c), f(d)
    /// Layer 2: g(f(a), f(b)), g(f(c), f(d))
    ///
    /// Merge a≡c (axiom 1), b≡d (axiom 2), rebuild.
    /// This cascades: f(a)≡f(c), f(b)≡f(d), then g(f(a),f(b))≡g(f(c),f(d)).
    /// Extract deep proof of g(f(a),f(b)) ≡ g(f(c),f(d)).
    #[test]
    fn deep_proof_layered() {
        let mut eg = EGraph31::<NiraLitVal, false, true>::new();
        let int = eg.intern_sort("Int");
        let f = eg.register_op1("f", int, int);
        let g = eg.register_op2("g", int, int, int);

        // Layer 0
        let op_a = eg.register_op0("a", int);
        let op_b = eg.register_op0("b", int);
        let op_c = eg.register_op0("c", int);
        let op_d = eg.register_op0("d", int);
        let a = eg.add(op_a, &[]);
        let b = eg.add(op_b, &[]);
        let c = eg.add(op_c, &[]);
        let d = eg.add(op_d, &[]);

        // Layer 1
        let fa = eg.add(f, &[a]);
        let fb = eg.add(f, &[b]);
        let fc = eg.add(f, &[c]);
        let fd = eg.add(f, &[d]);

        // Layer 2
        let gab = eg.add(g, &[fa, fb]);
        let gcd = eg.add(g, &[fc, fd]);

        assert_ne!(eg.find(gab), eg.find(gcd));

        // Merge leaves
        eg.merge_justified(
            a,
            c,
            Justification::Axiom {
                axiom_id: crate::id::AxiomId::new(1),
            },
        );
        eg.merge_justified(
            b,
            d,
            Justification::Axiom {
                axiom_id: crate::id::AxiomId::new(2),
            },
        );
        eg.rebuild();

        // Verify cascading congruence
        assert_eq!(eg.find(fa), eg.find(fc));
        assert_eq!(eg.find(fb), eg.find(fd));
        assert_eq!(eg.find(gab), eg.find(gcd));

        // Extract deep proof
        let mut buf = ProofBuf::new();
        assert!(eg.explain_deep(gab, gcd, &mut buf));

        // Print proof
        let name = |id: ENodeId| -> String { eg.node_op_name(id).to_string() };
        eprintln!("\n=== Deep proof: g(f(a),f(b)) ≡ g(f(c),f(d)) ===");
        eprintln!("{} steps:", buf.steps.len());
        for (i, (from, to, just)) in buf.steps.iter().enumerate() {
            let reason = match just {
                Justification::Axiom { axiom_id } => format!("axiom #{axiom_id}"),
                Justification::Congruence { node_a, node_b } => {
                    let na = *node_a;
                    let nb = *node_b;
                    format!("congruence({}, {})", name(na), name(nb))
                }
                Justification::Rewrite { rule_id, .. } => format!("rewrite #{rule_id}"),
                Justification::Filler => unreachable!("filler is never a real proof step"),
            };
            eprintln!("  [{i}] {} ≡ {}  by {reason}", name(*from), name(*to));
        }

        // Must contain at least one Congruence step (the g-level merge)
        assert!(
            buf.steps
                .iter()
                .any(|(_, _, j)| matches!(j, Justification::Congruence { .. }))
        );
        // Must contain axiom steps (the leaf merges, expanded from congruence children)
        assert!(
            buf.steps
                .iter()
                .any(|(_, _, j)| matches!(j, Justification::Axiom { .. }))
        );

        eprintln!("\n✓ Deep proof extracted successfully");
    }
}

#[cfg(test)]
mod kind_proof_tests {
    use crate::egraph::EGraph31;
    use crate::id::{ENodeId, OpId};
    use crate::literal::NiraLitVal;
    use crate::union_find::{Justification, ProofBuf};

    struct Th {
        x: OpId,
        y: OpId,
        z: OpId,
        w: OpId,
        f: OpId,
        g: OpId,
        eq: OpId,   // C
        sub: OpId,  // A
        plus: OpId, // AC
        and: OpId,  // ACI
    }

    fn setup() -> (EGraph31<NiraLitVal, false, true>, Th) {
        let mut eg = EGraph31::new();
        let int = eg.intern_sort("Int");
        let th = Th {
            x: eg.register_op0("x", int),
            y: eg.register_op0("y", int),
            z: eg.register_op0("z", int),
            w: eg.register_op0("w", int),
            f: eg.register_op1("f", int, int),
            g: eg.register_op2("g", int, int, int),
            eq: eg.register_c("eq", [int, int], int),
            sub: eg.register_a("sub", int, int, crate::registry::AssocDir::Left),
            plus: eg.register_mset("plus", int, int),
            and: eg.register_set("and", int, int),
        };
        (eg, th)
    }

    fn has_congruence(buf: &ProofBuf<ENodeId>) -> bool {
        buf.steps
            .iter()
            .any(|(_, _, j)| matches!(j, Justification::Congruence { .. }))
    }

    fn has_axiom(buf: &ProofBuf<ENodeId>, id: u32) -> bool {
        buf.steps.iter().any(|(_, _, j)| {
            *j == Justification::Axiom {
                axiom_id: crate::id::AxiomId::new(id as u16),
            }
        })
    }

    fn print_proof(label: &str, buf: &ProofBuf<ENodeId>, eg: &EGraph31<NiraLitVal, false, true>) {
        eprintln!("\n--- {label} ({} steps) ---", buf.steps.len());
        for (i, (from, to, just)) in buf.steps.iter().enumerate() {
            let reason = match just {
                Justification::Axiom { axiom_id } => format!("axiom #{axiom_id}"),
                Justification::Congruence { node_a, node_b } => format!(
                    "congruence({}, {})",
                    eg.node_op_name(*node_a),
                    eg.node_op_name(*node_b)
                ),
                Justification::Rewrite { rule_id, .. } => format!("rewrite #{rule_id}"),
                Justification::Filler => unreachable!("filler is never a real proof step"),
            };
            eprintln!(
                "  [{i}] {} ≡ {}  by {reason}",
                eg.node_op_name(*from),
                eg.node_op_name(*to)
            );
        }
    }

    // -- Plain1: f(x) ≡ f(y) after merge(x,y) --

    #[test]
    fn proof_plain1() {
        let (ref mut eg, th) = setup();
        let x = eg.add(th.x, &[]);
        let y = eg.add(th.y, &[]);
        let fx = eg.add(th.f, &[x]);
        let fy = eg.add(th.f, &[y]);
        eg.merge_justified(
            x,
            y,
            Justification::Axiom {
                axiom_id: crate::id::AxiomId::new(10),
            },
        );
        eg.rebuild();
        assert_eq!(eg.find(fx), eg.find(fy));

        let mut buf = ProofBuf::new();
        eg.explain_deep(fx, fy, &mut buf);
        print_proof("Plain1: f(x)≡f(y)", &buf, eg);
        assert!(has_congruence(&buf));
        assert!(has_axiom(&buf, 10));
    }

    // -- Plain2: g(x,y) ≡ g(z,w) after merge(x,z), merge(y,w) --

    #[test]
    fn proof_plain2() {
        let (ref mut eg, th) = setup();
        let x = eg.add(th.x, &[]);
        let y = eg.add(th.y, &[]);
        let z = eg.add(th.z, &[]);
        let w = eg.add(th.w, &[]);
        let gxy = eg.add(th.g, &[x, y]);
        let gzw = eg.add(th.g, &[z, w]);
        eg.merge_justified(
            x,
            z,
            Justification::Axiom {
                axiom_id: crate::id::AxiomId::new(20),
            },
        );
        eg.merge_justified(
            y,
            w,
            Justification::Axiom {
                axiom_id: crate::id::AxiomId::new(21),
            },
        );
        eg.rebuild();
        assert_eq!(eg.find(gxy), eg.find(gzw));

        let mut buf = ProofBuf::new();
        eg.explain_deep(gxy, gzw, &mut buf);
        print_proof("Plain2: g(x,y)≡g(z,w)", &buf, eg);
        assert!(has_congruence(&buf));
        assert!(has_axiom(&buf, 20));
        assert!(has_axiom(&buf, 21));
    }

    // -- C: eq(x,y) ≡ eq(z,w) after merge(x,z), merge(y,w) --
    // Children are sorted, so proof must match by repr not position.

    #[test]
    fn proof_commutative() {
        let (ref mut eg, th) = setup();
        let x = eg.add(th.x, &[]);
        let y = eg.add(th.y, &[]);
        let z = eg.add(th.z, &[]);
        let w = eg.add(th.w, &[]);
        let eq_xy = eg.add(th.eq, &[x, y]);
        let eq_zw = eg.add(th.eq, &[z, w]);
        eg.merge_justified(
            x,
            z,
            Justification::Axiom {
                axiom_id: crate::id::AxiomId::new(30),
            },
        );
        eg.merge_justified(
            y,
            w,
            Justification::Axiom {
                axiom_id: crate::id::AxiomId::new(31),
            },
        );
        eg.rebuild();
        assert_eq!(eg.find(eq_xy), eg.find(eq_zw));

        let mut buf = ProofBuf::new();
        eg.explain_deep(eq_xy, eq_zw, &mut buf);
        print_proof("C: eq(x,y)≡eq(z,w)", &buf, eg);
        assert!(has_congruence(&buf));
        assert!(has_axiom(&buf, 30));
        assert!(has_axiom(&buf, 31));
    }

    // -- A: sub(x,y) ≡ sub(z,w) after merge(x,z), merge(y,w) --

    #[test]
    fn proof_associative() {
        let (ref mut eg, th) = setup();
        let x = eg.add(th.x, &[]);
        let y = eg.add(th.y, &[]);
        let z = eg.add(th.z, &[]);
        let w = eg.add(th.w, &[]);
        let sxy = eg.add(th.sub, &[x, y]);
        let szw = eg.add(th.sub, &[z, w]);
        eg.merge_justified(
            x,
            z,
            Justification::Axiom {
                axiom_id: crate::id::AxiomId::new(40),
            },
        );
        eg.merge_justified(
            y,
            w,
            Justification::Axiom {
                axiom_id: crate::id::AxiomId::new(41),
            },
        );
        eg.rebuild();
        assert_eq!(eg.find(sxy), eg.find(szw));

        let mut buf = ProofBuf::new();
        eg.explain_deep(sxy, szw, &mut buf);
        print_proof("A: sub(x,y)≡sub(z,w)", &buf, eg);
        assert!(has_congruence(&buf));
        assert!(has_axiom(&buf, 40));
        assert!(has_axiom(&buf, 41));
    }

    // -- AC: plus(x,y) ≡ plus(z,w) after merge(x,z), merge(y,w) --

    #[test]
    fn proof_ac() {
        let (ref mut eg, th) = setup();
        let x = eg.add(th.x, &[]);
        let y = eg.add(th.y, &[]);
        let z = eg.add(th.z, &[]);
        let w = eg.add(th.w, &[]);
        let pxy = eg.add(th.plus, &[x, y]);
        let pzw = eg.add(th.plus, &[z, w]);
        eg.merge_justified(
            x,
            z,
            Justification::Axiom {
                axiom_id: crate::id::AxiomId::new(50),
            },
        );
        eg.merge_justified(
            y,
            w,
            Justification::Axiom {
                axiom_id: crate::id::AxiomId::new(51),
            },
        );
        eg.rebuild();
        assert_eq!(eg.find(pxy), eg.find(pzw));

        let mut buf = ProofBuf::new();
        eg.explain_deep(pxy, pzw, &mut buf);
        print_proof("AC: plus(x,y)≡plus(z,w)", &buf, eg);
        assert!(has_congruence(&buf));
        assert!(has_axiom(&buf, 50));
        assert!(has_axiom(&buf, 51));
    }

    // -- ACI: and(x,y) ≡ and(z,w) after merge(x,z), merge(y,w) --

    #[test]
    fn proof_aci() {
        let (ref mut eg, th) = setup();
        let x = eg.add(th.x, &[]);
        let y = eg.add(th.y, &[]);
        let z = eg.add(th.z, &[]);
        let w = eg.add(th.w, &[]);
        let axy = eg.add(th.and, &[x, y]);
        let azw = eg.add(th.and, &[z, w]);
        eg.merge_justified(
            x,
            z,
            Justification::Axiom {
                axiom_id: crate::id::AxiomId::new(60),
            },
        );
        eg.merge_justified(
            y,
            w,
            Justification::Axiom {
                axiom_id: crate::id::AxiomId::new(61),
            },
        );
        eg.rebuild();
        assert_eq!(eg.find(axy), eg.find(azw));

        let mut buf = ProofBuf::new();
        eg.explain_deep(axy, azw, &mut buf);
        print_proof("ACI: and(x,y)≡and(z,w)", &buf, eg);
        assert!(has_congruence(&buf));
        assert!(has_axiom(&buf, 60));
        assert!(has_axiom(&buf, 61));
    }

    // -- End-to-end: all kinds in one graph --

    #[test]
    fn proof_all_kinds() {
        let (ref mut eg, th) = setup();
        let x = eg.add(th.x, &[]);
        let y = eg.add(th.y, &[]);
        let z = eg.add(th.z, &[]);
        let w = eg.add(th.w, &[]);

        // Build nodes of every kind using x,y
        let fx = eg.add(th.f, &[x]); // Plain1
        let gxy = eg.add(th.g, &[x, y]); // Plain2
        let eq_xy = eg.add(th.eq, &[x, y]); // C
        let sxy = eg.add(th.sub, &[x, y]); // A
        let pxy = eg.add(th.plus, &[x, y]); // AC
        let axy = eg.add(th.and, &[x, y]); // ACI

        // Build matching nodes using z,w
        let fz = eg.add(th.f, &[z]);
        let gzw = eg.add(th.g, &[z, w]);
        let eq_zw = eg.add(th.eq, &[z, w]);
        let szw = eg.add(th.sub, &[z, w]);
        let pzw = eg.add(th.plus, &[z, w]);
        let azw = eg.add(th.and, &[z, w]);

        // Merge leaves
        eg.merge_justified(
            x,
            z,
            Justification::Axiom {
                axiom_id: crate::id::AxiomId::new(100),
            },
        );
        eg.merge_justified(
            y,
            w,
            Justification::Axiom {
                axiom_id: crate::id::AxiomId::new(101),
            },
        );
        eg.rebuild();

        // Verify all congruences
        assert_eq!(eg.find(fx), eg.find(fz));
        assert_eq!(eg.find(gxy), eg.find(gzw));
        assert_eq!(eg.find(eq_xy), eg.find(eq_zw));
        assert_eq!(eg.find(sxy), eg.find(szw));
        assert_eq!(eg.find(pxy), eg.find(pzw));
        assert_eq!(eg.find(axy), eg.find(azw));

        // Extract and print deep proofs for each
        let mut buf = ProofBuf::new();
        let cases: &[(&str, ENodeId, ENodeId)] = &[
            ("Plain1 f", fx, fz),
            ("Plain2 g", gxy, gzw),
            ("C eq", eq_xy, eq_zw),
            ("A sub", sxy, szw),
            ("AC plus", pxy, pzw),
            ("ACI and", axy, azw),
        ];
        for &(label, a, b) in cases {
            buf.clear();
            eg.explain_deep(a, b, &mut buf);
            print_proof(label, &buf, eg);
            assert!(has_congruence(&buf), "{label}: missing congruence step");
            assert!(
                has_axiom(&buf, 100) || has_axiom(&buf, 101),
                "{label}: missing axiom step"
            );
        }
        eprintln!("\n✓ All kinds proof extraction passed");
    }
}

#[cfg(test)]
mod stress_proof_test {
    use crate::egraph::EGraph31;
    use crate::id::{ENodeId, OpId};
    use crate::literal::NiraLitVal;
    use crate::union_find::{Justification, ProofBuf};
    use std::collections::HashSet;

    struct Ops {
        f: OpId,   // Plain1
        g: OpId,   // Plain2
        eq: OpId,  // C
        sub: OpId, // A
        add: OpId, // AC
        and: OpId, // ACI
    }

    fn build_stress(seed: u64, n_leaves: usize, n_layers: usize, n_merges: usize) {
        let mut eg = EGraph31::<NiraLitVal, false, true>::new();
        let int = eg.intern_sort("Int");
        let ops = Ops {
            f: eg.register_op1("f", int, int),
            g: eg.register_op2("g", int, int, int),
            eq: eg.register_c("eq", [int, int], int),
            sub: eg.register_a("sub", int, int, crate::registry::AssocDir::Left),
            add: eg.register_mset("add", int, int),
            and: eg.register_set("and", int, int),
        };

        // Simple LCG for deterministic pseudo-random
        let mut rng = seed;
        let mut next = || -> usize {
            rng = rng
                .wrapping_mul(6364136223846793005)
                .wrapping_add(1442695040888963407);
            (rng >> 33) as usize
        };

        // Layer 0: leaves
        let mut prev_layer: Vec<ENodeId> = Vec::new();
        for i in 0..n_leaves {
            let op = eg.register_op0(&format!("c{i}"), int);
            prev_layer.push(eg.add(op, &[]));
        }

        // Build layers — create pairs of nodes with same op, different children
        // to maximize congruence opportunities after leaf merges
        for _layer in 0..n_layers {
            let n = prev_layer.len();
            let mut new_layer: Vec<ENodeId> = Vec::new();
            // For each op kind, build multiple nodes over different children
            let ops_list: &[(
                &dyn Fn(&mut EGraph31<NiraLitVal, false, true>, ENodeId, ENodeId) -> ENodeId,
                usize,
            )] = &[
                (
                    &|eg: &mut EGraph31<NiraLitVal, false, true>, a, _| eg.add(ops.f, &[a]),
                    1,
                ),
                (&|eg, a, b| eg.add(ops.g, &[a, b]), 2),
                (&|eg, a, b| eg.add(ops.eq, &[a, b]), 2),
                (&|eg, a, b| eg.add(ops.sub, &[a, b]), 2),
                (&|eg, a, b| eg.add(ops.add, &[a, b]), 2),
                (&|eg, a, b| eg.add(ops.and, &[a, b]), 2),
            ];
            for &(builder, _arity) in ops_list {
                for _ in 0..(n / 3).max(2) {
                    let a = prev_layer[next() % n];
                    let b = prev_layer[next() % n];
                    new_layer.push(builder(&mut eg, a, b));
                }
            }
            prev_layer = new_layer;
        }

        let all_nodes: usize = eg.node_count();

        // Random merges on leaves with axiom justifications
        let mut axioms_issued: HashSet<crate::id::AxiomId> = HashSet::new();
        for i in 0..n_merges {
            let a_idx = next() % n_leaves;
            let b_idx = next() % n_leaves;
            if a_idx == b_idx {
                continue;
            }
            let a = ENodeId::new(a_idx as u32);
            let b = ENodeId::new(b_idx as u32);
            let axiom_id = crate::id::AxiomId::new(i as u16);
            if eg
                .merge_justified(a, b, Justification::Axiom { axiom_id })
                .is_some()
            {
                axioms_issued.insert(axiom_id);
            }
        }
        eg.rebuild();

        // Find pairs that became equivalent and extract deep proofs
        let mut buf = ProofBuf::new();
        let mut proofs_extracted = 0;
        let top = &prev_layer;
        for i in 0..top.len().min(50) {
            for j in (i + 1)..top.len().min(50) {
                if eg.find(top[i]) == eg.find(top[j]) && top[i] != top[j] {
                    buf.clear();
                    let ok = eg.explain_deep(top[i], top[j], &mut buf);
                    assert!(ok, "explain_deep failed for equivalent nodes");
                    assert!(!buf.steps.is_empty(), "empty proof for equivalent nodes");

                    // Validate: every axiom step must be one we issued
                    for (_, _, just) in &buf.steps {
                        if let Justification::Axiom { axiom_id } = just {
                            assert!(
                                axioms_issued.contains(axiom_id),
                                "proof references axiom #{axiom_id} which was never issued"
                            );
                        }
                    }

                    // Validate: every congruence step references valid node ids
                    for (_, _, just) in &buf.steps {
                        if let Justification::Congruence { node_a, node_b } = just {
                            assert!(
                                node_a.raw() < all_nodes as u32,
                                "congruence references invalid node_a"
                            );
                            assert!(
                                node_b.raw() < all_nodes as u32,
                                "congruence references invalid node_b"
                            );
                        }
                    }

                    proofs_extracted += 1;
                }
            }
        }

        eprintln!(
            "  seed={seed} leaves={n_leaves} layers={n_layers} merges={n_merges} \
             nodes={all_nodes} axioms={} proofs_extracted={proofs_extracted}",
            axioms_issued.len()
        );
    }

    /// Investigation harness (F5): rebuild the same stress structure with AC completion
    /// ON, so the basis-invariant dump (`AC_BASIS_DUMP=1`) and the divergence trace
    /// (`AC_COMPLETE_TRACE=1`) fire per completion round. Ignored by default because
    /// completion is known to diverge on these graphs; this exists to witness *why*.
    /// Run: `AC_BASIS_DUMP=1 AC_COMPLETE_TRACE=1 cargo test investigate_completion -- --ignored --nocapture`
    fn build_stress_cc(seed: u64, n_leaves: usize, n_layers: usize, n_merges: usize) {
        let mut eg = EGraph31::<NiraLitVal, false, true>::new();
        eg.set_cc(true);
        // Investigation harness: always run the reduced-basis invariant checks so the
        // per-round and final `cc_basis_dump`s fire regardless of the env var.
        eg.set_basis_checks(true);
        let int = eg.intern_sort("Int");
        let ops = Ops {
            f: eg.register_op1("f", int, int),
            g: eg.register_op2("g", int, int, int),
            eq: eg.register_c("eq", [int, int], int),
            sub: eg.register_a("sub", int, int, crate::registry::AssocDir::Left),
            add: eg.register_mset("add", int, int),
            and: eg.register_set("and", int, int),
        };

        let mut rng = seed;
        let mut next = || -> usize {
            rng = rng
                .wrapping_mul(6364136223846793005)
                .wrapping_add(1442695040888963407);
            (rng >> 33) as usize
        };

        let mut prev_layer: Vec<ENodeId> = Vec::new();
        for i in 0..n_leaves {
            let op = eg.register_op0(&format!("c{i}"), int);
            prev_layer.push(eg.add(op, &[]));
        }

        for _layer in 0..n_layers {
            let n = prev_layer.len();
            let mut new_layer: Vec<ENodeId> = Vec::new();
            let ops_list: &[(
                &dyn Fn(&mut EGraph31<NiraLitVal, false, true>, ENodeId, ENodeId) -> ENodeId,
                usize,
            )] = &[
                (
                    &|eg: &mut EGraph31<NiraLitVal, false, true>, a, _| eg.add(ops.f, &[a]),
                    1,
                ),
                (&|eg, a, b| eg.add(ops.g, &[a, b]), 2),
                (&|eg, a, b| eg.add(ops.eq, &[a, b]), 2),
                (&|eg, a, b| eg.add(ops.sub, &[a, b]), 2),
                (&|eg, a, b| eg.add(ops.add, &[a, b]), 2),
                (&|eg, a, b| eg.add(ops.and, &[a, b]), 2),
            ];
            for &(builder, _arity) in ops_list {
                for _ in 0..(n / 3).max(2) {
                    let a = prev_layer[next() % n];
                    let b = prev_layer[next() % n];
                    new_layer.push(builder(&mut eg, a, b));
                }
            }
            prev_layer = new_layer;
        }

        for i in 0..n_merges {
            let a_idx = next() % n_leaves;
            let b_idx = next() % n_leaves;
            if a_idx == b_idx {
                continue;
            }
            let a = ENodeId::new(a_idx as u32);
            let b = ENodeId::new(b_idx as u32);
            let axiom_id = crate::id::AxiomId::new(i as u16);
            eg.merge_justified(a, b, Justification::Axiom { axiom_id });
        }
        eprintln!("[investigate] seed={seed} starting rebuild with completion ON");
        eg.rebuild();
        eg.cc_basis_dump("final");
        eprintln!(
            "[investigate] seed={seed} final node_count={}",
            eg.node_count()
        );
    }

    /// Like `build_stress_cc` but with no basis dump; returns the final node count.
    /// On divergence the `rebuild` backstop's `debug_assert` panics, which the sweep catches.
    fn build_stress_ac_complete_quiet(
        seed: u64,
        n_leaves: usize,
        n_layers: usize,
        n_merges: usize,
    ) -> usize {
        let mut eg = EGraph31::<NiraLitVal, false, true>::new();
        eg.set_cc(true);
        let int = eg.intern_sort("Int");
        let ops = Ops {
            f: eg.register_op1("f", int, int),
            g: eg.register_op2("g", int, int, int),
            eq: eg.register_c("eq", [int, int], int),
            sub: eg.register_a("sub", int, int, crate::registry::AssocDir::Left),
            add: eg.register_mset("add", int, int),
            and: eg.register_set("and", int, int),
        };
        let mut rng = seed;
        let mut next = || -> usize {
            rng = rng
                .wrapping_mul(6364136223846793005)
                .wrapping_add(1442695040888963407);
            (rng >> 33) as usize
        };
        let mut prev_layer: Vec<ENodeId> = Vec::new();
        for i in 0..n_leaves {
            let op = eg.register_op0(&format!("c{i}"), int);
            prev_layer.push(eg.add(op, &[]));
        }
        for _layer in 0..n_layers {
            let n = prev_layer.len();
            let mut new_layer: Vec<ENodeId> = Vec::new();
            let ops_list: &[&dyn Fn(
                &mut EGraph31<NiraLitVal, false, true>,
                ENodeId,
                ENodeId,
            ) -> ENodeId] = &[
                &|eg, a, _| eg.add(ops.f, &[a]),
                &|eg, a, b| eg.add(ops.g, &[a, b]),
                &|eg, a, b| eg.add(ops.eq, &[a, b]),
                &|eg, a, b| eg.add(ops.sub, &[a, b]),
                &|eg, a, b| eg.add(ops.add, &[a, b]),
                &|eg, a, b| eg.add(ops.and, &[a, b]),
            ];
            for builder in ops_list {
                for _ in 0..(n / 3).max(2) {
                    let a = prev_layer[next() % n];
                    let b = prev_layer[next() % n];
                    new_layer.push(builder(&mut eg, a, b));
                }
            }
            prev_layer = new_layer;
        }
        for i in 0..n_merges {
            let a_idx = next() % n_leaves;
            let b_idx = next() % n_leaves;
            if a_idx == b_idx {
                continue;
            }
            let a = ENodeId::new(a_idx as u32);
            let b = ENodeId::new(b_idx as u32);
            let axiom_id = crate::id::AxiomId::new(i as u16);
            eg.merge_justified(a, b, Justification::Axiom { axiom_id });
        }
        eg.rebuild();
        eg.node_count()
    }

    #[test]
    #[ignore = "completion diverges on this graph; investigation harness only"]
    fn investigate_completion() {
        build_stress_cc(42, 30, 4, 20);
    }

    /// Sweep a grid of stress configs with AC completion ON and report which converge and
    /// which hit the divergence backstop (the `debug_assert` in `rebuild`, caught per config).
    /// Maps the boundary of "what still blows up". Basis checks off here (we only want the
    /// converge/diverge verdict, not the per-round dump).
    /// Run: `cargo test investigate_completion_sweep -- --ignored --nocapture`
    #[test]
    #[ignore = "investigation sweep: maps the converge/diverge boundary; slow"]
    fn investigate_completion_sweep() {
        // (seed, leaves, layers, merges)
        let grid: &[(u64, usize, usize, usize)] = &[
            (1, 6, 2, 4),
            (2, 8, 2, 6),
            (7, 12, 2, 5),
            (3, 12, 3, 8),
            (4, 16, 3, 10),
            (5, 20, 3, 12),
            (8, 24, 3, 14),
            (6, 30, 4, 20),
            (123, 30, 4, 20),
            (999, 40, 3, 30),
        ];
        // NOTE: seed 42 at (30, 4, 20) is the one known *diverging* input; it is witnessed
        // separately by `investigate_completion` (it churns slowly to the 50k-node backstop,
        // so including it here would make the sweep hang for minutes). Divergence is
        // input-specific, not size-specific: same-size configs above converge in well under a
        // second. See the spec §3.3 / plan §0.5.
        for &(seed, leaves, layers, merges) in grid {
            let res = std::panic::catch_unwind(|| {
                build_stress_ac_complete_quiet(seed, leaves, layers, merges)
            });
            match res {
                Ok(nodes) => eprintln!(
                    "[sweep] seed={seed} leaves={leaves} layers={layers} merges={merges}: CONVERGED, {nodes} nodes"
                ),
                Err(_) => eprintln!(
                    "[sweep] seed={seed} leaves={leaves} layers={layers} merges={merges}: DIVERGED (hit backstop)"
                ),
            }
        }
    }

    #[test]
    #[ignore = "investigation harness: a small CONVERGING graph, to check the basis is fully
                Kapur-reduced at the true fixpoint (kapur_lhs_reducible=0 in the final dump)"]
    fn investigate_completion_small() {
        build_stress_cc(7, 12, 2, 5);
    }

    #[test]
    fn stress_small() {
        for seed in 0..20 {
            build_stress(seed, 8, 2, 6);
        }
        eprintln!("✓ stress_small passed");
    }

    #[test]
    fn stress_medium() {
        for seed in 0..10 {
            build_stress(seed, 16, 3, 12);
        }
        eprintln!("✓ stress_medium passed");
    }

    #[test]
    fn stress_large() {
        build_stress(42, 30, 4, 20);
        build_stress(123, 30, 4, 20);
        build_stress(999, 40, 3, 30);
        eprintln!("✓ stress_large passed");
    }
}

#[cfg(test)]
mod aci_deep_proof_test {
    use crate::egraph::EGraph31;
    use crate::id::ENodeId;
    use crate::literal::NiraLitVal;
    use crate::union_find::{Justification, ProofBuf};

    /// Two ACI (and) nodes with n children each:
    /// - k children shared
    /// - n-k children distinct per side
    ///
    /// Merge the n-k distinct pairs, rebuild, verify equivalence, extract deep proof.
    fn aci_overlap(n: usize, k: usize) {
        assert!(k <= n);
        let mut eg = EGraph31::<NiraLitVal, false, true>::new();
        let int = eg.intern_sort("Int");
        let and = eg.register_set("and", int, int);

        // Shared children: s0..s(k-1)
        let mut shared = Vec::new();
        for i in 0..k {
            let op = eg.register_op0(&format!("s{i}"), int);
            shared.push(eg.add(op, &[]));
        }

        // Distinct children for left: a0..a(n-k-1)
        let mut left_only = Vec::new();
        for i in 0..(n - k) {
            let op = eg.register_op0(&format!("a{i}"), int);
            left_only.push(eg.add(op, &[]));
        }

        // Distinct children for right: b0..b(n-k-1)
        let mut right_only = Vec::new();
        for i in 0..(n - k) {
            let op = eg.register_op0(&format!("b{i}"), int);
            right_only.push(eg.add(op, &[]));
        }

        // Build and(shared..., left_only...)
        let mut left_children: Vec<ENodeId> = Vec::new();
        left_children.extend_from_slice(&shared);
        left_children.extend_from_slice(&left_only);
        let left = eg.add(and, &left_children);

        // Build and(shared..., right_only...)
        let mut right_children: Vec<ENodeId> = Vec::new();
        right_children.extend_from_slice(&shared);
        right_children.extend_from_slice(&right_only);
        let right = eg.add(and, &right_children);

        assert_ne!(eg.find(left), eg.find(right));

        // Merge each distinct pair: a_i ≡ b_i
        for i in 0..(n - k) {
            eg.merge_justified(
                left_only[i],
                right_only[i],
                Justification::Axiom {
                    axiom_id: crate::id::AxiomId::new(i as u16),
                },
            );
        }
        eg.rebuild();

        assert_eq!(
            eg.find(left),
            eg.find(right),
            "and-nodes should be equivalent after merging distinct children (n={n}, k={k})"
        );

        // Extract deep proof
        let mut buf = ProofBuf::new();
        assert!(eg.explain_deep(left, right, &mut buf));

        eprintln!(
            "\n--- ACI overlap n={n} k={k} ({} steps) ---",
            buf.steps.len()
        );
        for (i, (from, to, just)) in buf.steps.iter().enumerate() {
            let reason = match just {
                Justification::Axiom { axiom_id } => format!("axiom #{axiom_id}"),
                Justification::Congruence { node_a, node_b } => format!(
                    "congruence({}, {})",
                    eg.node_op_name(*node_a),
                    eg.node_op_name(*node_b)
                ),
                Justification::Rewrite { rule_id, .. } => format!("rewrite #{rule_id}"),
                Justification::Filler => unreachable!("filler is never a real proof step"),
            };
            eprintln!(
                "  [{i}] {} ≡ {}  by {reason}",
                eg.node_op_name(*from),
                eg.node_op_name(*to)
            );
        }

        // Validate: must have congruence + all axioms we issued
        assert!(
            buf.steps
                .iter()
                .any(|(_, _, j)| matches!(j, Justification::Congruence { .. })),
            "missing congruence step"
        );
        for i in 0..(n - k) {
            assert!(
                buf.steps.iter().any(|(_, _, j)| *j
                    == Justification::Axiom {
                        axiom_id: crate::id::AxiomId::new(i as u16)
                    }),
                "missing axiom #{i}"
            );
        }
    }

    #[test]
    fn aci_no_overlap() {
        aci_overlap(4, 0);
    }

    #[test]
    fn aci_half_overlap() {
        aci_overlap(6, 3);
    }

    #[test]
    fn aci_mostly_shared() {
        aci_overlap(8, 6);
    }

    #[test]
    fn aci_deep() {
        aci_overlap(20, 10);
    }

    #[test]
    fn aci_wide() {
        aci_overlap(50, 25);
    }
}

#[cfg(test)]
mod bench_overhead {
    use crate::egraph::EGraph31;
    use crate::id::{ENodeId, OpId};
    use crate::literal::NiraLitVal;
    use crate::union_find::Justification;
    use std::time::Instant;

    fn build_and_rebuild<const TRACK: bool, const PROOFS: bool>(
        n_leaves: usize,
        n_layers: usize,
        n_merges: usize,
    ) -> std::time::Duration {
        let mut eg = EGraph31::<NiraLitVal, TRACK, PROOFS>::new();
        let int = eg.intern_sort("Int");
        let f = eg.register_op1("f", int, int);
        let g = eg.register_op2("g", int, int, int);
        let eq = eg.register_c("eq", [int, int], int);
        let add = eg.register_mset("add", int, int);
        let and = eg.register_set("and", int, int);

        let mut rng: u64 = 12345;
        let mut next = || -> usize {
            rng = rng
                .wrapping_mul(6364136223846793005)
                .wrapping_add(1442695040888963407);
            (rng >> 33) as usize
        };

        // Leaves
        let mut prev: Vec<ENodeId> = Vec::new();
        for i in 0..n_leaves {
            let op = eg.register_op0(&format!("c{i}"), int);
            prev.push(eg.add(op, &[]));
        }

        // Layers
        for _ in 0..n_layers {
            let n = prev.len();
            let mut layer = Vec::new();
            let ops: [OpId; 5] = [f, g, eq, add, and];
            for _ in 0..n {
                let a = prev[next() % n];
                let b = prev[next() % n];
                let op = ops[next() % 5];
                if op == f {
                    layer.push(eg.add(op, &[a]));
                } else {
                    layer.push(eg.add(op, &[a, b]));
                }
            }
            prev = layer;
        }

        // Merges
        let start = Instant::now();
        for i in 0..n_merges {
            let a = ENodeId::new((next() % n_leaves) as u32);
            let b = ENodeId::new((next() % n_leaves) as u32);
            if PROOFS {
                eg.merge_justified(
                    a,
                    b,
                    Justification::Axiom {
                        axiom_id: crate::id::AxiomId::new(i as u16),
                    },
                );
            } else {
                eg.merge(a, b);
            }
        }
        eg.rebuild();
        start.elapsed()
    }

    #[test]
    fn overhead_comparison() {
        let params = [
            (50, 3, 20, "small"),
            (100, 3, 40, "medium"),
            (200, 4, 80, "large"),
        ];

        // Warmup
        build_and_rebuild::<false, false>(20, 2, 10);
        build_and_rebuild::<false, true>(20, 2, 10);
        build_and_rebuild::<true, true>(20, 2, 10);

        eprintln!("\n=== PROOFS overhead comparison (merge+rebuild) ===");
        eprintln!(
            "{:<10} {:>12} {:>12} {:>12} {:>8} {:>8}",
            "size", "T=f,P=f", "T=f,P=t", "T=t,P=t", "P ratio", "TP ratio"
        );
        eprintln!("{}", "-".repeat(72));

        for &(leaves, layers, merges, label) in &params {
            let mut t_ff = Vec::new();
            let mut t_ft = Vec::new();
            let mut t_tt = Vec::new();
            let iters = 20;
            for _ in 0..iters {
                t_ff.push(build_and_rebuild::<false, false>(leaves, layers, merges));
                t_ft.push(build_and_rebuild::<false, true>(leaves, layers, merges));
                t_tt.push(build_and_rebuild::<true, true>(leaves, layers, merges));
            }
            t_ff.sort();
            t_ft.sort();
            t_tt.sort();
            let m_ff = t_ff[iters / 2];
            let m_ft = t_ft[iters / 2];
            let m_tt = t_tt[iters / 2];
            let r_p = m_ft.as_nanos() as f64 / m_ff.as_nanos().max(1) as f64;
            let r_tp = m_tt.as_nanos() as f64 / m_ff.as_nanos().max(1) as f64;
            eprintln!(
                "{:<10} {:>10.1}µs {:>10.1}µs {:>10.1}µs {:>7.2}x {:>7.2}x",
                label,
                m_ff.as_nanos() as f64 / 1000.0,
                m_ft.as_nanos() as f64 / 1000.0,
                m_tt.as_nanos() as f64 / 1000.0,
                r_p,
                r_tp,
            );
        }
    }
}

#[cfg(test)]
mod proof_restore_test {
    use crate::containers::ShrinkPolicy;
    use crate::egraph::EGraph31;
    use crate::literal::NiraLitVal;
    use crate::union_find::{Justification, ProofBuf};

    /// Merge + rebuild + mark/restore: verify that proof state is fully rolled back.
    /// After restore, congruence should be undone and explain_deep should fail.
    /// Then re-merge different leaves and verify new proofs work correctly.
    #[test]
    fn proof_state_restored() {
        let mut eg = EGraph31::<NiraLitVal, true, true>::new();
        let int = eg.intern_sort("Int");
        let f = eg.register_op1("f", int, int);
        let x_op = eg.register_op0("x", int);
        let y_op = eg.register_op0("y", int);
        let z_op = eg.register_op0("z", int);

        let x = eg.add(x_op, &[]);
        let y = eg.add(y_op, &[]);
        let z = eg.add(z_op, &[]);
        let fx = eg.add(f, &[x]);
        let fy = eg.add(f, &[y]);
        let fz = eg.add(f, &[z]);

        // Mark before any merges
        let token = eg.mark(ShrinkPolicy::Never);

        // Merge x≡y, rebuild → f(x)≡f(y) by congruence
        eg.merge_justified(
            x,
            y,
            Justification::Axiom {
                axiom_id: crate::id::AxiomId::new(1),
            },
        );
        eg.rebuild();
        assert_eq!(eg.find(fx), eg.find(fy));
        assert_ne!(eg.find(fx), eg.find(fz));

        // Deep proof should work
        let mut buf = ProofBuf::new();
        assert!(eg.explain_deep(fx, fy, &mut buf));
        assert!(
            buf.steps
                .iter()
                .any(|(_, _, j)| matches!(j, Justification::Congruence { .. }))
        );
        assert!(buf.steps.iter().any(|(_, _, j)| *j
            == Justification::Axiom {
                axiom_id: crate::id::AxiomId::new(1)
            }));

        // Restore
        eg.restore(token);

        // Congruence should be undone
        assert_ne!(eg.find(fx), eg.find(fy));
        assert_ne!(eg.find(fx), eg.find(fz));

        // Proof should fail
        buf.clear();
        assert!(!eg.explain_deep(fx, fy, &mut buf));

        // Now merge x≡z instead, rebuild → f(x)≡f(z)
        eg.merge_justified(
            x,
            z,
            Justification::Axiom {
                axiom_id: crate::id::AxiomId::new(2),
            },
        );
        eg.rebuild();
        assert_eq!(eg.find(fx), eg.find(fz));
        assert_ne!(eg.find(fx), eg.find(fy));

        // New proof should reference axiom #2, not axiom #1
        buf.clear();
        assert!(eg.explain_deep(fx, fz, &mut buf));
        assert!(buf.steps.iter().any(|(_, _, j)| *j
            == Justification::Axiom {
                axiom_id: crate::id::AxiomId::new(2)
            }));
        assert!(!buf.steps.iter().any(|(_, _, j)| *j
            == Justification::Axiom {
                axiom_id: crate::id::AxiomId::new(1)
            }));

        eprintln!("✓ proof_state_restored passed");
    }

    /// Multiple mark/restore cycles with proofs.
    #[test]
    fn proof_nested_restore() {
        let mut eg = EGraph31::<NiraLitVal, true, true>::new();
        let int = eg.intern_sort("Int");
        let f = eg.register_op1("f", int, int);
        let a_op = eg.register_op0("a", int);
        let b_op = eg.register_op0("b", int);
        let c_op = eg.register_op0("c", int);

        let a = eg.add(a_op, &[]);
        let b = eg.add(b_op, &[]);
        let c = eg.add(c_op, &[]);
        let fa = eg.add(f, &[a]);
        let fb = eg.add(f, &[b]);
        let fc = eg.add(f, &[c]);

        let tok1 = eg.mark(ShrinkPolicy::Never);

        // Merge a≡b
        eg.merge_justified(
            a,
            b,
            Justification::Axiom {
                axiom_id: crate::id::AxiomId::new(10),
            },
        );
        eg.rebuild();
        assert_eq!(eg.find(fa), eg.find(fb));

        let tok2 = eg.mark(ShrinkPolicy::Never);

        // Merge a≡c on top
        eg.merge_justified(
            a,
            c,
            Justification::Axiom {
                axiom_id: crate::id::AxiomId::new(20),
            },
        );
        eg.rebuild();
        assert_eq!(eg.find(fa), eg.find(fc));

        // Restore to tok2: a≡c undone, a≡b still holds
        eg.restore(tok2);
        assert_eq!(eg.find(fa), eg.find(fb));
        assert_ne!(eg.find(fa), eg.find(fc));

        let mut buf = ProofBuf::new();
        assert!(eg.explain_deep(fa, fb, &mut buf));
        assert!(!eg.explain_deep(fa, fc, &mut buf));

        // Restore to tok1: everything undone
        eg.restore(tok1);
        assert_ne!(eg.find(fa), eg.find(fb));
        assert_ne!(eg.find(fa), eg.find(fc));

        buf.clear();
        assert!(!eg.explain_deep(fa, fb, &mut buf));

        eprintln!("✓ proof_nested_restore passed");
    }
}
