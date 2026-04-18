// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0
use semi_persistent_egraph::EGraph31;
use semi_persistent_egraph::literal::NiraLitVal;

fn main() {
    let mut eg = EGraph31::<NiraLitVal, false, false>::new();
    let int = eg.intern_sort("Int");
    let bool_ = eg.intern_sort("Bool");
    let x = eg.register_op0("x", int);
    let y = eg.register_op0("y", int);
    let z = eg.register_op0("z", int);
    let f = eg.register_op1("f", int, int);
    let g = eg.register_op2("g", int, int, int);
    let eq = eg.register_c("eq", [int, int], bool_);
    let plus = eg.register_ac("plus", int, int);

    let ex = eg.add(x, &[]);
    let ey = eg.add(y, &[]);
    let ez = eg.add(z, &[]);
    let _fx = eg.add(f, &[ex]);
    let _fy = eg.add(f, &[ey]);
    let _gxy = eg.add(g, &[ex, ey]);
    let _eqxy = eg.add(eq, &[ex, ey]);
    let _pxyz = eg.add(plus, &[ex, ey, ez]);

    eprintln!("Before merge:");
    eg.show("before");

    eg.merge(ex, ey);
    eg.rebuild();

    eprintln!("\nAfter merge(x,y) + rebuild:");
    eg.show("after");
}
