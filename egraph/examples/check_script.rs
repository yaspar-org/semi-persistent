// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0
//! Compile a cost script and report: `check_script PATH`.
fn main() {
    let p = std::env::args().nth(1).expect("path");
    match semi_persistent_egraph::extraction::script::Script::compile(&p) {
        Ok(_) => println!("compiled"),
        Err(e) => println!("rejected:\n{e}"),
    }
}
