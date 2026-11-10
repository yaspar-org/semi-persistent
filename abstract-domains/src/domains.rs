// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0
/// The executable domains at each native width.
///
/// Every executable domain is generic over the word and proved once for every
/// `W: BitWord` (`ExecTnum`, `ExecAnum`, `ExecUnum`) or `W: Word`
/// (`Interval`, `Congruence`); each `dN` module names them at one width. These
/// domains are combined through `reduce::Product`, not a product of their own.
macro_rules! abstract_domain {
    ($mod_name:ident, $uint:ty) => {
        pub mod $mod_name {
            pub type ExecTnum = crate::exec_tnum::ExecTnum<$uint>;
            pub type ExecAnum = crate::exec_anum::ExecAnum<$uint>;
            pub type ExecUnum = crate::exec_unum::ExecUnum<$uint>;
            pub type Interval = crate::interval::Interval<$uint>;
            pub type Congruence = crate::congruence::Congruence<$uint>;
        }
    };
}

abstract_domain!(d8, u8);
abstract_domain!(d16, u16);
abstract_domain!(d32, u32);
abstract_domain!(d64, u64);
