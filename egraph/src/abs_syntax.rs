// egraph/src/abs_syntax.rs

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Carrier {
    Int,
    Bool,
    BitVec(u32),
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Domain {
    Interval,
    UBounds,
    SBounds,
    Congruence,
    NonZero,
    Bits,
    Bool,
}

#[derive(Clone, Copy, Debug, Default, PartialEq, Eq)]
pub struct DomainMask(pub u8);

impl DomainMask {
    pub fn enable(&mut self, domain: Domain) {
        self.0 |= 1 << (domain as u8);
    }

    pub fn has(&self, domain: Domain) -> bool {
        (self.0 & (1 << (domain as u8))) != 0
    }
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum AbsValueLit {
    Interval { lo: String, hi: String },
    Bits { val: String, mask: String },
    Congruence { r: String, m: String },
    NonZero,
    True,
    False,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum AbsTestLit {
    Within {
        var: String,
        lo: String,
        hi: String,
    },
    NonZero {
        var: String,
    },
    KnownBits {
        var: String,
        val: String,
        mask: String,
    },
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct AbsValue {
    pub domain: Domain,
    // The resolved internal representation goes here
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct AbsTest {
    pub domain: Domain,
    pub var: String,
}
