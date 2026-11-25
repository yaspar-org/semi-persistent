// egraph/src/abs_syntax.rs
use num_bigint::BigInt;

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

    pub fn is_empty(&self) -> bool {
        self.0 == 0
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
pub enum AbsValueKind {
    Interval { lo: BigInt, hi: BigInt },
    Bits { val: BigInt, mask: BigInt },
    Congruence { r: BigInt, m: BigInt },
    NonZero,
    Bool(bool),
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct AbsValue {
    pub domain: Domain,
    pub kind: AbsValueKind,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum AbsTestKind {
    Within { lo: BigInt, hi: BigInt },
    NonZero,
    KnownBits { val: BigInt, mask: BigInt },
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct AbsTest {
    pub domain: Domain,
    pub var: String,
    pub kind: AbsTestKind,
}

fn parse_int(raw: &str) -> Result<BigInt, String> {
    raw.parse::<BigInt>()
        .map_err(|_| format!("invalid integer literal '{raw}'"))
}

fn check_fits_carrier(raw: &str, val: &BigInt, carrier: Option<Carrier>) -> Result<(), String> {
    if let Some(Carrier::BitVec(w)) = carrier {
        let max_excl = BigInt::from(1u8) << (w as usize);
        if val < &BigInt::from(0) || val >= &max_excl {
            return Err(format!("value {raw} does not fit (bitvec {w})"));
        }
    }
    Ok(())
}

pub fn check_abs_value(
    lit: &AbsValueLit,
    sort_name: &str,
    carrier: Option<Carrier>,
    domains: DomainMask,
) -> Result<AbsValue, String> {
    let (domain, domain_name) = match lit {
        AbsValueLit::Interval { .. } => match carrier {
            Some(Carrier::BitVec(_)) => (Domain::UBounds, "ubounds"),
            _ => (Domain::Interval, "interval"),
        },
        AbsValueLit::Bits { .. } => (Domain::Bits, "bits"),
        AbsValueLit::Congruence { .. } => (Domain::Congruence, "congruence"),
        AbsValueLit::NonZero => (Domain::NonZero, "nonzero"),
        AbsValueLit::True | AbsValueLit::False => (Domain::Bool, "bool"),
    };

    if !domains.has(domain) {
        return Err(format!(
            "refine: domain '{domain_name}' is not enabled on sort '{sort_name}'"
        ));
    }

    let kind = match lit {
        AbsValueLit::Interval { lo, hi } => {
            let lo_v = parse_int(lo)?;
            let hi_v = parse_int(hi)?;
            if lo_v > hi_v {
                return Err("(interval lo hi) needs lo <= hi".to_string());
            }
            check_fits_carrier(lo, &lo_v, carrier)?;
            check_fits_carrier(hi, &hi_v, carrier)?;
            AbsValueKind::Interval { lo: lo_v, hi: hi_v }
        }
        AbsValueLit::Bits { val, mask } => {
            let v = parse_int(val)?;
            let m = parse_int(mask)?;
            check_fits_carrier(val, &v, carrier)?;
            check_fits_carrier(mask, &m, carrier)?;
            if (&v & &m) != BigInt::from(0) {
                return Err("(bits :val V :mask M) needs V and M to share no bit".to_string());
            }
            AbsValueKind::Bits { val: v, mask: m }
        }
        AbsValueLit::Congruence { r, m } => {
            let r_v = parse_int(r)?;
            let m_v = parse_int(m)?;
            if m_v < BigInt::from(1) || r_v < BigInt::from(0) || r_v >= m_v {
                return Err("(congruence r m) needs m >= 1 and 0 <= r < m".to_string());
            }
            AbsValueKind::Congruence { r: r_v, m: m_v }
        }
        AbsValueLit::NonZero => AbsValueKind::NonZero,
        AbsValueLit::True => AbsValueKind::Bool(true),
        AbsValueLit::False => AbsValueKind::Bool(false),
    };

    Ok(AbsValue { domain, kind })
}

pub fn check_abs_test(
    lit: &AbsTestLit,
    sort_name: &str,
    carrier: Option<Carrier>,
    domains: DomainMask,
) -> Result<AbsTest, String> {
    let (guard_name, var, domain, domain_name) = match lit {
        AbsTestLit::Within { var, .. } => {
            let (d, dn) = match carrier {
                Some(Carrier::BitVec(_)) => (Domain::UBounds, "ubounds"),
                _ => (Domain::Interval, "interval"),
            };
            ("within", var, d, dn)
        }
        AbsTestLit::NonZero { var } => ("nonzero", var, Domain::NonZero, "nonzero"),
        AbsTestLit::KnownBits { var, .. } => ("known-bits", var, Domain::Bits, "bits"),
    };

    if !domains.has(domain) {
        return Err(format!(
            "{guard_name}: domain '{domain_name}' is not enabled on sort '{sort_name}'"
        ));
    }

    let kind = match lit {
        AbsTestLit::Within { lo, hi, .. } => {
            let lo_v = parse_int(lo)?;
            let hi_v = parse_int(hi)?;
            if lo_v > hi_v {
                return Err("(interval lo hi) needs lo <= hi".to_string());
            }
            check_fits_carrier(lo, &lo_v, carrier)?;
            check_fits_carrier(hi, &hi_v, carrier)?;
            AbsTestKind::Within { lo: lo_v, hi: hi_v }
        }
        AbsTestLit::NonZero { .. } => AbsTestKind::NonZero,
        AbsTestLit::KnownBits { val, mask, .. } => {
            let v = parse_int(val)?;
            let m = parse_int(mask)?;
            check_fits_carrier(val, &v, carrier)?;
            check_fits_carrier(mask, &m, carrier)?;
            if (&v & &m) != BigInt::from(0) {
                return Err("(bits :val V :mask M) needs V and M to share no bit".to_string());
            }
            AbsTestKind::KnownBits { val: v, mask: m }
        }
    };

    Ok(AbsTest {
        domain,
        var: var.clone(),
        kind,
    })
}
