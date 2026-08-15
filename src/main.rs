use anyhow::{bail, Context, Result};
use sha2::{Digest, Sha256};
use std::{collections::BTreeMap, env, fs};
fn main() -> Result<()> {
    let mut a = env::args().skip(1);
    if a.next().as_deref() != Some("run") {
        bail!("usage: axiom-runtime run --spec S --program P --proof R --x N");
    }
    let sp = arg(&mut a, "--spec")?;
    let pp = arg(&mut a, "--program")?;
    let rp = arg(&mut a, "--proof")?;
    let x: i64 = arg(&mut a, "--x")?.parse()?;
    let s = fs::read_to_string(sp)?;
    let p = fs::read_to_string(pp)?;
    let r = fs::read_to_string(rp)?;
    let receipt = parse_receipt(&r)?;
    if receipt.get("verdict").map(String::as_str) != Some("VALID") {
        bail!("receipt is not VALID");
    }
    if receipt.get("spec.sha256") != Some(&hex(&hash(s.as_bytes()))) {
        bail!("spec hash does not match receipt");
    }
    if receipt.get("program.sha256") != Some(&hex(&hash(p.as_bytes()))) {
        bail!("program hash does not match receipt");
    }
    let min: i64 = receipt["domain.min"].parse()?;
    let max: i64 = receipt["domain.max"].parse()?;
    if x < min || x > max {
        bail!("input {x} lies outside proven domain {min}..{max}");
    }
    let result = run_program(&p, x)?;
    println!("{result}");
    Ok(())
}
fn arg(a: &mut impl Iterator<Item = String>, name: &str) -> Result<String> {
    let f = a.next().context("missing flag")?;
    if f != name {
        bail!("expected {name}, got {f}");
    }
    a.next().context("missing value")
}
fn parse_receipt(raw: &str) -> Result<BTreeMap<String, String>> {
    let mut it = raw.lines();
    if it.next() != Some("AXIOM-PROOF/1") {
        bail!("bad proof header");
    }
    let mut m = BTreeMap::new();
    for l in it.filter(|l| !l.trim().is_empty()) {
        let (k, v) = l.split_once('=').context("bad proof line")?;
        m.insert(k.to_owned(), v.to_owned());
    }
    Ok(m)
}
fn run_program(raw: &str, x: i64) -> Result<i64> {
    let mut r = [0i64; 128];
    let mut code = false;
    for l in raw.lines() {
        let t = l.trim();
        if t == "code:" {
            code = true;
            continue;
        }
        if t == "end" {
            break;
        }
        if !code {
            continue;
        }
        let w: Vec<_> = t.split_whitespace().collect();
        match w.as_slice() {
            ["LOAD_INPUT", d, "x"] => r[reg(d)?] = x,
            ["CONST", d, v] => r[reg(d)?] = v.parse()?,
            ["NEG", d, a] => r[reg(d)?] = r[reg(a)?].wrapping_neg(),
            ["ADD", d, a, b] => r[reg(d)?] = r[reg(a)?].wrapping_add(r[reg(b)?]),
            ["SUB", d, a, b] => r[reg(d)?] = r[reg(a)?].wrapping_sub(r[reg(b)?]),
            ["SELECT_NEG", d, a, b] => r[reg(d)?] = if x < 0 { r[reg(a)?] } else { r[reg(b)?] },
            ["RETURN", a] => return Ok(r[reg(a)?]),
            _ => bail!("unsupported instruction: {t}"),
        }
    }
    bail!("no RETURN")
}
fn reg(s: &str) -> Result<usize> {
    let n = s
        .strip_prefix('r')
        .context("bad register")?
        .parse::<usize>()?;
    if n >= 128 {
        bail!("register out of range")
    };
    Ok(n)
}
fn hash(b: &[u8]) -> [u8; 32] {
    Sha256::digest(b).into()
}
fn hex(h: &[u8; 32]) -> String {
    h.iter().map(|b| format!("{b:02x}")).collect()
}
