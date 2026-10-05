// SPDX-FileCopyrightText: 2026 Ivan Zorin <creator@localzet.com> (Localzet contributions)
// SPDX-License-Identifier: MIT
use anyhow::{bail, Context, Result};
use sha2::{Digest, Sha256};
use std::{collections::BTreeMap, env, fs};

fn main() -> Result<()> {
    let mut args = env::args().skip(1);
    if args.next().as_deref() != Some("run") {
        bail!("usage: axiom-runtime run --spec S --program P --proof R --x N");
    }
    let spec_path = arg(&mut args, "--spec")?;
    let program_path = arg(&mut args, "--program")?;
    let proof_path = arg(&mut args, "--proof")?;
    let x: i64 = arg(&mut args, "--x")?.parse()?;

    let spec = fs::read_to_string(spec_path)?;
    let program = fs::read_to_string(program_path)?;
    let proof = fs::read_to_string(proof_path)?;
    authorize(&spec, &program, &proof, x)?;
    println!("{}", execute(&program, x)?);
    Ok(())
}

fn authorize(spec: &str, program: &str, proof: &str, x: i64) -> Result<()> {
    let receipt = parse_kv(proof, "AXIOM-PROOF/2")?;
    if receipt.get("verdict").map(String::as_str) != Some("VALID") {
        bail!("receipt is not VALID");
    }
    if receipt.get("counterexample").map(String::as_str) != Some("none") {
        bail!("VALID receipt must not carry a counterexample");
    }
    if receipt.get("spec.sha256") != Some(&sha256_hex(spec.as_bytes())) {
        bail!("spec hash mismatch");
    }
    if receipt.get("program.sha256") != Some(&sha256_hex(program.as_bytes())) {
        bail!("program hash mismatch");
    }
    if receipt.get("soundness.scope").map(String::as_str) != Some("exact-for-supported-fragment") {
        bail!("runtime does not accept this proof scope");
    }

    let spec_doc = parse_kv(spec, "AXIOM-IR/2")?;
    let input = spec_doc.get("input.0.name").context("missing input name")?;
    let kind = spec_doc
        .get(&format!("domain.{input}.kind"))
        .context("missing domain kind")?;
    match kind.as_str() {
        "unbounded" => {}
        "range" => {
            let min: i64 = spec_doc
                .get(&format!("domain.{input}.min"))
                .context("missing domain minimum")?
                .parse()?;
            let max: i64 = spec_doc
                .get(&format!("domain.{input}.max"))
                .context("missing domain maximum")?
                .parse()?;
            if x < min || x > max {
                bail!("input {x} lies outside proven range {min}..{max}");
            }
        }
        other => bail!("unsupported domain kind: {other}"),
    }
    Ok(())
}

fn execute(raw: &str, x: i64) -> Result<i64> {
    let mut registers = [0i64; 256];
    let mut in_code = false;
    for line in raw.lines() {
        let line = line.trim();
        if line == "code:" {
            in_code = true;
            continue;
        }
        if line == "end" {
            break;
        }
        if !in_code || line.is_empty() {
            continue;
        }
        let words: Vec<_> = line.split_whitespace().collect();
        match words.as_slice() {
            ["LOAD_INPUT", dest, "x"] => registers[register(dest)?] = x,
            ["CONST", dest, value] => registers[register(dest)?] = value.parse()?,
            ["NEG", dest, src] => {
                registers[register(dest)?] = registers[register(src)?]
                    .checked_neg()
                    .context("integer negation overflow")?
            }
            ["ADD", dest, left, right] => {
                registers[register(dest)?] = registers[register(left)?]
                    .checked_add(registers[register(right)?])
                    .context("integer addition overflow")?;
            }
            ["SUB", dest, left, right] => {
                registers[register(dest)?] = registers[register(left)?]
                    .checked_sub(registers[register(right)?])
                    .context("integer subtraction overflow")?;
            }
            ["SELECT_NEG_INPUT", dest, "x", negative, nonnegative] => {
                registers[register(dest)?] = if x < 0 {
                    registers[register(negative)?]
                } else {
                    registers[register(nonnegative)?]
                };
            }
            ["RETURN", src] => return Ok(registers[register(src)?]),
            _ => bail!("unsupported instruction: {line}"),
        }
    }
    bail!("program has no RETURN")
}

fn arg(args: &mut impl Iterator<Item = String>, expected: &str) -> Result<String> {
    let flag = args.next().context("missing flag")?;
    if flag != expected {
        bail!("expected {expected}, got {flag}");
    }
    args.next().context("missing value")
}

fn register(raw: &str) -> Result<usize> {
    let number = raw
        .strip_prefix('r')
        .context("invalid register")?
        .parse::<usize>()?;
    if number >= 256 {
        bail!("register out of range");
    }
    Ok(number)
}

fn parse_kv(raw: &str, header: &str) -> Result<BTreeMap<String, String>> {
    let mut lines = raw.lines();
    if lines.next() != Some(header) {
        bail!("expected {header}");
    }
    let mut map = BTreeMap::new();
    for line in lines.filter(|line| !line.trim().is_empty()) {
        let (key, value) = line.split_once('=').context("malformed artifact field")?;
        if map.insert(key.to_owned(), value.to_owned()).is_some() {
            bail!("duplicate artifact field: {key}");
        }
    }
    Ok(map)
}

fn sha256_hex(bytes: &[u8]) -> String {
    Sha256::digest(bytes)
        .iter()
        .map(|byte| format!("{byte:02x}"))
        .collect()
}

#[cfg(test)]
mod tests {
    use super::*;

    fn program(code: &str) -> String {
        format!("AXIOM-PROGRAM/2\ncode:\n{code}\nend\n")
    }

    #[test]
    fn arithmetic_fails_instead_of_wrapping() {
        let negate = program("LOAD_INPUT r0 x\nNEG r1 r0\nRETURN r1");
        assert_eq!(execute(&negate, -123).unwrap(), 123);
        assert!(execute(&negate, i64::MIN).is_err());
        let add = program("LOAD_INPUT r0 x\nCONST r1 1\nADD r2 r0 r1\nRETURN r2");
        assert!(execute(&add, i64::MAX).is_err());
        let subtract = program("LOAD_INPUT r0 x\nCONST r1 1\nSUB r2 r0 r1\nRETURN r2");
        assert!(execute(&subtract, i64::MIN).is_err());
    }

    #[test]
    fn rejects_ambiguous_artifacts_and_missing_domain() {
        assert!(parse_kv("AXIOM-IR/2\nmodule=a\nmodule=b\n", "AXIOM-IR/2").is_err());
        assert!(parse_kv("AXIOM-IR/2\nmalformed\n", "AXIOM-IR/2").is_err());
        let spec = "AXIOM-IR/2\nmodule=abs\n";
        let program = program("LOAD_INPUT r0 x\nRETURN r0");
        let proof = format!("AXIOM-PROOF/2\nverdict=VALID\ncounterexample=none\nspec.sha256={}\nprogram.sha256={}\nsoundness.scope=exact-for-supported-fragment\n", sha256_hex(spec.as_bytes()), sha256_hex(program.as_bytes()));
        assert!(authorize(spec, &program, &proof, 0).is_err());
    }
}
