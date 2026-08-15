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
    let input = &spec_doc["input.0.name"];
    let kind = &spec_doc[&format!("domain.{input}.kind")];
    match kind.as_str() {
        "unbounded" => {}
        "range" => {
            let min: i64 = spec_doc[&format!("domain.{input}.min")].parse()?;
            let max: i64 = spec_doc[&format!("domain.{input}.max")].parse()?;
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
                registers[register(dest)?] = registers[register(src)?].wrapping_neg()
            }
            ["ADD", dest, left, right] => {
                registers[register(dest)?] =
                    registers[register(left)?].wrapping_add(registers[register(right)?]);
            }
            ["SUB", dest, left, right] => {
                registers[register(dest)?] =
                    registers[register(left)?].wrapping_sub(registers[register(right)?]);
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
    for line in lines {
        if let Some((key, value)) = line.split_once('=') {
            map.insert(key.to_owned(), value.to_owned());
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
