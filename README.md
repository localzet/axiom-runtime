# axiom-runtime

A tiny proof-gated VM. It refuses to execute a program unless a `VALID` receipt binds exactly to the supplied
specification and program hashes.

> **Maturity:** research prototype v0.1. The default verifier proves properties by exhaustive evaluation over an
> explicitly finite input domain. A VALID receipt is therefore a theorem about that bounded model, not a claim of
> unbounded program correctness.

```bash
cargo run -- run --spec spec.aix --program candidate.axp --proof candidate.axproof --x -7
```

This is the seed of the Axiom trusted computing base: **generation is not authority; verification is authority**.
