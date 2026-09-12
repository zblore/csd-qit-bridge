# csd-qit-bridge

A bridge package that reads `physlib`'s unconditional strong subadditivity and relative-entropy
data processing back into `csd-lean4`'s vocabulary. Neither library is modified; `csd-lean4`
keeps its Mathlib-only footprint (`specs/lieb-dpi-scoping.md`, route (b), architecture of
2026-07-31).

## What it exports (`CsdQitBridge`, foundational triple only)

| Theorem | Statement |
|---|---|
| `strong_subadditivity` | `S(ρ_ABC) + S(ρ_B) ≤ S(ρ_AB) + S(ρ_BC)` for every density matrix on `a × b × c`, in `QuantumInfo.vonNeumannEntropy` / `rhoAB` / `rhoBC` / `partialTraceLeft` vocabulary; no support hypothesis. |
| `relEntropy_traceC_le` | Data processing of `QuantumInfo.relEntropy` under the `C`-partial trace, in exactly the form `QuantumInfo.strong_subadditivity_of_relEntropy_monotone` takes as its `hDPI` hypothesis. |
| `strong_subadditivity_of_posDef` | The corpus's own theorem applied, `hDPI` discharged. |
| `Sᵥₙ_eq`, `qRelativeEnt_toEReal_eq` | `physlib`'s `Sᵥₙ` and `𝐃` are the corpus's `vonNeumannEntropy` and `relEntropy` on the same matrices. |

Pins are checked by `CsdQitBridge/Tests/AxiomAudit.lean` (`lake build CsdQitBridgeTests`).

## Pins

`lakefile.toml` requires both libraries by pinned git revision (see the comment there): the two
pins must agree on Lean and Mathlib, and at the current pins both resolve Mathlib to
`db584cd6d46c92f209a44c0f1c829460d327499d` on Lean `v4.33.0`. Bump them together, never one
alone. The Lean toolchain is `lean-toolchain`.

| Dependency | Revision |
|---|---|
| `csd-lean4` | `6b88f5f50fadc20ccd1a624d50c1eef163179c10` |
| `physlib` | `8b2b23701c07409f882c49e0bd290a214e44450c` |

The bridge imports only `CsdLean4.Mathlib.QuantumInfo.StrongSubadditivity` from `csd-lean4` and
`QuantumInfo.Entropy.SSA`, `QuantumInfo.Entropy.DPI` from `physlib`.

## Build

```
lake exe cache get               # Mathlib's oleans
lake build                       # the bridge; csd-lean4 and physlib compile from source
lake build CsdQitBridgeTests     # the axiom pins
```

Neither dependency publishes oleans that a dependent workspace can restore, so the first build
compiles the `csd-lean4` corpus and physlib's SSA cone (about an hour on a laptop, less in CI).
For local work against a checkout of `csd-lean4` and physlib, the two `git` requires can be
replaced by `path` requires pointing at those checkouts; that is how this package was developed
and is not the published configuration.

## The permanent cost

Depending on two libraries by revision means every Lean or Mathlib bump opens a window in which
this package does not build until both have landed on the new pins
(`specs/lieb-dpi-scoping.md` §3b in `csd-lean4`). That tax is paid here, by whoever bumps the
pins, and nowhere in `csd-lean4`.
