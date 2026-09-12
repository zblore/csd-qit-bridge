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

## Pins (2026-09-12)

* Lean `v4.33.0`; Mathlib `db584cd6d46c92f209a44c0f1c829460d327499d` — identical in both libraries.
* `csd-lean4` at `df177bf` (path dependency `../lean4`).
* `physlib` at `8b2b237` (path dependency `../../physlib`, i.e. `C:\zayn\physlib`).

Path dependencies are the probe configuration: both sides use the oleans they already have
(`physlib`'s from its artifact cache, `lake exe cache get` then
`LAKE_CONFIG=$PWD/lake-cache.toml lake cache get --scope=physlib-master/leanprover-lean4-v4.33.0/physlib`).
To pin by tag instead, replace the two `path` requires with

```toml
[[require]]
name = "csd-lean4"
git = "https://github.com/zblore/csd-lean4.git"
rev = "<tag>"

[[require]]
name = "Physlib"
git = "https://github.com/leanprover-community/physlib.git"
rev = "8b2b237"
```

## Build

```
lake build            # the bridge
lake build CsdQitBridgeTests   # the axiom pins
```
