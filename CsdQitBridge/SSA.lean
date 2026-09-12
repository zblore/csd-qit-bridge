/-
Copyright (c) 2026 Zayn Blore. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zayn Blore
-/
module

public import CsdLean4.Mathlib.QuantumInfo.StrongSubadditivity
public import QuantumInfo.Entropy.SSA

/-!
# Strong subadditivity, unconditional, in `csd-lean4`'s vocabulary

`csd-lean4` proves strong subadditivity from an explicit data-processing hypothesis `hDPI`
(`QuantumInfo.strong_subadditivity_of_relEntropy_monotone`) and never discharges it: the
operator-convexity summit behind it (Lieb) is absent from Mathlib (`specs/lieb-dpi-scoping.md`).
`physlib` proves it unconditionally (`Sᵥₙ_strong_subadditivity`, `QuantumInfo/Entropy/SSA.lean`,
on the same Lean and Mathlib pins, foundational triple only — Gate 0, 2026-09-12).

This bridge packs a `csd-lean4` density matrix into a `physlib` `MState` and reads the theorem back:

* `toMState` — a `PosSemidef` unit-trace matrix as an `MState`;
* `Sᵥₙ_eq` — `physlib`'s `Sᵥₙ` is `csd-lean4`'s `vonNeumannEntropy` on the same matrix
  (both are `Re Tr (cfc negMulLog ρ)`);
* the marginals agree entrywise (`m_traceLeft`, `m_traceRight`, `m_assoc'`), so
  `ρ₁₂ = rhoAB`, `ρ₂₃ = rhoBC`, `ρ₂ = rhoB`;
* ★★ `strong_subadditivity` — `S(ρ_ABC) + S(ρ_B) ≤ S(ρ_AB) + S(ρ_BC)` for **every** density matrix,
  no support hypothesis and no `hDPI`.

Neither library is modified; `csd-lean4` keeps its Mathlib-only footprint.
-/

@[expose] public section

open Matrix
open scoped ComplexOrder

namespace CsdQitBridge

variable {d : Type*} [Fintype d] [DecidableEq d]

/-- A `csd-lean4` density matrix (positive semidefinite, unit trace) as a `physlib` `MState`. -/
noncomputable def toMState {ρ : Matrix d d ℂ} (hpsd : ρ.PosSemidef) (htr : ρ.trace = 1) :
    MState d where
  M := { val := ρ, property := hpsd.1 }
  nonneg := HermitianMat.zero_le_iff.mpr hpsd
  tr := by
    show RCLike.re ρ.trace = 1
    rw [htr, RCLike.one_re]

@[simp]
theorem m_toMState {ρ : Matrix d d ℂ} (hpsd : ρ.PosSemidef) (htr : ρ.trace = 1) :
    (toMState hpsd htr).m = ρ := rfl

/-- `physlib`'s von Neumann entropy of a state whose matrix is `M` is `csd-lean4`'s
`vonNeumannEntropy` of `M`. -/
theorem Sᵥₙ_eq (σ : MState d) {M : Matrix d d ℂ} (hM : M.IsHermitian) (h : σ.m = M) :
    Sᵥₙ σ = QuantumInfo.vonNeumannEntropy hM := by
  rw [Sᵥₙ_eq_trace_cfc_negMulLog, HermitianMat.trace_eq_re_trace, HermitianMat.mat_cfc,
    MState.mat_M, h, QuantumInfo.vonNeumannEntropy_eq_re_trace_cfc, hM.cfc_eq]

section marginals

variable {a b c : Type*} [Fintype a] [Fintype b] [Fintype c]
  [DecidableEq a] [DecidableEq b] [DecidableEq c]

theorem m_traceLeft (σ : MState (a × b)) :
    σ.traceLeft.m = QuantumInfo.partialTraceLeft σ.m := rfl

theorem m_traceRight (σ : MState (a × b)) :
    σ.traceRight.m = QuantumInfo.partialTraceRight σ.m := rfl

theorem m_assoc' (σ : MState (a × b × c)) :
    σ.assoc'.m = QuantumInfo.reassocABC σ.m := by
  ext ⟨⟨i, j⟩, k⟩ ⟨⟨i', j'⟩, k'⟩
  rfl

end marginals

/-- ★★ **Strong subadditivity, unconditional**, in `csd-lean4`'s vocabulary: for every density
matrix `ρ` on `a × b × c`, `S(ρ_ABC) + S(ρ_B) ≤ S(ρ_AB) + S(ρ_BC)`. No support hypothesis, no
`hDPI`: the data-processing content is `physlib`'s `Sᵥₙ_strong_subadditivity`. -/
theorem strong_subadditivity {a b c : Type*} [Fintype a] [Fintype b] [Fintype c]
    [DecidableEq a] [DecidableEq b] [DecidableEq c]
    {ρ : Matrix (a × b × c) (a × b × c) ℂ} (hpsd : ρ.PosSemidef) (htr : ρ.trace = 1) :
    QuantumInfo.vonNeumannEntropy hpsd.1
      + QuantumInfo.vonNeumannEntropy
          (QuantumInfo.partialTraceLeft_posSemidef (QuantumInfo.rhoAB_posSemidef hpsd)).1
      ≤ QuantumInfo.vonNeumannEntropy (QuantumInfo.rhoAB_posSemidef hpsd).1
        + QuantumInfo.vonNeumannEntropy (QuantumInfo.rhoBC_posSemidef hpsd).1 := by
  have h := Sᵥₙ_strong_subadditivity (toMState hpsd htr)
  dsimp only at h
  rw [Sᵥₙ_eq _ hpsd.1 rfl,
    Sᵥₙ_eq _ (QuantumInfo.partialTraceLeft_posSemidef (QuantumInfo.rhoAB_posSemidef hpsd)).1
      (by rw [m_traceRight, m_traceLeft, m_toMState]
          exact (QuantumInfo.rhoB_consistency ρ).symm),
    Sᵥₙ_eq _ (QuantumInfo.rhoAB_posSemidef hpsd).1
      (by rw [m_traceRight, m_assoc', m_toMState]; rfl),
    Sᵥₙ_eq _ (QuantumInfo.rhoBC_posSemidef hpsd).1 (by rw [m_traceLeft, m_toMState]; rfl)] at h
  exact h

end CsdQitBridge
