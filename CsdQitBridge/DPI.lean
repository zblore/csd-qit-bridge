/-
Copyright (c) 2026 Zayn Blore. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zayn Blore
-/
module

public import CsdQitBridge.SSA
public import QuantumInfo.Entropy.DPI

/-!
# The `hDPI` hypothesis of `csd-lean4`'s strong subadditivity, discharged

`QuantumInfo.strong_subadditivity_of_relEntropy_monotone` (`csd-lean4`) takes data processing of
`relEntropy` under the `C`-partial trace as an explicit hypothesis `hDPI`. `physlib` proves data
processing of the (Umegaki) relative entropy under every CPTP map
(`sandwichedRenyiEntropy_DPI_eq_one`, `QuantumInfo/Entropy/DPI.lean`, via the sandwiched Rényi
divergences at `α > 1` and continuity at `α = 1`). This file reads that back as `hDPI`:

* `ker_eq_bot_of_posDef` — a positive definite `MState` has trivial kernel, so `physlib`'s
  `ENNReal`-valued `𝐃(ρ‖σ)` is finite;
* `qRelativeEnt_toEReal_eq` — on matrices with `σ` positive definite, `physlib`'s `𝐃` is
  `csd-lean4`'s real `relEntropy` (both are `Re Tr (ρ (log ρ − log σ))`);
* `partialTraceRight_reassocABC_kronecker` — `Tr_C (A ⊗ B_BC) = A ⊗ Tr_C B_BC`;
* ★★ `relEntropy_traceC_le` — **`hDPI` in exactly the form the corpus's theorem takes**:
  `D(ρ_AB ‖ ρ_A ⊗ ρ_B) ≤ D(ρ_ABC ‖ ρ_A ⊗ ρ_BC)`;
* ★ `strong_subadditivity_of_posDef` — the corpus's own
  `strong_subadditivity_of_relEntropy_monotone` applied, its `hDPI` discharged.
-/

@[expose] public section

open Matrix
open scoped ComplexOrder Kronecker

namespace CsdQitBridge

variable {d : Type*} [Fintype d] [DecidableEq d]

/-- A positive definite state has trivial kernel. -/
theorem ker_eq_bot_of_posDef (σ : MState d) (hpos : σ.m.PosDef) : σ.M.ker = ⊥ := by
  have := hpos.toLin_ker_eq_bot
  simp [LinearMap.ker_eq_bot', HermitianMat.ker] at this ⊢
  intro m hm
  simpa only [WithLp.ofLp_eq_zero] using this m congr($hm)

/-- `physlib`'s relative entropy of states whose matrices are `M`, `N` with `N` positive definite is
`csd-lean4`'s `relEntropy`, read in `EReal`. -/
theorem qRelativeEnt_toEReal_eq (X Y : MState d) {M N : Matrix d d ℂ} (hM : M.IsHermitian)
    (hN : N.PosDef) (hX : X.m = M) (hY : Y.m = N) :
    (𝐃(X‖Y)).toEReal = ((QuantumInfo.relEntropy hM hN.1 : ℝ) : EReal) := by
  have hker : Y.M.ker ≤ X.M.ker := by
    rw [ker_eq_bot_of_posDef Y (hY ▸ hN)]
    exact bot_le
  rw [qRelativeEnt_ker hker, HermitianMat.inner_eq_re_trace, HermitianMat.mat_sub,
    HermitianMat.log, HermitianMat.log, HermitianMat.mat_cfc, HermitianMat.mat_cfc,
    MState.mat_M, MState.mat_M, hX, hY, QuantumInfo.relEntropy, hM.cfc_eq, hN.1.cfc_eq,
    Matrix.mul_sub, Matrix.trace_sub, map_sub]

section marginals

variable {a b c : Type*} [Fintype a] [Fintype b] [Fintype c]
  [DecidableEq a] [DecidableEq b] [DecidableEq c]

omit [Fintype a] [Fintype b] [DecidableEq a] [DecidableEq b] [DecidableEq c] in
/-- `Tr_C (A ⊗ B_BC) = A ⊗ Tr_C B_BC`, through the `(A B) | C` regrouping. -/
theorem partialTraceRight_reassocABC_kronecker (A : Matrix a a ℂ) (B : Matrix (b × c) (b × c) ℂ) :
    QuantumInfo.partialTraceRight (QuantumInfo.reassocABC (A ⊗ₖ B))
      = A ⊗ₖ QuantumInfo.partialTraceRight B := by
  ext ⟨i, j⟩ ⟨i', j'⟩
  simp only [QuantumInfo.partialTraceRight_apply, QuantumInfo.reassocABC, Matrix.reindex_apply,
    Matrix.submatrix_apply, Matrix.kroneckerMap_apply, Finset.mul_sum]
  rfl

omit [DecidableEq a] [DecidableEq b] [DecidableEq c] in
/-- `ρ_A ⊗ ρ_BC` is a density matrix when `ρ_ABC` is. -/
theorem kronecker_rhoA_rhoBC_trace {ρ : Matrix (a × b × c) (a × b × c) ℂ} (htr : ρ.trace = 1) :
    (QuantumInfo.rhoA ρ ⊗ₖ QuantumInfo.rhoBC ρ).trace = 1 := by
  rw [Matrix.trace_kronecker, QuantumInfo.rhoA, QuantumInfo.partialTraceRight_trace,
    QuantumInfo.rhoBC_trace, htr, one_mul]

/-- ★★ **Data processing of `relEntropy` under the `C`-partial trace**, in exactly the form
`QuantumInfo.strong_subadditivity_of_relEntropy_monotone` takes as `hDPI`:
`D(ρ_AB ‖ ρ_A ⊗ ρ_B) ≤ D(ρ_ABC ‖ ρ_A ⊗ ρ_BC)`. The content is `physlib`'s
`sandwichedRenyiEntropy_DPI_eq_one` for the channel `Tr_C ∘ assoc'`. -/
theorem relEntropy_traceC_le {ρ : Matrix (a × b × c) (a × b × c) ℂ}
    (hpsd : ρ.PosSemidef) (htr : ρ.trace = 1)
    (hpdA : (QuantumInfo.rhoA ρ).PosDef) (hpdB : (QuantumInfo.rhoB ρ).PosDef)
    (hpdBC : (QuantumInfo.rhoBC ρ).PosDef) :
    ∀ (hpdA' : (QuantumInfo.partialTraceRight (QuantumInfo.rhoAB ρ)).PosDef),
      QuantumInfo.relEntropy (QuantumInfo.rhoAB_posSemidef hpsd).1
          (Matrix.PosDef.kronecker hpdA' hpdB).1
        ≤ QuantumInfo.relEntropy hpsd.1 (Matrix.PosDef.kronecker hpdA hpdBC).1 := by
  intro hpdA'
  -- the states
  set X : MState (a × b × c) := toMState hpsd htr with hXdef
  set Y : MState (a × b × c) :=
    toMState (Matrix.PosDef.kronecker hpdA hpdBC).posSemidef (kronecker_rhoA_rhoBC_trace htr)
    with hYdef
  -- physlib's DPI, twice: the regrouping `assoc'` and the partial trace `Tr_C`
  set Φ₁ := CPTPMap.assoc' (d₁ := a) (d₂ := b) (d₃ := c) with hΦ₁
  set Φ₂ := CPTPMap.traceRight (d₁ := a × b) (d₂ := c) with hΦ₂
  have h₁ := sandwichedRenyiEntropy_DPI_eq_one X Y Φ₁
  have h₂ := sandwichedRenyiEntropy_DPI_eq_one (Φ₁ X) (Φ₁ Y) Φ₂
  rw [hΦ₁, CPTPMap.assoc'_eq_MState_assoc', CPTPMap.assoc'_eq_MState_assoc'] at h₁ h₂
  rw [hΦ₂, CPTPMap.traceRight_eq_MState_traceRight, CPTPMap.traceRight_eq_MState_traceRight] at h₂
  have h : 𝐃(X.assoc'.traceRight‖Y.assoc'.traceRight) ≤ 𝐃(X‖Y) := h₂.trans h₁
  -- read both sides in the corpus's vocabulary
  have hL : (𝐃(X.assoc'.traceRight‖Y.assoc'.traceRight)).toEReal
      = ((QuantumInfo.relEntropy (QuantumInfo.rhoAB_posSemidef hpsd).1
          (Matrix.PosDef.kronecker hpdA' hpdB).1 : ℝ) : EReal) := by
    refine qRelativeEnt_toEReal_eq _ _ (QuantumInfo.rhoAB_posSemidef hpsd).1
      (Matrix.PosDef.kronecker hpdA' hpdB) ?_ ?_
    · rw [m_traceRight, m_assoc', hXdef, m_toMState]; rfl
    · rw [m_traceRight, m_assoc', hYdef, m_toMState, partialTraceRight_reassocABC_kronecker,
        QuantumInfo.rhoA, QuantumInfo.rhoA_eq_traceB_AB, ← QuantumInfo.rhoB_consistency]
  have hR : (𝐃(X‖Y)).toEReal
      = ((QuantumInfo.relEntropy hpsd.1 (Matrix.PosDef.kronecker hpdA hpdBC).1 : ℝ) : EReal) :=
    qRelativeEnt_toEReal_eq _ _ hpsd.1 (Matrix.PosDef.kronecker hpdA hpdBC) rfl rfl
  have h' : (𝐃(X.assoc'.traceRight‖Y.assoc'.traceRight)).toEReal ≤ (𝐃(X‖Y)).toEReal :=
    EReal.coe_ennreal_le_coe_ennreal_iff.mpr h
  rw [hL, hR] at h'
  exact EReal.coe_le_coe_iff.mp h'

/-- ★ The corpus's own strong subadditivity, its `hDPI` discharged by `relEntropy_traceC_le`.
(`strong_subadditivity` in `SSA.lean` reaches the same conclusion with no support hypotheses;
this is the corpus's theorem *applied*.) -/
theorem strong_subadditivity_of_posDef {ρ : Matrix (a × b × c) (a × b × c) ℂ}
    (hpsd : ρ.PosSemidef) (htr : ρ.trace = 1)
    (hpdA : (QuantumInfo.rhoA ρ).PosDef) (hpdB : (QuantumInfo.rhoB ρ).PosDef)
    (hpdBC : (QuantumInfo.rhoBC ρ).PosDef) :
    QuantumInfo.vonNeumannEntropy hpsd.1 + QuantumInfo.vonNeumannEntropy hpdB.1
      ≤ QuantumInfo.vonNeumannEntropy (QuantumInfo.rhoAB_posSemidef hpsd).1
        + QuantumInfo.vonNeumannEntropy hpdBC.1 :=
  QuantumInfo.strong_subadditivity_of_relEntropy_monotone hpsd htr hpdA hpdB hpdBC
    (relEntropy_traceC_le hpsd htr hpdA hpdB hpdBC)

end marginals

end CsdQitBridge
