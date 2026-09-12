/-
Copyright (c) 2026 Zayn Blore. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zayn Blore
-/
module

public import CsdQitBridge

/-!
# Axiom audit for the bridge

Every exported theorem, and the two `physlib` theorems it rests on, depend on the foundational
triple only. `lake build CsdQitBridge.Tests.AxiomAudit` fails if any pin drifts.
-/

/-- info: 'CsdQitBridge.strong_subadditivity' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CsdQitBridge.strong_subadditivity

/-- info: 'CsdQitBridge.relEntropy_traceC_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CsdQitBridge.relEntropy_traceC_le

/-- info: 'CsdQitBridge.strong_subadditivity_of_posDef' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CsdQitBridge.strong_subadditivity_of_posDef

/-- info: 'CsdQitBridge.qRelativeEnt_toEReal_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CsdQitBridge.qRelativeEnt_toEReal_eq

/-- info: 'CsdQitBridge.Sᵥₙ_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CsdQitBridge.Sᵥₙ_eq

/-- info: 'Sᵥₙ_strong_subadditivity' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Sᵥₙ_strong_subadditivity

/-- info: 'sandwichedRenyiEntropy_DPI_eq_one' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms sandwichedRenyiEntropy_DPI_eq_one

/-- info: 'qRelativeEnt_joint_convexity' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms qRelativeEnt_joint_convexity
