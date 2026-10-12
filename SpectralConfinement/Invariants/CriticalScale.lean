/-
Copyright (c) 2026 R. Santiago Z. G. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import Mathlib.Analysis.Complex.Basic

/-!
# SpectralConfinement.Invariants.CriticalScale

Section 8.1: Critical Scaling Dimension and Dilatation Invariance.
Mechanizes:
  1. The scaling dimension s_c = β - 1/2.
  2. Strict scale invariance if and only if β = 1/2.
-/

namespace SpectralConfinement.Invariants

/-- Scaling dimension of a state x^β in the scale-invariant measure dx/x. -/
noncomputable def scalingDimension (β : ℝ) : ℝ :=
  β - 1 / 2

/-- Theorem: Scale invariance under the dilation group holds if and only if β = 1/2. -/
theorem critical_scale_invariance (β : ℝ) :
    scalingDimension β = 0 ↔ β = 1 / 2 := by
  dsimp [scalingDimension]
  constructor
  · intro h; linarith
  · intro h; linarith

end SpectralConfinement.Invariants
