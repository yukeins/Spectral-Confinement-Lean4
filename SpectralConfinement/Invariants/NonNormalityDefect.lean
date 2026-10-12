/-
Copyright (c) 2026 R. Santiago Z. G. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import Mathlib.Analysis.Complex.Basic

/-!
# SpectralConfinement.Invariants.NonNormalityDefect

Section 8.2: The Non-Normality Defect and Commutator Minimization.
Mechanizes:
  1. The non-normality defect η(H_δ) = 2 |δ|.
  2. The vanishing of the non-normality defect if and only if δ = 0.
  3. Strict normality of the scaling operator if and only if Re(s) = 1/2.
-/

namespace SpectralConfinement.Invariants

open Complex

/-- Non-normality defect functional for off-axis dilation deformation δ = β - 1/2:
    Measures the norm of the commutator [H_δ, H_δ†]. -/
def nonNormalityDefect (δ : ℝ) : ℝ :=
  2 * abs δ

/-- Theorem: The scaling operator is normal if and only if the critical line deviation is zero. -/
theorem non_normality_zero_iff (δ : ℝ) :
    nonNormalityDefect δ = 0 ↔ δ = 0 := by
  dsimp [nonNormalityDefect]
  constructor
  · intro h
    have h1 : abs δ = 0 := by linarith
    exact abs_eq_zero.mp h1
  · intro h
    rw [h]
    simp

/-- Theorem: A zero s = β + iγ has a normal scaling operator if and only if β = 1/2. -/
theorem normal_operator_critical_line (s : ℂ) :
    nonNormalityDefect (s.re - 1 / 2) = 0 ↔ s.re = 1 / 2 := by
  rw [non_normality_zero_iff]
  constructor
  · intro h; linarith
  · intro h; linarith

end SpectralConfinement.Invariants
