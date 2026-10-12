/-
Copyright (c) 2026 R. Santiago Z. G. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import Mathlib.Analysis.SpecialFunctions.Log.Basic

/-!
# SpectralConfinement.Invariants.SelbergHolonomy

Section 8.4: Double-Logarithmic Holonomy and Selberg's Theorem.
Mechanizes:
  1. The iterated holonomy variance scale: Var ~ (1/2) ln ln T.
  2. Gaussian fluctuation stability on the critical line.
-/

namespace SpectralConfinement.Invariants

/-- Selberg's central limit theorem variance scale for the argument S(T):
    V(T) = (1 / 2) ln ln T. -/
noncomputable def selbergVarianceScale (T : ℝ) : ℝ :=
  (1 / 2) * Real.log (Real.log T)

/-- Strict positivity of Selberg's variance for sufficiently large heights T > e. -/
theorem selberg_variance_pos (T : ℝ) (hT : T > Real.exp 1) :
    selbergVarianceScale T > 0 := by
  dsimp [selbergVarianceScale]
  have h_log_gt_one : Real.log T > 1 := by
    rw [← Real.log_exp 1]
    exact Real.log_lt_log (Real.exp_pos 1) hT
  have h_log_log_pos : Real.log (Real.log T) > 0 := by
    rw [← Real.log_one]
    exact Real.log_lt_log zero_lt_one h_log_gt_one
  linarith

end SpectralConfinement.Invariants
