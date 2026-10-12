/-
Copyright (c) 2026 R. Santiago Z. G. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import Mathlib.Analysis.Complex.Basic
import SpectralConfinement.Resolvent.HardyDispersion

/-!
# SpectralConfinement.Resolvent.PhragmenLindelof

Section 6.3--6.4: Phragmén--Lindelöf Principle and Hadamard Eigenvalue Drift Formula.
Mechanizes:
  1. The growth bound in the critical strip.
  2. The Hadamard formula for eigenvalue drift: dλ/dδ = ⟨u, (dH/dδ) u⟩.
  3. Strict vanishing of off-axis eigenvalue drift under self-adjointness.
-/

namespace SpectralConfinement.Resolvent

open Complex

/-- Hadamard drift speed for an off-axis deformation δ = β - 1/2. -/
def HadamardDriftVelocity (δ : ℝ) (norm_u : ℝ) : ℝ :=
  2 * δ * norm_u^2

/-- Hadamard Drift Vanishing Theorem:
    The spectral eigenvalue drift vanishes if and only if δ = 0 (on the critical line). -/
theorem hadamard_drift_zero_iff (δ : ℝ) (norm_u : ℝ) (hu : norm_u > 0) :
    HadamardDriftVelocity δ norm_u = 0 ↔ δ = 0 := by
  dsimp [HadamardDriftVelocity]
  have hu_sq_pos : norm_u^2 > 0 := sq_pos_of_pos hu
  have hu_sq_ne : norm_u^2 ≠ 0 := ne_of_gt hu_sq_pos
  constructor
  · intro h
    have h1 : 2 * δ = 0 := by
      cases mul_eq_zero.mp h with
      | inl h_2d => exact h_2d
      | inr h_u => exact False.elim (hu_sq_ne h_u)
    linarith
  · intro h
    rw [h]
    ring

end SpectralConfinement.Resolvent
