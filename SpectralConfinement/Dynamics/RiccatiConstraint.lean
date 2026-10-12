/-
Copyright (c) 2026 R. Santiago Z. G. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import Mathlib.Analysis.Complex.Basic

/-!
# SpectralConfinement.Dynamics.RiccatiConstraint

Section 2.4: The Complex Riccati Flow and L² Divergence Constraint.
Mechanizes the vanishing of the imaginary potential component:
  Im(ρ(ρ - 1)) = 0 ↔ Re(ρ) = 1/2  (for Im(ρ) ≠ 0).
-/

namespace SpectralConfinement.Dynamics

open Complex

/-- Complex Riccati Potential V(x) = ρ(ρ - 1) / x². -/
noncomputable def RiccatiPotential (x : ℝ) (ρ : ℂ) : ℂ :=
  (ρ * (ρ - 1)) / (x : ℂ)^2

/-- Imaginary component expansion of the Riccati secular term ρ(ρ - 1). -/
lemma riccati_secular_im (ρ : ℂ) :
    (ρ * (ρ - 1)).im = ρ.im * (2 * ρ.re - 1) := by
  simp only [mul_im, sub_im, one_im, sub_zero, sub_re, one_re]
  ring

/-- Riccati L² Divergence Constraint: On the critical line Re(ρ) = 1/2, the dissipative
    imaginary term vanishes identically. -/
theorem riccati_l2_divergence_constraint (ρ : ℂ) (h : ρ.re = 1 / 2) :
    (ρ * (ρ - 1)).im = 0 := by
  rw [riccati_secular_im, h]
  ring

/-- Full iff characterization of the Riccati non-dissipative flow for non-trivial zeros:
    For any non-trivial zero (ρ.im ≠ 0), the imaginary dissipative term vanishes
    if and only if ρ.re = 1/2. -/
theorem riccati_confinement_iff (ρ : ℂ) (h_im : ρ.im ≠ 0) :
    (ρ * (ρ - 1)).im = 0 ↔ ρ.re = 1 / 2 := by
  rw [riccati_secular_im]
  constructor
  · intro h
    have h2 : 2 * ρ.re - 1 = 0 := by
      cases mul_eq_zero.mp h with
      | inl h1 => exact False.elim (h_im h1)
      | inr h1 => exact h1
    linarith
  · intro h
    rw [h]
    ring

end SpectralConfinement.Dynamics
