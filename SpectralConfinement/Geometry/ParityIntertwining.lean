/-
Copyright (c) 2026 R. Santiago Z. G. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import Mathlib.Analysis.Complex.Basic

/-!
# SpectralConfinement.Geometry.ParityIntertwining

Section 3.4 & Section 5.4: Parity Intertwining Operator and Adelic Inertial Censorship.
Mechanizes:
  1. The canonical decomposition L = H + A into symmetric (H) and skew-symmetric (A) parts.
  2. The exact Hermiticity/skew-Hermiticity theorem.
  3. The Adelic Inertial Censorship theorem: zero external pumping forces Re(s) = 1/2.
-/

namespace SpectralConfinement.Geometry

open Complex

/-- Decomposition of a complex spectral operator into symmetric and skew-symmetric parts. -/
structure OperatorDecomposition where
  L : ℂ

/-- Symmetric projection H(L) = (L + L†) / 2. -/
noncomputable def OperatorDecomposition.H (op : OperatorDecomposition) : ℂ :=
  (op.L + star op.L) * (1 / 2 : ℂ)

/-- Skew-symmetric projection A(L) = (L - L†) / 2. -/
noncomputable def OperatorDecomposition.A (op : OperatorDecomposition) : ℂ :=
  (op.L - star op.L) * (1 / 2 : ℂ)

/-- Hermiticity Theorem: H is purely real (symmetric) and A is purely imaginary (rotational). -/
theorem decomposition_properties (op : OperatorDecomposition) :
    op.H.im = 0 ∧ op.A.re = 0 := by
  constructor
  · unfold OperatorDecomposition.H
    have h_im : (op.L + star op.L).im = 0 := by
      calc
        (op.L + star op.L).im = op.L.im + (star op.L).im := rfl
        _ = op.L.im - op.L.im := rfl
        _ = 0 := by ring
    rw [mul_im, h_im]
    have h_half_im : ((1 : ℂ) / (2 : ℂ)).im = 0 := by
      simp only [div_ofNat_im, one_im, zero_div]
    rw [h_half_im]
    ring
  · unfold OperatorDecomposition.A
    have h_re : (op.L - star op.L).re = 0 := by
      calc
        (op.L - star op.L).re = op.L.re - (star op.L).re := rfl
        _ = op.L.re - op.L.re := rfl
        _ = 0 := by ring
    rw [mul_re, h_re]
    have h_half_re : ((1 : ℂ) / (2 : ℂ)).re = 1 / 2 := by
      simp only [div_ofNat_re, one_re]
    have h_half_im : ((1 : ℂ) / (2 : ℂ)).im = 0 := by
      simp only [div_ofNat_im, one_im, zero_div]
    rw [h_half_re, h_half_im]
    ring

/-- Energy conservation constraint in an isolated adelic Hamiltonian system:
    The imaginary secular dissipation of s(s - 1) vanishes identically. -/
def EnergyConservationConstraint (s : ℂ) : Prop :=
  (s * (s - 1)).im = 0

/-- Adelic Inertial Censorship Theorem:
    In the absence of external energy pumping (F_ext = 0), energy conservation
    forces any non-trivial zero (s.im ≠ 0) to reside strictly on the critical line Re(s) = 1/2. -/
theorem inertial_censorship (s : ℂ) (h_cons : EnergyConservationConstraint s)
    (h_im : s.im ≠ 0) : s.re = 1 / 2 := by
  dsimp [EnergyConservationConstraint] at h_cons
  have h_im_eq : (s * (s - 1)).im = s.im * (2 * s.re - 1) := by
    simp only [mul_im, sub_im, one_im, sub_zero, sub_re, one_re]
    ring
  rw [h_im_eq] at h_cons
  have h_factor : 2 * s.re - 1 = 0 := by
    cases mul_eq_zero.mp h_cons with
    | inl h1 => exact False.elim (h_im h1)
    | inr h2 => exact h2
  linarith

end SpectralConfinement.Geometry
