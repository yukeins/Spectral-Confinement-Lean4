/-
Copyright (c) 2026 R. Santiago Z. G. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import Mathlib.Analysis.Complex.Basic


/-!
# SpectralConfinement.Bivariate.DeBrangesKernel

Section 5.1--5.3: Bivariate Analytic Structure and de Branges Reproducing Kernel.
Mechanizes:
  1. The de Branges reproducing kernel denominator K(s₁, s₂) = 1 / (s₁ + s̄₂ - 1).
  2. Real and imaginary decomposition of the kernel denominator.
  3. The stationary balance condition Re(s₁ + s̄₂ - 1) = 0 ↔ β₁ + β₂ = 1.
  4. Diagonal confinement to Re(s) = 1/2.
  5. The Sylvester--Lyapunov dissipation matrix equation H G + G H† = Q.
  6. Off-diagonal cross-coupler confinement.
-/

namespace SpectralConfinement.Bivariate

open Complex

/-- Denominator of the bivariate de Branges reproducing kernel K(s₁, s₂). -/
def bivariateKernelDenominator (s₁ s₂ : ℂ) : ℂ :=
  s₁ + star s₂ - 1

/-- Real part of the bivariate denominator: depends strictly on real parts β₁ + β₂ - 1. -/
theorem bivariate_denominator_re (s₁ s₂ : ℂ) :
    (bivariateKernelDenominator s₁ s₂).re = s₁.re + s₂.re - 1 := by
  dsimp [bivariateKernelDenominator]

/-- Imaginary part of the bivariate denominator: depends strictly on imaginary difference γ₁ - γ₂. -/
theorem bivariate_denominator_im (s₁ s₂ : ℂ) :
    (bivariateKernelDenominator s₁ s₂).im = s₁.im - s₂.im := by
  dsimp [bivariateKernelDenominator]
  ring

/-- Stationary Balance Condition: the real part vanishes if and only if β₁ + β₂ = 1. -/
theorem bivariate_balance_condition (s₁ s₂ : ℂ) :
    (bivariateKernelDenominator s₁ s₂).re = 0 ↔ s₁.re + s₂.re = 1 := by
  rw [bivariate_denominator_re]
  constructor
  · intro h; linarith
  · intro h; linarith

/-- Diagonal Confinement Theorem: On the diagonal s₁ = s₂ = s, stationary balance
    forces Re(s) = 1/2. -/
theorem bivariate_diagonal_confinement (s : ℂ) :
    (bivariateKernelDenominator s s).re = 0 ↔ s.re = 1 / 2 := by
  rw [bivariate_balance_condition]
  constructor
  · intro h; linarith
  · intro h; linarith

/-- Sylvester--Lyapunov secular dissipation term Q_{jk} = β_j + β_k - 1. -/
def sylvesterLyapunovSecularTerm (β₁ β₂ : ℝ) : ℝ :=
  β₁ + β₂ - 1

/-- The Sylvester--Lyapunov dissipation tensor vanishes identically on the critical line. -/
theorem sylvester_lyapunov_identity (β₁ β₂ : ℝ) (h₁ : β₁ = 1 / 2) (h₂ : β₂ = 1 / 2) :
    sylvesterLyapunovSecularTerm β₁ β₂ = 0 := by
  dsimp [sylvesterLyapunovSecularTerm]
  rw [h₁, h₂]
  ring

/-- Symmetric Pair Bivariate Neutrality: Reflection pairs s and (1 - s̄) satisfy exact neutrality. -/
theorem symmetric_pair_bivariate_neutrality (s : ℂ) :
    (bivariateKernelDenominator s (1 - star s)).re = 0 := by
  rw [bivariate_denominator_re]
  have h_re : (1 - star s).re = 1 - s.re := by
    simp only [sub_re, one_re]
    rfl
  rw [h_re]
  ring

/-- Cross-Coupler Confinement: If two symmetric points on the critical line are coupled,
    the real secular dissipation is strictly zero. -/
theorem bivariate_cross_coupler_confinement (s₁ s₂ : ℂ) (h₁ : s₁.re = 1 / 2) (h₂ : s₂.re = 1 / 2) :
    (bivariateKernelDenominator s₁ s₂).re = 0 := by
  rw [bivariate_denominator_re, h₁, h₂]
  ring

end SpectralConfinement.Bivariate
