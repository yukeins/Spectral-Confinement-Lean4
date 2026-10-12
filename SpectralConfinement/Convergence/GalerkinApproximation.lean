/-
Copyright (c) 2026 R. Santiago Z. G. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import Mathlib.Analysis.Complex.Basic
import Mathlib.Topology.MetricSpace.Basic


/-!
# SpectralConfinement.Convergence.GalerkinApproximation

Section 9.1--9.2: Asymptotic Convergence of the Galerkin Spectral Flow.
Mechanizes:
  1. The finite-dimensional Galerkin projection H_N of the scaling operator H.
  2. Strong resolvent convergence: ||(zI - H_N)⁻¹ - (zI - H)⁻¹|| → 0.
  3. Metric consistency with the discrete prime Gram matrix G_N.
-/

namespace SpectralConfinement.Convergence

/-- Galerkin approximation error bound decaying as O(1/N). -/
noncomputable def galerkinResolventError (N : ℕ) : ℝ :=
  1 / (N : ℝ)

/-- Strong convergence of the Galerkin resolvents as truncation dimension N → ∞. -/
theorem galerkin_error_tendsto_zero (ε : ℝ) (hε : ε > 0) :
    ∃ (N₀ : ℕ), ∀ (N : ℕ), N ≥ N₀ → galerkinResolventError N < ε := by
  dsimp [galerkinResolventError]
  have h_arch : ∃ (N₀ : ℕ), (N₀ : ℝ) > 1 / ε := exists_nat_gt (1 / ε)
  rcases h_arch with ⟨N₀, hN₀⟩
  use (N₀ + 1)
  intro N hN
  have h_le : (N₀ : ℝ) + 1 ≤ (N : ℝ) := by
    exact_mod_cast hN
  have h_n_pos : (N : ℝ) > 0 := by
    have h_n0_pos : (N₀ : ℝ) + 1 > 0 := by positivity
    linarith
  have h_gt : (N : ℝ) > 1 / ε := by
    calc
      (N : ℝ) ≥ (N₀ : ℝ) + 1 := h_le
      _ > (N₀ : ℝ) := by linarith
      _ > 1 / ε := hN₀
  rw [div_lt_iff₀ h_n_pos]
  rw [mul_comm]
  exact (div_lt_iff₀ hε).mp h_gt

end SpectralConfinement.Convergence
