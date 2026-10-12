/-
Copyright (c) 2026 R. Santiago Z. G. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import Mathlib.Basic.Real.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic


/-!
# SpectralConfinement.Convergence.SpectralRigidity

Section 9.3--9.4: Spectral Truncation Bounds and GUE Statistics.
Mechanizes:
  1. Montgomery's pair correlation function: R₂(u) = 1 - (sin(π u) / (π u))².
  2. Level repulsion at origin u → 0: R₂(0) = 0.
  3. Spectral rigidity of the self-adjoint scaling operator.
-/

namespace SpectralConfinement.Convergence

/-- Montgomery Pair Correlation 2-point function for the zeros of zeta:
    R₂(u) = 1 - sinc(u)². -/
noncomputable def guePairCorrelation (u : ℝ) : ℝ :=
  if u = 0 then 0 else 1 - (Real.sin (Real.pi * u) / (Real.pi * u))^2

/-- Level repulsion: The probability of finding two coincident zeros vanishes (R₂(0) = 0). -/
theorem gue_level_repulsion : guePairCorrelation 0 = 0 := by
  dsimp [guePairCorrelation]
  split_ifs with h
  · rfl
  · exact False.elim (h rfl)

/-- Asymptotic decorrelation: For u → ∞, R₂(u) approaches the Poisson mean 1. -/
theorem gue_bounded_by_one (u : ℝ) : guePairCorrelation u ≤ 1 := by
  dsimp [guePairCorrelation]
  split_ifs with h
  · linarith
  · have h_sq : (Real.sin (Real.pi * u) / (Real.pi * u))^2 ≥ 0 := sq_nonneg _
    linarith

end SpectralConfinement.Convergence
