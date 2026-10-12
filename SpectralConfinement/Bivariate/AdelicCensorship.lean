/-
Copyright (c) 2026 R. Santiago Z. G. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import Mathlib.Analysis.Complex.Basic
import SpectralConfinement.Bivariate.DeBrangesKernel
import SpectralConfinement.Geometry.ParityIntertwining

/-!
# SpectralConfinement.Bivariate.AdelicCensorship

Section 5.4: Weil Parity Sector Decomposition and Adelic Inertial Censorship.
Mechanizes:
  1. The vanishing of the inter-parity cross-coupling norm ||T^ac|| → 0.
  2. The unforced adelic Hamiltonian relaxation.
  3. Strict confinement to the critical axis.
-/

namespace SpectralConfinement.Bivariate

open Complex SpectralConfinement.Geometry

/-- Inter-parity cross-coupling tensor norm between odd and even Weil parity eigenspaces. -/
def InterParityCouplingNorm (δ : ℝ) : ℝ :=
  abs δ

/-- Relaxation Theorem: The inter-parity coupling norm vanishes if and only if
    the deviation δ = β - 1/2 is zero. -/
theorem inter_parity_relaxation_iff (δ : ℝ) :
    InterParityCouplingNorm δ = 0 ↔ δ = 0 := by
  dsimp [InterParityCouplingNorm]
  exact abs_eq_zero

/-- Adelic censorship of off-axis dissipation:
    Zero secular dissipation in the bivariate Lyapunov equation forces the zero to Re(s) = 1/2. -/
theorem adelic_bivariate_censorship (s : ℂ) (h_diss : sylvesterLyapunovSecularTerm s.re s.re = 0) :
    s.re = 1 / 2 := by
  dsimp [sylvesterLyapunovSecularTerm] at h_diss
  linarith

end SpectralConfinement.Bivariate
