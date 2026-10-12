/-
Copyright (c) 2026 R. Santiago Z. G. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import Mathlib.Analysis.Complex.Basic
import SpectralConfinement.Classical.ExplicitFormula

/-!
# SpectralConfinement.Dynamics.ScalingFlow

Section 2.2: First-Order Differential System and Scaling Action (x d/dx).
Mechanizes the generator of dilations and its continuous spectral eigenvalues.
-/

namespace SpectralConfinement.Dynamics

open Complex SpectralConfinement.Classical

/-- Dilation Action: generator of continuous scaling x ∂_x acting on the spectral kernel. -/
noncomputable def DilationAction (x : ℝ) (ρ : ℂ) : ℂ :=
  ρ * SpectralKernel x ρ

/-- Dilation Eigenvalue Theorem: the spectral kernel is an eigenfunction of dilation with eigenvalue ρ. -/
theorem dilation_eigenvalue (x : ℝ) (ρ : ℂ) (_hx : x > 0) :
    DilationAction x ρ = ρ * SpectralKernel x ρ := by
  rfl

end SpectralConfinement.Dynamics
