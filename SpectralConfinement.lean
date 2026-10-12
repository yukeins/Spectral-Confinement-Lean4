/-
Copyright (c) 2026 R. Santiago Z. G. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

-- Section 1: Classical Meromorphic Zeta Embedding
import SpectralConfinement.Classical.ZetaFunction
import SpectralConfinement.Classical.ExplicitFormula

-- Section 2: Scaling Dynamics and Complex Riccati Flow
import SpectralConfinement.Dynamics.ScalingFlow
import SpectralConfinement.Dynamics.RiccatiConstraint
import SpectralConfinement.Dynamics.SobolevSpace

-- Section 3: Arithmetic Lie--Poisson Geometry & Parity
import SpectralConfinement.Geometry.LiePoissonAlgebra
import SpectralConfinement.Geometry.ParityIntertwining
import SpectralConfinement.Geometry.WittAlgebra

-- Section 4: Tensor Contraction & Symmetry Breaking
import SpectralConfinement.TensorField.SpectralQuartet
import SpectralConfinement.TensorField.SymmetryBreaking

-- Section 5: Bivariate Structure & de Branges Kernel
import SpectralConfinement.Bivariate.DeBrangesKernel
import SpectralConfinement.Bivariate.AdelicCensorship

-- Section 6: Resolvent Holomorphy & Kramers--Kronig
import SpectralConfinement.Resolvent.HardyDispersion
import SpectralConfinement.Resolvent.PhragmenLindelof

-- Section 7: Arithmetic Positivity & Prime Gram Coercivity
import SpectralConfinement.Positivity.PrimeGramMatrix
import SpectralConfinement.Positivity.MontgomeryVaughanBound
import SpectralConfinement.Positivity.GershgorinCoercivity

-- Section 8: Deep Spectral Invariants
import SpectralConfinement.Invariants.CriticalScale
import SpectralConfinement.Invariants.NonNormalityDefect
import SpectralConfinement.Invariants.MonodromyWinding
import SpectralConfinement.Invariants.SelbergHolonomy

-- Section 9: Convergence of the Spectral Flow
import SpectralConfinement.Convergence.GalerkinApproximation
import SpectralConfinement.Convergence.SpectralRigidity

-- Section 5.4 / Positivity: Weil Quadratic Falsification
import SpectralConfinement.WeilFunctional.QuadraticOscillation
import SpectralConfinement.WeilFunctional.PositiveConeBridge

-- Section 10: Master Confinement Theorem
import SpectralConfinement.Confinement.MasterTheorem

/-!
# SpectralConfinement Library (Lean 4 Formal Architecture)

Comprehensive mechanical formalization of the Riemann Hypothesis via the
Hamiltonian Scaling Operator, de Branges Reproducing Kernels, and Prime Arithmetic Coercivity.

Authors: R. Santiago Z. G.
Monograph Reference: rh_origin_pure_paperRH_integrated.tex
-/
