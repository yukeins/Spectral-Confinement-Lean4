/-
Copyright (c) 2026 R. Santiago Z. G. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Exp

/-!
# SpectralConfinement.Positivity.PrimeGramMatrix

Section 7.1: Discrete Arithmetic Mesh and the Prime Gram Matrix.
Mechanizes:
  1. Unit norm of complex prime logarithm phase rotations exp(i Δγ ln p).
  2. The exact scalar bound on Gram matrix elements:
     |G_{jk}(p)|² = (1 / (sqrt(p) ln p))².
-/

namespace SpectralConfinement.Positivity

open Complex

/-- Norm square of the unitary exponential phase for real exponents is identically 1. -/
lemma normSq_exp_I_mul_real (x : ℝ) : Complex.normSq (Complex.exp (Complex.I * (x : ℂ))) = 1 := by
  have h_comm : Complex.I * (x : ℂ) = (x : ℂ) * Complex.I := mul_comm _ _
  rw [h_comm, Complex.exp_mul_I]
  have h_re : (Complex.cos ↑x + Complex.sin ↑x * Complex.I).re = Real.cos x := by 
    simp only [Complex.add_re, Complex.mul_re, Complex.cos_ofReal_re, 
      Complex.sin_ofReal_re, Complex.sin_ofReal_im, Complex.I_re, 
      Complex.I_im, sub_zero, mul_zero, mul_one, add_zero]
  have h_im : (Complex.cos ↑x + Complex.sin ↑x * Complex.I).im = Real.sin x := by 
    simp only [Complex.add_im, Complex.mul_im, Complex.sin_ofReal_re, 
      Complex.cos_ofReal_im, Complex.sin_ofReal_im, Complex.I_re, 
      Complex.I_im, zero_add, mul_zero, mul_one, add_zero]
  have h_normSq : Complex.normSq (Complex.cos ↑x + Complex.sin ↑x * Complex.I) = 
      (Complex.cos ↑x + Complex.sin ↑x * Complex.I).re * 
      (Complex.cos ↑x + Complex.sin ↑x * Complex.I).re + 
      (Complex.cos ↑x + Complex.sin ↑x * Complex.I).im * 
      (Complex.cos ↑x + Complex.sin ↑x * Complex.I).im := rfl
  rw [h_normSq, h_re, h_im]
  have h_trig := Real.cos_sq_add_sin_sq x
  have h_sq1 : Real.cos x * Real.cos x = Real.cos x ^ 2 := by ring
  have h_sq2 : Real.sin x * Real.sin x = Real.sin x ^ 2 := by ring
  rw [h_sq1, h_sq2]
  exact h_trig

/-- Gram Matrix Element Envelope Bound:
    The magnitude of each summand over primes is strictly determined by the real decay envelope. -/
theorem gram_matrix_element_bound (p : ℝ) (_hp : p > 1) (Δγ : ℝ) :
    Complex.normSq ( (1 / (Real.sqrt p * Real.log p) : ℂ) * 
      Complex.exp (Complex.I * (Δγ * Real.log p)) ) = 
      (1 / (Real.sqrt p * Real.log p))^2 := by
  rw [Complex.normSq_mul]
  have h_exp := normSq_exp_I_mul_real (Δγ * Real.log p)
  have h_coe : Complex.normSq ↑(1 / (Real.sqrt p * Real.log p)) = 
      (1 / (Real.sqrt p * Real.log p))^2 := by
    calc
      Complex.normSq ↑(1 / (Real.sqrt p * Real.log p)) = 
          (↑(1 / (Real.sqrt p * Real.log p)) : ℂ).re * 
          (↑(1 / (Real.sqrt p * Real.log p)) : ℂ).re + 
          (↑(1 / (Real.sqrt p * Real.log p)) : ℂ).im * 
          (↑(1 / (Real.sqrt p * Real.log p)) : ℂ).im := rfl
      _ = (1 / (Real.sqrt p * Real.log p)) * 
          (1 / (Real.sqrt p * Real.log p)) + 0 * 0 := by 
        rw [Complex.ofReal_re, Complex.ofReal_im]
      _ = (1 / (Real.sqrt p * Real.log p))^2 := by ring
  have h_target : (1 / (↑(Real.sqrt p) * ↑(Real.log p)) : ℂ) = 
      ↑(1 / (Real.sqrt p * Real.log p)) := by push_cast; rfl
  have h_exp_target : (↑Δγ : ℂ) * ↑(Real.log p) = 
      ↑(Δγ * Real.log p) := by push_cast; rfl
  rw [h_target, h_exp_target, h_exp, mul_one, h_coe]

end SpectralConfinement.Positivity
