/-
Copyright (c) 2026 Alex Masero. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Masero
-/
import Dahlquist.Characteristic
import Dahlquist.Defect

/-!
# Order Conditions for Linear Multistep Methods

This module introduces the order conditions for
linear multistep methods.

The moment residuals C_q are the coefficients appearing in
the formal Taylor expansion of the local truncation defect.

A method has order at least p when C_0 = ... = C_p = 0.
It has exact order p if, additionally, C_{p+1} != 0.
Consistency corresponds to order at least one.
-/

namespace Dahlquist.LinearMultistep

namespace Coefficients

variable {k : ℕ} (M : Coefficients k)

/-- Moment residuals for a linear multistep method. -/
noncomputable def momentResidual (q : ℕ) : ℝ :=
  M.defect (fun x => x ^ q / (Nat.factorial q : ℝ)) 0 1

/-- The 0th moment residual equals the sum of the alpha coefficients. -/
theorem momentResidual_zero : M.momentResidual 0 = ∑ j : Fin (k + 1), M.alpha j := by
  simp [momentResidual, defect]

/-- Algebraic expression for the (q + 1)-th moment residual. -/
theorem momentResidual_succ (q : ℕ) : M.momentResidual (q + 1) =
  ((∑ j : Fin (k + 1), M.alpha j * (j : ℝ) ^ (q + 1)) - (q + 1 : ℝ) *
  (∑ j : Fin (k + 1), M.beta j * (j : ℝ) ^ q)) / (Nat.factorial (q + 1) : ℝ) := by
  simp [momentResidual, defect]
  simp [sub_div, Finset.sum_div, Finset.mul_sum]
  grind

/-- Expresses the defect of a Taylor polynomial as a sum of
moment residuals C_q multiplied by a_q * h^q. -/
theorem defect_taylorPolynomial_residuals (a : ℕ → ℝ) (p : ℕ) (h : ℝ) :
  M.defect (fun x => (taylorPolynomial a p).eval x) 0 h =
  a 0 * M.momentResidual 0 + ∑ q ∈ Finset.range p, a (q + 1) *
  M.momentResidual (q + 1) * h ^ (q + 1) := by
  rw [M.defect_taylorPolinomial, M.momentResidual_zero]
  congr 1
  apply Finset.sum_congr rfl
  intro q _
  rw [M.momentResidual_succ]
  ring


/-- A linear multistep method has order at least p if all moment
residuals from degree zero to p are equal to zero. -/
def HasOrderAtLeast (p : ℕ) : Prop :=
  ∀ q : ℕ, q ≤ p → M.momentResidual q = 0

/-- A linear multistep method has exact order p if its moment
residuals from degree zero to p are equal to zero, but the p+1 is not. -/
def HasExactOrder (p : ℕ) : Prop :=
  M.HasOrderAtLeast p ∧ M.momentResidual (p + 1) ≠ 0

/-- A linear multisept method is consistent if it has order at least one. -/
def Consistent : Prop :=
  M.HasOrderAtLeast 1

/-- Consistency characterized by the characteristic polynomials. -/
theorem consistent_iff_characteristic :
  M.Consistent ↔ Polynomial.eval 1 M.rho = 0 ∧
  Polynomial.eval 1 (Polynomial.derivative M.rho) = Polynomial.eval 1 M.sigma := by
  constructor
  · unfold Consistent HasOrderAtLeast
    intro x
    constructor
    · specialize x 0 zero_le_one
      rw [M.momentResidual_zero] at x
      unfold rho
      simp only [Polynomial.eval_finsetSum, Polynomial.eval_monomial, one_pow, mul_one]
      exact x
    · specialize x 1
      rw [M.momentResidual_succ 0] at x
      simp at x
      unfold rho sigma
      simp [Polynomial.derivative_monomial, Polynomial.eval_finsetSum]
      grind
  · unfold Consistent HasOrderAtLeast
    rintro ⟨h1, h2⟩
    intro q hq
    interval_cases q
    · rw [momentResidual_zero]
      unfold rho at h1
      simp only [Polynomial.eval_finsetSum, Polynomial.eval_monomial, one_pow, mul_one] at h1
      exact h1
    · rw [momentResidual_succ]
      simp
      unfold rho sigma at h2
      simp [Polynomial.derivative_monomial, Polynomial.eval_finsetSum] at h2
      grind


end Coefficients

end Dahlquist.LinearMultistep
