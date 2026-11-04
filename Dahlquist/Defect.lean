/-
Copyright (c) 2026 Alex Masero. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Masero
-/
import Dahlquist.Basic

/-!
# Local Truncation Defect of Linear Multistep Methods

This module defines the local truncation defect operator
associated with a linear multistep method.

It also introduces Taylor polynomials and develops auxiliary
results to derive the order conditions by expanding the defect operator.
-/

namespace Dahlquist.LinearMultistep
namespace Coefficients

variable {k : ℕ} (M : Coefficients k)

/-- The local truncation defect of a LMM. -/
noncomputable def defect (y : ℝ → ℝ) (x h : ℝ) : ℝ :=
  (∑ j : Fin (k + 1), M.alpha j * y (x + (j : ℝ) * h)) -
  h * (∑ j : Fin (k + 1), M.beta j * deriv y (x + (j : ℝ) * h))

/-- Taylor polynomial of degree p with given coefficients a, centered at 0. -/
noncomputable def taylorPolynomial (a : ℕ → ℝ) (p : ℕ) : Polynomial ℝ :=
  ∑ q : Fin (p + 1), Polynomial.monomial q (a q / (Nat.factorial q : ℝ))



/-- The Taylor polynomial of degree p + 1 is obtained by adding
the corresponding monomial to the one of degree p.
-/
private theorem taylorPolynomial_succ (a : ℕ → ℝ) (p : ℕ) :
    taylorPolynomial a (p + 1) = taylorPolynomial a p +
    Polynomial.monomial (p + 1) (a (p + 1) / (Nat.factorial (p + 1) : ℝ)) := by
  unfold taylorPolynomial
  rw [Fin.sum_univ_castSucc]
  grind

/-- The defect operator is additive when using polynomials. -/
private theorem defect_add_polynomials (P Q : Polynomial ℝ) (h : ℝ) :
    M.defect (fun x => (P + Q).eval x) 0 h =
    M.defect (fun x => P.eval x) 0 h + M.defect (fun x => Q.eval x) 0 h := by
  unfold defect
  simp only [Polynomial.deriv]
  simp only [Polynomial.derivative_add, Polynomial.eval_add, mul_add, Finset.sum_add_distrib]
  grind

/-- Expansion of the defect operator applied to a monomial. -/
private theorem defect_monomial_succ (q : ℕ) (c h : ℝ) :
    M.defect (fun x => (Polynomial.monomial (q + 1) c).eval x) 0 h =
    c * h ^ (q + 1) * ((∑ j : Fin (k + 1), M.alpha j * (j : ℝ) ^ (q + 1)) - (q + 1 : ℝ) *
    (∑ j : Fin (k + 1), M.beta j * (j : ℝ) ^ q)) := by
  unfold defect
  simp only [Polynomial.deriv, Polynomial.derivative_monomial_succ]
  simp only [Polynomial.eval_monomial, zero_add, mul_pow]
  simp only [mul_sub, Finset.mul_sum]
  grind

/-- Expansion of the defect operator applied to a Taylor polynomial. -/
theorem defect_taylorPolinomial (a : ℕ → ℝ) (p : ℕ) (h : ℝ) :
    M.defect (fun x => (taylorPolynomial a p).eval x) 0 h =
    a 0 * (∑ j : Fin (k + 1), M.alpha j)+
    ∑ q ∈ Finset.range p, (a (q + 1) * h ^ (q + 1) / (Nat.factorial (q + 1) : ℝ)) *
    ((∑ j : Fin (k + 1), M.alpha j * (j : ℝ) ^ (q + 1)) -
    (q + 1 : ℝ) * (∑ j : Fin (k + 1), M.beta j * (j : ℝ) ^ q)) := by
  induction p with
  | zero =>
    simp [taylorPolynomial, defect, ← Finset.sum_mul]
    ring
  | succ p ih =>
    rw [Finset.sum_range_succ]
    rw [taylorPolynomial_succ]
    rw [defect_add_polynomials]
    rw[ih]
    rw[defect_monomial_succ]
    grind


end Coefficients
end Dahlquist.LinearMultistep
