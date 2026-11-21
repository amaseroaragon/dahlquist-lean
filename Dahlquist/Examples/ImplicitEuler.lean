/-
Copyright (c) 2026 Alex Masero. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Masero
-/
import Dahlquist.Basic
import Dahlquist.OrderConditions
import Dahlquist.ZeroStability

/-!
# Implicit Euler method

Basic properties of the Implicit Euler Method.
-/

namespace Dahlquist.LinearMultistep

/-- The implicit Euler method. -/
def implicitEuler : Coefficients 1 where
  alpha := ![-1, 1]
  beta := ![0, 1]

/-- Implicit Euler is a well-formed linear multistep method. -/
theorem implicitEuler_wellFormed : implicitEuler.WellFormed := by
  constructor
  · simp
  · change (1 : ℝ) ≠ 0
    simp

/-- Implicit Euler is normalized. -/
theorem implicitEuler_normalized : implicitEuler.Normalized := by
  change (1 : ℝ) = 1
  simp

/-- Implicit Euler is not an explicit method. -/
theorem implicitEuler_notExplicit : ¬ implicitEuler.Explicit := by
  change (1 : ℝ) ≠ 0
  simp

/-- Implicit Euler has at least order one. -/
theorem implicitEuler_order_at_least_one : implicitEuler.HasOrderAtLeast 1 := by
  intro n p
  interval_cases n
  · simp [Coefficients.momentResidual_zero, implicitEuler]
  · simp [Coefficients.momentResidual_succ, implicitEuler]

/-- Implicit Euler has order one. -/
theorem implicitEuler_order_one : implicitEuler.HasExactOrder 1 := by
  constructor
  · apply implicitEuler_order_at_least_one
  · simp [Coefficients.momentResidual_succ, implicitEuler]

/-- Implicit Euler is consistent. -/
theorem implicitEuler_consistent : implicitEuler.Consistent := by
  apply implicitEuler_order_at_least_one

/-- Implicit Euler is zero stable. -/
theorem implicitEuler_zeroStable : implicitEuler.ZeroStable := by
  -- Same demo as the explicit euler
  constructor
  · exact implicitEuler_wellFormed
  · unfold Coefficients.RootCondition
    intro z h
    constructor
    · simp only [Coefficients.rhoComplex, Coefficients.rho, Nat.reduceAdd, implicitEuler,
      Fin.sum_univ_two, Fin.isValue, Fin.coe_ofNat_eq_mod, Nat.zero_mod, Matrix.cons_val_zero,
      Polynomial.monomial_neg, Polynomial.monomial_zero_left, map_one, Nat.mod_succ,
      Matrix.cons_val_one, Matrix.cons_val_fin_one, Polynomial.map_add, Polynomial.map_neg,
      Polynomial.map_one, Polynomial.map_monomial, Polynomial.IsRoot.def, Polynomial.eval_add,
      Polynomial.eval_neg, Polynomial.eval_one, Polynomial.eval_monomial, pow_one, one_mul] at h
      rw [add_comm, ← sub_eq_add_neg, sub_eq_zero] at h
      subst z
      simp
    · intro h2 h3
      simp [Coefficients.rhoComplex, Coefficients.rho, implicitEuler] at h
      simp [Coefficients.rhoComplex, Coefficients.rho, implicitEuler] at h3

end Dahlquist.LinearMultistep
