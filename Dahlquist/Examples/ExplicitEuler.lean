/-
Copyright (c) 2026 Alex Masero. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Masero
-/
import Dahlquist.Basic
import Dahlquist.OrderConditions
import Dahlquist.ZeroStability

/-!
# Explicit Euler method

Basic properties of the Explicit Euler Method.
-/

namespace Dahlquist.LinearMultistep

/-- The explicit Euler method. -/
def explicitEuler : Coefficients 1 where
  alpha := ![-1, 1]
  beta := ![1, 0]

/-- Explicit Euler is a well-formed linear multistep method. -/
theorem explicitEuler_wellFormed : explicitEuler.WellFormed := by
  constructor
  · simp
  · change (1 : ℝ) ≠ 0
    simp

/-- Explicit Euler is normalized. -/
theorem explicitEuler_normalized : explicitEuler.Normalized := by
  change (1 : ℝ) = 1
  simp

/-- Explicit Euler is an explicit method. -/
theorem explicitEuler_explicit : explicitEuler.Explicit := by
  change (0 : ℝ) = 0
  simp

/-- Explicit Euler has order at least one -/
theorem explicitEuler_order_at_least_one : explicitEuler.HasOrderAtLeast 1 := by
  intro q hq
  interval_cases q
  · simp [Coefficients.momentResidual_zero, explicitEuler]
  · simp [Coefficients.momentResidual_succ, explicitEuler]

/-- Explicit Euler has order one. -/
theorem explicitEuler_order_one : explicitEuler.HasExactOrder 1 := by
  constructor
  · exact explicitEuler_order_at_least_one
  · simp [Coefficients.momentResidual_succ, explicitEuler]

/-- Explicit Euler is consistent. -/
theorem explicitEuler_consistent : explicitEuler.Consistent := by
  apply explicitEuler_order_at_least_one

/-- Explicit Euler is zero stable. -/
theorem explicitEuler_zeroStable : explicitEuler.ZeroStable := by
  constructor
  · exact explicitEuler_wellFormed
  · unfold Coefficients.RootCondition
    intro z h
    constructor
    · --simp? [Coefficients.rhoComplex, Coefficients.rho, explicitEuler] at h
      simp only [Coefficients.rhoComplex, Coefficients.rho, Nat.reduceAdd, explicitEuler,
      Fin.sum_univ_two, Fin.isValue, Fin.coe_ofNat_eq_mod, Nat.zero_mod, Matrix.cons_val_zero,
      Polynomial.monomial_neg, Polynomial.monomial_zero_left, map_one, Nat.mod_succ,
      Matrix.cons_val_one, Matrix.cons_val_fin_one, Polynomial.map_add, Polynomial.map_neg,
      Polynomial.map_one, Polynomial.map_monomial, Polynomial.IsRoot.def, Polynomial.eval_add,
      Polynomial.eval_neg, Polynomial.eval_one, Polynomial.eval_monomial, pow_one, one_mul] at h
      rw [add_comm, ← sub_eq_add_neg, sub_eq_zero] at h
      subst z
      simp
    · intro h2 h3
      simp [Coefficients.rhoComplex, Coefficients.rho, explicitEuler] at h
      simp [Coefficients.rhoComplex, Coefficients.rho, explicitEuler] at h3


end Dahlquist.LinearMultistep
