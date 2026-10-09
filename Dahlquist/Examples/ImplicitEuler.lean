/-
Copyright (c) 2026 Alex Masero. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Masero
-/
import Dahlquist.Basic
import Dahlquist.OrderConditions

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
  · simp [Coefficients.momentResidual, implicitEuler]
  · simp [Coefficients.momentResidual, implicitEuler]

/-- Implicit Euler has order one. -/
theorem implicitEuler_order_one : implicitEuler.HasExactOrder 1 := by
  constructor
  · apply implicitEuler_order_at_least_one
  · simp [Coefficients.momentResidual, implicitEuler]
    grind

/-- Implicit Euler is consistent. -/
theorem implicitEuler_consistent : implicitEuler.Consistent := by
  apply implicitEuler_order_at_least_one

end Dahlquist.LinearMultistep
