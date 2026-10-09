/-
Copyright (c) 2026 Alex Masero. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Masero
-/
import Dahlquist.Basic
import Dahlquist.OrderConditions

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
  intro n p
  interval_cases n <;> simp [Coefficients.momentResidual, explicitEuler]

/-- Explicit Euler has order one. -/
theorem explicitEuler_order_one : explicitEuler.HasExactOrder 1 := by
  constructor
  · apply explicitEuler_order_at_least_one
  · simp [Coefficients.momentResidual, explicitEuler]

/-- Explicit Euler is consistent. -/
theorem explicitEuler_consistent : explicitEuler.Consistent := by
  apply explicitEuler_order_at_least_one


end Dahlquist.LinearMultistep
