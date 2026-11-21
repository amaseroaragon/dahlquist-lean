/-
Copyright (c) 2026 Alex Masero. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Masero
-/
import Dahlquist.Characteristic

/-!
# Zero Stability for Linear Multistep Methods

This module introduces the root condition on the first
characteristic polynomial, which characterizes zero-stability.
-/

namespace Dahlquist.LinearMultistep

namespace Coefficients

variable {k : ℕ} (M : Coefficients k)

/-- The first characteristic polynomial with complex coefficients. -/
noncomputable def rhoComplex : Polynomial ℂ :=
  M.rho.map (algebraMap ℝ ℂ)

/-- Root condition means all roots are mod ≤ 1 and = 1 are simple -/
def RootCondition : Prop := ∀ z : ℂ, M.rhoComplex.IsRoot z →
  ‖z‖ ≤ 1 ∧ (‖z‖ = 1 → ¬ M.rhoComplex.derivative.IsRoot z)

/-- Zero-stability characterized by the root condition. -/
def ZeroStable : Prop :=
  M.WellFormed ∧ M.RootCondition


end Coefficients

end Dahlquist.LinearMultistep
