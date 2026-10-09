/-
Copyright (c) 2026 Alex Masero. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Masero
-/
import Mathlib

/-!
# Linear Multistep Methods — Basic Definitions

This module introduces the coefficient representation of linear
multistep methods and their fundamental properties.

A k-step method is represented by two families of real coefficients
indexed by j = 0, ..., k.
-/

namespace Dahlquist.LinearMultistep

/-- Coefficients of a k-step linear multistep method. -/
structure Coefficients (k : ℕ) where
  alpha : Fin (k + 1) → ℝ
  beta: Fin (k + 1) → ℝ

namespace Coefficients

variable {k : ℕ} (M : Coefficients k)

/-- A method is well-formed if it has at least one step
and its leading alpha coefficient is nonzero. -/
def WellFormed : Prop :=
  0 < k ∧ M.alpha (Fin.last k) ≠ 0

/-- A method is normalized if its leading alpha coefficient is one. -/
def Normalized : Prop :=
  M.alpha (Fin.last k) = 1

/-- A method is explicit if its last beta coefficient is zero. -/
def Explicit : Prop :=
  M.beta (Fin.last k) = 0


end Coefficients

end Dahlquist.LinearMultistep
