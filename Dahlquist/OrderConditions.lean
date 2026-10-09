/-
Copyright (c) 2026 Alex Masero. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Masero
-/
import Dahlquist.Characteristic

/-!
# Order Conditions for Linear Multistep Methods

This module introduces the order conditions for
linear multistep methods.

The moment residuals C_q are the coefficients appearing in
the formal Taylor expansion of the local truncation defect.

A method has order at least p when C_0 = ... = C_p and C_{p+1} != 0.
Consistency corresponds to order at least one.
-/

namespace Dahlquist.LinearMultistep

namespace Coefficients

variable {k : ℕ} (M : Coefficients k)

/-- sustituir por teorema. -/
noncomputable def momentResidual : ℕ → ℝ
  | 0 => ∑ j : Fin (k + 1), M.alpha j
  | q + 1 => ((∑ j : Fin (k + 1), M.alpha j * (j : ℝ) ^ (q + 1)) -
    ((q + 1 : ℕ) : ℝ) * (∑ j : Fin (k + 1), M.beta j * (j : ℝ) ^ (q)))
    / (Nat.factorial (q + 1) : ℝ)


def HasOrderAtLeast (p : ℕ) : Prop :=
  ∀ q : ℕ, q ≤ p → M.momentResidual q = 0

def HasExactOrder (p : ℕ) : Prop :=
  M.HasOrderAtLeast p ∧ M.momentResidual p + 1 ≠ 0

def Consistent : Prop :=
  M.HasOrderAtLeast 1


end Coefficients

end Dahlquist.LinearMultistep
