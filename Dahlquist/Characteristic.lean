/-
Copyright (c) 2026 Alex Masero. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Masero
-/
import Dahlquist.Basic

/-!
# Characteristic Polynomials of Linear Multistep Methods

This module defines the characteristic polynomials
rho and sigma associated with a linear multistep method.
-/

namespace Dahlquist.LinearMultistep

namespace Coefficients

variable {k : ℕ} (M : Coefficients k)

/-- The first characteristic polynomial of a linear multistep method. -/
noncomputable def rho : Polynomial ℝ :=
  ∑ j : Fin (k + 1), Polynomial.monomial (j : ℕ) (M.alpha j)

/-- The second characteristic polynomial of a linear multistep method. -/
noncomputable def sigma : Polynomial ℝ :=
  ∑ j : Fin (k + 1), Polynomial.monomial (j : ℕ) (M.beta j)


end Coefficients

end Dahlquist.LinearMultistep
