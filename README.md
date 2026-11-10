# Lean 4 formalization of Dahlquist theory

Lean 4 / Mathlib formalization of linear multistep methods, stability theory and Dahlquist barriers.

## Repository Structure

The main directory is `Dahlquist/`, which contains the following files:

```text
Dahlquist/
|--- Basic.lean                 # LMM coeffs and basic properties
|--- Characteristic.lean        # Characteristic polynomials
|--- OrderConditions.lean       # Order conditions and consistency
|--- Defect.lean                # Defect operator and Taylor expansion
|--- Examples/
     |--- ExplicitEuler.lean    # Explicit Euler method and proofs
     |--- ImplicitEuler.lean    # Implicit Euler method and proofs

```


## Current Progress

Already done:

- Coefficient-based representation of LMMs.
- Basic structural properties of LMMs.
- Definitions of the characteristic polynomials.
- Order conditions and consistency.
- Explicit and implicit Euler methods.
- Definition of the local truncation defect operator and Taylor polynomials.
- Taylor expansion of the defect operator. 
- Derivation of moment residuals.
- Characterization of consistency through the characteristic polynomials.

Next steps:

- Define the root condition for zero-stability.
- Prove zero-stability of explicit and implicit Euler methods.

Future ideas:
- Introduce reusable lemmas for characteristic polynomials:
     - Evaluation of rho and sigma at one (rho_eval_one and sigma_eval_one).
     - Evaluation of the derivative of rho at one (rho_derivative_eval_one).
- Refactor existing proofs to reuse these lemmas.


## License

Apache License 2.0. See [LICENSE](LICENSE).