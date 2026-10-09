# Lean 4 formalization of Dahlquist theory

Lean 4 / Mathlib formalization of linear multistep methods, stability theory and Dahlquist barriers.

## Repository Structure

The main directory is `Dahlquist/`, which contains the following files:

```text
Dahlquist/
|--- Basic.lean                 # LMM coeffs and basic properties
|--- Characteristic.lean        # Characteristic polynomials
|--- OrderConditions.lean       # Order conditions and consistency
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

Next steps:

- Derive order conditions from the local truncation error operator, instead of being introduced as a definition.
- Characterize consistency through the chacateristic polynomials.


## License

Apache License 2.0. See [LICENSE](LICENSE).