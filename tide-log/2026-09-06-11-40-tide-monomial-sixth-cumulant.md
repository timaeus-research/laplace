# Tide: monomial-sixth-cumulant

**Direction (user):** Continue with what you think best (auto). Fourth laplace tide; the next rung
of the monomial cumulant ladder after variance (κ₂) and kurtosis (κ₄).
**Seabed:** laplace, commit 53b955a (branch base)
**Started:** 2026-09-06

## Candidate

The sixth cumulant `κ₆ = ⟨x⁶⟩ − 15⟨x⁴⟩⟨x²⟩ + 30⟨x²⟩³` (symmetric weight, mean 0) of `x` against
`exp(-t·x^(2k)/(2k)!)` in Gamma closed form + its `t^(-3/k)` asymptotic scaling.

## Numerical check

Gaussian reference `k=1` (N(0,1): μ₂=1, μ₄=3, μ₆=15): κ₆ = 15 − 15·3·1 + 30·1³ = 0, the correct
vanishing sixth cumulant of a Gaussian. ✓  (Cumulant–moment relation for μ₃=0:
κ₆ = μ₆ − 15μ₄μ₂ + 30μ₂³.)

## Result

`Laplace/OneD/MonomialSixthCumulant.lean` (NEW): `monomial_sixth_cumulant` (closed form
`((2k)!/t)^(3/k)·(r₃−15r₂r₁+30r₁³)`, rⱼ=Γ((2j+1)/(2k))/Γ(1/(2k))), `sixthCumulantConst`, and the
three asymptotic rungs `_eq_const_mul_rpow`/`_rescaled_tendsto`/`_isEquivalent_rpow` (κ₆ = K₆(k)·t^(-3/k)
exactly). Zero-sorry, full build clean (8885 jobs). Compiled on the first attempt.

Proof mirrors `MonomialKurtosis` with THREE moments (j=3,2,1) and two power-folds into the common base
`B := ((2k)!/t)^(1/k)`: `hpow2 : B^... ` as in kurtosis, and `hpow3 : ((2k)!/t)^(3/k) = B^3` via
`← Real.rpow_natCast _ 3` then `← Real.rpow_mul hfac_t_pos.le` + `push_cast; ring` (the clean way to
turn `B^3` (npow) into `base^(3·exp)`). Then `push_cast; rw [hpow2, hpow3]; ring` (Gamma ratios as atoms).
`Authors:` header line included from the outset (per the header-linter gotcha). No GPT.

★ The monomial cumulant ladder (κ₂, κ₄, κ₆ + asymptotics + 1D moment base) is now COMPLETE at the clean
frontier; the general even cumulant would need Bell-polynomial / set-partition machinery (hard).
