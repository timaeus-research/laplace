# Tide: germbij-multi-gaussian (multivariate programme, stage H2)

**Direction (user):** the quadratic Gaussian package (auto mode,
standing delegation) — the consult's flagged API spike: for positive
definite H, prove 0 < Z_H < ∞, ∫x_i·K_H = 0, and
(1/Z_H)∫x_i x_j·K_H = (H⁻¹)_{ij}, with the polynomial-weight
integrability the later stages consume.

**Seabed:** laplace, main at cc3c747 (dilation wrapper merged).
**Worktree/branch:** laplace-tide-germbij-multi-gaussian /
tide/germbij-multi-gaussian
**Started:** 2026-08-10T07:05Z

## Mathlib survey (the consult's prescribed first step)

Mathlib's Probability/Distributions/Gaussian/Multivariate.lean has
`multivariateGaussian μ S` (built from stdGaussian via CFC.sqrt S)
with a COMPLETE abstract mean/covariance API:
integral_id_multivariateGaussian (mean = μ) and
covariance_eval_multivariateGaussian (cov[x_i,x_j] = S i j). But the
file contains NO density-vs-volume bridge (no withDensity, rnDeriv,
or volume lemmas) — our programme's objects are Lebesgue integrals of
e^{-⟨x,Hx⟩/2}, so identifying the two measures is itself the awkward
step the consult anticipated. RULING (per the consult's fallback):
prove the moment formulas directly by WHITENING, staying in the
Lebesgue world: with B := hH.sqrt (Matrix.PosDef.sqrt, B·B = H,
B self-adjoint pos def), ⟨x,Hx⟩ = ‖Bx‖²; substitute x = B⁻¹y via the
linear change of variables (|det B|⁻¹ Jacobian); the standard product
Gaussian then gives ∫y_k y_l e^{-‖y‖²/2} = δ_{kl}(2π)^{d/2} by the
measure-preserving equiv to (Fin d → ℝ) + Fubini
(integral_fintype_prod-style) + the 1D moments already in the seabed;
finally Σ_{kl}(B⁻¹)_{ik}(B⁻¹)_{jl}δ_{kl} = (B⁻¹B⁻¹)_{ij} = (H⁻¹)_{ij}
and the |det B|⁻¹(2π)^{d/2} factors cancel in the normalized ratio.
Key Mathlib pieces to pin at build time: Matrix.PosDef.sqrt +
sqrt_mul_self; the linear change of variables on volume
(Measure.addHaar-family or integral_comp_linearEquiv);
EuclideanSpace.volume_preserving_measurableEquiv; the pi-integral
product lemma.

## Vote

- Claude: H2 by whitening (the consult's fallback, now confirmed
  necessary by the survey).
- GPT-5.6 Sol (scoping consult): "If the density bridge is awkward,
  use: the standard H = I Gaussian; a positive square root; linear
  change of variables. Whitening is preferable to diagonalization."

Agreed.

## Numerical check

To be executed before formalisation in a separate command (d = 2,
non-diagonal H: Z, first moments, second-moment matrix vs H⁻¹).
Executed (quoted from output), d = 2 with the non-diagonal
H = [[2, 0.6], [0.6, 1.1]]: Z = 4.63202566 = (2π)/√(det H) to 8
decimals; first moment 0.00e+00; E[x²] = 0.59782609 = H⁻¹₀₀ and
E[xy] = −0.32608696 = H⁻¹₀₁, both to 8 decimals. All four target
formulas confirmed.
