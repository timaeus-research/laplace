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

## Shape consult and re-staging

Consult saved verbatim: `tide-log/gpt56_h2_shape_v1.md`. Rulings
adopted: (1) public representation qform H x := ⟪x, toEuclideanCLM H
x⟫ with K H x := exp(-qform H x / 2) — matrix bilinears only as
internal bridges; (2) the forward quadratic identity qform H x =
‖Bx‖² with B := toEuclideanCLM (CFC.sqrt H) (never invert inside the
form); (3) LinearMap.det B kept OPAQUE (nonzero suffices; it cancels
in M2, only positivity feeds Z) — never transported to Matrix.det;
(4) the standard-Gaussian API in coordinate-free linear-functional
form (∫ℓ(y)k₀ = 0; ∫ℓ(y)m(y)k₀ = Z₀⟪riesz ℓ, riesz m⟫) as the
abstraction boundary; (5) lintegral-first for integrability
transport; (6) TWO tides: H2a = the standard isotropic package (all
Pi/Fubini and 1D work; the flagged hardest step is the
EuclideanSpace/PiLp/product-measure identification), H2b = whitening
(no Fubini at all). THIS tide is re-staged as H2a; H2b follows.

## Vote (updated)

- Claude: H2a/H2b split as ruled; this tide = H2a.
- GPT-5.6 Sol: same (its own plan).

Agreed.

## Result

Merged content (three checkpoints on this branch):

- `Laplace/Multi/StdGaussian.lean` (~280 lines, sorry-free):
  `stdKernel` (k₀(y) = e^{-‖y‖²/2} on EuclidD d), positivity,
  continuity, integrability; `integral_stdKernel` (Z₀ = (2π)^{d/2},
  from Mathlib's inner-product-space Gaussian integral
  `GaussianFourier.integral_rexp_neg_mul_sq_norm` at b = 1/2);
  `integral_stdKernel_pos`; `pow_le_exp_sq_bound`
  (t^{2m} ≤ 8^m·m!·e^{t²/8}, single-term series bound) giving
  `stdKernel_integrable_pow` (all polynomial weights, dominated by
  e^{-3‖y‖²/8}, NO Fubini); `stdKernel_toLp` (coordinate
  factorization); `integral_prod_mul_stdKernel` (the Fubini
  workhorse: ∫ (∏ᵢ fᵢ(yᵢ))·k₀ = ∏ᵢ ∫ fᵢ(t)e^{-t²/2}dt);
  `integral_coord_mul_stdKernel` (first moments vanish);
  `integral_coord_mul_coord_stdKernel` (∫ y_a y_b k₀ = δ_ab Z₀);
  `stdKernel_integrable_coord`, `stdKernel_integrable_coord_mul`.

Surprises:

1. The consult flagged the EuclideanSpace/PiLp/product-measure
   identification as the hardest step; it fell in ONE iteration
   because Mathlib's `integral_fintype_prod_volume_eq_prod` needs no
   integrability hypotheses at all, and
   `PiLp.volume_preserving_toLp` + `MeasurePreserving.integral_comp`
   is exactly the FourierTransform.lean idiom. The 1D factors then
   land on the seabed's own Stage-1 moments
   (`integral_pow_mul_exp_neg_sq_half/odd`).
2. Deviation from the consult: the coordinate-free linear-functional
   API (riesz forms) was NOT built. The Fubini workhorse over factor
   functions plus the delta-form second moment is a smaller interface
   that H2b can consume by expanding (Cy)_i = Σ_a C_{ia} y_a as a
   finite double sum. If H2b hits friction there, the riesz forms are
   a fallback, not a prerequisite.
3. Error classes hit and cleared: beta-unreduced rw (again; simp only
   fixed), `PiLp.continuous_apply` takes p and β EXPLICITLY (a bare
   `a : Fin d` silently coerces into the p slot), and the vestigial
   `congr 1` after rw-closes (twice).
