# Tide: germbij-multi-dilation (multivariate programme, stages H0-H1)

**Direction (user):** the multivariate Theorem 3.1 programme opener
(auto mode, standing delegation): fix the ambient representation
(EuclideanSpace ℝ (Fin d)) and build the project-local
scalar-dilation wrapper ∫f = q^d·∫f(q•x) for q > 0 — stage H1 of the
H-recovery-first milestone.

**Seabed:** laplace, main at 803a7b3 (1D Theorem 3.1 complete at all
orders).
**Worktree/branch:** laplace-tide-germbij-multi-dilation /
tide/germbij-multi-dilation
**Started:** 2026-08-10T06:50Z

## Programme scoping

Consult saved verbatim: `tide-log/gpt56_multivariate_scoping_v1.md`
(with the note attached as context). Rulings adopted: H-recovery
first (NOT the full jet package — Hessian recovery already forces all
new foundations: dilation, expanding-domain DCT, multivariate
Gaussian moments, covariance bookkeeping); EuclideanSpace ℝ (Fin d)
throughout (coordinates + Hilbert APIs); ONE project-local dilation
wrapper insulating downstream proofs from Mathlib's
change-of-variables surface (trap: the pushforward carries q^{-d}
while substitution carries q^d — fix one orientation and test on an
indicator); whitening (H^{1/2}) rather than diagonalization for the
Gaussian package (H2, the flagged API spike); expanding domains as
indicators on the fixed space (H4 trap); and — the key structural
simplification — injectivity for the eventual degree-k tensors via
covariance-Gram positive-definiteness from the Gaussian's full
support (Var_γ(Q) = 0 → Q = 0 by the same open-support argument as
1D), avoiding Wick/Isserlis entirely. Stages H0-H6 listed with H6 =
pairwise Hessian recovery, the multivariate base_recovery analogue.

## Vote

- Claude: H0+H1 as the opening tide (representation + dilation
  wrapper + indicator smoke test).
- GPT-5.6 Sol: same staging (its own plan).

Agreed.

## Numerical check

Executed below in a separate command (values to be quoted from
output): the dilation identity on d = 2 with a Gaussian-with-cubic
integrand, and the orientation check on a box indicator (the
consult's named trap).
Executed (quoted from output): d = 2 with f = e^{-|x|²}(1 + 0.3x₁³),
q = 0.7: direct integral 3.14159265, q²·(scaled integral) 3.14159265
(equal to 8 decimals — the π of the pure Gaussian, the cubic term
vanishing by symmetry). Box-indicator orientation check: measured
volume 0.254800 = q²ab = 0.254800 exactly. The q^d orientation (NOT
q^{-d}) confirmed for the substitution form ∫f = q^d ∫f(q•x).

## Result

- Declarations (Laplace/Multi/Dilation.lean, ~50 lines, zero sorries,
  zero warnings; gate verified via import + .olean): EuclidD (the
  ambient abbreviation), integral_dilation (∫f = q^d·∫f(q•x), q > 0,
  wrapping Mathlib's Measure.integral_comp_smul with the orientation
  inverted once and for all), and setIntegral_dilation (the indicator
  form for the expanding domains of stage H4).
- Surprises: the Measure.-namespace gotcha struck again exactly as
  the catalogue predicts for its 1D sibling integral_comp_mul_right —
  the lemma is MeasureTheory.Measure.integral_comp_smul.
