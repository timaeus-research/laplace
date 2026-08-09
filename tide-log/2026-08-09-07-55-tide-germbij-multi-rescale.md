# Tide: germbij multivariate H3a (fixed-ray rescaling)

**Direction (user):** standing auto-mode commission on the germbij
note; this tide is stage H3a of the multivariate programme.
**Seabed:** laplace, branch tide/germbij-multi-whitening at 04e06a5
(stacked on unmerged H2b, PR #68; H2a already on main via #67).
**Started:** 2026-08-09T07:55Z (log timestamps local; earlier tide
logs this arc used UTC prefixes, kept consistent with dir listing)

## Candidates

Fixed by the H3/H4 shape consult (archived verbatim:
`tide-log/gpt56_h3_shape_v1.md`), which staged H3-H4 as THREE tides:
H3a (this) fixed-ray asymptotics + Hessian bridge; H3b multivariate
quadratic Peano + coercivity + local lower bound (flagged hardest);
H4 one generic quadratic-growth dominated-convergence theorem.

H3a deliverables (consult section 4, "Tide H3a"):

1. Ray restriction g_x(q) = L(q • x) via
   `ContinuousLinearMap.toSpanSingleton` (so regularity composes).
2. First and second ray derivatives from C² of L by chain rule:
   g_x''(0) = D²L(0)[x, x].
3. The Hessian bridge: with `hessianMatrix B i j := B ![e i, e j]`
   from the continuous bilinear second derivative, prove
   B[x, x] = qform (hessianMatrix B) x by coordinate expansion
   (consult: store the diagonal identity, least brittle interface).
4. `rescaled_tendsto`: for L C² near 0 with fderiv L 0 = 0,
   Tendsto (fun q ↦ (L (q • x) - L 0) / q²) (𝓝[>] 0)
     (𝓝 (qform H x / 2))
   via Mathlib `taylor_isLittleO` on the ray (SmoothRecovery's
   pattern), with 𝓝[>] 0 making q ≠ 0 eventually automatic.

Consult rulings adopted: rays for the pointwise limit (no
FormalMultilinearSeries); the bilinear form is the primary Hessian
with the matrix derived; coercivity and the uniform bound are NOT
this tide (H3b); H4 may take the lower bound as hypothesis if H3b
drags.

## Numerical check

Executed before this log was written (d=2,
H=[[2,0.6],[0.6,1.1]], L = quadratic + 0.4·w₀³ + 0.2·w₀w₁²,
x=(0.8,-1.3)). Output quoted verbatim:

    qform/2 = 0.9455000000000002
    q=0.1: (L(qx)-L(0))/q^2 = 0.99302000  diff = 4.75e-02
    q=0.01: (L(qx)-L(0))/q^2 = 0.95025200  diff = 4.75e-03
    q=0.001: (L(qx)-L(0))/q^2 = 0.94597520  diff = 4.75e-04
    lambda_min = 0.8000000000000002  lambda_min*|x|^2 = 1.8640000000000003  <= qform = 1.8910000000000005

The quotient converges to qform/2 with the expected linear-in-q
error from the cubic term; the coercivity inequality (H3b's target)
also verified.

## Vote

- Claude: H3a as staged above (the consult's own staging).
- GPT-5.6 Sol: same (its section 4 ruling, archived).

Agreed.

## Result

One checkpoint, one file (`Laplace/Multi/RayRescale.lean`, ~190
lines, sorry-free, single diagnostic pass with three trivial fixes):

- `hess L` (second Fréchet derivative at 0, curried CLM form) and
  `hessianMatrix L` (one-hot basis evaluation), per the consult.
- `eq_sum_single`, `clm_bilinear_expand` (one-hot expansion of a
  continuous bilinear map, calc over map_sum/map_smul), and the
  bridge `hess_apply_self : hess L x x = qform (hessianMatrix L) x`.
- Ray chain rule: `ray_hasDerivAt` (HasFDerivAt.comp_hasDerivAt),
  `ray_hasDerivAt_two` (C¹ of fderiv via ContDiff.fderiv_right, then
  HasDerivAt.clm_apply against a constant), `ray_iteratedDeriv_two`.
- `ray_taylor_eval`: the order-2 Taylor polynomial collapses to
  L 0 + q²·(hess/2) under vanishing gradient.
- `rescaled_loss_tendsto`: the headline, from taylor_isLittleO via
  IsLittleO.tendsto_div_nhds_zero + tendsto_sub_nhds_zero_iff.

Surprises: none mathematical. The consult's prediction that the ray
route is "relatively contained" was exact: the derivative plumbing it
warned about is three short haves because `HasDerivAt.clm_apply`
against `hasDerivAt_const` eats the evaluation step. New catalogue
entry: `ContDiff.differentiable` now wants `1 ≠ 0`-shaped side goals
discharged by norm_num rather than le_rfl when the regularity grade
is a literal.
