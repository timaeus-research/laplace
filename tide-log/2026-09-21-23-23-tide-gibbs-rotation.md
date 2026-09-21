# Tide: gibbs-rotation

**Direction (user):** auto mode on the Sanity-on-Sampling note; the rotation law for Gibbs moments under the affine isometry
`w ↦ Qᵀ(w − c)` (partition function, expectations and covariances invariant), and E2 in the note's rotated frame: the per-direction variances
along the eigenvectors `Q eᵢ`, the mean shift and the LLC of the rotated anharmonic potential.
**Seabed:** laplace, branch `tide/separable-exact` at commit cd603e5 (chained: needs `SeparableExact.lean`)
**Started:** 2026-09-21T23:25Z

## Candidates v1 (Claude)

See `gpt_gibbs_rotation_prompt_v1.md` (A–C verbatim).

- A: `Z_{L∘A} = Z_L`, `⟨φ∘A⟩_{L∘A} = ⟨φ⟩_L`, `Cov_{L∘A}[φ∘A, ψ∘A] = Cov_L[φ, ψ]` for `A w = Qᵀ(w − c)`, `Qᵀ Q = 1`; coordinate and energy corollaries.
- B: E2 in the note's frame: per-direction variance along `Q eᵢ` is the 1D anharmonic variance, remainder `→ a² − 1/2`, directional mean,
  `t⟨L⟩ → d/2`.
- C: the one-loop covariance rotates (tensor bookkeeping).

## GPT-6 Astra v1

Saved verbatim in `gpt_gibbs_rotation_v1.md`. Summary: A correct; `QᵀQ = 1` suffices (square, so `QQᵀ = 1` and `|det Q| = 1`); an orthogonal
matrix is not an isometry for the sup norm on `ι → ℝ`, so use the determinant/Haar route (`integral_comp_mulVec` with `M = Qᵀ` plus translation
invariance) rather than a normed-space `IsometryEquiv`; weak hypotheses (AE strong measurability of the weighted integrands) in the core with
continuity wrappers; no `Z > 0` or integrability is needed for the equalities of totalised expressions. B is a rewrite along the directional
covariance identity; no sign issue for the variance (`αᵢ² = a²λᵢ³`); the *ambient* mean `t⟨wⱼ − cⱼ⟩ → −∑ᵢ Qⱼᵢ αᵢ/(2λᵢ²)` needs linearity
and integrability (directional mean and energy are direct rewrites); leave the Hessian identification as a remark. C is a different layer;
defer. Vote: A+B.

## Vote
- Claude: A+B (directional statements; the ambient mean as an extra if cheap)
- GPT-6 Astra: A+B

## Numerical check

`numcheck_gibbs_rotation.py` (`d = 2`, rotated anharmonic, `θ = 0.7`, `w* = (0.3, −0.2)`, `t = 15`, quadrature): `Z` invariant (5e-14),
mean `= w* + Q⟨u⟩` (4e-14), `Cov_w = Q Cov_u Qᵀ` (2e-13), projected variances `= Var_{uᵢ}` (2e-13), `t⟨L⟩` identical in both frames.
