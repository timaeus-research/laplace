# Consult: local uniform (L^∞) agreement of Laplace weights from local total variation (germbij / laplace Lean)

## Context
Lean 4 + Mathlib. Smooth nonnegative losses `L₁ L₂ : ℝ^d → ℝ`; `h_t = e^{-tL₂} − e^{-tL₁}`; `SuperPoly f := ∀ N, f = o(t^{-N})`.
Merged today: exact smooth-test agreement ⇒ `∫_K |h_t| = o(t^{-∞})` for every compact `K` (`superPoly_setIntegral_abs_exp_sub`), and agreement on bounded compactly supported tests. Your previous consult stated that local `L^∞` agreement is also true under smoothness, via `‖∇h_t‖ ≤ Ct` and a Lipschitz-peak argument, and deferred it as needing interpolation infrastructure. This tide attempts it directly.

## Plan
(G) For `t ≥ 0`, `L ≥ 0` differentiable at `x`: `fderiv (e^{-tL}) x = e^{-tL(x)} • (−t • fderiv L x)`, so `‖fderiv (e^{-tL}) x‖ ≤ t ‖fderiv L x‖`.
(Lip) `K' := cthickening 1 K` is compact; `G := max over K' of ‖∇L₁‖ + ‖∇L₂‖` (exists by continuity + compactness). For `x₀ ∈ K` and `y ∈ ball x₀ 1 ⊆ K'`: `|h_t y − h_t x₀| ≤ Λ ‖y − x₀‖`, `Λ := tG + 1`, by the mean value inequality on the convex ball (`Convex.norm_image_sub_le_of_norm_fderiv_le`, with `DifferentiableAt` hypotheses).
(Peak) `H := |h_t x₀| ≤ 1` (both weights in `[0,1]` for `t ≥ 0`). `r := H/(2Λ) ≤ 1/2`. On `ball x₀ r`, `|h_t| ≥ H − Λ r = H/2`. So `∫_{K'} |h_t| ≥ ∫_{ball x₀ r} |h_t| ≥ (H/2) vol(ball x₀ r) = (H/2) c_d r^d` with `c_d = vol(ball 0 1)` (`Measure.addHaar_ball_of_pos`). Hence `H^{d+1} ≤ (2^{d+1}/c_d) Λ^d ∫_{K'} |h_t|`.
(Assemble) For `t ≥ 1`, `Λ ≤ (G+1) t`. Given `N`, eventually `∫_{K'}|h_t| ≤ t^{-(d+1)N − d}` (SuperPoly), so `H^{d+1} ≤ C' t^{-(d+1)N}` with `C' = (2^{d+1}/c_d)(G+1)^d`, and `H ≤ C'^{1/(d+1)} t^{-N}` (`Real.rpow_inv_natCast_pow`). The constant is uniform over `x₀ ∈ K`.
Statement: `∀ N, ∃ C, ∀ᶠ t in atTop, ∀ x ∈ K, |h_t x| ≤ C * t^{-N}`. Corollary: pointwise `SuperPoly (fun t ↦ h_t x)` for every `x`.

## Questions
1. Is the argument correct as stated? In particular (i) is `K' = cthickening 1 K` with `ball x₀ (H/(2Λ)) ⊆ K'` for `x₀ ∈ K` right (needs `r ≤ 1`, ensured by `H ≤ 1 ≤ 2Λ`); (ii) is the exponent `d+1` and the constant bookkeeping right; (iii) any subtlety with `H = 0` or `G = 0` (I add `+1` to `Λ` to avoid division by zero)?
2. Is there a cleaner formulation of the conclusion than `∀ N, ∃ C, ∀ᶠ t, ∀ x ∈ K, |h_t x| ≤ C t^{-N}`? E.g. `SuperPoly (fun t ↦ ⨆ x ∈ K, |h_t x|)` (sSup on ℝ is awkward in Lean) or via `‖h_t‖_{C(K)}`. I plan the uniform-bound form and a pointwise corollary.
3. Is the smoothness needed beyond `C¹` with locally bounded gradient (plus the exact smooth-test agreement, which itself used `C^∞` losses to test `η²D`)? I plan to keep `ContDiff ℝ ∞` for both since the upstream hypothesis already requires it.
4. Nearby stronger targets: (a) uniform agreement of normalized densities `e^{-tL₂}/Z₂ − e^{-tL₁}/Z₁` on `K` given the anchor lower bounds (`1/Z_i = O(t^n)`) — a one-liner from U∞ + `Z₂/Z₁ − 1` SuperPoly? (b) derivatives: `∇h_t` uniformly small? (`∇h_t = −t(e^{-tL₂}∇L₂ − e^{-tL₁}∇L₁)`, which is `−t e^{-tL₂}∇D − t h_t ∇L₁` … the first term is NOT small in general since `∇D ≠ 0` off the agreement set — so no.) (c) a rate-explicit version: `sup_K |h_t| ≤ C_K (t^d ∫_{K'} |h_t|)^{1/(d+1)}` as a standalone inequality (the assembly is then a corollary) — I plan to state this inequality explicitly, is that the right modular cut?
5. Vote: G + Lip + Peak-inequality + U∞ + pointwise corollary as one tide (~350 lines)?
Numbered answers, statement-level Lean shapes; one-line vote at the end.
