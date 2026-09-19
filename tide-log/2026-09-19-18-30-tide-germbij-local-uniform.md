# Tide: germbij local uniform agreement

**Direction (user):** "Continue" (2026-09-19) — the tide loop continues on the germbij closure programme; this tide takes the local `L^∞` upgrade that the total-variation consult showed to be true and deferred.
**Seabed:** laplace, commit ca13956 (main; TotalVariation merged)
**Started:** 2026-09-19T18:30Z
**Ledger direction:** germbij: local uniform (L^inf) agreement — sup over a compact K of |e^{-tL2} - e^{-tL1}| is o(t^-inf) from the local total-variation bound and the gradient bound |grad(e^{-tL})| <= Ct, via a Lipschitz-peak volume argument.

## Seabed snapshot
- `superPoly_setIntegral_abs_exp_sub` (TotalVariation): `∫_K |e^{-tL₂} − e^{-tL₁}| = o(t^{-∞})` for compact `K`, smooth
  nonnegative losses with exact smooth-test agreement.
- `superPoly_of_forall_eventually_le`, `SuperPoly.of_abs_le`, `SuperPoly.polyBounded_mul` (TotalVariation).
- Missing: any pointwise or uniform statement about the weights themselves.

## Candidates v1 (Claude)

Notation: `h_t = e^{-tL₂} − e^{-tL₁}`, `d = Fintype.card ι`.

### U∞. Local uniform agreement beyond all orders
```
theorem eventually_uniform_abs_exp_sub_le {L₁ L₂} (h1 h2 : ContDiff ℝ ∞) (hL1 hL2 : nonneg) (hexact : smooth-test exact agreement)
    {K : Set (ι → ℝ)} (hK : IsCompact K) :
    ∀ N : ℕ, ∃ C : ℝ, ∀ᶠ t in atTop, ∀ x ∈ K, |h_t x| ≤ C * t ^ (-(N : ℝ))
```
Proof. `K' := cthickening 1 K` (compact). Gradient: `‖∇ e^{-tL}‖ = t e^{-tL} ‖∇L‖ ≤ t G` on `K'` for `t ≥ 0`
(`G := sup_{K'} ‖∇L₁‖ + ‖∇L₂‖`, finite by compactness), so `h_t` is `Λ`-Lipschitz on balls inside `K'` with
`Λ := tG + 1` (mean value inequality on the convex ball). Peak: for `x₀ ∈ K` with `H := |h_t x₀|`, on
`ball x₀ r`, `r := H/(2Λ) ≤ 1` (since `H ≤ 1 ≤ 2Λ`), `|h_t| ≥ H/2`; so
`∫_{K'} |h_t| ≥ (H/2) vol(ball x₀ r) = (H/2) c_d (H/(2Λ))^d`, i.e. `H^{d+1} ≤ (2^{d+1}/c_d) Λ^d ∫_{K'} |h_t|`.
With `Λ ≤ (G+1) t` for `t ≥ 1` and `∫_{K'}|h_t| ≤ t^{-(d+1)N - d}` eventually: `H^{d+1} ≤ C' t^{-(d+1)N}`,
hence `H ≤ C'^{1/(d+1)} t^{-N}`. Uniform in `x₀ ∈ K` because `C'` depends only on `K, G, d`.

### P∞. Pointwise corollary
`∀ x, SuperPoly fun t ↦ h_t x` (take `K = {x}`), and the `∀ᶠ ∀ x ∈ K` form re-expressed as
`SuperPoly` of any measurable selection — not needed.

### G. Gradient bound lemma (reusable)
`‖fderiv ℝ (fun w ↦ exp(-(t L w))) x‖ ≤ t ‖fderiv ℝ L x‖` for `t ≥ 0`, `L ≥ 0`, `L` differentiable at `x`.

**Proposed tide:** G + U∞ + P∞ in `Laplace/Multi/LocalUniform.lean` (~350 lines). Vote: all.

## GPT-6 Astra v1 (summary; verbatim in `gpt_germbij_lu_v1.md`)
- Peak argument correct; exponent d+1 and constant `2^{d+1} Λ^d / c_d` right. Handle `H = 0` separately (positive-radius
  ball-volume lemma); `G = 0` harmless since `Λ ≥ 1`; empty `K` vacuous. Rapid `O(t^{-N})` for all N ⇒ little-o by
  shifting N (the seabed helper `superPoly_of_forall_eventually_le` is exactly this).
- API: `∀ N, ∃ C ≥ 0, ∀ᶠ t, ∀ x ∈ K, |h_t x| ≤ C t^{-N}`; pointwise corollary `∀ x, SuperPoly (fun t ↦ h_t x)`;
  avoid real `iSup`/`C(K,ℝ)` infrastructure.
- Regularity: `C¹` with bounded derivative on a neighbourhood suffices for the upgrade itself; keep `C^∞` in the
  application theorem (upstream hypothesis). Make the peak lemma generic: bounded amplitude + Lipschitz + L¹ mass ⇒ powered estimate.
- CORRECTION to my note: derivative agreement IS true under smoothness (second interpolation: `‖D²h_t‖ ≤ B t²`,
  Taylor along a segment with `s = t^{-(N+3)}`); all fixed-order derivatives locally uniformly SuperPoly. Follow-up tide.
- Normalized densities uniform: `|w₂/Z₂ − w₁/Z₁| ≤ Z₂^{-1}(|h_t| + |ρ|)`, `ρ = Z₂/Z₁ − 1` — one-liner later.

## Vote
- Claude: G + Lip + powered peak + root corollary + U∞ + pointwise, one file `Laplace/Multi/LocalUniform.lean`
- GPT-6 Astra: same; derivative agreement and normalized densities as separate follow-ups

## Numerical check
Not feasible: inequalities and SuperPoly assertions; the ball-volume scaling `vol(ball r) = r^d vol(ball 1)` is Mathlib's.

## Step 3 plan
`Laplace/Multi/LocalUniform.lean`: `norm_fderiv_exp_neg_le` (G), `abs_exp_sub_le_one`, `hasFDerivAt_expWeight`,
`norm_fderiv_weightDiff_le` (‖∇h_t‖ ≤ t(‖∇L₁‖+‖∇L₂‖)); generic `pow_abs_le_of_lipschitz_of_integral` (bounded
amplitude ≤ 1, Λ-Lipschitz on ball x₀ 1 ⊆ K', ⇒ |f x₀|^{d+1} ≤ 2^{d+1}/c_d · Λ^d ∫_{K'}|f|); `exists_lipschitz_const_on_cthickening`
(G from compactness + continuity of fderiv); `pow_abs_exp_sub_le` (powered peak for h_t, t ≥ 1);
`eventually_uniform_abs_exp_sub_le` (U∞); `superPoly_exp_sub_at` (pointwise).

## Result

Commit `73df2ae` on `tide/germbij-local-uniform`: `Laplace/Multi/LocalUniform.lean` (343 lines), imported from
`Laplace.lean`; `lake build` clean (8892 jobs), `scripts/sorries` 0/0/0/0. Three LSP rounds plus one
`omit [Fintype ι] in` that produced an `isDefEq` timeout although the linter called the instance unused.

Theorems: `expWeight_le_one`, `abs_exp_sub_le_one`, `hasFDerivAt_expWeight`, `norm_expWeight_deriv_le`,
`norm_fderiv_weightDiff_le`; generic peak lemma `pow_abs_le_of_lipschitz_of_setIntegral`;
`exists_gradient_bound_on`; powered peak `pow_abs_exp_sub_le` and root form `abs_exp_sub_le_rpow`;
**`eventually_uniform_abs_exp_sub_le`** (∀ N ∃ C, eventually ∀ x ∈ K, |h_t x| ≤ C t^{-N}); `superPoly_exp_sub_at`.

Surprises: (1) the peak argument needed no case on `G = 0` once `Λ = tG + 1`; (2) Astra's correction that
DERIVATIVES of `h_t` are also uniformly SuperPoly (second interpolation) — a clean follow-up; (3) the
`omit`/isDefEq interaction.

## Retrospective

`retrospectives/2026-09-19-18-30-tide-germbij-local-uniform.tex` (compiled PDF alongside).
