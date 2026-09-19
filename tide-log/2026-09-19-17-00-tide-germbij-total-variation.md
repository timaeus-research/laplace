# Tide: germbij local total-variation upgrade

**Direction (user):** "continue on auto" (2026-09-19) after the projective-closure tide; this tide takes that tide's first follow-up, the observable-class upgrade recommended by the consult ("arguably the best additional target").
**Seabed:** laplace, commit 3a8eaa9 (main; ProjectiveClosure merged)
**Started:** 2026-09-19T17:00Z
**Ledger direction:** germbij: local total-variation upgrade — exact beyond-all-orders agreement of two Laplace families on C_c^inf tests implies int_K |e^{-tL2} - e^{-tL1}| = o(t^-inf) and hence agreement on all continuous compactly supported tests.

## Seabed snapshot

- `superPoly_difference_of_projective` / `projective_forces_exact_at` / `normalized_expectations_closure`
  (ProjectiveClosure): exact agreement `SuperPoly (I₂(φ) − I₁(φ))` for every φ ∈ C_c^∞ — the tested class only.
- `SuperPoly` closure lemmas (`add`, `sub`, `congr`, `bounded_mul`, `div_id`), `superPoly_of_eventually_abs_le_exp`.
- `integrable_mul_exp_neg_of_compactSupport`, `laplace_moment_bounded` (OnePointAnchoring).
- Missing: any statement about continuous (or bounded measurable) observables; any pointwise control of
  `e^{-tL₂} − e^{-tL₁}` by `L₂ − L₁`.

## Candidates v1 (Claude)

Notation: `a = e^{-tL₁}`, `b = e^{-tL₂}`, `D = L₂ − L₁`, `I_i(φ) = ∫ φ e^{-tL_i}`.

### P. Pointwise inequalities (elementary)
For `x, y ≥ 0`: `|e^{-x} − e^{-y}| ≤ |x − y|` and `(y − x)(e^{-x} − e^{-y}) ≥ 0`. Hence for `t ≥ 0`:
`D·(a − b) ≥ 0` and `|a − b|² ≤ t·D·(a − b)`.

### V. Local total variation beyond all orders
```
theorem superPoly_integral_sq_mul_abs_exp_sub {L₁ L₂} (h1 h2 : ContDiff ℝ ∞) (hL1 hL2 : nonneg)
    (hexact : ∀ φ, ContDiff ℝ ∞ φ → HasCompactSupport φ → SuperPoly fun t ↦ I₂(φ) − I₁(φ))
    (η : smooth, compactly supported) :
    SuperPoly fun t ↦ ∫ w, η w ^ 2 * |e^{-tL₂ w} − e^{-tL₁ w}|
```
Proof: `E(t) := ∫ η² D (a − b) = I₁(η²D) − I₂(η²D)` is SuperPoly (η²D ∈ C_c^∞ — uses smoothness of the losses)
and ≥ 0. AM–GM with a free `ε = t^{-N}`: `|a−b| ≤ t^{-N}/2 + t^{N}|a−b|²/2 ≤ t^{-N}/2 + t^{N+1} D(a−b)/2`, so
`∫ η²|a−b| ≤ (∫η²) t^{-N}/2 + t^{N+1} E(t)/2 ≤ C_N t^{-N}` eventually, for every N. No Hölder, no square roots.

### U. Agreement on bounded measurable / continuous compactly supported tests
```
theorem superPoly_difference_of_bounded {φ} (hφm : AEStronglyMeasurable φ) (hφs : HasCompactSupport φ)
    (hφb : ∀ w, |φ w| ≤ M) : SuperPoly fun t ↦ I₂(φ) − I₁(φ)
theorem superPoly_difference_of_continuous {φ} (hφc : Continuous φ) (hφs) : SuperPoly fun t ↦ I₂(φ) − I₁(φ)
```
Take a bump `η = 1` on a closed ball containing `tsupport φ`; `|∫ φ (b − a)| ≤ M ∫ η² |a − b|`.

### C. Corollaries in the closure package
`superPoly_difference_of_projective_continuous` (projective agreement on C_c^∞ + agreement near one C² zero
⇒ exact agreement on C_c^0), `normalized_expectations_closure_continuous` (the 1/Z headline with the C⁰
conclusion added).

**Proposed tide:** P + V + U + C in `Laplace/Multi/TotalVariation.lean` (~300 lines). Vote: all.

## GPT-6 Astra v1 (summary; verbatim in `gpt_germbij_tv_v1.md`)

- P, V, U correct; the AM–GM route with ε = t^{-N} loses nothing at the SuperPoly level; use the O(t^{-(N+1)})
  bound to get o(t^{-N}). No hidden integrability (e^{-tL} ≤ 1 for t ≥ 0). Note E = I₁ − I₂ (one negation).
- Smooth losses are sufficient, not necessary: what is needed is `η²D ∈ C_c^∞`, i.e. smoothness of D = L₂ − L₁.
  Keep `ContDiff ℝ ∞` for both for this tide; do not claim a necessity theorem.
- Package the compact-set statement `∫_K |e^{-tL₂} − e^{-tL₁}| = o(t^{-∞})` (uniform over bounded tests
  supported in K, including t-dependent ones). Continuous cutoffs follow by domination. Local L^∞ is TRUE under
  smoothness (gradient bound ‖∇h_t‖ ≤ Ct ⇒ sup_K |h_t| ≤ C(t^d ∫_{K'}|h_t|)^{1/(d+1)}) but needs interpolation
  infrastructure — later tide. Global L^∞ / noncompact tails do not follow.
- Normalized version for bounded compactly supported tests via I₂/Z₂ − I₁/Z₁ = (I₂−I₁)/Z₁ + (I₂/Z₂)(1 − Z₂/Z₁);
  needs 1/Z₁ = O(t^{d/2}) (anchor) and Z₂/Z₁ − 1 SuperPoly. Scope: compactly supported φ only.
- (P): elementary route via `Real.add_one_le_exp`, split on x ≤ y; sign lemma by splitting on L₁ ≤ L₂ (handles t = 0).
- Wiring: keep the chain projective + anchor ⇒ smooth exact ⇒ local TV ⇒ bounded tests; do not replace the anchor
  hypotheses by a bare common zero.

## Vote
- Claude: P + V + local-TV + U + C (+ normalized bounded version), one file `Laplace/Multi/TotalVariation.lean`
- GPT-6 Astra: ship P+V+local-TV+U+C together; leave local L^∞ and noncompact tails for later

## Numerical check
Not feasible / not needed: the statements are inequalities and SuperPoly assertions; the one closed form
(|e^{-x} − e^{-y}| ≤ |x − y| on x, y ≥ 0) is the mean value theorem for a 1-Lipschitz function.

## Step 3 plan
`Laplace/Multi/TotalVariation.lean`: pointwise P (`abs_exp_neg_sub_exp_neg_le`, `mul_exp_neg_sub_exp_neg_nonneg`,
`weightDiff_mul_nonneg`, `sq_exp_sub_le_mul`); SuperPoly helpers (`superPoly_of_forall_eventually_le`,
`SuperPoly.of_abs_le`, `SuperPoly.polyBounded_mul`); `integrable_of_bounded_of_hasCompactSupport`;
V `superPoly_integral_sq_mul_abs_exp_sub`; `exists_smooth_bump_one_on_compact`; U `superPoly_difference_of_bounded`,
`superPoly_difference_of_continuous`; K-form `superPoly_setIntegral_abs_exp_sub`; C
`superPoly_difference_of_projective_bounded`, `superPoly_normalized_difference_of_bounded`.
