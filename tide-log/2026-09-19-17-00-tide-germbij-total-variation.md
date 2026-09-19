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
