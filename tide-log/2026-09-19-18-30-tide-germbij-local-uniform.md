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
