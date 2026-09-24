# Query: the pointwise fibre identity of the wall atlas — cleanest Lean route

## Proven on the hironaka branch `wall-atlas` (Lean 4 + Mathlib, real analytic manifolds)

`n = d + 1` coordinates on the total space `ℝ^n`, truth coordinate index `ℓ`, `F` analytic near
the wall point `0`, `W ∋ 0` a connected open (e.g. a box `K' × (−δ, δ)`), `g : U → W` the Watanabe
resolution of `G = F · z_ℓ` (proper, surjective, analytic iso off `{G = 0}`).

- `WallChartAt F ℓ g P` (every `P` over the wall `{z_ℓ = 0}`): a chart `φ` of `U` centred at `P`
  with, on the whole target, `F(rep u) = a(u) ∏ u_i^{k_i}` (`a` analytic unit),
  `(rep u)_ℓ = S ∏ u_i^{q_i}` EXACTLY (`S = ±1`, `q ≠ 0`), `det D rep(u) = b(u) ∏ u_i^{h_i}` (`b` unit),
  where `rep = g ∘ φ⁻¹ : ℝ^n ⊇ target → W ⊆ ℝ^n` is the chart representative (analytic on the target).
- `WallAtlas F ℓ g C` for compact `C ⊆ W ∩ {z_ℓ = 0}`: finitely many such charts `φ_i`, radii
  `ρ_i > 0` with closed sup-balls `B̄(0, ρ_i) ⊆ target_i`, two-sided bounds on `|a_i|, |b_i|` on the
  boxes, and the open cores `source_i ∩ φ_i⁻¹(B(0, ρ_i))` cover `g⁻¹(C)`.
- Small-parameter cover: for compact `L ⊆ W`, `g⁻¹(L ∩ {|z_ℓ| ≤ ε}) ⊆ ⋃ cores` for all small `ε`.

Available in the toolkit: the injectivity lemma `injOn_of_injOn_preimage_dense` (rep is injective
on `{det ≠ 0}` inside the target, from the iso property off `{G ≠ 0}` and density of `{G ≠ 0}`),
`IsMonomialChart` (target open, rep analytic, injective off `{monomial h = 0}`, phase and Jacobian
monomial × continuous unit) and `IsMonomialChart.exists_resolutionChartData`, which yields a box
`χ.K` around the centre and an exact TOTAL-SPACE transport certificate
`TransportsToOn volume volume χ.K χ.φ (ofReal ∘ jacAbs)`:
`∀ s ⊆ K, ∀ g measurable ≥ 0, ∫⁻_{s} g(φ x) J(x) dx = ∫⁻_{φ '' s} g dy`.
Mathlib: `integral_image_eq_integral_abs_det_fderiv_smul` (change of variables for injective C¹
maps on measurable sets), `integral_prod`/Fubini on `ℝ^n = ℝ^d × ℝ`, `PartitionOfUnity`.

## Target (what laplace consumes)

For every `0 < |s| < ε` and every bounded measurable `ψ : ℝ^d → ℝ` (in practice continuous with
compact support, or nonnegative measurable first):
```
∫_{ℝ^d} ψ(x) · 1_{K}(x) dx   (fibre over s: points (x, s))
  = ∑_i ∑_{sign branches} ∫_{D_i(s)} (ρ_i ψ)(rep_i(u', v_i(u', s))) · D_{i,s}(u') du'
```
with `u = (u', v)` the chart coordinates split at a solve index `ℓ_i` with `q_{i,ℓ_i} > 0`,
`v_i(u', s) = (|s| ∏_{j≠ℓ_i} |u'_j|^{-q_j})^{1/q_{ℓ_i}}` (sign fixed by the branch), and the fibre
density `D_{i,s}(u') = (|b_i| / q_{ℓ_i}) |s|^{(h_ℓ+1)/q_ℓ − 1} ∏_j |u'_j|^{h_j − q_j (h_ℓ+1)/q_ℓ}` (times the
unit read at `(u', v_i)`), `ρ_i` a partition of unity subordinate to the cores. (The algebraic
identities for `v_i`, the phase and the density are already formalised in laplace
`WallFibreFormulas.lean`.)

## Two candidate proofs

(A) **Total-space transport + Fubini + 1D substitution + continuity.** Transport certificate on each
box: `∫_{ℝ^n} Ψ(x, s) dx ds = ∑_i ∫_{K_i} Ψ(rep_i u) |det| du` for `Ψ = ρ_i-weighted test functions`
(needs the cores to cover the preimage of the support, and rep injective off a null set — the
toolkit's certificate handles this). Then on each box use Fubini in `(u', v)` and substitute
`v ↦ s = S v^{q_ℓ} ∏ u'^{q'}` on `v > 0` and `v < 0` separately (monotone in `v`, Jacobian
`|∂s/∂v| = q_ℓ |s| / |v|`), to rewrite the right side as `∫ η(s) [chart fibre integrals](s) ds` for
`Ψ(x,s) = ψ(x) η(s)`. Comparing with the left side `∫ η(s) [∫ ψ(x) dx] ds` for all `η` gives the
identity for a.e. `s`; both sides are continuous in `s` (compactly supported continuous
integrands, moving domains handled by the partition weights vanishing near the box boundary), so
the identity holds for every `s ≠ 0` small.

(B) **Fibrewise change of variables directly.** For fixed `s`, the map `u' ↦ (rep_i(u', v_i(u', s)))_x`
from the solved domain `D_i(s)` into the fibre `ℝ^d` is injective off a null set with Jacobian equal
to the relative determinant `|det D rep| · |v| / (q_ℓ |s|)` (Schur-complement / implicit-function
identity: `det D_{u'} x(u') = det D(rep) / (∂s/∂v)` when `s(rep(u', v(u')))` is constant); apply
Mathlib's `integral_image_eq_integral_abs_det_fderiv_smul` on each solved domain and sum over the
charts and branches, using the partition of unity to avoid double counting and the iso property
to see the images cover the fibre off a null set.

## Questions

1. Which route is cleaner to formalise with Mathlib as it stands? Route (A) leans on the existing
   total-space certificate and one-dimensional calculus but needs the a.e.-to-pointwise upgrade;
   route (B) needs the determinant identity for the implicit parametrisation and fibrewise
   injectivity/cover arguments on the manifold. Please give the mechanism of each step, the Mathlib
   lemmas you would use, and where the real friction is.
2. For the a.e.-to-pointwise step in (A): what exactly is needed for continuity in `s` of the chart
   side (the solved domain `D_i(s)` moves with `s`; the density has the factor
   `|s|^{(h_ℓ+1)/q_ℓ − 1}` and possibly negative powers of `|u'_j|`)? Is it better to avoid the
   continuity argument by proving the identity for all `s` at once via a measurable dependence / a
   `ν`-fibre disintegration statement, or by formulating the identity as an equality of pushforward
   measures on `ℝ^d × ℝ` restricted to the fibre?
3. Statement design for laplace: laplace's `RescaledData` needs, along a schedule `s(t) → 0`, the
   rescaled fibre integrand as an explicit function of `u'` with pointwise limits, a comparability
   lower bound and integrable envelopes. Given the fibre density above (negative powers of `|u'_j|`
   possible: `r_j = h_j − q_j (h_ℓ+1)/q_ℓ` may be `< 0`), how should the fibre identity be stated
   so that the sector analysis on the laplace side can start from it directly — e.g. as a finite sum
   over `(chart, sign branch)` of integrals over `ℝ^{d}` with an explicit indicator of the solved
   domain and the closed-form density, with the units evaluated at `(u', v_i(u', s))`?
4. Sign branches: with `(rep u)_ℓ = S ∏ u_i^{q_i}` exactly, the fibre over `s > 0` in the box is
   `{u : S ∏ u_i^{q_i} = s}`; for each sign pattern of the `u_i` with `q_i` odd this is a graph over
   `u'`. What is the least painful way to organise the branches in Lean — sum over the `2^{#odd}`
   sign vectors with indicator sets, or reparametrise the box by `u_i ↦ |u_i|` with multiplicities?
5. Is there any reason to prefer building the fibre identity on the hironaka side (manifold, in
   terms of `watanabeRep`, `TransportsToOn`) versus stating a Euclidean-only version on the laplace
   side (finitely many analytic maps `rep_i : box_i → ℝ^n` with the monomial identities as
   hypotheses, plus the cover/injectivity certificates), leaving the manifold only in the existence
   theorem? The second keeps laplace free of the manifold library.

Be concrete; name Mathlib lemmas where you can and flag the ones you are not sure exist.
