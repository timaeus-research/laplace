# Research round 80 — the intrinsic Fisher completion: Lean route

Context: germbij response-map programme inside the laplace seabed (Lean 4.33, Mathlib current). The user's standing
direction: "tackle core features of the change in posterior expectation values with the change in the data distribution
that allow us to map the space of responses across the data manifold, from the featureless distribution of maximal
entropy to the actual data distribution; maximum beauty and depth."

## What is landed since round 79 (all sorry-free)

* `DataRayHelpers`: one-sided weighted variation `∫_a^b g(r)|r'| ≤ ∫_{Ioi R} g + 2∫_a^b g(r)(r')₋` (for `R ≤ r` on `[a,b]`,
  `IntegrableOn g (Ioi R)`), `√Var(f+g) ≤ √Var f + √Var g`, `Var f ≤ K²`.
* `DataRayBlocks`: `slackMean`, `hasDerivAt_slackMean` (`a' = −⟨u, Cov_{ρ_t}(S,h)⟩`), `slackMeanVel_le` (`a' ≤ a E_{ρ_t}(H−h)`),
  `depthVel`, `tangentVel`, the two block identities `r'V = ⟨u,Cov⟩ + c`, `Var⟨v',S⟩ = −⟨v',Cov⟩ + r'c`.
* `DataRayEstimates.eventually_dataRay_estimates`: eventually `√responseSpeedSq ≤ C₁‖Cov_{ρ_t}(S,h)‖ + C₂ g(r_t)|r'_t|`,
  `g(r_t)(r'_t)₋ ≤ C₃E_{ρ_t}(H−h) + C₄‖Cov‖`, `r_t ≥ 0`.
* `DataRayReverse.data_fisher_length_lt_top_iff_ray`: **along the data path `ρ_t = ν.tilted (t h)` towards a facet
  containing `E[S | h = H]` in its relative interior, the response path has finite Fisher length ⇔ the normal ray does
  ⇔ Σ_k √a_k < ∞.** (Your §3–4 plan of round 79 went through essentially verbatim: after making every time-`t`
  quantity opaque, all eight scalar lemmas were `linarith`/`calc`.)

So ranks 4 (data-ray) and 5 (layer classification — `RayFisherLengthClassification` already states finite ray length
⇔ Σ_k √(shellMass k) < ∞ with dyadic shells `dyadicShell g R k = {R/2^{k+1} < g ≤ R/2^k}` of the slack `g`; is there
anything left in your §5.5 beyond the explicit `m_n ~ n^{−α}` examples?) are done. We now start rank 1, the intrinsic
completion (your §5.1). We want the precise Lean route BEFORE writing infrastructure.

## Seabed objects (exact)

```lean
-- the exponential family on W = dirSpan ν 1 S ⊆ (J → ℝ), S bounded (hS : ∀ j, Bdd (S j)), ν a probability measure
Pfam θ = familyMeasure ν (fun _ ↦ 1) (fun _ ↦ 0) S 1 θ = ν.tilted (fun x ↦ -1 * dirLoss S θ x)   -- dirLoss S θ x = ∑ i, θ i * S i x
lawCov ρ f g = (∫ f g ∂ρ) − (∫ f ∂ρ)(∫ g ∂ρ)
meanMap ν 1 0 S 1 θ = fun i ↦ ∫ S i ∂Pfam θ
raySpeedSq S ν θ u t = lawCov (Pfam (θ − t • u)) (dirLoss S u) (dirLoss S u)
responseSpeedSq hS ν hh t = lawCov (Pfam θ_t) (dirLoss S θ'_t) (dirLoss S θ'_t)   -- θ_t = dataTheta (response coordinates of ρ_t)
-- facts
exists_coercive_familyMeasure hS ν θ : ∃ lam > 0, ∀ w ∈ W, lam * ‖w‖^2 ≤ lawCov (Pfam θ) (dirLoss S w) (dirLoss S w)
lawCov_sq_le : lawCov ρ f g ^ 2 ≤ lawCov ρ f f * lawCov ρ g g          -- Cauchy–Schwarz
abs_lawCov_le : (∀ x, |f x| ≤ Bf) → (∀ x, |g x| ≤ Bg) → |lawCov ρ f g| ≤ 2 Bf Bg
continuous_lawCov_dirLoss_self hS P : Continuous fun w ↦ lawCov P (dirLoss S w) (dirLoss S w)
hasStrictFDerivAt_meanMap … : Dm(θ) v = fun i ↦ lawCov (Pfam θ) (S i) (dirLoss S v)  (as a CLM), and on W the
  intrinsic chart `intrinsicChart : W ≃ intrinsicInterior (momentBody ν 1 S)` (homeomorphism; `chartV`, `chartVInv`,
  `chartVInv_chartV`, `chartV_chartVInv`, continuity both ways); meanMap is injective on W.
-- the facet theorem (paths on [0,∞))
facet_fisher_access_iff … :
  (∃ η η' : ℝ → J → ℝ, (∀ s, η s ∈ W) ∧ (∀ s, 0 ≤ s → HasDerivAt η (η' s) s) ∧ ContinuousOn η' (Ici 0) ∧
     Tendsto (fun s ↦ meanMap … (η s)) atTop (𝓝 M) ∧
     (∫⁻ s in Ioi 0, ofReal √(lawCov (Pfam (η s)) (dirLoss S (η' s)) (dirLoss S (η' s)))) < ⊤)
  ↔ (∫⁻ r in Ioi 0, ofReal √(raySpeedSq S ν 0 u r)) < ⊤
```
Also available: `TiltVarianceComparison` (`e^{−2c} Var_Q f ≤ Var_{Q.tilted g} f ≤ e^{2c} Var_Q f` for `|g| ≤ c`),
`familyMeasure_sub_smul_eq_tilted_base : Pfam (θ − t•u) = (Pfam θ).tilted (fun x ↦ t * dirLoss S u x)`,
`tilted_tilted`, `integral_tilted`, Hellinger material is NOT yet on the seabed (no `√(dP/dν)` object).
Mathlib: `UniformSpace.Completion`, `Completion.extension`, `HasDerivAt`, `intervalIntegral`, `eVariationOn`,
`MeasureTheory.eLpNorm`, `Lp`.

## Questions

**Q1 (path class and the metric).** Define `fisherLength γ γ' a b = ∫ t in a..b, √(lawCov (Pfam (γ t)) (dirLoss S (γ' t)) (dirLoss S (γ' t)))`
and `d_F θ η = ⨅ over paths`. Which path class is the minimal one that makes (i) the triangle inequality, (ii) finiteness
(segments), (iii) `d_F = 0 → θ = η`, (iv) topology = usual, and (v) later the completion-point realisation, all cheap in
Lean? Options: (a) C¹ on `[0,1]` (`HasDerivAt` everywhere + continuous derivative) with a junction-smoothing
reparametrisation `φ(s) = 3s² − 2s³` for concatenation; (b) piecewise C¹ (a finite partition); (c) Lipschitz/absolutely
continuous with a.e. derivative; (d) avoid paths: define `d_F` as the *intrinsic metric of the Hellinger embedding* or via
a sup over "Fisher-1-Lipschitz functions". Please give the definition you would write, and the proof sketch of the
triangle inequality in that class (in particular how to glue `HasDerivAt` at the junction — `HasDerivWithinAt.union` on
`Iic ∪ Ici`? — and the change-of-variables lemma for the reparametrised length).

**Q2 (topology and positivity cheaply).** Our plan: (α) `d_F(θ,η) ≤ length of the segment ≤ C(θ,η) ‖θ − η‖` with
`C = sup_{[θ,η]} √Var⟨·⟩ ≤ 2 card·B·‖·‖`-type bound, so the usual topology is finer; (β) `‖m(θ) − m(η)‖ ≤ B d_F(θ,η)` via
`d/dt m(γ t) = Cov_{Pfam γ}(S, ⟨γ',S⟩)` and `|Cov(S_j, ℓ)| ≤ √Var S_j √Var ℓ ≤ B √Var ℓ` (Cauchy–Schwarz, landed), so
`d_F → 0 ⇒ m → m ⇒ θ → θ` by continuity of the inverse chart, giving positivity and the other inclusion. Any gap? Which
norm on `J → ℝ` should `B` refer to (sup norm on `J → ℝ` is the Pi norm in Lean; `dotJ` pairs coordinates)?

**Q3 (the Hellinger Lipschitz bound).** `‖√p_θ − √p_η‖_{L²(ν)} ≤ ½ d_F(θ,η)`. Route A: pointwise `d/dt √p_{γ t}(x) =
−½ √p_{γ t}(x) (ℓ_t(x) − E_{P_{γ t}} ℓ_t)` with `ℓ_t = ⟨γ'_t, S⟩`, then Minkowski's integral inequality in `L²(ν)`
(`∫₀¹ ‖F_t‖₂ dt ≥ ‖∫₀¹ F_t dt‖₂`) — which Mathlib lemma (`eLpNorm_integral_le`? `MeasureTheory.Lp` Bochner integral of an
`Lp`-valued function?) Route B: avoid Minkowski by a duality/Cauchy–Schwarz trick against a test function
(`‖F‖₂ = sup_{‖φ‖₂≤1} ∫ F φ`, then Fubini + pointwise bound + CS in x). Route C: prove only the energy bound
`H(θ,η)² ≤ ¼ ∫₀¹ Var_{γ t}⟨γ',S⟩ dt` and get `H ≤ ½ L` by constant-speed reparametrisation (is that worth it?).
Route D: work with the Hellinger *affinity* `∫ √(p_θ p_η) dν = Z(θ/2+η/2)/√(Z θ Z η)` (exact for exponential families!)
and relate `2 − 2 affinity = H²` to the length by a second-derivative/convexity argument along the segment (the log
partition function is convex; the Hellinger distance along a segment is controlled by ∫ √Var by the geodesic-convexity
of … ?). Which is cleanest in Lean, and is there a slicker *exact* identity for exponential families that gives the
inequality for segments, after which general paths follow by the triangle inequality of `H` (Hellinger is a metric —
`H(θ,η) ≤ Σ H(γ(t_i), γ(t_{i+1})) ≤ ½ Σ (segment lengths) → ½ L(γ)` by a Riemann-sum/partition argument, avoiding
L²-valued calculus entirely)? Please assess Route D + partitions carefully: it seems to need only (1) `H` is a metric,
(2) `H(θ,η) ≤ ½ · segment length + o(‖θ−η‖)`, (3) `L(γ) = lim Σ segment lengths` — is (3) a Mathlib-available
Riemann-sum statement for continuous integrands (`intervalIntegral` via `BoxIntegral`/`tendsto_sum_…`)? Perhaps better:
(2') `H(θ,η) ≤ ½ ∫₀¹ √Var_{P_{θ+t(η−θ)}}⟨η−θ,S⟩ dt` EXACTLY for segments by a one-dimensional argument (the family
restricted to the segment is a 1-parameter exponential family, `√p_t` is differentiable in `t`, and Minkowski in 1-D
over the segment is the same problem…). Tell us which route to take and the Lean skeleton (lemma list with statements).

**Q4 (the completion).** `W` is a `Submodule` (subtype of `J → ℝ`). We need a `MetricSpace` structure with `d_F` on a
type synonym (`def WF := dirSpan ν 1 S` with `@[instance]` `MetricSpace WF`?), then `UniformSpace.Completion WF`, and
`Completion.extension` of `m : WF → J → ℝ` (uniformly continuous by Q2) and of `Ψ : WF → L²(ν)`. Pitfalls with type
synonyms carrying two topologies (the subspace topology of `J → ℝ` versus the `d_F` topology; Q2 shows they coincide,
but instance diamonds are a Lean problem, not a math one). What is the cleanest Lean architecture: (i) a structure
`FisherPoint` wrapping `W`, (ii) `letI` local instances inside a section, (iii) transport the metric to the mean atlas
`ri P ⊆ J → ℝ` (a `Set`, so a subtype) via the chart, where the ambient topology is again the subspace one?

**Q5 (the upgraded facet theorem).** Which formulation of "completion points over `M ∈ ri F`" avoids the infinite
concatenation of near-optimal paths? Candidates: (a) `∃ x ∈ Ŵ_F, m̄ x = M` ⇔ `∃ (θ_n) d_F-Cauchy with m(θ_n) → M`
(true by definition of the completion + continuity of `m̄`); then (b) `(θ_n) d_F-Cauchy with m(θ_n) → M` ⇒ ray finite.
For (b): from Cauchy we get `Σ_n d_F(θ_n, θ_{n+1}) < ∞` along a subsequence; choose paths `γ_n` from `θ_n` to `θ_{n+1}`
of length `≤ d_F + 2^{−n}`, concatenate into ONE path on `[0,∞)` with finite total length whose means converge to `M`
(the concatenated path's means converge because … the path could wander: a segment of small Fisher length has means
within `B·length` of `m(θ_n)` by Q2(β)! so `sup_{t ∈ [n,n+1]} ‖m(γ t) − M‖ ≤ ‖m(θ_n) − M‖ + B(d_F + 2^{−n}) → 0`). The
infinite concatenation is a path defined piecewise on `[n, n+1]`; with the junction-smoothing reparametrisation each
piece is C¹ with zero derivative at both ends, so the glued path is C¹ on `[0,∞)` (derivative continuous: each piece's
derivative is continuous on `[n,n+1]` and vanishes at the ends). Then `facet_fisher_access_iff` applies verbatim.
Conversely ray finite ⇒ the ray is a finite-length path ⇒ `θ_n = −n u` (or `vM − n u`) is `d_F`-Cauchy with means → M.
Is this the right theorem? Any subtlety in the Lean gluing of countably many C¹ pieces (`HasDerivAt` at integer
junctions from the two one-sided within-derivatives, both zero)? Is `ContinuousOn η' (Ici 0)` fine with a piecewise
definition (continuity at junctions since both one-sided limits are `0`)?

**Q6 (what is the deep statement after that).** Your round-79 note: "whether completion points with the same limiting
mean, or the same Hellinger limit, must coincide". With the facet theory in hand, can we prove: over `M ∈ ri F` (facet,
accessible), the fibre `m̄^{−1}(M)` is a single point? Sketch: two Cauchy sequences with means → M; the facet analysis
shows both eventually decompose `θ = v − r u` with `v → vM`, `r → ∞`; `d_F(θ_n, θ'_n) ≤ d_F(θ_n, vM − r_n u) + d_F(vM −
r_n u, vM − r'_n u) + …`; the tangential correction `d_F(v − r u, vM − r u) ≤ ∫ √Var_{P_{v_s − r u}}⟨v − vM, S⟩ ds` is
`≤ e^{…}·‖v − vM‖·√(Var_{P^A}…)` hmm — this needs the *tangential* Fisher speed at depth `r` to stay bounded (true: the
tangential variance is bounded by `B²`), so `≤ C‖v_n − vM‖ → 0`; the radial piece is a tail of the finite ray length
`→ 0`. So the fibre is a point, and the completion boundary over the accessible facets is a copy of `ri F` (with the
Hellinger limit `√p_{vM}^A`, the face-conditioned density!). Is this right, and is it the theorem to state ("the
Fisher completion of the response space is the moment polytope's interior together with, over each accessible facet,
its relative interior, glued by the face charts")? What breaks in codimension ≥ 2 (charged square)?

**Q7 (ranking).** Given all of the above, rank the concrete next Lean modules (≤ 300 lines each) in the order you
would land them, with one-line statements. Remember: new mathematics over process; each module must be sorry-free.
