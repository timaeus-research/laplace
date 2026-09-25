# Research consult, round 31 (germbij / laplace `Laplace/Multi/*`)

Same programme (PI: "map the space of responses across the data manifold, from the featureless distribution of
maximal entropy to the actual data distribution, with maximum beauty and depth"). All formal, sorry-free, on `main`.

## Landed since round 30 (your ranking 1–8)

1. `EssentialRange` + `MomentBody` (your #1): for a bounded statistic `S : J → X → ℝ` under a positive prior `π·μ`
   on ANY measurable space, with no nonzero `v` such that `S_v` is a.e. constant:
   **`range η = interior (closure (convexHull (essRange S)))`**, `essRange := support of the law of S under π·μ`
   (Mathlib `Measure.support`, conull on second-countable spaces). Your cap lemma verbatim: far point in every
   direction (via the closed half-space and the test point `x − (3δ/4) sgn e`), ball of positive mass, perturbation
   stability by boundedness, compactness of the sup-norm sphere; coercivity `ψ(θ) + ⟨θ,x⟩ ≥ c‖θ‖ + log m`;
   Hahn–Banach for `⊆`. ~560 lines total.
2. `DualPotential` (your #2): `DA(a) = −t⟨·, m(a)⟩` (Fréchet), `I(y) = −t⟨θ(y), y⟩ − A(θ(y))` on the response space
   with `θ = m⁻¹` (global inverse from `MeanMapEmbedding`), **`KL(P_b‖P_a) = I(m_b) − I(m_a) + t⟨a, m_b − m_a⟩`**,
   `DI(m(a)) = −t⟨a,·⟩`, `D²I(m(a)) = −t (Dm(a))⁻¹` with `D²I (Cov(Rᵢ,R_v))ᵢ = v`, and
   `⟨Dm v, D²I (Dm v)⟩ = G_a(v,v)` (pointwise path-length transport).
3. `SegmentDivergence` (your #3): `KL(P_b‖P_a) = t²∫₀¹ s V`, `KL(P_a‖P_b) = t²∫₀¹(1−s)V`, Jeffreys
   `Length² ≤ KL + KL`, three-point identity, Pythagoras, projection ⇒ orthogonality.
4. `TemperatureSlice` (your #4, coverage half): the slice at `t` is the contrast family under the tilted prior
   `e^{−tL₀}π` with natural parameter `ta`; same null sets ⇒ same essential range; hence
   **`range (a ↦ m(t,a)) = interior (momentBody R)` for every `t > 0`** (bijection), and the joint slice is a graph
   `η₀ = h_t(M)` over that fixed body. NOT built: `∂_{η₀}I = −t`, the reduced potential `J_t`.
+ `ObservableRegression`: `Φ(y) = ⟨φ⟩_{θ(y)}` has `DΦ(m(a)) (Cov(Rᵢ,R_v))ᵢ = Cov(φ, R_v)` — the response of any
   observable in mean coordinates is the regression of `φ` on the statistic; `|DΦ ṁ| ≤ √Var(φ)√⟨ṁ, D²I ṁ⟩`.
Not done: (5) `N^⊥`, (6) the wall mean band, (7) two-term wall law, (8) abstract moving minimum.

## Where this leaves the programme
Bounded-statistic setting: the map is complete (natural coordinates; the prior at `θ = 0`; `η` a global chart onto the
interior of the moment body; `A` and `I` the two convex potentials with inverse Hessians = the Fisher metric in the two
charts; KL = Bregman in both; segment identities; the ray with Cramér's rate function and the ess-inf endpoint; faces
as endpoints on finite alphabets; temperature slices as graphs over one body; observables as regressions).
Unbounded/non-steep setting: only the two-monomial wall (`x^p + a x^q` on `(0,∞)`): three-regime phase diagram with
constants, chart `ℝ ≃ₜ (0,∞)`, interior-minimum geometry, but NOT your mean-band description and NOT the two-term law.

## Questions
1. **Re-rank what remains** for the PI's goal, now that the bounded case is closed. Candidates: (a) the wall mean band
   `{v^r < u ≤ C_Γ v^r}` and the geometric reading of the phase diagram (your round-30 §1); (b) the general
   "non-steep exponential family" theorem — for an unbounded statistic on a σ-finite base, `range η` is the interior of
   the moment body iff the family is steep, and for non-steep families the image misses a boundary piece: is there a
   clean formal target that the wall instantiates (e.g. "`η` extends continuously to the non-open boundary points
   `θ₁ = 0, θ₂ > 0` with finite mean, and those means are NOT interior points of the closed convex hull of the range
   but lie on the gamma curve `u = C_Γ v^r`")? (c) the two-term wall law; (d) the variational characterisation of the
   temperature slice `∂_{η₀}I(η₀, M) = −t` and the reduced potential `J_t(M) = inf_e (I(e,M) + te) + ψ(t,0)` with
   `D²J_t = G_{RR}⁻¹`; (e) `N^⊥`; (f) the Cramér/large-deviation reading of the joint potential `I` (finite-dimensional
   Cramér theorem for the empirical mean of `S` under the prior: `I` is the rate function — is this a cheap corollary of
   Mathlib's Cramér? probably not in Mathlib); (g) the response of observables along the whole segment
   `⟨φ⟩_{m₁} − ⟨φ⟩_{m₀} = ∫ Cov(φ, R_{ṁ}) ds` in mean coordinates (a mean-coordinate form of `DataQuotient`'s path
   inequality); (h) anything you consider the single most beautiful missing statement.
2. **The wall in the language of the moment body.** Given (a): what is the right *general* theorem about a
   two-parameter family `e^{−θ₁ f − θ₂ g} dx` on `(0,∞)` with `f, g` continuous, `0 ≤ g ≤ f` growth-ordered, of which the
   two-monomial wall is the instance, that yields the band and the chamber curve with a proof a formaliser can follow
   (fixed-mean monotonicity along `α ↦ β(α,v)`, endpoints), and which parts are genuinely Laplace-asymptotic?
3. **The joint rate function.** With `RayCramer` (1-d: `I'' = 1/Var`) and `DualPotential` (`D²I = Cov⁻¹`), the
   statement "`I(m) = sup_θ (−⟨θ,m⟩ − ψ(θ))` on the interior of the moment body" (the finite-dimensional Legendre
   identity) is presumably a ~40-line corollary of the convexity of `ψ` (`affLogZ_convexOn`) and the tangent
   inequality; confirm the cleanest route and whether the supremum should be stated as `IsMaxOn` at `θ(m)` (as we did
   for the ray) rather than as `sSup`.
Be concrete and Lean-aware; spell out hypotheses.
