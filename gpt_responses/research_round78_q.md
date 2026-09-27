# Research round 78: the facet accessibility theorem in our objects (Lemmas B and D, assembly)

## Landed since round 77 (laplace `Laplace/Multi/*`, sorry-free, warning-free, pushed)
- Your Lemma C: **TiltVarianceComparison** (`e^{−2c} Var_Q f ≤ Var_{Q.tilted g} f ≤ e^{2c} Var_Q f` for `|g| ≤ c`).
- Your Lemma E: **PathLengthPrimitive** (`|∫_{r a}^{r b} g| ≤ ∫_a^b |r'| g(r)`; `r → ∞` + finite weighted parameter length ⇒
  `IntegrableOn g (Ioi (r a))`).
- Your §2.2 (16)–(17): **DataDissipation** (`∫₀^∞ E_{ρ_t}(H − h) dt = log(1/p_*)`; data path → top-set conditional law; finite
  variation of the moment curve `∫₀^∞ |Cov_{ρ_t}(S_j,h)| ≤ 2‖S_j‖ log(1/p_*)`; total displacement `E[S_j | h = H] − E S_j`).
- Your rank 2 COMPLETE: **ScalarResponseRay** (1-D: `|q'_t|_F = |θ'_t| √Var_{P_{θ_t}} S`, mean map strictly decreasing, data means
  converging below the range ⇒ `θ_t → ∞`, finite response length ⇒ finite ray length), **AtomicIntervalDistortion** (atoms `2^{−k}`
  with masses `1/(2(k+1)(k+2))`, `h = 1_{S=0}`: shell masses `= w_{k+1}`, `Σ√ = ∞`, `∫₀^b |q'_t|_F → ∞`), **BinaryTiltLength**
  (`∫₀^∞ √Var_{ρ_t} 1_A dt = 2 arccos √p₀ < π`).

## The facet theorem: our objects and my proposed route (please check every step)
Objects: `ν` probability on `X`, `S : J → X → ℝ` bounded, `Pfam θ = ν.tilted(−⟨θ,S⟩)` (NEGATIVE exponent: our ray towards the
MAX-exposed face `{⟨u,·⟩ = β}` is `θ − t u`, uncharged gaps read `⟨η_n, v − v₀⟩ → +∞`), `W = dirSpan ν 1 S` (direction of the
affine span of the moment body; the chart `chartV : W ≃ ri(momentBody) − m₀` with inverse `chartVInv`, both strictly
differentiable), `V : Finset (J → ℝ)` with `statPoint S x ∈ conv V` a.e. and every vertex charged; an exposing pair `u, β` with
`∀ v ∈ V, ⟨u,v⟩ ≤ β`, face `F = conv(V.filter (⟨u,·⟩ = β))`, fibre `A = {x | ⟨u,S x⟩ = β}` (`faceFibre`), `faceMeasure ν A = ν(·|A)`,
face family `Pfam_A v = (faceMeasure ν A).tilted(−⟨v,S⟩)`, face mean map `meanMap_A`, face direction space
`T' = dirSpan (faceMeasure ν A) 1 S`, face chart `chartVInv_A`; `tendsto_meanMap_iff_faceMean_and_vertexGaps` (landed):
`meanMap(η_n) → M ∈ ri F ⟺ meanMap_A(η_n) → M ∧ ∀ uncharged v, ⟨η_n, v − v₀⟩ → +∞`.
Proposed Lemma B route:
 (B1) `T' ⊆ W ∩ u^⊥` always (face directions are differences `S x − S y` with `x, y ∈ A`, on which `⟨u,·⟩ = 0`).
      FACET HYPOTHESIS := `T' = W ∩ (ℝ u)^⊥` (with `u ∈ W`, WLOG by projecting `u` onto `W`: `⟨u, S x⟩` only depends on `proj_W u`
      when `S x − m₀ ∈ W` a.e.). Is this the right formal facet condition, and is it equivalent to `dim T' + 1 = dim W` given
      exposure? Do we even need `u ∈ W` if we decompose inside `J → ℝ` with the Euclidean inner product: `η = proj_{T'} η + (η − proj_{T'} η)`,
      and the second summand lies in `T'^⊥`? For the normal coordinate we need `η − proj_{T'} η ∈ ℝ u` for `η ∈ W`, i.e. `W ∩ T'^⊥ = ℝ u`.
 (B2) `Pfam_A η = Pfam_A (proj_{T'} η)` because `η − proj_{T'} η ∈ T'^⊥` = annihilator of `{S x − S y : x,y ∈ A}`, so `⟨η − proj η, S⟩`
      is a.e. constant on `A` and tilts of the face measure by a constant do nothing (`tilted_add_const`). Hence
      `meanMap_A η = meanMap_A (proj_{T'} η)` and `proj_{T'} η = chartVInv_A (meanMap_A η − m₀')` (the face chart is a bijection on `T'`).
 (B3) tangential convergence: `v_n := proj_{T'} η_n = chartVInv_A(meanMap_A η_n − m₀') → chartVInv_A(M − m₀') =: v_M` by
      continuity of `chartVInv_A` (from `hasStrictFDerivAt_chartVInv`) and `meanMap_A η_n → M` (from the landed criterion),
      provided `M − m₀' ∈ ri(face moment body)`: is `M ∈ ri F` (relative interior of the polytope face) the same as `M ∈ ri` of the
      face's moment body `conv{S x : x ∈ A}`? (We have `minimalFacePoly V M = F` and `ae_statPoint_mem_tightHull`.)
 (B4) normal divergence: pick an uncharged vertex `z` (exists iff `F ≠ P`) and a charged face vertex `z₀`:
      `⟨η_n, z − z₀⟩ = ⟨v_n, z − z₀⟩ − r_n ⟨u, z − z₀⟩` with `η_n = v_n − r_n u`, `⟨u, z − z₀⟩ = ⟨u,z⟩ − β < 0`, `⟨v_n, z − z₀⟩` convergent,
      hence `r_n → +∞`. Correct? (Here I need `η_n ∈ W`; our data paths and all natural-parameter paths in the atlas live in `W`.)
Proposed Lemma D (all under `q = Pfam η`, `η = v − r u`, `ℓ = β − ⟨u,S⟩ ≥ 0`, `A = {ℓ = 0}`, `p = q(A)`, `ε = 1 − p`,
`Y = S − ⟨proj⟩`… ): please restate D with the scalar completion of squares in OUR notation: for `a₀ : ℝ`, `z ∈ T'`,
`Var_q(a₀ ℓ + ⟨z,S⟩) ≥ a₀² (Var_q ℓ − ‖Cov_q(ℓ, S|_{T'})‖²/λ)` where `λ‖z‖² ≤ Var_q⟨z,S⟩` for all `z ∈ T'`. How is
`‖Cov_q(ℓ, S|_{T'})‖` best defined without matrices — as `sup_{z ∈ T', ‖z‖=1} |Cov_q(ℓ,⟨z,S⟩)|`, or via
`|Cov_q(ℓ,⟨z,S⟩)| ≤ 2 B ‖z‖ E_q ℓ` directly (your (8)), giving the cleaner scalar statement
`Var_q(a₀ ℓ + ⟨z,S⟩) ≥ a₀² Var_q ℓ − 2|a₀| (2B‖z‖ E_q ℓ) + λ‖z‖² ≥ a₀² (Var_q ℓ − 4B² (E_q ℓ)²/λ)`, then
`(E_q ℓ)² ≤ ε E_q ℓ² ≤ (ε/p) Var_q ℓ` (your (9)) so `Var_q(a₀ ℓ + ⟨z,S⟩) ≥ a₀² Var_q ℓ (1 − 4B² ε/(λ p))`? Please confirm the
constants and give the exact chain. For the eventual tangential lower bound `λ‖z‖² ≤ Var_q ⟨z,S⟩`: from
`Var_q⟨z,S⟩ ≥ p Var_{q(·|A)}⟨z,S⟩` and `q(·|A) = Pfam_A v_n → Pfam_A v_M` (bounded tilts, our Lemma C!), so
`Var_{Pfam_A v_n}⟨z,S⟩ ≥ e^{−2c} Var_{Pfam_A v_M}⟨z,S⟩ ≥ e^{−2c} λ_M ‖z‖²` for `n` large, where `λ_M > 0` is the minimum of the
continuous positive function `z ↦ Var_{Pfam_A v_M}⟨z,S⟩` on the unit sphere of `T'` (positive because `T'` is the direction space
of the face family: `priorCov_dirLoss_self_pos`). Correct?
Assembly: with `η_s = v_s − r_s u` a `C¹` path in `W`, `|η'_s|²_F = Var_{q_s}⟨η'_s, S⟩ = Var_{q_s}(−r'_s⟨u,S⟩ + ⟨v'_s,S⟩)
= Var_{q_s}(r'_s ℓ + ⟨v'_s, S⟩)` (constants drop) `≥ (r'_s)² Var_{q_s} ℓ /2` eventually (Lemma D) `≥ (r'_s)² e^{−2c} Var_{Pfam(v_M − r_s u)} ℓ /2`
(Lemma C with the tilt `⟨v_s − v_M, S⟩`, bounded by `c` eventually) `= (r'_s)² e^{−2c} raySpeedSq(v_M, u, r_s)/2`; then Lemma E with
`g(r) = √raySpeedSq(v_M,u,r)` (continuous in `r`? we have `raySpeedSq` differentiable in `t` I think) gives `IntegrableOn g (Ioi r₀)`,
and `lintegral_sqrt_raySpeedSq_lt_top_iff` converts. Converse: the ray `v_M − r u` is a path with `meanMap → M`
(`exists_ray_tendsto_responseProjection_of_mem_polytope` or the face-conditioning limit), reparametrise `r = s/(1−s)`.

## Questions
1. Is the route above correct and complete? Point out every gap, wrong constant, or missing hypothesis, and give the exact
   statement of `FacetFisherAccess` you would formalise first (both directions, with the path class `C¹ on [0,1)` in `W`).
2. Lemma B's formal shape: is `T' = W ∩ (ℝu)^⊥` the right facet condition (and is `u ∈ W` needed)? How do we get `M ∈ ri` of the
   face moment body from `M ∈ ri F` — is that automatic from `minimalFacePoly V M = F` + a.e. support in `conv V`?
3. Lemma D: confirm the scalar chain and constants; is `E_q ℓ² ≤ Var_q ℓ / p` right (`Var_q ℓ = E ℓ² − (Eℓ)² ≥ E ℓ² − ε E ℓ² = p E ℓ²`)?
4. Anything else fundamental and reachable now (after rank 2 is done), e.g. the data-ray strengthening (§2.3: on a facet the
   data path's response has finite length iff the ray does) — what is its cleanest Lean statement given `DataDissipation`?
