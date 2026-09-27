# Research round 81 — the completed response space: what next after the Hellinger layer

Context: germbij response-map programme inside the laplace seabed (Lean 4.33, Mathlib current). The user's standing
direction: "map the space of responses across the data manifold, from the featureless distribution of maximal entropy
to the actual data distribution; maximum beauty and depth". Your round-80 landing order has been executed in full
(modules 1–13), sorry-free:

* `FisherSpeedForm` (`fisherVar`, `fisherNorm`: joint continuity, homogeneity, `≤ card J·B·‖w‖`, coercive on `W`);
* `FlatC1Paths` (smoothstep flattening, double-speed pasting with `HasDerivWithinAt.union`);
* `FisherPathLength` (`FisherPath S ν x y`, `length`, `flat`/`rev`/`cat`/`segment`, `length_flat/rev/cat`, segment bound);
* `FisherMeanControl` (`‖m(γ_b) − m(γ_a)‖ ≤ B ∫_a^b F`);
* `FisherDistance` (`fisherDist` is a metric on `W`; `‖m y − m x‖ ≤ B d_F`; `d_F ≤ K‖y − x‖`);
* `FisherTopology` (`FisherPoint hS ν` wrapper with `MetricSpace`; `FisherPoint.homeomorphW`; `FisherCompletion :=
  UniformSpace.Completion (FisherPoint hS ν)`; Lipschitz `meanExt`; `exists_meanExt_eq_iff` via Cauchy sequences);
* `FisherCauchyRealisation` (countable concatenation on `[n,n+1]`, constant for `t ≤ 0`, globally `C¹`; length ≤ Σ;
  means converge; `fisherDist_le_integral`; Cauchy ⇒ subsequence with `d_F ≤ 2^{−n}`);
* `FacetCompletionAccess`: **`exists_meanExt_eq_iff_ray`** (`∃ x ∈ Ŵ_F, m̄ x = M ⇔ ∫_0^∞ √raySpeedSq(0,u,r) dr < ∞` for
  `M ∈ ri F`, facet) and `exists_meanExt_eq_iff_responseLength` (data-path form);
* `FacetCompletionUnique`: **`meanExt_eq_facet_unique`** (the fibre over `M ∈ ri F` is a single point);
* `SqrtDensityAffinity` (`rootDens`, affinity identity `∫ q_θ q_η = Z((θ+η)/2)/√(Z θ Z η)`, `∫ q_θ²(ℓ − Eℓ)² = fisherVar`,
  Cauchy–Schwarz for bounded integrands);
* `HellingerFisherControl` (chord derivative via the affinity + quotient rule; `H(a,b) ≤ ½ L(γ)` by monotonicity of
  `B − A`; **`hellingerDist_le_half_fisherDist`**);
* `FisherCompletionLaws` (`rootDensLp`, `dist = hellingerDist`, ½-Lipschitz, `rootDensExt` on the completion,
  `norm = 1`, `0 ≤ rootDensExt x` in `Lp`, **`meanExt x i = ∫ S_i (rootDensExt x)²`**).

Also on the seabed from before: the facet accessibility iff for paths (`facet_fisher_access_iff`), the data-ray
equivalence (`data_fisher_length_lt_top_iff_ray`), the dyadic shell classification (`Σ_k √a_k`), the vertex-gap
criterion for mean convergence (any filter), `tendsto_faceTheta_normalDepth_of_tendsto_meanMap` (facet asymptotics
for arbitrary sequences), `RayTiltInvariance`, `TiltVarianceComparison`, the 1-D atomic example with
`Σ√a_k = ∞`, `ThreePointNotContracting`, `ResponseDefectPythagoras`, `ResponseBregman`, `FisherPathBounds`
(`⟨u,v⟩² ≤ Var⟨u,S⟩·⟨v,C⁻¹v⟩`), `FaceMassConcentration`, `FaceCoercivity`, `FacetSchurBound`.

Notation: `Pfam θ = ν.tilted(−⟨θ,S⟩)`, `S` bounded, `W = dirSpan ν 1 S`, `T' = dirSpan (ν|_F) 1 S`, facet hypothesis
`hT : ∀ w ∈ W, ⟨w,u⟩ = 0 → w ∈ T'`, `momentBody ν 1 S = convexHull V` with every vertex charged.

## Questions

**Q1 (face-conditioned Hellinger limit).** Over an accessible facet mean `M ∈ ri F` with fibre point `x_M`, we expect
`rootDensExt x_M = √(1_F e^{−⟨v_M,S⟩}/Z_F(v_M))` in `L²(ν)` (`Z_F` the partition function of `ν|_F`). Lean route: the ray
`θ_r = v_M − r u` is Fisher–Cauchy (tails of a finite length), so `x_M = lim coe(θ_n)`, and `rootDensExt x_M =
lim rootDensLp(θ_n)` in `L²`; identify the limit by dominated convergence of `q_{θ_r}(x) = e^{−⟨v_M,S(x)⟩/2 + r⟨u,S(x)⟩/2}
/√Z(θ_r)`: on `F = {⟨u,S⟩ = β}` … wait, our convention is `Pfam θ ∝ e^{−⟨θ,S⟩}` and the ray `θ − r u` concentrates on the
MAX face `{⟨u,S⟩ = β}` (`β = max`), so `e^{r(⟨u,S⟩ − β)} → 1_F` pointwise and `e^{rβ} Z(θ_r) → ∫_F e^{−⟨v_M,S⟩} dν`. Which
Mathlib tool is cheapest for the `L²` limit: `tendsto_integral_of_dominated_convergence` on `∫ (q_r − q_∞)²` (dominated
by `4·(bounded)`), or `MeasureTheory.tendsto_Lp_of_tendsto_ae`-type (`tendstoInMeasure`/`Lp` convergence from a.e.
convergence + uniform bound: `tendsto_Lp_finite_of_tendsto_ae`?) — please name the lemma and its hypotheses. Is the
face-conditioned law the right *statement*, or should we rather state: `rootDensExt x_M ^2 · ν = (ν|_F).tilted(−⟨v_M,S⟩)`
(a `Measure` equality) so that the boundary point is literally the face exponential family member?

**Q2 (injectivity of the law map).** Is `rootDensExt : Ŵ_F → L²(ν)` injective (equivalently: is the completion's
topology the Hellinger topology on the image)? We have `H ≤ ½ d_F` only. On the interior `Ψ` is injective (means
separate points). For two Cauchy sequences with the same Hellinger limit, can `d_F(θ_n, θ'_n) ↛ 0`? Give a
counterexample or a proof sketch. If it fails in general, does it hold when all boundary points are over facets
(codimension one only)? This decides whether the completion is "the space of laws" or strictly finer.

**Q3 (the charged square / codimension ≥ 2).** Your round-80 remark: the right question is *small intrinsic diameter
of deep normal regions*. For a vertex `M` of the square `[0,1]²` charged with layers, please give the precise
statement you would formalise first: (a) an explicit countable atomic `ν` on the square where the fibre `m̄⁻¹(M)` has
two points (two normal rays with different `√`-shell tails that are both finite but not connected by short paths), or
(b) an explicit `ν` where two rays into `M` are Fisher-close so the fibre is a point; and the general theorem for a
vertex of a polygon in terms of the *two-parameter* layer masses `m_{j,k} = ν{2^{−j−1} < ℓ₁ ≤ 2^{−j}, 2^{−k−1} < ℓ₂ ≤ 2^{−k}}`
(`ℓ₁, ℓ₂` the two slacks). What is the criterion for the fibre to be nonempty, and for it to be a single point?

**Q4 (the boundary as a whole).** With the facet results in hand: is `range meanExt = ri P ∪ ⋃_{accessible facets F}
ri F ∪ (higher-codimension part)`? Can we prove now that `meanExt x ∈ closure (ri P)` (done) and that a boundary
extended mean always lies on a face charged by `ν` in the strong sense `ν(F) > 0` (you claimed this follows from the
law: `Ψ̄(x)² ν` has mean `m̄(x)` on the boundary of `P` ⇒ its support lies in the face)? Give the Lean route (the mean of
a law `q²ν` lying on a supporting hyperplane forces `q² = 0` off the face a.e.).

**Q5 (the data manifold).** The user's phrase "map the space of responses across the data manifold": we have the
response coordinates `θ_t` of the data path `ρ_t = ν.tilted(t h)` and the equivalence (finite response length ⇔
facet ray finite) when the top-set conditional mean lies in `ri F`. Is there a natural theorem of the form: the map
`t ↦ [θ_t] ∈ Ŵ_F` extends continuously to `t = ∞` iff the response length is finite, with limit the facet fibre point,
and the extended law is `Ψ̄(x_M)² ν = (ν|_F).tilted(−⟨v_M,S⟩)` = the maximum-entropy law on the face with mean `M`,
i.e. **the response map of the data limit `ν(·|h = H)` is the I-projection of the featureless law onto the face with
the data's conditional mean**? Please state precisely what is provable now and what is missing.

**Q6 (ranking).** Rank the next ≤ 300-line modules by depth given all of the above, with one-line statements. Options
we see: (i) face-conditioned limit (Q1), (ii) boundary means lie on charged faces (Q4), (iii) `t ↦ [θ_t]` extends to
`t = ∞` (Q5), (iv) charged-square fibre theorem (Q3), (v) injectivity or its failure (Q2), (vi) a `Measure`-level
statement `completionLaw x := (rootDensExt x)² • ν` with `IsProbabilityMeasure` and `∫ S = meanExt x`, (vii) flags.
