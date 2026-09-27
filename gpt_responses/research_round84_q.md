# Round 84: after the response compactification — what is deepest next for "mapping responses across the data manifold"?

## Landed since round 83 (all sorry-free; `Laplace/Multi/*`, timaeus-research/laplace)

Your round-83 list, with what each became:

1. `BoundedTiltFisherComparison` + `BoundedTiltCompletionAction` (your rank 1): `Var_{P.tilted g} f ≤ e^{hi−lo} Var_P f`;
   `d_F(x+h, y+h) ≤ e^K d_F(x,y)` for `|⟨h,S⟩| ≤ K`; `tiltExt h : Ŵ → Ŵ` (Completion.map, additive, inverse `−h`);
   `Q_{tiltExt h x} = Q_x.tilted(−⟨h,S⟩)` (by continuity of `x ↦ ∫ f dQ_x` for bounded `f`);
   `Q_x = P^A_{v₀} ⇒ Q_{tiltExt h x} = P^A_{v₀+h}` — one accessible face law carries the open face family.
2. `FacetFamilyAccessible`: finite normal ray ⇒ every point of `ri(momentBody ν_A)` is an extended mean.
3. `ResponseLocalMetricControl` (rank 8): coercivity `λ⟨w,w⟩ ≤ Var_{P_θ(M)}⟨w,S⟩` on a convex `U ⊆ ri` ⇒
   `d_F(θ(M₀), θ(M₁)) ≤ ‖M₁−M₀‖₂/√λ` (clamped-smoothstep pull-back of the mean segment).
4. `SamplingResolution` + `ResponseSamplingResolution` (from the user's mid-session "resolution" story: two shifts of
   the structural coordinate, from varying the truth and from sampling): `E[⟨w, M̂_n − m⟩²] = Var_D⟨w,S⟩/n`;
   `⟨w,b_t⟩ = Cov_{ρ_t}(⟨w,S⟩,h) = −Cov_{P_θ}(⟨w,S⟩,⟨θ',S⟩)`; data floor `⟨w,b_t⟩² ≤ n·noise·Var_{ρ_t}h`, response floor
   `⟨w,b_t⟩² ≤ Var_{P_θ}⟨w,S⟩·|θ'_t|²_F` (no matching), so at a matched law a resolvable truth shift has
   `δ² n |θ'_t|²_F ≥ 1`, equality along `w = θ'_t`.
5. `CompletionLawEqProjection` (your Q4 item 5): `P_θ = Π(m(θ))`; `Q_x = Π(meanExt x)` for EVERY completion point (the
   seabed already had `L¹` continuity of `M ↦ Π(M)` on the closed polytope, `tendsto_projL1_of_tendsto`, and lsc of the
   rate); `D(Q_x‖ν) = 𝓘(meanExt x)`; `Q_x` is the KL-minimiser at its mean.
6. `ResponseCompactification` (your rank 7, in `L¹` form): `M ↦ projL1 Π(M)` is a closed embedding of the closed
   polytope into `L¹(ν)` (continuous + injective + compact), continuous inverse.
7. `DataManifoldResponseLaw`: along `ρ_t ∝ e^{th}ν`, `Q_{[θ_t]} = Π(E_{ρ_t}S)`, starts at `ν`, continuous in `t`, and
   `→ Π(E[S | h=H])` in `L¹` as `t → ∞`, no accessibility.

Not done: `TiltedFisherCompactConvergence` (rank 2), the nonexpansion `d̂(j_A v, j_A w) ≤ d_A(v,w)` (rank 3/4),
`FaceChainAccessibility` (5), `PolyhedralEntropyRecovery` (6; not needed for the L¹ continuity), the length budget
(9–10; its bookkeeping exists inside `DataRayReverse` as `hwin` but is not a standalone theorem), Hellinger form of the
compactification (trivial from L¹ via `(√a−√b)² ≤ |a−b|`).

The standing direction: "map the space of responses across the data manifold, from the featureless distribution to
the data distribution, with maximum beauty and depth", plus the user's resolution story (sampling variance of the
structural coordinate vs. the size of walls and chambers; if the variance exceeds the chamber size one cannot
distinguish really different data distributions).

## Questions

### Q1. The resolution story, deepened
We have the direction-wise floors. What is the *right* global statement? Candidates:
(a) Le Cam form: `H²(P_θ^{⊗n}, P_{θ'}^{⊗n}) = 2 − 2(1 − H²(P_θ,P_{θ'})/2)^n` and `H(P_θ,P_{θ'}) ≤ ½ d_F` (landed
    `hellingerDist_le_half_fisherDist`), so two responses at intrinsic distance `d_F ≤ c/√n` are indistinguishable from
    `n` samples (testing affinity bound). Is the matching lower bound (`d_F ≥ C/√n` ⇒ distinguishable) available with
    the seabed's tools (local coercivity → `H ≥ c·d_F` locally)? What is the cleanest two-sided statement?
(b) The Fisher-normalised noise `E[(M̂−m)ᵀ C_θ⁻¹ (M̂−m)] = tr(C_θ⁻¹ C_ρ)/n` (= `dim W/n` at matched laws). We avoided
    it for lack of a Fisher-orthonormal basis of `W`; is there a basis-free proof (e.g. via the chart-derivative
    equivalence and a trace identity `tr(A) = Σ_i ⟨e_i, A e_i⟩` on `J → ℝ` with `A = R ∘ proj`)?
(c) "Chamber size": in the seabed the walls are the faces of the moment polytope in the structural coordinate and the
    chambers their complements; the response Fisher diameter of a chamber… what is the precise object whose comparison
    with `√(d/n)` captures the user's "we can't tell really different data distributions apart"? Is it the Fisher
    distance between the responses of two data laws (`d_F(Φ(ρ), Φ(ρ'))`, controlled above by
    `ResponseLocalMetricControl` and below by coercivity) or something about the germ/geometry classes (the note's
    main theorem transports the germ through the chart)?

### Q2. Multi-parameter data manifolds
Everything is along one-parameter paths `ρ_t ∝ e^{th}ν`. For a `k`-parameter family `ρ_g ∝ e^{g}ν`, `g ∈ span(h₁..h_k)`,
the response map `Φ : g ↦ θ(m(ρ_g))` is smooth on the interior with differential `DΦ_g[k] = −C_{Φ(g)}⁻¹ Cov_{ρ_g}(S,k)`
and pull-back form `G^{resp}_g(k,k) = bᵀC⁻¹b`. What is the deepest *statement* to land: (i) the pull-back metric as a
(possibly degenerate) Riemannian metric on the data manifold with its null directions = invisible directions,
(ii) the comparison `G^{resp} ≤ κ · G^{data}` with `κ` the relative covariance bound (your "relative-covariance
criterion"), (iii) the volume/Jacobian of the response map (how much of the response space a region of the data
manifold covers), (iv) the response geodesics vs data geodesics? Please give precise statements in seabed terms.

### Q3. Existence side: what remains and in which order
With `Q_x = Π(meanExt x)` and the compactification, accessibility is now a statement purely about `meanExt(Ŵ) ⊆ K`:
which points of the closed polytope are extended means. Known: interior (all), facets (iff normal ray finite; then the
whole open facet), vertices/faces (uniqueness). Missing: existence over faces of codimension ≥ 2 (face chains), and
whether `meanExt(Ŵ)` is a union of open faces (your "union of accessible open-face strata") — is the latter now cheap
from the tilt action (one accessible point of `ri F` ⇒ all of `ri F` for EVERY face `F`, via the face family law of
`Q_x` from `completionLaw_face_eq_one` + Pythagoras)? Please give the statement and route.

### Q4. Ranked list
Rank 8–10 modules (≤300 lines each) with statements in seabed terms and proof routes; mark deep vs infrastructure.

### Q5. Corrections
Anything in 1–7 that is weaker than it should be or misnamed? In particular the resolution floors: are the hypotheses
`hnoise : 0 < E[⟨w,Δ̂⟩²]` and `hdetect : E[⟨w,Δ̂⟩²] ≤ (⟨w,b_t⟩ δ)²` the right formalisation of "resolvable"?
