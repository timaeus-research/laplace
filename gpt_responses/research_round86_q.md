# Round 86: the response atlas after the covariance-quotient, length-budget and nonexpansion theorems — what is deepest next?

## Landed since round 85 (all sorry-free; `Laplace/Multi/*`, timaeus-research/laplace, main)

Your round-85 ranking, with what each became:

1. `ResponseHorizontalLift` (rank 1). For any bounded tilt `ρ_g` the data covariance operator `C_{ρ_g}` on `W`
   (`dataCovOp`, `⟨w, C_D w⟩ = Var_{ρ_g}⟨w,S⟩`) is positive definite (`lawCov_dirLoss_tilted_pos`, from the reverse
   tilt and `Var_{P.tilted g} ≤ e^{osc} Var_P`), so `hor_g(v) := ⟨C_{ρ_g}⁻¹ Dm(Φ(g)) v, S⟩` is defined for all `v ∈ W`
   (`horizontalLift`; `Dm = −C` so this is your `−⟨C_D⁻¹Cv, S⟩` up to a constant); `DΦ_g[hor_g v] = v`
   (`responseVel_horizontalLift`), `DΦ_g` onto `W` (`exists_responseVel_eq`), `G^{resp}_g(hor_g v) = |v|²_F`,
   `Var_{ρ_g} hor_g(v) = ⟨C_D⁻¹ Dm v, Dm v⟩`, VARIANCE-MINIMISING among contrasts with velocity `v`
   (`lawCov_self_ge_horizontalLift`); matched: `hor_g(v) = −⟨v,S⟩`, `Var = |v|²_F` (`lawCov_horizontalLift_self_of_matched`).
2. `ResponseBilinearForm` (rank 2): `G_g(k,ℓ) := −⟨DΦ_g[k], b_g(ℓ)⟩ = Cov_{P_Φ}(⟨DΦ[k],S⟩,⟨DΦ[ℓ],S⟩)`, symmetric, bilinear
   (`DΦ_g` linear), Cauchy–Schwarz, and at matched laws `Cov_D(k,ℓ) = G_g(k,ℓ) + Cov_D(k − k_vis, ℓ − ℓ_vis)`.
   NOT done: `d_eff ≤ κ dim W` (needs `tr(psd·psd) ≥ 0`).
3. `TiltedFisherCompactConvergence` + `TiltedCovarianceStability` (rank 3): for laws with densities
   `|E_{Q₁}F − E_{Q₂}F| ≤ ‖F‖_∞‖q₁−q₂‖₁`, `|Cov_{Q₁}(f,g) − Cov_{Q₂}(f,g)| ≤ 3‖f‖‖g‖‖q₁−q₂‖₁`,
   `|Var_{Q₁}⟨w,S⟩ − Var_{Q₂}⟨w,S⟩| ≤ 3B²‖w‖²‖q₁−q₂‖₁` (compact-uniform); tilting by common `|h| ≤ K` is `L¹`-Lipschitz
   `2e^{2K}`; measure-level: `(qν).tilted g = (tilt_g q)ν`; `‖p_θ − ρ_x‖₁ ≤ 2‖√p_θ − √ρ_x‖₂ → 0` as `θ → x ∈ Ŵ`; and
   `|Cov_{P_{θ+a}}(f,f') − Cov_{Q_{tiltExt a x}}(f,f')| ≤ 6‖f‖‖f'‖e^{2K}‖p_θ − ρ_x‖₁` for `|⟨a,S⟩| ≤ K`.
4. `ResponsePathLengthBudget` (rank 4, core on `W`-paths): `η : ℝ → W` locally `C¹` with `∫_0^∞ |η'|_F < ∞` ⇒
   `d̂(η(a),η(b)) ≤ ∫_a^b |η'|_F`, Cauchy at infinity, endpoint `x_∞ ∈ Ŵ` (`pathEndpoint`), tail bound
   `d̂(η(t), x_∞) ≤ ∫_t^∞ |η'|_F`, means → `meanExt x_∞`, `Q_{x_∞} = Π(lim m(η(t)))`. NOT done: the bounded-tilt adapter
   (chain rule for `g_t = ∑ a_j(t) h_j`).
5. `ResponseFormContinuity` (rank 5): NOT done (the `L¹` inputs above are ready).
6. `AccessibleFaceNonexpansion` (rank 6): for `x₀` with `Q_{x₀} = P^A_{v₀}`, `v₀ ∈ W_A`, the face embedding
   `j_A(w) := tiltExt (w − v₀) x₀` on the face's own direction space `W_A` has `Q_{j_A w} = P^A_w` and is NONEXPANSIVE
   `d̂(j_A w, j_A w') ≤ d_F^{(A)}(w,w')` (`dist_faceEmbed_le`: approximate `x₀` by `θ_n`, ambient path `θ_n + (γ_t − v₀)`,
   `fisherDist_le_integral`, uniform covariance stability along the action, `n → ∞`, inf over face paths). The
   `1`-Lipschitz extension to `Ŵ_A` and the mean identification `meanExt (ĵ_A y) = meanExt_A y` are being written now.
7. `ResponseIntrinsicResolution` (rank 7): `‖Dm(θ)u‖₂² ≤ Λ|u|²_F` (Fisher CS), `‖z‖₂² ≤ Λ q_θ(z)` on `W`, frozen → intrinsic
   margin `d_F(θ(M),θ(M+z)) ≤ √(Λ/λ)√(q_θ(z))` on coercive patches, and the TWO-CLASS SEPARATION THEOREM
   (`measureReal_both_resolved_ge`): responses at intrinsic distance `≥ √(Λ₀/λ₀)r₀ + √(Λ₁/λ₁)r₁` are resolved by
   `n₀, n₁` samples (empirical responses in the disjoint intrinsic balls) with probability
   `≥ 1 − tr(R₀C_{D₀})/(n₀r₀²) − tr(R₁C_{D₁})/(n₁r₁²)`; union bound, no independence.
8–10. `FaceChainAccessibility`, `ResponseProductAffinity`, `ResponseHellingerAtlas`: NOT done.

Earlier: response-map layer through round 84 (pull-back form, Fisher-normalised sampling trace identity
`E q_θ(M̂−m) = tr(R_θC_D)/n = dim W/n` at matching, local testing sandwich `√λ d_F ≤ 2B H ≤ B d_F`, chamber bound
`P(M̂ ∉ C) ≤ tr(R_θC_D)/(nr²)`, accessible face strata, completion laws `Q_x = Π(meanExt x)`, `L¹` compactification,
data-manifold response law, bounded-tilt action `tiltExt`, uniqueness of fibres over charged face interiors).

The standing direction is unchanged (map the responses across the data manifold from the featureless law to the data
law with maximum beauty and depth; the resolution story).

## Questions

### Q1. The note's main theorems, now
With I (covariance quotient: `ResponsePullbackForm` + `ResponseHorizontalLift` + `ResponseBilinearForm`), II (noise and
chambers: `FisherNormalisedSampling` + `ResponseClassResolution` + `ResponseIntrinsicResolution`), III (local statistical
geometry: `ResponseLocalTesting`), IV (stratified completion: completion laws + `AccessibleFaceStrata` +
`AccessibleFaceNonexpansion`) and the length budget landed, write the statements you would put in the note as the
main theorems of the response-map section, in the exact generality that is landed (hypotheses included), and say
which single statement is the headline. Is the "covariance quotient / Riemannian submersion at matched laws" claim
fully justified by `responseVel_horizontalLift` + `lawCov_horizontalLift_self_of_matched` + the bilinear score
decomposition, or is something missing (e.g. the identification of the vertical space as exactly the kernel, which we
have only as `G(k,k) = 0 ↔ b(k) = 0`)?

### Q2. Face chains and the boundary atlas (`FaceChainAccessibility`)
Given `j_A : W_A → Ŵ` nonexpansive with `Q_{j_A w} = P^A_w`, and its `1`-Lipschitz extension `ĵ_A : Ŵ_A → Ŵ` with
`meanExt ∘ ĵ_A = meanExt_A`: (a) state the compatibility `ĵ_A ∘ ĵ^A_E = ĵ_E` for a face `E ⊆ A` (face of the face) —
what are the objects (`E` as an event of `ν_A`, `ν_E = (ν_A)_E = ν_E`, `W_E ⊆ W_A ⊆ W`), and is the compatibility a
consequence of uniqueness of fibres (`meanExt_eq_face_unique`) plus the mean identification, or does it need a new
argument? (b) The intrinsic accessibility transfer: "if `M ∈ ri(face body of E)` is an extended mean of `Ŵ_A` then it
is an extended mean of `Ŵ`" — is this now immediate from `meanExt ∘ ĵ_A = meanExt_A`? (c) What is the right statement
of "the boundary atlas is coherent"?

### Q3. `ResponseFormContinuity`
With the `L¹` stability lemmas, the tilt `L¹`-Lipschitz bound and `tendsto_projL1_of_tendsto` (continuity of `M ↦ Π(M)`
in `L¹` on the closed polytope), state precisely the continuity theorem for `g ↦ G_g(k,ℓ)`, `g ↦ hor_g(v)`,
`g ↦ d_eff(g)` on interior patches with a uniform fitted-covariance lower bound, and the cheapest Lean route
(is it better to state continuity in the data LAW `D` (`L¹` distance of densities) than in the tilt `g`?).

### Q4. The bounded-tilt adapter for the length budget
Minimal differentiation package for `g_t = ∑_{j<N} a_j(t) h_j` (`h_j` bounded, `a_j ∈ C¹`): the seabed has the
one-parameter `dataTheta`/`dataThetaVel` (`ρ_t ∝ e^{th}ν`, chain rule through the chart). What is the cleanest way to
get `t ↦ Φ(g_t)` locally `C¹` in `W` with velocity `DΦ_{g_t}[ġ_t]` (`responseVel`) — via the inverse function theorem on
the chart (`chartVInv`/`responseTheta` is `C¹` on the interior? the seabed has `hasStrictFDerivAt` for the chart) composed
with `t ↦ E_{ρ_{g_t}} S` differentiable by dominated differentiation? Which existing lemma names would you reuse?

### Q5. Ranked list
Rank the next 8 modules by depth × reachability for the standing direction; include anything you consider missing
for the note's response-map section to be complete (e.g. the `d_eff ≤ κ dim W` inequality via a Fisher-orthonormal
basis, the Hellinger atlas, product affinity).

### Q6. Corrections
Any landed statement above you would restate, sharpen, or consider mis-scoped? In particular (i) the nonexpansion is
for `v₀ ∈ W_A`; is the reduction from general `v₀` (via the invisible directions of `ν_A`) worth stating; (ii) the
two-class theorem uses frozen ellipsoid margins `hell₀/hell₁ ⊆ U_i` as hypotheses — is there a cleaner sufficient
condition in terms of the patch geometry alone?
