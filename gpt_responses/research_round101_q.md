# Research round 101 — germbij response-map programme: programme K landed; what is programme L?

You are GPT-6 Astra, research advisor to a Lean 4 (Mathlib) formalisation of the note *germbij* ("The germ of a bijection": the response map `q ↦ Φ(q) ∈ W` of a bounded feature family `S : J → X → ℝ` over data laws `q ≪ ν`, `W = dirSpan` the direction space of the moment body, `P_θ = ν.tilted(−⟨θ,S⟩)`, mean map `m`, inverse chart `θr`, Fisher form `G`, m-Christoffel `C(u,v) = A⁻¹T(u,v)`, chart derivative `A = CD θ` and its inverse `(CDE θ).symm`, `atomMass θ x = P_θ{x}` on finite `X`, `polytopeJourney mD t = θr(m₀ + t(mD − m₀))`, `responseProjection hS ν M = R_M` the entropy projection (max-entropy law with mean `M`)). Everything below is sorry-free, warning-free Lean in laplace `Laplace/Multi/Response*` (≈72 modules, rounds 84–100).

The user's standing direction: *"make sure we are tackling core features of the change in posterior expectation values with the change in the data distribution that allow us to map the space of responses across the data manifold (ideally all the way from the featureless distribution of maximal entropy to our actual data distribution). What would it take to do this with maximum beauty and depth?"* plus the resolution story (truth shifts vs sampling shifts of the structural coordinate; chambers below the sampling scale are unresolvable). The user wants new mathematics, not packaging.

## What landed since round 100 (your programme K)

* **K1 `ResponseBoundaryJourney`** — finite charged `X`, ANY data law `D`: the polytope journey `θ_t = θr(m₀ + t(m_D − m₀))` exists for `t < 1`, its laws converge to the entropy projection `R_D` as `t ↑ 1` (atom masses and KL), and the exact budget `KL(D‖ν) = KL(D‖R_D) + KL(R_D‖ν)`: "the chart may end but the journey does not".
* **K2a `IIDFourthMoment`, K2b `ResponseIIDSamplingBias`** — `E‖ξ̄_n‖³ = O(n^{-3/2})` from fourth moments under `iIndepFun`, and the i.i.d. localised bias: `E[θ̂_loc − θ₀] = −(1/2n)·covContraction + O(n^{-3/2})`, `covContraction = ∑_{ab} Cov_D(S_a,S_b) C(A⁻¹pe_a, A⁻¹pe_b)`.
* **K3 `ResponseFiniteFibres`** — the response atlas is a literal quotient: barycentre `Δ → conv S(X)` is a quotient map with the entropy projection as continuous section; `dim F₀ + dim W = |X| − 1`; the fibre over an interior mean is an affine slice of dimension `|X| − 1 − dim W`.
* **K4 `ResponseJourneyInformationCost`** — the boundary information budget: for `T < 1`, `KL(P_{θ_T}‖ν) = ∫₀^T (T − t) g(t) dt` with `g(t) = G_{θ_t}(θ̇_t,θ̇_t)`; the truncated budgets `∫₀^T(1−t)g` are squeezed between `KL(P_{θ_T}‖ν)` and `KL(R_D‖ν)`; `(1−t)g` is Lebesgue integrable on `(0,1]` and **`KL(D‖ν) = KL(D‖R_D) + ∫₀¹ (1−t) G_{θ_t}(θ̇_t,θ̇_t) dt`** for every data law (no interior-mean hypothesis).
* **K5 `ResponseObservableSamplingGeometry`** — the Fisher form is a nondegenerate bilinear form on `W`, so every functional has a Fisher–Riesz representative; the **regression direction** `u_F ∈ W` represents `v ↦ Cov_θ(F,⟨v,S⟩)`; the residual `F − ⟨u_F,S⟩` is uncorrelated with all features, Pythagoras `Var(F − ⟨u_F,S⟩) = Var F − G(u_F,u_F)`; **influence** `d/dt E_{θ(m₀+te)}F|₀ = ⟨u_F,e⟩`; exact sampling covariance `E[⟨u,ξ_n⟩⟨w,ξ_n⟩] = Cov_D(⟨u,S⟩,⟨w,S⟩)/n` for any law; at a matched law the sampling covariance matrix of linearised posterior expectations is the Fisher Gram matrix `G(u_F,u_{F'})/n ≤ Var F/n` on the diagonal; **observable resolution floor**: if `F` resolves the shift `e` above its own noise then `n|A⁻¹e|²_F ≥ 1`.
* **K6 `ResponseSimplexCompletion`** — `SphSimplex X` = closed simplex with `dist = 2∠(√p,√q) = 2 arccos ∑√(pq)`, a compact metric space of diameter `π` (attained at distinct Diracs), positive part dense; **`fisherCompletionIso : FisherCompletion ≃ᵢ SphSimplex X`** for saturated finite families; hence the Fisher completion is compact.
* **K7 `ResponseExtrinsicGauss`** — NOT done as a new module because the intrinsic Gauss equation you asked for ALREADY EXISTED since round 96: `fisherSectional_eq_quarter_add_residual` (`K = ¼ + (E[r_uu r_vv] − E[r_uv²])/(4D)`, `r_uv` the score residual = `(I − Π)(h_u h_v)` in your notation). Only the *extrinsic* reading (the `2√P_θ` embedding into the radius-2 sphere of `L²(ν)`, second fundamental form `½√P r_uv`) is missing. Is it worth a module, or is the intrinsic identity the whole content?

## Key statements (verbatim Lean; `…` elides proofs)

```lean
-- Laplace/Multi/ResponseBoundaryJourney.lean
/-- **The information acquired along the boundary journey converges** to the relative entropy of
the entropy response. -/
theorem tendsto_klDiv_polytopeJourney :
    Tendsto (fun t : ℝ ↦ (klDiv (Pfam (polytopeJourney hS ν mD t : J → ℝ)) ν).toReal) (𝓝[<] 1)
      (𝓝 (klDiv (responseProjection hS ν mD) ν).toReal) := by …

-- Laplace/Multi/ResponseBoundaryJourney.lean
/-- **The exact information budget of a data law**: `KL(D‖ν) = KL(D‖R_D) + KL(R_D‖ν)` — the
information invisible to the features plus the information acquired by the response. -/
theorem toReal_klDiv_data_eq_defect_add_response :
    (klDiv D ν).toReal =
      (klDiv D (responseProjection hS ν mD)).toReal +
        (klDiv (responseProjection hS ν mD) ν).toReal := by …

-- Laplace/Multi/ResponseBoundaryJourney.lean
/-- **THE BOUNDARY JOURNEY THEOREM**: for a finite space with charged atoms and any data law `D`,
the response journey `θ_t = m⁻¹(m_ν + t(m_D − m_ν))` is defined on `[0,1)` with the prescribed
means, its laws converge to the entropy response `R_D` as `t ↑ 1`, every posterior expectation
converges to its `R_D`-value, and the information budget is exact:
`KL(D‖ν) = KL(D‖R_D) + KL(R_D‖ν)`. The chart may end, but the response journey does not. -/
theorem boundary_journey :
    (∀ t : ℝ, 0 ≤ t → t < 1 → mean (polytopeJourney hS ν mD t : J → ℝ) = m₀ + t • (mD - m₀)) ∧
    Tendsto (fun t : ℝ ↦ atomMass S ν (polytopeJourney hS ν mD t : J → ℝ)) (𝓝[<] 1)
      (𝓝 (qStarVec hS ν mD)) ∧
    (∀ F : X → ℝ, Tendsto (fun t : ℝ ↦ ∫ x, F x ∂Pfam (polytopeJourney hS ν mD t : J → ℝ))
      (𝓝[<] 1) (𝓝 (∫ x, F x ∂responseProjection hS ν mD))) ∧
    (klDiv D ν).toReal =
      (klDiv D (responseProjection hS ν mD)).toReal +
        (klDiv (responseProjection hS ν mD) ν).toReal :=

-- Laplace/Multi/ResponseIIDSamplingBias.lean
/-- **The m-connection contracted with the data covariance**:
`∑_{a,b} Cov_D(S_a,S_b) C_{θ₀}(A⁻¹ p e_a, A⁻¹ p e_b)`. -/
noncomputable def covContraction (p : (J → ℝ) →ₗ[ℝ] 𝕍) (θ₀ : 𝕍) : 𝕍 :=

-- Laplace/Multi/ResponseIIDSamplingBias.lean
/-- **THE i.i.d. SAMPLING BIAS OF THE LOCALISED RESPONSE**: for the reset-localised response of
`n` i.i.d. samples,
`‖ E[θ̂_loc − θ₀] + (1/(2n)) ∑_{a,b} Cov_D(S_a,S_b) C(A⁻¹p e_a, A⁻¹p e_b) ‖
  ≤ (‖A⁻¹‖/δ² + K + ½‖A⁻¹‖‖T‖‖A⁻¹‖²/δ) · √3 |J|³ (2B)³ / n^{3/2}`. -/
theorem iid_localizedBias_curvature (p : (J → ℝ) →ₗ[ℝ] 𝕍) (hp : ∀ w : 𝕍, p (w : J → ℝ) = w)
    (θ₀ : 𝕍) {K : ℝ} (hδ : 0 < δ) (hK : 0 ≤ K)
    (hdom : ∀ z : 𝕍, ‖z‖ ≤ δ → mean (θ₀ : J → ℝ) + (z : J → ℝ) ∈ Ωm)
    (hrem : ∀ z : 𝕍, ‖z‖ ≤ δ →
      ‖θr (mean (θ₀ : J → ℝ) + (z : J → ℝ)) - θ₀ - (CDE θ₀).symm z +
        (1 / 2 : ℝ) • curvatureForm hS ν θ₀ z‖ ≤ K * ‖z‖ ^ 3) :
    ‖(∫ z in cball, (θr (mean (θ₀ : J → ℝ) + (z : J → ℝ)) - θ₀)
          ∂(P.map fun ω ↦ p ((raw n) ω))) +
        (1 / 2 : ℝ) • ((1 / n : ℝ) • covContraction hS ν D p θ₀)‖ ≤
      (‖((CDE θ₀).symm : 𝕍 →L[ℝ] 𝕍)‖ / δ ^ 2 + K +
        (1 / 2 : ℝ) * (‖((CDE θ₀).symm : 𝕍 →L[ℝ] 𝕍)‖ * ‖thirdOp hS ν θ₀‖ *
          ‖((CDE θ₀).symm : 𝕍 →L[ℝ] 𝕍)‖ ^ 2) / δ) *
        (Real.sqrt 3 * Fintype.card J ^ 3 * (2 * B) ^ 3 / (n * Real.sqrt n)) := by …

-- Laplace/Multi/ResponseFiniteFibres.lean
/-- **The response atlas is a quotient**: the barycentre map is a quotient map of the simplex
onto the moment polytope, with the entropy projection as a continuous section. -/
theorem isQuotientMap_momentMapSimplex :
    Topology.IsQuotientMap (momentMapSimplex S) :=

-- Laplace/Multi/ResponseFiniteFibres.lean
/-- **What the response forgets**: `dim F₀ + dim W = |X| − 1`. -/
theorem finrank_fibreDirection_add :
    Module.finrank ℝ (fibreDirection S) + Module.finrank ℝ 𝕍 = Fintype.card X - 1 := by …

-- Laplace/Multi/ResponseFiniteFibres.lean
/-- **What the response forgets, at every interior mean**: the fibre over `M` is an affine slice of
the simplex of dimension `|X| − 1 − dim W`. -/
theorem finrank_direction_affineSpan_fibre {M : J → ℝ} (hM : M ∈ intrinsicInterior ℝ hull) :
    Module.finrank ℝ (affineSpan ℝ (fibre S M)).direction + Module.finrank ℝ 𝕍 =
      Fintype.card X - 1 := by …

-- Laplace/Multi/ResponseJourneyInformationCost.lean
/-- The velocity of the journey towards the data law, `θ̇_t = (Dm(θ_t)|_W)⁻¹ (m_D − m_ν)`. -/
noncomputable def journeyVelD (t : ℝ) : 𝕍 :=
  (CDE (polytopeJourney hS ν mD t)).symm ⟨mD - m₀, dataMean_sub_featureless_mem hS ν hν D⟩

-- Laplace/Multi/ResponseJourneyInformationCost.lean
/-- The Fisher energy `G_{θ_t}(θ̇_t, θ̇_t)` along the journey towards the data law. -/
noncomputable def journeyEnergy (t : ℝ) : ℝ :=
  fisherVar S ν (polytopeJourney hS ν mD t : J → ℝ) (journeyVelD hS ν hν D t : J → ℝ)

-- Laplace/Multi/ResponseJourneyInformationCost.lean
/-- **The interior information budget of the journey towards the data law**: for `T < 1`,
`KL(P_{θ_T}‖ν) = ∫₀^T (T − t) G_{θ_t}(θ̇_t, θ̇_t) dt`. -/
theorem toReal_klDiv_polytopeJourney_eq_action {T : ℝ} (hT0 : 0 ≤ T) (hT1 : T < 1) :
    (klDiv (Pfam (polytopeJourney hS ν mD T : J → ℝ)) ν).toReal =
      ∫ t in (0 : ℝ)..T, (T - t) * journeyEnergy hS ν hν D t := by …

-- Laplace/Multi/ResponseJourneyInformationCost.lean
/-- **The truncated budgets converge to the boundary information.** -/
theorem tendsto_journeyAction [MeasurableSingletonClass X] :
    Tendsto (journeyAction hS ν hν D) (𝓝[<] 1)
      (𝓝 (klDiv (responseProjection hS ν mD) ν).toReal) := by …

-- Laplace/Multi/ResponseJourneyInformationCost.lean
/-- **The weighted Fisher energy is Lebesgue integrable on `(0, 1]`.** -/
theorem integrableOn_journeyEnergy [MeasurableSingletonClass X] :
    IntegrableOn (fun t ↦ (1 - t) * journeyEnergy hS ν hν D t) (Ioc (0 : ℝ) 1) := by …

-- Laplace/Multi/ResponseJourneyInformationCost.lean
/-- **THE BOUNDARY INFORMATION BUDGET**: `KL(R_D‖ν) = ∫₀¹ (1 − t) G_{θ_t}(θ̇_t, θ̇_t) dt`, for
every data law. -/
theorem integral_journeyEnergy [MeasurableSingletonClass X] :
    ∫ t in Ioc (0 : ℝ) 1, (1 - t) * journeyEnergy hS ν hν D t =
      (klDiv (responseProjection hS ν mD) ν).toReal := by …

-- Laplace/Multi/ResponseJourneyInformationCost.lean
/-- **THE INFORMATION BUDGET OF THE JOURNEY TO ANY DATA LAW**:
`KL(D‖ν) = KL(D‖R_D) + ∫₀¹ (1 − t) G_{θ_t}(θ̇_t, θ̇_t) dt` — the information invisible to the
features plus the Fisher action of the journey from the featureless law to the entropy response of
the data. -/
theorem journey_information_budget [MeasurableSingletonClass X] :
    (klDiv D ν).toReal = (klDiv D (responseProjection hS ν mD)).toReal +
      ∫ t in Ioc (0 : ℝ) 1, (1 - t) * journeyEnergy hS ν hν D t := by …

-- Laplace/Multi/ResponseObservableSamplingGeometry.lean
/-- **The regression direction** `u_F ∈ W`: the Fisher–Riesz representative of the covariance
functional, `G_θ(u_F, v) = Cov_{P_θ}(F, ⟨v, S⟩)` for every `v ∈ W`. -/
noncomputable def regressionDir (F : X → ℝ) (θ : 𝕍) : 𝕍 :=
  fisherRiesz hS ν θ (covFunctional ν F θ)   -- fisherRiesz = (fisherBilin.toDual _).symm, covFunctional v = ∑_j Cov(F,S_j) v_j

-- Laplace/Multi/ResponseObservableSamplingGeometry.lean
/-- The defining property of the regression direction. -/
theorem fisherInner_regressionDir {F : X → ℝ} (hF : Bdd F) (θ v : 𝕍) :
    G θ (regressionDir hS ν F θ) v = lawCov (Pfam (θ : J → ℝ)) F (dirLoss S (v : J → ℝ)) := by …

-- Laplace/Multi/ResponseObservableSamplingGeometry.lean
/-- **Pythagoras for the regression**: `Var(F − ⟨u_F,S⟩) = Var F − G_θ(u_F, u_F)`. -/
theorem lawCov_regressionResidual_self {F : X → ℝ} (hF : Bdd F) (θ : 𝕍) :
    lawCov (Pfam (θ : J → ℝ)) (fun x ↦ F x - dirLoss S (regressionDir hS ν F θ : J → ℝ) x)
        (fun x ↦ F x - dirLoss S (regressionDir hS ν F θ : J → ℝ) x) =
      lawCov (Pfam (θ : J → ℝ)) F F -
        G θ (regressionDir hS ν F θ) (regressionDir hS ν F θ) := by …

-- Laplace/Multi/ResponseObservableSamplingGeometry.lean
/-- **The influence of a mean displacement on an observable**: along the response line
`θ(m(θ₀) + t e)`, `d/dt E_{θ_t} F |_{t=0} = ⟨u_F, e⟩`. -/
theorem hasDerivAt_lineObservable_zero {F : X → ℝ} (hF : Bdd F) (θ₀ e : 𝕍) :
    HasDerivAt (lineObservable hS ν F θ₀ e)
      (dotJ (regressionDir hS ν F θ₀ : J → ℝ) (e : J → ℝ)) 0 := by …

-- Laplace/Multi/ResponseObservableSamplingGeometry.lean
/-- **The observable signal is bounded by the structural signal**:
`⟨u_F, e⟩² ≤ G_θ(u_F, u_F) · |A_θ⁻¹ e|²_F`. -/
theorem sq_dotJ_regressionDir_le (F : X → ℝ) (θ e : 𝕍) :
    dotJ (regressionDir hS ν F θ : J → ℝ) (e : J → ℝ) ^ 2 ≤
      G θ (regressionDir hS ν F θ) (regressionDir hS ν F θ) *
        G θ ((CDE θ).symm e) ((CDE θ).symm e) := by …

-- Laplace/Multi/ResponseObservableSamplingGeometry.lean
/-- **The exact sampling covariance of two linear statistics of the empirical displacement**:
`E[⟨u, M̂_n − m_D⟩ ⟨w, M̂_n − m_D⟩] = Cov_D(⟨u,S⟩, ⟨w,S⟩) / n`. -/
theorem integral_dotJ_sampleResponse_sub_mul (hind : ∀ i k, i ≠ k → IndepFun (Xs i) (Xs k) P)
    {n : ℕ} (hn : 0 < n) (u w : J → ℝ) :
    ∫ ω, dotJ u ((raw n) ω) * dotJ w ((raw n) ω) ∂P =
      lawCov D (dirLoss S u) (dirLoss S w) / n := by …

-- Laplace/Multi/ResponseObservableSamplingGeometry.lean
/-- **At a matched law the sampling covariance matrix is the Fisher Gram matrix of the regression
directions over `n`**: `E[⟨u_F, ξ_n⟩ ⟨u_{F'}, ξ_n⟩] = G_{θ₀}(u_F, u_{F'}) / n`. -/
theorem integral_influence_mul_influence_matched
    (hind : ∀ i k, i ≠ k → IndepFun (Xs i) (Xs k) P) {n : ℕ} (hn : 0 < n) (F F' : X → ℝ)
    (θ₀ : 𝕍) (hD : D = Pfam (θ₀ : J → ℝ)) :
    ∫ ω, dotJ (regressionDir hS ν F θ₀ : J → ℝ) ((raw n) ω) *
        dotJ (regressionDir hS ν F' θ₀ : J → ℝ) ((raw n) ω) ∂P =
      G θ₀ (regressionDir hS ν F θ₀) (regressionDir hS ν F' θ₀) / n := by …

-- Laplace/Multi/ResponseObservableSamplingGeometry.lean
/-- **The sampling variance of a linearised posterior expectation at a matched law is the explained
variance over `n`, at most `Var_{θ₀} F / n`.** -/
theorem integral_sq_influence_matched_le (hind : ∀ i k, i ≠ k → IndepFun (Xs i) (Xs k) P)
    {n : ℕ} (hn : 0 < n) {F : X → ℝ} (hF : Bdd F) (θ₀ : 𝕍) (hD : D = Pfam (θ₀ : J → ℝ)) :
    ∫ ω, dotJ (regressionDir hS ν F θ₀ : J → ℝ) ((raw n) ω) ^ 2 ∂P ≤
      lawCov (Pfam (θ₀ : J → ℝ)) F F / n := by …

-- Laplace/Multi/ResponseObservableSamplingGeometry.lean
/-- **The observable resolution floor**: at a matched law, if the observable `F` resolves the truth
displacement `e` above its own sampling noise, `E[⟨u_F, ξ_n⟩²] ≤ ⟨u_F, e⟩²`, then
`n · |A_{θ₀}⁻¹ e|²_F ≥ 1`: no posterior expectation resolves a truth shift that the structural
coordinate does not resolve. -/
theorem observable_resolution_floor (hind : ∀ i k, i ≠ k → IndepFun (Xs i) (Xs k) P) {n : ℕ}
    (hn : 0 < n) (F : X → ℝ) (θ₀ e : 𝕍) (hD : D = Pfam (θ₀ : J → ℝ))
    (hpos : 0 < G θ₀ (regressionDir hS ν F θ₀) (regressionDir hS ν F θ₀))
    (hres : ∫ ω, dotJ (regressionDir hS ν F θ₀ : J → ℝ) ((raw n) ω) ^ 2 ∂P ≤
      dotJ (regressionDir hS ν F θ₀ : J → ℝ) (e : J → ℝ) ^ 2) :
    1 ≤ n * G θ₀ ((CDE θ₀).symm e) ((CDE θ₀).symm e) := by …

-- Laplace/Multi/ResponseSimplexCompletion.lean
/-- The closed probability simplex on a finite set, to carry the spherical metric. -/
@[ext]
structure SphSimplex where
  /-- The law. -/
  law : X → ℝ
  nonneg : ∀ x, 0 ≤ law x
  sum_one : ∑ x, law x = 1


-- Laplace/Multi/ResponseSimplexCompletion.lean
/-- `dist p q = 2 arccos ∑_x √(p_x q_x)`. -/
theorem dist_eq (p q : SphSimplex X) :
    dist p q = 2 * Real.arccos (∑ x, √(p.law x) * √(q.law x)) := by …

-- Laplace/Multi/ResponseSimplexCompletion.lean
/-- **Distinct vertices are at distance `π`**: the diameter is attained. -/
theorem dist_dirac [DecidableEq X] {x y : X} (hxy : x ≠ y) :
    dist (dirac x) (dirac y) = Real.pi := by …

-- Laplace/Multi/ResponseSimplexCompletion.lean
/-- **The arc is at most `π` times the chord**: `dist p q ≤ π ‖√p − √q‖` (the root vectors are
unit vectors, the Fisher sphere has radius `2`). -/
theorem le_dist_rootVec (p q : SphSimplex X) :
    dist p q ≤ Real.pi * dist (rootVec p) (rootVec q) := by …

-- Laplace/Multi/ResponseSimplexCompletion.lean
/-- **The spherical closed simplex is compact.** -/
instance compactSpace : CompactSpace (SphSimplex X) := by …

-- Laplace/Multi/ResponseSimplexCompletion.lean
/-- **The positive laws are dense in the spherical closed simplex.** -/
theorem dense_pos [Nonempty X] : Dense (pos (X := X)) := fun p ↦
  mem_closure_of_tendsto (tendsto_mixSeq p)
    (Eventually.of_forall fun k ↦ mix_mem_pos p _ _ (step_mem k).1)


-- Laplace/Multi/ResponseSimplexCompletion.lean
/-- **The response-to-law map is an isometry** of the Fisher space into the spherical simplex. -/
theorem isometry_toSph : Isometry (toSph hS ν hν) :=

-- Laplace/Multi/ResponseSimplexCompletion.lean
/-- **THE COMPLETION THEOREM**: the intrinsic Fisher completion of a saturated finite family is
isometric to the spherical closed simplex `Δ̄(X)` with `dist p q = 2 arccos ∑_x √(p_x q_x)`. -/
noncomputable def fisherCompletionIso : FisherCompletion hS ν ≃ᵢ SphSimplex X where
  toEquiv := Equiv.ofBijective (completionToSph hS ν hν)
    ⟨(isometry_completionToSph hS ν hν hspan).injective, surjective_completionToSph hS ν hν hspan⟩
  isometry_toFun := isometry_completionToSph hS ν hν hspan


-- Laplace/Multi/ResponseSimplexCompletion.lean
/-- **The Fisher completion of a saturated finite family is compact.** -/
theorem compactSpace_fisherCompletion : CompactSpace (FisherCompletion hS ν) :=

-- Laplace/Multi/ResponseCurvatureDefect.lean
/-- **The sectional curvature is `¼` plus the residual defect**:
`K_θ(u,v) = 1/4 + (E[r_{uu} r_{vv}] − E[r_{uv}²]) / (4 D)` on a nondegenerate plane. -/
theorem fisherSectional_eq_quarter_add_residual (θ u v : 𝕍)
    (hden : 0 < G θ u u * G θ v v - G θ u v ^ 2) :
    fisherSectional hS ν θ u v = 1 / 4 +
      ((∫ z, scoreResidual hS ν θ u u z * scoreResidual hS ν θ v v z ∂Pfam (θ : J → ℝ)) -
        ∫ z, scoreResidual hS ν θ u v z ^ 2 ∂Pfam (θ : J → ℝ)) /
        (4 * (G θ u u * G θ v v - G θ u v ^ 2)) := by …
```

## Questions

1. **Audit K4, K5, K6.** Are the statements correct and are they the *right* statements? In particular: (a) K4's `journeyEnergy` uses the velocity `(CDE θ_t).symm ⟨m_D − m₀,_⟩` — is `(1−t)` the right weight for the budget from the featureless end (the endpoint action gives `KL(P_{θ₁}‖P_{θ₀}) = ∫₀¹(1−s)G ds`), and is there a dual formula `KL(ν‖R_D) = ∫₀¹ t·G dt`-type statement worth landing (the seabed has `toReal_klDiv_modelJourney_eq_action'` with weight `t`)? (b) K5: is the "observable resolution floor" the right transfer statement, or should the headline be the Gram matrix / the regression Pythagoras? Is `⟨u_F, e⟩` the right notion of influence (the derivative in *mean* coordinates), or should the influence be stated in Fisher-normalised form `G(u_F, A⁻¹e)`? (c) K6: anything false or vacuous? (The `SphSimplex` metric is `2·angle` of unit root vectors; arc ≤ π·chord since root vectors are unit, not radius 2.)

2. **Programme L.** Given the user's direction (map the space of responses across the data manifold from the featureless law to the data law; the change of posterior expectation values with the change of the data distribution; truth vs sampling resolution), what are the 5–7 most valuable *new* theorems now, ranked, with proof routes sized against this seabed? Candidates we see: (i) the i.i.d. sampling variance of the *nonlinear* posterior expectation `E_{θ̂}F` to `O(n^{-3/2})` (bias `= −(1/2n)⋯` via K2b + K5 + the second response `E[(F−EF)r_{VV}]`); (ii) the journey of an *observable* `t ↦ E_{θ_t}F` from featureless to data, its total variation/energy `∫|⟨u_F(θ_t), θ̇_t⟩|dt` and an "observable information budget"; (iii) the boundary behaviour of `u_F` and of the observable journey at a non-saturated boundary (does `E_{θ_t}F → E_{R_D}F`? — yes since laws converge; rate?); (iv) the dual journey from the data law back to ν (the m-geodesic / mixture `(1−t)D + tν`) and its budget; (v) Pinsker/Hellinger-type transfer: `|E_{θ_t}F − E_D F| ≤ √(2 KL(D‖R_D))·‖F‖ + …` making the "invisible information" `KL(D‖R_D)` control how far any posterior expectation is from the data expectation; (vi) sampling resolution of *chambers* of the response for data laws off the model (mismatch), i.e. K5 at a non-matched law with the Gram matrix `Cov_D(⟨u_F,S⟩,⟨u_G,S⟩)/n`; (vii) the extrinsic Gauss module. Rank these against your own candidates, say which to skip, and give the sharpest theorem statements.

3. **Anything in K1–K6 that is a known-false or vacuous statement?** Please check the hypotheses lists for accidental strength (e.g. `hν : ∀ x, 0 < ν {x}` in K1/K4 is full support; `hspan : SpansAffine` is saturation).
