# Consult: germbij analytic layer, fifth research round (after research_round4)

Same setting as the previous consults (Lean 4 + Mathlib, repo laplace, namespace Laplace.Multi, mirrored on the hironaka wall-atlas branch; germbij = "What expectation values know about the loss landscape"). Both round-4 priorities are now landed, but target 1 landed WITH A CORRECTION that raises a framework question I want you to rule on.

## What happened with round-4 target 1 (record-level mixed truth)

Your target was a 2D `WallChartsData` instance with truth monomial `q = (1,1)` whose fibre kernel `K_φ(σ/t)/log t` converges to the point mass `W(0) e^{-σ a(0)} φ(0)`. This CANNOT exist, and I proved why:

* In `WallChartsData m ℓ L'` the truth is the coordinate `z ℓ` and the ambient measure on `L' ⊆ ℝ^{m+1}` is Lebesgue (the transport field is `∫⁻_{L'} Ψ = ∑_i ∫⁻_{dom i} Ψ(rep_i u) dens_i(u) du`). When `L' ⊆ closedBall(0,R)` (sup norm) and `0 ≤ θ ≤ M`, the push-forward identity gives `∫_E K_θ ≤ M·vol(L' ∩ {z ℓ ∈ E}) ≤ M (2R)^m |E|`, hence `K_θ(s) ≤ M (2R)^m` for a.e. `s` (`WallChartsData.totalKernel_ae_le`). No chart of a Euclidean wall atlas can produce a `log t`, whatever its truth monomial.
* Mechanism in the blow-up chart `(x,y) ↦ (xy, y)` of the sector (the existing `BlowupSectorRecord`, `q = (1,1)`, `dens = |y|`): along the fibre `y = s/x` the Jacobian `|y| = |s|/|x|` times the coarea factor `1/|x|` gives `|s|/x²`, and the substitution `z₁ = s/x` turns the fibre kernel into `∫_{|s|≤|z₁|≤1} θ(s, z₁) dz₁` — bounded, no log. In general an analytic chart realising a mixed monomial `z₀ = u₀u₁` has vanishing Jacobian at the corner (the monomial has zero differential there), and that is exactly what cancels the coarea `1/w`.
* So the `dx/x` log endpoint (`MixedTruthLog`, `tendsto_mixedLog`) is the GENERAL-TRUTH situation: Lebesgue measure on the (x,y) square pushed forward under the truth FUNCTION `T(x,y) = xy`. I made that a record: `TruthChartsData m T L'` has the fields of `WallChartsData` with `T (rep i u) = truthMono (S i) (q i) u` on the domains (`WallChartsData.toTruth` is the case `T = (· ℓ)`), the same push-forward identity `∫⁻_{L'} θ(z) η(T z) dz = ∫⁻ η(s) K_θ(s) ds` with the same proof (`lintegral_mul_comp_truth`); `mixData` is the identity chart of `(0,1/2]²` with `T = z₀z₁`, `q = (1,1)`, `k = 0` (solve for `z₀`), density `= 1` on the square; at `s > 0` only the sign branch `x > 0` meets the square, the fibre point is `(s/x, x)`, the Jacobian is `1/x`, and `K_θ(s) = ∫_{2s}^{1/2} θ(s/x, x) dx/x` exactly (`mixData_totalKernel`). Then `K(σ/t)/log t → e^{-σ a(0)} ψ(0)` for `F = z₀z₁ a(z)` (`mix_tendsto_totalKernel`) and the fibre expectation → `ψ(0)/χ(0)` (`mix_tendsto_fibre_expectation`).

The note's S14 setting (as written): `L = {z : z_ℓ ∈ B₀, z' ∈ A'} ⊆ W` a compact product region, truth = the coordinate `z_ℓ`, wall data over `L ∩ {|z_ℓ| ≤ ε}`. Under that setting, the mixed-truth log endpoint is impossible, and the whole "logarithmic endpoint" phenomenon comes only from the LOSS being flat along a tied face (`LogModel`, `tendsto_modelKernel_tied`), never from the truth.

## Round-4 target 2 landed (`ProductChartLP.lean`)

`LPOptimal Q κ γ δ a α` (feasible and minimal); with `Q = 0`, `κ > 0`, `δ > 0`, `λ > 0`, `a_i = λκ_i` on the tied set `T ≠ ∅` and `λκ_i < a_i` off it: `lpOptimal_product_iff` (optimal iff `α ≥ 0`, `α_N = 0`, `κ·α = δ`), `lpOptimal_value` (`λδ`), `lpOptimal_iff_exists_weights` (`Opt = conv{(δ/κ_i)e_i : i ∈ T}`), `uniqueLPMin_iff_card_eq_one` (unique minimiser iff `|T| = 1`, and then it is the tied vertex); in the index shape of `tendsto_modelKernel_partial` (`Fin (k+1) ⊕ ν`): `lpOptimal_partial_iff` and `card_image_inl` (`|T| = k+1`, so `|T| − 1 = k` = log exponent).

## Statements (Lean, verbatim)

```lean
/-- **Coordinate truths carry no logarithmic mass.** Over a bounded region the total fibre kernel
of a bounded observable is bounded almost everywhere. -/
theorem totalKernel_ae_le {θ : (Fin (m + 1) → ℝ) → ℝ≥0∞} (hθ : Measurable θ) {M : ℝ≥0∞}
    (hM : ∀ z, θ z ≤ M) {R : ℝ} (hR : 0 ≤ R)
    (hL : L' ⊆ Metric.closedBall (0 : Fin (m + 1) → ℝ) R) :
    ∀ᵐ s, D.totalKernel θ s ≤ M * ENNReal.ofReal ((2 * R) ^ m) := by
  refine ae_le_of_forall_setLIntegral_le_of_sigmaFinite (D.measurable_totalKernel hθ)
    fun E hE _ ↦ ?_
  set η : ℝ → ℝ≥0∞ := E.indicator (fun _ ↦ 1) with hη
  have hηm : Measurable η := measurable_const.indicator hE
  have hR' : ∫⁻ s, η s * D.totalKernel θ s = ∫⁻ s in E, D.totalKernel θ s := by

structure TruthChartsData (m : ℕ) (T : (Fin (m + 1) → ℝ) → ℝ) (L' : Set (Fin (m + 1) → ℝ)) where
  /-- The finite chart index. -/
  ι : Type
  [fin : Fintype ι]
  /-- The chart representatives. -/
  rep : ι → (Fin (m + 1) → ℝ) → (Fin (m + 1) → ℝ)
  rep_cont : ∀ i, Continuous (rep i)
  /-- The radii of the closed boxes. -/
  ρ : ι → ℝ
  ρ_pos : ∀ i, 0 < ρ i
  /-- The chart domains. -/
  dom : ι → Set (Fin (m + 1) → ℝ)
  dom_eq : ∀ i, dom i = Metric.closedBall (0 : Fin (m + 1) → ℝ) (ρ i) ∩ rep i ⁻¹' L'
  dom_meas : ∀ i, MeasurableSet (dom i)
  /-- The chart densities. -/
  dens : ι → (Fin (m + 1) → ℝ) → ℝ
  dens_cont : ∀ i, Continuous (dens i)
  dens_nonneg : ∀ i u, 0 ≤ dens i u
  dens_supp : ∀ i u, dens i u ≠ 0 → u ∈ Metric.ball (0 : Fin (m + 1) → ℝ) (ρ i)
  /-- Sign, exponents and solve index of the truth monomial of each chart. -/
  S : ι → ℝ
  S_ne : ∀ i, S i ≠ 0
  q : ι → Fin (m + 1) → ℕ
  k : ι → Fin (m + 1)
  q_pos : ∀ i, 0 < q i (k i)
  /-- On the domain, the truth function of the representative is the exact monomial. -/
  truth : ∀ i, ∀ u ∈ dom i, T (rep i u) = truthMono (S i) (q i) u
  /-- The weighted transport identity. -/
  transport : ∀ Ψ : (Fin (m + 1) → ℝ) → ℝ≥0∞, Measurable Ψ →
    ∫⁻ z in L', Ψ z = ∑ i, ∫⁻ u in dom i, Ψ (rep i u) * ENNReal.ofReal (dens i u)

attribute [instance] TruthChartsData.fin


/-- **The push-forward identity for a general truth.** For nonnegative measurable `θ` and `η`,
`∫⁻_{L'} θ(z) η(T z) dz = ∫⁻ η(s) K_θ(s) ds`. -/
theorem lintegral_mul_comp_truth (hT : Measurable T) {θ : (Fin (m + 1) → ℝ) → ℝ≥0∞}
    (hθ : Measurable θ) {η : ℝ → ℝ≥0∞} (hη : Measurable η) :
    ∫⁻ z in L', θ z * η (T z) = ∫⁻ s, η s * D.totalKernel θ s := by
  rw [D.transport (fun z ↦ θ z * η (T z)) (hθ.mul (hη.comp hT))]

noncomputable def mixData : TruthChartsData 1 (fun z ↦ z 0 * z 1) mixL' where
  ι := Unit
  rep := fun _ u ↦ u
  rep_cont := fun _ ↦ continuous_id
  ρ := fun _ ↦ 1
  ρ_pos := fun _ ↦ one_pos
  dom := fun _ ↦ Metric.closedBall (0 : Fin 2 → ℝ) 1 ∩ mixL'
  dom_eq := fun _ ↦ rfl
  dom_meas := fun _ ↦ Metric.isClosed_closedBall.measurableSet.inter measurableSet_mixL'
  dens := fun _ ↦ toyDens
  dens_cont := fun _ ↦ continuous_toyDens
  dens_nonneg := fun _ ↦ toyDens_nonneg
  dens_supp := fun _ u hu ↦ mem_ball_zero_iff.mpr (toyDens_supp hu)
  S := fun _ ↦ 1
  S_ne := fun _ ↦ one_ne_zero
  q := fun _ ↦ ![1, 1]
  k := fun _ ↦ 0
  q_pos := fun _ ↦ by simp
  truth := fun _ u _ ↦ by
    simp [truthMono, Fin.prod_univ_two]
  transport := fun Ψ _ ↦ by

/-- **The fibre kernel of the mixed truth.** `K_θ(s) = ∫_{2s}^{1/2} θ(s/x, x) dx/x`. -/
theorem mixData_totalKernel {θ : (Fin 2 → ℝ) → ℝ≥0∞} {s : ℝ} (hs : 0 < s) :
    mixData.totalKernel θ s =
      ∫⁻ x in Icc (2 * s) (1 / 2), θ ![s / x, x] * ENNReal.ofReal (1 / x) := by
  unfold TruthChartsData.totalKernel

/-- **The mixed truth at the logarithmic scale, record level.** For the loss `F = z₀ z₁ · a(z)`
along the ray `s = σ/t`, the fibre kernel of `e^{-tF} ψ` grows like `log t` with coefficient
`e^{-σ a(0)} ψ(0)`. -/
theorem mix_tendsto_totalKernel {σ : ℝ} (hσ : 0 < σ) {a ψ : (Fin 2 → ℝ) → ℝ} (ha : Continuous a)
    (hψc : Continuous ψ) (hψ : ∀ z, 0 ≤ ψ z) :
    Tendsto (fun t ↦ (mixData.totalKernel
        (fun z ↦ ENNReal.ofReal (exp (-(t * (z 0 * z 1 * a z))) * ψ z)) (σ / t)).toReal / log t)
      atTop (𝓝 (exp (-(σ * a 0)) * ψ 0)) := by
  have hvec : Continuous fun p : ℝ × ℝ ↦ (![p.2, p.1] : Fin 2 → ℝ) := by
    refine continuous_pi fun i ↦ ?_

    field_simp]

/-- **The fibre expectation of the mixed truth converges to the point evaluation.** -/
theorem mix_tendsto_fibre_expectation {σ : ℝ} (hσ : 0 < σ) {a ψ χ : (Fin 2 → ℝ) → ℝ}
    (ha : Continuous a) (hψc : Continuous ψ) (hψ : ∀ z, 0 ≤ ψ z) (hχc : Continuous χ)
    (hχ : ∀ z, 0 ≤ χ z) (hχ0 : 0 < χ 0) :
    Tendsto (fun t ↦ (mixData.totalKernel
        (fun z ↦ ENNReal.ofReal (exp (-(t * (z 0 * z 1 * a z))) * ψ z)) (σ / t)).toReal /
      (mixData.totalKernel
        (fun z ↦ ENNReal.ofReal (exp (-(t * (z 0 * z 1 * a z))) * χ z)) (σ / t)).toReal)
      atTop (𝓝 (ψ 0 / χ 0)) := by

def LPOptimal (Q κ : ι → ℝ) (γ δ : ℝ) (a α : ι → ℝ) : Prop :=
  ConstrainedFeasible Q κ γ δ α ∧
    ∀ β, ConstrainedFeasible Q κ γ δ β → ∑ i, a i * α i ≤ ∑ i, a i * β i



variable (hQ : ∀ i, Q i = 0) (hγ : 0 ≤ γ) (hκ : ∀ i, 0 < κ i) (hδ : 0 < δ) {lam : ℝ}
  (hlam : 0 < lam) {T : Finset ι} (hne : T.Nonempty) (hT : ∀ i ∈ T, a i = lam * κ i)
  (hN : ∀ i ∉ T, lam * κ i < a i)
include hQ hγ hκ hδ hlam hne hT hN

omit [DecidableEq ι] in
/-- **The optimal set of a product chart.** With `Q = 0`, `κ > 0`, `δ > 0` and
`λ = min a_i/κ_i` attained exactly on `T`, the optimal points are the nonnegative `α` supported on
`T` with `κ·α = δ`. -/
theorem lpOptimal_product_iff :
    LPOptimal Q κ γ δ a α ↔ (∀ i, 0 ≤ α i) ∧ (∀ i ∉ T, α i = 0) ∧ ∑ i, κ i * α i = δ := by
  classical

omit [DecidableEq ι] in
/-- **The optimal set is the simplex `conv{(δ/κ_i) e_i : i ∈ T}`**: the optimal points are exactly
the barycentric combinations `α_i = (δ/κ_i) w_i` with weights `w ≥ 0` supported on `T` summing to
one. -/
theorem lpOptimal_iff_exists_weights :
    LPOptimal Q κ γ δ a α ↔ ∃ w : ι → ℝ, (∀ i, 0 ≤ w i) ∧ (∀ i ∉ T, w i = 0) ∧ ∑ i, w i = 1 ∧
      ∀ i, α i = δ / κ i * w i := by
  rw [lpOptimal_product_iff hQ hγ hκ hδ hlam hne hT hN]
  constructor
  · rintro ⟨hα0, hαT, hκα⟩

/-- **Uniqueness of the LP minimiser is `|T| = 1`.** The LP minimiser is unique exactly when a
single coordinate is tied, and then it is the tied vertex. -/
theorem uniqueLPMin_iff_card_eq_one :
    UniqueLPMin Q κ γ δ a α ↔ T.card = 1 ∧ ∀ i, α i = if i ∈ T then δ / κ i else 0 := by
  rw [uniqueLPMin_iff_lpOptimal_unique]
  constructor

omit [DecidableEq ν] in
/-- **The optimal set of a partially tied chart** (hypotheses of `tendsto_modelKernel_partial`,
`a = r + 1`): the nonnegative `α` vanishing on the untied block `inr` with `κ_T·α_T = δ`, the
simplex on the tied block. -/
theorem lpOptimal_partial_iff {κ r α : Fin (k + 1) ⊕ ν → ℝ} {γ δ : ℝ} (hγ : 0 ≤ γ)
    (hκ : ∀ i, 0 < κ i) (hδ : 0 < δ) {lam : ℝ} (hlam : 0 < lam)
    (htied : ∀ i, (r (Sum.inl i) + 1) / κ (Sum.inl i) = lam)
    (hgap : ∀ j, lam * κ (Sum.inr j) < r (Sum.inr j) + 1) :
    LPOptimal 0 κ γ δ (fun i ↦ r i + 1) α ↔
      (∀ i, 0 ≤ α i) ∧ (∀ j, α (Sum.inr j) = 0) ∧ ∑ i, κ i * α i = δ := by
  classical
  have hmem : ∀ i : Fin (k + 1) ⊕ ν,
      i ∈ Finset.univ.image (Sum.inl : Fin (k + 1) → Fin (k + 1) ⊕ ν) ↔ ∃ i', Sum.inl i' = i :=
    fun i ↦ by simp
```

## Questions

1. **Framework ruling.** Is the correction right as mathematics: in the note's S14 setting (truth = coordinate `z_ℓ`, Lebesgue on a compact region), is the `log t` of a mixed truth genuinely impossible, and does the existing `MixedTruthLog` paragraph of the note need to be re-scoped as a statement about a truth FUNCTION rather than a wall chart? Please check the bound `K_θ ≤ M(2R)^m` a.e. and the cancellation argument for errors. Should the germbij note's principal theorem be stated for a truth function `T` (the `TruthChartsData` interface, which the hironaka export would then have to supply: charts monomialising the pair `(T, F)` — Hironaka on the ideal `(T)` with `F` monomialised as well) rather than for a coordinate? What is lost/gained? Concretely: is the coordinate case the right level of generality for "what expectation values of an observable know", or is the observable `T` the honest object (in which case every existing wall theorem should be re-read through `TruthChartsData` — does the analytic layer transfer verbatim, since it only consumes `chartFun`, `truthMono`, `fibreKernel`)?

2. **Audit** of the new statements (signs, constants, hypotheses): `totalKernel_ae_le`, `mixData_totalKernel` (range `Icc (2s) (1/2)`, Jacobian `1/x`, one branch), `mix_tendsto_totalKernel`, `lpOptimal_product_iff`, `uniqueLPMin_iff_card_eq_one`, `lpOptimal_partial_iff`. In particular: in `mixData` I solve for `z₀` (`k = 0`) so the fibre variable is `x = z₁`; the multiplicity is one because the other sign branch leaves the square — is a symmetric region (both sign branches admissible, giving `2 e^{-σ a(0)} ψ(0)`) worth recording, or is the one-branch statement enough?

3. **Ranking for the next rounds** (new math over process, as before). Candidates: (a) round-4 target 3, local σ-uniformity and `σ(t) → σ₀` (which model theorem to do first: fully tied constant-unit `tendsto_modelKernel_const`, or the partial face?); (b) round-4 target 4, scoped degeneracy — is anything left after the LP face theorem, e.g. `Q ≠ 0` with a tied truth constraint (optimal set as the intersection of two faces)? (c) the universal `TermMeasureCertificate` structure and the principal theorem stated with it; (d) hironaka-side atlas independence; (e) generalising the hironaka export to `TruthChartsData` (Hironaka on `(T)` — is that already what the wall-atlas branch's `WallAtlas.euclidean_export` does modulo naming?); (f) the mixed-truth `TruthChartsData` chart WITH a nontrivial density `|u|^h` — the intermediate cases between `h = 0` (log) and `h = 1` (bounded), e.g. `T = xy`, measure `y^h dx dy`: what is the asymptotic scale? Give an exact statement to formalise if you rank it. Rank by mathematical value to the note; say what to skip.

4. Anything in the new results you consider wrong or over-claimed.
