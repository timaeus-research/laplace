/-
Copyright (c) 2026 Timaeus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Timaeus
-/
import Laplace.Multi.ResponseClassResolution
import Laplace.Multi.ResponseLocalMetricControl

/-!
# Intrinsic chamber resolution: two responses are resolved above the sampling floor

The chamber bound of `ResponseClassResolution` is stated for **frozen** margins: Fisher-normalised
mean ellipsoids `{m + z : zᵀ C_θ⁻¹ z < r²}`. On a coercive patch (`λ ≤ C ≤ Λ`) these transfer to
**intrinsic** Fisher balls with a condition-number loss:

`d_F(θ(m), θ(m+z)) ≤ √(Λ/λ) · √(q_θ(z))`   (`fisherDist_responseTheta_le_sqrt_samplingEnergy`),

so a frozen margin `r` gives an intrinsic margin `√(Λ/λ) r`
(`mem_fisherBall_of_samplingEnergy_lt`). Hence the **two-class separation theorem**
(`measureReal_both_resolved_ge`): if two data laws `D₀, D₁` have responses at intrinsic distance
`δ ≥ √(Λ₀/λ₀) r₀ + √(Λ₁/λ₁) r₁`, then with `n₀`, `n₁` samples the two empirical responses lie in
the disjoint intrinsic balls around the two responses with probability at least

`1 − tr(R₀ C_{D₀})/(n₀ r₀²) − tr(R₁ C_{D₁})/(n₁ r₁²)`,

and `dim W/(n_i r_i²)` at matched laws. This is the resolution story in intrinsic form: two data
distributions with substantially different response geometry are told apart from samples once the
sampling floor `√(dim W/n)` clears the (condition-number-corrected) Fisher separation of their
responses.
-/

open MeasureTheory ProbabilityTheory Filter Topology Set

namespace Laplace.Multi

section Transfer

variable {X : Type*} [MeasurableSpace X] [Nonempty X] {J : Type*} [Fintype J] [Nonempty J]
  {S : J → X → ℝ} (hS : ∀ j, Bdd (S j)) (ν : Measure X) [IsProbabilityMeasure ν]
include hS

/-- The direction space. -/
local notation "𝕍" => dirSpan ν (fun _ ↦ (1 : ℝ)) S

/-- The chart derivative. -/
local notation "CD" => chartDeriv measurable_const (integrable_const 1) (fun _ ↦ one_pos)
  (one_integral_pos ν) hS

/-- The chart derivative equivalence. -/
local notation "CDE" => chartDerivEquiv measurable_const (integrable_const 1) (fun _ ↦ one_pos)
  (one_integral_pos ν) hS

/-- The response (inverse chart). -/
local notation "θr" => responseTheta measurable_const (integrable_const 1) (fun _ ↦ one_pos)
  (one_integral_pos ν) hS

/-- **An upper Fisher bound controls the Euclidean size of a chart derivative**:
`‖Dm(θ) u‖₂² ≤ Λ |u|²_{F,θ}` when `|w|²_F ≤ Λ ‖w‖₂²` for all `w`. -/
theorem dotJ_chartDeriv_self_le (θ : 𝕍) {Λ : ℝ} (hΛ0 : 0 ≤ Λ)
    (hΛ : ∀ w : J → ℝ, fisherVar S ν (θ : J → ℝ) w ≤ Λ * dotJ w w) (u : 𝕍) :
    dotJ (CD θ u : J → ℝ) (CD θ u : J → ℝ) ≤ Λ * fisherVar S ν (θ : J → ℝ) (u : J → ℝ) := by
  have hP := isProbabilityMeasure_family hS ν (θ : J → ℝ)
  obtain ⟨z, hz⟩ : ∃ z : J → ℝ, z = (CD θ u : J → ℝ) := ⟨_, rfl⟩
  have hzz : 0 ≤ dotJ z z := dotJ_self_nonneg z
  have hF := dotJ_chartDeriv_eq_neg_lawCov hS ν θ z u
  rw [← hz] at hF
  have hcs := lawCov_sq_le (familyMeasure ν (fun _ ↦ (1 : ℝ)) (fun _ ↦ (0 : ℝ)) S 1 (θ : J → ℝ))
    (bdd_dirLoss hS z) (bdd_dirLoss hS (u : J → ℝ))
  have hΛz := hΛ z
  have hu0 := fisherVar_nonneg hS ν (θ : J → ℝ) (u : J → ℝ)
  rw [← hz]
  rcases hzz.lt_or_eq with hpos | hzero
  · have key : dotJ z z * dotJ z z ≤ dotJ z z * (Λ * fisherVar S ν (θ : J → ℝ) (u : J → ℝ)) := by
      calc dotJ z z * dotJ z z = (dotJ z z) ^ 2 := by ring
        _ = (lawCov _ (dirLoss S z) (dirLoss S (u : J → ℝ))) ^ 2 := by rw [hF]; ring
        _ ≤ fisherVar S ν (θ : J → ℝ) z * fisherVar S ν (θ : J → ℝ) (u : J → ℝ) := hcs
        _ ≤ (Λ * dotJ z z) * fisherVar S ν (θ : J → ℝ) (u : J → ℝ) :=
            mul_le_mul_of_nonneg_right hΛz hu0
        _ = dotJ z z * (Λ * fisherVar S ν (θ : J → ℝ) (u : J → ℝ)) := by ring
    exact le_of_mul_le_mul_left key hpos
  · rw [← hzero]
    exact mul_nonneg hΛ0 hu0

/-- **The frozen Fisher energy dominates the Euclidean norm**: `‖z‖₂² ≤ Λ q_θ(z)` on `W`. -/
theorem dotJ_self_le_mul_samplingEnergy (θ : 𝕍) (p : (J → ℝ) →ₗ[ℝ] 𝕍)
    (hp : ∀ w : 𝕍, p (w : J → ℝ) = w) {Λ : ℝ} (hΛ0 : 0 ≤ Λ)
    (hΛ : ∀ w : J → ℝ, fisherVar S ν (θ : J → ℝ) w ≤ Λ * dotJ w w) {z : J → ℝ} (hz : z ∈ 𝕍) :
    dotJ z z ≤ Λ * samplingEnergy hS ν θ p z := by
  rw [samplingEnergy_eq_fisherVar hS ν θ p hp hz]
  have h := dotJ_chartDeriv_self_le hS ν θ hΛ0 hΛ ((CDE θ).symm ⟨z, hz⟩)
  have e : (CD θ ((CDE θ).symm ⟨z, hz⟩) : J → ℝ) = z :=
    meanMapDeriv_chartDerivEquiv_symm hS ν θ ⟨z, hz⟩
  rwa [e] at h

variable {U : Set (J → ℝ)} (hU : Convex ℝ U)
  (hUint : U ⊆ intrinsicInterior ℝ (momentBody ν (fun _ ↦ (1 : ℝ)) S))
include hU hUint

/-- **Frozen margins transfer to intrinsic margins with a condition-number loss**:
`d_F(θ(M), θ(M+z)) ≤ √(Λ/λ) √(q_{θ(M)}(z))` on a coercive convex patch. -/
theorem fisherDist_responseTheta_le_sqrt_samplingEnergy {lam : ℝ} (hlam : 0 < lam)
    (hcoer : ∀ M ∈ U, ∀ w : J → ℝ, lam * dotJ w w ≤ fisherVar S ν (θr M : J → ℝ) w)
    {M : J → ℝ} (hM : M ∈ U) {Λ : ℝ} (hΛ0 : 0 ≤ Λ)
    (hΛ : ∀ w : J → ℝ, fisherVar S ν (θr M : J → ℝ) w ≤ Λ * dotJ w w)
    (p : (J → ℝ) →ₗ[ℝ] 𝕍) (hp : ∀ w : 𝕍, p (w : J → ℝ) = w) {z : J → ℝ} (hz : z ∈ 𝕍)
    (hMz : M + z ∈ U) :
    fisherDist S ν (θr M) (θr (M + z)) ≤ √(Λ / lam) * √(samplingEnergy hS ν (θr M) p z) := by
  have h1 := fisherDist_responseTheta_le hS ν hU hUint hlam hcoer hM hMz
  have h2 := dotJ_self_le_mul_samplingEnergy hS ν (θr M) p hp hΛ0 hΛ hz
  rw [add_sub_cancel_left] at h1
  calc fisherDist S ν (θr M) (θr (M + z)) ≤ √(dotJ z z) / √lam := h1
    _ ≤ √(Λ * samplingEnergy hS ν (θr M) p z) / √lam :=
        div_le_div_of_nonneg_right (Real.sqrt_le_sqrt h2) (Real.sqrt_nonneg _)
    _ = √(Λ / lam) * √(samplingEnergy hS ν (θr M) p z) := by
        rw [Real.sqrt_mul hΛ0, Real.sqrt_div hΛ0]
        ring

/-- **The intrinsic Fisher ball of radius `√(Λ/λ) r` contains the frozen ellipsoid of
radius `r`.** -/
theorem mem_fisherBall_of_samplingEnergy_lt {lam : ℝ} (hlam : 0 < lam)
    (hcoer : ∀ M ∈ U, ∀ w : J → ℝ, lam * dotJ w w ≤ fisherVar S ν (θr M : J → ℝ) w)
    {M : J → ℝ} (hM : M ∈ U) {Λ : ℝ} (hΛ0 : 0 ≤ Λ)
    (hΛ : ∀ w : J → ℝ, fisherVar S ν (θr M : J → ℝ) w ≤ Λ * dotJ w w)
    (p : (J → ℝ) →ₗ[ℝ] 𝕍) (hp : ∀ w : 𝕍, p (w : J → ℝ) = w) {r : ℝ} (hr : 0 < r)
    (hell : ∀ z ∈ 𝕍, samplingEnergy hS ν (θr M) p z < r ^ 2 → M + z ∈ U) {z : J → ℝ} (hz : z ∈ 𝕍)
    (hlt : samplingEnergy hS ν (θr M) p z < r ^ 2) :
    fisherDist S ν (θr M) (θr (M + z)) < √(Λ / lam) * r ∨ Λ = 0 := by
  rcases hΛ0.lt_or_eq with hΛpos | hΛzero
  · left
    have h := fisherDist_responseTheta_le_sqrt_samplingEnergy hS ν hU hUint hlam hcoer hM hΛ0 hΛ
      p hp hz (hell z hz hlt)
    have hq0 : 0 ≤ samplingEnergy hS ν (θr M) p z := by
      rw [samplingEnergy_eq_fisherVar hS ν (θr M) p hp hz]
      exact fisherVar_nonneg hS ν _ _
    have hs : √(samplingEnergy hS ν (θr M) p z) < r := by
      calc √(samplingEnergy hS ν (θr M) p z) < √(r ^ 2) := Real.sqrt_lt_sqrt hq0 hlt
        _ = r := Real.sqrt_sq hr.le
    exact h.trans_lt (mul_lt_mul_of_pos_left hs (Real.sqrt_pos.2 (div_pos hΛpos hlam)))
  · right
    exact hΛzero.symm

end Transfer

section TwoClass

variable {X : Type*} [MeasurableSpace X] [Nonempty X] {J : Type*} [Fintype J] [Nonempty J]
  [DecidableEq J] {Ω : Type*} {S : J → X → ℝ} (hS : ∀ j, Bdd (S j)) (ν : Measure X)
  [IsProbabilityMeasure ν] [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
include hS

/-- The direction space. -/
local notation "𝕍" => dirSpan ν (fun _ ↦ (1 : ℝ)) S

/-- The response (inverse chart). -/
local notation "θr" => responseTheta measurable_const (integrable_const 1) (fun _ ↦ one_pos)
  (one_integral_pos ν) hS

omit [Nonempty X] [Nonempty J] [DecidableEq J] [IsProbabilityMeasure ν] hS in
/-- A union bound for two events on a probability space, without measurability. -/
theorem measureReal_inter_ge_one_sub {A B : Set Ω} :
    1 - P.real Aᶜ - P.real Bᶜ ≤ P.real (A ∩ B) := by
  have hcover : (univ : Set Ω) ⊆ (A ∩ B) ∪ (Aᶜ ∪ Bᶜ) := fun ω _ ↦ by
    by_cases hA : ω ∈ A
    · by_cases hB : ω ∈ B
      · exact Or.inl ⟨hA, hB⟩
      · exact Or.inr (Or.inr hB)
    · exact Or.inr (Or.inl hA)
  have h1 : P.real univ ≤ P.real ((A ∩ B) ∪ (Aᶜ ∪ Bᶜ)) := measureReal_mono hcover
  have h2 := measureReal_union_le (μ := P) (A ∩ B) (Aᶜ ∪ Bᶜ)
  have h3 := measureReal_union_le (μ := P) Aᶜ Bᶜ
  rw [probReal_univ] at h1
  linarith

/-- **Two-class separation**: two data laws whose responses are at intrinsic Fisher distance
`δ ≥ √(Λ₀/λ₀) r₀ + √(Λ₁/λ₁) r₁` are resolved by `n₀`, `n₁` samples — the empirical responses fall
in the disjoint intrinsic balls around the two responses — with probability at least
`1 − tr(R₀C_{D₀})/(n₀r₀²) − tr(R₁C_{D₁})/(n₁r₁²)`. -/
theorem measureReal_both_resolved_ge
    -- the two data laws and samples
    (D₀ D₁ : Measure X) [IsProbabilityMeasure D₀] [IsProbabilityMeasure D₁] (hD₀ν : D₀ ≪ ν)
    (hD₁ν : D₁ ≪ ν) (Xs₀ Xs₁ : ℕ → Ω → X) (hXm₀ : ∀ i, Measurable (Xs₀ i))
    (hXm₁ : ∀ i, Measurable (Xs₁ i)) (hid₀ : ∀ i, IdentDistrib (Xs₀ i) (Xs₀ 0) P P)
    (hid₁ : ∀ i, IdentDistrib (Xs₁ i) (Xs₁ 0) P P) (hlaw₀ : P.map (Xs₀ 0) = D₀)
    (hlaw₁ : P.map (Xs₁ 0) = D₁) (hind₀ : ∀ i k, i ≠ k → IndepFun (Xs₀ i) (Xs₀ k) P)
    (hind₁ : ∀ i k, i ≠ k → IndepFun (Xs₁ i) (Xs₁ k) P)
    -- the coercive patches
    {U₀ U₁ : Set (J → ℝ)} (hU₀ : Convex ℝ U₀) (hU₁ : Convex ℝ U₁)
    (hU₀int : U₀ ⊆ intrinsicInterior ℝ (momentBody ν (fun _ ↦ (1 : ℝ)) S))
    (hU₁int : U₁ ⊆ intrinsicInterior ℝ (momentBody ν (fun _ ↦ (1 : ℝ)) S))
    {lam₀ lam₁ : ℝ} (hlam₀ : 0 < lam₀) (hlam₁ : 0 < lam₁)
    (hcoer₀ : ∀ M ∈ U₀, ∀ w : J → ℝ, lam₀ * dotJ w w ≤ fisherVar S ν (θr M : J → ℝ) w)
    (hcoer₁ : ∀ M ∈ U₁, ∀ w : J → ℝ, lam₁ * dotJ w w ≤ fisherVar S ν (θr M : J → ℝ) w)
    (hm₀ : (fun j ↦ ∫ x, S j x ∂D₀) ∈ U₀) (hm₁ : (fun j ↦ ∫ x, S j x ∂D₁) ∈ U₁)
    {Λ₀ Λ₁ : ℝ} (hΛ₀ : 0 < Λ₀) (hΛ₁ : 0 < Λ₁)
    (hΛ₀' : ∀ w : J → ℝ, fisherVar S ν (θr (fun j ↦ ∫ x, S j x ∂D₀) : J → ℝ) w ≤ Λ₀ * dotJ w w)
    (hΛ₁' : ∀ w : J → ℝ, fisherVar S ν (θr (fun j ↦ ∫ x, S j x ∂D₁) : J → ℝ) w ≤ Λ₁ * dotJ w w)
    -- the frozen margins and the retraction
    (p : (J → ℝ) →ₗ[ℝ] 𝕍) (hp : ∀ w : 𝕍, p (w : J → ℝ) = w) {r₀ r₁ : ℝ} (hr₀ : 0 < r₀)
    (hr₁ : 0 < r₁)
    (hell₀ : ∀ z ∈ 𝕍, samplingEnergy hS ν (θr (fun j ↦ ∫ x, S j x ∂D₀)) p z < r₀ ^ 2 →
      (fun j ↦ ∫ x, S j x ∂D₀) + z ∈ U₀)
    (hell₁ : ∀ z ∈ 𝕍, samplingEnergy hS ν (θr (fun j ↦ ∫ x, S j x ∂D₁)) p z < r₁ ^ 2 →
      (fun j ↦ ∫ x, S j x ∂D₁) + z ∈ U₁)
    -- the intrinsic separation
    (hsep : √(Λ₀ / lam₀) * r₀ + √(Λ₁ / lam₁) * r₁ ≤
      fisherDist S ν (θr (fun j ↦ ∫ x, S j x ∂D₀)) (θr (fun j ↦ ∫ x, S j x ∂D₁)))
    {n₀ n₁ : ℕ} (hn₀ : 0 < n₀) (hn₁ : 0 < n₁) :
    Disjoint {M' | fisherDist S ν (θr (fun j ↦ ∫ x, S j x ∂D₀)) (θr M') < √(Λ₀ / lam₀) * r₀}
        {M' | fisherDist S ν (θr (fun j ↦ ∫ x, S j x ∂D₁)) (θr M') < √(Λ₁ / lam₁) * r₁} ∧
      1 - -(∑ a, ∑ b, samplingOp hS ν (θr (fun j ↦ ∫ x, S j x ∂D₀)) p (Pi.single b 1) a *
            lawCov D₀ (S a) (S b)) / n₀ / r₀ ^ 2 -
          -(∑ a, ∑ b, samplingOp hS ν (θr (fun j ↦ ∫ x, S j x ∂D₁)) p (Pi.single b 1) a *
            lawCov D₁ (S a) (S b)) / n₁ / r₁ ^ 2 ≤
        P.real {ω | fisherDist S ν (θr (fun j ↦ ∫ x, S j x ∂D₀)) (θr (sampleResponse S Xs₀ n₀ ω)) <
            √(Λ₀ / lam₀) * r₀ ∧
          fisherDist S ν (θr (fun j ↦ ∫ x, S j x ∂D₁)) (θr (sampleResponse S Xs₁ n₁ ω)) <
            √(Λ₁ / lam₁) * r₁} := by
  -- the intrinsic margins
  have hmargin₀ : ∀ z ∈ 𝕍, samplingEnergy hS ν (θr (fun j ↦ ∫ x, S j x ∂D₀)) p z < r₀ ^ 2 →
      (fun j ↦ ∫ x, S j x ∂D₀) + z ∈
        {M' | fisherDist S ν (θr (fun j ↦ ∫ x, S j x ∂D₀)) (θr M') < √(Λ₀ / lam₀) * r₀} :=
    fun z hz hlt ↦ (mem_fisherBall_of_samplingEnergy_lt hS ν hU₀ hU₀int hlam₀ hcoer₀ hm₀ hΛ₀.le
      hΛ₀' p hp hr₀ hell₀ hz hlt).resolve_right hΛ₀.ne'
  have hmargin₁ : ∀ z ∈ 𝕍, samplingEnergy hS ν (θr (fun j ↦ ∫ x, S j x ∂D₁)) p z < r₁ ^ 2 →
      (fun j ↦ ∫ x, S j x ∂D₁) + z ∈
        {M' | fisherDist S ν (θr (fun j ↦ ∫ x, S j x ∂D₁)) (θr M') < √(Λ₁ / lam₁) * r₁} :=
    fun z hz hlt ↦ (mem_fisherBall_of_samplingEnergy_lt hS ν hU₁ hU₁int hlam₁ hcoer₁ hm₁ hΛ₁.le
      hΛ₁' p hp hr₁ hell₁ hz hlt).resolve_right hΛ₁.ne'
  refine ⟨?_, ?_⟩
  · rw [Set.disjoint_left]
    intro M' h₀ h₁
    have htri := fisherDist_triangle hS ν (θr (fun j ↦ ∫ x, S j x ∂D₀)) (θr M')
      (θr (fun j ↦ ∫ x, S j x ∂D₁))
    rw [fisherDist_comm hS ν (x := θr M')] at htri
    simp only [mem_ofPred_eq] at h₀ h₁
    linarith
  · have hb₀ := measureReal_sampleResponse_notMem_le hS ν P D₀ hD₀ν Xs₀ hXm₀ hid₀ hlaw₀ hind₀
      (θr (fun j ↦ ∫ x, S j x ∂D₀)) p hp hr₀ hmargin₀ hn₀
    have hb₁ := measureReal_sampleResponse_notMem_le hS ν P D₁ hD₁ν Xs₁ hXm₁ hid₁ hlaw₁ hind₁
      (θr (fun j ↦ ∫ x, S j x ∂D₁)) p hp hr₁ hmargin₁ hn₁
    have hub := measureReal_inter_ge_one_sub P
      (A := {ω | fisherDist S ν (θr (fun j ↦ ∫ x, S j x ∂D₀)) (θr (sampleResponse S Xs₀ n₀ ω)) <
        √(Λ₀ / lam₀) * r₀})
      (B := {ω | fisherDist S ν (θr (fun j ↦ ∫ x, S j x ∂D₁)) (θr (sampleResponse S Xs₁ n₁ ω)) <
        √(Λ₁ / lam₁) * r₁})
    have e₀ : {ω | sampleResponse S Xs₀ n₀ ω ∉
        {M' | fisherDist S ν (θr (fun j ↦ ∫ x, S j x ∂D₀)) (θr M') < √(Λ₀ / lam₀) * r₀}} =
        {ω | fisherDist S ν (θr (fun j ↦ ∫ x, S j x ∂D₀)) (θr (sampleResponse S Xs₀ n₀ ω)) <
          √(Λ₀ / lam₀) * r₀}ᶜ := rfl
    have e₁ : {ω | sampleResponse S Xs₁ n₁ ω ∉
        {M' | fisherDist S ν (θr (fun j ↦ ∫ x, S j x ∂D₁)) (θr M') < √(Λ₁ / lam₁) * r₁}} =
        {ω | fisherDist S ν (θr (fun j ↦ ∫ x, S j x ∂D₁)) (θr (sampleResponse S Xs₁ n₁ ω)) <
          √(Λ₁ / lam₁) * r₁}ᶜ := rfl
    rw [e₀] at hb₀
    rw [e₁] at hb₁
    have hinter : ({ω | fisherDist S ν (θr (fun j ↦ ∫ x, S j x ∂D₀))
          (θr (sampleResponse S Xs₀ n₀ ω)) < √(Λ₀ / lam₀) * r₀} ∩
        {ω | fisherDist S ν (θr (fun j ↦ ∫ x, S j x ∂D₁)) (θr (sampleResponse S Xs₁ n₁ ω)) <
          √(Λ₁ / lam₁) * r₁}) =
        {ω | fisherDist S ν (θr (fun j ↦ ∫ x, S j x ∂D₀)) (θr (sampleResponse S Xs₀ n₀ ω)) <
            √(Λ₀ / lam₀) * r₀ ∧
          fisherDist S ν (θr (fun j ↦ ∫ x, S j x ∂D₁)) (θr (sampleResponse S Xs₁ n₁ ω)) <
            √(Λ₁ / lam₁) * r₁} := rfl
    rw [hinter] at hub
    linarith

end TwoClass

end Laplace.Multi
