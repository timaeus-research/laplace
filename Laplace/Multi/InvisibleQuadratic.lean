/-
Copyright (c) 2026 Timaeus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Timaeus
-/
import Laplace.Multi.CurvatureSplit
import Laplace.Multi.EntropyTaylor
import Laplace.Multi.ConditionalVariational
import Laplace.Multi.InformationTaylor
import Laplace.Multi.TangentPythagoras

/-!
# The invisible information is the squared normal data displacement

For a data law `D = d ν` with bounded positive density, the affine data path `D_s = (1 + s(d−1)) ν`
has response `M_s = m₀ + s δ` and invisible information `R(s) = KL(D_s ‖ Π(M_s))`. Writing
`h = d − 1` for the data displacement (centred, bounded),

  `R(s) / s² → ½ ‖N_{m₀} h‖²_{L²(ν)}`      (`tendsto_invisibleBridge_div_sq`):

the total information `KL(D_s ‖ ν) = ½ s² E_ν h² + o(s²)` (`tendsto_klDiv_bridge_div_sq`), the
visible information `𝓘(M_s) = ½ s² g_{m₀}(δ, δ) + o(s²)` (`tendsto_genRate_atlas_div_sq`), and the
tangent Pythagoras `E_ν h² = g_{m₀}(δ, δ) + ‖N_{m₀} h‖²` with `δ = Cov_ν(S, h)` split the data
displacement into its visible Fisher part and the normal part that reconstruction cannot see.
-/

open MeasureTheory Filter Topology Set InformationTheory

namespace Laplace.Multi

variable {X : Type*} [MeasurableSpace X] [Nonempty X] {J : Type*} [Fintype J] [Nonempty J]
  {S : J → X → ℝ} (hS : ∀ j, Bdd (S j)) (ν : Measure X) [IsProbabilityMeasure ν]
include hS

/-- The family `θ ↦ P_θ` in natural coordinates. -/
local notation "Pfam" => familyMeasure ν (fun _ ↦ (1 : ℝ)) (fun _ ↦ (0 : ℝ)) S 1

/-- The direction subspace. -/
local notation "𝕍" => dirSpan ν (fun _ ↦ (1 : ℝ)) S

/-- The natural coordinate of a response. -/
local notation "θr" => responseTheta measurable_const (integrable_const 1) (fun _ ↦ one_pos)
  (one_integral_pos ν) hS

/-- The featureless response. -/
local notation "m₀" => meanMap ν (fun _ ↦ (1 : ℝ)) (fun _ ↦ (0 : ℝ)) S 1 0

omit [Nonempty X] [Nonempty J] in
/-- The featureless response has finite rate. -/
theorem genRate_featureless_ne_top : genRate ν S m₀ ≠ ⊤ := by
  rw [meanMap_zero_eq_mean ν, genRate_mean_eq_zero ν hS]
  exact ENNReal.zero_ne_top

theorem featureless_mem_intrinsicInterior :
    m₀ ∈ intrinsicInterior ℝ (momentBody ν (fun _ ↦ (1 : ℝ)) S) := by
  have h := atlas_mem_intrinsicInterior hS ν (genRate_featureless_ne_top hS ν) (s := 0) le_rfl
    zero_lt_one
  rwa [atlasPath_zero] at h

/-- The natural coordinate of the featureless response vanishes. -/
theorem responseTheta_featureless : θr m₀ = 0 := by
  have h := atlasTheta_zero hS ν (M := m₀)
  unfold atlasTheta at h
  rwa [atlasPath_zero] at h

/-- The reconstruction of the featureless response is the reference law. -/
theorem familyMeasure_responseTheta_featureless : Pfam (θr m₀) = ν := by
  rw [responseTheta_featureless hS ν, Submodule.coe_zero, familyMeasure_zero_eq hS ν]

/-- **The visible information is quadratic along the atlas**:
`𝓘(m₀ + s δ) / s² → ½ g_{m₀}(δ, δ)` as `s ↓ 0`, for every visible `δ`. -/
theorem tendsto_genRate_atlas_div_sq (δ : 𝕍) :
    Tendsto (fun s : ℝ ↦ (genRate ν S (m₀ + s • (δ : J → ℝ))).toReal / s ^ 2) (𝓝[>] 0)
      (𝓝 ((1 / 2) * fisherForm hS ν m₀ δ δ)) := by
  have hrel₀ := featureless_mem_intrinsicInterior hS ν
  obtain ⟨r, hr, C, hC, hCc, hCK, hCnhd⟩ := exists_compact_convex_nhd hS ν hrel₀
  have hMC : m₀ ∈ C := hCnhd _ (intrinsicInterior_subset hrel₀) (by simp [hr.le])
  obtain ⟨ρ, hρ, hint⟩ := Metric.eventually_nhds_iff.1
    (eventually_add_mem_intrinsicInterior hS ν hrel₀)
  have hI0 : (genRate ν S m₀).toReal = 0 := by
    rw [meanMap_zero_eq_mean ν, genRate_mean_eq_zero ν hS, ENNReal.toReal_zero]
  rw [Metric.tendsto_nhdsWithin_nhds]
  intro η hη
  obtain ⟨ε, hε⟩ : ∃ ε : ℝ, ε = η / (2 * (‖δ‖ ^ 2 + 1)) := ⟨_, rfl⟩
  have hε0 : 0 < ε := hε ▸ by positivity
  obtain ⟨δ₁, hδ₁, hpe⟩ := rate_peano_at hS ν hC hCc hCK hMC ε hε0
  refine ⟨min ρ (min r δ₁) / (‖δ‖ + 1), by positivity, fun {s} hs hds ↦ ?_⟩
  have hs0 : 0 < s := hs
  rw [Real.dist_eq, sub_zero, abs_of_pos hs0] at hds
  have hsδ : s * ‖δ‖ < min ρ (min r δ₁) := by
    have := (lt_div_iff₀ (by positivity)).1 hds
    nlinarith [norm_nonneg δ]
  have hnorm : ‖s • δ‖ = s * ‖δ‖ := by rw [norm_smul, Real.norm_eq_abs, abs_of_pos hs0]
  have hmem : m₀ + ((s • δ : 𝕍) : J → ℝ) ∈ intrinsicInterior ℝ (momentBody ν (fun _ ↦ (1 : ℝ)) S) :=
    hint (by rw [dist_zero_right, hnorm]; exact hsδ.trans_le (min_le_left _ _))
  have hinC : m₀ + ((s • δ : 𝕍) : J → ℝ) ∈ C :=
    hCnhd _ (intrinsicInterior_subset hmem) (by
      rw [add_sub_cancel_left, Submodule.norm_coe, hnorm]
      exact (hsδ.trans_le ((min_le_right _ _).trans (min_le_left _ _))).le)
  have key := hpe (s • δ) hinC (by
    rw [hnorm]; exact (hsδ.trans_le ((min_le_right _ _).trans (min_le_right _ _))).le)
  rw [Submodule.coe_smul, hI0, responseTheta_featureless hS ν, Submodule.coe_zero, dotJ_comm,
    dotJ_zero_left, LinearMap.map_smul₂, map_smul, smul_eq_mul, smul_eq_mul,
    fisherAmb_coe hS ν hrel₀, hnorm] at key
  rw [Real.dist_eq]
  have hs2 : 0 < s ^ 2 := by positivity
  have e : (genRate ν S (m₀ + s • (δ : J → ℝ))).toReal / s ^ 2 - 1 / 2 * fisherForm hS ν m₀ δ δ =
      ((genRate ν S (m₀ + s • (δ : J → ℝ))).toReal - 0 + 0 -
        1 / 2 * (s * (s * fisherForm hS ν m₀ δ δ))) / s ^ 2 := by
    field_simp
    ring
  rw [e, abs_div, abs_of_pos hs2, div_lt_iff₀ hs2]
  calc |(genRate ν S (m₀ + s • (δ : J → ℝ))).toReal - 0 + 0 -
        1 / 2 * (s * (s * fisherForm hS ν m₀ δ δ))| ≤ ε * (s * ‖δ‖) ^ 2 := key
    _ = ε * ‖δ‖ ^ 2 * s ^ 2 := by ring
    _ < η * s ^ 2 := by
        refine mul_lt_mul_of_pos_right ?_ hs2
        rw [hε, div_mul_eq_mul_div, div_lt_iff₀ (by positivity)]
        nlinarith [sq_nonneg ‖δ‖]

section Bridge

variable {d : X → ℝ} (hd : Measurable d) {c C : ℝ} (hc0 : 0 < c) (hc : ∀ x, c ≤ d x)
  (hC : ∀ x, d x ≤ C) (hnorm : ∫ x, d x ∂ν = 1)
include hd hc0 hc hC hnorm

omit [Nonempty X] [Fintype J] [Nonempty J] hS [IsProbabilityMeasure ν] hnorm in
/-- The data displacement `h = d − 1` is bounded. -/
theorem bdd_sub_one : Bdd fun x ↦ d x - 1 :=
  ⟨hd.sub measurable_const, |c| + |C| + 1, fun x ↦ by
    have h1 := hc x
    have h2 := hC x
    rw [abs_le]
    constructor <;> nlinarith [neg_abs_le c, le_abs_self C, abs_nonneg c, abs_nonneg C]⟩

omit [Nonempty X] [Fintype J] [Nonempty J] hS in
/-- The data law is a probability measure. -/
theorem isProbabilityMeasure_densLaw' : IsProbabilityMeasure (densLaw ν d) := by
  have h := isProbabilityMeasure_densLaw_bridge ν hd hc0 hc hC hnorm zero_le_one le_rfl
  have e : bridgeDens d 1 = d := by
    funext x
    simp [bridgeDens]
  rwa [e] at h

omit [Nonempty J] in
set_option linter.unusedFintypeInType false in
/-- The response of a bounded positive data law is interior. -/
theorem mean_densLaw_mem_intrinsicInterior :
    (fun i ↦ ∫ x, S i x ∂densLaw ν d) ∈
      intrinsicInterior ℝ (momentBody ν (fun _ ↦ (1 : ℝ)) S) := by
  have hpos : ∀ x, 0 < d x := fun x ↦ lt_of_lt_of_le hc0 (hc x)
  rw [densLaw_eq_tilted_log ν hpos hnorm]
  refine mean_tilted_mem_intrinsicInterior hS ν ⟨hd.log, max |Real.log c| |Real.log C|, fun x ↦ ?_⟩
  have h1 := Real.log_le_log hc0 (hc x)
  have h2 := Real.log_le_log (hpos x) (hC x)
  rw [abs_le]
  constructor
  · linarith [neg_abs_le (Real.log c), le_max_left |Real.log c| |Real.log C|]
  · linarith [le_abs_self (Real.log C), le_max_right |Real.log c| |Real.log C|]

variable (d) in
/-- **The invisible information along the affine data path**: `R(s) = KL(D_s ‖ Π(M_s))`. -/
noncomputable def invisibleBridge (s : ℝ) : ℝ :=
  (klDiv (densLaw ν (bridgeDens d s))
    (responseProjection hS ν (fun i ↦ ∫ x, S i x ∂densLaw ν (bridgeDens d s)))).toReal

/-- The invisible information is the total minus the visible information. -/
theorem invisibleBridge_eq {s : ℝ} (hs0 : 0 ≤ s) (hs1 : s < 1) :
    invisibleBridge hS ν d s =
      (klDiv (densLaw ν (bridgeDens d s)) ν).toReal -
        (genRate ν S (fun i ↦ ∫ x, S i x ∂densLaw ν (bridgeDens d s))).toReal := by
  have hP := isProbabilityMeasure_densLaw_bridge ν hd hc0 hc hC hnorm hs0 hs1.le
  have hfinD := genRate_ne_top_of_mem_intrinsicInterior hS ν
    (mean_densLaw_mem_intrinsicInterior hS ν hd hc0 hc hC hnorm)
  have hmean := mean_densLaw_bridge ν hd hc0 hc hC hS hs0 hs1.le
  have hfin : genRate ν S (fun i ↦ ∫ x, S i x ∂densLaw ν (bridgeDens d s)) ≠ ⊤ := by
    rw [hmean]
    exact genRate_ne_top_of_mem_intrinsicInterior hS ν
      (atlas_mem_intrinsicInterior hS ν hfinD hs0 hs1)
  have hkl : klDiv (densLaw ν (bridgeDens d s)) ν ≠ ⊤ :=
    klDiv_densLaw_ne_top ν (measurable_bridgeDens hd s) (lt_min one_pos hc0)
      (fun x ↦ (bridgeDens_bounds hc hC hs0 hs1.le x).1)
      (fun x ↦ (bridgeDens_bounds hc hC hs0 hs1.le x).2)
  obtain ⟨-, -, -, hpyth⟩ := responseProjection_spec hS ν hfin
  have h := hpyth (densLaw ν (bridgeDens d s)) hP rfl
  unfold invisibleBridge
  have hR : klDiv (densLaw ν (bridgeDens d s))
      (responseProjection hS ν (fun i ↦ ∫ x, S i x ∂densLaw ν (bridgeDens d s))) ≠ ⊤ := by
    intro htop
    rw [htop, top_add] at h
    exact hkl h
  rw [h, ENNReal.toReal_add hR hfin]
  ring

omit [Fintype J] [Nonempty J] hS hnorm in
/-- **The total information is quadratic**: `KL(D_s ‖ ν) / s² → ½ E_ν (d − 1)²`. -/
theorem tendsto_klDiv_bridge_div_sq :
    Tendsto (fun s ↦ (klDiv (densLaw ν (bridgeDens d s)) ν).toReal / s ^ 2) (𝓝[>] 0)
      (𝓝 ((∫ x, (d x - 1) ^ 2 ∂ν) / 2)) := by
  have hB := bdd_sub_one hd hc0 hc hC
  obtain ⟨hm, B, hBd⟩ := hB
  have hB0 : 0 ≤ B := (abs_nonneg _).trans (hBd (Classical.arbitrary X))
  have h := tendsto_integral_klFun_div_sq ν (q := fun s ↦ bridgeDens d s) (g := fun x ↦ d x - 1)
    (e := fun _ _ ↦ 0) hm.aestronglyMeasurable hB0 (Eventually.of_forall hBd)
    (fun t ↦ Eventually.of_forall fun x ↦ by simp [bridgeDens]) (δ := 1) (K := 0) one_pos le_rfl
    (fun t _ ↦ Eventually.of_forall fun x ↦ by simp)
    (fun t ↦ (measurable_bridgeDens hd t).aestronglyMeasurable)
  have h' := h.mono_left (nhdsWithin_mono _ (fun x (hx : x ∈ Ioi (0 : ℝ)) ↦ ne_of_gt hx))
  refine h'.congr' ?_
  filter_upwards [Ioo_mem_nhdsGT one_pos] with s hs
  rw [toReal_klDiv_densLaw ν (measurable_bridgeDens hd s) (lt_min one_pos hc0)
    (fun x ↦ (bridgeDens_bounds hc hC hs.1.le hs.2.le x).1)
    (fun x ↦ (bridgeDens_bounds hc hC hs.1.le hs.2.le x).2)]

omit [Nonempty X] [Nonempty J] hnorm in
/-- The response of the bridge law at time `s` is `m₀ + s δ`, `δ = M_D − m₀`. -/
theorem mean_densLaw_bridge_eq {s : ℝ} (hs0 : 0 ≤ s) (hs1 : s ≤ 1) :
    (fun i ↦ ∫ x, S i x ∂densLaw ν (bridgeDens d s)) =
      m₀ + s • ((fun i ↦ ∫ x, S i x ∂densLaw ν d) - m₀) := by
  rw [mean_densLaw_bridge ν hd hc0 hc hC hS hs0 hs1, atlasPath, meanMap_zero_eq_mean ν]
  module

/-- The covariance vector of the data displacement under the reference law is the atlas
increment: `Cov_ν(S, d − 1) = M_D − m₀`. -/
theorem respCov_featureless_sub_one :
    respCov hS ν m₀ (fun x ↦ d x - 1) = (fun i ↦ ∫ x, S i x ∂densLaw ν d) - m₀ := by
  funext j
  unfold respCov
  rw [familyMeasure_responseTheta_featureless hS ν]
  unfold lawCov
  simp only [Pi.sub_apply]
  rw [integral_densLaw_of_bounds ν hd hc0 hc (S j), meanMap_zero_eq_mean ν]
  obtain ⟨hSm, Bj, hBj⟩ := hS j
  have h1 : Integrable (fun x ↦ S j x * d x) ν :=
    (integrable_of_bounds ν hd hc hC).bdd_mul hSm.aestronglyMeasurable
      (Eventually.of_forall fun x ↦ by rw [Real.norm_eq_abs]; exact hBj x)
  have hd1 : Integrable d ν := integrable_of_bounds ν hd hc hC
  have e : (fun x ↦ S j x * (d x - 1)) = fun x ↦ S j x * d x - S j x := by
    funext x; ring
  rw [e, integral_sub h1 (integrable_of_bdd_prob ν ⟨hSm, Bj, hBj⟩),
    integral_sub hd1 (integrable_const 1),
    hnorm, integral_const, probReal_univ, one_smul, sub_self, mul_zero, sub_zero]
  refine congrArg (· - ∫ x, S j x ∂ν) ?_
  exact integral_congr_ae (Eventually.of_forall fun x ↦ mul_comm _ _)

/-- The atlas increment of the data law is visible. -/
theorem sub_one_dir_mem : (fun i ↦ ∫ x, S i x ∂densLaw ν d) - m₀ ∈ 𝕍 :=
  respCov_featureless_sub_one hS ν hd hc0 hc hC hnorm ▸
    respCov_mem_dirSpan hS ν (bdd_sub_one hd hc0 hc hC)

/-- **Tangent Pythagoras for the data displacement at the featureless law**:
`E_ν (d − 1)² = g_{m₀}(δ, δ) + ‖N_{m₀}(d − 1)‖²`, `δ = M_D − m₀`. -/
theorem integral_sub_one_sq_eq_fisher_add_normal :
    ∫ x, (d x - 1) ^ 2 ∂ν =
      fisherForm hS ν m₀ ⟨(fun i ↦ ∫ x, S i x ∂densLaw ν d) - m₀,
          sub_one_dir_mem hS ν hd hc0 hc hC hnorm⟩
        ⟨(fun i ↦ ∫ x, S i x ∂densLaw ν d) - m₀, sub_one_dir_mem hS ν hd hc0 hc hC hnorm⟩ +
        ∫ x, normalProj hS ν m₀ (bdd_sub_one hd hc0 hc hC) x ^ 2 ∂ν := by
  have hrel₀ := featureless_mem_intrinsicInterior hS ν
  have h := tangent_pythagoras hS ν hrel₀ (bdd_sub_one hd hc0 hc hC)
  rw [familyMeasure_responseTheta_featureless hS ν] at h
  have hd1 : Integrable d ν := integrable_of_bounds ν hd hc hC
  have hmean : ∫ y, (d y - 1) ∂ν = 0 := by
    rw [integral_sub hd1 (integrable_const 1), hnorm, integral_const, probReal_univ, one_smul,
      sub_self]
  rw [hmean] at h
  simp only [sub_zero] at h
  rw [h]
  congr 1
  have hc' : (⟨respCov hS ν m₀ (fun x ↦ d x - 1),
      respCov_mem_dirSpan hS ν (bdd_sub_one hd hc0 hc hC)⟩ : 𝕍) =
      ⟨(fun i ↦ ∫ x, S i x ∂densLaw ν d) - m₀, sub_one_dir_mem hS ν hd hc0 hc hC hnorm⟩ :=
    Subtype.ext (respCov_featureless_sub_one hS ν hd hc0 hc hC hnorm)
  rw [hc']

/-- **The invisible information is the squared normal data displacement**:
`R(s) / s² → ½ ‖N_{m₀}(d − 1)‖²_{L²(ν)}` as `s ↓ 0`. -/
theorem tendsto_invisibleBridge_div_sq :
    Tendsto (fun s ↦ invisibleBridge hS ν d s / s ^ 2) (𝓝[>] 0)
      (𝓝 ((∫ x, normalProj hS ν m₀ (bdd_sub_one hd hc0 hc hC) x ^ 2 ∂ν) / 2)) := by
  have hδ : (fun i ↦ ∫ x, S i x ∂densLaw ν d) - m₀ ∈ 𝕍 := sub_one_dir_mem hS ν hd hc0 hc hC hnorm
  have h1 := tendsto_klDiv_bridge_div_sq ν hd hc0 hc hC
  have h2 := tendsto_genRate_atlas_div_sq hS ν ⟨_, hδ⟩
  have h3 := h1.sub h2
  have hpyth := integral_sub_one_sq_eq_fisher_add_normal hS ν hd hc0 hc hC hnorm
  have hlim : (∫ x, (d x - 1) ^ 2 ∂ν) / 2 -
      1 / 2 * fisherForm hS ν m₀ ⟨_, hδ⟩ ⟨_, hδ⟩ =
      (∫ x, normalProj hS ν m₀ (bdd_sub_one hd hc0 hc hC) x ^ 2 ∂ν) / 2 := by
    rw [hpyth]; ring
  rw [hlim] at h3
  refine h3.congr' ?_
  filter_upwards [Ioo_mem_nhdsGT one_pos] with s hs
  rw [invisibleBridge_eq hS ν hd hc0 hc hC hnorm hs.1.le hs.2, sub_div,
    mean_densLaw_bridge_eq hS ν hd hc0 hc hC hs.1.le hs.2.le]

end Bridge

end Laplace.Multi
