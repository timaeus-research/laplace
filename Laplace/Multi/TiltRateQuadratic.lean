/-
Copyright (c) 2026 Timaeus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Timaeus
-/
import Mathlib
import Laplace.Multi.TiltQuadratic
import Laplace.Multi.EmpiricalProjection
import Laplace.Multi.PathEnergy

/-!
# The visible information along a bounded tilt is the energy of the regression

For a bounded score `f`, the tilts `ν_t ∝ e^{tf} ν` have responses `M_t = E_{ν_t} S` with
`M_t = m₀ + t u + o(t)`, `u = Cov_ν(S, f)`, and the visible information satisfies

  `𝓘(M_t) / t² → ⟨a, u⟩ / 2`                          (`tendsto_genRate_tiltResponse_div_sq`),

where `a ∈ 𝕍` is the regression coefficient of `f` on the statistic (`Cov_ν(S_j, ⟨a,S⟩) = u_j`),
so that `⟨a, u⟩ = Var_ν⟨a, S⟩ = ‖B₀ f − E_ν f‖²` is the energy of the regression
(`RegressionProjection`). The proof is a sandwich around the family member `P_{−ta}`, whose
response `N_t` has the same first-order expansion `m₀ + t u + o(t)` and whose rate is the
information of the tilt by `t⟨a, S⟩`: the Fenchel inequality gives
`𝓘(M_t) ≥ 𝓘(N_t) + t⟨a, M_t − N_t⟩`, the Bregman identity between atlas points gives
`𝓘(M_t) ≤ 𝓘(N_t) + ⟨θ(M_t), N_t − M_t⟩`, and `θ(M_t) = O(t)` by the local Lipschitz property of
the inverse chart. Together with `TiltQuadratic`, this makes the visible part of the quadratic
information split `‖B h‖²` for `h = f − E_ν f`.
-/

open MeasureTheory Filter Topology Set InformationTheory Asymptotics
open scoped ENNReal

namespace Laplace.Multi

section Filter

variable {J : Type*}

/-- A family in `K` converging along a filter to a point of the relative interior is eventually
in the relative interior. -/
theorem eventually_mem_intrinsicInterior_of_tendsto_filter {K : Set (J → ℝ)} {ι : Type*}
    {l : Filter ι} {M : ι → J → ℝ} {L : J → ℝ} (hM : ∀ᶠ i in l, M i ∈ K)
    (hL : L ∈ intrinsicInterior ℝ K) (hlim : Tendsto M l (𝓝 L)) :
    ∀ᶠ i in l, M i ∈ intrinsicInterior ℝ K := by
  classical
  obtain ⟨y, hy, hyL⟩ := mem_intrinsicInterior.1 hL
  obtain ⟨N, hN⟩ : ∃ N : ι → affineSpan ℝ K, N = fun i ↦
    if h : M i ∈ K then (⟨M i, subset_affineSpan ℝ K h⟩ : affineSpan ℝ K) else y := ⟨_, rfl⟩
  have hlim' : Tendsto N l (𝓝 y) := by
    rw [tendsto_subtype_rng, hyL]
    refine hlim.congr' ?_
    filter_upwards [hM] with i hi
    rw [hN]
    simp only [dif_pos hi]
  filter_upwards [hM, hlim'.eventually (isOpen_interior.mem_nhds hy)] with i hi hn
  rw [hN] at hn
  simp only [dif_pos hi] at hn
  exact mem_intrinsicInterior.2 ⟨⟨M i, subset_affineSpan ℝ K hi⟩, hn, rfl⟩

end Filter

section Tilt

variable {X : Type*} [MeasurableSpace X] [Nonempty X] {J : Type*} [Fintype J]
  {S : J → X → ℝ}

/-- The response of the tilt `ν_t ∝ e^{tf} ν`. -/
noncomputable def tiltResponse (S : J → X → ℝ) (ν : Measure X) (f : X → ℝ) (t : ℝ) : J → ℝ :=
  fun i ↦ ∫ x, S i x ∂(ν.tilted fun x ↦ t * f x)

variable (hS : ∀ j, Bdd (S j)) (ν : Measure X) [IsProbabilityMeasure ν]
include hS

omit [Fintype J] [Nonempty X] hS in
theorem tiltResponse_zero (f : X → ℝ) : tiltResponse S ν f 0 = fun i ↦ ∫ x, S i x ∂ν := by
  funext i
  simp only [tiltResponse, tilted_zero_mul]

set_option linter.unusedSectionVars false in
set_option linter.unusedFintypeInType false in
/-- **The response of a tilt moves at the covariance velocity**: `M_t' (0) = Cov_ν(S, f)`. -/
theorem hasDerivAt_tiltResponse {f : X → ℝ} (hf : Bdd f) :
    HasDerivAt (tiltResponse S ν f) (fun j ↦ lawCov ν (S j) f) 0 := by
  rw [hasDerivAt_pi]
  intro j
  have h := hasDerivAt_integral_tilted ν hf (hS j) 0
  simp only [tilted_zero_mul] at h
  exact h

omit [Nonempty X] in
theorem genRate_tiltResponse_ne_top {f : X → ℝ} (hf : Bdd f) (t : ℝ) :
    genRate ν S (tiltResponse S ν f t) ≠ ⊤ := by
  have := isProbabilityMeasure_tilted (integrable_exp_of_bdd ν (Bdd.const_mul t hf))
  refine ne_top_of_le_ne_top ?_ (genRate_le_klDiv ν hS (ν.tilted fun x ↦ t * f x) rfl)
  rw [klDiv_tilted_eq ν (Bdd.const_mul t hf)]
  exact ENNReal.ofReal_ne_top

/-- The family member `P_{−ta}` is the tilt by `t⟨a, S⟩`. -/
theorem familyMeasure_neg_smul_eq_tilted (a : J → ℝ) (t : ℝ) :
    familyMeasure ν (fun _ ↦ (1 : ℝ)) (fun _ ↦ (0 : ℝ)) S 1 (-(t • a)) =
      ν.tilted fun x ↦ t * dirLoss S a x := by
  rw [familyMeasure_one_zero_eq_tilted hS ν]
  congr 1
  funext x
  rw [dirLoss_neg (S := S), dirLoss_smul]
  ring

/-- The response of `P_{−ta}` is the response of the tilt by `⟨a, S⟩`. -/
theorem meanMap_neg_smul_eq_tiltResponse (a : J → ℝ) (t : ℝ) :
    meanMap ν (fun _ ↦ (1 : ℝ)) (fun _ ↦ (0 : ℝ)) S 1 (-(t • a)) =
      tiltResponse S ν (dirLoss S a) t := by
  rw [← mean_familyMeasure_one_zero hS ν, familyMeasure_neg_smul_eq_tilted hS ν]
  rfl

/-- The rate of the response of `P_{−ta}` is the information of the tilt by `t⟨a, S⟩`. -/
theorem genRate_tiltResponse_dirLoss_toReal (a : J → ℝ) (t : ℝ) :
    (genRate ν S (tiltResponse S ν (dirLoss S a) t)).toReal =
      (klDiv (ν.tilted fun x ↦ t * dirLoss S a x) ν).toReal := by
  rw [← meanMap_neg_smul_eq_tiltResponse hS ν, ← familyMeasure_neg_smul_eq_tilted hS ν,
    klDiv_familyMeasure_featureless hS ν, genRate_meanMap_neg hS ν (t • a), neg_neg,
    dotJ_neg_left, neg_neg]

/-- The Fenchel lower bound: `𝓘(N_t) + t⟨a, M_t − N_t⟩ ≤ 𝓘(M_t)`. -/
theorem genRate_tiltResponse_dirLoss_add_le {f : X → ℝ} (hf : Bdd f) (a : J → ℝ) (t : ℝ) :
    (genRate ν S (tiltResponse S ν (dirLoss S a) t)).toReal +
        t * dotJ a (tiltResponse S ν f t - tiltResponse S ν (dirLoss S a) t) ≤
      (genRate ν S (tiltResponse S ν f t)).toReal := by
  have h1 := dotJ_sub_genRate_le_featCgf ν (genRate_tiltResponse_ne_top hS ν hf t) (t • a)
  obtain ⟨-, h2⟩ := featCgf_eq_dotJ_sub_genRate_meanMap hS ν (t • a)
  rw [meanMap_neg_smul_eq_tiltResponse hS ν] at h2
  rw [dotJ_smul_left] at h1 h2
  rw [(isLinearMap_dotJ a).map_sub]
  linarith

end Tilt

section Main

variable {X : Type*} [MeasurableSpace X] [Nonempty X] {J : Type*} [Fintype J] [Nonempty J]
  {S : J → X → ℝ} (hS : ∀ j, Bdd (S j)) (ν : Measure X) [IsProbabilityMeasure ν]
include hS

omit [Nonempty X] [Nonempty J] hS in
/-- A bound on the pairing by the sup norms. -/
theorem abs_dotJ_le_card_mul (θ v : J → ℝ) :
    |dotJ θ v| ≤ (Fintype.card J : ℝ) * ‖θ‖ * ‖v‖ := by
  refine (abs_dotJ_le θ v).trans ?_
  have : ∑ j, |θ j| ≤ ∑ _j : J, ‖θ‖ := Finset.sum_le_sum fun j _ ↦ by
    rw [← Real.norm_eq_abs]
    exact norm_le_pi_norm θ j
  rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul] at this
  exact mul_le_mul_of_nonneg_right this (norm_nonneg v)

/-- **The natural coordinates of the tilt response are `O(t)`**. -/
theorem isBigO_responseTheta_tiltResponse {f : X → ℝ} (hf : Bdd f) :
    (fun t ↦ ‖(responseTheta measurable_const (integrable_const 1) (fun _ ↦ one_pos)
      (one_integral_pos ν) hS (tiltResponse S ν f t) : J → ℝ)‖) =O[𝓝 0] fun t ↦ t := by
  obtain ⟨K, s, hs, hK⟩ := (hasStrictFDerivAt_chartVInv measurable_const (integrable_const 1)
    (fun _ ↦ one_pos) (one_integral_pos ν) hS 0).exists_lipschitzOnWith
  have hc0 : chartV measurable_const (integrable_const 1) (fun _ ↦ one_pos) (one_integral_pos ν)
      hS 0 = 0 := Subtype.ext (by rw [chartV_apply, Submodule.coe_zero, sub_self])
  rw [hc0] at hs
  have hinv0 : chartVInv measurable_const (integrable_const 1) (fun _ ↦ one_pos)
      (one_integral_pos ν) hS 0 = 0 := by
    conv_lhs => rw [← hc0]
    exact chartVInv_chartV measurable_const (integrable_const 1) (fun _ ↦ one_pos)
      (one_integral_pos ν) hS 0
  have hmem : ∀ t, tiltResponse S ν f t - meanMap ν (fun _ ↦ (1 : ℝ)) (fun _ ↦ (0 : ℝ)) S 1 0 ∈
      dirSpan ν (fun _ ↦ (1 : ℝ)) S := fun t ↦
    sub_mem_dirSpan_of_mem_momentBody measurable_const (integrable_const 1) (fun _ ↦ one_pos)
      (one_integral_pos ν) hS (mem_momentBody_of_genRate_ne_top hS ν
        (genRate_tiltResponse_ne_top hS ν hf t))
  have hMd := hasDerivAt_tiltResponse hS ν hf
  have hM0 : (fun t ↦ tiltResponse S ν f t - meanMap ν (fun _ ↦ (1 : ℝ)) (fun _ ↦ (0 : ℝ)) S 1 0)
      =O[𝓝 0] fun t ↦ t := by
    have h := hMd.isBigO_sub
    simp only [sub_zero, tiltResponse_zero] at h
    rw [meanMap_zero_eq_mean ν]
    exact h
  have hw : Tendsto (fun t ↦ toV ν (fun _ ↦ (1 : ℝ)) S (tiltResponse S ν f t)) (𝓝 0) (𝓝 0) := by
    rw [tendsto_subtype_rng]
    simp only [Submodule.coe_zero]
    have h := (hMd.continuousAt.tendsto.sub
      (tendsto_const_nhds (x := meanMap ν (fun _ ↦ (1 : ℝ)) (fun _ ↦ (0 : ℝ)) S 1 0)))
    rw [tiltResponse_zero, ← meanMap_zero_eq_mean ν, sub_self] at h
    refine h.congr fun t ↦ ?_
    rw [toV_apply (hmem t)]
  refine (IsBigO.of_bound K ?_).trans hM0
  filter_upwards [hw.eventually_mem hs] with t ht
  have h0s : (0 : dirSpan ν (fun _ ↦ (1 : ℝ)) S) ∈ s := mem_of_mem_nhds hs
  have hd := hK.dist_le_mul _ ht 0 h0s
  rw [hinv0, dist_eq_norm, dist_eq_norm, sub_zero, sub_zero] at hd
  rw [Real.norm_eq_abs, abs_of_nonneg (norm_nonneg _)]
  unfold responseTheta
  rw [Submodule.norm_coe]
  refine hd.trans ?_
  rw [← Submodule.norm_coe, toV_apply (hmem t)]

/-- **The visible information along a bounded tilt is the energy of the regression**:
`𝓘(M_t)/t² → ⟨a, u⟩/2` with `u = Cov_ν(S, f)` and `a` the regression coefficient. -/
theorem tendsto_genRate_tiltResponse_div_sq {f : X → ℝ} (hf : Bdd f) :
    ∃ a ∈ dirSpan ν (fun _ ↦ (1 : ℝ)) S,
      (∀ j, lawCov ν (S j) (dirLoss S a) = lawCov ν (S j) f) ∧
      Tendsto (fun t ↦ (genRate ν S (tiltResponse S ν f t)).toReal / t ^ 2) (𝓝[≠] 0)
        (𝓝 (dotJ a (fun j ↦ lawCov ν (S j) f) / 2)) := by
  obtain ⟨a, ha, hreg⟩ := exists_regression_coefficient hS ν
    (M := fun i ↦ ∫ x, S i x ∂ν) 0 hf
  have h0 : familyMeasure ν (fun _ ↦ (1 : ℝ)) (fun _ ↦ (0 : ℝ)) S 1
      (atlasTheta hS ν (fun i ↦ ∫ x, S i x ∂ν) 0) = ν := by
    rw [atlasTheta_zero, Submodule.coe_zero, familyMeasure_one_zero]
  rw [h0] at hreg
  refine ⟨a, ha, hreg, ?_⟩
  obtain ⟨M, hM⟩ : ∃ M : ℝ → J → ℝ, M = tiltResponse S ν f := ⟨_, rfl⟩
  obtain ⟨N, hN⟩ : ∃ N : ℝ → J → ℝ, N = tiltResponse S ν (dirLoss S a) := ⟨_, rfl⟩
  obtain ⟨u, hu⟩ : ∃ u : J → ℝ, u = fun j ↦ lawCov ν (S j) f := ⟨_, rfl⟩
  have hga : Bdd (dirLoss S a) := bdd_dirLoss hS a
  -- the two responses have the same velocity
  have hMd : HasDerivAt M u 0 := by
    rw [hM, hu]
    exact hasDerivAt_tiltResponse hS ν hf
  have hNd : HasDerivAt N u 0 := by
    rw [hN, hu]
    have h := hasDerivAt_tiltResponse hS ν hga
    refine h.congr_deriv ?_
    funext j
    exact hreg j
  have hM0 : M 0 = N 0 := by
    rw [hM, hN, tiltResponse_zero, tiltResponse_zero]
  -- `M − N = o(t)`
  have hMN : (fun t ↦ M t - N t) =o[𝓝 0] fun t ↦ t := by
    have h := hasDerivAt_iff_isLittleO.1 (hMd.sub hNd)
    simp only [sub_self, sub_zero, smul_zero, Pi.sub_apply, hM0] at h
    exact h
  -- `θ(M_t) = O(t)`
  have hθ := isBigO_responseTheta_tiltResponse hS ν hf
  rw [← hM] at hθ
  -- `M_t` is eventually interior
  have hint : ∀ᶠ t in 𝓝 0, M t ∈ intrinsicInterior ℝ (momentBody ν (fun _ ↦ (1 : ℝ)) S) := by
    refine eventually_mem_intrinsicInterior_of_tendsto_filter (Eventually.of_forall fun t ↦ ?_)
      ?_ hMd.continuousAt.tendsto
    · rw [hM]
      exact mem_momentBody_of_genRate_ne_top hS ν (genRate_tiltResponse_ne_top hS ν hf t)
    · rw [hM, tiltResponse_zero, ← meanMap_zero_eq_mean ν,
        ← range_meanMap_eq_intrinsicInterior_momentBody measurable_const (integrable_const 1)
          (fun _ ↦ one_pos) (one_integral_pos ν) hS]
      exact ⟨0, rfl⟩
  -- the sandwich
  obtain ⟨I, hI⟩ : ∃ I : ℝ → ℝ, I = fun t ↦ (genRate ν S (M t)).toReal := ⟨_, rfl⟩
  obtain ⟨I', hI'⟩ : ∃ I' : ℝ → ℝ, I' = fun t ↦ (genRate ν S (N t)).toReal := ⟨_, rfl⟩
  have hlow : ∀ t, I' t + t * dotJ a (M t - N t) ≤ I t := fun t ↦ by
    rw [hI, hI', hM, hN]
    exact genRate_tiltResponse_dirLoss_add_le hS ν hf a t
  have hupp : ∀ᶠ t in 𝓝 0, I t ≤ I' t +
      dotJ (responseTheta measurable_const (integrable_const 1) (fun _ ↦ one_pos)
        (one_integral_pos ν) hS (M t) : J → ℝ) (N t - M t) := by
    filter_upwards [hint] with t ht
    have h := toReal_klDiv_responseProjection_interior hS ν
      (hN ▸ genRate_tiltResponse_ne_top hS ν hga t) ht
    have hnn : 0 ≤ (klDiv (responseProjection hS ν (N t)) (responseProjection hS ν (M t))).toReal :=
      ENNReal.toReal_nonneg
    rw [hI, hI']
    linarith
  -- the error is `o(t²)`
  have hE : (fun t ↦ I t - I' t) =o[𝓝 0] fun t ↦ t ^ 2 := by
    have hA : (fun t ↦ t * ‖M t - N t‖) =o[𝓝 0] fun t ↦ t ^ 2 := by
      have h := (isBigO_refl (fun t : ℝ ↦ t) (𝓝 0)).mul_isLittleO (isLittleO_norm_left.2 hMN)
      refine h.congr_right fun t ↦ ?_
      ring
    have hB : (fun t ↦ ‖(responseTheta measurable_const (integrable_const 1) (fun _ ↦ one_pos)
        (one_integral_pos ν) hS (M t) : J → ℝ)‖ * ‖N t - M t‖) =o[𝓝 0] fun t ↦ t ^ 2 := by
      have h := hθ.mul_isLittleO (isLittleO_norm_left.2 hMN.neg_left)
      refine (h.congr_right fun t ↦ ?_).congr_left fun t ↦ ?_
      · ring
      · rw [neg_sub]
    have hsum := (isLittleO_norm_left.2 hA).add (isLittleO_norm_left.2 hB)
    refine IsBigO.trans_isLittleO ?_ hsum
    refine IsBigO.of_bound ((∑ j, |a j|) + Fintype.card J) ?_
    filter_upwards [hupp] with t ht
    have hl := hlow t
    have h1 : |t * dotJ a (M t - N t)| ≤ (∑ j, |a j|) * ‖t * ‖M t - N t‖‖ := by
      rw [abs_mul, Real.norm_eq_abs, abs_mul, abs_norm]
      have := abs_dotJ_le a (M t - N t)
      have h0 : 0 ≤ ∑ j, |a j| := Finset.sum_nonneg fun j _ ↦ abs_nonneg _
      nlinarith [abs_nonneg t, norm_nonneg (M t - N t)]
    have h2 : |dotJ (responseTheta measurable_const (integrable_const 1) (fun _ ↦ one_pos)
        (one_integral_pos ν) hS (M t) : J → ℝ) (N t - M t)| ≤
        (Fintype.card J : ℝ) * ‖‖(responseTheta measurable_const (integrable_const 1)
          (fun _ ↦ one_pos) (one_integral_pos ν) hS (M t) : J → ℝ)‖ * ‖N t - M t‖‖ := by
      rw [Real.norm_eq_abs, abs_mul, abs_norm, abs_norm, ← mul_assoc]
      exact abs_dotJ_le_card_mul _ _
    rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg
      (add_nonneg (norm_nonneg _) (norm_nonneg _))]
    have hc0 : 0 ≤ (Fintype.card J : ℝ) := Nat.cast_nonneg _
    have ha0 : 0 ≤ ∑ j, |a j| := Finset.sum_nonneg fun j _ ↦ abs_nonneg _
    rw [abs_le]
    constructor
    · nlinarith [abs_le.1 h1, abs_le.1 h2, norm_nonneg (t * ‖M t - N t‖),
        norm_nonneg (‖(responseTheta measurable_const (integrable_const 1) (fun _ ↦ one_pos)
          (one_integral_pos ν) hS (M t) : J → ℝ)‖ * ‖N t - M t‖)]
    · nlinarith [abs_le.1 h1, abs_le.1 h2, norm_nonneg (t * ‖M t - N t‖),
        norm_nonneg (‖(responseTheta measurable_const (integrable_const 1) (fun _ ↦ one_pos)
          (one_integral_pos ν) hS (M t) : J → ℝ)‖ * ‖N t - M t‖)]
  -- assemble the limit
  have hI'lim : Tendsto (fun t ↦ I' t / t ^ 2) (𝓝[≠] 0) (𝓝 (dotJ a u / 2)) := by
    have h := tendsto_klDiv_tilted_div_sq ν hga
    have hvar : lawCov ν (dirLoss S a) (dirLoss S a) = dotJ a u := by
      rw [lawCov_dirLoss_left hS ν a _ hga, hu]
      simp only [dotJ]
      exact Finset.sum_congr rfl fun j _ ↦ by rw [hreg j]
    rw [hvar] at h
    refine h.congr fun t ↦ ?_
    simp only [hI', hN, genRate_tiltResponse_dirLoss_toReal hS ν]
  have hElim : Tendsto (fun t ↦ (I t - I' t) / t ^ 2) (𝓝[≠] 0) (𝓝 0) :=
    (hE.mono nhdsWithin_le_nhds).tendsto_div_nhds_zero
  have h := hI'lim.add hElim
  rw [add_zero] at h
  rw [← hM, ← hu]
  refine h.congr fun t ↦ ?_
  simp only [hI, hI']
  rw [← add_div]
  congr 1
  ring

end Main

end Laplace.Multi
