/-
Copyright (c) 2026 Timaeus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Timaeus
-/
import Mathlib
import Laplace.Multi.PathEnergy
import Laplace.Multi.VisibleBudget
import Laplace.Multi.EndpointTail

/-!
# The Fisher energy of the atlas path

For an interior response `M` with natural coordinates `θ`, along the straight atlas path
`M_s = (1−s)m₀ + sM` with curvature `κ(s) = Var_{P_{θ_s}}⟨θ_s', S⟩`:

* the endpoint slope is continuous: `−⟨θ_s, M − m₀⟩ → −⟨θ, M − m₀⟩` as `s → 1⁻`
  (`tendsto_neg_dotJ_atlasTheta`; from the two Bregman identities between atlas points, no
  continuity of the inverse chart is needed);
* the curvature is integrable on `(0,1)` and `∫₀¹ κ = −⟨θ, M − m₀⟩`
  (`integral_atlasCurv_eq_neg_dotJ`);
* hence `KL(ν ‖ Π(M)) = ∫₀¹ s κ(s) ds`, the companion of
  `𝓘(M) = KL(Π(M) ‖ ν) = ∫₀¹ (1−s) κ(s) ds`
  (`toReal_klDiv_featureless_responseProjection_eq_integral`), and the Fisher energy of the atlas
  path equals the symmetrised divergence between its endpoints and the Fisher energy of the
  exponential path `s ↦ P_{sθ}` (`integral_atlasCurv_eq_symm_klDiv`,
  `integral_atlasCurv_eq_integral_var_segment`): the two straight paths from the featureless
  posterior to the representative, in response and in natural coordinates, have the same energy.
-/

open MeasureTheory Filter Topology Set InformationTheory
open scoped ENNReal

namespace Laplace.Multi

/-- The truncation sequence `r_n = 1 − 1/(n+1)`. -/
theorem tendsto_one_sub_one_div_nat :
    Tendsto (fun n : ℕ ↦ (1 : ℝ) - 1 / ((n : ℝ) + 1)) atTop (𝓝 1) := by
  have := (tendsto_const_nhds (x := (1 : ℝ))).sub tendsto_one_div_add_atTop_nhds_zero_nat
  simpa using this

variable {X : Type*} [MeasurableSpace X] [Nonempty X] {J : Type*} [Fintype J] [Nonempty J]
  {S : J → X → ℝ} (hS : ∀ j, Bdd (S j)) (ν : Measure X) [IsProbabilityMeasure ν] {M : J → ℝ}
  (hfin : genRate ν S M ≠ ⊤)
include hS hfin

omit hfin in
theorem atlasTheta_one :
    atlasTheta hS ν M 1 = responseTheta measurable_const (integrable_const 1) (fun _ ↦ one_pos)
      (one_integral_pos ν) hS M := by
  unfold atlasTheta
  rw [atlasPath_one]

omit [Nonempty X] [Nonempty J] hS [IsProbabilityMeasure ν] hfin in
/-- The atlas path as a line in the visible subspace. -/
theorem atlasPath_eq_add_smul (hΔ : M - meanMap ν (fun _ ↦ (1 : ℝ)) (fun _ ↦ (0 : ℝ)) S 1 0 ∈
    dirSpan ν (fun _ ↦ (1 : ℝ)) S) (s : ℝ) :
    atlasPath S ν M s = meanMap ν (fun _ ↦ (1 : ℝ)) (fun _ ↦ (0 : ℝ)) S 1 0 +
      ((s • (⟨_, hΔ⟩ : dirSpan ν (fun _ ↦ (1 : ℝ)) S)) : J → ℝ) := by
  change atlasPath S ν M s = meanMap ν (fun _ ↦ (1 : ℝ)) (fun _ ↦ (0 : ℝ)) S 1 0 +
    s • (M - meanMap ν (fun _ ↦ (1 : ℝ)) (fun _ ↦ (0 : ℝ)) S 1 0)
  rw [atlasPath_eq_sub]
  module

omit hfin in
/-- **The rate is differentiable at the interior endpoint of the atlas path**, with derivative
`−⟨θ(M), M − m₀⟩`. -/
theorem hasDerivAt_genRate_atlasPath_one
    (hrel : M ∈ intrinsicInterior ℝ (momentBody ν (fun _ ↦ (1 : ℝ)) S)) :
    HasDerivAt (fun s ↦ (genRate ν S (atlasPath S ν M s)).toReal)
      (-dotJ (atlasTheta hS ν M 1 : J → ℝ)
        (M - meanMap ν (fun _ ↦ (1 : ℝ)) (fun _ ↦ (0 : ℝ)) S 1 0)) 1 := by
  have hΔ := sub_mem_dirSpan_of_mem_momentBody measurable_const (integrable_const 1)
    (fun _ ↦ one_pos) (one_integral_pos ν) hS (intrinsicInterior_subset hrel)
  obtain ⟨Δ, hΔdef⟩ : ∃ Δ : dirSpan ν (fun _ ↦ (1 : ℝ)) S, Δ = ⟨_, hΔ⟩ := ⟨_, rfl⟩
  have hG := hasFDerivAt_genRate_chart hS ν (responseTheta measurable_const (integrable_const 1)
    (fun _ ↦ one_pos) (one_integral_pos ν) hS M)
  rw [chartV_responseTheta measurable_const (integrable_const 1) (fun _ ↦ one_pos)
    (one_integral_pos ν) hS hrel] at hG
  have htoV : toV ν (fun _ ↦ (1 : ℝ)) S M = Δ := by
    rw [hΔdef]
    exact Subtype.ext (toV_apply hΔ)
  rw [htoV] at hG
  have hline : HasDerivAt (fun s : ℝ ↦ s • Δ) Δ 1 := by
    simpa using (hasDerivAt_id' (x := (1 : ℝ))).smul_const Δ
  have h1 : (fun s : ℝ ↦ s • Δ) 1 = Δ := by simp
  rw [← h1] at hG
  have h := hG.comp_hasDerivAt (1 : ℝ) hline
  have e : (fun v : dirSpan ν (fun _ ↦ (1 : ℝ)) S ↦
      (genRate ν S (meanMap ν (fun _ ↦ (1 : ℝ)) (fun _ ↦ (0 : ℝ)) S 1 0 + v)).toReal) ∘
        (fun s : ℝ ↦ s • Δ) = fun s ↦ (genRate ν S (atlasPath S ν M s)).toReal := by
    funext s
    simp only [Function.comp]
    rw [atlasPath_eq_add_smul ν hΔ s, hΔdef, Submodule.coe_smul]
  rw [e] at h
  refine h.congr_deriv ?_
  rw [atlasTheta_one hS ν, hΔdef]
  simp only [neg_apply, ContinuousLinearMap.comp_apply,
    Submodule.subtypeL_apply, dotCLM_apply, dotJ_comm]

/-- The endpoint slope dominates the interior slopes: `−⟨θ_s, Δ⟩ ≤ −⟨θ(M), Δ⟩` for `s ∈ [0,1)`. -/
theorem neg_dotJ_atlasTheta_le_one
    (hrel : M ∈ intrinsicInterior ℝ (momentBody ν (fun _ ↦ (1 : ℝ)) S)) {s : ℝ} (hs0 : 0 ≤ s)
    (hs1 : s < 1) :
    -dotJ (atlasTheta hS ν M s : J → ℝ) (M - meanMap ν (fun _ ↦ (1 : ℝ)) (fun _ ↦ (0 : ℝ)) S 1 0) ≤
      -dotJ (atlasTheta hS ν M 1 : J → ℝ)
        (M - meanMap ν (fun _ ↦ (1 : ℝ)) (fun _ ↦ (0 : ℝ)) S 1 0) := by
  have h1 := toReal_klDiv_responseProjection_atlas hS ν hfin hs0 hs1
  have h1nn : 0 ≤ (klDiv (responseProjection hS ν M)
    (responseProjection hS ν (atlasPath S ν M s))).toReal := ENNReal.toReal_nonneg
  have hfs := genRate_ne_top_of_mem_intrinsicInterior hS ν
    (atlas_mem_intrinsicInterior hS ν hfin hs0 hs1)
  have h2 := toReal_klDiv_responseProjection_interior hS ν hfs hrel
  have h2nn : 0 ≤ (klDiv (responseProjection hS ν (atlasPath S ν M s))
    (responseProjection hS ν M)).toReal := ENNReal.toReal_nonneg
  rw [← atlasTheta_one hS ν] at h2
  have hdiff : atlasPath S ν M s - M =
      (-(1 - s)) • (M - meanMap ν (fun _ ↦ (1 : ℝ)) (fun _ ↦ (0 : ℝ)) S 1 0) := by
    rw [atlasPath_eq_sub]
    module
  rw [hdiff, (isLinearMap_dotJ _).map_smul, smul_eq_mul] at h2
  have hs' : 0 < 1 - s := by linarith
  nlinarith

/-- The chord slopes are dominated by the slope at the right end: for `0 ≤ s' < s < 1`,
`(𝓘(M_s) − 𝓘(M_{s'}))/(s − s') ≤ −⟨θ_s, Δ⟩`. -/
theorem slope_le_neg_dotJ_atlasTheta {s' s : ℝ} (hs'0 : 0 ≤ s') (hss' : s' < s) (hs1 : s < 1) :
    ((genRate ν S (atlasPath S ν M s)).toReal - (genRate ν S (atlasPath S ν M s')).toReal) /
        (s - s') ≤
      -dotJ (atlasTheta hS ν M s : J → ℝ)
        (M - meanMap ν (fun _ ↦ (1 : ℝ)) (fun _ ↦ (0 : ℝ)) S 1 0) := by
  have hfs' := genRate_ne_top_of_mem_intrinsicInterior hS ν
    (atlas_mem_intrinsicInterior hS ν hfin hs'0 (hss'.trans hs1))
  have hrels := atlas_mem_intrinsicInterior hS ν hfin (hs'0.trans hss'.le) hs1
  have h := toReal_klDiv_responseProjection_interior hS ν hfs' hrels
  have hnn : 0 ≤ (klDiv (responseProjection hS ν (atlasPath S ν M s'))
    (responseProjection hS ν (atlasPath S ν M s))).toReal := ENNReal.toReal_nonneg
  have hdiff : atlasPath S ν M s' - atlasPath S ν M s =
      (s' - s) • (M - meanMap ν (fun _ ↦ (1 : ℝ)) (fun _ ↦ (0 : ℝ)) S 1 0) := by
    unfold atlasPath
    module
  rw [hdiff, (isLinearMap_dotJ _).map_smul, smul_eq_mul] at h
  have hθ : (responseTheta measurable_const (integrable_const 1) (fun _ ↦ one_pos)
    (one_integral_pos ν) hS (atlasPath S ν M s) : J → ℝ) = (atlasTheta hS ν M s : J → ℝ) := rfl
  rw [hθ] at h
  rw [div_le_iff₀ (by linarith)]
  nlinarith

/-- **Continuity of the endpoint slope**: `−⟨θ_s, Δ⟩ → −⟨θ(M), Δ⟩` as `s → 1⁻`. -/
theorem tendsto_neg_dotJ_atlasTheta
    (hrel : M ∈ intrinsicInterior ℝ (momentBody ν (fun _ ↦ (1 : ℝ)) S)) :
    Tendsto (fun s ↦ -dotJ (atlasTheta hS ν M s : J → ℝ)
        (M - meanMap ν (fun _ ↦ (1 : ℝ)) (fun _ ↦ (0 : ℝ)) S 1 0)) (𝓝[<] 1)
      (𝓝 (-dotJ (atlasTheta hS ν M 1 : J → ℝ)
        (M - meanMap ν (fun _ ↦ (1 : ℝ)) (fun _ ↦ (0 : ℝ)) S 1 0))) := by
  obtain ⟨f, hf⟩ : ∃ f : ℝ → ℝ, f = fun s ↦ (genRate ν S (atlasPath S ν M s)).toReal := ⟨_, rfl⟩
  obtain ⟨c, hc⟩ : ∃ c : ℝ, c = -dotJ (atlasTheta hS ν M 1 : J → ℝ)
    (M - meanMap ν (fun _ ↦ (1 : ℝ)) (fun _ ↦ (0 : ℝ)) S 1 0) := ⟨_, rfl⟩
  have hB := hasDerivAt_genRate_atlasPath_one hS ν hrel
  rw [← hf, ← hc] at hB
  have hslope : Tendsto (fun s ↦ (f 1 - f s) / (1 - s)) (𝓝[<] 1) (𝓝 c) := by
    have h := (hasDerivAt_iff_tendsto_slope.1 hB).mono_left
      (nhdsWithin_mono _ fun x (hx : x < 1) ↦ (ne_of_lt hx : x ≠ 1))
    refine h.congr fun s ↦ ?_
    rw [slope_def_field, ← neg_sub (f 1), ← neg_sub (1 : ℝ), neg_div_neg_eq]
  rw [← hc]
  refine tendsto_order.2 ⟨fun y hy ↦ ?_, fun y hy ↦ ?_⟩
  · -- eventually `y < −⟨θ_s, Δ⟩`: pick a chord with slope above `y`, then dominate
    have h01 : ∀ᶠ s in 𝓝[<] (1 : ℝ), s ∈ Ioo (0 : ℝ) 1 := Ioo_mem_nhdsLT (zero_lt_one' ℝ)
    obtain ⟨s', hs', hy'⟩ := (h01.and ((tendsto_order.1 hslope).1 y hy)).exists
    have hlim : Tendsto (fun s ↦ (f s - f s') / (s - s')) (𝓝[<] 1)
        (𝓝 ((f 1 - f s') / (1 - s'))) := by
      refine ((hB.continuousAt.tendsto.sub tendsto_const_nhds).div
        (tendsto_id.sub tendsto_const_nhds) (sub_ne_zero.2 hs'.2.ne')).mono_left
        nhdsWithin_le_nhds
    filter_upwards [Ioo_mem_nhdsLT hs'.2, (tendsto_order.1 hlim).1 y hy'] with s hs hys
    refine lt_of_lt_of_le hys ?_
    rw [hf]
    exact slope_le_neg_dotJ_atlasTheta hS ν hfin hs'.1.le hs.1 hs.2
  · filter_upwards [Ioo_mem_nhdsLT (zero_lt_one' ℝ)] with s hs
    exact lt_of_le_of_lt (neg_dotJ_atlasTheta_le_one hS ν hfin hrel hs.1.le hs.2) (hc ▸ hy)

/-- **The curvature is integrable on `(0,1)`** when the endpoint is interior. -/
theorem integrableOn_atlasCurv
    (hrel : M ∈ intrinsicInterior ℝ (momentBody ν (fun _ ↦ (1 : ℝ)) S)) :
    IntegrableOn (atlasCurv hS ν hfin) (Ioo (0 : ℝ) 1) := by
  obtain ⟨r, hr⟩ : ∃ r : ℕ → ℝ, r = fun n : ℕ ↦ (1 : ℝ) - 1 / ((n : ℝ) + 1) := ⟨_, rfl⟩
  have hr0 : ∀ n, 0 ≤ r n := fun n ↦ by
    rw [hr]
    have : (1 : ℝ) / ((n : ℝ) + 1) ≤ 1 := by
      rw [div_le_one (by positivity)]
      linarith [(n.cast_nonneg : (0 : ℝ) ≤ n)]
    linarith
  have hr1 : ∀ n, r n < 1 := fun n ↦ by
    rw [hr]
    have : (0 : ℝ) < 1 / ((n : ℝ) + 1) := by positivity
    linarith
  have hrlim : Tendsto r atTop (𝓝 1) := by
    rw [hr]
    exact tendsto_one_sub_one_div_nat
  have hcont : ∀ n, ContinuousOn (atlasCurv hS ν hfin) (Icc 0 (r n)) := fun n s hs ↦
    (continuousAt_atlasCurv hS ν hfin hs.1 (lt_of_le_of_lt hs.2 (hr1 n))).continuousWithinAt
  have hfi : ∀ n, IntegrableOn (atlasCurv hS ν hfin) (Ioc 0 (r n)) := fun n ↦
    ((hcont n).integrableOn_Icc).mono_set Ioc_subset_Icc_self
  refine (integrableOn_Ioc_of_intervalIntegral_norm_bounded_right
    (I := -dotJ (atlasTheta hS ν M 1 : J → ℝ)
      (M - meanMap ν (fun _ ↦ (1 : ℝ)) (fun _ ↦ (0 : ℝ)) S 1 0)) hfi hrlim
    (Eventually.of_forall fun n ↦ ?_)).mono_set Ioo_subset_Ioc_self
  have e : ∫ x in Ioc 0 (r n), ‖atlasCurv hS ν hfin x‖ =
      ∫ x in (0 : ℝ)..r n, atlasCurv hS ν hfin x := by
    rw [intervalIntegral.integral_of_le (hr0 n)]
    refine setIntegral_congr_fun measurableSet_Ioc fun x _ ↦ ?_
    exact Real.norm_of_nonneg (atlasCurv_nonneg hS ν hfin x)
  rw [e, ← neg_dotJ_atlasTheta_eq_integral hS ν hfin (hr0 n) (hr1 n)]
  exact neg_dotJ_atlasTheta_le_one hS ν hfin hrel (hr0 n) (hr1 n)

/-- **The Fisher energy of the atlas path**: `∫₀¹ κ = −⟨θ(M), M − m₀⟩`. -/
theorem integral_atlasCurv_eq_neg_dotJ
    (hrel : M ∈ intrinsicInterior ℝ (momentBody ν (fun _ ↦ (1 : ℝ)) S)) :
    ∫ s in Ioo (0 : ℝ) 1, atlasCurv hS ν hfin s =
      -dotJ (atlasTheta hS ν M 1 : J → ℝ)
        (M - meanMap ν (fun _ ↦ (1 : ℝ)) (fun _ ↦ (0 : ℝ)) S 1 0) := by
  obtain ⟨r, hr⟩ : ∃ r : ℕ → ℝ, r = fun n : ℕ ↦ (1 : ℝ) - 1 / ((n : ℝ) + 1) := ⟨_, rfl⟩
  have hr0 : ∀ n, 0 ≤ r n := fun n ↦ by
    rw [hr]
    have : (1 : ℝ) / ((n : ℝ) + 1) ≤ 1 := by
      rw [div_le_one (by positivity)]
      linarith [(n.cast_nonneg : (0 : ℝ) ≤ n)]
    linarith
  have hr1 : ∀ n, r n < 1 := fun n ↦ by
    rw [hr]
    have : (0 : ℝ) < 1 / ((n : ℝ) + 1) := by positivity
    linarith
  have hrlim : Tendsto r atTop (𝓝 1) := by
    rw [hr]
    exact tendsto_one_sub_one_div_nat
  have hrmono : Monotone r := by
    intro m n hmn
    rw [hr]
    have : (1 : ℝ) / ((n : ℝ) + 1) ≤ 1 / ((m : ℝ) + 1) :=
      one_div_le_one_div_of_le (by positivity) (by exact_mod_cast Nat.add_le_add_right hmn 1)
    linarith
  have hunion : (⋃ n, Ioo (0 : ℝ) (r n)) = Ioo 0 1 := by
    ext x
    simp only [mem_iUnion, mem_Ioo]
    constructor
    · rintro ⟨n, hx0, hxn⟩
      exact ⟨hx0, hxn.trans (hr1 n)⟩
    · rintro ⟨hx0, hx1⟩
      obtain ⟨n, hn⟩ := exists_nat_gt (1 / (1 - x))
      refine ⟨n, hx0, ?_⟩
      rw [hr]
      have h1x : 0 < 1 - x := by linarith
      have : 1 / ((n : ℝ) + 1) < 1 - x := by
        rw [div_lt_iff₀ (by positivity)]
        have := (div_lt_iff₀ h1x).1 hn
        nlinarith
      linarith
  have hint := integrableOn_atlasCurv hS ν hfin hrel
  rw [← hunion] at hint
  have hlim1 := tendsto_setIntegral_of_monotone (fun n ↦ measurableSet_Ioo)
    (fun m n hmn ↦ Ioo_subset_Ioo le_rfl (hrmono hmn)) hint
  rw [hunion] at hlim1
  have hlim2 : Tendsto (fun n ↦ ∫ s in Ioo (0 : ℝ) (r n), atlasCurv hS ν hfin s) atTop
      (𝓝 (-dotJ (atlasTheta hS ν M 1 : J → ℝ)
        (M - meanMap ν (fun _ ↦ (1 : ℝ)) (fun _ ↦ (0 : ℝ)) S 1 0))) := by
    have h := (tendsto_neg_dotJ_atlasTheta hS ν hfin hrel).comp
      (tendsto_nhdsWithin_iff.2 ⟨hrlim, Eventually.of_forall hr1⟩)
    refine h.congr fun n ↦ ?_
    simp only [Function.comp]
    rw [neg_dotJ_atlasTheta_eq_integral hS ν hfin (hr0 n) (hr1 n),
      intervalIntegral.integral_of_le (hr0 n), integral_Ioc_eq_integral_Ioo]
  exact tendsto_nhds_unique hlim1 hlim2

/-- **`KL(ν ‖ Π(M)) = ∫₀¹ s κ(s) ds`**, the companion of `𝓘(M) = ∫₀¹ (1 − s) κ(s) ds`. -/
theorem toReal_klDiv_featureless_responseProjection_eq_integral
    (hrel : M ∈ intrinsicInterior ℝ (momentBody ν (fun _ ↦ (1 : ℝ)) S)) :
    (klDiv ν (responseProjection hS ν M)).toReal =
      ∫ s in Ioo (0 : ℝ) 1, s * atlasCurv hS ν hfin s := by
  have hsymm := toReal_klDiv_familyMeasure_symm hS ν
    (responseTheta measurable_const (integrable_const 1) (fun _ ↦ one_pos) (one_integral_pos ν)
      hS M : J → ℝ)
  rw [meanMap_responseTheta measurable_const (integrable_const 1) (fun _ ↦ one_pos)
    (one_integral_pos ν) hS hrel, ← responseProjection_eq_familyMeasure_responseTheta hS ν hrel,
    ← atlasTheta_one hS ν, ← integral_atlasCurv_eq_neg_dotJ hS ν hfin hrel] at hsymm
  obtain ⟨-, -, hQkl, -⟩ := responseProjection_spec hS ν hfin
  rw [hQkl, genRate_toReal_eq_integral_atlasCurv hS ν hfin] at hsymm
  have e : ∫ s in Ioo (0 : ℝ) 1, s * atlasCurv hS ν hfin s =
      (∫ s in Ioo (0 : ℝ) 1, atlasCurv hS ν hfin s) -
        ∫ s in Ioo (0 : ℝ) 1, (1 - s) * atlasCurv hS ν hfin s := by
    rw [← integral_sub (integrableOn_atlasCurv hS ν hfin hrel)
      (integrableOn_atlasCurv_weighted hS ν hfin)]
    refine integral_congr_ae (Eventually.of_forall fun s ↦ ?_)
    ring
  rw [e]
  linarith

/-- **The Fisher energy of the atlas path is the symmetrised divergence** between its endpoints. -/
theorem integral_atlasCurv_eq_symm_klDiv
    (hrel : M ∈ intrinsicInterior ℝ (momentBody ν (fun _ ↦ (1 : ℝ)) S)) :
    ∫ s in Ioo (0 : ℝ) 1, atlasCurv hS ν hfin s =
      (klDiv (responseProjection hS ν M) ν).toReal +
        (klDiv ν (responseProjection hS ν M)).toReal := by
  have hsymm := toReal_klDiv_familyMeasure_symm hS ν
    (responseTheta measurable_const (integrable_const 1) (fun _ ↦ one_pos) (one_integral_pos ν)
      hS M : J → ℝ)
  rw [meanMap_responseTheta measurable_const (integrable_const 1) (fun _ ↦ one_pos)
    (one_integral_pos ν) hS hrel, ← responseProjection_eq_familyMeasure_responseTheta hS ν hrel,
    ← atlasTheta_one hS ν, ← integral_atlasCurv_eq_neg_dotJ hS ν hfin hrel] at hsymm
  exact hsymm.symm

/-- **Equal Fisher energies**: the atlas path (straight in response coordinates) and the
exponential path (straight in natural coordinates) from `ν` to `Π(M)` have the same energy. -/
theorem integral_atlasCurv_eq_integral_var_segment
    (hrel : M ∈ intrinsicInterior ℝ (momentBody ν (fun _ ↦ (1 : ℝ)) S)) :
    ∫ s in Ioo (0 : ℝ) 1, atlasCurv hS ν hfin s =
      ∫ s in (0 : ℝ)..1, lawCov (familyMeasure ν (fun _ ↦ (1 : ℝ)) (fun _ ↦ (0 : ℝ)) S 1
        (s • (atlasTheta hS ν M 1 : J → ℝ)))
        (dirLoss S (atlasTheta hS ν M 1 : J → ℝ)) (dirLoss S (atlasTheta hS ν M 1 : J → ℝ)) := by
  rw [integral_atlasCurv_eq_symm_klDiv hS ν hfin hrel,
    integral_var_familyMeasure_segment_eq_symm_klDiv hS ν, atlasTheta_one hS ν,
    ← responseProjection_eq_familyMeasure_responseTheta hS ν hrel]

end Laplace.Multi
