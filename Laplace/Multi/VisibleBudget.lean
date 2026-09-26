/-
Copyright (c) 2026 Timaeus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Timaeus
-/
import Laplace.Multi.ProjectionPythagoras

/-!
# The visible information as an integral of the dual-Fisher energy over the whole bridge

`StraightPathAtlas` gives the truncated budget `𝓘(M_r) = ∫₀ʳ (r − s) κ(s) ds` for `r < 1`. This file
passes to the endpoint: for a response `M` of finite rate, with `κ(s) = ⟨Δ, C_{θ_s}⁻¹ Δ⟩` the
curvature along the straight path,

  `𝓘(M) = ∫₀¹ (1 − s) κ(s) ds`
  (`genRate_eq_lintegral_atlasCurv`, `genRate_toReal_eq_integral_atlasCurv`),

as an identity in `ℝ≥0∞` and as a Bochner integral over `Ioo 0 1`; the weighted curvature is
integrable (`integrableOn_atlasCurv_weighted`). The key inequality is the convexity gap
`(1 − r)·(−⟨θ_r, Δ⟩) ≤ 𝓘(M) − 𝓘(M_r)` (`gap_ge_atlasVelocity`), read off from the Chernoff
supremum at the natural coordinate of `M_r`: it shows that the truncated integrals
`∫₀ʳ (1 − s) κ(s) ds = 𝓘(M_r) + (1 − r)(−⟨θ_r, Δ⟩)` are squeezed between `𝓘(M_r)` and `𝓘(M)`, and
monotone convergence does the rest.
-/

open MeasureTheory Filter Topology Set InformationTheory
open scoped ENNReal

namespace Laplace.Multi

variable {X : Type*} [MeasurableSpace X] [Nonempty X] {J : Type*} [Fintype J] [Nonempty J]
  {S : J → X → ℝ} (hS : ∀ j, Bdd (S j)) (ν : Measure X) [IsProbabilityMeasure ν] {M : J → ℝ}

omit [Nonempty X] [Nonempty J] [IsProbabilityMeasure ν] in
/-- The featureless log-partition function is the cumulant generating function at `−θ`. -/
theorem affLogZ_one_zero_eq_featCgf (θ : J → ℝ) :
    affLogZ ν (fun _ ↦ (1 : ℝ)) (fun _ ↦ (0 : ℝ)) S 1 θ = featCgf ν S (-θ) := by
  unfold affLogZ priorZ featCgf
  congr 1
  refine integral_congr_ae (Eventually.of_forall fun x ↦ ?_)
  simp [affLoss, dirLoss, Finset.sum_neg_distrib]

variable (hfin : genRate ν S M ≠ ⊤)
include hS hfin

/-- The rate of a path point in Chernoff form at its own natural coordinate. -/
theorem genRate_atlasPath_toReal_eq {r : ℝ} (hr0 : 0 ≤ r) (hr1 : r < 1) :
    (genRate ν S (atlasPath S ν M r)).toReal =
      dotJ (-(atlasTheta hS ν M r : J → ℝ)) (atlasPath S ν M r) -
        featCgf ν S (-(atlasTheta hS ν M r : J → ℝ)) := by
  have h0 : ∀ x, |(fun _ : X ↦ (0 : ℝ)) x| ≤ 0 := fun x ↦ by simp
  have hm := meanMap_responseTheta measurable_const (integrable_const 1) (fun _ ↦ one_pos)
    (one_integral_pos ν) hS (atlas_mem_intrinsicInterior hS ν hfin hr0 hr1)
  unfold atlasTheta
  conv_lhs => rw [← hm]
  rw [genRate_eq_rateFun, rateFun_meanMap measurable_const (integrable_const 1) (fun _ ↦ one_pos)
    (one_integral_pos ν) measurable_const h0 hS one_pos,
    ENNReal.toReal_ofReal (famKL_nonneg measurable_const (integrable_const 1) (fun _ ↦ one_pos)
      (one_integral_pos ν) measurable_const h0 hS one_pos _ _),
    famKL_eq measurable_const (integrable_const 1) (fun _ ↦ one_pos) (one_integral_pos ν)
      measurable_const h0 hS, affLogZ_one_zero_eq_featCgf, affLogZ_one_zero_eq_featCgf, neg_zero,
    featCgf_zero' ν, hm]
  simp only [dotJ, Pi.zero_apply, zero_sub, Pi.neg_apply, neg_mul, one_mul]
  ring

/-- **The convexity gap along the straight path**: `(1 − r)·(−⟨θ_r, Δ⟩) ≤ 𝓘(M) − 𝓘(M_r)`. -/
theorem gap_ge_atlasVelocity {r : ℝ} (hr0 : 0 ≤ r) (hr1 : r < 1) :
    (1 - r) * (-dotJ (atlasTheta hS ν M r : J → ℝ)
        (M - meanMap ν (fun _ ↦ (1 : ℝ)) (fun _ ↦ (0 : ℝ)) S 1 0)) ≤
      (genRate ν S M).toReal - (genRate ν S (atlasPath S ν M r)).toReal := by
  have h1 : ENNReal.ofReal (dotJ (-(atlasTheta hS ν M r : J → ℝ)) M -
      featCgf ν S (-(atlasTheta hS ν M r : J → ℝ))) ≤ genRate ν S M := by
    unfold genRate
    exact le_iSup (fun q ↦ ENNReal.ofReal (dotJ q M - featCgf ν S q)) _
  have h2 := (ENNReal.ofReal_le_iff_le_toReal hfin).1 h1
  rw [genRate_atlasPath_toReal_eq hS ν hfin hr0 hr1]
  have e : dotJ (-(atlasTheta hS ν M r : J → ℝ)) M -
      dotJ (-(atlasTheta hS ν M r : J → ℝ)) (atlasPath S ν M r) =
      (1 - r) * (-dotJ (atlasTheta hS ν M r : J → ℝ)
        (M - meanMap ν (fun _ ↦ (1 : ℝ)) (fun _ ↦ (0 : ℝ)) S 1 0)) := by
    rw [← (isLinearMap_dotJ _).map_sub, dotJ_neg_left,
      show M - atlasPath S ν M r =
          (1 - r) • (M - meanMap ν (fun _ ↦ (1 : ℝ)) (fun _ ↦ (0 : ℝ)) S 1 0) by
        unfold atlasPath; module,
      (isLinearMap_dotJ _).map_smul, smul_eq_mul]
    ring
  linarith

/-- The truncated weighted budget: `∫₀ʳ (1 − s) κ(s) ds = 𝓘(M_r) + (1 − r)(−⟨θ_r, Δ⟩)`. -/
theorem integral_one_sub_mul_atlasCurv {r : ℝ} (hr0 : 0 ≤ r) (hr1 : r < 1) :
    ∫ s in (0 : ℝ)..r, (1 - s) * atlasCurv hS ν hfin s =
      (genRate ν S (atlasPath S ν M r)).toReal +
        (1 - r) * (-dotJ (atlasTheta hS ν M r : J → ℝ)
          (M - meanMap ν (fun _ ↦ (1 : ℝ)) (fun _ ↦ (0 : ℝ)) S 1 0)) := by
  have hcurv : IntervalIntegrable (atlasCurv hS ν hfin) volume 0 r := by
    refine ContinuousOn.intervalIntegrable fun s hs ↦ ?_
    rw [uIcc_of_le hr0] at hs
    exact (continuousAt_atlasCurv hS ν hfin hs.1 (lt_of_le_of_lt hs.2 hr1)).continuousWithinAt
  rw [genRate_atlasPath_eq_integral hS ν hfin hr0 hr1,
    neg_dotJ_atlasTheta_eq_integral hS ν hfin hr0 hr1]
  have e : ∀ s, (1 - s) * atlasCurv hS ν hfin s =
      (r - s) * atlasCurv hS ν hfin s + (1 - r) * atlasCurv hS ν hfin s := fun s ↦ by ring
  simp_rw [e]
  have hA : IntervalIntegrable (fun s ↦ (r - s) * atlasCurv hS ν hfin s) volume 0 r :=
    hcurv.continuousOn_mul (by fun_prop)
  rw [intervalIntegral.integral_add hA (hcurv.const_mul _), intervalIntegral.integral_const_mul]

/-- Continuity of the weighted curvature on the closed sub-intervals of `[0, 1)`. -/
theorem continuousOn_atlasCurv_weighted {r : ℝ} (hr1 : r < 1) :
    ContinuousOn (fun s ↦ (1 - s) * atlasCurv hS ν hfin s) (Icc 0 r) := fun _ hs ↦
  ((continuous_const.sub continuous_id).continuousAt.mul
    (continuousAt_atlasCurv hS ν hfin hs.1 (lt_of_le_of_lt hs.2 hr1))).continuousWithinAt

/-- The truncated weighted budget in Lebesgue form. -/
theorem lintegral_Ioc_atlasCurv_weighted {r : ℝ} (hr0 : 0 ≤ r) (hr1 : r < 1) :
    ∫⁻ s in Ioc (0 : ℝ) r, ENNReal.ofReal ((1 - s) * atlasCurv hS ν hfin s) =
      ENNReal.ofReal (∫ s in (0 : ℝ)..r, (1 - s) * atlasCurv hS ν hfin s) := by
  rw [intervalIntegral.integral_of_le hr0, ofReal_integral_eq_lintegral_ofReal]
  · exact ((continuousOn_atlasCurv_weighted hS ν hfin hr1).integrableOn_Icc).mono_set
      Ioc_subset_Icc_self
  · rw [Filter.EventuallyLE, ae_restrict_iff' measurableSet_Ioc]
    filter_upwards with s hs
    exact mul_nonneg (by linarith [hs.2]) (atlasCurv_nonneg hS ν hfin s)

/-- **The visible information is the dual-Fisher energy of the whole bridge**, in `ℝ≥0∞`:
`𝓘(M) = ∫₀¹ (1 − s) κ(s) ds`. -/
theorem genRate_eq_lintegral_atlasCurv :
    genRate ν S M = ∫⁻ s in Ioo (0 : ℝ) 1, ENNReal.ofReal ((1 - s) * atlasCurv hS ν hfin s) := by
  -- the weighted curvature is measurable on `Ioo 0 1`
  have hcont : ContinuousOn (fun s ↦ (1 - s) * atlasCurv hS ν hfin s) (Ioo 0 1) := fun s hs ↦
    ((continuous_const.sub continuous_id).continuousAt.mul
      (continuousAt_atlasCurv hS ν hfin hs.1.le hs.2)).continuousWithinAt
  have hgm : AEMeasurable (fun s ↦ ENNReal.ofReal ((1 - s) * atlasCurv hS ν hfin s))
      (volume.restrict (Ioo (0 : ℝ) 1)) :=
    ENNReal.measurable_ofReal.comp_aemeasurable (hcont.aemeasurable measurableSet_Ioo)
  refine le_antisymm ?_ ?_
  · -- `𝓘(M) ≤ ∫⁻`: the truncated integrals dominate `𝓘(M_r)`, which tends to `𝓘(M)`
    refine le_of_tendsto (tendsto_genRate_segment hS ν hfin) ?_
    filter_upwards [Ioo_mem_nhdsLT (zero_lt_one' ℝ)] with r hr
    rw [← atlasPath_eq]
    have hfinr : genRate ν S (atlasPath S ν M r) ≠ ⊤ := by
      rw [atlasPath_eq]
      intro h
      have := genRate_segment_le hS ν hr.1.le hr.2.le (M := M)
      rw [h, top_le_iff, ENNReal.mul_eq_top] at this
      rcases this with ⟨-, h2⟩ | ⟨h1, -⟩
      · exact hfin h2
      · exact ENNReal.ofReal_ne_top h1
    have hv : 0 ≤ -dotJ (atlasTheta hS ν M r : J → ℝ)
        (M - meanMap ν (fun _ ↦ (1 : ℝ)) (fun _ ↦ (0 : ℝ)) S 1 0) := by
      rw [neg_dotJ_atlasTheta_eq_integral hS ν hfin hr.1.le hr.2]
      exact intervalIntegral.integral_nonneg hr.1.le fun s _ ↦ atlasCurv_nonneg hS ν hfin s
    calc genRate ν S (atlasPath S ν M r)
        = ENNReal.ofReal (genRate ν S (atlasPath S ν M r)).toReal :=
          (ENNReal.ofReal_toReal hfinr).symm
      _ ≤ ENNReal.ofReal (∫ s in (0 : ℝ)..r, (1 - s) * atlasCurv hS ν hfin s) := by
          refine ENNReal.ofReal_le_ofReal ?_
          rw [integral_one_sub_mul_atlasCurv hS ν hfin hr.1.le hr.2]
          nlinarith [hv, hr.2]
      _ = ∫⁻ s in Ioc (0 : ℝ) r, ENNReal.ofReal ((1 - s) * atlasCurv hS ν hfin s) :=
          (lintegral_Ioc_atlasCurv_weighted hS ν hfin hr.1.le hr.2).symm
      _ ≤ ∫⁻ s in Ioo (0 : ℝ) 1, ENNReal.ofReal ((1 - s) * atlasCurv hS ν hfin s) :=
          lintegral_mono_set fun s hs ↦ ⟨hs.1, lt_of_le_of_lt hs.2 hr.2⟩
  · -- `∫⁻ ≤ 𝓘(M)`: monotone convergence along `r_n = 1 − 1/(n + 2)`
    obtain ⟨g, hg⟩ : ∃ g : ℝ → ℝ≥0∞, g = fun s ↦ ENNReal.ofReal ((1 - s) * atlasCurv hS ν hfin s) :=
      ⟨_, rfl⟩
    rw [← hg] at hgm ⊢
    obtain ⟨r, hr⟩ : ∃ r : ℕ → ℝ, r = fun n : ℕ ↦ 1 - 1 / ((n : ℝ) + 2) := ⟨_, rfl⟩
    have hr0 : ∀ n, 0 ≤ r n := fun n ↦ by
      rw [hr]
      have : (1 : ℝ) / ((n : ℝ) + 2) ≤ 1 := by
        rw [div_le_one (by positivity)]
        linarith [(n.cast_nonneg : (0 : ℝ) ≤ n)]
      linarith
    have hr1 : ∀ n, r n < 1 := fun n ↦ by
      rw [hr]
      have : (0 : ℝ) < 1 / ((n : ℝ) + 2) := by positivity
      linarith
    have hmono : Monotone r := by
      intro m n hmn
      rw [hr]
      have : (1 : ℝ) / ((n : ℝ) + 2) ≤ 1 / ((m : ℝ) + 2) :=
        one_div_le_one_div_of_le (by positivity) (by exact_mod_cast Nat.add_le_add_right hmn 2)
      linarith
    obtain ⟨f, hf⟩ : ∃ f : ℕ → ℝ → ℝ≥0∞, f = fun n ↦ (Ioc (0 : ℝ) (r n)).indicator g := ⟨_, rfl⟩
    have hfm : ∀ n, AEMeasurable (f n) (volume.restrict (Ioo (0 : ℝ) 1)) := fun n ↦ by
      rw [hf]
      exact hgm.indicator measurableSet_Ioc
    have hfmono : ∀ᵐ s ∂volume.restrict (Ioo (0 : ℝ) 1), Monotone fun n ↦ f n s := by
      refine Eventually.of_forall fun s m n hmn ↦ ?_
      rw [hf]
      by_cases hs : s ∈ Ioc (0 : ℝ) (r m)
      · have hs' : s ∈ Ioc (0 : ℝ) (r n) := ⟨hs.1, hs.2.trans (hmono hmn)⟩
        simp only [Set.indicator_of_mem hs, Set.indicator_of_mem hs', le_refl]
      · simp only [Set.indicator_of_notMem hs, zero_le]
    have hsup : ∀ s ∈ Ioo (0 : ℝ) 1, ⨆ n, f n s = g s := by
      intro s hs
      obtain ⟨N, hN⟩ := exists_nat_one_div_lt (sub_pos.2 hs.2)
      have hsN : s ∈ Ioc (0 : ℝ) (r N) := by
        refine ⟨hs.1, ?_⟩
        rw [hr]
        have : (1 : ℝ) / ((N : ℝ) + 2) ≤ 1 / ((N : ℝ) + 1) :=
          one_div_le_one_div_of_le (by positivity) (by linarith)
        linarith
      refine le_antisymm (iSup_le fun n ↦ ?_) (le_iSup_of_le N ?_)
      · rw [hf]
        by_cases hsn : s ∈ Ioc (0 : ℝ) (r n)
        · simp only [Set.indicator_of_mem hsn, le_refl]
        · simp only [Set.indicator_of_notMem hsn, zero_le]
      · rw [hf]
        simp only [Set.indicator_of_mem hsN, le_refl]
    have h1 : ∫⁻ s in Ioo (0 : ℝ) 1, g s = ∫⁻ s in Ioo (0 : ℝ) 1, ⨆ n, f n s :=
      setLIntegral_congr_fun measurableSet_Ioo fun s hs ↦ (hsup s hs).symm
    rw [h1, lintegral_iSup' hfm hfmono]
    refine iSup_le fun n ↦ ?_
    have hsub : Ioc (0 : ℝ) (r n) ⊆ Ioo (0 : ℝ) 1 := fun s hs ↦
      ⟨hs.1, lt_of_le_of_lt hs.2 (hr1 n)⟩
    rw [hf, lintegral_indicator measurableSet_Ioc, Measure.restrict_restrict measurableSet_Ioc,
      Set.inter_eq_left.2 hsub, hg, lintegral_Ioc_atlasCurv_weighted hS ν hfin (hr0 n) (hr1 n)]
    calc ENNReal.ofReal (∫ s in (0 : ℝ)..r n, (1 - s) * atlasCurv hS ν hfin s)
        ≤ ENNReal.ofReal (genRate ν S M).toReal := by
          refine ENNReal.ofReal_le_ofReal ?_
          rw [integral_one_sub_mul_atlasCurv hS ν hfin (hr0 n) (hr1 n)]
          linarith [gap_ge_atlasVelocity hS ν hfin (hr0 n) (hr1 n)]
      _ = genRate ν S M := ENNReal.ofReal_toReal hfin

/-- The weighted curvature is integrable over the bridge. -/
theorem integrableOn_atlasCurv_weighted :
    IntegrableOn (fun s ↦ (1 - s) * atlasCurv hS ν hfin s) (Ioo (0 : ℝ) 1) := by
  have hcont : ContinuousOn (fun s ↦ (1 - s) * atlasCurv hS ν hfin s) (Ioo 0 1) := fun s hs ↦
    ((continuous_const.sub continuous_id).continuousAt.mul
      (continuousAt_atlasCurv hS ν hfin hs.1.le hs.2)).continuousWithinAt
  have hgm : AEMeasurable (fun s ↦ ENNReal.ofReal ((1 - s) * atlasCurv hS ν hfin s))
      (volume.restrict (Ioo (0 : ℝ) 1)) :=
    ENNReal.measurable_ofReal.comp_aemeasurable (hcont.aemeasurable measurableSet_Ioo)
  have h := integrable_toReal_of_lintegral_ne_top hgm (by
    rw [← genRate_eq_lintegral_atlasCurv hS ν hfin]
    exact hfin)
  refine h.congr ?_
  rw [Filter.EventuallyEq, ae_restrict_iff' measurableSet_Ioo]
  filter_upwards with s hs
  exact ENNReal.toReal_ofReal (mul_nonneg (by linarith [hs.2]) (atlasCurv_nonneg hS ν hfin s))

/-- **The visible information is the dual-Fisher energy of the whole bridge**, as a real integral:
`𝓘(M) = ∫₀¹ (1 − s) κ(s) ds`. -/
theorem genRate_toReal_eq_integral_atlasCurv :
    (genRate ν S M).toReal = ∫ s in Ioo (0 : ℝ) 1, (1 - s) * atlasCurv hS ν hfin s := by
  have hcont : ContinuousOn (fun s ↦ (1 - s) * atlasCurv hS ν hfin s) (Ioo 0 1) := fun s hs ↦
    ((continuous_const.sub continuous_id).continuousAt.mul
      (continuousAt_atlasCurv hS ν hfin hs.1.le hs.2)).continuousWithinAt
  rw [integral_eq_lintegral_of_nonneg_ae ?_ (hcont.aestronglyMeasurable measurableSet_Ioo),
    ← genRate_eq_lintegral_atlasCurv hS ν hfin]
  rw [Filter.EventuallyLE, ae_restrict_iff' measurableSet_Ioo]
  filter_upwards with s hs
  exact mul_nonneg (by linarith [hs.2]) (atlasCurv_nonneg hS ν hfin s)

end Laplace.Multi
