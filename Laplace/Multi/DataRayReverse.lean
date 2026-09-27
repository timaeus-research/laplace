/-
Copyright (c) 2026 Timaeus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Timaeus
-/
import Laplace.Multi.DataRayEstimates
import Laplace.Multi.DataRayFacet

/-!
# The reverse data-ray theorem

Along the data path `ρ_t = ν.tilted (t h)` towards a facet, the eventual estimates of
`DataRayEstimates` integrate: the response speed is bounded by the data forcing `‖Cov_{ρ_t}(S,h)‖`
(integrable, by the dissipation identity) plus the weighted depth speed `g(r_t)|r'_t|`, whose
one-sided variation is controlled by the dissipation `E_{ρ_t}(H − h)` (integrable, with integral
`log(1/p_*)`) and the data forcing again; the positive variation is the Fisher length of the normal
ray. So a finite normal-ray length forces a finite response length.

Combined with the forward direction of `DataRayFacet`, this gives the equivalence
`data_fisher_length_lt_top_iff_ray`: **the response path from the featureless law to a facet of
the moment polytope has finite Fisher length if and only if the normal ray does.**
-/

open MeasureTheory Filter Topology Set Real

namespace Laplace.Multi

section Reverse

variable {X : Type*} [MeasurableSpace X] [Nonempty X] {J : Type*} [Fintype J] [Nonempty J]
  {S : J → X → ℝ} (hS : ∀ j, Bdd (S j)) (ν : Measure X) [IsProbabilityMeasure ν]
  {h : X → ℝ} (hh : Bdd h) {H : ℝ} (hH : ∀ x, h x ≤ H)
  (V : Finset (J → ℝ)) [Nonempty V]
  (hpoly : momentBody ν (fun _ ↦ (1 : ℝ)) S = convexHull ℝ (V : Set (J → ℝ)))
  (hcharged : ∀ v ∈ V, 0 < ν.real (statFibre S v))
include hS hh hH hpoly hcharged

/-- **The data path's response and a facet (reverse)**: if the normal ray has finite Fisher
length then so does the response path. -/
theorem lintegral_sqrt_responseSpeedSq_lt_top_of_ray (hp : 0 < ν.real {x | h x = H})
    {u : J → ℝ} {β : ℝ} (hV : ∀ v ∈ V, dotJ u v ≤ β)
    (hM : (fun i ↦ (∫ x in {x | h x = H}, S i x ∂ν) / ν.real {x | h x = H}) ∈
      convexHull ℝ (V : Set (J → ℝ)))
    (hMβ : dotJ u (fun i ↦ (∫ x in {x | h x = H}, S i x ∂ν) / ν.real {x | h x = H}) = β)
    (hF : minimalFacePoly V (fun i ↦ (∫ x in {x | h x = H}, S i x ∂ν) / ν.real {x | h x = H}) =
      convexHull ℝ ((V.filter fun v ↦ dotJ u v = β : Finset (J → ℝ)) : Set (J → ℝ)))
    (hMint : (fun i ↦ (∫ x in {x | h x = H}, S i x ∂ν) / ν.real {x | h x = H}) ∈
      intrinsicInterior ℝ
        (convexHull ℝ ((V.filter fun v ↦ dotJ u v = β : Finset (J → ℝ)) : Set (J → ℝ))))
    {v₀ : J → ℝ} (hv₀V : v₀ ∈ V) (hv₀β : dotJ u v₀ = β) {z : J → ℝ} (hzV : z ∈ V)
    (hz : dotJ u z < β) (huW : u ∈ dirSpan ν (fun _ ↦ (1 : ℝ)) S) (hu : dotJ u u ≠ 0)
    (hT : ∀ w ∈ dirSpan ν (fun _ ↦ (1 : ℝ)) S, dotJ w u = 0 →
      w ∈ dirSpan (faceMeasure ν {x | dirLoss S u x = β}) (fun _ ↦ (1 : ℝ)) S)
    (hray : (∫⁻ r in Ioi (0 : ℝ), ENNReal.ofReal (√(raySpeedSq S ν (0 : J → ℝ) u r))) < ⊤) :
    (∫⁻ t in Ioi (0 : ℝ), ENNReal.ofReal (√(responseSpeedSq hS ν hh t))) < ⊤ := by
  -- the face and the interior point
  have hp' : 0 < ν.real {x | dirLoss S u x = β} :=
    faceFibre_pos_of_charged ν V hcharged hv₀V hv₀β
  have hA0 : ν {x | dirLoss S u x = β} ≠ 0 := (ENNReal.toReal_pos_iff.1 hp').1.ne'
  have hPA := isProbabilityMeasure_faceMeasure ν hA0
  have hM' : (fun i ↦ (∫ x in {x | h x = H}, S i x ∂ν) / ν.real {x | h x = H}) ∈
      intrinsicInterior ℝ
        (momentBody (faceMeasure ν {x | dirLoss S u x = β}) (fun _ ↦ (1 : ℝ)) S) := by
    rw [momentBody_faceMeasure_eq_of_exposed hS ν V u β hpoly hcharged hV hp']
    exact hMint
  obtain ⟨C₁, C₂, C₃, C₄, hC₁, hC₂, hC₃, hC₄, hev⟩ := eventually_dataRay_estimates hS ν hh hH V
    hpoly hcharged hp hV hM hMβ hF hM' hv₀V hv₀β hzV hz huW hu hT
  -- the functions of time
  obtain ⟨vM, hvM⟩ : ∃ vM : J → ℝ,
      vM = (faceThetaOf hS ν {x | dirLoss S u x = β} hM' : J → ℝ) := ⟨_, rfl⟩
  obtain ⟨g, hg⟩ : ∃ g : ℝ → ℝ, g = fun s ↦ √(raySpeedSq S ν vM u s) := ⟨_, rfl⟩
  obtain ⟨r, hr⟩ : ∃ r : ℝ → ℝ, r = fun t ↦
      normalDepth hS ν {x | dirLoss S u x = β} u (dataTheta hS ν hh t : J → ℝ) := ⟨_, rfl⟩
  obtain ⟨r', hr'⟩ : ∃ r' : ℝ → ℝ, r' = fun t ↦ depthVel hS ν hh u t := ⟨_, rfl⟩
  obtain ⟨D, hD⟩ : ∃ D : ℝ → ℝ, D = fun t ↦ ‖dataCov S ν h t‖ := ⟨_, rfl⟩
  obtain ⟨e, he⟩ : ∃ e : ℝ → ℝ, e = fun t ↦ ∫ x, (H - h x) ∂ν.tilted (fun x ↦ t * h x) :=
    ⟨_, rfl⟩
  obtain ⟨speed, hspeed⟩ : ∃ speed : ℝ → ℝ, speed = fun t ↦ √(responseSpeedSq hS ν hh t) :=
    ⟨_, rfl⟩
  have hev' : ∀ᶠ t in atTop, speed t ≤ C₁ * D t + C₂ * (g (r t) * |r' t|) ∧
      g (r t) * max (-r' t) 0 ≤ C₃ * e t + C₄ * D t ∧ 0 ≤ r t := by
    rw [hvM] at hg
    rw [hg, hr, hr', hD, he, hspeed]
    exact hev
  -- continuity and derivatives
  have hg_cont : Continuous g := by rw [hg]; exact continuous_sqrt_raySpeedSq hS ν vM u
  have hg0 : ∀ s, 0 ≤ g s := fun s ↦ by rw [hg]; exact Real.sqrt_nonneg _
  have hdr : ∀ t, HasDerivAt r (r' t) t := fun t ↦ by
    have h1 : HasDerivAt (fun s ↦ dotJ (dataTheta hS ν hh s : J → ℝ) u)
        (dotJ (dataThetaVel hS ν hh t : J → ℝ) u) t := by
      have := HasDerivAt.fun_sum (u := Finset.univ) fun i _ ↦
        (hasDerivAt_pi.1 (hasDerivAt_coe_dataTheta hS ν hh t) i).mul_const (u i)
      exact this
    have h2 := h1.neg.div_const (dotJ u u)
    rw [hr, hr']
    unfold depthVel
    exact h2.congr_of_eventuallyEq (Eventually.of_forall fun s ↦ normalDepth_eq hS ν u β hp' _)
  have hrc : Continuous r := continuous_iff_continuousAt.2 fun t ↦ (hdr t).continuousAt
  have hr'c : Continuous r' := by
    rw [hr']
    unfold depthVel
    exact (((continuous_dotJ_left u).comp (continuous_coe_dataThetaVel hS ν hh)).neg).div_const _
  have hDc : Continuous D := by rw [hD]; exact (continuous_dataCov_vec hS ν hh).norm
  have hD0 : ∀ t, 0 ≤ D t := fun t ↦ by rw [hD]; exact norm_nonneg _
  have hec : Continuous e := by rw [he]; exact continuous_integral_gap_dataPath ν hh
  have he0 : ∀ t, 0 ≤ e t := fun t ↦ by rw [he]; exact integral_gap_dataPath_nonneg ν hH t
  have hspeed_cont : Continuous speed := by
    have h1 : Continuous fun t ↦ dotJ (dataThetaVel hS ν hh t : J → ℝ) (dataCov S ν h t) := by
      simp only [dotJ]
      exact continuous_finsetSum _ fun i _ ↦
        ((continuous_apply i).comp (continuous_coe_dataThetaVel hS ν hh)).mul
          ((continuous_apply i).comp (continuous_dataCov_vec hS ν hh))
    refine h1.neg.sqrt.congr fun t ↦ ?_
    simp only [Pi.neg_apply, hspeed, responseSpeedSq_eq_neg_dotJ hS ν hh]
  have hspeed0 : ∀ t, 0 ≤ speed t := fun t ↦ by rw [hspeed]; exact Real.sqrt_nonneg _
  -- the integrable functions on the half-line
  have hgint : IntegrableOn g (Ioi (0 : ℝ)) := by
    have h1 : (∫⁻ s in Ioi (0 : ℝ), ENNReal.ofReal (g s)) < ⊤ := by
      rw [hg]
      exact (lintegral_sqrt_raySpeedSq_lt_top_iff_tilt hS ν 0 vM u).1 hray
    exact ⟨hg_cont.aestronglyMeasurable, (hasFiniteIntegral_iff_ofReal (ae_of_all _ hg0)).2 h1⟩
  have heint : IntegrableOn e (Ioi (0 : ℝ)) := by
    rw [he]; exact integrableOn_gap_dataPath ν hh hH hp
  have hDint : IntegrableOn D (Ioi (0 : ℝ)) := by
    have hbound : IntegrableOn (fun t ↦ ∑ j, |dataCov S ν h t j|) (Ioi (0 : ℝ)) :=
      integrable_finsetSum _ fun j _ ↦ (integrableOn_dataCov ν hS hh hH hp j).abs
    refine hbound.mono' hDc.aestronglyMeasurable (ae_of_all _ fun t ↦ ?_)
    rw [hD, Real.norm_eq_abs, abs_of_nonneg (norm_nonneg _)]
    refine (pi_norm_le_iff_of_nonneg (Finset.sum_nonneg fun j _ ↦ abs_nonneg _)).2 fun i ↦ ?_
    rw [Real.norm_eq_abs]
    exact Finset.single_le_sum (f := fun j ↦ |dataCov S ν h t j|) (fun j _ ↦ abs_nonneg _)
      (Finset.mem_univ i)
  -- the eventual bounds hold from some time on
  obtain ⟨t₀, ht₀⟩ := Filter.eventually_atTop.1 (hev'.and (eventually_ge_atTop (0 : ℝ)))
  have ht₀0 : 0 ≤ t₀ := (ht₀ t₀ le_rfl).2
  -- window integrals are dominated by the half-line integrals
  have hIoc : ∀ f : ℝ → ℝ, (∀ s, 0 ≤ f s) → IntegrableOn f (Ioi (0 : ℝ)) → ∀ b, t₀ ≤ b →
      ∫ s in t₀..b, f s ≤ ∫ s in Ioi (0 : ℝ), f s := fun f hf hfi b hb ↦ by
    rw [intervalIntegral.integral_of_le hb]
    refine setIntegral_mono_set hfi (ae_of_all _ hf) ?_
    exact LE.le.eventuallyLE fun s hs ↦ Set.mem_Ioi.2 (ht₀0.trans_lt hs.1)
  -- the uniform window bound
  obtain ⟨I, hI⟩ : ∃ I : ℝ, I = C₁ * (∫ s in Ioi (0 : ℝ), D s) +
      C₂ * ((∫ s in Ioi (0 : ℝ), g s) +
        2 * (C₃ * (∫ s in Ioi (0 : ℝ), e s) + C₄ * ∫ s in Ioi (0 : ℝ), D s)) := ⟨_, rfl⟩
  have hwin : ∀ b, t₀ ≤ b → ∫ s in t₀..b, speed s ≤ I := fun b hb ↦ by
    have hRHS : Continuous fun s ↦ C₁ * D s + C₂ * (g (r s) * |r' s|) :=
      (continuous_const.mul hDc).add (continuous_const.mul ((hg_cont.comp hrc).mul hr'c.abs))
    have hRHS2 : Continuous fun s ↦ C₃ * e s + C₄ * D s :=
      (continuous_const.mul hec).add (continuous_const.mul hDc)
    have h1 : ∫ s in t₀..b, speed s ≤ ∫ s in t₀..b, (C₁ * D s + C₂ * (g (r s) * |r' s|)) :=
      intervalIntegral.integral_mono_on hb (hspeed_cont.intervalIntegrable _ _)
        (hRHS.intervalIntegrable _ _) fun s hs ↦ (ht₀ s hs.1).1.1
    have h2 : ∫ s in t₀..b, (C₁ * D s + C₂ * (g (r s) * |r' s|)) =
        C₁ * (∫ s in t₀..b, D s) + C₂ * ∫ s in t₀..b, g (r s) * |r' s| := by
      have hi1 : IntervalIntegrable (fun s ↦ C₁ * D s) volume t₀ b :=
        (continuous_const.mul hDc).intervalIntegrable _ _
      have hi2 : IntervalIntegrable (fun s ↦ C₂ * (g (r s) * |r' s|)) volume t₀ b :=
        (continuous_const.mul ((hg_cont.comp hrc).mul hr'c.abs)).intervalIntegrable _ _
      rw [intervalIntegral.integral_add hi1 hi2, intervalIntegral.integral_const_mul,
        intervalIntegral.integral_const_mul]
    have h3 := integral_mul_abs_deriv_le hg_cont hg0 (a := t₀) (b := b) (R := 0)
      (fun s _ ↦ hdr s) hr'c.continuousOn
      (fun s hs ↦ by
        rw [Set.uIcc_of_le hb] at hs
        exact (ht₀ s hs.1).1.2.2) hgint
    have h4 : ∫ s in t₀..b, g (r s) * max (-r' s) 0 ≤ ∫ s in t₀..b, (C₃ * e s + C₄ * D s) :=
      intervalIntegral.integral_mono_on hb
        (((hg_cont.comp hrc).mul (hr'c.neg.max continuous_const)).intervalIntegrable _ _)
        (hRHS2.intervalIntegrable _ _) fun s hs ↦ (ht₀ s hs.1).1.2.1
    have h5 : ∫ s in t₀..b, (C₃ * e s + C₄ * D s) =
        C₃ * (∫ s in t₀..b, e s) + C₄ * ∫ s in t₀..b, D s := by
      have hi1 : IntervalIntegrable (fun s ↦ C₃ * e s) volume t₀ b :=
        (continuous_const.mul hec).intervalIntegrable _ _
      have hi2 : IntervalIntegrable (fun s ↦ C₄ * D s) volume t₀ b :=
        (continuous_const.mul hDc).intervalIntegrable _ _
      rw [intervalIntegral.integral_add hi1 hi2, intervalIntegral.integral_const_mul,
        intervalIntegral.integral_const_mul]
    have hD' := hIoc D hD0 hDint b hb
    have he' := hIoc e he0 heint b hb
    have h6 : ∫ s in t₀..b, g (r s) * |r' s| ≤ (∫ s in Ioi (0 : ℝ), g s) +
        2 * (C₃ * (∫ s in Ioi (0 : ℝ), e s) + C₄ * ∫ s in Ioi (0 : ℝ), D s) := by
      refine h3.trans ?_
      have h7 := h4.trans_eq h5
      have h8 := mul_le_mul_of_nonneg_left he' hC₃
      have h9 := mul_le_mul_of_nonneg_left hD' hC₄
      linarith
    rw [hI]
    calc ∫ s in t₀..b, speed s ≤ ∫ s in t₀..b, (C₁ * D s + C₂ * (g (r s) * |r' s|)) := h1
      _ = C₁ * (∫ s in t₀..b, D s) + C₂ * ∫ s in t₀..b, g (r s) * |r' s| := h2
      _ ≤ _ := add_le_add (mul_le_mul_of_nonneg_left hD' hC₁) (mul_le_mul_of_nonneg_left h6 hC₂)
  -- integrability of the response speed beyond `t₀`, then on the whole half-line
  have hint : IntegrableOn speed (Ioi t₀) := by
    refine integrableOn_Ioi_of_intervalIntegral_norm_bounded I t₀ (b := id) (l := atTop)
      (fun _ ↦ hspeed_cont.integrableOn_Ioc) tendsto_id
      (Filter.eventually_atTop.2 ⟨t₀, fun b hb ↦ ?_⟩)
    have hn : ∀ x, ‖speed x‖ = speed x := fun x ↦ Real.norm_of_nonneg (hspeed0 x)
    simp only [id, hn]
    exact hwin b hb
  have hint0 : IntegrableOn speed (Ioi (0 : ℝ)) := by
    rcases eq_or_lt_of_le ht₀0 with h0 | h0
    · rw [← h0] at hint
      exact hint
    · rw [← Set.Ioc_union_Ioi_eq_Ioi h0.le]
      exact hspeed_cont.integrableOn_Ioc.union hint
  subst hspeed
  exact hint0.lintegral_lt_top

/-- **The data-ray equivalence.** Along the data path towards a facet of the moment polytope,
the response path from the featureless law has finite Fisher length if and only if the normal
ray of the facet has finite Fisher length. -/
theorem data_fisher_length_lt_top_iff_ray (hp : 0 < ν.real {x | h x = H})
    {u : J → ℝ} {β : ℝ} (hV : ∀ v ∈ V, dotJ u v ≤ β)
    (hM : (fun i ↦ (∫ x in {x | h x = H}, S i x ∂ν) / ν.real {x | h x = H}) ∈
      convexHull ℝ (V : Set (J → ℝ)))
    (hMβ : dotJ u (fun i ↦ (∫ x in {x | h x = H}, S i x ∂ν) / ν.real {x | h x = H}) = β)
    (hF : minimalFacePoly V (fun i ↦ (∫ x in {x | h x = H}, S i x ∂ν) / ν.real {x | h x = H}) =
      convexHull ℝ ((V.filter fun v ↦ dotJ u v = β : Finset (J → ℝ)) : Set (J → ℝ)))
    (hMint : (fun i ↦ (∫ x in {x | h x = H}, S i x ∂ν) / ν.real {x | h x = H}) ∈
      intrinsicInterior ℝ
        (convexHull ℝ ((V.filter fun v ↦ dotJ u v = β : Finset (J → ℝ)) : Set (J → ℝ))))
    {v₀ : J → ℝ} (hv₀V : v₀ ∈ V) (hv₀β : dotJ u v₀ = β) {z : J → ℝ} (hzV : z ∈ V)
    (hz : dotJ u z < β) (huW : u ∈ dirSpan ν (fun _ ↦ (1 : ℝ)) S) (hu : dotJ u u ≠ 0)
    (hT : ∀ w ∈ dirSpan ν (fun _ ↦ (1 : ℝ)) S, dotJ w u = 0 →
      w ∈ dirSpan (faceMeasure ν {x | dirLoss S u x = β}) (fun _ ↦ (1 : ℝ)) S) :
    (∫⁻ t in Ioi (0 : ℝ), ENNReal.ofReal (√(responseSpeedSq hS ν hh t))) < ⊤ ↔
      (∫⁻ r in Ioi (0 : ℝ), ENNReal.ofReal (√(raySpeedSq S ν (0 : J → ℝ) u r))) < ⊤ :=
  ⟨lintegral_sqrt_raySpeedSq_lt_top_of_responseLength hS ν hh hH V hpoly hcharged hp hV hM hMβ hF
      hMint hv₀V hv₀β hzV hz huW hu hT,
    lintegral_sqrt_responseSpeedSq_lt_top_of_ray hS ν hh hH V hpoly hcharged hp hV hM hMβ hF hMint
      hv₀V hv₀β hzV hz huW hu hT⟩

end Reverse

end Laplace.Multi
