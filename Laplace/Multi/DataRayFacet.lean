/-
Copyright (c) 2026 Timaeus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Timaeus
-/
import Laplace.Multi.FacetFisherAccess
import Laplace.Multi.ResponseSpeedDistortion
import Laplace.Multi.DataDissipation

/-!
# The data path's response and a facet (forward direction)

Along the data path `ρ_t = ν.tilted (t h)` the response coordinates `θ_t = dataTheta t ∈ W` form a
`C¹` path whose velocity `θ'_t = (Dm(θ_t)|_W)⁻¹ Cov_{ρ_t}(S, h)` is continuous
(`continuous_dataThetaVel`): the velocity solves the coercive linear equation
`Dm(θ_t) θ'_t = Cov_{ρ_t}(S,h)` and coercivity is stable under the small tilts between nearby
parameters. Its means converge to the top-set conditional mean `E_ν[S | h = H]`
(`tendsto_meanMap_dataTheta`), and its Fisher speed is `responseSpeedSq`. Hence when that limit
lies in the relative interior of a facet, finite total response length forces finite Fisher length
of the normal ray (`lintegral_sqrt_raySpeedSq_lt_top_of_responseLength`), by the facet
accessibility theorem.
-/

open MeasureTheory Filter Topology Set Real

namespace Laplace.Multi

section Velocity

variable {X : Type*} [MeasurableSpace X] [Nonempty X] {J : Type*} [Fintype J] [Nonempty J]
  {S : J → X → ℝ} (hS : ∀ j, Bdd (S j)) (ν : Measure X) [IsProbabilityMeasure ν]
  {h : X → ℝ} (hh : Bdd h)
include hS hh

/-- The family of tilts. -/
local notation "Pfam" => familyMeasure ν (fun _ ↦ (1 : ℝ)) (fun _ ↦ (0 : ℝ)) S 1

/-- The chart derivative. -/
local notation "CD" => chartDeriv measurable_const (integrable_const 1) (fun _ ↦ one_pos)
  (one_integral_pos ν) hS

omit hh in
/-- The pairing of a direction with the chart derivative is minus a covariance. -/
theorem dotJ_chartDeriv_eq_neg_lawCov (θ : dirSpan ν (fun _ ↦ (1 : ℝ)) S) (e : J → ℝ)
    (v : dirSpan ν (fun _ ↦ (1 : ℝ)) S) :
    dotJ e (CD θ v : J → ℝ) =
      -lawCov (Pfam (θ : J → ℝ)) (dirLoss S e) (dirLoss S (v : J → ℝ)) := by
  rw [dotJ_chartDeriv, priorCov_eq_lawCov_familyMeasure hS ν]

theorem continuous_coe_dataTheta : Continuous fun t ↦ (dataTheta hS ν hh t : J → ℝ) :=
  continuous_iff_continuousAt.2 fun t ↦
    ((dirSpan ν (fun _ ↦ (1 : ℝ)) S).subtypeL.hasFDerivAt.comp_hasDerivAt t
      (hasDerivAt_dataTheta_vel hS ν hh t)).continuousAt

theorem hasDerivAt_coe_dataTheta (t : ℝ) :
    HasDerivAt (fun s ↦ (dataTheta hS ν hh s : J → ℝ)) (dataThetaVel hS ν hh t : J → ℝ) t :=
  (dirSpan ν (fun _ ↦ (1 : ℝ)) S).subtypeL.hasFDerivAt.comp_hasDerivAt t
    (hasDerivAt_dataTheta_vel hS ν hh t)

omit [Fintype J] [Nonempty J] in
/-- The vector data forcing is continuous. -/
theorem continuous_dataCov_vec : Continuous (dataCov S ν h) :=
  continuous_pi fun j ↦ continuous_dataCov ν hS hh j

/-- **The response velocity is continuous**: it solves `Dm(θ_t) θ'_t = Cov_{ρ_t}(S,h)` with a
uniformly coercive `Dm(θ_t)` near every time. -/
theorem continuous_coe_dataThetaVel : Continuous fun t ↦ (dataThetaVel hS ν hh t : J → ℝ) := by
  refine continuous_iff_continuousAt.2 fun t₀ ↦ ?_
  obtain ⟨lam, hlam, hcoer⟩ := exists_coercive_familyMeasure hS ν (dataTheta hS ν hh t₀ : J → ℝ)
  obtain ⟨B, hB0, hB⟩ := exists_uniform_bound hS
  -- the tilt sizes tend to zero
  have hc : Tendsto (fun t ↦ (∑ i, |((dataTheta hS ν hh t : J → ℝ) -
      (dataTheta hS ν hh t₀ : J → ℝ)) i|) * B) (𝓝 t₀) (𝓝 0) := by
    have h0 : Tendsto (fun t ↦ (dataTheta hS ν hh t : J → ℝ) - (dataTheta hS ν hh t₀ : J → ℝ))
        (𝓝 t₀) (𝓝 0) := by
      have := ((continuous_coe_dataTheta hS ν hh).tendsto t₀).sub_const
        (dataTheta hS ν hh t₀ : J → ℝ)
      simpa using this
    have h1 : Tendsto (fun t ↦ ∑ i, |((dataTheta hS ν hh t : J → ℝ) -
        (dataTheta hS ν hh t₀ : J → ℝ)) i|) (𝓝 t₀) (𝓝 (∑ i, |(0 : J → ℝ) i|)) :=
      tendsto_finsetSum _ fun i _ ↦
        ((continuous_abs.comp (continuous_apply i)).tendsto _).comp h0
    simpa using h1.mul_const B
  -- eventually the family variance at `θ t` is coercive with constant `λ/2`
  have hcoer' : ∀ᶠ t in 𝓝 t₀, ∀ w ∈ dirSpan ν (fun _ ↦ (1 : ℝ)) S,
      lam / 2 * ‖w‖ ^ 2 ≤
        lawCov (Pfam (dataTheta hS ν hh t : J → ℝ)) (dirLoss S w) (dirLoss S w) := by
    filter_upwards [hc.eventually (Iic_mem_nhds (by positivity : (0 : ℝ) < Real.log 2 / 2))]
      with t ht w hw
    have hc' : ∀ x, |(fun x ↦ -(dirLoss S ((dataTheta hS ν hh t : J → ℝ) -
        (dataTheta hS ν hh t₀ : J → ℝ)) x)) x| ≤ Real.log 2 / 2 := fun x ↦ by
      simp only [abs_neg]
      exact (abs_dirLoss_le_sum_mul hB _ x).trans ht
    have hP0 : IsProbabilityMeasure (Pfam (dataTheta hS ν hh t₀ : J → ℝ)) := by
      rw [familyMeasure_one_zero_eq_tilted hS ν]
      exact isProbabilityMeasure_tilted
        (integrable_exp_of_bdd ν ((bdd_dirLoss hS _).const_mul (-1)))
    have h := le_lawCov_tilted (Pfam (dataTheta hS ν hh t₀ : J → ℝ)) (bdd_neg (bdd_dirLoss hS _))
      hc' (bdd_dirLoss hS w)
    have e := familyMeasure_sub_smul_eq_tilted hS ν (dataTheta hS ν hh t : J → ℝ)
      (dataTheta hS ν hh t₀ : J → ℝ) (0 : J → ℝ) 0
    simp only [zero_smul, sub_zero] at e
    rw [← e] at h
    have hexp : exp (-(2 * (Real.log 2 / 2))) = 1 / 2 := by
      rw [show -(2 * (Real.log 2 / 2)) = -Real.log 2 by ring, Real.exp_neg,
        Real.exp_log two_pos]
      ring
    rw [hexp] at h
    calc lam / 2 * ‖w‖ ^ 2 = 1 / 2 * (lam * ‖w‖ ^ 2) := by ring
      _ ≤ 1 / 2 * lawCov (Pfam (dataTheta hS ν hh t₀ : J → ℝ)) (dirLoss S w) (dirLoss S w) :=
          mul_le_mul_of_nonneg_left (hcoer w hw) (by norm_num)
      _ ≤ _ := h
  -- the perturbed linear equation
  have hb : Tendsto (fun t ↦ dataCov S ν h t) (𝓝 t₀) (𝓝 (dataCov S ν h t₀)) :=
    (continuous_dataCov_vec hS ν hh).tendsto t₀
  have hA : Tendsto (fun t ↦ (CD (dataTheta hS ν hh t) (dataThetaVel hS ν hh t₀) : J → ℝ)) (𝓝 t₀)
      (𝓝 (CD (dataTheta hS ν hh t₀) (dataThetaVel hS ν hh t₀) : J → ℝ)) := by
    have h0 : ∀ x, |(fun _ : X ↦ (0 : ℝ)) x| ≤ 0 := fun x ↦ by simp
    have hcont := continuous_meanMapDeriv (μ := ν) measurable_const (integrable_const 1)
      (fun _ ↦ zero_le_one) (one_integral_pos ν) measurable_const h0 hS one_pos
    have := ((ContinuousLinearMap.apply ℝ (J → ℝ)
      (dataThetaVel hS ν hh t₀ : J → ℝ)).continuous.comp
      (hcont.comp (continuous_coe_dataTheta hS ν hh))).tendsto t₀
    simpa only [chartDeriv_apply, Function.comp_def, ContinuousLinearMap.apply_apply] using this
  -- the key estimate
  rw [ContinuousAt, tendsto_iff_norm_sub_tendsto_zero]
  have hbound : ∀ᶠ t in 𝓝 t₀,
      ‖(dataThetaVel hS ν hh t : J → ℝ) - (dataThetaVel hS ν hh t₀ : J → ℝ)‖ ≤
      2 * Fintype.card J / lam * (‖dataCov S ν h t - dataCov S ν h t₀‖ +
        ‖(CD (dataTheta hS ν hh t) (dataThetaVel hS ν hh t₀) : J → ℝ) -
          (CD (dataTheta hS ν hh t₀) (dataThetaVel hS ν hh t₀) : J → ℝ)‖) := by
    filter_upwards [hcoer'] with t hct
    have hz : (dataThetaVel hS ν hh t : J → ℝ) - (dataThetaVel hS ν hh t₀ : J → ℝ) =
        ((dataThetaVel hS ν hh t - dataThetaVel hS ν hh t₀ :
          dirSpan ν (fun _ ↦ (1 : ℝ)) S) : J → ℝ) := rfl
    -- the variance of the difference is a pairing with the chart derivative
    have hpair : lawCov (Pfam (dataTheta hS ν hh t : J → ℝ))
        (dirLoss S ((dataThetaVel hS ν hh t : J → ℝ) - (dataThetaVel hS ν hh t₀ : J → ℝ)))
        (dirLoss S ((dataThetaVel hS ν hh t : J → ℝ) - (dataThetaVel hS ν hh t₀ : J → ℝ))) =
        -dotJ ((dataThetaVel hS ν hh t : J → ℝ) - (dataThetaVel hS ν hh t₀ : J → ℝ))
          ((CD (dataTheta hS ν hh t)
            (dataThetaVel hS ν hh t - dataThetaVel hS ν hh t₀) : J → ℝ)) := by
      rw [hz, dotJ_chartDeriv_eq_neg_lawCov hS ν, neg_neg]
    have hlin : (CD (dataTheta hS ν hh t)
        (dataThetaVel hS ν hh t - dataThetaVel hS ν hh t₀) : J → ℝ) =
        (dataCov S ν h t - dataCov S ν h t₀) -
          ((CD (dataTheta hS ν hh t) (dataThetaVel hS ν hh t₀) : J → ℝ) -
            (CD (dataTheta hS ν hh t₀) (dataThetaVel hS ν hh t₀) : J → ℝ)) := by
      rw [map_sub, Submodule.coe_sub, chartDeriv_dataThetaVel hS ν hh t,
        chartDeriv_dataThetaVel hS ν hh t₀]
      abel
    have hcs := hct _ (dataThetaVel hS ν hh t - dataThetaVel hS ν hh t₀).2
    rw [← hz, hpair, hlin] at hcs
    have habs : |dotJ ((dataThetaVel hS ν hh t : J → ℝ) - (dataThetaVel hS ν hh t₀ : J → ℝ))
        ((dataCov S ν h t - dataCov S ν h t₀) -
          ((CD (dataTheta hS ν hh t) (dataThetaVel hS ν hh t₀) : J → ℝ) -
            (CD (dataTheta hS ν hh t₀) (dataThetaVel hS ν hh t₀) : J → ℝ)))| ≤
        Fintype.card J *
          ‖(dataThetaVel hS ν hh t : J → ℝ) - (dataThetaVel hS ν hh t₀ : J → ℝ)‖ *
          (‖dataCov S ν h t - dataCov S ν h t₀‖ +
            ‖(CD (dataTheta hS ν hh t) (dataThetaVel hS ν hh t₀) : J → ℝ) -
              (CD (dataTheta hS ν hh t₀) (dataThetaVel hS ν hh t₀) : J → ℝ)‖) := by
      refine (abs_dotJ_le_card_mul _ _).trans ?_
      gcongr
      exact norm_sub_le _ _
    set N := ‖(dataThetaVel hS ν hh t : J → ℝ) - (dataThetaVel hS ν hh t₀ : J → ℝ)‖ with hN
    set R := ‖dataCov S ν h t - dataCov S ν h t₀‖ +
      ‖(CD (dataTheta hS ν hh t) (dataThetaVel hS ν hh t₀) : J → ℝ) -
        (CD (dataTheta hS ν hh t₀) (dataThetaVel hS ν hh t₀) : J → ℝ)‖ with hR
    have hN0 : 0 ≤ N := norm_nonneg _
    have hR0 : 0 ≤ R := add_nonneg (norm_nonneg _) (norm_nonneg _)
    have h1 : lam / 2 * N ^ 2 ≤ Fintype.card J * N * R :=
      hcs.trans ((neg_le_abs _).trans habs)
    rw [div_mul_eq_mul_div, le_div_iff₀ hlam]
    rcases eq_or_lt_of_le hN0 with h0 | hpos
    · rw [← h0, zero_mul]; positivity
    · nlinarith [h1, mul_pos hpos hlam]
  refine squeeze_zero' (Eventually.of_forall fun t ↦ norm_nonneg _) hbound ?_
  have := ((hb.sub_const (dataCov S ν h t₀)).norm.add
    (hA.sub_const (CD (dataTheta hS ν hh t₀) (dataThetaVel hS ν hh t₀) : J → ℝ)).norm).const_mul
    (2 * Fintype.card J / lam)
  simpa using this

/-- The means of the response coordinates are the data means. -/
theorem meanMap_dataTheta (t : ℝ) :
    meanMap ν (fun _ ↦ (1 : ℝ)) (fun _ ↦ (0 : ℝ)) S 1 (dataTheta hS ν hh t : J → ℝ) =
      fun i ↦ ∫ x, S i x ∂ν.tilted (fun x ↦ t * h x) := by
  have h1 := congrArg Subtype.val (chartV_dataTheta hS ν hh t)
  rw [chartV_apply, pathV_apply, sub_left_inj] at h1
  exact h1

variable {H : ℝ} (hH : ∀ x, h x ≤ H)
include hH

/-- **The response means converge to the top-set conditional mean.** -/
theorem tendsto_meanMap_dataTheta (hp : 0 < ν.real {x | h x = H}) :
    Tendsto (fun t ↦ meanMap ν (fun _ ↦ (1 : ℝ)) (fun _ ↦ (0 : ℝ)) S 1
      (dataTheta hS ν hh t : J → ℝ)) atTop
      (𝓝 fun i ↦ (∫ x in {x | h x = H}, S i x ∂ν) / ν.real {x | h x = H}) := by
  simp_rw [meanMap_dataTheta hS ν hh]
  exact tendsto_pi_nhds.2 fun i ↦ tendsto_integral_dataPath_atTop ν hh hH hp (hS i)

end Velocity

section Forward

variable {X : Type*} [MeasurableSpace X] [Nonempty X] {J : Type*} [Fintype J] [Nonempty J]
  {S : J → X → ℝ} (hS : ∀ j, Bdd (S j)) (ν : Measure X) [IsProbabilityMeasure ν]
  {h : X → ℝ} (hh : Bdd h) {H : ℝ} (hH : ∀ x, h x ≤ H)
  (V : Finset (J → ℝ)) [Nonempty V]
  (hpoly : momentBody ν (fun _ ↦ (1 : ℝ)) S = convexHull ℝ (V : Set (J → ℝ)))
  (hcharged : ∀ v ∈ V, 0 < ν.real (statFibre S v))
include hS hh hH hpoly hcharged

/-- **The data path's response and a facet (forward)**: if the top-set conditional mean
`M = E_ν[S | h = H]` lies in the relative interior of a facet and the response path from the
featureless law has finite Fisher length, then the normal ray has finite Fisher length. -/
theorem lintegral_sqrt_raySpeedSq_lt_top_of_responseLength (hp : 0 < ν.real {x | h x = H})
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
    (hI : (∫⁻ t in Ioi (0 : ℝ), ENNReal.ofReal (√(responseSpeedSq hS ν hh t))) < ⊤) :
    (∫⁻ r in Ioi (0 : ℝ), ENNReal.ofReal (√(raySpeedSq S ν (0 : J → ℝ) u r))) < ⊤ :=
  lintegral_sqrt_raySpeedSq_lt_top_of_path hS ν V hpoly hcharged hV hM hMβ hF hMint hv₀V hv₀β
    hzV hz huW hu hT (η := fun t ↦ (dataTheta hS ν hh t : J → ℝ))
    (fun t ↦ (dataTheta hS ν hh t).2) (η' := fun t ↦ (dataThetaVel hS ν hh t : J → ℝ))
    (fun t _ ↦ hasDerivAt_coe_dataTheta hS ν hh t)
    (continuous_coe_dataThetaVel hS ν hh).continuousOn
    (tendsto_meanMap_dataTheta hS ν hh hH hp) hI

end Forward

end Laplace.Multi
