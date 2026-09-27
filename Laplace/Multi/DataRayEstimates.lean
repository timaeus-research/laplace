/-
Copyright (c) 2026 Timaeus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Timaeus
-/
import Laplace.Multi.DataRayBlocks
import Laplace.Multi.DataRayHelpers
import Laplace.Multi.FacetFisherAccess

/-!
# The eventual estimates of the reverse data-ray theorem

Along the data path towards a facet, once the tangential coordinate has converged, the face
mass is close to one and the tangential covariance is coercive, the scalar block identities give:

* `‖v'_t‖ ≤ (card J/λ)(‖Cov_{ρ_t}(S,h)‖ + 2B a_t |r'_t|)` (tangential velocity estimate);
* `a_t² ≤ 2δ V_t` (mass at the face controls the slack mean against the slack variance), hence the
  absorption `4K₀²a_t²/λ ≤ V_t/2` and `a_t ≤ √V_t`;
* `√V_t (r'_t)₋ ≤ 2(E_{ρ_t}(H−h) + C₀ ‖Cov_{ρ_t}(S,h)‖)` (weighted negative depth velocity);
* `√responseSpeedSq_t ≤ K₀‖v'_t‖ + |r'_t| √V_t` (standard-deviation triangle inequality);
* `e^{−1} g(r_t) ≤ √V_t ≤ e g(r_t)` for the fixed reference ray `g = √raySpeedSq(v_M,u,·)`.

The depth `r_t` is also eventually nonnegative.

Packaged as `eventually_dataRay_estimates`: eventually the response speed is at most a fixed
combination of the data forcing and the weighted depth speed, and the weighted negative depth
variation is at most a fixed combination of the dissipation and the data forcing.
-/

open MeasureTheory Filter Topology Set Real

namespace Laplace.Multi

section Estimates

variable {X : Type*} [MeasurableSpace X] [Nonempty X] {J : Type*} [Fintype J] [Nonempty J]
  {S : J → X → ℝ} (hS : ∀ j, Bdd (S j)) (ν : Measure X) [IsProbabilityMeasure ν]
  {h : X → ℝ} (hh : Bdd h) {H : ℝ} (hH : ∀ x, h x ≤ H)
  (V : Finset (J → ℝ)) [Nonempty V]
  (hpoly : momentBody ν (fun _ ↦ (1 : ℝ)) S = convexHull ℝ (V : Set (J → ℝ)))
  (hcharged : ∀ v ∈ V, 0 < ν.real (statFibre S v))
include hS hh hH hpoly hcharged

/-- The family of tilts. -/
local notation "Pfam" => familyMeasure ν (fun _ ↦ (1 : ℝ)) (fun _ ↦ (0 : ℝ)) S 1

/-- **The eventual estimates of the reverse data-ray theorem.** -/
theorem eventually_dataRay_estimates (hp : 0 < ν.real {x | h x = H})
    {u : J → ℝ} {β : ℝ} (hV : ∀ v ∈ V, dotJ u v ≤ β)
    (hM : (fun i ↦ (∫ x in {x | h x = H}, S i x ∂ν) / ν.real {x | h x = H}) ∈
      convexHull ℝ (V : Set (J → ℝ)))
    (hMβ : dotJ u (fun i ↦ (∫ x in {x | h x = H}, S i x ∂ν) / ν.real {x | h x = H}) = β)
    (hF : minimalFacePoly V (fun i ↦ (∫ x in {x | h x = H}, S i x ∂ν) / ν.real {x | h x = H}) =
      convexHull ℝ ((V.filter fun v ↦ dotJ u v = β : Finset (J → ℝ)) : Set (J → ℝ)))
    [IsProbabilityMeasure (faceMeasure ν {x | dirLoss S u x = β})]
    (hM' : (fun i ↦ (∫ x in {x | h x = H}, S i x ∂ν) / ν.real {x | h x = H}) ∈
      intrinsicInterior ℝ
        (momentBody (faceMeasure ν {x | dirLoss S u x = β}) (fun _ ↦ (1 : ℝ)) S))
    {v₀ : J → ℝ} (hv₀V : v₀ ∈ V) (hv₀β : dotJ u v₀ = β) {z : J → ℝ} (hzV : z ∈ V)
    (hz : dotJ u z < β) (huW : u ∈ dirSpan ν (fun _ ↦ (1 : ℝ)) S) (hu : dotJ u u ≠ 0)
    (hT : ∀ w ∈ dirSpan ν (fun _ ↦ (1 : ℝ)) S, dotJ w u = 0 →
      w ∈ dirSpan (faceMeasure ν {x | dirLoss S u x = β}) (fun _ ↦ (1 : ℝ)) S) :
    ∃ C₁ C₂ C₃ C₄ : ℝ, 0 ≤ C₁ ∧ 0 ≤ C₂ ∧ 0 ≤ C₃ ∧ 0 ≤ C₄ ∧ ∀ᶠ t in atTop,
      √(responseSpeedSq hS ν hh t) ≤ C₁ * ‖dataCov S ν h t‖ +
        C₂ * (√(raySpeedSq S ν (faceThetaOf hS ν {x | dirLoss S u x = β} hM' : J → ℝ) u
          (normalDepth hS ν {x | dirLoss S u x = β} u (dataTheta hS ν hh t : J → ℝ))) *
          |depthVel hS ν hh u t|) ∧
      √(raySpeedSq S ν (faceThetaOf hS ν {x | dirLoss S u x = β} hM' : J → ℝ) u
          (normalDepth hS ν {x | dirLoss S u x = β} u (dataTheta hS ν hh t : J → ℝ))) *
          max (-depthVel hS ν hh u t) 0 ≤
        C₃ * (∫ x, (H - h x) ∂ν.tilted (fun x ↦ t * h x)) + C₄ * ‖dataCov S ν h t‖ ∧
      0 ≤ normalDepth hS ν {x | dirLoss S u x = β} u (dataTheta hS ν hh t : J → ℝ) := by
  -- the face
  have hp' : 0 < ν.real {x | dirLoss S u x = β} :=
    faceFibre_pos_of_charged ν V hcharged hv₀V hv₀β
  have hF' := measurableSet_faceFibre hS u β
  have hβ := ae_dirLoss_le_of_polytope hS ν V u β hpoly hV
  set vM : J → ℝ := (faceThetaOf hS ν {x | dirLoss S u x = β} hM' : J → ℝ) with hvM
  have hfacet := facet_invisible_of_orth hS ν u β huW hu hT
  obtain ⟨B, hB0, hB⟩ := exists_uniform_bound hS
  obtain ⟨-, Ku, hKu⟩ := bdd_dirLoss hS u
  have hPf : ∀ w : J → ℝ, IsProbabilityMeasure (Pfam w) := fun w ↦ by
    rw [familyMeasure_one_zero_eq_tilted hS ν]
    exact isProbabilityMeasure_tilted
      (integrable_exp_of_bdd ν ((bdd_dirLoss hS _).const_mul (-1)))
  -- the decomposition of the response coordinates
  have hdecomp : ∀ t, (dataTheta hS ν hh t : J → ℝ) =
      (faceTheta hS ν {x | dirLoss S u x = β} (dataTheta hS ν hh t : J → ℝ) : J → ℝ) -
        normalDepth hS ν {x | dirLoss S u x = β} u (dataTheta hS ν hh t : J → ℝ) • u :=
    fun t ↦ eq_faceTheta_sub_smul hS ν _ u hF' hp' hfacet hu (dataTheta hS ν hh t).2
  -- the sequential criterion transported to the real parameter
  have hlim := tendsto_meanMap_dataTheta hS ν hh hH hp
  have hcrit : ∀ x : ℕ → ℝ, Tendsto x atTop atTop →
      Tendsto (fun n ↦ meanMap (faceMeasure ν {x | dirLoss S u x = β}) (fun _ ↦ (1 : ℝ))
        (fun _ ↦ (0 : ℝ)) S 1 (dataTheta hS ν hh (x n) : J → ℝ)) atTop
        (𝓝 fun i ↦ (∫ x in {x | h x = H}, S i x ∂ν) / ν.real {x | h x = H}) ∧
      ∀ w ∈ V, dotJ u w < β →
        Tendsto (fun n ↦ dotJ (dataTheta hS ν hh (x n) : J → ℝ) (w - v₀)) atTop atTop :=
    fun x hx ↦ (tendsto_meanMap_iff_faceMean_and_vertexGaps hS ν V hpoly hcharged hV hM hMβ hF
      hv₀V hv₀β ((fun s ↦ (dataTheta hS ν hh s : J → ℝ)) ∘ x)).1 (hlim.comp hx)
  have hface : Tendsto (fun s ↦ meanMap (faceMeasure ν {x | dirLoss S u x = β})
      (fun _ ↦ (1 : ℝ)) (fun _ ↦ (0 : ℝ)) S 1 (dataTheta hS ν hh s : J → ℝ)) atTop
      (𝓝 fun i ↦ (∫ x in {x | h x = H}, S i x ∂ν) / ν.real {x | h x = H}) :=
    tendsto_iff_seq_tendsto.2 fun x hx ↦ (hcrit x hx).1
  have hgap : Tendsto (fun t ↦ dotJ (dataTheta hS ν hh t : J → ℝ) (z - v₀)) atTop atTop :=
    tendsto_iff_seq_tendsto.2 fun x hx ↦ (hcrit x hx).2 z hzV hz
  have hvθ : Tendsto (fun t ↦ (faceTheta hS ν {x | dirLoss S u x = β}
      (dataTheta hS ν hh t : J → ℝ) : J → ℝ)) atTop (𝓝 vM) :=
    (continuous_subtype_val.tendsto _).comp (tendsto_faceTheta hS ν _ hM' hface)
  have hr : Tendsto (fun t ↦ normalDepth hS ν {x | dirLoss S u x = β} u
      (dataTheta hS ν hh t : J → ℝ)) atTop atTop :=
    tendsto_normalDepth_atTop hS ν _ u hF' hp' hfacet hu (fun t ↦ (dataTheta hS ν hh t).2) hz
      hv₀β hgap hvθ
  -- concentration, coercivity and the tilt sizes
  have hmass := tendsto_measureReal_family_faceFibre_of_components hS ν u β hβ hp' hvθ hr
  obtain ⟨lam, hlam, hcoer⟩ := eventually_coercive_of_components hS ν u β hβ hp' hvθ hr
  have hc : Tendsto (fun t ↦ (∑ i, |((faceTheta hS ν {x | dirLoss S u x = β}
      (dataTheta hS ν hh t : J → ℝ) : J → ℝ) - vM) i|) * B) atTop (𝓝 0) := by
    have h0 : Tendsto (fun t ↦ (faceTheta hS ν {x | dirLoss S u x = β}
        (dataTheta hS ν hh t : J → ℝ) : J → ℝ) - vM) atTop (𝓝 0) := by
      simpa using hvθ.sub_const vM
    have h1 : Tendsto (fun t ↦ ∑ i, |((faceTheta hS ν {x | dirLoss S u x = β}
        (dataTheta hS ν hh t : J → ℝ) : J → ℝ) - vM) i|) atTop (𝓝 (∑ i, |(0 : J → ℝ) i|)) :=
      tendsto_finsetSum _ fun i _ ↦
        ((continuous_abs.comp (continuous_apply i)).tendsto _).comp h0
    simpa using h1.mul_const B
  -- the slack and its positive part
  set ℓp : X → ℝ := fun x ↦ max (β - dirLoss S u x) 0 with hℓp_def
  have hℓp_bdd : Bdd ℓp :=
    ⟨((bdd_dirLoss hS u).1.const_sub β).max measurable_const, |β| + Ku,
      fun x ↦ abs_max_sub_zero_le (hKu x)⟩
  have hℓp0 : ∀ x, 0 ≤ ℓp x := fun x ↦ le_max_right _ _
  have hℓp_meas : MeasurableSet {x | ℓp x = 0} := measurableSet_eq_fun hℓp_bdd.1 measurable_const
  have hac : ∀ w : J → ℝ, Pfam w ≪ ν := fun w ↦ by
    rw [familyMeasure_eq_withDensity_famDens]
    exact withDensity_absolutelyContinuous _ _
  have hβq : ∀ w : J → ℝ, ∀ᵐ x ∂Pfam w, dirLoss S u x ≤ β := fun w ↦ (hac w).ae_le hβ
  have hℓ_ae : ∀ w : J → ℝ, (fun x ↦ β - dirLoss S u x) =ᵐ[Pfam w] ℓp :=
    fun w ↦ (hβq w).mono fun x hx ↦ by
      simp only [hℓp_def]
      rw [max_eq_left (sub_nonneg.2 hx)]
  have hset_ae : ∀ w : J → ℝ, ({x | ℓp x = 0} : Set X) =ᵐ[Pfam w] {x | dirLoss S u x = β} :=
    fun w ↦ Filter.eventuallyEq_set.2 ((hβq w).mono fun x hx ↦ by
      simp only [hℓp_def, Set.mem_ofPred_eq]
      constructor
      · intro h1
        have := max_eq_right_iff.1 h1
        exact le_antisymm hx (by linarith)
      · intro h1
        rw [max_eq_right_iff]
        linarith)
  -- constants
  obtain ⟨K₀, hK₀⟩ : ∃ K₀ : ℝ, K₀ = (Fintype.card J : ℝ) * B := ⟨_, rfl⟩
  have hK₀0 : 0 ≤ K₀ := by rw [hK₀]; positivity
  obtain ⟨δ, hδ⟩ : ∃ δ : ℝ, δ = lam / (2 * (16 * K₀ ^ 2 + 1 + lam)) := ⟨_, rfl⟩
  have hδ0 : 0 < δ := by rw [hδ]; positivity
  have hδ1 : 2 * δ ≤ 1 := by
    rw [hδ, ← mul_div_assoc, div_le_one (by positivity)]
    linarith [sq_nonneg K₀]
  have hδ2 : 8 * K₀ ^ 2 * δ ≤ lam / 2 := by
    rw [hδ, ← mul_div_assoc, div_le_iff₀ (by positivity)]
    nlinarith [sq_nonneg K₀, mul_nonneg hlam.le (sq_nonneg K₀)]
  obtain ⟨C₀, hC₀⟩ : ∃ C₀ : ℝ, C₀ = 2 * (Fintype.card J : ℝ) * K₀ / lam := ⟨_, rfl⟩
  have hC₀0 : 0 ≤ C₀ := by rw [hC₀]; positivity
  have hK : ∀ w : J → ℝ, ∀ y, |dirLoss S w y| ≤ K₀ * ‖w‖ := fun w y ↦
    (abs_dirLoss_le_sum_mul hB _ y).trans (by
      rw [hK₀, mul_assoc, mul_comm B, ← mul_assoc]
      exact mul_le_mul_of_nonneg_right (sum_abs_le_card_mul_norm _) hB0)
  refine ⟨K₀ * (Fintype.card J : ℝ) / lam, (2 * K₀ * (Fintype.card J : ℝ) * B / lam + 1) * exp 1,
    2 * exp 1, 2 * exp 1 * C₀, by positivity, by positivity, by positivity, by positivity, ?_⟩
  filter_upwards [hcoer, hmass.eventually (Ici_mem_nhds (by norm_num : (1 / 2 : ℝ) < 1)),
    hmass.eventually (Ici_mem_nhds (by linarith : 1 - δ < 1)),
    hc.eventually (Iic_mem_nhds one_pos), eventually_ge_atTop (0 : ℝ),
    hr.eventually (eventually_ge_atTop (0 : ℝ))]
    with t hcs hms hms' hcs' hs0 hrt
  -- the facts at time `t`
  have hqP : IsProbabilityMeasure (Pfam (dataTheta hS ν hh t : J → ℝ)) := hPf _
  rw [← hdecomp t] at hms hms'
  have hv'T : tangentVel hS ν hh u t ∈
      dirSpan (faceMeasure ν {x | dirLoss S u x = β}) (fun _ ↦ (1 : ℝ)) S :=
    hT _ (Submodule.add_mem _ (dataThetaVel hS ν hh t).2 (Submodule.smul_mem _ _ huW))
      (dotJ_tangentVel_u hS ν hh u hu t)
  have hcoerc := hcs _ hv'T
  rw [← hdecomp t] at hcoerc
  have ha_model := integral_slack_family_eq hS ν hh u β t
  have h_var := var_tangentVel_eq hS ν hh u t
  have hb1 := depthVel_mul_var_eq hS ν hh u t
  have hb2 := slackMeanVel_le hS ν hh u β hH hβ t
  have hdot := abs_dotJ_le_card_mul (tangentVel hS ν hh u t) (dataCov S ν h t)
  have hKv := hK (tangentVel hS ν hh u t)
  have hspeed_eq : responseSpeedSq hS ν hh t =
      lawCov (Pfam (dataTheta hS ν hh t : J → ℝ))
        (fun y ↦ dirLoss S (tangentVel hS ν hh u t) y + (-depthVel hS ν hh u t) * dirLoss S u y)
        (fun y ↦ dirLoss S (tangentVel hS ν hh u t) y +
          (-depthVel hS ν hh u t) * dirLoss S u y) := by
    have e1 : dirLoss S (dataThetaVel hS ν hh t : J → ℝ) =
        fun y ↦ dirLoss S (tangentVel hS ν hh u t) y + (-depthVel hS ν hh u t) * dirLoss S u y := by
      funext y
      rw [coe_dataThetaVel_eq_tangentVel_sub hS ν hh u t, dirLoss_sub', dirLoss_smul]
      ring
    rw [responseSpeedSq, e1]
  have hray_eq : raySpeedSq S ν (faceTheta hS ν {x | dirLoss S u x = β}
      (dataTheta hS ν hh t : J → ℝ) : J → ℝ) u
        (normalDepth hS ν {x | dirLoss S u x = β} u (dataTheta hS ν hh t : J → ℝ)) =
      lawCov (Pfam (dataTheta hS ν hh t : J → ℝ)) (dirLoss S u) (dirLoss S u) := by
    rw [raySpeedSq, ← hdecomp t]
  have hray := raySpeedSq_tilt_comparable hS ν (faceTheta hS ν {x | dirLoss S u x = β}
      (dataTheta hS ν hh t : J → ℝ) : J → ℝ) vM u
      (fun y ↦ (abs_dirLoss_le_sum_mul hB _ y).trans hcs')
      (normalDepth hS ν {x | dirLoss S u x = β} u (dataTheta hS ν hh t : J → ℝ))
  rw [hray_eq] at hray
  have hℓ_q := hℓ_ae (dataTheta hS ν hh t : J → ℝ)
  have hset_q := hset_ae (dataTheta hS ν hh t : J → ℝ)
  have he0 := integral_gap_dataPath_nonneg ν hH t
  have hVq0 : 0 ≤ lawCov (Pfam (dataTheta hS ν hh t : J → ℝ)) (dirLoss S u) (dirLoss S u) :=
    lawCov_self_nonneg _ (bdd_dirLoss hS u)
  have hg0 : 0 ≤ raySpeedSq S ν vM u
      (normalDepth hS ν {x | dirLoss S u x = β} u (dataTheta hS ν hh t : J → ℝ)) :=
    lawCov_self_nonneg _ (bdd_dirLoss hS u)
  have hfv' : Bdd (dirLoss S (tangentVel hS ν hh u t)) := bdd_dirLoss hS _
  -- abbreviations
  set q := Pfam (dataTheta hS ν hh t : J → ℝ) with hq_def
  set r := normalDepth hS ν {x | dirLoss S u x = β} u (dataTheta hS ν hh t : J → ℝ) with hr_def
  set r' := depthVel hS ν hh u t with hr'_def
  set v' := tangentVel hS ν hh u t with hv'_def
  set Vq := lawCov q (dirLoss S u) (dirLoss S u) with hVq
  set c := lawCov q (dirLoss S u) (dirLoss S v') with hc_def
  set a := slackMean S ν h u β t with ha
  set e := ∫ x, (H - h x) ∂ν.tilted (fun x ↦ t * h x) with he
  set D := ‖dataCov S ν h t‖ with hD
  set xv := ‖v'‖ with hxv
  set g := raySpeedSq S ν vM u r with hg
  set dc := dotJ v' (dataCov S ν h t) with hdc
  set du := dotJ u (dataCov S ν h t) with hdu
  have hD0 : 0 ≤ D := norm_nonneg _
  have hx0 : 0 ≤ xv := norm_nonneg _
  clear_value dc du g xv D e a c Vq v' r' r q
  -- the slack mean is nonnegative and equals the model slack mean
  have ha_pos_model : ∫ y, ℓp y ∂q = a := by
    rw [← ha_model]
    exact (integral_congr_ae hℓ_q).symm
  have ha0 : 0 ≤ a := by
    rw [← ha_pos_model]
    exact integral_nonneg hℓp0
  -- the cross covariance is small in the slack mean
  have hcabs : |c| ≤ 2 * (K₀ * xv) * a := by
    have e0 := lawCov_congr_ae q hℓ_q (Filter.EventuallyEq.rfl (f := dirLoss S v'))
    have e1 : lawCov q ℓp (dirLoss S v') = -c := by
      rw [← e0, lawCov_sub_left_eq q (Bdd.const β) (bdd_dirLoss hS u) hfv',
        lawCov_const_left_eq_zero, hc_def]
      ring
    have h1 := abs_lawCov_le_mul_integral_of_nonneg q hfv' hKv hℓp_bdd hℓp0
    rw [ha_pos_model, lawCov_comm q, e1, abs_neg] at h1
    exact h1
  -- the tangential velocity estimate
  have hxbound : xv ≤ (Fintype.card J : ℝ) / lam * (D + 2 * B * a * |r'|) := by
    have h2 : lawCov q (dirLoss S v') (dirLoss S v') ≤
        (Fintype.card J : ℝ) * xv * D + |r'| * (2 * (K₀ * xv) * a) := by
      rw [h_var]
      have h4 : |r' * c| ≤ |r'| * (2 * (K₀ * xv) * a) := by
        rw [abs_mul]
        exact mul_le_mul_of_nonneg_left hcabs (abs_nonneg _)
      have h5 := neg_abs_le dc
      have h6 := le_abs_self (r' * c)
      linarith
    rcases eq_or_lt_of_le hx0 with h0 | hpos
    · rw [← h0]; positivity
    · have h7 : lam * xv ^ 2 ≤ (Fintype.card J : ℝ) * xv * D + |r'| * (2 * (K₀ * xv) * a) :=
        hcoerc.trans h2
      rw [div_mul_eq_mul_div, le_div_iff₀ hlam]
      have h8 : lam * xv ≤ (Fintype.card J : ℝ) * (D + 2 * B * a * |r'|) := by
        have h9 : xv * (lam * xv) ≤ xv * ((Fintype.card J : ℝ) * (D + 2 * B * a * |r'|)) := by
          rw [hK₀] at h7
          calc xv * (lam * xv) = lam * xv ^ 2 := by ring
            _ ≤ (Fintype.card J : ℝ) * xv * D +
                |r'| * (2 * ((Fintype.card J : ℝ) * B * xv) * a) := h7
            _ = xv * ((Fintype.card J : ℝ) * (D + 2 * B * a * |r'|)) := by ring
        exact le_of_mul_le_mul_left h9 hpos
      linarith
  -- the mass at the face controls the slack mean
  have hpp : q.real {x | ℓp x = 0} = q.real {x | dirLoss S u x = β} := measureReal_congr hset_q
  have hp'' : 0 < q.real {x | ℓp x = 0} := by rw [hpp]; linarith
  have hεp : q.real {x | ℓp x = 0}ᶜ = 1 - q.real {x | ℓp x = 0} := by
    rw [measureReal_compl hℓp_meas, probReal_univ]
  have hVar : lawCov q ℓp ℓp = Vq := by
    rw [hVq, ← lawCov_congr_ae q hℓ_q hℓ_q, lawCov_const_sub_self q (bdd_dirLoss hS u)]
  have ha2 : a ^ 2 ≤ 2 * δ * Vq := by
    have h1 := sq_integral_le_div_mul_lawCov q hℓp_bdd hp''
    rw [ha_pos_model, hVar, hεp, hpp] at h1
    refine h1.trans ?_
    have h2 : (1 - q.real {x | dirLoss S u x = β}) / q.real {x | dirLoss S u x = β} ≤ 2 * δ := by
      rw [div_le_iff₀ (by linarith)]
      have := mul_le_mul_of_nonneg_left hms (by positivity : (0 : ℝ) ≤ 2 * δ)
      linarith
    exact mul_le_mul_of_nonneg_right h2 hVq0
  have ha_le : a ≤ √Vq := by
    refine Real.le_sqrt_of_sq_le ?_
    calc a ^ 2 ≤ 2 * δ * Vq := ha2
      _ ≤ 1 * Vq := mul_le_mul_of_nonneg_right hδ1 hVq0
      _ = Vq := one_mul _
  have habs2 : 4 * K₀ ^ 2 * a ^ 2 / lam ≤ Vq / 2 := by
    rw [div_le_iff₀ hlam]
    calc 4 * K₀ ^ 2 * a ^ 2 ≤ 4 * K₀ ^ 2 * (2 * δ * Vq) :=
          mul_le_mul_of_nonneg_left ha2 (by positivity)
      _ = 8 * K₀ ^ 2 * δ * Vq := by ring
      _ ≤ lam / 2 * Vq := mul_le_mul_of_nonneg_right hδ2 hVq0
      _ = Vq / 2 * lam := by ring
  -- the weighted negative depth velocity
  have hneg : √Vq * max (-r') 0 ≤ 2 * (e + C₀ * D) := by
    rcases le_or_gt 0 r' with hr0 | hr0
    · rw [max_eq_right (neg_nonpos.2 hr0), mul_zero]
      positivity
    · rw [max_eq_left (neg_nonneg.2 hr0.le)]
      have hz : 0 < -r' := neg_pos.2 hr0
      -- `(−r') V ≤ a e + |c|`
      have h1 : -r' * Vq ≤ a * e + 2 * (K₀ * xv) * a := by
        have := neg_le_abs c
        linarith [hb1, hb2, hcabs]
      have h2 : xv ≤ (Fintype.card J : ℝ) / lam * (D + 2 * B * a * (-r')) := by
        rwa [abs_of_neg hr0] at hxbound
      have h3 : -r' * Vq ≤ a * e + 2 * (K₀ * ((Fintype.card J : ℝ) / lam *
          (D + 2 * B * a * (-r')))) * a := by
        refine h1.trans ?_
        have := mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left h2 (by positivity : (0 : ℝ) ≤ 2 * K₀)) ha0
        linarith
      have h4 : -r' * (Vq - 4 * K₀ ^ 2 * a ^ 2 / lam) ≤ a * (e + C₀ * D) := by
        have : 2 * (K₀ * ((Fintype.card J : ℝ) / lam * (D + 2 * B * a * (-r')))) * a =
            a * (C₀ * D) + (-r') * (4 * K₀ ^ 2 * a ^ 2 / lam) := by
          rw [hC₀, hK₀]
          field_simp
          ring
        linarith [h3, this]
      have h5 : -r' * (Vq / 2) ≤ a * (e + C₀ * D) := by
        have : Vq / 2 ≤ Vq - 4 * K₀ ^ 2 * a ^ 2 / lam := by linarith
        exact (mul_le_mul_of_nonneg_left this hz.le).trans h4
      have h6 : -r' * Vq ≤ 2 * √Vq * (e + C₀ * D) := by
        have hae : a * (e + C₀ * D) ≤ √Vq * (e + C₀ * D) :=
          mul_le_mul_of_nonneg_right ha_le (by positivity)
        linarith
      rcases eq_or_lt_of_le hVq0 with hV0 | hVpos
      · rw [← hV0, Real.sqrt_zero, zero_mul]
        positivity
      · have hsq : √Vq * √Vq = Vq := Real.mul_self_sqrt hVq0
        have hsqpos : 0 < √Vq := Real.sqrt_pos.2 hVpos
        refine le_of_mul_le_mul_left ?_ hsqpos
        calc √Vq * (√Vq * -r') = -r' * (√Vq * √Vq) := by ring
          _ = -r' * Vq := by rw [hsq]
          _ ≤ 2 * √Vq * (e + C₀ * D) := h6
          _ = √Vq * (2 * (e + C₀ * D)) := by ring
  -- the response speed
  have hspeed : √(responseSpeedSq hS ν hh t) ≤ K₀ * xv + |r'| * √Vq := by
    rw [hspeed_eq]
    have hg' : Bdd fun y ↦ (-r') * dirLoss S u y := Bdd.const_mul _ (bdd_dirLoss hS u)
    refine (sqrt_lawCov_add_self_le q hfv' hg').trans ?_
    have h2 : √(lawCov q (dirLoss S v') (dirLoss S v')) ≤ K₀ * xv :=
      Real.sqrt_le_iff.2 ⟨by positivity, lawCov_self_le_sq q hfv' hKv⟩
    have h3 : √(lawCov q (fun y ↦ (-r') * dirLoss S u y) (fun y ↦ (-r') * dirLoss S u y)) =
        |r'| * √Vq := by
      rw [lawCov_const_mul_self, Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq_eq_abs, abs_neg,
        ← hVq]
    rw [h3]
    linarith
  -- the tilt comparison with the reference ray
  have hexp2 : exp (2 * 1) = exp 1 ^ 2 := by rw [sq, ← Real.exp_add]; norm_num
  have hsqrt1 : √Vq ≤ exp 1 * √g := by
    calc √Vq ≤ √(exp (2 * 1) * g) := Real.sqrt_le_sqrt hray.2
      _ = exp 1 * √g := by rw [Real.sqrt_mul (exp_pos _).le, hexp2, Real.sqrt_sq (exp_pos _).le]
  have hsqrt2 : √g ≤ exp 1 * √Vq := by
    have h1 : g ≤ exp (2 * 1) * Vq := by
      have := hray.1
      rw [Real.exp_neg] at this
      exact (inv_mul_le_iff₀ (exp_pos _)).1 this
    calc √g ≤ √(exp (2 * 1) * Vq) := Real.sqrt_le_sqrt h1
      _ = exp 1 * √Vq := by rw [Real.sqrt_mul (exp_pos _).le, hexp2, Real.sqrt_sq (exp_pos _).le]
  refine ⟨?_, ?_, hrt⟩
  · -- speed bound
    calc √(responseSpeedSq hS ν hh t) ≤ K₀ * xv + |r'| * √Vq := hspeed
      _ ≤ K₀ * ((Fintype.card J : ℝ) / lam * (D + 2 * B * a * |r'|)) + |r'| * √Vq :=
          add_le_add (mul_le_mul_of_nonneg_left hxbound hK₀0) le_rfl
      _ ≤ K₀ * ((Fintype.card J : ℝ) / lam * (D + 2 * B * √Vq * |r'|)) + |r'| * √Vq := by
          gcongr
      _ = K₀ * (Fintype.card J : ℝ) / lam * D +
          (2 * K₀ * (Fintype.card J : ℝ) * B / lam + 1) * (√Vq * |r'|) := by
          field_simp
          ring
      _ ≤ K₀ * (Fintype.card J : ℝ) / lam * D +
          (2 * K₀ * (Fintype.card J : ℝ) * B / lam + 1) * exp 1 * (√g * |r'|) := by
          have : √Vq * |r'| ≤ exp 1 * (√g * |r'|) := by
            rw [← mul_assoc]
            exact mul_le_mul_of_nonneg_right hsqrt1 (abs_nonneg _)
          have hC : 0 ≤ 2 * K₀ * (Fintype.card J : ℝ) * B / lam + 1 := by positivity
          linarith [mul_le_mul_of_nonneg_left this hC]
  · -- negative variation bound
    calc √g * max (-r') 0 ≤ exp 1 * √Vq * max (-r') 0 :=
          mul_le_mul_of_nonneg_right hsqrt2 (le_max_right _ _)
      _ = exp 1 * (√Vq * max (-r') 0) := by ring
      _ ≤ exp 1 * (2 * (e + C₀ * D)) := mul_le_mul_of_nonneg_left hneg (exp_pos _).le
      _ = 2 * exp 1 * e + 2 * exp 1 * C₀ * D := by ring

end Estimates

end Laplace.Multi
