/-
Copyright (c) 2026 Timaeus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Timaeus
-/
import Laplace.Multi.ReconstructionDerivative
import Laplace.Multi.AtlasEnergy
import Laplace.Multi.SusceptibilityDefect

/-!
# The Fisher-orthogonal retraction

Reconstruction `Π` is the identity on the family (`responseProjection_mean_familyMeasure`), and its
differential at a reconstructed law `Q = Π(M)`, `M` interior, is the Fisher-orthogonal projection
onto
the tangent space of the family. Along the normalised tilt `D_t = e^{th} Q / E_Q e^{th}` of `Q` by
a bounded `h`, with `M_t = E_{D_t} S` its response,

`∫ |q_{M_t} − q_M − t · q_M (⟨a, S⟩ − ⟨a, M⟩)| dν = o(t)`,

where `a ∈ 𝕍` is the regression coefficient of `h` on the centred features under `Q`
(`Cov_Q(S_j, ⟨a,S⟩) = Cov_Q(S_j, h)`), so that `⟨a, S − M⟩ = B_M h` is the `L²(Q)`-orthogonal
projection of `h` onto the span of the centred features. Dividing by `q_M`, the derivative of the
density ratio `dΠ(M_t)/dQ` at `t = 0` is `B_M h` in `L¹(Q)`. The proof composes the
response-coordinate derivative of the reconstruction density with the tilt response `t ↦ M_t`,
whose velocity `u = Cov_Q(S, h)` is the image of `−a` under the chart derivative.
-/

open MeasureTheory Filter Topology Set Asymptotics
open scoped ENNReal

namespace Laplace.Multi

section Score

variable {X : Type*} [MeasurableSpace X] {J : Type*} [Fintype J] {S : J → X → ℝ}
  (hS : ∀ j, Bdd (S j)) (ν : Measure X) [IsProbabilityMeasure ν] {B : ℝ} (hB0 : 0 ≤ B)
  (hB : ∀ j x, |S j x| ≤ B)
include hS hB0 hB

/-- The centred score of a direction is bounded by `2K‖v‖`. -/
theorem abs_score_le (θ₀ v : J → ℝ) (x : X) :
    |dotJ v (famMean S ν θ₀) - dirLoss S v x| ≤ 2 * ((Fintype.card J : ℝ) * B) * ‖v‖ := by
  refine (abs_sub _ _).trans ?_
  have h1 := abs_dotJ_famMean_le hS ν hB0 hB θ₀ v
  have h2 := abs_dirLoss_le_card_mul hB0 hB v x
  linarith

omit [MeasurableSpace X] hS hB0 hB in
theorem score_sub (m v w : J → ℝ) (x : X) :
    (dotJ v m - dirLoss S v x) - (dotJ w m - dirLoss S w x) =
      dotJ (v - w) m - dirLoss S (v - w) x := by
  simp only [dotJ, dirLoss, Pi.sub_apply, sub_mul, Finset.sum_sub_distrib]
  ring

theorem integrable_famDens_mul_score (θ₀ v : J → ℝ) :
    Integrable (fun x ↦ famDens S ν θ₀ x * (dotJ v (famMean S ν θ₀) - dirLoss S v x)) ν := by
  have hm : Measurable (fun x ↦ dotJ v (famMean S ν θ₀) - dirLoss S v x) :=
    measurable_const.sub (bdd_dirLoss hS v).1
  have h := (integrable_famDens hS ν θ₀).bdd_mul (c := 2 * ((Fintype.card J : ℝ) * B) * ‖v‖)
    hm.aestronglyMeasurable (Eventually.of_forall fun x ↦ by
      rw [Real.norm_eq_abs]; exact abs_score_le hS ν hB0 hB θ₀ v x)
  exact h.congr (Eventually.of_forall fun x ↦ mul_comm _ _)

/-- The `L¹` norm of the density times the score is at most `2K‖v‖`. -/
theorem integral_famDens_mul_abs_score_le (θ₀ v : J → ℝ) :
    ∫ x, famDens S ν θ₀ x * |dotJ v (famMean S ν θ₀) - dirLoss S v x| ∂ν ≤
      2 * ((Fintype.card J : ℝ) * B) * ‖v‖ := by
  have hint : Integrable (fun x ↦ famDens S ν θ₀ x * (2 * ((Fintype.card J : ℝ) * B) * ‖v‖)) ν :=
    (integrable_famDens hS ν θ₀).mul_const _
  calc ∫ x, famDens S ν θ₀ x * |dotJ v (famMean S ν θ₀) - dirLoss S v x| ∂ν
      ≤ ∫ x, famDens S ν θ₀ x * (2 * ((Fintype.card J : ℝ) * B) * ‖v‖) ∂ν :=
        integral_mono_of_nonneg (Eventually.of_forall fun x ↦
          mul_nonneg (famDens_nonneg hS ν θ₀ x) (abs_nonneg _)) hint
          (Eventually.of_forall fun x ↦ mul_le_mul_of_nonneg_left
            (abs_score_le hS ν hB0 hB θ₀ v x) (famDens_nonneg hS ν θ₀ x))
    _ = 2 * ((Fintype.card J : ℝ) * B) * ‖v‖ := by
        rw [integral_mul_const, integral_famDens hS ν, one_mul]

end Score

theorem dotJ_single {J : Type*} [Fintype J] [DecidableEq J] (j : J) (w : J → ℝ) :
    dotJ (Pi.single j 1) w = w j := by
  simp [dotJ, Pi.single_apply]

section Retraction

variable {X : Type*} [MeasurableSpace X] [Nonempty X] {J : Type*} [Fintype J] [Nonempty J]
  {S : J → X → ℝ} (hS : ∀ j, Bdd (S j)) (ν : Measure X) [IsProbabilityMeasure ν]
  {M : J → ℝ} (hrel : M ∈ intrinsicInterior ℝ (momentBody ν (fun _ ↦ (1 : ℝ)) S))
  {h : X → ℝ} (hh : Bdd h)
include hS hrel hh

omit hrel in
/-- The response of a bounded tilt of a family member lies in the moment body. -/
theorem tiltResponse_familyMeasure_mem_momentBody (θ : J → ℝ) (t : ℝ) :
    tiltResponse S (familyMeasure ν (fun _ ↦ (1 : ℝ)) (fun _ ↦ (0 : ℝ)) S 1 θ) h t ∈
      momentBody ν (fun _ ↦ (1 : ℝ)) S := by
  have hF : Bdd fun x ↦ -1 * dirLoss S θ x + t * h x :=
    (Bdd.const_mul (-1) (bdd_dirLoss hS θ)).add (Bdd.const_mul t hh)
  have e : (familyMeasure ν (fun _ ↦ (1 : ℝ)) (fun _ ↦ (0 : ℝ)) S 1 θ).tilted (fun x ↦ t * h x) =
      ν.tilted fun x ↦ -1 * dirLoss S θ x + t * h x := by
    rw [familyMeasure_one_zero_eq_tilted hS ν θ, tilted_tilted (integrable_exp_of_bdd ν
      (Bdd.const_mul (-1) (bdd_dirLoss hS θ))) (fun x ↦ t * h x)]
    rfl
  have hP : IsProbabilityMeasure (ν.tilted fun x ↦ -1 * dirLoss S θ x + t * h x) :=
    isProbabilityMeasure_tilted (integrable_exp_of_bdd ν hF)
  have hfin : genRate ν S (tiltResponse S (familyMeasure ν (fun _ ↦ (1 : ℝ)) (fun _ ↦ (0 : ℝ)) S 1
      θ) h t) ≠ ⊤ := by
    unfold tiltResponse
    rw [e]
    refine ne_top_of_le_ne_top ?_ (genRate_le_klDiv ν hS (ν.tilted fun x ↦ -1 * dirLoss S θ x +
      t * h x) rfl)
    rw [klDiv_tilted_eq ν hF]
    exact ENNReal.ofReal_ne_top
  exact mem_momentBody_of_genRate_ne_top hS ν hfin

omit hrel hh in
/-- The velocity of the tilt response is the image of minus the regression coefficient under the
chart derivative. -/
theorem lawCov_eq_chartDeriv_neg {a : J → ℝ} (ha : a ∈ dirSpan ν (fun _ ↦ (1 : ℝ)) S)
    (hreg : ∀ j, lawCov (familyMeasure ν (fun _ ↦ (1 : ℝ)) (fun _ ↦ (0 : ℝ)) S 1
      (responseTheta measurable_const (integrable_const 1) (fun _ ↦ one_pos) (one_integral_pos ν)
        hS M)) (S j) (dirLoss S a) =
      lawCov (familyMeasure ν (fun _ ↦ (1 : ℝ)) (fun _ ↦ (0 : ℝ)) S 1
        (responseTheta measurable_const (integrable_const 1) (fun _ ↦ one_pos)
          (one_integral_pos ν) hS M)) (S j) h) :
    (fun j ↦ lawCov (familyMeasure ν (fun _ ↦ (1 : ℝ)) (fun _ ↦ (0 : ℝ)) S 1
      (responseTheta measurable_const (integrable_const 1) (fun _ ↦ one_pos) (one_integral_pos ν)
        hS M)) (S j) h) =
      (chartDeriv measurable_const (integrable_const 1) (fun _ ↦ one_pos) (one_integral_pos ν) hS
        (responseTheta measurable_const (integrable_const 1) (fun _ ↦ one_pos)
          (one_integral_pos ν) hS M) (-⟨a, ha⟩) : J → ℝ) := by
  classical
  obtain ⟨θ₀, hθ₀⟩ : ∃ θ₀, θ₀ = responseTheta measurable_const (integrable_const 1)
    (fun _ ↦ one_pos) (one_integral_pos ν) hS M := ⟨_, rfl⟩
  rw [← hθ₀] at hreg ⊢
  obtain ⟨Q, hQ⟩ : ∃ Q, Q = familyMeasure ν (fun _ ↦ (1 : ℝ)) (fun _ ↦ (0 : ℝ)) S 1 θ₀ := ⟨_, rfl⟩
  have hQP : IsProbabilityMeasure Q := by
    rw [hQ]
    exact isProbabilityMeasure_familyMeasure measurable_const (integrable_const 1)
      (fun _ ↦ one_pos) (one_integral_pos ν) measurable_const (M₀ := 0) (fun _ ↦ by simp) hS
      (t := 1) θ₀
  rw [← hQ] at hreg ⊢
  funext j
  have h1 := dotJ_chartDeriv measurable_const (integrable_const 1) (fun _ ↦ one_pos)
    (one_integral_pos ν) hS θ₀ (Pi.single j 1) (-⟨a, ha⟩)
  rw [dotJ_single, priorCov_eq_lawCov_familyMeasure hS ν, ← hQ] at h1
  rw [h1]
  have e : dirLoss S (-⟨a, ha⟩ : dirSpan ν (fun _ ↦ (1 : ℝ)) S) = fun x ↦ -dirLoss S a x := by
    funext x
    rw [Submodule.coe_neg]
    exact dirLoss_neg (S := S) a x
  rw [e, lawCov_neg_right_eq, neg_neg,
    lawCov_dirLoss_left hS Q (Pi.single j 1) _ (bdd_dirLoss hS a)]
  simp only [Pi.single_apply, ite_mul, one_mul, zero_mul, Finset.sum_ite_eq', Finset.mem_univ,
    if_true]
  exact (hreg j).symm

/-- **The Fisher-orthogonal retraction**: along the tilt `D_t = e^{th}Π(M)/Z_t` of the
reconstruction
of an interior response, the reconstruction density of the tilted response satisfies
`∫ |q_{M_t} − q_M − t q_M(⟨a,S⟩ − ⟨a,M⟩)| dν = o(t)`, with `a` the regression coefficient of `h` on
the
centred features under `Π(M)`; the differential of reconstruction at `Π(M)` is the `L²(Π(M))`
projection of the score onto the span of the centred features. -/
theorem isLittleO_retraction_remainder :
    ∃ a ∈ dirSpan ν (fun _ ↦ (1 : ℝ)) S,
      (∀ j, lawCov (responseProjection hS ν M) (S j) (dirLoss S a) =
        lawCov (responseProjection hS ν M) (S j) h) ∧
      (fun t ↦ ∫ x, |famDens S ν (responseTheta measurable_const (integrable_const 1)
          (fun _ ↦ one_pos) (one_integral_pos ν) hS
            (tiltResponse S (responseProjection hS ν M) h t)) x -
        famDens S ν (responseTheta measurable_const (integrable_const 1) (fun _ ↦ one_pos)
          (one_integral_pos ν) hS M) x -
        t * (famDens S ν (responseTheta measurable_const (integrable_const 1) (fun _ ↦ one_pos)
          (one_integral_pos ν) hS M) x * (dirLoss S a x - dotJ a M))| ∂ν)
        =o[𝓝 0] fun t ↦ t := by
  obtain ⟨θ₀, hθ₀⟩ : ∃ θ₀, θ₀ = responseTheta measurable_const (integrable_const 1)
    (fun _ ↦ one_pos) (one_integral_pos ν) hS M := ⟨_, rfl⟩
  obtain ⟨Q, hQ'⟩ : ∃ Q, Q = familyMeasure ν (fun _ ↦ (1 : ℝ)) (fun _ ↦ (0 : ℝ)) S 1 θ₀ := ⟨_, rfl⟩
  have hQ : responseProjection hS ν M = Q := by
    rw [hQ', hθ₀]
    exact responseProjection_eq_familyMeasure_responseTheta hS ν hrel
  have hQP : IsProbabilityMeasure Q := by
    rw [hQ']
    exact isProbabilityMeasure_familyMeasure measurable_const (integrable_const 1)
      (fun _ ↦ one_pos) (one_integral_pos ν) measurable_const (M₀ := 0) (fun _ ↦ by simp) hS
      (t := 1) θ₀
  obtain ⟨a, ha, hreg⟩ := exists_regression_coefficient hS ν (M := M) 1 hh
  rw [atlasTheta_one hS ν] at hreg
  have hD := lawCov_eq_chartDeriv_neg hS ν ha hreg
  rw [← hθ₀, ← hQ'] at hreg hD
  refine ⟨a, ha, fun j ↦ by rw [hQ]; exact hreg j, ?_⟩
  rw [hQ, ← hθ₀]
  -- the response curve and its velocity
  obtain ⟨u, hu_def⟩ : ∃ u : J → ℝ, u = fun j ↦ lawCov Q (S j) h := ⟨_, rfl⟩
  rw [← hu_def] at hD
  have hu : u ∈ dirSpan ν (fun _ ↦ (1 : ℝ)) S := by
    rw [hD]
    exact (chartDeriv measurable_const (integrable_const 1) (fun _ ↦ one_pos)
      (one_integral_pos ν) hS θ₀ (-⟨a, ha⟩)).2
  have hM0 : tiltResponse S Q h 0 = M := by
    rw [tiltResponse_zero Q h, hQ', mean_familyMeasure_one_zero hS ν θ₀, hθ₀]
    exact meanMap_responseTheta measurable_const (integrable_const 1) (fun _ ↦ one_pos)
      (one_integral_pos ν) hS hrel
  have hM : M ∈ momentBody ν (fun _ ↦ (1 : ℝ)) S := intrinsicInterior_subset hrel
  have hmem : ∀ t, tiltResponse S Q h t - M ∈ dirSpan ν (fun _ ↦ (1 : ℝ)) S := fun t ↦ by
    have hmemt : tiltResponse S Q h t ∈ momentBody ν (fun _ ↦ (1 : ℝ)) S := by
      rw [hQ']
      exact tiltResponse_familyMeasure_mem_momentBody hS ν hh θ₀ t
    have h1 := sub_mem_dirSpan_of_mem_momentBody measurable_const (integrable_const 1)
      (fun _ ↦ one_pos) (one_integral_pos ν) hS hmemt
    have h2 := sub_mem_dirSpan_of_mem_momentBody measurable_const (integrable_const 1)
      (fun _ ↦ one_pos) (one_integral_pos ν) hS hM
    have := Submodule.sub_mem _ h1 h2
    rwa [sub_sub_sub_cancel_right] at this
  obtain ⟨z, hz⟩ : ∃ z : ℝ → dirSpan ν (fun _ ↦ (1 : ℝ)) S,
    z = fun t ↦ ⟨tiltResponse S Q h t - M, hmem t⟩ := ⟨_, rfl⟩
  have hzc : ∀ t, (z t : J → ℝ) = tiltResponse S Q h t - M := fun t ↦ by rw [hz]
  have hder : HasDerivAt (fun t ↦ tiltResponse S Q h t - M) u 0 := by
    rw [hu_def]
    exact (hasDerivAt_tiltResponse hS Q hh).sub_const M
  have hzt : Tendsto z (𝓝 0) (𝓝 0) := by
    rw [tendsto_subtype_rng]
    simp only [hzc, Submodule.coe_zero]
    have := hder.continuousAt.tendsto
    rwa [hM0, sub_self] at this
  have hzO : (fun t ↦ ‖z t‖) =O[𝓝 0] fun t ↦ t := by
    have := hder.isBigO_sub
    simp only [sub_zero, hM0, sub_self] at this
    refine this.norm_left.congr_left fun t ↦ ?_
    rw [← Submodule.norm_coe (z t), hzc]
  have hzo : (fun t ↦ (z t : J → ℝ) - t • u) =o[𝓝 0] fun t ↦ t := by
    have := hasDerivAt_iff_isLittleO_nhds_zero.1 hder
    simp only [zero_add, hM0, sub_self, sub_zero] at this
    refine this.congr_left fun t ↦ ?_
    rw [hzc]
  -- the chart derivative sends the velocity to minus the regression coefficient
  obtain ⟨L, hL⟩ : ∃ L : dirSpan ν (fun _ ↦ (1 : ℝ)) S →L[ℝ] dirSpan ν (fun _ ↦ (1 : ℝ)) S,
    L = ((chartDerivEquiv measurable_const (integrable_const 1) (fun _ ↦ one_pos)
      (one_integral_pos ν) hS θ₀).symm : _ →L[ℝ] _) := ⟨_, rfl⟩
  have e1 : (chartDerivEquiv measurable_const (integrable_const 1) (fun _ ↦ one_pos)
      (one_integral_pos ν) hS θ₀ : dirSpan ν (fun _ ↦ (1 : ℝ)) S →L[ℝ]
        dirSpan ν (fun _ ↦ (1 : ℝ)) S) (-⟨a, ha⟩) = ⟨u, hu⟩ := by
    rw [coe_chartDerivEquiv]
    exact Subtype.ext hD.symm
  have hLu : L ⟨u, hu⟩ = -⟨a, ha⟩ := by
    rw [← e1, hL]
    exact (chartDerivEquiv measurable_const (integrable_const 1) (fun _ ↦ one_pos)
      (one_integral_pos ν) hS θ₀).symm_apply_apply _
  -- the reconstruction remainder along the curve
  have hrem := ((isLittleO_reconstruction_density_remainder hS ν hrel).comp_tendsto
    hzt).trans_isBigO hzO
  rw [← hθ₀, ← hL] at hrem
  -- constants
  choose Mj hMj using fun j ↦ (hS j).2
  obtain ⟨B, hB0, hB⟩ : ∃ B : ℝ, 0 ≤ B ∧ ∀ j x, |S j x| ≤ B :=
    ⟨∑ j, |Mj j|, Finset.sum_nonneg fun j _ ↦ abs_nonneg _, fun j x ↦
      (hMj j x).trans ((le_abs_self _).trans (Finset.single_le_sum
        (f := fun j ↦ |Mj j|) (fun j _ ↦ abs_nonneg _) (Finset.mem_univ j)))⟩
  obtain ⟨K₀, hK₀⟩ : ∃ K₀ : ℝ, K₀ = 2 * ((Fintype.card J : ℝ) * B) := ⟨_, rfl⟩
  have hK₀0 : 0 ≤ K₀ := by rw [hK₀]; positivity
  have hmean : famMean S ν θ₀ = M := by
    rw [famMean_eq_meanMap hS ν, hθ₀]
    exact meanMap_responseTheta measurable_const (integrable_const 1) (fun _ ↦ one_pos)
      (one_integral_pos ν) hS hrel
  -- the linearisation error term
  have hf2 : (fun t ↦ K₀ * ‖L‖ * ‖(z t : J → ℝ) - t • u‖) =o[𝓝 0] fun t ↦ t := by
    have := hzo.norm_left.const_mul_left (K₀ * ‖L‖)
    exact this
  refine IsBigO.trans_isLittleO (g := fun t ↦ (∫ x, |famDens S ν (responseTheta measurable_const
      (integrable_const 1) (fun _ ↦ one_pos) (one_integral_pos ν) hS (M + z t)) x -
      famDens S ν θ₀ x - famDens S ν θ₀ x * (dotJ (L (z t) : J → ℝ) M -
        dirLoss S (L (z t) : J → ℝ) x)| ∂ν) + K₀ * ‖L‖ * ‖(z t : J → ℝ) - t • u‖) ?_
    (hrem.add hf2)
  refine IsBigO.of_bound 1 (Eventually.of_forall fun t ↦ ?_)
  rw [one_mul]
  have hMz : M + z t = tiltResponse S Q h t := by rw [hzc]; abel
  rw [hMz]
  have hI0 := integrable_famDens hS ν θ₀
  have hI1 := integrable_famDens hS ν (responseTheta measurable_const (integrable_const 1)
    (fun _ ↦ one_pos) (one_integral_pos ν) hS (tiltResponse S Q h t))
  -- the difference of the two scores
  have hLsplit : (L (z t) : J → ℝ) = (L (z t - t • ⟨u, hu⟩) : J → ℝ) + t • (-a) := by
    rw [map_sub, map_smul, hLu, Submodule.coe_sub, Submodule.coe_smul, Submodule.coe_neg]
    abel
  have hscore : ∀ x, famDens S ν θ₀ x * (dotJ (L (z t) : J → ℝ) M - dirLoss S (L (z t) : J → ℝ) x) -
      t * (famDens S ν θ₀ x * (dirLoss S a x - dotJ a M)) =
      famDens S ν θ₀ x * (dotJ (L (z t - t • ⟨u, hu⟩) : J → ℝ) M -
        dirLoss S (L (z t - t • ⟨u, hu⟩) : J → ℝ) x) := fun x ↦ by
    rw [hLsplit]
    have e2 : ∀ v w : J → ℝ, dotJ (v + w) M - dirLoss S (v + w) x =
        (dotJ v M - dirLoss S v x) + (dotJ w M - dirLoss S w x) := fun v w ↦ by
      simp only [dotJ, dirLoss, Pi.add_apply, add_mul, Finset.sum_add_distrib]
      ring
    rw [e2]
    have e3 : dotJ (t • -a) M - dirLoss S (t • -a) x = t * (dirLoss S a x - dotJ a M) := by
      simp only [dotJ, dirLoss, Pi.smul_apply, Pi.neg_apply, smul_eq_mul, mul_sub, Finset.mul_sum,
        mul_neg, neg_mul, Finset.sum_neg_distrib, mul_assoc]
      ring
    rw [e3]
    ring
  have hpt : ∀ x, |famDens S ν (responseTheta measurable_const (integrable_const 1)
      (fun _ ↦ one_pos) (one_integral_pos ν) hS (tiltResponse S Q h t)) x - famDens S ν θ₀ x -
      t * (famDens S ν θ₀ x * (dirLoss S a x - dotJ a M))| ≤
      |famDens S ν (responseTheta measurable_const (integrable_const 1) (fun _ ↦ one_pos)
        (one_integral_pos ν) hS (tiltResponse S Q h t)) x - famDens S ν θ₀ x -
        famDens S ν θ₀ x * (dotJ (L (z t) : J → ℝ) M - dirLoss S (L (z t) : J → ℝ) x)| +
      famDens S ν θ₀ x * |dotJ (L (z t - t • ⟨u, hu⟩) : J → ℝ) M -
        dirLoss S (L (z t - t • ⟨u, hu⟩) : J → ℝ) x| := fun x ↦ by
    have e := hscore x
    calc |famDens S ν (responseTheta measurable_const (integrable_const 1)
          (fun _ ↦ one_pos) (one_integral_pos ν) hS (tiltResponse S Q h t)) x -
          famDens S ν θ₀ x - t * (famDens S ν θ₀ x * (dirLoss S a x - dotJ a M))|
        = |(famDens S ν (responseTheta measurable_const (integrable_const 1) (fun _ ↦ one_pos)
            (one_integral_pos ν) hS (tiltResponse S Q h t)) x - famDens S ν θ₀ x -
            famDens S ν θ₀ x * (dotJ (L (z t) : J → ℝ) M - dirLoss S (L (z t) : J → ℝ) x)) +
          famDens S ν θ₀ x * (dotJ (L (z t - t • ⟨u, hu⟩) : J → ℝ) M -
            dirLoss S (L (z t - t • ⟨u, hu⟩) : J → ℝ) x)| := by
          rw [← e]
          ring_nf
      _ ≤ _ := by
          refine (abs_add_le _ _).trans (add_le_add le_rfl ?_)
          rw [abs_mul, abs_of_nonneg (famDens_nonneg hS ν θ₀ x)]
  have hg1 : Integrable (fun x ↦ |famDens S ν (responseTheta measurable_const (integrable_const 1)
      (fun _ ↦ one_pos) (one_integral_pos ν) hS (tiltResponse S Q h t)) x - famDens S ν θ₀ x -
      famDens S ν θ₀ x * (dotJ (L (z t) : J → ℝ) M - dirLoss S (L (z t) : J → ℝ) x)|) ν := by
    have h1 := integrable_famDens_mul_score hS ν hB0 hB θ₀ (L (z t) : J → ℝ)
    rw [hmean] at h1
    have h2 := (hI1.sub hI0).sub h1
    exact h2.abs
  have hg2 : Integrable (fun x ↦ famDens S ν θ₀ x * |dotJ (L (z t - t • ⟨u, hu⟩) : J → ℝ) M -
      dirLoss S (L (z t - t • ⟨u, hu⟩) : J → ℝ) x|) ν := by
    have h1 := integrable_famDens_mul_score hS ν hB0 hB θ₀ (L (z t - t • ⟨u, hu⟩) : J → ℝ)
    rw [hmean] at h1
    have h2 := h1.abs
    refine h2.congr (Eventually.of_forall fun x ↦ ?_)
    simp only [abs_mul, abs_of_nonneg (famDens_nonneg hS ν θ₀ x)]
  have hsecond : ∫ x, famDens S ν θ₀ x * |dotJ (L (z t - t • ⟨u, hu⟩) : J → ℝ) M -
      dirLoss S (L (z t - t • ⟨u, hu⟩) : J → ℝ) x| ∂ν ≤ K₀ * ‖L‖ * ‖(z t : J → ℝ) - t • u‖ := by
    have h1 := integral_famDens_mul_abs_score_le hS ν hB0 hB θ₀ (L (z t - t • ⟨u, hu⟩) : J → ℝ)
    rw [hmean, ← hK₀] at h1
    refine h1.trans ?_
    rw [Submodule.norm_coe, mul_assoc]
    refine mul_le_mul_of_nonneg_left ?_ hK₀0
    refine (L.le_opNorm _).trans ?_
    rw [← Submodule.norm_coe, Submodule.coe_sub, Submodule.coe_smul]
  rw [Real.norm_eq_abs, abs_of_nonneg (integral_nonneg fun x ↦ abs_nonneg _), Real.norm_eq_abs,
    abs_of_nonneg (add_nonneg (integral_nonneg fun x ↦ abs_nonneg _) (by positivity))]
  calc ∫ x, |famDens S ν (responseTheta measurable_const (integrable_const 1)
        (fun _ ↦ one_pos) (one_integral_pos ν) hS (tiltResponse S Q h t)) x - famDens S ν θ₀ x -
        t * (famDens S ν θ₀ x * (dirLoss S a x - dotJ a M))| ∂ν
      ≤ ∫ x, (|famDens S ν (responseTheta measurable_const (integrable_const 1)
          (fun _ ↦ one_pos) (one_integral_pos ν) hS (tiltResponse S Q h t)) x -
          famDens S ν θ₀ x - famDens S ν θ₀ x * (dotJ (L (z t) : J → ℝ) M -
            dirLoss S (L (z t) : J → ℝ) x)| +
          famDens S ν θ₀ x * |dotJ (L (z t - t • ⟨u, hu⟩) : J → ℝ) M -
            dirLoss S (L (z t - t • ⟨u, hu⟩) : J → ℝ) x|) ∂ν :=
        integral_mono_of_nonneg (Eventually.of_forall fun x ↦ abs_nonneg _) (hg1.add hg2)
          (Eventually.of_forall hpt)
    _ = (∫ x, |famDens S ν (responseTheta measurable_const (integrable_const 1)
          (fun _ ↦ one_pos) (one_integral_pos ν) hS (tiltResponse S Q h t)) x -
          famDens S ν θ₀ x - famDens S ν θ₀ x * (dotJ (L (z t) : J → ℝ) M -
            dirLoss S (L (z t) : J → ℝ) x)| ∂ν) +
        ∫ x, famDens S ν θ₀ x * |dotJ (L (z t - t • ⟨u, hu⟩) : J → ℝ) M -
            dirLoss S (L (z t - t • ⟨u, hu⟩) : J → ℝ) x| ∂ν := integral_add hg1 hg2
    _ ≤ _ := add_le_add le_rfl hsecond

/-- The normalised form: the density ratio `dΠ(M_t)/dΠ(M)` has derivative `⟨a, S − M⟩` at `t = 0`
in `L¹(ν)`-weighted-by-`q_M`, i.e. `(1/t) ∫ |q_{M_t} − q_M − t q_M ⟨a, S − M⟩| dν → 0`. -/
theorem tendsto_retraction_quotient :
    ∃ a ∈ dirSpan ν (fun _ ↦ (1 : ℝ)) S,
      (∀ j, lawCov (responseProjection hS ν M) (S j) (dirLoss S a) =
        lawCov (responseProjection hS ν M) (S j) h) ∧
      Tendsto (fun t ↦ (∫ x, |famDens S ν (responseTheta measurable_const (integrable_const 1)
          (fun _ ↦ one_pos) (one_integral_pos ν) hS
            (tiltResponse S (responseProjection hS ν M) h t)) x -
        famDens S ν (responseTheta measurable_const (integrable_const 1) (fun _ ↦ one_pos)
          (one_integral_pos ν) hS M) x -
        t * (famDens S ν (responseTheta measurable_const (integrable_const 1) (fun _ ↦ one_pos)
          (one_integral_pos ν) hS M) x * (dirLoss S a x - dotJ a M))| ∂ν) / t) (𝓝 0) (𝓝 0) := by
  obtain ⟨a, ha, hreg, hlo⟩ := isLittleO_retraction_remainder hS ν hrel hh
  exact ⟨a, ha, hreg, hlo.tendsto_div_nhds_zero⟩

end Retraction

end Laplace.Multi
