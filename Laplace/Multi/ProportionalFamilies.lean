/-
Copyright (c) 2026 Timaeus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Timaeus
-/
import Mathlib
import Laplace.Multi.SingularPoint
import Laplace.Multi.AnalyticBridge
import Laplace.Multi.LocatedCutoff
import Laplace.Multi.CutoffRemoval

/-!
# Proportional Laplace families force equal germs

The germbij note asks (`q:proportional`) whether two analytic losses
`L₁ ≠ L₂` with a common zero locus can have *exactly proportional*
unnormalised Laplace families, `∫ φ e^{-tL₂} ≃ C(t) ∫ φ e^{-tL₁}` for
every test function `φ`, for some scalar series `C`. The note's answer is
no, by integration by parts: feeding `∂_v φ` and `φ ∂_v L₁` to the
proportionality and subtracting cancels the unknown scalar `C(t)` and
leaves `t ∫ φ ∂_v(L₂ - L₁) e^{-tL₂}` beyond all orders
(`proportional_families_superPoly_derivative`); the sector lower bound in
its square form (`analytic_square_not_superpolynomial`) then forces
`∂_v(L₂ - L₁)` to vanish near every zero of `L₂`, so `L₂ - L₁` is locally
constant, hence zero, near a common zero
(`proportional_families_force_germ_eq_at`) and on a neighbourhood of the
common zero locus (`proportional_families_force_eq_near`).

The hypothesis is formulated with an arbitrary function `C : ℝ → ℝ` and the
`SuperPoly` predicate (decay faster than every negative power): no
positivity, power-log structure, or leading-coefficient assumption on `C`
is needed, and only `L₂` needs to be nonnegative.

This generalises `Laplace.Multi.NormalizedSingular` (the same argument under
global smoothness of both losses and `L₁ ≥ 0`, with the normalised-expectation
corollaries `normalized_families_force_eq_near`,
`normalized_expectations_force_eq_near`): here the losses are only continuous
and analytic near the common zero locus, the hypotheses of the unnormalised
pencil theorem `pencil_families_force_eq_near`.
-/

open Asymptotics Filter MeasureTheory Set
open scoped Topology ContDiff Pointwise

namespace Laplace

variable {ι : Type*} [Fintype ι]

/-! ### `SuperPoly` under multiplication by `t` -/

theorem SuperPoly.id_mul {f : ℝ → ℝ} (hf : SuperPoly f) :
    SuperPoly fun t ↦ t * f t := by
  intro N
  refine ((isBigO_refl (fun t : ℝ ↦ t) atTop).mul_isLittleO (hf (N + 1))).congr'
    EventuallyEq.rfl ?_
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with t ht
  push_cast
  rw [neg_add, Real.rpow_add ht, Real.rpow_neg_one]
  field_simp

theorem SuperPoly.of_id_mul {f : ℝ → ℝ} (hf : SuperPoly fun t ↦ t * f t) :
    SuperPoly f := by
  intro N
  have h := (hf N).mul_isBigO (isBigO_refl (fun t : ℝ ↦ t⁻¹) atTop)
  refine (h.congr' ?_ EventuallyEq.rfl).trans_isBigO ?_
  · filter_upwards [eventually_gt_atTop (0 : ℝ)] with t ht
    field_simp
  · refine IsBigO.of_bound 1 ?_
    filter_upwards [eventually_ge_atTop (1 : ℝ)] with t ht
    rw [norm_mul, one_mul]
    refine mul_le_of_le_one_right (norm_nonneg _) ?_
    rw [Real.norm_eq_abs, abs_inv, abs_of_pos (by linarith)]
    exact inv_le_one_of_one_le₀ ht

/-! ### Products with a function that is only regular on an open set -/

omit [Fintype ι] in
/-- A product `g · f` with `f` continuous on an open set `V` containing the
support of `g` is continuous. -/
theorem continuous_mul_of_continuousOn_tsupport_subset {f g : (ι → ℝ) → ℝ} {V : Set (ι → ℝ)}
    (hV : IsOpen V) (hf : ContinuousOn f V) (hg : Continuous g)
    (hs : tsupport g ⊆ V) : Continuous fun w ↦ g w * f w := by
  refine continuous_iff_continuousAt.2 fun x ↦ ?_
  by_cases hx : x ∈ V
  · exact hg.continuousAt.mul ((hf x hx).continuousAt (hV.mem_nhds hx))
  · have hx' : x ∉ tsupport g := fun h ↦ hx (hs h)
    have hev : (fun y ↦ g y * f y) =ᶠ[𝓝 x] fun _ ↦ (0 : ℝ) := by
      filter_upwards [(isClosed_tsupport g).isOpen_compl.mem_nhds hx'] with y hy
      rw [image_eq_zero_of_notMem_tsupport hy, zero_mul]
    exact continuousAt_const.congr hev.symm

/-- A product `g · f` with `f` smooth on an open set `V` containing the
support of the smooth function `g` is smooth. -/
theorem contDiff_mul_of_contDiffOn_tsupport_subset {f g : (ι → ℝ) → ℝ} {V : Set (ι → ℝ)}
    (hV : IsOpen V) (hf : ContDiffOn ℝ ∞ f V) (hg : ContDiff ℝ ∞ g)
    (hs : tsupport g ⊆ V) : ContDiff ℝ ∞ fun w ↦ g w * f w := by
  refine contDiff_iff_contDiffAt.2 fun x ↦ ?_
  by_cases hx : x ∈ V
  · exact hg.contDiffAt.mul ((hf x hx).contDiffAt (hV.mem_nhds hx))
  · have hx' : x ∉ tsupport g := fun h ↦ hx (hs h)
    have hev : (fun y ↦ g y * f y) =ᶠ[𝓝 x] fun _ ↦ (0 : ℝ) := by
      filter_upwards [(isClosed_tsupport g).isOpen_compl.mem_nhds hx'] with y hy
      rw [image_eq_zero_of_notMem_tsupport hy, zero_mul]
    exact contDiffAt_const.congr_of_eventuallyEq hev

/-! ### The diagonal series lemma without the vanishing hypothesis -/

/-- `exists_least_nonzero_diagonal` without `g 0 = 0`: when the constant
term is nonzero, degree `0` and any vector of norm `3/2` serve. -/
theorem exists_least_nonzero_diagonal' [Nonempty ι] {g : (ι → ℝ) → ℝ}
    {p : FormalMultilinearSeries ℝ (ι → ℝ) ℝ} {r : ENNReal}
    (hg : HasFPowerSeriesOnBall g p 0 r)
    (hne : ∃ w ∈ Metric.eball (0 : ι → ℝ) r, g w ≠ 0) :
    ∃ m : ℕ, (∀ k, k < m → ∀ y : ι → ℝ, (p k) (fun _ ↦ y) = 0) ∧
      ∃ x₀ : ι → ℝ, (p m) (fun _ ↦ x₀) ≠ 0 ∧ ‖x₀‖ = 3 / 2 := by
  by_cases hg0 : g 0 = 0
  · exact Multi.exists_least_nonzero_diagonal hg hg0 hne
  · refine ⟨0, fun k hk ↦ absurd hk (Nat.not_lt_zero k), fun _ ↦ (3 / 2 : ℝ), ?_, ?_⟩
    · have hr0 : (0 : ι → ℝ) ∈ Metric.eball (0 : ι → ℝ) r :=
        Metric.mem_eball_self hg.r_pos
      have hsum := hg.hasSum hr0
      rw [add_zero] at hsum
      have hsingle : HasSum (fun n ↦ (p n) fun _ ↦ (0 : ι → ℝ))
          ((p 0) fun _ ↦ (0 : ι → ℝ)) := by
        refine hasSum_single 0 fun n hn ↦ ?_
        exact (p n).map_coord_zero ⟨0, Nat.pos_of_ne_zero hn⟩ rfl
      have hp0 : (p 0) (fun _ ↦ (0 : ι → ℝ)) = g 0 := hsingle.unique hsum
      have harg : (fun _ : Fin 0 ↦ (fun _ : ι ↦ (3 / 2 : ℝ))) =
          fun _ : Fin 0 ↦ (0 : ι → ℝ) := funext fun i ↦ i.elim0
      rw [harg, hp0]
      exact hg0
    · rw [pi_norm_const, Real.norm_eq_abs, abs_of_pos (by norm_num : (0 : ℝ) < 3 / 2)]

/-! ### The sector bound for a square observable -/

/-- **The sector bound, square form.** For `a` analytic at `0` with a nonzero
diagonal series term of degree `m`, `K ≥ 0` with a quadratic upper bound
near `0`, and a nonnegative bump `ψ` equal to `1` near `0`, the integral
`∫ ψ a² e^{-tK}` is bounded below by a constant times
`t^{-m - d/2}`, hence is not beyond all orders. -/
theorem analytic_square_not_superpolynomial
    (K a ψ : (ι → ℝ) → ℝ) {p : FormalMultilinearSeries ℝ (ι → ℝ) ℝ}
    {r : ENNReal} (m : ℕ) (ha : HasFPowerSeriesOnBall a p 0 r)
    (hlow : ∀ k, k < m → ∀ x : ι → ℝ, (p k) (fun _ ↦ x) = 0)
    {x₀ : ι → ℝ} (hx₀ : (p m) (fun _ ↦ x₀) ≠ 0) (hx₀n : ‖x₀‖ = 3 / 2)
    {C0 R : ℝ} (hC0 : 0 ≤ C0) (hR : 0 < R)
    (hquad : ∀ w : ι → ℝ, ‖w‖ ≤ R → K w ≤ C0 * ‖w‖ ^ 2)
    (hψ0 : ∀ w, 0 ≤ ψ w) (hψ1 : ∀ w : ι → ℝ, ‖w‖ ≤ R → ψ w = 1)
    (hint : ∀ t : ℝ, Integrable fun w ↦ ψ w * a w ^ 2 * Real.exp (-(t * K w))) :
    ¬ SuperPoly (fun t ↦ ∫ w, ψ w * a w ^ 2 * Real.exp (-(t * K w))) := by
  intro hdecay
  obtain ⟨C, u₁, hCnn, hu₁, hrem⟩ := analytic_remainder_bound ha m hlow
  have hPc : Continuous fun x : ι → ℝ ↦ (p m) (fun _ ↦ x) :=
    (p m).coe_continuous.comp (continuous_pi fun _ ↦ continuous_id)
  have hPh : ∀ (c : ℝ) (x : ι → ℝ), 0 ≤ c →
      (p m) (fun _ ↦ c • x) = c ^ m * (p m) (fun _ ↦ x) := by
    intro c x _
    simpa [Finset.prod_const, smul_eq_mul] using
      (p m).map_smul_univ (fun _ : Fin m ↦ c) (fun _ ↦ x)
  obtain ⟨S, c, u₀, hS, hSfin, hSvol0, hSnorm, hc, hu₀, hbound⟩ :=
    leading_part_scaled_set a (fun x ↦ (p m) (fun _ ↦ x)) m hPc hPh hx₀ hx₀n
      hCnn hu₁ hrem
  have hvolpos : 0 < (volume S).toReal := ENNReal.toReal_pos hSvol0 hSfin
  refine lower_bound_not_superpolynomial
    (κ := (volume S).toReal * (c ^ 2 * Real.exp (-(4 * C0))))
    (T₀ := max (4 / R ^ 2) (u₀⁻¹ ^ 2))
    (γ := -(m : ℝ) - (Fintype.card ι : ℝ) / 2) (by positivity)
    (fun t ht ↦ ?_) hdecay
  have htpos : 0 < t :=
    lt_of_lt_of_le (lt_max_of_lt_left (by positivity : (0:ℝ) < 4 / R ^ 2)) ht
  have hst : 0 < Real.sqrt t := Real.sqrt_pos.mpr htpos
  have ht4 : 4 ≤ R ^ 2 * t := by
    have h1 : 4 / R ^ 2 ≤ t := le_trans (le_max_left _ _) ht
    have hR2 : (0 : ℝ) < R ^ 2 := by positivity
    exact (div_le_iff₀' hR2).mp h1
  have hinvle : (Real.sqrt t)⁻¹ ≤ u₀ := by
    have h2 : u₀⁻¹ ^ 2 ≤ t := le_trans (le_max_right _ _) ht
    have h3 : u₀⁻¹ ≤ Real.sqrt t := Real.le_sqrt_of_sq_le h2
    rw [inv_le_comm₀ hst hu₀]
    exact h3
  have hgrow : ∀ x ∈ S, c * ((Real.sqrt t)⁻¹) ^ m ≤ |a ((Real.sqrt t)⁻¹ • x)| :=
    fun x hx ↦ hbound ((Real.sqrt t)⁻¹) ⟨inv_pos.mpr hst, hinvle⟩ x hx
  set u : ℝ := (Real.sqrt t)⁻¹ with hu_def
  have hu : 0 < u := inv_pos.mpr hst
  have h2 : (2 : ℝ) ≤ R * Real.sqrt t := by
    have hb : (0 : ℝ) ≤ R * Real.sqrt t := by positivity
    nlinarith [Real.sq_sqrt htpos.le, sq_nonneg (R * Real.sqrt t - 2)]
  have hur : 2 * u ≤ R := by
    have heq : 2 * u = 2 / Real.sqrt t := rfl
    rw [heq, div_le_iff₀ hst]
    exact h2
  have hwnorm : ∀ x ∈ S, ‖u • x‖ ≤ R := by
    intro x hxS
    rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg hu.le]
    calc u * ‖x‖ ≤ u * 2 := mul_le_mul_of_nonneg_left (hSnorm x hxS) hu.le
      _ = 2 * u := mul_comm u 2
      _ ≤ R := hur
  have hmin := hint t
  have hSm : MeasurableSet (u • S) := hS.const_smul_of_ne_zero hu.ne'
  have hwinψ : Set.EqOn (fun w ↦ ψ w * a w ^ 2 * Real.exp (-(t * K w)))
      (fun w ↦ a w ^ 2 * Real.exp (-(t * K w))) (u • S) := by
    rintro w ⟨x, hxS, rfl⟩
    simp only [hψ1 _ (hwnorm x hxS), one_mul]
  have hintW : IntegrableOn (fun w ↦ a w ^ 2 * Real.exp (-(t * K w))) (u • S) volume :=
    (hmin.integrableOn).congr_fun hwinψ hSm
  have hBwin : (∫ w in u • S, ψ w * a w ^ 2 * Real.exp (-(t * K w)))
      ≤ ∫ w, ψ w * a w ^ 2 * Real.exp (-(t * K w)) := by
    apply MeasureTheory.setIntegral_le_integral hmin
    filter_upwards with w
    have hψw := hψ0 w
    positivity
  have hwin_eq : (∫ w in u • S, ψ w * a w ^ 2 * Real.exp (-(t * K w)))
      = ∫ w in u • S, a w ^ 2 * Real.exp (-(t * K w)) :=
    MeasureTheory.setIntegral_congr_fun hSm hwinψ
  have hsec := sector_lower_bound_multi K a m hS hSfin hc.le hC0 hR ht4 hSnorm hgrow
    hquad hintW
  calc (volume S).toReal * (c ^ 2 * Real.exp (-(4 * C0))) *
        t ^ (-(m : ℝ) - (Fintype.card ι : ℝ) / 2)
      = (volume S).toReal * (c ^ 2 * Real.exp (-(4 * C0)) *
          t ^ (-(m : ℝ) - (Fintype.card ι : ℝ) / 2)) := by ring
    _ ≤ ∫ w in u • S, a w ^ 2 * Real.exp (-(t * K w)) := hsec
    _ = ∫ w in u • S, ψ w * a w ^ 2 * Real.exp (-(t * K w)) := hwin_eq.symm
    _ ≤ ∫ w, ψ w * a w ^ 2 * Real.exp (-(t * K w)) := hBwin

/-! ### Integration by parts against the Boltzmann factor -/

/-- **Integration by parts.** For `φ` smooth with compact support inside an
open set `V` on which `L` is analytic,
`∫ ∂_v φ e^{-tL} = t ∫ φ ∂_v L e^{-tL}`. -/
theorem integral_fderiv_mul_exp_neg {L φ : (ι → ℝ) → ℝ} {V : Set (ι → ℝ)}
    (hV : IsOpen V) (hL : ∀ w ∈ V, AnalyticAt ℝ L w) (hLc : Continuous L)
    (hφ : ContDiff ℝ ∞ φ) (hφs : HasCompactSupport φ) (hsupp : tsupport φ ⊆ V)
    (t : ℝ) (v : ι → ℝ) :
    ∫ w, fderiv ℝ φ w v * Real.exp (-(t * L w))
      = t * ∫ w, φ w * fderiv ℝ L w v * Real.exp (-(t * L w)) := by
  have hfc : Continuous fun w ↦ Real.exp (-(t * L w)) := by fun_prop
  have hfderiv : ∀ w ∈ V, HasFDerivAt (fun w ↦ Real.exp (-(t * L w)))
      (Real.exp (-(t * L w)) • -(t • fderiv ℝ L w)) w := by
    intro w hw
    have h1 : HasFDerivAt L (fderiv ℝ L w) w := (hL w hw).differentiableAt.hasFDerivAt
    exact ((h1.const_mul t).neg).exp
  have hfd_eq : ∀ w ∈ V, fderiv ℝ (fun w ↦ Real.exp (-(t * L w))) w v
      = -(t * fderiv ℝ L w v) * Real.exp (-(t * L w)) := by
    intro w hw
    rw [(hfderiv w hw).fderiv]
    simp only [smul_apply, neg_apply, smul_eq_mul]
    ring
  have hprod : ∀ w, fderiv ℝ (fun w ↦ Real.exp (-(t * L w))) w v * φ w
      = -(t * fderiv ℝ L w v) * Real.exp (-(t * L w)) * φ w := by
    intro w
    by_cases hw : w ∈ tsupport φ
    · rw [hfd_eq w (hsupp hw)]
    · rw [image_eq_zero_of_notMem_tsupport hw, mul_zero, mul_zero]
  have hDc : ContinuousOn (fun w ↦ fderiv ℝ L w v) V :=
    ContinuousOn.clm_apply (fun w hw ↦ (hL w hw).fderiv.continuousAt.continuousWithinAt)
      continuousOn_const
  have hFc : ContinuousOn (fun w ↦ -(t * fderiv ℝ L w v) * Real.exp (-(t * L w))) V :=
    (continuousOn_const.mul hDc).neg.mul hfc.continuousOn
  have hI1 : Integrable fun w ↦ fderiv ℝ (fun w ↦ Real.exp (-(t * L w))) w v * φ w := by
    have hc : Continuous fun w ↦ φ w * (-(t * fderiv ℝ L w v) * Real.exp (-(t * L w))) :=
      continuous_mul_of_continuousOn_tsupport_subset hV hFc hφ.continuous hsupp
    refine (hc.integrable_of_hasCompactSupport hφs.mul_right).congr
      (Eventually.of_forall fun w ↦ ?_)
    beta_reduce
    rw [hprod w]
    ring
  have hI2 : Integrable fun w ↦ Real.exp (-(t * L w)) * fderiv ℝ φ w v := by
    have hc : Continuous fun w ↦ Real.exp (-(t * L w)) * fderiv ℝ φ w v :=
      hfc.mul ((contDiff_infty_iff_fderiv.mp hφ).2.continuous.clm_apply continuous_const)
    exact hc.integrable_of_hasCompactSupport
      (((hφs.fderiv (𝕜 := ℝ)).comp_left (g := fun l : (ι → ℝ) →L[ℝ] ℝ ↦ l v) rfl).mul_left)
  have hI3 : Integrable fun w ↦ Real.exp (-(t * L w)) * φ w :=
    (hfc.mul hφ.continuous).integrable_of_hasCompactSupport hφs.mul_left
  have hIBP := integral_mul_fderiv_eq_neg_fderiv_mul_of_integrable (μ := volume)
    (f := fun w ↦ Real.exp (-(t * L w))) (g := φ) (v := v) hI1 hI2 hI3
    (fun w hw ↦ (((hL w (hsupp hw)).differentiableAt.const_mul t).neg).exp)
    (fun w _ ↦ hφ.differentiable (by simp) w)
  have hL' : (∫ w, fderiv ℝ φ w v * Real.exp (-(t * L w)))
      = ∫ w, Real.exp (-(t * L w)) * fderiv ℝ φ w v :=
    integral_congr_ae (Eventually.of_forall fun w ↦ mul_comm _ _)
  rw [hL', hIBP, ← integral_neg, ← integral_const_mul]
  refine integral_congr_ae (Eventually.of_forall fun w ↦ ?_)
  beta_reduce
  rw [hprod w]
  ring

/-! ### Cancelling the scalar series -/

/-- **The scalar cancels.** If the unnormalised Laplace families of `L₁, L₂`
are proportional beyond all orders through an arbitrary scalar function
`C`, then for every smooth `φ` supported in the analyticity domain and every
direction `v`, `t ∫ φ ∂_v(L₂ - L₁) e^{-tL₂}` decays beyond all orders. -/
theorem proportional_families_superPoly_derivative {L₁ L₂ : (ι → ℝ) → ℝ}
    {V : Set (ι → ℝ)} (hV : IsOpen V)
    (hV1 : ∀ w ∈ V, AnalyticAt ℝ L₁ w) (hV2 : ∀ w ∈ V, AnalyticAt ℝ L₂ w)
    (hL1c : Continuous L₁) (hL2c : Continuous L₂) (C : ℝ → ℝ)
    (hfam : ∀ φ : (ι → ℝ) → ℝ, ContDiff ℝ ∞ φ → HasCompactSupport φ →
      SuperPoly fun t ↦ (∫ w, φ w * Real.exp (-(t * L₂ w)))
        - C t * ∫ w, φ w * Real.exp (-(t * L₁ w)))
    {φ : (ι → ℝ) → ℝ} (hφ : ContDiff ℝ ∞ φ) (hφs : HasCompactSupport φ)
    (hsupp : tsupport φ ⊆ V) (v : ι → ℝ) :
    SuperPoly fun t ↦ t * ∫ w, φ w * (fderiv ℝ L₂ w v - fderiv ℝ L₁ w v) *
      Real.exp (-(t * L₂ w)) := by
  have hdφ : ContDiff ℝ ∞ fun w ↦ fderiv ℝ φ w v :=
    (contDiff_infty_iff_fderiv.mp hφ).2.clm_apply contDiff_const
  have hdφs : HasCompactSupport fun w ↦ fderiv ℝ φ w v :=
    (hφs.fderiv (𝕜 := ℝ)).comp_left (g := fun l : (ι → ℝ) →L[ℝ] ℝ ↦ l v) rfl
  have h1 := hfam _ hdφ hdφs
  have hD1 : ContDiffOn ℝ ∞ (fun w ↦ fderiv ℝ L₁ w v) V := fun w hw ↦
    ((hV1 w hw).fderiv.contDiffAt.clm_apply contDiffAt_const).contDiffWithinAt
  have hφD : ContDiff ℝ ∞ fun w ↦ φ w * fderiv ℝ L₁ w v :=
    contDiff_mul_of_contDiffOn_tsupport_subset hV hD1 hφ hsupp
  have hφDs : HasCompactSupport fun w ↦ φ w * fderiv ℝ L₁ w v := hφs.mul_right
  have h2 := (hfam _ hφD hφDs).id_mul
  have hibp1 := integral_fderiv_mul_exp_neg hV hV1 hL1c hφ hφs hsupp (v := v)
  have hibp2 := integral_fderiv_mul_exp_neg hV hV2 hL2c hφ hφs hsupp (v := v)
  have hint : ∀ (L : (ι → ℝ) → ℝ), (∀ w ∈ V, AnalyticAt ℝ L w) → ∀ t : ℝ,
      Integrable fun w ↦ φ w * fderiv ℝ L w v * Real.exp (-(t * L₂ w)) := by
    intro L hL t
    have hDc : ContinuousOn (fun w ↦ fderiv ℝ L w v) V :=
      ContinuousOn.clm_apply (fun w hw ↦ (hL w hw).fderiv.continuousAt.continuousWithinAt)
        continuousOn_const
    have hc : Continuous fun w ↦ φ w * fderiv ℝ L w v * Real.exp (-(t * L₂ w)) :=
      (continuous_mul_of_continuousOn_tsupport_subset hV hDc hφ.continuous hsupp).mul (by fun_prop)
    exact hc.integrable_of_hasCompactSupport hφs.mul_right.mul_right
  refine (h1.sub h2).congr (Eventually.of_forall fun t ↦ ?_)
  beta_reduce
  rw [hibp1 t, hibp2 t]
  have hsplit : ∫ w, φ w * (fderiv ℝ L₂ w v - fderiv ℝ L₁ w v) * Real.exp (-(t * L₂ w))
      = (∫ w, φ w * fderiv ℝ L₂ w v * Real.exp (-(t * L₂ w)))
        - ∫ w, φ w * fderiv ℝ L₁ w v * Real.exp (-(t * L₂ w)) := by
    rw [← integral_sub (hint L₂ hV2 t) (hint L₁ hV1 t)]
    exact integral_congr_ae (Eventually.of_forall fun w ↦ by ring)
  rw [hsplit]
  ring

/-! ### The derivative of `L₂ - L₁` vanishes near a zero -/

/-- **Vanishing partial derivatives.** Under exact proportionality of the
families, every directional derivative of `L₂ - L₁` vanishes on a
neighbourhood of a zero `p` of `L₂` at which both losses are analytic. -/
theorem proportional_families_fderiv_apply_eventually_eq {L₁ L₂ : (ι → ℝ) → ℝ}
    {p : ι → ℝ} (hL1c : Continuous L₁) (hL2c : Continuous L₂)
    (hL2 : ∀ w, 0 ≤ L₂ w) (hA1 : AnalyticAt ℝ L₁ p) (hA2 : AnalyticAt ℝ L₂ p)
    (hp2 : L₂ p = 0) (C : ℝ → ℝ)
    (hfam : ∀ φ : (ι → ℝ) → ℝ, ContDiff ℝ ∞ φ → HasCompactSupport φ →
      SuperPoly fun t ↦ (∫ w, φ w * Real.exp (-(t * L₂ w)))
        - C t * ∫ w, φ w * Real.exp (-(t * L₁ w)))
    (v : ι → ℝ) :
    ∀ᶠ w in 𝓝 p, fderiv ℝ L₂ w v = fderiv ℝ L₁ w v := by
  rcases isEmpty_or_nonempty ι with hι | hι
  · exact Eventually.of_forall fun w ↦ by rw [Subsingleton.elim v 0, map_zero, map_zero]
  -- the analyticity neighbourhood
  obtain ⟨ε, hε, hεV⟩ := Metric.eventually_nhds_iff_ball.mp
    (hA1.eventually_analyticAt.and hA2.eventually_analyticAt)
  have hV : IsOpen (Metric.ball p ε) := Metric.isOpen_ball
  have hV1 : ∀ w ∈ Metric.ball p ε, AnalyticAt ℝ L₁ w := fun w hw ↦ (hεV w hw).1
  have hV2 : ∀ w ∈ Metric.ball p ε, AnalyticAt ℝ L₂ w := fun w hw ↦ (hεV w hw).2
  -- the derivative difference
  set g : (ι → ℝ) → ℝ := fun w ↦ fderiv ℝ L₂ w v - fderiv ℝ L₁ w v with hg_def
  by_contra hcon
  have hfreq : ∃ᶠ w in 𝓝 p, g w ≠ 0 :=
    (Filter.not_eventually.mp hcon).mono fun w hw ↦ sub_ne_zero.mpr hw
  have hgA : AnalyticAt ℝ g p := by
    have h2 : AnalyticAt ℝ (fun w ↦ fderiv ℝ L₂ w v) p :=
      ((ContinuousLinearMap.apply ℝ ℝ v).analyticAt _).comp hA2.fderiv
    have h1 : AnalyticAt ℝ (fun w ↦ fderiv ℝ L₁ w v) p :=
      ((ContinuousLinearMap.apply ℝ ℝ v).analyticAt _).comp hA1.fderiv
    exact h2.sub h1
  have hshift : AnalyticAt ℝ (fun w : ι → ℝ ↦ p + w) 0 :=
    analyticAt_const.add analyticAt_id
  have hG : AnalyticAt ℝ (fun w ↦ g (p + w)) 0 := by
    have hg' : AnalyticAt ℝ g ((fun w : ι → ℝ ↦ p + w) 0) := by simpa using hgA
    exact hg'.comp hshift
  obtain ⟨q, r, hqr⟩ := hG
  obtain ⟨δ, hδ0, hδr⟩ : ∃ δ : ℝ, 0 < δ ∧ ENNReal.ofReal δ ≤ r := by
    rcases eq_or_ne r ⊤ with hr | hr
    · exact ⟨1, one_pos, by rw [hr]; exact le_top⟩
    · exact ⟨r.toReal, ENNReal.toReal_pos hqr.r_pos.ne' hr,
        (ENNReal.ofReal_toReal hr).le⟩
  have hball : ∀ᶠ w in 𝓝 p, w ∈ Metric.ball p δ :=
    Metric.isOpen_ball.eventually_mem (Metric.mem_ball_self hδ0)
  obtain ⟨u, hu_ne, hu_mem⟩ := (hfreq.and_eventually hball).exists
  have hne : ∃ w ∈ Metric.eball (0 : ι → ℝ) r, (fun w ↦ g (p + w)) w ≠ 0 := by
    refine ⟨u - p, ?_, ?_⟩
    · have hd : dist (u - p) (0 : ι → ℝ) = dist u p := by
        rw [dist_zero_right, dist_eq_norm]
      have hlt : edist (u - p) (0 : ι → ℝ) < ENNReal.ofReal δ := by
        rw [edist_dist, hd]
        exact (ENNReal.ofReal_lt_ofReal_iff hδ0).mpr hu_mem
      exact Metric.mem_eball.mpr (lt_of_lt_of_le hlt hδr)
    · simpa [add_sub_cancel p u] using hu_ne
  obtain ⟨m, hlow, x₀, hx₀, hx₀n⟩ := exists_least_nonzero_diagonal' hqr hne
  -- the quadratic bound on the shifted `L₂`
  have hA2' : AnalyticAt ℝ (fun w ↦ L₂ (p + w)) 0 := by
    have hg' : AnalyticAt ℝ L₂ ((fun w : ι → ℝ ↦ p + w) 0) := by simpa using hA2
    exact hg'.comp hshift
  have hK : ContDiffAt ℝ 2 (fun w ↦ L₂ (p + w)) 0 := hA2'.contDiffAt
  have hK0 : (fun w ↦ L₂ (p + w)) 0 = 0 := by simp [hp2]
  have hKnn : ∀ᶠ w in 𝓝 (0 : ι → ℝ), 0 ≤ L₂ (p + w) :=
    Eventually.of_forall fun w ↦ hL2 _
  obtain ⟨C0, R, hC0, hR, hsum⟩ := Multi.quadratic_upper_bound_of_nonneg hK hK0 hKnn
  -- a radius small enough for the bump to live in the analyticity ball
  have hR' : 0 < min R (ε / 3) := lt_min hR (by positivity)
  have hR'R : min R (ε / 3) ≤ R := min_le_left _ _
  have hR'ε : 2 * min R (ε / 3) < ε := by
    have : min R (ε / 3) ≤ ε / 3 := min_le_right _ _
    linarith
  -- the smooth bump at `p`
  let ψ : ContDiffBump p := ⟨min R (ε / 3), 2 * min R (ε / 3), hR', by linarith⟩
  have hψ1 : ∀ w : ι → ℝ, ‖w‖ ≤ min R (ε / 3) → ψ (p + w) = 1 := fun w hw ↦
    ψ.one_of_mem_closedBall (by
      rw [Metric.mem_closedBall, dist_eq_norm, add_sub_cancel_left]
      exact hw)
  have hsuppψ : tsupport ψ ⊆ Metric.ball p ε := by
    rw [ψ.tsupport_eq]
    exact Metric.closedBall_subset_ball hR'ε
  -- the observable `ψ · g`
  have hgV : ContDiffOn ℝ ∞ g (Metric.ball p ε) := fun w hw ↦
    (((hV2 w hw).fderiv.contDiffAt.clm_apply contDiffAt_const).sub
      ((hV1 w hw).fderiv.contDiffAt.clm_apply contDiffAt_const)).contDiffWithinAt
  have hφ : ContDiff ℝ ∞ fun w ↦ ψ w * g w :=
    contDiff_mul_of_contDiffOn_tsupport_subset hV hgV ψ.contDiff hsuppψ
  have hφs : HasCompactSupport fun w ↦ ψ w * g w := ψ.hasCompactSupport.mul_right
  have hsupp : tsupport (fun w ↦ ψ w * g w) ⊆ Metric.ball p ε :=
    tsupport_mul_subset_left.trans hsuppψ
  have hsp := proportional_families_superPoly_derivative hV hV1 hV2 hL1c hL2c C hfam
    hφ hφs hsupp v
  have hsq : SuperPoly fun t ↦ ∫ w, ψ w * g w ^ 2 * Real.exp (-(t * L₂ w)) := by
    refine hsp.of_id_mul.congr (Eventually.of_forall fun t ↦ ?_)
    beta_reduce
    congr 1
    funext w
    simp only [hg_def]
    ring
  -- integrability of the square observable
  have hint : ∀ t : ℝ, Integrable fun w ↦ ψ w * g w ^ 2 * Real.exp (-(t * L₂ w)) := by
    intro t
    have h1 : Continuous fun w ↦ ψ w * g w ^ 2 :=
      continuous_mul_of_continuousOn_tsupport_subset hV (hgV.continuousOn.pow 2) ψ.continuous hsuppψ
    have hc : Continuous fun w ↦ ψ w * g w ^ 2 * Real.exp (-(t * L₂ w)) :=
      h1.mul (by fun_prop)
    exact hc.integrable_of_hasCompactSupport ψ.hasCompactSupport.mul_right.mul_right
  -- shift to the origin
  have hsq' : SuperPoly fun t ↦ ∫ w, ψ (p + w) * g (p + w) ^ 2 *
      Real.exp (-(t * L₂ (p + w))) := by
    refine hsq.congr (Eventually.of_forall fun t ↦ ?_)
    beta_reduce
    exact (integral_add_left_eq_self
      (fun w ↦ ψ w * g w ^ 2 * Real.exp (-(t * L₂ w))) p).symm
  have hint' : ∀ t : ℝ, Integrable fun w ↦ ψ (p + w) * g (p + w) ^ 2 *
      Real.exp (-(t * L₂ (p + w))) := fun t ↦
    ((measurePreserving_add_left volume p).integrable_comp_emb
      (measurableEmbedding_addLeft p)).mpr (hint t)
  exact analytic_square_not_superpolynomial (fun w ↦ L₂ (p + w)) (fun w ↦ g (p + w))
    (fun w ↦ ψ (p + w)) m hqr hlow hx₀ hx₀n hC0 hR' (fun w hw ↦ hsum w (hw.trans hR'R))
    (fun w ↦ ψ.nonneg) hψ1 hint' hsq'

/-! ### The answer to `q:proportional` -/

/-- **Proportional families force equal germs, point form.** If `L₁, L₂` are
continuous, `L₂ ≥ 0`, both are analytic at a common zero `p`, and their
unnormalised Laplace families are proportional beyond all orders through
some scalar function `C`, then `L₁ = L₂` on a neighbourhood of `p`. -/
theorem proportional_families_force_germ_eq_at {L₁ L₂ : (ι → ℝ) → ℝ} {p : ι → ℝ}
    (hL1c : Continuous L₁) (hL2c : Continuous L₂) (hL2 : ∀ w, 0 ≤ L₂ w)
    (hA1 : AnalyticAt ℝ L₁ p) (hA2 : AnalyticAt ℝ L₂ p)
    (hp1 : L₁ p = 0) (hp2 : L₂ p = 0) (C : ℝ → ℝ)
    (hfam : ∀ φ : (ι → ℝ) → ℝ, ContDiff ℝ ∞ φ → HasCompactSupport φ →
      SuperPoly fun t ↦ (∫ w, φ w * Real.exp (-(t * L₂ w)))
        - C t * ∫ w, φ w * Real.exp (-(t * L₁ w))) :
    ∀ᶠ w in 𝓝 p, L₁ w = L₂ w := by
  classical
  have hcoord : ∀ i : ι, ∀ᶠ w in 𝓝 p,
      fderiv ℝ L₂ w (Pi.single i 1) = fderiv ℝ L₁ w (Pi.single i 1) := fun i ↦
    proportional_families_fderiv_apply_eventually_eq hL1c hL2c hL2 hA1 hA2 hp2 C hfam _
  have hall : ∀ᶠ w in 𝓝 p, fderiv ℝ L₂ w = fderiv ℝ L₁ w := by
    filter_upwards [eventually_all.mpr hcoord] with w hw
    ext v
    rw [pi_eq_sum_univ' v, map_sum, map_sum]
    exact Finset.sum_congr rfl fun i _ ↦ by rw [map_smul, map_smul, hw i]
  obtain ⟨ε, hε, hεB⟩ := Metric.eventually_nhds_iff_ball.mp
    (hall.and (hA1.eventually_analyticAt.and hA2.eventually_analyticAt))
  have hB : IsOpen (Metric.ball p ε) := Metric.isOpen_ball
  have hdiff : DifferentiableOn ℝ (fun w ↦ L₂ w - L₁ w) (Metric.ball p ε) := fun w hw ↦
    ((hεB w hw).2.2.differentiableAt.sub (hεB w hw).2.1.differentiableAt).differentiableWithinAt
  have hzero : (Metric.ball p ε).EqOn (fderiv ℝ fun w ↦ L₂ w - L₁ w) 0 := by
    intro w hw
    rw [fderiv_fun_sub (hεB w hw).2.2.differentiableAt (hεB w hw).2.1.differentiableAt,
      (hεB w hw).1, sub_self]
    rfl
  filter_upwards [Metric.ball_mem_nhds p hε] with w hw
  have hconst := hB.is_const_of_fderiv_eq_zero (convex_ball p ε).isPreconnected hdiff hzero
    hw (Metric.mem_ball_self hε)
  simp only [hp1, hp2, sub_zero] at hconst
  linarith

/-- **Proportional families force equal germs, locus form** (the answer to
`q:proportional`). If `L₁, L₂` are continuous, `L₂ ≥ 0`, both analytic at
each point of a set `W₀` of common zeros, and their unnormalised Laplace
families are proportional beyond all orders through some scalar function
`C`, then `L₁ = L₂` on an open neighbourhood of `W₀`. -/
theorem proportional_families_force_eq_near {L₁ L₂ : (ι → ℝ) → ℝ} {W₀ : Set (ι → ℝ)}
    (hL1c : Continuous L₁) (hL2c : Continuous L₂) (hL2 : ∀ w, 0 ≤ L₂ w)
    (hA1 : ∀ p ∈ W₀, AnalyticAt ℝ L₁ p) (hA2 : ∀ p ∈ W₀, AnalyticAt ℝ L₂ p)
    (hzero1 : ∀ p ∈ W₀, L₁ p = 0) (hzero2 : ∀ p ∈ W₀, L₂ p = 0) (C : ℝ → ℝ)
    (hfam : ∀ φ : (ι → ℝ) → ℝ, ContDiff ℝ ∞ φ → HasCompactSupport φ →
      SuperPoly fun t ↦ (∫ w, φ w * Real.exp (-(t * L₂ w)))
        - C t * ∫ w, φ w * Real.exp (-(t * L₁ w))) :
    ∃ U : Set (ι → ℝ), IsOpen U ∧ W₀ ⊆ U ∧ ∀ w ∈ U, L₁ w = L₂ w := by
  have h : ∀ p ∈ W₀, ∃ V : Set (ι → ℝ),
      (∀ w ∈ V, L₁ w = L₂ w) ∧ IsOpen V ∧ p ∈ V := fun p hp ↦
    eventually_nhds_iff.mp
      (proportional_families_force_germ_eq_at hL1c hL2c hL2 (hA1 p hp) (hA2 p hp)
        (hzero1 p hp) (hzero2 p hp) C hfam)
  choose V hVeq hVopen hVmem using h
  refine ⟨⋃ p, ⋃ hp : p ∈ W₀, V p hp, ?_, ?_, ?_⟩
  · exact isOpen_iUnion fun p ↦ isOpen_iUnion fun hp ↦ hVopen p hp
  · exact fun p hp ↦ Set.mem_iUnion₂.mpr ⟨p, hp, hVmem p hp⟩
  · intro w hw
    obtain ⟨p, hp, hwV⟩ := Set.mem_iUnion₂.mp hw
    exact hVeq p hp w hwV

end Laplace
