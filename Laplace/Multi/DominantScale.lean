/-
Copyright (c) 2026 Timaeus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Timaeus
-/
import Laplace.Multi.ConstrainedLP
import Laplace.Multi.RescaledData

/-!
# The dominant-scale certificate

Astra's certificates (1) and (2) (`research_kernel_asymptotics_v1`, §8): a feasible scale `α` of
the constrained LP, with the phase constraint either tied (`κ·α = δ`, the critical scale) or strict,
and the truth constraint either tied (the truth-boundary scale) or strict, turns the rescaled
model integrand of `modelKernel_eq_rescaled` into a `RescaledData`, provided the unit `a` and the
weight `W` are bounded and converge along the rescaling and the limiting profile is integrable
(`DominantScaleHyp`). The limiting domain is `(0,1)` in the unscaled coordinates and `(0,∞)` in the
scaled ones, cut by the tied cutoff when `Q·α = γ` (`limitDomain`); the limiting phase is
`B a₀(u) ∏ u^κ` when the phase is tied and `0` otherwise (`dsProfile`); the unit is evaluated at the
limiting face point through `a₀`, never frozen (Astra §2.2).

The conclusion (`DominantScaleHyp.tendsto_modelKernel`): `t^λ K(t) → A ∫ w₀ e^{-Φ₀}` with
`λ = γp + ∑ (r_j + 1) α_j`; the integrability of the profile is the hypothesis that encodes the
uniqueness of the dominant scale (a degenerate face would make it diverge).
-/

open Real MeasureTheory Filter Topology Set

namespace Laplace.Multi

variable {ι : Type*} [Fintype ι]

/-! ### The limiting domain -/

/-- The limiting domain of the rescaling `x = t^{-α} u`. -/
def limitDomain (D γ q : ℝ) (Q α : ι → ℝ) : Set (ι → ℝ) :=
  Set.pi univ (fun j ↦ if α j = 0 then Ioo (0 : ℝ) 1 else Ioi 0) ∩
    {u | ∑ j, Q j * α j = γ → D * ∏ j, u j ^ (-(Q j / q)) < 1}

variable {D γ q : ℝ} {Q α : ι → ℝ}

theorem limitDomain_pos {u : ι → ℝ} (hu : u ∈ limitDomain D γ q Q α) (j : ι) : 0 < u j := by
  have h := Set.mem_univ_pi.mp hu.1 j
  split_ifs at h with h0
  · exact h.1
  · exact h

theorem rescaledDomain_subset {t : ℝ} :
    rescaledDomain D γ q Q α t ⊆ limitDomain D γ q Q α := by
  intro u hu
  obtain ⟨h1, h2⟩ := hu
  refine ⟨Set.mem_univ_pi.mpr fun j ↦ ?_, fun htied ↦ ?_⟩
  · have hj := Set.mem_univ_pi.mp h1 j
    split_ifs with h0
    · rwa [h0, Real.rpow_zero] at hj
    · exact hj.1
  · have h2' : rescaledCut D γ q Q α t u < 1 := h2
    unfold rescaledCut at h2'
    rwa [htied, sub_self, zero_div, neg_zero, Real.rpow_zero, mul_one] at h2'

theorem eventually_mem_rescaledDomain (hq : 0 < q) (hα : ∀ j, 0 ≤ α j)
    (htruth : ∑ j, Q j * α j ≤ γ) {u : ι → ℝ} (hu : u ∈ limitDomain D γ q Q α) :
    ∀ᶠ t in atTop, u ∈ rescaledDomain D γ q Q α t := by
  have hpi : ∀ᶠ t in atTop, ∀ j, u j ∈ Ioo (0 : ℝ) (t ^ α j) := by
    refine Filter.eventually_all.2 fun j ↦ ?_
    have hj := Set.mem_univ_pi.mp hu.1 j
    by_cases h0 : α j = 0
    · rw [if_pos h0] at hj
      exact Eventually.of_forall fun t ↦ by rw [h0, Real.rpow_zero]; exact hj
    · rw [if_neg h0] at hj
      have hpos : 0 < α j := lt_of_le_of_ne (hα j) (Ne.symm h0)
      filter_upwards [(tendsto_rpow_atTop hpos).eventually_gt_atTop (u j)] with t ht
      exact ⟨hj, ht⟩
  have hcut : ∀ᶠ t in atTop, rescaledCut D γ q Q α t u < 1 := by
    by_cases htied : ∑ j, Q j * α j = γ
    · refine Eventually.of_forall fun t ↦ ?_
      unfold rescaledCut
      rw [htied, sub_self, zero_div, neg_zero, Real.rpow_zero, mul_one]
      exact hu.2 htied
    · have hlt : ∑ j, Q j * α j < γ := lt_of_le_of_ne htruth htied
      have h0 : Tendsto (fun t : ℝ ↦ rescaledCut D γ q Q α t u) atTop (𝓝 0) := by
        unfold rescaledCut
        simpa using ((tendsto_rpow_truth hq hlt).const_mul D).mul_const (∏ j, u j ^ (-(Q j / q)))
      exact h0.eventually_lt_const zero_lt_one
  filter_upwards [hpi, hcut] with t h1 h2
  exact ⟨Set.mem_univ_pi.mpr h1, h2⟩

theorem measurableSet_limitDomain : MeasurableSet (limitDomain D γ q Q α) := by
  refine (MeasurableSet.pi countable_univ fun j _ ↦ ?_).inter ?_
  · split_ifs
    · exact measurableSet_Ioo
    · exact measurableSet_Ioi
  · by_cases htied : ∑ j, Q j * α j = γ
    · have : {u : ι → ℝ | ∑ j, Q j * α j = γ → D * ∏ j, u j ^ (-(Q j / q)) < 1} =
          {u | D * ∏ j, u j ^ (-(Q j / q)) < 1} := by
        ext u; simp [htied]
      rw [this]
      exact measurableSet_lt (measurable_const.mul
        (Finset.measurable_prod _ fun j _ ↦ (measurable_pi_apply j).pow_const _)) measurable_const
    · have : {u : ι → ℝ | ∑ j, Q j * α j = γ → D * ∏ j, u j ^ (-(Q j / q)) < 1} = univ := by
        ext u; simp [htied]
      rw [this]
      exact MeasurableSet.univ

omit [Fintype ι] in
theorem measurable_rescale (t : ℝ) (α : ι → ℝ) : Measurable (rescale t α) :=
  measurable_pi_lambda _ fun j ↦ measurable_const.mul (measurable_pi_apply j)

theorem measurable_rescaledCut (t : ℝ) : Measurable (rescaledCut D γ q Q α t) :=
  measurable_const.mul (Finset.measurable_prod _ fun j _ ↦ (measurable_pi_apply j).pow_const _)

theorem measurableSet_rescaledDomain (t : ℝ) : MeasurableSet (rescaledDomain D γ q Q α t) :=
  (MeasurableSet.pi countable_univ fun _ _ ↦ measurableSet_Ioo).inter
    (measurableSet_lt (measurable_rescaledCut t) measurable_const)

/-! ### The moving data and the profile -/

open scoped Classical in
/-- The moving phase `B t^{δ − κ·α} a(x_t, v_t) ∏ u^κ`, zero off the limiting domain and for
`t < 1`. -/
noncomputable def dsPhase (B D γ q δ : ℝ) (Q κ α : ι → ℝ) (a : (ι → ℝ) → ℝ → ℝ) (t : ℝ)
    (u : ι → ℝ) : ℝ :=
  if 1 ≤ t ∧ u ∈ limitDomain D γ q Q α then
    B * t ^ (δ - ∑ j, κ j * α j) * a (rescale t α u) (rescaledCut D γ q Q α t u) * ∏ j, u j ^ κ j
  else 0

/-- The moving weight `1_{domain_t} W(x_t, v_t) ∏ u^r`, zero for `t < 1`. -/
noncomputable def dsWeight (D γ q : ℝ) (Q r α : ι → ℝ) (W : (ι → ℝ) → ℝ → ℝ) (t : ℝ)
    (u : ι → ℝ) : ℝ :=
  if 1 ≤ t then
    (rescaledDomain D γ q Q α t).indicator
      (fun u ↦ W (rescale t α u) (rescaledCut D γ q Q α t u) * ∏ j, u j ^ r j) u
  else 0

open scoped Classical in
/-- The limiting phase: `B a₀(u) ∏ u^κ` on the limiting domain when the phase constraint is tied,
`0` otherwise. -/
noncomputable def dsProfile (B D γ q δ : ℝ) (Q κ α : ι → ℝ) (a₀ : (ι → ℝ) → ℝ) (u : ι → ℝ) :
    ℝ :=
  if u ∈ limitDomain D γ q Q α then
    (if ∑ j, κ j * α j = δ then B * a₀ u * ∏ j, u j ^ κ j else 0)
  else 0

/-- The limiting weight `1_{limitDomain} W₀ ∏ u^r`. -/
noncomputable def dsWeight₀ (D γ q : ℝ) (Q r α : ι → ℝ) (W₀ : (ι → ℝ) → ℝ) (u : ι → ℝ) : ℝ :=
  (limitDomain D γ q Q α).indicator (fun u ↦ W₀ u * ∏ j, u j ^ r j) u

/-- The envelope `Wmax 1_{limitDomain} ∏ u^r`. -/
noncomputable def dsEnvelope (D γ q : ℝ) (Q r α : ι → ℝ) (Wmax : ℝ) (u : ι → ℝ) : ℝ :=
  Wmax * (limitDomain D γ q Q α).indicator (fun u ↦ ∏ j, u j ^ r j) u

variable {B δ : ℝ} {κ r : ι → ℝ} {W a : (ι → ℝ) → ℝ → ℝ} {W₀ a₀ : (ι → ℝ) → ℝ} {Wmax : ℝ}

/-- For `t ≥ 1` the weighted Boltzmann factor of the moving data is the rescaled integrand. -/
theorem dsWeight_mul_exp {t : ℝ} (ht : 1 ≤ t) (u : ι → ℝ) :
    dsWeight D γ q Q r α W t u * exp (-(dsPhase B D γ q δ Q κ α a t u)) =
      rescaledIntegrand B D γ q δ Q κ r α W a t u := by
  unfold dsWeight dsPhase rescaledIntegrand
  rw [if_pos ht]
  by_cases hu : u ∈ rescaledDomain D γ q Q α t
  · rw [Set.indicator_of_mem hu, Set.indicator_of_mem hu,
      if_pos ⟨ht, rescaledDomain_subset hu⟩]
  · rw [Set.indicator_of_notMem hu, Set.indicator_of_notMem hu, zero_mul]

theorem dsWeight_ne_zero {t : ℝ} {u : ι → ℝ} (hw : dsWeight D γ q Q r α W t u ≠ 0) :
    1 ≤ t ∧ u ∈ rescaledDomain D γ q Q α t ∧
      W (rescale t α u) (rescaledCut D γ q Q α t u) ≠ 0 := by
  unfold dsWeight at hw
  by_cases ht : 1 ≤ t
  · rw [if_pos ht] at hw
    by_cases hu : u ∈ rescaledDomain D γ q Q α t
    · rw [Set.indicator_of_mem hu] at hw
      exact ⟨ht, hu, left_ne_zero_of_mul hw⟩
    · rw [Set.indicator_of_notMem hu] at hw
      exact absurd rfl hw
  · rw [if_neg ht] at hw
    exact absurd rfl hw

/-- The hypotheses of the dominant-scale certificate. -/
structure DominantScaleHyp (B D γ q δ : ℝ) (Q κ r α : ι → ℝ) (W a : (ι → ℝ) → ℝ → ℝ)
    (W₀ a₀ : (ι → ℝ) → ℝ) (Wmax amin amax : ℝ) : Prop where
  hq : 0 < q
  hB : 0 < B
  hamin : 0 < amin
  hle : amin ≤ amax
  feasible : ConstrainedFeasible Q κ γ δ α
  W_meas : Measurable (Function.uncurry W)
  a_meas : Measurable (Function.uncurry a)
  W_bd : ∀ x v, |W x v| ≤ Wmax
  a_bounds : ∀ x v, W x v ≠ 0 → amin ≤ a x v ∧ a x v ≤ amax
  a₀_bounds : ∀ u ∈ limitDomain D γ q Q α, amin ≤ a₀ u ∧ a₀ u ≤ amax
  W_lim : ∀ u ∈ limitDomain D γ q Q α,
    Tendsto (fun t ↦ W (rescale t α u) (rescaledCut D γ q Q α t u)) atTop (𝓝 (W₀ u))
  a_lim : ∀ u ∈ limitDomain D γ q Q α,
    Tendsto (fun t ↦ a (rescale t α u) (rescaledCut D γ q Q α t u)) atTop (𝓝 (a₀ u))
  int : Integrable (fun u ↦ dsEnvelope D γ q Q r α Wmax u *
    exp (-(amin / amax * dsProfile B D γ q δ Q κ α a₀ u)))
  Φint : Integrable (fun u ↦ dsEnvelope D γ q Q r α Wmax u *
    (dsProfile B D γ q δ Q κ α a₀ u * exp (-(amin / amax * dsProfile B D γ q δ Q κ α a₀ u))))

namespace DominantScaleHyp

variable {amin amax : ℝ} (h : DominantScaleHyp B D γ q δ Q κ r α W a W₀ a₀ Wmax amin amax)
include h

theorem Wmax_nonneg : 0 ≤ Wmax := (abs_nonneg _).trans (h.W_bd 0 0)

theorem amax_pos : 0 < amax := h.hamin.trans_le h.hle

omit h in
theorem measurable_dsPhase (ha : Measurable (Function.uncurry a)) (t : ℝ) :
    Measurable (dsPhase B D γ q δ Q κ α a t) := by
  classical
  by_cases ht : 1 ≤ t
  · have e : dsPhase B D γ q δ Q κ α a t = fun u ↦ if u ∈ limitDomain D γ q Q α then
        B * t ^ (δ - ∑ j, κ j * α j) * a (rescale t α u) (rescaledCut D γ q Q α t u) *
          ∏ j, u j ^ κ j else 0 := by
      funext u; simp only [dsPhase, ht, true_and]
    rw [e]
    refine Measurable.ite measurableSet_limitDomain ?_ measurable_const
    exact (measurable_const.mul (ha.comp ((measurable_rescale t α).prodMk
      (measurable_rescaledCut t)))).mul
      (Finset.measurable_prod _ fun j _ ↦ (measurable_pi_apply j).pow_const _)
  · have e : dsPhase B D γ q δ Q κ α a t = fun _ ↦ 0 := by
      funext u; simp only [dsPhase, ht, false_and, if_false]
    rw [e]
    exact measurable_const

omit h in
theorem measurable_dsWeight (hW : Measurable (Function.uncurry W)) (t : ℝ) :
    Measurable (dsWeight D γ q Q r α W t) := by
  by_cases ht : 1 ≤ t
  · have e : dsWeight D γ q Q r α W t = (rescaledDomain D γ q Q α t).indicator
        (fun u ↦ W (rescale t α u) (rescaledCut D γ q Q α t u) * ∏ j, u j ^ r j) := by
      funext u; simp only [dsWeight, ht, if_true]
    rw [e]
    exact Measurable.indicator ((hW.comp ((measurable_rescale t α).prodMk
      (measurable_rescaledCut t))).mul
      (Finset.measurable_prod _ fun j _ ↦ (measurable_pi_apply j).pow_const _))
      (measurableSet_rescaledDomain t)
  · have e : dsWeight D γ q Q r α W t = fun _ ↦ 0 := by
      funext u; simp only [dsWeight, ht, if_false]
    rw [e]
    exact measurable_const

theorem dsProfile_nonneg (u : ι → ℝ) : 0 ≤ dsProfile B D γ q δ Q κ α a₀ u := by
  unfold dsProfile
  split_ifs with hu htied
  · exact mul_nonneg (mul_nonneg h.hB.le (h.hamin.le.trans (h.a₀_bounds u hu).1))
      (Finset.prod_nonneg fun j _ ↦ rpow_nonneg (limitDomain_pos hu j).le _)
  · exact le_rfl
  · exact le_rfl

/-- The phase at a point where the weight is nonzero: positivity of the unit is available. -/
theorem dsPhase_ge {t : ℝ} {u : ι → ℝ} (hw : dsWeight D γ q Q r α W t u ≠ 0) :
    B * t ^ (δ - ∑ j, κ j * α j) * amin * ∏ j, u j ^ κ j ≤ dsPhase B D γ q δ Q κ α a t u ∧
      0 ≤ dsPhase B D γ q δ Q κ α a t u := by
  obtain ⟨ht, hu, hW⟩ := dsWeight_ne_zero hw
  have huL := rescaledDomain_subset hu
  have hP : 0 < ∏ j, u j ^ κ j :=
    Finset.prod_pos fun j _ ↦ rpow_pos_of_pos (limitDomain_pos huL j) _
  have ht0 : 0 < t := zero_lt_one.trans_le ht
  have hBt : 0 ≤ B * t ^ (δ - ∑ j, κ j * α j) := mul_nonneg h.hB.le (rpow_pos_of_pos ht0 _).le
  have ha := h.a_bounds _ _ hW
  unfold dsPhase
  rw [if_pos ⟨ht, huL⟩]
  refine ⟨mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left ha.1 hBt) hP.le, ?_⟩
  exact mul_nonneg (mul_nonneg hBt (h.hamin.le.trans ha.1)) hP.le

theorem dsPhase_tendsto (u : ι → ℝ) :
    Tendsto (fun t ↦ dsPhase B D γ q δ Q κ α a t u) atTop (𝓝 (dsProfile B D γ q δ Q κ α a₀ u)) := by
  by_cases hu : u ∈ limitDomain D γ q Q α
  · have hev : (fun t ↦ dsPhase B D γ q δ Q κ α a t u) =ᶠ[atTop] fun t ↦
        B * t ^ (δ - ∑ j, κ j * α j) * a (rescale t α u) (rescaledCut D γ q Q α t u) *
          ∏ j, u j ^ κ j := by
      filter_upwards [eventually_ge_atTop 1] with t ht
      unfold dsPhase
      rw [if_pos ⟨ht, hu⟩]
    unfold dsProfile
    rw [if_pos hu]
    by_cases htied : ∑ j, κ j * α j = δ
    · rw [if_pos htied]
      have hev' : (fun t ↦ dsPhase B D γ q δ Q κ α a t u) =ᶠ[atTop] fun t ↦
          B * a (rescale t α u) (rescaledCut D γ q Q α t u) * ∏ j, u j ^ κ j := by
        filter_upwards [hev] with t ht
        rw [ht, htied, sub_self, Real.rpow_zero, mul_one]
      exact (((h.a_lim u hu).const_mul B).mul_const _).congr' hev'.symm
    · rw [if_neg htied]
      have hlt : δ < ∑ j, κ j * α j := lt_of_le_of_ne h.feasible.2.2 (Ne.symm htied)
      have h0 := (((tendsto_rpow_phase hlt).const_mul B).mul (h.a_lim u hu)).mul_const
        (∏ j, u j ^ κ j)
      simp only [mul_zero, zero_mul] at h0
      exact h0.congr' hev.symm
  · have e : (fun t ↦ dsPhase B D γ q δ Q κ α a t u) = fun _ ↦ 0 := by
      funext t; simp only [dsPhase, hu, and_false, if_false]
    unfold dsProfile
    rw [if_neg hu, e]
    exact tendsto_const_nhds

theorem dsWeight_tendsto (u : ι → ℝ) :
    Tendsto (fun t ↦ dsWeight D γ q Q r α W t u) atTop (𝓝 (dsWeight₀ D γ q Q r α W₀ u)) := by
  by_cases hu : u ∈ limitDomain D γ q Q α
  · have hev : (fun t ↦ dsWeight D γ q Q r α W t u) =ᶠ[atTop] fun t ↦
        W (rescale t α u) (rescaledCut D γ q Q α t u) * ∏ j, u j ^ r j := by
      filter_upwards [eventually_ge_atTop 1,
        eventually_mem_rescaledDomain h.hq h.feasible.1 h.feasible.2.1 hu] with t ht hmem
      unfold dsWeight
      rw [if_pos ht, Set.indicator_of_mem hmem]
    unfold dsWeight₀
    rw [Set.indicator_of_mem hu]
    exact ((h.W_lim u hu).mul_const _).congr' hev.symm
  · have e : (fun t ↦ dsWeight D γ q Q r α W t u) = fun _ ↦ 0 := by
      funext t
      by_contra hne
      exact hu (rescaledDomain_subset (dsWeight_ne_zero hne).2.1)
    unfold dsWeight₀
    rw [Set.indicator_of_notMem hu, e]
    exact tendsto_const_nhds

theorem abs_dsWeight_le (t : ℝ) (u : ι → ℝ) :
    |dsWeight D γ q Q r α W t u| ≤ dsEnvelope D γ q Q r α Wmax u := by
  have henv : 0 ≤ dsEnvelope D γ q Q r α Wmax u :=
    mul_nonneg h.Wmax_nonneg (Set.indicator_nonneg (fun u hu ↦
      Finset.prod_nonneg fun j _ ↦ rpow_nonneg (limitDomain_pos hu j).le _) u)
  by_cases hw : dsWeight D γ q Q r α W t u = 0
  · rw [hw, abs_zero]; exact henv
  · obtain ⟨ht, hu, _⟩ := dsWeight_ne_zero hw
    have huL := rescaledDomain_subset hu
    have hr : 0 ≤ ∏ j, u j ^ r j :=
      Finset.prod_nonneg fun j _ ↦ rpow_nonneg (limitDomain_pos huL j).le _
    unfold dsWeight dsEnvelope
    rw [if_pos ht, Set.indicator_of_mem hu, Set.indicator_of_mem huL, abs_mul, abs_of_nonneg hr]
    exact mul_le_mul_of_nonneg_right (h.W_bd _ _) hr

theorem lower {t : ℝ} {u : ι → ℝ} (hw : dsWeight D γ q Q r α W t u ≠ 0) :
    amin / amax * dsProfile B D γ q δ Q κ α a₀ u ≤ dsPhase B D γ q δ Q κ α a t u := by
  obtain ⟨_, hu, _⟩ := dsWeight_ne_zero hw
  have huL := rescaledDomain_subset hu
  obtain ⟨hge, hnn⟩ := h.dsPhase_ge hw
  unfold dsProfile
  rw [if_pos huL]
  by_cases htied : ∑ j, κ j * α j = δ
  · rw [if_pos htied]
    rw [htied, sub_self, Real.rpow_zero, mul_one] at hge
    have hP : 0 ≤ ∏ j, u j ^ κ j :=
      Finset.prod_nonneg fun j _ ↦ rpow_nonneg (limitDomain_pos huL j).le _
    have ha₀ := h.a₀_bounds u huL
    have h1 : amin / amax * a₀ u ≤ amin := by
      rw [div_mul_eq_mul_div, div_le_iff₀ h.amax_pos]
      exact mul_le_mul_of_nonneg_left ha₀.2 h.hamin.le
    calc amin / amax * (B * a₀ u * ∏ j, u j ^ κ j)
        = B * (amin / amax * a₀ u) * ∏ j, u j ^ κ j := by ring
      _ ≤ B * amin * ∏ j, u j ^ κ j :=
          mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left h1 h.hB.le) hP
      _ ≤ dsPhase B D γ q δ Q κ α a t u := hge
  · rw [if_neg htied, mul_zero]
    exact hnn

/-- **The dominant-scale certificate**: the moving data form a `RescaledData`. -/
theorem rescaledData :
    RescaledData atTop volume (dsPhase B D γ q δ Q κ α a) (dsWeight D γ q Q r α W)
      (dsProfile B D γ q δ Q κ α a₀) (dsWeight₀ D γ q Q r α W₀) (dsEnvelope D γ q Q r α Wmax)
      (amin / amax) where
  hc := div_pos h.hamin h.amax_pos
  hc1 := div_le_one_of_le₀ h.hle h.amax_pos.le
  G_meas := measurable_dsPhase h.a_meas
  w_meas := measurable_dsWeight h.W_meas
  G_nonneg := Eventually.of_forall fun _ _ hw ↦ (h.dsPhase_ge hw).2
  Φ₀_nonneg := h.dsProfile_nonneg
  G_lim := h.dsPhase_tendsto
  w_lim := h.dsWeight_tendsto
  w_bd := h.abs_dsWeight_le
  lower := Eventually.of_forall fun _ _ hw ↦ h.lower hw
  int := h.int
  Φint := h.Φint

/-- **The constant of the dominant scale**: `t^λ K(t) → A ∫ w₀ e^{-Φ₀}` with
`λ = γp + ∑ (r_j + 1) α_j`. -/
theorem tendsto_modelKernel (A p : ℝ) :
    Tendsto (fun t ↦ t ^ lpExponent γ p (fun j ↦ r j + 1) α *
        modelKernel A B D γ p q δ Q κ r W a t) atTop
      (𝓝 (A * ∫ u, dsWeight₀ D γ q Q r α W₀ u * exp (-dsProfile B D γ q δ Q κ α a₀ u))) := by
  have hd := h.rescaledData
  have hlim := (hd.tendsto_den (g := fun _ ↦ 1) measurable_const (Mg := 1)
    (fun _ ↦ by simp) zero_le_one).const_mul A
  simp only [one_mul] at hlim
  refine hlim.congr' ?_
  filter_upwards [eventually_ge_atTop 1] with t ht
  have ht0 : 0 < t := zero_lt_one.trans_le ht
  rw [modelKernel_eq_rescaled (α := α) A p h.W_meas h.a_meas ht0]
  have hI : ∫ u, rescaledIntegrand B D γ q δ Q κ r α W a t u =
      ∫ u, dsWeight D γ q Q r α W t u * exp (-(dsPhase B D γ q δ Q κ α a t u)) :=
    integral_congr_ae (Eventually.of_forall fun u ↦ (dsWeight_mul_exp ht u).symm)
  rw [hI, Real.rpow_neg ht0.le]
  have hne : t ^ lpExponent γ p (fun j ↦ r j + 1) α ≠ 0 := (rpow_pos_of_pos ht0 _).ne'
  field_simp

end DominantScaleHyp

end Laplace.Multi
