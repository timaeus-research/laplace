/-
Copyright (c) 2026 Timaeus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Timaeus
-/
import Mathlib
import Laplace.Multi.EssentialRange
import Laplace.Multi.MeanMapEmbedding

/-!
# The moment-body theorem for a bounded statistic on a general alphabet

For a bounded measurable statistic `S : J → X → ℝ` under a positive prior `π·μ` on a general
measurable space, with no nonzero direction `v` such that `S_v` is a.e. constant, the mean map
`η(θ) = E_θ[S]` of the exponential family `P_θ ∝ π e^{-⟨θ,S⟩}` satisfies

  `range η = interior (momentBody μ π S)`,
  `momentBody = closed convex hull of the essential range`

(`range_meanMap_eq_interior_momentBody`). The inclusion `⊆` is the open-map theorem of
`MeanMapEmbedding` together with `mean_mem_momentBody` (Hahn–Banach); the inclusion `⊇` is the
variational argument of `MomentPolytope` with the minimal prior weight replaced by the cap lemma of
`EssentialRange`: `ψ(θ) + ⟨θ, x⟩ ≥ c‖θ‖ + log m` (`coercive_bound_general`), a minimiser exists, and
the first-order condition at the minimiser is `η(θ*) = x`.

Together with `NaturalCoordinates` (temperature and data as one family) this is the global
description of the response chart of the joint family on an arbitrary alphabet: the prior at the
origin of natural coordinates, exactly one posterior for every interior point of the moment body.
-/

open MeasureTheory Filter Topology Set

namespace Laplace.Multi

section

variable {X : Type*} [MeasurableSpace X] {μ : Measure X} {J : Type*} [Fintype J] [Nonempty J]
variable [Nonempty X] {π : X → ℝ} (hπm : Measurable π) (hπi : Integrable π μ)
  (hπ : ∀ x, 0 < π x) (hπpos : 0 < ∫ x, π x ∂μ) {S : J → X → ℝ} (hS : ∀ j, Bdd (S j))
include hπm hπi hπ hπpos hS

omit [MeasurableSpace X] [Nonempty X] [Nonempty J] hπm hπi hπ hπpos hS in
theorem affLoss_zero_eq_dotJ (θ : J → ℝ) (y : X) :
    affLoss (fun _ ↦ (0 : ℝ)) S θ y = dotJ θ (statPoint S y) := by
  simp [affLoss, dotJ, statPoint]

/-! ### The mean map lands in the moment body -/

omit [Nonempty J] in
/-- **The mean map lands in the moment body** (Hahn–Banach separation). -/
theorem mean_mem_momentBody (θ : J → ℝ) :
    meanMap μ π (fun _ ↦ (0 : ℝ)) S 1 θ ∈ momentBody μ π S := by
  classical
  by_contra hnot
  obtain ⟨f, u, hfu, hC⟩ := geometric_hahn_banach_point_closed (convex_momentBody S)
    (isClosed_momentBody S) hnot
  set v : J → ℝ := fun j ↦ f (Pi.single j 1) with hv
  -- the functional in coordinates
  have hf : ∀ y : J → ℝ, f y = ∑ j, v j * y j := fun y ↦ by
    conv_lhs => rw [pi_eq_sum_univ' y]
    rw [map_sum]
    exact Finset.sum_congr rfl fun j _ ↦ by rw [map_smul, smul_eq_mul, mul_comm]
  have hfS : ∀ x, f (statPoint S x) = dirLoss S v x := fun x ↦ by
    rw [hf]; rfl
  have hν : Integrable (baseWeight π (affLoss (fun _ ↦ (0 : ℝ)) S θ) 1) μ :=
    (tiltData_aff hπm hπi (fun x ↦ (hπ x).le) hπpos measurable_const (zero_bdd (X := X)) hS θ θ
      1).choose_spec.ν_int
  have hη : f (meanMap μ π (fun _ ↦ (0 : ℝ)) S 1 θ) =
      priorExp μ π (affLoss (fun _ ↦ (0 : ℝ)) S θ) (dirLoss S v) 1 := by
    rw [hf, priorExp_dirLoss hν hS v]
    rfl
  -- a.e. lower bound on the functional of the statistic
  have hae : ∀ᵐ x ∂μ, u < dirLoss S v x := by
    filter_upwards [ae_statPoint_mem_essRange hπm hπ hS] with x hx
    rw [← hfS]
    exact hC _ (essRange_subset_momentBody S hx)
  have hZ := affZ_pos hπm hπi hπ hπpos measurable_const (zero_bdd (X := X)) hS (t := 1) θ
  have hint := integrable_mul_affWeight_of_bdd hπm hπi hπ hπpos measurable_const (zero_bdd (X := X))
    hS (t := 1) θ (bdd_dirLoss hS v)
  have hle : u ≤ priorExp μ π (affLoss (fun _ ↦ (0 : ℝ)) S θ) (dirLoss S v) 1 := by
    unfold priorExp
    rw [le_div_iff₀ hZ]
    calc u * priorZ μ π (affLoss (fun _ ↦ (0 : ℝ)) S θ) 1
        = ∫ x, u * (Real.exp (-(1 * affLoss (fun _ ↦ (0 : ℝ)) S θ x)) * π x) ∂μ := by
          unfold priorZ; rw [MeasureTheory.integral_const_mul]
      _ ≤ ∫ x, dirLoss S v x * Real.exp (-(1 * affLoss (fun _ ↦ (0 : ℝ)) S θ x)) * π x ∂μ := by
          refine integral_mono_ae (hν.const_mul u) hint ?_
          filter_upwards [hae] with x hx
          have : 0 < Real.exp (-(1 * affLoss (fun _ ↦ (0 : ℝ)) S θ x)) * π x := by
            have := hπ x; positivity
          exact (mul_le_mul_of_nonneg_right hx.le this.le).trans_eq (by ring)
  rw [← hη] at hle
  linarith

/-! ### Coercivity from the cap lemma -/

omit [Nonempty X] [Nonempty J] hπm hπi hπ hπpos in
theorem measurable_cap (e x : J → ℝ) (c : ℝ) :
    MeasurableSet {y | c ≤ dotJ e (x - statPoint S y)} := by
  refine measurableSet_le measurable_const ?_
  simp only [dotJ, Pi.sub_apply, statPoint]
  exact Finset.measurable_sum _ fun j _ ↦ (measurable_const.sub (hS j).1).const_mul _

omit [Nonempty X] in
/-- **Coercivity on a general alphabet**: with the cap constants `c, m` of `x`,
`ψ(θ) + ⟨θ, x⟩ ≥ c ‖θ‖ + log m`. -/
theorem coercive_bound_general {x : J → ℝ} {c m : ℝ} (hm : 0 < m)
    (hcap : ∀ e : J → ℝ, ‖e‖ = 1 → m ≤ ∫ y in {y | c ≤ dotJ e (x - statPoint S y)}, π y ∂μ)
    (θ : J → ℝ) :
    c * ‖θ‖ + Real.log m ≤ affLogZ μ π (fun _ ↦ (0 : ℝ)) S 1 θ + dotJ θ x := by
  -- a unit direction: `θ/‖θ‖`, or any unit vector when `θ = 0`
  obtain ⟨j₀⟩ := ‹Nonempty J›
  classical
  set e : J → ℝ := if θ = 0 then Pi.single j₀ 1 else ‖θ‖⁻¹ • θ with he
  have he1 : ‖e‖ = 1 := by
    rw [he]
    split_ifs with h0
    · rw [Pi.norm_single, norm_one]
    · rw [norm_smul, norm_inv, norm_norm, inv_mul_cancel₀ (norm_ne_zero_iff.2 h0)]
  -- on the cap of `e`, the exponent is at least `c‖θ‖ − ⟨θ,x⟩`
  have hpt : ∀ y ∈ {y | c ≤ dotJ e (x - statPoint S y)},
      c * ‖θ‖ - dotJ θ x ≤ -(1 * affLoss (fun _ ↦ (0 : ℝ)) S θ y) := by
    intro y hy
    have hy' : c ≤ dotJ e (x - statPoint S y) := hy
    rw [one_mul, affLoss_zero_eq_dotJ]
    have hlin := isLinearMap_dotJ θ
    have e1 : dotJ θ (x - statPoint S y) = ‖θ‖ * dotJ e (x - statPoint S y) := by
      rw [he]
      split_ifs with h0
      · simp [h0, dotJ]
      · have : dotJ (‖θ‖⁻¹ • θ) (x - statPoint S y) = ‖θ‖⁻¹ * dotJ θ (x - statPoint S y) :=
          dotJ_smul_left _ _ _
        rw [this, ← mul_assoc, mul_inv_cancel₀ (norm_ne_zero_iff.2 h0), one_mul]
    have e2 : dotJ θ (x - statPoint S y) = dotJ θ x - dotJ θ (statPoint S y) :=
      (isLinearMap_dotJ θ).map_sub _ _
    have : c * ‖θ‖ ≤ dotJ θ (x - statPoint S y) := by
      rw [e1]
      exact mul_le_mul_of_nonneg_left hy' (norm_nonneg _) |>.trans_eq' (by ring)
    linarith
  have hA := measurable_cap hS e x c
  have hmass := hcap e he1
  have hZ : 0 < priorZ μ π (affLoss (fun _ ↦ (0 : ℝ)) S θ) 1 :=
    affZ_pos hπm hπi hπ hπpos measurable_const (zero_bdd (X := X)) hS (t := 1) θ
  have hν : Integrable (baseWeight π (affLoss (fun _ ↦ (0 : ℝ)) S θ) 1) μ :=
    (tiltData_aff hπm hπi (fun x ↦ (hπ x).le) hπpos measurable_const (zero_bdd (X := X)) hS θ θ
      1).choose_spec.ν_int
  -- the partition function dominates the cap contribution
  have hlow : Real.exp (c * ‖θ‖ - dotJ θ x) * m ≤ priorZ μ π (affLoss (fun _ ↦ (0 : ℝ)) S θ) 1 := by
    calc Real.exp (c * ‖θ‖ - dotJ θ x) * m
        ≤ Real.exp (c * ‖θ‖ - dotJ θ x) * ∫ y in {y | c ≤ dotJ e (x - statPoint S y)}, π y ∂μ :=
          mul_le_mul_of_nonneg_left hmass (Real.exp_pos _).le
      _ = ∫ y in {y | c ≤ dotJ e (x - statPoint S y)}, Real.exp (c * ‖θ‖ - dotJ θ x) * π y ∂μ := by
          rw [MeasureTheory.integral_const_mul]
      _ ≤ ∫ y in {y | c ≤ dotJ e (x - statPoint S y)},
            Real.exp (-(1 * affLoss (fun _ ↦ (0 : ℝ)) S θ y)) * π y ∂μ := by
          refine setIntegral_mono_on (hπi.const_mul _).integrableOn hν.integrableOn hA
            fun y hy ↦ ?_
          exact mul_le_mul_of_nonneg_right (Real.exp_le_exp.2 (hpt y hy)) (hπ y).le
      _ ≤ priorZ μ π (affLoss (fun _ ↦ (0 : ℝ)) S θ) 1 := by
          unfold priorZ
          exact setIntegral_le_integral hν
            (Filter.Eventually.of_forall fun y ↦ by have := hπ y; positivity)
  have := Real.log_le_log (by positivity) hlow
  rw [Real.log_mul (Real.exp_pos _).ne' hm.ne', Real.log_exp] at this
  unfold affLogZ
  linarith

/-! ### Existence of a minimiser and the first-order condition -/

omit [Nonempty J] in
theorem continuous_affLogZ_general : Continuous (affLogZ μ π (fun _ ↦ (0 : ℝ)) S 1) := by
  have hZ : Continuous (fun θ : J → ℝ ↦ priorZ μ π (affLoss (fun _ ↦ (0 : ℝ)) S θ) 1) := by
    refine continuous_iff_continuousAt.2 fun θ ↦ ?_
    have h := (hasFDerivAt_affNum hπm hπi (fun x ↦ (hπ x).le) measurable_const (zero_bdd (X := X))
      hS (φ := fun _ ↦ (1 : ℝ)) measurable_const (Mφ := 1) (fun _ ↦ by simp) one_pos
      θ).2.continuousAt
    refine h.congr (Filter.Eventually.of_forall fun a ↦ ?_)
    unfold priorZ
    simp
  exact hZ.log fun θ ↦ (affZ_pos hπm hπi hπ hπpos measurable_const (zero_bdd (X := X)) hS
    (t := 1) θ).ne'

/-- The variational functional attains its minimum when `x` is interior. -/
theorem exists_min_variational_general {x : J → ℝ}
    (hx : x ∈ interior (momentBody μ π S)) :
    ∃ θ₀ : J → ℝ, ∀ θ, affLogZ μ π (fun _ ↦ (0 : ℝ)) S 1 θ₀ + dotJ θ₀ x ≤
      affLogZ μ π (fun _ ↦ (0 : ℝ)) S 1 θ + dotJ θ x := by
  obtain ⟨c, hc, m, hm, hcap⟩ := cap_lemma hπm hπ hS hπi hx
  have hcont : Continuous (fun θ : J → ℝ ↦ affLogZ μ π (fun _ ↦ (0 : ℝ)) S 1 θ + dotJ θ x) :=
    (continuous_affLogZ_general hπm hπi hπ hπpos hS).add (continuous_dotJ_left x)
  refine hcont.exists_forall_le ?_
  have hlim : Tendsto (fun θ : J → ℝ ↦ c * ‖θ‖ + Real.log m) (cocompact _) atTop :=
    tendsto_atTop_add_const_right _ _ (tendsto_norm_cocompact_atTop.const_mul_atTop hc)
  exact tendsto_atTop_mono (coercive_bound_general hπm hπi hπ hπpos hS hm hcap) hlim

omit [Nonempty J] in
/-- The first-order condition at a minimiser: `η(θ₀) = x`. -/
theorem meanMap_eq_of_min_general {x θ₀ : J → ℝ}
    (hmin : ∀ θ, affLogZ μ π (fun _ ↦ (0 : ℝ)) S 1 θ₀ + dotJ θ₀ x ≤
      affLogZ μ π (fun _ ↦ (0 : ℝ)) S 1 θ + dotJ θ x) :
    meanMap μ π (fun _ ↦ (0 : ℝ)) S 1 θ₀ = x := by
  classical
  obtain ⟨hLm, ML, hLb⟩ := bdd_affLoss (L₀ := fun _ : X ↦ (0 : ℝ)) measurable_const
    (zero_bdd (X := X)) hS θ₀
  have hT : TiltData μ (baseWeight π (affLoss (fun _ ↦ (0 : ℝ)) S θ₀) 1) (fun _ ↦ 0) 0 :=
    tiltData_baseWeight_of_bounded μ hπm hπi (fun x ↦ (hπ x).le) hπpos hLm hLb measurable_const
      (fun _ ↦ by simp) 1
  funext j
  set v : J → ℝ := Pi.single j 1 with hv
  have hψ := hT.hasDerivAt_affLogZ_dir' hS v
  have hd : HasDerivAt (fun ε : ℝ ↦ dotJ (θ₀ + ε • v) x) (dotJ v x) 0 := by
    have e : (fun ε : ℝ ↦ dotJ (θ₀ + ε • v) x) = fun ε ↦ dotJ θ₀ x + ε * dotJ v x := by
      funext ε; rw [dotJ_add_left, dotJ_smul_left]
    rw [e]
    simpa using ((hasDerivAt_id (0 : ℝ)).mul_const (dotJ v x)).const_add (dotJ θ₀ x)
  have hsum := hψ.add hd
  have hloc : IsLocalMin (fun ε : ℝ ↦ affLogZ μ π (fun _ ↦ (0 : ℝ)) S 1 (θ₀ + ε • v) +
      dotJ (θ₀ + ε • v) x) 0 := by
    refine Filter.Eventually.of_forall fun ε ↦ ?_
    simp only [zero_smul, add_zero]
    exact hmin _
  have h0 := hloc.hasDerivAt_eq_zero hsum
  rw [hv, dotJ_single_left] at h0
  rw [Finset.sum_eq_single j (fun i _ hi ↦ by simp [hi]) (by simp)] at h0
  simp only [Pi.single_eq_same, one_mul, neg_mul] at h0
  linarith

/-! ### The moment-body theorem -/

/-- **The moment-body theorem**: for a bounded statistic under a positive prior on a general
alphabet, with no a.e.-constant nonzero contrast, the image of the mean map is exactly the interior
of the moment body. -/
theorem range_meanMap_eq_interior_momentBody
    (hnd : ∀ v : J → ℝ, v ≠ 0 → ¬ ∃ c : ℝ, ∀ᵐ x ∂μ, π x ≠ 0 → dirLoss S v x = c) :
    Set.range (meanMap μ π (fun _ ↦ (0 : ℝ)) S 1) = interior (momentBody μ π S) := by
  refine Set.Subset.antisymm ?_ fun x hx ↦ ?_
  · refine interior_maximal (Set.range_subset_iff.2 fun θ ↦
      mean_mem_momentBody hπm hπi hπ hπpos hS θ) ?_
    exact isOpen_range_meanMap hπm hπi (fun x ↦ (hπ x).le) hπpos measurable_const
      (zero_bdd (X := X)) hS one_pos hnd
  · obtain ⟨θ₀, hmin⟩ := exists_min_variational_general hπm hπi hπ hπpos hS hx
    exact ⟨θ₀, meanMap_eq_of_min_general hπm hπi hπ hπpos hS hmin⟩

end

end Laplace.Multi
