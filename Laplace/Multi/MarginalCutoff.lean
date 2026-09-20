/-
Copyright (c) 2026 Timaeus Research. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniel Murfet
-/
import Mathlib
import Laplace.Multi.CylinderSufficient
import Laplace.Multi.PositiveWeightFamily

/-!
# Common cylinders with an arbitrary cutoff: the marginal weight

The common-cylinder theorem (`cylinder_normalized_families_force_germ_eq_at`) used a product
cutoff `χ₁(x) χ₂(y)`. For an arbitrary smooth compactly supported cutoff `χ(x, y)` on the
product, positive near the base point, the tangential variables still integrate out: the data
of tangential degree zero are `∫ a(x) x^α e^{-tK_j(x)} dx` with the *marginal weight*
`a(x) = ∫ χ(x, y) dy`. The marginal is smooth (it is the convolution of the constant `1` with
the parametric family `y ↦ χ(x, y)`, `contDiffOn_convolution_right_with_param`), compactly
supported, nonnegative, and bounded below by `c₀ · vol B(p₂, r)` on `B(p₁, r)`; so the
positive-weight form of the isolated-zero theorem
(`normalized_families_force_germ_eq_at_of_weight_monomials`) applies in the transverse
variables.
-/

open Real MeasureTheory Filter Topology
open scoped ContDiff Convolution

namespace Laplace.Multi

variable {ι₁ ι₂ : Type*} [Fintype ι₁] [Fintype ι₂]

/-- Gluing transverse and tangential coordinates. -/
abbrev glue (x : ι₁ → ℝ) (y : ι₂ → ℝ) : ι₁ ⊕ ι₂ → ℝ := Sum.elim x y

omit [Fintype ι₁] [Fintype ι₂] in
theorem continuous_transverse : Continuous (transverse : (ι₁ ⊕ ι₂ → ℝ) → ι₁ → ℝ) :=
  continuous_pi fun i ↦ continuous_apply (Sum.inl i)

omit [Fintype ι₁] [Fintype ι₂] in
theorem continuous_tangential : Continuous (tangential : (ι₁ ⊕ ι₂ → ℝ) → ι₂ → ℝ) :=
  continuous_pi fun i ↦ continuous_apply (Sum.inr i)

omit [Fintype ι₁] [Fintype ι₂] in
theorem continuous_glue (x : ι₁ → ℝ) : Continuous (glue x : (ι₂ → ℝ) → ι₁ ⊕ ι₂ → ℝ) :=
  continuous_pi fun i ↦ by
    cases i with
    | inl i => exact continuous_const
    | inr i => exact continuous_apply i

/-- Gluing points of two balls of the same radius lands in the sup-norm ball. -/
theorem glue_mem_ball {p : ι₁ ⊕ ι₂ → ℝ} {r : ℝ} (hr : 0 < r) {x : ι₁ → ℝ} {y : ι₂ → ℝ}
    (hx : x ∈ Metric.ball (transverse p) r) (hy : y ∈ Metric.ball (tangential p) r) :
    glue x y ∈ Metric.ball p r := by
  rw [Metric.mem_ball, dist_pi_lt_iff hr] at hx hy ⊢
  intro i
  cases i with
  | inl i => exact hx i
  | inr i => exact hy i

/-- The marginal weight of a cutoff on the product: the tangential variables integrated out. -/
noncomputable def marginal (χ : (ι₁ ⊕ ι₂ → ℝ) → ℝ) (x : ι₁ → ℝ) : ℝ := ∫ y, χ (glue x y)

variable {χ : (ι₁ ⊕ ι₂ → ℝ) → ℝ}

omit [Fintype ι₁] in
theorem marginal_nonneg (hχ0 : ∀ w, 0 ≤ χ w) (x : ι₁ → ℝ) : 0 ≤ marginal χ x :=
  integral_nonneg fun _ ↦ hχ0 _

omit [Fintype ι₁] in
theorem marginal_eq_zero_of_notMem {x : ι₁ → ℝ} (hx : x ∉ transverse '' tsupport χ) :
    marginal χ x = 0 := by
  have h : ∀ y, χ (glue x y) = 0 := by
    intro y
    by_contra hne
    exact hx ⟨glue x y, subset_tsupport _ hne, rfl⟩
  simp [marginal, h]

omit [Fintype ι₁] in
theorem hasCompactSupport_marginal (hχs : HasCompactSupport χ) :
    HasCompactSupport (marginal χ) :=
  HasCompactSupport.intro (hχs.image continuous_transverse) fun _ hx ↦
    marginal_eq_zero_of_notMem hx

omit [Fintype ι₁] in
theorem tsupport_marginal_subset (hχs : HasCompactSupport χ) :
    tsupport (marginal χ) ⊆ transverse '' tsupport χ := by
  refine closure_minimal ?_ (hχs.image continuous_transverse).isClosed
  intro x hx
  by_contra hnot
  exact hx (marginal_eq_zero_of_notMem hnot)

omit [Fintype ι₁] in
/-- Slices of a compactly supported cutoff are integrable. -/
theorem integrable_slice (hχc : Continuous χ) (hχs : HasCompactSupport χ) (x : ι₁ → ℝ) :
    Integrable fun y ↦ χ (glue x y) := by
  refine (hχc.comp (continuous_glue x)).integrable_of_hasCompactSupport
    (HasCompactSupport.intro (hχs.image continuous_tangential) fun y hy ↦ ?_)
  by_contra hne
  exact hy ⟨glue x y, subset_tsupport _ hne, rfl⟩

/-- A cutoff bounded below on a sup-norm ball has marginal bounded below on the transverse
ball. -/
theorem marginal_ge (hχc : Continuous χ) (hχs : HasCompactSupport χ) (hχ0 : ∀ w, 0 ≤ χ w)
    {p : ι₁ ⊕ ι₂ → ℝ} {r c₀ : ℝ} (hr : 0 < r) (hc₀ : ∀ w ∈ Metric.ball p r, c₀ ≤ χ w) :
    ∀ x ∈ Metric.ball (transverse p) r,
      c₀ * (volume (Metric.ball (tangential p) r)).toReal ≤ marginal χ x := by
  intro x hx
  have hlow : ∀ y, (Metric.ball (tangential p) r).indicator (fun _ ↦ c₀) y ≤ χ (glue x y) := by
    intro y
    by_cases hy : y ∈ Metric.ball (tangential p) r
    · rw [Set.indicator_of_mem hy]
      exact hc₀ _ (glue_mem_ball hr hx hy)
    · rw [Set.indicator_of_notMem hy]
      exact hχ0 _
  have h := integral_mono ((integrable_indicator_iff Metric.isOpen_ball.measurableSet).mpr
    (integrableOn_const measure_ball_lt_top.ne)) (integrable_slice hχc hχs x) hlow
  rwa [integral_indicator_const _ Metric.isOpen_ball.measurableSet, smul_eq_mul, measureReal_def,
    mul_comm] at h

/-- **Smoothness of the marginal.** The marginal of a smooth compactly supported cutoff is
smooth: it is the convolution of the constant `1` with the parametric family `y ↦ χ (x, y)`. -/
theorem contDiff_marginal (hχ : ContDiff ℝ ∞ χ) (hχs : HasCompactSupport χ) :
    ContDiff ℝ ∞ (marginal χ) := by
  have hk : IsCompact (tangential '' tsupport χ) := hχs.image continuous_tangential
  have hgs : ∀ (q : ι₁ → ℝ) (y : ι₂ → ℝ), q ∈ (Set.univ : Set (ι₁ → ℝ)) →
      y ∉ tangential '' tsupport χ → χ (glue q y) = 0 := by
    intro q y _ hy
    by_contra hne
    exact hy ⟨glue q y, subset_tsupport _ hne, rfl⟩
  have hg : ContDiffOn ℝ ∞ (↿fun (q : ι₁ → ℝ) (y : ι₂ → ℝ) ↦ χ (glue q y))
      (Set.univ ×ˢ Set.univ) := by
    rw [Set.univ_prod_univ, contDiffOn_univ]
    have hlin : (↿fun (q : ι₁ → ℝ) (y : ι₂ → ℝ) ↦ χ (glue q y)) =
        χ ∘ ⇑(LinearMap.toContinuousLinearMap
          (LinearEquiv.sumArrowLequivProdArrow ι₁ ι₂ ℝ ℝ).symm.toLinearMap) := by
      funext q
      rfl
    rw [hlin]
    exact hχ.comp (ContinuousLinearMap.contDiff _)
  have hconv := contDiffOn_convolution_right_with_param (𝕜 := ℝ)
    (μ := (volume : Measure (ι₂ → ℝ))) (f := fun _ : ι₂ → ℝ ↦ (1 : ℝ)) (n := ⊤)
    (ContinuousLinearMap.mul ℝ ℝ) isOpen_univ hk hgs (locallyIntegrable_const 1) hg
  rw [Set.univ_prod_univ, contDiffOn_univ] at hconv
  have hcomp := hconv.comp ((contDiff_id (E := ι₁ → ℝ)).prodMk (contDiff_const (c := (0 : ι₂ → ℝ))))
  have heq : marginal χ = (fun q : (ι₁ → ℝ) × (ι₂ → ℝ) ↦
      ((fun _ : ι₂ → ℝ ↦ (1 : ℝ)) ⋆[ContinuousLinearMap.mul ℝ ℝ, volume]
        fun y ↦ χ (glue q.1 y)) q.2) ∘ fun x ↦ (x, (0 : ι₂ → ℝ)) := by
    funext x
    simp only [Function.comp, marginal, convolution_def, ContinuousLinearMap.mul_apply', one_mul,
      zero_sub]
    exact (integral_neg_eq_self (fun y ↦ χ (glue x y)) volume).symm
  rw [heq]
  exact hcomp

/-- **Integrating out the tangential variables** against a transverse function. -/
theorem integral_mul_transverse_eq_marginal (hχc : Continuous χ) (hχs : HasCompactSupport χ)
    {F : (ι₁ → ℝ) → ℝ} (hF : Continuous F) :
    ∫ w : ι₁ ⊕ ι₂ → ℝ, χ w * F (transverse w) = ∫ x : ι₁ → ℝ, marginal χ x * F x := by
  have hmp := volume_measurePreserving_sumPiEquivProdPi_symm (fun _ : ι₁ ⊕ ι₂ ↦ ℝ)
  have hint : Integrable (fun w : ι₁ ⊕ ι₂ → ℝ ↦ χ w * F (transverse w)) :=
    (hχc.mul (hF.comp continuous_transverse)).integrable_of_hasCompactSupport hχs.mul_right
  rw [← hmp.integral_comp' (fun w ↦ χ w * F (transverse w))]
  have hint' : Integrable (fun z : (ι₁ → ℝ) × (ι₂ → ℝ) ↦
      χ ((MeasurableEquiv.sumPiEquivProdPi fun _ ↦ ℝ).symm z) *
        F (transverse ((MeasurableEquiv.sumPiEquivProdPi fun _ ↦ ℝ).symm z)))
      (volume.prod volume) := by
    rw [← Measure.volume_eq_prod]
    exact (hmp.integrable_comp_emb (MeasurableEquiv.measurableEmbedding _)).mpr hint
  rw [Measure.volume_eq_prod (ι₁ → ℝ) (ι₂ → ℝ), integral_prod _ hint']
  refine integral_congr_ae (Filter.Eventually.of_forall fun x ↦ ?_)
  beta_reduce
  change ∫ y, χ (glue x y) * F x = marginal χ x * F x
  rw [integral_mul_const]
  rfl

/-- **Common cylinders with an arbitrary cutoff.** As
`cylinder_normalized_families_force_germ_eq_at` but with any smooth compactly supported cutoff
`χ ≥ 0` on the product with `χ ≥ c₀ > 0` on a ball around `p`; the marginal weight
`∫ χ(x, y) dy` carries the transverse data. -/
theorem cylinder_normalized_families_force_germ_eq_at_of_cutoff
    {K₁ K₂ : (ι₁ → ℝ) → ℝ} {L₁ L₂ : (ι₁ ⊕ ι₂ → ℝ) → ℝ}
    (hL₁ : ∀ w, L₁ w = K₁ (transverse w)) (hL₂ : ∀ w, L₂ w = K₂ (transverse w))
    (h1 : ContDiff ℝ ∞ K₁) (h2 : ContDiff ℝ ∞ K₂)
    (hK1 : ∀ x, 0 ≤ K₁ x) (hK2 : ∀ x, 0 ≤ K₂ x) {p : ι₁ ⊕ ι₂ → ℝ}
    (hA1 : AnalyticAt ℝ K₁ (transverse p)) (hA2 : AnalyticAt ℝ K₂ (transverse p))
    (hp1 : K₁ (transverse p) = 0) (hp2 : K₂ (transverse p) = 0)
    (hχ : ContDiff ℝ ∞ χ) (hχs : HasCompactSupport χ) (hχ0 : ∀ w, 0 ≤ χ w)
    {r c₀ : ℝ} (hr : 0 < r) (hc₀ : 0 < c₀) (hχc₀ : ∀ w ∈ Metric.ball p r, c₀ ≤ χ w)
    {c ν : ℝ} (hc : 0 < c) (hν : 0 < ν)
    (hcoer : ∀ w ∈ tsupport χ, c * ‖transverse w - transverse p‖ ^ ν ≤ K₁ (transverse w))
    {C : ℝ → ℝ}
    (hfam : ∀ (k : ℕ) (m : Fin k → ι₁ ⊕ ι₂),
      SuperPoly (projDiff L₁ L₂ C fun w ↦ χ w * coordMonomial p m w)) :
    ∀ᶠ w in 𝓝 p, L₁ w = L₂ w := by
  have ha : ContDiff ℝ ∞ (marginal χ) := contDiff_marginal hχ hχs
  have has : HasCompactSupport (marginal χ) := hasCompactSupport_marginal hχs
  have ha0 : ∀ x, 0 ≤ marginal χ x := marginal_nonneg hχ0
  have hvol : 0 < (volume (Metric.ball (tangential p) r)).toReal :=
    ENNReal.toReal_pos (Metric.measure_ball_pos volume _ hr).ne' measure_ball_lt_top.ne
  have haball := marginal_ge hχ.continuous hχs hχ0 hr hχc₀
  have hcoer' : ∀ x ∈ tsupport (marginal χ), c * ‖x - transverse p‖ ^ ν ≤ K₁ x := by
    intro x hx
    obtain ⟨w, hw, rfl⟩ := tsupport_marginal_subset hχs hx
    exact hcoer w hw
  -- the transverse data
  have hfam₁ : ∀ (k : ℕ) (m : Fin k → ι₁),
      SuperPoly (projDiff K₁ K₂ C fun x ↦ marginal χ x * coordMonomial (transverse p) m x) := by
    intro k m
    have h := hfam k (Sum.inl ∘ m)
    have hfactor : ∀ (K : (ι₁ → ℝ) → ℝ), Continuous K → ∀ (t : ℝ),
        (∫ w : ι₁ ⊕ ι₂ → ℝ, (χ w * coordMonomial p (Sum.inl ∘ m) w) *
          Real.exp (-(t * K (transverse w)))) =
        ∫ x : ι₁ → ℝ, (marginal χ x * coordMonomial (transverse p) m x) *
          Real.exp (-(t * K x)) := by
      intro K hKc t
      calc ∫ w : ι₁ ⊕ ι₂ → ℝ, (χ w * coordMonomial p (Sum.inl ∘ m) w) *
              Real.exp (-(t * K (transverse w)))
          = ∫ w : ι₁ ⊕ ι₂ → ℝ, χ w * (coordMonomial (transverse p) m (transverse w) *
              Real.exp (-(t * K (transverse w)))) := by
            refine integral_congr_ae (Filter.Eventually.of_forall fun w ↦ ?_)
            beta_reduce
            rw [coordMonomial_inl]
            ring
        _ = ∫ x : ι₁ → ℝ, marginal χ x * (coordMonomial (transverse p) m x *
              Real.exp (-(t * K x))) :=
            integral_mul_transverse_eq_marginal hχ.continuous hχs
              (F := fun x ↦ coordMonomial (transverse p) m x * Real.exp (-(t * K x)))
              ((coordMonomial_continuous _ m).mul (by fun_prop))
        _ = ∫ x : ι₁ → ℝ, (marginal χ x * coordMonomial (transverse p) m x) *
              Real.exp (-(t * K x)) := by
            refine integral_congr_ae (Filter.Eventually.of_forall fun x ↦ ?_)
            beta_reduce
            ring
    refine h.congr (Filter.Eventually.of_forall fun t ↦ ?_)
    unfold projDiff
    simp only [hL₁, hL₂]
    rw [hfactor K₂ h2.continuous t, hfactor K₁ h1.continuous t]
  have hK := normalized_families_force_germ_eq_at_of_weight_monomials (C := C) h1 h2 hK1 hK2 hA1
    hA2 hp1 hp2 ha has ha0 hr (by positivity) haball hc hν hcoer' hfam₁
  obtain ⟨δ, hδ, hK'⟩ := Metric.eventually_nhds_iff.mp hK
  rw [Metric.eventually_nhds_iff]
  refine ⟨δ, hδ, fun w hw ↦ ?_⟩
  rw [hL₁, hL₂, hK' ?_]
  rw [dist_eq_norm] at hw ⊢
  exact lt_of_le_of_lt (norm_transverse_sub_le w p) hw

end Laplace.Multi
