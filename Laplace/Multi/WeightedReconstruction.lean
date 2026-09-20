/-
Copyright (c) 2026 Timaeus Research. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniel Murfet
-/
import Mathlib
import Laplace.Multi.WeightedPolynomialComparison

/-!
# Constructive grade-by-grade reconstruction

The uniqueness proof of the weighted-jet induction becomes a reconstruction formula. On the
monomials of a fixed weighted grade the covariance form under the reference density `e^{-P}`
has a Gram matrix `gram P Sk`, which is invertible: a vector in its kernel gives a monomial
combination with vanishing covariances against every grade monomial, hence (Stage C and
coefficient uniqueness) the zero vector (`gram_mulVec_injective`, `isUnit_gram`). The
one-grade engine identifies the leading rate coefficients of the masked normalized moments
with `−(gram *ᵥ d)` for the grade coefficient difference `d`, so
`d = gram⁻¹ *ᵥ (−v)` where `v` is the vector of measured leading coefficients
(`grade_coefficients_eq_gram_inv_mulVec`): after the lower grades have been recovered, the
grade-`k` coefficients are read off by one linear solve.
-/

open Real MeasureTheory Filter Topology Matrix

namespace Laplace.Multi

variable {ι : Type*} [Fintype ι]

/-- The covariance under a reference density is symmetric. -/
theorem covarianceUnder_comm {X : Type*} [MeasurableSpace X] (μ : Measure X) (P A Q : X → ℝ) :
    covarianceUnder μ P A Q = covarianceUnder μ P Q A := by
  unfold covarianceUnder
  rw [mul_comm (expectationUnder μ P A)]
  congr 1
  unfold expectationUnder
  congr 1
  exact integral_congr_ae (Filter.Eventually.of_forall fun x ↦ by ring)

namespace IntWeights

variable (W : IntWeights ι)

/-- Extension of a vector indexed by a finset by zero. -/
noncomputable def extZero (S : Finset (ι → ℕ)) (c : S → ℝ) : (ι → ℕ) → ℝ :=
  fun β ↦ if h : β ∈ S then c ⟨β, h⟩ else 0

theorem extZero_apply_mem (S : Finset (ι → ℕ)) (c : S → ℝ) (β : S) :
    extZero S c β = c β := by
  unfold extZero
  rw [dif_pos β.2]

/-- The Gram matrix of the covariance form on the monomials of a finite exponent set. -/
noncomputable def gram (P : (ι → ℝ) → ℝ) (S : Finset (ι → ℕ)) : Matrix S S ℝ :=
  fun α β ↦ covarianceUnder volume P (mvMonomial α) (mvMonomial β)

/-- The monomial combination with coefficients `c` on `S`. -/
noncomputable def combo (S : Finset (ι → ℕ)) (c : S → ℝ) (u : ι → ℝ) : ℝ :=
  ∑ β ∈ S, extZero S c β * mvMonomial β u

/-- **The Gram matrix acts by covariance against the combination.** -/
theorem gram_mulVec {P : (ι → ℝ) → ℝ} (S : Finset (ι → ℕ))
    (hint_m : ∀ α ∈ S, Integrable (fun w : ι → ℝ ↦ mvMonomial α w * Real.exp (-P w)))
    (hint_pair : ∀ α ∈ S, ∀ β ∈ S, Integrable (fun w : ι → ℝ ↦
      mvMonomial β w * mvMonomial α w * Real.exp (-P w)))
    (c : S → ℝ) (α : S) :
    (gram P S *ᵥ c) α = covarianceUnder volume P (mvMonomial α) (combo S c) := by
  unfold combo
  rw [covarianceUnder_comm, covarianceUnder_combo_left P (mvMonomial α) S (extZero S c)
    (fun β hβ ↦ hint_pair α α.2 β hβ) hint_m]
  rw [← Finset.sum_coe_sort]
  unfold gram Matrix.mulVec dotProduct
  refine Finset.sum_congr rfl fun β _ ↦ ?_
  rw [extZero_apply_mem, covarianceUnder_comm]
  ring

/-- **Injectivity of the Gram matrix**: a kernel vector gives a monomial combination with
vanishing covariances against every monomial of the set, hence vanishes. -/
theorem gram_mulVec_eq_zero {P : (ι → ℝ) → ℝ} (S : Finset (ι → ℕ)) (hS0 : ∀ α ∈ S, α ≠ 0)
    (he : Integrable (fun w : ι → ℝ ↦ Real.exp (-P w)))
    (hint_m : ∀ α ∈ S, Integrable (fun w : ι → ℝ ↦ mvMonomial α w * Real.exp (-P w)))
    (hint_pair : ∀ α ∈ S, ∀ β ∈ S, Integrable (fun w : ι → ℝ ↦
      mvMonomial β w * mvMonomial α w * Real.exp (-P w)))
    (hZpos : 0 < ∫ w : ι → ℝ, Real.exp (-P w))
    (c : S → ℝ) (hc : gram P S *ᵥ c = 0) : c = 0 := by
  have hcov : ∀ α ∈ S, covarianceUnder volume P (mvMonomial α) (combo S c) = 0 := by
    intro α hα
    have := congrFun hc ⟨α, hα⟩
    rwa [gram_mulVec S hint_m hint_pair, Pi.zero_apply] at this
  have hint_pair' : ∀ α ∈ S, Integrable (fun w : ι → ℝ ↦
      mvMonomial α w * (∑ β ∈ S, extZero S c β * mvMonomial β w) * Real.exp (-P w)) := by
    intro α hα
    have h1 : Integrable (fun w : ι → ℝ ↦ ∑ β ∈ S, extZero S c β *
        (mvMonomial β w * mvMonomial α w * Real.exp (-P w))) :=
      integrable_finsetSum _ fun β hβ ↦ (hint_pair α hα β hβ).const_mul _
    refine h1.congr (Filter.Eventually.of_forall fun w ↦ ?_)
    simp only []
    rw [Finset.mul_sum, Finset.sum_mul]
    refine Finset.sum_congr rfl fun β _ ↦ ?_
    ring
  have hfun := monomialCombo_eq_zero_of_covariance_monomials_zero P S (extZero S c) hS0 he hint_m
    hint_pair' hZpos hcov
  have hcoef := coefficients_zero_of_monomialCombo_eq_zero S (extZero S c) hfun
  funext β
  have := hcoef β β.2
  rwa [extZero_apply_mem] at this

theorem gram_mulVec_injective {P : (ι → ℝ) → ℝ} (S : Finset (ι → ℕ)) (hS0 : ∀ α ∈ S, α ≠ 0)
    (he : Integrable (fun w : ι → ℝ ↦ Real.exp (-P w)))
    (hint_m : ∀ α ∈ S, Integrable (fun w : ι → ℝ ↦ mvMonomial α w * Real.exp (-P w)))
    (hint_pair : ∀ α ∈ S, ∀ β ∈ S, Integrable (fun w : ι → ℝ ↦
      mvMonomial β w * mvMonomial α w * Real.exp (-P w)))
    (hZpos : 0 < ∫ w : ι → ℝ, Real.exp (-P w)) :
    Function.Injective (gram P S).mulVec := by
  intro c c' h
  have : gram P S *ᵥ (c - c') = 0 := by
    rw [Matrix.mulVec_sub, h, sub_self]
  exact sub_eq_zero.mp (gram_mulVec_eq_zero S hS0 he hint_m hint_pair hZpos _ this)

/-- **The Gram matrix is invertible.** -/
theorem isUnit_gram_det {P : (ι → ℝ) → ℝ} (S : Finset (ι → ℕ)) (hS0 : ∀ α ∈ S, α ≠ 0)
    (he : Integrable (fun w : ι → ℝ ↦ Real.exp (-P w)))
    (hint_m : ∀ α ∈ S, Integrable (fun w : ι → ℝ ↦ mvMonomial α w * Real.exp (-P w)))
    (hint_pair : ∀ α ∈ S, ∀ β ∈ S, Integrable (fun w : ι → ℝ ↦
      mvMonomial β w * mvMonomial α w * Real.exp (-P w)))
    (hZpos : 0 < ∫ w : ι → ℝ, Real.exp (-P w)) :
    IsUnit (gram P S).det :=
  (Matrix.isUnit_iff_isUnit_det _).mp
    (Matrix.mulVec_injective_iff_isUnit.mp (gram_mulVec_injective S hS0 he hint_m hint_pair hZpos))

/-- **Reconstruction from the Gram action.** -/
theorem eq_gram_inv_mulVec {P : (ι → ℝ) → ℝ} (S : Finset (ι → ℕ)) (hdet : IsUnit (gram P S).det)
    (c : S → ℝ) : c = (gram P S)⁻¹ *ᵥ (gram P S *ᵥ c) := by
  rw [Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul _ hdet, Matrix.one_mulVec]

/-! ### The reconstruction formula at a grade -/

/-- **Grade-by-grade reconstruction** (polynomial setting): once the coefficients below
weighted degree `k` agree, the grade-`k` coefficient difference is the Gram inverse applied to
the negatives of the measured leading rate coefficients of the masked normalized moments. -/
theorem grade_coefficients_eq_gram_inv_mulVec {P : (ι → ℝ) → ℝ}
    (hPm : Measurable P) (hP0 : ∀ u, 0 ≤ P u)
    (hint : ∀ c : ℝ, 0 < c → Integrable fun u : ι → ℝ ↦ Real.exp (-(c * P u)))
    {κ : ℝ} (hκ : 0 ≤ κ) (hcoer : ∀ u i, |u i| ^ W.D ≤ κ * P u ^ W.a i)
    {U : Set (ι → ℝ)} (hU : MeasurableSet U) (hU0 : U ∈ 𝓝 (0 : ι → ℝ))
    (S : Finset (ι → ℕ)) (c₁ c₂ : (ι → ℕ) → ℝ) (hS : ∀ α ∈ S, W.D < W.wdeg α)
    {c₀ : ℝ} (hc₀ : 0 < c₀)
    (hlow₁ : ∀ᶠ ε in 𝓝[>] (0 : ℝ), ∀ u ∈ W.mask U ε, c₀ * P u ≤ P u + W.corr S c₁ ε u)
    (hlow₂ : ∀ᶠ ε in 𝓝[>] (0 : ℝ), ∀ u ∈ W.mask U ε, c₀ * P u ≤ P u + W.corr S c₂ ε u)
    {k : ℕ} (hk : W.D < k) (hlower : ∀ α ∈ S, W.wdeg α < k → c₁ α = c₂ α)
    (Sk : Finset (ι → ℕ)) (hSk : Sk = S.filter (fun α ↦ W.wdeg α = k))
    (v : Sk → ℝ)
    (hdata : ∀ α : Sk, Tendsto (fun ε : ℝ ↦
      (W.maskedMoment U P S c₂ (mvMonomial α) ε - W.maskedMoment U P S c₁ (mvMonomial α) ε) /
        ε ^ (k - W.D)) (𝓝[>] (0 : ℝ)) (𝓝 (v α))) :
    (fun α : Sk ↦ c₂ α - c₁ α) = (gram P Sk)⁻¹ *ᵥ (fun α ↦ -v α) := by
  set d : Sk → ℝ := fun α ↦ c₂ α - c₁ α with hd_def
  set Q : (ι → ℝ) → ℝ := fun u ↦ ∑ β ∈ Sk, (c₂ β - c₁ β) * mvMonomial β u with hQ_def
  have hQ_eq : W.gradePart S (fun α ↦ c₂ α - c₁ α) k = Q := by
    unfold gradePart
    rw [← hSk]
  have hQ_combo : combo Sk d = Q := by
    funext u
    unfold combo
    refine Finset.sum_congr rfl fun β hβ ↦ ?_
    have := extZero_apply_mem Sk d ⟨β, hβ⟩
    simp only [hd_def] at this
    rw [this]
  have he1 : Integrable fun u : ι → ℝ ↦ Real.exp (-P u) := by
    have := hint 1 one_pos
    simpa using this
  have hZpos : 0 < ∫ u : ι → ℝ, Real.exp (-P u) := integral_exp_neg_pos he1
  have hS0 : ∀ α ∈ Sk, α ≠ 0 := by
    intro α hα
    rw [hSk] at hα
    have hαk : W.wdeg α = k := (Finset.mem_filter.mp hα).2
    intro h0
    rw [h0] at hαk
    have : W.wdeg (0 : ι → ℕ) = 0 := by
      unfold wdeg
      simp
    omega
  have hint_m : ∀ α ∈ Sk, Integrable (fun w : ι → ℝ ↦ mvMonomial α w * Real.exp (-P w)) := by
    intro α _
    have := integrable_mul_exp_neg_of_polyBoundedBy hPm hP0 hint
      (W.polyBoundedBy_mvMonomial hκ hP0 hcoer α) (mvMonomial_measurable α).aestronglyMeasurable
      one_pos
    simpa using this
  have hint_pair : ∀ α ∈ Sk, ∀ β ∈ Sk, Integrable (fun w : ι → ℝ ↦
      mvMonomial β w * mvMonomial α w * Real.exp (-P w)) := by
    intro α _ β _
    have := integrable_mul_exp_neg_of_polyBoundedBy hPm hP0 hint
      ((W.polyBoundedBy_mvMonomial hκ hP0 hcoer β).mul hP0
        (W.polyBoundedBy_mvMonomial hκ hP0 hcoer α))
      ((mvMonomial_measurable β).mul (mvMonomial_measurable α)).aestronglyMeasurable one_pos
    simpa using this
  -- the covariance limit at each grade-`k` monomial identifies `-v`
  have hcov : ∀ α : Sk, covarianceUnder volume P (mvMonomial α) Q = -v α := by
    intro α
    have hAm : Measurable (mvMonomial (α : ι → ℕ)) := mvMonomial_measurable (α : ι → ℕ)
    have hApb : PolyBoundedBy P (mvMonomial (α : ι → ℕ)) :=
      W.polyBoundedBy_mvMonomial hκ hP0 hcoer α
    have hBpb : PolyBoundedBy P (corrBound S c₁ c₂) :=
      W.polyBoundedBy_corrBound hκ hP0 hcoer S c₁ c₂
    have hBm : Measurable (corrBound S c₁ c₂) := measurable_corrBound S c₁ c₂
    have hbound : ∀ᶠ ε in 𝓝[>] (0 : ℝ), ∀ u ∈ W.mask U ε,
        |W.corr S c₂ ε u - W.corr S c₁ ε u| / ε ^ (k - W.D) ≤ corrBound S c₁ c₂ u := by
      filter_upwards [Ioc_mem_nhdsGT (zero_lt_one' ℝ)] with ε hε u _
      exact W.abs_corr_sub_div_pow_le S c₁ c₂ hk hlower hε.1 hε.2 u
    have hlim := tendsto_masked_normalized_difference_div_pow (μ := volume)
      (E := W.mask U) (P := P) (V₁ := W.corr S c₁) (V₂ := W.corr S c₂) (A := mvMonomial α)
      (Q := Q) (B := corrBound S c₁ c₂) (c := c₀) (ρ := k - W.D)
      (W.measurableSet_mask hU) (W.eventually_mem_mask hU0) hPm (W.measurable_corr S c₁)
      (W.measurable_corr S c₂) hAm (W.tendsto_corr S c₁ hS) (W.tendsto_corr S c₂ hS)
      (fun u ↦ by rw [← hQ_eq]; exact W.tendsto_corr_sub_div_pow S c₁ c₂ hk hlower u)
      hlow₁ hlow₂ (corrBound_nonneg S c₁ c₂) hbound
      (integrable_mul_exp_neg_of_polyBoundedBy hPm hP0 hint hApb.abs
        hAm.abs.aestronglyMeasurable hc₀)
      (integrable_mul_exp_neg_of_polyBoundedBy hPm hP0 hint (hApb.abs.mul hP0 hBpb)
        (hAm.abs.mul hBm).aestronglyMeasurable hc₀)
      (hint c₀ hc₀)
      (integrable_mul_exp_neg_of_polyBoundedBy hPm hP0 hint hBpb hBm.aestronglyMeasurable hc₀)
      hZpos
    have huniq : -covarianceUnder volume P (mvMonomial (α : ι → ℕ)) Q = v α :=
      tendsto_nhds_unique hlim (hdata α)
    linarith
  have hdet := isUnit_gram_det (P := P) Sk hS0 he1 hint_m hint_pair hZpos
  have hmul : gram P Sk *ᵥ d = fun α ↦ -v α := by
    funext α
    rw [gram_mulVec Sk hint_m hint_pair, hQ_combo, hcov]
  calc d = (gram P Sk)⁻¹ *ᵥ (gram P Sk *ᵥ d) := eq_gram_inv_mulVec Sk hdet d
    _ = (gram P Sk)⁻¹ *ᵥ (fun α ↦ -v α) := by rw [hmul]

end IntWeights

end Laplace.Multi
