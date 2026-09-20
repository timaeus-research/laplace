/-
Copyright (c) 2026 Timaeus Research. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniel Murfet
-/
import Mathlib
import Laplace.Multi.WeightedDegree
import Laplace.Multi.KernelComparison

/-!
# Weighted-jet induction for semi-quasi-homogeneous polynomial losses (germbij §7.4(b))

Two losses `L_j = P + ∑_{α ∈ S} c_j α x^α` sharing the leading part `P` (quasi-homogeneous
of weighted degree `D` for integerized weights `W`) and with every correction of weighted
degree `> D`. Under the weighted dilation `x = dil ε u` at temperature `t = ε^{-D}`,

  `t · L_j (dil ε u) = P u + corr S c_j ε u`,   `corr S c ε u = ∑_α c α ε^{wdeg α − D} u^α`.

If the coefficients agree below weighted degree `k`, the divided difference
`(corr c₂ − corr c₁)/ε^{k−D}` converges pointwise to the grade-`k` component of `c₂ − c₁`
and is uniformly bounded by a `P`-polynomial for `ε ≤ 1`; the masked one-grade engine then
identifies the covariance `Cov_P(u^α, Q_k)` from the rescaled data, Stage C
(`monomialCombo_eq_zero_of_covariance_monomials_zero`) kills the grade-`k` component as a
function, and coefficient uniqueness through `MvPolynomial` kills the coefficients.
Strong induction on the integer weighted degree closes the polynomial case.
-/

open Real MeasureTheory Filter Topology

namespace Laplace.Multi

variable {ι : Type*}

/-! ### Coefficient uniqueness through `MvPolynomial` -/

/-- **Coefficient uniqueness**: a finite monomial combination vanishing as a function on
`ι → ℝ` has all coefficients zero. -/
theorem coefficients_zero_of_monomialCombo_eq_zero [Fintype ι]
    (S : Finset (ι → ℕ)) (c : (ι → ℕ) → ℝ)
    (hzero : ∀ u : ι → ℝ, ∑ α ∈ S, c α * mvMonomial α u = 0) :
    ∀ α ∈ S, c α = 0 := by
  classical
  set p : MvPolynomial ι ℝ :=
    ∑ α ∈ S, MvPolynomial.monomial (Finsupp.equivFunOnFinite.symm α) (c α) with hp_def
  have heval : ∀ u : ι → ℝ, MvPolynomial.eval u p = ∑ α ∈ S, c α * mvMonomial α u := by
    intro u
    rw [hp_def, map_sum]
    refine Finset.sum_congr rfl fun α _ ↦ ?_
    rw [MvPolynomial.eval_monomial, Finsupp.prod_pow]
    rfl
  have hp0 : p = 0 := by
    refine MvPolynomial.funext fun u ↦ ?_
    rw [heval u, hzero u, map_zero]
  intro α hα
  have hcoeff : MvPolynomial.coeff (Finsupp.equivFunOnFinite.symm α) p = c α := by
    rw [hp_def, MvPolynomial.coeff_sum]
    rw [Finset.sum_eq_single α]
    · rw [MvPolynomial.coeff_monomial, if_pos rfl]
    · intro β _ hβ
      rw [MvPolynomial.coeff_monomial, if_neg]
      intro h
      exact hβ (Finsupp.equivFunOnFinite.symm.injective h)
    · intro h
      exact absurd hα h
  rw [hp0, MvPolynomial.coeff_zero] at hcoeff
  exact hcoeff.symm

namespace IntWeights

variable [Fintype ι] (W : IntWeights ι)

/-! ### Weighted polynomials and their rescaled corrections -/

/-- The weighted polynomial `∑_{α ∈ S} c α x^α`. -/
noncomputable def wpoly (S : Finset (ι → ℕ)) (c : (ι → ℕ) → ℝ) (x : ι → ℝ) : ℝ :=
  ∑ α ∈ S, c α * mvMonomial α x

/-- The rescaled correction at temperature `ε^{-D}`: `∑_α c α ε^{wdeg α − D} u^α`. -/
noncomputable def corr (S : Finset (ι → ℕ)) (c : (ι → ℕ) → ℝ) (ε : ℝ) (u : ι → ℝ) : ℝ :=
  ∑ α ∈ S, c α * ε ^ (W.wdeg α - W.D) * mvMonomial α u

/-- The grade-`k` component of a weighted polynomial. -/
noncomputable def gradePart (S : Finset (ι → ℕ)) (c : (ι → ℕ) → ℝ) (k : ℕ) (u : ι → ℝ) : ℝ :=
  ∑ α ∈ S.filter (fun α ↦ W.wdeg α = k), c α * mvMonomial α u

/-- **The rescaling identity**: `wpoly (dil ε u) = ε^D · corr ε u` when every exponent has
weighted degree `> D`. -/
theorem wpoly_dil (S : Finset (ι → ℕ)) (c : (ι → ℕ) → ℝ) (hS : ∀ α ∈ S, W.D < W.wdeg α)
    (ε : ℝ) (u : ι → ℝ) : wpoly S c (W.dil ε u) = ε ^ W.D * W.corr S c ε u := by
  unfold wpoly corr
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun α hα ↦ ?_
  have hpow : ε ^ W.wdeg α = ε ^ (W.wdeg α - W.D) * ε ^ W.D := by
    rw [← pow_add, Nat.sub_add_cancel (hS α hα).le]
  rw [W.mvMonomial_dil, hpow]
  ring

theorem measurable_corr (S : Finset (ι → ℕ)) (c : (ι → ℕ) → ℝ) (ε : ℝ) :
    Measurable (W.corr S c ε) :=
  Finset.measurable_sum _ fun α _ ↦ (mvMonomial_measurable α).const_mul _

theorem continuous_corr_in_scale (S : Finset (ι → ℕ)) (c : (ι → ℕ) → ℝ) (u : ι → ℝ) :
    Continuous fun ε : ℝ ↦ W.corr S c ε u := by
  unfold corr
  fun_prop

/-- The corrections vanish pointwise as `ε → 0⁺`. -/
theorem tendsto_corr (S : Finset (ι → ℕ)) (c : (ι → ℕ) → ℝ) (hS : ∀ α ∈ S, W.D < W.wdeg α)
    (u : ι → ℝ) : Tendsto (fun ε : ℝ ↦ W.corr S c ε u) (𝓝[>] (0 : ℝ)) (𝓝 0) := by
  have h0 : W.corr S c 0 u = 0 := by
    unfold corr
    refine Finset.sum_eq_zero fun α hα ↦ ?_
    rw [zero_pow (by have := hS α hα; omega), mul_zero, zero_mul]
  have := ((W.continuous_corr_in_scale S c u).tendsto 0).mono_left
    (nhdsWithin_le_nhds (s := Set.Ioi 0))
  rwa [h0] at this

/-- The divided correction difference, as a polynomial in `ε`. -/
noncomputable def divCorr (S : Finset (ι → ℕ)) (c₁ c₂ : (ι → ℕ) → ℝ) (k : ℕ) (ε : ℝ)
    (u : ι → ℝ) : ℝ :=
  ∑ α ∈ S, (c₂ α - c₁ α) * ε ^ (W.wdeg α - k) * mvMonomial α u

/-- For `ε > 0`, once the coefficients below grade `k` agree, the divided difference of the
corrections is the polynomial `divCorr`. -/
theorem corr_sub_div_pow_eq (S : Finset (ι → ℕ)) (c₁ c₂ : (ι → ℕ) → ℝ) {k : ℕ} (hk : W.D < k)
    (hlower : ∀ α ∈ S, W.wdeg α < k → c₁ α = c₂ α) {ε : ℝ} (hε : 0 < ε) (u : ι → ℝ) :
    (W.corr S c₂ ε u - W.corr S c₁ ε u) / ε ^ (k - W.D) = W.divCorr S c₁ c₂ k ε u := by
  unfold corr divCorr
  rw [← Finset.sum_sub_distrib, Finset.sum_div]
  refine Finset.sum_congr rfl fun α hα ↦ ?_
  rcases lt_or_ge (W.wdeg α) k with hlt | hge
  · rw [hlower α hα hlt]
    simp
  · have hpow : ε ^ (W.wdeg α - W.D) = ε ^ (W.wdeg α - k) * ε ^ (k - W.D) := by
      rw [← pow_add]
      congr 1
      omega
    rw [hpow]
    field_simp

theorem divCorr_zero (S : Finset (ι → ℕ)) (c₁ c₂ : (ι → ℕ) → ℝ) {k : ℕ}
    (hlower : ∀ α ∈ S, W.wdeg α < k → c₁ α = c₂ α) (u : ι → ℝ) :
    W.divCorr S c₁ c₂ k 0 u = W.gradePart S (fun α ↦ c₂ α - c₁ α) k u := by
  unfold divCorr gradePart
  rw [Finset.sum_filter]
  refine Finset.sum_congr rfl fun α hα ↦ ?_
  split_ifs with h
  · rw [h, Nat.sub_self, pow_zero, mul_one]
  · rcases lt_or_gt_of_ne h with hlt | hgt
    · rw [hlower α hα hlt, sub_self, zero_mul, zero_mul]
    · rw [zero_pow (by omega), mul_zero, zero_mul]

/-- **Pointwise leading-grade limit** of the divided correction difference. -/
theorem tendsto_corr_sub_div_pow (S : Finset (ι → ℕ)) (c₁ c₂ : (ι → ℕ) → ℝ) {k : ℕ}
    (hk : W.D < k) (hlower : ∀ α ∈ S, W.wdeg α < k → c₁ α = c₂ α) (u : ι → ℝ) :
    Tendsto (fun ε : ℝ ↦ (W.corr S c₂ ε u - W.corr S c₁ ε u) / ε ^ (k - W.D))
      (𝓝[>] (0 : ℝ)) (𝓝 (W.gradePart S (fun α ↦ c₂ α - c₁ α) k u)) := by
  have hcont : Continuous fun ε : ℝ ↦ W.divCorr S c₁ c₂ k ε u := by
    unfold divCorr
    fun_prop
  have := ((hcont.tendsto 0).mono_left (nhdsWithin_le_nhds (s := Set.Ioi 0)))
  rw [W.divCorr_zero S c₁ c₂ hlower u] at this
  refine this.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with ε hε
  exact (W.corr_sub_div_pow_eq S c₁ c₂ hk hlower hε u).symm

/-- The uniform polynomial majorant of the divided difference for `0 < ε ≤ 1`. -/
noncomputable def corrBound (S : Finset (ι → ℕ)) (c₁ c₂ : (ι → ℕ) → ℝ) (u : ι → ℝ) : ℝ :=
  ∑ α ∈ S, |c₂ α - c₁ α| * |mvMonomial α u|

theorem corrBound_nonneg (S : Finset (ι → ℕ)) (c₁ c₂ : (ι → ℕ) → ℝ) (u : ι → ℝ) :
    0 ≤ corrBound S c₁ c₂ u :=
  Finset.sum_nonneg fun _ _ ↦ mul_nonneg (abs_nonneg _) (abs_nonneg _)

theorem abs_corr_sub_div_pow_le (S : Finset (ι → ℕ)) (c₁ c₂ : (ι → ℕ) → ℝ) {k : ℕ}
    (hk : W.D < k) (hlower : ∀ α ∈ S, W.wdeg α < k → c₁ α = c₂ α) {ε : ℝ} (hε : 0 < ε)
    (hε1 : ε ≤ 1) (u : ι → ℝ) :
    |W.corr S c₂ ε u - W.corr S c₁ ε u| / ε ^ (k - W.D) ≤ corrBound S c₁ c₂ u := by
  rw [← abs_of_pos (pow_pos hε (k - W.D)), ← abs_div,
    W.corr_sub_div_pow_eq S c₁ c₂ hk hlower hε u]
  unfold divCorr corrBound
  refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun α _ ↦ ?_)
  rw [abs_mul, abs_mul, abs_of_pos (pow_pos hε _)]
  have : ε ^ (W.wdeg α - k) ≤ 1 := pow_le_one₀ hε.le hε1
  calc |c₂ α - c₁ α| * ε ^ (W.wdeg α - k) * |mvMonomial α u|
      ≤ |c₂ α - c₁ α| * 1 * |mvMonomial α u| := by gcongr
    _ = _ := by ring

theorem measurable_corrBound (S : Finset (ι → ℕ)) (c₁ c₂ : (ι → ℕ) → ℝ) :
    Measurable (corrBound S c₁ c₂) :=
  Finset.measurable_sum _ fun α _ ↦ (mvMonomial_measurable α).abs.const_mul _

theorem polyBoundedBy_corrBound {P : (ι → ℝ) → ℝ} {κ : ℝ} (hκ : 0 ≤ κ) (hP0 : ∀ u, 0 ≤ P u)
    (hcoer : ∀ u i, |u i| ^ W.D ≤ κ * P u ^ W.a i) (S : Finset (ι → ℕ))
    (c₁ c₂ : (ι → ℕ) → ℝ) : PolyBoundedBy P (corrBound S c₁ c₂) :=
  PolyBoundedBy.finset_sum hP0 S fun α _ ↦
    ((W.polyBoundedBy_mvMonomial hκ hP0 hcoer α).abs).const_mul _

/-! ### The localization mask -/

/-- The rescaled mask `{u | dil ε u ∈ U}`. -/
def mask (U : Set (ι → ℝ)) (ε : ℝ) : Set (ι → ℝ) := {u | W.dil ε u ∈ U}

omit [Fintype ι] in
theorem measurableSet_mask {U : Set (ι → ℝ)} (hU : MeasurableSet U) (ε : ℝ) :
    MeasurableSet (W.mask U ε) :=
  (W.measurable_dil ε) hU

omit [Fintype ι] in
theorem tendsto_dil_zero (u : ι → ℝ) :
    Tendsto (fun ε : ℝ ↦ W.dil ε u) (𝓝[>] (0 : ℝ)) (𝓝 0) := by
  have hcont : Continuous fun ε : ℝ ↦ W.dil ε u := by
    unfold dil
    fun_prop
  have := (hcont.tendsto 0).mono_left (nhdsWithin_le_nhds (s := Set.Ioi 0))
  convert this using 2
  funext i
  simp [dil, zero_pow (W.a_pos i).ne']

omit [Fintype ι] in
theorem eventually_mem_mask {U : Set (ι → ℝ)} (hU : U ∈ 𝓝 (0 : ι → ℝ)) (u : ι → ℝ) :
    ∀ᶠ ε in 𝓝[>] (0 : ℝ), u ∈ W.mask U ε :=
  (W.tendsto_dil_zero u).eventually hU

/-- The masked normalized rescaled moment of the weighted polynomial loss. -/
noncomputable def maskedMoment (U : Set (ι → ℝ)) (P : (ι → ℝ) → ℝ) (S : Finset (ι → ℕ))
    (c : (ι → ℕ) → ℝ) (A : (ι → ℝ) → ℝ) (ε : ℝ) : ℝ :=
  (∫ u, A u * maskedKernel (W.mask U) P (W.corr S c) ε u) /
    ∫ u, maskedKernel (W.mask U) P (W.corr S c) ε u

/-! ### The grade step -/

theorem integral_exp_neg_pos {P : (ι → ℝ) → ℝ}
    (hint : Integrable fun u : ι → ℝ ↦ Real.exp (-P u)) :
    0 < ∫ u : ι → ℝ, Real.exp (-P u) := by
  rw [integral_pos_iff_support_of_nonneg (fun u ↦ (Real.exp_pos _).le) hint]
  have hsupp : Function.support (fun u : ι → ℝ ↦ Real.exp (-P u)) = Set.univ :=
    Set.eq_univ_of_forall fun u ↦ (Real.exp_pos _).ne'
  rw [hsupp]
  exact isOpen_univ.measure_pos _ Set.univ_nonempty

/-- **The grade step**: if the coefficients agree below weighted degree `k` and the
masked normalized moments of the grade-`k` monomials agree to `o(ε^{k−D})`, the grade-`k`
coefficients agree. -/
theorem coefficients_eq_at_grade_of_lower_eq {P : (ι → ℝ) → ℝ}
    (hPm : Measurable P) (hP0 : ∀ u, 0 ≤ P u)
    (hint : ∀ c : ℝ, 0 < c → Integrable fun u : ι → ℝ ↦ Real.exp (-(c * P u)))
    {κ : ℝ} (hκ : 0 ≤ κ) (hcoer : ∀ u i, |u i| ^ W.D ≤ κ * P u ^ W.a i)
    {U : Set (ι → ℝ)} (hU : MeasurableSet U) (hU0 : U ∈ 𝓝 (0 : ι → ℝ))
    (S : Finset (ι → ℕ)) (c₁ c₂ : (ι → ℕ) → ℝ) (hS : ∀ α ∈ S, W.D < W.wdeg α)
    {c₀ : ℝ} (hc₀ : 0 < c₀)
    (hlow₁ : ∀ᶠ ε in 𝓝[>] (0 : ℝ), ∀ u ∈ W.mask U ε, c₀ * P u ≤ P u + W.corr S c₁ ε u)
    (hlow₂ : ∀ᶠ ε in 𝓝[>] (0 : ℝ), ∀ u ∈ W.mask U ε, c₀ * P u ≤ P u + W.corr S c₂ ε u)
    {k : ℕ} (hk : W.D < k) (hlower : ∀ α ∈ S, W.wdeg α < k → c₁ α = c₂ α)
    (hdata : ∀ α ∈ S, W.wdeg α = k → Tendsto (fun ε : ℝ ↦
      (W.maskedMoment U P S c₂ (mvMonomial α) ε - W.maskedMoment U P S c₁ (mvMonomial α) ε) /
        ε ^ (k - W.D)) (𝓝[>] (0 : ℝ)) (𝓝 0)) :
    ∀ α ∈ S, W.wdeg α = k → c₁ α = c₂ α := by
  set Sk := S.filter (fun α ↦ W.wdeg α = k) with hSk_def
  set Q : (ι → ℝ) → ℝ := fun u ↦ ∑ β ∈ Sk, (c₂ β - c₁ β) * mvMonomial β u with hQ_def
  have hQ_eq : W.gradePart S (fun α ↦ c₂ α - c₁ α) k = Q := rfl
  have he1 : Integrable fun u : ι → ℝ ↦ Real.exp (-P u) := by
    have := hint 1 one_pos
    simpa using this
  have hZpos : 0 < ∫ u : ι → ℝ, Real.exp (-P u) := integral_exp_neg_pos he1
  -- the covariance limit at each grade-`k` monomial
  have hcov : ∀ α ∈ Sk, covarianceUnder volume P (mvMonomial α) Q = 0 := by
    intro α hα
    have hαS : α ∈ S := (Finset.mem_filter.mp hα).1
    have hαk : W.wdeg α = k := (Finset.mem_filter.mp hα).2
    have hAm : Measurable (mvMonomial α) := mvMonomial_measurable α
    have hApb : PolyBoundedBy P (mvMonomial α) := W.polyBoundedBy_mvMonomial hκ hP0 hcoer α
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
    have hzero := hdata α hαS hαk
    have huniq := tendsto_nhds_unique hlim hzero
    exact neg_eq_zero.mp huniq
  -- Stage C: the grade component vanishes as a function
  have hfun : ∀ u, ∑ β ∈ Sk, (c₂ β - c₁ β) * mvMonomial β u = 0 := by
    refine monomialCombo_eq_zero_of_covariance_monomials_zero P Sk (fun β ↦ c₂ β - c₁ β)
      ?_ he1 ?_ ?_ hZpos hcov
    · intro α hα
      have hαk : W.wdeg α = k := (Finset.mem_filter.mp hα).2
      intro h0
      rw [h0] at hαk
      have : W.wdeg (0 : ι → ℕ) = 0 := by
        unfold wdeg
        simp
      omega
    · intro α _
      have := integrable_mul_exp_neg_of_polyBoundedBy hPm hP0 hint
        (W.polyBoundedBy_mvMonomial hκ hP0 hcoer α) (mvMonomial_measurable α).aestronglyMeasurable
        one_pos
      simpa using this
    · intro α _
      have hQpb : PolyBoundedBy P Q :=
        PolyBoundedBy.finset_sum hP0 Sk fun β _ ↦
          (W.polyBoundedBy_mvMonomial hκ hP0 hcoer β).const_mul _
      have hQm : Measurable Q :=
        Finset.measurable_sum _ fun β _ ↦ (mvMonomial_measurable β).const_mul _
      have := integrable_mul_exp_neg_of_polyBoundedBy hPm hP0 hint
        ((W.polyBoundedBy_mvMonomial hκ hP0 hcoer α).mul hP0 hQpb)
        ((mvMonomial_measurable α).mul hQm).aestronglyMeasurable one_pos
      simpa using this
  -- coefficient uniqueness
  have hcoef := coefficients_zero_of_monomialCombo_eq_zero Sk (fun β ↦ c₂ β - c₁ β) hfun
  intro α hα hαk
  have := hcoef α (Finset.mem_filter.mpr ⟨hα, hαk⟩)
  linarith

/-- **Weighted-jet induction for polynomial losses**: with the leading part and weights
shared, matching masked normalized moments at every grade force equal coefficients. -/
theorem weightedPolynomial_coefficients_eq_of_rates {P : (ι → ℝ) → ℝ}
    (hPm : Measurable P) (hP0 : ∀ u, 0 ≤ P u)
    (hint : ∀ c : ℝ, 0 < c → Integrable fun u : ι → ℝ ↦ Real.exp (-(c * P u)))
    {κ : ℝ} (hκ : 0 ≤ κ) (hcoer : ∀ u i, |u i| ^ W.D ≤ κ * P u ^ W.a i)
    {U : Set (ι → ℝ)} (hU : MeasurableSet U) (hU0 : U ∈ 𝓝 (0 : ι → ℝ))
    (S : Finset (ι → ℕ)) (c₁ c₂ : (ι → ℕ) → ℝ) (hS : ∀ α ∈ S, W.D < W.wdeg α)
    {c₀ : ℝ} (hc₀ : 0 < c₀)
    (hlow₁ : ∀ᶠ ε in 𝓝[>] (0 : ℝ), ∀ u ∈ W.mask U ε, c₀ * P u ≤ P u + W.corr S c₁ ε u)
    (hlow₂ : ∀ᶠ ε in 𝓝[>] (0 : ℝ), ∀ u ∈ W.mask U ε, c₀ * P u ≤ P u + W.corr S c₂ ε u)
    (hdata : ∀ k, W.D < k → ∀ α ∈ S, W.wdeg α = k → Tendsto (fun ε : ℝ ↦
      (W.maskedMoment U P S c₂ (mvMonomial α) ε - W.maskedMoment U P S c₁ (mvMonomial α) ε) /
        ε ^ (k - W.D)) (𝓝[>] (0 : ℝ)) (𝓝 0)) :
    ∀ α ∈ S, c₁ α = c₂ α := by
  have hgrade : ∀ k, ∀ α ∈ S, W.wdeg α = k → c₁ α = c₂ α := by
    intro k
    induction k using Nat.strong_induction_on with
    | _ k ih =>
      intro α hα hdeg
      have hk : W.D < k := hdeg ▸ hS α hα
      exact W.coefficients_eq_at_grade_of_lower_eq hPm hP0 hint hκ hcoer hU hU0 S c₁ c₂ hS hc₀
        hlow₁ hlow₂ hk (fun β hβ hβk ↦ ih (W.wdeg β) hβk β hβ rfl) (hdata k hk) α hα hdeg
  exact fun α hα ↦ hgrade (W.wdeg α) α hα rfl

end IntWeights

end Laplace.Multi
