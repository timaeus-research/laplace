/-
Copyright (c) 2026 Timaeus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Timaeus
-/
import Mathlib
import Laplace.Multi.RescaledData
import Laplace.Multi.GaussianMomentsPosDef

/-!
# The residual on the divisor determines the profile: several fibre variables

Item C of the relative push-forward programme (germbij_slop S14). Fibre variables `x ∈ ℝ^ι`, an
anisotropic rescaling `x_i = t^{-α_i} u_i` (`aniScale`), a monomial fibre density
`∏ |x_i|^{h_i}` (`monoDensity`), and the chart-level hypotheses of `DivisorData` in this setting
(`MultiDivisorData`). The substitution lemma (`rpow_mul_integral_aniScale_eq`) is a diagonal change
of variables with Jacobian `t^{-∑ α_i}`; everything else is the dominated rescaling lemma on
`(ℝ^ι, volume)` (`MultiDivisorData.toRescaledData`), so the energy statistic and every rescaled
bounded observable converge to their Boltzmann values under `∏|u_i|^{h_i} e^{-Φ₀}`
(`MultiDivisorData.tendsto_energy`, `MultiDivisorData.tendsto_rescaled_expectation`).
-/

open Real MeasureTheory Filter Topology Matrix

namespace Laplace.Multi

variable {ι : Type*} [Fintype ι]

/-- Anisotropic rescaling `x_i = t^{-α_i} u_i`. -/
noncomputable def aniScale (α : ι → ℝ) (t : ℝ) (u : ι → ℝ) : ι → ℝ := fun i ↦ t ^ (-α i) * u i

/-- The monomial fibre density `∏ |x_i|^{h_i}`. -/
noncomputable def monoDensity (h : ι → ℕ) (x : ι → ℝ) : ℝ := ∏ i, |x i| ^ (h i)

theorem monoDensity_nonneg (h : ι → ℕ) (x : ι → ℝ) : 0 ≤ monoDensity h x :=
  Finset.prod_nonneg fun _ _ ↦ pow_nonneg (abs_nonneg _) _

theorem continuous_monoDensity (h : ι → ℕ) : Continuous (monoDensity h) :=
  continuous_finsetProd _ fun i _ ↦ (continuous_apply i).abs.pow _

omit [Fintype ι] in
theorem continuous_aniScale (α : ι → ℝ) (t : ℝ) : Continuous (aniScale α t) :=
  continuous_pi fun i ↦ continuous_const.mul (continuous_apply i)

theorem aniScale_eq_mulVec [DecidableEq ι] (α : ι → ℝ) (t : ℝ) (u : ι → ℝ) :
    aniScale α t u = Matrix.diagonal (fun i ↦ t ^ (-α i)) *ᵥ u := by
  funext i
  simp [aniScale, Matrix.mulVec_diagonal]

omit [Fintype ι] in
theorem aniScale_neg_aniScale (α : ι → ℝ) {t : ℝ} (ht : 0 < t) (u : ι → ℝ) :
    aniScale (fun i ↦ -α i) t (aniScale α t u) = u := by
  funext i
  simp only [aniScale, neg_neg]
  rw [← mul_assoc, ← Real.rpow_add ht, add_neg_cancel, Real.rpow_zero, one_mul]

omit [Fintype ι] in
theorem tendsto_aniScale (α : ι → ℝ) (hα : ∀ i, 0 < α i) (u : ι → ℝ) :
    Tendsto (fun t ↦ aniScale α t u) atTop (𝓝 0) := by
  refine tendsto_pi_nhds.mpr fun i ↦ ?_
  have := (tendsto_rpow_neg_atTop (hα i)).mul_const (u i)
  rw [zero_mul] at this
  exact this

theorem monoDensity_aniScale (h : ι → ℕ) (α : ι → ℝ) {t : ℝ} (ht : 0 < t) (u : ι → ℝ) :
    monoDensity h (aniScale α t u) = t ^ (-(∑ i, α i * h i)) * monoDensity h u := by
  unfold monoDensity aniScale
  have e : ∀ i, |t ^ (-α i) * u i| ^ (h i) = t ^ (-(α i * h i)) * |u i| ^ (h i) := by
    intro i
    rw [abs_mul, abs_of_pos (Real.rpow_pos_of_pos ht _), mul_pow, ← Real.rpow_natCast,
      ← Real.rpow_mul ht.le, neg_mul]
  simp only [e]
  rw [Finset.prod_mul_distrib, ← Real.rpow_sum_of_pos ht, Finset.sum_neg_distrib]

/-- The diagonal change of variables `x = aniScale α t u`: Jacobian `t^{-∑ α_i}`. -/
theorem integral_aniScale (α : ι → ℝ) {t : ℝ} (ht : 0 < t) (f : (ι → ℝ) → ℝ)
    (hf : AEStronglyMeasurable f volume) :
    ∫ x, f x = t ^ (-(∑ i, α i)) * ∫ u, f (aniScale α t u) := by
  classical
  have hdet : (Matrix.diagonal fun i ↦ t ^ (-α i)).det = t ^ (-(∑ i, α i)) := by
    rw [Matrix.det_diagonal, ← Real.rpow_sum_of_pos ht, Finset.sum_neg_distrib]
  have hdet0 : (Matrix.diagonal fun i ↦ t ^ (-α i)).det ≠ 0 := by
    rw [hdet]; exact (Real.rpow_pos_of_pos ht _).ne'
  rw [integral_comp_mulVec _ hdet0 f hf, hdet, abs_of_pos (Real.rpow_pos_of_pos ht _)]
  congr 1
  refine integral_congr_ae (Filter.Eventually.of_forall fun u ↦ ?_)
  simp only
  rw [aniScale_eq_mulVec]

/-- The fibre substitution with the monomial density and a test function read at the rescaled
position `t^{α} x`. -/
theorem rpow_mul_integral_aniScale_eq {F : (ι → ℝ) → ℝ → ℝ} (α : ι → ℝ) (χ g : (ι → ℝ) → ℝ)
    (h : ι → ℕ) {t : ℝ} (ht : 0 < t) (s : ℝ) (Ψ : ℝ → ℝ)
    (hmeas : AEStronglyMeasurable
      (fun x ↦ χ x * (monoDensity h x * (g (aniScale (fun i ↦ -α i) t x) * Ψ (t * F x s)))) volume) :
    t ^ (∑ i, α i * (h i + 1)) *
      ∫ x, χ x * (monoDensity h x * (g (aniScale (fun i ↦ -α i) t x) * Ψ (t * F x s))) =
      ∫ u, χ (aniScale α t u) * (monoDensity h u * (g u * Ψ (t * F (aniScale α t u) s))) := by
  rw [integral_aniScale α ht _ hmeas]
  have hpt : ∀ u, χ (aniScale α t u) * (monoDensity h (aniScale α t u) *
      (g (aniScale (fun i ↦ -α i) t (aniScale α t u)) * Ψ (t * F (aniScale α t u) s))) =
      t ^ (-(∑ i, α i * h i)) *
        (χ (aniScale α t u) * (monoDensity h u * (g u * Ψ (t * F (aniScale α t u) s)))) := by
    intro u
    rw [aniScale_neg_aniScale α ht, monoDensity_aniScale h α ht]
    ring
  simp only [hpt]
  rw [integral_const_mul, ← mul_assoc, ← mul_assoc, ← Real.rpow_add ht, ← Real.rpow_add ht]
  have : ∑ i, α i * (h i + 1) + -(∑ i, α i) + -(∑ i, α i * h i) = 0 := by
    rw [← Finset.sum_neg_distrib, ← Finset.sum_neg_distrib, ← Finset.sum_add_distrib,
      ← Finset.sum_add_distrib]
    exact Finset.sum_eq_zero fun i _ ↦ by ring
  rw [this, Real.rpow_zero, one_mul]

/-- Chart-level hypotheses in several fibre variables. -/
structure MultiDivisorData (F : (ι → ℝ) → ℝ → ℝ) (Φ₀ : (ι → ℝ) → ℝ) (α : ι → ℝ) (γ σ c : ℝ)
    (h : ι → ℕ) : Prop where
  hα : ∀ i, 0 < α i
  hc : 0 < c
  hc1 : c ≤ 1
  F_cont : Continuous (Function.uncurry F)
  F_nonneg : ∀ x s, 0 ≤ F x s
  Φ₀_nonneg : ∀ u, 0 ≤ Φ₀ u
  lim : ∀ u, Tendsto (fun t ↦ t * F (aniScale α t u) (σ * t ^ (-γ))) atTop (𝓝 (Φ₀ u))
  lower : ∀ᶠ t in atTop, ∀ u, c * Φ₀ u ≤ t * F (aniScale α t u) (σ * t ^ (-γ))
  int : Integrable fun u ↦ monoDensity h u * Real.exp (-(c * Φ₀ u))
  Φint : Integrable fun u ↦ monoDensity h u * (Φ₀ u * Real.exp (-(c * Φ₀ u)))

namespace MultiDivisorData

variable {F : (ι → ℝ) → ℝ → ℝ} {Φ₀ : (ι → ℝ) → ℝ} {α : ι → ℝ} {γ σ c : ℝ} {h : ι → ℕ}
  (hd : MultiDivisorData F Φ₀ α γ σ c h)
include hd

theorem continuous_rescaled (t : ℝ) :
    Continuous fun u : ι → ℝ ↦ t * F (aniScale α t u) (σ * t ^ (-γ)) :=
  continuous_const.mul (hd.F_cont.comp ((continuous_aniScale α t).prodMk continuous_const))

/-- The dominated rescaling lemma on `(ℝ^ι, volume)`. -/
theorem toRescaledData {χ : (ι → ℝ) → ℝ} (hχ : Continuous χ) {M : ℝ} (hM : ∀ x, |χ x| ≤ M) :
    RescaledData volume (fun t u ↦ t * F (aniScale α t u) (σ * t ^ (-γ)))
      (fun t u ↦ χ (aniScale α t u) * monoDensity h u) Φ₀ (fun u ↦ χ 0 * monoDensity h u)
      (fun u ↦ M * monoDensity h u) c where
  hc := hd.hc
  hc1 := hd.hc1
  G_meas := fun t ↦ (hd.continuous_rescaled t).measurable
  w_meas := fun t ↦ ((hχ.comp (continuous_aniScale α t)).mul (continuous_monoDensity h)).measurable
  G_nonneg := by
    filter_upwards [eventually_gt_atTop 0] with t ht u _
    exact mul_nonneg ht.le (hd.F_nonneg _ _)
  Φ₀_nonneg := hd.Φ₀_nonneg
  G_lim := hd.lim
  w_lim := fun u ↦ ((hχ.tendsto 0).comp (tendsto_aniScale α hd.hα u)).mul_const _
  w_bd := fun t u ↦ by
    rw [abs_mul, abs_of_nonneg (monoDensity_nonneg h u)]
    exact mul_le_mul_of_nonneg_right (hM _) (monoDensity_nonneg h u)
  lower := by
    filter_upwards [hd.lower] with t hl u _
    exact hl u
  int := by simpa [mul_assoc] using hd.int.const_mul M
  Φint := by simpa [mul_assoc] using hd.Φint.const_mul M

/-- The positive orthant has positive measure, so the limiting partition function is positive. -/
theorem integral_limit_den_pos {χ : (ι → ℝ) → ℝ} (hχ0 : 0 < χ 0) :
    0 < ∫ u, χ 0 * monoDensity h u * Real.exp (-Φ₀ u) := by
  have hmeasΦ : Measurable Φ₀ :=
    measurable_of_tendsto_metrizable' atTop (fun t ↦ (hd.continuous_rescaled t).measurable)
      (tendsto_pi_nhds.mpr hd.lim)
  have hint : Integrable fun u ↦ χ 0 * monoDensity h u * Real.exp (-Φ₀ u) := by
    refine (hd.int.const_mul (χ 0)).mono' ?_ (Filter.Eventually.of_forall fun u ↦ ?_)
    · have := continuous_monoDensity h
      exact Measurable.aestronglyMeasurable (by fun_prop)
    · rw [Real.norm_eq_abs, abs_of_nonneg (by
        have := monoDensity_nonneg h u
        positivity), mul_assoc]
      refine mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr ?_)
        (monoDensity_nonneg h u)) hχ0.le
      have := hd.Φ₀_nonneg u
      nlinarith [hd.hc1]
  refine (integral_pos_iff_support_of_nonneg (fun u ↦ by
    have := monoDensity_nonneg h u
    positivity) hint).mpr ?_
  have hsub : Set.pi Set.univ (fun _ : ι ↦ Set.Ioi (0 : ℝ)) ⊆
      Function.support fun u ↦ χ 0 * monoDensity h u * Real.exp (-Φ₀ u) := by
    intro u hu
    simp only [Function.mem_support]
    have hpos : 0 < monoDensity h u :=
      Finset.prod_pos fun i _ ↦ pow_pos (abs_pos.mpr (ne_of_gt (hu i (Set.mem_univ i)))) _
    positivity
  refine lt_of_lt_of_le ?_ (measure_mono hsub)
  rw [volume_pi, Measure.pi_pi]
  exact CanonicallyOrderedAdd.prod_pos.mpr fun i _ ↦ by rw [Real.volume_Ioi]; exact ENNReal.coe_lt_top

/-- The energy statistic with the monomial fibre density. -/
noncomputable def energy (χ : (ι → ℝ) → ℝ) (F : (ι → ℝ) → ℝ → ℝ) (h : ι → ℕ) (s t : ℝ) : ℝ :=
  t * ((∫ x, χ x * (monoDensity h x * (F x s * Real.exp (-(t * F x s))))) /
    ∫ x, χ x * (monoDensity h x * Real.exp (-(t * F x s))))

theorem hmeas_aux {χ g : (ι → ℝ) → ℝ} (hχ : Continuous χ) (hg : Continuous g) (t s : ℝ)
    {Ψ : ℝ → ℝ} (hΨ : Continuous Ψ) :
    AEStronglyMeasurable
      (fun x ↦ χ x * (monoDensity h x * (g (aniScale (fun i ↦ -α i) t x) * Ψ (t * F x s)))) volume := by
  have h1 := continuous_monoDensity h
  have h2 := continuous_aniScale (fun i ↦ -α i) t
  have h3 := hd.F_cont
  exact Measurable.aestronglyMeasurable (by fun_prop)

/-- **The profile in several fibre variables.** -/
theorem tendsto_energy {χ : (ι → ℝ) → ℝ} (hχ : Continuous χ) {M : ℝ} (hM : ∀ x, |χ x| ≤ M)
    (hχ0 : 0 < χ 0) :
    Tendsto (fun t ↦ energy χ F h (σ * t ^ (-γ)) t) atTop
      (𝓝 ((∫ u, monoDensity h u * (Φ₀ u * Real.exp (-Φ₀ u))) /
        ∫ u, monoDensity h u * Real.exp (-Φ₀ u))) := by
  have hr := hd.toRescaledData hχ hM
  have hpos := hd.integral_limit_den_pos (χ := χ) hχ0
  have hpos' : ∫ u, χ 0 * monoDensity h u * Real.exp (-Φ₀ u) ≠ 0 := hpos.ne'
  have hT := hr.tendsto_energy hpos'
  have hlim : (∫ u, χ 0 * monoDensity h u * (Φ₀ u * Real.exp (-Φ₀ u))) /
      ∫ u, χ 0 * monoDensity h u * Real.exp (-Φ₀ u) =
      (∫ u, monoDensity h u * (Φ₀ u * Real.exp (-Φ₀ u))) /
        ∫ u, monoDensity h u * Real.exp (-Φ₀ u) := by
    simp only [mul_assoc, integral_const_mul]
    rw [mul_div_mul_left _ _ hχ0.ne']
  rw [hlim] at hT
  refine hT.congr' ?_
  filter_upwards [eventually_gt_atTop 0] with t ht
  set s := σ * t ^ (-γ) with hs
  have hp : (t ^ (∑ i, α i * (h i + 1)) : ℝ) ≠ 0 := (Real.rpow_pos_of_pos ht _).ne'
  have hN := rpow_mul_integral_aniScale_eq (F := F) α χ (fun _ ↦ (1 : ℝ)) h ht s
    (fun y ↦ y * Real.exp (-y))
    (hd.hmeas_aux hχ continuous_const t s (Ψ := fun y ↦ y * Real.exp (-y)) (by fun_prop))
  have hD := rpow_mul_integral_aniScale_eq (F := F) α χ (fun _ ↦ (1 : ℝ)) h ht s
    (fun y ↦ Real.exp (-y))
    (hd.hmeas_aux hχ continuous_const t s (Ψ := fun y ↦ Real.exp (-y)) (by fun_prop))
  simp only [one_mul] at hN hD
  have hN' : (∫ u, χ (aniScale α t u) * monoDensity h u *
      (t * F (aniScale α t u) s * Real.exp (-(t * F (aniScale α t u) s)))) =
      t ^ (∑ i, α i * (h i + 1)) *
        ∫ x, χ x * (monoDensity h x * (t * F x s * Real.exp (-(t * F x s)))) := by
    rw [hN]
    exact integral_congr_ae (Filter.Eventually.of_forall fun u ↦ by ring)
  have hD' : (∫ u, χ (aniScale α t u) * monoDensity h u * Real.exp (-(t * F (aniScale α t u) s))) =
      t ^ (∑ i, α i * (h i + 1)) * ∫ x, χ x * (monoDensity h x * Real.exp (-(t * F x s))) := by
    rw [hD]
    exact integral_congr_ae (Filter.Eventually.of_forall fun u ↦ by ring)
  simp only [energy]
  rw [hN', hD', mul_div_mul_left _ _ hp, mul_div_assoc', ← integral_const_mul]
  congr 1
  exact integral_congr_ae (Filter.Eventually.of_forall fun x ↦ by ring)

/-- **Rescaled observables in several fibre variables.** -/
theorem tendsto_rescaled_expectation {χ : (ι → ℝ) → ℝ} (hχ : Continuous χ) {M : ℝ}
    (hM : ∀ x, |χ x| ≤ M) (hχ0 : 0 < χ 0) {g : (ι → ℝ) → ℝ} (hg : Continuous g) {Mg : ℝ}
    (hMg : ∀ u, |g u| ≤ Mg) (hMg0 : 0 ≤ Mg) :
    Tendsto (fun t ↦ (∫ x, χ x * (monoDensity h x * (g (aniScale (fun i ↦ -α i) t x) *
        Real.exp (-(t * F x (σ * t ^ (-γ))))))) /
      ∫ x, χ x * (monoDensity h x * Real.exp (-(t * F x (σ * t ^ (-γ)))))) atTop
      (𝓝 ((∫ u, monoDensity h u * (g u * Real.exp (-Φ₀ u))) /
        ∫ u, monoDensity h u * Real.exp (-Φ₀ u))) := by
  have hr := hd.toRescaledData hχ hM
  have hpos := hd.integral_limit_den_pos (χ := χ) hχ0
  have hpos' : ∫ u, χ 0 * monoDensity h u * Real.exp (-Φ₀ u) ≠ 0 := hpos.ne'
  have hT := hr.tendsto_expectation hpos' hg.measurable hMg hMg0
  have hlim : (∫ u, χ 0 * monoDensity h u * (g u * Real.exp (-Φ₀ u))) /
      ∫ u, χ 0 * monoDensity h u * Real.exp (-Φ₀ u) =
      (∫ u, monoDensity h u * (g u * Real.exp (-Φ₀ u))) /
        ∫ u, monoDensity h u * Real.exp (-Φ₀ u) := by
    simp only [mul_assoc, integral_const_mul]
    rw [mul_div_mul_left _ _ hχ0.ne']
  rw [hlim] at hT
  refine hT.congr' ?_
  filter_upwards [eventually_gt_atTop 0] with t ht
  set s := σ * t ^ (-γ) with hs
  have hp : (t ^ (∑ i, α i * (h i + 1)) : ℝ) ≠ 0 := (Real.rpow_pos_of_pos ht _).ne'
  have hN := rpow_mul_integral_aniScale_eq (F := F) α χ g h ht s (fun y ↦ Real.exp (-y))
    (hd.hmeas_aux hχ hg t s (Ψ := fun y ↦ Real.exp (-y)) (by fun_prop))
  have hD := rpow_mul_integral_aniScale_eq (F := F) α χ (fun _ ↦ (1 : ℝ)) h ht s
    (fun y ↦ Real.exp (-y))
    (hd.hmeas_aux hχ continuous_const t s (Ψ := fun y ↦ Real.exp (-y)) (by fun_prop))
  simp only [one_mul] at hN hD
  have hN' : (∫ u, χ (aniScale α t u) * monoDensity h u *
      (g u * Real.exp (-(t * F (aniScale α t u) s)))) =
      t ^ (∑ i, α i * (h i + 1)) * ∫ x, χ x * (monoDensity h x *
        (g (aniScale (fun i ↦ -α i) t x) * Real.exp (-(t * F x s)))) := by
    rw [hN]
    exact integral_congr_ae (Filter.Eventually.of_forall fun u ↦ by ring)
  have hD' : (∫ u, χ (aniScale α t u) * monoDensity h u * Real.exp (-(t * F (aniScale α t u) s))) =
      t ^ (∑ i, α i * (h i + 1)) * ∫ x, χ x * (monoDensity h x * Real.exp (-(t * F x s))) := by
    rw [hD]
    exact integral_congr_ae (Filter.Eventually.of_forall fun u ↦ by ring)
  rw [hN', hD', mul_div_mul_left _ _ hp]

end MultiDivisorData

end Laplace.Multi
