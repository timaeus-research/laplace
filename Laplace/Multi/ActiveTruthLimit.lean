/-
Copyright (c) 2026 Timaeus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Timaeus
-/
import Laplace.Multi.ActiveTruthFibre
import Laplace.Multi.TwoScaledInner

/-!
# The transverse limit of an active-truth face

Step 5 of the transverse active-truth face theorem (`notes/active_truth_handoff.md`): dominated
convergence in the transverse variables `v = (s, h)`. The weight `vWeight` factors as
`e^{-mL}` times the `L`-free weight `e^{-βs} e^{-c₀ e^{-s}} · 1_{h > h₀} e^{-ηh}`
(`vWeight_eq_mul`, `vWeight_zero_eq`), whose integral is `Γ(β) c₀^{-β} · e^{-ηh₀}/η`
(`lintegral_vWeight_zero`). The fibre volume divided by `L^k` is bounded, for `L ≥ 1`, by
`(|s| + δ)^k / ∏ κ'_i` (`volume_fibreSet_div_le`), and the polynomial factor is integrable against
the `s`-weight (`integrable_sWeight_mul_pow`, via `(|s| + δ)^k ≤ C e^{β|s|/2}`), so
`∫ vWeight · volume(fibreSet)/L^k` converges to `∫ vWeight · vol(F')`
(`tendsto_lintegral_vWeight_fibre`).
-/

open Real MeasureTheory Set Filter Topology
open scoped ENNReal Matrix

namespace Laplace.Multi

variable {k : ℕ}

/-! ### The transverse weight -/

/-- The `s`-weight `e^{-βs} e^{-c₀ e^{-s}}`. -/
noncomputable def sWeight (β c₀ s : ℝ) : ℝ := exp (-(β * s)) * exp (-(c₀ * exp (-s)))

/-- The `h`-weight `1_{h > h₀} e^{-ηh}`. -/
noncomputable def hWeight (η h₀ : ℝ) : ℝ → ℝ := (Ioi h₀).indicator fun h ↦ exp (-(η * h))

theorem sWeight_nonneg (β c₀ s : ℝ) : 0 ≤ sWeight β c₀ s :=
  mul_nonneg (exp_pos _).le (exp_pos _).le

theorem hWeight_nonneg (η h₀ h : ℝ) : 0 ≤ hWeight η h₀ h :=
  Set.indicator_nonneg (fun _ _ ↦ (exp_pos _).le) h

theorem continuous_sWeight (β c₀ : ℝ) : Continuous (sWeight β c₀) := by
  unfold sWeight; fun_prop

theorem vWeight_zero_eq (β η c₀ h₀ : ℝ) (v : Fin 2 → ℝ) :
    vWeight β η 0 c₀ h₀ v = ENNReal.ofReal (sWeight β c₀ (v 0) * hWeight η h₀ (v 1)) := by
  unfold vWeight sWeight hWeight
  by_cases h : v 1 ∈ Ioi h₀
  · rw [Set.indicator_of_mem h, Set.indicator_of_mem h, one_mul]
    congr 1
    rw [add_zero, mul_right_comm, ← Real.exp_add, ← Real.exp_add, ← Real.exp_add]
    congr 1
    ring
  · rw [Set.indicator_of_notMem h, Set.indicator_of_notMem h, zero_mul, mul_zero,
      ENNReal.ofReal_zero]

theorem vWeight_eq_mul (β η mL c₀ h₀ : ℝ) (v : Fin 2 → ℝ) :
    vWeight β η mL c₀ h₀ v = ENNReal.ofReal (exp (-mL)) * vWeight β η 0 c₀ h₀ v := by
  unfold vWeight
  have e : exp (-(β * v 0 + η * v 1 + mL)) * exp (-(c₀ * exp (-v 0))) =
      exp (-mL) * (exp (-(β * v 0 + η * v 1 + 0)) * exp (-(c₀ * exp (-v 0)))) := by
    rw [← Real.exp_add, ← Real.exp_add, ← Real.exp_add]
    congr 1
    ring
  rw [e, ENNReal.ofReal_mul (exp_pos _).le, mul_left_comm]

theorem integral_sWeight {β c₀ : ℝ} (hβ : 0 < β) (hc : 0 < c₀) :
    ∫ s, sWeight β c₀ s = Gamma β * c₀ ^ (-β) := by
  rw [← integral_exp_mul_exp_neg_exp hβ hc, ← integral_neg_eq_self]
  refine integral_congr_ae (Eventually.of_forall fun s ↦ ?_)
  simp only [sWeight, mul_neg, neg_neg]

theorem integrable_sWeight {β c₀ : ℝ} (hβ : 0 < β) (hc : 0 < c₀) :
    Integrable (sWeight β c₀) := by
  have := (integrable_exp_mul_exp_neg_exp hβ hc).comp_neg
  refine this.congr (Eventually.of_forall fun s ↦ ?_)
  simp only [sWeight, mul_neg]

theorem integral_hWeight {η : ℝ} (hη : 0 < η) (h₀ : ℝ) :
    ∫ h, hWeight η h₀ h = exp (-(η * h₀)) / η := by
  rw [hWeight, integral_indicator measurableSet_Ioi, integral_exp_neg_mul_Ioi_shift hη]

theorem integrable_hWeight {η : ℝ} (hη : 0 < η) (h₀ : ℝ) : Integrable (hWeight η h₀) :=
  (integrableOn_exp_neg_mul_Ioi' hη h₀).integrable_indicator measurableSet_Ioi

/-- `∫ vWeight(0) = Γ(β) c₀^{-β} · e^{-ηh₀}/η`. -/
theorem lintegral_vWeight_zero {β η c₀ : ℝ} (hβ : 0 < β) (hη : 0 < η) (hc : 0 < c₀) (h₀ : ℝ) :
    ∫⁻ v : Fin 2 → ℝ, vWeight β η 0 c₀ h₀ v =
      ENNReal.ofReal (Gamma β * c₀ ^ (-β) * (exp (-(η * h₀)) / η)) := by
  simp_rw [vWeight_zero_eq]
  rw [← ofReal_integral_eq_lintegral_ofReal
    (integrable_fin_two_mul (integrable_sWeight hβ hc) (integrable_hWeight hη h₀))
    (Eventually.of_forall fun v ↦ mul_nonneg (sWeight_nonneg _ _ _) (hWeight_nonneg _ _ _)),
    integral_fin_two_mul, integral_sWeight hβ hc, integral_hWeight hη]

/-! ### The polynomial envelope -/

/-- `(|s| + δ)^k ≤ (k/a + δ)^k e^{a|s|}`. -/
theorem pow_abs_add_le_exp {a δ : ℝ} (ha : 0 < a) (hδ : 0 ≤ δ) (k : ℕ) (s : ℝ) :
    (|s| + δ) ^ k ≤ (k / a + δ) ^ k * exp (a * |s|) := by
  rcases Nat.eq_zero_or_pos k with rfl | hk
  · simp only [pow_zero, one_mul]
    exact Real.one_le_exp (mul_nonneg ha.le (abs_nonneg s))
  have hk' : (0 : ℝ) < k := Nat.cast_pos.mpr hk
  have h1 : |s| + δ ≤ (k / a + δ) * exp (a * |s| / k) := by
    have hx := Real.add_one_le_exp (a * |s| / k)
    have h2 : 1 ≤ exp (a * |s| / k) := Real.one_le_exp (by positivity)
    have h3 : |s| ≤ k / a * exp (a * |s| / k) := by
      calc |s| = k / a * (a * |s| / k) := by field_simp
        _ ≤ k / a * exp (a * |s| / k) := mul_le_mul_of_nonneg_left (by linarith) (by positivity)
    rw [add_mul]
    exact add_le_add h3 (le_mul_of_one_le_right hδ h2)
  calc (|s| + δ) ^ k ≤ ((k / a + δ) * exp (a * |s| / k)) ^ k :=
        pow_le_pow_left₀ (by positivity) h1 k
    _ = (k / a + δ) ^ k * exp (a * |s|) := by
        rw [mul_pow, ← Real.exp_nat_mul]
        congr 2
        field_simp

theorem exp_abs_le_add (a s : ℝ) : exp (a * |s|) ≤ exp (a * s) + exp (-(a * s)) := by
  rcases le_or_gt 0 s with hs | hs
  · rw [abs_of_nonneg hs]
    linarith [exp_pos (-(a * s))]
  · rw [abs_of_neg hs, mul_neg]
    linarith [exp_pos (a * s)]

theorem integrable_sWeight_mul_pow {β c₀ δ : ℝ} (hβ : 0 < β) (hc : 0 < c₀) (hδ : 0 ≤ δ)
    (k : ℕ) : Integrable fun s ↦ sWeight β c₀ s * (|s| + δ) ^ k := by
  set C : ℝ := (k / (β / 2) + δ) ^ k with hC
  have hC0 : 0 ≤ C := by positivity
  have hi1 := (integrable_sWeight (half_pos hβ) hc).const_mul C
  have hi2 := (integrable_sWeight (by linarith : 0 < 3 * β / 2) hc).const_mul C
  refine (hi1.add hi2).mono' ?_ (Eventually.of_forall fun s ↦ ?_)
  · exact ((continuous_sWeight β c₀).mul (by fun_prop)).aestronglyMeasurable
  · simp only [Pi.add_apply]
    rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (sWeight_nonneg _ _ _) (by positivity))]
    have h1 := pow_abs_add_le_exp (half_pos hβ) hδ k s
    have h2 := exp_abs_le_add (β / 2) s
    have e1 : sWeight (β / 2) c₀ s = sWeight β c₀ s * exp (β / 2 * s) := by
      simp only [sWeight]
      rw [mul_right_comm, ← Real.exp_add (-(β * s))]
      congr 2
      ring
    have e2 : sWeight (3 * β / 2) c₀ s = sWeight β c₀ s * exp (-(β / 2 * s)) := by
      simp only [sWeight]
      rw [mul_right_comm, ← Real.exp_add (-(β * s))]
      congr 2
      ring
    rw [e1, e2]
    rw [← hC] at h1
    have hw := sWeight_nonneg β c₀ s
    calc sWeight β c₀ s * (|s| + δ) ^ k
        ≤ sWeight β c₀ s * (C * exp (β / 2 * |s|)) := mul_le_mul_of_nonneg_left h1 hw
      _ ≤ sWeight β c₀ s * (C * (exp (β / 2 * s) + exp (-(β / 2 * s)))) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left h2 hC0) hw
      _ = C * (sWeight β c₀ s * exp (β / 2 * s)) +
          C * (sWeight β c₀ s * exp (-(β / 2 * s))) := by ring

/-! ### The dominated bound on the fibre volume -/

/-- For `L ≥ 1`, `volume (fibreSet v) / L^k ≤ (|s| + δ)^k / ∏ κ'_i`. -/
theorem volume_fibreSet_div_le {κ Q : Fin k ⊕ Fin 2 → ℝ} (hΔ : (transMat κ Q).det ≠ 0)
    (hκ : ∀ i, 0 < κ i) {δ : ℝ} (hδ : 0 ≤ δ) (γ : ℝ) {L : ℝ} (hL : 1 ≤ L) (v : Fin 2 → ℝ) :
    volume (fibreSet κ Q δ γ L v) / ENNReal.ofReal (L ^ k) ≤
      ENNReal.ofReal ((|v 0| + δ) ^ k / ∏ i, κ (Sum.inl i)) := by
  have hL0 : 0 < L := zero_lt_one.trans_le hL
  have hP : 0 < ∏ i, κ (Sum.inl i) := Finset.prod_pos fun i _ ↦ hκ _
  rw [ENNReal.div_le_iff (ENNReal.ofReal_pos.mpr (pow_pos hL0 _)).ne' ENNReal.ofReal_ne_top]
  refine (volume_fibreSet_le hΔ hκ δ γ L v).trans ?_
  have hprod : ∀ i : Fin k, 0 ≤ L * ((|v 0| + δ) / κ (Sum.inl i)) := fun i ↦ by
    have := hκ (Sum.inl i)
    positivity
  calc ∏ i, ENNReal.ofReal ((v 0 + δ * L) / κ (Sum.inl i))
      ≤ ∏ i, ENNReal.ofReal (L * ((|v 0| + δ) / κ (Sum.inl i))) := by
        refine Finset.prod_le_prod' fun i _ ↦ ENNReal.ofReal_le_ofReal ?_
        rw [mul_div_assoc', div_le_div_iff_of_pos_right (hκ _)]
        have h1 : v 0 ≤ |v 0| * L := by
          calc v 0 ≤ |v 0| := le_abs_self _
            _ = |v 0| * 1 := (mul_one _).symm
            _ ≤ |v 0| * L := mul_le_mul_of_nonneg_left hL (abs_nonneg _)
        linarith
    _ = ENNReal.ofReal (∏ i, L * ((|v 0| + δ) / κ (Sum.inl i))) :=
        (ENNReal.ofReal_prod_of_nonneg fun i _ ↦ hprod i).symm
    _ = ENNReal.ofReal ((|v 0| + δ) ^ k / ∏ i, κ (Sum.inl i)) * ENNReal.ofReal (L ^ k) := by
        rw [← ENNReal.ofReal_mul (div_nonneg (by positivity) hP.le)]
        congr 1
        rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ, Fintype.card_fin,
          Finset.prod_div_distrib, Finset.prod_const, Finset.card_univ, Fintype.card_fin]
        ring

theorem measurable_volume_fibreSet {κ Q : Fin k ⊕ Fin 2 → ℝ} (hΔ : (transMat κ Q).det ≠ 0)
    (δ γ L : ℝ) : Measurable fun v : Fin 2 → ℝ ↦ volume (fibreSet κ Q δ γ L v) :=
  measurable_measure_prodMk_right (μ := volume) (measurableSet_fibreSet_prod hΔ δ γ L)

/-! ### Dominated convergence in the transverse variables -/

/-- **The transverse limit**: `∫ vWeight · volume(fibreSet)/L^k → ∫ vWeight · vol(F')`. -/
theorem tendsto_lintegral_vWeight_fibre {κ Q : Fin k ⊕ Fin 2 → ℝ}
    (hΔ : (transMat κ Q).det ≠ 0) (hκ : ∀ i, 0 < κ i) {β η c₀ δ γ : ℝ}
    (hc₀ : fibreCoef κ Q 0 ≠ 0 ∨ fibreA κ Q δ γ 0 ≠ 0)
    (hc₁ : fibreCoef κ Q 1 ≠ 0 ∨ fibreA κ Q δ γ 1 ≠ 0) (hβ : 0 < β) (hη : 0 < η) (hc : 0 < c₀)
    (hδ : 0 ≤ δ) (h₀ : ℝ) :
    Tendsto (fun L ↦ ∫⁻ v : Fin 2 → ℝ,
        vWeight β η 0 c₀ h₀ v * (volume (fibreSet κ Q δ γ L v) / ENNReal.ofReal (L ^ k))) atTop
      (𝓝 (∫⁻ v : Fin 2 → ℝ, vWeight β η 0 c₀ h₀ v * volume (poly2 (fibreCoef κ Q 0)
        (fibreCoef κ Q 1) (fibreA κ Q δ γ 0) (fibreA κ Q δ γ 1)))) := by
  have hP : 0 < ∏ i, κ (Sum.inl i) := Finset.prod_pos fun i _ ↦ hκ _
  refine tendsto_lintegral_filter_of_dominated_convergence
    (fun v ↦ vWeight β η 0 c₀ h₀ v * ENNReal.ofReal ((|v 0| + δ) ^ k / ∏ i, κ (Sum.inl i)))
    (Eventually.of_forall fun L ↦ (measurable_vWeight _ _ _ _ _).mul
      ((measurable_volume_fibreSet hΔ δ γ L).div_const _)) ?_ ?_ ?_
  · filter_upwards [eventually_ge_atTop (1 : ℝ)] with L hL
    exact Eventually.of_forall fun v ↦
      mul_le_mul_of_nonneg_left (volume_fibreSet_div_le hΔ hκ hδ γ hL v) zero_le
  · have e : (fun v : Fin 2 → ℝ ↦
        vWeight β η 0 c₀ h₀ v * ENNReal.ofReal ((|v 0| + δ) ^ k / ∏ i, κ (Sum.inl i))) =
        fun v ↦ ENNReal.ofReal ((sWeight β c₀ (v 0) * (|v 0| + δ) ^ k / ∏ i, κ (Sum.inl i)) *
          hWeight η h₀ (v 1)) := by
      funext v
      rw [vWeight_zero_eq, ← ENNReal.ofReal_mul
        (mul_nonneg (sWeight_nonneg _ _ _) (hWeight_nonneg _ _ _))]
      congr 1
      ring
    rw [e, ← ofReal_integral_eq_lintegral_ofReal
      (integrable_fin_two_mul ((integrable_sWeight_mul_pow hβ hc hδ k).div_const _)
        (integrable_hWeight hη h₀))
      (Eventually.of_forall fun v ↦ mul_nonneg
        (div_nonneg (mul_nonneg (sWeight_nonneg _ _ _) (by positivity)) hP.le)
        (hWeight_nonneg _ _ _))]
    exact ENNReal.ofReal_ne_top
  · refine Eventually.of_forall fun v ↦ ?_
    refine ENNReal.Tendsto.const_mul (tendsto_volume_fibreSet_div hΔ hκ hc₀ hc₁ v)
      (Or.inr ?_)
    rw [vWeight_zero_eq]
    exact ENNReal.ofReal_ne_top

end Laplace.Multi
