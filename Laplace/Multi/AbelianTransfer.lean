/-
Copyright (c) 2026 Timaeus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Timaeus
-/
import Mathlib

/-!
# Abelian transfer: sublevel mass to Laplace asymptotics

For a finite measure `μ` and a measurable `K ≥ 0`, write `F(ε) = μ{K ≤ ε}`
(`sublevelMass`) and `Z(t) = ∫ e^{-tK} dμ` (`boltzmannMass`). The two are
related by the Laplace transform identity

  `Z(t) = t ∫₀^∞ e^{-tε} F(ε) dε`   (`boltzmannMass_eq_integral_sublevelMass`),

proved by Tonelli on the indicator of `{K ≤ ε}` against the kernel
`t e^{-tε}`. The transfer theorem (`boltzmannMass_power_transfer`): two-sided
power bounds `c₁ ε^λ ≤ F(ε) ≤ c₂ ε^λ` near `ε = 0` give two-sided bounds
`C₁ t^{-λ} ≤ Z(t) ≤ C₂ t^{-λ}` for large `t`. The upper bound globalises the
sublevel bound (`F ≤ μ(univ)` handles `ε ≥ ε₀`) and integrates the power kernel
to `Γ(λ+1) t^{-(λ+1)}`; the lower bound needs no identity at all:
`Z(t) ≥ e^{-1} F(1/t)` since `e^{-tK} ≥ e^{-1}` on `{K ≤ 1/t}`
(`exp_mul_sublevelMass_le_boltzmannMass`).

This is the standalone lemma the germbij note's next arc needs: hironaka's
sublevel-volume bounds for analytic `K` on a compact cube plug in as `μ =
volume.restrict cube`, `λ` the real log canonical threshold, and the forward
direction `Z(t) = Θ(t^{-λ})` at a singular point follows with no resolution
machinery on this side. No topology on the ambient space, no continuity of
`K`, and no absence of atoms is assumed.
-/

open MeasureTheory Set Filter
open scoped Topology ENNReal

namespace Laplace

variable {X : Type*} [MeasurableSpace X]

/-- The sublevel mass `μ{K ≤ ε}` as a real number. -/
noncomputable def sublevelMass (μ : Measure X) (K : X → ℝ) (ε : ℝ) : ℝ :=
  μ.real {x | K x ≤ ε}

/-- The Boltzmann mass `∫ e^{-tK} dμ`. -/
noncomputable def boltzmannMass (μ : Measure X) (K : X → ℝ) (t : ℝ) : ℝ :=
  ∫ x, Real.exp (-(t * K x)) ∂μ

variable (μ : Measure X) [IsFiniteMeasure μ] (K : X → ℝ)

omit [IsFiniteMeasure μ] in
theorem sublevelMass_nonneg (ε : ℝ) : 0 ≤ sublevelMass μ K ε := measureReal_nonneg

theorem sublevelMass_le_univ (ε : ℝ) : sublevelMass μ K ε ≤ μ.real univ :=
  measureReal_mono (subset_univ _)

theorem sublevelMass_mono : Monotone (sublevelMass μ K) := fun a b hab ↦
  measureReal_mono fun x hx ↦ le_trans (show K x ≤ a from hx) hab

theorem sublevelMass_measurable : Measurable (sublevelMass μ K) :=
  (sublevelMass_mono μ K).measurable

/-! ### The exponential tail -/

/-- `∫_a^∞ t e^{-tε} dε = e^{-ta}`. -/
theorem integral_exp_tail {t : ℝ} (ht : 0 < t) (a : ℝ) :
    ∫ ε in Ioi a, t * Real.exp (-(t * ε)) = Real.exp (-(t * a)) := by
  have h := integral_comp_mul_left_Ioi (fun x ↦ Real.exp (-x)) a ht
  rw [integral_exp_neg_Ioi, smul_eq_mul] at h
  rw [integral_const_mul, h, ← mul_assoc, mul_inv_cancel₀ ht.ne', one_mul]

theorem integrableOn_exp_tail {t : ℝ} (ht : 0 < t) (a : ℝ) :
    IntegrableOn (fun ε ↦ t * Real.exp (-(t * ε))) (Ioi a) := by
  have h := (integrableOn_Ioi_comp_mul_left_iff (fun x ↦ Real.exp (-x)) a ht).mpr
    (integrableOn_exp_neg_Ioi _)
  exact h.const_mul t

/-! ### The direct lower bound -/

/-- **Sublevel lower bound**: `e^{-ta} μ{K ≤ a} ≤ Z(t)` for `t > 0`. -/
theorem exp_mul_sublevelMass_le_boltzmannMass (hK : Measurable K) (hK0 : ∀ x, 0 ≤ K x)
    {t : ℝ} (ht : 0 < t) (a : ℝ) :
    Real.exp (-(t * a)) * sublevelMass μ K a ≤ boltzmannMass μ K t := by
  have hs : MeasurableSet {x | K x ≤ a} := measurableSet_le hK measurable_const
  have h1 : Integrable (fun x ↦ ({x | K x ≤ a}).indicator (fun _ ↦ Real.exp (-(t * a))) x) μ :=
    (integrable_const _).indicator hs
  have h2 : Integrable (fun x ↦ Real.exp (-(t * K x))) μ := by
    refine Integrable.of_bound (by fun_prop) 1 (Eventually.of_forall fun x ↦ ?_)
    rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _), Real.exp_le_one_iff]
    exact neg_nonpos.mpr (mul_nonneg ht.le (hK0 x))
  have hmono := integral_mono h1 h2 fun x ↦ by
    by_cases hx : K x ≤ a
    · simp only [indicator, mem_ofPred_eq, hx, if_true]
      exact Real.exp_le_exp.mpr (neg_le_neg (mul_le_mul_of_nonneg_left hx ht.le))
    · simp only [indicator, mem_ofPred_eq, hx, if_false]
      exact (Real.exp_pos _).le
  rw [integral_indicator_const _ hs, smul_eq_mul] at hmono
  unfold boltzmannMass sublevelMass
  linarith

/-! ### The Laplace transform identity -/

/-- **Abelian identity**: `Z(t) = t ∫₀^∞ e^{-tε} μ{K ≤ ε} dε` for `t > 0`. -/
theorem boltzmannMass_eq_integral_sublevelMass (hK : Measurable K) (hK0 : ∀ x, 0 ≤ K x)
    {t : ℝ} (ht : 0 < t) :
    boltzmannMass μ K t = t * ∫ ε in Ioi (0 : ℝ), Real.exp (-(t * ε)) * sublevelMass μ K ε := by
  set g : ℝ → ℝ := fun ε ↦ t * Real.exp (-(t * ε)) with hg_def
  have hg0 : ∀ ε, 0 ≤ g ε := fun ε ↦ mul_nonneg ht.le (Real.exp_pos _).le
  have hgm : Measurable g := by fun_prop
  set H : X → ℝ → ℝ≥0∞ := fun x ε ↦ if K x ≤ ε then ENNReal.ofReal (g ε) else 0 with hH_def
  -- Step 1: the fibre integral over `ε` recovers the Boltzmann weight.
  have hfib : ∀ x, ENNReal.ofReal (Real.exp (-(t * K x))) = ∫⁻ ε in Ioi (0 : ℝ), H x ε := by
    intro x
    have h1 : (fun ε ↦ H x ε) = (Ici (K x)).indicator fun ε ↦ ENNReal.ofReal (g ε) := by
      funext ε
      simp only [hH_def, indicator, mem_Ici]
    rw [h1, lintegral_indicator measurableSet_Ici, Measure.restrict_restrict measurableSet_Ici]
    have hae : (Ici (K x) ∩ Ioi 0 : Set ℝ) =ᵐ[volume] (Ioi (K x) : Set ℝ) := by
      have h2 : (Ici (K x) ∩ Ioi 0 : Set ℝ) =ᵐ[volume] (Ioi (K x) ∩ Ioi 0 : Set ℝ) :=
        Ioi_ae_eq_Ici.symm.inter EventuallyEq.rfl
      rw [inter_eq_left.mpr (Ioi_subset_Ioi (hK0 x))] at h2
      exact h2
    rw [setLIntegral_congr hae,
      ← ofReal_integral_eq_lintegral_ofReal (integrableOn_exp_tail ht (K x))
        (Eventually.of_forall hg0), integral_exp_tail ht]
  -- Step 2: the fibre integral over `x` is the kernel times the sublevel mass.
  have hfib' : ∀ ε, ∫⁻ x, H x ε ∂μ = ENNReal.ofReal (g ε) * μ {x | K x ≤ ε} := by
    intro ε
    have hs : MeasurableSet {x | K x ≤ ε} := measurableSet_le hK measurable_const
    have h1 : (fun x ↦ H x ε) = ({x | K x ≤ ε}).indicator fun _ ↦ ENNReal.ofReal (g ε) := by
      funext x
      simp only [hH_def, indicator, mem_ofPred_eq]
    rw [h1, lintegral_indicator_const hs]
  -- Measurability of the kernel on the product.
  have hHm : AEMeasurable (Function.uncurry H) (μ.prod (volume.restrict (Ioi (0 : ℝ)))) := by
    refine Measurable.aemeasurable ?_
    change Measurable fun p : X × ℝ ↦ if K p.1 ≤ p.2 then ENNReal.ofReal (g p.2) else 0
    exact Measurable.ite (measurableSet_le (hK.comp measurable_fst) measurable_snd)
      (ENNReal.measurable_ofReal.comp (hgm.comp measurable_snd)) measurable_const
  -- Integrability of the right-hand integrand.
  have hFm : Measurable (sublevelMass μ K) := sublevelMass_measurable μ K
  have hint : IntegrableOn (fun ε ↦ g ε * sublevelMass μ K ε) (Ioi (0 : ℝ)) := by
    refine Integrable.mono' ((integrableOn_exp_tail ht 0).mul_const (μ.real univ))
      (hgm.mul hFm).aestronglyMeasurable (Eventually.of_forall fun ε ↦ ?_)
    rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (hg0 ε) (sublevelMass_nonneg μ K ε))]
    exact mul_le_mul_of_nonneg_left (sublevelMass_le_univ μ K ε) (hg0 ε)
  have hnn : 0 ≤ ∫ ε in Ioi (0 : ℝ), g ε * sublevelMass μ K ε :=
    integral_nonneg fun ε ↦ mul_nonneg (hg0 ε) (sublevelMass_nonneg μ K ε)
  -- Assemble.
  have hL : boltzmannMass μ K t = (∫⁻ x, (∫⁻ ε in Ioi (0 : ℝ), H x ε) ∂μ).toReal := by
    unfold boltzmannMass
    rw [integral_eq_lintegral_of_nonneg_ae (Eventually.of_forall fun x ↦ (Real.exp_pos _).le)
      (by fun_prop)]
    congr 1
    exact lintegral_congr fun x ↦ hfib x
  have hR : (∫⁻ ε in Ioi (0 : ℝ), ∫⁻ x, H x ε ∂μ).toReal =
      ∫ ε in Ioi (0 : ℝ), g ε * sublevelMass μ K ε := by
    have h1 : ∀ ε, ∫⁻ x, H x ε ∂μ = ENNReal.ofReal (g ε * sublevelMass μ K ε) := by
      intro ε
      rw [hfib' ε, ENNReal.ofReal_mul (hg0 ε), sublevelMass, measureReal_def,
        ENNReal.ofReal_toReal (measure_ne_top _ _)]
    rw [lintegral_congr h1, ← ofReal_integral_eq_lintegral_ofReal hint
      (Eventually.of_forall fun ε ↦ mul_nonneg (hg0 ε) (sublevelMass_nonneg μ K ε)),
      ENNReal.toReal_ofReal hnn]
  rw [hL, lintegral_lintegral_swap hHm, hR, ← integral_const_mul]
  congr 1
  funext ε
  simp only [hg_def]
  ring

/-! ### The power kernel -/

/-- `∫₀^∞ e^{-tε} ε^λ dε = Γ(λ+1) t^{-(λ+1)}`. -/
theorem integral_exp_mul_rpow_Ioi {lam t : ℝ} (hlam : -1 < lam) (ht : 0 < t) :
    ∫ ε in Ioi (0 : ℝ), Real.exp (-(t * ε)) * ε ^ lam =
      Real.Gamma (lam + 1) * t ^ (-(lam + 1)) := by
  have h := integral_rpow_mul_exp_neg_mul_rpow (p := 1) (q := lam) (b := t) one_pos hlam ht
  simp only [Real.rpow_one, div_one, mul_one] at h
  calc ∫ ε in Ioi (0 : ℝ), Real.exp (-(t * ε)) * ε ^ lam
      = ∫ x in Ioi (0 : ℝ), x ^ lam * Real.exp (-t * x) := by
        refine setIntegral_congr_fun measurableSet_Ioi fun x _ ↦ ?_
        rw [neg_mul, mul_comm]
    _ = Real.Gamma (lam + 1) * t ^ (-(lam + 1)) := by rw [h, mul_comm]

theorem integrableOn_exp_mul_rpow_Ioi {lam t : ℝ} (hlam : -1 < lam) (ht : 0 < t) :
    IntegrableOn (fun ε ↦ Real.exp (-(t * ε)) * ε ^ lam) (Ioi (0 : ℝ)) := by
  have h := integrableOn_rpow_mul_exp_neg_mul_rpow (p := 1) (s := lam) (b := t) hlam one_pos ht
  refine h.congr_fun (fun x _ ↦ ?_) measurableSet_Ioi
  simp only [Real.rpow_one]
  rw [neg_mul, mul_comm]

/-! ### The transfer -/

/-- Globalising a local power upper bound on the sublevel mass. -/
theorem exists_global_sublevel_bound {lam ε₀ c₂ : ℝ} (hlam : 0 < lam) (hε₀ : 0 < ε₀)
    (hc₂ : 0 < c₂)
    (hupper : ∀ ε : ℝ, 0 < ε → ε ≤ ε₀ → sublevelMass μ K ε ≤ c₂ * ε ^ lam) :
    ∃ A : ℝ, 0 < A ∧ ∀ ε : ℝ, 0 < ε → sublevelMass μ K ε ≤ A * ε ^ lam := by
  refine ⟨max c₂ (μ.real univ / ε₀ ^ lam), lt_max_of_lt_left hc₂, fun ε hε ↦ ?_⟩
  have hεpow : 0 < ε ^ lam := Real.rpow_pos_of_pos hε _
  by_cases hle : ε ≤ ε₀
  · exact (hupper ε hε hle).trans
      (mul_le_mul_of_nonneg_right (le_max_left _ _) hεpow.le)
  · have hle' : ε₀ < ε := not_le.mp hle
    have h0 : 0 < ε₀ ^ lam := Real.rpow_pos_of_pos hε₀ _
    have hpow : ε₀ ^ lam ≤ ε ^ lam := Real.rpow_le_rpow hε₀.le hle'.le hlam.le
    calc sublevelMass μ K ε ≤ μ.real univ := sublevelMass_le_univ μ K ε
      _ = μ.real univ / ε₀ ^ lam * ε₀ ^ lam := by field_simp
      _ ≤ μ.real univ / ε₀ ^ lam * ε ^ lam :=
          mul_le_mul_of_nonneg_left hpow (div_nonneg measureReal_nonneg h0.le)
      _ ≤ max c₂ (μ.real univ / ε₀ ^ lam) * ε ^ lam :=
          mul_le_mul_of_nonneg_right (le_max_right _ _) hεpow.le

/-- **Upper bound from a global power bound**: `Z(t) ≤ A Γ(λ+1) t^{-λ}`. -/
theorem boltzmannMass_le_of_sublevel_bound (hK : Measurable K) (hK0 : ∀ x, 0 ≤ K x)
    {lam A : ℝ} (hlam : 0 < lam)
    (hupper : ∀ ε : ℝ, 0 < ε → sublevelMass μ K ε ≤ A * ε ^ lam) {t : ℝ} (ht : 0 < t) :
    boltzmannMass μ K t ≤ A * Real.Gamma (lam + 1) * t ^ (-lam) := by
  rw [boltzmannMass_eq_integral_sublevelMass μ K hK hK0 ht]
  have hFm : Measurable (sublevelMass μ K) := sublevelMass_measurable μ K
  have hg0 : ∀ ε, 0 ≤ Real.exp (-(t * ε)) := fun ε ↦ (Real.exp_pos _).le
  have hint : IntegrableOn (fun ε ↦ Real.exp (-(t * ε)) * sublevelMass μ K ε) (Ioi (0 : ℝ)) := by
    have h := (integrableOn_exp_tail ht 0).mul_const (μ.real univ)
    refine Integrable.mono' (h.const_mul t⁻¹) ((by fun_prop : Measurable fun ε ↦
      Real.exp (-(t * ε))).mul hFm).aestronglyMeasurable (Eventually.of_forall fun ε ↦ ?_)
    rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (hg0 ε) (sublevelMass_nonneg μ K ε))]
    calc Real.exp (-(t * ε)) * sublevelMass μ K ε ≤ Real.exp (-(t * ε)) * μ.real univ :=
          mul_le_mul_of_nonneg_left (sublevelMass_le_univ μ K ε) (hg0 ε)
      _ = t⁻¹ * (t * Real.exp (-(t * ε)) * μ.real univ) := by
          field_simp
  have hlam' : -1 < lam := by linarith
  have hint2 : IntegrableOn (fun ε ↦ Real.exp (-(t * ε)) * (A * ε ^ lam)) (Ioi (0 : ℝ)) := by
    have h : IntegrableOn (fun ε ↦ A * (Real.exp (-(t * ε)) * ε ^ lam)) (Ioi (0 : ℝ)) :=
      (integrableOn_exp_mul_rpow_Ioi hlam' ht).const_mul A
    refine h.congr_fun (fun x _ ↦ ?_) measurableSet_Ioi
    ring
  have hmono := setIntegral_mono_on hint hint2 measurableSet_Ioi fun ε hε ↦
    mul_le_mul_of_nonneg_left (hupper ε hε) (hg0 ε)
  have hval : ∫ ε in Ioi (0 : ℝ), Real.exp (-(t * ε)) * (A * ε ^ lam) =
      A * (Real.Gamma (lam + 1) * t ^ (-(lam + 1))) := by
    rw [← integral_exp_mul_rpow_Ioi hlam' ht, ← integral_const_mul]
    refine setIntegral_congr_fun measurableSet_Ioi fun x _ ↦ ?_
    ring
  rw [hval] at hmono
  have hpow : t * t ^ (-(lam + 1)) = t ^ (-lam) := by
    rw [show -(lam + 1) = -lam + (-1) by ring, Real.rpow_add ht, Real.rpow_neg_one]
    field_simp
  calc t * ∫ ε in Ioi (0 : ℝ), Real.exp (-(t * ε)) * sublevelMass μ K ε
      ≤ t * (A * (Real.Gamma (lam + 1) * t ^ (-(lam + 1)))) :=
        mul_le_mul_of_nonneg_left hmono ht.le
    _ = A * Real.Gamma (lam + 1) * (t * t ^ (-(lam + 1))) := by ring
    _ = A * Real.Gamma (lam + 1) * t ^ (-lam) := by rw [hpow]

/-- **Abelian transfer, power case.** Two-sided power bounds
`c₁ ε^λ ≤ μ{K ≤ ε} ≤ c₂ ε^λ` for small `ε > 0` give two-sided bounds
`C₁ t^{-λ} ≤ ∫ e^{-tK} dμ ≤ C₂ t^{-λ}` for large `t`, with
`C₁ = e^{-1} c₁` and `C₂ = A Γ(λ+1)`. -/
theorem boltzmannMass_power_transfer (hK : Measurable K) (hK0 : ∀ x, 0 ≤ K x)
    {lam ε₀ c₁ c₂ : ℝ} (hlam : 0 < lam) (hε₀ : 0 < ε₀) (hc₁ : 0 < c₁) (hc₂ : 0 < c₂)
    (hlower : ∀ ε : ℝ, 0 < ε → ε ≤ ε₀ → c₁ * ε ^ lam ≤ sublevelMass μ K ε)
    (hupper : ∀ ε : ℝ, 0 < ε → ε ≤ ε₀ → sublevelMass μ K ε ≤ c₂ * ε ^ lam) :
    ∃ C₁ C₂ : ℝ, 0 < C₁ ∧ 0 < C₂ ∧ ∀ᶠ t : ℝ in atTop,
      C₁ * t ^ (-lam) ≤ boltzmannMass μ K t ∧ boltzmannMass μ K t ≤ C₂ * t ^ (-lam) := by
  obtain ⟨A, hA, hglob⟩ := exists_global_sublevel_bound μ K hlam hε₀ hc₂ hupper
  refine ⟨Real.exp (-1) * c₁, A * Real.Gamma (lam + 1), mul_pos (Real.exp_pos _) hc₁,
    mul_pos hA (Real.Gamma_pos_of_pos (by linarith)), ?_⟩
  filter_upwards [eventually_ge_atTop (max 1 ε₀⁻¹)] with t ht
  have ht1 : 1 ≤ t := le_trans (le_max_left _ _) ht
  have htpos : 0 < t := lt_of_lt_of_le one_pos ht1
  have hinv : t⁻¹ ≤ ε₀ := by
    have : ε₀⁻¹ ≤ t := le_trans (le_max_right _ _) ht
    calc t⁻¹ ≤ (ε₀⁻¹)⁻¹ := inv_anti₀ (inv_pos.mpr hε₀) this
      _ = ε₀ := inv_inv ε₀
  constructor
  · have h := exp_mul_sublevelMass_le_boltzmannMass μ K hK hK0 htpos t⁻¹
    rw [mul_inv_cancel₀ htpos.ne'] at h
    have hF := hlower t⁻¹ (inv_pos.mpr htpos) hinv
    rw [Real.inv_rpow htpos.le, ← Real.rpow_neg htpos.le] at hF
    calc Real.exp (-1) * c₁ * t ^ (-lam) = Real.exp (-1) * (c₁ * t ^ (-lam)) := by ring
      _ ≤ Real.exp (-1) * sublevelMass μ K t⁻¹ :=
          mul_le_mul_of_nonneg_left hF (Real.exp_pos _).le
      _ ≤ boltzmannMass μ K t := h
  · exact boltzmannMass_le_of_sublevel_bound μ K hK hK0 hlam hglob htpos

end Laplace
