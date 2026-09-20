/-
Copyright (c) 2026 Timaeus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Timaeus
-/
import Mathlib
import Laplace.Multi.AbelianTransfer

/-!
# Abelian transfer with logarithmic multiplicity

The power-case transfer of `AbelianTransfer` extended to sublevel masses with
a logarithmic factor: if `c₁ ε^λ (log 1/ε)^k ≤ μ{K ≤ ε} ≤ c₂ ε^λ (log 1/ε)^k`
for small `ε`, then `C₁ t^{-λ} (log t)^k ≤ ∫ e^{-tK} dμ ≤ C₂ t^{-λ} (log t)^k`
for large `t` (`boltzmannMass_log_transfer`). This is the shape of the
singular Laplace leading term with real log canonical threshold `λ` and
multiplicity `m = k + 1`.

The lower bound is the direct sublevel bound `Z(t) ≥ e^{-1} μ{K ≤ 1/t}` as
before. For the upper bound the local sublevel bound is globalised with the
weight `logWeight ε = 1 + max 0 (log 1/ε)`, the weight is compared to
`(1 + log t)(1 + |log(tε)|)` for `t ≥ 1`, and after the substitution
`s = tε` the kernel integral `∫₀^∞ e^{-s} s^λ (1 + |log s|)^k ds` is a finite
constant (`integrableOn_exp_rpow_logpow`: the logarithm is dominated by
`s^{±δ}` with `δ` small).
-/

open MeasureTheory Set Filter
open scoped Topology ENNReal

namespace Laplace

/-! ### The logarithmic weight -/

/-- The global weight `1 + max 0 (log 1/ε)`. -/
noncomputable def logWeight (ε : ℝ) : ℝ := 1 + max 0 (-Real.log ε)

theorem one_le_logWeight (ε : ℝ) : 1 ≤ logWeight ε := by
  unfold logWeight
  linarith [le_max_left 0 (-Real.log ε)]

theorem logWeight_nonneg (ε : ℝ) : 0 ≤ logWeight ε := zero_le_one.trans (one_le_logWeight ε)

theorem neg_log_le_logWeight (ε : ℝ) : -Real.log ε ≤ logWeight ε := by
  unfold logWeight
  linarith [le_max_right 0 (-Real.log ε)]

/-- For `t ≥ 1` and `ε > 0`: `logWeight ε ≤ (1 + log t) (1 + |log (tε)|)`. -/
theorem logWeight_le_mul {t ε : ℝ} (ht : 1 ≤ t) (hε : 0 < ε) :
    logWeight ε ≤ (1 + Real.log t) * (1 + |Real.log (t * ε)|) := by
  have hlt : 0 ≤ Real.log t := Real.log_nonneg ht
  have habs : 0 ≤ |Real.log (t * ε)| := abs_nonneg _
  have hsplit : Real.log (t * ε) = Real.log t + Real.log ε :=
    Real.log_mul (by linarith) hε.ne'
  have h1 : -Real.log ε ≤ Real.log t + |Real.log (t * ε)| := by
    have := neg_abs_le (Real.log (t * ε))
    linarith
  have h2 : max 0 (-Real.log ε) ≤ Real.log t + |Real.log (t * ε)| :=
    max_le (by linarith) h1
  unfold logWeight
  nlinarith [mul_nonneg hlt habs]

/-! ### Finiteness of the kernel constant -/

/-- `log x ≤ x^δ / δ` for `x > 0`, `δ > 0`. -/
theorem log_le_rpow_div' {x δ : ℝ} (hx : 0 < x) (hδ : 0 < δ) : Real.log x ≤ x ^ δ / δ := by
  have h := Real.log_le_sub_one_of_pos (Real.rpow_pos_of_pos hx δ)
  rw [Real.log_rpow hx] at h
  rw [le_div_iff₀ hδ]
  linarith [Real.rpow_pos_of_pos hx δ]

/-- `|log s| ≤ (s^δ + s^{-δ}) / δ` for `s > 0`, `δ > 0`. -/
theorem abs_log_le_rpow_add {s δ : ℝ} (hs : 0 < s) (hδ : 0 < δ) :
    |Real.log s| ≤ (s ^ δ + s ^ (-δ)) / δ := by
  have h1 : Real.log s ≤ s ^ δ / δ := log_le_rpow_div' hs hδ
  have h2 : -Real.log s ≤ s ^ (-δ) / δ := by
    have := log_le_rpow_div' (inv_pos.mpr hs) hδ
    rwa [Real.log_inv, Real.inv_rpow hs.le, ← Real.rpow_neg hs.le] at this
  have hp : 0 ≤ s ^ δ / δ := div_nonneg (Real.rpow_nonneg hs.le _) hδ.le
  have hn : 0 ≤ s ^ (-δ) / δ := div_nonneg (Real.rpow_nonneg hs.le _) hδ.le
  rw [abs_le]
  constructor <;> · rw [add_div]; linarith

/-- `(1 + |log s|)^k ≤ (2 (1 + 1/δ))^k (s^{kδ} + s^{-kδ})` for `s > 0`. -/
theorem one_add_abs_log_pow_le {s δ : ℝ} (hs : 0 < s) (hδ : 0 < δ) (k : ℕ) :
    (1 + |Real.log s|) ^ k ≤
      (2 * (1 + 1 / δ)) ^ k * (s ^ ((k : ℝ) * δ) + s ^ (-((k : ℝ) * δ))) := by
  have hpos : 0 < s ^ δ := Real.rpow_pos_of_pos hs δ
  have hneg : 0 < s ^ (-δ) := Real.rpow_pos_of_pos hs _
  -- `1 ≤ s^δ + s^{-δ}` (the two are reciprocal).
  have hrecip : s ^ δ * s ^ (-δ) = 1 := by
    rw [← Real.rpow_add hs, add_neg_cancel, Real.rpow_zero]
  have hsum1 : 1 ≤ s ^ δ + s ^ (-δ) := by nlinarith [sq_nonneg (s ^ δ - s ^ (-δ))]
  have h1 : 1 + |Real.log s| ≤ (1 + 1 / δ) * (s ^ δ + s ^ (-δ)) := by
    have := abs_log_le_rpow_add hs hδ
    have h1δ : 0 ≤ 1 / δ := by positivity
    calc 1 + |Real.log s| ≤ 1 + (s ^ δ + s ^ (-δ)) / δ := by linarith
      _ = 1 + 1 / δ * (s ^ δ + s ^ (-δ)) := by ring
      _ ≤ (s ^ δ + s ^ (-δ)) + 1 / δ * (s ^ δ + s ^ (-δ)) := by linarith
      _ = (1 + 1 / δ) * (s ^ δ + s ^ (-δ)) := by ring
  -- `(a + b)^k ≤ (2a)^k + (2b)^k` for `a, b ≥ 0` (case on which is larger).
  have h2 : (s ^ δ + s ^ (-δ)) ^ k ≤ (2 * s ^ δ) ^ k + (2 * s ^ (-δ)) ^ k := by
    rcases le_total (s ^ (-δ)) (s ^ δ) with hle | hle
    · calc (s ^ δ + s ^ (-δ)) ^ k ≤ (2 * s ^ δ) ^ k :=
            pow_le_pow_left₀ (by positivity) (by linarith) k
        _ ≤ (2 * s ^ δ) ^ k + (2 * s ^ (-δ)) ^ k := by
            linarith [pow_nonneg (by positivity : (0 : ℝ) ≤ 2 * s ^ (-δ)) k]
    · calc (s ^ δ + s ^ (-δ)) ^ k ≤ (2 * s ^ (-δ)) ^ k :=
            pow_le_pow_left₀ (by positivity) (by linarith) k
        _ ≤ (2 * s ^ δ) ^ k + (2 * s ^ (-δ)) ^ k := by
            linarith [pow_nonneg (by positivity : (0 : ℝ) ≤ 2 * s ^ δ) k]
  have hk1 : (s ^ δ) ^ k = s ^ ((k : ℝ) * δ) := by
    rw [mul_comm, Real.rpow_mul hs.le, Real.rpow_natCast]
  have hk2 : (s ^ (-δ)) ^ k = s ^ (-((k : ℝ) * δ)) := by
    rw [show -((k : ℝ) * δ) = (-δ) * k by ring, Real.rpow_mul hs.le, Real.rpow_natCast]
  calc (1 + |Real.log s|) ^ k ≤ ((1 + 1 / δ) * (s ^ δ + s ^ (-δ))) ^ k :=
        pow_le_pow_left₀ (by positivity) h1 k
    _ = (1 + 1 / δ) ^ k * (s ^ δ + s ^ (-δ)) ^ k := mul_pow _ _ _
    _ ≤ (1 + 1 / δ) ^ k * ((2 * s ^ δ) ^ k + (2 * s ^ (-δ)) ^ k) :=
        mul_le_mul_of_nonneg_left h2 (by positivity)
    _ = (2 * (1 + 1 / δ)) ^ k * (s ^ ((k : ℝ) * δ) + s ^ (-((k : ℝ) * δ))) := by
        rw [← hk1, ← hk2, mul_pow, mul_pow, mul_pow]
        ring

/-- The kernel `e^{-s} s^λ` is integrable on `(0, ∞)` for `λ > -1`. -/
theorem integrableOn_exp_neg_mul_rpow {lam : ℝ} (hlam : -1 < lam) :
    IntegrableOn (fun s : ℝ ↦ Real.exp (-s) * s ^ lam) (Ioi (0 : ℝ)) := by
  have h := integrableOn_rpow_mul_exp_neg_rpow (p := 1) (s := lam) hlam one_pos
  refine h.congr_fun (fun x _ ↦ ?_) measurableSet_Ioi
  simp only [Real.rpow_one]
  ring

/-- **Finiteness of the kernel constant**: `e^{-s} s^λ (1 + |log s|)^k` is
integrable on `(0, ∞)` for `λ > -1`. -/
theorem integrableOn_exp_rpow_logpow {lam : ℝ} (hlam : -1 < lam) (k : ℕ) :
    IntegrableOn (fun s : ℝ ↦ Real.exp (-s) * s ^ lam * (1 + |Real.log s|) ^ k)
      (Ioi (0 : ℝ)) := by
  set δ : ℝ := (lam + 1) / (2 * ((k : ℝ) + 1)) with hδ_def
  have hδ : 0 < δ := div_pos (by linarith) (by positivity)
  have hkδ : (k : ℝ) * δ ≤ (lam + 1) / 2 := by
    rw [hδ_def]
    have hk1 : (0 : ℝ) < (k : ℝ) + 1 := by positivity
    rw [mul_div_assoc', div_le_div_iff₀ (by positivity) (by norm_num)]
    nlinarith [hk1]
  have hlam1 : -1 < lam + (k : ℝ) * δ := by
    have : 0 ≤ (k : ℝ) * δ := by positivity
    linarith
  have hlam2 : -1 < lam - (k : ℝ) * δ := by linarith
  set C : ℝ := (2 * (1 + 1 / δ)) ^ k with hC_def
  have hC : 0 ≤ C := by positivity
  have hint1 := integrableOn_exp_neg_mul_rpow hlam1
  have hint2 := integrableOn_exp_neg_mul_rpow hlam2
  have hbound : IntegrableOn (fun s : ℝ ↦ C * (Real.exp (-s) * s ^ (lam + (k : ℝ) * δ) +
      Real.exp (-s) * s ^ (lam - (k : ℝ) * δ))) (Ioi (0 : ℝ)) := (hint1.add hint2).const_mul C
  refine Integrable.mono' hbound ?_ ?_
  · refine Measurable.aestronglyMeasurable ?_
    fun_prop
  · rw [ae_restrict_iff' measurableSet_Ioi]
    refine Eventually.of_forall fun s hs ↦ ?_
    have hs : 0 < s := hs
    have he : 0 < Real.exp (-s) := Real.exp_pos _
    have hsl : 0 ≤ s ^ lam := Real.rpow_nonneg hs.le _
    rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    have h1 := one_add_abs_log_pow_le hs hδ k
    have h2 : s ^ lam * s ^ ((k : ℝ) * δ) = s ^ (lam + (k : ℝ) * δ) := (Real.rpow_add hs _ _).symm
    have h3 : s ^ lam * s ^ (-((k : ℝ) * δ)) = s ^ (lam - (k : ℝ) * δ) := by
      rw [← Real.rpow_add hs]
      ring_nf
    calc Real.exp (-s) * s ^ lam * (1 + |Real.log s|) ^ k
        ≤ Real.exp (-s) * s ^ lam * (C * (s ^ ((k : ℝ) * δ) + s ^ (-((k : ℝ) * δ)))) :=
          mul_le_mul_of_nonneg_left h1 (by positivity)
      _ = C * (Real.exp (-s) * (s ^ lam * s ^ ((k : ℝ) * δ)) +
            Real.exp (-s) * (s ^ lam * s ^ (-((k : ℝ) * δ)))) := by ring
      _ = C * (Real.exp (-s) * s ^ (lam + (k : ℝ) * δ) +
            Real.exp (-s) * s ^ (lam - (k : ℝ) * δ)) := by rw [h2, h3]

/-- The kernel constant `I_k(λ) = ∫₀^∞ e^{-s} s^λ (1 + |log s|)^k ds`. -/
noncomputable def logKernelConst (lam : ℝ) (k : ℕ) : ℝ :=
  ∫ s in Ioi (0 : ℝ), Real.exp (-s) * s ^ lam * (1 + |Real.log s|) ^ k

theorem logKernelConst_nonneg (lam : ℝ) (k : ℕ) : 0 ≤ logKernelConst lam k :=
  setIntegral_nonneg measurableSet_Ioi fun s hs ↦
    mul_nonneg (mul_nonneg (Real.exp_pos _).le (Real.rpow_nonneg (le_of_lt hs) _))
      (pow_nonneg (by positivity) k)

/-! ### Scaling -/

/-- Scaling the kernel: `∫₀^∞ e^{-tε} ε^λ (1 + |log(tε)|)^k dε = t^{-(λ+1)} I_k(λ)`. -/
theorem integral_exp_mul_rpow_logpow_scaled {lam t : ℝ} (ht : 0 < t) (k : ℕ) :
    ∫ ε in Ioi (0 : ℝ), Real.exp (-(t * ε)) * ε ^ lam * (1 + |Real.log (t * ε)|) ^ k =
      t ^ (-(lam + 1)) * logKernelConst lam k := by
  set h : ℝ → ℝ := fun s ↦ Real.exp (-s) * s ^ lam * (1 + |Real.log s|) ^ k with hh_def
  have hsub := integral_comp_mul_left_Ioi h 0 ht
  rw [mul_zero, smul_eq_mul] at hsub
  have hpt : ∀ ε ∈ Ioi (0 : ℝ), Real.exp (-(t * ε)) * ε ^ lam * (1 + |Real.log (t * ε)|) ^ k =
      (t ^ lam)⁻¹ * h (t * ε) := by
    intro ε hε
    have hε : 0 < ε := hε
    simp only [hh_def]
    rw [Real.mul_rpow ht.le hε.le]
    have : t ^ lam ≠ 0 := (Real.rpow_pos_of_pos ht lam).ne'
    field_simp
  rw [setIntegral_congr_fun measurableSet_Ioi hpt, integral_const_mul, hsub]
  have hpow : t ^ (-(lam + 1)) = (t ^ lam)⁻¹ * t⁻¹ := by
    rw [Real.rpow_neg ht.le, Real.rpow_add ht, Real.rpow_one, mul_inv]
  rw [hpow]
  unfold logKernelConst
  ring

theorem integrableOn_exp_mul_rpow_logpow_scaled {lam t : ℝ} (hlam : -1 < lam) (ht : 0 < t)
    (k : ℕ) :
    IntegrableOn (fun ε ↦ Real.exp (-(t * ε)) * ε ^ lam * (1 + |Real.log (t * ε)|) ^ k)
      (Ioi (0 : ℝ)) := by
  set h : ℝ → ℝ := fun s ↦ Real.exp (-s) * s ^ lam * (1 + |Real.log s|) ^ k with hh_def
  have h1 : IntegrableOn (fun ε ↦ h (t * ε)) (Ioi (0 : ℝ)) := by
    rw [integrableOn_Ioi_comp_mul_left_iff h 0 ht, mul_zero]
    exact integrableOn_exp_rpow_logpow hlam k
  have h2 : IntegrableOn (fun ε ↦ (t ^ lam)⁻¹ * h (t * ε)) (Ioi (0 : ℝ)) :=
    h1.const_mul _
  refine h2.congr_fun (fun ε hε ↦ ?_) measurableSet_Ioi
  have hε : 0 < ε := hε
  simp only [hh_def]
  rw [Real.mul_rpow ht.le hε.le]
  have : t ^ lam ≠ 0 := (Real.rpow_pos_of_pos ht lam).ne'
  field_simp

/-! ### The transfer -/

variable {X : Type*} [MeasurableSpace X] (μ : Measure X) [IsFiniteMeasure μ] (K : X → ℝ)

/-- Globalising a local log-power upper bound with the weight `logWeight`. -/
theorem exists_global_sublevel_logBound {lam ε₀ c₂ : ℝ} (k : ℕ) (hlam : 0 < lam)
    (hε₀ : 0 < ε₀) (hε₀1 : ε₀ < 1) (hc₂ : 0 < c₂)
    (hupper : ∀ ε : ℝ, 0 < ε → ε ≤ ε₀ →
      sublevelMass μ K ε ≤ c₂ * ε ^ lam * (Real.log ε⁻¹) ^ k) :
    ∃ A : ℝ, 0 < A ∧ ∀ ε : ℝ, 0 < ε → sublevelMass μ K ε ≤ A * ε ^ lam * logWeight ε ^ k := by
  refine ⟨max c₂ (μ.real univ / ε₀ ^ lam), lt_max_of_lt_left hc₂, fun ε hε ↦ ?_⟩
  have hεpow : 0 < ε ^ lam := Real.rpow_pos_of_pos hε _
  have hlw : 1 ≤ logWeight ε ^ k := one_le_pow₀ (one_le_logWeight ε)
  have hlw0 : 0 ≤ logWeight ε ^ k := zero_le_one.trans hlw
  by_cases hle : ε ≤ ε₀
  · have hlog : 0 ≤ -Real.log ε := by
      have : Real.log ε < 0 := Real.log_neg hε (lt_of_le_of_lt hle hε₀1)
      linarith
    have hpowle : (Real.log ε⁻¹) ^ k ≤ logWeight ε ^ k := by
      rw [Real.log_inv]
      exact pow_le_pow_left₀ hlog (neg_log_le_logWeight ε) k
    calc sublevelMass μ K ε ≤ c₂ * ε ^ lam * (Real.log ε⁻¹) ^ k := hupper ε hε hle
      _ ≤ c₂ * ε ^ lam * logWeight ε ^ k :=
          mul_le_mul_of_nonneg_left hpowle (by positivity)
      _ ≤ max c₂ (μ.real univ / ε₀ ^ lam) * ε ^ lam * logWeight ε ^ k := by
          gcongr
          exact le_max_left _ _
  · have hle' : ε₀ < ε := not_le.mp hle
    have h0 : 0 < ε₀ ^ lam := Real.rpow_pos_of_pos hε₀ _
    have hpow : ε₀ ^ lam ≤ ε ^ lam := Real.rpow_le_rpow hε₀.le hle'.le hlam.le
    have hM : 0 ≤ μ.real univ / ε₀ ^ lam := div_nonneg measureReal_nonneg h0.le
    calc sublevelMass μ K ε ≤ μ.real univ := sublevelMass_le_univ μ K ε
      _ = μ.real univ / ε₀ ^ lam * ε₀ ^ lam := by field_simp
      _ ≤ μ.real univ / ε₀ ^ lam * ε ^ lam := mul_le_mul_of_nonneg_left hpow hM
      _ = μ.real univ / ε₀ ^ lam * ε ^ lam * 1 := (mul_one _).symm
      _ ≤ μ.real univ / ε₀ ^ lam * ε ^ lam * logWeight ε ^ k :=
          mul_le_mul_of_nonneg_left hlw (by positivity)
      _ ≤ max c₂ (μ.real univ / ε₀ ^ lam) * ε ^ lam * logWeight ε ^ k := by
          gcongr
          exact le_max_right _ _

/-- **Upper bound from a global log-power bound**:
`Z(t) ≤ A I_k(λ) t^{-λ} (1 + log t)^k` for `t ≥ 1`. -/
theorem boltzmannMass_le_of_sublevel_logBound (hK : Measurable K) (hK0 : ∀ x, 0 ≤ K x)
    {lam A : ℝ} (hlam : 0 < lam) (hA : 0 ≤ A) (k : ℕ)
    (hupper : ∀ ε : ℝ, 0 < ε → sublevelMass μ K ε ≤ A * ε ^ lam * logWeight ε ^ k)
    {t : ℝ} (ht : 1 ≤ t) :
    boltzmannMass μ K t ≤
      A * logKernelConst lam k * t ^ (-lam) * (1 + Real.log t) ^ k := by
  have htpos : 0 < t := lt_of_lt_of_le one_pos ht
  have hlt : 0 ≤ Real.log t := Real.log_nonneg ht
  rw [boltzmannMass_eq_integral_sublevelMass μ K hK hK0 htpos]
  have hFm : Measurable (sublevelMass μ K) := sublevelMass_measurable μ K
  have hg0 : ∀ ε, 0 ≤ Real.exp (-(t * ε)) := fun ε ↦ (Real.exp_pos _).le
  have hint : IntegrableOn (fun ε ↦ Real.exp (-(t * ε)) * sublevelMass μ K ε) (Ioi (0 : ℝ)) := by
    have h := (integrableOn_exp_tail htpos 0).mul_const (μ.real univ)
    refine Integrable.mono' (h.const_mul t⁻¹) ((by fun_prop : Measurable fun ε ↦
      Real.exp (-(t * ε))).mul hFm).aestronglyMeasurable (Eventually.of_forall fun ε ↦ ?_)
    rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (hg0 ε) (sublevelMass_nonneg μ K ε))]
    calc Real.exp (-(t * ε)) * sublevelMass μ K ε ≤ Real.exp (-(t * ε)) * μ.real univ :=
          mul_le_mul_of_nonneg_left (sublevelMass_le_univ μ K ε) (hg0 ε)
      _ = t⁻¹ * (t * Real.exp (-(t * ε)) * μ.real univ) := by
          field_simp
  have hlam' : -1 < lam := by linarith
  set B : ℝ := A * (1 + Real.log t) ^ k with hB_def
  have hB : 0 ≤ B := by positivity
  have hint2 : IntegrableOn (fun ε ↦ Real.exp (-(t * ε)) *
      (B * (ε ^ lam * (1 + |Real.log (t * ε)|) ^ k))) (Ioi (0 : ℝ)) := by
    have h : IntegrableOn (fun ε ↦ B * (Real.exp (-(t * ε)) * ε ^ lam *
        (1 + |Real.log (t * ε)|) ^ k)) (Ioi (0 : ℝ)) :=
      (integrableOn_exp_mul_rpow_logpow_scaled hlam' htpos k).const_mul B
    refine h.congr_fun (fun x _ ↦ ?_) measurableSet_Ioi
    ring
  have hmono := setIntegral_mono_on hint hint2 measurableSet_Ioi fun ε hε ↦ by
    have hε : 0 < ε := hε
    have hεpow : 0 ≤ ε ^ lam := Real.rpow_nonneg hε.le _
    have hw : logWeight ε ^ k ≤ (1 + Real.log t) ^ k * (1 + |Real.log (t * ε)|) ^ k := by
      rw [← mul_pow]
      exact pow_le_pow_left₀ (logWeight_nonneg ε) (logWeight_le_mul ht hε) k
    calc Real.exp (-(t * ε)) * sublevelMass μ K ε
        ≤ Real.exp (-(t * ε)) * (A * ε ^ lam * logWeight ε ^ k) :=
          mul_le_mul_of_nonneg_left (hupper ε hε) (hg0 ε)
      _ ≤ Real.exp (-(t * ε)) * (A * ε ^ lam *
            ((1 + Real.log t) ^ k * (1 + |Real.log (t * ε)|) ^ k)) := by
          gcongr
      _ = Real.exp (-(t * ε)) * (B * (ε ^ lam * (1 + |Real.log (t * ε)|) ^ k)) := by
          rw [hB_def]
          ring
  have hval : ∫ ε in Ioi (0 : ℝ), Real.exp (-(t * ε)) *
      (B * (ε ^ lam * (1 + |Real.log (t * ε)|) ^ k)) =
      B * (t ^ (-(lam + 1)) * logKernelConst lam k) := by
    rw [← integral_exp_mul_rpow_logpow_scaled htpos k, ← integral_const_mul]
    refine setIntegral_congr_fun measurableSet_Ioi fun x _ ↦ ?_
    ring
  rw [hval] at hmono
  have hpow : t * t ^ (-(lam + 1)) = t ^ (-lam) := by
    rw [show -(lam + 1) = -lam + (-1) by ring, Real.rpow_add htpos, Real.rpow_neg_one]
    field_simp
  calc t * ∫ ε in Ioi (0 : ℝ), Real.exp (-(t * ε)) * sublevelMass μ K ε
      ≤ t * (B * (t ^ (-(lam + 1)) * logKernelConst lam k)) :=
        mul_le_mul_of_nonneg_left hmono htpos.le
    _ = B * logKernelConst lam k * (t * t ^ (-(lam + 1))) := by ring
    _ = A * logKernelConst lam k * t ^ (-lam) * (1 + Real.log t) ^ k := by
        rw [hpow, hB_def]
        ring

/-- **Abelian transfer with logarithmic multiplicity.** Two-sided bounds
`c₁ ε^λ (log 1/ε)^k ≤ μ{K ≤ ε} ≤ c₂ ε^λ (log 1/ε)^k` for `0 < ε ≤ ε₀ < 1`
give `C₁ t^{-λ} (log t)^k ≤ ∫ e^{-tK} dμ ≤ C₂ t^{-λ} (log t)^k` for large `t`. -/
theorem boltzmannMass_log_transfer (hK : Measurable K) (hK0 : ∀ x, 0 ≤ K x)
    {lam ε₀ c₁ c₂ : ℝ} (k : ℕ) (hlam : 0 < lam) (hε₀ : 0 < ε₀) (hε₀1 : ε₀ < 1)
    (hc₁ : 0 < c₁) (hc₂ : 0 < c₂)
    (hlower : ∀ ε : ℝ, 0 < ε → ε ≤ ε₀ →
      c₁ * ε ^ lam * (Real.log ε⁻¹) ^ k ≤ sublevelMass μ K ε)
    (hupper : ∀ ε : ℝ, 0 < ε → ε ≤ ε₀ →
      sublevelMass μ K ε ≤ c₂ * ε ^ lam * (Real.log ε⁻¹) ^ k) :
    ∃ C₁ C₂ : ℝ, 0 < C₁ ∧ 0 < C₂ ∧ ∀ᶠ t : ℝ in atTop,
      C₁ * t ^ (-lam) * (Real.log t) ^ k ≤ boltzmannMass μ K t ∧
      boltzmannMass μ K t ≤ C₂ * t ^ (-lam) * (Real.log t) ^ k := by
  obtain ⟨A, hA, hglob⟩ := exists_global_sublevel_logBound μ K k hlam hε₀ hε₀1 hc₂ hupper
  have hI : 0 ≤ logKernelConst lam k := logKernelConst_nonneg lam k
  refine ⟨Real.exp (-1) * c₁, A * (logKernelConst lam k + 1) * 2 ^ k,
    mul_pos (Real.exp_pos _) hc₁, by positivity, ?_⟩
  filter_upwards [eventually_ge_atTop (max (Real.exp 1) ε₀⁻¹)] with t ht
  have hte : Real.exp 1 ≤ t := le_trans (le_max_left _ _) ht
  have ht1 : 1 ≤ t := le_trans (by linarith [Real.add_one_le_exp (1 : ℝ)]) hte
  have htpos : 0 < t := lt_of_lt_of_le one_pos ht1
  have hlog1 : 1 ≤ Real.log t := by
    have := Real.log_le_log (Real.exp_pos 1) hte
    rwa [Real.log_exp] at this
  have hlog0 : 0 ≤ Real.log t := zero_le_one.trans hlog1
  have hinv : t⁻¹ ≤ ε₀ := by
    have : ε₀⁻¹ ≤ t := le_trans (le_max_right _ _) ht
    calc t⁻¹ ≤ (ε₀⁻¹)⁻¹ := inv_anti₀ (inv_pos.mpr hε₀) this
      _ = ε₀ := inv_inv ε₀
  constructor
  · have h := exp_mul_sublevelMass_le_boltzmannMass μ K hK hK0 htpos t⁻¹
    rw [mul_inv_cancel₀ htpos.ne'] at h
    have hF := hlower t⁻¹ (inv_pos.mpr htpos) hinv
    rw [Real.inv_rpow htpos.le, ← Real.rpow_neg htpos.le, inv_inv] at hF
    calc Real.exp (-1) * c₁ * t ^ (-lam) * (Real.log t) ^ k
        = Real.exp (-1) * (c₁ * t ^ (-lam) * (Real.log t) ^ k) := by ring
      _ ≤ Real.exp (-1) * sublevelMass μ K t⁻¹ :=
          mul_le_mul_of_nonneg_left hF (Real.exp_pos _).le
      _ ≤ boltzmannMass μ K t := h
  · have h := boltzmannMass_le_of_sublevel_logBound μ K hK hK0 hlam hA.le k hglob ht1
    have hlogpow : (1 + Real.log t) ^ k ≤ 2 ^ k * (Real.log t) ^ k := by
      rw [← mul_pow]
      exact pow_le_pow_left₀ (by linarith) (by linarith) k
    have htneg : 0 ≤ t ^ (-lam) := Real.rpow_nonneg htpos.le _
    calc boltzmannMass μ K t
        ≤ A * logKernelConst lam k * t ^ (-lam) * (1 + Real.log t) ^ k := h
      _ ≤ A * logKernelConst lam k * t ^ (-lam) * (2 ^ k * (Real.log t) ^ k) :=
          mul_le_mul_of_nonneg_left hlogpow (by positivity)
      _ ≤ A * (logKernelConst lam k + 1) * t ^ (-lam) * (2 ^ k * (Real.log t) ^ k) := by
          gcongr
          linarith
      _ = A * (logKernelConst lam k + 1) * 2 ^ k * t ^ (-lam) * (Real.log t) ^ k := by ring

end Laplace
