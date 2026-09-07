/-
Copyright (c) 2026 Timaeus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Laplace.Grammar.MomentInterchange

/-!
# Integrating a block expansion over noncritical parameters (grammar §4.2)

An abstract wrapper for the "equal-exponent block × noncritical coordinates" situation. A
parametrised family `Z_w(n)` of block integrals satisfies, for `n ≥ 1`,
`|Z_w(n) − n^{-p}(A(w) log n + B(w))| ≤ K(w) n^{-q}(1 + log n)` (`q = p + δ`) and, for `n < 1`,
`|Z_w(n)| ≤ G(w)`. If `0 < t(w) ≤ T` and the envelope `t^{-q}(G + K + |A| + |B|)` is `μ`-integrable
(the strict gap), then

  `∫ Z_w(N t(w)) dμ = N^{-p}(Ā log N + B̄) + O(N^{-q}(1 + log N))`,
  `Ā = ∫ t^{-p} A dμ`,  `B̄ = ∫ t^{-p}(B + A log t) dμ`.

The region `N t(w) < 1` is handled by subtracting the full local expression and the elementary
bound `n^{-p}|log n| ≤ n^{-q}/δ` for `n < 1`. The wrapper knows nothing about kernels or
decompositions. Zero `sorry`/`axiom`.
-/

open Real MeasureTheory Set Filter

namespace Laplace.Grammar

/-- `x^δ |log x| ≤ 1/δ` on `(0, 1]`. -/
theorem rpow_mul_abs_log_le (x δ : ℝ) (hx : 0 < x) (hx1 : x ≤ 1) (hδ : 0 < δ) :
    x ^ δ * |Real.log x| ≤ 1 / δ := by
  have hy : 0 < x ^ δ := Real.rpow_pos_of_pos hx δ
  have hy1 : x ^ δ ≤ 1 := Real.rpow_le_one hx.le hx1 hδ.le
  have h := Real.abs_log_mul_self_lt (x ^ δ) hy hy1
  rw [Real.log_rpow hx, abs_mul, abs_mul, abs_of_pos hδ, abs_of_pos hy] at h
  rw [le_div_iff₀ hδ]
  have : x ^ δ * |Real.log x| * δ = δ * |Real.log x| * x ^ δ := by ring
  linarith

/-- `t^{-p} ≤ T^δ t^{-(p+δ)}` on `(0, T]`. -/
theorem rpow_neg_le_shift (t T p δ : ℝ) (ht : 0 < t) (htT : t ≤ T) (hδ : 0 < δ) :
    t ^ (-p) ≤ T ^ δ * t ^ (-(p + δ)) := by
  rw [show -p = δ + -(p + δ) by ring, Real.rpow_add ht]
  exact mul_le_mul_of_nonneg_right (Real.rpow_le_rpow ht.le htT hδ.le) (Real.rpow_nonneg ht.le _)

/-- The constant bounding `t^δ |log t|` on `(0, T]`. -/
noncomputable def logShiftConst (T δ : ℝ) : ℝ := 1 / δ + T ^ δ * max 0 (Real.log T)

theorem logShiftConst_nonneg (T δ : ℝ) (hT : 0 ≤ T) (hδ : 0 < δ) : 0 ≤ logShiftConst T δ := by
  unfold logShiftConst
  have : 0 ≤ T ^ δ * max 0 (Real.log T) := mul_nonneg (Real.rpow_nonneg hT _) (le_max_left _ _)
  have : 0 ≤ 1 / δ := by positivity
  linarith

/-- `t^{-p} |log t| ≤ logShiftConst · t^{-(p+δ)}` on `(0, T]`. -/
theorem rpow_neg_mul_abs_log_le_shift (t T p δ : ℝ) (ht : 0 < t) (htT : t ≤ T) (hδ : 0 < δ) :
    t ^ (-p) * |Real.log t| ≤ logShiftConst T δ * t ^ (-(p + δ)) := by
  have hT : 0 < T := lt_of_lt_of_le ht htT
  have hq0 : 0 ≤ t ^ (-(p + δ)) := Real.rpow_nonneg ht.le _
  have h2 : 0 ≤ T ^ δ * max 0 (Real.log T) :=
    mul_nonneg (Real.rpow_nonneg hT.le _) (le_max_left _ _)
  have h1δ : 0 ≤ 1 / δ := by positivity
  rw [show -p = δ + -(p + δ) by ring, Real.rpow_add ht]
  unfold logShiftConst
  rcases le_or_gt t 1 with h1 | h1
  · have := rpow_mul_abs_log_le t δ ht h1 hδ
    calc t ^ δ * t ^ (-(p + δ)) * |Real.log t| = (t ^ δ * |Real.log t|) * t ^ (-(p + δ)) := by ring
      _ ≤ (1 / δ) * t ^ (-(p + δ)) := mul_le_mul_of_nonneg_right this hq0
      _ ≤ _ := mul_le_mul_of_nonneg_right (by linarith) hq0
  · have hlog : |Real.log t| = Real.log t := abs_of_pos (Real.log_pos h1)
    have hlogT : Real.log t ≤ max 0 (Real.log T) :=
      (Real.log_le_log ht htT).trans (le_max_right _ _)
    have htδ : t ^ δ ≤ T ^ δ := Real.rpow_le_rpow ht.le htT hδ.le
    calc t ^ δ * t ^ (-(p + δ)) * |Real.log t| = (t ^ δ * Real.log t) * t ^ (-(p + δ)) := by
          rw [hlog]; ring
      _ ≤ (T ^ δ * max 0 (Real.log T)) * t ^ (-(p + δ)) :=
          mul_le_mul_of_nonneg_right (mul_le_mul htδ hlogT (Real.log_pos h1).le
            (Real.rpow_nonneg hT.le _)) hq0
      _ ≤ _ := mul_le_mul_of_nonneg_right (by linarith) hq0

/-- The constant of the pointwise parameter bound. -/
noncomputable def paramConst (T δ : ℝ) : ℝ := 1 + max 0 (Real.log T) + 1 / δ

/-- **Pointwise bound for one parameter value**: for `N ≥ 1` and `0 < t ≤ T`, the deviation of
`Z(Nt)` from the full local expression is `O(N^{-q}(1+log N) t^{-q}(G+K+|A|+|B|))`, in both the
regions `Nt ≥ 1` and `Nt < 1`. -/
theorem param_pointwise_bound (Z : ℝ → ℝ) (A B K G t T p δ N : ℝ) (hδ : 0 < δ) (hp : 0 ≤ p)
    (ht : 0 < t) (htT : t ≤ T) (hN : 1 ≤ N) (hK : 0 ≤ K) (hG : 0 ≤ G)
    (hexp : ∀ n, 1 ≤ n →
      |Z n - n ^ (-p) * (A * Real.log n + B)| ≤ K * n ^ (-(p + δ)) * (1 + Real.log n))
    (hsmall : ∀ n, 0 < n → n < 1 → |Z n| ≤ G) :
    |Z (N * t) - N ^ (-p) * (t ^ (-p) * A * Real.log N + t ^ (-p) * (B + A * Real.log t))|
      ≤ N ^ (-(p + δ)) * (1 + Real.log N)
        * (paramConst T δ * (t ^ (-(p + δ)) * (G + K + |A| + |B|))) := by
  set n := N * t with hn
  have hN0 : 0 < N := by linarith
  have hn0 : 0 < n := by positivity
  have hlogN : 0 ≤ Real.log N := Real.log_nonneg hN
  have hLT : 0 ≤ max 0 (Real.log T) := le_max_left _ _
  have h1δ : 0 ≤ 1 / δ := by positivity
  have hM1 : 1 ≤ paramConst T δ := by unfold paramConst; linarith
  have hMδ : 1 / δ ≤ paramConst T δ := by unfold paramConst; linarith
  have hMT : 1 + max 0 (Real.log T) ≤ paramConst T δ := by unfold paramConst; linarith
  have hM0 : 0 ≤ paramConst T δ := by linarith
  have hnp : n ^ (-p) = N ^ (-p) * t ^ (-p) := by rw [hn, Real.mul_rpow hN0.le ht.le]
  have hnq : n ^ (-(p + δ)) = N ^ (-(p + δ)) * t ^ (-(p + δ)) := by
    rw [hn, Real.mul_rpow hN0.le ht.le]
  have hlogn : Real.log n = Real.log N + Real.log t := by rw [hn, Real.log_mul hN0.ne' ht.ne']
  have hid : N ^ (-p) * (t ^ (-p) * A * Real.log N + t ^ (-p) * (B + A * Real.log t))
      = n ^ (-p) * (A * Real.log n + B) := by
    rw [hnp, hlogn]; ring
  rw [hid]
  have hE : 0 ≤ G + K + |A| + |B| := by positivity
  have hq0 : 0 ≤ t ^ (-(p + δ)) := Real.rpow_nonneg ht.le _
  have hNq : 0 ≤ N ^ (-(p + δ)) := Real.rpow_nonneg hN0.le _
  have h1N : 1 ≤ 1 + Real.log N := by linarith
  rcases le_or_gt 1 n with h1 | h1
  · -- the region `n ≥ 1`
    have hlt : Real.log t ≤ max 0 (Real.log T) :=
      (Real.log_le_log ht htT).trans (le_max_right _ _)
    have hbound : 1 + Real.log n ≤ paramConst T δ * (1 + Real.log N) := by
      rw [hlogn]
      calc 1 + (Real.log N + Real.log t) ≤ (1 + max 0 (Real.log T)) * (1 + Real.log N) := by
            nlinarith
        _ ≤ _ := mul_le_mul_of_nonneg_right hMT (by linarith)
    have hKq : 0 ≤ K * n ^ (-(p + δ)) := mul_nonneg hK (Real.rpow_nonneg hn0.le _)
    calc |Z n - n ^ (-p) * (A * Real.log n + B)|
        ≤ K * n ^ (-(p + δ)) * (1 + Real.log n) := hexp n h1
      _ ≤ K * n ^ (-(p + δ)) * (paramConst T δ * (1 + Real.log N)) :=
          mul_le_mul_of_nonneg_left hbound hKq
      _ = N ^ (-(p + δ)) * (1 + Real.log N) * (paramConst T δ * (t ^ (-(p + δ)) * K)) := by
          rw [hnq]; ring
      _ ≤ _ := by
          gcongr
          linarith [abs_nonneg A, abs_nonneg B]
  · -- the region `n < 1`
    have hnq1 : 1 ≤ n ^ (-(p + δ)) := by
      have := Real.rpow_le_rpow_of_exponent_ge hn0 h1.le (by linarith : -(p + δ) ≤ 0)
      rwa [Real.rpow_zero] at this
    have hnpq : n ^ (-p) ≤ n ^ (-(p + δ)) :=
      Real.rpow_le_rpow_of_exponent_ge hn0 h1.le (by linarith)
    have hnq0 : 0 ≤ n ^ (-(p + δ)) := Real.rpow_nonneg hn0.le _
    have hlogbound : n ^ (-p) * |Real.log n| ≤ (1 / δ) * n ^ (-(p + δ)) := by
      have := rpow_mul_abs_log_le n δ hn0 h1.le hδ
      rw [show -p = δ + -(p + δ) by ring, Real.rpow_add hn0]
      calc n ^ δ * n ^ (-(p + δ)) * |Real.log n| = (n ^ δ * |Real.log n|) * n ^ (-(p + δ)) := by
            ring
        _ ≤ _ := mul_le_mul_of_nonneg_right this hnq0
    have hZ := hsmall n hn0 h1
    have hnp0 : 0 ≤ n ^ (-p) := Real.rpow_nonneg hn0.le _
    have hAlog : |A * Real.log n + B| ≤ |A| * |Real.log n| + |B| :=
      (abs_add_le _ _).trans (by rw [abs_mul])
    have hA' : n ^ (-p) * |Real.log n| * |A| ≤ (1 / δ) * n ^ (-(p + δ)) * |A| :=
      mul_le_mul_of_nonneg_right hlogbound (abs_nonneg _)
    have hB' : n ^ (-p) * |B| ≤ n ^ (-(p + δ)) * |B| :=
      mul_le_mul_of_nonneg_right hnpq (abs_nonneg _)
    have hG' : G ≤ paramConst T δ * n ^ (-(p + δ)) * G := by
      calc G = 1 * 1 * G := by ring
        _ ≤ paramConst T δ * n ^ (-(p + δ)) * G := by gcongr
    have hA'' : (1 / δ) * n ^ (-(p + δ)) * |A| ≤ paramConst T δ * n ^ (-(p + δ)) * |A| := by
      gcongr
    have hB'' : n ^ (-(p + δ)) * |B| ≤ paramConst T δ * n ^ (-(p + δ)) * |B| := by
      calc n ^ (-(p + δ)) * |B| = 1 * n ^ (-(p + δ)) * |B| := by ring
        _ ≤ _ := by gcongr
    have hK' : 0 ≤ paramConst T δ * n ^ (-(p + δ)) * K := by positivity
    calc |Z n - n ^ (-p) * (A * Real.log n + B)|
        ≤ |Z n| + n ^ (-p) * |A * Real.log n + B| := by
          refine (abs_sub _ _).trans ?_
          rw [abs_mul, abs_of_nonneg hnp0]
      _ ≤ G + n ^ (-p) * (|A| * |Real.log n| + |B|) := by gcongr
      _ = G + (n ^ (-p) * |Real.log n| * |A| + n ^ (-p) * |B|) := by ring
      _ ≤ paramConst T δ * n ^ (-(p + δ)) * (G + K + |A| + |B|) := by linarith
      _ = N ^ (-(p + δ)) * 1 * (paramConst T δ * (t ^ (-(p + δ)) * (G + K + |A| + |B|))) := by
          rw [hnq]; ring
      _ ≤ _ := by gcongr

/-- **Integration over noncritical parameters with a strict gap.** -/
theorem param_integration {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    (Z : Ω → ℝ → ℝ) (A B K G t : Ω → ℝ) (T p δ : ℝ) (hδ : 0 < δ) (hp : 0 ≤ p) (hT : 0 ≤ T)
    (htm : Measurable t) (hAm : AEStronglyMeasurable A μ) (hBm : AEStronglyMeasurable B μ)
    (hZm : ∀ N : ℝ, AEStronglyMeasurable (fun w => Z w (N * t w)) μ)
    (ht : ∀ᵐ w ∂μ, 0 < t w ∧ t w ≤ T)
    (hKG : ∀ᵐ w ∂μ, 0 ≤ K w ∧ 0 ≤ G w)
    (hexp : ∀ᵐ w ∂μ, ∀ n, 1 ≤ n →
      |Z w n - n ^ (-p) * (A w * Real.log n + B w)| ≤ K w * n ^ (-(p + δ)) * (1 + Real.log n))
    (hsmall : ∀ᵐ w ∂μ, ∀ n, 0 < n → n < 1 → |Z w n| ≤ G w)
    (hE : Integrable (fun w => t w ^ (-(p + δ)) * (G w + K w + |A w| + |B w|)) μ) :
    ∃ C : ℝ, ∀ N : ℝ, 1 ≤ N →
      |(∫ w, Z w (N * t w) ∂μ)
          - N ^ (-p) * ((∫ w, t w ^ (-p) * A w ∂μ) * Real.log N
              + ∫ w, t w ^ (-p) * (B w + A w * Real.log (t w)) ∂μ)|
        ≤ C * N ^ (-(p + δ)) * (1 + Real.log N) := by
  set E : Ω → ℝ := fun w => t w ^ (-(p + δ)) * (G w + K w + |A w| + |B w|) with hEdef
  have hE0 : ∀ᵐ w ∂μ, 0 ≤ E w := by
    filter_upwards [ht, hKG] with w hw hKGw
    simp only [hEdef]
    have h1 := Real.rpow_nonneg hw.1.le (-(p + δ))
    have h2 : 0 ≤ G w + K w + |A w| + |B w| := by
      linarith [hKGw.1, hKGw.2, abs_nonneg (A w), abs_nonneg (B w)]
    exact mul_nonneg h1 h2
  set Tδ : ℝ := T ^ δ with hTδ
  have hTδ0 : 0 ≤ Tδ := Real.rpow_nonneg hT _
  set D₂ : ℝ := logShiftConst T δ with hD₂
  have hD₂0 : 0 ≤ D₂ := logShiftConst_nonneg T δ hT hδ
  -- integrability of the two coefficient integrands
  have hg₁m : AEStronglyMeasurable (fun w => t w ^ (-p) * A w) μ :=
    (htm.pow_const _).aestronglyMeasurable.mul hAm
  have hg₂m : AEStronglyMeasurable (fun w => t w ^ (-p) * (B w + A w * Real.log (t w))) μ :=
    (htm.pow_const _).aestronglyMeasurable.mul
      (hBm.add (hAm.mul (Real.measurable_log.comp htm).aestronglyMeasurable))
  have hg₁ : Integrable (fun w => t w ^ (-p) * A w) μ := by
    refine Integrable.mono' (hE.const_mul Tδ) hg₁m ?_
    filter_upwards [ht, hKG] with w hw hKGw
    rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (Real.rpow_nonneg hw.1.le _)]
    have h1 := rpow_neg_le_shift (t w) T p δ hw.1 hw.2 hδ
    have hq0 : 0 ≤ t w ^ (-(p + δ)) := Real.rpow_nonneg hw.1.le _
    calc t w ^ (-p) * |A w| ≤ Tδ * t w ^ (-(p + δ)) * |A w| :=
          mul_le_mul_of_nonneg_right h1 (abs_nonneg _)
      _ ≤ Tδ * (t w ^ (-(p + δ)) * (G w + K w + |A w| + |B w|)) := by
          rw [mul_assoc]
          refine mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left ?_ hq0) hTδ0
          linarith [hKGw.1, hKGw.2, abs_nonneg (B w)]
  have hg₂ : Integrable (fun w => t w ^ (-p) * (B w + A w * Real.log (t w))) μ := by
    refine Integrable.mono' (hE.const_mul (Tδ + D₂)) hg₂m ?_
    filter_upwards [ht, hKG] with w hw hKGw
    rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (Real.rpow_nonneg hw.1.le _)]
    have h1 := rpow_neg_le_shift (t w) T p δ hw.1 hw.2 hδ
    have h2 := rpow_neg_mul_abs_log_le_shift (t w) T p δ hw.1 hw.2 hδ
    have hq0 : 0 ≤ t w ^ (-(p + δ)) := Real.rpow_nonneg hw.1.le _
    have hp0 : 0 ≤ t w ^ (-p) := Real.rpow_nonneg hw.1.le _
    have hsum : |B w + A w * Real.log (t w)| ≤ |B w| + |A w| * |Real.log (t w)| :=
      (abs_add_le _ _).trans (by rw [abs_mul])
    calc t w ^ (-p) * |B w + A w * Real.log (t w)|
        ≤ t w ^ (-p) * (|B w| + |A w| * |Real.log (t w)|) :=
          mul_le_mul_of_nonneg_left hsum hp0
      _ = t w ^ (-p) * |B w| + (t w ^ (-p) * |Real.log (t w)|) * |A w| := by ring
      _ ≤ Tδ * t w ^ (-(p + δ)) * |B w| + (D₂ * t w ^ (-(p + δ))) * |A w| := by
          gcongr
      _ ≤ (Tδ + D₂) * (t w ^ (-(p + δ)) * (G w + K w + |A w| + |B w|)) := by
          have e1 : Tδ * t w ^ (-(p + δ)) * |B w|
              ≤ Tδ * (t w ^ (-(p + δ)) * (G w + K w + |A w| + |B w|)) := by
            rw [mul_assoc]
            refine mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left ?_ hq0) hTδ0
            linarith [hKGw.1, hKGw.2, abs_nonneg (A w)]
          have e2 : D₂ * t w ^ (-(p + δ)) * |A w|
              ≤ D₂ * (t w ^ (-(p + δ)) * (G w + K w + |A w| + |B w|)) := by
            rw [mul_assoc]
            refine mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left ?_ hq0) hD₂0
            linarith [hKGw.1, hKGw.2, abs_nonneg (B w)]
          linarith
  -- the constant
  refine ⟨paramConst T δ * ∫ w, E w ∂μ, fun N hN => ?_⟩
  have hN0 : 0 < N := by linarith
  have hlogN : 0 ≤ Real.log N := Real.log_nonneg hN
  have hNq : 0 ≤ N ^ (-(p + δ)) := Real.rpow_nonneg hN0.le _
  have hNp : 0 ≤ N ^ (-p) := Real.rpow_nonneg hN0.le _
  have h1δ : 0 ≤ 1 / δ := by positivity
  have hM0 : 0 ≤ paramConst T δ := by
    unfold paramConst
    have := le_max_left (0 : ℝ) (Real.log T)
    linarith
  set c₁ : ℝ := N ^ (-(p + δ)) * (1 + Real.log N) * paramConst T δ with hc₁
  have hc₁0 : 0 ≤ c₁ := by positivity
  -- the pointwise bound
  have hpt : ∀ᵐ w ∂μ, |Z w (N * t w)
      - (N ^ (-p) * Real.log N * (t w ^ (-p) * A w)
        + N ^ (-p) * (t w ^ (-p) * (B w + A w * Real.log (t w))))| ≤ c₁ * E w := by
    filter_upwards [ht, hKG, hexp, hsmall] with w hw hKGw hexpw hsmallw
    have := param_pointwise_bound (Z w) (A w) (B w) (K w) (G w) (t w) T p δ N hδ hp hw.1 hw.2 hN
      hKGw.1 hKGw.2 hexpw hsmallw
    rw [show N ^ (-p) * Real.log N * (t w ^ (-p) * A w)
        + N ^ (-p) * (t w ^ (-p) * (B w + A w * Real.log (t w)))
        = N ^ (-p) * (t w ^ (-p) * A w * Real.log N + t w ^ (-p) * (B w + A w * Real.log (t w)))
      by ring]
    refine this.trans (le_of_eq ?_)
    simp only [hc₁, hEdef]
    ring
  -- integrability of the scaled block
  have hg : Integrable (fun w => N ^ (-p) * Real.log N * (t w ^ (-p) * A w)
      + N ^ (-p) * (t w ^ (-p) * (B w + A w * Real.log (t w)))) μ :=
    (hg₁.const_mul _).add (hg₂.const_mul _)
  have hf : Integrable (fun w => Z w (N * t w)) μ := by
    have hdiff : Integrable (fun w => Z w (N * t w)
        - (N ^ (-p) * Real.log N * (t w ^ (-p) * A w)
          + N ^ (-p) * (t w ^ (-p) * (B w + A w * Real.log (t w))))) μ := by
      refine Integrable.mono' (hE.const_mul c₁) ((hZm N).sub hg.aestronglyMeasurable) ?_
      filter_upwards [hpt] with w hw
      rwa [Real.norm_eq_abs]
    have := hdiff.add hg
    refine this.congr (Filter.Eventually.of_forall fun w => ?_)
    simp
  -- assemble
  have hint : ∫ w, Z w (N * t w) ∂μ
      - N ^ (-p) * ((∫ w, t w ^ (-p) * A w ∂μ) * Real.log N
          + ∫ w, t w ^ (-p) * (B w + A w * Real.log (t w)) ∂μ)
      = ∫ w, (Z w (N * t w)
          - (N ^ (-p) * Real.log N * (t w ^ (-p) * A w)
            + N ^ (-p) * (t w ^ (-p) * (B w + A w * Real.log (t w))))) ∂μ := by
    rw [integral_sub hf hg, integral_add (hg₁.const_mul _) (hg₂.const_mul _), integral_const_mul,
      integral_const_mul]
    ring
  rw [hint]
  have hbound := norm_integral_le_of_norm_le (hE.const_mul c₁)
    (hpt.mono fun w hw => by rw [Real.norm_eq_abs]; exact hw)
  rw [Real.norm_eq_abs, integral_const_mul] at hbound
  refine hbound.trans (le_of_eq ?_)
  simp only [hc₁]
  ring

end Laplace.Grammar
