/-
Copyright (c) 2026 Timaeus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Laplace.Grammar.CandidateSupport

/-!
# Cutoff constants depending only on mass bounds (Stage 4e)

Unit 246 (Taylor-tree programme, Stage 4; Astra #28 §2.4 (III)). The constant of the quantitative
cutoff theorem (Headline XXV) is monotone in the data: the log majorant `M_{ν,r}(b)` is increasing
in
the phase parameter `b` (`phaseLogMoment_mono`) and the tail constant in `|b|` (`tailConst_mono`).
Hence for polynomial data with `ξ(0) = a`, `‖η‖₁ ≤ E`, `‖J‖₁ ≤ B` the cutoff constant is at most an
explicit `cutoffBound n k β L a E B` depending on the data only through `a, E, B`
(`taylorCutoffConst_le`), and Headline XXV holds with this uniform constant
(`taylorTree_cutoff_bound_uniform`) — the form in which it passes to the limit of truncations.
No `sorry` and no additional `axiom` declarations.
-/

open MeasureTheory Set Real Filter Topology

namespace Laplace.Grammar

open MonoRep

theorem logMajorant_mono (β : ℝ) (hβ : 0 < β) {b b' : ℝ} (hbb : b ≤ b') (ν : ℝ) (r p : ℕ) {t : ℝ}
    (ht : 0 ≤ t) : logMajorant β b ν r p t ≤ logMajorant β b' ν r p t := by
  unfold logMajorant phaseKernel
  refine mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left (Real.exp_le_exp.2 ?_)
    (pow_nonneg (Real.sqrt_nonneg _) _)) (by positivity)
  have : 0 ≤ β * Real.sqrt t := by positivity
  nlinarith

/-- `M_{ν,r,p}(b)` is increasing in `b`. -/
theorem phaseLogMoment_mono (β : ℝ) (hβ : 0 < β) {b b' : ℝ} (hbb : b ≤ b') {ν : ℝ} (hν : 0 < ν)
    (r p : ℕ) : phaseLogMoment β b ν r p ≤ phaseLogMoment β b' ν r p := by
  unfold phaseLogMoment
  exact setIntegral_mono_on (integrableOn_logMajorant β b ν hβ hν r p)
    (integrableOn_logMajorant β b' ν hβ hν r p) measurableSet_Ioi fun t ht =>
      logMajorant_mono β hβ hbb ν r p (mem_Ioi.1 ht).le

/-- `tailConst β b p ν i` is increasing in `|b|`. -/
theorem tailConst_mono (β : ℝ) (hβ : 0 < β) {b b' : ℝ} (hbb : |b| ≤ |b'|) (p : ℕ) (ν : ℝ)
    (i : ℕ) : tailConst β b p ν i ≤ tailConst β b' p ν i := by
  unfold tailConst
  refine mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (Real.exp_le_exp.2 ?_)
    (by positivity)) (by positivity)
  have : b ^ 2 ≤ b' ^ 2 := by
    rw [← sq_abs, ← sq_abs b']; exact pow_le_pow_left₀ (abs_nonneg _) hbb 2
  nlinarith

/-- The uniform cutoff constant: `highConst + tailSeriesConst` with `‖η‖₁ → E` and
`ξ(0) + ‖J‖₁ → |a| + B`. -/
noncomputable def cutoffBound (n : ℕ) (k : Fin (n + 1) → ℕ) (β L a E B : ℝ) : ℝ :=
  (∏ i, 1 / (2 * (k i : ℝ))) * E * (((n + 1).factorial : ℝ) * (latticeQ k : ℝ) ^ n) *
    (phaseLogMoment β (|a| + B) L n 0 +
      tailConst β (|a| + B) 0 L n * (4 / β) * ((⌈L⌉₊.factorial : ℝ) * (4 / β) ^ ⌈L⌉₊))

/-- The polynomial cutoff constant is at most the uniform bound. -/
theorem taylorCutoffConst_le (n : ℕ) (k : Fin (n + 1) → ℕ) (β : ℝ) (hβ : 0 < β) {L : ℝ}
    (hL : 0 < L) (ξ η : MonoRep (n + 1)) {a E B : ℝ} (ha : eval ξ 0 = a) (hE : l1 η ≤ E)
    (hB : l1 (fluct ξ) ≤ B) :
    taylorCutoffConst n k β L ξ η ≤ cutoffBound n k β L a E B := by
  have hK : 0 ≤ ∏ i, 1 / (2 * (k i : ℝ)) := Finset.prod_nonneg fun i _ => by positivity
  have hD : 0 ≤ ((n + 1).factorial : ℝ) * (latticeQ k : ℝ) ^ n := by positivity
  have hb : eval ξ 0 + l1 (fluct ξ) ≤ |a| + B := by
    have := le_abs_self (eval ξ 0); rw [ha] at this ⊢; linarith
  have hb' : |eval ξ 0 + l1 (fluct ξ)| ≤ |(|a| + B)| := by
    have h0 : 0 ≤ l1 (fluct ξ) := l1_nonneg _
    have hB0 : 0 ≤ B := h0.trans hB
    rw [abs_of_nonneg (by positivity : (0 : ℝ) ≤ |a| + B)]
    refine (abs_add_le _ _).trans ?_
    rw [abs_of_nonneg h0, ha]
    linarith
  have hM := phaseLogMoment_mono β hβ hb hL n 0
  have hT := tailConst_mono β hβ hb' 0 L n
  have hE0 : 0 ≤ E := (l1_nonneg η).trans hE
  unfold taylorCutoffConst highConst tailSeriesConst cutoffBound
  have h1 : (∏ i, 1 / (2 * (k i : ℝ))) * l1 η * (((n + 1).factorial : ℝ) * (latticeQ k : ℝ) ^ n) *
      phaseLogMoment β (eval ξ 0 + l1 (fluct ξ)) L n 0 ≤
      (∏ i, 1 / (2 * (k i : ℝ))) * E * (((n + 1).factorial : ℝ) * (latticeQ k : ℝ) ^ n) *
      phaseLogMoment β (|a| + B) L n 0 :=
    mul_le_mul (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hE hK) hD) hM
      (phaseLogMoment_nonneg _ _ _ _ _) (by positivity)
  have h2 : (∏ i, 1 / (2 * (k i : ℝ))) * l1 η * (((n + 1).factorial : ℝ) * (latticeQ k : ℝ) ^ n) *
      (tailConst β (eval ξ 0 + l1 (fluct ξ)) 0 L n * (4 / β) *
        ((⌈L⌉₊.factorial : ℝ) * (4 / β) ^ ⌈L⌉₊)) ≤
      (∏ i, 1 / (2 * (k i : ℝ))) * E * (((n + 1).factorial : ℝ) * (latticeQ k : ℝ) ^ n) *
      (tailConst β (|a| + B) 0 L n * (4 / β) * ((⌈L⌉₊.factorial : ℝ) * (4 / β) ^ ⌈L⌉₊)) :=
    mul_le_mul (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hE hK) hD)
      (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hT (by positivity)) (by positivity))
      (by have := tailConst_nonneg β (eval ξ 0 + l1 (fluct ξ)) hβ 0 L n; positivity) (by positivity)
  linarith

/-- **Headline XXV with a uniform constant**: for polynomial data with `ξ(0) = a`, `‖η‖₁ ≤ E`,
`‖J‖₁ ≤ B`, the remainder is at most `cutoffBound n k β L a E B · N^{-L}(1+log N)^n`. -/
theorem taylorTree_cutoff_bound_uniform (n : ℕ) (h k : Fin (n + 1) → ℕ) (hk : ∀ i, 0 < k i)
    (β : ℝ) (hβ : 0 < β) {L : ℝ} (hL : 0 < L) {N : ℝ} (hN : 1 ≤ N) (ξ η : MonoRep (n + 1))
    {a E B : ℝ} (ha : eval ξ 0 = a) (hE : l1 η ≤ E) (hB : l1 (fluct ξ) ≤ B) :
    |polyPhaseIntegral n h k β N ξ η - spectralSum n h k β L ξ η N| ≤
      cutoffBound n k β L a E B * (N ^ (-L) * (1 + Real.log N) ^ n) := by
  refine (taylorTree_cutoff_bound n h k hk β hβ hL hN ξ η).trans ?_
  exact mul_le_mul_of_nonneg_right (taylorCutoffConst_le n k β hβ hL ξ η ha hE hB)
    (mul_nonneg (Real.rpow_nonneg (by linarith) _)
      (pow_nonneg (by linarith [Real.log_nonneg hN]) _))

end Laplace.Grammar
