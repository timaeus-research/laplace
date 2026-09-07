/-
Copyright (c) 2026 Timaeus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Laplace.Grammar.PhaseShiftedTerm

/-!
# The phase-dressed normal moment

Unit 201 (programme A, step 3). The one-dimensional normal moment dressed by a constant phase `a`,
`phaseMoment β p a = S^{(β)}_{p/2}(a) = ∫₀^∞ s^{p-1} e^{-βs² + βas} ds`
(`quadKernel β a s = e^{-βs²+βas}`; this is the paper's `J_p(a) = S_{p/2}(a)/2`, since the
paper's `S_λ(a) = ∫₀^∞ t^{λ-1} e^{-βt+βa√t} dt` is `2 phaseMoment β (2λ) a` under `t = s²`), with:

* integrability and the Gaussian domination
  `s^{p-1} quadKernel β a s ≤ e^{βR²/2} s^{p-1} e^{-βs²/2}` for `|a| ≤ R`
  (`phaseMoment_integrand_le`);
* continuity in the phase `a` (`continuous_phaseMoment`, dominated convergence on a ball);
* the Gaussian moments `∫₀^∞ s^{p-1} s^j e^{-βs²} ds = Γ(p/2 + j/2) β^{-(p/2+j/2)} / 2`
  (`gaussMoment_nat_eq`) and the zero-phase value `phaseMoment β p 0 = Γ(p/2)β^{-p/2}/2`;
* the **finite Taylor approximation** (`phaseMoment_taylor_le`): for `|βa| ≤ b`,
  `|S(a) - Σ_{j<2K} (βa)^j/j! · Γ(p/2+j/2)β^{-(p/2+j/2)}/2| ≤ tailCoeff β b K · gaussTail β p`,
  `gaussTail β p = ∫₀^∞ s^{p-1} e^{-βs²/4} ds`, with the uniform tail constant of unit 199.

Zero `sorry`/`axiom`.
-/

open MeasureTheory Filter Topology Real Set

namespace Laplace.Grammar

/-- `S^{(β)}_{p/2}(a) = ∫₀^∞ s^{p-1} e^{-βs² + βas} ds` (the paper's `J_p(a) = S_{p/2}(a)/2`). -/
noncomputable def phaseMoment (β p a : ℝ) : ℝ :=
  ∫ s in Ioi (0 : ℝ), s ^ (p - 1) * quadKernel β a s

/-- `∫₀^∞ s^{p-1} e^{-βs²/4} ds`, the Gaussian envelope of the tail. -/
noncomputable def gaussTail (β p : ℝ) : ℝ :=
  ∫ s in Ioi (0 : ℝ), s ^ (p - 1) * Real.exp (-(β / 4 * s ^ 2))

theorem gauss_integrableOn (c q : ℝ) (hc : 0 < c) (hq : -1 < q) :
    IntegrableOn (fun s : ℝ => s ^ q * Real.exp (-(c * s ^ 2))) (Ioi 0) := by
  refine (integrableOn_rpow_mul_exp_neg_mul_sq hc hq).congr_fun (fun s _ => ?_) measurableSet_Ioi
  simp only [neg_mul]

/-- Uniform Gaussian domination of the dressed kernel for `|a| ≤ R`, `s ≥ 0`. -/
theorem quadKernel_le_of_abs_le (β a R s : ℝ) (hβ : 0 < β) (hs : 0 ≤ s) (haR : |a| ≤ R) :
    quadKernel β a s ≤ Real.exp (β * R ^ 2 / 2) * Real.exp (-(β / 2 * s ^ 2)) := by
  unfold quadKernel
  have h1 : -β * s ^ 2 + β * a * s ≤ (β * R) * s - β * s ^ 2 := by
    have haR' : a ≤ R := (le_abs_self a).trans haR
    have := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left haR' hβ.le) hs
    linarith
  calc Real.exp (-β * s ^ 2 + β * a * s) ≤ Real.exp ((β * R) * s - β * s ^ 2) :=
        Real.exp_le_exp.2 h1
    _ ≤ Real.exp ((β * R) ^ 2 / (2 * β)) * Real.exp (-(β / 2 * s ^ 2)) :=
        exp_linear_sub_sq_le β (β * R) s hβ
    _ = Real.exp (β * R ^ 2 / 2) * Real.exp (-(β / 2 * s ^ 2)) := by
        rw [show (β * R) ^ 2 / (2 * β) = β * R ^ 2 / 2 by field_simp]

theorem phaseMoment_integrand_aestronglyMeasurable (β p a : ℝ) :
    AEStronglyMeasurable (fun s : ℝ => s ^ (p - 1) * quadKernel β a s)
      (volume.restrict (Ioi (0 : ℝ))) :=
  ((continuousOn_id.rpow_const fun _ hs => Or.inl (ne_of_gt hs)).mul
    (quadKernel_continuous β a).continuousOn).aestronglyMeasurable measurableSet_Ioi

theorem phaseMoment_integrand_le (β p a R s : ℝ) (hβ : 0 < β) (hs : 0 < s) (haR : |a| ≤ R) :
    ‖s ^ (p - 1) * quadKernel β a s‖ ≤
      Real.exp (β * R ^ 2 / 2) * (s ^ (p - 1) * Real.exp (-(β / 2 * s ^ 2))) := by
  rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (Real.rpow_nonneg hs.le _),
    abs_of_pos (quadKernel_pos β a s)]
  calc s ^ (p - 1) * quadKernel β a s
      ≤ s ^ (p - 1) * (Real.exp (β * R ^ 2 / 2) * Real.exp (-(β / 2 * s ^ 2))) :=
        mul_le_mul_of_nonneg_left (quadKernel_le_of_abs_le β a R s hβ hs.le haR)
          (Real.rpow_nonneg hs.le _)
    _ = Real.exp (β * R ^ 2 / 2) * (s ^ (p - 1) * Real.exp (-(β / 2 * s ^ 2))) := by ring

theorem phaseMoment_integrand_integrableOn (β p a : ℝ) (hβ : 0 < β) (hp : 0 < p) :
    IntegrableOn (fun s : ℝ => s ^ (p - 1) * quadKernel β a s) (Ioi 0) := by
  refine Integrable.mono' ((gauss_integrableOn (β / 2) (p - 1) (by positivity)
    (by linarith)).const_mul (Real.exp (β * |a| ^ 2 / 2)))
    (phaseMoment_integrand_aestronglyMeasurable β p a) ?_
  refine (ae_restrict_iff' measurableSet_Ioi).2 (Eventually.of_forall fun s hs => ?_)
  exact phaseMoment_integrand_le β p a |a| s hβ hs le_rfl

/-- The dressed normal moment is continuous in the phase. -/
theorem continuous_phaseMoment (β p : ℝ) (hβ : 0 < β) (hp : 0 < p) :
    Continuous fun a => phaseMoment β p a := by
  refine continuous_iff_continuousAt.2 fun a₀ => ?_
  unfold phaseMoment
  have hnhds : ∀ᶠ a in 𝓝 a₀, |a| ≤ |a₀| + 1 := by
    have hball : ∀ᶠ a in 𝓝 a₀, a ∈ Metric.ball a₀ 1 := Metric.ball_mem_nhds a₀ one_pos
    refine hball.mono fun a ha => ?_
    rw [Metric.mem_ball, Real.dist_eq] at ha
    have := abs_sub_abs_le_abs_sub a a₀
    linarith
  refine continuousAt_of_dominated (bound := fun s => Real.exp (β * (|a₀| + 1) ^ 2 / 2) *
    (s ^ (p - 1) * Real.exp (-(β / 2 * s ^ 2)))) ?_ ?_ ?_ ?_
  · exact Eventually.of_forall fun a => phaseMoment_integrand_aestronglyMeasurable β p a
  · filter_upwards [hnhds] with a ha
    refine (ae_restrict_iff' measurableSet_Ioi).2 (Eventually.of_forall fun s hs => ?_)
    exact phaseMoment_integrand_le β p a (|a₀| + 1) s hβ hs ha
  · exact (gauss_integrableOn (β / 2) (p - 1) (by positivity) (by linarith)).const_mul _
  · refine Eventually.of_forall fun s => ?_
    have : Continuous fun a => s ^ (p - 1) * quadKernel β a s := by
      unfold quadKernel
      fun_prop
    exact this.continuousAt

/-- Gaussian moments: `∫₀^∞ s^q e^{-βs²} ds = Γ((q+1)/2) β^{-(q+1)/2} / 2`. -/
theorem gaussMoment_eq (β q : ℝ) (hβ : 0 < β) (hq : -1 < q) :
    ∫ s in Ioi (0 : ℝ), s ^ q * Real.exp (-(β * s ^ 2)) =
      Real.Gamma ((q + 1) / 2) * β ^ (-((q + 1) / 2)) / 2 := by
  have h := integral_rpow_mul_exp_neg_mul_rpow (p := 2) (q := q) (b := β) two_pos hq hβ
  have hcongr : ∫ s in Ioi (0 : ℝ), s ^ q * Real.exp (-(β * s ^ 2)) =
      ∫ x in Ioi (0 : ℝ), x ^ q * Real.exp (-β * x ^ (2 : ℝ)) := by
    refine setIntegral_congr_fun measurableSet_Ioi fun s _ => ?_
    rw [Real.rpow_two, neg_mul]
  rw [hcongr, h, neg_div]
  ring

/-- `∫₀^∞ s^{p-1} s^j e^{-βs²} ds = Γ(p/2 + j/2) β^{-(p/2 + j/2)} / 2`. -/
theorem gaussMoment_nat_eq (β p : ℝ) (j : ℕ) (hβ : 0 < β) (hp : 0 < p) :
    ∫ s in Ioi (0 : ℝ), s ^ (p - 1) * (s ^ j * Real.exp (-(β * s ^ 2))) =
      Real.Gamma (p / 2 + j / 2) * β ^ (-(p / 2 + j / 2)) / 2 := by
  have hj : (0 : ℝ) ≤ j := Nat.cast_nonneg j
  have h := gaussMoment_eq β (p - 1 + j) hβ (by linarith)
  have hcongr : ∫ s in Ioi (0 : ℝ), s ^ (p - 1) * (s ^ j * Real.exp (-(β * s ^ 2))) =
      ∫ s in Ioi (0 : ℝ), s ^ (p - 1 + j) * Real.exp (-(β * s ^ 2)) := by
    refine setIntegral_congr_fun measurableSet_Ioi fun s hs => ?_
    have hs0 : (0 : ℝ) < s := hs
    rw [Real.rpow_add_natCast hs0.ne', mul_assoc]
  rw [hcongr, h, show (p - 1 + j + 1) / 2 = p / 2 + j / 2 by ring]

/-- Zero phase: `S^{(β)}_{p/2}(0) = Γ(p/2) β^{-p/2} / 2`. -/
theorem phaseMoment_zero (β p : ℝ) (hβ : 0 < β) (hp : 0 < p) :
    phaseMoment β p 0 = Real.Gamma (p / 2) * β ^ (-(p / 2)) / 2 := by
  have h := gaussMoment_nat_eq β p 0 hβ hp
  simp only [pow_zero, one_mul, Nat.cast_zero, zero_div, add_zero] at h
  rw [← h]
  unfold phaseMoment quadKernel
  refine setIntegral_congr_fun measurableSet_Ioi fun s _ => ?_
  simp only [mul_zero, zero_mul, add_zero, neg_mul]

theorem gaussTail_integrand_integrableOn (β p : ℝ) (hβ : 0 < β) (hp : 0 < p) :
    IntegrableOn (fun s : ℝ => s ^ (p - 1) * Real.exp (-(β / 4 * s ^ 2))) (Ioi 0) :=
  gauss_integrableOn (β / 4) (p - 1) (by positivity) (by linarith)

/-- **Finite Taylor approximation of the dressed normal moment**, with the uniform tail of
`phase_tail_le`: for `|βa| ≤ b`,
`|S(a) - Σ_{j<2K} (βa)^j/j! Γ(p/2+j/2)β^{-(p/2+j/2)}/2| ≤ tailCoeff β b K · gaussTail β p`. -/
theorem phaseMoment_taylor_le (β p a b : ℝ) (hβ : 0 < β) (hp : 0 < p) (hab : |β * a| ≤ b)
    (K : ℕ) :
    |phaseMoment β p a - ∑ j ∈ Finset.range (2 * K), (β * a) ^ j / (j.factorial : ℝ) *
        (Real.Gamma (p / 2 + j / 2) * β ^ (-(p / 2 + j / 2)) / 2)| ≤
      tailCoeff β b K * gaussTail β p := by
  have hterm : ∀ j : ℕ, (β * a) ^ j / (j.factorial : ℝ) *
      (Real.Gamma (p / 2 + j / 2) * β ^ (-(p / 2 + j / 2)) / 2) =
      ∫ s in Ioi (0 : ℝ), s ^ (p - 1) *
        ((s * (β * a)) ^ j / (j.factorial : ℝ) * Real.exp (-(β * s ^ 2))) := by
    intro j
    rw [← gaussMoment_nat_eq β p j hβ hp, ← integral_const_mul]
    refine setIntegral_congr_fun measurableSet_Ioi fun s _ => ?_
    rw [mul_pow]
    ring
  have hint_j : ∀ j : ℕ, IntegrableOn (fun s : ℝ => s ^ (p - 1) *
      ((s * (β * a)) ^ j / (j.factorial : ℝ) * Real.exp (-(β * s ^ 2)))) (Ioi 0) := by
    intro j
    have hj : (0 : ℝ) ≤ j := Nat.cast_nonneg j
    have hf : IntegrableOn (fun s : ℝ => (β * a) ^ j / (j.factorial : ℝ) *
        (s ^ (p - 1 + j) * Real.exp (-(β * s ^ 2)))) (Ioi 0) :=
      (gauss_integrableOn β (p - 1 + j) hβ (by linarith)).const_mul _
    refine hf.congr_fun (fun s hs => ?_) measurableSet_Ioi
    have hs0 : (0 : ℝ) < s := hs
    beta_reduce
    rw [Real.rpow_add_natCast hs0.ne', mul_pow]
    ring
  have hsum : ∑ j ∈ Finset.range (2 * K), (β * a) ^ j / (j.factorial : ℝ) *
      (Real.Gamma (p / 2 + j / 2) * β ^ (-(p / 2 + j / 2)) / 2) =
      ∫ s in Ioi (0 : ℝ), s ^ (p - 1) *
        ((∑ j ∈ Finset.range (2 * K), (s * (β * a)) ^ j / (j.factorial : ℝ)) *
          Real.exp (-(β * s ^ 2))) := by
    rw [Finset.sum_congr rfl fun j _ => hterm j, ← integral_finsetSum _ fun j _ => hint_j j]
    refine setIntegral_congr_fun measurableSet_Ioi fun s _ => ?_
    rw [Finset.sum_mul, Finset.mul_sum]
  have hint_sum : IntegrableOn (fun s : ℝ => s ^ (p - 1) *
      ((∑ j ∈ Finset.range (2 * K), (s * (β * a)) ^ j / (j.factorial : ℝ)) *
        Real.exp (-(β * s ^ 2)))) (Ioi 0) := by
    have hf : IntegrableOn (fun s : ℝ => ∑ j ∈ Finset.range (2 * K), s ^ (p - 1) *
        ((s * (β * a)) ^ j / (j.factorial : ℝ) * Real.exp (-(β * s ^ 2)))) (Ioi 0) :=
      integrable_finsetSum (Finset.range (2 * K)) fun j _ => hint_j j
    refine hf.congr_fun (fun s _ => ?_) measurableSet_Ioi
    beta_reduce
    rw [Finset.sum_mul, Finset.mul_sum]
  rw [hsum, phaseMoment, ← integral_sub (phaseMoment_integrand_integrableOn β p a hβ hp) hint_sum]
  have hbound_int : IntegrableOn (fun s : ℝ => tailCoeff β b K *
      (s ^ (p - 1) * Real.exp (-(β / 4 * s ^ 2)))) (Ioi 0) :=
    (gaussTail_integrand_integrableOn β p hβ hp).const_mul _
  have hpt : ∀ᵐ s ∂(volume.restrict (Ioi (0 : ℝ))),
      ‖s ^ (p - 1) * quadKernel β a s - s ^ (p - 1) *
        ((∑ j ∈ Finset.range (2 * K), (s * (β * a)) ^ j / (j.factorial : ℝ)) *
          Real.exp (-(β * s ^ 2)))‖ ≤
      tailCoeff β b K * (s ^ (p - 1) * Real.exp (-(β / 4 * s ^ 2))) := by
    refine (ae_restrict_iff' measurableSet_Ioi).2 (Eventually.of_forall fun s hs => ?_)
    have hs0 : (0 : ℝ) < s := hs
    have hq : quadKernel β a s = Real.exp (s * (β * a)) * Real.exp (-(β * s ^ 2)) := by
      unfold quadKernel
      rw [← Real.exp_add]
      congr 1
      ring
    rw [hq, Real.norm_eq_abs, ← mul_sub, ← sub_mul, abs_mul, abs_mul,
      abs_of_nonneg (Real.rpow_nonneg hs0.le _), abs_of_pos (Real.exp_pos _)]
    have := phase_tail_le β b s (β * a) hβ hs0.le hab K
    calc s ^ (p - 1) * (|Real.exp (s * (β * a)) -
          ∑ j ∈ Finset.range (2 * K), (s * (β * a)) ^ j / (j.factorial : ℝ)| *
            Real.exp (-(β * s ^ 2)))
        ≤ s ^ (p - 1) * (tailCoeff β b K * Real.exp (-(β / 4 * s ^ 2))) :=
          mul_le_mul_of_nonneg_left this (Real.rpow_nonneg hs0.le _)
      _ = tailCoeff β b K * (s ^ (p - 1) * Real.exp (-(β / 4 * s ^ 2))) := by ring
  have h := norm_integral_le_of_norm_le hbound_int hpt
  rw [Real.norm_eq_abs] at h
  rw [gaussTail, ← integral_const_mul]
  exact h

end Laplace.Grammar
