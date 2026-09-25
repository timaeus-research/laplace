/-
Copyright (c) 2026 Timaeus Research. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniel Murfet
-/
import Mathlib
import Laplace.Multi.TermScoreResponse

/-!
# The Gamma marginal: from the exponential score to the face score

Integrating out a scaled coordinate `z` with density `z^{β-1}` against the exponential-form term
`e^{-B U_a(u) z}` produces the Gamma integral

  `∫₀^∞ z^{β-1} e^{-B U z} dz = Γ(β) (B U)^{-β}`   (`integral_rpow_mul_exp_neg_mul`),

so the term integral of a product-domain term is the face coefficient of `CoefficientResponse`
(`termCoef_prod_eq_faceCoef`), and the score-weighted term integral of `S_v = B R_v z` is `β`
times the face-score-weighted integral (`termScoreCoef_prod_eq`): conditionally on the face
point, the exponential score averages to the face score,

  `E[B R_v z | u] = β R_v(u) / U_a(u)`   (`gamma_score`).

This is the exact bridge between the two singular fluctuation–response identities: the
exponential form of `TermScoreResponse` (`−Cov(φ, B R_v P)`) marginalises to the face form of
`CoefficientResponse` (`−β Cov(φ, R_v/U_a)`).
-/

open MeasureTheory Filter Topology Set

namespace Laplace.Multi

/-- `∫₀^∞ z^{β-1} e^{-b z} dz = b^{-β} Γ(β)`. -/
theorem integral_rpow_mul_exp_neg_mul {β b : ℝ} (hβ : 0 < β) (hb : 0 < b) :
    ∫ z in Ioi (0 : ℝ), z ^ (β - 1) * Real.exp (-b * z) = b ^ (-β) * Real.Gamma β := by
  have := integral_rpow_mul_exp_neg_mul_rpow (p := 1) (q := β - 1) (b := b) one_pos
    (by linarith) hb
  simp only [Real.rpow_one, sub_add_cancel, div_one, mul_one] at this
  exact this

/-- `∫₀^∞ z^{β} e^{-b z} dz = b^{-(β+1)} Γ(β+1)`. -/
theorem integral_rpow_mul_exp_neg_mul' {β b : ℝ} (hβ : 0 < β) (hb : 0 < b) :
    ∫ z in Ioi (0 : ℝ), z ^ β * Real.exp (-b * z) = b ^ (-(β + 1)) * Real.Gamma (β + 1) := by
  have := integral_rpow_mul_exp_neg_mul (β := β + 1) (by linarith) hb
  simpa only [add_sub_cancel_right] using this

theorem integrableOn_rpow_mul_exp_neg_mul {q b : ℝ} (hq : -1 < q) (hb : 0 < b) :
    IntegrableOn (fun z : ℝ ↦ z ^ q * Real.exp (-b * z)) (Ioi 0) := by
  have := integrableOn_rpow_mul_exp_neg_mul_rpow (p := 1) (s := q) (b := b) hq one_pos hb
  simpa only [Real.rpow_one] using this

/-- **The conditional expectation of the exponential score is the face score**:
`∫ z^{β-1} (B R z) e^{-B U z} / ∫ z^{β-1} e^{-B U z} = β R / U`. -/
theorem gamma_score {β B U : ℝ} (hβ : 0 < β) (hB : 0 < B) (hU : 0 < U) (R : ℝ) :
    (∫ z in Ioi (0 : ℝ), z ^ (β - 1) * (B * R * z) * Real.exp (-(B * U) * z)) /
      (∫ z in Ioi (0 : ℝ), z ^ (β - 1) * Real.exp (-(B * U) * z)) = β * R / U := by
  have hBU : 0 < B * U := mul_pos hB hU
  have h1 : (∫ z in Ioi (0 : ℝ), z ^ (β - 1) * (B * R * z) * Real.exp (-(B * U) * z)) =
      B * R * ∫ z in Ioi (0 : ℝ), z ^ β * Real.exp (-(B * U) * z) := by
    rw [← integral_const_mul]
    refine setIntegral_congr_fun measurableSet_Ioi fun z hz ↦ ?_
    have hz0 : (0 : ℝ) < z := hz
    rw [Real.rpow_sub_one hz0.ne']
    field_simp
  rw [h1, integral_rpow_mul_exp_neg_mul' hβ hBU, integral_rpow_mul_exp_neg_mul hβ hBU,
    Real.Gamma_add_one hβ.ne', show -(β + 1) = -β - 1 by ring, Real.rpow_sub_one hBU.ne']
  have hG := Real.Gamma_pos_of_pos hβ
  have hp : 0 < (B * U) ^ (-β) := Real.rpow_pos_of_pos hBU _
  field_simp

section Product

variable {Y : Type*} [MeasurableSpace Y] {ι : Type*} [Fintype ι]

/-- The product-domain term: face point `u`, scaled coordinate `z > 0`, weight `w(u) z^{β-1}`,
profile `z`. -/
noncomputable def prodMeasure (ν : Measure Y) : Measure (Y × ℝ) :=
  ν.prod (volume.restrict (Ioi 0))

theorem integrable_prod_term {ν : Measure Y} {g : Y → ℝ} (hg : Integrable g ν) {β b : ℝ}
    (hβ : 0 < β) (hb : 0 < b) :
    Integrable (fun p : Y × ℝ ↦ g p.1 * (p.2 ^ (β - 1) * Real.exp (-b * p.2)))
      (prodMeasure ν) :=
  hg.mul_prod (integrableOn_rpow_mul_exp_neg_mul (by linarith) hb)

theorem ae_snd_pos (ν : Measure Y) : ∀ᵐ p ∂(prodMeasure ν), 0 < p.2 := by
  unfold prodMeasure
  have hs : MeasurableSet {p : Y × ℝ | 0 < p.2} := measurableSet_lt measurable_const measurable_snd
  have h := (Measure.ae_prod_mem_iff_ae_ae_mem (μ := ν) (ν := volume.restrict (Ioi 0)) hs).mpr
    (Filter.Eventually.of_forall fun u ↦ ae_restrict_mem measurableSet_Ioi)
  exact h

/-- **The term integral of a product-domain term is a face coefficient**:
`∫∫ φ(u) w(u) z^{β-1} e^{-B U_a(u) z} dz dν = Γ(β) B^{-β} ∫ φ w U_a^{-β} dν`. -/
theorem termCoef_prod_eq_faceCoef {ν : Measure Y} [SFinite ν] {h : ι → Y → ℝ}
    (hhm : ∀ i, Measurable (h i))
    {a : ι → ℝ} {c : ℝ} (hc : 0 < c) (hU : ∀ u, c ≤ faceUnit h a u) {β B : ℝ} (hβ : 0 < β)
    (hB : 0 < B) {φ w : Y → ℝ} (hφm : Measurable φ) (hwm : Measurable w)
    (hint : Integrable (fun u ↦ φ u * w u) ν) :
    termCoef (prodMeasure ν) (fun p ↦ w p.1 * p.2 ^ (β - 1)) (fun p ↦ p.2) Prod.fst h B
        (fun p ↦ φ p.1) a =
      Real.Gamma β * B ^ (-β) * faceCoef ν (fun u ↦ φ u * w u) h β a := by
  have hpos : ∀ u, 0 < faceUnit h a u := fun u ↦ hc.trans_le (hU u)
  have hUm : Measurable (faceUnit h a) :=
    Finset.measurable_sum Finset.univ fun i _ ↦ (hhm i).const_mul (a i)
  have hmeas : Measurable fun p : Y × ℝ ↦
      φ p.1 * (w p.1 * p.2 ^ (β - 1)) * Real.exp (-(B * faceUnit h a p.1 * p.2)) :=
    ((hφm.comp measurable_fst).mul ((hwm.comp measurable_fst).mul
      (measurable_snd.pow_const _))).mul (Real.measurable_exp.comp
      (((hUm.comp measurable_fst).const_mul B).mul measurable_snd).neg)
  have hint2 : Integrable (fun p : Y × ℝ ↦
      φ p.1 * (w p.1 * p.2 ^ (β - 1)) * Real.exp (-(B * faceUnit h a p.1 * p.2)))
      (prodMeasure ν) := by
    refine (integrable_prod_term hint.norm hβ (mul_pos hB hc)).mono' hmeas.aestronglyMeasurable
      ?_
    filter_upwards [ae_snd_pos ν] with p hp
    simp only [Real.norm_eq_abs, abs_mul, abs_of_pos (Real.exp_pos _),
      abs_of_pos (Real.rpow_pos_of_pos hp _)]
    have he : Real.exp (-(B * faceUnit h a p.1 * p.2)) ≤ Real.exp (-(B * c) * p.2) := by
      rw [Real.exp_le_exp]
      have := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left (hU p.1) hB.le) hp.le
      linarith
    calc _ ≤ |φ p.1| * (|w p.1| * p.2 ^ (β - 1)) * Real.exp (-(B * c) * p.2) :=
          mul_le_mul_of_nonneg_left he (by positivity)
      _ = |φ p.1| * |w p.1| * (p.2 ^ (β - 1) * Real.exp (-(B * c) * p.2)) := by ring
  unfold termCoef prodMeasure
  rw [integral_prod _ (by simpa [prodMeasure] using hint2)]
  have hinner : ∀ u, (∫ z in Ioi (0 : ℝ),
      φ u * (w u * z ^ (β - 1)) * Real.exp (-(B * faceUnit h a u * z))) =
      Real.Gamma β * B ^ (-β) * ((φ u * w u) * faceUnit h a u ^ (-β)) := by
    intro u
    have e : ∀ z : ℝ, φ u * (w u * z ^ (β - 1)) * Real.exp (-(B * faceUnit h a u * z)) =
        (φ u * w u) * (z ^ (β - 1) * Real.exp (-(B * faceUnit h a u) * z)) := by
      intro z
      rw [neg_mul]
      ring
    simp_rw [e]
    rw [integral_const_mul, integral_rpow_mul_exp_neg_mul hβ (mul_pos hB (hpos u)),
      Real.mul_rpow hB.le (hpos u).le]
    ring
  simp only [hinner]
  rw [integral_const_mul]
  rfl

/-- **The score-weighted term integral marginalises to the face score**:
`∫∫ φ (B R_v z) w z^{β-1} e^{-B U_a z} dz dν = Γ(β) B^{-β} · β ∫ φ w U_a^{-β-1} R_v dν`. -/
theorem termScoreCoef_prod_eq [Nonempty Y] {ν : Measure Y} [SFinite ν] {h : ι → Y → ℝ}
    (hhm : ∀ i, Measurable (h i))
    {Mh : ℝ} (hhb : ∀ i u, |h i u| ≤ Mh) {a : ι → ℝ} {c : ℝ} (hc : 0 < c)
    (hU : ∀ u, c ≤ faceUnit h a u) {β B : ℝ} (hβ : 0 < β) (hB : 0 < B) {φ w : Y → ℝ}
    (hφm : Measurable φ) (hwm : Measurable w) (hint : Integrable (fun u ↦ φ u * w u) ν)
    (v : ι → ℝ) :
    (∫ p, φ p.1 * termScore (fun p : Y × ℝ ↦ p.2) Prod.fst h B v p * (w p.1 * p.2 ^ (β - 1)) *
        Real.exp (-(B * faceUnit h a p.1 * p.2)) ∂(prodMeasure ν)) =
      Real.Gamma β * B ^ (-β) *
        (β * ∫ u, (φ u * w u) * faceUnit h a u ^ (-β - 1) * faceUnit h v u ∂ν) := by
  have hpos : ∀ u, 0 < faceUnit h a u := fun u ↦ hc.trans_le (hU u)
  have hUm : Measurable (faceUnit h a) :=
    Finset.measurable_sum Finset.univ fun i _ ↦ (hhm i).const_mul (a i)
  have hVm : Measurable (faceUnit h v) :=
    Finset.measurable_sum Finset.univ fun i _ ↦ (hhm i).const_mul (v i)
  have hS : ∀ u, |faceUnit h v u| ≤ (∑ i, |v i|) * Mh := fun u ↦ by
    unfold faceUnit
    rw [Finset.sum_mul]
    refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun i _ ↦ ?_)
    rw [abs_mul]
    exact mul_le_mul_of_nonneg_left (hhb i u) (abs_nonneg _)
  have hS0 : 0 ≤ (∑ i, |v i|) * Mh := le_trans (abs_nonneg _) (hS (Classical.arbitrary Y))
  have hmeas : Measurable fun p : Y × ℝ ↦
      φ p.1 * termScore (fun p : Y × ℝ ↦ p.2) Prod.fst h B v p *
        (w p.1 * p.2 ^ (β - 1)) * Real.exp (-(B * faceUnit h a p.1 * p.2)) := by
    unfold termScore
    exact (((hφm.comp measurable_fst).mul (((hVm.comp measurable_fst).const_mul B).mul
      measurable_snd)).mul ((hwm.comp measurable_fst).mul (measurable_snd.pow_const _))).mul
      (Real.measurable_exp.comp ((((hUm.comp measurable_fst).const_mul B).mul measurable_snd).neg))
  have hint2 : Integrable (fun p : Y × ℝ ↦
      φ p.1 * termScore (fun p : Y × ℝ ↦ p.2) Prod.fst h B v p *
        (w p.1 * p.2 ^ (β - 1)) * Real.exp (-(B * faceUnit h a p.1 * p.2))) (prodMeasure ν) := by
    refine (integrable_prod_term (hint.norm.const_mul (B * ((∑ i, |v i|) * Mh))) (β := β + 1)
      (by linarith) (mul_pos hB hc)).mono' hmeas.aestronglyMeasurable ?_
    filter_upwards [ae_snd_pos ν] with p hp
    unfold termScore
    simp only [add_sub_cancel_right, Real.norm_eq_abs, abs_mul, abs_of_pos hB, abs_of_pos hp,
      abs_of_pos (Real.rpow_pos_of_pos hp _), abs_of_pos (Real.exp_pos _)]
    have he : Real.exp (-(B * faceUnit h a p.1 * p.2)) ≤ Real.exp (-(B * c) * p.2) := by
      rw [Real.exp_le_exp]
      have := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left (hU p.1) hB.le) hp.le
      linarith
    have hR := hS p.1
    have hz : p.2 ^ (β - 1) * p.2 = p.2 ^ β := by
      rw [Real.rpow_sub_one hp.ne']
      field_simp
    have hzβ : 0 < p.2 ^ β := Real.rpow_pos_of_pos hp _
    calc _ = (|φ p.1| * |w p.1|) * (B * |faceUnit h v p.1|) * (p.2 ^ (β - 1) * p.2) *
          Real.exp (-(B * faceUnit h a p.1 * p.2)) := by ring
      _ ≤ (|φ p.1| * |w p.1|) * (B * ((∑ i, |v i|) * Mh)) * p.2 ^ β *
          Real.exp (-(B * c) * p.2) := by
          rw [hz]
          refine mul_le_mul (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left
            (mul_le_mul_of_nonneg_left hR hB.le) (mul_nonneg (abs_nonneg _) (abs_nonneg _)))
            hzβ.le) he (Real.exp_pos _).le ?_
          exact mul_nonneg (mul_nonneg (mul_nonneg (abs_nonneg _) (abs_nonneg _))
            (mul_nonneg hB.le hS0)) hzβ.le
      _ = B * ((∑ i, |v i|) * Mh) * (|φ p.1| * |w p.1|) *
          (p.2 ^ β * Real.exp (-(B * c) * p.2)) := by ring
  unfold prodMeasure
  rw [integral_prod _ (by simpa [prodMeasure] using hint2)]
  have hinner : ∀ u, (∫ z in Ioi (0 : ℝ), φ u * termScore (fun p : Y × ℝ ↦ p.2) Prod.fst h B v
      (u, z) * (w u * z ^ (β - 1)) * Real.exp (-(B * faceUnit h a u * z))) =
      Real.Gamma β * B ^ (-β) * (β * ((φ u * w u) * faceUnit h a u ^ (-β - 1) *
        faceUnit h v u)) := by
    intro u
    have e : ∀ z : ℝ, φ u * termScore (fun p : Y × ℝ ↦ p.2) Prod.fst h B v (u, z) *
        (w u * z ^ (β - 1)) * Real.exp (-(B * faceUnit h a u * z)) =
        (φ u * w u * (B * faceUnit h v u)) *
          (z ^ (β - 1) * (z * Real.exp (-(B * faceUnit h a u) * z))) := by
      intro z
      unfold termScore
      rw [neg_mul]
      ring
    have e2 : ∀ z ∈ Ioi (0 : ℝ), z ^ (β - 1) * (z * Real.exp (-(B * faceUnit h a u) * z)) =
        z ^ β * Real.exp (-(B * faceUnit h a u) * z) := fun z hz ↦ by
      have hz0 : (0 : ℝ) < z := hz
      rw [Real.rpow_sub_one hz0.ne']
      field_simp
    simp_rw [e]
    rw [integral_const_mul, setIntegral_congr_fun measurableSet_Ioi e2,
      integral_rpow_mul_exp_neg_mul' hβ (mul_pos hB (hpos u)), Real.Gamma_add_one hβ.ne',
      show -(β + 1) = -β - 1 by ring, Real.mul_rpow hB.le (hpos u).le, Real.rpow_sub_one hB.ne']
    field_simp
  simp only [hinner]
  rw [integral_const_mul, integral_const_mul]

end Product

end Laplace.Multi
