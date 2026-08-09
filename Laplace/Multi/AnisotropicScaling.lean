/-
Copyright (c) 2026 Timaeus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib
import Laplace.Multi.SeparableAffinity
import Laplace.OneD.Recovery

/-!
# Abstract anisotropic scaling and weight recovery

The genuinely non-separable step of the degenerate programme
(germbij §7.4(b)): a one-parameter dilation family that scales the
reference measure (`ScalesMeasure`), together with quasi-homogeneity
of the potential and homogeneity of the observable along the family,
forces the exact moment law
\[ I_\varphi(t) = t^{-(Q + r)}\, I_\varphi(1), \qquad
   M_\varphi(t) = t^{-r}\, M_\varphi(1), \]
with no integrability hypotheses (the substitution preserves
non-integrability, so the junk-value convention degenerates
coherently). On the pi type with the diagonal dilation
`w ↦ fun i ↦ s^(q i) * w i`, coordinate-square observables have
`r = 2 q i`, and matched coordinate moment data recover the
anisotropic weights `q` of a quasi-homogeneous potential without any
separability. Separability is nowhere used: the only facts about the
potential are measurability and quasi-homogeneity.

The concrete fact that the diagonal dilation on pi-type volume
satisfies `ScalesMeasure` (a determinant computation) is deferred to
a separate infrastructure result; every theorem here takes it as the
geometric hypothesis, per the shape consult.
-/

open Real MeasureTheory Filter

namespace Laplace.Multi

/-- A one-parameter family of maps scales a measure with total
homogeneity `Q`. -/
def ScalesMeasure {X : Type*} [MeasurableSpace X] (δ : ℝ → X → X)
    (Q : ℝ) (μ : Measure X) : Prop :=
  ∀ s : ℝ, 0 < s →
    Measure.map (δ s) μ = ENNReal.ofReal (s ^ (-Q)) • μ

section Abstract

variable {X : Type*} [MeasurableSpace X] {μ : Measure X}
  {δ : ℝ → X → X} {Q : ℝ}

/-- **The exact unnormalized moment law**: if the dilation family
scales the measure with homogeneity `Q`, the potential is
quasi-homogeneous of weight one, and the observable is homogeneous
of weight `r` along the family, then the Laplace moment at
temperature `t` is exactly `t^(-(Q+r))` times the moment at
temperature one. No integrability is assumed. -/
theorem scalesMeasure_moment_law
    (hscale : ScalesMeasure δ Q μ)
    (hδ : ∀ s : ℝ, 0 < s → Measurable (δ s))
    {P φ : X → ℝ} (hP : Measurable P) (hφ : Measurable φ)
    (hPqh : ∀ s : ℝ, 0 < s → ∀ w, P (δ s w) = s * P w)
    {r : ℝ} (hφh : ∀ s : ℝ, 0 < s → ∀ w, φ (δ s w) = s ^ r * φ w)
    {t : ℝ} (ht : 0 < t) :
    ∫ w, φ w * Real.exp (-(t * P w)) ∂μ =
      t ^ (-(Q + r)) *
        ∫ w, φ w * Real.exp (-(P w)) ∂μ := by
  have hs : (0 : ℝ) < t⁻¹ := by positivity
  set f : X → ℝ := fun w ↦ φ w * Real.exp (-(t * P w)) with hf_def
  have hf_meas : Measurable f :=
    hφ.mul (Real.measurable_exp.comp ((measurable_const.mul hP).neg))
  have hmap := hscale t⁻¹ hs
  have hintmap : ∫ w, f w ∂(Measure.map (δ t⁻¹) μ) =
      ∫ w, f (δ t⁻¹ w) ∂μ :=
    integral_map (hδ t⁻¹ hs).aemeasurable hf_meas.aestronglyMeasurable
  rw [hmap, integral_smul_measure] at hintmap
  have htoReal : (ENNReal.ofReal (t⁻¹ ^ (-Q))).toReal =
      t ^ Q := by
    rw [ENNReal.toReal_ofReal (by positivity)]
    rw [show t⁻¹ = t ^ (-1 : ℝ) from by
      rw [Real.rpow_neg ht.le, Real.rpow_one]]
    rw [← Real.rpow_mul ht.le]
    norm_num
  rw [htoReal] at hintmap
  have hsub : ∀ w, f (δ t⁻¹ w) =
      t⁻¹ ^ r * (φ w * Real.exp (-(P w))) := by
    intro w
    rw [hf_def]
    simp only []
    rw [hφh t⁻¹ hs w, hPqh t⁻¹ hs w]
    have harg : t * (t⁻¹ * P w) = P w := by
      field_simp
    rw [harg]
    ring
  rw [integral_congr_ae (Filter.Eventually.of_forall hsub),
    integral_const_mul] at hintmap
  have hpow : t⁻¹ ^ r = t ^ (-r) := by
    rw [show t⁻¹ = t ^ (-1 : ℝ) from by
      rw [Real.rpow_neg ht.le, Real.rpow_one]]
    rw [← Real.rpow_mul ht.le]
    rw [show (-1 : ℝ) * r = -r by ring]
  rw [hpow] at hintmap
  rw [smul_eq_mul] at hintmap
  have hQpos : (0 : ℝ) < t ^ Q := Real.rpow_pos_of_pos ht _
  have hsolve : ∫ w, f w ∂μ =
      (t ^ (-r) * ∫ w, φ w * Real.exp (-(P w)) ∂μ) / t ^ Q := by
    rw [eq_div_iff hQpos.ne', mul_comm]
    exact hintmap
  rw [hsolve, div_eq_mul_inv, ← Real.rpow_neg ht.le]
  rw [show t ^ (-r) * (∫ w, φ w * Real.exp (-(P w)) ∂μ) *
      t ^ (-Q) =
    t ^ (-r) * t ^ (-Q) * ∫ w, φ w * Real.exp (-(P w)) ∂μ from by
      ring]
  rw [← Real.rpow_add ht, show -r + -Q = -(Q + r) from by ring]

/-- **The exact normalized moment law**: the partition-function
exponent cancels, leaving `M_φ(t) = t^(-r) M_φ(1)`. Pure field
algebra on top of the unnormalized law; the degenerate `0/0` case is
coherent, so no positivity is needed. -/
theorem scalesMeasure_normalized_law
    (hscale : ScalesMeasure δ Q μ)
    (hδ : ∀ s : ℝ, 0 < s → Measurable (δ s))
    {P φ : X → ℝ} (hP : Measurable P) (hφ : Measurable φ)
    (hPqh : ∀ s : ℝ, 0 < s → ∀ w, P (δ s w) = s * P w)
    {r : ℝ} (hφh : ∀ s : ℝ, 0 < s → ∀ w, φ (δ s w) = s ^ r * φ w)
    {t : ℝ} (ht : 0 < t) :
    (∫ w, φ w * Real.exp (-(t * P w)) ∂μ) /
        (∫ w, Real.exp (-(t * P w)) ∂μ) =
      t ^ (-r) *
        ((∫ w, φ w * Real.exp (-(P w)) ∂μ) /
          (∫ w, Real.exp (-(P w)) ∂μ)) := by
  have hnum := scalesMeasure_moment_law hscale hδ hP hφ hPqh hφh ht
  have hden := scalesMeasure_moment_law hscale hδ hP
    (measurable_const : Measurable fun _ : X ↦ (1 : ℝ))
    hPqh (r := 0)
    (fun s hs w ↦ by rw [Real.rpow_zero]; ring) ht
  simp only [one_mul] at hden
  rw [hnum, hden]
  have hQr : (0 : ℝ) < t ^ (-(Q + r)) := Real.rpow_pos_of_pos ht _
  have hQ0 : (0 : ℝ) < t ^ (-(Q + 0)) := Real.rpow_pos_of_pos ht _
  rw [mul_div_mul_comm]
  congr 1
  rw [← Real.rpow_sub ht]
  congr 1
  ring

end Abstract

section

variable {ι : Type*}

/-- The diagonal quasi-homogeneous dilation
`(δ_q s)(w) i = s^(q i) * w i`. -/
noncomputable def qhDilation (q : ι → ℝ) (s : ℝ) :
    (ι → ℝ) → (ι → ℝ) :=
  fun w i ↦ s ^ (q i) * w i

theorem qhDilation_measurable (q : ι → ℝ) (s : ℝ) :
    Measurable (qhDilation q s) :=
  measurable_pi_lambda _ fun i ↦
    (measurable_pi_apply i).const_mul _

/-- Coordinate squares are homogeneous of weight `2 q i` along the
diagonal dilation. -/
theorem coordSq_qhDilation (q : ι → ℝ) {s : ℝ} (hs : 0 < s)
    (i : ι) (w : ι → ℝ) :
    (qhDilation q s w i) ^ 2 = s ^ (2 * q i) * (w i) ^ 2 := by
  simp only [qhDilation]
  rw [mul_pow, ← Real.rpow_natCast (s ^ (q i)) 2,
    ← Real.rpow_mul hs.le]
  push_cast
  rw [show q i * (2 : ℝ) = 2 * q i from by ring]

/-- **Weight recovery without separability** (germbij §7.4(b)): two
quasi-homogeneous potentials whose dilation families scale the
measure and whose normalized coordinate second moments are positive
at temperature one and agree on a temperature ray have equal
anisotropic weights. Separability is nowhere assumed; the potentials
may contain arbitrary mixed terms. -/
theorem weights_eq_of_coordSq_moments_eq [Fintype ι]
    {μ : Measure (ι → ℝ)}
    {q₁ q₂ : ι → ℝ} {P₁ P₂ : (ι → ℝ) → ℝ}
    (hscale₁ : ScalesMeasure (qhDilation q₁) (∑ i, q₁ i) μ)
    (hscale₂ : ScalesMeasure (qhDilation q₂) (∑ i, q₂ i) μ)
    (hP₁ : Measurable P₁) (hP₂ : Measurable P₂)
    (hqh₁ : ∀ s : ℝ, 0 < s → ∀ w,
      P₁ (qhDilation q₁ s w) = s * P₁ w)
    (hqh₂ : ∀ s : ℝ, 0 < s → ∀ w,
      P₂ (qhDilation q₂ s w) = s * P₂ w)
    (hpos₁ : ∀ i : ι, 0 <
      (∫ w, (w i) ^ 2 * Real.exp (-(P₁ w)) ∂μ) /
        (∫ w, Real.exp (-(P₁ w)) ∂μ))
    {T : ℝ}
    (hmatch : ∀ (i : ι) (t : ℝ), T ≤ t →
      (∫ w, (w i) ^ 2 * Real.exp (-(t * P₁ w)) ∂μ) /
          (∫ w, Real.exp (-(t * P₁ w)) ∂μ) =
        (∫ w, (w i) ^ 2 * Real.exp (-(t * P₂ w)) ∂μ) /
          (∫ w, Real.exp (-(t * P₂ w)) ∂μ)) :
    q₁ = q₂ := by
  funext i
  have hφ : Measurable fun w : ι → ℝ ↦ (w i) ^ 2 :=
    (measurable_pi_apply i).pow measurable_const
  have hlaw₁ := fun (t : ℝ) (ht : 0 < t) ↦
    scalesMeasure_normalized_law hscale₁
      (fun s hs ↦ qhDilation_measurable q₁ s) hP₁ hφ hqh₁
      (r := 2 * q₁ i)
      (fun s hs w ↦ coordSq_qhDilation q₁ hs i w) ht
  have hlaw₂ := fun (t : ℝ) (ht : 0 < t) ↦
    scalesMeasure_normalized_law hscale₂
      (fun s hs ↦ qhDilation_measurable q₂ s) hP₂ hφ hqh₂
      (r := 2 * q₂ i)
      (fun s hs w ↦ coordSq_qhDilation q₂ hs i w) ht
  obtain ⟨hβ, -⟩ := Laplace.OneD.eventual_power_eq
    (α₁ := (∫ w, (w i) ^ 2 * Real.exp (-(P₁ w)) ∂μ) /
      (∫ w, Real.exp (-(P₁ w)) ∂μ))
    (α₂ := (∫ w, (w i) ^ 2 * Real.exp (-(P₂ w)) ∂μ) /
      (∫ w, Real.exp (-(P₂ w)) ∂μ))
    (β₁ := -(2 * q₁ i)) (β₂ := -(2 * q₂ i)) (T := max T 1)
    (hpos₁ i)
    (fun t htT ↦ by
      have ht0 : 0 < t :=
        lt_of_lt_of_le one_pos (le_trans (le_max_right _ _) htT)
      have h₁ := hlaw₁ t ht0
      have h₂ := hlaw₂ t ht0
      rw [mul_comm] at h₁ h₂
      rw [← h₁, ← h₂]
      exact hmatch i t (le_trans (le_max_left _ _) htT))
  have : (2 : ℝ) * q₁ i = 2 * q₂ i := by linarith
  linarith

end

end Laplace.Multi
