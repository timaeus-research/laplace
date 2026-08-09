/-
Copyright (c) 2026 Timaeus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib
import Laplace.Multi.AnisotropicScaling

/-!
# Pi-volume satisfies the scaling interface

The deferred infrastructure piece of the anisotropic-scaling tide:
Lebesgue measure on `ι → ℝ` satisfies `ScalesMeasure` for the
diagonal dilation `qhDilation q` with total homogeneity
`Q = ∑ i, q i`. The route is the linear-map Haar theorem plus the
determinant of a diagonal map (`LinearMap.det_pi`). Consequences:
the exact quasi-homogeneous moment laws and the weight-recovery
theorem hold unconditionally on Lebesgue measure, and the note's
mixed example `x⁴ + x²y² + y⁴` (quasi-homogeneous for
`q = (1/4, 1/4)`, not separable) is covered concretely.
-/

open Real MeasureTheory Filter

namespace Laplace.Multi

variable {ι : Type*}

/-- The diagonal linear map `w ↦ fun i ↦ c i * w i`. -/
noncomputable def diagonalMap (c : ι → ℝ) : (ι → ℝ) →ₗ[ℝ] (ι → ℝ) :=
  LinearMap.pi fun i ↦ (c i • LinearMap.id).comp (LinearMap.proj i)

@[simp] theorem diagonalMap_apply (c : ι → ℝ) (w : ι → ℝ) (i : ι) :
    diagonalMap c w i = c i * w i := rfl

/-- The determinant of the diagonal map is the product of its
entries. -/
theorem det_diagonalMap [Fintype ι] (c : ι → ℝ) :
    LinearMap.det (diagonalMap c) = ∏ i, c i := by
  rw [diagonalMap, LinearMap.det_pi]
  refine Finset.prod_congr rfl fun i _ ↦ ?_
  rw [LinearMap.det_smul, LinearMap.det_id, Module.finrank_self]
  simp

/-- The diagonal dilation is the diagonal map with entries
`s ^ q i`. -/
theorem qhDilation_eq_diagonalMap (q : ι → ℝ) (s : ℝ) :
    qhDilation q s = diagonalMap (fun i ↦ s ^ q i) := by
  funext w
  rfl

/-- **Pi-volume satisfies the scaling interface**: Lebesgue measure
on `ι → ℝ` scales under the diagonal dilation with total homogeneity
`∑ i, q i`. -/
theorem scalesMeasure_qhDilation_volume [Fintype ι] (q : ι → ℝ) :
    ScalesMeasure (qhDilation q) (∑ i, q i)
      (volume : Measure (ι → ℝ)) := by
  intro s hs
  have hdet : LinearMap.det (diagonalMap fun i ↦ s ^ q i) =
      s ^ (∑ i, q i) := by
    rw [det_diagonalMap, Real.rpow_sum_of_pos hs]
  have hdet_ne : LinearMap.det (diagonalMap fun i ↦ s ^ q i) ≠ 0 := by
    rw [hdet]
    exact (Real.rpow_pos_of_pos hs _).ne'
  have hmap := Measure.map_linearMap_addHaar_pi_eq_smul_addHaar
    hdet_ne (volume : Measure (ι → ℝ))
  rw [hdet] at hmap
  rw [qhDilation_eq_diagonalMap]
  rw [show ⇑(diagonalMap fun i ↦ s ^ q i) =
    fun w : ι → ℝ ↦ (diagonalMap fun i ↦ s ^ q i) w from rfl]
  rw [hmap]
  congr 1
  rw [abs_of_pos (inv_pos.mpr (Real.rpow_pos_of_pos hs _)),
    ← Real.rpow_neg hs.le]

/-- **Unconditional weight recovery on Lebesgue measure**: two
quasi-homogeneous potentials (arbitrary mixed terms) with matched
normalized coordinate second moments on a temperature ray and
positive moments at temperature one have equal anisotropic
weights. -/
theorem weights_eq_of_coordSq_moments_eq_volume [Fintype ι]
    {q₁ q₂ : ι → ℝ} {P₁ P₂ : (ι → ℝ) → ℝ}
    (hP₁ : Measurable P₁) (hP₂ : Measurable P₂)
    (hqh₁ : ∀ s : ℝ, 0 < s → ∀ w,
      P₁ (qhDilation q₁ s w) = s * P₁ w)
    (hqh₂ : ∀ s : ℝ, 0 < s → ∀ w,
      P₂ (qhDilation q₂ s w) = s * P₂ w)
    (hpos₁ : ∀ i : ι, 0 <
      (∫ w : ι → ℝ, (w i) ^ 2 * Real.exp (-(P₁ w))) /
        (∫ w : ι → ℝ, Real.exp (-(P₁ w))))
    {T : ℝ}
    (hmatch : ∀ (i : ι) (t : ℝ), T ≤ t →
      (∫ w : ι → ℝ, (w i) ^ 2 * Real.exp (-(t * P₁ w))) /
          (∫ w : ι → ℝ, Real.exp (-(t * P₁ w))) =
        (∫ w : ι → ℝ, (w i) ^ 2 * Real.exp (-(t * P₂ w))) /
          (∫ w : ι → ℝ, Real.exp (-(t * P₂ w)))) :
    q₁ = q₂ :=
  weights_eq_of_coordSq_moments_eq
    (scalesMeasure_qhDilation_volume q₁)
    (scalesMeasure_qhDilation_volume q₂)
    hP₁ hP₂ hqh₁ hqh₂ hpos₁ hmatch

/-- The note's mixed example: `x⁴ + x²y² + y⁴` on `Fin 2 → ℝ`. -/
noncomputable def mixedQuartic : (Fin 2 → ℝ) → ℝ :=
  fun w ↦ (w 0) ^ 4 + (w 0) ^ 2 * (w 1) ^ 2 + (w 1) ^ 4

theorem mixedQuartic_measurable : Measurable mixedQuartic := by
  unfold mixedQuartic
  fun_prop

/-- The mixed quartic is quasi-homogeneous for the common weights
`q = 1/4`: each of its three terms — including the mixed one, which
no separable potential contains — scales by `s`. -/
theorem mixedQuartic_quasiHomogeneous {s : ℝ} (hs : 0 < s)
    (w : Fin 2 → ℝ) :
    mixedQuartic (qhDilation (fun _ ↦ (1 : ℝ) / 4) s w) =
      s * mixedQuartic w := by
  have hcoord : ∀ (i : Fin 2) (n : ℕ),
      (qhDilation (fun _ : Fin 2 ↦ (1 : ℝ) / 4) s w i) ^ n =
        s ^ (((n : ℝ)) / 4) * (w i) ^ n := by
    intro i n
    simp only [qhDilation]
    rw [mul_pow, ← Real.rpow_natCast (s ^ ((1 : ℝ) / 4)) n,
      ← Real.rpow_mul hs.le]
    rw [show (1 : ℝ) / 4 * (n : ℝ) = (n : ℝ) / 4 from by ring]
  unfold mixedQuartic
  rw [hcoord 0 4, hcoord 0 2, hcoord 1 2, hcoord 1 4]
  have h44 : s ^ ((4 : ℝ) / 4) = s := by
    norm_num
  have h22 : s ^ ((2 : ℝ) / 4) * s ^ ((2 : ℝ) / 4) = s := by
    rw [← Real.rpow_add hs]
    norm_num
  push_cast
  rw [h44]
  calc s * (w 0) ^ 4 +
      s ^ ((2:ℝ)/4) * (w 0) ^ 2 * (s ^ ((2:ℝ)/4) * (w 1) ^ 2) +
      s * (w 1) ^ 4
      = s * (w 0) ^ 4 +
        (s ^ ((2:ℝ)/4) * s ^ ((2:ℝ)/4)) * ((w 0) ^ 2 * (w 1) ^ 2) +
        s * (w 1) ^ 4 := by ring
    _ = s * ((w 0) ^ 4 + (w 0) ^ 2 * (w 1) ^ 2 + (w 1) ^ 4) := by
        rw [h22]; ring

end Laplace.Multi
