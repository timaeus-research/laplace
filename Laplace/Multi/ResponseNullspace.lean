/-
Copyright (c) 2026 Timaeus Research. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniel Murfet
-/
import Mathlib
import Laplace.Multi.ResponseMap

/-!
# The nullspace of the response form: invisible data directions

The response form `g_a(v, v) = t² Var_a(R_v)` of `ResponseMap` is a pseudometric on the data
manifold. Its nullspace is exactly the set of data directions whose loss `R_v` is constant on the
support of the prior (`responseForm_self_eq_zero_iff`): those are the directions the posterior
cannot see, since replacing `L` by `L + c` for a constant `c` changes no expectation value. The
identifiable quotient of the data manifold is the quotient by these directions, and the response
form is a metric there. The variance identity `Var(f) = E[(f − E f)²]` and the characterisation
`Var(f) = 0 ↔ f = E f` a.e. on the support of the weight are proved for the tilted expectations
(`TiltData.tiltCov_self_eq_tiltExp_sq`, `TiltData.tiltCov_self_eq_zero_iff`).
-/

open MeasureTheory Filter Topology

namespace Laplace.Multi

variable {X : Type*} [MeasurableSpace X] {μ : Measure X} [Nonempty X]

/-- `Var(f) = E[(f − E f)²]` for the tilted expectations. -/
theorem TiltData.tiltCov_self_eq_tiltExp_sq {ν R : X → ℝ} {M : ℝ} (h : TiltData μ ν R M)
    {f : X → ℝ} (hf : Bdd f) (t u : ℝ) :
    tiltCov μ ν f f R t u = tiltExp μ ν (fun x ↦ (f x - tiltExp μ ν f R t u) ^ 2) R t u := by
  set c := tiltExp μ ν f R t u with hc
  have e : (fun x ↦ (f x - c) ^ 2) = fun x ↦ (f x * f x + (-(2 * c)) * f x) + c * c :=
    funext fun x ↦ by ring
  rw [e, h.tiltExp_add ((hf.mul hf).add (hf.const_mul _)) (Bdd.const _), h.tiltExp_add (hf.mul hf)
    (hf.const_mul _), tiltExp_const_mul, h.tiltExp_const]
  unfold tiltCov
  rw [← hc]
  ring

/-- **The tilted variance vanishes iff the observable is a.e. constant on the support of the
weight.** -/
theorem TiltData.tiltCov_self_eq_zero_iff {ν R : X → ℝ} {M : ℝ} (h : TiltData μ ν R M)
    {f : X → ℝ} (hf : Bdd f) (t u : ℝ) :
    tiltCov μ ν f f R t u = 0 ↔ ∀ᵐ x ∂μ, ν x ≠ 0 → f x = tiltExp μ ν f R t u := by
  rw [h.tiltCov_self_eq_tiltExp_sq hf]
  set c := tiltExp μ ν f R t u with hc
  obtain ⟨hfm, Mf, hfb⟩ := hf
  have hg : Bdd fun x ↦ (f x - c) ^ 2 :=
    ⟨(hfm.sub measurable_const).pow_const 2, (Mf + |c|) ^ 2, fun x ↦ by
      rw [abs_pow]
      exact pow_le_pow_left₀ (abs_nonneg _) ((abs_sub _ _).trans (add_le_add (hfb x) le_rfl)) 2⟩
  obtain ⟨hgm, Mg, hgb⟩ := hg
  unfold tiltExp
  rw [div_eq_zero_iff, or_iff_left (h.tiltNum_one_pos t u).ne']
  unfold tiltNum
  rw [integral_eq_zero_iff_of_nonneg (fun x ↦ mul_nonneg (mul_nonneg (sq_nonneg _)
    (Real.exp_pos _).le) (h.ν_nonneg x)) (h.integrable_tilt hgm hgb t u)]
  refine Filter.eventually_congr (Filter.Eventually.of_forall fun x ↦ ?_)
  simp only [Pi.zero_apply]
  constructor
  · intro h0 hν
    rcases mul_eq_zero.mp h0 with h1 | h1
    · rcases mul_eq_zero.mp h1 with h2 | h2
      · exact sub_eq_zero.mp (pow_eq_zero_iff two_ne_zero |>.mp h2)
      · exact absurd h2 (Real.exp_pos _).ne'
    · exact absurd h1 hν
  · intro h0
    by_cases hν : ν x = 0
    · simp [hν]
    · simp [h0 hν]

section Affine

variable {ι : Type*} [Fintype ι] {π L₀ : X → ℝ} {R : ι → X → ℝ} {a : ι → ℝ} {t M₀ : ℝ}

/-- **The nullspace of the response form**: for `t ≠ 0`, `g_a(v, v) = 0` iff the direction loss
`R_v` is a.e. constant (equal to its posterior mean) on the support of the prior — the invisible
data directions are those that shift the loss by a constant. -/
theorem TiltData.responseForm_self_eq_zero_iff
    (h : TiltData μ (baseWeight π (affLoss L₀ R a) t) (fun _ ↦ 0) M₀) (hR : ∀ i, Bdd (R i))
    (ht : t ≠ 0) (v : ι → ℝ) :
    responseForm μ π L₀ R a t v v = 0 ↔
      ∀ᵐ x ∂μ, π x ≠ 0 → dirLoss R v x = priorExp μ π (affLoss L₀ R a) (dirLoss R v) t := by
  unfold responseForm
  rw [mul_eq_zero, or_iff_right (pow_ne_zero 2 ht), priorCov_eq_tiltCov_zero (R := fun _ ↦ (0 : ℝ)),
    h.tiltCov_self_eq_zero_iff (bdd_dirLoss hR v), priorExp_eq_tiltExp_zero (R := fun _ ↦ (0 : ℝ))]
  refine Filter.eventually_congr (Filter.Eventually.of_forall fun x ↦ ?_)
  simp only [baseWeight, ne_eq, mul_eq_zero, (Real.exp_pos _).ne', false_or]

end Affine

end Laplace.Multi
