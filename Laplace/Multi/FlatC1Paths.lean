/-
Copyright (c) 2026 Timaeus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Timaeus
-/
import Mathlib

/-!
# Flat `C¹` paths: smoothstep reparametrisation, reversal and pasting

Generic (Mathlib-only) infrastructure for the intrinsic Fisher distance. A *flat* `C¹` path on
`[0,1]` is a globally differentiable path with continuous velocity vanishing at both endpoints.
The cubic smoothstep `φ(t) = 3t² − 2t³` flattens any `C¹` path without changing its length
(change of variables `∫₀¹ f(φ) φ' = ∫₀¹ f`), and two flat paths with matching endpoints paste to a
flat path (`catPath`), the derivative at the junction being the common value `0` of the two
one-sided derivatives.
-/

open Set Filter Topology

namespace Laplace.Multi

section Smoothstep

/-- The cubic smoothstep `φ(t) = 3t² − 2t³`. -/
noncomputable def smoothStep (t : ℝ) : ℝ := 3 * t ^ 2 - 2 * t ^ 3

/-- The derivative `φ'(t) = 6t − 6t²` of the smoothstep. -/
noncomputable def smoothStepDeriv (t : ℝ) : ℝ := 6 * t - 6 * t ^ 2

theorem hasDerivAt_smoothStep (t : ℝ) : HasDerivAt smoothStep (smoothStepDeriv t) t := by
  have h := ((hasDerivAt_pow 2 t).const_mul 3).sub ((hasDerivAt_pow 3 t).const_mul 2)
  unfold smoothStep smoothStepDeriv
  exact h.congr_deriv (by simp; ring)

theorem smoothStep_zero : smoothStep 0 = 0 := by simp [smoothStep]

theorem smoothStep_one : smoothStep 1 = 1 := by norm_num [smoothStep]

theorem smoothStepDeriv_zero : smoothStepDeriv 0 = 0 := by simp [smoothStepDeriv]

theorem smoothStepDeriv_one : smoothStepDeriv 1 = 0 := by norm_num [smoothStepDeriv]

theorem smoothStepDeriv_nonneg {t : ℝ} (h0 : 0 ≤ t) (h1 : t ≤ 1) : 0 ≤ smoothStepDeriv t := by
  unfold smoothStepDeriv
  nlinarith

theorem continuous_smoothStep : Continuous smoothStep := by
  unfold smoothStep
  fun_prop

theorem continuous_smoothStepDeriv : Continuous smoothStepDeriv := by
  unfold smoothStepDeriv
  fun_prop

theorem smoothStep_mem_Icc {t : ℝ} (h0 : 0 ≤ t) (h1 : t ≤ 1) : smoothStep t ∈ Icc 0 1 := by
  unfold smoothStep
  constructor
  · nlinarith [mul_nonneg (mul_nonneg h0 h0) (sub_nonneg.2 h1)]
  · nlinarith [mul_nonneg (sq_nonneg (1 - t)) (by linarith : (0 : ℝ) ≤ 1 + 2 * t)]

/-- **Change of variables along the smoothstep**: `∫₀¹ f(φ(t)) φ'(t) dt = ∫₀¹ f`. -/
theorem integral_comp_smoothStep {f : ℝ → ℝ} (hf : Continuous f) :
    ∫ t in (0 : ℝ)..1, f (smoothStep t) * smoothStepDeriv t = ∫ s in (0 : ℝ)..1, f s := by
  have h := intervalIntegral.integral_comp_mul_deriv' (a := 0) (b := 1) (f := smoothStep)
    (f' := smoothStepDeriv) (g := f) (fun x _ ↦ hasDerivAt_smoothStep x)
    continuous_smoothStepDeriv.continuousOn hf.continuousOn
  rw [smoothStep_zero, smoothStep_one] at h
  exact h

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- Flattening a `C¹` path: the reparametrised path `γ ∘ φ` has velocity `φ' • γ' ∘ φ`. -/
theorem hasDerivAt_comp_smoothStep {γ γ' : ℝ → E} (hγ : ∀ t, HasDerivAt γ (γ' t) t) (t : ℝ) :
    HasDerivAt (fun t ↦ γ (smoothStep t)) (smoothStepDeriv t • γ' (smoothStep t)) t :=
  (hγ _).scomp t (hasDerivAt_smoothStep t)

theorem continuous_smoothStepDeriv_smul {γ' : ℝ → E} (hγ' : Continuous γ') :
    Continuous fun t ↦ smoothStepDeriv t • γ' (smoothStep t) :=
  continuous_smoothStepDeriv.smul (hγ'.comp continuous_smoothStep)

end Smoothstep

section Paste

variable {E : Type*}

/-- Concatenation of two paths on `[0,1]`, each traversed at double speed. -/
noncomputable def catPath (p q : ℝ → E) (t : ℝ) : E :=
  if t ≤ 1 / 2 then p (2 * t) else q (2 * t - 1)

theorem catPath_zero (p q : ℝ → E) : catPath p q 0 = p 0 := by simp [catPath]

theorem catPath_one (p q : ℝ → E) : catPath p q 1 = q 1 := by norm_num [catPath]

theorem catPath_of_le (p q : ℝ → E) {t : ℝ} (ht : t ≤ 1 / 2) : catPath p q t = p (2 * t) :=
  if_pos ht

theorem catPath_of_lt (p q : ℝ → E) {t : ℝ} (ht : 1 / 2 < t) : catPath p q t = q (2 * t - 1) :=
  if_neg (not_le.2 ht)

variable [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- Reversal of a path on `[0,1]`. -/
theorem hasDerivAt_rev {γ γ' : ℝ → E} (hγ : ∀ t, HasDerivAt γ (γ' t) t) (t : ℝ) :
    HasDerivAt (fun t ↦ γ (1 - t)) (-γ' (1 - t)) t := by
  have h := (hγ (1 - t)).scomp t ((hasDerivAt_id t).const_sub 1)
  rw [neg_one_smul] at h
  exact h

/-- The velocity of the concatenation. -/
noncomputable def catVel (p' q' : ℝ → E) (t : ℝ) : E :=
  if t ≤ 1 / 2 then (2 : ℝ) • p' (2 * t) else (2 : ℝ) • q' (2 * t - 1)

theorem catVel_zero (p' q' : ℝ → E) : catVel p' q' 0 = (2 : ℝ) • p' 0 := by simp [catVel]

theorem catVel_one (p' q' : ℝ → E) : catVel p' q' 1 = (2 : ℝ) • q' 1 := by norm_num [catVel]

theorem catVel_of_le (p' q' : ℝ → E) {t : ℝ} (ht : t ≤ 1 / 2) :
    catVel p' q' t = (2 : ℝ) • p' (2 * t) :=
  if_pos ht

theorem catVel_of_lt (p' q' : ℝ → E) {t : ℝ} (ht : 1 / 2 < t) :
    catVel p' q' t = (2 : ℝ) • q' (2 * t - 1) :=
  if_neg (not_le.2 ht)

theorem hasDerivAt_double {p p' : ℝ → E} (hp : ∀ t, HasDerivAt p (p' t) t) (t : ℝ) :
    HasDerivAt (fun t ↦ p (2 * t)) ((2 : ℝ) • p' (2 * t)) t := by
  have h := (hp (2 * t)).scomp t ((hasDerivAt_id' (x := t)).const_mul (2 : ℝ))
  rw [mul_one] at h
  exact h

theorem hasDerivAt_double_sub {q q' : ℝ → E} (hq : ∀ t, HasDerivAt q (q' t) t) (t : ℝ) :
    HasDerivAt (fun t ↦ q (2 * t - 1)) ((2 : ℝ) • q' (2 * t - 1)) t := by
  have h := (hq (2 * t - 1)).scomp t (((hasDerivAt_id' (x := t)).const_mul (2 : ℝ)).sub_const 1)
  rw [mul_one] at h
  exact h

/-- **The pasting lemma**: two `C¹` paths with matching endpoints and vanishing velocities at
the junction concatenate to a `C¹` path. -/
theorem hasDerivAt_catPath {p q p' q' : ℝ → E} (hp : ∀ t, HasDerivAt p (p' t) t)
    (hq : ∀ t, HasDerivAt q (q' t) t) (hpq : p 1 = q 0) (hp1 : p' 1 = 0) (hq0 : q' 0 = 0)
    (t : ℝ) : HasDerivAt (catPath p q) (catVel p' q' t) t := by
  rcases lt_trichotomy t (1 / 2) with h | h | h
  · have hev : catPath p q =ᶠ[𝓝 t] fun t ↦ p (2 * t) :=
      Filter.eventuallyEq_of_mem (Iio_mem_nhds h) fun s hs ↦ catPath_of_le p q (le_of_lt hs)
    rw [catVel_of_le p' q' h.le]
    exact (hasDerivAt_double hp t).congr_of_eventuallyEq hev
  · subst h
    have h1 : HasDerivWithinAt (catPath p q) ((2 : ℝ) • p' (2 * (1 / 2))) (Iic (1 / 2))
        (1 / 2) :=
      (hasDerivAt_double hp _).hasDerivWithinAt.congr (fun s hs ↦ catPath_of_le p q hs)
        (catPath_of_le p q le_rfl)
    have h2 : HasDerivWithinAt (catPath p q) ((2 : ℝ) • q' (2 * (1 / 2) - 1)) (Ici (1 / 2))
        (1 / 2) := by
      refine (hasDerivAt_double_sub hq _).hasDerivWithinAt.congr (fun s hs ↦ ?_) ?_
      · rcases eq_or_lt_of_le (mem_Ici.1 hs) with hs' | hs'
        · rw [← hs', catPath_of_le p q le_rfl]
          norm_num [hpq]
        · exact catPath_of_lt p q hs'
      · rw [catPath_of_le p q le_rfl]
        norm_num [hpq]
    have hval : (2 : ℝ) • q' (2 * (1 / 2) - 1) = (2 : ℝ) • p' (2 * (1 / 2)) := by
      norm_num [hp1, hq0]
    rw [hval] at h2
    rw [catVel_of_le p' q' le_rfl, ← hasDerivWithinAt_univ, ← Set.Iic_union_Ici]
    exact h1.union h2
  · have hev : catPath p q =ᶠ[𝓝 t] fun t ↦ q (2 * t - 1) :=
      Filter.eventuallyEq_of_mem (Ioi_mem_nhds h) fun s hs ↦ catPath_of_lt p q hs
    rw [catVel_of_lt p' q' h]
    exact (hasDerivAt_double_sub hq t).congr_of_eventuallyEq hev

/-- The velocity of the concatenation is continuous when the junction velocities vanish. -/
theorem continuous_catVel {p' q' : ℝ → E} (hp' : Continuous p') (hq' : Continuous q')
    (hp1 : p' 1 = 0) (hq0 : q' 0 = 0) : Continuous (catVel p' q') := by
  refine Continuous.if_le ((hp'.comp (continuous_const.mul continuous_id)).const_smul _)
    ((hq'.comp ((continuous_const.mul continuous_id).sub continuous_const)).const_smul _)
    continuous_id continuous_const fun t ht ↦ ?_
  rw [ht]
  norm_num [hp1, hq0]

end Paste

end Laplace.Multi
