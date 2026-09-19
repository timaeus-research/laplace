/-
Copyright (c) 2026 Timaeus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Timaeus
-/
import Mathlib
import Laplace.Multi.ProjectiveClosure
import Laplace.Multi.TotalVariation
import Laplace.Multi.LocalUniform

/-!
# The normalized closure with the anchor discharged

`ProjectiveClosure.normalized_expectations_closure` takes normalized
agreement `Φ_{L₁} = Φ_{L₂}` (common window `χ`, positive partition values)
and returns equal zero sets, local equality, `Z₂/Z₁ = 1 + o(t^{-∞})`, and
exact agreement of smooth compactly supported moments.
`TotalVariation.superPoly_normalized_difference_of_bounded` extends the
last conclusion to bounded compactly supported tests *provided* the
partition values carry polynomial lower bounds. Here those bounds are
discharged from the anchor (`anchor_lower_bound_eventually`) under one
extra hypothesis on the window: `χ = 1` near some zero of `L₁`. The
results:

* `normalized_expectations_closure_bounded`: normalized agreement of
  every bounded measurable compactly supported test, hence of every
  continuous one.
* `eventually_uniform_normalized_density_le`: the normalized densities
  `e^{-tL_i}/Z_i` agree uniformly on compacts beyond all orders, via
  `w₂/Z₂ - w₁/Z₁ = h_t/Z₂ - (w₁/Z₂)(Z₂/Z₁ - 1)` with `0 ≤ w₁ ≤ 1`.
-/

open Asymptotics Filter MeasureTheory
open scoped ENNReal Topology ContDiff

namespace Laplace

variable {ι : Type*} [Fintype ι]

/-- **Normalized agreement of bounded tests, anchor discharged.** Smooth
nonnegative losses analytic at their zeros, both with zeros; a nonnegative
compactly supported window equal to `1` near a zero `p₀` of `L₁`, with
positive partition values; normalized agreement on smooth tests. Then the
normalized moments of every bounded measurable compactly supported test
agree beyond all orders. -/
theorem normalized_expectations_closure_bounded {L₁ L₂ χ : (ι → ℝ) → ℝ}
    (h1 : ContDiff ℝ ∞ L₁) (h2 : ContDiff ℝ ∞ L₂)
    (hL1 : ∀ w, 0 ≤ L₁ w) (hL2 : ∀ w, 0 ≤ L₂ w)
    (hA1 : ∀ p, L₁ p = 0 → AnalyticAt ℝ L₁ p) (hA2 : ∀ p, L₂ p = 0 → AnalyticAt ℝ L₂ p)
    (hne2 : ∃ q, L₂ q = 0)
    (hχc : Continuous χ) (hχs : HasCompactSupport χ) (hχ0 : ∀ w, 0 ≤ χ w)
    {p₀ : ι → ℝ} (hp₀ : L₁ p₀ = 0) (hχ1 : ∀ᶠ w in 𝓝 p₀, χ w = 1)
    (hZ1 : ∀ t : ℝ, 0 < ∫ w, χ w * Real.exp (-(t * L₁ w)))
    (hZ2 : ∀ t : ℝ, 0 < ∫ w, χ w * Real.exp (-(t * L₂ w)))
    (hfam : ∀ φ : (ι → ℝ) → ℝ, ContDiff ℝ ∞ φ → HasCompactSupport φ →
      SuperPoly fun t ↦
        (∫ w, φ w * Real.exp (-(t * L₂ w))) / (∫ w, χ w * Real.exp (-(t * L₂ w)))
        - (∫ w, φ w * Real.exp (-(t * L₁ w))) / (∫ w, χ w * Real.exp (-(t * L₁ w))))
    {φ : (ι → ℝ) → ℝ} (hφm : AEStronglyMeasurable φ (volume : Measure (ι → ℝ)))
    (hφs : HasCompactSupport φ) {M : ℝ} (hφM : ∀ w, |φ w| ≤ M) :
    SuperPoly fun t ↦
      (∫ w, φ w * Real.exp (-(t * L₂ w))) / (∫ w, χ w * Real.exp (-(t * L₂ w)))
      - (∫ w, φ w * Real.exp (-(t * L₁ w))) / (∫ w, χ w * Real.exp (-(t * L₁ w))) := by
  obtain ⟨hzero, _, hratio, hexact⟩ := normalized_expectations_closure h1 h2 hL1 hL2 hA1 hA2
    ⟨p₀, hp₀⟩ hne2 hχc hχs hχ0 hZ1 hZ2 hfam
  have hq₀ : L₂ p₀ = 0 := (hzero p₀).mp hp₀
  obtain ⟨κ₁, hκ₁, hZ1low⟩ := anchor_lower_bound_eventually h1.continuous hL1 hp₀
    (hA1 p₀ hp₀).contDiffAt hχc hχs hχ0 hχ1
  obtain ⟨κ₂, hκ₂, hZ2low⟩ := anchor_lower_bound_eventually h2.continuous hL2 hq₀
    (hA2 p₀ hq₀).contDiffAt hχc hχs hχ0 hχ1
  exact superPoly_normalized_difference_of_bounded h1 h2 hL1 hL2 hexact hZ1 hZ2 hκ₁ hκ₂
    hZ1low hZ2low hratio hφm hφs hφM

/-- The continuous-test specialisation. -/
theorem normalized_expectations_closure_continuous {L₁ L₂ χ : (ι → ℝ) → ℝ}
    (h1 : ContDiff ℝ ∞ L₁) (h2 : ContDiff ℝ ∞ L₂)
    (hL1 : ∀ w, 0 ≤ L₁ w) (hL2 : ∀ w, 0 ≤ L₂ w)
    (hA1 : ∀ p, L₁ p = 0 → AnalyticAt ℝ L₁ p) (hA2 : ∀ p, L₂ p = 0 → AnalyticAt ℝ L₂ p)
    (hne2 : ∃ q, L₂ q = 0)
    (hχc : Continuous χ) (hχs : HasCompactSupport χ) (hχ0 : ∀ w, 0 ≤ χ w)
    {p₀ : ι → ℝ} (hp₀ : L₁ p₀ = 0) (hχ1 : ∀ᶠ w in 𝓝 p₀, χ w = 1)
    (hZ1 : ∀ t : ℝ, 0 < ∫ w, χ w * Real.exp (-(t * L₁ w)))
    (hZ2 : ∀ t : ℝ, 0 < ∫ w, χ w * Real.exp (-(t * L₂ w)))
    (hfam : ∀ φ : (ι → ℝ) → ℝ, ContDiff ℝ ∞ φ → HasCompactSupport φ →
      SuperPoly fun t ↦
        (∫ w, φ w * Real.exp (-(t * L₂ w))) / (∫ w, χ w * Real.exp (-(t * L₂ w)))
        - (∫ w, φ w * Real.exp (-(t * L₁ w))) / (∫ w, χ w * Real.exp (-(t * L₁ w))))
    {φ : (ι → ℝ) → ℝ} (hφc : Continuous φ) (hφs : HasCompactSupport φ) :
    SuperPoly fun t ↦
      (∫ w, φ w * Real.exp (-(t * L₂ w))) / (∫ w, χ w * Real.exp (-(t * L₂ w)))
      - (∫ w, φ w * Real.exp (-(t * L₁ w))) / (∫ w, χ w * Real.exp (-(t * L₁ w))) := by
  obtain ⟨M, hM⟩ := hφs.exists_bound_of_continuous hφc
  exact normalized_expectations_closure_bounded h1 h2 hL1 hL2 hA1 hA2 hne2 hχc hχs hχ0 hp₀ hχ1
    hZ1 hZ2 hfam hφc.aestronglyMeasurable hφs (M := M) fun w ↦ by
      simpa [Real.norm_eq_abs] using hM w

/-- **Uniform agreement of the normalized densities.** Under the same
hypotheses, for every compact `K` and every `N` there is `C` with
`|e^{-tL₂ x}/Z₂ - e^{-tL₁ x}/Z₁| ≤ C t^{-N}` for all `x ∈ K`, eventually. -/
theorem eventually_uniform_normalized_density_le {L₁ L₂ χ : (ι → ℝ) → ℝ}
    (h1 : ContDiff ℝ ∞ L₁) (h2 : ContDiff ℝ ∞ L₂)
    (hL1 : ∀ w, 0 ≤ L₁ w) (hL2 : ∀ w, 0 ≤ L₂ w)
    (hA1 : ∀ p, L₁ p = 0 → AnalyticAt ℝ L₁ p) (hA2 : ∀ p, L₂ p = 0 → AnalyticAt ℝ L₂ p)
    (hne2 : ∃ q, L₂ q = 0)
    (hχc : Continuous χ) (hχs : HasCompactSupport χ) (hχ0 : ∀ w, 0 ≤ χ w)
    {p₀ : ι → ℝ} (hp₀ : L₁ p₀ = 0) (hχ1 : ∀ᶠ w in 𝓝 p₀, χ w = 1)
    (hZ1 : ∀ t : ℝ, 0 < ∫ w, χ w * Real.exp (-(t * L₁ w)))
    (hZ2 : ∀ t : ℝ, 0 < ∫ w, χ w * Real.exp (-(t * L₂ w)))
    (hfam : ∀ φ : (ι → ℝ) → ℝ, ContDiff ℝ ∞ φ → HasCompactSupport φ →
      SuperPoly fun t ↦
        (∫ w, φ w * Real.exp (-(t * L₂ w))) / (∫ w, χ w * Real.exp (-(t * L₂ w)))
        - (∫ w, φ w * Real.exp (-(t * L₁ w))) / (∫ w, χ w * Real.exp (-(t * L₁ w))))
    {K : Set (ι → ℝ)} (hK : IsCompact K) :
    ∀ N : ℕ, ∃ C : ℝ, ∀ᶠ t in atTop, ∀ x ∈ K,
      |Real.exp (-(t * L₂ x)) / (∫ w, χ w * Real.exp (-(t * L₂ w))) -
        Real.exp (-(t * L₁ x)) / (∫ w, χ w * Real.exp (-(t * L₁ w)))| ≤
          C * t ^ (-(N : ℝ)) := by
  obtain ⟨hzero, _, hratio, hexact⟩ := normalized_expectations_closure h1 h2 hL1 hL2 hA1 hA2
    ⟨p₀, hp₀⟩ hne2 hχc hχs hχ0 hZ1 hZ2 hfam
  have hq₀ : L₂ p₀ = 0 := (hzero p₀).mp hp₀
  obtain ⟨κ₂, hκ₂, hZ2low⟩ := anchor_lower_bound_eventually h2.continuous hL2 hq₀
    (hA2 p₀ hq₀).contDiffAt hχc hχs hχ0 hχ1
  set d := Fintype.card ι with hd
  intro N
  obtain ⟨C₁, hC₁⟩ := eventually_uniform_abs_exp_sub_le h1 h2 hL1 hL2 hexact hK (N + d)
  set C₁' := max C₁ 0 with hC₁'_def
  have hC₁'0 : 0 ≤ C₁' := le_max_right _ _
  refine ⟨(C₁' + 1) / κ₂, ?_⟩
  have hρ := isLittleO_iff.mp (hratio (N + d)) one_pos
  filter_upwards [hC₁, hZ2low, hρ, eventually_gt_atTop (0 : ℝ)] with t hAt hZt hρt htpos
  intro x hx
  set Z₁ := ∫ w, χ w * Real.exp (-(t * L₁ w)) with hZ₁
  set Z₂ := ∫ w, χ w * Real.exp (-(t * L₂ w)) with hZ₂
  set w₁ := Real.exp (-(t * L₁ x)) with hw₁
  set w₂ := Real.exp (-(t * L₂ x)) with hw₂
  have hZ₁pos : 0 < Z₁ := hZ1 t
  have hZ₂pos : 0 < Z₂ := hZ2 t
  rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_pos (Real.rpow_pos_of_pos htpos _),
    one_mul] at hρt
  have hAx := hAt x hx
  have hAx' : |w₂ - w₁| ≤ C₁' * t ^ (-((N + d : ℕ) : ℝ)) :=
    hAx.trans (mul_le_mul_of_nonneg_right (le_max_left _ _) (Real.rpow_pos_of_pos htpos _).le)
  have hw₁0 : 0 ≤ w₁ := (Real.exp_pos _).le
  have hw₁1 : w₁ ≤ 1 := expWeight_le_one hL1 htpos.le x
  -- the identity `w₂/Z₂ - w₁/Z₁ = (w₂ - w₁)/Z₂ - (w₁/Z₂) * (Z₂/Z₁ - 1)`
  have hid : w₂ / Z₂ - w₁ / Z₁ = (w₂ - w₁) / Z₂ - w₁ / Z₂ * (Z₂ / Z₁ - 1) := by
    field_simp
    ring
  -- the two exponents combine: `t^{-d} · t^{-N} = t^{-(N+d)}`
  have hexp : t ^ (-(d : ℝ)) * t ^ (-(N : ℝ)) = t ^ (-((N + d : ℕ) : ℝ)) := by
    rw [← Real.rpow_add htpos]
    congr 1
    push_cast
    ring
  have hZ₂inv : Z₂⁻¹ ≤ (κ₂ * t ^ (-(d : ℝ)))⁻¹ := by
    have : 0 < κ₂ * t ^ (-(d : ℝ)) := by positivity
    exact inv_anti₀ this hZt
  have hrpos : 0 < t ^ (-((N + d : ℕ) : ℝ)) := Real.rpow_pos_of_pos htpos _
  have hNpos : 0 < t ^ (-(N : ℝ)) := Real.rpow_pos_of_pos htpos _
  have hdpos : 0 < t ^ (-(d : ℝ)) := Real.rpow_pos_of_pos htpos _
  rw [hid]
  calc |(w₂ - w₁) / Z₂ - w₁ / Z₂ * (Z₂ / Z₁ - 1)|
      ≤ |(w₂ - w₁) / Z₂| + |w₁ / Z₂ * (Z₂ / Z₁ - 1)| := abs_sub _ _
    _ = |w₂ - w₁| / Z₂ + w₁ / Z₂ * |Z₂ / Z₁ - 1| := by
        rw [abs_div, abs_of_pos hZ₂pos, abs_mul, abs_div, abs_of_nonneg hw₁0,
          abs_of_pos hZ₂pos]
    _ ≤ C₁' * t ^ (-((N + d : ℕ) : ℝ)) / Z₂ + 1 / Z₂ * t ^ (-((N + d : ℕ) : ℝ)) := by
        gcongr
    _ = (C₁' + 1) * t ^ (-((N + d : ℕ) : ℝ)) * Z₂⁻¹ := by ring
    _ ≤ (C₁' + 1) * t ^ (-((N + d : ℕ) : ℝ)) * (κ₂ * t ^ (-(d : ℝ)))⁻¹ := by
        gcongr
    _ = (C₁' + 1) / κ₂ * t ^ (-(N : ℝ)) := by
        rw [← hexp]
        field_simp

end Laplace
