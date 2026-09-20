/-
Copyright (c) 2026 Timaeus Research. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniel Murfet
-/
import Mathlib
import Laplace.Multi.WeightedTaylor

/-!
# Coercivity of a quasi-homogeneous leading part from positivity

The natural-power coercivity `|u i|^D ≤ κ P(u)^{a i}` used throughout the weighted-jet
induction follows from continuity and strict positivity away from the origin. The weighted
gauge `g(u) = ∑ i, |u i|^{D / a i}` scales exactly like `P` under the dilation; its unit
sphere is compact, `P` attains a positive minimum `m` there, every `u ≠ 0` is a dilate of a
point of the sphere, so `P u ≥ m · g(u) ≥ m · |u i|^{D/a i}`, and raising to the power `a i`
gives the natural-power bound with `κ = ∑ i, m^{-a i}`.

Headline: `analytic_weighted_germ_recovery_of_pos`, the analytic recovery theorem with the
coercivity hypothesis replaced by `∀ u ≠ 0, 0 < P u`.
-/

open Real MeasureTheory Filter Topology

namespace Laplace.Multi

namespace IntWeights

variable {ι : Type*} [Fintype ι] (W : IntWeights ι)

/-- The weighted gauge `∑ i, |u i|^{D / a i}`, homogeneous of degree `D` under the dilation. -/
noncomputable def gauge (u : ι → ℝ) : ℝ := ∑ i, |u i| ^ ((W.D : ℝ) / W.a i)

theorem gauge_nonneg (u : ι → ℝ) : 0 ≤ W.gauge u :=
  Finset.sum_nonneg fun _ _ ↦ Real.rpow_nonneg (abs_nonneg _) _

omit [Fintype ι] in
theorem exponent_pos (i : ι) : (0 : ℝ) < (W.D : ℝ) / W.a i :=
  div_pos (by exact_mod_cast W.D_pos) (by exact_mod_cast W.a_pos i)

theorem continuous_gauge : Continuous W.gauge := by
  unfold gauge
  refine continuous_finsetSum _ fun i _ ↦ ?_
  exact (Real.continuous_rpow_const (W.exponent_pos i).le).comp (continuous_apply i).abs

theorem gauge_dil {ε : ℝ} (hε : 0 < ε) (u : ι → ℝ) : W.gauge (W.dil ε u) = ε ^ W.D * W.gauge u := by
  unfold gauge
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  have hai : (W.a i : ℝ) ≠ 0 := by exact_mod_cast (W.a_pos i).ne'
  rw [dil_apply, abs_mul, abs_of_pos (pow_pos hε _), Real.mul_rpow (pow_nonneg hε.le _)
    (abs_nonneg _), ← Real.rpow_natCast, ← Real.rpow_mul hε.le, mul_div_cancel₀ _ hai,
    Real.rpow_natCast]

theorem abs_rpow_le_gauge (u : ι → ℝ) (i : ι) : |u i| ^ ((W.D : ℝ) / W.a i) ≤ W.gauge u :=
  Finset.single_le_sum (f := fun j ↦ |u j| ^ ((W.D : ℝ) / W.a j))
    (fun _ _ ↦ Real.rpow_nonneg (abs_nonneg _) _) (Finset.mem_univ i)

theorem gauge_pos_of_ne_zero {u : ι → ℝ} (hu : u ≠ 0) : 0 < W.gauge u := by
  obtain ⟨i, hi⟩ : ∃ i, u i ≠ 0 := by
    by_contra h
    exact hu (funext fun i ↦ not_not.mp fun h' ↦ h ⟨i, h'⟩)
  have h1 : 0 < |u i| ^ ((W.D : ℝ) / W.a i) := Real.rpow_pos_of_pos (abs_pos.mpr hi) _
  exact lt_of_lt_of_le h1 (W.abs_rpow_le_gauge u i)

/-- The weighted unit sphere `{g = 1}` is compact. -/
theorem isCompact_gauge_sphere : IsCompact {v : ι → ℝ | W.gauge v = 1} := by
  refine Metric.isCompact_of_isClosed_isBounded (isClosed_eq W.continuous_gauge continuous_const) ?_
  rw [Metric.isBounded_iff_subset_closedBall (0 : ι → ℝ)]
  refine ⟨1, fun v hv ↦ ?_⟩
  rw [Metric.mem_closedBall, dist_zero_right, pi_norm_le_iff_of_nonneg zero_le_one]
  intro i
  rw [Real.norm_eq_abs]
  by_contra h
  have h1 : 1 < |v i| ^ ((W.D : ℝ) / W.a i) := Real.one_lt_rpow (lt_of_not_ge h) (W.exponent_pos i)
  have h2 := W.abs_rpow_le_gauge v i
  have hv' : W.gauge v = 1 := hv
  linarith

/-- The weighted sphere is nonempty when there is at least one coordinate. -/
theorem gauge_sphere_nonempty [Nonempty ι] :
    ({v : ι → ℝ | W.gauge v = 1} : Set (ι → ℝ)).Nonempty := by
  classical
  obtain ⟨i₀⟩ := ‹Nonempty ι›
  refine ⟨Pi.single i₀ 1, ?_⟩
  change W.gauge (Pi.single i₀ 1) = 1
  unfold gauge
  rw [Finset.sum_eq_single i₀]
  · simp
  · intro j _ hj
    simp [hj, Real.zero_rpow (W.exponent_pos j).ne']
  · intro h
    exact absurd (Finset.mem_univ i₀) h

omit [Fintype ι] in
/-- **Coercivity from positivity**: a continuous quasi-homogeneous `P` that is positive away
from the origin satisfies `|u i|^D ≤ κ P(u)^{a i}` for some `κ ≥ 0`. -/
theorem exists_coercive_of_pos [Finite ι] {P : (ι → ℝ) → ℝ} (hPc : Continuous P)
    (hP0 : ∀ u, 0 ≤ P u)
    (hPqh : ∀ ε : ℝ, 0 < ε → ∀ u, P (W.dil ε u) = ε ^ W.D * P u)
    (hPpos : ∀ u, u ≠ 0 → 0 < P u) :
    ∃ κ : ℝ, 0 ≤ κ ∧ ∀ u i, |u i| ^ W.D ≤ κ * P u ^ W.a i := by
  have := Fintype.ofFinite ι
  rcases isEmpty_or_nonempty ι with hι | hι
  · exact ⟨0, le_rfl, fun _ i ↦ (hι.false i).elim⟩
  -- the minimum of `P` on the weighted sphere
  obtain ⟨v₀, hv₀, hmin⟩ := W.isCompact_gauge_sphere.exists_isMinOn W.gauge_sphere_nonempty
    hPc.continuousOn
  have hv₀ne : v₀ ≠ 0 := by
    intro h
    have : W.gauge v₀ = 1 := hv₀
    rw [h] at this
    unfold gauge at this
    simp [Real.zero_rpow (W.exponent_pos _).ne'] at this
  set m : ℝ := P v₀ with hm_def
  have hm : 0 < m := hPpos v₀ hv₀ne
  -- `P u ≥ m · gauge u`
  have hlow : ∀ u, m * W.gauge u ≤ P u := by
    intro u
    rcases eq_or_ne u 0 with rfl | hu
    · have : W.gauge 0 = 0 := by
        unfold gauge
        simp [Real.zero_rpow (W.exponent_pos _).ne']
      rw [this, mul_zero]
      exact hP0 0
    · have hg := W.gauge_pos_of_ne_zero hu
      set ε : ℝ := W.gauge u ^ ((W.D : ℝ)⁻¹) with hε_def
      have hε : 0 < ε := Real.rpow_pos_of_pos hg _
      have hεD : ε ^ W.D = W.gauge u := Real.rpow_inv_natCast_pow hg.le W.D_pos.ne'
      have hεinv : 0 < ε⁻¹ := inv_pos.mpr hε
      set v : ι → ℝ := W.dil ε⁻¹ u with hv_def
      have hdil : W.dil ε v = u := by
        funext i
        simp only [hv_def, dil_apply]
        rw [← mul_assoc, ← mul_pow, mul_inv_cancel₀ hε.ne', one_pow, one_mul]
      have hgv : W.gauge v = 1 := by
        rw [hv_def, W.gauge_dil hεinv, inv_pow, hεD, inv_mul_cancel₀ hg.ne']
      have hPv : m ≤ P v := hmin (show v ∈ {v : ι → ℝ | W.gauge v = 1} from hgv)
      calc m * W.gauge u = ε ^ W.D * m := by rw [hεD, mul_comm]
        _ ≤ ε ^ W.D * P v := mul_le_mul_of_nonneg_left hPv (pow_pos hε _).le
        _ = P u := by rw [← hPqh ε hε, hdil]
  -- the natural-power bound
  refine ⟨∑ i, (m⁻¹) ^ W.a i, Finset.sum_nonneg fun i _ ↦ by positivity, fun u i ↦ ?_⟩
  have hai : (W.a i : ℝ) ≠ 0 := by exact_mod_cast (W.a_pos i).ne'
  have h1 : |u i| ^ ((W.D : ℝ) / W.a i) ≤ m⁻¹ * P u := by
    calc |u i| ^ ((W.D : ℝ) / W.a i) ≤ W.gauge u := W.abs_rpow_le_gauge u i
      _ ≤ m⁻¹ * P u := by
          rw [← div_eq_inv_mul]
          exact (le_div_iff₀' hm).mpr (hlow u)
  have h2 : (|u i| ^ ((W.D : ℝ) / W.a i)) ^ W.a i = |u i| ^ W.D := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul (abs_nonneg _), div_mul_cancel₀ _ hai,
      Real.rpow_natCast]
  calc |u i| ^ W.D = (|u i| ^ ((W.D : ℝ) / W.a i)) ^ W.a i := h2.symm
    _ ≤ (m⁻¹ * P u) ^ W.a i := pow_le_pow_left₀ (Real.rpow_nonneg (abs_nonneg _) _) h1 _
    _ = (m⁻¹) ^ W.a i * P u ^ W.a i := mul_pow _ _ _
    _ ≤ (∑ j, (m⁻¹) ^ W.a j) * P u ^ W.a i := by
        apply mul_le_mul_of_nonneg_right _ (pow_nonneg (hP0 u) _)
        exact Finset.single_le_sum (f := fun j ↦ (m⁻¹) ^ W.a j) (fun j _ ↦ by positivity)
          (Finset.mem_univ i)

/-- **Analytic semi-quasi-homogeneous germ recovery, positivity form**: as
`analytic_weighted_germ_recovery`, with coercivity replaced by strict positivity of the leading
part away from the origin. -/
theorem analytic_weighted_germ_recovery_of_pos [DecidableEq ι] {P L₁ L₂ : (ι → ℝ) → ℝ}
    (hPc : Continuous P) (hP0 : ∀ u, 0 ≤ P u)
    (hPqh : ∀ ε : ℝ, 0 < ε → ∀ u, P (W.dil ε u) = ε ^ W.D * P u)
    (hPpos : ∀ u, u ≠ 0 → 0 < P u)
    (hint : Integrable fun u : ι → ℝ ↦ Real.exp (-P u))
    (hL₁ : Measurable L₁) (hL₂ : Measurable L₂)
    {p₁ p₂ : FormalMultilinearSeries ℝ (ι → ℝ) ℝ} {r₁ r₂ : ENNReal}
    (h₁ : HasFPowerSeriesOnBall L₁ p₁ 0 r₁) (h₂ : HasFPowerSeriesOnBall L₂ p₂ 0 r₂)
    (hP₁ : ∀ x, P x = ∑ α ∈ W.lowSet, taylorCoeff p₁ (totalDeg α) α * mvMonomial α x)
    (hP₂ : ∀ x, P x = ∑ α ∈ W.lowSet, taylorCoeff p₂ (totalDeg α) α * mvMonomial α x)
    {r' : NNReal} (hr'0 : 0 < r') (hr'₁ : (r' : ENNReal) < r₁) (hr'₂ : (r' : ENNReal) < r₂) :
    ∃ δ₀ : ℝ, 0 < δ₀ ∧ ∀ δ : ℝ, 0 < δ → δ ≤ δ₀ →
      (∀ α : ι → ℕ, W.D < W.wdeg α → Laplace.SuperPoly fun t : ℝ ↦
        tempMoment (Metric.ball (0 : ι → ℝ) r' ∩ {x | P x ≤ δ}) L₂ (mvMonomial α) t -
          tempMoment (Metric.ball (0 : ι → ℝ) r' ∩ {x | P x ≤ δ}) L₁ (mvMonomial α) t) →
      ∀ᶠ y in 𝓝 (0 : ι → ℝ), L₁ y = L₂ y := by
  obtain ⟨κ, hκ, hcoer⟩ := W.exists_coercive_of_pos hPc hP0 hPqh hPpos
  exact W.analytic_weighted_germ_recovery hPc hP0 hPqh hint hκ hcoer hL₁ hL₂ h₁ h₂ hP₁ hP₂ hr'0
    hr'₁ hr'₂

end IntWeights

end Laplace.Multi
