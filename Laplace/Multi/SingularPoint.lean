/-
Copyright (c) 2026 Timaeus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib
import Laplace.Decay
import Laplace.Multi.SingularPrep

/-!
# The composed point theorem for the singular pencil

Composes the preparation lemmas of `Laplace.Multi.SingularPrep` with the
endpoint contradiction `analytic_pencil_difference_not_superpolynomial`
into the point form of the germbij singular theorem: if two continuous
nonnegative potentials, analytic at a common zero `p`, produce Laplace
families that agree beyond all orders against every continuous compactly
supported observable, then their germs at `p` coincide
(`pencil_families_force_germ_eq_at`).

The translation to the origin is the Lebesgue substitution
`integral_add_left_eq_self`; the observable fed to the family hypothesis
is `(L₂ - L₁) · ψ(· - p)` with `ψ` the bump from
`exists_bump_one_on_ball`.
-/

open Asymptotics Filter MeasureTheory
open scoped ENNReal Topology

namespace Laplace

/-- **The germbij singular theorem, point form.** If `L₁, L₂` are
continuous, nonnegative, analytic at `p`, vanish at `p`, and for every
continuous compactly supported observable `φ` the pencil difference
`t ↦ ∫ φ (e^{-tL₁} - e^{-tL₂})` decays faster than every negative power
of `t`, then `L₁ = L₂` on a neighborhood of `p`. -/
theorem pencil_families_force_germ_eq_at
    {ι : Type*} [Fintype ι] {L₁ L₂ : (ι → ℝ) → ℝ} {p : ι → ℝ}
    (hL1c : Continuous L₁) (hL2c : Continuous L₂)
    (hL1 : ∀ w, 0 ≤ L₁ w) (hL2 : ∀ w, 0 ≤ L₂ w)
    (hA1 : AnalyticAt ℝ L₁ p) (hA2 : AnalyticAt ℝ L₂ p)
    (hp1 : L₁ p = 0) (hp2 : L₂ p = 0)
    (hfam : ∀ φ : (ι → ℝ) → ℝ, Continuous φ → HasCompactSupport φ →
      ∀ N : ℕ, (fun t : ℝ ↦ ∫ w, φ w *
          (Real.exp (-(t * L₁ w)) - Real.exp (-(t * L₂ w))))
        =o[atTop] fun t : ℝ ↦ t ^ (-(N : ℝ))) :
    ∀ᶠ w in 𝓝 p, L₁ w = L₂ w := by
  by_contra h
  have hshift : AnalyticAt ℝ (fun w : ι → ℝ ↦ p + w) 0 :=
    analyticAt_const.add analyticAt_id
  have hshift0 : (fun w : ι → ℝ ↦ p + w) 0 = p := by simp
  have hA1' : AnalyticAt ℝ (fun w ↦ L₁ (p + w)) 0 := by
    have hg : AnalyticAt ℝ L₁ ((fun w : ι → ℝ ↦ p + w) 0) := by simpa using hA1
    simpa [Function.comp] using hg.comp hshift
  have hA2' : AnalyticAt ℝ (fun w ↦ L₂ (p + w)) 0 := by
    have hg : AnalyticAt ℝ L₂ ((fun w : ι → ℝ ↦ p + w) 0) := by simpa using hA2
    simpa [Function.comp] using hg.comp hshift
  obtain ⟨q, hq⟩ := hA2'.sub hA1'
  obtain ⟨r, hqr⟩ := hq
  -- A point near `p` where the germs differ, inside the series ball
  obtain ⟨ε, hε0, hεr⟩ : ∃ ε : ℝ, 0 < ε ∧ ENNReal.ofReal ε ≤ r := by
    rcases eq_or_ne r ⊤ with hr | hr
    · exact ⟨1, one_pos, by simp [hr]⟩
    · exact ⟨r.toReal, ENNReal.toReal_pos hqr.r_pos.ne' hr,
        (ENNReal.ofReal_toReal hr).le⟩
  have hfreq : ∃ᶠ w in 𝓝 p, L₁ w ≠ L₂ w := Filter.not_eventually.mp h
  have hball : ∀ᶠ w in 𝓝 p, w ∈ Metric.ball p ε :=
    Metric.isOpen_ball.eventually_mem (Metric.mem_ball_self hε0)
  obtain ⟨u, hu_ne, hu_mem⟩ := (hfreq.and_eventually hball).exists
  have hG0 : (fun w ↦ L₂ (p + w) - L₁ (p + w)) 0 = 0 := by
    simp [hp1, hp2]
  have hne : ∃ w ∈ Metric.eball (0 : ι → ℝ) r,
      (fun w ↦ L₂ (p + w) - L₁ (p + w)) w ≠ 0 := by
    refine ⟨u - p, ?_, ?_⟩
    · have hd : dist (u - p) (0 : ι → ℝ) = dist u p := by
        rw [dist_zero_right, dist_eq_norm]
      have hlt : edist (u - p) (0 : ι → ℝ) < ENNReal.ofReal ε := by
        rw [edist_dist, hd]
        exact ENNReal.ofReal_lt_ofReal_iff hε0 |>.mpr (Metric.mem_ball.mp hu_mem)
      exact Metric.mem_eball.mpr (lt_of_lt_of_le hlt hεr)
    · have hu : p + (u - p) = u := by abel
      simpa [hu] using sub_ne_zero_of_ne (Ne.symm hu_ne)
  obtain ⟨m, hlow, x₀, hx₀, hx₀n⟩ := Multi.exists_least_nonzero_diagonal hqr hG0 hne
  -- The quadratic bound on the shifted sum
  have hK : ContDiffAt ℝ 2 (fun w ↦ L₁ (p + w) + L₂ (p + w)) 0 :=
    (hA1'.add hA2').contDiffAt
  have hK0 : (fun w ↦ L₁ (p + w) + L₂ (p + w)) 0 = 0 := by simp [hp1, hp2]
  have hKnn : ∀ᶠ w in 𝓝 (0 : ι → ℝ), 0 ≤ L₁ (p + w) + L₂ (p + w) :=
    Eventually.of_forall fun w ↦ add_nonneg (hL1 _) (hL2 _)
  obtain ⟨C0, R, hC0, hR, hsum⟩ := Multi.quadratic_upper_bound_of_nonneg hK hK0 hKnn
  obtain ⟨ψ, hψc, hψs, hψ0, hψ1⟩ := Multi.exists_bump_one_on_ball (ι := ι) R hR
  have hshiftc : Continuous (fun w : ι → ℝ ↦ p + w) :=
    continuous_const.add continuous_id
  -- The endpoint contradiction for the shifted pencil
  have happly := analytic_pencil_difference_not_superpolynomial
    (fun w ↦ L₁ (p + w)) (fun w ↦ L₂ (p + w)) ψ m hqr hlow hx₀ hx₀n
    (hL1c.comp hshiftc) (hL2c.comp hshiftc)
    (fun w ↦ hL1 _) (fun w ↦ hL2 _) hC0 hR hsum hψc hψs hψ0 hψ1
  refine happly fun N ↦ ?_
  -- The observable for the family hypothesis
  set φ : (ι → ℝ) → ℝ := fun u ↦ (L₂ u - L₁ u) * ψ (u - p) with hφ_def
  have hφc : Continuous φ :=
    (hL2c.sub hL1c).mul (hψc.comp (continuous_id.sub continuous_const))
  have hφs : HasCompactSupport φ := by
    have hψs' : HasCompactSupport (fun u : ι → ℝ ↦ ψ (u - p)) :=
      hψs.comp_homeomorph (Homeomorph.subRight p)
    exact hψs'.mul_left
  have hint := hfam φ hφc hφs N
  refine hint.congr' (Eventually.of_forall fun t ↦ ?_) EventuallyEq.rfl
  beta_reduce
  rw [← integral_add_left_eq_self
    (fun u ↦ φ u * (Real.exp (-(t * L₁ u)) - Real.exp (-(t * L₂ u)))) p]
  congr 1
  funext w
  simp only [hφ_def, add_sub_cancel_left]

/-- **The germbij singular theorem, locus form** (`thm:singular`). If
`L₁, L₂` are continuous, nonnegative, analytic at each point of a set
`W₀` of common zeros, and the pencil difference decays beyond all
orders against every continuous compactly supported observable, then
`L₁ = L₂` on an open neighborhood of `W₀`. No compactness of `W₀` is
needed: the neighborhood is the union of the per-point ones. -/
theorem pencil_families_force_eq_near
    {ι : Type*} [Fintype ι] {L₁ L₂ : (ι → ℝ) → ℝ} {W₀ : Set (ι → ℝ)}
    (hL1c : Continuous L₁) (hL2c : Continuous L₂)
    (hL1 : ∀ w, 0 ≤ L₁ w) (hL2 : ∀ w, 0 ≤ L₂ w)
    (hA1 : ∀ p ∈ W₀, AnalyticAt ℝ L₁ p) (hA2 : ∀ p ∈ W₀, AnalyticAt ℝ L₂ p)
    (hzero1 : ∀ p ∈ W₀, L₁ p = 0) (hzero2 : ∀ p ∈ W₀, L₂ p = 0)
    (hfam : ∀ φ : (ι → ℝ) → ℝ, Continuous φ → HasCompactSupport φ →
      ∀ N : ℕ, (fun t : ℝ ↦ ∫ w, φ w *
          (Real.exp (-(t * L₁ w)) - Real.exp (-(t * L₂ w))))
        =o[atTop] fun t : ℝ ↦ t ^ (-(N : ℝ))) :
    ∃ U : Set (ι → ℝ), IsOpen U ∧ W₀ ⊆ U ∧ ∀ w ∈ U, L₁ w = L₂ w := by
  have h : ∀ p ∈ W₀, ∃ V : Set (ι → ℝ),
      (∀ w ∈ V, L₁ w = L₂ w) ∧ IsOpen V ∧ p ∈ V := fun p hp ↦
    eventually_nhds_iff.mp
      (pencil_families_force_germ_eq_at hL1c hL2c hL1 hL2 (hA1 p hp)
        (hA2 p hp) (hzero1 p hp) (hzero2 p hp) hfam)
  choose V hVeq hVopen hVmem using h
  refine ⟨⋃ p, ⋃ hp : p ∈ W₀, V p hp, ?_, ?_, ?_⟩
  · exact isOpen_iUnion fun p ↦ isOpen_iUnion fun hp ↦ hVopen p hp
  · exact fun p hp ↦ Set.mem_iUnion₂.mpr ⟨p, hp, hVmem p hp⟩
  · intro w hw
    obtain ⟨p, hp, hwV⟩ := Set.mem_iUnion₂.mp hw
    exact hVeq p hp w hwV

end Laplace
