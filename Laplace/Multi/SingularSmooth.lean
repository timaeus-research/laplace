/-
Copyright (c) 2026 Timaeus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib
import Laplace.Multi.SingularPoint

/-!
# The singular theorem with smooth observables

`Laplace.Multi.SingularPoint` proves the point and locus forms of the
germbij singular theorem with the decay premise quantified over all
continuous compactly supported observables. The note (`thm:singular`)
quantifies over `φ ∈ C_c^∞`, a smaller class, so its premise is weaker
and the theorems there do not literally subsume it. This file closes
that gap: the observable `(L₂ - L₁) · ψ(· - p)` is rebuilt with a
`ContDiffBump` whose closed support sits inside the analyticity ball of
`L₂ - L₁` at `p`, and glued to a globally smooth function
(`contDiff_mul_of_tsupport_subset`). The resulting
`pencil_families_force_germ_eq_at_smooth` and
`pencil_families_force_eq_near_smooth` have the note's premise
verbatim.
-/

open Asymptotics Filter MeasureTheory
open scoped ENNReal Topology ContDiff

namespace Laplace

/-- Gluing: a product `g · ψ` with `ψ` smooth and supported inside an
open set on which `g` is smooth is globally smooth (it vanishes on a
neighborhood of every point outside the support). -/
theorem contDiff_mul_of_tsupport_subset {ι : Type*} [Fintype ι]
    {g ψ : (ι → ℝ) → ℝ} {U : Set (ι → ℝ)}
    (hg : ∀ u ∈ U, ContDiffAt ℝ ∞ g u) (hψ : ContDiff ℝ ∞ ψ)
    (hsub : tsupport ψ ⊆ U) :
    ContDiff ℝ ∞ fun w ↦ g w * ψ w := by
  rw [contDiff_iff_contDiffAt]
  intro u
  by_cases hu : u ∈ U
  · exact (hg u hu).mul hψ.contDiffAt
  · have hu' : u ∈ (tsupport ψ)ᶜ := fun hmem ↦ hu (hsub hmem)
    have hev : ∀ᶠ w in 𝓝 u, g w * ψ w = 0 := by
      filter_upwards [(isClosed_tsupport ψ).isOpen_compl.mem_nhds hu'] with w hw
      rw [image_eq_zero_of_notMem_tsupport hw, mul_zero]
    exact (contDiffAt_const (c := (0 : ℝ))).congr_of_eventuallyEq hev

/-- **The germbij singular theorem, point form, smooth observables**
(the note's premise verbatim). If `L₁, L₂` are continuous,
nonnegative, analytic at `p`, vanish at `p`, and for every
`φ ∈ C_c^∞` the pencil difference decays faster than every negative
power of `t`, then `L₁ = L₂` on a neighborhood of `p`. -/
theorem pencil_families_force_germ_eq_at_smooth
    {ι : Type*} [Fintype ι] {L₁ L₂ : (ι → ℝ) → ℝ} {p : ι → ℝ}
    (hL1c : Continuous L₁) (hL2c : Continuous L₂)
    (hL1 : ∀ w, 0 ≤ L₁ w) (hL2 : ∀ w, 0 ≤ L₂ w)
    (hA1 : AnalyticAt ℝ L₁ p) (hA2 : AnalyticAt ℝ L₂ p)
    (hp1 : L₁ p = 0) (hp2 : L₂ p = 0)
    (hfam : ∀ φ : (ι → ℝ) → ℝ, ContDiff ℝ ∞ φ → HasCompactSupport φ →
      ∀ N : ℕ, (fun t : ℝ ↦ ∫ w, φ w *
          (Real.exp (-(t * L₁ w)) - Real.exp (-(t * L₂ w))))
        =o[atTop] fun t : ℝ ↦ t ^ (-(N : ℝ))) :
    ∀ᶠ w in 𝓝 p, L₁ w = L₂ w := by
  by_contra h
  -- The shifted difference and its power series at the origin
  have hshift : AnalyticAt ℝ (fun w : ι → ℝ ↦ p + w) 0 :=
    analyticAt_const.add analyticAt_id
  have hA1' : AnalyticAt ℝ (fun w ↦ L₁ (p + w)) 0 := by
    have hg : AnalyticAt ℝ L₁ ((fun w : ι → ℝ ↦ p + w) 0) := by simpa using hA1
    simpa [Function.comp] using hg.comp hshift
  have hA2' : AnalyticAt ℝ (fun w ↦ L₂ (p + w)) 0 := by
    have hg : AnalyticAt ℝ L₂ ((fun w : ι → ℝ ↦ p + w) 0) := by simpa using hA2
    simpa [Function.comp] using hg.comp hshift
  obtain ⟨q, hq⟩ := hA2'.sub hA1'
  obtain ⟨r, hqr⟩ := hq
  -- The analyticity radius of the unshifted difference at `p`
  have hG'a : AnalyticAt ℝ (fun w ↦ L₂ w - L₁ w) p := hA2.sub hA1
  obtain ⟨q0, hq0⟩ := hG'a
  obtain ⟨r0, hq0r⟩ := hq0
  obtain ⟨ρ, hρ0, hρr⟩ : ∃ ρ : ℝ, 0 < ρ ∧ ENNReal.ofReal ρ ≤ r0 := by
    rcases eq_or_ne r0 ⊤ with hr | hr
    · exact ⟨1, one_pos, by simp [hr]⟩
    · exact ⟨r0.toReal, ENNReal.toReal_pos hq0r.r_pos.ne' hr,
        (ENNReal.ofReal_toReal hr).le⟩
  have hGsmooth : ∀ u ∈ Metric.ball p ρ, ContDiffAt ℝ ∞ (fun w ↦ L₂ w - L₁ w) u := by
    intro u hu
    have hmem : u ∈ Metric.eball p r0 := by
      have : edist u p < ENNReal.ofReal ρ := by
        rw [edist_dist]
        exact (ENNReal.ofReal_lt_ofReal_iff hρ0).mpr (Metric.mem_ball.mp hu)
      exact Metric.mem_eball.mpr (lt_of_lt_of_le this hρr)
    exact (hq0r.analyticOnNhd u hmem).contDiffAt
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
  -- The quadratic bound on the shifted sum, then shrink to fit the
  -- analyticity ball
  have hK : ContDiffAt ℝ 2 (fun w ↦ L₁ (p + w) + L₂ (p + w)) 0 :=
    (hA1'.add hA2').contDiffAt
  have hK0 : (fun w ↦ L₁ (p + w) + L₂ (p + w)) 0 = 0 := by simp [hp1, hp2]
  have hKnn : ∀ᶠ w in 𝓝 (0 : ι → ℝ), 0 ≤ L₁ (p + w) + L₂ (p + w) :=
    Eventually.of_forall fun w ↦ add_nonneg (hL1 _) (hL2 _)
  obtain ⟨C0, R, hC0, hR, hsum⟩ := Multi.quadratic_upper_bound_of_nonneg hK hK0 hKnn
  set rIn : ℝ := min R (ρ / 4) with hrIn_def
  have hrIn0 : 0 < rIn := lt_min hR (by linarith)
  have hrInR : rIn ≤ R := min_le_left _ _
  have hrInρ : 2 * rIn < ρ := by
    have : rIn ≤ ρ / 4 := min_le_right _ _
    linarith
  have hsum' : ∀ w : ι → ℝ, ‖w‖ ≤ rIn → L₁ (p + w) + L₂ (p + w) ≤ C0 * ‖w‖ ^ 2 :=
    fun w hw ↦ hsum w (hw.trans hrInR)
  -- The smooth bump
  set f : ContDiffBump (0 : ι → ℝ) :=
    { rIn := rIn, rOut := 2 * rIn, rIn_pos := hrIn0,
      rIn_lt_rOut := by linarith } with hf_def
  have hψ1 : ∀ w : ι → ℝ, ‖w‖ ≤ rIn → f w = 1 := fun w hw ↦
    f.one_of_mem_closedBall (by simpa [Metric.mem_closedBall, dist_zero_right] using hw)
  -- The smooth observable
  have hψshift : ContDiff ℝ ∞ (fun u : ι → ℝ ↦ f (u - p)) :=
    f.contDiff.comp (contDiff_id.sub contDiff_const)
  have hsupp : tsupport (fun u : ι → ℝ ↦ f (u - p)) ⊆ Metric.ball p ρ := by
    have h1 : Function.support (fun u : ι → ℝ ↦ f (u - p)) ⊆
        Metric.closedBall p (2 * rIn) := by
      intro u hu
      have : u - p ∈ Function.support f := hu
      rw [f.support_eq] at this
      have hn : ‖u - p‖ < 2 * rIn := by
        simpa [Metric.mem_ball, dist_zero_right] using this
      exact Metric.mem_closedBall.mpr (by rw [dist_eq_norm]; exact hn.le)
    exact (closure_minimal h1 Metric.isClosed_closedBall).trans
      (Metric.closedBall_subset_ball hrInρ)
  have hφ_smooth : ContDiff ℝ ∞ fun u ↦ (L₂ u - L₁ u) * f (u - p) :=
    contDiff_mul_of_tsupport_subset hGsmooth hψshift hsupp
  have hφs : HasCompactSupport fun u : ι → ℝ ↦ (L₂ u - L₁ u) * f (u - p) := by
    have hψs' : HasCompactSupport (fun u : ι → ℝ ↦ f (u - p)) :=
      f.hasCompactSupport.comp_homeomorph (Homeomorph.subRight p)
    exact hψs'.mul_left
  -- The endpoint contradiction for the shifted pencil
  have hshiftc : Continuous (fun w : ι → ℝ ↦ p + w) :=
    continuous_const.add continuous_id
  have happly := analytic_pencil_difference_not_superpolynomial
    (fun w ↦ L₁ (p + w)) (fun w ↦ L₂ (p + w)) f m hqr hlow hx₀ hx₀n
    (hL1c.comp hshiftc) (hL2c.comp hshiftc)
    (fun w ↦ hL1 _) (fun w ↦ hL2 _) hC0 hrIn0 hsum' f.continuous
    f.hasCompactSupport f.nonneg' hψ1
  refine happly fun N ↦ ?_
  have hint := hfam (fun u ↦ (L₂ u - L₁ u) * f (u - p)) hφ_smooth hφs N
  refine hint.congr' (Eventually.of_forall fun t ↦ ?_) EventuallyEq.rfl
  beta_reduce
  rw [← integral_add_left_eq_self
    (fun u ↦ ((L₂ u - L₁ u) * f (u - p)) *
      (Real.exp (-(t * L₁ u)) - Real.exp (-(t * L₂ u)))) p]
  congr 1
  funext w
  simp only [add_sub_cancel_left]

/-- **The germbij singular theorem, locus form, smooth observables**
(`thm:singular` verbatim, modulo the open-neighborhood packaging). -/
theorem pencil_families_force_eq_near_smooth
    {ι : Type*} [Fintype ι] {L₁ L₂ : (ι → ℝ) → ℝ} {W₀ : Set (ι → ℝ)}
    (hL1c : Continuous L₁) (hL2c : Continuous L₂)
    (hL1 : ∀ w, 0 ≤ L₁ w) (hL2 : ∀ w, 0 ≤ L₂ w)
    (hA1 : ∀ p ∈ W₀, AnalyticAt ℝ L₁ p) (hA2 : ∀ p ∈ W₀, AnalyticAt ℝ L₂ p)
    (hzero1 : ∀ p ∈ W₀, L₁ p = 0) (hzero2 : ∀ p ∈ W₀, L₂ p = 0)
    (hfam : ∀ φ : (ι → ℝ) → ℝ, ContDiff ℝ ∞ φ → HasCompactSupport φ →
      ∀ N : ℕ, (fun t : ℝ ↦ ∫ w, φ w *
          (Real.exp (-(t * L₁ w)) - Real.exp (-(t * L₂ w))))
        =o[atTop] fun t : ℝ ↦ t ^ (-(N : ℝ))) :
    ∃ U : Set (ι → ℝ), IsOpen U ∧ W₀ ⊆ U ∧ ∀ w ∈ U, L₁ w = L₂ w := by
  have h : ∀ p ∈ W₀, ∃ V : Set (ι → ℝ),
      (∀ w ∈ V, L₁ w = L₂ w) ∧ IsOpen V ∧ p ∈ V := fun p hp ↦
    eventually_nhds_iff.mp
      (pencil_families_force_germ_eq_at_smooth hL1c hL2c hL1 hL2 (hA1 p hp)
        (hA2 p hp) (hzero1 p hp) (hzero2 p hp) hfam)
  choose V hVeq hVopen hVmem using h
  refine ⟨⋃ p, ⋃ hp : p ∈ W₀, V p hp, ?_, ?_, ?_⟩
  · exact isOpen_iUnion fun p ↦ isOpen_iUnion fun hp ↦ hVopen p hp
  · exact fun p hp ↦ Set.mem_iUnion₂.mpr ⟨p, hp, hVmem p hp⟩
  · intro w hw
    obtain ⟨p, hp, hwV⟩ := Set.mem_iUnion₂.mp hw
    exact hVeq p hp w hwV

end Laplace
