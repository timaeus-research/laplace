/-
Copyright (c) 2026 Timaeus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib
import Laplace.Decay

/-!
# Preparation for the composed singular theorem

Part 1 of closing the composition gap identified by the adversarial
critique of `thm:singular` (archived in the tide log): the three
hypothesis-manufacturing lemmas that stand between a bare pair of
losses and the quantitative endpoint
`analytic_pencil_difference_not_superpolynomial`.

- The **quadratic upper bound**: a `C²` function, nonnegative near a
  zero, admits `K ≤ C₀‖w‖²` on a ball — the gradient dies by the
  local-minimum rule, and the Lipschitz derivative gives the
  mean-value second-order bound.
- The **least nonzero diagonal**: the power-series sum evaluates only
  diagonals, so a nonvanishing analytic function on the ball has a
  least degree whose diagonal polynomial is nonzero — no
  symmetric-multilinear polarization is needed — and homogeneity
  rescales a witness to the endpoint's `‖x₀‖ = 3/2` normalization.
- The **bump wrapper**: a continuous, compactly supported,
  nonnegative `ψ` equal to one on a prescribed ball, hand-rolled from
  the norm to avoid smooth-bump instance requirements (the endpoint
  needs only continuity).
-/

open Real Filter Topology
open scoped ENNReal

namespace Laplace.Multi

variable {ι : Type*} [Fintype ι]

/-- **The quadratic upper bound** (critique step 6): a `C²` function
vanishing and nonnegative at a local zero is bounded by a multiple of
`‖w‖²` on a ball. -/
theorem quadratic_upper_bound_of_nonneg {K : (ι → ℝ) → ℝ}
    (hK : ContDiffAt ℝ 2 K 0) (hK0 : K 0 = 0)
    (hKnn : ∀ᶠ w in 𝓝 (0 : ι → ℝ), 0 ≤ K w) :
    ∃ C0 R : ℝ, 0 ≤ C0 ∧ 0 < R ∧
      ∀ w : ι → ℝ, ‖w‖ ≤ R → K w ≤ C0 * ‖w‖ ^ 2 := by
  -- the gradient vanishes at the local minimum
  have hmin : IsLocalMin K 0 := by
    refine hKnn.mono fun w hw ↦ ?_
    rw [hK0]
    exact hw
  have hgrad : fderiv ℝ K 0 = 0 := hmin.fderiv_eq_zero
  -- the derivative is Lipschitz near 0
  have hf1 : ContDiffAt ℝ 1 (fderiv ℝ K) 0 :=
    hK.fderiv_right (le_refl _)
  obtain ⟨M, s, hs, hLip⟩ := hf1.exists_lipschitzOnWith
  -- differentiability on a neighborhood
  obtain ⟨u, hu, hKu⟩ : ∃ u ∈ 𝓝 (0 : ι → ℝ), ContDiffOn ℝ 1 K u :=
    hK.contDiffOn (m := 1) (by norm_num) (by norm_num)
  -- a radius inside both neighborhoods
  obtain ⟨R, hR0, hRsub⟩ : ∃ R : ℝ, 0 < R ∧
      Metric.closedBall (0 : ι → ℝ) R ⊆ s ∩ interior u := by
    have hmem : s ∩ interior u ∈ 𝓝 (0 : ι → ℝ) :=
      Filter.inter_mem hs (interior_mem_nhds.mpr hu)
    obtain ⟨ε, hε0, hεsub⟩ := Metric.mem_nhds_iff.mp hmem
    exact ⟨ε / 2, by positivity,
      (Metric.closedBall_subset_ball (by linarith)).trans hεsub⟩
  refine ⟨(M : ℝ), R, M.coe_nonneg, hR0, fun w hw ↦ ?_⟩
  -- mean value on the ‖w‖-ball with the Lipschitz gradient bound
  have hball_sub : Metric.closedBall (0 : ι → ℝ) ‖w‖ ⊆
      Metric.closedBall (0 : ι → ℝ) R :=
    Metric.closedBall_subset_closedBall hw
  have hdiff : ∀ v ∈ Metric.closedBall (0 : ι → ℝ) ‖w‖,
      HasFDerivWithinAt K (fderiv ℝ K v)
        (Metric.closedBall (0 : ι → ℝ) ‖w‖) v := by
    intro v hv
    have hvu : v ∈ interior u := (hRsub (hball_sub hv)).2
    have : DifferentiableAt ℝ K v := by
      have hCD : ContDiffAt ℝ 1 K v :=
        (hKu.contDiffAt (mem_interior_iff_mem_nhds.mp hvu))
      exact hCD.differentiableAt one_ne_zero
    exact this.hasFDerivAt.hasFDerivWithinAt
  have hbound : ∀ v ∈ Metric.closedBall (0 : ι → ℝ) ‖w‖,
      ‖fderiv ℝ K v‖ ≤ (M : ℝ) * ‖w‖ := by
    intro v hv
    have hvs : v ∈ s := (hRsub (hball_sub hv)).1
    have h0s : (0 : ι → ℝ) ∈ s := by
      refine (hRsub ?_).1
      simp [hR0.le]
    have hd := hLip.dist_le_mul v hvs 0 h0s
    rw [hgrad] at hd
    calc ‖fderiv ℝ K v‖ = dist (fderiv ℝ K v) 0 := by
          rw [dist_zero_right]
      _ ≤ (M : ℝ) * dist v 0 := hd
      _ ≤ (M : ℝ) * ‖w‖ := by
          rw [dist_zero_right]
          refine mul_le_mul_of_nonneg_left ?_ M.coe_nonneg
          simpa [dist_zero_right] using hv
  have h0mem : (0 : ι → ℝ) ∈ Metric.closedBall (0 : ι → ℝ) ‖w‖ := by
    simp [norm_nonneg]
  have hwmem : w ∈ Metric.closedBall (0 : ι → ℝ) ‖w‖ := by
    simp
  have hmvt := Convex.norm_image_sub_le_of_norm_hasFDerivWithin_le
    hdiff hbound (convex_closedBall _ _) h0mem hwmem
  rw [hK0, sub_zero, sub_zero] at hmvt
  calc K w ≤ ‖K w‖ := le_abs_self _
    _ ≤ (M : ℝ) * ‖w‖ * ‖w‖ := hmvt
    _ = (M : ℝ) * ‖w‖ ^ 2 := by ring

/-- **The least nonzero diagonal** (critique steps 4–5): a
nonvanishing analytic function with `g 0 = 0` has a least degree
whose diagonal polynomial is nonzero, and a witness rescales to the
endpoint's normalization. No polarization is needed: the
power-series sum evaluates only diagonals. -/
theorem exists_least_nonzero_diagonal {g : (ι → ℝ) → ℝ}
    {p : FormalMultilinearSeries ℝ (ι → ℝ) ℝ} {r : ℝ≥0∞}
    (hg : HasFPowerSeriesOnBall g p 0 r) (hg0 : g 0 = 0)
    (hne : ∃ w ∈ Metric.eball (0 : ι → ℝ) r, g w ≠ 0) :
    ∃ m : ℕ, (∀ k, k < m → ∀ y : ι → ℝ, (p k) (fun _ ↦ y) = 0) ∧
      ∃ x₀ : ι → ℝ, (p m) (fun _ ↦ x₀) ≠ 0 ∧ ‖x₀‖ = 3 / 2 := by
  classical
  -- some diagonal is nonzero, else g vanishes on the ball
  have hex : ∃ k, ∃ y : ι → ℝ, (p k) (fun _ ↦ y) ≠ 0 := by
    by_contra hall
    push Not at hall
    obtain ⟨w, hw, hwne⟩ := hne
    have hsum := hg.hasSum hw
    rw [zero_add] at hsum
    rw [show (fun n ↦ (p n) fun _ ↦ w) = fun _ ↦ (0 : ℝ) from
      funext fun n ↦ hall n w] at hsum
    exact hwne (hsum.unique hasSum_zero)
  -- the constant diagonal vanishes: p 0 (anything) = g 0 = 0
  have hzero : ∀ y : ι → ℝ, (p 0) (fun _ ↦ y) = 0 := by
    intro y
    have hr0 : (0 : ι → ℝ) ∈ Metric.eball (0 : ι → ℝ) r :=
      Metric.mem_eball_self hg.r_pos
    have hsum := hg.hasSum hr0
    rw [add_zero] at hsum
    have hsingle : HasSum (fun n ↦ (p n) fun _ ↦ (0 : ι → ℝ))
        ((p 0) fun _ ↦ (0 : ι → ℝ)) := by
      refine hasSum_single 0 fun n hn ↦ ?_
      exact (p n).map_coord_zero ⟨0, Nat.pos_of_ne_zero hn⟩ rfl
    have hp0 : (p 0) (fun _ ↦ (0 : ι → ℝ)) = g 0 :=
      hsingle.unique hsum
    have harg : (fun _ : Fin 0 ↦ y) = fun _ : Fin 0 ↦ (0 : ι → ℝ) :=
      funext fun i ↦ i.elim0
    rw [harg, hp0, hg0]
  have hlow : ∀ k, k < Nat.find hex → ∀ y : ι → ℝ,
      (p k) (fun _ ↦ y) = 0 := by
    intro k hk y
    by_contra hne'
    exact Nat.find_min hex hk ⟨y, hne'⟩
  -- the found degree is at least one
  have hm1 : 1 ≤ Nat.find hex := by
    rcases Nat.eq_zero_or_pos (Nat.find hex) with h0 | h1
    · exfalso
      have hspec := Nat.find_spec hex
      rw [h0] at hspec
      obtain ⟨y, hy⟩ := hspec
      exact hy (hzero y)
    · exact h1
  obtain ⟨x, hx⟩ := Nat.find_spec hex
  -- the witness is nonzero, hence rescalable to norm 3/2
  have hxne : x ≠ 0 := by
    intro h0
    apply hx
    rw [h0]
    exact (p (Nat.find hex)).map_coord_zero ⟨0, hm1⟩ rfl
  have hxnorm : 0 < ‖x‖ := norm_pos_iff.mpr hxne
  set c : ℝ := 3 / (2 * ‖x‖) with hc_def
  have hcpos : 0 < c := by
    rw [hc_def]
    positivity
  refine ⟨Nat.find hex, hlow, c • x, ?_, ?_⟩
  · have hsmul : (p (Nat.find hex))
        (fun _ : Fin (Nat.find hex) ↦ c • x) =
        (∏ _i : Fin (Nat.find hex), c) •
          (p (Nat.find hex)) (fun _ : Fin (Nat.find hex) ↦ x) :=
      (p (Nat.find hex)).map_smul_univ (fun _ ↦ c) (fun _ ↦ x)
    rw [hsmul, Finset.prod_const, Finset.card_univ, Fintype.card_fin,
      smul_eq_mul]
    exact mul_ne_zero (pow_ne_zero _ hcpos.ne') hx
  · rw [norm_smul, Real.norm_eq_abs, abs_of_pos hcpos, hc_def]
    field_simp

/-- **The bump wrapper** (critique step 7): a continuous, compactly
supported, nonnegative bump equal to one on a prescribed ball. -/
theorem exists_bump_one_on_ball (R : ℝ) (_hR : 0 < R) :
    ∃ ψ : (ι → ℝ) → ℝ, Continuous ψ ∧ HasCompactSupport ψ ∧
      (∀ w, 0 ≤ ψ w) ∧ ∀ w : ι → ℝ, ‖w‖ ≤ R → ψ w = 1 := by
  refine ⟨fun w ↦ min 1 (max 0 (R + 1 - ‖w‖)), ?_, ?_, ?_, ?_⟩
  · exact continuous_const.min
      (continuous_const.max (continuous_const.sub continuous_norm))
  · have hsub : Function.support
        (fun w : ι → ℝ ↦ min 1 (max 0 (R + 1 - ‖w‖))) ⊆
        Metric.closedBall (0 : ι → ℝ) (R + 1) := by
      intro w hw
      rw [Function.mem_support] at hw
      rw [Metric.mem_closedBall, dist_zero_right]
      by_contra hout
      push Not at hout
      apply hw
      rw [max_eq_left (by linarith), min_eq_right zero_le_one]
    refine HasCompactSupport.of_support_subset_isCompact
      (isCompact_closedBall _ _) hsub
  · intro w
    exact le_min zero_le_one (le_max_left _ _)
  · intro w hw
    beta_reduce
    rw [min_eq_left]
    calc (1 : ℝ) ≤ R + 1 - ‖w‖ := by linarith
      _ ≤ max 0 (R + 1 - ‖w‖) := le_max_right _ _

end Laplace.Multi
