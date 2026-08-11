/-
Copyright (c) 2026 Timaeus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib
import Laplace.Multi.PackageConstructor

/-!
# The radial Taylor bound

Discharges the package-derivation wrapper's remaining hypothesis: a
globally `C^k` loss admits, on every ball, a fixed-ball Taylor
remainder bound at order `k`
(`exists_taylorRemainder_bound`). The proof is the radial route
recommended by the scoping consult: the ray derivative identity at
arbitrary points (`ray_iteratedDeriv_at`, generalizing the corpus's
origin-only lemma), the one-dimensional Taylor--Lagrange theorem
along each ray, the compactness bound for the `k`-th Fréchet
derivative on the closed ball, and the multilinear operator-norm
estimate. The corollary
`higherLaplaceDomainFamily_ofContDiff` then produces the certified
package family from smoothness, the vanishing gradient, and the
diagonal-matched positive-definite matrix alone.
-/

open Real MeasureTheory Filter Topology Metric Set

namespace Laplace.Multi

variable {d : ℕ} {L : EuclidD d → ℝ}

/-- **Ray iterated derivatives at every point**: the `m`-th derivative
of the ray restriction at `t` is the `m`-th Fréchet derivative's
diagonal at `t • x` (the corpus's origin lemma, generalized). -/
theorem ray_iteratedDeriv_at {n : WithTop ℕ∞}
    (hL : ContDiff ℝ n L) {m : ℕ} (hm : (m : WithTop ℕ∞) ≤ n)
    (x : EuclidD d) (t : ℝ) :
    iteratedDeriv m (fun s : ℝ ↦ L (s • x)) t =
      iteratedFDeriv ℝ m L (t • x) (fun _ ↦ x) := by
  have hcomp : (fun s : ℝ ↦ L (s • x)) =
      L ∘ (ContinuousLinearMap.toSpanSingleton ℝ x) := by
    funext s
    simp [ContinuousLinearMap.toSpanSingleton_apply]
  rw [hcomp, iteratedDeriv_eq_iteratedFDeriv,
    ContinuousLinearMap.iteratedFDeriv_comp_right _ hL _ hm,
    ContinuousMultilinearMap.compContinuousLinearMap_apply]
  congr 1
  funext i
  rw [ContinuousLinearMap.toSpanSingleton_apply, one_smul]

/-- **The fixed-ball Taylor remainder bound from smoothness**: a
globally `C^k` loss satisfies, on any ball, the order-`k` remainder
bound the higher package requires. -/
theorem exists_taylorRemainder_bound {k : ℕ} (hk : 0 < k)
    (hL : ContDiff ℝ k L) {R : ℝ} (hR : 0 < R) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ y ∈ Metric.ball (0 : EuclidD d) R,
      |L y - ∑ j ∈ Finset.range k, taylorHomogeneousTerm j L y| ≤
        C * ‖y‖ ^ k := by
  -- the compact-ball bound for the k-th derivative
  obtain ⟨M, hM⟩ : ∃ M : ℝ, ∀ z ∈ Metric.closedBall (0 : EuclidD d) R,
      ‖iteratedFDeriv ℝ k L z‖ ≤ M := by
    obtain ⟨M, hM⟩ := (isCompact_closedBall (0 : EuclidD d) R).exists_bound_of_continuousOn
      (hL.continuous_iteratedFDeriv le_rfl).continuousOn
    exact ⟨M, hM⟩
  have hM0 : 0 ≤ M :=
    le_trans (norm_nonneg _) (hM 0 (Metric.mem_closedBall_self hR.le))
  refine ⟨M / k.factorial, by positivity, fun y hy ↦ ?_⟩
  have hyR : ‖y‖ < R := by
    have := Metric.mem_ball.mp hy
    rwa [dist_zero_right] at this
  -- the ray restriction
  set g : ℝ → ℝ := fun s ↦ L (s • y) with hg_def
  have hg : ContDiff ℝ k g :=
    hL.comp ((contDiff_id.smul contDiff_const :
      ContDiff ℝ k fun s : ℝ ↦ s • y))
  have hunique : UniqueDiffOn ℝ (Icc (0 : ℝ) 1) :=
    uniqueDiffOn_Icc one_pos
  -- bridging Within to global derivatives on the interval
  have hbridge : ∀ (j : ℕ), (j : WithTop ℕ∞) ≤ k → ∀ t ∈ Icc (0 : ℝ) 1,
      iteratedDerivWithin j g (Icc (0 : ℝ) 1) t = iteratedDeriv j g t :=
    fun j hj t ht ↦ iteratedDerivWithin_eq_iteratedDeriv hunique
      ((hg.of_le hj).contDiffAt) ht
  -- 1D Taylor–Lagrange with n := k - 1
  obtain ⟨n, rfl⟩ : ∃ n, k = n + 1 :=
    ⟨k - 1, (Nat.succ_pred_eq_of_pos hk).symm⟩
  have hfIcc : ContDiffOn ℝ n g (Icc (0 : ℝ) 1) :=
    (hg.of_le (by exact_mod_cast Nat.le_succ n)).contDiffOn
  have hf' : DifferentiableOn ℝ
      (iteratedDerivWithin n g (Icc (0 : ℝ) 1)) (Ioo (0 : ℝ) 1) := by
    refine DifferentiableOn.congr
      (f := fun t ↦ iteratedDeriv n g t) ?_ ?_
    · refine (Differentiable.differentiableOn ?_)
      exact hg.differentiable_iteratedDeriv n
        (by exact_mod_cast Nat.lt_succ_self n)
    · intro t ht
      exact hbridge n (by exact_mod_cast Nat.le_succ n) t
        (Ioo_subset_Icc_self ht)
  obtain ⟨ξ, hξ, hlag⟩ := taylor_mean_remainder_lagrange
    (f := g) (x₀ := 0) (x := 1) one_pos hfIcc hf'
  -- identify the Taylor polynomial with the homogeneous terms
  have hpoly : taylorWithinEval g n (Icc (0 : ℝ) 1) 0 1 =
      ∑ j ∈ Finset.range (n + 1), taylorHomogeneousTerm j L y := by
    rw [taylor_within_apply]
    refine Finset.sum_congr rfl fun j hj ↦ ?_
    have hjk : (j : WithTop ℕ∞) ≤ (n + 1 : ℕ) := by
      exact_mod_cast Nat.le_of_lt_succ (Finset.mem_range.mp hj) |>.trans
        (Nat.le_succ n)
    rw [hbridge j hjk 0 (Set.left_mem_Icc.mpr one_pos.le),
      ray_iteratedDeriv_at hL hjk y 0, zero_smul]
    unfold taylorHomogeneousTerm
    rw [smul_eq_mul]
    ring
  -- the remainder value at ξ
  have hξIcc : ξ ∈ Icc (0 : ℝ) 1 := Ioo_subset_Icc_self hξ
  have hrem : iteratedDerivWithin (n + 1) g (Icc (0 : ℝ) 1) ξ =
      iteratedFDeriv ℝ (n + 1) L (ξ • y) (fun _ ↦ y) := by
    rw [hbridge (n + 1) le_rfl ξ hξIcc, ray_iteratedDeriv_at hL le_rfl]
  -- the bound
  have hξball : ξ • y ∈ Metric.closedBall (0 : EuclidD d) R := by
    rw [Metric.mem_closedBall, dist_zero_right, norm_smul,
      Real.norm_eq_abs, abs_of_pos hξ.1]
    calc ξ * ‖y‖ ≤ 1 * ‖y‖ :=
          mul_le_mul_of_nonneg_right hξ.2.le (norm_nonneg _)
      _ = ‖y‖ := one_mul _
      _ ≤ R := hyR.le
  have hval : |iteratedFDeriv ℝ (n + 1) L (ξ • y) (fun _ ↦ y)| ≤
      M * ‖y‖ ^ (n + 1) := by
    have hop := (iteratedFDeriv ℝ (n + 1) L (ξ • y)).le_opNorm
      (fun _ ↦ y)
    have hprod : (∏ _i : Fin (n + 1), ‖y‖) = ‖y‖ ^ (n + 1) := by
      rw [Finset.prod_const, Finset.card_fin]
    rw [hprod] at hop
    calc |iteratedFDeriv ℝ (n + 1) L (ξ • y) (fun _ ↦ y)|
        ≤ ‖iteratedFDeriv ℝ (n + 1) L (ξ • y)‖ * ‖y‖ ^ (n + 1) := by
          simpa [Real.norm_eq_abs] using hop
      _ ≤ M * ‖y‖ ^ (n + 1) := by
          refine mul_le_mul_of_nonneg_right (hM _ hξball) (by positivity)
  -- assemble
  have hg1 : g 1 = L y := by rw [hg_def]; simp
  rw [hg1, hpoly] at hlag
  rw [hlag, hrem]
  have h10 : ((1 : ℝ) - 0) ^ (n + 1) = 1 := by norm_num
  rw [h10, mul_one, abs_div, Nat.abs_cast]
  have hfac : (0 : ℝ) < ((n + 1).factorial : ℝ) := by positivity
  calc |iteratedFDeriv ℝ (n + 1) L (ξ • y) (fun _ ↦ y)| /
        ((n + 1).factorial : ℝ)
      ≤ M * ‖y‖ ^ (n + 1) / ((n + 1).factorial : ℝ) := by
        gcongr
    _ = M / ((n + 1).factorial : ℝ) * ‖y‖ ^ (n + 1) := by ring

/-- **The package family from smoothness alone**: the certified
family the located recovery headlines consume, with the Taylor
bounds discharged by the radial theorem. -/
noncomputable def higherLaplaceDomainFamily_ofContDiff
    {H : Matrix (Fin d) (Fin d) ℝ}
    (hcont : ∀ k : ℕ, ContDiff ℝ k L)
    (hgrad : fderiv ℝ L 0 = 0)
    (hdiag : ∀ y, qform (hessianMatrix L) y = qform H y)
    (hH : H.PosDef) :
    ∀ k, 2 < k → HigherLaplaceDomain k L H :=
  higherLaplaceDomainFamily_ofTaylorBounds hcont hgrad hdiag hH
    (fun k h2 ↦ by
      obtain ⟨C, hC, hb⟩ := exists_taylorRemainder_bound
        (by omega : 0 < k) (hcont k) (one_pos : (0:ℝ) < 1)
      exact ⟨1, C, one_pos, hC, hb⟩)

end Laplace.Multi
