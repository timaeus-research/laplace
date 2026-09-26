/-
Copyright (c) 2026 Timaeus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Timaeus
-/
import Mathlib
import Laplace.Multi.NestedProjections

/-!
# The projection onto the affine span of the statistic is the regression

For a bounded observable `φ` and a coefficient vector `a` solving the normal equations
`Cov_Q(S_j, ⟨a, S⟩) = Cov_Q(S_j, φ)` for all `j`, the orthogonal projection of `φ` onto the affine
span `A = span{1, S_j}` in `L²(Q)` is the regression

  `B φ = E_Q φ + (⟨a, S⟩ − E_Q⟨a, S⟩)`                    (`starProjection_statSpan_toLp`),

and the energy of its centred part is the Fisher energy of the induced response velocity
`u = Cov_Q(S, φ)`:

  `‖B φ − E_Q φ‖² = Var_Q⟨a, S⟩ = ⟨a, u⟩`                 (`norm_sq_regressionLp_sub_eq_dotJ`).

On the atlas path the normal equations are solvable with `a` in the visible subspace
(`exists_regression_coefficient`), so the identification holds at every reconstructed law
(`starProjection_statSpan_toLp_atlas`). Together with the three-way Pythagoras of
`NestedProjections`, this identifies the first term of the quadratic information split with the
rate's second-order form `g_M(u,u) = ⟨u, Σ_M⁻¹ u⟩`.
-/

open MeasureTheory Filter Topology Set
open scoped ENNReal

namespace Laplace.Multi

section Regression

variable {X : Type*} [MeasurableSpace X] {J : Type*} [Fintype J] {S : J → X → ℝ}
  (hS : ∀ j, Bdd (S j)) (Q : Measure X) [IsProbabilityMeasure Q]

omit [Fintype J] [IsProbabilityMeasure Q] in
/-- The `L²` inner product of two representatives. -/
theorem inner_toLp_toLp {f g : X → ℝ} (hf : MemLp f 2 Q) (hg : MemLp g 2 Q) :
    inner ℝ (hf.toLp f) (hg.toLp g) = ∫ x, f x * g x ∂Q := by
  rw [L2.inner_def]
  refine integral_congr_ae ?_
  filter_upwards [hf.coeFn_toLp, hg.coeFn_toLp] with x hx hy
  rw [hx, hy]
  simp [mul_comm]

omit [Fintype J] in
/-- The constant function `1` in `L²(Q)`. -/
noncomputable def oneLp : Lp ℝ 2 Q := (memLp_const (1 : ℝ)).toLp fun _ ↦ (1 : ℝ)

include hS

omit [Fintype J] in
theorem oneLp_mem_statSpan : oneLp Q ∈ statSpan hS Q :=
  Submodule.subset_span (Set.mem_insert _ _)

omit [Fintype J] in
theorem toLp_stat_mem_statSpan (j : J) : (memLp_two_bdd Q (hS j)).toLp (S j) ∈ statSpan hS Q :=
  Submodule.subset_span (Set.mem_insert_of_mem _ ⟨j, rfl⟩)

/-- A visible contrast in `L²(Q)` is the corresponding combination of the statistics. -/
theorem toLp_dirLoss_eq_sum (a : J → ℝ) :
    (memLp_two_bdd Q (bdd_dirLoss hS a)).toLp (dirLoss S a) =
      ∑ j, a j • (memLp_two_bdd Q (hS j)).toLp (S j) := by
  refine Lp.ext ?_
  filter_upwards [MemLp.coeFn_toLp (memLp_two_bdd Q (bdd_dirLoss hS a)),
    Lp.coeFn_finsetSum Finset.univ (fun j ↦ a j • (memLp_two_bdd Q (hS j)).toLp (S j)),
    (ae_all_iff (ι := J)).2 fun j ↦ Lp.coeFn_smul (a j) ((memLp_two_bdd Q (hS j)).toLp (S j)),
    (ae_all_iff (ι := J)).2 fun j ↦ MemLp.coeFn_toLp (memLp_two_bdd Q (hS j))] with x h1 h2 h3 h4
  rw [h1, h2, Finset.sum_apply]
  simp only [dirLoss]
  refine Finset.sum_congr rfl fun j _ ↦ ?_
  rw [h3 j, Pi.smul_apply, h4 j, smul_eq_mul]

theorem toLp_dirLoss_mem_statSpan (a : J → ℝ) :
    (memLp_two_bdd Q (bdd_dirLoss hS a)).toLp (dirLoss S a) ∈ statSpan hS Q := by
  rw [toLp_dirLoss_eq_sum hS Q a]
  exact Submodule.sum_mem _ fun j _ ↦ Submodule.smul_mem _ _ (toLp_stat_mem_statSpan hS Q j)

/-- **The regression of `φ` on the statistic**: `E φ + (⟨a, S⟩ − E⟨a, S⟩)` in `L²(Q)`. -/
noncomputable def regressionLp (a : J → ℝ) (φ : X → ℝ) : Lp ℝ 2 Q :=
  (∫ x, φ x ∂Q) • oneLp Q + (memLp_two_bdd Q (bdd_dirLoss hS a)).toLp (dirLoss S a) -
    (∫ x, dirLoss S a x ∂Q) • oneLp Q

theorem regressionLp_mem_statSpan (a : J → ℝ) (φ : X → ℝ) :
    regressionLp hS Q a φ ∈ statSpan hS Q :=
  Submodule.sub_mem _ (Submodule.add_mem _ (Submodule.smul_mem _ _ (oneLp_mem_statSpan hS Q))
    (toLp_dirLoss_mem_statSpan hS Q a)) (Submodule.smul_mem _ _ (oneLp_mem_statSpan hS Q))

/-- **The projection onto the affine span of the statistic is the regression**, whenever the
coefficient solves the normal equations `Cov(S_j, ⟨a,S⟩) = Cov(S_j, φ)`. -/
theorem starProjection_statSpan_toLp {φ : X → ℝ} (hφ : Bdd φ) {a : J → ℝ}
    (hreg : ∀ j, lawCov Q (S j) (dirLoss S a) = lawCov Q (S j) φ) :
    (statSpan hS Q).starProjection ((memLp_two_bdd Q hφ).toLp φ) = regressionLp hS Q a φ := by
  refine Submodule.eq_starProjection_of_mem_of_inner_eq_zero (regressionLp_mem_statSpan hS Q a φ)
    fun w hw ↦ ?_
  have hdi := integrable_of_bdd_prob Q (bdd_dirLoss hS a)
  have hφi := integrable_of_bdd_prob Q hφ
  have h_one : inner ℝ ((memLp_two_bdd Q hφ).toLp φ - regressionLp hS Q a φ) (oneLp Q) = 0 := by
    rw [real_inner_comm]
    unfold regressionLp oneLp
    rw [inner_sub_right, inner_sub_right, inner_add_right, real_inner_smul_right,
      real_inner_smul_right, inner_toLp_toLp, inner_toLp_toLp, inner_toLp_toLp]
    simp only [one_mul, integral_const, probReal_univ, smul_eq_mul]
    ring
  have h_S : ∀ j, inner ℝ ((memLp_two_bdd Q hφ).toLp φ - regressionLp hS Q a φ)
      ((memLp_two_bdd Q (hS j)).toLp (S j)) = 0 := by
    intro j
    have hr := hreg j
    simp only [lawCov] at hr
    rw [real_inner_comm]
    unfold regressionLp oneLp
    rw [inner_sub_right, inner_sub_right, inner_add_right, real_inner_smul_right,
      real_inner_smul_right, inner_toLp_toLp, inner_toLp_toLp, inner_toLp_toLp]
    simp only [mul_one]
    linear_combination -hr
  have key : statSpan hS Q ≤ (ℝ ∙ ((memLp_two_bdd Q hφ).toLp φ - regressionLp hS Q a φ))ᗮ := by
    refine Submodule.span_le.2 ?_
    rintro f (rfl | ⟨j, rfl⟩)
    · rw [SetLike.mem_coe, Submodule.mem_orthogonal_singleton_iff_inner_right]
      exact h_one
    · rw [SetLike.mem_coe, Submodule.mem_orthogonal_singleton_iff_inner_right]
      exact h_S j
  exact Submodule.mem_orthogonal_singleton_iff_inner_right.1 (key hw)

/-- **The energy of the centred regression is the variance of the visible contrast**. -/
theorem norm_sq_regressionLp_sub (a : J → ℝ) (φ : X → ℝ) :
    ‖regressionLp hS Q a φ - (∫ x, φ x ∂Q) • oneLp Q‖ ^ 2 =
      lawCov Q (dirLoss S a) (dirLoss S a) := by
  have e : regressionLp hS Q a φ - (∫ x, φ x ∂Q) • oneLp Q =
      (memLp_two_bdd Q (bdd_dirLoss hS a)).toLp (dirLoss S a) -
        (∫ x, dirLoss S a x ∂Q) • oneLp Q := by
    unfold regressionLp
    abel
  rw [e, ← real_inner_self_eq_norm_sq]
  unfold oneLp
  rw [inner_sub_left, inner_sub_right, inner_sub_right, real_inner_smul_left,
    real_inner_smul_right, real_inner_smul_left, real_inner_smul_right, inner_toLp_toLp,
    inner_toLp_toLp, inner_toLp_toLp, inner_toLp_toLp]
  simp only [lawCov, mul_one, one_mul, integral_const, probReal_univ, smul_eq_mul]
  ring

/-- **The Fisher energy of the response velocity**: with `u_j = Cov_Q(S_j, φ)` and `a` solving the
normal equations, `‖B φ − E φ‖² = ⟨a, u⟩`. -/
theorem norm_sq_regressionLp_sub_eq_dotJ {φ : X → ℝ} {a : J → ℝ}
    (hreg : ∀ j, lawCov Q (S j) (dirLoss S a) = lawCov Q (S j) φ) :
    ‖regressionLp hS Q a φ - (∫ x, φ x ∂Q) • oneLp Q‖ ^ 2 =
      dotJ a (fun j ↦ lawCov Q (S j) φ) := by
  rw [norm_sq_regressionLp_sub hS Q a φ, lawCov_dirLoss_left hS Q a _ (bdd_dirLoss hS a)]
  simp only [dotJ]
  exact Finset.sum_congr rfl fun j _ ↦ by rw [hreg j]

end Regression

section Atlas

variable {X : Type*} [MeasurableSpace X] [Nonempty X] {J : Type*} [Fintype J] [Nonempty J]
  {S : J → X → ℝ} (hS : ∀ j, Bdd (S j)) (ν : Measure X) [IsProbabilityMeasure ν] {M : J → ℝ}
include hS

/-- **On the atlas path the projection onto the statistic is a visible regression**: there is a
coefficient in the visible subspace `𝕍` with `B φ = E φ + (⟨β, S⟩ − E⟨β, S⟩)` under
`P_{θ_s}`. -/
theorem starProjection_statSpan_toLp_atlas (Q : Measure X) [IsProbabilityMeasure Q] (s₀ : ℝ)
    (hQ : Q = familyMeasure ν (fun _ ↦ (1 : ℝ)) (fun _ ↦ (0 : ℝ)) S 1 (atlasTheta hS ν M s₀))
    {φ : X → ℝ} (hφ : Bdd φ) :
    ∃ β ∈ dirSpan ν (fun _ ↦ (1 : ℝ)) S,
      (statSpan hS Q).starProjection ((memLp_two_bdd Q hφ).toLp φ) = regressionLp hS Q β φ := by
  obtain ⟨β, hβ, hreg⟩ := exists_regression_coefficient hS ν (M := M) s₀ hφ
  refine ⟨β, hβ, starProjection_statSpan_toLp hS Q hφ fun j ↦ ?_⟩
  rw [hQ]
  exact hreg j

end Atlas

end Laplace.Multi
