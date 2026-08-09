/-
Copyright (c) 2026 Timaeus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib
import Laplace.Multi.NormalizedRate
import Laplace.Multi.MultilinearDiagonal
import Laplace.Multi.GaussianCovariance

/-!
# Single-degree tensor recovery

Stage J6 of the tensor programme, the composition: two losses with
the higher-order domain packages, matched derivative tensors below
order `k`, permutation-symmetric `k`-th tensors, and rescaled moment
data agreeing to `o(q^(k-2))` at every continuous polynomial-growth
homogeneous test of degree `k`, have equal `k`-th derivative tensors
at the origin. The chain: instantiate the data at the diagonal
difference itself, J5e turns the rate into minus its self-covariance,
uniqueness of limits kills the covariance, J2 rigidity kills the
diagonal, and J3 polarization upgrades diagonal equality to tensor
equality.
-/

open Real MeasureTheory Filter Topology Asymptotics

namespace Laplace.Multi

variable {d : ℕ}

/-- The diagonal Taylor term is continuous. -/
theorem taylorHomogeneousTerm_continuous (k : ℕ) (L : EuclidD d → ℝ) :
    Continuous (taylorHomogeneousTerm k L) := by
  unfold taylorHomogeneousTerm
  refine continuous_const.mul ?_
  exact (iteratedFDeriv ℝ k L 0).cont.comp
    (continuous_pi fun _ ↦ continuous_id)

/-- The diagonal Taylor term has polynomial growth. -/
theorem taylorHomogeneousTerm_hasPolynomialGrowth (k : ℕ)
    (L : EuclidD d → ℝ) :
    HasPolynomialGrowth (taylorHomogeneousTerm k L) := by
  refine ⟨(k.factorial : ℝ)⁻¹ * ‖iteratedFDeriv ℝ k L 0‖, k,
    by positivity, fun x ↦ ?_⟩
  unfold taylorHomogeneousTerm
  rw [abs_mul, abs_of_nonneg (by positivity :
    (0:ℝ) ≤ (k.factorial : ℝ)⁻¹)]
  have hbound : |(iteratedFDeriv ℝ k L 0) (fun _ ↦ x)| ≤
      ‖iteratedFDeriv ℝ k L 0‖ * ‖x‖ ^ k := by
    have h := (iteratedFDeriv ℝ k L 0).le_opNorm (fun _ ↦ x)
    rw [Real.norm_eq_abs] at h
    calc |(iteratedFDeriv ℝ k L 0) (fun _ ↦ x)|
        ≤ ‖iteratedFDeriv ℝ k L 0‖ * ∏ _i : Fin k, ‖x‖ := h
      _ = ‖iteratedFDeriv ℝ k L 0‖ * ‖x‖ ^ k := by
          rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  calc (k.factorial : ℝ)⁻¹ * |(iteratedFDeriv ℝ k L 0) (fun _ ↦ x)|
      ≤ (k.factorial : ℝ)⁻¹ *
          (‖iteratedFDeriv ℝ k L 0‖ * ‖x‖ ^ k) := by
        apply mul_le_mul_of_nonneg_left hbound (by positivity)
    _ ≤ (k.factorial : ℝ)⁻¹ * ‖iteratedFDeriv ℝ k L 0‖ *
          (1 + ‖x‖ ^ k) := by
        have hfac : (0:ℝ) ≤ (k.factorial : ℝ)⁻¹ := by positivity
        nlinarith [pow_nonneg (norm_nonneg x) k,
          norm_nonneg (iteratedFDeriv ℝ k L 0)]

namespace HigherLaplaceDomain

variable {k : ℕ} {L₁ L₂ : EuclidD d → ℝ}
  {H : Matrix (Fin d) (Fin d) ℝ}

/-- **Single-degree tensor recovery** (J6): `o(q^(k-2))` rescaled
moment data at every homogeneous degree-`k` test identifies the
`k`-th derivative tensor. -/
theorem iteratedFDeriv_recovery_of_moment_rates (hk : 2 < k)
    (A₁ : HigherLaplaceDomain k L₁ H) (A₂ : HigherLaplaceDomain k L₂ H)
    (hlower : ∀ j < k,
      iteratedFDeriv ℝ j L₁ 0 = iteratedFDeriv ℝ j L₂ 0)
    (hsymm₁ : (iteratedFDeriv ℝ k L₁ 0).IsSymm)
    (hsymm₂ : (iteratedFDeriv ℝ k L₂ 0).IsSymm)
    (hdata : ∀ P : EuclidD d → ℝ, Continuous P →
      HasPolynomialGrowth P → IsHomogeneousOfDegree k P →
      (fun q : ℝ ↦ A₁.rescaledMoment P q - A₂.rescaledMoment P q)
        =o[𝓝[>] (0 : ℝ)] fun q : ℝ ↦ q ^ (k - 2)) :
    iteratedFDeriv ℝ k L₁ 0 = iteratedFDeriv ℝ k L₂ 0 := by
  set Q : EuclidD d → ℝ := fun x ↦
    taylorHomogeneousTerm k L₁ x - taylorHomogeneousTerm k L₂ x
    with hQ_def
  -- certificates for Q
  have hQ_cont : Continuous Q :=
    (taylorHomogeneousTerm_continuous k L₁).sub
      (taylorHomogeneousTerm_continuous k L₂)
  have hQ_growth : HasPolynomialGrowth Q := by
    obtain ⟨C₁, n₁, hC₁, h₁⟩ :=
      taylorHomogeneousTerm_hasPolynomialGrowth k L₁
    obtain ⟨C₂, n₂, hC₂, h₂⟩ :=
      taylorHomogeneousTerm_hasPolynomialGrowth k L₂
    refine ⟨2 * (C₁ + C₂), max n₁ n₂, by linarith, fun x ↦ ?_⟩
    have hmax : ∀ n m : ℕ, n ≤ m →
        (1 + ‖x‖ ^ n) ≤ 2 * (1 + ‖x‖ ^ m) := by
      intro n m hnm
      rcases le_total ‖x‖ 1 with hy | hy
      · have := pow_le_one₀ (norm_nonneg x) hy (n := n)
        have h2 : (0:ℝ) ≤ ‖x‖ ^ m := by positivity
        linarith
      · have := pow_le_pow_right₀ hy hnm
        have h2 : (0:ℝ) ≤ ‖x‖ ^ n := by positivity
        linarith
    have hb₁ := h₁ x
    have hb₂ := h₂ x
    have hle₁ : (1 + ‖x‖ ^ n₁) ≤ 2 * (1 + ‖x‖ ^ max n₁ n₂) :=
      hmax n₁ _ (le_max_left _ _)
    have hle₂ : (1 + ‖x‖ ^ n₂) ≤ 2 * (1 + ‖x‖ ^ max n₁ n₂) :=
      hmax n₂ _ (le_max_right _ _)
    calc |Q x| ≤ |taylorHomogeneousTerm k L₁ x| +
          |taylorHomogeneousTerm k L₂ x| := abs_sub _ _
      _ ≤ C₁ * (1 + ‖x‖ ^ n₁) + C₂ * (1 + ‖x‖ ^ n₂) := by
          linarith
      _ ≤ 2 * (C₁ + C₂) * (1 + ‖x‖ ^ max n₁ n₂) := by
          nlinarith [mul_le_mul_of_nonneg_left hle₁ hC₁,
            mul_le_mul_of_nonneg_left hle₂ hC₂]
  have hQ_hom : IsHomogeneousOfDegree k Q := by
    intro a x
    rw [hQ_def]
    simp only []
    rw [taylorHomogeneousTerm_smul, taylorHomogeneousTerm_smul]
    ring
  -- instantiate the data at Q and identify the covariance
  have hQdata := hdata Q hQ_cont hQ_growth hQ_hom
  have hzero : Tendsto (fun q : ℝ ↦
      (A₁.rescaledMoment Q q - A₂.rescaledMoment Q q) / q ^ (k - 2))
      (𝓝[>] (0 : ℝ)) (𝓝 0) :=
    hQdata.tendsto_div_nhds_zero
  have hlim := tendsto_pairwise_normalized_moment_difference hk
    A₁ A₂ hlower hQ_cont hQ_growth
  have hcov : -gaussianCovariance H Q Q = 0 :=
    tendsto_nhds_unique hlim hzero
  have hcov' : gaussianCovariance H Q Q = 0 := by linarith
  -- rigidity kills Q
  have hQ0 : Q = 0 :=
    homogeneous_eq_zero_of_gaussianCovariance_self_eq_zero
      A₁.hH_posDef (by omega) hQ_cont hQ_growth hQ_hom hcov'
  -- equal diagonals
  have hdiag : ∀ x : EuclidD d,
      iteratedFDeriv ℝ k L₁ 0 (fun _ ↦ x) =
        iteratedFDeriv ℝ k L₂ 0 (fun _ ↦ x) := by
    intro x
    have hx := congrFun hQ0 x
    rw [hQ_def] at hx
    simp only [Pi.zero_apply] at hx
    unfold taylorHomogeneousTerm at hx
    have hfac : ((k.factorial : ℝ)⁻¹ : ℝ) ≠ 0 := by
      have : (k.factorial : ℝ) ≠ 0 := by
        exact_mod_cast (Nat.factorial_ne_zero k)
      exact inv_ne_zero this
    have hx' : (k.factorial : ℝ)⁻¹ *
        (iteratedFDeriv ℝ k L₁ 0 (fun _ ↦ x)) =
        (k.factorial : ℝ)⁻¹ *
        (iteratedFDeriv ℝ k L₂ 0 (fun _ ↦ x)) := by
      linarith [hx]
    exact mul_left_cancel₀ hfac hx'
  -- polarization upgrades to tensors
  exact iteratedFDeriv_eq_of_diag_eq hsymm₁ hsymm₂ hdiag

end HigherLaplaceDomain

end Laplace.Multi
