/-
Copyright (c) 2026 Timaeus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Timaeus
-/
import Laplace.Multi.ResponseLocalMetricControl
import Laplace.Multi.HellingerFisherControl
import Laplace.Multi.SqrtDensityAffinity

/-!
# Local testing of responses: the two-sided Hellinger–Fisher comparison

Hellinger distance between two response laws is at most half their intrinsic Fisher distance
(`hellingerDist_le_half_fisherDist`). This module proves the **local converse** on a coercive
convex patch of interior means: with `‖S − a‖₂ ≤ B` and covariance coercivity `λ` on the patch,

`√λ · d_F(θ(M₀), θ(M₁)) ≤ 2B · H(P_{θ(M₀)}, P_{θ(M₁)}) ≤ B · d_F(θ(M₀), θ(M₁))`

(`sqrt_mul_fisherDist_le_hellinger`, `hellinger_fisher_sandwich`). The engine is **mean control by
Hellinger**: for any bounded contrast, `|E_P f − E_Q f| ≤ 2 ‖f − c‖_∞ H(P,Q)`
(`abs_dotJ_meanMap_sub_le_hellinger`), hence `‖m(P) − m(Q)‖₂ ≤ 2B H(P,Q)`
(`sqrt_dotJ_meanMap_sub_le_hellinger`), combined with the local metric control
`d_F ≤ ‖Δm‖₂/√λ`.

Statistically, the `n`-sample Bhattacharyya affinity of two responses on the patch decays as
`exp(−n λ d_F² / (8B²))` (`pow_affinity_le_exp_fisher`): the binary testing scale between responses
is `n^{−1/2}` in Fisher distance, with explicit patch constants.
-/

open MeasureTheory Filter Topology Set

namespace Laplace.Multi

section Mean

variable {X : Type*} [MeasurableSpace X] [Nonempty X] {J : Type*} [Fintype J]
  {S : J → X → ℝ} (hS : ∀ j, Bdd (S j)) (ν : Measure X) [IsProbabilityMeasure ν]
include hS

/-- The mean map. -/
local notation "mean" => meanMap ν (fun _ ↦ (1 : ℝ)) (fun _ ↦ (0 : ℝ)) S 1

omit [Nonempty X] [IsProbabilityMeasure ν] hS in
theorem hellingerDist_comm (θ η : J → ℝ) : hellingerDist S ν θ η = hellingerDist S ν η θ := by
  unfold hellingerDist
  congr 1
  exact integral_congr_ae (Eventually.of_forall fun x ↦ by ring)

omit [Nonempty X] in
theorem integral_rootDens_mul_self (θ : J → ℝ) :
    ∫ x, rootDens S ν θ x * rootDens S ν θ x ∂ν = 1 := by
  simp_rw [← sq]
  exact integral_rootDens_sq hS ν θ

/-- `⟨w, m(θ)⟩ = ∫ q_θ² (⟨w,S⟩ − c) + c` for any centring constant `c`. -/
theorem dotJ_meanMap_eq_integral_rootDens (θ w : J → ℝ) (c : ℝ) :
    dotJ w (mean θ) =
      (∫ x, rootDens S ν θ x * rootDens S ν θ x * (dirLoss S w x - c) ∂ν) + c := by
  rw [← famMean_eq_meanMap hS ν, ← integral_famDens_mul_dirLoss hS ν θ w]
  have hq : Bdd fun x ↦ rootDens S ν θ x * rootDens S ν θ x :=
    (bdd_rootDens hS ν θ).mul (bdd_rootDens hS ν θ)
  have e : ∀ x, famDens S ν θ x * dirLoss S w x =
      rootDens S ν θ x * rootDens S ν θ x * (dirLoss S w x - c) +
        rootDens S ν θ x * rootDens S ν θ x * c := fun x ↦ by
    rw [← rootDens_sq hS ν, sq]
    ring
  simp_rw [e]
  rw [integral_add (integrable_of_bdd_prob ν (hq.mul ((bdd_dirLoss hS w).sub (Bdd.const c))))
    (integrable_of_bdd_prob ν (hq.mul (Bdd.const c))), integral_mul_const,
    integral_rootDens_mul_self hS ν θ, one_mul]

/-- **Mean control by Hellinger**: `|⟨w, m(θ) − m(η)⟩| ≤ 2 ‖⟨w,S⟩ − c‖_∞ H(θ, η)`. -/
theorem abs_dotJ_meanMap_sub_le_hellinger (θ η w : J → ℝ) {c K : ℝ}
    (hK : ∀ x, |dirLoss S w x - c| ≤ K) :
    |dotJ w (mean θ - mean η)| ≤ 2 * K * hellingerDist S ν θ η := by
  have hK0 : 0 ≤ K := (abs_nonneg _).trans (hK (Classical.arbitrary X))
  have hH0 := hellingerDist_nonneg S ν θ η
  have hf : Bdd fun x ↦ rootDens S ν θ x - rootDens S ν η x :=
    (bdd_rootDens hS ν θ).sub (bdd_rootDens hS ν η)
  have hg : Bdd fun x ↦ (rootDens S ν θ x + rootDens S ν η x) * (dirLoss S w x - c) :=
    ((bdd_rootDens hS ν θ).add (bdd_rootDens hS ν η)).mul ((bdd_dirLoss hS w).sub (Bdd.const c))
  have hd : dotJ w (mean θ - mean η) = ∫ x, (rootDens S ν θ x - rootDens S ν η x) *
      ((rootDens S ν θ x + rootDens S ν η x) * (dirLoss S w x - c)) ∂ν := by
    rw [(isLinearMap_dotJ w).map_sub, dotJ_meanMap_eq_integral_rootDens hS ν θ w c,
      dotJ_meanMap_eq_integral_rootDens hS ν η w c, add_sub_add_right_eq_sub,
      ← integral_sub (integrable_of_bdd_prob ν
        (((bdd_rootDens hS ν θ).mul (bdd_rootDens hS ν θ)).mul
          ((bdd_dirLoss hS w).sub (Bdd.const c)))) (integrable_of_bdd_prob ν
        (((bdd_rootDens hS ν η).mul (bdd_rootDens hS ν η)).mul
          ((bdd_dirLoss hS w).sub (Bdd.const c))))]
    exact integral_congr_ae (Eventually.of_forall fun x ↦ by ring)
  have hgg : ∫ x, ((rootDens S ν θ x + rootDens S ν η x) * (dirLoss S w x - c)) *
      ((rootDens S ν θ x + rootDens S ν η x) * (dirLoss S w x - c)) ∂ν ≤ 4 * K ^ 2 := by
    have hpt : ∀ x, ((rootDens S ν θ x + rootDens S ν η x) * (dirLoss S w x - c)) *
        ((rootDens S ν θ x + rootDens S ν η x) * (dirLoss S w x - c)) ≤
        K ^ 2 * (2 * (rootDens S ν θ x * rootDens S ν θ x) +
          2 * (rootDens S ν η x * rootDens S ν η x)) := fun x ↦ by
      have h1 : (dirLoss S w x - c) ^ 2 ≤ K ^ 2 := by
        rw [← sq_abs]
        exact pow_le_pow_left₀ (abs_nonneg _) (hK x) 2
      calc ((rootDens S ν θ x + rootDens S ν η x) * (dirLoss S w x - c)) *
            ((rootDens S ν θ x + rootDens S ν η x) * (dirLoss S w x - c)) =
            (rootDens S ν θ x + rootDens S ν η x) ^ 2 * (dirLoss S w x - c) ^ 2 := by ring
        _ ≤ (rootDens S ν θ x + rootDens S ν η x) ^ 2 * K ^ 2 :=
            mul_le_mul_of_nonneg_left h1 (sq_nonneg _)
        _ ≤ K ^ 2 * (2 * (rootDens S ν θ x * rootDens S ν θ x) +
              2 * (rootDens S ν η x * rootDens S ν η x)) := by
            nlinarith [sq_nonneg (rootDens S ν θ x - rootDens S ν η x), sq_nonneg K]
    have hq1 : Bdd fun x ↦ rootDens S ν θ x * rootDens S ν θ x :=
      (bdd_rootDens hS ν θ).mul (bdd_rootDens hS ν θ)
    have hq2 : Bdd fun x ↦ rootDens S ν η x * rootDens S ν η x :=
      (bdd_rootDens hS ν η).mul (bdd_rootDens hS ν η)
    have hint : Integrable (fun x ↦ 2 * (rootDens S ν θ x * rootDens S ν θ x) +
        2 * (rootDens S ν η x * rootDens S ν η x)) ν :=
      ((integrable_of_bdd_prob ν hq1).const_mul 2).add ((integrable_of_bdd_prob ν hq2).const_mul 2)
    calc _ ≤ ∫ x, K ^ 2 * (2 * (rootDens S ν θ x * rootDens S ν θ x) +
          2 * (rootDens S ν η x * rootDens S ν η x)) ∂ν :=
          integral_mono (integrable_of_bdd_prob ν (hg.mul hg)) (hint.const_mul _) hpt
      _ = 4 * K ^ 2 := by
          rw [integral_const_mul, integral_add ((integrable_of_bdd_prob ν hq1).const_mul 2)
            ((integrable_of_bdd_prob ν hq2).const_mul 2), integral_const_mul, integral_const_mul,
            integral_rootDens_mul_self hS ν θ, integral_rootDens_mul_self hS ν η]
          ring
  have hsq : dotJ w (mean θ - mean η) ^ 2 ≤ (2 * K * hellingerDist S ν θ η) ^ 2 := by
    rw [hd]
    calc _ ≤ (∫ x, (rootDens S ν θ x - rootDens S ν η x) *
          (rootDens S ν θ x - rootDens S ν η x) ∂ν) *
          ∫ x, ((rootDens S ν θ x + rootDens S ν η x) * (dirLoss S w x - c)) *
            ((rootDens S ν θ x + rootDens S ν η x) * (dirLoss S w x - c)) ∂ν :=
          sq_integral_mul_le ν hf hg
      _ ≤ hellingerDist S ν θ η ^ 2 * (4 * K ^ 2) := by
          rw [← hellingerDist_sq]
          exact mul_le_mul_of_nonneg_left hgg (sq_nonneg _)
      _ = (2 * K * hellingerDist S ν θ η) ^ 2 := by ring
  rw [← sq_abs] at hsq
  exact (pow_le_pow_iff_left₀ (abs_nonneg _) (by positivity) two_ne_zero).1 hsq

/-- **Euclidean mean control by Hellinger**: with `‖S − a‖₂ ≤ B`,
`‖m(θ) − m(η)‖₂ ≤ 2B H(θ, η)`. -/
theorem sqrt_dotJ_meanMap_sub_le_hellinger (θ η : J → ℝ) {a : J → ℝ} {B : ℝ} (hB0 : 0 ≤ B)
    (hB : ∀ x, dotJ (statPoint S x - a) (statPoint S x - a) ≤ B ^ 2) :
    √(dotJ (mean θ - mean η) (mean θ - mean η)) ≤ 2 * B * hellingerDist S ν θ η := by
  obtain ⟨w, hw⟩ : ∃ w : J → ℝ, w = mean θ - mean η := ⟨_, rfl⟩
  rw [← hw]
  have hww := dotJ_self_nonneg w
  have hH0 := hellingerDist_nonneg S ν θ η
  have hK : ∀ x, |dirLoss S w x - dotJ w a| ≤ √(dotJ w w) * B := fun x ↦ by
    rw [dirLoss_eq_dotJ_statPoint, ← (isLinearMap_dotJ w).map_sub, ← Real.sqrt_sq_eq_abs]
    calc √(dotJ w (statPoint S x - a) ^ 2) ≤
          √(dotJ w w * dotJ (statPoint S x - a) (statPoint S x - a)) :=
          Real.sqrt_le_sqrt (sq_dotJ_le _ _)
      _ ≤ √(dotJ w w * B ^ 2) := Real.sqrt_le_sqrt (mul_le_mul_of_nonneg_left (hB x) hww)
      _ = √(dotJ w w) * B := by rw [Real.sqrt_mul hww, Real.sqrt_sq hB0]
  have h := abs_dotJ_meanMap_sub_le_hellinger hS ν θ η w hK
  rw [← hw, abs_of_nonneg hww] at h
  rcases (Real.sqrt_nonneg (dotJ w w)).lt_or_eq with hpos | hzero
  · refine le_of_mul_le_mul_left ?_ hpos
    calc √(dotJ w w) * √(dotJ w w) = dotJ w w := Real.mul_self_sqrt hww
      _ ≤ 2 * (√(dotJ w w) * B) * hellingerDist S ν θ η := h
      _ = √(dotJ w w) * (2 * B * hellingerDist S ν θ η) := by ring
  · rw [← hzero]
    exact mul_nonneg (mul_nonneg two_pos.le hB0) hH0

omit [Nonempty X] in
/-- The Bhattacharyya affinity is `1 − H²/2`. -/
theorem integral_rootDens_mul_eq_one_sub (θ η : J → ℝ) :
    ∫ x, rootDens S ν θ x * rootDens S ν η x ∂ν = 1 - hellingerDist S ν θ η ^ 2 / 2 := by
  rw [hellingerDist_sq]
  have e : ∀ x, (rootDens S ν θ x - rootDens S ν η x) * (rootDens S ν θ x - rootDens S ν η x) =
      rootDens S ν θ x * rootDens S ν θ x + rootDens S ν η x * rootDens S ν η x -
        2 * (rootDens S ν θ x * rootDens S ν η x) := fun x ↦ by ring
  simp_rw [e]
  have hq1 : Bdd fun x ↦ rootDens S ν θ x * rootDens S ν θ x :=
    (bdd_rootDens hS ν θ).mul (bdd_rootDens hS ν θ)
  have hq2 : Bdd fun x ↦ rootDens S ν η x * rootDens S ν η x :=
    (bdd_rootDens hS ν η).mul (bdd_rootDens hS ν η)
  have hq3 : Bdd fun x ↦ rootDens S ν θ x * rootDens S ν η x :=
    (bdd_rootDens hS ν θ).mul (bdd_rootDens hS ν η)
  have h12 : Integrable (fun x ↦ rootDens S ν θ x * rootDens S ν θ x +
      rootDens S ν η x * rootDens S ν η x) ν :=
    (integrable_of_bdd_prob ν hq1).add (integrable_of_bdd_prob ν hq2)
  rw [integral_sub h12 ((integrable_of_bdd_prob ν hq3).const_mul 2),
    integral_add (integrable_of_bdd_prob ν hq1) (integrable_of_bdd_prob ν hq2), integral_const_mul,
    integral_rootDens_mul_self hS ν θ, integral_rootDens_mul_self hS ν η]
  ring

omit [Nonempty X] in
/-- **The `n`-sample affinity decays exponentially in the Hellinger distance**:
`A(θ,η)^n ≤ exp(−n H²/2)`. -/
theorem pow_affinity_le_exp (θ η : J → ℝ) (n : ℕ) :
    (∫ x, rootDens S ν θ x * rootDens S ν η x ∂ν) ^ n ≤
      Real.exp (-(n * hellingerDist S ν θ η ^ 2 / 2)) := by
  have h0 : 0 ≤ ∫ x, rootDens S ν θ x * rootDens S ν η x ∂ν :=
    integral_nonneg fun x ↦ mul_nonneg (rootDens_nonneg S ν θ x) (rootDens_nonneg S ν η x)
  rw [integral_rootDens_mul_eq_one_sub hS ν] at h0 ⊢
  have h1 : 1 - hellingerDist S ν θ η ^ 2 / 2 ≤ Real.exp (-(hellingerDist S ν θ η ^ 2 / 2)) := by
    have := Real.add_one_le_exp (-(hellingerDist S ν θ η ^ 2 / 2))
    linarith
  calc (1 - hellingerDist S ν θ η ^ 2 / 2) ^ n ≤
        Real.exp (-(hellingerDist S ν θ η ^ 2 / 2)) ^ n := pow_le_pow_left₀ h0 h1 n
    _ = Real.exp (-(n * hellingerDist S ν θ η ^ 2 / 2)) := by
        rw [← Real.exp_nat_mul]
        congr 1
        ring

end Mean

section Patch

variable {X : Type*} [MeasurableSpace X] [Nonempty X] {J : Type*} [Fintype J] [Nonempty J]
  {S : J → X → ℝ} (hS : ∀ j, Bdd (S j)) (ν : Measure X) [IsProbabilityMeasure ν]
include hS

/-- The direction space. -/
local notation "𝕍" => dirSpan ν (fun _ ↦ (1 : ℝ)) S

/-- The response (inverse chart). -/
local notation "θr" => responseTheta measurable_const (integrable_const 1) (fun _ ↦ one_pos)
  (one_integral_pos ν) hS

variable {U : Set (J → ℝ)} (hU : Convex ℝ U)
  (hUint : U ⊆ intrinsicInterior ℝ (momentBody ν (fun _ ↦ (1 : ℝ)) S))
include hU hUint

/-- **The local converse**: on a coercive convex patch of interior means, with `‖S − a‖₂ ≤ B`,
`√λ · d_F(θ(M₀), θ(M₁)) ≤ 2B · H(P_{θ(M₀)}, P_{θ(M₁)})`. -/
theorem sqrt_mul_fisherDist_le_hellinger {lam : ℝ} (hlam : 0 < lam)
    (hcoer : ∀ M ∈ U, ∀ w : J → ℝ, lam * dotJ w w ≤ fisherVar S ν (θr M : J → ℝ) w)
    {a : J → ℝ} {B : ℝ} (hB0 : 0 ≤ B)
    (hB : ∀ x, dotJ (statPoint S x - a) (statPoint S x - a) ≤ B ^ 2)
    {M₀ M₁ : J → ℝ} (h₀ : M₀ ∈ U) (h₁ : M₁ ∈ U) :
    √lam * fisherDist S ν (θr M₀) (θr M₁) ≤
      2 * B * hellingerDist S ν (θr M₀ : J → ℝ) (θr M₁ : J → ℝ) := by
  have hd := fisherDist_responseTheta_le hS ν hU hUint hlam hcoer h₀ h₁
  have hm := sqrt_dotJ_meanMap_sub_le_hellinger hS ν (θr M₁ : J → ℝ) (θr M₀ : J → ℝ) hB0 hB
  rw [meanMap_responseTheta measurable_const (integrable_const 1) (fun _ ↦ one_pos)
    (one_integral_pos ν) hS (hUint h₁), meanMap_responseTheta measurable_const (integrable_const 1)
    (fun _ ↦ one_pos) (one_integral_pos ν) hS (hUint h₀), hellingerDist_comm] at hm
  have hl : 0 < √lam := Real.sqrt_pos.2 hlam
  calc √lam * fisherDist S ν (θr M₀) (θr M₁) ≤
        √lam * (√(dotJ (M₁ - M₀) (M₁ - M₀)) / √lam) := mul_le_mul_of_nonneg_left hd hl.le
    _ = √(dotJ (M₁ - M₀) (M₁ - M₀)) := mul_div_cancel₀ _ hl.ne'
    _ ≤ 2 * B * hellingerDist S ν (θr M₀ : J → ℝ) (θr M₁ : J → ℝ) := hm

/-- **The two-sided Hellinger–Fisher comparison on a coercive patch**:
`√λ · d_F ≤ 2B · H ≤ B · d_F`. -/
theorem hellinger_fisher_sandwich {lam : ℝ} (hlam : 0 < lam)
    (hcoer : ∀ M ∈ U, ∀ w : J → ℝ, lam * dotJ w w ≤ fisherVar S ν (θr M : J → ℝ) w)
    {a : J → ℝ} {B : ℝ} (hB0 : 0 ≤ B)
    (hB : ∀ x, dotJ (statPoint S x - a) (statPoint S x - a) ≤ B ^ 2)
    {M₀ M₁ : J → ℝ} (h₀ : M₀ ∈ U) (h₁ : M₁ ∈ U) :
    √lam * fisherDist S ν (θr M₀) (θr M₁) ≤
        2 * B * hellingerDist S ν (θr M₀ : J → ℝ) (θr M₁ : J → ℝ) ∧
      hellingerDist S ν (θr M₀ : J → ℝ) (θr M₁ : J → ℝ) ≤
        1 / 2 * fisherDist S ν (θr M₀) (θr M₁) :=
  ⟨sqrt_mul_fisherDist_le_hellinger hS ν hU hUint hlam hcoer hB0 hB h₀ h₁, by
    rw [hellingerDist_comm]
    exact hellingerDist_le_half_fisherDist hS ν _ _⟩

/-- **Exponential testing separation of responses in Fisher distance**: on a coercive patch the
`n`-sample affinity of two responses is at most `exp(−n λ d_F² / (8B²))`. -/
theorem pow_affinity_le_exp_fisher {lam : ℝ} (hlam : 0 < lam)
    (hcoer : ∀ M ∈ U, ∀ w : J → ℝ, lam * dotJ w w ≤ fisherVar S ν (θr M : J → ℝ) w)
    {a : J → ℝ} {B : ℝ} (hB0 : 0 < B)
    (hB : ∀ x, dotJ (statPoint S x - a) (statPoint S x - a) ≤ B ^ 2)
    {M₀ M₁ : J → ℝ} (h₀ : M₀ ∈ U) (h₁ : M₁ ∈ U) (n : ℕ) :
    (∫ x, rootDens S ν (θr M₀ : J → ℝ) x * rootDens S ν (θr M₁ : J → ℝ) x ∂ν) ^ n ≤
      Real.exp (-(n * (lam * fisherDist S ν (θr M₀) (θr M₁) ^ 2 / (8 * B ^ 2)))) := by
  refine (pow_affinity_le_exp hS ν _ _ n).trans (Real.exp_le_exp.2 (neg_le_neg ?_))
  have h := sqrt_mul_fisherDist_le_hellinger hS ν hU hUint hlam hcoer hB0.le hB h₀ h₁
  have hd0 : 0 ≤ fisherDist S ν (θr M₀) (θr M₁) := fisherDist_nonneg
  have hsq := pow_le_pow_left₀ (mul_nonneg (Real.sqrt_nonneg _) hd0) h 2
  rw [mul_pow, Real.sq_sqrt hlam.le] at hsq
  have hB2 : 0 < 8 * B ^ 2 := by positivity
  have hkey : lam * fisherDist S ν (θr M₀) (θr M₁) ^ 2 / (8 * B ^ 2) ≤
      hellingerDist S ν (θr M₀ : J → ℝ) (θr M₁ : J → ℝ) ^ 2 / 2 := by
    rw [div_le_iff₀ hB2]
    nlinarith [hsq]
  calc n * (lam * fisherDist S ν (θr M₀) (θr M₁) ^ 2 / (8 * B ^ 2)) ≤
        n * (hellingerDist S ν (θr M₀ : J → ℝ) (θr M₁ : J → ℝ) ^ 2 / 2) :=
        mul_le_mul_of_nonneg_left hkey (Nat.cast_nonneg n)
    _ = n * hellingerDist S ν (θr M₀ : J → ℝ) (θr M₁ : J → ℝ) ^ 2 / 2 := by ring

end Patch

end Laplace.Multi
