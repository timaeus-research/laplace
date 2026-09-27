/-
Copyright (c) 2026 Timaeus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Timaeus
-/
import Laplace.Multi.EmpiricalMoments
import Laplace.Multi.ResponsePullbackMetric
import Laplace.Multi.BoundaryBlowup

/-!
# Sampling resolution of the structural coordinate

The structural coordinate `m = E_ρ S` moves for two reasons: the truth moves (along the data path
`ρ_t ∝ e^{th} ν` the shift per unit time is the forcing `b_t = Cov_{ρ_t}(S, h)`), and sampling
replaces `m` by the empirical response `M̂_n`. In a direction `w` the two shifts are

* signal: `⟨w, b_t⟩ = Cov_{ρ_t}(⟨w,S⟩, h)`;
* noise:  `E[⟨w, M̂_n − m⟩²] = Var_{ρ_t}⟨w,S⟩ / n`  (`integral_sq_dotJ_sampleResponse_sub`).

Cauchy–Schwarz for covariances gives the **resolution floor**

`⟨w, b_t⟩² ≤ n · E[⟨w, M̂_n − m⟩²] · Var_{ρ_t} h`   (`sq_signal_le_mul_noise`),

so a truth shift `δt` is visible above the sampling noise in some direction of the observables
only if `δt² ≥ 1 / (n Var_{ρ_t} h)` (`resolution_floor`): two data distributions whose
separation along the data manifold is below this floor produce structural coordinates that
sampling cannot tell apart, whatever the wall-and-chamber geometry of the response does with
them. The floor is the data Fisher–Rao length `√(Var_{ρ_t} h) δt` compared with `1/√n`.
-/

open MeasureTheory ProbabilityTheory Filter Topology Set

namespace Laplace.Multi

section Noise

variable {X : Type*} {J : Type*} {Ω : Type*} [MeasurableSpace X] [Fintype J] {S : J → X → ℝ}
  (hS : ∀ j, Bdd (S j)) [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
  (D : Measure X) [IsProbabilityMeasure D] (Xs : ℕ → Ω → X) (hXm : ∀ i, Measurable (Xs i))
  (hid : ∀ i, IdentDistrib (Xs i) (Xs 0) P P) (hlaw : P.map (Xs 0) = D)
include hS hXm hid hlaw

omit [Fintype J] hS [MeasurableSpace Ω] [IsProbabilityMeasure P] hXm hid hlaw in
/-- The centred empirical response is bounded. -/
theorem abs_sampleResponse_sub_le {n : ℕ} (hn : 0 < n) (a : J) {B : ℝ}
    (hB : ∀ x, |S a x| ≤ B) (ω : Ω) :
    |sampleResponse S Xs n ω a - ∫ x, S a x ∂D| ≤ 2 * B := by
  rw [sampleResponse_sub_eq D Xs hn ω a, abs_div, Nat.abs_cast]
  have hmean : |∫ x, S a x ∂D| ≤ B := by
    refine (norm_integral_le_of_norm_le_const (μ := D) (f := S a) (C := B)
      (Eventually.of_forall fun x ↦ hB x)).trans ?_
    simp [probReal_univ]
  have hterm : ∀ i, |S a (Xs i ω) - ∫ x, S a x ∂D| ≤ 2 * B := fun i ↦
    (abs_sub _ _).trans (by linarith [hB (Xs i ω)])
  rw [div_le_iff₀ (by exact_mod_cast hn)]
  calc |∑ i ∈ Finset.range n, (S a (Xs i ω) - ∫ x, S a x ∂D)|
      ≤ ∑ i ∈ Finset.range n, |S a (Xs i ω) - ∫ x, S a x ∂D| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _i ∈ Finset.range n, 2 * B := Finset.sum_le_sum fun i _ ↦ hterm i
    _ = 2 * B * n := by simp [mul_comm]

omit [Fintype J] hid hlaw in
/-- Products of centred empirical responses are integrable. -/
theorem integrable_sampleResponse_sub_mul {n : ℕ} (hn : 0 < n) (a b : J) :
    Integrable (fun ω ↦ (sampleResponse S Xs n ω a - ∫ x, S a x ∂D) *
      (sampleResponse S Xs n ω b - ∫ x, S b x ∂D)) P := by
  obtain ⟨_, Ba, hBa⟩ := hS a
  obtain ⟨_, Bb, hBb⟩ := hS b
  have hm : Measurable fun ω ↦ (sampleResponse S Xs n ω a - ∫ x, S a x ∂D) *
      (sampleResponse S Xs n ω b - ∫ x, S b x ∂D) :=
    (((measurable_pi_apply a).comp (measurable_sampleResponse hS Xs hXm n)).sub
      measurable_const).mul (((measurable_pi_apply b).comp
        (measurable_sampleResponse hS Xs hXm n)).sub measurable_const)
  refine Integrable.of_bound hm.aestronglyMeasurable ((2 * Ba) * (2 * Bb))
    (Eventually.of_forall fun ω ↦ ?_)
  rw [Real.norm_eq_abs, abs_mul]
  exact mul_le_mul (abs_sampleResponse_sub_le D Xs hn a hBa ω)
    (abs_sampleResponse_sub_le D Xs hn b hBb ω) (abs_nonneg _)
    ((abs_nonneg _).trans (abs_sampleResponse_sub_le D Xs hn a hBa ω))

/-- **The sampling noise of the structural coordinate in a direction `w`** is `Var_D⟨w,S⟩ / n`:
`E[⟨w, M̂_n − m⟩²] = Var_D⟨w,S⟩ / n`. -/
theorem integral_sq_dotJ_sampleResponse_sub (hind : ∀ i k, i ≠ k → IndepFun (Xs i) (Xs k) P)
    {n : ℕ} (hn : 0 < n) (w : J → ℝ) :
    ∫ ω, dotJ w (fun j ↦ sampleResponse S Xs n ω j - ∫ x, S j x ∂D) ^ 2 ∂P =
      lawCov D (dirLoss S w) (dirLoss S w) / n := by
  have hexp : ∀ ω, dotJ w (fun j ↦ sampleResponse S Xs n ω j - ∫ x, S j x ∂D) ^ 2 =
      ∑ a, ∑ b, w a * w b * ((sampleResponse S Xs n ω a - ∫ x, S a x ∂D) *
        (sampleResponse S Xs n ω b - ∫ x, S b x ∂D)) := fun ω ↦ by
    simp only [dotJ, sq, Finset.sum_mul_sum]
    refine Finset.sum_congr rfl fun a _ ↦ Finset.sum_congr rfl fun b _ ↦ ?_
    ring
  simp_rw [hexp]
  rw [integral_finsetSum _ fun a _ ↦ integrable_finsetSum _ fun b _ ↦
    (integrable_sampleResponse_sub_mul hS P D Xs hXm hn a b).const_mul _]
  simp_rw [integral_finsetSum _ fun b _ ↦
    (integrable_sampleResponse_sub_mul hS P D Xs hXm hn _ b).const_mul _,
    integral_const_mul, integral_sampleResponse_sub_mul_sub hS P D Xs hXm hid hlaw hind hn]
  rw [lawCov_dirLoss_left hS D w _ (bdd_dirLoss hS w), Finset.sum_div]
  refine Finset.sum_congr rfl fun a _ ↦ ?_
  rw [lawCov_comm, lawCov_dirLoss_left hS D w _ (hS a), Finset.mul_sum, Finset.sum_div]
  refine Finset.sum_congr rfl fun b _ ↦ ?_
  rw [lawCov_comm, lawCov_eq_integral_centred D (hS a) (hS b)]
  ring

end Noise

section Resolution

variable {X : Type*} [MeasurableSpace X] {J : Type*} [Fintype J]
  {S : J → X → ℝ} (hS : ∀ j, Bdd (S j)) (ν : Measure X) [IsProbabilityMeasure ν]
  {h : X → ℝ} (hh : Bdd h)
include hS hh

/-- **The truth shift of the structural coordinate in a direction `w`** is the covariance of
the visible contrast with the data direction: `⟨w, b_t⟩ = Cov_{ρ_t}(⟨w,S⟩, h)`. -/
theorem dotJ_dataCov_eq_lawCov_dir (t : ℝ) (w : J → ℝ) :
    dotJ w (dataCov S ν h t) = lawCov (ν.tilted fun x ↦ t * h x) (dirLoss S w) h := by
  have := isProbabilityMeasure_dataPath' ν hh t
  rw [dataCov_eq_lawCov ν, lawCov_dirLoss_left hS _ w h hh]
  rfl

/-- **Signal against data variance**: `⟨w, b_t⟩² ≤ Var_{ρ_t}⟨w,S⟩ · Var_{ρ_t} h`. -/
theorem sq_dotJ_dataCov_le (t : ℝ) (w : J → ℝ) :
    dotJ w (dataCov S ν h t) ^ 2 ≤
      lawCov (ν.tilted fun x ↦ t * h x) (dirLoss S w) (dirLoss S w) *
        lawCov (ν.tilted fun x ↦ t * h x) h h := by
  have := isProbabilityMeasure_dataPath' ν hh t
  rw [dotJ_dataCov_eq_lawCov_dir hS ν hh]
  exact lawCov_sq_le _ (bdd_dirLoss hS w) hh

variable {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P] (Xs : ℕ → Ω → X)
  (hXm : ∀ i, Measurable (Xs i)) (hid : ∀ i, IdentDistrib (Xs i) (Xs 0) P P)
  (hind : ∀ i k, i ≠ k → IndepFun (Xs i) (Xs k) P)
include hXm hid hind

/-- **The resolution floor**: with `n` samples from the data law `ρ_t`, the truth shift of the
structural coordinate in any direction `w` is bounded by the sampling noise in that direction
times `√(n Var_{ρ_t} h)`:
`⟨w, b_t⟩² ≤ n · E[⟨w, M̂_n − m⟩²] · Var_{ρ_t} h`. -/
theorem sq_signal_le_mul_noise (t : ℝ) (hlaw : P.map (Xs 0) = ν.tilted fun x ↦ t * h x)
    {n : ℕ} (hn : 0 < n) (w : J → ℝ) :
    dotJ w (dataCov S ν h t) ^ 2 ≤
      n * (∫ ω, dotJ w (fun j ↦ sampleResponse S Xs n ω j -
        ∫ x, S j x ∂(ν.tilted fun x ↦ t * h x)) ^ 2 ∂P) *
        lawCov (ν.tilted fun x ↦ t * h x) h h := by
  have := isProbabilityMeasure_dataPath' ν hh t
  rw [integral_sq_dotJ_sampleResponse_sub hS P _ Xs hXm hid hlaw hind hn w,
    mul_div_cancel₀ _ (by exact_mod_cast hn.ne')]
  exact sq_dotJ_dataCov_le hS ν hh t w

/-- **Unresolvable truth shifts**: if a shift `δ` of the truth moves the structural coordinate in
direction `w` by at least the sampling noise in that direction, then
`δ² · n · Var_{ρ_t} h ≥ 1`. Shifts below the data Fisher–Rao floor `1/√(n Var_{ρ_t} h)` are
invisible in every direction of the observables. -/
theorem resolution_floor (t : ℝ) (hlaw : P.map (Xs 0) = ν.tilted fun x ↦ t * h x) {n : ℕ}
    (hn : 0 < n) (w : J → ℝ) {δ : ℝ}
    (hnoise : 0 < ∫ ω, dotJ w (fun j ↦ sampleResponse S Xs n ω j -
      ∫ x, S j x ∂(ν.tilted fun x ↦ t * h x)) ^ 2 ∂P)
    (hdetect : ∫ ω, dotJ w (fun j ↦ sampleResponse S Xs n ω j -
      ∫ x, S j x ∂(ν.tilted fun x ↦ t * h x)) ^ 2 ∂P ≤ (dotJ w (dataCov S ν h t) * δ) ^ 2) :
    1 ≤ δ ^ 2 * (n * lawCov (ν.tilted fun x ↦ t * h x) h h) := by
  have hkey := sq_signal_le_mul_noise hS ν hh P Xs hXm hid hind t hlaw hn w
  obtain ⟨N, hNdef⟩ : ∃ N : ℝ, N = ∫ ω, dotJ w (fun j ↦ sampleResponse S Xs n ω j -
      ∫ x, S j x ∂(ν.tilted fun x ↦ t * h x)) ^ 2 ∂P := ⟨_, rfl⟩
  rw [← hNdef] at hnoise hdetect hkey
  rw [mul_pow] at hdetect
  have hV : 0 ≤ lawCov (ν.tilted fun x ↦ t * h x) h h := by
    have := isProbabilityMeasure_dataPath' ν hh t
    exact lawCov_self_nonneg _ hh
  have hδ : 0 ≤ δ ^ 2 := sq_nonneg δ
  -- `N ≤ s² δ²` and `s² ≤ n N V` give `N ≤ n N V δ²`, hence `1 ≤ n V δ²`
  have h1 : N ≤ N * (δ ^ 2 * (n * lawCov (ν.tilted fun x ↦ t * h x) h h)) := by
    calc N ≤ dotJ w (dataCov S ν h t) ^ 2 * δ ^ 2 := hdetect
      _ ≤ (n * N * lawCov (ν.tilted fun x ↦ t * h x) h h) * δ ^ 2 :=
          mul_le_mul_of_nonneg_right hkey hδ
      _ = N * (δ ^ 2 * (n * lawCov (ν.tilted fun x ↦ t * h x) h h)) := by ring
  have h2 := le_of_mul_le_mul_left (by linarith [h1] : N * 1 ≤ N * (δ ^ 2 *
    (n * lawCov (ν.tilted fun x ↦ t * h x) h h))) hnoise
  exact h2

end Resolution

end Laplace.Multi
