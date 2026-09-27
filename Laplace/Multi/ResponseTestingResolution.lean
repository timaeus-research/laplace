/-
Copyright (c) 2026 Timaeus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Timaeus
-/
import Laplace.Multi.ResponseIntrinsicDistance
import Laplace.Multi.SharpAffinityTesting
import Laplace.Multi.ReconstructionDerivative

/-!
# The testing lower bound: nearby responses cannot be resolved from few samples

The converse of the probabilistic resolution theorem. Two model laws `P_{θ₀}, P_{θ₁}` at intrinsic
Fisher distance `d = d_F(θ₀,θ₁) ≤ π` have affinity at least `cos(d/2)`
(`cos_half_fisherDist_le_affinity`, from `sphericalDist_le_fisherDist`), and every equal-prior test
on `n` i.i.d. samples has average error at least

`(1 − √(1 − cos^{2n}(d/2))) / 2`   (`testing_error_model_ge_of_fisherDist`),

in particular at least `1/2 − √n d/4` (`testing_error_model_ge_half_sub`): fixed-confidence
discrimination of two responses requires `n d² ≳ 1`. Together with `measureReal_sign_certified_ge`
this is the two-sided resolution story: a certified margin resolves a chamber crossing with
probability `≥ 1 − τ/(nr²)`, and no test resolves two model laws whose intrinsic separation is
below the sampling scale `1/√n`.

Cautions: the bound is for the equal-prior average error; for `d > π` the useful statement is the
trivial one (use `cos(min(d,π)/2)`); the two sides are complementary, not a matched minimax
theorem.
-/

open MeasureTheory Filter Topology Set

namespace Laplace.Multi

/-- The Bernoulli-type estimate `cos^{2n}(x) ≥ 1 − n x²`. -/
theorem one_sub_mul_sq_le_cos_pow (n : ℕ) {x : ℝ} (hx : 0 ≤ x) :
    1 - n * x ^ 2 ≤ (Real.cos x ^ n) ^ 2 := by
  have hs : Real.sin x ^ 2 ≤ x ^ 2 := by
    have h1 := Real.sin_le hx
    have h2 : -x ≤ Real.sin x := by
      by_cases hx1 : 1 ≤ x
      · linarith [Real.neg_one_le_sin x]
      · have := Real.sin_nonneg_of_nonneg_of_le_pi hx (by linarith [Real.pi_gt_three])
        linarith
    exact sq_le_sq' h2 h1
  have hcos : Real.cos x ^ 2 = 1 - Real.sin x ^ 2 := by linarith [Real.sin_sq_add_cos_sq x]
  have hbern : 1 + (n : ℝ) * (-(Real.sin x ^ 2)) ≤ (1 + -(Real.sin x ^ 2)) ^ n :=
    one_add_mul_le_pow (by nlinarith [Real.sin_sq_le_one x]) n
  calc 1 - n * x ^ 2 ≤ 1 + (n : ℝ) * (-(Real.sin x ^ 2)) := by nlinarith
    _ ≤ (1 + -(Real.sin x ^ 2)) ^ n := hbern
    _ = (Real.cos x ^ n) ^ 2 := by rw [← pow_mul, mul_comm, pow_mul, hcos]; ring_nf

section Testing

variable {X : Type*} [MeasurableSpace X] {J : Type*} [Fintype J]
  {S : J → X → ℝ} (hS : ∀ j, Bdd (S j)) (ν : Measure X) [IsProbabilityMeasure ν]
include hS

/-- The reconstructed family. -/
local notation "Pfam" => familyMeasure ν (fun _ ↦ (1 : ℝ)) (fun _ ↦ (0 : ℝ)) S 1

/-- The direction space. -/
local notation "𝕍" => dirSpan ν (fun _ ↦ (1 : ℝ)) S

/-- The law with square-root density `√p_θ` is the model law. -/
theorem rootLaw_rootDensL2 (θ : J → ℝ) : rootLaw ν (rootDensL2 hS ν θ) = Pfam θ := by
  rw [familyMeasure_eq_withDensity_famDens ν θ, rootLaw]
  refine withDensity_congr_ae ?_
  filter_upwards [(memLp_rootDens hS ν θ).coeFn_toLp] with x hx
  simp only [rootDensL2]
  rw [hx, ← sq, rootDens_sq hS ν]

/-- The `n`-fold product of the model law as a root law. -/
theorem pi_familyMeasure_eq_rootLaw (n : ℕ) (θ : J → ℝ) :
    (Measure.pi fun _ : Fin n ↦ Pfam θ) =
      rootLaw (Measure.pi fun _ : Fin n ↦ ν) (prodRoot ν n (rootDensL2 hS ν θ)) := by
  rw [rootLaw_prodRoot, rootLaw_rootDensL2 hS ν]

/-- **Every equal-prior test of two model laws on `n` samples has error at least
`(1 − √(1 − A^{2n}))/2`**, `A` the affinity. -/
theorem testing_error_model_ge (n : ℕ) (θ₀ θ₁ : J → ℝ) {φ : (Fin n → X) → ℝ}
    (hφm : Measurable φ) (hφ0 : ∀ z, 0 ≤ φ z) (hφ1 : ∀ z, φ z ≤ 1) :
    (1 - √(1 - (affinity S ν θ₀ θ₁ ^ n) ^ 2)) / 2 ≤
      ((∫ z, φ z ∂(Measure.pi fun _ : Fin n ↦ Pfam θ₀)) +
        ∫ z, (1 - φ z) ∂(Measure.pi fun _ : Fin n ↦ Pfam θ₁)) / 2 := by
  rw [pi_familyMeasure_eq_rootLaw hS ν, pi_familyMeasure_eq_rootLaw hS ν]
  have h := testing_error_ge_sqrt (Measure.pi fun _ : Fin n ↦ ν)
    (norm_prodRoot ν n (norm_rootDensL2 hS ν θ₀)) (norm_prodRoot ν n (norm_rootDensL2 hS ν θ₁))
    hφm hφ0 hφ1
  have e : ∫ z, prodRoot ν n (rootDensL2 hS ν θ₀) z * prodRoot ν n (rootDensL2 hS ν θ₁) z
      ∂(Measure.pi fun _ : Fin n ↦ ν) = affinity S ν θ₀ θ₁ ^ n := by
    rw [← inner_eq_integral_mul, inner_prodRoot, ← inner_eq_integral_mul, inner_rootDensL2 hS ν]
  rwa [e] at h

/-- **The affinity of two model laws is at least `cos(d_F/2)`** when `d_F ≤ π`. -/
theorem cos_half_fisherDist_le_affinity [Nonempty X] (θ₀ θ₁ : 𝕍)
    (hd : fisherDist S ν θ₀ θ₁ ≤ Real.pi) :
    Real.cos (fisherDist S ν θ₀ θ₁ / 2) ≤ affinity S ν (θ₀ : J → ℝ) (θ₁ : J → ℝ) := by
  have h : 2 * Real.arccos (affinity S ν (θ₀ : J → ℝ) (θ₁ : J → ℝ)) ≤ fisherDist S ν θ₀ θ₁ :=
    sphericalDist_le_fisherDist hS ν θ₀ θ₁
  have hA0 := affinity_nonneg S ν (θ₀ : J → ℝ) (θ₁ : J → ℝ)
  have hA1 := affinity_le_one hS ν (θ₀ : J → ℝ) (θ₁ : J → ℝ)
  have hd0 : 0 ≤ fisherDist S ν θ₀ θ₁ := fisherDist_nonneg
  have harc : Real.arccos (affinity S ν (θ₀ : J → ℝ) (θ₁ : J → ℝ)) ≤ fisherDist S ν θ₀ θ₁ / 2 := by
    linarith
  calc Real.cos (fisherDist S ν θ₀ θ₁ / 2)
      ≤ Real.cos (Real.arccos (affinity S ν (θ₀ : J → ℝ) (θ₁ : J → ℝ))) :=
        Real.cos_le_cos_of_nonneg_of_le_pi (Real.arccos_nonneg _) (by linarith) harc
    _ = affinity S ν (θ₀ : J → ℝ) (θ₁ : J → ℝ) := Real.cos_arccos (by linarith) hA1

/-- **The testing lower bound in terms of the intrinsic distance**: for `d_F(θ₀,θ₁) ≤ π`, every
equal-prior test on `n` samples has error at least `(1 − √(1 − cos^{2n}(d_F/2)))/2`. -/
theorem testing_error_model_ge_of_fisherDist [Nonempty X] (n : ℕ) (θ₀ θ₁ : 𝕍)
    (hd : fisherDist S ν θ₀ θ₁ ≤ Real.pi) {φ : (Fin n → X) → ℝ}
    (hφm : Measurable φ) (hφ0 : ∀ z, 0 ≤ φ z) (hφ1 : ∀ z, φ z ≤ 1) :
    (1 - √(1 - (Real.cos (fisherDist S ν θ₀ θ₁ / 2) ^ n) ^ 2)) / 2 ≤
      ((∫ z, φ z ∂(Measure.pi fun _ : Fin n ↦ Pfam (θ₀ : J → ℝ))) +
        ∫ z, (1 - φ z) ∂(Measure.pi fun _ : Fin n ↦ Pfam (θ₁ : J → ℝ))) / 2 := by
  refine le_trans ?_ (testing_error_model_ge hS ν n _ _ hφm hφ0 hφ1)
  have hc := cos_half_fisherDist_le_affinity hS ν θ₀ θ₁ hd
  have hd0 : 0 ≤ fisherDist S ν θ₀ θ₁ := fisherDist_nonneg
  have hc0 : 0 ≤ Real.cos (fisherDist S ν θ₀ θ₁ / 2) :=
    Real.cos_nonneg_of_neg_pi_div_two_le_of_le (by linarith [Real.pi_pos]) (by linarith)
  have hpow : Real.cos (fisherDist S ν θ₀ θ₁ / 2) ^ n ≤
      affinity S ν (θ₀ : J → ℝ) (θ₁ : J → ℝ) ^ n :=
    pow_le_pow_left₀ hc0 hc n
  have hpow2 : (Real.cos (fisherDist S ν θ₀ θ₁ / 2) ^ n) ^ 2 ≤
      (affinity S ν (θ₀ : J → ℝ) (θ₁ : J → ℝ) ^ n) ^ 2 :=
    pow_le_pow_left₀ (pow_nonneg hc0 n) hpow 2
  have hsq := Real.sqrt_le_sqrt (sub_le_sub_left hpow2 1)
  linarith

/-- **The resolution scale**: for `d_F ≤ π`, every equal-prior test on `n` samples has error at
least `1/2 − √n d_F/4`. -/
theorem testing_error_model_ge_half_sub [Nonempty X] (n : ℕ) (θ₀ θ₁ : 𝕍)
    (hd : fisherDist S ν θ₀ θ₁ ≤ Real.pi) {φ : (Fin n → X) → ℝ}
    (hφm : Measurable φ) (hφ0 : ∀ z, 0 ≤ φ z) (hφ1 : ∀ z, φ z ≤ 1) :
    1 / 2 - Real.sqrt n * fisherDist S ν θ₀ θ₁ / 4 ≤
      ((∫ z, φ z ∂(Measure.pi fun _ : Fin n ↦ Pfam (θ₀ : J → ℝ))) +
        ∫ z, (1 - φ z) ∂(Measure.pi fun _ : Fin n ↦ Pfam (θ₁ : J → ℝ))) / 2 := by
  refine le_trans ?_ (testing_error_model_ge_of_fisherDist hS ν n θ₀ θ₁ hd hφm hφ0 hφ1)
  set d := fisherDist S ν θ₀ θ₁ with hdd
  have hd0 : 0 ≤ d := fisherDist_nonneg
  have h1 := one_sub_mul_sq_le_cos_pow n (x := d / 2) (by linarith)
  have h2 : 1 - (Real.cos (d / 2) ^ n) ^ 2 ≤ n * (d / 2) ^ 2 := by linarith
  have h3 : Real.sqrt (1 - (Real.cos (d / 2) ^ n) ^ 2) ≤ Real.sqrt (n * (d / 2) ^ 2) :=
    Real.sqrt_le_sqrt h2
  have h4 : Real.sqrt ((n : ℝ) * (d / 2) ^ 2) = Real.sqrt n * (d / 2) := by
    rw [Real.sqrt_mul (Nat.cast_nonneg n), Real.sqrt_sq (by positivity)]
  rw [h4] at h3
  linarith

end Testing

end Laplace.Multi
