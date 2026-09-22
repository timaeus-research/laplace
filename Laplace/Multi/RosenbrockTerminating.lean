/-
Copyright (c) 2026 Timaeus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Timaeus
-/
import Laplace.Multi.TwoLoopEnergy

/-!
# Rosenbrock: the series terminates

E5 and E7 of the note observe that for the Rosenbrock potential in two dimensions the `y` integral
is Gaussian given `x`, so the exact LLC is `d/2 = 1` at every `t` and "the series terminates". The
seabed already has the exact moments (`Laplace.TwoD.Rosenbrock`) and the one-loop covariance being
exact (`oneLoopCov_rosenbrock`). This file checks the remaining Laplace formulas of the note against
the exact measure:

* `twoLoopEnergy_rosenbrock`: `θ = 12a/t³`, `δ = 4a/t³`, `q = 12a/t²`, so
  `(t/12)θ + (t/8)δ − q/8 = 0` and `twoLoopEnergy = ½ tr(HS) = 1/t = ⟨L⟩` at every `t`
  (`twoLoopEnergy_rosenbrock_exact`); `θ = 3δ`, so this is a non-separable check of the two-loop
  weights;
* `meanShift_rosenbrock`: eq:mean's `−½ S (tT:S) = (0, 1/t) = (⟨x⟩ − 1, ⟨y⟩ − 1)` exactly
  (`meanShift_rosenbrock_exact`);
* `gibbsCov_rosenbrock_probe`: for the probe `ψ = ½ vᵀBv + b⬝v`, `v = (x − 1, y − 1)`,
  `Cov[L, ψ] = covKFormula + 3B₁₁/t³`: eq:covK misses exactly the term
  `Cov[z²/2, ½B₁₁ z⁴] = 3B₁₁/t³` from the flat direction's `z²` in `y − 1 = u + 2z + z²`, and is
  exact for linear probes (`gibbsCov_rosenbrock_linear_probe`).

The loss times a quadratic probe has degree six in `z = x − 1`, so the harmonic moment vector is
extended to degree six (`harmonicMoment_vec7`) and the shear-polynomial evaluation to arbitrary
degree bounds (`gibbsExpectation_valley_poly'`).
-/

open Real MeasureTheory Matrix Laplace.TwoD

namespace Laplace.Multi

open Laplace.OneD (harmonicPotential)

/-! ### Shear polynomials of arbitrary degree -/

/-- `gibbsExpectation_valley_poly` for coefficient matrices of any shape. -/
theorem gibbsExpectation_valley_poly' (μ : ℝ) (g : ℝ → ℝ) (hg : Continuous g)
    {a t : ℝ} (ha : 0 < a) (ht : 0 < t) {n m : ℕ} (c : Fin n → Fin m → ℝ) :
    Laplace.TwoD.gibbsExpectation (valley μ g a) t
      (fun p => ∑ i, ∑ j, c i j * ((p.1 - μ) ^ (i : ℕ) * (p.2 - g p.1) ^ (j : ℕ))) =
      ∑ i, ∑ j, c i j * (harmonicMoment 1 t i * harmonicMoment a t j) := by
  have hint : ∀ (i : Fin n) (j : Fin m), Integrable (fun p : ℝ × ℝ =>
      c i j * ((p.1 - μ) ^ (i : ℕ) * (p.2 - g p.1) ^ (j : ℕ)) * exp (-(t * valley μ g a p))) := by
    intro i j
    have h := (integrable_valley_shearMonomial μ g hg ha ht i j).const_mul (c i j)
    exact h.congr (Filter.Eventually.of_forall fun p => by ring)
  have hnum : (∫ p, (∑ i, ∑ j, c i j * ((p.1 - μ) ^ (i : ℕ) * (p.2 - g p.1) ^ (j : ℕ))) *
      exp (-(t * valley μ g a p))) =
      ∑ i, ∑ j, c i j * ((∫ z, z ^ (i : ℕ) * exp (-(t * harmonicPotential 1 z))) *
        (∫ u, u ^ (j : ℕ) * exp (-(t * harmonicPotential a u)))) := by
    have hrw : (fun p : ℝ × ℝ =>
        (∑ i, ∑ j, c i j * ((p.1 - μ) ^ (i : ℕ) * (p.2 - g p.1) ^ (j : ℕ))) *
          exp (-(t * valley μ g a p))) =
        fun p => ∑ i, ∑ j, c i j * ((p.1 - μ) ^ (i : ℕ) * (p.2 - g p.1) ^ (j : ℕ)) *
          exp (-(t * valley μ g a p)) := by
      funext p; simp only [Finset.sum_mul]
    rw [hrw, integral_finsetSum _ (fun i _ => integrable_finsetSum _ (fun j _ => hint i j))]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [integral_finsetSum _ (fun j _ => hint i j)]
    refine Finset.sum_congr rfl fun j _ => ?_
    have hrw2 : (fun p : ℝ × ℝ => c i j * ((p.1 - μ) ^ (i : ℕ) * (p.2 - g p.1) ^ (j : ℕ)) *
        exp (-(t * valley μ g a p))) =
        fun p => c i j * ((p.1 - μ) ^ (i : ℕ) * (p.2 - g p.1) ^ (j : ℕ) *
          exp (-(t * valley μ g a p))) := by
      funext p; ring
    rw [hrw2, integral_const_mul, integral_valley_shearMonomial μ g hg a t]
  unfold Laplace.TwoD.gibbsExpectation
  rw [hnum, partitionFunction_valley μ g hg a t, Finset.sum_div]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Finset.sum_div]
  refine Finset.sum_congr rfl fun j _ => ?_
  unfold harmonicMoment Laplace.gibbsExpectation
  rw [mul_div_assoc, mul_div_mul_comm]

theorem harmonicMoment_five {lam t : ℝ} (hlam : 0 < lam) (ht : 0 < t) :
    harmonicMoment lam t 5 = 0 := by
  have h := Laplace.OneD.gibbsExpectation_harmonic_pow_odd hlam ht 2
  norm_num at h
  unfold harmonicMoment
  simpa using h

theorem harmonicMoment_six {lam t : ℝ} (hlam : 0 < lam) (ht : 0 < t) :
    harmonicMoment lam t 6 = 15 / (lam * t) ^ 3 := by
  have h := Laplace.OneD.gibbsExpectation_harmonic_pow_even hlam ht 3
  norm_num [Nat.doubleFactorial] at h
  unfold harmonicMoment
  simpa using h

/-- The harmonic moments up to degree six as a vector. -/
theorem harmonicMoment_vec7 {lam t : ℝ} (hlam : 0 < lam) (ht : 0 < t) :
    (fun i : Fin 7 => harmonicMoment lam t i) =
      ![1, 0, 1 / (lam * t), 0, 3 / (lam * t) ^ 2, 0, 15 / (lam * t) ^ 3] := by
  funext i
  fin_cases i
  · exact harmonicMoment_zero hlam ht
  · exact harmonicMoment_one hlam ht
  · exact harmonicMoment_two hlam ht
  · exact harmonicMoment_three hlam ht
  · exact harmonicMoment_four hlam ht
  · exact harmonicMoment_five hlam ht
  · exact harmonicMoment_six hlam ht

section Rosenbrock

variable {a t : ℝ}

/-- Evaluate a Rosenbrock expectation through a `7 × 5` coefficient matrix in the shear
coordinates (`z`-degree up to six). -/
theorem gibbsExpectation_rosenbrock_of_poly7 (ha : 0 < a) (ht : 0 < t)
    (c : Fin 7 → Fin 5 → ℝ) (φ : ℝ × ℝ → ℝ)
    (hφ : ∀ p : ℝ × ℝ,
      φ p = ∑ i, ∑ j, c i j * ((p.1 - 1) ^ (i : ℕ) * (p.2 - p.1 ^ 2) ^ (j : ℕ))) :
    Laplace.TwoD.gibbsExpectation (rosenbrock a) t φ =
      ∑ i, ∑ j, c i j * (![1, 0, 1 / (1 * t), 0, 3 / (1 * t) ^ 2, 0, 15 / (1 * t) ^ 3] i *
        ![1, 0, 1 / (a * t), 0, 3 / (a * t) ^ 2] j) := by
  have hφ' : φ = fun p => ∑ i, ∑ j, c i j * ((p.1 - 1) ^ (i : ℕ) * (p.2 - p.1 ^ 2) ^ (j : ℕ)) :=
    funext hφ
  rw [hφ', rosenbrock_eq_valley,
    gibbsExpectation_valley_poly' 1 (fun x => x ^ 2) (by fun_prop) ha ht c]
  have h1 := harmonicMoment_vec7 one_pos ht
  have ha' := harmonicMoment_vec ha ht
  simp only [funext_iff] at h1 ha'
  simp only [h1, ha']

/-! ### The two-loop energy is exact -/

theorem thetaDiagram_rosenbrock (ha : a ≠ 0) (ht : t ≠ 0) :
    thetaDiagram (rosenT a) ((1 / t) • rosenSigma a) = 12 * a / t ^ 3 := by
  rw [thetaDiagram, bubble_rosenbrock a t ha]
  simp [rosenSigma, Fin.sum_univ_two]
  field_simp
  ring

theorem dumbbell_rosenbrock (ha : a ≠ 0) (ht : t ≠ 0) :
    dumbbell (rosenT a) ((1 / t) • rosenSigma a) = 4 * a / t ^ 3 := by
  rw [dumbbell, contractT_rosenbrock a t ha]
  simp [rosenSigma, Matrix.mulVec, dotProduct, Fin.sum_univ_two]
  field_simp
  ring

theorem figureEight_rosenbrock (ha : a ≠ 0) (ht : t ≠ 0) :
    figureEight (rosenQ a) ((1 / t) • rosenSigma a) = 12 * a / t ^ 2 := by
  rw [figureEight, contractQ_rosenbrock a t]
  simp [rosenSigma, Fin.sum_univ_two]
  field_simp

theorem trace_HS_rosenbrock (ha : a ≠ 0) (ht : t ≠ 0) :
    (rosenHess a * ((1 / t) • rosenSigma a)).trace = 2 / t := by
  simp [rosenHess, rosenSigma, Matrix.trace, Fin.sum_univ_two]
  field_simp
  ring

/-- **The two-loop energy is exact for Rosenbrock**: the three diagrams cancel and
`twoLoopEnergy = ½ tr(HS) = 1/t` at every `t`. -/
theorem twoLoopEnergy_rosenbrock (ha : 0 < a) (ht : 0 < t) :
    twoLoopEnergy t (rosenHess a) (rosenT a) (rosenQ a) = 1 / t := by
  rw [twoLoopEnergy, rosenHess_smul_inv ha ht, thetaDiagram_rosenbrock ha.ne' ht.ne',
    dumbbell_rosenbrock ha.ne' ht.ne', figureEight_rosenbrock ha.ne' ht.ne',
    trace_HS_rosenbrock ha.ne' ht.ne']
  field_simp
  ring

/-- `twoLoopEnergy = ⟨L⟩` exactly for Rosenbrock (E5: the exact LLC is `1` at every `t`). -/
theorem twoLoopEnergy_rosenbrock_exact (ha : 0 < a) (ht : 0 < t) :
    twoLoopEnergy t (rosenHess a) (rosenT a) (rosenQ a) =
      Laplace.TwoD.gibbsExpectation (rosenbrock a) t (rosenbrock a) := by
  rw [twoLoopEnergy_rosenbrock ha ht, gibbsExpectation_rosenbrock_self ha ht]

/-! ### eq:mean is exact -/

theorem meanShift_rosenbrock (ha : 0 < a) (ht : 0 < t) :
    meanShift t (rosenHess a) (rosenT a) = ![0, 1 / t] := by
  rw [meanShift, rosenHess_smul_inv ha ht, contractT_rosenbrock a t ha.ne']
  ext i
  fin_cases i <;> simp [rosenSigma] <;> field_simp <;> ring

/-- **eq:mean is exact for Rosenbrock**: `−½ S (tT:S) = (⟨x⟩ − 1, ⟨y⟩ − 1) = (0, 1/t)`. -/
theorem meanShift_rosenbrock_exact (ha : 0 < a) (ht : 0 < t) :
    meanShift t (rosenHess a) (rosenT a) =
      ![Laplace.TwoD.gibbsExpectation (rosenbrock a) t (fun p => p.1) - 1,
        Laplace.TwoD.gibbsExpectation (rosenbrock a) t (fun p => p.2) - 1] := by
  rw [meanShift_rosenbrock ha ht, gibbsExpectation_rosenbrock_fst ha ht,
    gibbsExpectation_rosenbrock_snd ha ht]
  ext i
  fin_cases i <;> simp

/-! ### eq:covK misses exactly `3B₁₁/t³` -/

/-- The ambient quadratic probe `ψ(p) = ½ vᵀBv + b⬝v` with `v = (x − 1, y − 1)`. -/
noncomputable def rosenProbe (B : Matrix (Fin 2) (Fin 2) ℝ) (b : Fin 2 → ℝ) (p : ℝ × ℝ) : ℝ :=
  1 / 2 * (![p.1 - 1, p.2 - 1] ⬝ᵥ (B *ᵥ ![p.1 - 1, p.2 - 1])) + b ⬝ᵥ ![p.1 - 1, p.2 - 1]

/-- `(T:(SHS))` for Rosenbrock: `SHS = S/t`. -/
theorem contractT_rosenbrock_SHS (ha : a ≠ 0) (ht : t ≠ 0) :
    contractT (rosenT a) ((1 / t) • rosenSigma a * rosenHess a * ((1 / t) • rosenSigma a)) =
      ![4 * a / t ^ 2, -2 * a / t ^ 2] := by
  ext l
  fin_cases l <;> simp [contractT, rosenT, rosenSigma, rosenHess, Matrix.mul_apply,
    Fin.sum_univ_two] <;> field_simp <;> ring

/-- eq:covK's right-hand side for Rosenbrock. -/
theorem covKFormula_rosenbrock (ha : 0 < a) (ht : 0 < t) (B : Matrix (Fin 2) (Fin 2) ℝ)
    (b : Fin 2 → ℝ) :
    covKFormula t (rosenHess a) (rosenT a) B b =
      (a * B 0 0 + 2 * a * (B 0 1 + B 1 0) + (4 * a + 1) * B 1 1 + 2 * a * b 1) /
        (2 * a * t ^ 2) := by
  rw [covKFormula, rosenHess_smul_inv ha ht, contractT_rosenbrock a t ha.ne',
    contractT_rosenbrock_SHS ha.ne' ht.ne']
  simp only [Matrix.trace, Matrix.diag_apply, Matrix.mul_apply, Matrix.mulVec, dotProduct,
    Fin.sum_univ_two, rosenHess, rosenSigma, Matrix.smul_apply, smul_eq_mul, Matrix.of_apply,
    Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.empty_val',
    Matrix.cons_val_fin_one]
  field_simp
  ring

/-- **eq:covK for Rosenbrock misses exactly `3B₁₁/t³`**: `Cov[L, ψ] = covKFormula + 3B₁₁/t³`
for every quadratic probe `ψ = ½ vᵀBv + b⬝v`, at every `t`. -/
theorem gibbsCov_rosenbrock_probe (ha : 0 < a) (ht : 0 < t) (B : Matrix (Fin 2) (Fin 2) ℝ)
    (b : Fin 2 → ℝ) :
    Laplace.TwoD.gibbsCov (rosenbrock a) t (rosenbrock a) (rosenProbe B b) =
      covKFormula t (rosenHess a) (rosenT a) B b + 3 * B 1 1 / t ^ 3 := by
  rw [covKFormula_rosenbrock ha ht B b]
  unfold Laplace.TwoD.gibbsCov
  rw [gibbsExpectation_rosenbrock_self ha ht]
  have hψ := gibbsExpectation_rosenbrock_of_poly ha ht
    ![![0, b 1, B 1 1 / 2, 0, 0],
      ![b 0 + 2 * b 1, (B 0 1 + B 1 0 + 4 * B 1 1) / 2, 0, 0, 0],
      ![(B 0 0 + 2 * B 0 1 + 2 * B 1 0 + 4 * B 1 1 + 2 * b 1) / 2, B 1 1, 0, 0, 0],
      ![(B 0 1 + B 1 0 + 4 * B 1 1) / 2, 0, 0, 0, 0],
      ![B 1 1 / 2, 0, 0, 0, 0]] (rosenProbe B b) (fun p => by
      simp only [rosenProbe, Fin.sum_univ_five, Matrix.mulVec, dotProduct, Fin.sum_univ_two]
      simp
      ring)
  have hLψ := gibbsExpectation_rosenbrock_of_poly7 ha ht
    ![![0, 0, 0, a * b 1 / 2, B 1 1 * a / 4],
      ![0, 0, a * (b 0 + 2 * b 1) / 2, a * (B 0 1 + B 1 0 + 4 * B 1 1) / 4, 0],
      ![0, b 1 / 2, (B 0 0 * a + 2 * B 0 1 * a + 2 * B 1 0 * a + 4 * B 1 1 * a + B 1 1 +
        2 * a * b 1) / 4, B 1 1 * a / 2, 0],
      ![(b 0 + 2 * b 1) / 2, (B 0 1 + B 1 0 + 4 * B 1 1) / 4, a * (B 0 1 + B 1 0 + 4 * B 1 1) / 4,
        0, 0],
      ![(B 0 0 + 2 * B 0 1 + 2 * B 1 0 + 4 * B 1 1 + 2 * b 1) / 4, B 1 1 / 2, B 1 1 * a / 4, 0, 0],
      ![(B 0 1 + B 1 0 + 4 * B 1 1) / 4, 0, 0, 0, 0],
      ![B 1 1 / 4, 0, 0, 0, 0]] (fun p => rosenbrock a p * rosenProbe B b p) (fun p => by
      simp only [rosenProbe, rosenbrock, Fin.sum_univ_seven, Fin.sum_univ_five, Matrix.mulVec,
        dotProduct, Fin.sum_univ_two]
      simp
      ring)
  rw [hψ, hLψ]
  simp only [Fin.sum_univ_five, Fin.sum_univ_seven]
  simp
  field_simp
  ring

/-- **eq:covK is exact for linear probes on Rosenbrock**: `Cov[L, b⬝v] = b₁/t²`. -/
theorem gibbsCov_rosenbrock_linear_probe (ha : 0 < a) (ht : 0 < t) (b : Fin 2 → ℝ) :
    Laplace.TwoD.gibbsCov (rosenbrock a) t (rosenbrock a) (rosenProbe 0 b) =
      covKFormula t (rosenHess a) (rosenT a) 0 b := by
  rw [gibbsCov_rosenbrock_probe ha ht 0 b]
  simp

theorem covKFormula_rosenbrock_linear (ha : 0 < a) (ht : 0 < t) (b : Fin 2 → ℝ) :
    covKFormula t (rosenHess a) (rosenT a) 0 b = b 1 / t ^ 2 := by
  rw [covKFormula_rosenbrock ha ht 0 b]
  simp only [Matrix.zero_apply, mul_zero, add_zero, zero_add]
  field_simp

end Rosenbrock

end Laplace.Multi
