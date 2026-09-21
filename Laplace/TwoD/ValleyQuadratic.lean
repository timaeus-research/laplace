/-
Copyright (c) 2026 Timaeus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Timaeus
-/
import Laplace.TwoD.Rosenbrock
import Laplace.Multi.OneLoop

/-!
# Quadratic curved valleys: exact covariance and one-loop exactness

For the curved valley `L(x, y) = ((x − μ)² + a (y − g x)²) / 2` with a quadratic floor
`g x = b x² + c x + e` and slope `p = g'(μ) = 2bμ + c` at the minimiser `(μ, g μ)`:

* the exact Gibbs moments follow from the shear machinery of `Rosenbrock.lean`
  (`⟨x⟩ = μ`, `⟨y⟩ = g μ + b/t`, `Var x = 1/t`, `Cov(x,y) = p/t`, `Var y = p²/t + 2b²/t² + 1/(at)`,
  `⟨L⟩ = 1/t`);
* the Hessian at the minimiser is `H = !![1 + ap², −ap; −ap, a]`, and the whole Laplace error is the
  cubic coupling of the flat direction: `Cov = (tH)⁻¹ + (2b²/t²) e_y e_yᵀ`
  (`quadValleyCov_eq_laplace_add`);
* the one-loop formula of `OneLoop.lean` is exact: `Π = 2a²b² (p, −1)(p, −1)ᵀ` and
  `oneLoopCov t H T Q = Cov` (`oneLoopCov_quadValley`).

Rosenbrock is the case `μ = 1`, `b = 1`, `c = e = 0`.
-/

open Real MeasureTheory Matrix Laplace.Multi

namespace Laplace.TwoD

/-- The quadratic valley floor `g x = b x² + c x + e`. -/
noncomputable def quadFn (b c e : ℝ) : ℝ → ℝ := fun x => b * x ^ 2 + c * x + e

lemma continuous_quadFn (b c e : ℝ) : Continuous (quadFn b c e) := by
  unfold quadFn
  fun_prop

/-- The slope `g'(μ) = 2bμ + c` of the valley floor at the minimiser. -/
noncomputable def valleySlope (μ b c : ℝ) : ℝ := 2 * b * μ + c

lemma rosenbrock_eq_quadValley (a : ℝ) : rosenbrock a = valley 1 (quadFn 1 0 0) a := by
  rw [rosenbrock_eq_valley]
  congr 1
  funext x
  simp [quadFn]

/-! ### The LLC of every curved valley -/

section AnyFloor

variable {μ a t : ℝ} (g : ℝ → ℝ) (hg : Continuous g)
include hg

/-- Evaluate a valley expectation through a coefficient matrix in the shear coordinates. -/
lemma gibbsExpectation_valley_of_poly (ha : 0 < a) (ht : 0 < t) (cf : Fin 5 → Fin 5 → ℝ)
    (φ : ℝ × ℝ → ℝ)
    (hφ : ∀ q : ℝ × ℝ, φ q = ∑ i, ∑ j, cf i j * ((q.1 - μ) ^ (i : ℕ) * (q.2 - g q.1) ^ (j : ℕ))) :
    gibbsExpectation (valley μ g a) t φ =
      ∑ i, ∑ j, cf i j * (![1, 0, 1 / (1 * t), 0, 3 / (1 * t) ^ 2] i *
        ![1, 0, 1 / (a * t), 0, 3 / (a * t) ^ 2] j) := by
  have hφ' : φ = fun q => ∑ i, ∑ j, cf i j * ((q.1 - μ) ^ (i : ℕ) * (q.2 - g q.1) ^ (j : ℕ)) :=
    funext hφ
  rw [hφ', gibbsExpectation_valley_poly μ g hg ha ht cf]
  have h1 := harmonicMoment_vec one_pos ht
  have ha' := harmonicMoment_vec ha ht
  simp only [funext_iff] at h1 ha'
  simp only [h1, ha']

/-- `⟨L⟩ = 1/t` for every curved valley: `t⟨L⟩ = 1 = d/2` exactly. -/
theorem gibbsExpectation_valley_self (ha : 0 < a) (ht : 0 < t) :
    gibbsExpectation (valley μ g a) t (valley μ g a) = 1 / t := by
  rw [gibbsExpectation_valley_of_poly g hg ha ht
    ![![0, 0, a / 2, 0, 0], 0, ![1 / 2, 0, 0, 0, 0], 0, 0] _ (fun q => by
      simp only [Fin.sum_univ_five, valley]; simp; ring)]
  simp only [Fin.sum_univ_five]; simp
  field_simp
  ring

/-- `⟨L²⟩ = 2/t²` for every curved valley. -/
theorem gibbsExpectation_valley_self_sq (ha : 0 < a) (ht : 0 < t) :
    gibbsExpectation (valley μ g a) t (fun q => valley μ g a q ^ 2) = 2 / t ^ 2 := by
  rw [gibbsExpectation_valley_of_poly g hg ha ht
    ![![0, 0, 0, 0, a ^ 2 / 4], 0, ![0, 0, a / 2, 0, 0], 0, ![1 / 4, 0, 0, 0, 0]] _ (fun q => by
      simp only [Fin.sum_univ_five, valley]; simp; ring)]
  simp only [Fin.sum_univ_five]; simp
  field_simp
  ring

/-- `Var L = 1/t²` for every curved valley. -/
theorem gibbsCov_valley_self (ha : 0 < a) (ht : 0 < t) :
    gibbsCov (valley μ g a) t (valley μ g a) (valley μ g a) = 1 / t ^ 2 := by
  unfold gibbsCov
  have h := gibbsExpectation_valley_self_sq (μ := μ) g hg ha ht
  simp only [pow_two] at h
  rw [h, gibbsExpectation_valley_self (μ := μ) g hg ha ht]
  field_simp
  ring

end AnyFloor

section QuadValley

variable {μ b c e a t : ℝ}

/-! ### Exact moments -/

/-- Evaluate a quadratic-valley expectation through a coefficient matrix in the shear
coordinates `z = x − μ`, `u = y − g x`. -/
lemma gibbsExpectation_quadValley_of_poly (ha : 0 < a) (ht : 0 < t) (cf : Fin 5 → Fin 5 → ℝ)
    (φ : ℝ × ℝ → ℝ)
    (hφ : ∀ q : ℝ × ℝ, φ q =
      ∑ i, ∑ j, cf i j * ((q.1 - μ) ^ (i : ℕ) * (q.2 - quadFn b c e q.1) ^ (j : ℕ))) :
    gibbsExpectation (valley μ (quadFn b c e) a) t φ =
      ∑ i, ∑ j, cf i j * (![1, 0, 1 / (1 * t), 0, 3 / (1 * t) ^ 2] i *
        ![1, 0, 1 / (a * t), 0, 3 / (a * t) ^ 2] j) :=
  gibbsExpectation_valley_of_poly (quadFn b c e) (continuous_quadFn b c e) ha ht cf φ hφ

/-- `⟨x⟩ = μ`. -/
theorem gibbsExpectation_quadValley_fst (ha : 0 < a) (ht : 0 < t) :
    gibbsExpectation (valley μ (quadFn b c e) a) t (fun q => q.1) = μ := by
  rw [gibbsExpectation_quadValley_of_poly ha ht
    ![![μ, 0, 0, 0, 0], ![1, 0, 0, 0, 0], 0, 0, 0] _ (fun q => by
      simp only [Fin.sum_univ_five]; simp)]
  simp only [Fin.sum_univ_five]; simp

/-- `⟨x²⟩ = μ² + 1/t`. -/
theorem gibbsExpectation_quadValley_fst_sq (ha : 0 < a) (ht : 0 < t) :
    gibbsExpectation (valley μ (quadFn b c e) a) t (fun q => q.1 ^ 2) = μ ^ 2 + 1 / t := by
  rw [gibbsExpectation_quadValley_of_poly ha ht
    ![![μ ^ 2, 0, 0, 0, 0], ![2 * μ, 0, 0, 0, 0], ![1, 0, 0, 0, 0], 0, 0] _ (fun q => by
      simp only [Fin.sum_univ_five]; simp; ring)]
  simp only [Fin.sum_univ_five]; simp

/-- `⟨y⟩ = g(μ) + b/t`: the curvature of the floor shifts the mean of `y` off the minimiser. -/
theorem gibbsExpectation_quadValley_snd (ha : 0 < a) (ht : 0 < t) :
    gibbsExpectation (valley μ (quadFn b c e) a) t (fun q => q.2) = quadFn b c e μ + b / t := by
  rw [gibbsExpectation_quadValley_of_poly ha ht
    ![![quadFn b c e μ, 1, 0, 0, 0], ![valleySlope μ b c, 0, 0, 0, 0], ![b, 0, 0, 0, 0], 0, 0] _
    (fun q => by simp only [Fin.sum_univ_five, quadFn, valleySlope]; simp; ring)]
  simp only [Fin.sum_univ_five]; simp
  ring

/-- `⟨xy⟩ = μ g(μ) + (μb + p)/t`. -/
theorem gibbsExpectation_quadValley_fst_mul_snd (ha : 0 < a) (ht : 0 < t) :
    gibbsExpectation (valley μ (quadFn b c e) a) t (fun q => q.1 * q.2) =
      μ * quadFn b c e μ + (μ * b + valleySlope μ b c) / t := by
  rw [gibbsExpectation_quadValley_of_poly ha ht
    ![![μ * quadFn b c e μ, μ, 0, 0, 0], ![μ * valleySlope μ b c + quadFn b c e μ, 1, 0, 0, 0],
      ![μ * b + valleySlope μ b c, 0, 0, 0, 0], ![b, 0, 0, 0, 0], 0] _
    (fun q => by simp only [Fin.sum_univ_five, quadFn, valleySlope]; simp; ring)]
  simp only [Fin.sum_univ_five]; simp
  ring

/-- `⟨y²⟩ = g(μ)² + (p² + 2 g(μ) b)/t + 3b²/t² + 1/(at)`. -/
theorem gibbsExpectation_quadValley_snd_sq (ha : 0 < a) (ht : 0 < t) :
    gibbsExpectation (valley μ (quadFn b c e) a) t (fun q => q.2 ^ 2) =
      quadFn b c e μ ^ 2 + (valleySlope μ b c ^ 2 + 2 * quadFn b c e μ * b) / t
        + 3 * b ^ 2 / t ^ 2 + 1 / (a * t) := by
  rw [gibbsExpectation_quadValley_of_poly ha ht
    ![![quadFn b c e μ ^ 2, 2 * quadFn b c e μ, 1, 0, 0],
      ![2 * quadFn b c e μ * valleySlope μ b c, 2 * valleySlope μ b c, 0, 0, 0],
      ![valleySlope μ b c ^ 2 + 2 * quadFn b c e μ * b, 2 * b, 0, 0, 0],
      ![2 * valleySlope μ b c * b, 0, 0, 0, 0], ![b ^ 2, 0, 0, 0, 0]] _
    (fun q => by simp only [Fin.sum_univ_five, quadFn, valleySlope]; simp; ring)]
  simp only [Fin.sum_univ_five]; simp
  field_simp
  ring

/-- `⟨L⟩ = 1/t`: `t⟨L⟩ = 1 = d/2` exactly, for every quadratic valley. -/
theorem gibbsExpectation_quadValley_self (ha : 0 < a) (ht : 0 < t) :
    gibbsExpectation (valley μ (quadFn b c e) a) t (valley μ (quadFn b c e) a) = 1 / t :=
  gibbsExpectation_valley_self (quadFn b c e) (continuous_quadFn b c e) ha ht

/-- `Var x = 1/t`. -/
theorem gibbsCov_quadValley_fst_fst (ha : 0 < a) (ht : 0 < t) :
    gibbsCov (valley μ (quadFn b c e) a) t (fun q => q.1) (fun q => q.1) = 1 / t := by
  unfold gibbsCov
  have h := gibbsExpectation_quadValley_fst_sq (μ := μ) (b := b) (c := c) (e := e) ha ht
  simp only [pow_two] at h
  rw [h, gibbsExpectation_quadValley_fst ha ht]
  ring

/-- `Cov(x, y) = p/t`. -/
theorem gibbsCov_quadValley_fst_snd (ha : 0 < a) (ht : 0 < t) :
    gibbsCov (valley μ (quadFn b c e) a) t (fun q => q.1) (fun q => q.2) =
      valleySlope μ b c / t := by
  unfold gibbsCov
  rw [gibbsExpectation_quadValley_fst_mul_snd ha ht, gibbsExpectation_quadValley_fst ha ht,
    gibbsExpectation_quadValley_snd ha ht]
  ring

/-- `Var y = p²/t + 2b²/t² + 1/(at)`. -/
theorem gibbsCov_quadValley_snd_snd (ha : 0 < a) (ht : 0 < t) :
    gibbsCov (valley μ (quadFn b c e) a) t (fun q => q.2) (fun q => q.2) =
      valleySlope μ b c ^ 2 / t + 2 * b ^ 2 / t ^ 2 + 1 / (a * t) := by
  unfold gibbsCov
  have h := gibbsExpectation_quadValley_snd_sq (μ := μ) (b := b) (c := c) (e := e) ha ht
  simp only [pow_two] at h
  rw [h, gibbsExpectation_quadValley_snd ha ht]
  field_simp
  ring

/-! ### The Laplace comparison -/

/-- The Hessian of the quadratic valley at its minimiser `(μ, g μ)`. -/
noncomputable def quadValleyHess (μ b c a : ℝ) : Matrix (Fin 2) (Fin 2) ℝ :=
  !![1 + a * valleySlope μ b c ^ 2, -a * valleySlope μ b c; -a * valleySlope μ b c, a]

/-- `Σ = t (tH)⁻¹`. -/
noncomputable def quadValleySigma (μ b c a : ℝ) : Matrix (Fin 2) (Fin 2) ℝ :=
  !![1, valleySlope μ b c; valleySlope μ b c, valleySlope μ b c ^ 2 + 1 / a]

theorem quadValleyHess_rosenbrock (a : ℝ) : quadValleyHess 1 1 0 a = rosenHess a := by
  simp only [quadValleyHess, rosenHess, valleySlope]
  ext i j
  fin_cases i <;> fin_cases j <;> simp <;> ring

theorem quadValleyHess_smul_inv (ha : 0 < a) (ht : 0 < t) :
    (t • quadValleyHess μ b c a)⁻¹ = (1 / t) • quadValleySigma μ b c a := by
  apply Matrix.inv_eq_right_inv
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [quadValleyHess, quadValleySigma, Matrix.mul_apply, Fin.sum_univ_two] <;>
    field_simp <;> ring

/-- The exact Gibbs covariance matrix of `(x, y)`. -/
noncomputable def quadValleyCov (μ b c e a t : ℝ) : Matrix (Fin 2) (Fin 2) ℝ :=
  !![gibbsCov (valley μ (quadFn b c e) a) t (fun q => q.1) (fun q => q.1),
     gibbsCov (valley μ (quadFn b c e) a) t (fun q => q.1) (fun q => q.2);
     gibbsCov (valley μ (quadFn b c e) a) t (fun q => q.2) (fun q => q.1),
     gibbsCov (valley μ (quadFn b c e) a) t (fun q => q.2) (fun q => q.2)]

/-- **The Laplace error of a quadratic valley is the cubic coupling**:
`Cov = (tH)⁻¹ + (2b²/t²) e_y e_yᵀ`. -/
theorem quadValleyCov_eq_laplace_add (ha : 0 < a) (ht : 0 < t) :
    quadValleyCov μ b c e a t =
      (t • quadValleyHess μ b c a)⁻¹ + (2 * b ^ 2 / t ^ 2) • !![0, 0; 0, 1] := by
  rw [quadValleyHess_smul_inv ha ht]
  have hsymm : gibbsCov (valley μ (quadFn b c e) a) t (fun q => q.2) (fun q => q.1) =
      gibbsCov (valley μ (quadFn b c e) a) t (fun q => q.1) (fun q => q.2) := by
    unfold gibbsCov
    rw [mul_comm (gibbsExpectation _ _ _)]
    congr 2
    funext q
    ring
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [quadValleyCov, quadValleySigma, hsymm, gibbsCov_quadValley_fst_fst ha ht,
      gibbsCov_quadValley_fst_snd ha ht, gibbsCov_quadValley_snd_snd ha ht] <;>
    field_simp
  ring

/-- Along any direction `v`: `vᵀ Cov v = vᵀ (tH)⁻¹ v + (2b²/t²) v_y²`. -/
theorem quadValleyCov_quadForm (ha : 0 < a) (ht : 0 < t) (v : Fin 2 → ℝ) :
    v ⬝ᵥ quadValleyCov μ b c e a t *ᵥ v =
      v ⬝ᵥ (t • quadValleyHess μ b c a)⁻¹ *ᵥ v + 2 * b ^ 2 / t ^ 2 * v 1 ^ 2 := by
  rw [quadValleyCov_eq_laplace_add ha ht, Matrix.add_mulVec, dotProduct_add]
  congr 1
  simp [Matrix.mulVec, dotProduct, Fin.sum_univ_two]
  ring

/-! ### The one-loop formula is exact -/

/-- The cubic Taylor tensor at the minimiser: `T_zzz = 6abp`, `T_zzw = T_zwz = T_wzz = −2ab`. -/
noncomputable def quadValleyT (μ b c a : ℝ) : Fin 2 → Fin 2 → Fin 2 → ℝ :=
  ![![![6 * a * b * valleySlope μ b c, -2 * a * b], ![-2 * a * b, 0]],
    ![![-2 * a * b, 0], ![0, 0]]]

/-- The quartic Taylor tensor at the minimiser: `Q_zzzz = 12ab²`. -/
noncomputable def quadValleyQ (b a : ℝ) : Fin 2 → Fin 2 → Fin 2 → Fin 2 → ℝ :=
  fun i j k l => if i = 0 ∧ j = 0 ∧ k = 0 ∧ l = 0 then 12 * a * b ^ 2 else 0

/-- **Taylor identity** at `(μ, g μ)` certifying `quadValleyHess`, `quadValleyT`, `quadValleyQ`. -/
theorem quadValley_taylor (μ b c e a z w : ℝ) :
    valley μ (quadFn b c e) a (μ + z, quadFn b c e μ + w) =
      (1 / 2) * (![z, w] ⬝ᵥ (quadValleyHess μ b c a).mulVec ![z, w])
        + (1 / 6) * ∑ i, ∑ j, ∑ k,
            quadValleyT μ b c a i j k * ![z, w] i * ![z, w] j * ![z, w] k
        + (1 / 24) * ∑ i, ∑ j, ∑ k, ∑ l,
            quadValleyQ b a i j k l * ![z, w] i * ![z, w] j * ![z, w] k * ![z, w] l := by
  simp [valley, quadFn, quadValleyHess, quadValleyT, quadValleyQ, valleySlope, Matrix.mulVec,
    dotProduct, Fin.sum_univ_two]
  ring

theorem contractQ_quadValley :
    contractQ (quadValleyQ b a) ((1 / t) • quadValleySigma μ b c a) =
      (12 * a * b ^ 2 / t) • !![1, 0; 0, 0] := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [contractQ, quadValleyQ, quadValleySigma, Fin.sum_univ_two]
  ring

theorem contractT_quadValley (ha : a ≠ 0) :
    contractT (quadValleyT μ b c a) ((1 / t) • quadValleySigma μ b c a) =
      ![2 * a * b * valleySlope μ b c / t, -2 * a * b / t] := by
  ext l
  fin_cases l <;> simp [contractT, quadValleyT, quadValleySigma, Fin.sum_univ_two] <;> field_simp
  ring

theorem bubble_quadValley (ha : a ≠ 0) :
    bubble (quadValleyT μ b c a) ((1 / t) • quadValleySigma μ b c a) =
      (1 / t ^ 2) • !![4 * a ^ 2 * b ^ 2 * valleySlope μ b c ^ 2 + 8 * a * b ^ 2,
        -4 * a ^ 2 * b ^ 2 * valleySlope μ b c;
        -4 * a ^ 2 * b ^ 2 * valleySlope μ b c, 4 * a ^ 2 * b ^ 2] := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [bubble, quadValleyT, quadValleySigma, Fin.sum_univ_two] <;>
    field_simp <;> ring

theorem tadpoleLine_quadValley (ha : a ≠ 0) :
    tadpoleLine (quadValleyT μ b c a) ((1 / t) • quadValleySigma μ b c a) =
      (4 * a * b ^ 2 / t ^ 2) • !![1, 0; 0, 0] := by
  ext i j
  simp only [tadpoleLine, Matrix.of_apply, contractT_quadValley ha]
  fin_cases i <;> fin_cases j <;> simp [quadValleyT, quadValleySigma, Fin.sum_univ_two] <;>
    field_simp <;> ring

/-- `Π = 2a²b² (p, −1)(p, −1)ᵀ`. -/
theorem oneLoopPi_quadValley (ha : a ≠ 0) (ht : t ≠ 0) :
    oneLoopPi t (quadValleyT μ b c a) (quadValleyQ b a) ((1 / t) • quadValleySigma μ b c a) =
      (2 * a ^ 2 * b ^ 2) • !![valleySlope μ b c ^ 2, -valleySlope μ b c;
        -valleySlope μ b c, 1] := by
  rw [oneLoopPi, contractQ_quadValley, bubble_quadValley ha, tadpoleLine_quadValley ha]
  ext i j
  fin_cases i <;> fin_cases j <;> simp <;> field_simp <;> ring

/-- **The one-loop formula is exact for every quadratic valley**: `S + SΠS = Cov`. -/
theorem oneLoopCov_quadValley (ha : 0 < a) (ht : 0 < t) :
    oneLoopCov t (quadValleyHess μ b c a) (quadValleyT μ b c a) (quadValleyQ b a) =
      quadValleyCov μ b c e a t := by
  rw [quadValleyCov_eq_laplace_add ha ht, oneLoopCov, quadValleyHess_smul_inv ha ht,
    oneLoopPi_quadValley ha.ne' ht.ne']
  ext i j
  fin_cases i <;> fin_cases j <;> simp [quadValleySigma] <;> field_simp <;> ring

end QuadValley

end Laplace.TwoD
