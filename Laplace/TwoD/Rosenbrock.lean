/-
Copyright (c) 2026 Timaeus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniel Murfet
-/
import Laplace.TwoD.SemiDegenerate
import Laplace.OneD.Harmonic
import Laplace.OneD.IntegralRemainder

/-!
# Curved Gaussian valleys and the two-dimensional Rosenbrock potential

A *curved Gaussian valley* is the potential `L(x, y) = ((x - μ)² + a (y - g x)²) / 2` on `ℝ²`.
The triangular shear `(z, u) ↦ (μ + z, u + g (μ + z))` preserves Lebesgue measure and turns the
Boltzmann weight `exp (-t L)` into the product of two harmonic weights, so every Gibbs
expectation of a polynomial in the *shear coordinates* `z = x - μ`, `u = y - g x` is a product
of one-dimensional harmonic Gibbs expectations.

The Rosenbrock potential `L(x, y) = (a (y - x²)² + (1 - x)²) / 2` is the valley with `μ = 1`,
`g x = x²`. Its exact Gibbs moments (`Z = 2π/(t√a)`, `⟨x⟩ = 1`, `⟨y⟩ = 1 + 1/t`,
`Var x = 1/t`, `Cov(x, y) = 2/t`, `Var y = 4/t + 2/t² + 1/(ta)`, `⟨L⟩ = 1/t`,
`Var L = 1/t²`) are the reference values of experiments E5 and E7 of the note *Sanity on
Sampling*. The Laplace (inverse-Hessian) covariance `(tH)⁻¹` with `H = [[1+4a, -2a], [-2a, a]]`
misses exactly `2/t²` in the `y`-variance and nothing else.
-/

open Real MeasureTheory Set

namespace Laplace.TwoD

open Laplace.OneD (harmonicPotential)

/-! ### Curved valleys and the triangular shear -/

/-- The curved Gaussian valley `L(x, y) = ((x - μ)² + a (y - g x)²) / 2`. -/
noncomputable def valley (μ : ℝ) (g : ℝ → ℝ) (a : ℝ) : ℝ × ℝ → ℝ :=
  fun p => ((p.1 - μ) ^ 2 + a * (p.2 - g p.1) ^ 2) / 2

/-- The Rosenbrock potential `L(x, y) = (a (y - x²)² + (1 - x)²) / 2`, minimised at `(1, 1)`. -/
noncomputable def rosenbrock (a : ℝ) : ℝ × ℝ → ℝ :=
  fun p => (a * (p.2 - p.1 ^ 2) ^ 2 + (1 - p.1) ^ 2) / 2

lemma rosenbrock_eq_valley (a : ℝ) : rosenbrock a = valley 1 (fun x => x ^ 2) a := by
  funext p; simp only [rosenbrock, valley]; ring

/-- The triangular shear `(z, u) ↦ (μ + z, u + g (μ + z))` as a homeomorphism of the plane. -/
def valleyShearHomeo (μ : ℝ) (g : ℝ → ℝ) (hg : Continuous g) : ℝ × ℝ ≃ₜ ℝ × ℝ where
  toFun p := (μ + p.1, p.2 + g (μ + p.1))
  invFun q := (q.1 - μ, q.2 - g q.1)
  left_inv p := by ext <;> simp
  right_inv q := by ext <;> simp
  continuous_toFun := by fun_prop
  continuous_invFun := by fun_prop

/-- The triangular shear as a measurable equivalence. -/
def valleyShear (μ : ℝ) (g : ℝ → ℝ) (hg : Continuous g) : ℝ × ℝ ≃ᵐ ℝ × ℝ :=
  (valleyShearHomeo μ g hg).toMeasurableEquiv

@[simp] lemma valleyShear_apply (μ : ℝ) (g : ℝ → ℝ) (hg : Continuous g) (p : ℝ × ℝ) :
    valleyShear μ g hg p = (μ + p.1, p.2 + g (μ + p.1)) := rfl

/-- The shear preserves Lebesgue measure on the plane. -/
theorem valleyShear_measurePreserving (μ : ℝ) (g : ℝ → ℝ) (hg : Continuous g) :
    MeasurePreserving (valleyShear μ g hg) volume volume := by
  change MeasurePreserving (fun p : ℝ × ℝ => (μ + p.1, p.2 + g (μ + p.1)))
    (volume.prod volume) (volume.prod volume)
  refine MeasurePreserving.skew_product (g := fun z u => u + g (μ + z))
    (measurePreserving_add_left volume μ) ?_ ?_
  · exact (continuous_snd.add (hg.comp (continuous_const.add continuous_fst))).measurable
  · exact Filter.Eventually.of_forall fun z => map_add_right_eq_self volume _

lemma valley_shear (μ : ℝ) (g : ℝ → ℝ) (hg : Continuous g) (a : ℝ) (p : ℝ × ℝ) :
    valley μ g a (valleyShear μ g hg p) = (p.1 ^ 2 + a * p.2 ^ 2) / 2 := by
  simp only [valley, valleyShear_apply]; ring

/-- After the shear the Boltzmann factor is a product of two harmonic factors. -/
lemma exp_neg_t_valley_shear (μ : ℝ) (g : ℝ → ℝ) (hg : Continuous g) (a t : ℝ) (p : ℝ × ℝ) :
    exp (-(t * valley μ g a (valleyShear μ g hg p))) =
      exp (-(t * harmonicPotential 1 p.1)) * exp (-(t * harmonicPotential a p.2)) := by
  rw [valley_shear, ← Real.exp_add]
  congr 1
  simp only [harmonicPotential]; ring

/-- **Transport of integrals through the shear.** -/
theorem integral_valley_shear (μ : ℝ) (g : ℝ → ℝ) (hg : Continuous g) (a t : ℝ)
    (f : ℝ × ℝ → ℝ) :
    ∫ p, f p * exp (-(t * valley μ g a p)) =
      ∫ q, f (valleyShear μ g hg q) *
        (exp (-(t * harmonicPotential 1 q.1)) * exp (-(t * harmonicPotential a q.2))) := by
  rw [← (valleyShear_measurePreserving μ g hg).integral_comp'
    (fun p => f p * exp (-(t * valley μ g a p)))]
  congr 1
  funext q
  rw [exp_neg_t_valley_shear]

/-- **Transport of integrability through the shear.** -/
theorem integrable_valley_shear_iff (μ : ℝ) (g : ℝ → ℝ) (hg : Continuous g) (a t : ℝ)
    (f : ℝ × ℝ → ℝ) :
    Integrable (fun p => f p * exp (-(t * valley μ g a p))) ↔
      Integrable (fun q => f (valleyShear μ g hg q) *
        (exp (-(t * harmonicPotential 1 q.1)) * exp (-(t * harmonicPotential a q.2)))) := by
  rw [← (valleyShear_measurePreserving μ g hg).integrable_comp_emb
    (valleyShear μ g hg).measurableEmbedding]
  congr! 2 with q
  simp only [Function.comp]
  rw [exp_neg_t_valley_shear]

/-- **Partition function of a curved valley**: independent of the curve `g`. -/
theorem partitionFunction_valley (μ : ℝ) (g : ℝ → ℝ) (hg : Continuous g) (a t : ℝ) :
    partitionFunction (valley μ g a) t =
      Laplace.partitionFunction (harmonicPotential 1) t *
        Laplace.partitionFunction (harmonicPotential a) t := by
  unfold partitionFunction Laplace.partitionFunction
  have h := integral_valley_shear μ g hg a t (fun _ => 1)
  simp only [one_mul] at h
  rw [h]
  exact integral_prod_mul (fun z : ℝ => exp (-(t * harmonicPotential 1 z)))
    (fun u : ℝ => exp (-(t * harmonicPotential a u)))

theorem partitionFunction_valley_eq (μ : ℝ) (g : ℝ → ℝ) (hg : Continuous g) {a t : ℝ}
    (ha : 0 < a) (ht : 0 < t) :
    partitionFunction (valley μ g a) t = sqrt (2 * π / (1 * t)) * sqrt (2 * π / (a * t)) := by
  rw [partitionFunction_valley μ g hg, Laplace.OneD.partitionFunction_harmonic one_pos ht,
    Laplace.OneD.partitionFunction_harmonic ha ht]

theorem partitionFunction_valley_pos (μ : ℝ) (g : ℝ → ℝ) (hg : Continuous g) {a t : ℝ}
    (ha : 0 < a) (ht : 0 < t) : 0 < partitionFunction (valley μ g a) t := by
  rw [partitionFunction_valley_eq μ g hg ha ht]
  have h1 : 0 < 2 * π / (1 * t) := by positivity
  have h2 : 0 < 2 * π / (a * t) := by positivity
  exact mul_pos (Real.sqrt_pos.mpr h1) (Real.sqrt_pos.mpr h2)

/-! ### Shear monomials -/

/-- One-dimensional integrability of `z^i · exp(-t · λ z²/2)`. -/
lemma integrable_pow_mul_exp_harmonic {lam t : ℝ} (hlam : 0 < lam) (ht : 0 < t) (i : ℕ) :
    Integrable (fun z : ℝ => z ^ i * exp (-(t * harmonicPotential lam z))) := by
  have h := Laplace.OneD.integrable_pow_mul_exp_neg_mul_sq (c := lam * t / 2) (by positivity) i
  convert h using 3 with z
  simp only [harmonicPotential]; congr 1; ring

/-- The integral of a shear monomial factorises into one-dimensional harmonic integrals. -/
theorem integral_valley_shearMonomial (μ : ℝ) (g : ℝ → ℝ) (hg : Continuous g) (a t : ℝ)
    (i j : ℕ) :
    ∫ p, (p.1 - μ) ^ i * (p.2 - g p.1) ^ j * exp (-(t * valley μ g a p)) =
      (∫ z, z ^ i * exp (-(t * harmonicPotential 1 z))) *
        (∫ u, u ^ j * exp (-(t * harmonicPotential a u))) := by
  rw [integral_valley_shear μ g hg a t (fun p => (p.1 - μ) ^ i * (p.2 - g p.1) ^ j)]
  rw [← integral_prod_mul (fun z : ℝ => z ^ i * exp (-(t * harmonicPotential 1 z)))
    (fun u : ℝ => u ^ j * exp (-(t * harmonicPotential a u)))]
  congr 1
  funext q
  simp only [valleyShear_apply, add_sub_cancel_left, add_sub_cancel_right]
  ring

theorem integrable_valley_shearMonomial (μ : ℝ) (g : ℝ → ℝ) (hg : Continuous g) {a t : ℝ}
    (ha : 0 < a) (ht : 0 < t) (i j : ℕ) :
    Integrable (fun p : ℝ × ℝ => (p.1 - μ) ^ i * (p.2 - g p.1) ^ j *
      exp (-(t * valley μ g a p))) := by
  rw [integrable_valley_shear_iff μ g hg a t (fun p => (p.1 - μ) ^ i * (p.2 - g p.1) ^ j)]
  have h : Integrable (fun q : ℝ × ℝ => (q.1 ^ i * exp (-(t * harmonicPotential 1 q.1))) *
      (q.2 ^ j * exp (-(t * harmonicPotential a q.2)))) :=
    (integrable_pow_mul_exp_harmonic one_pos ht i).mul_prod
      (integrable_pow_mul_exp_harmonic ha ht j)
  refine h.congr (Filter.Eventually.of_forall fun q => ?_)
  simp only [valleyShear_apply, add_sub_cancel_left, add_sub_cancel_right]
  ring

/-- The one-dimensional harmonic Gibbs expectation of `z ^ i`. -/
noncomputable def harmonicMoment (lam t : ℝ) (i : ℕ) : ℝ :=
  Laplace.gibbsExpectation (harmonicPotential lam) t (fun z => z ^ i)

/-- Gibbs expectation of a shear monomial: a product of harmonic moments. -/
theorem gibbsExpectation_valley_shearMonomial (μ : ℝ) (g : ℝ → ℝ) (hg : Continuous g)
    (a t : ℝ) (i j : ℕ) :
    gibbsExpectation (valley μ g a) t (fun p => (p.1 - μ) ^ i * (p.2 - g p.1) ^ j) =
      harmonicMoment 1 t i * harmonicMoment a t j := by
  unfold gibbsExpectation harmonicMoment Laplace.gibbsExpectation
  rw [integral_valley_shearMonomial μ g hg a t i j, partitionFunction_valley μ g hg a t,
    mul_div_mul_comm]

/-- **Polynomials in the shear coordinates.** For coefficients `c i j` (degrees `< 5`),
`⟨∑ c i j z^i u^j⟩ = ∑ c i j ⟨z^i⟩_{harm 1} ⟨u^j⟩_{harm a}`. -/
theorem gibbsExpectation_valley_poly (μ : ℝ) (g : ℝ → ℝ) (hg : Continuous g)
    {a t : ℝ} (ha : 0 < a) (ht : 0 < t) (c : Fin 5 → Fin 5 → ℝ) :
    gibbsExpectation (valley μ g a) t
      (fun p => ∑ i, ∑ j, c i j * ((p.1 - μ) ^ (i : ℕ) * (p.2 - g p.1) ^ (j : ℕ))) =
      ∑ i, ∑ j, c i j * (harmonicMoment 1 t i * harmonicMoment a t j) := by
  have hint : ∀ i j : Fin 5, Integrable (fun p : ℝ × ℝ =>
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
  unfold gibbsExpectation
  rw [hnum, partitionFunction_valley μ g hg a t, Finset.sum_div]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Finset.sum_div]
  refine Finset.sum_congr rfl fun j _ => ?_
  unfold harmonicMoment Laplace.gibbsExpectation
  rw [mul_div_assoc, mul_div_mul_comm]

/-! ### Harmonic moments up to degree four -/

theorem harmonicMoment_zero {lam t : ℝ} (hlam : 0 < lam) (ht : 0 < t) :
    harmonicMoment lam t 0 = 1 := by
  have h := Laplace.OneD.gibbsExpectation_harmonic_pow_even hlam ht 0
  norm_num [Nat.doubleFactorial] at h
  unfold harmonicMoment
  simpa using h

theorem harmonicMoment_one {lam t : ℝ} (hlam : 0 < lam) (ht : 0 < t) :
    harmonicMoment lam t 1 = 0 := by
  have h := Laplace.OneD.gibbsExpectation_harmonic_pow_odd hlam ht 0
  norm_num at h
  unfold harmonicMoment
  simpa using h

theorem harmonicMoment_two {lam t : ℝ} (hlam : 0 < lam) (ht : 0 < t) :
    harmonicMoment lam t 2 = 1 / (lam * t) := by
  have h := Laplace.OneD.gibbsExpectation_harmonic_pow_even hlam ht 1
  norm_num [Nat.doubleFactorial] at h
  unfold harmonicMoment
  simpa using h

theorem harmonicMoment_three {lam t : ℝ} (hlam : 0 < lam) (ht : 0 < t) :
    harmonicMoment lam t 3 = 0 := by
  have h := Laplace.OneD.gibbsExpectation_harmonic_pow_odd hlam ht 1
  norm_num at h
  unfold harmonicMoment
  simpa using h

theorem harmonicMoment_four {lam t : ℝ} (hlam : 0 < lam) (ht : 0 < t) :
    harmonicMoment lam t 4 = 3 / (lam * t) ^ 2 := by
  have h := Laplace.OneD.gibbsExpectation_harmonic_pow_even hlam ht 2
  norm_num [Nat.doubleFactorial] at h
  unfold harmonicMoment
  simpa using h

/-- The harmonic moments up to degree four as a vector. -/
theorem harmonicMoment_vec {lam t : ℝ} (hlam : 0 < lam) (ht : 0 < t) :
    (fun i : Fin 5 => harmonicMoment lam t i) = ![1, 0, 1 / (lam * t), 0, 3 / (lam * t) ^ 2] := by
  funext i
  fin_cases i
  · exact harmonicMoment_zero hlam ht
  · exact harmonicMoment_one hlam ht
  · exact harmonicMoment_two hlam ht
  · exact harmonicMoment_three hlam ht
  · exact harmonicMoment_four hlam ht

/-! ### Rosenbrock: exact moments -/

section Rosenbrock

variable {a t : ℝ}

lemma continuous_sq : Continuous (fun x : ℝ => x ^ 2) := by fun_prop

/-- Rewrite a Rosenbrock expectation as a valley expectation. -/
lemma gibbsExpectation_rosenbrock_eq (φ : ℝ × ℝ → ℝ) :
    gibbsExpectation (rosenbrock a) t φ = gibbsExpectation (valley 1 (fun x => x ^ 2) a) t φ := by
  rw [rosenbrock_eq_valley]

/-- The Rosenbrock expectation of a polynomial in `z = x - 1`, `u = y - x²`. -/
theorem gibbsExpectation_rosenbrock_poly (ha : 0 < a) (ht : 0 < t) (c : Fin 5 → Fin 5 → ℝ) :
    gibbsExpectation (rosenbrock a) t
      (fun p => ∑ i, ∑ j, c i j * ((p.1 - 1) ^ (i : ℕ) * (p.2 - p.1 ^ 2) ^ (j : ℕ))) =
      ∑ i, ∑ j, c i j * (harmonicMoment 1 t i * harmonicMoment a t j) := by
  rw [gibbsExpectation_rosenbrock_eq]
  exact gibbsExpectation_valley_poly 1 (fun x => x ^ 2) continuous_sq ha ht c

theorem partitionFunction_rosenbrock (ha : 0 < a) (ht : 0 < t) :
    partitionFunction (rosenbrock a) t = 2 * π / (t * sqrt a) := by
  rw [rosenbrock_eq_valley, partitionFunction_valley_eq 1 _ continuous_sq ha ht, one_mul,
    ← Real.sqrt_mul (by positivity)]
  have hsq : 2 * π / t * (2 * π / (a * t)) = (2 * π / (t * sqrt a)) ^ 2 := by
    rw [div_pow, mul_pow t, Real.sq_sqrt ha.le]; field_simp
  rw [hsq, Real.sqrt_sq (by positivity)]

theorem partitionFunction_rosenbrock_pos (ha : 0 < a) (ht : 0 < t) :
    0 < partitionFunction (rosenbrock a) t := by
  rw [rosenbrock_eq_valley]; exact partitionFunction_valley_pos 1 _ continuous_sq ha ht

/-- Evaluate a Rosenbrock expectation through a coefficient matrix in the shear coordinates. -/
lemma gibbsExpectation_rosenbrock_of_poly (ha : 0 < a) (ht : 0 < t) (c : Fin 5 → Fin 5 → ℝ)
    (φ : ℝ × ℝ → ℝ)
    (hφ : ∀ p : ℝ × ℝ,
      φ p = ∑ i, ∑ j, c i j * ((p.1 - 1) ^ (i : ℕ) * (p.2 - p.1 ^ 2) ^ (j : ℕ))) :
    gibbsExpectation (rosenbrock a) t φ =
      ∑ i, ∑ j, c i j * (![1, 0, 1 / (1 * t), 0, 3 / (1 * t) ^ 2] i *
        ![1, 0, 1 / (a * t), 0, 3 / (a * t) ^ 2] j) := by
  have hφ' : φ = fun p => ∑ i, ∑ j, c i j * ((p.1 - 1) ^ (i : ℕ) * (p.2 - p.1 ^ 2) ^ (j : ℕ)) :=
    funext hφ
  rw [hφ', gibbsExpectation_rosenbrock_poly ha ht c]
  have h1 := harmonicMoment_vec one_pos ht
  have ha' := harmonicMoment_vec ha ht
  simp only [funext_iff] at h1 ha'
  simp only [h1, ha']

/-- `⟨x⟩ = 1`. -/
theorem gibbsExpectation_rosenbrock_fst (ha : 0 < a) (ht : 0 < t) :
    gibbsExpectation (rosenbrock a) t (fun p => p.1) = 1 := by
  rw [gibbsExpectation_rosenbrock_of_poly ha ht
    ![![1, 0, 0, 0, 0], ![1, 0, 0, 0, 0], 0, 0, 0] _ (fun p => by
      simp only [Fin.sum_univ_five]; simp)]
  simp only [Fin.sum_univ_five]; simp

/-- `⟨x²⟩ = 1 + 1/t`. -/
theorem gibbsExpectation_rosenbrock_fst_sq (ha : 0 < a) (ht : 0 < t) :
    gibbsExpectation (rosenbrock a) t (fun p => p.1 ^ 2) = 1 + 1 / t := by
  rw [gibbsExpectation_rosenbrock_of_poly ha ht
    ![![1, 0, 0, 0, 0], ![2, 0, 0, 0, 0], ![1, 0, 0, 0, 0], 0, 0] _ (fun p => by
      simp only [Fin.sum_univ_five]; simp; ring)]
  simp only [Fin.sum_univ_five]; simp

/-- `⟨y⟩ = 1 + 1/t`. -/
theorem gibbsExpectation_rosenbrock_snd (ha : 0 < a) (ht : 0 < t) :
    gibbsExpectation (rosenbrock a) t (fun p => p.2) = 1 + 1 / t := by
  rw [gibbsExpectation_rosenbrock_of_poly ha ht
    ![![1, 1, 0, 0, 0], ![2, 0, 0, 0, 0], ![1, 0, 0, 0, 0], 0, 0] _ (fun p => by
      simp only [Fin.sum_univ_five]; simp; ring)]
  simp only [Fin.sum_univ_five]; simp

/-- `⟨x y⟩ = 1 + 3/t`. -/
theorem gibbsExpectation_rosenbrock_fst_mul_snd (ha : 0 < a) (ht : 0 < t) :
    gibbsExpectation (rosenbrock a) t (fun p => p.1 * p.2) = 1 + 3 / t := by
  rw [gibbsExpectation_rosenbrock_of_poly ha ht
    ![![1, 1, 0, 0, 0], ![3, 1, 0, 0, 0], ![3, 0, 0, 0, 0], ![1, 0, 0, 0, 0], 0] _ (fun p => by
      simp only [Fin.sum_univ_five]; simp; ring)]
  simp only [Fin.sum_univ_five]; simp; ring

/-- `⟨y²⟩ = 1 + 6/t + 3/t² + 1/(t a)`. -/
theorem gibbsExpectation_rosenbrock_snd_sq (ha : 0 < a) (ht : 0 < t) :
    gibbsExpectation (rosenbrock a) t (fun p => p.2 ^ 2) =
      1 + 6 / t + 3 / t ^ 2 + 1 / (t * a) := by
  rw [gibbsExpectation_rosenbrock_of_poly ha ht
    ![![1, 2, 1, 0, 0], ![4, 4, 0, 0, 0], ![6, 2, 0, 0, 0], ![4, 0, 0, 0, 0], ![1, 0, 0, 0, 0]] _
    (fun p => by simp only [Fin.sum_univ_five]; simp; ring)]
  simp only [Fin.sum_univ_five]; simp
  field_simp; ring

/-- `⟨L⟩ = 1/t`: the Rosenbrock LLC `t⟨K⟩ = 1 = d/2` is exact at every temperature. -/
theorem gibbsExpectation_rosenbrock_self (ha : 0 < a) (ht : 0 < t) :
    gibbsExpectation (rosenbrock a) t (rosenbrock a) = 1 / t := by
  rw [gibbsExpectation_rosenbrock_of_poly ha ht
    ![![0, 0, a / 2, 0, 0], 0, ![1 / 2, 0, 0, 0, 0], 0, 0] _ (fun p => by
      simp only [Fin.sum_univ_five, rosenbrock]; simp; ring)]
  simp only [Fin.sum_univ_five]; simp
  field_simp; ring

/-- `⟨L²⟩ = 2/t²`. -/
theorem gibbsExpectation_rosenbrock_self_sq (ha : 0 < a) (ht : 0 < t) :
    gibbsExpectation (rosenbrock a) t (fun p => rosenbrock a p ^ 2) = 2 / t ^ 2 := by
  rw [gibbsExpectation_rosenbrock_of_poly ha ht
    ![![0, 0, 0, 0, a ^ 2 / 4], 0, ![0, 0, a / 2, 0, 0], 0, ![1 / 4, 0, 0, 0, 0]] _ (fun p => by
      simp only [Fin.sum_univ_five, rosenbrock]; simp; ring)]
  simp only [Fin.sum_univ_five]; simp
  field_simp; ring

/-- `Var x = 1/t`. -/
theorem gibbsCov_rosenbrock_fst_fst (ha : 0 < a) (ht : 0 < t) :
    gibbsCov (rosenbrock a) t (fun p => p.1) (fun p => p.1) = 1 / t := by
  unfold gibbsCov
  have h := gibbsExpectation_rosenbrock_fst_sq ha ht
  simp only [pow_two] at h
  rw [h, gibbsExpectation_rosenbrock_fst ha ht]; ring

/-- `Cov(x, y) = 2/t`. -/
theorem gibbsCov_rosenbrock_fst_snd (ha : 0 < a) (ht : 0 < t) :
    gibbsCov (rosenbrock a) t (fun p => p.1) (fun p => p.2) = 2 / t := by
  unfold gibbsCov
  rw [gibbsExpectation_rosenbrock_fst_mul_snd ha ht, gibbsExpectation_rosenbrock_fst ha ht,
    gibbsExpectation_rosenbrock_snd ha ht]; ring

/-- `Var y = 4/t + 2/t² + 1/(t a)`. -/
theorem gibbsCov_rosenbrock_snd_snd (ha : 0 < a) (ht : 0 < t) :
    gibbsCov (rosenbrock a) t (fun p => p.2) (fun p => p.2) = 4 / t + 2 / t ^ 2 + 1 / (t * a) := by
  unfold gibbsCov
  have h := gibbsExpectation_rosenbrock_snd_sq ha ht
  simp only [pow_two] at h
  rw [h, gibbsExpectation_rosenbrock_snd ha ht]
  field_simp
  ring

/-- `Var L = 1/t²`. -/
theorem gibbsCov_rosenbrock_self (ha : 0 < a) (ht : 0 < t) :
    gibbsCov (rosenbrock a) t (rosenbrock a) (rosenbrock a) = 1 / t ^ 2 := by
  unfold gibbsCov
  have h := gibbsExpectation_rosenbrock_self_sq ha ht
  simp only [pow_two] at h
  rw [h, gibbsExpectation_rosenbrock_self ha ht]
  field_simp
  ring

/-! ### The Laplace comparison -/

/-- The Hessian of the Rosenbrock potential at its minimiser `(1, 1)`. -/
noncomputable def rosenHess (a : ℝ) : Matrix (Fin 2) (Fin 2) ℝ := !![1 + 4 * a, -2 * a; -2 * a, a]

/-- **Taylor identity** certifying `rosenHess` as the Hessian at `(1, 1)`: the potential is the
quadratic form `½ vᵀ H v` plus a cubic and a quartic remainder. -/
theorem rosenbrock_taylor (a z w : ℝ) :
    rosenbrock a (1 + z, 1 + w) =
      (1 / 2) * (![z, w] ⬝ᵥ (rosenHess a).mulVec ![z, w]) - a * (w - 2 * z) * z ^ 2
        + a * z ^ 4 / 2 := by
  simp only [rosenbrock, rosenHess, Matrix.mulVec, dotProduct, Fin.sum_univ_two,
    Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.empty_val', Matrix.cons_val_fin_one]
  ring

/-- The inverse Hessian `H⁻¹ = [[1, 2], [2, 4 + 1/a]]`. -/
theorem rosenHess_inv (ha : 0 < a) : (rosenHess a)⁻¹ = !![1, 2; 2, 4 + 1 / a] := by
  apply Matrix.inv_eq_right_inv
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [rosenHess, Matrix.mul_apply, Fin.sum_univ_two] <;> field_simp <;> ring

/-- The exact Gibbs covariance matrix of `(x, y)`. -/
noncomputable def rosenCov (a t : ℝ) : Matrix (Fin 2) (Fin 2) ℝ :=
  !![gibbsCov (rosenbrock a) t (fun p => p.1) (fun p => p.1),
     gibbsCov (rosenbrock a) t (fun p => p.1) (fun p => p.2);
     gibbsCov (rosenbrock a) t (fun p => p.1) (fun p => p.2),
     gibbsCov (rosenbrock a) t (fun p => p.2) (fun p => p.2)]

/-- **Exact covariance versus Laplace.** `Cov = (tH)⁻¹ + (2/t²) e_y e_yᵀ`. -/
theorem rosenCov_eq_laplace_add (ha : 0 < a) (ht : 0 < t) :
    rosenCov a t = (t • rosenHess a)⁻¹ + (2 / t ^ 2) • !![0, 0; 0, 1] := by
  have hinv : (t • rosenHess a)⁻¹ = (1 / t) • !![1, 2; 2, 4 + 1 / a] := by
    apply Matrix.inv_eq_right_inv
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [rosenHess, Matrix.mul_apply, Fin.sum_univ_two] <;> field_simp <;> ring
  rw [hinv]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [rosenCov, gibbsCov_rosenbrock_fst_fst ha ht, gibbsCov_rosenbrock_fst_snd ha ht,
      gibbsCov_rosenbrock_snd_snd ha ht]
  all_goals field_simp
  all_goals ring

end Rosenbrock

end Laplace.TwoD
