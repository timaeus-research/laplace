/-
Copyright (c) 2026 Timaeus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniel Murfet
-/
import Mathlib

/-!
# The degenerate 4-gon of the toy model of superposition

The algebra of Proposition 11.1 (ii)–(iv) of the working note *Patterning flow*, in the
population model with single-feature inputs: five columns `W : Fin 5 → Fin 2 → ℝ`, per-feature
losses `ℓ_i(W) = ⅓[(1 - |W_i|²)² + ∑_{j≠i} [W_j·W_i]_+²]`, weighted loss `L_h = ∑ h_i ℓ_i`,
and the 4-gon `W_0 = (1,0), W_1 = (0,1), W_2 = (-1,0), W_3 = (0,-1), W_4 = 0`.

* `weightedLoss_fourGon`: the exact loss with the dead unit at `(x, y)` and the alive units
  frozen, for every `h` (Cartesian form of eq. *(stability)*);
* `weightedLoss_fourGon_uniform`: at uniform `h` it is `r⁴/15` with `r² = x² + y²`
  (part (ii): the `r²` terms cancel);
* `weightedLoss_fourGon_ray`: along the ray `r(cos θ, sin θ)`, `r ≥ 0`, it is
  `a(θ;h) r² + (h_4/3) r⁴` with the stability coefficient `a(θ;h)` (part (iv));
* `volume_sublevel_quartic`: the sublevel volume of `r⁴/15` on `ℝ²` is `π √(15 ε)`, the
  `ε^{1/2}` behind `λ_{C₄} = ½` (part (iii)).

The stationarity claim (i) and the Gibbs moments of (iii) are not formalised here.
-/

namespace Laplace.Patterning

open Finset Real MeasureTheory

/-- `[z]_+ = max z 0`. -/
def relu (z : ℝ) : ℝ := max z 0

lemma relu_of_nonneg {z : ℝ} (h : 0 ≤ z) : relu z = z := max_eq_left h

lemma relu_of_nonpos {z : ℝ} (h : z ≤ 0) : relu z = 0 := max_eq_right h

@[simp] lemma relu_zero : relu 0 = 0 := by simp [relu]

/-- `[z]_+² + [-z]_+² = z²`: the identity behind the cancellation at uniform `h`. -/
lemma relu_sq_add_relu_neg_sq (z : ℝ) : relu z ^ 2 + relu (-z) ^ 2 = z ^ 2 := by
  rcases le_total 0 z with h | h
  · rw [relu_of_nonneg h, relu_of_nonpos (by linarith)]
    ring
  · rw [relu_of_nonpos h, relu_of_nonneg (by linarith)]
    ring

/-- `[r z]_+ = r [z]_+` for `r ≥ 0`. -/
lemma relu_mul_of_nonneg {r : ℝ} (hr : 0 ≤ r) (z : ℝ) : relu (r * z) = r * relu z := by
  unfold relu
  rw [mul_max_of_nonneg _ _ hr, mul_zero]

/-- Squared Euclidean length of a column. -/
def sqNorm (v : Fin 2 → ℝ) : ℝ := v 0 ^ 2 + v 1 ^ 2

/-- Dot product of two columns. -/
def dot2 (v w : Fin 2 → ℝ) : ℝ := v 0 * w 0 + v 1 * w 1

/-- The per-feature population loss `ℓ_i(W) = ⅓[(1 - |W_i|²)² + ∑_{j≠i} [W_j·W_i]_+²]`. -/
noncomputable def featureLoss (W : Fin 5 → Fin 2 → ℝ) (i : Fin 5) : ℝ :=
  (1 / 3) * ((1 - sqNorm (W i)) ^ 2 + ∑ j, if j = i then 0 else relu (dot2 (W j) (W i)) ^ 2)

/-- The reweighted loss `L_h = ∑ h_i ℓ_i`. -/
noncomputable def weightedLoss (h : Fin 5 → ℝ) (W : Fin 5 → Fin 2 → ℝ) : ℝ :=
  ∑ i, h i * featureLoss W i

/-- The 4-gon with the dead unit at `(x, y)`. -/
def fourGon (x y : ℝ) : Fin 5 → Fin 2 → ℝ :=
  ![![1, 0], ![0, 1], ![-1, 0], ![0, -1], ![x, y]]

lemma relu_neg_one : relu (-1) = 0 := relu_of_nonpos (by norm_num)

lemma featureLoss_fourGon_0 (x y : ℝ) : featureLoss (fourGon x y) 0 = (1 / 3) * relu x ^ 2 := by
  simp [featureLoss, fourGon, sqNorm, dot2, Fin.sum_univ_five, relu_neg_one]

lemma featureLoss_fourGon_1 (x y : ℝ) : featureLoss (fourGon x y) 1 = (1 / 3) * relu y ^ 2 := by
  simp [featureLoss, fourGon, sqNorm, dot2, Fin.sum_univ_five, relu_neg_one]

lemma featureLoss_fourGon_2 (x y : ℝ) :
    featureLoss (fourGon x y) 2 = (1 / 3) * relu (-x) ^ 2 := by
  simp [featureLoss, fourGon, sqNorm, dot2, Fin.sum_univ_five, relu_neg_one]

lemma featureLoss_fourGon_3 (x y : ℝ) :
    featureLoss (fourGon x y) 3 = (1 / 3) * relu (-y) ^ 2 := by
  simp [featureLoss, fourGon, sqNorm, dot2, Fin.sum_univ_five, relu_neg_one]

lemma featureLoss_fourGon_4 (x y : ℝ) :
    featureLoss (fourGon x y) 4 = (1 / 3) * ((1 - (x ^ 2 + y ^ 2)) ^ 2 + (x ^ 2 + y ^ 2)) := by
  simp [featureLoss, fourGon, sqNorm, dot2, Fin.sum_univ_five]
  have hx := relu_sq_add_relu_neg_sq x
  have hy := relu_sq_add_relu_neg_sq y
  linear_combination hx + hy

/-- **The frozen loss with the dead unit at `(x, y)`**, for every reweighting `h`. -/
theorem weightedLoss_fourGon (h : Fin 5 → ℝ) (x y : ℝ) :
    weightedLoss h (fourGon x y) - weightedLoss h (fourGon 0 0)
      = (1 / 3) * (h 0 * relu x ^ 2 + h 1 * relu y ^ 2 + h 2 * relu (-x) ^ 2
          + h 3 * relu (-y) ^ 2 - h 4 * (x ^ 2 + y ^ 2))
        + h 4 / 3 * (x ^ 2 + y ^ 2) ^ 2 := by
  simp only [weightedLoss, Fin.sum_univ_five, featureLoss_fourGon_0, featureLoss_fourGon_1,
    featureLoss_fourGon_2, featureLoss_fourGon_3, featureLoss_fourGon_4, neg_zero, relu_zero]
  ring

/-- **Part (ii).** At uniform `h_i = 1/5` the frozen excess loss is `r⁴/15`. -/
theorem weightedLoss_fourGon_uniform (x y : ℝ) :
    weightedLoss (fun _ => 1 / 5) (fourGon x y) - weightedLoss (fun _ => 1 / 5) (fourGon 0 0)
      = (1 / 15) * (x ^ 2 + y ^ 2) ^ 2 := by
  rw [weightedLoss_fourGon]
  have hx := relu_sq_add_relu_neg_sq x
  have hy := relu_sq_add_relu_neg_sq y
  linear_combination (1 / 15) * hx + (1 / 15) * hy

/-- The stability coefficient `a(θ;h) = ⅓[∑_{j<4} h_j [cos(θ - θ_j)]_+² - h_4]` with
`θ_j = 0, π/2, π, 3π/2`. -/
noncomputable def stabilityCoeff (h : Fin 5 → ℝ) (θ : ℝ) : ℝ :=
  (1 / 3) * (h 0 * relu (cos θ) ^ 2 + h 1 * relu (sin θ) ^ 2 + h 2 * relu (-cos θ) ^ 2
    + h 3 * relu (-sin θ) ^ 2 - h 4)

/-- **Part (iv): the frozen loss along a ray.** For `r ≥ 0`,
`L_h(r(cos θ, sin θ)) - L_h(4-gon) = a(θ;h) r² + (h_4/3) r⁴`. -/
theorem weightedLoss_fourGon_ray (h : Fin 5 → ℝ) (r θ : ℝ) (hr : 0 ≤ r) :
    weightedLoss h (fourGon (r * cos θ) (r * sin θ)) - weightedLoss h (fourGon 0 0)
      = stabilityCoeff h θ * r ^ 2 + h 4 / 3 * r ^ 4 := by
  rw [weightedLoss_fourGon, stabilityCoeff, ← mul_neg, ← mul_neg, relu_mul_of_nonneg hr,
    relu_mul_of_nonneg hr, relu_mul_of_nonneg hr, relu_mul_of_nonneg hr]
  have hsc := sin_sq_add_cos_sq θ
  linear_combination (h 4 / 3 * r ^ 2 * (r ^ 2 * (sin θ ^ 2 + cos θ ^ 2 + 1) - 1)) * hsc

/-- At uniform `h` the stability coefficient vanishes for every `θ`. -/
theorem stabilityCoeff_uniform (θ : ℝ) : stabilityCoeff (fun _ => 1 / 5) θ = 0 := by
  unfold stabilityCoeff
  have hc := relu_sq_add_relu_neg_sq (cos θ)
  have hs := relu_sq_add_relu_neg_sq (sin θ)
  have hsc := sin_sq_add_cos_sq θ
  linear_combination (1 / 15) * hc + (1 / 15) * hs + (1 / 15) * hsc

/-- **Part (iii): the sublevel volume of `r⁴/15` on `ℝ²` is `π √(15 ε)`**, i.e. `∝ ε^{1/2}`,
the volume scaling behind `λ_{C₄} = ½`, multiplicity `1`. -/
theorem volume_sublevel_quartic (ε : ℝ) (hε : 0 < ε) :
    volume {p : EuclideanSpace ℝ (Fin 2) | ‖p‖ ^ 4 / 15 < ε} = ENNReal.ofReal (π * √(15 * ε)) := by
  set R := √(√(15 * ε)) with hR
  have hR0 : 0 ≤ R := Real.sqrt_nonneg _
  have hR2 : R ^ 2 = √(15 * ε) := Real.sq_sqrt (Real.sqrt_nonneg _)
  have hR4 : R ^ 4 = ε * 15 := by
    rw [show (4 : ℕ) = 2 * 2 from rfl, pow_mul, hR2, Real.sq_sqrt (by positivity), mul_comm]
  have hset : {p : EuclideanSpace ℝ (Fin 2) | ‖p‖ ^ 4 / 15 < ε} = Metric.ball 0 R := by
    ext p
    simp only [Set.mem_ofPred_eq, Metric.mem_ball, dist_zero_right]
    rw [div_lt_iff₀ (by norm_num), ← hR4]
    exact pow_lt_pow_iff_left₀ (norm_nonneg p) hR0 (by norm_num)
  rw [hset, EuclideanSpace.volume_ball_fin_two, ← ENNReal.ofReal_pow hR0,
    ← ENNReal.ofReal_mul (by positivity), hR2, mul_comm]

end Laplace.Patterning
