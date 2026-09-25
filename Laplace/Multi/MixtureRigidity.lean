/-
Copyright (c) 2026 Timaeus Research. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniel Murfet
-/
import Mathlib
import Laplace.Multi.PatternAttenuation

/-!
# Uniform interior rigidity of the singular type over the mixture simplex

For a finite family of nonnegative losses `fᵢ` (each the loss of one population of the data, with
the common minimiser as its zero) and mixture weights `aᵢ ∈ [c, C]` with `0 < c`, the mixture loss
`L_a = ∑ᵢ aᵢ fᵢ` is uniformly comparable to `G = ∑ᵢ fᵢ`: `cG ≤ L_a ≤ CG`. The partition function of
`L_a` is therefore sandwiched between rescalings of that of `G`,
`Z_G(Ct) ≤ Z_{L_a}(t) ≤ Z_G(ct)` (`attZ_family_sandwich`), and the leading exponent and log
multiplicity of `Z_{L_a}` are those of `Z_G`, uniformly over the compact subset `[c, C]^ι` of the
open weight simplex (`family_isTheta`). This is the interior-stratum rigidity of the asymptotic
response map over the data manifold: along any path of mixtures that keeps every weight bounded
away from zero, the singular type `(λ, m)` cannot change; jumps can only happen where a weight
vanishes. It generalises the two-population statement `mixture_isTheta` of `PatternAttenuation`.
-/

open Real MeasureTheory Filter Topology Set Asymptotics

namespace Laplace.Multi

variable {d : ℕ} {ι : Type*} [Fintype ι]

/-- `cG ≤ L_a ≤ CG` pointwise for weights in `[c, C]`. -/
theorem family_loss_bounds {f : ι → EuclidD d → ℝ} (hf0 : ∀ i w, 0 ≤ f i w) {a : ι → ℝ}
    {c C : ℝ} (hc : ∀ i, c ≤ a i) (hC : ∀ i, a i ≤ C) (w : EuclidD d) :
    c * ∑ i, f i w ≤ ∑ i, a i * f i w ∧ ∑ i, a i * f i w ≤ C * ∑ i, f i w := by
  constructor
  · rw [Finset.mul_sum]
    exact Finset.sum_le_sum fun i _ ↦ mul_le_mul_of_nonneg_right (hc i) (hf0 i w)
  · rw [Finset.mul_sum]
    exact Finset.sum_le_sum fun i _ ↦ mul_le_mul_of_nonneg_right (hC i) (hf0 i w)

/-- **The mixture sandwich for a finite family**: `Z_G(Ct) ≤ Z_{L_a}(t) ≤ Z_G(ct)`. -/
theorem attZ_family_sandwich {f : ι → EuclidD d → ℝ} {χ : EuclidD d → ℝ} (hχc : Continuous χ)
    (hχs : HasCompactSupport χ) (hχ : ∀ w, 0 ≤ χ w) (hf : ∀ i, Continuous (f i))
    (hf0 : ∀ i w, 0 ≤ f i w) {a : ι → ℝ} {c C : ℝ} (hc : ∀ i, c ≤ a i) (hC : ∀ i, a i ≤ C)
    {t : ℝ} (ht : 0 ≤ t) :
    attZ (fun w ↦ ∑ i, f i w) χ (C * t) ≤ attZ (fun w ↦ ∑ i, a i * f i w) χ t ∧
      attZ (fun w ↦ ∑ i, a i * f i w) χ t ≤ attZ (fun w ↦ ∑ i, f i w) χ (c * t) := by
  have hLa : Continuous fun w ↦ ∑ i, a i * f i w :=
    continuous_finsetSum _ fun i _ ↦ (hf i).const_mul _
  have hG : Continuous fun w ↦ ∑ i, f i w := continuous_finsetSum _ fun i _ ↦ hf i
  constructor
  · rw [← attZ_scale]
    exact attZ_mono hχ (fun w ↦ (family_loss_bounds hf0 hc hC w).2) ht
      (integrable_cutoff_mul_exp hχc hχs hLa t)
  · rw [← attZ_scale]
    exact attZ_mono hχ (fun w ↦ (family_loss_bounds hf0 hc hC w).1) ht
      (integrable_cutoff_mul_exp hχc hχs (hG.const_mul c) t)

/-- **Uniform interior rigidity.** If `Z_G(t) = Θ(t^{-λ} log^p t)` for `G = ∑ᵢ fᵢ`, then
`Z_{L_a}(t) = Θ(t^{-λ} log^p t)` for every weight vector `a` with `0 < c ≤ aᵢ ≤ C`: the singular
type of a mixture of populations with a common minimiser is constant on compact subsets of the open
weight simplex. -/
theorem family_isTheta [Nonempty ι] {f : ι → EuclidD d → ℝ} {χ : EuclidD d → ℝ}
    (hχc : Continuous χ) (hχs : HasCompactSupport χ) (hχ : ∀ w, 0 ≤ χ w)
    (hf : ∀ i, Continuous (f i)) (hf0 : ∀ i w, 0 ≤ f i w) {a : ι → ℝ} {c C : ℝ} (hc0 : 0 < c)
    (hc : ∀ i, c ≤ a i) (hC : ∀ i, a i ≤ C) {lam : ℝ} {p : ℕ}
    (hZ : attZ (fun w ↦ ∑ i, f i w) χ =Θ[atTop] fun t ↦ t ^ (-lam) * Real.log t ^ p) :
    attZ (fun w ↦ ∑ i, a i * f i w) χ =Θ[atTop] fun t ↦ t ^ (-lam) * Real.log t ^ p := by
  have hC0 : 0 < C :=
    lt_of_lt_of_le hc0 ((hc (Classical.arbitrary ι)).trans (hC (Classical.arbitrary ι)))
  refine isTheta_of_sandwich (Z₁ := fun t ↦ attZ (fun w ↦ ∑ i, f i w) χ (C * t))
    (Z₃ := fun t ↦ attZ (fun w ↦ ∑ i, f i w) χ (c * t))
    (Filter.Eventually.of_forall fun t ↦ attZ_nonneg hχ _) ?_ ?_
    (isTheta_comp_const_mul hZ hC0) (isTheta_comp_const_mul hZ hc0)
  · filter_upwards [eventually_ge_atTop (0 : ℝ)] with t ht
    exact (attZ_family_sandwich hχc hχs hχ hf hf0 hc hC ht).1
  · filter_upwards [eventually_ge_atTop (0 : ℝ)] with t ht
    exact (attZ_family_sandwich hχc hχs hχ hf hf0 hc hC ht).2

end Laplace.Multi
