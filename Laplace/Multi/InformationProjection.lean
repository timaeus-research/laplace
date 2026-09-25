/-
Copyright (c) 2026 Timaeus Research. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniel Murfet
-/
import Mathlib
import Laplace.Multi.EntropyDuality

/-!
# The KL Pythagorean theorem: response coordinates are the dual affine coordinates

For the affine posterior family `P_a ∝ e^{-t L_a} π`, `L_a = L₀ + a·R`, the seabed's Bregman
identity (`mixKL_aff_eq`) reads `KL(P_a ‖ P_b) = A(b) − A(a) + t (b − a)·m(a)`, with `A = log Z`
and `m` the mean map. Here we add the **information-projection (Pythagorean) theorem**: if a
probability density `q` matches the moments of `P_a`, `E_q[R] = m(a)`, then for every `b`

  `KL(q ‖ P_b) = KL(q ‖ P_a) + KL(P_a ‖ P_b)`   (`relEnt_pythagoras`).

So `P_a` is the information projection of `q` onto the exponential family through the moment
condition, and the mean map `m` — the response coordinates — is the dual affine coordinate system
in which projections are orthogonal. The featureless line is straight in the natural coordinate `a`;
this is its exact geometric distinction (Astra, round 26, Theorem B).
-/

open MeasureTheory Filter Topology Set

namespace Laplace.Multi

variable {X : Type*} [MeasurableSpace X] {μ : Measure X} {ι : Type*} [Fintype ι]

/-- The pointwise log-ratio of two members of the affine family: `log p_a − log p_b =
t R_{b−a} + A(b) − A(a)`. -/
theorem log_gibbsDensity_sub {π L₀ : X → ℝ} (hπ : ∀ x, 0 < π x) {R : ι → X → ℝ} {t : ℝ}
    {a b : ι → ℝ} (hZa : 0 < priorZ μ π (affLoss L₀ R a) t)
    (hZb : 0 < priorZ μ π (affLoss L₀ R b) t) (x : X) :
    Real.log (gibbsDensity μ π (affLoss L₀ R a) t x) -
        Real.log (gibbsDensity μ π (affLoss L₀ R b) t x) =
      t * dirLoss R (b - a) x + (affLogZ μ π L₀ R t b - affLogZ μ π L₀ R t a) := by
  unfold gibbsDensity affLogZ
  rw [Real.log_div (mul_pos (Real.exp_pos _) (hπ x)).ne' hZa.ne',
    Real.log_div (mul_pos (Real.exp_pos _) (hπ x)).ne' hZb.ne',
    Real.log_mul (Real.exp_pos _).ne' (hπ x).ne', Real.log_mul (Real.exp_pos _).ne' (hπ x).ne',
    Real.log_exp, Real.log_exp]
  simp only [affLoss, dirLoss, Pi.sub_apply, sub_mul, Finset.sum_sub_distrib]
  ring

/-- **The KL Pythagorean theorem**: a moment-matched density decomposes its divergence to every
member of the affine family through the matched member. -/
theorem relEnt_pythagoras [Nonempty X] {π L₀ : X → ℝ} (hπm : Measurable π) (hπi : Integrable π μ)
    (hπ : ∀ x, 0 < π x) (hπpos : 0 < ∫ x, π x ∂μ) (hL₀m : Measurable L₀) {M₀ : ℝ}
    (hL₀ : ∀ x, |L₀ x| ≤ M₀) {R : ι → X → ℝ} (hR : ∀ i, Bdd (R i)) (t : ℝ) (a b : ι → ℝ)
    {q : X → ℝ} (hqi : Integrable q μ) (hq1 : ∫ x, q x ∂μ = 1)
    (hqR : ∀ i, Integrable (fun x ↦ q x * R i x) μ)
    (hmatch : ∀ i, ∫ x, q x * R i x ∂μ = meanMap μ π L₀ R t a i)
    (hka : Integrable (fun x ↦ q x * Real.log (q x / gibbsDensity μ π (affLoss L₀ R a) t x)) μ)
    (hkb : Integrable (fun x ↦ q x * Real.log (q x / gibbsDensity μ π (affLoss L₀ R b) t x)) μ) :
    relEnt μ q (gibbsDensity μ π (affLoss L₀ R b) t) =
      relEnt μ q (gibbsDensity μ π (affLoss L₀ R a) t) +
        mixKL μ π (affLoss L₀ R a) (dirLoss R (b - a)) t 0 1 := by
  have hπ' : ∀ x, 0 ≤ π x := fun x ↦ (hπ x).le
  obtain ⟨_, ha⟩ := tiltData_aff hπm hπi hπ' hπpos hL₀m hL₀ hR a 0 t
  obtain ⟨_, hb⟩ := tiltData_aff hπm hπi hπ' hπpos hL₀m hL₀ hR b 0 t
  have hZa := ha.ν_pos
  have hZb := hb.ν_pos
  rw [mixKL_aff_eq hπm hπi hπ' hπpos hL₀m hL₀ hR t a b]
  -- the pointwise identity
  have hpt : ∀ x, q x * Real.log (q x / gibbsDensity μ π (affLoss L₀ R b) t x) -
      q x * Real.log (q x / gibbsDensity μ π (affLoss L₀ R a) t x) =
      q x * (t * dirLoss R (b - a) x + (affLogZ μ π L₀ R t b - affLogZ μ π L₀ R t a)) := fun x ↦ by
    by_cases hq : q x = 0
    · simp [hq]
    rw [← mul_sub, Real.log_div hq (gibbsDensity_pos hπ' hZb (hπ x).ne').ne',
      Real.log_div hq (gibbsDensity_pos hπ' hZa (hπ x).ne').ne',
      ← log_gibbsDensity_sub hπ hZa hZb x]
    ring
  have hsplit : relEnt μ q (gibbsDensity μ π (affLoss L₀ R b) t) -
      relEnt μ q (gibbsDensity μ π (affLoss L₀ R a) t) =
      ∫ x, q x * (t * dirLoss R (b - a) x + (affLogZ μ π L₀ R t b - affLogZ μ π L₀ R t a)) ∂μ := by
    unfold relEnt
    rw [← integral_sub hkb hka]
    exact integral_congr_ae (Filter.Eventually.of_forall hpt)
  -- evaluate the right-hand side
  have hqdir : Integrable (fun x ↦ q x * dirLoss R (b - a) x) μ := by
    have : (fun x ↦ q x * dirLoss R (b - a) x) =
        fun x ↦ ∑ i, (b i - a i) * (q x * R i x) := by
      funext x
      simp only [dirLoss, Pi.sub_apply, Finset.mul_sum]
      refine Finset.sum_congr rfl fun i _ ↦ ?_
      ring
    rw [this]
    exact integrable_finsetSum Finset.univ fun i _ ↦ (hqR i).const_mul _
  have hrhs : (∫ x, q x * (t * dirLoss R (b - a) x +
      (affLogZ μ π L₀ R t b - affLogZ μ π L₀ R t a)) ∂μ) =
      t * ∑ i, (b i - a i) * meanMap μ π L₀ R t a i +
        (affLogZ μ π L₀ R t b - affLogZ μ π L₀ R t a) := by
    have e : ∀ x, q x * (t * dirLoss R (b - a) x + (affLogZ μ π L₀ R t b - affLogZ μ π L₀ R t a)) =
        t * (q x * dirLoss R (b - a) x) +
          (affLogZ μ π L₀ R t b - affLogZ μ π L₀ R t a) * q x := fun x ↦ by ring
    simp_rw [e]
    rw [integral_add (hqdir.const_mul _) (hqi.const_mul _), integral_const_mul, integral_const_mul,
      hq1, mul_one]
    congr 2
    have : (fun x ↦ q x * dirLoss R (b - a) x) =
        fun x ↦ ∑ i, (b i - a i) * (q x * R i x) := by
      funext x
      simp only [dirLoss, Pi.sub_apply, Finset.mul_sum]
      refine Finset.sum_congr rfl fun i _ ↦ ?_
      ring
    rw [this, integral_finsetSum Finset.univ fun i _ ↦ (hqR i).const_mul _]
    refine Finset.sum_congr rfl fun i _ ↦ ?_
    rw [integral_const_mul, hmatch i]
  linarith [hsplit, hrhs]

end Laplace.Multi
