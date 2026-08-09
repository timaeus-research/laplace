/-
Copyright (c) 2026 Timaeus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib
import Laplace.Multi.QuadLowerBound
import Laplace.Multi.QuadMoments

/-!
# Dominated convergence for the rescaled Boltzmann integrand

Stage H4 of the multivariate programme: one generic theorem, not
three. For a loss carrying the H3 package and an integration domain
`U` (with a ball around the origin inside it and the rescaled lower
bound on it), every continuous observable of quadratic growth
satisfies
`∫ 1_{q•x ∈ U} h(x) e^{-(L(q•x)-L(0))/q²} dx → ∫ h(x) K_H(x) dx`
as `q → 0⁺`, by dominated convergence against the
`C(1+‖x‖²)e^{-c‖x‖²}` majorant. The corollaries at `h = 1, x_i,
x_i·x_j` land on the H2 Gaussian values.
-/

open Real Matrix Filter Topology Asymptotics MeasureTheory

namespace Laplace.Multi

variable {d : ℕ}

/-- The Gaussian-with-polynomial dominator is integrable, for every
positive decay rate. -/
theorem integrable_one_add_sq_mul_exp {c : ℝ} (hc : 0 < c) :
    Integrable (fun x : EuclidD d ↦
      (1 + ‖x‖ ^ 2) * Real.exp (-c * ‖x‖ ^ 2)) := by
  have h1 : Integrable (fun x : EuclidD d ↦
      Real.exp (-c * ‖x‖ ^ 2)) := integrable_exp_neg_mul_sq_norm hc
  have h2 : Integrable (fun x : EuclidD d ↦
      (2 / c) * Real.exp (-(c / 2) * ‖x‖ ^ 2)) :=
    (integrable_exp_neg_mul_sq_norm (by positivity)).const_mul _
  have hsum := h1.add h2
  refine hsum.mono' ?_ (Filter.Eventually.of_forall fun x ↦ ?_)
  · exact ((continuous_const.add (continuous_norm.pow 2)).mul
      (Real.continuous_exp.comp
        ((continuous_norm.pow 2).const_mul (-c)))).aestronglyMeasurable
  · rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    have hsq : ‖x‖ ^ 2 ≤ (2 / c) * Real.exp ((c / 2) * ‖x‖ ^ 2) := by
      have hu := Real.add_one_le_exp ((c / 2) * ‖x‖ ^ 2)
      have hc2 : (0 : ℝ) < c / 2 := by positivity
      calc ‖x‖ ^ 2 = (2 / c) * ((c / 2) * ‖x‖ ^ 2) := by
            field_simp
        _ ≤ (2 / c) * ((c / 2) * ‖x‖ ^ 2 + 1) := by
            apply mul_le_mul_of_nonneg_left (by linarith) (by positivity)
        _ ≤ (2 / c) * Real.exp ((c / 2) * ‖x‖ ^ 2) := by
            apply mul_le_mul_of_nonneg_left _ (by positivity)
            linarith [hu]
    calc (1 + ‖x‖ ^ 2) * Real.exp (-c * ‖x‖ ^ 2)
        ≤ (1 + (2 / c) * Real.exp ((c / 2) * ‖x‖ ^ 2)) *
            Real.exp (-c * ‖x‖ ^ 2) := by
          apply mul_le_mul_of_nonneg_right _ (Real.exp_pos _).le
          linarith [hsq]
      _ = Real.exp (-c * ‖x‖ ^ 2) +
            (2 / c) * Real.exp (-(c / 2) * ‖x‖ ^ 2) := by
          rw [add_mul, one_mul, mul_assoc, ← Real.exp_add]
          have harg : c / 2 * ‖x‖ ^ 2 + -c * ‖x‖ ^ 2 =
              -(c / 2) * ‖x‖ ^ 2 := by ring
          rw [harg]

/-- **The H4 hypothesis package**: the H3 quadratic approximation
plus an integration domain with a ball around the origin and the
support-wide rescaled lower bound (the shape consult's H4-facing
form, so no closed-ball inclusion needs exposing). -/
structure LocalLaplaceDomain {d : ℕ} (L : EuclidD d → ℝ)
    (H : Matrix (Fin d) (Fin d) ℝ)
    extends LocalQuadraticApprox L H where
  U : Set (EuclidD d)
  measurableSet_U : MeasurableSet U
  delta : ℝ
  delta_pos : 0 < delta
  ball_subset_U : Metric.ball (0 : EuclidD d) delta ⊆ U
  c : ℝ
  c_pos : 0 < c
  rescaled_lower : ∀ {q : ℝ} {x : EuclidD d}, 0 < q → q • x ∈ U →
    c * ‖x‖ ^ 2 ≤ (L (q • x) - L 0) / q ^ 2
  measurable_L : Measurable L

namespace LocalLaplaceDomain

variable {L : EuclidD d → ℝ} {H : Matrix (Fin d) (Fin d) ℝ}

/-- The rescaled indicator integrand at parameter `q`. -/
noncomputable def integrand (A : LocalLaplaceDomain L H)
    (h : EuclidD d → ℝ) (q : ℝ) (x : EuclidD d) : ℝ :=
  Set.indicator {x : EuclidD d | q • x ∈ A.U}
    (fun x ↦ h x * Real.exp (-((L (q • x) - L 0) / q ^ 2))) x

/-- **Generic dominated convergence for the rescaled Boltzmann
integrand**: continuous observables of quadratic growth converge to
their quadratic-Gaussian integrals. -/
theorem tendsto_integral_rescaled (A : LocalLaplaceDomain L H)
    {h : EuclidD d → ℝ} (h_cont : Continuous h) {C : ℝ} (hC : 0 ≤ C)
    (h_growth : ∀ x : EuclidD d, |h x| ≤ C * (1 + ‖x‖ ^ 2)) :
    Tendsto (fun q : ℝ ↦ ∫ x : EuclidD d, A.integrand h q x)
      (𝓝[>] (0 : ℝ))
      (𝓝 (∫ x : EuclidD d, h x * quadKernel H x)) := by
  refine tendsto_integral_filter_of_dominated_convergence
    (fun x : EuclidD d ↦ C * ((1 + ‖x‖ ^ 2) *
      Real.exp (-A.c * ‖x‖ ^ 2))) ?_ ?_ ?_ ?_
  · -- eventual measurability
    filter_upwards [self_mem_nhdsWithin] with q hq
    have hset : MeasurableSet {x : EuclidD d | q • x ∈ A.U} :=
      (measurable_const_smul q) A.measurableSet_U
    refine AEStronglyMeasurable.indicator ?_ hset
    have hmL : Measurable fun x : EuclidD d ↦
        Real.exp (-((L (q • x) - L 0) / q ^ 2)) := by
      have hm : Measurable fun x : EuclidD d ↦ L (q • x) :=
        A.measurable_L.comp (measurable_const_smul q)
      exact Real.measurable_exp.comp
        (((hm.sub measurable_const).div_const _).neg)
    exact (h_cont.measurable.mul hmL).aestronglyMeasurable
  · -- domination
    filter_upwards [self_mem_nhdsWithin] with q hq
    refine Filter.Eventually.of_forall fun x ↦ ?_
    unfold integrand
    by_cases hmem : q • x ∈ A.U
    · rw [Set.indicator_of_mem
        (show x ∈ {x : EuclidD d | q • x ∈ A.U} from hmem)]
      have hlow := A.rescaled_lower hq hmem
      rw [Real.norm_eq_abs, abs_mul,
        abs_of_pos (Real.exp_pos _)]
      calc |h x| * Real.exp (-((L (q • x) - L 0) / q ^ 2))
          ≤ (C * (1 + ‖x‖ ^ 2)) *
              Real.exp (-(A.c * ‖x‖ ^ 2)) := by
            apply mul_le_mul (h_growth x) _ (Real.exp_pos _).le
              (mul_nonneg hC (by positivity))
            exact Real.exp_le_exp.mpr (by linarith [hlow])
        _ = C * ((1 + ‖x‖ ^ 2) * Real.exp (-A.c * ‖x‖ ^ 2)) := by
            rw [neg_mul]
            ring
    · rw [Set.indicator_of_notMem
        (show x ∉ {x : EuclidD d | q • x ∈ A.U} from hmem)]
      simp only [norm_zero]
      have h1 := sq_nonneg ‖x‖
      have h2 := (Real.exp_pos (-A.c * ‖x‖ ^ 2)).le
      have h3 : (0 : ℝ) ≤ (1 + ‖x‖ ^ 2) * Real.exp (-A.c * ‖x‖ ^ 2) := by
        positivity
      exact mul_nonneg hC h3
  · -- dominator integrability
    exact (integrable_one_add_sq_mul_exp A.c_pos).const_mul C
  · -- pointwise limit
    refine Filter.Eventually.of_forall fun x ↦ ?_
    have hev : ∀ᶠ q in 𝓝[>] (0 : ℝ), q • x ∈ A.U := by
      have hq_small : ∀ᶠ q in 𝓝[>] (0 : ℝ),
          q < A.delta / (‖x‖ + 1) := by
        apply eventually_nhdsWithin_of_eventually_nhds
        exact eventually_lt_nhds (div_pos A.delta_pos (by positivity))
      filter_upwards [hq_small, self_mem_nhdsWithin] with q hq hq0
      apply A.ball_subset_U
      rw [Metric.mem_ball, dist_eq_norm, sub_zero, norm_smul,
        Real.norm_eq_abs, abs_of_pos hq0]
      calc q * ‖x‖ ≤ q * (‖x‖ + 1) := by
            apply mul_le_mul_of_nonneg_left _ hq0.le
            linarith
        _ < A.delta / (‖x‖ + 1) * (‖x‖ + 1) := by
            apply mul_lt_mul_of_pos_right hq (by positivity)
        _ = A.delta := by
            field_simp
    have hlim : Tendsto
        (fun q : ℝ ↦ h x * Real.exp (-((L (q • x) - L 0) / q ^ 2)))
        (𝓝[>] (0 : ℝ)) (𝓝 (h x * quadKernel H x)) := by
      have h1 := A.rescaled_tendsto x
      have h2 : Tendsto
          (fun q : ℝ ↦ Real.exp (-((L (q • x) - L 0) / q ^ 2)))
          (𝓝[>] (0 : ℝ)) (𝓝 (Real.exp (-(qform H x / 2)))) :=
        (Real.continuous_exp.continuousAt.tendsto.comp h1.neg)
      have hqk : quadKernel H x = Real.exp (-(qform H x / 2)) := by
        unfold quadKernel
        rw [neg_div]
      rw [hqk]
      exact h2.const_mul (h x)
    refine hlim.congr' ?_
    filter_upwards [hev] with q hmem
    unfold integrand
    rw [Set.indicator_of_mem
      (show x ∈ {x : EuclidD d | q • x ∈ A.U} from hmem)]

/-- Moment-zero corollary: the rescaled partition integral converges
to the quadratic-Gaussian mass. -/
theorem tendsto_integral_rescaled_one (A : LocalLaplaceDomain L H) :
    Tendsto (fun q : ℝ ↦ ∫ x : EuclidD d,
        A.integrand (fun _ ↦ 1) q x) (𝓝[>] (0 : ℝ))
      (𝓝 (jacInv H * (2 * π) ^ ((d : ℝ) / 2))) := by
  have h := A.tendsto_integral_rescaled (h := fun _ ↦ 1)
    continuous_const (C := 1) one_pos.le
    (fun x ↦ by rw [abs_one, one_mul]; linarith [sq_nonneg ‖x‖])
  have hval : (∫ x : EuclidD d, (1 : ℝ) * quadKernel H x) =
      jacInv H * (2 * π) ^ ((d : ℝ) / 2) := by
    simp only [one_mul]
    exact integral_quadKernel A.hH_posDef
  rwa [hval] at h

/-- First-moment corollary: rescaled coordinate integrals vanish in
the limit. -/
theorem tendsto_integral_rescaled_coord (A : LocalLaplaceDomain L H)
    (i : Fin d) :
    Tendsto (fun q : ℝ ↦ ∫ x : EuclidD d,
        A.integrand (fun x ↦ x i) q x) (𝓝[>] (0 : ℝ)) (𝓝 0) := by
  have hcont : Continuous fun x : EuclidD d ↦ x i :=
    PiLp.continuous_apply 2 (fun _ : Fin d ↦ ℝ) i
  have h := A.tendsto_integral_rescaled (h := fun x ↦ x i)
    hcont (C := 1) one_pos.le (fun x ↦ ?_)
  · have hval : (∫ x : EuclidD d, x i * quadKernel H x) = 0 :=
      integral_coord_mul_quadKernel A.hH_posDef i
    rwa [hval] at h
  · rw [one_mul]
    calc |x i| ≤ ‖x‖ := by simpa using PiLp.norm_apply_le x i
      _ ≤ 1 + ‖x‖ ^ 2 := by nlinarith [sq_nonneg (‖x‖ - 1)]

/-- Second-moment corollary: rescaled coordinate-pair integrals
converge to the unnormalized `H⁻¹` Gaussian moments. -/
theorem tendsto_integral_rescaled_coord_mul
    (A : LocalLaplaceDomain L H) (i j : Fin d) :
    Tendsto (fun q : ℝ ↦ ∫ x : EuclidD d,
        A.integrand (fun x ↦ x i * x j) q x) (𝓝[>] (0 : ℝ))
      (𝓝 (jacInv H * (2 * π) ^ ((d : ℝ) / 2) * H⁻¹ i j)) := by
  have hci : Continuous fun x : EuclidD d ↦ x i :=
    PiLp.continuous_apply 2 (fun _ : Fin d ↦ ℝ) i
  have hcj : Continuous fun x : EuclidD d ↦ x j :=
    PiLp.continuous_apply 2 (fun _ : Fin d ↦ ℝ) j
  have h := A.tendsto_integral_rescaled (h := fun x ↦ x i * x j)
    (hci.mul hcj) (C := 1) one_pos.le (fun x ↦ ?_)
  · have hval : (∫ x : EuclidD d, x i * x j * quadKernel H x) =
        jacInv H * (2 * π) ^ ((d : ℝ) / 2) * H⁻¹ i j :=
      integral_coord_mul_coord_quadKernel A.hH_posDef i j
    rwa [hval] at h
  · rw [one_mul, abs_mul]
    have h1 : |x i| ≤ ‖x‖ := by simpa using PiLp.norm_apply_le x i
    have h2 : |x j| ≤ ‖x‖ := by simpa using PiLp.norm_apply_le x j
    calc |x i| * |x j| ≤ ‖x‖ * ‖x‖ :=
          mul_le_mul h1 h2 (abs_nonneg _) (norm_nonneg _)
      _ = ‖x‖ ^ 2 := by ring
      _ ≤ 1 + ‖x‖ ^ 2 := by linarith [sq_nonneg ‖x‖]

end LocalLaplaceDomain

end Laplace.Multi
