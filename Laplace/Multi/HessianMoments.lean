/-
Copyright (c) 2026 Timaeus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib
import Laplace.Multi.RescaledDCT

/-!
# Normalized posterior moments and the covariance limit

Stage H5 of the multivariate programme: the bookkeeping between the
`U`-restricted Gibbs integrals and the H4 rescaled integrands. The
dilation identity factors every posterior integral into
`q^d·e^{-L(0)/q²}` times an H4 integrand integral (an exact identity
per `q > 0`, so the prefactors cancel exactly in every normalized
ratio), and the H4 limits then give
`q⁻¹·E_q[w_i] → 0`, `q⁻²·E_q[w_i w_j] → (H⁻¹)_{ij}`, and the
covariance form `q⁻²·Cov_q(w_i, w_j) → (H⁻¹)_{ij}` — the multivariate
Hessian-recovery limit of the germbij note. The first-moment limit
is load-bearing: covariance is not the raw second moment.
-/

open Real Matrix Filter Topology MeasureTheory

namespace Laplace.Multi

namespace LocalLaplaceDomain

variable {d : ℕ} {L : EuclidD d → ℝ} {H : Matrix (Fin d) (Fin d) ℝ}

/-- The `U`-restricted unnormalized Gibbs integral of an
observable. -/
noncomputable def posteriorIntegral (A : LocalLaplaceDomain L H)
    (f : EuclidD d → ℝ) (q : ℝ) : ℝ :=
  ∫ w : EuclidD d,
    Set.indicator A.U (fun w ↦ f w * Real.exp (-(L w / q ^ 2))) w

/-- **The dilation identity**: every posterior integral factors into
the scale prefactor times an H4 rescaled-integrand integral,
exactly, for each `q > 0`. -/
theorem posteriorIntegral_eq (A : LocalLaplaceDomain L H)
    (f : EuclidD d → ℝ) {q : ℝ} (hq : 0 < q) :
    A.posteriorIntegral f q =
      q ^ d * Real.exp (-(L 0 / q ^ 2)) *
        ∫ x : EuclidD d, A.integrand (fun x ↦ f (q • x)) q x := by
  unfold posteriorIntegral
  rw [integral_dilation
    (fun w ↦ Set.indicator A.U
      (fun w ↦ f w * Real.exp (-(L w / q ^ 2))) w) hq,
    mul_assoc]
  congr 1
  rw [← integral_const_mul]
  refine integral_congr_ae (Filter.Eventually.of_forall fun x ↦ ?_)
  unfold integrand
  simp only []
  by_cases hm : q • x ∈ A.U
  · rw [Set.indicator_of_mem hm,
      Set.indicator_of_mem
        (show x ∈ {x : EuclidD d | q • x ∈ A.U} from hm)]
    rw [mul_left_comm, ← Real.exp_add]
    congr 2
    ring
  · rw [Set.indicator_of_notMem hm,
      Set.indicator_of_notMem
        (show x ∉ {x : EuclidD d | q • x ∈ A.U} from hm), mul_zero]

/-- The composed constant observable. -/
theorem integrand_comp_one (A : LocalLaplaceDomain L H) (q : ℝ) :
    (fun x : EuclidD d ↦
        A.integrand (fun x ↦ (fun _ : EuclidD d ↦ (1 : ℝ)) (q • x)) q x) =
      fun x : EuclidD d ↦ A.integrand (fun _ ↦ 1) q x :=
  rfl

/-- Composing a coordinate observable with the dilation pulls out one
power of `q`. -/
theorem integrand_comp_coord (A : LocalLaplaceDomain L H) (i : Fin d)
    (q : ℝ) :
    (fun x : EuclidD d ↦
        A.integrand (fun x ↦ (q • x) i) q x) =
      fun x : EuclidD d ↦ q * A.integrand (fun x ↦ x i) q x := by
  funext x
  unfold integrand
  rw [← Set.indicator_const_mul]
  congr 1
  funext y
  simp only [PiLp.smul_apply, smul_eq_mul]
  ring

/-- Composing a coordinate-pair observable with the dilation pulls
out two powers of `q`. -/
theorem integrand_comp_coord_mul (A : LocalLaplaceDomain L H)
    (i j : Fin d) (q : ℝ) :
    (fun x : EuclidD d ↦
        A.integrand (fun x ↦ (q • x) i * (q • x) j) q x) =
      fun x : EuclidD d ↦ q ^ 2 * A.integrand (fun x ↦ x i * x j) q x := by
  funext x
  unfold integrand
  rw [← Set.indicator_const_mul]
  congr 1
  funext y
  simp only [PiLp.smul_apply, smul_eq_mul]
  ring

/-- The zeroth rescaled integral is eventually positive. -/
theorem eventually_integrand_one_pos (A : LocalLaplaceDomain L H) :
    ∀ᶠ q in 𝓝[>] (0 : ℝ),
      0 < ∫ x : EuclidD d, A.integrand (fun _ ↦ 1) q x := by
  have hpos : 0 < jacInv H * (2 * π) ^ ((d : ℝ) / 2) :=
    mul_pos (jacInv_pos A.hH_posDef) (by positivity)
  exact A.tendsto_integral_rescaled_one.eventually
    (eventually_gt_nhds hpos)

/-- **Normalized first moments vanish at rate `q`**:
`q⁻¹·E_q[w_i] → 0`. -/
theorem tendsto_normalized_first_moment (A : LocalLaplaceDomain L H)
    (i : Fin d) :
    Tendsto (fun q : ℝ ↦
        A.posteriorIntegral (fun w ↦ w i) q /
          A.posteriorIntegral (fun _ ↦ 1) q / q)
      (𝓝[>] (0 : ℝ)) (𝓝 0) := by
  have hZ : jacInv H * (2 * π) ^ ((d : ℝ) / 2) ≠ 0 :=
    (mul_pos (jacInv_pos A.hH_posDef) (by positivity)).ne'
  have hlim := (A.tendsto_integral_rescaled_coord i).div
    A.tendsto_integral_rescaled_one hZ
  rw [zero_div] at hlim
  refine hlim.congr' ?_
  filter_upwards [A.eventually_integrand_one_pos, self_mem_nhdsWithin]
    with q hpos hq
  simp only [Pi.div_apply]
  have hq0 : (q : ℝ) ≠ 0 := ne_of_gt hq
  have hP : q ^ d * Real.exp (-(L 0 / q ^ 2)) ≠ 0 := by positivity
  rw [posteriorIntegral_eq A _ hq, posteriorIntegral_eq A _ hq]
  rw [show (fun x : EuclidD d ↦
      A.integrand (fun x ↦ (q • x) i) q x) =
    fun x : EuclidD d ↦ q * A.integrand (fun x ↦ x i) q x from
    A.integrand_comp_coord i q]
  rw [integral_const_mul]
  field_simp

/-- **Normalized second moments recover `H⁻¹`**:
`q⁻²·E_q[w_i w_j] → (H⁻¹)_{ij}`. -/
theorem tendsto_normalized_second_moment (A : LocalLaplaceDomain L H)
    (i j : Fin d) :
    Tendsto (fun q : ℝ ↦
        A.posteriorIntegral (fun w ↦ w i * w j) q /
          A.posteriorIntegral (fun _ ↦ 1) q / q ^ 2)
      (𝓝[>] (0 : ℝ)) (𝓝 (H⁻¹ i j)) := by
  have hZpos : 0 < jacInv H * (2 * π) ^ ((d : ℝ) / 2) :=
    mul_pos (jacInv_pos A.hH_posDef) (by positivity)
  have hlim := (A.tendsto_integral_rescaled_coord_mul i j).div
    A.tendsto_integral_rescaled_one hZpos.ne'
  have hval : jacInv H * (2 * π) ^ ((d : ℝ) / 2) * H⁻¹ i j /
      (jacInv H * (2 * π) ^ ((d : ℝ) / 2)) = H⁻¹ i j := by
    have hj : jacInv H ≠ 0 := (jacInv_pos A.hH_posDef).ne'
    field_simp
  rw [hval] at hlim
  refine hlim.congr' ?_
  filter_upwards [A.eventually_integrand_one_pos, self_mem_nhdsWithin]
    with q hpos hq
  simp only [Pi.div_apply]
  have hq0 : (q : ℝ) ≠ 0 := ne_of_gt hq
  have hP : q ^ d * Real.exp (-(L 0 / q ^ 2)) ≠ 0 := by positivity
  rw [posteriorIntegral_eq A _ hq, posteriorIntegral_eq A _ hq]
  rw [show (fun x : EuclidD d ↦
      A.integrand (fun x ↦ (q • x) i * (q • x) j) q x) =
    fun x : EuclidD d ↦ q ^ 2 * A.integrand (fun x ↦ x i * x j) q x from
    A.integrand_comp_coord_mul i j q]
  rw [integral_const_mul]
  field_simp

/-- **The multivariate Hessian-recovery limit** (germbij §3, Hessian
step): the normalized posterior covariance at scale `q⁻²` converges
to the inverse Hessian. -/
theorem tendsto_normalized_covariance (A : LocalLaplaceDomain L H)
    (i j : Fin d) :
    Tendsto (fun q : ℝ ↦
        (A.posteriorIntegral (fun w ↦ w i * w j) q /
            A.posteriorIntegral (fun _ ↦ 1) q -
          A.posteriorIntegral (fun w ↦ w i) q /
              A.posteriorIntegral (fun _ ↦ 1) q *
            (A.posteriorIntegral (fun w ↦ w j) q /
              A.posteriorIntegral (fun _ ↦ 1) q)) / q ^ 2)
      (𝓝[>] (0 : ℝ)) (𝓝 (H⁻¹ i j)) := by
  have h2 := A.tendsto_normalized_second_moment i j
  have h1i := A.tendsto_normalized_first_moment i
  have h1j := A.tendsto_normalized_first_moment j
  have hcomb := h2.sub (h1i.mul h1j)
  rw [mul_zero, sub_zero] at hcomb
  refine hcomb.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with q hq
  have hq0 : (q : ℝ) ≠ 0 := ne_of_gt hq
  field_simp

end LocalLaplaceDomain

end Laplace.Multi
