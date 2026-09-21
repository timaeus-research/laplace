/-
Copyright (c) 2026 Timaeus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniel Murfet
-/
import Laplace.Patterning.OUPathwise

/-!
# Increment sums along a continuous path

The deterministic core of the identification of the OU semigroup with the stochastic
differential equation: for a `C¹` matrix path `F` and a continuous vector path `w`, the
"Itô sums" `∑ₖ F(uₖ) (w(uₖ₊₁) - w(uₖ))` over the uniform partition of `[0, s]` converge to the
integration-by-parts expression `F(s) w(s) - F(0) w(0) - ∫₀ˢ F'(u) w(u) du`
(`tendsto_incrementSum`). Applied to `F(u) = e^{-(s-u)H} σ` this recovers the pathwise OU solution
`ouSol` of `OUPathwise.lean` (`tendsto_ouIncrementSum`). The same mesh estimate gives the
convergence of left Riemann sums of a continuous function (`tendsto_riemannSum`).

Nothing here is probabilistic; the increments are later fed with Brownian paths in
`OUBrownian.lean`.
-/

namespace Laplace.Patterning

open Matrix NormedSpace MeasureTheory Filter Topology intervalIntegral Finset

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

attribute [local instance] Matrix.linftyOpNormedRing Matrix.linftyOpNormedAlgebra

noncomputable section

/-! ### The uniform partition -/

/-- Mesh of the uniform partition of `[0, s]` into `n + 1` pieces. -/
def mesh (s : ℝ) (n : ℕ) : ℝ := s / (n + 1)

/-- The `k`-th node of the uniform partition of `[0, s]` into `n + 1` pieces. -/
def node (s : ℝ) (n k : ℕ) : ℝ := k * mesh s n

theorem node_zero (s : ℝ) (n : ℕ) : node s n 0 = 0 := by simp [node]

theorem node_last (s : ℝ) (n : ℕ) : node s n (n + 1) = s := by
  have : (n : ℝ) + 1 ≠ 0 := by positivity
  simp only [node, mesh]
  push_cast
  field_simp

theorem node_succ_sub (s : ℝ) (n k : ℕ) : node s n (k + 1) - node s n k = mesh s n := by
  simp only [node]
  push_cast
  ring

theorem mesh_nonneg {s : ℝ} (hs : 0 ≤ s) (n : ℕ) : 0 ≤ mesh s n := by
  unfold mesh
  positivity

theorem node_le_succ {s : ℝ} (hs : 0 ≤ s) (n k : ℕ) : node s n k ≤ node s n (k + 1) := by
  have := node_succ_sub s n k
  linarith [mesh_nonneg hs n]

theorem node_nonneg {s : ℝ} (hs : 0 ≤ s) (n k : ℕ) : 0 ≤ node s n k :=
  mul_nonneg (Nat.cast_nonneg k) (mesh_nonneg hs n)

theorem node_le {s : ℝ} (hs : 0 ≤ s) {n k : ℕ} (hk : k ≤ n + 1) : node s n k ≤ s :=
  calc node s n k ≤ node s n (n + 1) :=
        mul_le_mul_of_nonneg_right (by exact_mod_cast hk) (mesh_nonneg hs n)
    _ = s := node_last s n

theorem node_mem_Icc {s : ℝ} (hs : 0 ≤ s) {n k : ℕ} (hk : k ≤ n + 1) :
    node s n k ∈ Set.Icc 0 s :=
  ⟨node_nonneg hs n k, node_le hs hk⟩

theorem exists_mesh_lt {s δ : ℝ} (hδ : 0 < δ) :
    ∃ N : ℕ, ∀ n ≥ N, mesh s n < δ := by
  obtain ⟨N, hN⟩ := exists_nat_gt (s / δ)
  refine ⟨N, fun n hn => ?_⟩
  have hNn : (N : ℝ) ≤ n := by exact_mod_cast hn
  have h2 : s / δ < n + 1 := by linarith
  rw [div_lt_iff₀ hδ] at h2
  unfold mesh
  rw [div_lt_iff₀ (by positivity)]
  linarith [h2]

/-! ### The mesh estimate -/

/-- **Mesh estimate.** If the integrands `φ n k` are uniformly small on their cells once the
mesh is fine, the sum of their cell integrals tends to zero. -/
theorem tendsto_sum_integral_nodes {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [CompleteSpace E] {s : ℝ} (hs : 0 ≤ s) (φ : ℕ → ℕ → ℝ → E)
    (hsmall : ∀ ε > 0, ∃ N, ∀ n ≥ N, ∀ k ≤ n,
      ∀ u ∈ Set.Icc (node s n k) (node s n (k + 1)), ‖φ n k u‖ ≤ ε) :
    Tendsto (fun n => ∑ k ∈ range (n + 1), ∫ u in node s n k..node s n (k + 1), φ n k u) atTop
      (𝓝 0) := by
  rw [Metric.tendsto_atTop]
  intro ε hε
  have hs1 : 0 < s + 1 := by linarith
  obtain ⟨N, hN⟩ := hsmall (ε / (2 * (s + 1))) (by positivity)
  refine ⟨N, fun n hn => ?_⟩
  rw [dist_zero_right]
  have hn1 : (n : ℝ) + 1 ≠ 0 := by positivity
  calc ‖∑ k ∈ range (n + 1), ∫ u in node s n k..node s n (k + 1), φ n k u‖
      ≤ ∑ k ∈ range (n + 1), ‖∫ u in node s n k..node s n (k + 1), φ n k u‖ := norm_sum_le _ _
    _ ≤ ∑ k ∈ range (n + 1), ε / (2 * (s + 1)) * |node s n (k + 1) - node s n k| := by
        refine sum_le_sum fun k hk => ?_
        refine norm_integral_le_of_norm_le_const fun u hu => ?_
        refine hN n hn k (Nat.lt_succ_iff.mp (mem_range.mp hk)) u ?_
        rw [Set.uIoc_of_le (node_le_succ hs n k)] at hu
        exact Set.Ioc_subset_Icc_self hu
    _ = ε / (2 * (s + 1)) * s := by
        simp only [node_succ_sub, abs_of_nonneg (mesh_nonneg hs n), sum_const, card_range,
          nsmul_eq_mul]
        unfold mesh
        field_simp
        push_cast
        ring
    _ < ε := by
        rw [div_mul_eq_mul_div, div_lt_iff₀ (by positivity)]
        nlinarith

/-! ### Left Riemann sums -/

/-- **Left Riemann sums of a continuous function converge to the integral.** -/
theorem tendsto_riemannSum {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [CompleteSpace E] {s : ℝ} (hs : 0 ≤ s) {f : ℝ → E} (hf : Continuous f) :
    Tendsto (fun n => ∑ k ∈ range (n + 1), mesh s n • f (node s n k)) atTop
      (𝓝 (∫ u in (0 : ℝ)..s, f u)) := by
  have key : ∀ n, (∑ k ∈ range (n + 1), mesh s n • f (node s n k)) - ∫ u in (0 : ℝ)..s, f u
      = ∑ k ∈ range (n + 1), ∫ u in node s n k..node s n (k + 1), (f (node s n k) - f u) := by
    intro n
    have hadj := sum_integral_adjacent_intervals (μ := volume) (f := f) (a := node s n)
      (n := n + 1) (fun k _ => hf.intervalIntegrable _ _)
    rw [node_zero, node_last] at hadj
    rw [← hadj, ← sum_sub_distrib]
    refine sum_congr rfl fun k _ => ?_
    rw [integral_sub intervalIntegrable_const (hf.intervalIntegrable _ _),
      intervalIntegral.integral_const, node_succ_sub]
  rw [← tendsto_sub_nhds_zero_iff]
  simp_rw [key]
  refine tendsto_sum_integral_nodes hs _ ?_
  intro ε hε
  have huc := (isCompact_Icc (a := (0 : ℝ)) (b := s)).uniformContinuousOn_of_continuous
    hf.continuousOn
  rw [Metric.uniformContinuousOn_iff] at huc
  obtain ⟨δ, hδ, hδ'⟩ := huc ε hε
  obtain ⟨N, hN⟩ := exists_mesh_lt hδ
  refine ⟨N, fun n hn k hk u hu => ?_⟩
  have hu' : u ∈ Set.Icc 0 s :=
    ⟨(node_nonneg hs n k).trans hu.1, hu.2.trans (node_le hs (by omega))⟩
  have hd : dist (node s n k) u < δ := by
    rw [Real.dist_eq, abs_sub_comm, abs_of_nonneg (by linarith [hu.1])]
    calc u - node s n k ≤ node s n (k + 1) - node s n k := by linarith [hu.2]
      _ = mesh s n := node_succ_sub s n k
      _ < δ := hN n hn
  have := hδ' _ (node_mem_Icc hs (by omega)) u hu' hd
  rw [dist_eq_norm] at this
  exact this.le

/-! ### Increment sums -/

/-- A differentiable matrix path applied to a constant vector. -/
theorem hasDerivAt_mulVec_const {M : ℝ → Matrix ι ι ℝ} {M' : Matrix ι ι ℝ} {s : ℝ}
    (hM : HasDerivAt M M' s) (v : ι → ℝ) :
    HasDerivAt (fun s => M s *ᵥ v) (M' *ᵥ v) s := by
  have h := hasDerivAt_matrix_mulVec hM (hasDerivAt_const s v)
  simpa using h

/-- **FTC for a matrix path applied to a vector**: `∫ₐᵇ F'(u) v du = F(b) v - F(a) v`. -/
theorem integral_deriv_mulVec_const {F F' : ℝ → Matrix ι ι ℝ} (hF : ∀ u, HasDerivAt F (F' u) u)
    (hF' : Continuous F') (v : ι → ℝ) (a b : ℝ) :
    ∫ u in a..b, F' u *ᵥ v = F b *ᵥ v - F a *ᵥ v :=
  integral_eq_sub_of_hasDerivAt (fun u _ => hasDerivAt_mulVec_const (hF u) v)
    ((hF'.matrix_mulVec continuous_const).intervalIntegrable a b)

/-- Summation by parts for one cell. -/
theorem incrementCell_eq (A B : Matrix ι ι ℝ) (v v' : ι → ℝ) :
    A *ᵥ (v' - v) = (B *ᵥ v' - A *ᵥ v) - (B - A) *ᵥ v' := by
  rw [Matrix.mulVec_sub, Matrix.sub_mulVec]
  abel

/-- **Increment sums converge to the integration-by-parts expression.** For a `C¹` matrix path
`F` and a continuous vector path `w`,
`∑ₖ F(uₖ) (w(uₖ₊₁) - w(uₖ)) → F(s) w(s) - F(0) w(0) - ∫₀ˢ F'(u) w(u) du`. -/
theorem tendsto_incrementSum {s : ℝ} (hs : 0 ≤ s) {F F' : ℝ → Matrix ι ι ℝ}
    (hF : ∀ u, HasDerivAt F (F' u) u) (hF' : Continuous F') {w : ℝ → ι → ℝ}
    (hw : Continuous w) :
    Tendsto (fun n => ∑ k ∈ range (n + 1),
        F (node s n k) *ᵥ (w (node s n (k + 1)) - w (node s n k))) atTop
      (𝓝 (F s *ᵥ w s - F 0 *ᵥ w 0 - ∫ u in (0 : ℝ)..s, F' u *ᵥ w u)) := by
  have hF'w : Continuous fun u => F' u *ᵥ w u := hF'.matrix_mulVec hw
  have key : ∀ n, (∑ k ∈ range (n + 1), F (node s n k) *ᵥ (w (node s n (k + 1)) - w (node s n k)))
      - (F s *ᵥ w s - F 0 *ᵥ w 0 - ∫ u in (0 : ℝ)..s, F' u *ᵥ w u)
      = ∑ k ∈ range (n + 1), ∫ u in node s n k..node s n (k + 1),
          F' u *ᵥ (w u - w (node s n (k + 1))) := by
    intro n
    have hadj := sum_integral_adjacent_intervals (μ := volume) (f := fun u => F' u *ᵥ w u)
      (a := node s n) (n := n + 1) (fun k _ => hF'w.intervalIntegrable (μ := volume) _ _)
    rw [node_zero, node_last] at hadj
    have htel := sum_range_sub (fun k => F (node s n k) *ᵥ w (node s n k)) (n + 1)
    rw [node_zero, node_last] at htel
    have hcell : ∀ k, F (node s n k) *ᵥ (w (node s n (k + 1)) - w (node s n k))
        = (F (node s n (k + 1)) *ᵥ w (node s n (k + 1)) - F (node s n k) *ᵥ w (node s n k))
          - ∫ u in node s n k..node s n (k + 1), F' u *ᵥ w (node s n (k + 1)) := by
      intro k
      rw [incrementCell_eq _ (F (node s n (k + 1))), Matrix.sub_mulVec,
        integral_deriv_mulVec_const hF hF']
    simp_rw [hcell]
    rw [sum_sub_distrib, htel, ← hadj, sub_sub_sub_cancel_left, ← sum_sub_distrib]
    refine sum_congr rfl fun k _ => ?_
    rw [← integral_sub (hF'w.intervalIntegrable _ _)
      ((hF'.matrix_mulVec continuous_const).intervalIntegrable _ _)]
    refine integral_congr fun u _ => ?_
    simp only [Matrix.mulVec_sub]
  rw [← tendsto_sub_nhds_zero_iff]
  simp_rw [key]
  refine tendsto_sum_integral_nodes hs _ ?_
  intro ε hε
  obtain ⟨C, hC⟩ : ∃ C, ∀ u ∈ Set.Icc (0 : ℝ) s, ‖F' u‖ ≤ C :=
    isCompact_Icc.exists_bound_of_continuousOn (E := Matrix ι ι ℝ) hF'.continuousOn
  set C' := max C 0 + 1 with hC'
  have hC'pos : 0 < C' := by positivity
  have hCle : ∀ u ∈ Set.Icc (0 : ℝ) s, ‖F' u‖ ≤ C' := fun u hu =>
    (hC u hu).trans (by linarith [le_max_left C 0])
  have huc := (isCompact_Icc (a := (0 : ℝ)) (b := s)).uniformContinuousOn_of_continuous
    hw.continuousOn
  rw [Metric.uniformContinuousOn_iff] at huc
  obtain ⟨δ, hδ, hδ'⟩ := huc (ε / C') (by positivity)
  obtain ⟨N, hN⟩ := exists_mesh_lt hδ
  refine ⟨N, fun n hn k hk u hu => ?_⟩
  have hu' : u ∈ Set.Icc 0 s :=
    ⟨(node_nonneg hs n k).trans hu.1, hu.2.trans (node_le hs (by omega))⟩
  have hd : dist u (node s n (k + 1)) < δ := by
    rw [Real.dist_eq, abs_sub_comm, abs_of_nonneg (by linarith [hu.2])]
    calc node s n (k + 1) - u ≤ node s n (k + 1) - node s n k := by linarith [hu.1]
      _ = mesh s n := node_succ_sub s n k
      _ < δ := hN n hn
  have hw' := hδ' u hu' _ (node_mem_Icc hs (by omega)) hd
  rw [dist_eq_norm] at hw'
  calc ‖F' u *ᵥ (w u - w (node s n (k + 1)))‖
      ≤ ‖F' u‖ * ‖w u - w (node s n (k + 1))‖ := linfty_opNorm_mulVec _ _
    _ ≤ C' * (ε / C') := mul_le_mul (hCle u hu') hw'.le (norm_nonneg _) hC'pos.le
    _ = ε := mul_div_cancel₀ ε hC'pos.ne'

/-! ### The OU increment sums -/

/-- `d/du (e^{-(s-u)H} σ) = e^{-(s-u)H} H σ`. -/
theorem hasDerivAt_ouFlow_shift (H σ : Matrix ι ι ℝ) (s u : ℝ) :
    HasDerivAt (fun u => ouFlow H (s - u) * σ) (ouFlow H (s - u) * H * σ) u := by
  have h := ((hasDerivAt_ouFlow_neg H u).const_mul (ouFlow H s)).mul_const σ
  have hfun : (fun u => ouFlow H (s - u) * σ) = fun u => ouFlow H s * ouFlow H (-u) * σ := by
    funext u
    rw [sub_eq_add_neg, ouFlow_add]
  rw [hfun]
  refine h.congr_deriv ?_
  rw [sub_eq_add_neg, ouFlow_add, ouFlow_comm]
  simp only [Matrix.mul_assoc]

theorem continuous_ouFlow_shift (H σ : Matrix ι ι ℝ) (s : ℝ) :
    Continuous fun u => ouFlow H (s - u) * H * σ :=
  (((continuous_ouFlow H).comp (continuous_const.sub continuous_id)).mul continuous_const).mul
    continuous_const

/-- **The OU increment sums converge to the pathwise solution.** For a continuous path with
`w 0 = 0`, `∑ₖ e^{-(s-uₖ)H} σ (w(uₖ₊₁) - w(uₖ)) → X_s - e^{-sH} x₀` where `X = ouSol`. -/
theorem tendsto_ouIncrementSum (H σ : Matrix ι ι ℝ) (x₀ : ι → ℝ) {w : ℝ → ι → ℝ}
    (hw : Continuous w) (hw0 : w 0 = 0) {s : ℝ} (hs : 0 ≤ s) :
    Tendsto (fun n => ∑ k ∈ range (n + 1),
        (ouFlow H (s - node s n k) * σ) *ᵥ (w (node s n (k + 1)) - w (node s n k))) atTop
      (𝓝 (ouSol H σ x₀ w s - ouFlow H s *ᵥ x₀)) := by
  have h := tendsto_incrementSum hs (fun u => hasDerivAt_ouFlow_shift H σ s u)
    (continuous_ouFlow_shift H σ s) hw
  convert h using 2
  simp only [ouSol, sub_self, ouFlow_zero, Matrix.one_mul, hw0, Matrix.mulVec_zero, sub_zero]
  abel

end

end Laplace.Patterning
