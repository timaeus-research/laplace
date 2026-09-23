/-
Copyright (c) 2026 Timaeus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Timaeus
-/
import Laplace.Multi.ChartAssembly
import Laplace.Multi.PowerLogDominance

/-!
# Finite dominant-cluster assembly

The general form of `ChartAssembly.dominated_chart_limit`: with a reference chart `i₀` and
`L i / L i₀ → d i ≥ 0`, the assembled ratio converges to `(∑ d i J i)/(∑ d i C i)`
(`ChartAssembly.cluster_limit`): the dominant cluster is the set of charts with `d i > 0`, their
constants add, and the others are absorbed. For power–log normalisations `k i · t^{-λ i} (log t)^{r i}`
the weights are `k i / k i₀` on the charts sharing the minimal pair `(λ, r)` (smaller `λ` wins,
then larger `r`) and `0` elsewhere (`ChartAssembly.powLog_cluster_limit`). Ties add constants and
never create a logarithm.
-/

open Real Filter Topology

namespace Laplace.Multi

namespace ChartAssembly

variable {ι : Type*} [Fintype ι] {L Z Q : ι → ℝ → ℝ} {C J : ι → ℝ} {RZ RQ : ℝ → ℝ} {c₀ MJ : ℝ}

/-- **Finite dominant-cluster assembly.** -/
theorem cluster_limit [Nonempty ι] (hd : ChartAssembly L Z Q C J RZ RQ c₀ MJ) (i₀ : ι)
    {d : ι → ℝ} (hd0 : ∀ i, 0 ≤ d i)
    (hrat : ∀ i, Tendsto (fun t ↦ L i t / L i₀ t) atTop (𝓝 (d i))) :
    Tendsto (fun t ↦ (∑ i, Q i t + RQ t) / (∑ i, Z i t + RZ t)) atTop
      (𝓝 ((∑ i, d i * J i) / ∑ i, d i * C i)) := by
  have hmain := hd.tendsto_sub
  have hdi₀ : d i₀ = 1 := by
    have h1 : Tendsto (fun t ↦ L i₀ t / L i₀ t) atTop (𝓝 1) := by
      refine tendsto_const_nhds.congr' ?_
      filter_upwards [hd.L_pos] with t ht
      exact (div_self (ht i₀).ne').symm
    exact tendsto_nhds_unique (hrat i₀) h1
  have hC : ∀ i, 0 < C i := fun i ↦ lt_of_lt_of_le hd.hc₀ (hd.C_lb i)
  have hden : 0 < ∑ i, d i * C i :=
    Finset.sum_pos' (fun i _ ↦ mul_nonneg (hd0 i) (hC i).le)
      ⟨i₀, Finset.mem_univ _, by rw [hdi₀, one_mul]; exact hC i₀⟩
  have hnum : Tendsto (fun t ↦ ∑ i, L i t / L i₀ t * J i) atTop (𝓝 (∑ i, d i * J i)) :=
    tendsto_finsetSum _ fun i _ ↦ (hrat i).mul_const _
  have hden' : Tendsto (fun t ↦ ∑ i, L i t / L i₀ t * C i) atTop (𝓝 (∑ i, d i * C i)) :=
    tendsto_finsetSum _ fun i _ ↦ (hrat i).mul_const _
  have htarget : Tendsto (fun t ↦ (∑ i, L i t * J i) / ∑ i, L i t * C i) atTop
      (𝓝 ((∑ i, d i * J i) / ∑ i, d i * C i)) := by
    refine (hnum.div hden' hden.ne').congr' ?_
    filter_upwards [hd.L_pos] with t ht
    have h0 : L i₀ t ≠ 0 := (ht i₀).ne'
    have e : ∀ X : ι → ℝ, ∑ i, L i t / L i₀ t * X i = (∑ i, L i t * X i) / L i₀ t := by
      intro X
      rw [Finset.sum_div]
      exact Finset.sum_congr rfl fun i _ ↦ by rw [div_mul_eq_mul_div]
    simp only [Pi.div_apply, e, div_div_div_cancel_right₀ h0]
  have h := hmain.add htarget
  rw [zero_add] at h
  exact h.congr' (Eventually.of_forall fun t ↦ sub_add_cancel _ _)

/-- **Power–log cluster assembly.** With `L i = k i · powLog (lam i) (r i)` and `i₀` carrying the
winning pair (smallest `lam`, then largest `r`), the ratio converges to the weighted average over the
charts sharing the winning pair. -/
theorem powLog_cluster_limit [Nonempty ι] {k lam r : ι → ℝ} (hk : ∀ i, 0 < k i)
    (hd : ChartAssembly (fun i t ↦ k i * powLog (lam i) (r i) t) Z Q C J RZ RQ c₀ MJ) (i₀ : ι)
    (hmin : ∀ i, lam i₀ < lam i ∨ (lam i₀ = lam i ∧ r i ≤ r i₀)) :
    Tendsto (fun t ↦ (∑ i, Q i t + RQ t) / (∑ i, Z i t + RZ t)) atTop
      (𝓝 ((∑ i, (if lam i = lam i₀ ∧ r i = r i₀ then k i / k i₀ else 0) * J i) /
        ∑ i, (if lam i = lam i₀ ∧ r i = r i₀ then k i / k i₀ else 0) * C i)) := by
  classical
  refine hd.cluster_limit i₀ (fun i ↦ ?_) fun i ↦ ?_
  · split_ifs
    · exact (div_pos (hk i) (hk i₀)).le
    · exact le_rfl
  · by_cases h : lam i = lam i₀ ∧ r i = r i₀
    · rw [if_pos h, h.1, h.2]
      refine tendsto_const_nhds.congr' ?_
      filter_upwards [eventually_gt_atTop (1 : ℝ)] with t ht
      rw [mul_div_mul_right _ _ (powLog_pos ht).ne']
    · rw [if_neg h]
      have hlt : lam i₀ < lam i ∨ (lam i₀ = lam i ∧ r i < r i₀) := by
        rcases hmin i with h1 | ⟨h1, h2⟩
        · exact Or.inl h1
        · exact Or.inr ⟨h1, lt_of_le_of_ne h2 fun h3 ↦ h ⟨h1.symm, h3⟩⟩
      have h0 := (tendsto_powLog_div_powLog hlt).const_mul (k i / k i₀)
      rw [mul_zero] at h0
      refine h0.congr' (Eventually.of_forall fun t ↦ ?_)
      beta_reduce
      rw [mul_div_mul_comm]

end ChartAssembly

end Laplace.Multi
