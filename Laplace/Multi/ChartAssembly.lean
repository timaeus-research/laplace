/-
Copyright (c) 2026 Timaeus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Timaeus
-/
import Mathlib
import Laplace.Multi.WellCompetition

/-!
# Finite-chart assembly

The assembly interface of the relative push-forward statement (germbij_slop S14): the partition
function and an energy or observable numerator are finite sums of chart contributions plus
remainders. Each chart contribution has a positive normalisation `L i t` against which it converges
(`Z i t / L i t → C i > 0`, `Q i t / L i t → J i`), and the remainders are `o(∑ L i t)`. Then the
normalised statistic `(∑ Q + R_Q) / (∑ Z + R_Z)` is asymptotic to the `L`-weighted average
`(∑ L i t · J i) / (∑ L i t · C i)` (`ChartAssembly.tendsto_sub`). This is resolution-invariant
without any bijection between charts and layers: two chart systems that both satisfy the interface
give the same limit. Corollaries: two charts with a convergent mass ratio (`two_chart_limit`), a
dominated chart (`dominated_chart_limit`), and the hump of `WellCompetition.lean` as the assembly of
two Morse wells with an energy offset (`hump_of_assembly`).
-/

open Real Filter Topology

namespace Laplace.Multi

/-- Standing hypotheses of the finite-chart assembly along a schedule `t → ∞`. -/
structure ChartAssembly {ι : Type*} [Fintype ι] (L Z Q : ι → ℝ → ℝ) (C J : ι → ℝ) (RZ RQ : ℝ → ℝ)
    (c₀ MJ : ℝ) : Prop where
  hc₀ : 0 < c₀
  L_pos : ∀ᶠ t in atTop, ∀ i, 0 < L i t
  C_lb : ∀ i, c₀ ≤ C i
  J_bd : ∀ i, |J i| ≤ MJ
  Z_lim : ∀ i, Tendsto (fun t ↦ Z i t / L i t) atTop (𝓝 (C i))
  Q_lim : ∀ i, Tendsto (fun t ↦ Q i t / L i t) atTop (𝓝 (J i))
  RZ_lim : Tendsto (fun t ↦ RZ t / ∑ i, L i t) atTop (𝓝 0)
  RQ_lim : Tendsto (fun t ↦ RQ t / ∑ i, L i t) atTop (𝓝 0)

namespace ChartAssembly

variable {ι : Type*} [Fintype ι] {L Z Q : ι → ℝ → ℝ} {C J : ι → ℝ} {RZ RQ : ℝ → ℝ} {c₀ MJ : ℝ}

/-- `(∑ X i t + R t) / ∑ L i t − (∑ L i t · Xl i) / ∑ L i t → 0` whenever `X i t / L i t → Xl i`
and `R = o(∑ L)`. -/
theorem tendsto_weighted_sub [Nonempty ι] (hL : ∀ᶠ t in atTop, ∀ i, 0 < L i t) {X : ι → ℝ → ℝ}
    {Xl : ι → ℝ}
    (hX : ∀ i, Tendsto (fun t ↦ X i t / L i t) atTop (𝓝 (Xl i))) {R : ℝ → ℝ}
    (hR : Tendsto (fun t ↦ R t / ∑ i, L i t) atTop (𝓝 0)) :
    Tendsto (fun t ↦ (∑ i, X i t + R t) / ∑ i, L i t - (∑ i, L i t * Xl i) / ∑ i, L i t) atTop
      (𝓝 0) := by
  have hterm : ∀ i, Tendsto (fun t ↦ L i t / (∑ j, L j t) * (X i t / L i t - Xl i)) atTop
      (𝓝 0) := by
    intro i
    have h0 : Tendsto (fun t ↦ X i t / L i t - Xl i) atTop (𝓝 0) := by
      simpa using (hX i).sub_const (Xl i)
    have hbd : IsBoundedUnder (· ≤ ·) atTop (norm ∘ fun t ↦ L i t / ∑ j, L j t) := by
      refine isBoundedUnder_of_eventually_le (a := 1) ?_
      filter_upwards [hL] with t ht
      have hS : 0 < ∑ j, L j t := Finset.sum_pos (fun j _ ↦ ht j) Finset.univ_nonempty
      simp only [Function.comp, Real.norm_eq_abs]
      rw [abs_of_nonneg (div_nonneg (ht i).le hS.le), div_le_one hS]
      exact Finset.single_le_sum (fun j _ ↦ (ht j).le) (Finset.mem_univ i)
    refine (h0.zero_mul_isBoundedUnder_le hbd).congr' (Filter.Eventually.of_forall fun t ↦ ?_)
    simp only
    ring
  have hsum := (tendsto_finsetSum Finset.univ fun i _ ↦ hterm i).add hR
  rw [add_zero, Finset.sum_const_zero] at hsum
  refine hsum.congr' ?_
  filter_upwards [hL] with t ht
  have hS : (∑ j, L j t) ≠ 0 := (Finset.sum_pos (fun j _ ↦ ht j) Finset.univ_nonempty).ne'
  have hpt : ∀ c, (L c t / ∑ j, L j t) * (X c t / L c t - Xl c) =
      (X c t - L c t * Xl c) / ∑ j, L j t := fun c ↦ by
    have hLc : L c t ≠ 0 := (ht c).ne'
    field_simp
  rw [Finset.sum_congr rfl fun c _ ↦ hpt c, ← Finset.sum_div, Finset.sum_sub_distrib]
  ring

/-- **Assembly.** The normalised statistic is asymptotic to the `L`-weighted average of the chart
limits. -/
theorem tendsto_sub [Nonempty ι] (hd : ChartAssembly L Z Q C J RZ RQ c₀ MJ) :
    Tendsto (fun t ↦ (∑ i, Q i t + RQ t) / (∑ i, Z i t + RZ t) -
      (∑ i, L i t * J i) / ∑ i, L i t * C i) atTop (𝓝 0) := by
  have hA0 := tendsto_weighted_sub hd.L_pos hd.Q_lim hd.RQ_lim
  have hB0 := tendsto_weighted_sub hd.L_pos hd.Z_lim hd.RZ_lim
  -- opaque names for the normalised quantities
  obtain ⟨S, hS⟩ : ∃ S : ℝ → ℝ, S = fun t ↦ ∑ i, L i t := ⟨_, rfl⟩
  obtain ⟨A, hA'⟩ : ∃ A : ℝ → ℝ, A = fun t ↦ (∑ i, Q i t + RQ t) / S t := ⟨_, rfl⟩
  obtain ⟨B, hB'⟩ : ∃ B : ℝ → ℝ, B = fun t ↦ (∑ i, Z i t + RZ t) / S t := ⟨_, rfl⟩
  obtain ⟨A', hA''⟩ : ∃ A' : ℝ → ℝ, A' = fun t ↦ (∑ i, L i t * J i) / S t := ⟨_, rfl⟩
  obtain ⟨B', hB''⟩ : ∃ B' : ℝ → ℝ, B' = fun t ↦ (∑ i, L i t * C i) / S t := ⟨_, rfl⟩
  have hA : Tendsto (fun t ↦ A t - A' t) atTop (𝓝 0) :=
    hA0.congr' (Filter.Eventually.of_forall fun t ↦ by simp only [hA', hA'', hS])
  have hB : Tendsto (fun t ↦ B t - B' t) atTop (𝓝 0) :=
    hB0.congr' (Filter.Eventually.of_forall fun t ↦ by simp only [hB', hB'', hS])
  have hSpos : ∀ᶠ t in atTop, 0 < S t := by
    filter_upwards [hd.L_pos] with t ht
    rw [hS]
    exact Finset.sum_pos (fun j _ ↦ ht j) Finset.univ_nonempty
  have hB'lb : ∀ᶠ t in atTop, c₀ ≤ B' t := by
    filter_upwards [hd.L_pos, hSpos] with t ht hSt
    rw [hB'', le_div_iff₀ hSt, hS, Finset.mul_sum]
    exact Finset.sum_le_sum fun i _ ↦ by
      rw [mul_comm]; exact mul_le_mul_of_nonneg_left (hd.C_lb i) (ht i).le
  have hA'bd : ∀ᶠ t in atTop, |A' t| ≤ MJ := by
    filter_upwards [hd.L_pos, hSpos] with t ht hSt
    rw [hA'', abs_div, abs_of_pos hSt, div_le_iff₀ hSt]
    calc |∑ i, L i t * J i| ≤ ∑ i, |L i t * J i| := Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ i, L i t * MJ := Finset.sum_le_sum fun i _ ↦ by
          rw [abs_mul, abs_of_pos (ht i)]
          exact mul_le_mul_of_nonneg_left (hd.J_bd i) (ht i).le
      _ = MJ * S t := by
          rw [hS, Finset.mul_sum]
          exact Finset.sum_congr rfl fun i _ ↦ mul_comm _ _
  have hBlb : ∀ᶠ t in atTop, c₀ / 2 ≤ B t := by
    have := hB.eventually (Metric.closedBall_mem_nhds (0 : ℝ) (half_pos hd.hc₀))
    filter_upwards [this, hB'lb] with t ht ht'
    rw [dist_zero_right, Real.norm_eq_abs, abs_le] at ht
    linarith [ht.1]
  -- the identity `A/B − A'/B' = (A − A')/B + A' (B' − B)/(B B')`
  have h1 : Tendsto (fun t ↦ (A t - A' t) / B t) atTop (𝓝 0) := by
    have hbd : IsBoundedUnder (· ≤ ·) atTop (norm ∘ fun t ↦ (B t)⁻¹) := by
      refine isBoundedUnder_of_eventually_le (a := 2 / c₀) ?_
      filter_upwards [hBlb] with t ht
      simp only [Function.comp, Real.norm_eq_abs]
      have hBpos : 0 < B t := lt_of_lt_of_le (half_pos hd.hc₀) ht
      rw [abs_inv, abs_of_pos hBpos, inv_le_comm₀ hBpos (div_pos two_pos hd.hc₀), inv_div]
      exact ht
    refine (hA.zero_mul_isBoundedUnder_le hbd).congr' (Filter.Eventually.of_forall fun t ↦ ?_)
    simp only [div_eq_mul_inv]
  have h2 : Tendsto (fun t ↦ A' t / (B t * B' t) * (B' t - B t)) atTop (𝓝 0) := by
    have hB0' : Tendsto (fun t ↦ B' t - B t) atTop (𝓝 0) := by
      have := hB.neg
      rw [neg_zero] at this
      exact this.congr' (Filter.Eventually.of_forall fun t ↦ by ring)
    have hbd : IsBoundedUnder (· ≤ ·) atTop (norm ∘ fun t ↦ A' t / (B t * B' t)) := by
      refine isBoundedUnder_of_eventually_le (a := MJ / (c₀ / 2 * c₀)) ?_
      filter_upwards [hBlb, hB'lb, hA'bd] with t ht ht' hA'
      simp only [Function.comp, Real.norm_eq_abs]
      have hBpos : 0 < B t := lt_of_lt_of_le (half_pos hd.hc₀) ht
      have hB'pos : 0 < B' t := lt_of_lt_of_le hd.hc₀ ht'
      rw [abs_div, abs_of_pos (mul_pos hBpos hB'pos), div_le_div_iff₀ (mul_pos hBpos hB'pos)
        (mul_pos (half_pos hd.hc₀) hd.hc₀)]
      have hMJ : 0 ≤ MJ := (abs_nonneg _).trans hA'
      exact mul_le_mul hA' (mul_le_mul ht ht' hd.hc₀.le hBpos.le)
        (mul_pos (half_pos hd.hc₀) hd.hc₀).le hMJ
    refine (hB0'.zero_mul_isBoundedUnder_le hbd).congr' (Filter.Eventually.of_forall fun t ↦ ?_)
    simp only
    ring
  have hsum := h1.add h2
  rw [add_zero] at hsum
  refine hsum.congr' ?_
  filter_upwards [hBlb, hB'lb, hSpos] with t ht ht' hSt
  have hBpos : 0 < B t := lt_of_lt_of_le (half_pos hd.hc₀) ht
  have hB'pos : 0 < B' t := lt_of_lt_of_le hd.hc₀ ht'
  have e1 : (∑ i, Q i t + RQ t) / (∑ i, Z i t + RZ t) = A t / B t := by
    rw [hA', hB']
    simp only
    rw [div_div_div_cancel_right₀ hSt.ne']
  have e2 : (∑ i, L i t * J i) / ∑ i, L i t * C i = A' t / B' t := by
    rw [hA'', hB'']
    simp only
    rw [div_div_div_cancel_right₀ hSt.ne']
  rw [e1, e2]
  field_simp
  ring

end ChartAssembly

/-- **Two charts with a convergent mass ratio.** If `L₂/L₁ → ρ ≥ 0`, the statistic converges to
`(J₁ + ρ J₂)/(C₁ + ρ C₂)`. -/
theorem two_chart_limit {L Z Q : Fin 2 → ℝ → ℝ} {C J : Fin 2 → ℝ} {RZ RQ : ℝ → ℝ} {c₀ MJ : ℝ}
    (hd : ChartAssembly L Z Q C J RZ RQ c₀ MJ) {ρ : ℝ} (hρ : 0 ≤ ρ)
    (hrat : Tendsto (fun t ↦ L 1 t / L 0 t) atTop (𝓝 ρ)) :
    Tendsto (fun t ↦ (∑ i, Q i t + RQ t) / (∑ i, Z i t + RZ t)) atTop
      (𝓝 ((J 0 + ρ * J 1) / (C 0 + ρ * C 1))) := by
  have hmain := hd.tendsto_sub
  have hC0 : 0 < C 0 := lt_of_lt_of_le hd.hc₀ (hd.C_lb 0)
  have hC1 : 0 < C 1 := lt_of_lt_of_le hd.hc₀ (hd.C_lb 1)
  have hden : C 0 + ρ * C 1 ≠ 0 := by positivity
  have hw : Tendsto (fun t ↦ (∑ i, L i t * J i) / ∑ i, L i t * C i) atTop
      (𝓝 ((J 0 + ρ * J 1) / (C 0 + ρ * C 1))) := by
    have := ((hrat.const_mul (J 1)).const_add (J 0)).div
      ((hrat.const_mul (C 1)).const_add (C 0)) (by rw [mul_comm]; exact hden)
    rw [mul_comm ρ (J 1), mul_comm ρ (C 1)]
    refine this.congr' ?_
    filter_upwards [hd.L_pos] with t ht
    have h0 : L 0 t ≠ 0 := (ht 0).ne'
    simp only [Fin.sum_univ_two, Pi.div_apply]
    field_simp
  have := hmain.add hw
  rw [zero_add] at this
  exact this.congr' (Filter.Eventually.of_forall fun t ↦ by ring)

/-- **A dominated chart.** If `L₂ = o(L₁)` the second chart is invisible: the statistic converges to
`J₁/C₁`. -/
theorem dominated_chart_limit {L Z Q : Fin 2 → ℝ → ℝ} {C J : Fin 2 → ℝ} {RZ RQ : ℝ → ℝ} {c₀ MJ : ℝ}
    (hd : ChartAssembly L Z Q C J RZ RQ c₀ MJ)
    (hrat : Tendsto (fun t ↦ L 1 t / L 0 t) atTop (𝓝 0)) :
    Tendsto (fun t ↦ (∑ i, Q i t + RQ t) / (∑ i, Z i t + RZ t)) atTop (𝓝 (J 0 / C 0)) := by
  have := two_chart_limit hd le_rfl hrat
  simpa using this

/-- **The hump from assembly.** Two Morse wells of equal mass constant, the second lifted by the
energy offset `z` (`L 1 t = L 0 t · e^{-z}`, `J 0 = C/2`, `J 1 = C (1/2 + z)`): the energy converges
to `1/2 + z/(1 + e^z)`. -/
theorem hump_of_assembly {L Z Q : Fin 2 → ℝ → ℝ} {Cw : ℝ} {J : Fin 2 → ℝ} {RZ RQ : ℝ → ℝ}
    {c₀ MJ z : ℝ} (hd : ChartAssembly L Z Q (fun _ ↦ Cw) J RZ RQ c₀ MJ)
    (hL : ∀ t, L 1 t = L 0 t * Real.exp (-z)) (hJ0 : J 0 = 1 / 2 * Cw)
    (hJ1 : J 1 = (1 / 2 + z) * Cw) :
    Tendsto (fun t ↦ (∑ i, Q i t + RQ t) / (∑ i, Z i t + RZ t)) atTop (𝓝 (humpProfile z)) := by
  have hCw : 0 < Cw := lt_of_lt_of_le hd.hc₀ (hd.C_lb 0)
  have hrat : Tendsto (fun t ↦ L 1 t / L 0 t) atTop (𝓝 (Real.exp (-z))) := by
    refine tendsto_const_nhds.congr' ?_
    filter_upwards [hd.L_pos] with t ht
    rw [hL, mul_div_cancel_left₀ _ (ht 0).ne']
  have := two_chart_limit hd (Real.exp_pos _).le hrat
  rw [hJ0, hJ1] at this
  have heq : (1 / 2 * Cw + Real.exp (-z) * ((1 / 2 + z) * Cw)) / (Cw + Real.exp (-z) * Cw) =
      humpProfile z := by
    rw [← twoWell_energy_eq_hump hCw]
    congr 1 <;> ring
  rw [← heq]
  exact this

end Laplace.Multi
