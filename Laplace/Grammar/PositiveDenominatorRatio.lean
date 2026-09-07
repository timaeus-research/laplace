/-
Copyright (c) 2026 Timaeus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Laplace.Grammar.ApproxInDistribution

/-!
# Quotients of jointly convergent random variables with positive limiting denominator

If `(U_n, V_n) ⇒ (U, V)` in `ℝ²` and `V > 0` a.s., then `U_n / V_n ⇒ U / V`
(`tendstoInDistribution_div_of_pos`). Division is not continuous at `v = 0`, so the continuous
mapping theorem does not apply directly; instead we divide by `max v c` (continuous), which agrees
with division on `{v ≥ c}`. By portmanteau on the closed half-line `{v ≤ c}` the disagreement
probability is eventually at most `μ' {V ≤ c}`, which is small for small `c` since `V > 0` a.s.;
the approximation lemma of unit 156 then gives the claim (Astra #13, route R1). Lean's totalised
division is used throughout: no finite-`n` nonvanishing is required. Zero `sorry`/`axiom`.
-/

open MeasureTheory Filter Topology

namespace Laplace.Grammar

variable {ι Ω Ω' : Type*} [MeasurableSpace Ω] [MeasurableSpace Ω'] {μ : Measure Ω}
  [IsProbabilityMeasure μ] {μ' : Measure Ω'} [IsProbabilityMeasure μ'] {l : Filter ι}

/-- Clipped division `u / max v c`, continuous for `c > 0`. -/
noncomputable def clipDiv (c : ℝ) (p : ℝ × ℝ) : ℝ := p.1 / max p.2 c

theorem continuous_clipDiv (c : ℝ) (hc : 0 < c) : Continuous (clipDiv c) := by
  unfold clipDiv
  exact continuous_fst.div (continuous_snd.max continuous_const)
    fun p => (lt_max_of_lt_right hc).ne'

theorem clipDiv_eq (c : ℝ) (p : ℝ × ℝ) (h : c ≤ p.2) : clipDiv c p = p.1 / p.2 := by
  unfold clipDiv
  rw [max_eq_left h]

/-- The tail `μ' {V ≤ 1/(m+1)}` tends to `μ' {V ≤ 0}`, which is `0` when `V > 0` a.s. -/
theorem tendsto_measure_le_inv_atTop (V : Ω' → ℝ) (hV : Measurable V) (hpos : ∀ᵐ ω ∂μ', 0 < V ω) :
    Tendsto (fun m : ℕ => μ' {ω | V ω ≤ 1 / ((m : ℝ) + 1)}) atTop (𝓝 0) := by
  have hnull : ∀ m : ℕ, NullMeasurableSet {ω | V ω ≤ 1 / ((m : ℝ) + 1)} μ' :=
    fun m => (hV measurableSet_Iic).nullMeasurableSet
  have hanti : Antitone fun m : ℕ => {ω | V ω ≤ 1 / ((m : ℝ) + 1)} := by
    intro m m' hmm' ω hω
    simp only [Set.mem_ofPred_eq] at hω ⊢
    refine hω.trans (one_div_le_one_div_of_le (by positivity) ?_)
    exact_mod_cast Nat.succ_le_succ hmm'
  have h := tendsto_measure_iInter_atTop (μ := μ') hnull hanti ⟨0, measure_ne_top _ _⟩
  have hinter : (⋂ m : ℕ, {ω | V ω ≤ 1 / ((m : ℝ) + 1)}) ⊆ {ω | V ω ≤ 0} := by
    intro ω hω
    simp only [Set.mem_iInter, Set.mem_ofPred_eq] at hω ⊢
    by_contra hlt
    push Not at hlt
    obtain ⟨m, hm⟩ := exists_nat_one_div_lt hlt
    exact absurd (hω m) (not_le.2 hm)
  have hzero : μ' {ω | V ω ≤ 0} = 0 := by
    rw [← nonpos_iff_eq_zero]
    calc μ' {ω | V ω ≤ 0} ≤ μ' {ω | ¬ 0 < V ω} := measure_mono fun ω hω => not_lt.2 hω
      _ = 0 := hpos
  have : μ' (⋂ m : ℕ, {ω | V ω ≤ 1 / ((m : ℝ) + 1)}) = 0 :=
    le_antisymm ((measure_mono hinter).trans hzero.le) zero_le
  rw [this] at h
  exact h

variable [l.IsCountablyGenerated]

/-- **Quotient theorem**: joint convergence in distribution with an a.s. positive limiting
denominator implies convergence in distribution of the quotients (totalised division). -/
theorem tendstoInDistribution_div_of_pos (U V : ι → Ω → ℝ) (U₀ V₀ : Ω' → ℝ)
    (hU : ∀ n, Measurable (U n)) (hV : ∀ n, Measurable (V n)) (hU₀ : Measurable U₀)
    (hV₀ : Measurable V₀)
    (hUV : TendstoInDistribution (fun n ω => (U n ω, V n ω)) l (fun ω => (U₀ ω, V₀ ω))
      (fun _ => μ) μ')
    (hpos : ∀ᵐ ω ∂μ', 0 < V₀ ω) :
    TendstoInDistribution (fun n ω => U n ω / V n ω) l (fun ω => U₀ ω / V₀ ω) (fun _ => μ) μ' := by
  refine tendstoInDistribution_of_approx _ _ (fun n => (hU n).div (hV n)) (hU₀.div hV₀)
    fun η hη => ?_
  -- choose the clipping level
  have hhalf : (0 : ENNReal) < ENNReal.ofReal (η / 2) := by
    rw [ENNReal.ofReal_pos]; positivity
  obtain ⟨m, hm⟩ := ((tendsto_measure_le_inv_atTop V₀ hV₀ hpos).eventually
    (gt_mem_nhds hhalf)).exists
  set c : ℝ := 1 / ((m : ℝ) + 1) with hcdef
  have hc : 0 < c := by positivity
  -- the denominators converge in distribution, and portmanteau on the closed half-line
  have hVd : TendstoInDistribution V l V₀ (fun _ => μ) μ' :=
    (hUV.continuous_comp (g := fun p : ℝ × ℝ => p.2) continuous_snd).congr
      (fun n => Filter.Eventually.of_forall fun ω => rfl) (Filter.Eventually.of_forall fun ω => rfl)
  have hport := ProbabilityMeasure.limsup_measure_closed_le_of_tendsto hVd.tendsto
    (isClosed_Iic (a := c))
  simp only [ProbabilityMeasure.coe_mk] at hport
  have hmap : ∀ n, (μ.map (V n)) (Set.Iic c) = μ (V n ⁻¹' Set.Iic c) := fun n =>
    Measure.map_apply_of_aemeasurable (hV n).aemeasurable measurableSet_Iic
  simp only [hmap, Measure.map_apply_of_aemeasurable hV₀.aemeasurable measurableSet_Iic] at hport
  have hVc : μ' (V₀ ⁻¹' Set.Iic c) < ENNReal.ofReal (η / 2) := hm
  have hlt : limsup (fun n => μ (V n ⁻¹' Set.Iic c)) l < ENNReal.ofReal η := by
    refine lt_of_le_of_lt hport (lt_of_lt_of_le hVc (ENNReal.ofReal_le_ofReal (by linarith)))
  have hev := eventually_lt_of_limsup_lt hlt
  refine ⟨fun n ω => clipDiv c (U n ω, V n ω), fun ω => clipDiv c (U₀ ω, V₀ ω),
    fun n => (continuous_clipDiv c hc).measurable.comp ((hU n).prodMk (hV n)),
    (continuous_clipDiv c hc).measurable.comp (hU₀.prodMk hV₀),
    hUV.continuous_comp (continuous_clipDiv c hc), ?_, ?_⟩
  · filter_upwards [hev] with n hn
    refine le_trans (measure_mono ?_) hn.le
    intro ω hω
    simp only [Set.mem_ofPred_eq] at hω
    show V n ω ∈ Set.Iic c
    rw [Set.mem_Iic]
    by_contra hcon
    exact hω (clipDiv_eq c (U n ω, V n ω) (not_le.1 hcon).le).symm
  · refine le_trans (measure_mono ?_) (hVc.le.trans (ENNReal.ofReal_le_ofReal (by linarith)))
    intro ω hω
    simp only [Set.mem_ofPred_eq] at hω
    show V₀ ω ∈ Set.Iic c
    rw [Set.mem_Iic]
    by_contra hcon
    exact hω (clipDiv_eq c (U₀ ω, V₀ ω) (not_le.1 hcon).le).symm

end Laplace.Grammar
