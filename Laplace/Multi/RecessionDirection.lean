/-
Copyright (c) 2026 Timaeus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Timaeus
-/
import Laplace.Multi.RecessionObstruction

/-!
# The general recession direction

The recession-cone obstruction of `RecessionObstruction` along an arbitrary direction `d`. If the
domain `L` is invariant under the flow `u ↦ e^{s d} ⊙ u` (`s ≥ 0`), contains a box, the phase is
bounded by `K ∏ u^κ` with `d · κ ≤ 0`, and `d · (r + 1) ≥ 0`, then `1_L ∏ u^r e^{-Φ}` is not
integrable (`not_integrable_of_recession_direction`). The proof does not use shells: the tail sets
`A_n = L ∩ {n |d|² + m₀ ≤ ⟨d, log u⟩}` decrease to `∅`, so the tail integrals of an integrable
function tend to `0`, while the transported box `e^{n d} ⊙ K₀ ⊆ A_n` carries mass at least
`e^{n d·(r+1)} J₀ ≥ J₀ > 0` by the change of variables `u ↦ e^{n d} ⊙ u`.

For the limiting domain of the dominant-scale analysis this gives
`not_integrable_envelope_of_recession_direction`: any direction `d ≠ 0` supported on the scaled
coordinates with `d · κ ≤ 0` and `d · (r + 1) ≥ 0` forbids the profile certificate.
-/

open Real MeasureTheory Set Filter Topology
open scoped ENNReal

namespace Laplace.Multi

variable {ι : Type*} [Fintype ι]

/-- The flow `u ↦ e^{s d} ⊙ u` along the direction `d`. -/
noncomputable def flow (d : ι → ℝ) (s : ℝ) (u : ι → ℝ) : ι → ℝ := fun i ↦ exp (s * d i) * u i

omit [Fintype ι] in
theorem flow_eq_rescale (d : ι → ℝ) (s : ℝ) (u : ι → ℝ) : flow d s u = rescale (exp s) (-d) u := by
  funext i
  unfold flow rescale
  rw [Pi.neg_apply, neg_neg, ← Real.exp_mul]

omit [Fintype ι] in
theorem flow_flow (d : ι → ℝ) (s t : ℝ) (u : ι → ℝ) : flow d s (flow d t u) = flow d (s + t) u := by
  funext i
  simp only [flow]
  rw [← mul_assoc, ← Real.exp_add, add_mul]

omit [Fintype ι] in
theorem flow_zero (d : ι → ℝ) (u : ι → ℝ) : flow d 0 u = u := by
  funext i
  simp [flow]

omit [Fintype ι] in
theorem flow_pos (d : ι → ℝ) (s : ℝ) {u : ι → ℝ} (hu : ∀ i, 0 < u i) (i : ι) : 0 < flow d s u i :=
  mul_pos (exp_pos _) (hu i)

/-- The flow scales monomials by `e^{s d·e}`. -/
theorem prod_flow_rpow (d : ι → ℝ) (s : ℝ) {u : ι → ℝ} (hu : ∀ i, 0 < u i) (e : ι → ℝ) :
    ∏ i, flow d s u i ^ e i = exp (s * ∑ i, d i * e i) * ∏ i, u i ^ e i := by
  unfold flow
  rw [Finset.mul_sum, Real.exp_sum, ← Finset.prod_mul_distrib]
  exact Finset.prod_congr rfl fun i _ ↦ by
    rw [Real.mul_rpow (exp_pos _).le (hu i).le, ← Real.exp_mul, mul_assoc]

/-- The log-height `⟨d, log u⟩`. -/
noncomputable def logHeight (d : ι → ℝ) (u : ι → ℝ) : ℝ := ∑ i, d i * Real.log (u i)

theorem measurable_logHeight (d : ι → ℝ) : Measurable (logHeight d) :=
  Finset.measurable_sum _ fun i _ ↦
    measurable_const.mul (Real.measurable_log.comp (measurable_pi_apply i))

theorem logHeight_flow (d : ι → ℝ) (s : ℝ) {u : ι → ℝ} (hu : ∀ i, 0 < u i) :
    logHeight d (flow d s u) = s * ∑ i, d i ^ 2 + logHeight d u := by
  unfold logHeight flow
  rw [Finset.mul_sum, ← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun i _ ↦ by
    rw [Real.log_mul (exp_pos _).ne' (hu i).ne', Real.log_exp]
    ring

omit [Fintype ι] in
/-- Membership of the flowed point in the flowed box. -/
theorem flow_mem_box_iff (d : ι → ℝ) (s : ℝ) (a b u : ι → ℝ) :
    flow d s u ∈ (Set.pi univ fun i ↦ Icc (flow d s a i) (flow d s b i)) ↔
      u ∈ Set.pi univ fun i ↦ Icc (a i) (b i) := by
  rw [Set.mem_univ_pi, Set.mem_univ_pi]
  refine forall_congr' fun i ↦ ?_
  simp only [flow, Set.mem_Icc]
  constructor
  · rintro ⟨h1, h2⟩
    exact ⟨le_of_mul_le_mul_left h1 (exp_pos _), le_of_mul_le_mul_left h2 (exp_pos _)⟩
  · rintro ⟨h1, h2⟩
    exact ⟨mul_le_mul_of_nonneg_left h1 (exp_pos _).le, mul_le_mul_of_nonneg_left h2 (exp_pos _).le⟩

/-- On a box `[a, b]` with `0 < a`, `∏ u^r e^{-C ∏ u^κ}` is integrable. -/
theorem integrableOn_prod_rpow_mul_exp_box {a b : ι → ℝ} (hab : ∀ i, 0 < a i ∧ a i ≤ b i)
    {C : ℝ} (hC : 0 ≤ C) (r κ : ι → ℝ) :
    IntegrableOn (fun u : ι → ℝ ↦ (∏ i, u i ^ r i) * exp (-(C * ∏ i, u i ^ κ i)))
      (Set.pi univ fun i ↦ Icc (a i) (b i)) := by
  have hbox : MeasurableSet (Set.pi univ fun i ↦ Icc (a i) (b i)) :=
    MeasurableSet.pi countable_univ fun i _ ↦ measurableSet_Icc
  have hvol : volume (Set.pi univ fun i ↦ Icc (a i) (b i)) ≠ ∞ := by
    rw [Set.pi_univ_Icc, Real.volume_Icc_pi]
    exact ENNReal.prod_ne_top fun i _ ↦ ENNReal.ofReal_ne_top
  have hmeas : Measurable fun u : ι → ℝ ↦ (∏ i, u i ^ r i) * exp (-(C * ∏ i, u i ^ κ i)) :=
    (Finset.measurable_prod _ fun i _ ↦ (measurable_pi_apply i).pow_const _).mul
      (Real.measurable_exp.comp ((measurable_const.mul
        (Finset.measurable_prod _ fun i _ ↦ (measurable_pi_apply i).pow_const _)).neg))
  refine Measure.integrableOn_of_bounded (M := ∏ i, max (a i ^ r i) (b i ^ r i)) hvol
    hmeas.aestronglyMeasurable ((ae_restrict_iff' hbox).2 (Eventually.of_forall fun u hu ↦ ?_))
  have hupos : ∀ i, 0 < u i := fun i ↦ (hab i).1.trans_le (Set.mem_univ_pi.mp hu i).1
  have hr0 : 0 ≤ ∏ i, u i ^ r i := Finset.prod_nonneg fun i _ ↦ rpow_nonneg (hupos i).le _
  rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg hr0 (exp_pos _).le)]
  calc (∏ i, u i ^ r i) * exp (-(C * ∏ i, u i ^ κ i))
      ≤ (∏ i, max (a i ^ r i) (b i ^ r i)) * 1 := by
        refine mul_le_mul (Finset.prod_le_prod (fun i _ ↦ rpow_nonneg (hupos i).le _)
          fun i _ ↦ rpow_le_max (hab i).1 (Set.mem_univ_pi.mp hu i)) ?_ (exp_pos _).le
          (Finset.prod_nonneg fun i _ ↦ le_max_of_le_left (rpow_nonneg (hab i).1.le _))
        refine Real.exp_le_one_iff.mpr (neg_nonpos.mpr (mul_nonneg hC ?_))
        exact Finset.prod_nonneg fun i _ ↦ rpow_nonneg (hupos i).le _
    _ = _ := mul_one _

/-- **Recession-direction obstruction.** If `L` (positive coordinates) is invariant under the
flow along `d ≠ 0`, contains a box, the phase is bounded by `K ∏ u^κ` on `L` with `d·κ ≤ 0`, and
`d·(r + 1) ≥ 0`, then `1_L ∏ u^r e^{-Φ}` is not integrable. -/
theorem not_integrable_of_recession_direction {L : Set (ι → ℝ)} (hLm : MeasurableSet L)
    (hLpos : ∀ u ∈ L, ∀ i, 0 < u i) (d : ι → ℝ) (hd : d ≠ 0)
    (hLinv : ∀ s : ℝ, 0 ≤ s → ∀ u ∈ L, flow d s u ∈ L)
    (a b : ι → ℝ) (hab : ∀ i, 0 < a i ∧ a i < b i)
    (hbox : (Set.pi univ fun i ↦ Icc (a i) (b i)) ⊆ L)
    {r κ : ι → ℝ} (hrd : 0 ≤ ∑ i, d i * (r i + 1)) (hκd : ∑ i, d i * κ i ≤ 0)
    {Φ : (ι → ℝ) → ℝ} {K : ℝ} (hK : 0 ≤ K) (hΦ : ∀ u ∈ L, Φ u ≤ K * ∏ i, u i ^ κ i) :
    ¬ Integrable (fun u ↦ L.indicator (fun u ↦ ∏ i, u i ^ r i) u * exp (-Φ u)) := by
  classical
  intro hint
  have hg0 : ∀ u, 0 ≤ L.indicator (fun u ↦ ∏ i, u i ^ r i) u * exp (-Φ u) := fun u ↦
    mul_nonneg (Set.indicator_nonneg (fun u hu ↦
      Finset.prod_nonneg fun i _ ↦ rpow_nonneg (hLpos u hu i).le _) u) (exp_pos _).le
  -- the squared norm of `d` and the height floor of the box
  have hNpos : 0 < ∑ i, d i ^ 2 := by
    obtain ⟨i, hi⟩ : ∃ i, d i ≠ 0 := by
      by_contra h
      push Not at h
      exact hd (funext h)
    exact Finset.sum_pos' (fun i _ ↦ sq_nonneg _) ⟨i, Finset.mem_univ _, sq_pos_iff.mpr hi⟩
  set N := ∑ i, d i ^ 2 with hN
  set m₀ := ∑ i, min (d i * Real.log (a i)) (d i * Real.log (b i)) with hm₀
  set K₀ := Set.pi univ fun i ↦ Icc (a i) (b i) with hK₀
  have hK₀m : MeasurableSet K₀ := MeasurableSet.pi countable_univ fun i _ ↦ measurableSet_Icc
  have hK₀pos : ∀ u ∈ K₀, ∀ i, 0 < u i := fun u hu i ↦
    (hab i).1.trans_le (Set.mem_univ_pi.mp hu i).1
  have hheight : ∀ u ∈ K₀, m₀ ≤ logHeight d u := fun u hu ↦ by
    unfold logHeight
    refine Finset.sum_le_sum fun i _ ↦ ?_
    have hui := Set.mem_univ_pi.mp hu i
    have hla : Real.log (a i) ≤ Real.log (u i) := Real.log_le_log (hab i).1 hui.1
    have hlb : Real.log (u i) ≤ Real.log (b i) :=
      Real.log_le_log ((hab i).1.trans_le hui.1) hui.2
    rcases le_or_gt 0 (d i) with hdi | hdi
    · exact (min_le_left _ _).trans (mul_le_mul_of_nonneg_left hla hdi)
    · exact (min_le_right _ _).trans (mul_le_mul_of_nonpos_left hlb hdi.le)
  -- the nested tail sets
  set A : ℕ → Set (ι → ℝ) := fun n ↦ L ∩ {u | (n : ℝ) * N + m₀ ≤ logHeight d u} with hA
  have hAm : ∀ n, MeasurableSet (A n) := fun n ↦
    hLm.inter (measurableSet_le measurable_const (measurable_logHeight d))
  have hAanti : Antitone A := fun n m hnm u hu ↦ by
    refine ⟨hu.1, ?_⟩
    have h2 : (m : ℝ) * N + m₀ ≤ logHeight d u := hu.2
    change (n : ℝ) * N + m₀ ≤ logHeight d u
    have : (n : ℝ) ≤ m := by exact_mod_cast hnm
    nlinarith [mul_le_mul_of_nonneg_right this hNpos.le]
  have hAempty : ⋂ n, A n = ∅ := by
    refine Set.eq_empty_iff_forall_notMem.mpr fun u hu ↦ ?_
    obtain ⟨n, hn⟩ := exists_nat_gt ((logHeight d u - m₀) / N)
    have h : (n : ℝ) * N + m₀ ≤ logHeight d u := (Set.mem_iInter.mp hu n).2
    rw [div_lt_iff₀ hNpos] at hn
    linarith
  have htend : Tendsto (fun n ↦ ∫ u in A n, L.indicator (fun u ↦ ∏ i, u i ^ r i) u * exp (-Φ u))
      atTop (𝓝 0) := by
    have := tendsto_setIntegral_of_antitone hAm hAanti ⟨0, hint.integrableOn⟩
    rwa [hAempty, Measure.restrict_empty, integral_zero_measure] at this
  -- the frozen integrand on the base box and its positive integral
  have hmfpos : 0 < (∏ i, min (a i ^ r i) (b i ^ r i)) *
      exp (-(K * ∏ i, max (a i ^ κ i) (b i ^ κ i))) :=
    mul_pos (Finset.prod_pos fun i _ ↦ lt_min (rpow_pos_of_pos (hab i).1 _)
      (rpow_pos_of_pos ((hab i).1.trans (hab i).2) _)) (exp_pos _)
  have hflow : ∀ u ∈ K₀, (∏ i, min (a i ^ r i) (b i ^ r i)) *
      exp (-(K * ∏ i, max (a i ^ κ i) (b i ^ κ i))) ≤
        (∏ i, u i ^ r i) * exp (-(K * ∏ i, u i ^ κ i)) := fun u hu ↦ by
    have hui : ∀ i, u i ∈ Icc (a i) (b i) := fun i ↦ Set.mem_univ_pi.mp hu i
    refine mul_le_mul (Finset.prod_le_prod (fun i _ ↦ (lt_min (rpow_pos_of_pos (hab i).1 _)
      (rpow_pos_of_pos ((hab i).1.trans (hab i).2) _)).le) fun i _ ↦ rpow_ge_min (hab i).1 (hui i))
      (Real.exp_le_exp.mpr ?_) (exp_pos _).le
      (Finset.prod_nonneg fun i _ ↦ rpow_nonneg (hK₀pos u hu i).le _)
    rw [neg_le_neg_iff]
    exact mul_le_mul_of_nonneg_left (Finset.prod_le_prod
      (fun i _ ↦ rpow_nonneg (hK₀pos u hu i).le _) fun i _ ↦ rpow_le_max (hab i).1 (hui i)) hK
  have hvol : volume K₀ ≠ ∞ := by
    rw [hK₀, Set.pi_univ_Icc, Real.volume_Icc_pi]
    exact ENNReal.prod_ne_top fun i _ ↦ ENNReal.ofReal_ne_top
  have hvolpos : 0 < volume.real K₀ := by
    rw [measureReal_def, hK₀, Set.pi_univ_Icc, Real.volume_Icc_pi, ENNReal.toReal_prod]
    refine Finset.prod_pos fun i _ ↦ ?_
    rw [ENNReal.toReal_ofReal (by linarith [(hab i).2])]
    linarith [(hab i).2]
  have hfint : IntegrableOn (fun u : ι → ℝ ↦ (∏ i, u i ^ r i) * exp (-(K * ∏ i, u i ^ κ i))) K₀ :=
    integrableOn_prod_rpow_mul_exp_box (fun i ↦ ⟨(hab i).1, (hab i).2.le⟩) hK r κ
  have hJ₀pos : 0 < ∫ u in K₀, (∏ i, u i ^ r i) * exp (-(K * ∏ i, u i ^ κ i)) :=
    lt_of_lt_of_le (mul_pos hmfpos hvolpos)
      (setIntegral_ge_of_const_le_real hK₀m hvol hflow hfint)
  -- the lower bound of the tail integrals
  have hlow : ∀ n : ℕ, (∫ u in K₀, (∏ i, u i ^ r i) * exp (-(K * ∏ i, u i ^ κ i))) ≤
      ∫ u in A n, L.indicator (fun u ↦ ∏ i, u i ^ r i) u * exp (-Φ u) := fun n ↦ by
    have hn0 : (0 : ℝ) ≤ n := Nat.cast_nonneg n
    set cn := exp (-(n * ∑ i, d i * κ i)) with hcn
    have hcn1 : 1 ≤ cn := Real.one_le_exp (by nlinarith)
    set Kn := Set.pi univ fun i ↦ Icc (flow d n a i) (flow d n b i) with hKn
    have hKnm : MeasurableSet Kn := MeasurableSet.pi countable_univ fun i _ ↦ measurableSet_Icc
    have hmemKn : ∀ u, flow d n u ∈ Kn ↔ u ∈ K₀ := fun u ↦ flow_mem_box_iff d n a b u
    have hinv : ∀ v, flow d n (flow d (-n) v) = v := fun v ↦ by
      rw [flow_flow, add_neg_cancel, flow_zero]
    have hKnL : Kn ⊆ L := fun v hv ↦ by
      have hv2 : flow d n (flow d (-n) v) ∈ Kn := by rw [hinv]; exact hv
      rw [← hinv v]
      exact hLinv n hn0 _ (hbox ((hmemKn _).mp hv2))
    have hKnA : Kn ⊆ A n := fun v hv ↦ by
      refine ⟨hKnL hv, ?_⟩
      change (n : ℝ) * N + m₀ ≤ logHeight d v
      have hv2 : flow d n (flow d (-n) v) ∈ Kn := by rw [hinv]; exact hv
      have hw : flow d (-n) v ∈ K₀ := (hmemKn _).mp hv2
      have := hheight _ hw
      have hv' := hinv v
      rw [← hv', logHeight_flow d n (hK₀pos _ hw)]
      linarith
    -- the lower function on the transported box
    have hle : ∀ u, Kn.indicator (fun u ↦ (∏ i, u i ^ r i) * exp (-(K * cn * ∏ i, u i ^ κ i))) u ≤
        (A n).indicator (fun u ↦ L.indicator (fun u ↦ ∏ i, u i ^ r i) u * exp (-Φ u)) u := by
      intro u
      by_cases hu : u ∈ Kn
      · rw [Set.indicator_of_mem hu, Set.indicator_of_mem (hKnA hu),
          Set.indicator_of_mem (hKnL hu)]
        have hupos : ∀ i, 0 < u i := hLpos u (hKnL hu)
        have hprod : 0 ≤ ∏ i, u i ^ κ i := Finset.prod_nonneg fun i _ ↦ rpow_nonneg (hupos i).le _
        refine mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr ?_)
          (Finset.prod_nonneg fun i _ ↦ rpow_nonneg (hupos i).le _)
        rw [neg_le_neg_iff]
        calc Φ u ≤ K * ∏ i, u i ^ κ i := hΦ u (hKnL hu)
          _ = K * 1 * ∏ i, u i ^ κ i := by ring
          _ ≤ K * cn * ∏ i, u i ^ κ i :=
            mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hcn1 hK) hprod
      · rw [Set.indicator_of_notMem hu]
        exact Set.indicator_nonneg (fun u _ ↦ hg0 u) u
    have hlnint : Integrable fun u ↦
        Kn.indicator (fun u ↦ (∏ i, u i ^ r i) * exp (-(K * cn * ∏ i, u i ^ κ i))) u :=
      (integrable_indicator_iff hKnm).mpr (integrableOn_prod_rpow_mul_exp_box
        (fun i ↦ ⟨flow_pos d n (fun i ↦ (hab i).1) i,
          mul_le_mul_of_nonneg_left (hab i).2.le (exp_pos _).le⟩)
        (mul_nonneg hK (zero_le_one.trans hcn1)) r κ)
    have hlnmeas : Measurable fun u ↦
        Kn.indicator (fun u ↦ (∏ i, u i ^ r i) * exp (-(K * cn * ∏ i, u i ^ κ i))) u :=
      ((Finset.measurable_prod _ fun i _ ↦ (measurable_pi_apply i).pow_const _).mul
        (Real.measurable_exp.comp ((measurable_const.mul
          (Finset.measurable_prod _ fun i _ ↦ (measurable_pi_apply i).pow_const _)).neg))).indicator
        hKnm
    -- its integral by the change of variables `u ↦ e^{n d} ⊙ u`
    have hchange : (∫ u, Kn.indicator (fun u ↦ (∏ i, u i ^ r i) *
        exp (-(K * cn * ∏ i, u i ^ κ i))) u) = exp (n * ∑ i, d i * (r i + 1)) *
          ∫ u in K₀, (∏ i, u i ^ r i) * exp (-(K * ∏ i, u i ^ κ i)) := by
      rw [integral_comp_rescale (exp_pos (n : ℝ)) (-d) _ hlnmeas.aestronglyMeasurable]
      have hpre : (∏ j, exp (n : ℝ) ^ (-(-d) j)) = exp (n * ∑ i, d i) := by
        rw [Finset.mul_sum, Real.exp_sum]
        exact Finset.prod_congr rfl fun j _ ↦ by rw [Pi.neg_apply, neg_neg, ← Real.exp_mul]
      have hpt : ∀ u, Kn.indicator (fun u ↦ (∏ i, u i ^ r i) *
          exp (-(K * cn * ∏ i, u i ^ κ i))) (rescale (exp (n : ℝ)) (-d) u) =
          K₀.indicator (fun u ↦ exp (n * ∑ i, d i * r i) *
            ((∏ i, u i ^ r i) * exp (-(K * ∏ i, u i ^ κ i)))) u := fun u ↦ by
        rw [← flow_eq_rescale]
        by_cases hu : u ∈ K₀
        · rw [Set.indicator_of_mem ((hmemKn u).mpr hu), Set.indicator_of_mem hu]
          have hupos := hK₀pos u hu
          rw [prod_flow_rpow d _ hupos, prod_flow_rpow d _ hupos]
          have hc : K * cn * (exp (n * ∑ i, d i * κ i) * ∏ i, u i ^ κ i) = K * ∏ i, u i ^ κ i := by
            rw [hcn, show K * exp (-(n * ∑ i, d i * κ i)) * (exp (n * ∑ i, d i * κ i) *
              ∏ i, u i ^ κ i) = K * (exp (-(n * ∑ i, d i * κ i)) * exp (n * ∑ i, d i * κ i)) *
                ∏ i, u i ^ κ i by ring, ← Real.exp_add, neg_add_cancel, Real.exp_zero, mul_one]
          rw [hc]
          ring
        · rw [Set.indicator_of_notMem (fun h ↦ hu ((hmemKn u).mp h)), Set.indicator_of_notMem hu]
      simp only [hpt]
      rw [hpre, integral_indicator hK₀m, integral_const_mul, ← mul_assoc, ← Real.exp_add]
      congr 2
      rw [← mul_add, ← Finset.sum_add_distrib]
      congr 1
      exact Finset.sum_congr rfl fun i _ ↦ by ring
    calc (∫ u in K₀, (∏ i, u i ^ r i) * exp (-(K * ∏ i, u i ^ κ i)))
        ≤ exp (n * ∑ i, d i * (r i + 1)) *
          ∫ u in K₀, (∏ i, u i ^ r i) * exp (-(K * ∏ i, u i ^ κ i)) :=
          le_mul_of_one_le_left hJ₀pos.le (Real.one_le_exp (mul_nonneg hn0 hrd))
      _ = ∫ u, Kn.indicator (fun u ↦ (∏ i, u i ^ r i) * exp (-(K * cn * ∏ i, u i ^ κ i))) u :=
          hchange.symm
      _ ≤ ∫ u, (A n).indicator (fun u ↦ L.indicator (fun u ↦ ∏ i, u i ^ r i) u * exp (-Φ u)) u :=
          integral_mono hlnint (hint.indicator (hAm n)) hle
      _ = _ := integral_indicator (hAm n)
  exact (not_lt.mpr (ge_of_tendsto' htend hlow)) hJ₀pos

/-- **The recession-direction obstruction for the limiting domain.** Any direction `d ≠ 0`
supported on the scaled coordinates with `d·κ ≤ 0` and `d·(r + 1) ≥ 0` forbids the profile
certificate (strict truth constraint). -/
theorem not_integrable_envelope_of_recession_direction {ρ B D γ q δ : ℝ} {Q κ r α : ι → ℝ}
    {a₀ : (ι → ℝ) → ℝ} {amax c : ℝ} (hρ : 0 < ρ) (hstrict : ∑ i, Q i * α i < γ) (d : ι → ℝ)
    (hd : d ≠ 0) (hsupp : ∀ j, α j = 0 → d j = 0) (hκd : ∑ i, d i * κ i ≤ 0)
    (hrd : 0 ≤ ∑ i, d i * (r i + 1)) (hB : 0 ≤ B) (hc : 0 ≤ c) (ha₀ : ∀ u, |a₀ u| ≤ amax) :
    ¬ Integrable fun u ↦ dsEnvelope ρ D γ q Q r α 1 u *
      exp (-(c * dsProfile ρ B D γ q δ Q κ α a₀ u)) := by
  classical
  have e : (fun u ↦ dsEnvelope ρ D γ q Q r α 1 u * exp (-(c * dsProfile ρ B D γ q δ Q κ α a₀ u))) =
      fun u ↦ (limitDomain ρ D γ q Q α).indicator (fun u ↦ ∏ i, u i ^ r i) u *
        exp (-(c * dsProfile ρ B D γ q δ Q κ α a₀ u)) := by
    funext u
    unfold dsEnvelope
    rw [one_mul]
  rw [e]
  have hL : limitDomain ρ D γ q Q α =
      Set.pi univ fun i ↦ if α i = 0 then Ioo (0 : ℝ) ρ else Ioi 0 := by
    unfold limitDomain
    have : {u : ι → ℝ | ∑ i, Q i * α i = γ → D * ∏ i, u i ^ (-(Q i / q)) < ρ} = univ := by
      ext u; simp [hstrict.ne]
    rw [this, inter_univ]
  have hamax : 0 ≤ amax := (abs_nonneg _).trans (ha₀ 0)
  refine not_integrable_of_recession_direction measurableSet_limitDomain
    (fun u hu i ↦ limitDomain_pos hu i) d hd ?_ (fun _ ↦ ρ / 4) (fun _ ↦ ρ / 2)
    (fun _ ↦ ⟨by positivity, by linarith⟩) ?_ hrd hκd (K := c * B * amax) (by positivity) ?_
  · intro s _ u hu
    rw [hL, Set.mem_univ_pi] at hu ⊢
    intro i
    have hi := hu i
    by_cases h0 : α i = 0
    · simp only [h0, if_true] at hi ⊢
      rw [flow, hsupp i h0, mul_zero, Real.exp_zero, one_mul]
      exact hi
    · simp only [h0, if_false] at hi ⊢
      exact mul_pos (exp_pos _) hi
  · intro u hu
    rw [hL, Set.mem_univ_pi]
    intro i
    have hi := Set.mem_univ_pi.mp hu i
    split_ifs
    · exact ⟨by linarith [hi.1], by linarith [hi.2]⟩
    · exact show (0 : ℝ) < u i by linarith [hi.1]
  · intro u hu
    have hpos : 0 ≤ ∏ i, u i ^ κ i := Finset.prod_nonneg fun i _ ↦
      rpow_nonneg (limitDomain_pos hu i).le _
    unfold dsProfile
    rw [if_pos hu]
    split_ifs
    · calc c * (B * a₀ u * ∏ i, u i ^ κ i) ≤ c * (B * amax * ∏ i, u i ^ κ i) := by
            gcongr
            exact (le_abs_self _).trans (ha₀ u)
        _ = c * B * amax * ∏ i, u i ^ κ i := by ring
    · rw [mul_zero]
      exact mul_nonneg (mul_nonneg (mul_nonneg hc hB) hamax) hpos

end Laplace.Multi
