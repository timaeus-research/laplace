/-
Copyright (c) 2026 Timaeus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Laplace.Grammar.SpectralCoefficients

/-!
# Low-spectrum tail replacement and the quantitative cutoff theorem (Stage 3h)

Unit 238 (Taylor-tree programme; Astra #27). In the low-spectrum part of the exact polynomial
Taylor tree the truncated moments `∫₀^N` are replaced by the full fluctuation moments `∫₀^∞`. The
difference is a **tail** `∫_N^∞ t^{μ-1}(-log t)^i g_p(t) dt`, which for `0 < μ ≤ L`, `i ≤ n`,
`N ≥ 1`
is dominated by the tail of the log majorant `∫_N^∞ logMajorant β a L n p`
(`abs_entryTail_le`); the phase orders are summed under the absolute integral first
(`tsum_logTailMoment_series`, the Tonelli identity of unit 234 on `(N,∞)`), producing the kernel
`e^{-βt+β(a+‖J‖₁)√t}`, whose tail is `O(e^{-βN/4})` and hence `O(N^{-L})`
(`logTailMoment_le`, `exp_le_rpow_const`). Assembling Gate C (unit 236) and Gate D (unit 237):

**Headline XXV — the quantitative polynomial Taylor tree.** For polynomial phase `ξ` and amplitude
`η`, `β > 0`, positive `k`, every cutoff `L > 0` and every `N ≥ 1`,
```
|Z(N) - ∑_{μ ∈ Λ_L} N^{-μ} ∑_{j ≤ n} A_{μ,j} (log N)^j| ≤ taylorCutoffConst · N^{-L} (1+log N)^n,
```
with `Λ_L = latticeBelow (2∏kᵢ) L`, `A_{μ,j}` the cutoff-free spectral coefficients of unit 237 and
an explicit constant independent of `N` (`taylorTree_cutoff_bound`). No `sorry` and no additional
`axiom` declarations.
-/

open MeasureTheory Set Real Filter Topology

namespace Laplace.Grammar

open MonoRep

/-! ### Tails of the log majorant -/

/-- `∫_N^∞ logMajorant β a L n p`. -/
noncomputable def logTailMoment (β a L : ℝ) (n p : ℕ) (N : ℝ) : ℝ :=
  ∫ t in Ioi N, logMajorant β a L n p t

theorem logTailMoment_nonneg (β a L : ℝ) (n p : ℕ) {N : ℝ} (hN : 0 ≤ N) :
    0 ≤ logTailMoment β a L n p N :=
  setIntegral_nonneg measurableSet_Ioi fun _ ht => logMajorant_nonneg β a L n p (by
    have := mem_Ioi.1 ht; linarith)

/-- The Tonelli identity of unit 234 on `(N,∞)`, `N ≥ 0`. -/
theorem tsum_logTailMoment_series (β a B L : ℝ) (hβ : 0 < β) (hL : 0 < L) (hB : 0 ≤ B) (n : ℕ)
    {N : ℝ} (hN : 0 ≤ N) :
    ∑' p : ℕ, (β * B) ^ p / (p.factorial : ℝ) * logTailMoment β a L n p N =
      logTailMoment β (a + B) L n 0 N := by
  unfold logTailMoment
  have hsub : Ioi N ⊆ Ioi 0 := Ioi_subset_Ioi hN
  have hint : ∀ p : ℕ, IntegrableOn
      (fun t => (β * B) ^ p / (p.factorial : ℝ) * logMajorant β a L n p t) (Ioi N) := fun p =>
    (integrableOn_phase_series_term β a B L hβ hL n p).mono_set hsub
  have hpart : ∀ P : ℕ, ∑ p ∈ Finset.range P, (β * B) ^ p / (p.factorial : ℝ) *
      ∫ t in Ioi N, logMajorant β a L n p t ≤ ∫ t in Ioi N, logMajorant β (a + B) L n 0 t := by
    intro P
    have h1 : ∑ p ∈ Finset.range P, (β * B) ^ p / (p.factorial : ℝ) *
        ∫ t in Ioi N, logMajorant β a L n p t =
        ∫ t in Ioi N, ∑ p ∈ Finset.range P,
          (β * B) ^ p / (p.factorial : ℝ) * logMajorant β a L n p t := by
      rw [integral_finsetSum _ fun p _ => hint p]
      refine Finset.sum_congr rfl fun p _ => ?_
      rw [integral_const_mul]
    rw [h1]
    refine setIntegral_mono_on (integrable_finsetSum _ fun p _ => hint p)
      ((integrableOn_logMajorant β (a + B) L hβ hL n 0).mono_set hsub) measurableSet_Ioi
      fun t ht => ?_
    have ht0 : 0 < t := lt_of_le_of_lt hN (mem_Ioi.1 ht)
    exact sum_range_logMajorant_le β a B L hB hβ.le n ht0 P
  have hsumm : Summable fun p : ℕ => (β * B) ^ p / (p.factorial : ℝ) *
      ∫ t in Ioi N, logMajorant β a L n p t :=
    summable_of_sum_range_le (fun p => mul_nonneg (by positivity)
      (logTailMoment_nonneg β a L n p hN)) hpart
  have hnorm : Summable fun p : ℕ => ∫ t in Ioi N,
      ‖(β * B) ^ p / (p.factorial : ℝ) * logMajorant β a L n p t‖ := by
    refine hsumm.congr fun p => ?_
    rw [← integral_const_mul]
    refine setIntegral_congr_fun measurableSet_Ioi fun t ht => ?_
    have ht0 : 0 < t := lt_of_le_of_lt hN (mem_Ioi.1 ht)
    rw [Real.norm_eq_abs, abs_of_nonneg
      (mul_nonneg (by positivity) (logMajorant_nonneg β a L n p ht0.le))]
  have hsum := hasSum_integral_of_summable_integral_norm (fun p => hint p) hnorm
  have h1 : ∀ p : ℕ, ∫ t in Ioi N, (β * B) ^ p / (p.factorial : ℝ) * logMajorant β a L n p t =
      (β * B) ^ p / (p.factorial : ℝ) * ∫ t in Ioi N, logMajorant β a L n p t :=
    fun p => integral_const_mul _ _
  simp_rw [h1] at hsum
  rw [hsum.tsum_eq]
  exact setIntegral_congr_fun measurableSet_Ioi fun t _ => tsum_logMajorant_series β a B L n t

theorem summable_logTailMoment_series (β a B L : ℝ) (hβ : 0 < β) (hL : 0 < L) (hB : 0 ≤ B) (n : ℕ)
    {N : ℝ} (hN : 0 ≤ N) :
    Summable fun p : ℕ => (β * B) ^ p / (p.factorial : ℝ) * logTailMoment β a L n p N := by
  have hsub : Ioi N ⊆ Ioi 0 := Ioi_subset_Ioi hN
  have hint : ∀ p : ℕ, IntegrableOn
      (fun t => (β * B) ^ p / (p.factorial : ℝ) * logMajorant β a L n p t) (Ioi N) := fun p =>
    (integrableOn_phase_series_term β a B L hβ hL n p).mono_set hsub
  refine summable_of_sum_range_le (c := logTailMoment β (a + B) L n 0 N)
    (fun p => mul_nonneg (by positivity) (logTailMoment_nonneg β a L n p hN)) fun P => ?_
  unfold logTailMoment
  have h1 : ∑ p ∈ Finset.range P, (β * B) ^ p / (p.factorial : ℝ) *
      ∫ t in Ioi N, logMajorant β a L n p t =
      ∫ t in Ioi N, ∑ p ∈ Finset.range P,
        (β * B) ^ p / (p.factorial : ℝ) * logMajorant β a L n p t := by
    rw [integral_finsetSum _ fun p _ => hint p]
    refine Finset.sum_congr rfl fun p _ => ?_
    rw [integral_const_mul]
  rw [h1]
  refine setIntegral_mono_on (integrable_finsetSum _ fun p _ => hint p)
    ((integrableOn_logMajorant β (a + B) L hβ hL n 0).mono_set hsub) measurableSet_Ioi
    fun t ht => ?_
  exact sum_range_logMajorant_le β a B L hB hβ.le n (lt_of_le_of_lt hN (mem_Ioi.1 ht)) P

/-- The tail of the log majorant at phase order `0` decays exponentially. -/
theorem logTailMoment_le (β b L : ℝ) (hβ : 0 < β) (n : ℕ) {N : ℝ} (hN : 1 ≤ N) :
    logTailMoment β b L n 0 N ≤ tailConst β b 0 L n * (4 / β) * Real.exp (-(β * N / 4)) := by
  unfold logTailMoment
  have hg : IntegrableOn (fun t => tailConst β b 0 L n * Real.exp (-(β * t / 4))) (Ioi N) := by
    have this : IntegrableOn (fun t => tailConst β b 0 L n * Real.exp (-(β / 4) * t)) (Ioi N) :=
      (exp_neg_integrableOn_Ioi N (by positivity : 0 < β / 4)).const_mul _
    refine this.congr_fun (fun t _ => ?_) measurableSet_Ioi
    beta_reduce
    ring_nf
  calc ∫ t in Ioi N, logMajorant β b L n 0 t
      ≤ ∫ t in Ioi N, tailConst β b 0 L n * Real.exp (-(β * t / 4)) := by
        refine integral_mono_of_nonneg (ae_restrict_of_forall_mem measurableSet_Ioi fun t ht =>
          logMajorant_nonneg β b L n 0 (by have := mem_Ioi.1 ht; linarith)) hg
          (ae_restrict_of_forall_mem measurableSet_Ioi fun t ht =>
            logMajorant_le β b L hβ n 0 (by have := mem_Ioi.1 ht; linarith))
    _ = tailConst β b 0 L n * (4 / β * Real.exp (-(β * N / 4))) := by
        rw [integral_const_mul, integral_exp_tail β hβ N]
    _ = _ := by ring

/-- `e^{-βN/4} ≤ ⌈L⌉! (4/β)^{⌈L⌉} N^{-L}` for `N ≥ 1`, `L > 0`. -/
theorem exp_le_rpow_const (β L : ℝ) (hβ : 0 < β) {N : ℝ} (hN : 1 ≤ N) :
    Real.exp (-(β * N / 4)) ≤
      ((⌈L⌉₊.factorial : ℝ) * (4 / β) ^ ⌈L⌉₊) * N ^ (-L) := by
  have hN0 : 0 < N := by linarith
  set m : ℕ := ⌈L⌉₊
  have hNL : N ^ L ≤ N ^ (m : ℕ) := by
    rw [← Real.rpow_natCast]
    exact Real.rpow_le_rpow_of_exponent_le hN (Nat.le_ceil L)
  have hexp : N ^ m * Real.exp (-(β * N / 4)) ≤ (m.factorial : ℝ) * (4 / β) ^ m := by
    have h := Real.pow_div_factorial_le_exp (β * N / 4) (by positivity) m
    rw [div_le_iff₀ (by positivity)] at h
    have hE : Real.exp (-(β * N / 4)) * Real.exp (β * N / 4) = 1 := by
      rw [← Real.exp_add, neg_add_cancel, Real.exp_zero]
    calc N ^ m * Real.exp (-(β * N / 4))
        = (β * N / 4) ^ m * (4 / β) ^ m * Real.exp (-(β * N / 4)) := by
          rw [← mul_pow]; congr 2; field_simp
      _ ≤ Real.exp (β * N / 4) * (m.factorial : ℝ) * (4 / β) ^ m * Real.exp (-(β * N / 4)) :=
          mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right h (by positivity))
            (Real.exp_nonneg _)
      _ = (m.factorial : ℝ) * (4 / β) ^ m * (Real.exp (-(β * N / 4)) * Real.exp (β * N / 4)) := by
          ring
      _ = _ := by rw [hE, mul_one]
  have hpos : 0 < N ^ L := Real.rpow_pos_of_pos hN0 L
  rw [Real.rpow_neg hN0.le, ← div_eq_mul_inv, le_div_iff₀ hpos]
  calc Real.exp (-(β * N / 4)) * N ^ L ≤ Real.exp (-(β * N / 4)) * N ^ (m : ℕ) :=
        mul_le_mul_of_nonneg_left hNL (Real.exp_nonneg _)
    _ = N ^ m * Real.exp (-(β * N / 4)) := by ring
    _ ≤ _ := hexp

/-! ### Tail entries -/

/-- The tail `∫_N^∞ t^{μ-1}(-log t)^i g_p(t) dt` of a fluctuation moment. -/
noncomputable def momentTail (β a : ℝ) (p : ℕ) (μ : ℝ) (i : ℕ) (N : ℝ) : ℝ :=
  ∫ t in Ioi N, t ^ (μ - 1) * (-Real.log t) ^ i * phaseKernel β a p t

/-- One density entry with the tails of the moments. -/
noncomputable def entryTail (β a : ℝ) (p : ℕ) (N : ℝ) (t : ℝ × ℕ × ℝ) : ℝ :=
  t.2.2 * (N ^ (-t.1) * ∑ i ∈ Finset.range (t.2.1 + 1),
    (t.2.1.choose i : ℝ) * (Real.log N) ^ (t.2.1 - i) * momentTail β a p t.1 i N)

theorem entryTrunc_eq_main_sub_tail (β a : ℝ) (hβ : 0 < β) (p : ℕ) {N : ℝ} (hN : 1 ≤ N)
    {t : ℝ × ℕ × ℝ} (hμ : 0 < t.1) :
    entryTrunc β a p N t = entryMain β a p N t - entryTail β a p N t := by
  unfold entryTrunc entryMain entryTail momentTail
  simp_rw [truncMoment_eq_fluct_sub β a hβ p hμ _ hN]
  rw [← mul_sub, ← mul_sub, ← Finset.sum_sub_distrib]
  congr 2
  refine Finset.sum_congr rfl fun i _ => ?_
  ring

/-- `|momentTail| ≤ logTailMoment β a L n p N` for `0 < μ ≤ L`, `i ≤ n`, `N ≥ 1`. -/
theorem abs_momentTail_le (β a : ℝ) (hβ : 0 < β) (p : ℕ) {L μ : ℝ} (hL : 0 < L) (hμ : μ ≤ L)
    {i n : ℕ} (hi : i ≤ n) {N : ℝ} (hN : 1 ≤ N) :
    |momentTail β a p μ i N| ≤ logTailMoment β a L n p N := by
  unfold momentTail logTailMoment
  refine abs_integral_le_integral_abs.trans ?_
  refine integral_mono_of_nonneg (Eventually.of_forall fun t => abs_nonneg _)
    ((integrableOn_logMajorant β a L hβ hL n p).mono_set (Ioi_subset_Ioi (by linarith)))
    (ae_restrict_of_forall_mem measurableSet_Ioi fun t ht => ?_)
  have ht1 : 1 ≤ t := by have := mem_Ioi.1 ht; linarith
  have ht0 : 0 < t := by linarith
  beta_reduce
  rw [abs_mul, abs_mul, abs_of_nonneg (Real.rpow_nonneg ht0.le _),
    abs_of_nonneg (phaseKernel_nonneg _ _ _ _), abs_pow, abs_neg]
  unfold logMajorant
  have h0 := abs_nonneg (Real.log t)
  refine mul_le_mul_of_nonneg_right (mul_le_mul (Real.rpow_le_rpow_of_exponent_le ht1
    (by linarith)) ?_ (by positivity) (Real.rpow_nonneg ht0.le _)) (phaseKernel_nonneg _ _ _ _)
  calc |Real.log t| ^ i ≤ (1 + |Real.log t|) ^ i := pow_le_pow_left₀ h0 (by linarith) i
    _ ≤ (1 + |Real.log t|) ^ n := pow_le_pow_right₀ (by linarith) hi

/-- **Single-entry tail bound**: `|entryTail| ≤ |c| (1+log N)^n logTailMoment`
(`0 < μ ≤ L`, `j ≤ n`). -/
theorem abs_entryTail_le (β a : ℝ) (hβ : 0 < β) (p : ℕ) {L : ℝ} (hL : 0 < L) {n : ℕ} {N : ℝ}
    (hN : 1 ≤ N) {t : ℝ × ℕ × ℝ} (hμ0 : 0 < t.1) (hμ : t.1 ≤ L) (hj : t.2.1 ≤ n) :
    |entryTail β a p N t| ≤ |t.2.2| * ((1 + Real.log N) ^ n * logTailMoment β a L n p N) := by
  have hN0 : 0 < N := by linarith
  have hlN : 0 ≤ Real.log N := Real.log_nonneg hN
  have hT := logTailMoment_nonneg β a L n p hN0.le
  unfold entryTail
  rw [abs_mul]
  refine mul_le_mul_of_nonneg_left ?_ (abs_nonneg _)
  have hNμ : N ^ (-t.1) ≤ 1 := by
    rw [Real.rpow_neg hN0.le]
    exact inv_le_one_of_one_le₀ (Real.one_le_rpow hN hμ0.le)
  have hsum : |∑ i ∈ Finset.range (t.2.1 + 1),
      (t.2.1.choose i : ℝ) * (Real.log N) ^ (t.2.1 - i) * momentTail β a p t.1 i N| ≤
      (1 + Real.log N) ^ t.2.1 * logTailMoment β a L n p N := by
    refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
    have hbin : (1 + Real.log N) ^ t.2.1 = ∑ i ∈ Finset.range (t.2.1 + 1),
        (t.2.1.choose i : ℝ) * (Real.log N) ^ (t.2.1 - i) := by
      rw [add_pow]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [one_pow, one_mul, mul_comm]
    rw [hbin, Finset.sum_mul]
    refine Finset.sum_le_sum fun i hi => ?_
    have hi' : i ≤ n := by
      have := Nat.lt_succ_iff.1 (Finset.mem_range.1 hi); omega
    rw [abs_mul, abs_mul, Nat.abs_cast, abs_pow, abs_of_nonneg hlN]
    exact mul_le_mul_of_nonneg_left (abs_momentTail_le β a hβ p hL hμ hi' hN) (by positivity)
  rw [abs_mul, abs_of_nonneg (Real.rpow_nonneg hN0.le _)]
  calc N ^ (-t.1) * |∑ i ∈ Finset.range (t.2.1 + 1),
        (t.2.1.choose i : ℝ) * (Real.log N) ^ (t.2.1 - i) * momentTail β a p t.1 i N|
      ≤ 1 * ((1 + Real.log N) ^ t.2.1 * logTailMoment β a L n p N) :=
        mul_le_mul hNμ hsum (abs_nonneg _) zero_le_one
    _ ≤ 1 * ((1 + Real.log N) ^ n * logTailMoment β a L n p N) := by
        gcongr
        linarith
    _ = _ := one_mul _

/-! ### Low-spectrum tails of a density list and of a phase order -/

/-- The low-spectrum tail part of a density list. -/
noncomputable def lowTail (β a : ℝ) (p : ℕ) (N L : ℝ) (c : PowLogRep) : ℝ :=
  (c.map fun t => if t.1 < L then entryTail β a p N t else 0).sum

theorem lowSum_add_lowTail (β a : ℝ) (hβ : 0 < β) (p : ℕ) {N : ℝ} (hN : 1 ≤ N) (L : ℝ)
    (c : PowLogRep) (hpos : ∀ t ∈ c, 0 < t.1) :
    lowSum β a p N L c + lowTail β a p N L c = lowMain β a p N L c := by
  unfold lowSum lowMain lowTail
  rw [← List.sum_map_add]
  refine congrArg List.sum (List.map_congr_left fun t ht => ?_)
  split_ifs
  · rw [entryTrunc_eq_main_sub_tail β a hβ p hN (hpos t ht)]
    ring
  · ring

theorem lowSum_eq_main_sub_tail (β a : ℝ) (hβ : 0 < β) (p : ℕ) {N : ℝ} (hN : 1 ≤ N) (L : ℝ)
    (c : PowLogRep) (hpos : ∀ t ∈ c, 0 < t.1) :
    lowSum β a p N L c = lowMain β a p N L c - lowTail β a p N L c :=
  eq_sub_of_add_eq (lowSum_add_lowTail β a hβ p hN L c hpos)

theorem abs_lowTail_le (β a : ℝ) (hβ : 0 < β) (p : ℕ) {L : ℝ} (hL : 0 < L) {n : ℕ} {N : ℝ}
    (hN : 1 ≤ N) (c : PowLogRep) (hpos : ∀ t ∈ c, 0 < t.1) (hdeg : ∀ t ∈ c, t.2.1 ≤ n) :
    |lowTail β a p N L c| ≤ (c.map fun t => |t.2.2|).sum *
      ((1 + Real.log N) ^ n * logTailMoment β a L n p N) := by
  have hM : 0 ≤ (1 + Real.log N) ^ n * logTailMoment β a L n p N :=
    mul_nonneg (pow_nonneg (by linarith [Real.log_nonneg hN]) _)
      (logTailMoment_nonneg β a L n p (by linarith))
  induction c with
  | nil => simp [lowTail]
  | cons t c ih =>
    have ht := hdeg t (List.mem_cons.2 (Or.inl rfl))
    have ht0 := hpos t (List.mem_cons.2 (Or.inl rfl))
    have ih' := ih (fun s hs => hpos s (List.mem_cons.2 (Or.inr hs)))
      (fun s hs => hdeg s (List.mem_cons.2 (Or.inr hs)))
    simp only [lowTail, List.map_cons, List.sum_cons] at ih' ⊢
    rw [add_mul]
    refine (abs_add_le _ _).trans (add_le_add ?_ ih')
    split_ifs with h1
    · exact abs_entryTail_le β a hβ p hL hN ht0 h1.le ht
    · rw [abs_zero]
      exact mul_nonneg (abs_nonneg _) hM

/-- The low-spectrum tail part of one phase order. -/
noncomputable def tailPart (n : ℕ) (h k : Fin (n + 1) → ℕ) (β a : ℝ) (p : ℕ) (N L : ℝ)
    (P : MonoRep (n + 1)) : ℝ :=
  (∏ i, 1 / (2 * (k i : ℝ))) * (P.map fun s => s.2 *
    lowTail β a p N L (stateDensityRep n (monoWeights (h + s.1) k))).sum

theorem lowPart_eq_main_sub_tail (n : ℕ) (h k : Fin (n + 1) → ℕ) (hk : ∀ i, 0 < k i) (β a : ℝ)
    (hβ : 0 < β) (p : ℕ) {N : ℝ} (hN : 1 ≤ N) (L : ℝ) (P : MonoRep (n + 1)) :
    lowPart n h k β a p N L P = mainPart n h k β a p N L P - tailPart n h k β a p N L P := by
  refine eq_sub_of_add_eq ?_
  unfold lowPart mainPart tailPart
  rw [← mul_add, ← List.sum_map_add]
  congr 1
  refine congrArg List.sum (List.map_congr_left fun s _ => ?_)
  rw [← mul_add]
  congr 1
  exact lowSum_add_lowTail β a hβ p hN L _ (stateDensityRep_monoWeights_pos n (h + s.1) k hk)

theorem abs_tailPart_le (n : ℕ) (h k : Fin (n + 1) → ℕ) (hk : ∀ i, 0 < k i) (β a : ℝ)
    (hβ : 0 < β) (p : ℕ) {L : ℝ} (hL : 0 < L) {N : ℝ} (hN : 1 ≤ N) (P : MonoRep (n + 1)) :
    |tailPart n h k β a p N L P| ≤ (∏ i, 1 / (2 * (k i : ℝ))) * l1 P *
      (((n + 1).factorial : ℝ) * (latticeQ k : ℝ) ^ n) *
      ((1 + Real.log N) ^ n * logTailMoment β a L n p N) := by
  have hM : 0 ≤ (1 + Real.log N) ^ n * logTailMoment β a L n p N :=
    mul_nonneg (pow_nonneg (by linarith [Real.log_nonneg hN]) _)
      (logTailMoment_nonneg β a L n p (by linarith))
  have hK : 0 ≤ ∏ i, 1 / (2 * (k i : ℝ)) := Finset.prod_nonneg fun i _ => by positivity
  unfold tailPart
  rw [abs_mul, abs_of_nonneg hK, mul_assoc, mul_assoc]
  refine mul_le_mul_of_nonneg_left ?_ hK
  induction P with
  | nil => simp [l1]
  | cons s P ih =>
    rw [List.map_cons, List.sum_cons, l1_cons, add_mul]
    refine (abs_add_le _ _).trans (add_le_add ?_ ih)
    rw [abs_mul]
    refine mul_le_mul_of_nonneg_left ?_ (abs_nonneg _)
    refine (abs_lowTail_le β a hβ p hL hN _ (stateDensityRep_monoWeights_pos n _ k hk)
      (stateDensityRep_degree_le n _)).trans ?_
    exact mul_le_mul_of_nonneg_right (sum_abs_stateDensityRep_le n (h + s.1) k hk) hM

/-! ### The summed low-spectrum tail -/

/-- The tail series `∑_p β^p/p! tailPart_p`. -/
noncomputable def tailSeries (n : ℕ) (h k : Fin (n + 1) → ℕ) (β N L : ℝ) (ξ η : MonoRep (n + 1)) :
    ℝ :=
  ∑' p : ℕ, β ^ p / (p.factorial : ℝ) *
    tailPart n h k β (eval ξ 0) p N L (mul η (pow (fluct ξ) p))

theorem tailTerm_le (n : ℕ) (h k : Fin (n + 1) → ℕ) (hk : ∀ i, 0 < k i) (β : ℝ) (hβ : 0 < β)
    {L : ℝ} (hL : 0 < L) {N : ℝ} (hN : 1 ≤ N) (ξ η : MonoRep (n + 1)) (p : ℕ) :
    ‖β ^ p / (p.factorial : ℝ) * tailPart n h k β (eval ξ 0) p N L (mul η (pow (fluct ξ) p))‖ ≤
      ((∏ i, 1 / (2 * (k i : ℝ))) * l1 η * (((n + 1).factorial : ℝ) * (latticeQ k : ℝ) ^ n) *
        (1 + Real.log N) ^ n) *
        ((β * l1 (fluct ξ)) ^ p / (p.factorial : ℝ) * logTailMoment β (eval ξ 0) L n p N) := by
  have hM : 0 ≤ (1 + Real.log N) ^ n * logTailMoment β (eval ξ 0) L n p N :=
    mul_nonneg (pow_nonneg (by linarith [Real.log_nonneg hN]) _)
      (logTailMoment_nonneg _ _ _ _ _ (by linarith))
  have hK : 0 ≤ ∏ i, 1 / (2 * (k i : ℝ)) := Finset.prod_nonneg fun i _ => by positivity
  have hD : 0 ≤ ((n + 1).factorial : ℝ) * (latticeQ k : ℝ) ^ n := by positivity
  have hb : 0 ≤ β ^ p / (p.factorial : ℝ) := by positivity
  have hl1 : l1 (mul η (pow (fluct ξ) p)) ≤ l1 η * l1 (fluct ξ) ^ p := by
    rw [l1_mul]
    exact mul_le_mul_of_nonneg_left (l1_pow_le _ _) (l1_nonneg η)
  rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg hb]
  calc β ^ p / (p.factorial : ℝ) *
        |tailPart n h k β (eval ξ 0) p N L (mul η (pow (fluct ξ) p))|
      ≤ β ^ p / (p.factorial : ℝ) * ((∏ i, 1 / (2 * (k i : ℝ))) *
          (l1 η * l1 (fluct ξ) ^ p) * (((n + 1).factorial : ℝ) * (latticeQ k : ℝ) ^ n) *
          ((1 + Real.log N) ^ n * logTailMoment β (eval ξ 0) L n p N)) := by
        refine mul_le_mul_of_nonneg_left ((abs_tailPart_le n h k hk β _ hβ p hL hN _).trans ?_) hb
        exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left hl1 hK) hD) hM
    _ = _ := by rw [mul_pow]; ring

theorem hasSum_tailMajorant (n : ℕ) (k : Fin (n + 1) → ℕ) (β : ℝ) (hβ : 0 < β) {L : ℝ}
    (hL : 0 < L) {N : ℝ} (hN : 1 ≤ N) (ξ η : MonoRep (n + 1)) :
    HasSum (fun p : ℕ =>
      ((∏ i, 1 / (2 * (k i : ℝ))) * l1 η * (((n + 1).factorial : ℝ) * (latticeQ k : ℝ) ^ n) *
        (1 + Real.log N) ^ n) *
        ((β * l1 (fluct ξ)) ^ p / (p.factorial : ℝ) * logTailMoment β (eval ξ 0) L n p N))
      (((∏ i, 1 / (2 * (k i : ℝ))) * l1 η * (((n + 1).factorial : ℝ) * (latticeQ k : ℝ) ^ n) *
        (1 + Real.log N) ^ n) * logTailMoment β (eval ξ 0 + l1 (fluct ξ)) L n 0 N) := by
  have hs := (summable_logTailMoment_series β (eval ξ 0) (l1 (fluct ξ)) L hβ hL (l1_nonneg _) n
    (by linarith : (0 : ℝ) ≤ N)).hasSum.mul_left
    ((∏ i, 1 / (2 * (k i : ℝ))) * l1 η * (((n + 1).factorial : ℝ) * (latticeQ k : ℝ) ^ n) *
      (1 + Real.log N) ^ n)
  rwa [tsum_logTailMoment_series β (eval ξ 0) (l1 (fluct ξ)) L hβ hL (l1_nonneg _) n
    (by linarith : (0 : ℝ) ≤ N)] at hs

theorem summable_tailSeries_terms (n : ℕ) (h k : Fin (n + 1) → ℕ) (hk : ∀ i, 0 < k i) (β : ℝ)
    (hβ : 0 < β) {L : ℝ} (hL : 0 < L) {N : ℝ} (hN : 1 ≤ N) (ξ η : MonoRep (n + 1)) :
    Summable fun p : ℕ => β ^ p / (p.factorial : ℝ) *
      tailPart n h k β (eval ξ 0) p N L (mul η (pow (fluct ξ) p)) :=
  Summable.of_norm_bounded (hasSum_tailMajorant n k β hβ hL hN ξ η).summable
    (tailTerm_le n h k hk β hβ hL hN ξ η)

/-- The `N`-free constant of the low-spectrum tail bound. -/
noncomputable def tailSeriesConst (n : ℕ) (k : Fin (n + 1) → ℕ) (β L : ℝ)
    (ξ η : MonoRep (n + 1)) : ℝ :=
  (∏ i, 1 / (2 * (k i : ℝ))) * l1 η * (((n + 1).factorial : ℝ) * (latticeQ k : ℝ) ^ n) *
    (tailConst β (eval ξ 0 + l1 (fluct ξ)) 0 L n * (4 / β) *
      ((⌈L⌉₊.factorial : ℝ) * (4 / β) ^ ⌈L⌉₊))

/-- **Summed low-spectrum tail bound**: `|tailSeries| ≤ tailSeriesConst · N^{-L}(1+log N)^n`. -/
theorem abs_tailSeries_le (n : ℕ) (h k : Fin (n + 1) → ℕ) (hk : ∀ i, 0 < k i) (β : ℝ)
    (hβ : 0 < β) {L : ℝ} (hL : 0 < L) {N : ℝ} (hN : 1 ≤ N) (ξ η : MonoRep (n + 1)) :
    |tailSeries n h k β N L ξ η| ≤
      tailSeriesConst n k β L ξ η * (N ^ (-L) * (1 + Real.log N) ^ n) := by
  have h1 := tsum_of_norm_bounded (hasSum_tailMajorant n k β hβ hL hN ξ η)
    (tailTerm_le n h k hk β hβ hL hN ξ η)
  rw [Real.norm_eq_abs] at h1
  refine h1.trans ?_
  have hK : 0 ≤ ∏ i, 1 / (2 * (k i : ℝ)) := Finset.prod_nonneg fun i _ => by positivity
  have hpre : 0 ≤ (∏ i, 1 / (2 * (k i : ℝ))) * l1 η *
      (((n + 1).factorial : ℝ) * (latticeQ k : ℝ) ^ n) * (1 + Real.log N) ^ n :=
    mul_nonneg (mul_nonneg (mul_nonneg hK (l1_nonneg η)) (by positivity))
      (pow_nonneg (by linarith [Real.log_nonneg hN]) _)
  have hT := (logTailMoment_le β (eval ξ 0 + l1 (fluct ξ)) L hβ n hN).trans
    (mul_le_mul_of_nonneg_left (exp_le_rpow_const β L hβ hN)
      (mul_nonneg (tailConst_nonneg β _ hβ 0 L n) (by positivity)))
  calc _ ≤ ((∏ i, 1 / (2 * (k i : ℝ))) * l1 η *
        (((n + 1).factorial : ℝ) * (latticeQ k : ℝ) ^ n) * (1 + Real.log N) ^ n) *
        (tailConst β (eval ξ 0 + l1 (fluct ξ)) 0 L n * (4 / β) *
          (((⌈L⌉₊.factorial : ℝ) * (4 / β) ^ ⌈L⌉₊) * N ^ (-L))) :=
        mul_le_mul_of_nonneg_left hT hpre
    _ = _ := by unfold tailSeriesConst; ring

/-! ### Assembly: the quantitative cutoff theorem -/

theorem lowSeries_eq_main_sub_tail (n : ℕ) (h k : Fin (n + 1) → ℕ) (hk : ∀ i, 0 < k i) (β : ℝ)
    (hβ : 0 < β) {L : ℝ} (hL : 0 < L) {N : ℝ} (hN : 1 ≤ N) (ξ η : MonoRep (n + 1)) :
    lowSeries n h k β N L ξ η = mainSeries n h k β N L ξ η - tailSeries n h k β N L ξ η := by
  have hlow := summable_lowSeries_terms n h k hk β hβ hL hN ξ η
  have htail := summable_tailSeries_terms n h k hk β hβ hL hN ξ η
  have hsplit : ∀ p : ℕ, β ^ p / (p.factorial : ℝ) *
      mainPart n h k β (eval ξ 0) p N L (mul η (pow (fluct ξ) p)) =
      β ^ p / (p.factorial : ℝ) * lowPart n h k β (eval ξ 0) p N L (mul η (pow (fluct ξ) p)) +
        β ^ p / (p.factorial : ℝ) *
          tailPart n h k β (eval ξ 0) p N L (mul η (pow (fluct ξ) p)) := fun p => by
    rw [lowPart_eq_main_sub_tail n h k hk β _ hβ p hN L]
    ring
  unfold lowSeries mainSeries tailSeries
  rw [tsum_congr hsplit, hlow.tsum_add htail]
  ring

/-- The constant of the cutoff theorem: high-spectrum plus low-spectrum-tail contributions. -/
noncomputable def taylorCutoffConst (n : ℕ) (k : Fin (n + 1) → ℕ) (β L : ℝ)
    (ξ η : MonoRep (n + 1)) : ℝ :=
  highConst n k β L ξ η + tailSeriesConst n k β L ξ η

/-- **The polynomial Taylor tree, exact form**: `Z(N)` minus the spectral sum below the cutoff is
the high-spectrum remainder minus the low-spectrum tail. -/
theorem polyPhaseIntegral_sub_spectralSum (n : ℕ) (h k : Fin (n + 1) → ℕ) (hk : ∀ i, 0 < k i)
    (β : ℝ) (hβ : 0 < β) {L : ℝ} (hL : 0 < L) {N : ℝ} (hN : 1 ≤ N) (ξ η : MonoRep (n + 1)) :
    polyPhaseIntegral n h k β N ξ η - ∑ μ ∈ latticeBelow (latticeQ k) L, N ^ (-μ) *
        ∑ j ∈ Finset.range (n + 1), spectralCoeff n h k β ξ η μ j * (Real.log N) ^ j =
      highRemainder n h k β N L ξ η - tailSeries n h k β N L ξ η := by
  rw [polyPhaseIntegral_eq_low_add_high n h k hk β hβ hL hN ξ η,
    lowSeries_eq_main_sub_tail n h k hk β hβ hL hN ξ η, mainSeries_eq_sum n h k hk β hβ N L ξ η]
  ring

/-- **Headline XXV — quantitative polynomial Taylor tree.** For polynomial phase `ξ` and
amplitude `η`, `β > 0`, positive `k`, every cutoff `L > 0` and every `N ≥ 1`,
`|Z(N) - ∑_{μ ∈ Λ_L} N^{-μ} ∑_{j ≤ n} A_{μ,j} (log N)^j| ≤ taylorCutoffConst · N^{-L} (1+log N)^n`,
with `A_{μ,j}` independent of `L` and `N`. -/
theorem taylorTree_cutoff_bound (n : ℕ) (h k : Fin (n + 1) → ℕ) (hk : ∀ i, 0 < k i) (β : ℝ)
    (hβ : 0 < β) {L : ℝ} (hL : 0 < L) {N : ℝ} (hN : 1 ≤ N) (ξ η : MonoRep (n + 1)) :
    |polyPhaseIntegral n h k β N ξ η - ∑ μ ∈ latticeBelow (latticeQ k) L, N ^ (-μ) *
        ∑ j ∈ Finset.range (n + 1), spectralCoeff n h k β ξ η μ j * (Real.log N) ^ j| ≤
      taylorCutoffConst n k β L ξ η * (N ^ (-L) * (1 + Real.log N) ^ n) := by
  rw [polyPhaseIntegral_sub_spectralSum n h k hk β hβ hL hN ξ η]
  refine (abs_sub _ _).trans ?_
  unfold taylorCutoffConst
  rw [add_mul]
  exact add_le_add (abs_highRemainder_le n h k hk β hβ hL hN ξ η)
    (abs_tailSeries_le n h k hk β hβ hL hN ξ η)

end Laplace.Grammar
