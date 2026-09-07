/-
Copyright (c) 2026 Timaeus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Laplace.Grammar.BoxScaling

/-!
# The Taylor tree on a general box `(0,b]^d` (Stage 4i)

Unit 249 (Taylor-tree programme; Astra #28 candidate D, second half). Combining the scaling identity
`Z_b(N) = b^{|h|+d} Z_1(N b^{2|k|}; ξ(b·), η(b·))` (unit 248) with Headline XXVII at the rescaled
sample size gives, for coefficient families with finite weighted mass `∑ |c_γ| b^{|γ|}` and every
`L > 0`:

**Headline XXVIII** (`boxTaylorTree_cutoff_bound`): for `N ≥ 1` with `N b^{2|k|} ≥ 1`,
```
|Z_b(N) − b^{|h|+d} ∑_{μ ∈ Λ_L} (N b^{2|k|})^{-μ} ∑_{j ≤ d-1} A^b_{μ,j} (log(N b^{2|k|}))^j|
  ≤ b^{|h|+d} · cutoffBound · (N b^{2|k|})^{-L} (1 + log(N b^{2|k|}))^{d-1},
```
with `A^b_{μ,j}` the family coefficients of the rescaled data. In the sample size `N` this is
`O(N^{-L}(1+log N)^{d-1})` (`boxTaylorTree_isBigO`), and the spectral sum is `∑_μ N^{-μ} P_μ(log N)`
with
`P_μ` a polynomial of degree `≤ d-1` whose coefficients are obtained by the binomial re-expansion
`(log N + 2|k| log b)^j` (`boxSpectralSum_eq`, `boxCoeff`): the paper's
`∑_μ ∑_{m=1}^d C_{μ,m} n^{-μ} (log n)^{m-1}` on `[0,b]^d`. No `sorry` and no additional `axiom`
declarations.
-/

open MeasureTheory Set Real Filter Topology Asymptotics

namespace Laplace.Grammar

open MonoRep CoeffFamily

/-- The rescaled sample size `N b^{2|k|}`. -/
noncomputable def boxScale {d : ℕ} (k : Fin d → ℕ) (b N : ℝ) : ℝ := N * b ^ (2 * ∑ i, k i)

/-- The spectral sum on the box `(0,b]^d` (in the rescaled sample size). -/
noncomputable def boxSpectralSum (n : ℕ) (h k : Fin (n + 1) → ℕ) (β L b : ℝ)
    (cξ cη : CoeffFamily (n + 1)) (N : ℝ) : ℝ :=
  b ^ (∑ i, h i + (n + 1)) *
    familySpectralSum n h k β L (scale cξ b) (scale cη b) (boxScale k b N)

/-- **Headline XXVIII — the Taylor tree on `(0,b]^d`, quantitative form.** -/
theorem boxTaylorTree_cutoff_bound (n : ℕ) (h k : Fin (n + 1) → ℕ) (hk : ∀ i, 0 < k i) (β : ℝ)
    (hβ : 0 < β) {L b : ℝ} (hL : 0 < L) (hb : 0 < b) {N : ℝ} (hN : 0 ≤ N)
    (hN' : 1 ≤ boxScale k b N) {cξ cη : CoeffFamily (n + 1)} (hξ : AbsSummableAt cξ b)
    (hη : AbsSummableAt cη b) :
    |familyPhaseIntegralBox n h k β N b cξ cη - boxSpectralSum n h k β L b cξ cη N| ≤
      b ^ (∑ i, h i + (n + 1)) *
        cutoffBound n k β L (scale cξ b 0) (mass (scale cη b)) (mass (scale cξ b)) *
        (boxScale k b N ^ (-L) * (1 + Real.log (boxScale k b N)) ^ n) := by
  rw [familyPhaseIntegralBox_eq n h k β hN hb, boxSpectralSum, ← mul_sub, abs_mul,
    abs_of_nonneg (pow_nonneg hb.le _), mul_assoc]
  refine mul_le_mul_of_nonneg_left ?_ (pow_nonneg hb.le _)
  exact familyTaylorTree_cutoff_bound n h k hk β hβ hL hN' (AbsSummable.of_scale hb.le hξ)
    (AbsSummable.of_scale hb.le hη)

theorem cutoffBound_nonneg (n : ℕ) (k : Fin (n + 1) → ℕ) (β : ℝ) (hβ : 0 < β) (L a : ℝ) {E : ℝ}
    (hE : 0 ≤ E) (B : ℝ) : 0 ≤ cutoffBound n k β L a E B := by
  unfold cutoffBound
  have hK : 0 ≤ ∏ i, 1 / (2 * (k i : ℝ)) := Finset.prod_nonneg fun i _ => by positivity
  have hM := phaseLogMoment_nonneg β (|a| + B) L n 0
  have hT := tailConst_nonneg β (|a| + B) hβ 0 L n
  have hD : (0 : ℝ) ≤ ((n + 1).factorial : ℝ) * (latticeQ k : ℝ) ^ n := by positivity
  have h4 : (0 : ℝ) ≤ 4 / β := by positivity
  have h5 : (0 : ℝ) ≤ (⌈L⌉₊.factorial : ℝ) * (4 / β) ^ ⌈L⌉₊ := by positivity
  exact mul_nonneg (mul_nonneg (mul_nonneg hK hE) hD)
    (add_nonneg hM (mul_nonneg (mul_nonneg hT h4) h5))

/-- `1 + log(N c) ≤ (1 + |log c|)(1 + log N)` for `N ≥ 1`, `c > 0`. -/
theorem one_add_log_mul_le {N c : ℝ} (hN : 1 ≤ N) (hc : 0 < c) :
    1 + Real.log (N * c) ≤ (1 + |Real.log c|) * (1 + Real.log N) := by
  rw [Real.log_mul (by linarith) hc.ne']
  have h1 := Real.log_nonneg hN
  have h2 := le_abs_self (Real.log c)
  have h3 := abs_nonneg (Real.log c)
  nlinarith

/-- **Headline XXVIII, `IsBigO` form in the sample size**: `Z_b(N) − boxSpectralSum(N) =
O(N^{-L}(1+log N)^{d-1})`. -/
theorem boxTaylorTree_isBigO (n : ℕ) (h k : Fin (n + 1) → ℕ) (hk : ∀ i, 0 < k i) (β : ℝ)
    (hβ : 0 < β) {L b : ℝ} (hL : 0 < L) (hb : 0 < b) {cξ cη : CoeffFamily (n + 1)}
    (hξ : AbsSummableAt cξ b) (hη : AbsSummableAt cη b) :
    (fun N : ℝ => familyPhaseIntegralBox n h k β N b cξ cη - boxSpectralSum n h k β L b cξ cη N)
      =O[atTop] fun N : ℝ => N ^ (-L) * (1 + Real.log N) ^ n := by
  set c : ℝ := b ^ (2 * ∑ i, k i) with hc
  have hc0 : 0 < c := pow_pos hb _
  set C : ℝ := b ^ (∑ i, h i + (n + 1)) *
    cutoffBound n k β L (scale cξ b 0) (mass (scale cη b)) (mass (scale cξ b)) with hC
  have hC0 : 0 ≤ C :=
    mul_nonneg (pow_nonneg hb.le _) (cutoffBound_nonneg n k β hβ L _ (mass_nonneg _) _)
  refine IsBigO.of_bound (C * c ^ (-L) * (1 + |Real.log c|) ^ n) ?_
  filter_upwards [eventually_ge_atTop (max 1 c⁻¹)] with N hN
  have hN1 : 1 ≤ N := le_trans (le_max_left _ _) hN
  have hNc : 1 ≤ boxScale k b N := by
    unfold boxScale; rw [← hc]
    calc (1 : ℝ) = c⁻¹ * c := (inv_mul_cancel₀ hc0.ne').symm
      _ ≤ N * c := mul_le_mul_of_nonneg_right (le_trans (le_max_right _ _) hN) hc0.le
  have hbound := boxTaylorTree_cutoff_bound n h k hk β hβ hL hb (zero_le_one.trans hN1) hNc hξ hη
  rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg (mul_nonneg
    (Real.rpow_nonneg (by linarith) _)
    (pow_nonneg (by linarith [Real.log_nonneg hN1]) _))]
  refine hbound.trans ?_
  have hlog : (1 + Real.log (boxScale k b N)) ^ n ≤
      ((1 + |Real.log c|) * (1 + Real.log N)) ^ n := by
    refine pow_le_pow_left₀ ?_ (one_add_log_mul_le hN1 hc0) n
    have : 0 ≤ Real.log (N * c) := Real.log_nonneg hNc
    linarith
  have hrpow : boxScale k b N ^ (-L) = N ^ (-L) * c ^ (-L) := by
    unfold boxScale; rw [← hc]; exact Real.mul_rpow (by linarith) hc0.le
  rw [← hC, hrpow]
  calc C * (N ^ (-L) * c ^ (-L) * (1 + Real.log (boxScale k b N)) ^ n)
      ≤ C * (N ^ (-L) * c ^ (-L) * ((1 + |Real.log c|) * (1 + Real.log N)) ^ n) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hlog (by positivity)) hC0
    _ = _ := by rw [mul_pow]; ring

/-! ### The paper's form: a polynomial in `log N` at each exponent -/

/-- The box coefficients
`C^b_{μ,j'} = b^{|h|+d} c^{-μ} ∑_{q ≥ j'} A^b_{μ,q} C(q,j') (log c)^{q-j'}`,
`c = b^{2|k|}`. -/
noncomputable def boxCoeff (n : ℕ) (h k : Fin (n + 1) → ℕ) (β b : ℝ) (cξ cη : CoeffFamily (n + 1))
    (μ : ℝ) (j : ℕ) : ℝ :=
  b ^ (∑ i, h i + (n + 1)) * (b ^ (2 * ∑ i, k i)) ^ (-μ) *
    ∑ q ∈ Finset.Ico j (n + 1), familySpectralCoeff n h k β (scale cξ b) (scale cη b) μ q *
      (q.choose j : ℝ) * (Real.log (b ^ (2 * ∑ i, k i))) ^ (q - j)

/-- **The box spectral sum in the sample size `N`**:
`∑_μ N^{-μ} ∑_{j ≤ d-1} C^b_{μ,j} (log N)^j`. -/
theorem boxSpectralSum_eq (n : ℕ) (h k : Fin (n + 1) → ℕ) (β L : ℝ) {b : ℝ} (hb : 0 < b)
    (cξ cη : CoeffFamily (n + 1)) {N : ℝ} (hN : 0 < N) :
    boxSpectralSum n h k β L b cξ cη N = ∑ μ ∈ latticeBelow (latticeQ k) L, N ^ (-μ) *
      ∑ j ∈ Finset.range (n + 1), boxCoeff n h k β b cξ cη μ j * (Real.log N) ^ j := by
  unfold boxSpectralSum familySpectralSum boxCoeff boxScale
  set c : ℝ := b ^ (2 * ∑ i, k i) with hc
  have hc0 : 0 < c := pow_pos hb _
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun μ _ => ?_
  rw [Real.mul_rpow hN.le hc0.le, Real.log_mul hN.ne' hc0.ne']
  -- expand `(log N + log c)^q` binomially and swap the sums
  have hbin : ∀ q : ℕ, (Real.log N + Real.log c) ^ q =
      ∑ j ∈ Finset.range (q + 1), (q.choose j : ℝ) * (Real.log c) ^ (q - j) * (Real.log N) ^ j := by
    intro q
    rw [add_pow]
    refine Finset.sum_congr rfl fun j _ => ?_
    ring
  simp_rw [hbin, Finset.mul_sum]
  rw [Finset.sum_comm' (t' := Finset.range (n + 1)) (s' := fun j => Finset.Ico j (n + 1))]
  · refine Finset.sum_congr rfl fun j _ => ?_
    rw [Finset.sum_mul, Finset.mul_sum]
    refine Finset.sum_congr rfl fun q _ => ?_
    ring
  · intro q j
    simp only [Finset.mem_range, Finset.mem_Ico]
    omega

end Laplace.Grammar
