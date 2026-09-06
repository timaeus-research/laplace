/-
Copyright (c) 2026 Timaeus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Laplace.Grammar.IterChartMixed

/-!
# Complete expansions of the chart integrals with arbitrary `(k, h)` (grammar §4.2)

Every chart integral reduced in units 50 and 52 has the shape
`Z(√n) = K (√n)^{-p} D H_j(√n b^S)` for a divide-and-integrate tower `H` on an admissible base with
tail rate `ε`. The expansion of unit 49/51 then gives, uniformly,

  `Z(√n) = n^{-p/2} K D ∑_{i ≤ j} c_{j,i} (log n / 2 + S log b)^i + O(n^{-p/2 - ε/2})`.

Instances: the all-equal case with arbitrary `(k, h)` (`ε = 1`, remainder `O(n^{-(p+1)/2})`) and the
mixed case with one noncritical inner coordinate (`ε = q − p`). A bridge lemma identifies unit 39's
`iterChart` with `iterChartGen` at `k = 1`, `h = 0`. Zero `sorry`/`axiom`.
-/

open Real MeasureTheory Set Asymptotics Filter Topology

namespace Laplace.Grammar

/-- The polynomial coefficient of a tower expansion, as a function of `n`. -/
noncomputable def towerCoeff (G : ℝ → ℝ) (A : ℝ) (j : ℕ) (b : ℝ) (S : ℕ) (n : ℝ) : ℝ :=
  ∑ i ∈ Finset.range (j + 1), divCoeff G A j i * (Real.log n / 2 + (S : ℝ) * Real.log b) ^ i

/-- **Generic complete expansion**: if `Z(√n) = K (√n)^{-p} D H_j(√n b^S)` for an admissible tower,
then `Z(√n) = n^{-p/2} K D · towerCoeff(n) + O(n^{-p/2 - ε/2})`. -/
theorem tower_expansion_isBigO {G : ℝ → ℝ} {A M C δ ε : ℝ} (hG : LogBase G A M C δ ε) (j : ℕ)
    (K D p b : ℝ) (S : ℕ) (hb : 0 < b) (Z : ℝ → ℝ)
    (hZ : ∀ n, 0 < n → Z n = K * (Real.sqrt n) ^ (-p) * D * iterDivPrim G j (Real.sqrt n * b ^ S)) :
    (fun n : ℝ => Z n - n ^ (-(p / 2)) * (K * D * towerCoeff G A j b S n))
      =O[atTop] fun n : ℝ => n ^ (-(p / 2) - ε / 2) := by
  have hε := hG.ε_pos
  have hM : 0 ≤ M := by
    have := hG.tail 1 le_rfl
    rw [Real.one_rpow, mul_one] at this
    exact (abs_nonneg _).trans this
  apply IsBigO.of_bound (|K * D| * (M / ε ^ j) * b ^ (-(S : ℝ) * ε))
  filter_upwards [eventually_ge_atTop (1 : ℝ), eventually_ge_atTop (1 / b ^ (2 * S))] with n hn hnb
  have hn0 : (0 : ℝ) < n := by linarith
  have hsn : 0 < Real.sqrt n := Real.sqrt_pos.2 hn0
  have hL : 1 ≤ Real.sqrt n * b ^ S := by
    have h1 : (1 / b ^ S) ^ 2 ≤ n := by rw [div_pow, one_pow, ← pow_mul, mul_comm]; exact hnb
    have h2 : 1 / b ^ S ≤ Real.sqrt n := by rw [Real.le_sqrt (by positivity) hn0.le]; exact h1
    calc (1 : ℝ) = 1 / b ^ S * b ^ S := by field_simp
      _ ≤ Real.sqrt n * b ^ S := by gcongr
  have hlogL : Real.log (Real.sqrt n * b ^ S) = Real.log n / 2 + (S : ℝ) * Real.log b := by
    rw [Real.log_mul hsn.ne' (by positivity), Real.log_sqrt hn0.le, Real.log_pow]
  have hθ := iterDivPrim_expansion hG j _ hL
  rw [hlogL] at hθ
  have hpow : (Real.sqrt n) ^ (-p) = n ^ (-(p / 2)) := by
    rw [Real.sqrt_eq_rpow, ← Real.rpow_mul hn0.le]
    congr 1
    ring
  have h1 : (Real.sqrt n) ^ (-ε) = n ^ (-(ε / 2)) := by
    rw [Real.sqrt_eq_rpow, ← Real.rpow_mul hn0.le]
    congr 1
    ring
  have h2 : ((b ^ S : ℝ)) ^ (-ε) = b ^ (-(S : ℝ) * ε) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hb.le]
    congr 1
    ring
  have hLε : (Real.sqrt n * b ^ S) ^ (-ε) = b ^ (-(S : ℝ) * ε) * n ^ (-(ε / 2)) := by
    rw [Real.mul_rpow hsn.le (by positivity), h1, h2, mul_comm]
  set H := iterDivPrim G j (Real.sqrt n * b ^ S) with hH
  set P := towerCoeff G A j b S n with hP
  have hθ' : |H - P| ≤ M / ε ^ j * (b ^ (-(S : ℝ) * ε) * n ^ (-(ε / 2))) := by
    rw [← hLε, hP, towerCoeff]
    exact hθ
  rw [hZ n hn0, hpow, Real.norm_eq_abs, Real.norm_eq_abs, abs_of_pos (Real.rpow_pos_of_pos hn0 _),
    show K * n ^ (-(p / 2)) * D * H - n ^ (-(p / 2)) * (K * D * P)
      = (K * D) * n ^ (-(p / 2)) * (H - P) by ring,
    abs_mul, abs_mul, abs_of_pos (Real.rpow_pos_of_pos hn0 (-(p / 2)))]
  calc |K * D| * n ^ (-(p / 2)) * |H - P|
      ≤ |K * D| * n ^ (-(p / 2)) * (M / ε ^ j * (b ^ (-(S : ℝ) * ε) * n ^ (-(ε / 2)))) :=
        mul_le_mul_of_nonneg_left hθ' (by positivity)
    _ = |K * D| * (M / ε ^ j) * b ^ (-(S : ℝ) * ε) * n ^ (-(p / 2) - ε / 2) := by
        rw [show -(p / 2) - ε / 2 = -(p / 2) + -(ε / 2) by ring, Real.rpow_add hn0]
        ring

/-- **Complete expansion, all exponents equal, arbitrary `(k, h)`**:
`Z_{d+2}(√n) = n^{-p/2} (∏ k_i^{-1}) ∑_{i ≤ d+1} c_{d+1,i} (log n/2 + S log b)^i + O(n^{-(p+1)/2})`,
`S = ∑ k_i`, coefficients of the tower on `F_{p−1}`. -/
theorem iterChartGen_expansion_isBigO (β a b : ℝ) (k h : ℕ → ℕ) (p : ℝ) (hβ : 0 < β) (hb : 0 < b)
    (hk : ∀ i, 0 < k i) (d : ℕ) (hp : ∀ i, i ≤ d + 1 → ((h i : ℝ) + 1) / k i = p) :
    (fun n : ℝ => iterChartGen β a b k h (d + 2) (Real.sqrt n)
        - n ^ (-(p / 2)) * ((∏ i ∈ Finset.range (d + 2), (1 : ℝ) / k i) * 1
          * towerCoeff (weightedPrimitive β a (p - 1)) (weightedMass β a (p - 1)) (d + 1) b
              (∑ i ∈ Finset.range (d + 2), k i) n))
      =O[atTop] fun n : ℝ => n ^ (-(p / 2) - 1 / 2) := by
  have hp0 : 0 < p := by
    rw [← hp 0 (Nat.zero_le _)]
    have := hk 0
    positivity
  have hγ : -1 < p - 1 := by linarith
  refine tower_expansion_isBigO (weightedPrimitive_logBase β a (p - 1) hβ hγ) (d + 1)
    (∏ i ∈ Finset.range (d + 2), (1 : ℝ) / k i) 1 p b (∑ i ∈ Finset.range (d + 2), k i) hb _
    fun n hn => ?_
  rw [iterChartGen_succ_eq β a b k h p hb hk (d + 1) hp (Real.sqrt n) (Real.sqrt_pos.2 hn), mul_one]

/-- **Complete expansion, mixed case**: with one noncritical inner coordinate (`q > p`),
`Z_{m+2}(√n) = n^{-p/2} (∏ k_i^{-1}) b^{k₀(q−p)} ∑ c_{m,i} (log n/2 + S log b)^i`
`+ O(n^{-p/2-(q-p)/2})`,
coefficients of the tower on the noncritical base `G₁`. -/
theorem iterChartGen_mixed_expansion_isBigO (β a b : ℝ) (k h : ℕ → ℕ) (p q : ℝ) (hβ : 0 < β)
    (hb : 0 < b) (hk : ∀ i, 0 < k i) (hq : ((h 0 : ℝ) + 1) / k 0 = q) (m : ℕ)
    (hp : ∀ i, 1 ≤ i → i ≤ m + 1 → ((h i : ℝ) + 1) / k i = p) (hlt : p < q) :
    (fun n : ℝ => iterChartGen β a b k h (m + 2) (Real.sqrt n)
        - n ^ (-(p / 2)) * ((∏ i ∈ Finset.range (m + 2), (1 : ℝ) / k i) * b ^ ((k 0 : ℝ) * (q - p))
          * towerCoeff (noLogBase β a p q) (noLogConst β a p q) m b
              (∑ i ∈ Finset.range (m + 2), k i) n))
      =O[atTop] fun n : ℝ => n ^ (-(p / 2) - (q - p) / 2) := by
  have hp0 : 0 < p := by
    rw [← hp 1 le_rfl (by omega)]
    have := hk 1
    positivity
  refine tower_expansion_isBigO (noLogBase_logBase β a p q hβ hp0 hlt) m
    (∏ i ∈ Finset.range (m + 2), (1 : ℝ) / k i) (b ^ ((k 0 : ℝ) * (q - p))) p b
    (∑ i ∈ Finset.range (m + 2), k i) hb _ fun n hn => ?_
  exact iterChartGen_mixed_eq β a b k h p q hb hk hq m hp (Real.sqrt n) (Real.sqrt_pos.2 hn)

/-- Unit 39's `iterChart` is `iterChartGen` at `k = 1`, `h = 0`. -/
theorem iterChart_eq_iterChartGen (β a b : ℝ) (d : ℕ) (c : ℝ) :
    iterChart β a b d c = iterChartGen β a b (fun _ => 1) (fun _ => 0) d c := by
  induction d generalizing c with
  | zero => rfl
  | succ d ih =>
    rw [iterChart_succ, iterChartGen_succ]
    refine setIntegral_congr_fun measurableSet_Ioc fun u _ => ?_
    rw [pow_zero, pow_one, one_mul, ih]

end Laplace.Grammar
