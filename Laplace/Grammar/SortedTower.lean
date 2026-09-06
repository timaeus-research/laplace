/-
Copyright (c) 2026 Timaeus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Laplace.Grammar.PolyLogClass

/-!
# Only minimal exponents count: sorted exponent vectors (grammar §4.2)

Let the candidate exponents `q_i = (h_i+1)/k_i` be sorted so that the first `r+1` coordinates are
non-increasing, `q_0 ≥ q_1 ≥ … ≥ q_r`, and the remaining `m+1` coordinates all equal `p < q_r`
(the minimal exponent, multiplicity `m+1`). Then the tower levels `G_1, …, G_{r+1}` stay
polylog-bounded, `G_{r+2}` is an admissible base with mass `C > 0`, and `G_{r+2+i} = H^{G_{r+2}}_i`,
so

  `Z_{r+2+m}(√n) ~ (∏ k_i^{-1}) D_{r+2+m} · C/(2^m m!) · n^{-p/2} (log n)^m`,

the general multiplicity statement of `thm:TaylorTree` for constant `ξ`: the exponent is half the
minimal candidate exponent and the power of the logarithm is the multiplicity minus one.
Zero `sorry`/`axiom`.
-/

open Real MeasureTheory Set Asymptotics Filter Topology

namespace Laplace.Grammar

theorem chartExp_pos (k h : ℕ → ℕ) (hk : ∀ i, 0 < k i) (i : ℕ) : 0 < chartExp k h i := by
  unfold chartExp
  have := hk i
  positivity

/-- **Noncritical levels stay polylog-bounded** (and positive) when the exponents are
non-increasing. -/
theorem genTower_polyLog (β a : ℝ) (k h : ℕ → ℕ) (hβ : 0 < β) (hk : ∀ i, 0 < k i) (r : ℕ)
    (hsort : ∀ i, i < r → chartExp k h (i + 1) ≤ chartExp k h i) :
    (∃ C₀ C₁ : ℝ, ∃ j : ℕ, PolyLogBounded (genTower β a k h (r + 1)) C₀ (chartExp k h r) C₁ j)
      ∧ ∀ x, 0 < x → 0 < genTower β a k h (r + 1) x := by
  have hq := chartExp_pos k h hk
  induction r with
  | zero =>
    have h1 : genTower β a k h 1 = weightedPrimitive β a (chartExp k h 0 - 1) :=
      genTower_eq_iterDivPrim β a k h (chartExp k h 0) 0 fun i hi => by rw [Nat.le_zero.1 hi]
    rw [h1]
    refine ⟨⟨_, _, 0, weightedPrimitive_polyLog β a _ hβ (hq 0)⟩, fun x hx => ?_⟩
    exact weightedPrimitive_pos β a _ x hβ (by linarith [hq 0]) hx
  | succ r ih =>
    have hsort' : ∀ i, i < r → chartExp k h (i + 1) ≤ chartExp k h i :=
      fun i hi => hsort i (Nat.lt_succ_of_lt hi)
    obtain ⟨⟨C₀, C₁, j, hG⟩, hpos⟩ := ih hsort'
    have hle := hsort r (Nat.lt_succ_self r)
    have htower : genTower β a k h (r + 1 + 1)
        = powStep (chartExp k h (r + 1) - chartExp k h r - 1) (genTower β a k h (r + 1)) := by
      rw [genTower_succ, prevExp_succ]
    have ht' : -1 < chartExp k h (r + 1) - chartExp k h r - 1 + chartExp k h r := by
      linarith [hq (r + 1)]
    rw [htower]
    refine ⟨?_, fun x hx => hG.powStep_pos hpos _ ht' x hx⟩
    rcases eq_or_lt_of_le hle with heq | hlt
    · have ht1 : chartExp k h (r + 1) - chartExp k h r - 1 = -1 := by rw [heq]; ring
      rw [ht1]
      have := hG.powStep_neg_one
      rw [← heq] at this
      exact ⟨_, _, _, this⟩
    · have htlt : chartExp k h (r + 1) - chartExp k h r - 1 < -1 := by linarith
      have := hG.powStep_of_lt _ htlt ht'
      rw [show chartExp k h (r + 1) - chartExp k h r - 1 + chartExp k h r + 1
        = chartExp k h (r + 1) by ring] at this
      exact ⟨_, _, _, this⟩

/-- The mass of the first minimal level: `C = ∫₀^∞ x^{p − q_r − 1} G_{r+1}(x) dx`. -/
noncomputable def sortedConst (β a : ℝ) (k h : ℕ → ℕ) (r : ℕ) (p : ℝ) : ℝ :=
  PolyLogBounded.powLimit (p - chartExp k h r - 1) (genTower β a k h (r + 1))

/-- **The first minimal level is an admissible base** with mass `sortedConst > 0` and tail rate
`(q_r − p)/2`. -/
theorem genTower_logBase (β a : ℝ) (k h : ℕ → ℕ) (hβ : 0 < β) (hk : ∀ i, 0 < k i) (r : ℕ) (p : ℝ)
    (hsort : ∀ i, i < r → chartExp k h (i + 1) ≤ chartExp k h i) (hp : chartExp k h (r + 1) = p)
    (hlt : p < chartExp k h r) :
    0 < sortedConst β a k h r p ∧ ∃ M C' : ℝ,
      LogBase (genTower β a k h (r + 2)) (sortedConst β a k h r p) M C' p
        ((chartExp k h r - p) / 2) := by
  obtain ⟨⟨C₀, C₁, j, hG⟩, hpos⟩ := genTower_polyLog β a k h hβ hk r hsort
  have hp0 : 0 < p := hp ▸ chartExp_pos k h hk (r + 1)
  have htower : genTower β a k h (r + 2)
      = powStep (p - chartExp k h r - 1) (genTower β a k h (r + 1)) := by
    rw [show r + 2 = r + 1 + 1 by ring, genTower_succ, prevExp_succ, hp]
  have htlt : p - chartExp k h r - 1 < -1 := by linarith
  have ht' : -1 < p - chartExp k h r - 1 + chartExp k h r := by linarith
  refine ⟨hG.powLimit_pos hpos _ htlt ht', ?_⟩
  rw [htower]
  have := hG.logBase_powStep_of_lt _ htlt ht'
  rw [show p - chartExp k h r - 1 + chartExp k h r + 1 = p by ring,
    show -(p - chartExp k h r - 1) - 1 = chartExp k h r - p by ring] at this
  exact ⟨_, _, this⟩

/-- **The minimal block is the divide-and-integrate tower** on `G_{r+2}`. -/
theorem genTower_block_eq_iterDivPrim (β a : ℝ) (k h : ℕ → ℕ) (r i : ℕ) (p : ℝ)
    (hp : ∀ l, r + 1 ≤ l → l ≤ r + 1 + i → chartExp k h l = p) :
    genTower β a k h (r + 2 + i) = iterDivPrim (genTower β a k h (r + 2)) i := by
  induction i with
  | zero => rfl
  | succ i ih =>
    have hp' : ∀ l, r + 1 ≤ l → l ≤ r + 1 + i → chartExp k h l = p :=
      fun l h1 h2 => hp l h1 (Nat.le_succ_of_le h2)
    have hcur : chartExp k h (r + 2 + i) = p := hp _ (by omega) (by omega)
    have hprev : prevExp k h (r + 2 + i) = p := by
      rw [show r + 2 + i = r + 1 + i + 1 by ring, prevExp_succ]
      exact hp _ (by omega) (by omega)
    funext y
    rw [show r + 2 + (i + 1) = r + 2 + i + 1 by ring, genTower_succ, hcur, hprev, sub_self,
      zero_sub, ih hp', iterDivPrim_succ, powStep]
    refine setIntegral_congr_fun measurableSet_Ioc fun x hx => ?_
    rw [Real.rpow_neg hx.1.le, Real.rpow_one, inv_mul_eq_div]

/-- **Only minimal exponents count (sorted form)**: with
`q_0 ≥ … ≥ q_r > p = q_{r+1} = … = q_{r+1+m}`,
`Z_{r+2+m}(√n) ~ (∏ k_i^{-1}) D · C/(2^m m!) · n^{-p/2} (log n)^m`. -/
theorem iterChartGen_sorted_isEquivalent (β a b : ℝ) (k h : ℕ → ℕ) (hβ : 0 < β) (hb : 0 < b)
    (hk : ∀ i, 0 < k i) (r m : ℕ) (p : ℝ)
    (hsort : ∀ i, i < r → chartExp k h (i + 1) ≤ chartExp k h i)
    (hp : ∀ l, r + 1 ≤ l → l ≤ r + 1 + m → chartExp k h l = p) (hlt : p < chartExp k h r) :
    (fun n : ℝ => iterChartGen β a b k h (r + 2 + m) (Real.sqrt n)) ~[atTop]
      fun n : ℝ => (∏ i ∈ Finset.range (r + 2 + m), (1 : ℝ) / k i) * genScale b k h (r + 2 + m)
        * (sortedConst β a k h r p / (2 ^ m * (m.factorial : ℝ)))
        * (n ^ (-(p / 2)) * Real.log n ^ m) := by
  obtain ⟨hC, M, C', hLB⟩ := genTower_logBase β a k h hβ hk r p hsort (hp (r + 1) le_rfl (by omega))
    hlt
  have hprev : prevExp k h (r + 2 + m) = p := by
    rw [show r + 2 + m = r + 1 + m + 1 by ring, prevExp_succ]
    exact hp _ (by omega) le_rfl
  set K : ℝ := ∏ i ∈ Finset.range (r + 2 + m), (1 : ℝ) / k i with hK
  set D : ℝ := genScale b k h (r + 2 + m) with hD
  set S : ℕ := ∑ i ∈ Finset.range (r + 2 + m), k i with hS
  set C : ℝ := sortedConst β a k h r p with hCdef
  have hZ : ∀ n : ℝ, 0 < n → iterChartGen β a b k h (r + 2 + m) (Real.sqrt n)
      = K * (Real.sqrt n) ^ (-p) * D
        * iterDivPrim (genTower β a k h (r + 2)) m (Real.sqrt n * b ^ S) := by
    intro n hn
    rw [iterChartGen_eq_genTower β a b k h hb hk (r + 2 + m) (Real.sqrt n) (Real.sqrt_pos.2 hn),
      hprev, genTower_block_eq_iterDivPrim β a k h r m p hp]
    ring
  have hLtend : Tendsto (fun n : ℝ => Real.sqrt n * b ^ S) atTop atTop :=
    tendsto_sqrt_atTop.atTop_mul_const (pow_pos hb _)
  have h2 := (iterDivPrim_isEquivalent_all hLB hC m).comp_tendsto hLtend
  have h3 := (log_sqrt_mul_pow_isEquivalent b hb S).pow m
  have h4 : (fun n : ℝ => iterDivPrim (genTower β a k h (r + 2)) m (Real.sqrt n * b ^ S))
      ~[atTop] fun n : ℝ => C / (m.factorial : ℝ) * ((1 / 2 : ℝ) * Real.log n) ^ m := by
    refine h2.trans ?_
    have := (IsEquivalent.refl (u := fun _ : ℝ => C / (m.factorial : ℝ)) (l := atTop)).mul h3
    exact this
  have h5 := (IsEquivalent.refl (u := fun n : ℝ => K * (Real.sqrt n) ^ (-p) * D)
    (l := atTop)).mul h4
  refine (h5.congr_left ?_).congr_right ?_
  · filter_upwards [eventually_gt_atTop (0 : ℝ)] with n hn
    simp only [Pi.mul_apply]
    rw [hZ n hn]
  · filter_upwards [eventually_gt_atTop (0 : ℝ)] with n hn
    simp only [Pi.mul_apply]
    have hpow : (Real.sqrt n) ^ (-p) = n ^ (-(p / 2)) := by
      rw [Real.sqrt_eq_rpow, ← Real.rpow_mul hn.le]
      congr 1
      ring
    rw [hpow, mul_pow, div_pow, one_pow]
    field_simp

/-- **Complete expansion, sorted form**, with remainder `O(n^{-p/2 - (q_r - p)/4})`. -/
theorem iterChartGen_sorted_expansion_isBigO (β a b : ℝ) (k h : ℕ → ℕ) (hβ : 0 < β) (hb : 0 < b)
    (hk : ∀ i, 0 < k i) (r m : ℕ) (p : ℝ)
    (hsort : ∀ i, i < r → chartExp k h (i + 1) ≤ chartExp k h i)
    (hp : ∀ l, r + 1 ≤ l → l ≤ r + 1 + m → chartExp k h l = p) (hlt : p < chartExp k h r) :
    (fun n : ℝ => iterChartGen β a b k h (r + 2 + m) (Real.sqrt n)
        - n ^ (-(p / 2)) * ((∏ i ∈ Finset.range (r + 2 + m), (1 : ℝ) / k i)
          * genScale b k h (r + 2 + m)
          * towerCoeff (genTower β a k h (r + 2)) (sortedConst β a k h r p) m b
              (∑ i ∈ Finset.range (r + 2 + m), k i) n))
      =O[atTop] fun n : ℝ => n ^ (-(p / 2) - (chartExp k h r - p) / 2 / 2) := by
  obtain ⟨hC, M, C', hLB⟩ := genTower_logBase β a k h hβ hk r p hsort (hp (r + 1) le_rfl (by omega))
    hlt
  have hprev : prevExp k h (r + 2 + m) = p := by
    rw [show r + 2 + m = r + 1 + m + 1 by ring, prevExp_succ]
    exact hp _ (by omega) le_rfl
  refine tower_expansion_isBigO hLB m (∏ i ∈ Finset.range (r + 2 + m), (1 : ℝ) / k i)
    (genScale b k h (r + 2 + m)) p b (∑ i ∈ Finset.range (r + 2 + m), k i) hb _ fun n hn => ?_
  rw [iterChartGen_eq_genTower β a b k h hb hk (r + 2 + m) (Real.sqrt n) (Real.sqrt_pos.2 hn),
    hprev, genTower_block_eq_iterDivPrim β a k h r m p hp]
  ring

end Laplace.Grammar
