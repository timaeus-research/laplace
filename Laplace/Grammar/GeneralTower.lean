/-
Copyright (c) 2026 Timaeus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Laplace.Grammar.BoxIntegral

/-!
# The general power-step tower: exact reduction for any `(k, h)` (grammar §4.2)

Every reduction so far (units 44, 50, 52) is an instance of one recursion. Write
`q_i = (h_i+1)/k_i` for the candidate exponents (times two) and `q_{-1} = 0`. Define the tower

  `G_0 = f`,  `G_{j+1}(y) = ∫₀^y x^{q_j − q_{j-1} − 1} G_j(x) dx`  (`powStep`),

and the scale factors `D_0 = 1`, `D_{d+1} = D_d (b^{S_d})^{q_{d-1} − q_d}`, `S_d = ∑_{i<d} k_i`.
Then for every `d` and `c > 0`

  `Z_d(c) = (∏_{i<d} k_i^{-1}) · D_d · c^{-q_{d-1}} · G_d(c b^{S_d})`.

The all-equal tower is `iterDivPrim (F_{p-1})` and the mixed base is `G_2`; both identifications are
proved. This isolates the asymptotic problem: the growth of `G_d(y)` as `y → ∞`, which is
`y^{q_{d-1} − q_min} (log y)^{m-1}` with `m` the multiplicity of the minimum. Zero `sorry`/`axiom`.
-/

open Real MeasureTheory Set Asymptotics Filter Topology

namespace Laplace.Grammar

/-- One power step: `powStep s G (y) = ∫₀^y x^s G(x) dx`. -/
noncomputable def powStep (s : ℝ) (G : ℝ → ℝ) (y : ℝ) : ℝ := ∫ x in Ioc (0 : ℝ) y, x ^ s * G x

/-- The candidate exponent (times two) of coordinate `i`. -/
noncomputable def chartExp (k h : ℕ → ℕ) (i : ℕ) : ℝ := ((h i : ℝ) + 1) / k i

/-- The previous exponent, with `q_{-1} = 0`. -/
noncomputable def prevExp (k h : ℕ → ℕ) : ℕ → ℝ
  | 0 => 0
  | j + 1 => chartExp k h j

theorem prevExp_zero (k h : ℕ → ℕ) : prevExp k h 0 = 0 := rfl
theorem prevExp_succ (k h : ℕ → ℕ) (j : ℕ) : prevExp k h (j + 1) = chartExp k h j := rfl

/-- The general tower `G_d`. -/
noncomputable def genTower (β a : ℝ) (k h : ℕ → ℕ) : ℕ → ℝ → ℝ
  | 0 => quadKernel β a
  | j + 1 => powStep (chartExp k h j - prevExp k h j - 1) (genTower β a k h j)

theorem genTower_zero (β a : ℝ) (k h : ℕ → ℕ) : genTower β a k h 0 = quadKernel β a := rfl
theorem genTower_succ (β a : ℝ) (k h : ℕ → ℕ) (j : ℕ) :
    genTower β a k h (j + 1) = powStep (chartExp k h j - prevExp k h j - 1) (genTower β a k h j) :=
  rfl

/-- The scale factors `D_d`. -/
noncomputable def genScale (b : ℝ) (k h : ℕ → ℕ) : ℕ → ℝ
  | 0 => 1
  | d + 1 => genScale b k h d
      * (b ^ (∑ i ∈ Finset.range d, k i)) ^ (prevExp k h d - chartExp k h d)

theorem genScale_zero (b : ℝ) (k h : ℕ → ℕ) : genScale b k h 0 = 1 := rfl
theorem genScale_succ (b : ℝ) (k h : ℕ → ℕ) (d : ℕ) :
    genScale b k h (d + 1) = genScale b k h d
      * (b ^ (∑ i ∈ Finset.range d, k i)) ^ (prevExp k h d - chartExp k h d) := rfl

/-- **General recursion step**: if `Z_d(c) = K c^{-q'} D G(cB)` and coordinate `d` has exponent
`q`, then `Z_{d+1}(c) = K k_d^{-1} (D B^{q'−q}) c^{-q} (powStep (q − q' − 1) G)(c B b^{k_d})`. -/
theorem iterChartGen_step_general (β a b : ℝ) (k h : ℕ → ℕ) (d : ℕ) (G : ℝ → ℝ) (K D q' B : ℝ)
    (hB : 0 < B) (hb : 0 < b) (hk : 0 < k d)
    (hZ : ∀ c, 0 < c → iterChartGen β a b k h d c = K * c ^ (-q') * D * G (c * B))
    (c : ℝ) (hc : 0 < c) :
    iterChartGen β a b k h (d + 1) c
      = K * (1 / (k d : ℝ)) * c ^ (-(chartExp k h d)) * (D * B ^ (q' - chartExp k h d))
        * powStep (chartExp k h d - q' - 1) G (c * (B * b ^ (k d))) := by
  have hcB : 0 < c * B := by positivity
  set q : ℝ := chartExp k h d with hq
  set Gs : ℝ → ℝ := fun s => s ^ (-q') * G (c * B * s) with hGs
  have hpt : ∀ u ∈ Ioc (0 : ℝ) b, u ^ (h d) * iterChartGen β a b k h d (c * u ^ (k d))
      = (K * c ^ (-q') * D) * (u ^ (h d) * Gs (u ^ (k d))) := by
    intro u hu
    have hu0 : (0 : ℝ) < u := hu.1
    rw [hZ (c * u ^ (k d)) (by positivity)]
    simp only [hGs]
    rw [Real.mul_rpow hc.le (by positivity), show c * u ^ (k d) * B = c * B * u ^ (k d) by ring]
    ring
  rw [iterChartGen_succ, setIntegral_congr_fun measurableSet_Ioc hpt,
    MeasureTheory.integral_const_mul, integral_Ioc_pow_mul_comp_pow (h d) (k d) b Gs hk hb]
  have hexp : ((h d : ℝ) + 1) / k d = q := rfl
  rw [hexp]
  simp only [hGs]
  have hpt2 : ∀ s ∈ Ioc (0 : ℝ) (b ^ (k d)), s ^ (q - 1) * (s ^ (-q') * G (c * B * s))
      = s ^ (q - q' - 1) * G (c * B * s) := by
    intro s hs
    rw [← mul_assoc, ← Real.rpow_add hs.1, show q - 1 + -q' = q - q' - 1 by ring]
  rw [setIntegral_congr_fun measurableSet_Ioc hpt2,
    integral_Ioc_rpow_mul_comp_mul_left (q - q' - 1) (c * B) _ G hcB (by positivity),
    show -(q - q' - 1 + 1) = -(q - q') by ring, Real.mul_rpow hc.le hB.le]
  have hcq : c ^ (-q') * c ^ (-(q - q')) = c ^ (-q) := by
    rw [← Real.rpow_add hc]; congr 1; ring
  have hint : (∫ x in Ioc (0 : ℝ) (c * B * b ^ (k d)), x ^ (q - q' - 1) * G x)
      = powStep (q - q' - 1) G (c * (B * b ^ (k d))) := by
    rw [powStep, ← mul_assoc]
  have hB' : B ^ (-(q - q')) = B ^ (q' - q) := by congr 1; ring
  rw [hint, hB']
  calc K * c ^ (-q') * D * (1 / (k d : ℝ) * (c ^ (-(q - q')) * B ^ (q' - q)
        * powStep (q - q' - 1) G (c * (B * b ^ (k d)))))
      = K * (1 / (k d : ℝ)) * (c ^ (-q') * c ^ (-(q - q'))) * (D * B ^ (q' - q))
        * powStep (q - q' - 1) G (c * (B * b ^ (k d))) := by ring
    _ = _ := by rw [hcq]

/-- **Exact reduction for arbitrary `(k, h)`**:
`Z_d(c) = (∏_{i<d} k_i^{-1}) D_d c^{-q_{d-1}} G_d(c b^{S_d})`. -/
theorem iterChartGen_eq_genTower (β a b : ℝ) (k h : ℕ → ℕ) (hb : 0 < b) (hk : ∀ i, 0 < k i)
    (d : ℕ) (c : ℝ) (hc : 0 < c) :
    iterChartGen β a b k h d c
      = (∏ i ∈ Finset.range d, (1 : ℝ) / k i) * genScale b k h d * c ^ (-(prevExp k h d))
        * genTower β a k h d (c * b ^ (∑ i ∈ Finset.range d, k i)) := by
  induction d generalizing c with
  | zero =>
    simp [iterChartGen_zero, genScale_zero, prevExp_zero, genTower_zero]
  | succ d ih =>
    have hZ : ∀ c, 0 < c → iterChartGen β a b k h d c
        = (∏ i ∈ Finset.range d, (1 : ℝ) / k i) * c ^ (-(prevExp k h d)) * genScale b k h d
          * genTower β a k h d (c * b ^ (∑ i ∈ Finset.range d, k i)) := by
      intro c hc
      rw [ih c hc]
      ring
    have hstep := iterChartGen_step_general β a b k h d (genTower β a k h d)
      (∏ i ∈ Finset.range d, (1 : ℝ) / k i) (genScale b k h d) (prevExp k h d)
      (b ^ (∑ i ∈ Finset.range d, k i)) (by positivity) hb (hk d) hZ c hc
    rw [hstep, Finset.prod_range_succ, Finset.sum_range_succ, pow_add, genScale_succ,
      genTower_succ, prevExp_succ]
    ring

/-- With all exponents equal to `p`, the tower is the iterated weighted primitive:
`G_{d+1} = iterDivPrim (F_{p-1}) d`. -/
theorem genTower_eq_iterDivPrim (β a : ℝ) (k h : ℕ → ℕ) (p : ℝ) (d : ℕ)
    (hp : ∀ i, i ≤ d → chartExp k h i = p) :
    genTower β a k h (d + 1) = iterDivPrim (weightedPrimitive β a (p - 1)) d := by
  induction d with
  | zero =>
    funext y
    rw [genTower_succ, genTower_zero, prevExp_zero, hp 0 le_rfl, sub_zero, iterDivPrim_zero,
      powStep, weightedPrimitive]
  | succ d ih =>
    have hp' : ∀ i, i ≤ d → chartExp k h i = p := fun i hi => hp i (Nat.le_succ_of_le hi)
    funext y
    rw [genTower_succ, prevExp_succ, hp (d + 1) le_rfl, hp d (Nat.le_succ d), sub_self, zero_sub,
      ih hp', iterDivPrim_succ, powStep]
    refine setIntegral_congr_fun measurableSet_Ioc fun x hx => ?_
    rw [Real.rpow_neg hx.1.le, Real.rpow_one, inv_mul_eq_div]

/-- With exponents `q` then `p`, the second tower level is the noncritical base of unit 52. -/
theorem genTower_two_eq_noLogBase (β a : ℝ) (k h : ℕ → ℕ) (p q : ℝ) (hq : chartExp k h 0 = q)
    (hp : chartExp k h 1 = p) :
    genTower β a k h 2 = noLogBase β a p q := by
  funext y
  rw [genTower_succ, genTower_succ, genTower_zero, prevExp_succ, prevExp_zero, hq, hp, sub_zero]
  rfl

end Laplace.Grammar
