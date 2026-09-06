/-
Copyright (c) 2026 Timaeus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Laplace.Grammar.IterChartGeneral

/-!
# Mixed multiplicity in general dimension: one noncritical coordinate (grammar §4.2)

The innermost coordinate has candidate exponent `q = (h₀+1)/k₀`, the remaining `m+1` coordinates all
have the strictly smaller exponent `p`. Only the minimal exponent counts: the chart integral is

  `Z_{m+2}(c) = (∏ k_i^{-1}) · c^{-p} · b^{k₀(q−p)} · H_m(c b^{∑ k_i})`,

where now `H = iterDivPrim G₁` is built on the **noncritical base**
`G₁(y) = ∫₀^y x^{p−q−1} F_{q−1}(x) dx`, which is a `LogBase` with mass `C(p,q)` (unit 46's
`noLogConst`), tail rate `ε = q − p`, and `δ = p`. Hence

  `Z_{m+2}(√n) ~ (∏ k_i^{-1}) b^{k₀(q−p)} C(p,q)/(2^m m!) · n^{-p/2} (log n)^m`:

multiplicity `m+1`, not `m+2`. Unit 40 is `k = (1,1,1)`, `h = (1,0,0)` up to the order of
integration. Zero `sorry`/`axiom`.
-/

open Real MeasureTheory Set Asymptotics Filter Topology

namespace Laplace.Grammar

/-- **One recursion step at a minimal coordinate**: if `Z_d(c) = K c^{-p} D H_j(cB)` for a
`divide-and-integrate` tower `H` and coordinate `d` has exponent `p`, then
`Z_{d+1}(c) = K k_d^{-1} c^{-p} D H_{j+1}(c B b^{k_d})`. -/
theorem iterChartGen_step (β a b : ℝ) (k h : ℕ → ℕ) (d : ℕ) (G : ℝ → ℝ) (j : ℕ) (K D p B : ℝ)
    (hB : 0 < B) (hb : 0 < b) (hk : 0 < k d) (hpd : ((h d : ℝ) + 1) / k d = p)
    (hZ : ∀ c, 0 < c → iterChartGen β a b k h d c = K * c ^ (-p) * D * iterDivPrim G j (c * B))
    (c : ℝ) (hc : 0 < c) :
    iterChartGen β a b k h (d + 1) c
      = K * (1 / (k d : ℝ)) * c ^ (-p) * D * iterDivPrim G (j + 1) (c * (B * b ^ (k d))) := by
  set H : ℝ → ℝ := iterDivPrim G j with hH
  have hcB : 0 < c * B := by positivity
  set Gs : ℝ → ℝ := fun s => s ^ (-p) * H (c * B * s) with hGs
  have hpt : ∀ u ∈ Ioc (0 : ℝ) b, u ^ (h d) * iterChartGen β a b k h d (c * u ^ (k d))
      = (K * c ^ (-p) * D) * (u ^ (h d) * Gs (u ^ (k d))) := by
    intro u hu
    have hu0 : (0 : ℝ) < u := hu.1
    rw [hZ (c * u ^ (k d)) (by positivity)]
    simp only [hGs, hH]
    rw [Real.mul_rpow hc.le (by positivity), show c * u ^ (k d) * B = c * B * u ^ (k d) by ring]
    ring
  rw [iterChartGen_succ, setIntegral_congr_fun measurableSet_Ioc hpt,
    MeasureTheory.integral_const_mul, integral_Ioc_pow_mul_comp_pow (h d) (k d) b Gs hk hb, hpd]
  simp only [hGs]
  have hpt2 : ∀ s ∈ Ioc (0 : ℝ) (b ^ (k d)), s ^ (p - 1) * (s ^ (-p) * H (c * B * s))
      = s ^ (-1 : ℝ) * H (c * B * s) := by
    intro s hs
    rw [← mul_assoc, ← Real.rpow_add hs.1, show p - 1 + -p = -1 by ring]
  rw [setIntegral_congr_fun measurableSet_Ioc hpt2,
    integral_Ioc_rpow_mul_comp_mul_left (-1) (c * B) _ H hcB (by positivity),
    show -((-1 : ℝ) + 1) = 0 by norm_num, Real.rpow_zero, one_mul]
  have hint : (∫ x in Ioc (0 : ℝ) (c * B * b ^ (k d)), x ^ (-1 : ℝ) * H x)
      = iterDivPrim G (j + 1) (c * (B * b ^ (k d))) := by
    rw [iterDivPrim_succ, ← mul_assoc]
    refine setIntegral_congr_fun measurableSet_Ioc fun x hx => ?_
    rw [Real.rpow_neg hx.1.le, Real.rpow_one, inv_mul_eq_div, hH]
  rw [hint]
  ring

/-- The noncritical base `G₁(y) = ∫₀^y x^{p−q−1} F_{q−1}(x) dx`. -/
noncomputable def noLogBase (β a p q y : ℝ) : ℝ :=
  ∫ x in Ioc (0 : ℝ) y, x ^ (p - q - 1) * weightedPrimitive β a (q - 1) x

theorem noLogBase_nonneg (β a p q y : ℝ) : 0 ≤ noLogBase β a p q y :=
  setIntegral_nonneg measurableSet_Ioc fun x hx =>
    mul_nonneg (Real.rpow_nonneg hx.1.le _) (weightedPrimitive_nonneg β a _ x)

theorem noLogBase_mono (β a p q : ℝ) (hβ : 0 < β) (hp : 0 < p) (hlt : p < q) :
    Monotone (noLogBase β a p q) := by
  intro x y hxy
  refine setIntegral_mono_set
    ((noLog_integrand_integrableOn β a p q hβ hp hlt).mono_set Ioc_subset_Ioi_self) ?_
    (Filter.Eventually.of_forall fun z hz => Ioc_subset_Ioc_right hxy hz)
  rw [Filter.EventuallyLE, ae_restrict_iff' measurableSet_Ioc]
  exact Filter.Eventually.of_forall fun t ht =>
    mul_nonneg (Real.rpow_nonneg ht.1.le _) (weightedPrimitive_nonneg β a _ t)

/-- `C(p,q) − G₁(L) = ∫_L^∞ x^{p−q−1} F_{q−1}`. -/
theorem noLogConst_sub_base (β a p q L : ℝ) (hβ : 0 < β) (hp : 0 < p) (hlt : p < q) (hL : 0 ≤ L) :
    noLogConst β a p q - noLogBase β a p q L
      = ∫ x in Ioi L, x ^ (p - q - 1) * weightedPrimitive β a (q - 1) x := by
  have hint := noLog_integrand_integrableOn β a p q hβ hp hlt
  have hsplit := setIntegral_union (Ioc_disjoint_Ioi (le_refl L)) measurableSet_Ioi
    (hint.mono_set Ioc_subset_Ioi_self) (hint.mono_set (Ioi_subset_Ioi hL))
  rw [Ioc_union_Ioi_eq_Ioi hL] at hsplit
  rw [noLogConst, noLogBase, hsplit]
  ring

theorem noLogBase_le_const (β a p q L : ℝ) (hβ : 0 < β) (hp : 0 < p) (hlt : p < q) :
    noLogBase β a p q L ≤ noLogConst β a p q := by
  rcases le_or_gt 0 L with hL | hL
  · have := noLogConst_sub_base β a p q L hβ hp hlt hL
    have h0 : 0 ≤ ∫ x in Ioi L, x ^ (p - q - 1) * weightedPrimitive β a (q - 1) x :=
      setIntegral_nonneg measurableSet_Ioi fun x hx =>
        mul_nonneg (Real.rpow_nonneg (hL.trans_lt hx).le _) (weightedPrimitive_nonneg β a _ x)
    linarith
  · rw [noLogBase, Ioc_eq_empty (not_lt.2 hL.le), Measure.restrict_empty, integral_zero_measure]
    exact (noLogConst_pos β a p q hβ hp hlt).le

/-- Tail of the noncritical base: `C(p,q) − G₁(L) ≤ A_{q−1}/(q−p) · L^{-(q−p)}`. -/
theorem noLogConst_sub_base_le (β a p q L : ℝ) (hβ : 0 < β) (hp : 0 < p) (hlt : p < q)
    (hL : 0 < L) :
    noLogConst β a p q - noLogBase β a p q L
      ≤ weightedMass β a (q - 1) / (q - p) * L ^ (-(q - p)) := by
  have hγ : -1 < q - 1 := by linarith
  have hint := noLog_integrand_integrableOn β a p q hβ hp hlt
  rw [noLogConst_sub_base β a p q L hβ hp hlt hL.le]
  have hval : (∫ x in Ioi L, weightedMass β a (q - 1) * x ^ (p - q - 1))
      = weightedMass β a (q - 1) / (q - p) * L ^ (-(q - p)) := by
    rw [MeasureTheory.integral_const_mul, integral_Ioi_rpow_of_lt (by linarith) hL,
      show p - q - 1 + 1 = -(q - p) by ring]
    have : q - p ≠ 0 := by linarith
    field_simp
  rw [← hval]
  refine setIntegral_mono_on (hint.mono_set (Ioi_subset_Ioi hL.le))
    ((integrableOn_Ioi_rpow_of_lt (by linarith) hL).const_mul _) measurableSet_Ioi fun x hx => ?_
  have hx0 : (0 : ℝ) < x := hL.trans hx
  calc x ^ (p - q - 1) * weightedPrimitive β a (q - 1) x
      ≤ x ^ (p - q - 1) * weightedMass β a (q - 1) :=
        mul_le_mul_of_nonneg_left (weightedPrimitive_le_mass β a (q - 1) x hβ hγ hx0.le)
          (Real.rpow_nonneg hx0.le _)
    _ = weightedMass β a (q - 1) * x ^ (p - q - 1) := mul_comm _ _

/-- Near `0`: `G₁(y) ≤ E/(pq) · y^p`. -/
theorem noLogBase_le_pow (β a p q y : ℝ) (hβ : 0 < β) (hp : 0 < p) (hlt : p < q) (hy : 0 ≤ y) :
    noLogBase β a p q y ≤ Real.exp (β * a ^ 2 / 2) / (p * q) * y ^ p := by
  have hγ : -1 < q - 1 := by linarith
  have hq : 0 < q := hp.trans hlt
  have hint := noLog_integrand_integrableOn β a p q hβ hp hlt
  calc noLogBase β a p q y
      ≤ ∫ x in Ioc (0 : ℝ) y, Real.exp (β * a ^ 2 / 2) / q * x ^ (p - 1) := by
        refine setIntegral_mono_on (hint.mono_set Ioc_subset_Ioi_self)
          ((intervalIntegral.intervalIntegrable_rpow' (by linarith : (-1 : ℝ) < p - 1)
            (a := 0) (b := y)).1.const_mul _) measurableSet_Ioc fun x hx => ?_
        have hx0 : (0 : ℝ) < x := hx.1
        calc x ^ (p - q - 1) * weightedPrimitive β a (q - 1) x
            ≤ x ^ (p - q - 1) * (Real.exp (β * a ^ 2 / 2) * x ^ (q - 1 + 1) / (q - 1 + 1)) :=
              mul_le_mul_of_nonneg_left (weightedPrimitive_le β a (q - 1) x hβ hγ hx0.le)
                (Real.rpow_nonneg hx0.le _)
          _ = Real.exp (β * a ^ 2 / 2) / q * x ^ (p - 1) := by
              rw [show q - 1 + 1 = q by ring, show p - 1 = (p - q - 1) + q by ring,
                Real.rpow_add hx0]
              ring
    _ = Real.exp (β * a ^ 2 / 2) / (p * q) * y ^ p := by
        rw [MeasureTheory.integral_const_mul, integral_Ioc_rpow_sub_one p y hp hy]
        field_simp

/-- **The noncritical base is admissible**: `LogBase G₁ C(p,q) (A_{q−1}/(q−p)) (E/(pq)) p (q−p)`. -/
theorem noLogBase_logBase (β a p q : ℝ) (hβ : 0 < β) (hp : 0 < p) (hlt : p < q) :
    LogBase (noLogBase β a p q) (noLogConst β a p q) (weightedMass β a (q - 1) / (q - p))
      (Real.exp (β * a ^ 2 / 2) / (p * q)) p (q - p) where
  measurable := (noLogBase_mono β a p q hβ hp hlt).measurable
  nonneg := noLogBase_nonneg β a p q
  le_mass := fun L => noLogBase_le_const β a p q L hβ hp hlt
  le_pow := fun y hy _ => noLogBase_le_pow β a p q y hβ hp hlt hy.le
  δ_pos := hp
  ε_pos := by linarith
  tail := by
    intro L hL
    have hL0 : (0 : ℝ) < L := one_pos.trans_le hL
    rw [abs_sub_comm, abs_of_nonneg (by linarith [noLogBase_le_const β a p q L hβ hp hlt])]
    exact noLogConst_sub_base_le β a p q L hβ hp hlt hL0

/-- **Exact mixed reduction**: innermost exponent `q`, the other `m+1` exponents equal to `p < q`:
`Z_{m+2}(c) = (∏ k_i^{-1}) c^{-p} b^{k₀(q−p)} H^{G₁}_m(c b^{∑ k_i})`. -/
theorem iterChartGen_mixed_eq (β a b : ℝ) (k h : ℕ → ℕ) (p q : ℝ) (hb : 0 < b) (hk : ∀ i, 0 < k i)
    (hq : ((h 0 : ℝ) + 1) / k 0 = q) (m : ℕ)
    (hp : ∀ i, 1 ≤ i → i ≤ m + 1 → ((h i : ℝ) + 1) / k i = p) (c : ℝ) (hc : 0 < c) :
    iterChartGen β a b k h (m + 2) c
      = (∏ i ∈ Finset.range (m + 2), (1 : ℝ) / k i) * c ^ (-p) * b ^ ((k 0 : ℝ) * (q - p))
        * iterDivPrim (noLogBase β a p q) m (c * b ^ (∑ i ∈ Finset.range (m + 2), k i)) := by
  induction m generalizing c with
  | zero =>
    -- Z₁(c) = (1/k₀) c^{-q} F_{q-1}(c b^{k₀}), then one substitution at exponent p
    have hZ1 : ∀ c, 0 < c → iterChartGen β a b k h 1 c
        = 1 / (k 0 : ℝ) * c ^ (-q) * weightedPrimitive β a (q - 1) (c * b ^ (k 0)) := by
      intro c hc
      have := iterChartGen_succ_eq β a b k h q hb hk 0 (fun i hi => by
        rw [Nat.le_zero.1 hi]; exact hq) c hc
      rwa [Finset.prod_range_one, Finset.sum_range_one, iterDivPrim_zero] at this
    rw [iterChartGen_succ, Finset.prod_range_succ, Finset.prod_range_one, Finset.sum_range_succ,
      Finset.sum_range_one, iterDivPrim_zero]
    set G : ℝ → ℝ := fun s => s ^ (-q) * weightedPrimitive β a (q - 1) (c * b ^ (k 0) * s) with hG
    have hpt : ∀ u ∈ Ioc (0 : ℝ) b, u ^ (h 1) * iterChartGen β a b k h 1 (c * u ^ (k 1))
        = (1 / (k 0 : ℝ) * c ^ (-q)) * (u ^ (h 1) * G (u ^ (k 1))) := by
      intro u hu
      have hu0 : (0 : ℝ) < u := hu.1
      rw [hZ1 (c * u ^ (k 1)) (by positivity)]
      simp only [hG]
      rw [Real.mul_rpow hc.le (by positivity),
        show c * u ^ (k 1) * b ^ (k 0) = c * b ^ (k 0) * u ^ (k 1) by ring]
      ring
    rw [setIntegral_congr_fun measurableSet_Ioc hpt, MeasureTheory.integral_const_mul,
      integral_Ioc_pow_mul_comp_pow (h 1) (k 1) b G (hk 1) hb, hp 1 le_rfl le_rfl]
    simp only [hG]
    have hpt2 : ∀ s ∈ Ioc (0 : ℝ) (b ^ (k 1)),
        s ^ (p - 1) * (s ^ (-q) * weightedPrimitive β a (q - 1) (c * b ^ (k 0) * s))
        = s ^ (p - q - 1) * weightedPrimitive β a (q - 1) (c * b ^ (k 0) * s) := by
      intro s hs
      rw [← mul_assoc, ← Real.rpow_add hs.1, show p - 1 + -q = p - q - 1 by ring]
    have hcB : 0 < c * b ^ (k 0) := by positivity
    have hD : ((b ^ (k 0) : ℝ)) ^ (q - p) = b ^ ((k 0 : ℝ) * (q - p)) := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul hb.le]
    rw [setIntegral_congr_fun measurableSet_Ioc hpt2,
      integral_Ioc_rpow_mul_comp_mul_left (p - q - 1) (c * b ^ (k 0)) _
        (weightedPrimitive β a (q - 1)) hcB (by positivity),
      show -(p - q - 1 + 1) = q - p by ring, Real.mul_rpow hc.le (by positivity), hD]
    have hcq : c ^ (-q) * c ^ (q - p) = c ^ (-p) := by
      rw [← Real.rpow_add hc]; congr 1; ring
    have hint : (∫ x in Ioc (0 : ℝ) (c * b ^ (k 0) * b ^ (k 1)),
        x ^ (p - q - 1) * weightedPrimitive β a (q - 1) x)
        = noLogBase β a p q (c * b ^ (k 0 + k 1)) := by
      rw [noLogBase, pow_add, ← mul_assoc]
    rw [hint]
    calc 1 / (k 0 : ℝ) * c ^ (-q) * (1 / (k 1 : ℝ) * (c ^ (q - p) * b ^ ((k 0 : ℝ) * (q - p))
          * noLogBase β a p q (c * b ^ (k 0 + k 1))))
        = 1 / (k 0 : ℝ) * (1 / (k 1 : ℝ)) * (c ^ (-q) * c ^ (q - p)) * b ^ ((k 0 : ℝ) * (q - p))
          * noLogBase β a p q (c * b ^ (k 0 + k 1)) := by ring
      _ = _ := by rw [hcq]
  | succ m ih =>
    have hp' : ∀ i, 1 ≤ i → i ≤ m + 1 → ((h i : ℝ) + 1) / k i = p :=
      fun i hi1 hi2 => hp i hi1 (Nat.le_succ_of_le hi2)
    have hZ : ∀ c, 0 < c → iterChartGen β a b k h (m + 2) c
        = (∏ i ∈ Finset.range (m + 2), (1 : ℝ) / k i) * c ^ (-p) * b ^ ((k 0 : ℝ) * (q - p))
          * iterDivPrim (noLogBase β a p q) m (c * b ^ (∑ i ∈ Finset.range (m + 2), k i)) :=
      fun c hc => ih hp' c hc
    have hstep := iterChartGen_step β a b k h (m + 2) (noLogBase β a p q) m
      (∏ i ∈ Finset.range (m + 2), (1 : ℝ) / k i) (b ^ ((k 0 : ℝ) * (q - p))) p
      (b ^ (∑ i ∈ Finset.range (m + 2), k i)) (by positivity) hb (hk (m + 2))
      (hp (m + 2) (by omega) le_rfl) hZ c hc
    rw [show m + 1 + 2 = m + 2 + 1 by ring, hstep,
      Finset.prod_range_succ (fun i => (1 : ℝ) / k i) (m + 2),
      Finset.sum_range_succ k (m + 2), pow_add]

/-- **Mixed multiplicity theorem**: with one noncritical inner coordinate (`q > p`) and `m+1`
minimal coordinates,
`Z_{m+2}(√n) ~ (∏ k_i^{-1}) b^{k₀(q−p)} C(p,q)/(2^m m!) · n^{-p/2} (log n)^m`. -/
theorem iterChartGen_mixed_isEquivalent (β a b : ℝ) (k h : ℕ → ℕ) (p q : ℝ) (hβ : 0 < β)
    (hb : 0 < b) (hk : ∀ i, 0 < k i) (hq : ((h 0 : ℝ) + 1) / k 0 = q) (m : ℕ) (hm : 0 < m)
    (hp : ∀ i, 1 ≤ i → i ≤ m + 1 → ((h i : ℝ) + 1) / k i = p) (hlt : p < q) :
    (fun n : ℝ => iterChartGen β a b k h (m + 2) (Real.sqrt n)) ~[atTop]
      fun n : ℝ => (∏ i ∈ Finset.range (m + 2), (1 : ℝ) / k i) * b ^ ((k 0 : ℝ) * (q - p))
        * (noLogConst β a p q / (2 ^ m * (m.factorial : ℝ)))
        * (n ^ (-(p / 2)) * Real.log n ^ m) := by
  have hp0 : 0 < p := by
    rw [← hp 1 le_rfl (by omega)]
    have := hk 1
    positivity
  have hG := noLogBase_logBase β a p q hβ hp0 hlt
  have hC := noLogConst_pos β a p q hβ hp0 hlt
  set K : ℝ := ∏ i ∈ Finset.range (m + 2), (1 : ℝ) / k i with hK
  set D : ℝ := b ^ ((k 0 : ℝ) * (q - p)) with hD
  set S : ℕ := ∑ i ∈ Finset.range (m + 2), k i with hS
  have hZ : ∀ n : ℝ, 0 < n → iterChartGen β a b k h (m + 2) (Real.sqrt n)
      = K * (Real.sqrt n) ^ (-p) * D * iterDivPrim (noLogBase β a p q) m (Real.sqrt n * b ^ S) :=
    fun n hn => iterChartGen_mixed_eq β a b k h p q hb hk hq m hp (Real.sqrt n) (Real.sqrt_pos.2 hn)
  have hLtend : Tendsto (fun n : ℝ => Real.sqrt n * b ^ S) atTop atTop :=
    tendsto_sqrt_atTop.atTop_mul_const (pow_pos hb _)
  have h2 := (iterDivPrim_isEquivalent hG hC m hm).comp_tendsto hLtend
  have h3 := (log_sqrt_mul_pow_isEquivalent b hb S).pow m
  have h4 : (fun n : ℝ => iterDivPrim (noLogBase β a p q) m (Real.sqrt n * b ^ S))
      ~[atTop] fun n : ℝ => noLogConst β a p q / (m.factorial : ℝ)
        * ((1 / 2 : ℝ) * Real.log n) ^ m := by
    refine h2.trans ?_
    have := (IsEquivalent.refl (u := fun _ : ℝ => noLogConst β a p q / (m.factorial : ℝ))
      (l := atTop)).mul h3
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

end Laplace.Grammar
