/-
Copyright (c) 2026 Timaeus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Laplace.Grammar.MonomialPhaseExpansion

/-!
# Exponentially small tails and the asymptotic form of the monomial moments (Stage 2c)

Unit 229 (Taylor-tree programme). The truncated moments `∫₀^N t^{ν-1}(-log t)^i g(t) dt` of unit 227
differ from the **full fluctuation moments**
`fluctMoment β a p ν i = ∫₀^∞ t^{ν-1}(-log t)^i g(t) dt`
by a tail that is exponentially small: the phase kernel satisfies
`g(t) ≤ (√t)^p e^{βa²/2} e^{-βt/2}` (`phaseKernel_le`, from `2√t a ≤ t + a²`), and for `t ≥ 1` the
power–log factor is at most `t^{⌈ν⌉+i+p}`, so the integrand is bounded by `C e^{-βt/4}`
(`tail_integrand_le`, using `t^m e^{-βt/4} ≤ m!(4/β)^m`), giving
`|∫_N^∞ …| ≤ C (4/β) e^{-βN/4}` (`tail_le`). Consequently the exact identity of Headline XXIII
becomes the **asymptotic form** (Headline XXIII′, `monomialPhase_isBigO`):
```
T(N) - ∏ 1/(2kᵢ) ∑_{(μ,j,c)} c N^{-μ} ∑_{i≤j} C(j,i) (log N)^{j-i} fluctMoment β a p μ i
  = O(e^{-βN/8})   as N → ∞,
```
the tail-replacement contribution of one fixed monomial and one fixed phase order to the paper's
`Δ(β,n;ξ,η) = O(e^{-εn})` (`b = 1`, `ε = β/8`, `β > 0`), with the main sum a finite combination of the
scales `N^{-μ} (log N)^k`, `μ ∈ {(hᵢ+1)/(2kᵢ)}`, `k < multiplicity`.

**Scope and conventions.** All parameters `n, h, k, β, a, p` are fixed; the implicit constant
depends on them (it contains `(⌈ν⌉+i+p)! (4/β)^{⌈ν⌉+i+p}`), so nothing here licenses summing infinitely many
phase orders or monomials — that uniformity is Stage 3's obligation. Interpretation of the moments:
with `S_μ(a) = ∫₀^∞ t^{μ-1} e^{-βt+β√t a} dt`, mathematically
`β^p · fluctMoment β a p μ i = (-∂_μ)^i ∂_a^p S_μ(a) = (-∂_ν)^i S_ν(a) |_{ν = μ+p/2}`;
this
identification (differentiation under the integral) is not formalised here. Index shift against the
paper: Lean's density degree `j` is the paper's `j - 1`, and Lean's moment index `i` is the paper's
`j - 1 - k`. No `sorry` and no additional `axiom` declarations.
-/

open MeasureTheory Set Real Filter Topology Asymptotics

namespace Laplace.Grammar

/-- The full log-weighted fluctuation moment `∫₀^∞ t^{ν-1} (-log t)^i g(t) dt`. -/
noncomputable def fluctMoment (β a : ℝ) (p : ℕ) (ν : ℝ) (i : ℕ) : ℝ :=
  ∫ t in Ioi (0 : ℝ), t ^ (ν - 1) * (-Real.log t) ^ i * phaseKernel β a p t

/-- `g(t) ≤ (√t)^p e^{βa²/2} e^{-βt/2}` for `t ≥ 0`, `β > 0`. -/
theorem phaseKernel_le (β a : ℝ) (hβ : 0 < β) (p : ℕ) {t : ℝ} (ht : 0 ≤ t) :
    phaseKernel β a p t ≤
      Real.sqrt t ^ p * (Real.exp (β * a ^ 2 / 2) * Real.exp (-(β * t / 2))) := by
  unfold phaseKernel
  rw [← Real.exp_add]
  refine mul_le_mul_of_nonneg_left (Real.exp_le_exp.2 ?_) (pow_nonneg (Real.sqrt_nonneg _) _)
  have h2 : 2 * Real.sqrt t * a ≤ Real.sqrt t ^ 2 + a ^ 2 := two_mul_le_add_sq _ _
  rw [Real.sq_sqrt ht] at h2
  nlinarith

/-- For `t ≥ 1` the integrand is at most `C e^{-βt/4}` with an explicit `C`. -/
theorem tail_integrand_le (β a : ℝ) (hβ : 0 < β) (p : ℕ) (ν : ℝ) (i : ℕ) {t : ℝ} (ht : 1 ≤ t) :
    |t ^ (ν - 1) * (-Real.log t) ^ i * phaseKernel β a p t| ≤
      Real.exp (β * a ^ 2 / 2) * ((⌈ν⌉₊ + i + p).factorial : ℝ) * (4 / β) ^ (⌈ν⌉₊ + i + p) *
        Real.exp (-(β * t / 4)) := by
  have ht0 : 0 < t := by linarith
  set m : ℕ := ⌈ν⌉₊ + i + p with hm
  -- `|t^{ν-1} (-log t)^i (√t)^p| ≤ t^m`
  have hlog : |(-Real.log t) ^ i| ≤ t ^ i := by
    rw [abs_pow, abs_neg, abs_of_nonneg (Real.log_nonneg ht)]
    exact pow_le_pow_left₀ (Real.log_nonneg ht) (by linarith [Real.log_le_sub_one_of_pos ht0]) i
  have hsqrt : Real.sqrt t ^ p ≤ t ^ p :=
    pow_le_pow_left₀ (Real.sqrt_nonneg _) ((Real.sqrt_le_left ht0.le).2 (by nlinarith)) p
  have hrpow : t ^ (ν - 1) ≤ t ^ (⌈ν⌉₊ : ℕ) := by
    rw [← Real.rpow_natCast]
    exact Real.rpow_le_rpow_of_exponent_le ht (by linarith [Nat.le_ceil ν])
  have hpowm : t ^ (⌈ν⌉₊ : ℕ) * t ^ i * t ^ p = t ^ m := by
    rw [hm, pow_add, pow_add]
  -- `t^m e^{-βt/4} ≤ m! (4/β)^m`
  have hexp : t ^ m ≤ (m.factorial : ℝ) * (4 / β) ^ m * Real.exp (β * t / 4) := by
    have h := Real.pow_div_factorial_le_exp (β * t / 4) (by positivity) m
    rw [div_le_iff₀ (by positivity)] at h
    have hβ4 : (0 : ℝ) < 4 / β := by positivity
    calc t ^ m = (β * t / 4) ^ m * (4 / β) ^ m := by
          rw [← mul_pow]
          congr 1
          field_simp
      _ ≤ Real.exp (β * t / 4) * (m.factorial : ℝ) * (4 / β) ^ m :=
          mul_le_mul_of_nonneg_right h (by positivity)
      _ = (m.factorial : ℝ) * (4 / β) ^ m * Real.exp (β * t / 4) := by ring
  have hker := phaseKernel_le β a hβ p ht0.le
  have hker0 := phaseKernel_nonneg β a p t
  calc |t ^ (ν - 1) * (-Real.log t) ^ i * phaseKernel β a p t|
      = t ^ (ν - 1) * |(-Real.log t) ^ i| * phaseKernel β a p t := by
        rw [abs_mul, abs_mul, abs_of_nonneg (Real.rpow_nonneg ht0.le _), abs_of_nonneg hker0]
    _ ≤ t ^ (⌈ν⌉₊ : ℕ) * t ^ i *
          (t ^ p * (Real.exp (β * a ^ 2 / 2) * Real.exp (-(β * t / 2)))) := by
        gcongr
        exact hker.trans (mul_le_mul_of_nonneg_right hsqrt (by positivity))
    _ = Real.exp (β * a ^ 2 / 2) * (t ^ m * Real.exp (-(β * t / 2))) := by
        rw [← hpowm]; ring
    _ ≤ Real.exp (β * a ^ 2 / 2) * (((m.factorial : ℝ) * (4 / β) ^ m * Real.exp (β * t / 4)) *
          Real.exp (-(β * t / 2))) := by gcongr
    _ = Real.exp (β * a ^ 2 / 2) * (m.factorial : ℝ) * (4 / β) ^ m * Real.exp (-(β * t / 4)) := by
        rw [mul_assoc ((m.factorial : ℝ) * (4 / β) ^ m), ← Real.exp_add,
          show β * t / 4 + -(β * t / 2) = -(β * t / 4) by ring]
        ring

/-- The tail constant `C = e^{βa²/2} m! (4/β)^m`, `m = ⌈ν⌉ + i + p`. -/
noncomputable def tailConst (β a : ℝ) (p : ℕ) (ν : ℝ) (i : ℕ) : ℝ :=
  Real.exp (β * a ^ 2 / 2) * ((⌈ν⌉₊ + i + p).factorial : ℝ) * (4 / β) ^ (⌈ν⌉₊ + i + p)

theorem tailConst_nonneg (β a : ℝ) (hβ : 0 < β) (p : ℕ) (ν : ℝ) (i : ℕ) :
    0 ≤ tailConst β a p ν i := by
  unfold tailConst
  positivity

theorem continuousOn_tail_integrand (β a : ℝ) (p : ℕ) (ν : ℝ) (i : ℕ) :
    ContinuousOn (fun t => t ^ (ν - 1) * (-Real.log t) ^ i * phaseKernel β a p t) (Ioi 0) :=
  ((continuousOn_id.rpow_const fun _ ht => Or.inl (ne_of_gt ht)).mul
    ((Real.continuousOn_log.mono fun _ ht => ne_of_gt ht).neg.pow i)).mul
    (continuous_phaseKernel β a p).continuousOn

/-- Integrability on `(1,∞)` by domination. -/
theorem integrableOn_tail_Ioi_one (β a : ℝ) (hβ : 0 < β) (p : ℕ) (ν : ℝ) (i : ℕ) :
    IntegrableOn (fun t => t ^ (ν - 1) * (-Real.log t) ^ i * phaseKernel β a p t) (Ioi 1) := by
  refine Integrable.mono' ((exp_neg_integrableOn_Ioi 1 (by positivity : 0 < β / 4)).const_mul
    (tailConst β a p ν i)) (((continuousOn_tail_integrand β a p ν i).mono
      (Ioi_subset_Ioi zero_le_one)).aestronglyMeasurable measurableSet_Ioi)
    (ae_restrict_of_forall_mem measurableSet_Ioi fun t ht => ?_)
  rw [Real.norm_eq_abs, show -(β / 4) * t = -(β * t / 4) by ring]
  exact tail_integrand_le β a hβ p ν i (le_of_lt ht)

theorem integrableOn_tail_Ioi (β a : ℝ) (hβ : 0 < β) (p : ℕ) (ν : ℝ) (i : ℕ) {N : ℝ}
    (hN : 1 ≤ N) :
    IntegrableOn (fun t => t ^ (ν - 1) * (-Real.log t) ^ i * phaseKernel β a p t) (Ioi N) :=
  (integrableOn_tail_Ioi_one β a hβ p ν i).mono_set (Ioi_subset_Ioi hN)

/-- Integrability on `(0,∞)`. -/
theorem integrableOn_fluct (β a : ℝ) (hβ : 0 < β) (p : ℕ) {ν : ℝ} (hν : 0 < ν) (i : ℕ) :
    IntegrableOn (fun t => t ^ (ν - 1) * (-Real.log t) ^ i * phaseKernel β a p t) (Ioi 0) := by
  rw [← Ioc_union_Ioi_eq_Ioi zero_le_one]
  exact (integrableOn_truncMoment β a p hν i 1).union (integrableOn_tail_Ioi_one β a hβ p ν i)

/-- `truncMoment N = fluctMoment - ∫_N^∞` for `N ≥ 1`. -/
theorem truncMoment_eq_fluct_sub (β a : ℝ) (hβ : 0 < β) (p : ℕ) {ν : ℝ} (hν : 0 < ν) (i : ℕ)
    {N : ℝ} (hN : 1 ≤ N) :
    truncMoment β a p ν i N = fluctMoment β a p ν i -
      ∫ t in Ioi N, t ^ (ν - 1) * (-Real.log t) ^ i * phaseKernel β a p t := by
  have hint := integrableOn_fluct β a hβ p hν i
  have hsplit := setIntegral_union (Ioc_disjoint_Ioi le_rfl) measurableSet_Ioi
    (hint.mono_set (Ioc_subset_Ioi_self))
    (hint.mono_set (Ioi_subset_Ioi (by linarith : (0 : ℝ) ≤ N)))
    (f := fun t => t ^ (ν - 1) * (-Real.log t) ^ i * phaseKernel β a p t)
  rw [Ioc_union_Ioi_eq_Ioi (by linarith)] at hsplit
  unfold truncMoment fluctMoment
  rw [hsplit]
  ring

/-- `∫_N^∞ e^{-βt/4} dt = (4/β) e^{-βN/4}`. -/
theorem integral_exp_tail (β : ℝ) (hβ : 0 < β) (N : ℝ) :
    ∫ t in Ioi N, Real.exp (-(β * t / 4)) = 4 / β * Real.exp (-(β * N / 4)) := by
  have h := integral_comp_mul_left_Ioi (fun x => Real.exp (-x)) N (by positivity : 0 < β / 4)
  simp only [smul_eq_mul] at h
  rw [integral_exp_neg_Ioi] at h
  have : (fun t : ℝ => Real.exp (-(β * t / 4))) = fun t => Real.exp (-(β / 4 * t)) := by
    funext t; ring_nf
  rw [this, h]
  field_simp

/-- **Exponentially small tail**: `|∫_N^∞ t^{ν-1}(-log t)^i g| ≤ C (4/β) e^{-βN/4}` for `N ≥ 1`. -/
theorem tail_le (β a : ℝ) (hβ : 0 < β) (p : ℕ) (ν : ℝ) (i : ℕ) {N : ℝ} (hN : 1 ≤ N) :
    |∫ t in Ioi N, t ^ (ν - 1) * (-Real.log t) ^ i * phaseKernel β a p t| ≤
      tailConst β a p ν i * (4 / β) * Real.exp (-(β * N / 4)) := by
  have hg : IntegrableOn (fun t => tailConst β a p ν i * Real.exp (-(β * t / 4))) (Ioi N) := by
    have this : IntegrableOn (fun t => tailConst β a p ν i * Real.exp (-(β / 4) * t)) (Ioi N) :=
      (exp_neg_integrableOn_Ioi N (by positivity : 0 < β / 4)).const_mul (tailConst β a p ν i)
    refine this.congr_fun (fun t _ => ?_) measurableSet_Ioi
    beta_reduce
    ring_nf
  have h := norm_integral_le_of_norm_le hg (ae_restrict_of_forall_mem measurableSet_Ioi
    fun t ht => by
      rw [Real.norm_eq_abs]
      exact tail_integrand_le β a hβ p ν i (hN.trans (le_of_lt ht)))
  rw [Real.norm_eq_abs] at h
  refine h.trans (le_of_eq ?_)
  rw [integral_const_mul, integral_exp_tail β hβ N]
  ring

/-! ### The asymptotic form -/

/-- `(log N)^k N^{-μ} e^{-βN/4} ≤ k! (8/β)^k e^{-βN/8}` for `N ≥ 1`, `μ ≥ 0`. -/
theorem log_pow_mul_exp_le (β : ℝ) (hβ : 0 < β) {μ : ℝ} (hμ : 0 ≤ μ) (k : ℕ) {N : ℝ} (hN : 1 ≤ N) :
    N ^ (-μ) * (Real.log N) ^ k * Real.exp (-(β * N / 4)) ≤
      (k.factorial : ℝ) * (8 / β) ^ k * Real.exp (-(β * N / 8)) := by
  have hN0 : 0 < N := by linarith
  have h1 : N ^ (-μ) ≤ 1 := by
    rw [Real.rpow_neg hN0.le]
    exact inv_le_one_of_one_le₀ (Real.one_le_rpow hN hμ)
  have h2 : (Real.log N) ^ k ≤ N ^ k :=
    pow_le_pow_left₀ (Real.log_nonneg hN) (by linarith [Real.log_le_sub_one_of_pos hN0]) k
  have h3 : N ^ k ≤ (k.factorial : ℝ) * (8 / β) ^ k * Real.exp (β * N / 8) := by
    have h := Real.pow_div_factorial_le_exp (β * N / 8) (by positivity) k
    rw [div_le_iff₀ (by positivity)] at h
    calc N ^ k = (β * N / 8) ^ k * (8 / β) ^ k := by
          rw [← mul_pow]; congr 1; field_simp
      _ ≤ Real.exp (β * N / 8) * (k.factorial : ℝ) * (8 / β) ^ k :=
          mul_le_mul_of_nonneg_right h (by positivity)
      _ = _ := by ring
  have hlogk : 0 ≤ (Real.log N) ^ k := pow_nonneg (Real.log_nonneg hN) k
  calc N ^ (-μ) * (Real.log N) ^ k * Real.exp (-(β * N / 4))
      ≤ 1 * ((k.factorial : ℝ) * (8 / β) ^ k * Real.exp (β * N / 8)) * Real.exp (-(β * N / 4)) :=
        mul_le_mul_of_nonneg_right (mul_le_mul h1 (h2.trans h3) hlogk zero_le_one)
          (Real.exp_pos _).le
    _ = (k.factorial : ℝ) * (8 / β) ^ k * Real.exp (-(β * N / 8)) := by
        rw [one_mul, mul_assoc, ← Real.exp_add,
          show β * N / 8 + -(β * N / 4) = -(β * N / 8) by ring]

/-- One scaled tail term is `O(e^{-βN/8})`. -/
theorem term_tail_isBigO (β a : ℝ) (hβ : 0 < β) (p : ℕ) {μ : ℝ} (hμ : 0 < μ) (j i : ℕ) :
    (fun N : ℝ => N ^ (-μ) * (Real.log N) ^ (j - i) *
        (truncMoment β a p μ i N - fluctMoment β a p μ i)) =O[atTop]
      fun N => Real.exp (-(β * N / 8)) := by
  refine IsBigO.of_bound
    (tailConst β a p μ i * (4 / β) * (((j - i).factorial : ℝ) * (8 / β) ^ (j - i))) ?_
  filter_upwards [eventually_ge_atTop (1 : ℝ)] with N hN
  rw [truncMoment_eq_fluct_sub β a hβ p hμ i hN, sub_sub_cancel_left, Real.norm_eq_abs,
    Real.norm_eq_abs, abs_of_pos (Real.exp_pos _), abs_mul, abs_neg,
    abs_of_nonneg
      (mul_nonneg (Real.rpow_nonneg (by linarith) _) (pow_nonneg (Real.log_nonneg hN) _))]
  have hnn : 0 ≤ N ^ (-μ) * (Real.log N) ^ (j - i) :=
    mul_nonneg (Real.rpow_nonneg (by linarith) _) (pow_nonneg (Real.log_nonneg hN) _)
  calc N ^ (-μ) * (Real.log N) ^ (j - i) *
        |∫ t in Ioi N, t ^ (μ - 1) * (-Real.log t) ^ i * phaseKernel β a p t|
      ≤ N ^ (-μ) * (Real.log N) ^ (j - i) *
          (tailConst β a p μ i * (4 / β) * Real.exp (-(β * N / 4))) :=
        mul_le_mul_of_nonneg_left (tail_le β a hβ p μ i hN) hnn
    _ = tailConst β a p μ i * (4 / β) *
          (N ^ (-μ) * (Real.log N) ^ (j - i) * Real.exp (-(β * N / 4))) := by ring
    _ ≤ tailConst β a p μ i * (4 / β) * (((j - i).factorial : ℝ) * (8 / β) ^ (j - i) *
          Real.exp (-(β * N / 8))) :=
        mul_le_mul_of_nonneg_left (log_pow_mul_exp_le β hβ hμ.le (j - i) hN)
          (mul_nonneg (tailConst_nonneg β a hβ p μ i) (by positivity))
    _ = _ := by ring

/-- The main sum with full fluctuation moments. -/
noncomputable def monomialMainSum (n : ℕ) (h k : Fin (n + 1) → ℕ) (β a : ℝ) (p : ℕ) (N : ℝ) : ℝ :=
  (∏ i, 1 / (2 * (k i : ℝ))) *
    ((stateDensityRep n fun i => ((h i : ℝ) + 1) / (2 * (k i : ℝ)) - 1).map fun t =>
      t.2.2 * (N ^ (-t.1) * ∑ i ∈ Finset.range (t.2.1 + 1),
        (t.2.1.choose i : ℝ) * (Real.log N) ^ (t.2.1 - i) * fluctMoment β a p t.1 i)).sum

theorem list_sum_isBigO {c : PowLogRep} (F : ℝ × ℕ × ℝ → ℝ → ℝ) (g : ℝ → ℝ)
    (hc : ∀ t ∈ c, (F t) =O[atTop] g) :
    (fun N => (c.map fun t => F t N).sum) =O[atTop] g := by
  induction c with
  | nil => simp only [List.map_nil, List.sum_nil]; exact isBigO_zero _ _
  | cons t c ih =>
    have h1 := hc t (List.mem_cons_self ..)
    have h2 := ih fun u hu => hc u (List.mem_cons_of_mem t hu)
    simpa only [List.map_cons, List.sum_cons] using h1.add h2

theorem list_sum_map_sub (c : PowLogRep) (f g : ℝ × ℕ × ℝ → ℝ) :
    (c.map f).sum - (c.map g).sum = (c.map fun t => f t - g t).sum := by
  induction c with
  | nil => simp
  | cons t c ih => simp only [List.map_cons, List.sum_cons]; rw [← ih]; ring

/-- **Headline XXIII′ — asymptotic form of the monomial moment**:
`T(N) - monomialMainSum(N) = O(e^{-βN/8})`. -/
theorem monomialPhase_isBigO (n : ℕ) (h k : Fin (n + 1) → ℕ) (hk : ∀ i, 0 < k i) (β a : ℝ)
    (hβ : 0 < β) (p : ℕ) :
    (fun N : ℝ => (∫ u in unitBox (n + 1), (∏ i, u i ^ h i) * ((Real.sqrt N * ∏ i, u i ^ k i) ^ p *
        Real.exp (-(β * N * ∏ i, u i ^ (2 * k i)) + β * (Real.sqrt N * ∏ i, u i ^ k i) * a))) -
      monomialMainSum n h k β a p N) =O[atTop] fun N => Real.exp (-(β * N / 8)) := by
  set rep := stateDensityRep n fun i => ((h i : ℝ) + 1) / (2 * (k i : ℝ)) - 1 with hrep
  have hpos : ∀ t ∈ rep, 0 < t.1 := fun t ht => by
    obtain ⟨i, hi⟩ := stateDensityRep_exponent_mem n _ t ht
    rw [hi]
    have hk' : (0 : ℝ) < k i := by exact_mod_cast hk i
    simp only [sub_add_cancel]
    positivity
  -- the tail term of one entry
  set F : ℝ × ℕ × ℝ → ℝ → ℝ := fun t N => t.2.2 * ∑ i ∈ Finset.range (t.2.1 + 1),
    (t.2.1.choose i : ℝ) * (N ^ (-t.1) * (Real.log N) ^ (t.2.1 - i) *
      (truncMoment β a p t.1 i N - fluctMoment β a p t.1 i)) with hF
  have hdiff : (fun N : ℝ => (∏ i, 1 / (2 * (k i : ℝ))) * (rep.map fun t => F t N).sum) =ᶠ[atTop]
      fun N => (∫ u in unitBox (n + 1), (∏ i, u i ^ h i) * ((Real.sqrt N * ∏ i, u i ^ k i) ^ p *
        Real.exp (-(β * N * ∏ i, u i ^ (2 * k i)) + β * (Real.sqrt N * ∏ i, u i ^ k i) * a))) -
        monomialMainSum n h k β a p N := by
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with N hN
    rw [monomialPhase_eq n h k hk β a p hN, monomialMainSum, ← hrep, ← mul_sub, list_sum_map_sub]
    congr 1
    refine congrArg List.sum (List.map_congr_left fun t _ => ?_)
    simp only [hF, mul_sub, Finset.mul_sum, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    ring
  refine IsBigO.congr' ?_ hdiff EventuallyEq.rfl
  refine IsBigO.const_mul_left (list_sum_isBigO F _ fun t ht => ?_) _
  simp only [hF]
  refine IsBigO.const_mul_left ?_ _
  have hsum := IsBigO.sum (s := Finset.range (t.2.1 + 1)) (l := atTop)
    (g := fun N : ℝ => Real.exp (-(β * N / 8)))
    (A := fun i N => (t.2.1.choose i : ℝ) * (N ^ (-t.1) * (Real.log N) ^ (t.2.1 - i) *
      (truncMoment β a p t.1 i N - fluctMoment β a p t.1 i)))
    fun i _ => (term_tail_isBigO β a hβ p (hpos t ht) t.2.1 i).const_mul_left _
  exact hsum.congr_left fun N => Finset.sum_apply _ _ _

end Laplace.Grammar
