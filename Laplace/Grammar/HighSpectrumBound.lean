/-
Copyright (c) 2026 Timaeus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Laplace.Grammar.PhaseMajorant
import Laplace.Grammar.PhaseTaylorIdentity
import Laplace.Grammar.DensityBudget
import Laplace.Grammar.SpectralLattice

/-!
# The high-spectrum bound (Stage 3f, Gate C)

Unit 236 (Taylor-tree programme; Astra #27). Split every state-density entry `(μ, j, c)` of the
exact polynomial Taylor tree (Headline XXIV) according to a cutoff `L > 0`: **low** (`μ < L`) or
**high** (`L ≤ μ`). A high entry is estimated on the `τ`-side, *before* any moment is evaluated:
```
|c ∫₀¹ τ^{μ-1}(-log τ)^j g_p(Nτ) dτ| ≤ |c| · N^{-L} (1+log N)^n · M_{L,n,p}(a)
```
(`abs_entryTrunc_le`: lower `τ^{μ-1} ≤ τ^{L-1}` on `(0,1]`, substitute `t = Nτ`, use
`|log N - log t| ≤ (1+log N)(1+|log t|)` and enlarge `(0,N]` to `(0,∞)`; `M` is the positive log
moment of unit 234). Summing over the entries of one monomial density uses the uniform budget of
unit 231 (`∑|c| ≤ (n+1)! Q^n`, `Q = latticeQ k`, with **no dependence on the monomial**), over the
monomials of `P_p = η J^p` the ℓ¹ algebra of unit 233 (`‖P_p‖₁ ≤ ‖η‖₁ ‖J‖₁^p`), and over the phase
orders the Tonelli identity of unit 234, which folds `∑_p (β‖J‖₁)^p/p! M_{L,n,p}(a)` into
`M_{L,n,0}(a + ‖J‖₁)`. The result (`abs_highRemainder_le`, **Gate C**) is
```
|R_high(N)| ≤ K_k ‖η‖₁ (n+1)! Q^n M_{L,n}(a+‖J‖₁) · N^{-L} (1+log N)^n        (N ≥ 1),
```
with a constant independent of `N`, and the decomposition `Z(N) = lowSeries + highRemainder`
(`polyPhaseIntegral_eq_low_add_high`). No `sorry` and no additional `axiom` declarations.
-/

open MeasureTheory Set Real Filter Topology

namespace Laplace.Grammar

open MonoRep

/-! ### Entries of the truncated state-density sum -/

/-- One state-density entry's contribution to `monomialTruncSum`. -/
noncomputable def entryTrunc (β a : ℝ) (p : ℕ) (N : ℝ) (t : ℝ × ℕ × ℝ) : ℝ :=
  t.2.2 * (N ^ (-t.1) * ∑ i ∈ Finset.range (t.2.1 + 1),
    (t.2.1.choose i : ℝ) * (Real.log N) ^ (t.2.1 - i) * truncMoment β a p t.1 i N)

theorem monomialTruncSum_eq (n : ℕ) (h k : Fin (n + 1) → ℕ) (β a : ℝ) (p : ℕ) (N : ℝ) :
    monomialTruncSum n h k β a p N = (∏ i, 1 / (2 * (k i : ℝ))) *
      ((stateDensityRep n fun i => ((h i : ℝ) + 1) / (2 * (k i : ℝ)) - 1).map
        (entryTrunc β a p N)).sum := rfl

/-- An entry is the coefficient times the `τ`-side basis integral. -/
theorem entryTrunc_eq (β a : ℝ) (p : ℕ) {N : ℝ} (hN : 0 < N) {t : ℝ × ℕ × ℝ} (hμ : 0 < t.1) :
    entryTrunc β a p N t =
      t.2.2 * ∫ τ in Ioc (0 : ℝ) 1, powLogBasis t.1 t.2.1 τ * phaseKernel β a p (N * τ) := by
  unfold entryTrunc
  rw [basis_scaling β a p hμ t.2.1 hN]

theorem powLogBasis_nonneg_of_mem (μ : ℝ) (j : ℕ) {τ : ℝ} (hτ : τ ∈ Ioc (0 : ℝ) 1) :
    0 ≤ powLogBasis μ j τ :=
  mul_nonneg (Real.rpow_nonneg hτ.1.le _)
    (pow_nonneg (neg_nonneg.2 (Real.log_nonpos hτ.1.le hτ.2)) _)

theorem basis_integral_nonneg (β a : ℝ) (p : ℕ) (μ : ℝ) (j : ℕ) (N : ℝ) :
    0 ≤ ∫ τ in Ioc (0 : ℝ) 1, powLogBasis μ j τ * phaseKernel β a p (N * τ) :=
  setIntegral_nonneg measurableSet_Ioc fun _ hτ =>
    mul_nonneg (powLogBasis_nonneg_of_mem μ j hτ) (phaseKernel_nonneg β a p _)

/-! ### Scaling and the logarithmic comparison -/

/-- Scaling `τ = t/N` on `(0,1]`. -/
theorem integral_Ioc_one_scale (G : ℝ → ℝ) {N : ℝ} (hN : 0 < N) :
    ∫ τ in Ioc (0 : ℝ) 1, G τ = N⁻¹ * ∫ t in Ioc (0 : ℝ) N, G (t / N) := by
  have h := intervalIntegral.integral_comp_mul_left (fun t => G (t / N)) hN.ne' (a := 0) (b := 1)
  simp only [mul_zero, mul_one, smul_eq_mul] at h
  rw [intervalIntegral.integral_of_le zero_le_one, intervalIntegral.integral_of_le hN.le] at h
  rw [← h]
  refine setIntegral_congr_fun measurableSet_Ioc fun τ _ => ?_
  rw [mul_div_cancel_left₀ τ hN.ne']

/-- `(log N - log t)^j ≤ (1+log N)^n (1+|log t|)^n` for `N ≥ 1`, `t > 0`, `j ≤ n`. -/
theorem log_diff_pow_le {N t : ℝ} (hN : 1 ≤ N) {j n : ℕ} (hj : j ≤ n) :
    (Real.log N - Real.log t) ^ j ≤ (1 + Real.log N) ^ n * (1 + |Real.log t|) ^ n := by
  have hlN : 0 ≤ Real.log N := Real.log_nonneg hN
  have hlt := abs_nonneg (Real.log t)
  have h1 : |Real.log N - Real.log t| ≤ (1 + Real.log N) * (1 + |Real.log t|) := by
    calc |Real.log N - Real.log t| ≤ |Real.log N| + |Real.log t| := abs_sub _ _
      _ = Real.log N + |Real.log t| := by rw [abs_of_nonneg hlN]
      _ ≤ (1 + Real.log N) * (1 + |Real.log t|) := by nlinarith
  have hbase : 1 ≤ (1 + Real.log N) * (1 + |Real.log t|) := by nlinarith
  calc (Real.log N - Real.log t) ^ j ≤ |(Real.log N - Real.log t) ^ j| := le_abs_self _
    _ = |Real.log N - Real.log t| ^ j := abs_pow _ _
    _ ≤ ((1 + Real.log N) * (1 + |Real.log t|)) ^ j := pow_le_pow_left₀ (abs_nonneg _) h1 j
    _ ≤ ((1 + Real.log N) * (1 + |Real.log t|)) ^ n := pow_le_pow_right₀ hbase hj
    _ = _ := mul_pow _ _ _

/-- Pointwise on `(0,N]`: `τ^{L-1}(-log τ)^j g(t)` at `τ = t/N` is at most
`N^{1-L} (1+log N)^n · logMajorant β a L n p t`. -/
theorem basis_div_mul_le (β a : ℝ) (p : ℕ) (L : ℝ) {j n : ℕ} (hj : j ≤ n) {N t : ℝ} (hN : 1 ≤ N)
    (ht : 0 < t) :
    powLogBasis L j (t / N) * phaseKernel β a p t ≤
      N ^ (1 - L) * (1 + Real.log N) ^ n * logMajorant β a L n p t := by
  have hN0 : 0 < N := by linarith
  unfold powLogBasis logMajorant
  rw [Real.div_rpow ht.le hN0.le, Real.log_div ht.ne' hN0.ne', neg_sub,
    show (1 : ℝ) - L = -(L - 1) by ring, Real.rpow_neg hN0.le, div_eq_mul_inv]
  have hg := phaseKernel_nonneg β a p t
  have ht1 : 0 ≤ t ^ (L - 1) := Real.rpow_nonneg ht.le _
  have hNi : 0 ≤ (N ^ (L - 1))⁻¹ := inv_nonneg.2 (Real.rpow_nonneg hN0.le _)
  have hlog := log_diff_pow_le (t := t) hN hj
  calc t ^ (L - 1) * (N ^ (L - 1))⁻¹ * (Real.log N - Real.log t) ^ j * phaseKernel β a p t
      ≤ t ^ (L - 1) * (N ^ (L - 1))⁻¹ * ((1 + Real.log N) ^ n * (1 + |Real.log t|) ^ n) *
          phaseKernel β a p t :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hlog (mul_nonneg ht1 hNi)) hg
    _ = _ := by ring

/-- **Single-basis high-spectrum bound**: for `L ≤ μ`, `j ≤ n`, `N ≥ 1`,
`∫₀¹ τ^{μ-1}(-log τ)^j g_p(Nτ) dτ ≤ N^{-L} (1+log N)^n M_{L,n,p}(a)`. -/
theorem basis_integral_le (β a : ℝ) (hβ : 0 < β) (p : ℕ) {L μ : ℝ} (hL : 0 < L) (hμ : L ≤ μ)
    {j n : ℕ} (hj : j ≤ n) {N : ℝ} (hN : 1 ≤ N) :
    ∫ τ in Ioc (0 : ℝ) 1, powLogBasis μ j τ * phaseKernel β a p (N * τ) ≤
      N ^ (-L) * (1 + Real.log N) ^ n * phaseLogMoment β a L n p := by
  have hN0 : 0 < N := by linarith
  have hμ0 : 0 < μ := hL.trans_le hμ
  have h1 : ∫ τ in Ioc (0 : ℝ) 1, powLogBasis μ j τ * phaseKernel β a p (N * τ) ≤
      ∫ τ in Ioc (0 : ℝ) 1, powLogBasis L j τ * phaseKernel β a p (N * τ) := by
    refine setIntegral_mono_on (integrableOn_powLogBasis_mul_phaseKernel β a p hμ0 j N)
      (integrableOn_powLogBasis_mul_phaseKernel β a p hL j N) measurableSet_Ioc fun τ hτ => ?_
    unfold powLogBasis
    refine mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right ?_ ?_)
      (phaseKernel_nonneg _ _ _ _)
    · exact Real.rpow_le_rpow_of_exponent_ge hτ.1 hτ.2 (by linarith)
    · exact pow_nonneg (neg_nonneg.2 (Real.log_nonpos hτ.1.le hτ.2)) _
  have h2 : ∫ τ in Ioc (0 : ℝ) 1, powLogBasis L j τ * phaseKernel β a p (N * τ) =
      N⁻¹ * ∫ t in Ioc (0 : ℝ) N, powLogBasis L j (t / N) * phaseKernel β a p t := by
    rw [integral_Ioc_one_scale (fun τ => powLogBasis L j τ * phaseKernel β a p (N * τ)) hN0]
    congr 1
    refine setIntegral_congr_fun measurableSet_Ioc fun t _ => ?_
    rw [mul_div_cancel₀ t hN0.ne']
  have hint : IntegrableOn (fun t => N ^ (1 - L) * (1 + Real.log N) ^ n * logMajorant β a L n p t)
      (Ioi 0) :=
    (integrableOn_logMajorant β a L hβ hL n p).const_mul (N ^ (1 - L) * (1 + Real.log N) ^ n)
  have hpos : 0 ≤ N ^ (1 - L) * (1 + Real.log N) ^ n :=
    mul_nonneg (Real.rpow_nonneg hN0.le _) (pow_nonneg (by linarith [Real.log_nonneg hN]) _)
  have h3 : ∫ t in Ioc (0 : ℝ) N, powLogBasis L j (t / N) * phaseKernel β a p t ≤
      N ^ (1 - L) * (1 + Real.log N) ^ n * phaseLogMoment β a L n p := by
    calc ∫ t in Ioc (0 : ℝ) N, powLogBasis L j (t / N) * phaseKernel β a p t
        ≤ ∫ t in Ioc (0 : ℝ) N,
            N ^ (1 - L) * (1 + Real.log N) ^ n * logMajorant β a L n p t := by
          refine integral_mono_of_nonneg (ae_restrict_of_forall_mem measurableSet_Ioc
            fun t ht => ?_) (hint.mono_set Ioc_subset_Ioi_self)
            (ae_restrict_of_forall_mem measurableSet_Ioc fun t ht =>
              basis_div_mul_le β a p L hj hN ht.1)
          have htN : t / N ∈ Ioc (0 : ℝ) 1 := ⟨div_pos ht.1 hN0, (div_le_one hN0).2 ht.2⟩
          exact mul_nonneg (powLogBasis_nonneg_of_mem L j htN) (phaseKernel_nonneg _ _ _ _)
      _ ≤ ∫ t in Ioi (0 : ℝ), N ^ (1 - L) * (1 + Real.log N) ^ n * logMajorant β a L n p t :=
          setIntegral_mono_set hint (ae_restrict_of_forall_mem measurableSet_Ioi fun t ht =>
            mul_nonneg hpos (logMajorant_nonneg β a L n p (mem_Ioi.1 ht).le))
            Ioc_subset_Ioi_self.eventuallyLE
      _ = _ := by unfold phaseLogMoment; rw [integral_const_mul]
  calc _ ≤ _ := h1
    _ = _ := h2
    _ ≤ N⁻¹ * (N ^ (1 - L) * (1 + Real.log N) ^ n * phaseLogMoment β a L n p) :=
        mul_le_mul_of_nonneg_left h3 (inv_nonneg.2 hN0.le)
    _ = _ := by
        rw [show N⁻¹ = N ^ (-(1 : ℝ)) by rw [Real.rpow_neg hN0.le, Real.rpow_one],
          ← mul_assoc, ← mul_assoc, ← Real.rpow_add hN0]
        congr 3
        ring

/-- **High single-entry bound** (`L ≤ μ`, degree `≤ n`, `N ≥ 1`). -/
theorem abs_entryTrunc_le (β a : ℝ) (hβ : 0 < β) (p : ℕ) {L : ℝ} (hL : 0 < L) {n : ℕ} {N : ℝ}
    (hN : 1 ≤ N) {t : ℝ × ℕ × ℝ} (hμ : L ≤ t.1) (hj : t.2.1 ≤ n) :
    |entryTrunc β a p N t| ≤
      |t.2.2| * (N ^ (-L) * (1 + Real.log N) ^ n * phaseLogMoment β a L n p) := by
  have hN0 : 0 < N := by linarith
  rw [entryTrunc_eq β a p hN0 (hL.trans_le hμ), abs_mul,
    abs_of_nonneg (basis_integral_nonneg β a p _ _ _)]
  exact mul_le_mul_of_nonneg_left (basis_integral_le β a hβ p hL hμ hj hN) (abs_nonneg _)

/-! ### Low and high parts of a density list -/

/-- The high-spectrum part (`L ≤ μ`) of a density list's truncated sum. -/
noncomputable def highSum (β a : ℝ) (p : ℕ) (N L : ℝ) (c : PowLogRep) : ℝ :=
  (c.map fun t => if L ≤ t.1 then entryTrunc β a p N t else 0).sum

/-- The low-spectrum part (`μ < L`). -/
noncomputable def lowSum (β a : ℝ) (p : ℕ) (N L : ℝ) (c : PowLogRep) : ℝ :=
  (c.map fun t => if t.1 < L then entryTrunc β a p N t else 0).sum

theorem lowSum_add_highSum (β a : ℝ) (p : ℕ) (N L : ℝ) (c : PowLogRep) :
    lowSum β a p N L c + highSum β a p N L c = (c.map (entryTrunc β a p N)).sum := by
  induction c with
  | nil => simp [lowSum, highSum]
  | cons t c ih =>
    simp only [lowSum, highSum, List.map_cons, List.sum_cons] at ih ⊢
    rw [← ih]
    split_ifs <;> first | (exfalso; linarith) | ring

/-- The high part of a list is bounded by `∑|c|` times the single-entry majorant. -/
theorem abs_highSum_le (β a : ℝ) (hβ : 0 < β) (p : ℕ) {L : ℝ} (hL : 0 < L) {n : ℕ} {N : ℝ}
    (hN : 1 ≤ N) (c : PowLogRep) (hdeg : ∀ t ∈ c, t.2.1 ≤ n) :
    |highSum β a p N L c| ≤ (c.map fun t => |t.2.2|).sum *
      (N ^ (-L) * (1 + Real.log N) ^ n * phaseLogMoment β a L n p) := by
  have hM : 0 ≤ N ^ (-L) * (1 + Real.log N) ^ n * phaseLogMoment β a L n p :=
    mul_nonneg (mul_nonneg (Real.rpow_nonneg (by linarith) _)
      (pow_nonneg (by linarith [Real.log_nonneg hN]) _)) (phaseLogMoment_nonneg β a L n p)
  induction c with
  | nil => simp [highSum]
  | cons t c ih =>
    have ht := hdeg t (List.mem_cons.2 (Or.inl rfl))
    have ih' := ih fun s hs => hdeg s (List.mem_cons.2 (Or.inr hs))
    simp only [highSum, List.map_cons, List.sum_cons] at ih' ⊢
    rw [add_mul]
    refine (abs_add_le _ _).trans (add_le_add ?_ ih')
    split_ifs with h1
    · exact abs_entryTrunc_le β a hβ p hL hN h1 ht
    · rw [abs_zero]
      exact mul_nonneg (abs_nonneg _) hM

/-! ### Uniform bounds for one monomial density -/

theorem stateDensityRep_degree_le (n : ℕ) (w : Fin (n + 1) → ℝ) :
    ∀ t ∈ stateDensityRep n w, t.2.1 ≤ n := fun t ht => by
  have h1 := stateDensityRep_degree_lt n w t ht
  have h2 : expMult w t.1 ≤ n + 1 := by
    unfold expMult
    exact (Finset.card_filter_le _ _).trans (by simp)
  omega

/-- The coefficient ℓ¹ norm of a monomial state density is at most `(n+1)! Q^n`, `Q = latticeQ k`,
uniformly in the monomial exponent `h`. -/
theorem sum_abs_stateDensityRep_le (n : ℕ) (h k : Fin (n + 1) → ℕ) (hk : ∀ i, 0 < k i) :
    ((stateDensityRep n fun i => ((h i : ℝ) + 1) / (2 * (k i : ℝ)) - 1).map
      fun t => |t.2.2|).sum ≤ ((n + 1).factorial : ℝ) * (latticeQ k : ℝ) ^ n := by
  have hQ1 : (1 : ℝ) ≤ latticeQ k := by exact_mod_cast latticeQ_pos k hk
  refine (PowLogRep.sum_abs_le_budget hQ1 _).trans
    (budget_stateDensityRep_le hQ1 ⟨latticeQ k, rfl⟩ n _ fun i => ?_)
  obtain ⟨m, -, hm⟩ := ratio_mem_lattice k hk i (h i)
  exact ⟨m, by rw [sub_add_cancel]; exact hm⟩

/-! ### Low and high parts of a polynomial phase order -/

/-- The high-spectrum part of `∑_{(γ,c) ∈ P} c · monomialTruncSum (h+γ)`. -/
noncomputable def highPart (n : ℕ) (h k : Fin (n + 1) → ℕ) (β a : ℝ) (p : ℕ) (N L : ℝ)
    (P : MonoRep (n + 1)) : ℝ :=
  (∏ i, 1 / (2 * (k i : ℝ))) * (P.map fun s => s.2 * highSum β a p N L
    (stateDensityRep n fun i => ((((h + s.1) i : ℕ) : ℝ) + 1) / (2 * (k i : ℝ)) - 1)).sum

/-- The low-spectrum part. -/
noncomputable def lowPart (n : ℕ) (h k : Fin (n + 1) → ℕ) (β a : ℝ) (p : ℕ) (N L : ℝ)
    (P : MonoRep (n + 1)) : ℝ :=
  (∏ i, 1 / (2 * (k i : ℝ))) * (P.map fun s => s.2 * lowSum β a p N L
    (stateDensityRep n fun i => ((((h + s.1) i : ℕ) : ℝ) + 1) / (2 * (k i : ℝ)) - 1)).sum

theorem lowPart_add_highPart (n : ℕ) (h k : Fin (n + 1) → ℕ) (β a : ℝ) (p : ℕ) (N L : ℝ)
    (P : MonoRep (n + 1)) :
    lowPart n h k β a p N L P + highPart n h k β a p N L P =
      (P.map fun s => s.2 * monomialTruncSum n (h + s.1) k β a p N).sum := by
  unfold lowPart highPart
  rw [← mul_add, ← List.sum_map_add, ← List.sum_map_mul_left]
  refine congrArg List.sum (List.map_congr_left fun s _ => ?_)
  rw [monomialTruncSum_eq, ← mul_add, lowSum_add_highSum]
  ring

theorem abs_sum_highSum_le (n : ℕ) (h k : Fin (n + 1) → ℕ) (hk : ∀ i, 0 < k i) (β a : ℝ)
    (hβ : 0 < β) (p : ℕ) {L : ℝ} (hL : 0 < L) {N : ℝ} (hN : 1 ≤ N) (P : MonoRep (n + 1)) :
    |(P.map fun s => s.2 * highSum β a p N L
      (stateDensityRep n fun i => ((((h + s.1) i : ℕ) : ℝ) + 1) / (2 * (k i : ℝ)) - 1)).sum| ≤
      l1 P * ((((n + 1).factorial : ℝ) * (latticeQ k : ℝ) ^ n) *
        (N ^ (-L) * (1 + Real.log N) ^ n * phaseLogMoment β a L n p)) := by
  have hM : 0 ≤ N ^ (-L) * (1 + Real.log N) ^ n * phaseLogMoment β a L n p :=
    mul_nonneg (mul_nonneg (Real.rpow_nonneg (by linarith) _)
      (pow_nonneg (by linarith [Real.log_nonneg hN]) _)) (phaseLogMoment_nonneg β a L n p)
  induction P with
  | nil => simp [l1]
  | cons s P ih =>
    rw [List.map_cons, List.sum_cons, l1_cons, add_mul]
    refine (abs_add_le _ _).trans (add_le_add ?_ ih)
    rw [abs_mul]
    refine mul_le_mul_of_nonneg_left ?_ (abs_nonneg _)
    refine (abs_highSum_le β a hβ p hL hN _ (stateDensityRep_degree_le n _)).trans ?_
    exact mul_le_mul_of_nonneg_right (sum_abs_stateDensityRep_le n (h + s.1) k hk) hM

/-- **Uniform high-part bound for one phase order** (Gate C, single order). -/
theorem abs_highPart_le (n : ℕ) (h k : Fin (n + 1) → ℕ) (hk : ∀ i, 0 < k i) (β a : ℝ)
    (hβ : 0 < β) (p : ℕ) {L : ℝ} (hL : 0 < L) {N : ℝ} (hN : 1 ≤ N) (P : MonoRep (n + 1)) :
    |highPart n h k β a p N L P| ≤ (∏ i, 1 / (2 * (k i : ℝ))) * l1 P *
      (((n + 1).factorial : ℝ) * (latticeQ k : ℝ) ^ n) *
      (N ^ (-L) * (1 + Real.log N) ^ n * phaseLogMoment β a L n p) := by
  have hK : 0 ≤ ∏ i, 1 / (2 * (k i : ℝ)) := Finset.prod_nonneg fun i _ => by positivity
  unfold highPart
  rw [abs_mul, abs_of_nonneg hK]
  calc _ ≤ (∏ i, 1 / (2 * (k i : ℝ))) * (l1 P * ((((n + 1).factorial : ℝ) * (latticeQ k : ℝ) ^ n) *
        (N ^ (-L) * (1 + Real.log N) ^ n * phaseLogMoment β a L n p))) :=
        mul_le_mul_of_nonneg_left (abs_sum_highSum_le n h k hk β a hβ p hL hN P) hK
    _ = _ := by ring

/-! ### The summed high-spectrum remainder -/

/-- The high-spectrum remainder `R_high(N) = ∑_p β^p/p! · highPart_p`. -/
noncomputable def highRemainder (n : ℕ) (h k : Fin (n + 1) → ℕ) (β N L : ℝ)
    (ξ η : MonoRep (n + 1)) : ℝ :=
  ∑' p : ℕ, β ^ p / (p.factorial : ℝ) *
    highPart n h k β (eval ξ 0) p N L (mul η (pow (fluct ξ) p))

/-- The low-spectrum series `∑_p β^p/p! · lowPart_p`. -/
noncomputable def lowSeries (n : ℕ) (h k : Fin (n + 1) → ℕ) (β N L : ℝ)
    (ξ η : MonoRep (n + 1)) : ℝ :=
  ∑' p : ℕ, β ^ p / (p.factorial : ℝ) *
    lowPart n h k β (eval ξ 0) p N L (mul η (pow (fluct ξ) p))

/-- The `N`-free prefactor of the high-spectrum bound. -/
noncomputable def highConst (n : ℕ) (k : Fin (n + 1) → ℕ) (β L : ℝ) (ξ η : MonoRep (n + 1)) :
    ℝ :=
  (∏ i, 1 / (2 * (k i : ℝ))) * l1 η * (((n + 1).factorial : ℝ) * (latticeQ k : ℝ) ^ n) *
    phaseLogMoment β (eval ξ 0 + l1 (fluct ξ)) L n 0

theorem highTerm_le (n : ℕ) (h k : Fin (n + 1) → ℕ) (hk : ∀ i, 0 < k i) (β : ℝ) (hβ : 0 < β)
    {L : ℝ} (hL : 0 < L) {N : ℝ} (hN : 1 ≤ N) (ξ η : MonoRep (n + 1)) (p : ℕ) :
    ‖β ^ p / (p.factorial : ℝ) *
        highPart n h k β (eval ξ 0) p N L (mul η (pow (fluct ξ) p))‖ ≤
      ((∏ i, 1 / (2 * (k i : ℝ))) * l1 η * (((n + 1).factorial : ℝ) * (latticeQ k : ℝ) ^ n) *
        (N ^ (-L) * (1 + Real.log N) ^ n)) *
        ((β * l1 (fluct ξ)) ^ p / (p.factorial : ℝ) * phaseLogMoment β (eval ξ 0) L n p) := by
  have hM : 0 ≤ N ^ (-L) * (1 + Real.log N) ^ n * phaseLogMoment β (eval ξ 0) L n p :=
    mul_nonneg (mul_nonneg (Real.rpow_nonneg (by linarith) _)
      (pow_nonneg (by linarith [Real.log_nonneg hN]) _)) (phaseLogMoment_nonneg _ _ _ _ _)
  have hK : 0 ≤ ∏ i, 1 / (2 * (k i : ℝ)) := Finset.prod_nonneg fun i _ => by positivity
  have hD : 0 ≤ ((n + 1).factorial : ℝ) * (latticeQ k : ℝ) ^ n := by positivity
  have hb : 0 ≤ β ^ p / (p.factorial : ℝ) := by positivity
  have hl1 : l1 (mul η (pow (fluct ξ) p)) ≤ l1 η * l1 (fluct ξ) ^ p := by
    rw [l1_mul]
    exact mul_le_mul_of_nonneg_left (l1_pow_le _ _) (l1_nonneg η)
  rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg hb]
  calc β ^ p / (p.factorial : ℝ) *
        |highPart n h k β (eval ξ 0) p N L (mul η (pow (fluct ξ) p))|
      ≤ β ^ p / (p.factorial : ℝ) * ((∏ i, 1 / (2 * (k i : ℝ))) *
          (l1 η * l1 (fluct ξ) ^ p) * (((n + 1).factorial : ℝ) * (latticeQ k : ℝ) ^ n) *
          (N ^ (-L) * (1 + Real.log N) ^ n * phaseLogMoment β (eval ξ 0) L n p)) := by
        refine mul_le_mul_of_nonneg_left ((abs_highPart_le n h k hk β _ hβ p hL hN _).trans ?_) hb
        refine mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left hl1 hK) hD) hM
    _ = _ := by rw [mul_pow]; ring

/-- The majorant series of the high remainder sums to `highConst · N^{-L}(1+log N)^n`. -/
theorem hasSum_highMajorant (n : ℕ) (k : Fin (n + 1) → ℕ) (β : ℝ) (hβ : 0 < β) {L : ℝ}
    (hL : 0 < L) (N : ℝ) (ξ η : MonoRep (n + 1)) :
    HasSum (fun p : ℕ =>
      ((∏ i, 1 / (2 * (k i : ℝ))) * l1 η * (((n + 1).factorial : ℝ) * (latticeQ k : ℝ) ^ n) *
        (N ^ (-L) * (1 + Real.log N) ^ n)) *
        ((β * l1 (fluct ξ)) ^ p / (p.factorial : ℝ) * phaseLogMoment β (eval ξ 0) L n p))
      (highConst n k β L ξ η * (N ^ (-L) * (1 + Real.log N) ^ n)) := by
  have hs := (summable_phaseLogMoment_series β (eval ξ 0) (l1 (fluct ξ)) L hβ hL
    (l1_nonneg _) n).hasSum.mul_left
    ((∏ i, 1 / (2 * (k i : ℝ))) * l1 η * (((n + 1).factorial : ℝ) * (latticeQ k : ℝ) ^ n) *
      (N ^ (-L) * (1 + Real.log N) ^ n))
  rw [tsum_phaseLogMoment_series β (eval ξ 0) (l1 (fluct ξ)) L hβ hL (l1_nonneg _) n] at hs
  have heq : highConst n k β L ξ η * (N ^ (-L) * (1 + Real.log N) ^ n) =
      ((∏ i, 1 / (2 * (k i : ℝ))) * l1 η * (((n + 1).factorial : ℝ) * (latticeQ k : ℝ) ^ n) *
        (N ^ (-L) * (1 + Real.log N) ^ n)) *
        phaseLogMoment β (eval ξ 0 + l1 (fluct ξ)) L n 0 := by
    unfold highConst
    ring
  rw [heq]
  exact hs

theorem summable_highRemainder_terms (n : ℕ) (h k : Fin (n + 1) → ℕ) (hk : ∀ i, 0 < k i)
    (β : ℝ) (hβ : 0 < β) {L : ℝ} (hL : 0 < L) {N : ℝ} (hN : 1 ≤ N) (ξ η : MonoRep (n + 1)) :
    Summable fun p : ℕ => β ^ p / (p.factorial : ℝ) *
      highPart n h k β (eval ξ 0) p N L (mul η (pow (fluct ξ) p)) :=
  Summable.of_norm_bounded (hasSum_highMajorant n k β hβ hL N ξ η).summable
    (highTerm_le n h k hk β hβ hL hN ξ η)

/-- **Gate C — the high-spectrum remainder bound**:
`|R_high(N)| ≤ K_k ‖η‖₁ (n+1)! Q^n M_{L,n}(ξ(0)+‖J‖₁) · N^{-L} (1+log N)^n` for all `N ≥ 1`. -/
theorem abs_highRemainder_le (n : ℕ) (h k : Fin (n + 1) → ℕ) (hk : ∀ i, 0 < k i) (β : ℝ)
    (hβ : 0 < β) {L : ℝ} (hL : 0 < L) {N : ℝ} (hN : 1 ≤ N) (ξ η : MonoRep (n + 1)) :
    |highRemainder n h k β N L ξ η| ≤
      highConst n k β L ξ η * (N ^ (-L) * (1 + Real.log N) ^ n) := by
  have := tsum_of_norm_bounded (hasSum_highMajorant n k β hβ hL N ξ η)
    (highTerm_le n h k hk β hβ hL hN ξ η)
  rwa [Real.norm_eq_abs] at this

theorem truncSum_term_split (n : ℕ) (h k : Fin (n + 1) → ℕ) (β : ℝ) (N L : ℝ)
    (ξ η : MonoRep (n + 1)) (p : ℕ) :
    β ^ p / (p.factorial : ℝ) *
      ((mul η (pow (fluct ξ) p)).map fun s =>
        s.2 * monomialTruncSum n (h + s.1) k β (eval ξ 0) p N).sum =
      β ^ p / (p.factorial : ℝ) * lowPart n h k β (eval ξ 0) p N L (mul η (pow (fluct ξ) p)) +
        β ^ p / (p.factorial : ℝ) *
          highPart n h k β (eval ξ 0) p N L (mul η (pow (fluct ξ) p)) := by
  rw [← mul_add, lowPart_add_highPart]

theorem summable_lowSeries_terms (n : ℕ) (h k : Fin (n + 1) → ℕ) (hk : ∀ i, 0 < k i) (β : ℝ)
    (hβ : 0 < β) {L : ℝ} (hL : 0 < L) {N : ℝ} (hN : 1 ≤ N) (ξ η : MonoRep (n + 1)) :
    Summable fun p : ℕ => β ^ p / (p.factorial : ℝ) *
      lowPart n h k β (eval ξ 0) p N L (mul η (pow (fluct ξ) p)) := by
  have htot := hasSum_truncSum_series n h k hk β hβ.le (by linarith : (0 : ℝ) < N) ξ η
  have hhigh := summable_highRemainder_terms n h k hk β hβ hL hN ξ η
  refine (htot.summable.sub hhigh).congr fun p => ?_
  rw [truncSum_term_split n h k β N L ξ η p]
  ring

/-- **Decomposition** `Z(N) = lowSeries + highRemainder` for `N ≥ 1`. -/
theorem polyPhaseIntegral_eq_low_add_high (n : ℕ) (h k : Fin (n + 1) → ℕ) (hk : ∀ i, 0 < k i)
    (β : ℝ) (hβ : 0 < β) {L : ℝ} (hL : 0 < L) {N : ℝ} (hN : 1 ≤ N) (ξ η : MonoRep (n + 1)) :
    polyPhaseIntegral n h k β N ξ η =
      lowSeries n h k β N L ξ η + highRemainder n h k β N L ξ η := by
  have htot := hasSum_truncSum_series n h k hk β hβ.le (by linarith : (0 : ℝ) < N) ξ η
  have hhigh := summable_highRemainder_terms n h k hk β hβ hL hN ξ η
  have hlow := summable_lowSeries_terms n h k hk β hβ hL hN ξ η
  unfold lowSeries highRemainder
  rw [← hlow.tsum_add hhigh, ← htot.tsum_eq]
  exact tsum_congr (truncSum_term_split n h k β N L ξ η)

end Laplace.Grammar
