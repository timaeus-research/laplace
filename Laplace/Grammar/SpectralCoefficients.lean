/-
Copyright (c) 2026 Timaeus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Laplace.Grammar.HighSpectrumBound
import Laplace.Grammar.StateDensityLeadCoeff

/-!
# Spectral coefficients and regrouping (Stage 3g, Gate D)

Unit 237 (Taylor-tree programme; Astra #27). The low-spectrum part of the polynomial Taylor tree,
with truncated moments replaced by full fluctuation moments, is regrouped by spectral exponent
`μ ∈ latticeBelow Q L` and log power `j`:
```
mainPart_p = ∑_{μ ∈ Λ_L} ∑_{j ≤ n} N^{-μ} (log N)^j · coeffTerm_p(μ, j),
coeffTerm_p(μ, j)
  = K_k ∑_{(γ,c) ∈ P_p} c ∑_{q=j}^{n} coeffAt(ρ_{h+γ}, μ, q) C(q,j) fluctMoment_p(μ, q-j)
```
(`mainPart_eq_sum`: aggregate the list entries with `coeffAt` — the coefficient is the aggregated
one, never that of a single list entry — and reflect the binomial sum). The **spectral
coefficient** `A_{μ,j} = ∑_p β^p/p! coeffTerm_p(μ,j)` (`spectralCoeff`) is defined independently of
the cutoff `L` and its series is absolutely convergent (`summable_coeffTerm_series`: the uniform
budget `|coeffAt| ≤ (n+1)! Q^n`, `C(q,j) ≤ 2^n`, `|fluctMoment| ≤ M_{μ,n,p}(a)` and the Tonelli
majorant of unit 234; **Gate D**). Consequently the main series regroups exactly
(`mainSeries_eq_sum`):
```
∑_p β^p/p! mainPart_p = ∑_{μ ∈ Λ_L} N^{-μ} ∑_{j ≤ n} A_{μ,j} (log N)^j.
```
No `sorry` and no additional `axiom` declarations.
-/

open MeasureTheory Set Real Filter Topology

namespace Laplace.Grammar

open MonoRep

/-! ### A uniform bound on the fluctuation moments -/

/-- `|fluctMoment β a p μ i| ≤ M_{μ,n,p}(a)` for `i ≤ n`, `μ > 0`, `β > 0`. -/
theorem abs_fluctMoment_le (β a : ℝ) (hβ : 0 < β) (p : ℕ) {μ : ℝ} (hμ : 0 < μ) {i n : ℕ}
    (hi : i ≤ n) : |fluctMoment β a p μ i| ≤ phaseLogMoment β a μ n p := by
  unfold fluctMoment phaseLogMoment
  refine abs_integral_le_integral_abs.trans ?_
  refine integral_mono_of_nonneg (Eventually.of_forall fun t => abs_nonneg _)
    (integrableOn_logMajorant β a μ hβ hμ n p)
    (ae_restrict_of_forall_mem measurableSet_Ioi fun t ht => ?_)
  have ht0 : 0 < t := mem_Ioi.1 ht
  beta_reduce
  rw [abs_mul, abs_mul, abs_of_nonneg (Real.rpow_nonneg ht0.le _),
    abs_of_nonneg (phaseKernel_nonneg _ _ _ _), abs_pow, abs_neg]
  unfold logMajorant
  refine mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left ?_ (Real.rpow_nonneg ht0.le _))
    (phaseKernel_nonneg _ _ _ _)
  have h0 := abs_nonneg (Real.log t)
  calc |Real.log t| ^ i ≤ (1 + |Real.log t|) ^ i := pow_le_pow_left₀ h0 (by linarith) i
    _ ≤ (1 + |Real.log t|) ^ n := pow_le_pow_right₀ (by linarith) hi

/-! ### The lattice below the cutoff -/

theorem lt_of_mem_latticeBelow {Q : ℕ} (hQ : 0 < Q) {L μ : ℝ} (hμ : μ ∈ latticeBelow Q L) :
    μ < L := by
  obtain ⟨m, hm, rfl⟩ := Finset.mem_image.1 hμ
  have hQ' : (0 : ℝ) < Q := by exact_mod_cast hQ
  rw [div_lt_iff₀ hQ']
  exact Nat.lt_ceil.1 (Finset.mem_range.1 hm)

/-! ### Regrouping a list by aggregated coefficients -/

open Classical in
theorem sum_sum_ite_coeff (S : Finset ℝ) (R : Finset ℕ) (μ₀ : ℝ) {q₀ : ℕ} (hq : q₀ ∈ R) (x : ℝ)
    (G : ℝ → ℕ → ℝ) :
    ∑ μ ∈ S, ∑ q ∈ R, (if μ₀ = μ ∧ q₀ = q then x else 0) * G μ q =
      if μ₀ ∈ S then x * G μ₀ q₀ else 0 := by
  have h1 : ∀ μ, ∑ q ∈ R, (if μ₀ = μ ∧ q₀ = q then x else 0) * G μ q =
      if μ₀ = μ then x * G μ q₀ else 0 := by
    intro μ
    by_cases hμ : μ₀ = μ
    · subst hμ
      simp only [true_and, ite_mul, zero_mul, if_true]
      rw [Finset.sum_ite_eq, if_pos hq]
    · simp [hμ]
  simp_rw [h1]
  rw [Finset.sum_ite_eq]

/-- Regrouping a lattice-supported representation by aggregated coefficients: for entries with
exponents in `Q⁻¹ℕ` and degrees `≤ n`,
`∑_{entries, μ < L} c · G μ j = ∑_{μ ∈ Λ_L} ∑_{q ≤ n} coeffAt μ q · G μ q`. -/
theorem sum_map_lt_eq_sum_coeffAt {Q : ℕ} (hQ : 0 < Q) (L : ℝ) (n : ℕ) (G : ℝ → ℕ → ℝ) :
    ∀ c : PowLogRep, (∀ t ∈ c, ∃ m : ℕ, t.1 = (m : ℝ) / Q) → (∀ t ∈ c, t.2.1 < n + 1) →
      (c.map fun t => if t.1 < L then t.2.2 * G t.1 t.2.1 else 0).sum =
        ∑ μ ∈ latticeBelow Q L, ∑ q ∈ Finset.range (n + 1),
          PowLogRep.coeffAt c μ q * G μ q := by
  intro c
  induction c with
  | nil => simp [PowLogRep.coeffAt_nil]
  | cons t c ih =>
    intro hlat hdeg
    have ih' := ih (fun s hs => hlat s (List.mem_cons_of_mem _ hs))
      (fun s hs => hdeg s (List.mem_cons_of_mem _ hs))
    rw [List.map_cons, List.sum_cons, ih']
    simp only [PowLogRep.coeffAt_cons, add_mul, Finset.sum_add_distrib]
    congr 1
    have hq : t.2.1 ∈ Finset.range (n + 1) :=
      Finset.mem_range.2 (hdeg t (List.mem_cons.2 (Or.inl rfl)))
    rw [sum_sum_ite_coeff (latticeBelow Q L) (Finset.range (n + 1)) t.1 hq t.2.2 G]
    obtain ⟨m, hm⟩ := hlat t (List.mem_cons.2 (Or.inl rfl))
    by_cases hL : t.1 < L
    · rw [if_pos hL, if_pos]
      rw [hm] at hL ⊢
      exact mem_latticeBelow hQ hL
    · rw [if_neg hL, if_neg]
      exact fun hmem => hL (lt_of_mem_latticeBelow hQ hmem)

/-! ### Binomial reflection -/

theorem sum_choose_reflect (q : ℕ) (x : ℝ) (f : ℕ → ℝ) :
    ∑ i ∈ Finset.range (q + 1), (q.choose i : ℝ) * x ^ (q - i) * f i =
      ∑ j ∈ Finset.range (q + 1), (q.choose j : ℝ) * x ^ j * f (q - j) := by
  rw [← Finset.sum_range_reflect]
  refine Finset.sum_congr rfl fun j hj => ?_
  have hj' : j ≤ q := Nat.lt_succ_iff.1 (Finset.mem_range.1 hj)
  rw [show q + 1 - 1 - j = q - j by omega, Nat.choose_symm hj', show q - (q - j) = j by omega]

/-! ### Main entries and the coefficient terms -/

/-- One density entry with the full fluctuation moments. -/
noncomputable def entryMain (β a : ℝ) (p : ℕ) (N : ℝ) (t : ℝ × ℕ × ℝ) : ℝ :=
  t.2.2 * (N ^ (-t.1) * ∑ i ∈ Finset.range (t.2.1 + 1),
    (t.2.1.choose i : ℝ) * (Real.log N) ^ (t.2.1 - i) * fluctMoment β a p t.1 i)

/-- The low-spectrum part with full moments. -/
noncomputable def lowMain (β a : ℝ) (p : ℕ) (N L : ℝ) (c : PowLogRep) : ℝ :=
  (c.map fun t => if t.1 < L then entryMain β a p N t else 0).sum

/-- The Stage 1 weights of the monomial `u^h` with exponents `2k`. -/
noncomputable def monoWeights {d : ℕ} (h k : Fin d → ℕ) : Fin d → ℝ :=
  fun i => ((h i : ℝ) + 1) / (2 * (k i : ℝ)) - 1

theorem monoWeights_lattice {d : ℕ} (h k : Fin d → ℕ) (hk : ∀ i, 0 < k i) (i : Fin d) :
    ∃ m : ℕ, monoWeights h k i + 1 = (m : ℝ) / latticeQ k := by
  obtain ⟨m, -, hm⟩ := ratio_mem_lattice k hk i (h i)
  exact ⟨m, by unfold monoWeights; rw [sub_add_cancel]; exact hm⟩

theorem stateDensityRep_monoWeights_lattice (n : ℕ) (h k : Fin (n + 1) → ℕ) (hk : ∀ i, 0 < k i) :
    ∀ t ∈ stateDensityRep n (monoWeights h k), ∃ m : ℕ, t.1 = (m : ℝ) / latticeQ k := by
  intro t ht
  obtain ⟨i, hi⟩ := stateDensityRep_exponent_mem n _ t ht
  obtain ⟨m, hm⟩ := monoWeights_lattice h k hk i
  exact ⟨m, by rw [hi, hm]⟩

theorem stateDensityRep_monoWeights_pos (n : ℕ) (h k : Fin (n + 1) → ℕ) (hk : ∀ i, 0 < k i) :
    ∀ t ∈ stateDensityRep n (monoWeights h k), 0 < t.1 := by
  intro t ht
  obtain ⟨i, hi⟩ := stateDensityRep_exponent_mem n _ t ht
  rw [hi]
  unfold monoWeights
  rw [sub_add_cancel]
  have := hk i
  positivity

/-- The aggregated coefficient of a monomial density is bounded by `(n+1)! Q^n`, uniformly. -/
theorem abs_coeffAt_stateDensityRep_le (n : ℕ) (h k : Fin (n + 1) → ℕ) (hk : ∀ i, 0 < k i)
    (μ : ℝ) (q : ℕ) :
    |PowLogRep.coeffAt (stateDensityRep n (monoWeights h k)) μ q| ≤
      ((n + 1).factorial : ℝ) * (latticeQ k : ℝ) ^ n := by
  have hQ1 : (1 : ℝ) ≤ latticeQ k := by exact_mod_cast latticeQ_pos k hk
  have h1 : (1 : ℝ) ≤ (q.factorial : ℝ) * (latticeQ k : ℝ) ^ q :=
    one_le_mul_of_one_le_of_one_le (by exact_mod_cast q.factorial_pos) (one_le_pow₀ hQ1)
  calc |PowLogRep.coeffAt (stateDensityRep n (monoWeights h k)) μ q|
      ≤ |PowLogRep.coeffAt (stateDensityRep n (monoWeights h k)) μ q| *
          ((q.factorial : ℝ) * (latticeQ k : ℝ) ^ q) := le_mul_of_one_le_right (abs_nonneg _) h1
    _ ≤ PowLogRep.budget (latticeQ k) (stateDensityRep n (monoWeights h k)) :=
        PowLogRep.abs_coeffAt_le hQ1 _ μ q
    _ ≤ _ := budget_stateDensityRep_le hQ1 ⟨latticeQ k, rfl⟩ n _ (monoWeights_lattice h k hk)

/-- `coeffAt` vanishes at an exponent not carried by the list. -/
theorem coeffAt_eq_zero_of_forall_ne (c : PowLogRep) {μ : ℝ} (hc : ∀ t ∈ c, t.1 ≠ μ) (q : ℕ) :
    PowLogRep.coeffAt c μ q = 0 := by
  induction c with
  | nil => rfl
  | cons t c ih =>
    rw [PowLogRep.coeffAt_cons, if_neg (fun h => hc t (List.mem_cons.2 (Or.inl rfl)) h.1),
      zero_add]
    exact ih fun s hs => hc s (List.mem_cons.2 (Or.inr hs))

/-- Per phase order: the coefficient of `N^{-μ} (log N)^j` (the paper's `A_{μ,j}` before the
sum over phase orders). -/
noncomputable def coeffTerm (n : ℕ) (h k : Fin (n + 1) → ℕ) (β a : ℝ) (p : ℕ) (μ : ℝ) (j : ℕ)
    (P : MonoRep (n + 1)) : ℝ :=
  (∏ i, 1 / (2 * (k i : ℝ))) * (P.map fun s => s.2 * ∑ q ∈ Finset.Ico j (n + 1),
    PowLogRep.coeffAt (stateDensityRep n (monoWeights (h + s.1) k)) μ q * (q.choose j : ℝ) *
      fluctMoment β a p μ (q - j)).sum

/-- The low-spectrum main part of one phase order. -/
noncomputable def mainPart (n : ℕ) (h k : Fin (n + 1) → ℕ) (β a : ℝ) (p : ℕ) (N L : ℝ)
    (P : MonoRep (n + 1)) : ℝ :=
  (∏ i, 1 / (2 * (k i : ℝ))) * (P.map fun s => s.2 *
    lowMain β a p N L (stateDensityRep n (monoWeights (h + s.1) k))).sum

theorem list_sum_finset_sum_comm {ι κ : Type*} (P : List ι) (S : Finset κ) (f : ι → ℝ)
    (g : ι → κ → ℝ) :
    (P.map fun s => f s * ∑ μ ∈ S, g s μ).sum = ∑ μ ∈ S, (P.map fun s => f s * g s μ).sum := by
  induction P with
  | nil => simp
  | cons s P ih =>
    rw [List.map_cons, List.sum_cons, ih, Finset.mul_sum, ← Finset.sum_add_distrib]
    simp only [List.map_cons, List.sum_cons]

/-- Regrouping one monomial density: `lowMain = ∑_{μ ∈ Λ_L} ∑_{j ≤ n} N^{-μ} (log N)^j T(μ,j)`. -/
theorem lowMain_eq_sum (n : ℕ) (h k : Fin (n + 1) → ℕ) (hk : ∀ i, 0 < k i) (β a : ℝ) (p : ℕ)
    (N L : ℝ) :
    lowMain β a p N L (stateDensityRep n (monoWeights h k)) =
      ∑ μ ∈ latticeBelow (latticeQ k) L, ∑ j ∈ Finset.range (n + 1),
        N ^ (-μ) * (Real.log N) ^ j * ∑ q ∈ Finset.Ico j (n + 1),
          PowLogRep.coeffAt (stateDensityRep n (monoWeights h k)) μ q * (q.choose j : ℝ) *
            fluctMoment β a p μ (q - j) := by
  simp only [lowMain, entryMain]
  have hdeg : ∀ t ∈ stateDensityRep n (monoWeights h k), t.2.1 < n + 1 := fun t ht =>
    Nat.lt_succ_of_le (stateDensityRep_degree_le n _ t ht)
  rw [sum_map_lt_eq_sum_coeffAt (latticeQ_pos k hk) L n
    (fun μ q => N ^ (-μ) * ∑ i ∈ Finset.range (q + 1),
      (q.choose i : ℝ) * (Real.log N) ^ (q - i) * fluctMoment β a p μ i)
    _ (stateDensityRep_monoWeights_lattice n h k hk) hdeg]
  refine Finset.sum_congr rfl fun μ _ => ?_
  -- reflect the binomial sums and swap `q` with `j`
  have hrefl : ∀ q : ℕ, ∑ i ∈ Finset.range (q + 1),
      (q.choose i : ℝ) * (Real.log N) ^ (q - i) * fluctMoment β a p μ i =
      ∑ j ∈ Finset.range (q + 1), (q.choose j : ℝ) * (Real.log N) ^ j *
        fluctMoment β a p μ (q - j) := fun q => sum_choose_reflect q _ _
  simp_rw [hrefl, Finset.mul_sum]
  rw [Finset.sum_comm' (t' := Finset.range (n + 1)) (s' := fun j => Finset.Ico j (n + 1))]
  · refine Finset.sum_congr rfl fun j _ => ?_
    refine Finset.sum_congr rfl fun q _ => ?_
    ring
  · intro q j
    simp only [Finset.mem_range, Finset.mem_Ico]
    omega

/-- **Regrouping of the main part** by spectral exponent and log power. -/
theorem mainPart_eq_sum (n : ℕ) (h k : Fin (n + 1) → ℕ) (hk : ∀ i, 0 < k i) (β a : ℝ) (p : ℕ)
    (N L : ℝ) (P : MonoRep (n + 1)) :
    mainPart n h k β a p N L P = ∑ μ ∈ latticeBelow (latticeQ k) L, ∑ j ∈ Finset.range (n + 1),
      N ^ (-μ) * (Real.log N) ^ j * coeffTerm n h k β a p μ j P := by
  unfold mainPart coeffTerm
  simp_rw [lowMain_eq_sum n _ k hk β a p N L]
  rw [list_sum_finset_sum_comm, Finset.mul_sum]
  refine Finset.sum_congr rfl fun μ _ => ?_
  rw [list_sum_finset_sum_comm, Finset.mul_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  have : (P.map fun s => s.2 * (N ^ (-μ) * (Real.log N) ^ j * ∑ q ∈ Finset.Ico j (n + 1),
      PowLogRep.coeffAt (stateDensityRep n (monoWeights (h + s.1) k)) μ q * (q.choose j : ℝ) *
        fluctMoment β a p μ (q - j))).sum =
      N ^ (-μ) * (Real.log N) ^ j * (P.map fun s => s.2 * ∑ q ∈ Finset.Ico j (n + 1),
      PowLogRep.coeffAt (stateDensityRep n (monoWeights (h + s.1) k)) μ q * (q.choose j : ℝ) *
        fluctMoment β a p μ (q - j)).sum := by
    rw [← List.sum_map_mul_left]
    congr 1
    exact List.map_congr_left fun s _ => by ring
  rw [this]
  ring

/-! ### Absolute summability of the coefficient series (Gate D) -/

/-- Uniform bound on one coefficient term (`μ > 0`). -/
theorem abs_coeffTerm_le (n : ℕ) (h k : Fin (n + 1) → ℕ) (hk : ∀ i, 0 < k i) (β a : ℝ)
    (hβ : 0 < β) (p : ℕ) {μ : ℝ} (hμ : 0 < μ) (j : ℕ) (P : MonoRep (n + 1)) :
    |coeffTerm n h k β a p μ j P| ≤ (∏ i, 1 / (2 * (k i : ℝ))) * l1 P *
      ((n + 1 : ℝ) * (((n + 1).factorial : ℝ) * (latticeQ k : ℝ) ^ n) * 2 ^ n) *
      phaseLogMoment β a μ n p := by
  have hK : 0 ≤ ∏ i, 1 / (2 * (k i : ℝ)) := Finset.prod_nonneg fun i _ => by positivity
  set D : ℝ := (n + 1 : ℝ) * (((n + 1).factorial : ℝ) * (latticeQ k : ℝ) ^ n) * 2 ^ n with hD
  set M := phaseLogMoment β a μ n p with hM
  have hM0 : 0 ≤ M := phaseLogMoment_nonneg β a μ n p
  have hD0 : 0 ≤ D := by positivity
  -- inner sum bound, uniform in the monomial
  have hinner : ∀ h' : Fin (n + 1) → ℕ, |∑ q ∈ Finset.Ico j (n + 1),
      PowLogRep.coeffAt (stateDensityRep n (monoWeights h' k)) μ q * (q.choose j : ℝ) *
        fluctMoment β a p μ (q - j)| ≤ D * M := by
    intro h'
    refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
    have hterm : ∀ q ∈ Finset.Ico j (n + 1),
        |PowLogRep.coeffAt (stateDensityRep n (monoWeights h' k)) μ q * (q.choose j : ℝ) *
          fluctMoment β a p μ (q - j)| ≤
        (((n + 1).factorial : ℝ) * (latticeQ k : ℝ) ^ n) * 2 ^ n * M := by
      intro q hq
      have hqn : q ≤ n := Nat.lt_succ_iff.1 (Finset.mem_Ico.1 hq).2
      rw [abs_mul, abs_mul, Nat.abs_cast]
      refine mul_le_mul (mul_le_mul (abs_coeffAt_stateDensityRep_le n h' k hk μ q) ?_
        (by positivity) (by positivity)) (abs_fluctMoment_le β a hβ p hμ (by omega))
        (abs_nonneg _) (by positivity)
      calc (q.choose j : ℝ) ≤ (2 ^ q : ℕ) := by exact_mod_cast Nat.choose_le_two_pow q j
        _ ≤ 2 ^ n := by exact_mod_cast Nat.pow_le_pow_right two_pos hqn
    refine (Finset.sum_le_card_nsmul _ _ _ hterm).trans ?_
    rw [nsmul_eq_mul, Nat.card_Ico, hD]
    have hcard : ((n + 1 - j : ℕ) : ℝ) ≤ n + 1 := by exact_mod_cast Nat.sub_le (n + 1) j
    calc ((n + 1 - j : ℕ) : ℝ) * ((((n + 1).factorial : ℝ) * (latticeQ k : ℝ) ^ n) * 2 ^ n * M)
        ≤ (n + 1 : ℝ) * ((((n + 1).factorial : ℝ) * (latticeQ k : ℝ) ^ n) * 2 ^ n * M) :=
          mul_le_mul_of_nonneg_right hcard (by positivity)
      _ = _ := by ring
  unfold coeffTerm
  rw [abs_mul, abs_of_nonneg hK, mul_assoc, mul_assoc]
  refine mul_le_mul_of_nonneg_left ?_ hK
  induction P with
  | nil => simp [l1]
  | cons s P ih =>
    rw [List.map_cons, List.sum_cons, l1_cons, add_mul]
    refine (abs_add_le _ _).trans (add_le_add ?_ ih)
    rw [abs_mul]
    exact mul_le_mul_of_nonneg_left (hinner (h + s.1)) (abs_nonneg _)

/-- The `N`-free constant of the coefficient majorant. -/
noncomputable def coeffConst (n : ℕ) (k : Fin (n + 1) → ℕ) (η : MonoRep (n + 1)) : ℝ :=
  (∏ i, 1 / (2 * (k i : ℝ))) * l1 η *
    ((n + 1 : ℝ) * (((n + 1).factorial : ℝ) * (latticeQ k : ℝ) ^ n) * 2 ^ n)

theorem coeffTerm_series_le (n : ℕ) (h k : Fin (n + 1) → ℕ) (hk : ∀ i, 0 < k i) (β : ℝ)
    (hβ : 0 < β) {μ : ℝ} (hμ : 0 < μ) (j : ℕ) (ξ η : MonoRep (n + 1)) (p : ℕ) :
    ‖β ^ p / (p.factorial : ℝ) * coeffTerm n h k β (eval ξ 0) p μ j (mul η (pow (fluct ξ) p))‖ ≤
      coeffConst n k η *
        ((β * l1 (fluct ξ)) ^ p / (p.factorial : ℝ) * phaseLogMoment β (eval ξ 0) μ n p) := by
  have hK : 0 ≤ ∏ i, 1 / (2 * (k i : ℝ)) := Finset.prod_nonneg fun i _ => by positivity
  have hD : 0 ≤ (n + 1 : ℝ) * (((n + 1).factorial : ℝ) * (latticeQ k : ℝ) ^ n) * 2 ^ n := by
    positivity
  have hM := phaseLogMoment_nonneg β (eval ξ 0) μ n p
  have hb : 0 ≤ β ^ p / (p.factorial : ℝ) := by positivity
  have hl1 : l1 (mul η (pow (fluct ξ) p)) ≤ l1 η * l1 (fluct ξ) ^ p := by
    rw [l1_mul]
    exact mul_le_mul_of_nonneg_left (l1_pow_le _ _) (l1_nonneg η)
  rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg hb]
  calc β ^ p / (p.factorial : ℝ) *
        |coeffTerm n h k β (eval ξ 0) p μ j (mul η (pow (fluct ξ) p))|
      ≤ β ^ p / (p.factorial : ℝ) * ((∏ i, 1 / (2 * (k i : ℝ))) * (l1 η * l1 (fluct ξ) ^ p) *
          ((n + 1 : ℝ) * (((n + 1).factorial : ℝ) * (latticeQ k : ℝ) ^ n) * 2 ^ n) *
          phaseLogMoment β (eval ξ 0) μ n p) := by
        refine mul_le_mul_of_nonneg_left
          ((abs_coeffTerm_le n h k hk β _ hβ p hμ j _).trans ?_) hb
        exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left hl1 hK) hD) hM
    _ = _ := by unfold coeffConst; rw [mul_pow]; ring

/-- **Gate D — absolute convergence of the spectral-coefficient series** for every `μ`. -/
theorem summable_coeffTerm_series (n : ℕ) (h k : Fin (n + 1) → ℕ) (hk : ∀ i, 0 < k i) (β : ℝ)
    (hβ : 0 < β) (μ : ℝ) (j : ℕ) (ξ η : MonoRep (n + 1)) :
    Summable fun p : ℕ => β ^ p / (p.factorial : ℝ) *
      coeffTerm n h k β (eval ξ 0) p μ j (mul η (pow (fluct ξ) p)) := by
  rcases lt_or_ge 0 μ with hμ | hμ
  · exact Summable.of_norm_bounded ((summable_phaseLogMoment_series β (eval ξ 0) (l1 (fluct ξ))
      μ hβ hμ (l1_nonneg _) n).mul_left (coeffConst n k η))
      (coeffTerm_series_le n h k hk β hβ hμ j ξ η)
  · -- no density exponent is `≤ 0`: every coefficient term vanishes
    have hzero : ∀ p, coeffTerm n h k β (eval ξ 0) p μ j (mul η (pow (fluct ξ) p)) = 0 := by
      intro p
      unfold coeffTerm
      rw [mul_eq_zero]
      right
      rw [List.sum_eq_zero]
      intro x hx
      obtain ⟨s, -, rfl⟩ := List.mem_map.1 hx
      rw [Finset.sum_eq_zero, mul_zero]
      intro q _
      rw [coeffAt_eq_zero_of_forall_ne _ (fun t ht hμt => by
        have := stateDensityRep_monoWeights_pos n (h + s.1) k hk t ht
        rw [hμt] at this
        exact absurd this (not_lt.2 hμ)) q]
      ring
    simp_rw [hzero, mul_zero]
    exact summable_zero

/-- **The spectral coefficient** `A_{μ,j}` — defined without reference to any cutoff. -/
noncomputable def spectralCoeff (n : ℕ) (h k : Fin (n + 1) → ℕ) (β : ℝ) (ξ η : MonoRep (n + 1))
    (μ : ℝ) (j : ℕ) : ℝ :=
  ∑' p : ℕ, β ^ p / (p.factorial : ℝ) *
    coeffTerm n h k β (eval ξ 0) p μ j (mul η (pow (fluct ξ) p))

/-- The main series `∑_p β^p/p! mainPart_p`. -/
noncomputable def mainSeries (n : ℕ) (h k : Fin (n + 1) → ℕ) (β N L : ℝ) (ξ η : MonoRep (n + 1)) :
    ℝ :=
  ∑' p : ℕ, β ^ p / (p.factorial : ℝ) *
    mainPart n h k β (eval ξ 0) p N L (mul η (pow (fluct ξ) p))

/-- **Regrouped main series**:
`∑_p β^p/p! mainPart_p = ∑_{μ ∈ Λ_L} N^{-μ} ∑_{j ≤ n} A_{μ,j} (log N)^j`. -/
theorem mainSeries_eq_sum (n : ℕ) (h k : Fin (n + 1) → ℕ) (hk : ∀ i, 0 < k i) (β : ℝ)
    (hβ : 0 < β) (N L : ℝ) (ξ η : MonoRep (n + 1)) :
    mainSeries n h k β N L ξ η = ∑ μ ∈ latticeBelow (latticeQ k) L, N ^ (-μ) *
      ∑ j ∈ Finset.range (n + 1), spectralCoeff n h k β ξ η μ j * (Real.log N) ^ j := by
  unfold mainSeries spectralCoeff
  have hsum : ∀ μ j, Summable fun p : ℕ => N ^ (-μ) * (Real.log N) ^ j *
      (β ^ p / (p.factorial : ℝ) *
        coeffTerm n h k β (eval ξ 0) p μ j (mul η (pow (fluct ξ) p))) := fun μ j =>
    (summable_coeffTerm_series n h k hk β hβ μ j ξ η).mul_left _
  have hterm : ∀ p : ℕ, β ^ p / (p.factorial : ℝ) *
      mainPart n h k β (eval ξ 0) p N L (mul η (pow (fluct ξ) p)) =
      ∑ μ ∈ latticeBelow (latticeQ k) L, ∑ j ∈ Finset.range (n + 1),
        N ^ (-μ) * (Real.log N) ^ j * (β ^ p / (p.factorial : ℝ) *
          coeffTerm n h k β (eval ξ 0) p μ j (mul η (pow (fluct ξ) p))) := by
    intro p
    rw [mainPart_eq_sum n h k hk, Finset.mul_sum]
    refine Finset.sum_congr rfl fun μ _ => ?_
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    ring
  simp_rw [hterm]
  rw [Summable.tsum_finsetSum fun μ _ => summable_sum fun j _ => hsum μ j]
  refine Finset.sum_congr rfl fun μ _ => ?_
  rw [Summable.tsum_finsetSum fun j _ => hsum μ j, Finset.mul_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [tsum_mul_left]
  ring

end Laplace.Grammar
