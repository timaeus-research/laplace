/-
Copyright (c) 2026 Timaeus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Laplace.Grammar.BoxPerm
import Mathlib.Data.Fin.Tuple.Sort

/-!
# The multiplicity theorem without hypotheses on the order of the coordinates (grammar §4.2)

For any exponent vectors `k, h : Fin (D+2) → ℕ` (`k_i > 0`), let `p` be the minimum of the candidate
exponents `q_i = (h_i+1)/k_i` and `m+1` its multiplicity (the number of `i` with `q_i = p`). Then

  `∫_{(0,b]^{D+2}} ∏ u_i^{h_i} f(√n ∏ u_i^{k_i}) du ~ C · n^{-p/2} (log n)^m`  for some `C > 0`.

The coordinates are sorted by `Tuple.sort`, the first index attaining the minimum is read off with
`Finset.min'`, and the two cases (all exponents equal / some strictly larger) are units 50 and 58.
This is the leading-term content of `thm:TaylorTree` for constant `ξ` and `η ≡ 1`: the exponent is
half the minimal candidate exponent and the power of the logarithm is the multiplicity minus one.
Zero `sorry`/`axiom`.
-/

open Real MeasureTheory Set Asymptotics Filter Topology

namespace Laplace.Grammar

/-- The candidate exponents (times two) on `Fin d`. -/
noncomputable def finExp {d : ℕ} (k h : Fin d → ℕ) (i : Fin d) : ℝ := ((h i : ℝ) + 1) / k i

theorem chartExp_toNatFun_eq_finExp {d : ℕ} (k h : Fin d → ℕ) (i : Fin d) :
    chartExp (toNatFun k 1) (toNatFun h 0) (i : ℕ) = finExp k h i :=
  chartExp_toNatFun k h i

theorem finExp_pos {d : ℕ} (k h : Fin d → ℕ) (hk : ∀ i, 0 < k i) (i : Fin d) :
    0 < finExp k h i := by
  unfold finExp
  have := hk i
  positivity

/-- The permutation sorting the exponents in non-increasing order. -/
noncomputable def sortPerm {d : ℕ} (k h : Fin d → ℕ) : Equiv.Perm (Fin d) :=
  Tuple.sort fun i => -(finExp k h i)

theorem sortPerm_antitone {d : ℕ} (k h : Fin d → ℕ) : Antitone (finExp k h ∘ sortPerm k h) := by
  intro i j hij
  have := Tuple.monotone_sort (fun i => -(finExp k h i)) hij
  simp only [Function.comp_apply, sortPerm] at this ⊢
  linarith

theorem genScale_pos (b : ℝ) (k h : ℕ → ℕ) (hb : 0 < b) (d : ℕ) : 0 < genScale b k h d := by
  induction d with
  | zero => rw [genScale_zero]; exact one_pos
  | succ d ih => rw [genScale_succ]; exact mul_pos ih (Real.rpow_pos_of_pos (pow_pos hb _) _)

/-- Unit 58's theorem with the dimension given as `r + 2 + m = d`. -/
theorem boxIntegralFin_isEquivalent_of_perm' (β a b : ℝ) (hβ : 0 < β) (hb : 0 < b) {d : ℕ}
    (k h : Fin d → ℕ) (hk : ∀ i, 0 < k i) (σ : Equiv.Perm (Fin d)) (r m : ℕ) (hd : r + 2 + m = d)
    (p : ℝ)
    (hsort : ∀ i, i < r → chartExp (toNatFun (k ∘ σ) 1) (toNatFun (h ∘ σ) 0) (i + 1)
      ≤ chartExp (toNatFun (k ∘ σ) 1) (toNatFun (h ∘ σ) 0) i)
    (hp : ∀ l, r + 1 ≤ l → l ≤ r + 1 + m →
      chartExp (toNatFun (k ∘ σ) 1) (toNatFun (h ∘ σ) 0) l = p)
    (hlt : p < chartExp (toNatFun (k ∘ σ) 1) (toNatFun (h ∘ σ) 0) r) :
    (fun n : ℝ => boxIntegralFin β a b (Real.sqrt n) k h) ~[atTop]
      fun n : ℝ => (∏ i ∈ Finset.range (r + 2 + m), (1 : ℝ) / toNatFun (k ∘ σ) 1 i)
        * genScale b (toNatFun (k ∘ σ) 1) (toNatFun (h ∘ σ) 0) (r + 2 + m)
        * (sortedConst β a (toNatFun (k ∘ σ) 1) (toNatFun (h ∘ σ) 0) r p
            / (2 ^ m * (m.factorial : ℝ)))
        * (n ^ (-(p / 2)) * Real.log n ^ m) := by
  have hk' := toNatFun_pos (k ∘ σ) (fun i => hk (σ i))
  refine (iterChartGen_sorted_isEquivalent β a b _ _ hβ hb hk' r m p hsort hp hlt).congr_left
    (Filter.Eventually.of_forall fun n => ?_)
  beta_reduce
  rw [← boxIntegralFin_perm β a b _ k h σ, boxIntegralFin_eq_toNatFun, boxIntegral_eq_iterChartGen,
    hd]

/-- **The multiplicity theorem, hypothesis-free form**: for any exponents on `Fin (D+2)`, with `p`
the minimal candidate exponent and `m+1` its multiplicity, the box integral is
`~ C n^{-p/2} (log n)^m` for some `C > 0`. -/
theorem boxIntegralFin_isEquivalent_general (β a b : ℝ) (hβ : 0 < β) (hb : 0 < b) (D : ℕ)
    (k h : Fin (D + 2) → ℕ) (hk : ∀ i, 0 < k i) :
    ∃ (p : ℝ) (m : ℕ) (C : ℝ), 0 < C ∧ (∀ i, p ≤ finExp k h i) ∧
      m + 1 = (Finset.univ.filter fun i => finExp k h i = p).card ∧
      (fun n : ℝ => boxIntegralFin β a b (Real.sqrt n) k h) ~[atTop]
        fun n : ℝ => C * (n ^ (-(p / 2)) * Real.log n ^ m) := by
  set σ := sortPerm k h with hσ
  set q : Fin (D + 2) → ℝ := finExp k h ∘ σ with hq
  have hanti : Antitone q := sortPerm_antitone k h
  set p : ℝ := q (Fin.last (D + 1)) with hp
  -- p is the minimum
  have hmin_q : ∀ j, p ≤ q j := fun j => hanti (Fin.le_last j)
  have hmin : ∀ i, p ≤ finExp k h i := by
    intro i
    have := hmin_q (σ.symm i)
    simpa [hq, Function.comp] using this
  -- the first index attaining the minimum
  set S : Finset (Fin (D + 2)) := Finset.univ.filter fun j => q j = p with hS
  have hlastS : Fin.last (D + 1) ∈ S := by
    rw [hS, Finset.mem_filter]
    exact ⟨Finset.mem_univ _, rfl⟩
  have hSne : S.Nonempty := ⟨_, hlastS⟩
  set i₀ : Fin (D + 2) := S.min' hSne with hi₀
  have hi₀S : i₀ ∈ S := Finset.min'_mem S hSne
  have hi₀p : q i₀ = p := by simpa [hS] using hi₀S
  have hge : ∀ j, i₀ ≤ j → q j = p := fun j hj => le_antisymm (hi₀p ▸ hanti hj) (hmin_q j)
  have hlt_p : ∀ j, j < i₀ → p < q j := by
    intro j hj
    refine lt_of_le_of_ne (hmin_q j) fun heq => ?_
    have hjS : j ∈ S := by simp [hS, heq.symm]
    exact absurd (Finset.min'_le S j hjS) (not_le.2 hj)
  -- the multiplicity
  have hcard : (Finset.univ.filter fun i => finExp k h i = p).card = D + 2 - (i₀ : ℕ) := by
    have h1 : (Finset.univ.filter fun i => finExp k h i = p).card = S.card := by
      refine Finset.card_equiv σ.symm fun i => ?_
      simp [hS, hq]
    have h2 : S = Finset.Ici i₀ := by
      ext j
      simp only [hS, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_Ici]
      constructor
      · intro hjp
        by_contra hlt
        exact absurd hjp (hlt_p j (not_le.1 hlt)).ne'
      · exact hge j
    rw [h1, h2, Fin.card_Ici]
  -- chart exponents of the sorted vector
  have hchart : ∀ (i : ℕ) (hi : i < D + 2),
      chartExp (toNatFun (k ∘ σ) 1) (toNatFun (h ∘ σ) 0) i = q ⟨i, hi⟩ := by
    intro i hi
    have := chartExp_toNatFun_eq_finExp (k ∘ σ) (h ∘ σ) ⟨i, hi⟩
    simpa [hq, finExp, Function.comp] using this
  have hk' := toNatFun_pos (k ∘ σ) (fun i => hk (σ i))
  rcases Nat.eq_zero_or_pos (i₀ : ℕ) with h0 | hpos
  · -- all exponents equal: unit 50
    have hall : ∀ i, i ≤ D + 1 → chartExp (toNatFun (k ∘ σ) 1) (toNatFun (h ∘ σ) 0) i = p := by
      intro i hi
      rw [hchart i (by omega)]
      exact hge _ (Fin.le_def.2 (by simp [h0]))
    have hE := iterChartGen_isEquivalent β a b (toNatFun (k ∘ σ) 1) (toNatFun (h ∘ σ) 0) p hβ hb
      hk' D hall
    have hp0 : 0 < p := by rw [hp, hq]; exact finExp_pos k h hk _
    refine ⟨p, D + 1, (∏ i ∈ Finset.range (D + 2), (1 : ℝ) / toNatFun (k ∘ σ) 1 i)
      * (weightedMass β a (p - 1) / (2 ^ (D + 1) * ((D + 1).factorial : ℝ))), ?_, hmin, ?_, ?_⟩
    · have hA := weightedMass_pos β a (p - 1) hβ (by linarith)
      have hK : 0 < ∏ i ∈ Finset.range (D + 2), (1 : ℝ) / toNatFun (k ∘ σ) 1 i :=
        Finset.prod_pos fun i _ => by have := hk' i; positivity
      positivity
    · rw [hcard, h0]; omega
    · refine hE.congr_left (Filter.Eventually.of_forall fun n => ?_)
      beta_reduce
      rw [← boxIntegralFin_perm β a b _ k h σ, boxIntegralFin_eq_toNatFun,
        boxIntegral_eq_iterChartGen]
  · -- some exponent strictly larger: unit 58
    have hi₀le : (i₀ : ℕ) ≤ D + 1 := Nat.lt_succ_iff.1 i₀.isLt
    obtain ⟨r, hr⟩ : ∃ r, (i₀ : ℕ) = r + 1 := ⟨(i₀ : ℕ) - 1, by omega⟩
    set m : ℕ := D + 1 - (i₀ : ℕ) with hm
    have hd : r + 2 + m = D + 2 := by omega
    have hsort : ∀ i, i < r → chartExp (toNatFun (k ∘ σ) 1) (toNatFun (h ∘ σ) 0) (i + 1)
        ≤ chartExp (toNatFun (k ∘ σ) 1) (toNatFun (h ∘ σ) 0) i := by
      intro i hi
      rw [hchart (i + 1) (by omega), hchart i (by omega)]
      exact hanti (Fin.le_def.2 (by simp))
    have hpblock : ∀ l, r + 1 ≤ l → l ≤ r + 1 + m →
        chartExp (toNatFun (k ∘ σ) 1) (toNatFun (h ∘ σ) 0) l = p := by
      intro l hl1 hl2
      rw [hchart l (by omega)]
      exact hge _ (Fin.le_def.2 (by simp; omega))
    have hltr : p < chartExp (toNatFun (k ∘ σ) 1) (toNatFun (h ∘ σ) 0) r := by
      rw [hchart r (by omega)]
      exact hlt_p _ (Fin.lt_def.2 (by simp; omega))
    have hE := boxIntegralFin_isEquivalent_of_perm' β a b hβ hb k h hk σ r m hd p hsort hpblock hltr
    obtain ⟨hC, -⟩ := genTower_logBase β a (toNatFun (k ∘ σ) 1) (toNatFun (h ∘ σ) 0) hβ hk' r p
      hsort (hpblock (r + 1) le_rfl (by omega)) hltr
    refine ⟨p, m, (∏ i ∈ Finset.range (r + 2 + m), (1 : ℝ) / toNatFun (k ∘ σ) 1 i)
      * genScale b (toNatFun (k ∘ σ) 1) (toNatFun (h ∘ σ) 0) (r + 2 + m)
      * (sortedConst β a (toNatFun (k ∘ σ) 1) (toNatFun (h ∘ σ) 0) r p
          / (2 ^ m * (m.factorial : ℝ))), ?_, hmin, ?_, hE⟩
    · have hK : 0 < ∏ i ∈ Finset.range (r + 2 + m), (1 : ℝ) / toNatFun (k ∘ σ) 1 i :=
        Finset.prod_pos fun i _ => by have := hk' i; positivity
      have hD := genScale_pos b (toNatFun (k ∘ σ) 1) (toNatFun (h ∘ σ) 0) hb (r + 2 + m)
      positivity
    · rw [hcard]; omega

end Laplace.Grammar
