/-
Copyright (c) 2026 Timaeus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Laplace.Grammar.StateDensityAPI
import Laplace.Grammar.MellinCoefficient

/-!
# The leading coefficient of the state density

Unit 226 (Taylor-tree programme, Stage 1d). Let `l = min (wᵢ + 1)` with multiplicity `m`. The
state density `v = eval (stateDensityRep n w)` has terms `z^{μ-1} (-log z)^j` with `μ ≥ l` and, at
`μ = l`, `j ≤ m - 1` (unit 224). Its **top coefficient** (the coefficient of
`z^{l-1} (-log z)^{m-1}`, `PowLogRep.coeffAt`) is
```
c_{l,m-1} = (1/(m-1)!) · ∏_{i : wᵢ+1 ≠ l} 1/(wᵢ + 1 - l)
```
(`stateDensityRep_leadCoeff`). The proof is Abelian, as in Headline XXI: `(s+l)^m ∫₀¹ z^s v(z) dz`
is computed in two ways as `s → -l⁺` — from the product Mellin transform `∏ 1/(wᵢ+s+1)`
(unit 225) it tends to the product on the right; from the termwise transform
`∑ cₜ jₜ!/(s+μₜ)^{jₜ+1}` every term tends to `0` except the top one, which tends to
`(m-1)! · c_{l,m-1}`. In the monomial normalisation (`wᵢ = (hᵢ+1)/(2kᵢ) - 1`, Jacobian `∏ 1/(2kᵢ)`)
the top coefficient of the monomial state density is `a_{-m}/(m-1)!` with `a_{-m}` the paper's
leading Laurent coefficient (= `mellinCoeff h k l 1` of Headline XXI): the density coefficient is
the Laurent coefficient divided by `(m-1)!` (`monomial_leadCoeff`). Zero `sorry`/`axiom`.
-/

open MeasureTheory Set Real Filter Topology

namespace Laplace.Grammar

open Classical in
/-- The coefficient of `z^{μ-1} (-log z)^j` in a representation (sum over matching terms). -/
noncomputable def PowLogRep.coeffAt (c : PowLogRep) (μ : ℝ) (j : ℕ) : ℝ :=
  ((c.filter fun t => t.1 = μ ∧ t.2.1 = j).map fun t => t.2.2).sum

theorem PowLogRep.coeffAt_nil (μ : ℝ) (j : ℕ) : PowLogRep.coeffAt [] μ j = 0 := rfl

open Classical in
theorem PowLogRep.coeffAt_cons (t : ℝ × ℕ × ℝ) (c : PowLogRep) (μ : ℝ) (j : ℕ) :
    PowLogRep.coeffAt (t :: c) μ j =
      (if t.1 = μ ∧ t.2.1 = j then t.2.2 else 0) + PowLogRep.coeffAt c μ j := by
  unfold PowLogRep.coeffAt
  rw [List.filter_cons]
  by_cases h : t.1 = μ ∧ t.2.1 = j <;> simp [h]

/-! ### The two Abelian limits -/

theorem tendsto_add_min (l : ℝ) : Tendsto (fun s : ℝ => s + l) (𝓝[>] (-l)) (𝓝 0) := by
  have : Tendsto (fun s : ℝ => s + l) (𝓝 (-l)) (𝓝 (-l + l)) :=
    (continuous_id.add continuous_const).tendsto _
  rw [neg_add_cancel] at this
  exact this.mono_left nhdsWithin_le_nhds

theorem tendsto_add_const_min (l a : ℝ) : Tendsto (fun s : ℝ => s + a) (𝓝[>] (-l)) (𝓝 (-l + a)) :=
  ((continuous_id.add continuous_const).tendsto _).mono_left nhdsWithin_le_nhds

/-- Limit of one term of the termwise Mellin transform, multiplied by `(s+l)^m`. -/
theorem term_tendsto (l : ℝ) (m : ℕ) (hm : 0 < m) (t : ℝ × ℕ × ℝ) (hμ : l ≤ t.1)
    (hdeg : t.1 = l → t.2.1 < m) :
    Tendsto (fun s : ℝ => (s + l) ^ m * (t.2.2 * ((t.2.1.factorial : ℝ) / (s + t.1) ^ (t.2.1 + 1))))
      (𝓝[>] (-l))
      (𝓝 (if t.1 = l ∧ t.2.1 = m - 1 then t.2.2 * ((m - 1).factorial : ℝ) else 0)) := by
  obtain ⟨μ, j, c⟩ := t
  simp only at hμ hdeg ⊢
  by_cases hμl : μ = l
  · subst hμl
    have hj : j < m := hdeg rfl
    have hev : ∀ᶠ s in 𝓝[>] (-μ),
        c * (j.factorial : ℝ) * (s + μ) ^ (m - 1 - j) =
          (s + μ) ^ m * (c * ((j.factorial : ℝ) / (s + μ) ^ (j + 1))) := by
      filter_upwards [self_mem_nhdsWithin] with s hs
      have hs0 : s + μ ≠ 0 := by
        have : -μ < s := hs
        linarith
      have hpow : (s + μ) ^ m = (s + μ) ^ (m - 1 - j) * (s + μ) ^ (j + 1) := by
        rw [← pow_add]
        congr 1
        omega
      rw [hpow]
      field_simp
    have hlim := ((tendsto_add_min μ).pow (m - 1 - j)).const_mul (c * (j.factorial : ℝ))
    have key : (if μ = μ ∧ j = m - 1 then c * ((m - 1).factorial : ℝ) else 0) =
        c * (j.factorial : ℝ) * (0 : ℝ) ^ (m - 1 - j) := by
      by_cases hjm : j = m - 1
      · subst hjm
        simp
      · rw [if_neg (fun h => hjm h.2), zero_pow (by omega), mul_zero]
    rw [key]
    exact hlim.congr' hev
  · have hlt : l < μ := lt_of_le_of_ne hμ (Ne.symm hμl)
    have hne : (-l + μ) ^ (j + 1) ≠ 0 := pow_ne_zero _ (by linarith)
    have h1 : Tendsto (fun s : ℝ => (s + l) ^ m) (𝓝[>] (-l)) (𝓝 0) := by
      have := (tendsto_add_min l).pow m
      rwa [zero_pow hm.ne'] at this
    have h2 : Tendsto (fun s : ℝ => c * ((j.factorial : ℝ) / (s + μ) ^ (j + 1))) (𝓝[>] (-l))
        (𝓝 (c * ((j.factorial : ℝ) / (-l + μ) ^ (j + 1)))) :=
      tendsto_const_nhds.mul
        (tendsto_const_nhds.div ((tendsto_add_const_min l μ).pow (j + 1)) hne)
    rw [if_neg (fun h => hμl h.1)]
    simpa using h1.mul h2

/-- The termwise Mellin sum, multiplied by `(s+l)^m`, tends to `(m-1)!` times the top
coefficient. -/
theorem list_tendsto (l : ℝ) (m : ℕ) (hm : 0 < m) :
    ∀ c : PowLogRep, (∀ t ∈ c, l ≤ t.1 ∧ (t.1 = l → t.2.1 < m)) →
      Tendsto (fun s : ℝ => (s + l) ^ m *
          (c.map fun t => t.2.2 * ((t.2.1.factorial : ℝ) / (s + t.1) ^ (t.2.1 + 1))).sum)
        (𝓝[>] (-l)) (𝓝 (((m - 1).factorial : ℝ) * PowLogRep.coeffAt c l (m - 1))) := by
  intro c
  induction c with
  | nil =>
    intro _
    simp only [List.map_nil, List.sum_nil, mul_zero, PowLogRep.coeffAt_nil]
    exact tendsto_const_nhds
  | cons t c ih =>
    intro hc
    have ht := hc t (List.mem_cons_self ..)
    have hrest := ih fun u hu => hc u (List.mem_cons_of_mem t hu)
    have hterm := term_tendsto l m hm t ht.1 ht.2
    have hfun : (fun s : ℝ => (s + l) ^ m *
        ((t :: c).map fun u => u.2.2 * ((u.2.1.factorial : ℝ) / (s + u.1) ^ (u.2.1 + 1))).sum) =
        fun s => (s + l) ^ m * (t.2.2 * ((t.2.1.factorial : ℝ) / (s + t.1) ^ (t.2.1 + 1))) +
          (s + l) ^ m *
            (c.map fun u => u.2.2 * ((u.2.1.factorial : ℝ) / (s + u.1) ^ (u.2.1 + 1))).sum := by
      funext s
      simp only [List.map_cons, List.sum_cons]
      ring
    rw [hfun, PowLogRep.coeffAt_cons,
      show ((m - 1).factorial : ℝ) * ((if t.1 = l ∧ t.2.1 = m - 1 then t.2.2 else 0) +
        PowLogRep.coeffAt c l (m - 1)) =
        (if t.1 = l ∧ t.2.1 = m - 1 then t.2.2 * ((m - 1).factorial : ℝ) else 0) +
          ((m - 1).factorial : ℝ) * PowLogRep.coeffAt c l (m - 1) by split_ifs <;> ring]
    exact hterm.add hrest

/-- The product Mellin transform, multiplied by `(s+l)^m`, tends to
`∏_{wᵢ+1 ≠ l} 1/(wᵢ+1-l)`. -/
theorem product_tendsto {d : ℕ} (w : Fin d → ℝ) (l : ℝ) (hl : ∀ i, l ≤ w i + 1) :
    Tendsto (fun s : ℝ => (s + l) ^ expMult w l * ∏ i, 1 / (w i + s + 1)) (𝓝[>] (-l))
      (𝓝 (∏ i, if w i + 1 = l then (1 : ℝ) else 1 / (w i + 1 - l))) := by
  have hev : ∀ᶠ s in 𝓝[>] (-l),
      (∏ i, if w i + 1 = l then (1 : ℝ) else 1 / (w i + s + 1)) =
        (s + l) ^ expMult w l * ∏ i, 1 / (w i + s + 1) := by
    filter_upwards [self_mem_nhdsWithin] with s hs
    have hs0 : s + l ≠ 0 := by
      have : -l < s := hs
      linarith
    have hpow : (s + l) ^ expMult w l = ∏ i, (if w i + 1 = l then s + l else 1) := by
      simp only [expMult]
      rw [← Finset.prod_filter (fun i => w i + 1 = l) (fun _ => s + l), Finset.prod_const]
    rw [hpow, ← Finset.prod_mul_distrib]
    refine Finset.prod_congr rfl fun i _ => ?_
    by_cases hi : w i + 1 = l
    · rw [if_pos hi, if_pos hi, show w i + s + 1 = s + l by linarith]
      field_simp
    · rw [if_neg hi, if_neg hi, one_mul]
  refine (tendsto_finsetProd _ fun i _ => ?_).congr' hev
  by_cases hi : w i + 1 = l
  · simp only [if_pos hi]
    exact tendsto_const_nhds
  · simp only [if_neg hi]
    have hne : w i + -l + 1 ≠ 0 := by
      have := lt_of_le_of_ne (hl i) (Ne.symm hi)
      linarith
    have hden : Tendsto (fun s : ℝ => w i + s + 1) (𝓝[>] (-l)) (𝓝 (w i + -l + 1)) :=
      (((continuous_const.add continuous_id).add continuous_const).tendsto (-l)).mono_left
        nhdsWithin_le_nhds
    have := (tendsto_const_nhds (x := (1 : ℝ))).div hden hne
    rwa [show w i + -l + 1 = w i + 1 - l by ring] at this

/-! ### The leading coefficient -/

/-- **Top coefficient of the state density**:
`coeffAt v l (m-1) = (1/(m-1)!) ∏_{wᵢ+1 ≠ l} 1/(wᵢ+1-l)` where `l = min (wᵢ+1)` and `m` is its
multiplicity. -/
theorem stateDensityRep_leadCoeff (n : ℕ) (w : Fin (n + 1) → ℝ) (l : ℝ) (hl : ∀ i, l ≤ w i + 1)
    (hatt : ∃ i, w i + 1 = l) :
    PowLogRep.coeffAt (stateDensityRep n w) l (expMult w l - 1) =
      (1 / ((expMult w l - 1).factorial : ℝ)) *
        ∏ i, if w i + 1 = l then (1 : ℝ) else 1 / (w i + 1 - l) := by
  have hm : 0 < expMult w l := by
    obtain ⟨i, hi⟩ := hatt
    simp only [expMult]
    exact Finset.card_pos.2 ⟨i, by simp [hi]⟩
  have hc : ∀ t ∈ stateDensityRep n w, l ≤ t.1 ∧ (t.1 = l → t.2.1 < expMult w l) := by
    intro t ht
    obtain ⟨i, hi⟩ := stateDensityRep_exponent_mem n w t ht
    refine ⟨by rw [hi]; exact hl i, fun htl => ?_⟩
    have := stateDensityRep_degree_lt n w t ht
    rwa [htl] at this
  have hA := product_tendsto w l hl
  have hB := list_tendsto l (expMult w l) hm (stateDensityRep n w) hc
  have heq : (fun s : ℝ => (s + l) ^ expMult w l * ∏ i, 1 / (w i + s + 1)) =ᶠ[𝓝[>] (-l)]
      fun s => (s + l) ^ expMult w l * ((stateDensityRep n w).map fun t =>
        t.2.2 * ((t.2.1.factorial : ℝ) / (s + t.1) ^ (t.2.1 + 1))).sum := by
    filter_upwards [self_mem_nhdsWithin] with s hs
    have hs' : -l < s := hs
    congr 1
    rw [← mellin_stateDensity n w s (fun i => by linarith [hl i]),
      mellin_eval _ s (fun t ht => ?_)]
    obtain ⟨i, hi⟩ := stateDensityRep_exponent_mem n w t ht
    rw [hi]
    linarith [hl i]
  have hfac : (((expMult w l - 1).factorial : ℕ) : ℝ) ≠ 0 := by positivity
  have h := tendsto_nhds_unique_of_eventuallyEq hA hB heq
  rw [h]
  field_simp

/-- **Monomial normalisation.** With `wᵢ = (hᵢ+1)/(2kᵢ) - 1` and the Jacobian `∏ 1/(2kᵢ)`, the top
coefficient of the monomial state density is `a_{-m}/(m-1)!`, where `a_{-m} = mellinCoeff h k l 1`
is the paper's leading Laurent coefficient (Headline XXI). -/
theorem monomial_leadCoeff (n : ℕ) (h k : Fin (n + 1) → ℕ) (hk : ∀ i, 0 < k i) (l : ℝ)
    (hmin : ∀ i, l ≤ ratioExp h k i) (hatt : ∃ i, ratioExp h k i = l) :
    (∏ i, 1 / (2 * (k i : ℝ))) *
        PowLogRep.coeffAt (stateDensityRep n fun i => ratioExp h k i - 1) l
          (multCount (ratioExp h k) l - 1) =
      mellinCoeff h k l (fun _ => 1) / ((multCount (ratioExp h k) l - 1).factorial : ℝ) := by
  have hE : expMult (fun i => ratioExp h k i - 1) l = multCount (ratioExp h k) l := by
    simp only [expMult, multCount_eq_card, sub_add_cancel]
  have hlead := stateDensityRep_leadCoeff n (fun i => ratioExp h k i - 1) l
    (fun i => by simpa using hmin i) (by obtain ⟨i, hi⟩ := hatt; exact ⟨i, by simpa using hi⟩)
  rw [hE] at hlead
  rw [hlead, mellinCoeff_one (n + 1) h k hk l hmin]
  simp only [sub_add_cancel]
  have hprod : (∏ i, 1 / (2 * (k i : ℝ))) *
      ∏ i, (if ratioExp h k i = l then (1 : ℝ) else 1 / (ratioExp h k i - l)) =
      ∏ i, (if ratioExp h k i = l then 1 / (2 * (k i : ℝ))
        else 1 / ((h i : ℝ) + 1 - 2 * (k i : ℝ) * l)) := by
    rw [← Finset.prod_mul_distrib]
    refine Finset.prod_congr rfl fun i _ => ?_
    by_cases hi : ratioExp h k i = l
    · rw [if_pos hi, if_pos hi, mul_one]
    · rw [if_neg hi, if_neg hi]
      unfold ratioExp at hi ⊢
      have hk' : (0 : ℝ) < k i := by exact_mod_cast hk i
      have hne : (h i : ℝ) + 1 - 2 * (k i : ℝ) * l ≠ 0 := by
        intro h0
        apply hi
        field_simp
        linarith
      field_simp
  rw [div_eq_mul_one_div, ← hprod]
  ring

end Laplace.Grammar
