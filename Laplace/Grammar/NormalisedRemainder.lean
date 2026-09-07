/-
Copyright (c) 2026 Timaeus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Laplace.Grammar.CoeffDistribution

/-!
# Normalised remainders of a finite log-polynomial expansion (grammar §4.3, Astra #11 rank 4)

Deterministic half of the ordered-remainder statement of thm:strataempiricalexpansion. Given a
finite expansion `Z(N) = ∑_{γ∈P} N^{-γ}(A_γ log N + B_γ) + R(N)` with `|R(N)| ≤ K N^{-E}(1+log N)`
(`E` beyond every exponent of `P`), bounded coefficients `|A_γ|, |B_γ| ≤ K_c`, and a gap `δ` above
the exponent `α ∈ P`, the two normalised remainders satisfy, for `N ≥ e`,

* A-slot: `|(Z(N) − L_{<α}(N)) / (N^{-α} log N) − A_α| ≤ errA(N)`,
* B-slot: `|(Z(N) − L_{<α}(N) − N^{-α} A_α log N) / N^{-α} − B_α| ≤ errB(N)`,

where `L_{<α}` is the part of the expansion below `α` and `errA`, `errB` are explicit rates tending
to `0` (`tendsto_errA`, `tendsto_errB`). Note the B-slot subtracts the CURRENT coefficient `A_α`,
as required when the coefficients are random. Zero `sorry`/`axiom`.
-/

open Real Filter Topology Asymptotics

namespace Laplace.Grammar

/-- The part of the expansion strictly below the exponent `α`. -/
noncomputable def lowerPart (P : Finset ℝ) (A B : ℝ → ℝ) (α N : ℝ) : ℝ :=
  ∑ γ ∈ P.filter (· < α), N ^ (-γ) * (A γ * Real.log N + B γ)

/-- The part of the expansion strictly above the exponent `α`. -/
noncomputable def upperPart (P : Finset ℝ) (A B : ℝ → ℝ) (α N : ℝ) : ℝ :=
  ∑ γ ∈ P.filter (α < ·), N ^ (-γ) * (A γ * Real.log N + B γ)

theorem sum_split (P : Finset ℝ) (A B : ℝ → ℝ) (α N : ℝ) (hα : α ∈ P) :
    ∑ γ ∈ P, N ^ (-γ) * (A γ * Real.log N + B γ)
      = lowerPart P A B α N + N ^ (-α) * (A α * Real.log N + B α) + upperPart P A B α N := by
  rw [← Finset.add_sum_erase P _ hα,
    ← Finset.sum_filter_add_sum_filter_not (P.erase α) (· < α)]
  have h1 : (P.erase α).filter (· < α) = P.filter (· < α) := by
    ext γ
    simp only [Finset.mem_filter, Finset.mem_erase]
    constructor
    · rintro ⟨⟨_, h⟩, hlt⟩; exact ⟨h, hlt⟩
    · rintro ⟨h, hlt⟩; exact ⟨⟨hlt.ne, h⟩, hlt⟩
  have h2 : (P.erase α).filter (fun γ => ¬ γ < α) = P.filter (α < ·) := by
    ext γ
    simp only [Finset.mem_filter, Finset.mem_erase]
    constructor
    · rintro ⟨⟨hne, h⟩, hnlt⟩; exact ⟨h, lt_of_le_of_ne (not_lt.1 hnlt) (Ne.symm hne)⟩
    · rintro ⟨h, hlt⟩; exact ⟨⟨hlt.ne', h⟩, not_lt.2 hlt.le⟩
  rw [h1, h2]
  unfold lowerPart upperPart
  ring

/-- The upper part is `O(N^{-(α+δ)} (1 + log N))` under a gap `δ` and coefficient bounds. -/
theorem abs_upperPart_le (P : Finset ℝ) (A B : ℝ → ℝ) (α N δ Kc : ℝ) (hN : 1 ≤ N) (hKc : 0 ≤ Kc)
    (hgap : ∀ γ ∈ P, α < γ → α + δ ≤ γ) (hAB : ∀ γ ∈ P, |A γ| ≤ Kc ∧ |B γ| ≤ Kc) :
    |upperPart P A B α N| ≤ (P.card : ℝ) * (N ^ (-(α + δ)) * (Kc * (1 + Real.log N))) := by
  have hN0 : 0 ≤ N := by linarith
  have hlog : 0 ≤ Real.log N := Real.log_nonneg hN
  unfold upperPart
  refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
  have hterm : ∀ γ ∈ P.filter (α < ·),
      |N ^ (-γ) * (A γ * Real.log N + B γ)| ≤ N ^ (-(α + δ)) * (Kc * (1 + Real.log N)) := by
    intro γ hγ
    obtain ⟨hγP, hαγ⟩ := Finset.mem_filter.1 hγ
    have hge := hgap γ hγP hαγ
    have hpow : N ^ (-γ) ≤ N ^ (-(α + δ)) :=
      Real.rpow_le_rpow_of_exponent_le hN (by linarith)
    rw [abs_mul, abs_of_nonneg (Real.rpow_nonneg hN0 _)]
    refine mul_le_mul hpow ?_ (abs_nonneg _) (Real.rpow_nonneg hN0 _)
    calc |A γ * Real.log N + B γ| ≤ |A γ| * Real.log N + |B γ| := by
          refine (abs_add_le _ _).trans ?_
          rw [abs_mul, abs_of_nonneg hlog]
      _ ≤ Kc * Real.log N + Kc :=
          add_le_add (mul_le_mul_of_nonneg_right (hAB γ hγP).1 hlog) (hAB γ hγP).2
      _ = Kc * (1 + Real.log N) := by ring
  refine (Finset.sum_le_card_nsmul _ _ _ hterm).trans ?_
  rw [nsmul_eq_mul]
  exact mul_le_mul_of_nonneg_right (by exact_mod_cast Finset.card_filter_le _ _) (by positivity)

/-- The A-slot error rate. -/
noncomputable def errA (K Kc E α δ : ℝ) (P : Finset ℝ) (N : ℝ) : ℝ :=
  2 * (K * N ^ (α - E) + (P.card : ℝ) * Kc * N ^ (-δ)) + Kc / Real.log N

/-- The B-slot error rate. -/
noncomputable def errB (K Kc E α δ : ℝ) (P : Finset ℝ) (N : ℝ) : ℝ :=
  (K * N ^ (α - E) + (P.card : ℝ) * Kc * N ^ (-δ)) * (1 + Real.log N)

/-- **A-slot normalised remainder.** -/
theorem normalised_A_le (P : Finset ℝ) (A B Z : ℝ → ℝ) (K Kc E α δ : ℝ) (hK : 0 ≤ K)
    (hKc : 0 ≤ Kc) (hα : α ∈ P) (hgap : ∀ γ ∈ P, α < γ → α + δ ≤ γ)
    (hZ : ∀ N, 1 ≤ N → |Z N - ∑ γ ∈ P, N ^ (-γ) * (A γ * Real.log N + B γ)|
      ≤ K * (N ^ (-E) * (1 + Real.log N)))
    (hAB : ∀ γ ∈ P, |A γ| ≤ Kc ∧ |B γ| ≤ Kc) (N : ℝ) (hN : Real.exp 1 ≤ N) :
    |(Z N - lowerPart P A B α N) / (N ^ (-α) * Real.log N) - A α| ≤ errA K Kc E α δ P N := by
  have hN1 : 1 ≤ N := le_trans (Real.one_le_exp zero_le_one) hN
  have hN0 : 0 < N := by linarith
  have hlog1 : 1 ≤ Real.log N := (Real.le_log_iff_exp_le hN0).2 hN
  have hlogpos : 0 < Real.log N := by linarith
  have hpα : 0 < N ^ (-α) := Real.rpow_pos_of_pos hN0 _
  have hD : 0 < N ^ (-α) * Real.log N := mul_pos hpα hlogpos
  set R := Z N - ∑ γ ∈ P, N ^ (-γ) * (A γ * Real.log N + B γ) with hR
  set U := upperPart P A B α N with hU
  have hRb := hZ N hN1
  have hUb := abs_upperPart_le P A B α N δ Kc hN1 hKc hgap hAB
  have hsplit : Z N - lowerPart P A B α N = R + N ^ (-α) * (A α * Real.log N + B α) + U := by
    rw [hR, sum_split P A B α N hα]; ring
  have hid : (Z N - lowerPart P A B α N) / (N ^ (-α) * Real.log N) - A α
      = (R + U) / (N ^ (-α) * Real.log N) + B α / Real.log N := by
    rw [hsplit]
    field_simp
    ring
  have hE1 : N ^ (α - E) * N ^ (-α) = N ^ (-E) := by
    rw [← Real.rpow_add hN0]; congr 1; ring
  have hE2 : N ^ (-δ) * N ^ (-α) = N ^ (-(α + δ)) := by
    rw [← Real.rpow_add hN0]; congr 1; ring
  have hmain : |R + U| / (N ^ (-α) * Real.log N)
      ≤ 2 * (K * N ^ (α - E) + (P.card : ℝ) * Kc * N ^ (-δ)) := by
    rw [div_le_iff₀ hD]
    calc |R + U| ≤ |R| + |U| := abs_add_le _ _
      _ ≤ K * (N ^ (-E) * (1 + Real.log N))
          + (P.card : ℝ) * (N ^ (-(α + δ)) * (Kc * (1 + Real.log N))) := add_le_add hRb hUb
      _ = (K * N ^ (-E) + (P.card : ℝ) * Kc * N ^ (-(α + δ))) * (1 + Real.log N) := by ring
      _ ≤ (K * N ^ (-E) + (P.card : ℝ) * Kc * N ^ (-(α + δ))) * (2 * Real.log N) := by
          refine mul_le_mul_of_nonneg_left (by linarith) ?_
          have := Real.rpow_nonneg hN0.le (-E)
          have := Real.rpow_nonneg hN0.le (-(α + δ))
          positivity
      _ = 2 * (K * N ^ (α - E) + (P.card : ℝ) * Kc * N ^ (-δ)) * (N ^ (-α) * Real.log N) := by
          rw [← hE1, ← hE2]; ring
  rw [hid]
  unfold errA
  calc |(R + U) / (N ^ (-α) * Real.log N) + B α / Real.log N|
      ≤ |R + U| / (N ^ (-α) * Real.log N) + |B α| / Real.log N := by
        refine (abs_add_le _ _).trans (le_of_eq ?_)
        rw [abs_div, abs_div, abs_of_pos hD, abs_of_pos hlogpos]
    _ ≤ 2 * (K * N ^ (α - E) + (P.card : ℝ) * Kc * N ^ (-δ)) + Kc / Real.log N :=
        add_le_add hmain (div_le_div_of_nonneg_right (hAB α hα).2 hlogpos.le)

/-- **B-slot normalised remainder** (subtracting the current `A_α`). -/
theorem normalised_B_le (P : Finset ℝ) (A B Z : ℝ → ℝ) (K Kc E α δ : ℝ) (_hK : 0 ≤ K)
    (hKc : 0 ≤ Kc) (hα : α ∈ P) (hgap : ∀ γ ∈ P, α < γ → α + δ ≤ γ)
    (hZ : ∀ N, 1 ≤ N → |Z N - ∑ γ ∈ P, N ^ (-γ) * (A γ * Real.log N + B γ)|
      ≤ K * (N ^ (-E) * (1 + Real.log N)))
    (hAB : ∀ γ ∈ P, |A γ| ≤ Kc ∧ |B γ| ≤ Kc) (N : ℝ) (hN : Real.exp 1 ≤ N) :
    |(Z N - lowerPart P A B α N - N ^ (-α) * (A α * Real.log N)) / N ^ (-α) - B α|
      ≤ errB K Kc E α δ P N := by
  have hN1 : 1 ≤ N := le_trans (Real.one_le_exp zero_le_one) hN
  have hN0 : 0 < N := by linarith
  have hlog : 0 ≤ Real.log N := Real.log_nonneg hN1
  have hpα : 0 < N ^ (-α) := Real.rpow_pos_of_pos hN0 _
  set R := Z N - ∑ γ ∈ P, N ^ (-γ) * (A γ * Real.log N + B γ) with hR
  set U := upperPart P A B α N with hU
  have hRb := hZ N hN1
  have hUb := abs_upperPart_le P A B α N δ Kc hN1 hKc hgap hAB
  have hsplit : Z N - lowerPart P A B α N = R + N ^ (-α) * (A α * Real.log N + B α) + U := by
    rw [hR, sum_split P A B α N hα]; ring
  have hid : (Z N - lowerPart P A B α N - N ^ (-α) * (A α * Real.log N)) / N ^ (-α) - B α
      = (R + U) / N ^ (-α) := by
    rw [hsplit]
    field_simp
    ring
  have hE1 : N ^ (α - E) * N ^ (-α) = N ^ (-E) := by
    rw [← Real.rpow_add hN0]; congr 1; ring
  have hE2 : N ^ (-δ) * N ^ (-α) = N ^ (-(α + δ)) := by
    rw [← Real.rpow_add hN0]; congr 1; ring
  rw [hid, abs_div, abs_of_pos hpα, div_le_iff₀ hpα]
  unfold errB
  calc |R + U| ≤ |R| + |U| := abs_add_le _ _
    _ ≤ K * (N ^ (-E) * (1 + Real.log N))
        + (P.card : ℝ) * (N ^ (-(α + δ)) * (Kc * (1 + Real.log N))) := add_le_add hRb hUb
    _ = (K * N ^ (α - E) + (P.card : ℝ) * Kc * N ^ (-δ)) * (1 + Real.log N) * N ^ (-α) := by
        rw [← hE1, ← hE2]; ring

/-- `N^{-a}(1 + log N) → 0` for `a > 0`. -/
theorem tendsto_rpow_neg_mul_one_add_log (a : ℝ) (ha : 0 < a) :
    Tendsto (fun N : ℝ => N ^ (-a) * (1 + Real.log N)) atTop (𝓝 0) := by
  have h1 : Tendsto (fun N : ℝ => N ^ (-a)) atTop (𝓝 0) := tendsto_rpow_neg_atTop ha
  have h2 : Tendsto (fun N : ℝ => Real.log N / N ^ a) atTop (𝓝 0) :=
    (isLittleO_log_rpow_atTop ha).tendsto_div_nhds_zero
  have h : (fun N : ℝ => N ^ (-a) * (1 + Real.log N))
      =ᶠ[atTop] fun N => N ^ (-a) + Real.log N / N ^ a := by
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with N hN
    rw [Real.rpow_neg hN.le, div_eq_mul_inv]; ring
  rw [tendsto_congr' h]
  simpa using h1.add h2

theorem tendsto_errA (K Kc E α δ : ℝ) (P : Finset ℝ) (hαE : α < E) (hδ : 0 < δ) :
    Tendsto (errA K Kc E α δ P) atTop (𝓝 0) := by
  unfold errA
  have h1 : Tendsto (fun N : ℝ => N ^ (α - E)) atTop (𝓝 0) := by
    refine (tendsto_rpow_neg_atTop (sub_pos.2 hαE)).congr fun N => ?_
    congr 1; ring
  have h2 : Tendsto (fun N : ℝ => N ^ (-δ)) atTop (𝓝 0) := tendsto_rpow_neg_atTop hδ
  have h3 : Tendsto (fun N : ℝ => Kc / Real.log N) atTop (𝓝 0) := by
    have := Real.tendsto_log_atTop.inv_tendsto_atTop.const_mul Kc
    simpa [div_eq_mul_inv] using this
  have := (((h1.const_mul K).add (h2.const_mul ((P.card : ℝ) * Kc))).const_mul 2).add h3
  simpa using this

theorem tendsto_errB (K Kc E α δ : ℝ) (P : Finset ℝ) (hαE : α < E) (hδ : 0 < δ) :
    Tendsto (errB K Kc E α δ P) atTop (𝓝 0) := by
  unfold errB
  have h1 : Tendsto (fun N : ℝ => N ^ (α - E) * (1 + Real.log N)) atTop (𝓝 0) := by
    refine (tendsto_rpow_neg_mul_one_add_log (E - α) (sub_pos.2 hαE)).congr fun N => ?_
    congr 2; ring
  have h2 := tendsto_rpow_neg_mul_one_add_log δ hδ
  have := (h1.const_mul K).add (h2.const_mul ((P.card : ℝ) * Kc))
  refine (this.congr fun N => ?_).trans (by simp)
  ring

end Laplace.Grammar
