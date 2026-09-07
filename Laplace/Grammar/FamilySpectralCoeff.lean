/-
Copyright (c) 2026 Timaeus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Laplace.Grammar.CoeffFamily

/-!
# Spectral coefficients of coefficient-family data (Stage 4f)

Unit 245 (Taylor-tree programme, Stage 4; Astra #28 §2.4 (II)). For absolutely summable coefficient
families `cξ, cη`, the spectral coefficients of the box truncations
`A_{μ,j}(truncList cξ m, truncList cη m)` form a Cauchy sequence: by the stability gate (unit 242)
consecutive differences are bounded by explicit constants times the tail masses of `cξ, cη`, which
tend to `0`. The **family spectral coefficient** `A_{μ,j}(cξ, cη)` is their limit
(`familySpectralCoeff`, `tendsto_truncCoeff`), it vanishes off the candidate set `Λ(h,k)`
(`familySpectralCoeff_eq_zero_of_not_candidate`), and the spectral sums below any cutoff converge
(`tendsto_spectralSum_truncList`). No `sorry` and no additional `axiom` declarations.
-/

open MeasureTheory Set Real Filter Topology
open scoped List

namespace Laplace.Grammar

open MonoRep CoeffFamily

namespace CoeffFamily

variable {d : ℕ}

theorem boxSet_indicator_le {c : CoeffFamily d} {m m' : ℕ} (h : m ≤ m') (γ : Fin d → ℕ) :
    (if γ ∈ boxSet d m' then 0 else |c γ|) ≤ if γ ∈ boxSet d m then 0 else |c γ| := by
  by_cases hm : γ ∈ boxSet d m
  · rw [if_pos hm, if_pos (boxSet_mono h hm)]
  · rw [if_neg hm]; exact tail_term_le c m' γ

/-- The tail mass is antitone in the level. -/
theorem tailMass_anti {c : CoeffFamily d} (hc : AbsSummable c) {m m' : ℕ} (h : m ≤ m') :
    tailMass c m' ≤ tailMass c m :=
  Summable.tsum_le_tsum (boxSet_indicator_le h) (summable_tail_term hc m') (summable_tail_term hc m)

end CoeffFamily

/-- The spectral coefficient of the level-`m` truncations. -/
noncomputable def truncCoeff (n : ℕ) (h k : Fin (n + 1) → ℕ) (β : ℝ) (cξ cη : CoeffFamily (n + 1))
    (μ : ℝ) (j : ℕ) (m : ℕ) : ℝ :=
  spectralCoeff n h k β (truncList cξ m) (truncList cη m) μ j

/-- The stability constants of the truncation sequence. -/
noncomputable def truncStabConst₁ (n : ℕ) (k : Fin (n + 1) → ℕ) (β : ℝ)
    (cξ cη : CoeffFamily (n + 1))
    (μ : ℝ) : ℝ :=
  stabilityPrefactor n k * (mass cη * β * phaseLogMoment β (cξ 0 + mass cξ) (μ + 1 / 2) n 0)

noncomputable def truncStabConst₂ (n : ℕ) (k : Fin (n + 1) → ℕ) (β : ℝ) (cξ : CoeffFamily (n + 1))
    (μ : ℝ) : ℝ :=
  stabilityPrefactor n k * phaseLogMoment β (cξ 0 + mass cξ) μ n 0

theorem stabilityPrefactor_nonneg (n : ℕ) (k : Fin (n + 1) → ℕ) : 0 ≤ stabilityPrefactor n k := by
  unfold stabilityPrefactor
  exact mul_nonneg (Finset.prod_nonneg fun i _ => by positivity) (by positivity)

/-- **Consecutive truncation coefficients are close**: for `m ≤ m'` and `μ > 0`,
`|A(m') − A(m)| ≤ C₁ tailMass cξ m + C₂ tailMass cη m`. -/
theorem abs_truncCoeff_sub_le (n : ℕ) (h k : Fin (n + 1) → ℕ) (hk : ∀ i, 0 < k i) (β : ℝ)
    (hβ : 0 < β) {cξ cη : CoeffFamily (n + 1)} (hξ : AbsSummable cξ) (hη : AbsSummable cη) {μ : ℝ}
    (hμ : 0 < μ) (j : ℕ) {m m' : ℕ} (hmm : m ≤ m') :
    |truncCoeff n h k β cξ cη μ j m' - truncCoeff n h k β cξ cη μ j m| ≤
      truncStabConst₁ n k β cξ cη μ * tailMass cξ m +
        truncStabConst₂ n k β cξ μ * tailMass cη m := by
  unfold truncCoeff
  have hB : l1 (fluct (truncList cξ m)) + l1 (fluct (restList cξ m m')) ≤ mass cξ := by
    rw [← l1_append, ← l1_perm (fluct_truncList_perm cξ hmm)]
    exact (l1_fluct_le _).trans (l1_truncList_le_mass hξ m')
  have hst := abs_spectralCoeff_sub_le n h k hk β hβ hμ j (truncList cξ m) (truncList cξ m')
    (truncList cη m) (truncList cη m') (restList cη m m') (fluct (restList cξ m m'))
    (truncList_perm cη hmm) (fluct_truncList_perm cξ hmm)
    (by rw [eval_truncList_zero, eval_truncList_zero]) (l1_truncList_le_mass hη m) hB
  rw [eval_truncList_zero] at hst
  refine hst.trans ?_
  have hP := stabilityPrefactor_nonneg n k
  have h1 : l1 (fluct (restList cξ m m')) ≤ tailMass cξ m :=
    (l1_fluct_le _).trans (l1_restList_le_tailMass hξ m m')
  have h2 : l1 (restList cη m m') ≤ tailMass cη m := l1_restList_le_tailMass hη m m'
  have hM1 := phaseLogMoment_nonneg β (cξ 0 + mass cξ) (μ + 1 / 2) n 0
  have hM2 := phaseLogMoment_nonneg β (cξ 0 + mass cξ) μ n 0
  have hE := mass_nonneg cη
  unfold truncStabConst₁ truncStabConst₂
  have := mul_le_mul_of_nonneg_left h1 (mul_nonneg (mul_nonneg hE hβ.le) hM1)
  have := mul_le_mul_of_nonneg_left h2 hM2
  nlinarith

/-- The truncation coefficients form a Cauchy sequence. -/
theorem cauchySeq_truncCoeff (n : ℕ) (h k : Fin (n + 1) → ℕ) (hk : ∀ i, 0 < k i) (β : ℝ)
    (hβ : 0 < β) {cξ cη : CoeffFamily (n + 1)} (hξ : AbsSummable cξ) (hη : AbsSummable cη) (μ : ℝ)
    (j : ℕ) : CauchySeq (truncCoeff n h k β cξ cη μ j) := by
  rcases lt_or_ge 0 μ with hμ | hμ
  · refine cauchySeq_of_le_tendsto_0 (fun m => truncStabConst₁ n k β cξ cη μ * tailMass cξ m +
      truncStabConst₂ n k β cξ μ * tailMass cη m) (fun a b N ha hb => ?_) ?_
    · have hC1 : 0 ≤ truncStabConst₁ n k β cξ cη μ := by
        unfold truncStabConst₁
        exact mul_nonneg (stabilityPrefactor_nonneg n k)
          (mul_nonneg (mul_nonneg (mass_nonneg _) hβ.le) (phaseLogMoment_nonneg _ _ _ _ _))
      have hC2 : 0 ≤ truncStabConst₂ n k β cξ μ := by
        unfold truncStabConst₂
        exact mul_nonneg (stabilityPrefactor_nonneg n k) (phaseLogMoment_nonneg _ _ _ _ _)
      have hmono : ∀ {a b : ℕ}, a ≤ b → N ≤ a →
          dist (truncCoeff n h k β cξ cη μ j a) (truncCoeff n h k β cξ cη μ j b) ≤
          truncStabConst₁ n k β cξ cη μ * tailMass cξ N +
            truncStabConst₂ n k β cξ μ * tailMass cη N := by
        intro a b hab hNa
        rw [Real.dist_eq, abs_sub_comm]
        refine (abs_truncCoeff_sub_le n h k hk β hβ hξ hη hμ j hab).trans ?_
        exact add_le_add (mul_le_mul_of_nonneg_left (tailMass_anti hξ hNa) hC1)
          (mul_le_mul_of_nonneg_left (tailMass_anti hη hNa) hC2)
      rcases le_total a b with hab | hab
      · exact hmono hab ha
      · rw [dist_comm]; exact hmono hab hb
    · have := ((tailMass_tendsto_zero hξ).const_mul (truncStabConst₁ n k β cξ cη μ)).add
        ((tailMass_tendsto_zero hη).const_mul (truncStabConst₂ n k β cξ μ))
      simpa using this
  · -- `μ ≤ 0`: every truncation coefficient vanishes
    have hz : ∀ m, truncCoeff n h k β cξ cη μ j m = 0 := fun m =>
      spectralCoeff_eq_zero_of_nonpos n h k hk β _ _ hμ j
    refine cauchySeq_of_le_tendsto_0 (fun _ => (0 : ℝ)) (fun a b _ _ _ => ?_) tendsto_const_nhds
    rw [hz a, hz b, dist_self]

/-- **The family spectral coefficient** `A_{μ,j}(cξ, cη)`: the limit of the truncation
coefficients. -/
noncomputable def familySpectralCoeff (n : ℕ) (h k : Fin (n + 1) → ℕ) (β : ℝ)
    (cξ cη : CoeffFamily (n + 1)) (μ : ℝ) (j : ℕ) : ℝ :=
  limUnder atTop (truncCoeff n h k β cξ cη μ j)

/-- **Convergence of the truncation coefficients** to the family coefficient. -/
theorem tendsto_truncCoeff (n : ℕ) (h k : Fin (n + 1) → ℕ) (hk : ∀ i, 0 < k i) (β : ℝ) (hβ : 0 < β)
    {cξ cη : CoeffFamily (n + 1)} (hξ : AbsSummable cξ) (hη : AbsSummable cη) (μ : ℝ) (j : ℕ) :
    Tendsto (truncCoeff n h k β cξ cη μ j) atTop (𝓝 (familySpectralCoeff n h k β cξ cη μ j)) :=
  tendsto_nhds_limUnder
    (cauchySeq_tendsto_of_complete (cauchySeq_truncCoeff n h k hk β hβ hξ hη μ j))

/-- The family coefficients vanish off the paper's candidate set `Λ(h,k)`. -/
theorem familySpectralCoeff_eq_zero_of_not_candidate (n : ℕ) (h k : Fin (n + 1) → ℕ)
    (hk : ∀ i, 0 < k i) (β : ℝ) (hβ : 0 < β) {cξ cη : CoeffFamily (n + 1)} (hξ : AbsSummable cξ)
    (hη : AbsSummable cη) {μ : ℝ} (hμ : ¬ candidateExp h k μ) (j : ℕ) :
    familySpectralCoeff n h k β cξ cη μ j = 0 := by
  have h1 := tendsto_truncCoeff n h k hk β hβ hξ hη μ j
  have h2 : Tendsto (truncCoeff n h k β cξ cη μ j) atTop (𝓝 0) := by
    have : truncCoeff n h k β cξ cη μ j = fun _ => 0 := funext fun m =>
      spectralCoeff_eq_zero_of_not_candidate n h k β _ _ hμ j
    rw [this]; exact tendsto_const_nhds
  exact tendsto_nhds_unique h1 h2

/-- The spectral sum of coefficient-family data below the cutoff `L`. -/
noncomputable def familySpectralSum (n : ℕ) (h k : Fin (n + 1) → ℕ) (β L : ℝ)
    (cξ cη : CoeffFamily (n + 1)) (N : ℝ) : ℝ :=
  ∑ μ ∈ latticeBelow (latticeQ k) L, N ^ (-μ) *
    ∑ j ∈ Finset.range (n + 1), familySpectralCoeff n h k β cξ cη μ j * (Real.log N) ^ j

/-- **The spectral sums of the truncations converge** to the family spectral sum. -/
theorem tendsto_spectralSum_truncList (n : ℕ) (h k : Fin (n + 1) → ℕ) (hk : ∀ i, 0 < k i) (β : ℝ)
    (hβ : 0 < β) (L : ℝ) {cξ cη : CoeffFamily (n + 1)} (hξ : AbsSummable cξ) (hη : AbsSummable cη)
    (N : ℝ) :
    Tendsto (fun m => spectralSum n h k β L (truncList cξ m) (truncList cη m) N) atTop
      (𝓝 (familySpectralSum n h k β L cξ cη N)) := by
  unfold spectralSum familySpectralSum
  refine tendsto_finsetSum _ fun μ _ => tendsto_const_nhds.mul (tendsto_finsetSum _ fun j _ => ?_)
  exact (tendsto_truncCoeff n h k hk β hβ hξ hη μ j).mul tendsto_const_nhds

end Laplace.Grammar
