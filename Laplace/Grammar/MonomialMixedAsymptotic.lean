/-
Copyright (c) 2026 Daniel Murfet. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniel Murfet
-/
import Laplace.Grammar.WeightedMixedAsymptotic

/-!
# The mixed-ratio monomial asymptotic in general dimension

Assembly of the mixed-ratio general-`d` monomial programme (Astra #15). For exponents
`h k : Fin (m+1) → ℕ` with `kᵢ > 0`, Mellin ratios `ℓᵢ = (hᵢ+1)/(2kᵢ)`, minimum `λ = min ℓᵢ` attained
`|J|` times, the monomial box integral

  `M(N) = ∫_{(0,1]^{m+1}} ∏ xᵢ^{hᵢ} e^{-βN ∏ xᵢ^{2kᵢ}} dx`

satisfies

  `M(N) ~ Γ(λ) β^{-λ} / (|J|-1)! · ∏_{i∈J} 1/(2kᵢ) · ∏_{i∉J} 1/(hᵢ+1-2kᵢλ) · N^{-λ} (log N)^{|J|-1}`

(`monomialBoxReal_mixed_isEquivalent`), which is the paper's Laurent coefficient
`a_{-|J|}` (eq. `a_minus_m_explicit`, cutoff `b = 1`) times the Laplace–Tauberian factor
`Γ(λ)/(|J|-1)!` and the inverse-temperature factor `β^{-λ}` (the paper has `β = 1`). The exact relation `M(N) = ∏ 1/(2kᵢ) · W_ℓ(N)` (`monomialBoxReal_eq_mixed`) comes
from the coordinatewise substitution of unit 174; the weighted asymptotic is unit 180. A `min`
wrapper (`minRatio`) removes the explicit minimum/attainment hypotheses.
-/

open MeasureTheory Set Filter Topology Asymptotics

namespace Laplace.Grammar

/-- The Mellin ratios `ℓᵢ = (hᵢ+1)/(2kᵢ)`. -/
noncomputable def ratioExp {d : ℕ} (h k : Fin d → ℕ) (i : Fin d) : ℝ :=
  ((h i : ℝ) + 1) / (2 * (k i : ℝ))

theorem ratioExp_pos {d : ℕ} (h k : Fin d → ℕ) (hk : ∀ i, 0 < k i) (i : Fin d) :
    0 < ratioExp h k i := by
  unfold ratioExp
  have := hk i
  positivity

/-- **Exact relation**: `M(N) = ∏ 1/(2kᵢ) · W_ℓ(N)` with `ℓᵢ = (hᵢ+1)/(2kᵢ)`. -/
theorem monomialBoxReal_eq_mixed (d : ℕ) (h k : Fin d → ℕ) (hk : ∀ i, 0 < k i) (β N : ℝ) :
    monomialBoxReal d h k β N =
      (∏ i, 1 / (2 * (k i : ℝ))) * mixedBoxReal d (ratioExp h k) β N := by
  have hP : 0 ≤ ∏ i, 1 / (2 * (k i : ℝ)) := Finset.prod_nonneg fun i _ => by positivity
  have h1 := ofReal_monomialBoxReal d h k β N
  rw [monomialBoxIntegral_eq_weighted d h k hk _ (measurable_expKernel β N)] at h1
  have h2 := congrArg ENNReal.toReal h1
  rw [ENNReal.toReal_ofReal (monomialBoxReal_nonneg d h k β N), ENNReal.toReal_mul,
    ENNReal.toReal_ofReal hP] at h2
  rw [h2]
  rfl

/-- The paper-form mixed constant
`Γ(λ) β^{-λ} / (|J|-1)! · ∏_{i∈J} 1/(2kᵢ) · ∏_{i∉J} 1/(hᵢ+1-2kᵢλ)`. -/
noncomputable def monomialMixedConst {d : ℕ} (h k : Fin d → ℕ) (l β : ℝ) : ℝ :=
  Real.Gamma l * β ^ (-l) / ((multCount (ratioExp h k) l - 1).factorial : ℝ) *
    ∏ i, if ratioExp h k i = l then 1 / (2 * (k i : ℝ))
      else 1 / ((h i : ℝ) + 1 - 2 * (k i : ℝ) * l)

theorem monomialMixedConst_eq {d : ℕ} (h k : Fin d → ℕ) (hk : ∀ i, 0 < k i) (l β : ℝ) :
    monomialMixedConst h k l β =
      (∏ i, 1 / (2 * (k i : ℝ))) * mixedConst (ratioExp h k) l β := by
  unfold monomialMixedConst mixedConst resFactor
  have hprod : (∏ i, if ratioExp h k i = l then 1 / (2 * (k i : ℝ))
      else 1 / ((h i : ℝ) + 1 - 2 * (k i : ℝ) * l)) =
      (∏ i, 1 / (2 * (k i : ℝ))) *
        ∏ i, if ratioExp h k i = l then (1 : ℝ) else 1 / (ratioExp h k i - l) := by
    rw [← Finset.prod_mul_distrib]
    refine Finset.prod_congr rfl fun i _ => ?_
    have hk0 : (k i : ℝ) ≠ 0 := Nat.cast_ne_zero.2 (hk i).ne'
    split_ifs with hi
    · ring
    · have hne : (h i : ℝ) + 1 - 2 * (k i : ℝ) * l ≠ 0 := by
        intro h0
        apply hi
        unfold ratioExp
        field_simp
        linarith
      unfold ratioExp at hne ⊢
      field_simp
  rw [hprod]
  ring

theorem monomialMixedConst_pos {d : ℕ} (h k : Fin d → ℕ) (hk : ∀ i, 0 < k i) (l β : ℝ)
    (hl : 0 < l) (hβ : 0 < β) (hmin : ∀ i, l ≤ ratioExp h k i) :
    0 < monomialMixedConst h k l β := by
  rw [monomialMixedConst_eq h k hk l β]
  exact mul_pos (Finset.prod_pos fun i _ => by have := hk i; positivity)
    (mixedConst_pos _ l β hl hβ hmin)

/-- **Mixed-ratio monomial asymptotic (ratio form)**. -/
theorem monomialBoxReal_mixed_tendsto (d : ℕ) (h k : Fin (d + 1) → ℕ) (hk : ∀ i, 0 < k i)
    (l β : ℝ) (hl : 0 < l) (hβ : 0 < β) (hmin : ∀ i, l ≤ ratioExp h k i)
    (hatt : ∃ i, ratioExp h k i = l) :
    Tendsto (fun N => monomialBoxReal (d + 1) h k β N /
        (N ^ (-l) * Real.log N ^ (multCount (ratioExp h k) l - 1))) atTop
      (𝓝 (monomialMixedConst h k l β)) := by
  rw [monomialMixedConst_eq h k hk l β]
  refine ((mixedBoxReal_tendsto l β hl hβ d _ hmin hatt).const_mul _).congr'
    (Eventually.of_forall fun N => ?_)
  beta_reduce
  rw [monomialBoxReal_eq_mixed _ h k hk β N, mul_div_assoc]

/-- **Mixed-ratio monomial asymptotic (equivalence form)**:
`M(N) ~ Γ(λ) β^{-λ}/(|J|-1)! · ∏_{J} 1/(2kᵢ) · ∏_{∉J} 1/(hᵢ+1-2kᵢλ) · N^{-λ} (log N)^{|J|-1}`. -/
theorem monomialBoxReal_mixed_isEquivalent (d : ℕ) (h k : Fin (d + 1) → ℕ) (hk : ∀ i, 0 < k i)
    (l β : ℝ) (hl : 0 < l) (hβ : 0 < β) (hmin : ∀ i, l ≤ ratioExp h k i)
    (hatt : ∃ i, ratioExp h k i = l) :
    (fun N => monomialBoxReal (d + 1) h k β N) ~[atTop]
      fun N => monomialMixedConst h k l β * N ^ (-l) *
        Real.log N ^ (multCount (ratioExp h k) l - 1) := by
  have hC := monomialMixedConst_pos h k hk l β hl hβ hmin
  refine isEquivalent_of_tendsto_one ?_
  have hT := (monomialBoxReal_mixed_tendsto d h k hk l β hl hβ hmin hatt).div_const
    (monomialMixedConst h k l β)
  rw [div_self hC.ne'] at hT
  refine hT.congr' ?_
  filter_upwards [eventually_gt_atTop (1 : ℝ)] with N hN
  have hN0 : 0 < N := by linarith
  have hpow : N ^ (-l) ≠ 0 := (Real.rpow_pos_of_pos hN0 _).ne'
  have hlog : Real.log N ^ (multCount (ratioExp h k) l - 1) ≠ 0 :=
    pow_ne_zero _ (Real.log_pos hN).ne'
  simp only [Pi.div_apply]
  field_simp

/-- The minimal Mellin ratio `λ = minᵢ (hᵢ+1)/(2kᵢ)`. -/
noncomputable def minRatio {d : ℕ} (h k : Fin (d + 1) → ℕ) : ℝ :=
  Finset.univ.inf' Finset.univ_nonempty (ratioExp h k)

theorem minRatio_le {d : ℕ} (h k : Fin (d + 1) → ℕ) (i : Fin (d + 1)) :
    minRatio h k ≤ ratioExp h k i :=
  Finset.inf'_le _ (Finset.mem_univ i)

theorem exists_ratioExp_eq_minRatio {d : ℕ} (h k : Fin (d + 1) → ℕ) :
    ∃ i, ratioExp h k i = minRatio h k := by
  obtain ⟨i, -, hi⟩ := Finset.exists_mem_eq_inf' Finset.univ_nonempty (ratioExp h k)
  exact ⟨i, hi.symm⟩

theorem minRatio_pos {d : ℕ} (h k : Fin (d + 1) → ℕ) (hk : ∀ i, 0 < k i) : 0 < minRatio h k := by
  obtain ⟨i, hi⟩ := exists_ratioExp_eq_minRatio h k
  rw [← hi]
  exact ratioExp_pos h k hk i

/-- **Mixed-ratio monomial asymptotic at the minimal ratio** (no explicit minimum hypotheses). -/
theorem monomialBoxReal_minRatio_isEquivalent (d : ℕ) (h k : Fin (d + 1) → ℕ)
    (hk : ∀ i, 0 < k i) (β : ℝ) (hβ : 0 < β) :
    (fun N => monomialBoxReal (d + 1) h k β N) ~[atTop]
      fun N => monomialMixedConst h k (minRatio h k) β * N ^ (-(minRatio h k)) *
        Real.log N ^ (multCount (ratioExp h k) (minRatio h k) - 1) :=
  monomialBoxReal_mixed_isEquivalent d h k hk _ β (minRatio_pos h k hk) hβ (minRatio_le h k)
    (exists_ratioExp_eq_minRatio h k)

end Laplace.Grammar
