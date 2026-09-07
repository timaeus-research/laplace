/-
Copyright (c) 2026 Daniel Murfet. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniel Murfet
-/
import Laplace.Grammar.WeightedMixedReal

/-!
# The mixed-ratio weighted asymptotic

Fourth step of the mixed-ratio general-`d` monomial programme (Astra #15, route A): the leading
asymptotic of the real weighted box integral

  `W_ℓ(N) = ∫_{(0,1]^d} ∏ tᵢ^{ℓᵢ-1} e^{-βN ∏ tᵢ} dt`

for **arbitrary** positive exponents `ℓᵢ` with minimum `λ` attained `m` times:

  `W_ℓ(N) / (N^{-λ} (log N)^{m-1}) → Γ(λ) β^{-λ} / (m-1)! · ∏_{ℓᵢ > λ} 1/(ℓᵢ - λ)`

(`mixedBoxReal_tendsto`). The multiplicity is `multCount ℓ λ = ∑ᵢ [ℓᵢ = λ]` and the residue product
`resFactor ℓ λ = ∏ᵢ (if ℓᵢ = λ then 1 else 1/(ℓᵢ-λ))`, both stated as sums/products over all
coordinates so that they are manifestly permutation invariant and peel off the first coordinate by
`Fin.sum_univ_succ`/`Fin.prod_univ_succ`.

The proof is an induction on the number of coordinates. If every coordinate is minimal, this is the
equal-ratio theorem (units 172–173). Otherwise a nonminimal coordinate is moved to position `0` by
the permutation invariance of unit 179, the real recursion peels it, and the dominated-coordinate
transfer lemma of unit 178 applied to the lower-dimensional integral (bounded by its mass, measurable
in the parameter) multiplies the constant by `1/(ℓ₀-λ)` without changing exponent or log degree.
-/

open MeasureTheory Set Filter Topology Asymptotics

namespace Laplace.Grammar

/-- The multiplicity of the value `l` among the exponents. -/
noncomputable def multCount {d : ℕ} (ℓ : Fin d → ℝ) (l : ℝ) : ℕ :=
  ∑ i, if ℓ i = l then 1 else 0

/-- The residue product over the nonminimal coordinates. -/
noncomputable def resFactor {d : ℕ} (ℓ : Fin d → ℝ) (l : ℝ) : ℝ :=
  ∏ i, if ℓ i = l then 1 else 1 / (ℓ i - l)

/-- The mixed-ratio leading constant `Γ(λ) β^{-λ} / (m-1)! · ∏_{ℓᵢ > λ} 1/(ℓᵢ - λ)`. -/
noncomputable def mixedConst {d : ℕ} (ℓ : Fin d → ℝ) (l β : ℝ) : ℝ :=
  Real.Gamma l * β ^ (-l) / ((multCount ℓ l - 1).factorial : ℝ) * resFactor ℓ l

theorem multCount_comp {d : ℕ} (ℓ : Fin d → ℝ) (l : ℝ) (σ : Equiv.Perm (Fin d)) :
    multCount (ℓ ∘ σ) l = multCount ℓ l :=
  Equiv.sum_comp σ (fun i => if ℓ i = l then 1 else 0)

theorem resFactor_comp {d : ℕ} (ℓ : Fin d → ℝ) (l : ℝ) (σ : Equiv.Perm (Fin d)) :
    resFactor (ℓ ∘ σ) l = resFactor ℓ l :=
  Equiv.prod_comp σ (fun i => if ℓ i = l then 1 else 1 / (ℓ i - l))

theorem mixedConst_comp {d : ℕ} (ℓ : Fin d → ℝ) (l β : ℝ) (σ : Equiv.Perm (Fin d)) :
    mixedConst (ℓ ∘ σ) l β = mixedConst ℓ l β := by
  unfold mixedConst
  rw [multCount_comp, resFactor_comp]

theorem multCount_succ {d : ℕ} (ℓ : Fin (d + 1) → ℝ) (l : ℝ) :
    multCount ℓ l = (if ℓ 0 = l then 1 else 0) + multCount (Fin.tail ℓ) l := by
  unfold multCount
  rw [Fin.sum_univ_succ]
  rfl

theorem resFactor_succ {d : ℕ} (ℓ : Fin (d + 1) → ℝ) (l : ℝ) :
    resFactor ℓ l = (if ℓ 0 = l then 1 else 1 / (ℓ 0 - l)) * resFactor (Fin.tail ℓ) l := by
  unfold resFactor
  rw [Fin.prod_univ_succ]
  rfl

theorem multCount_const (d : ℕ) (l : ℝ) : multCount (fun _ : Fin (d + 1) => l) l = d + 1 := by
  simp [multCount]

theorem resFactor_const (d : ℕ) (l : ℝ) : resFactor (fun _ : Fin (d + 1) => l) l = 1 := by
  simp [resFactor]

theorem multCount_pos {d : ℕ} (ℓ : Fin d → ℝ) (l : ℝ) (hatt : ∃ i, ℓ i = l) :
    0 < multCount ℓ l := by
  obtain ⟨i, hi⟩ := hatt
  unfold multCount
  calc 0 < (if ℓ i = l then 1 else 0) := by rw [if_pos hi]; exact one_pos
    _ ≤ ∑ j, if ℓ j = l then 1 else 0 :=
      Finset.single_le_sum (f := fun j => if ℓ j = l then (1 : ℕ) else 0)
        (fun j _ => Nat.zero_le _) (Finset.mem_univ i)

theorem resFactor_pos {d : ℕ} (ℓ : Fin d → ℝ) (l : ℝ) (hmin : ∀ i, l ≤ ℓ i) :
    0 < resFactor ℓ l := by
  unfold resFactor
  refine Finset.prod_pos fun i _ => ?_
  split_ifs with h
  · exact one_pos
  · exact div_pos one_pos (by linarith [lt_of_le_of_ne (hmin i) (Ne.symm h)])

theorem mixedConst_pos {d : ℕ} (ℓ : Fin d → ℝ) (l β : ℝ) (hl : 0 < l) (hβ : 0 < β)
    (hmin : ∀ i, l ≤ ℓ i) : 0 < mixedConst ℓ l β := by
  unfold mixedConst
  have h1 := Real.Gamma_pos_of_pos hl
  have h2 := Real.rpow_pos_of_pos hβ (-l)
  have h3 := resFactor_pos ℓ l hmin
  positivity

/-- The permuted integrals agree. -/
theorem mixedBoxReal_comp_perm {d : ℕ} (ℓ : Fin d → ℝ) (β N : ℝ) (σ : Equiv.Perm (Fin d)) :
    mixedBoxReal d (ℓ ∘ σ) β N = mixedBoxReal d ℓ β N := by
  unfold mixedBoxReal
  have h : (fun i => (ℓ ∘ σ) i - 1) = (fun i => ℓ i - 1) ∘ σ := rfl
  rw [h, weightedBoxIntegral_comp_perm]

/-- **Equal exponents**: the exact reduction to the Gamma/log integral. -/
theorem mixedBoxReal_const_eq (d : ℕ) (l β N : ℝ) (hl : 0 < l) (hβN : 0 < β * N) :
    mixedBoxReal (d + 1) (fun _ => l) β N = 1 / (d.factorial : ℝ) * gammaLogIntegral l d β N := by
  unfold mixedBoxReal
  rw [weightedBoxIntegral_const_eq_productIntegral l (d + 1) _ (measurable_expKernel β N),
    productIntegral_succ_eq l d _ (measurable_expKernel β N)]
  simp only [expKernel]
  rw [lintegral_logDensity_mul_exp l d β N hl hβN, ← ENNReal.ofReal_mul (by positivity),
    ENNReal.toReal_ofReal (mul_nonneg (by positivity) (gammaLogIntegral_nonneg l d β N))]

/-- **Equal exponents**: the asymptotic. -/
theorem mixedBoxReal_const_tendsto (d : ℕ) (l β : ℝ) (hl : 0 < l) (hβ : 0 < β) :
    Tendsto (fun N => mixedBoxReal (d + 1) (fun _ => l) β N / (N ^ (-l) * Real.log N ^ d)) atTop
      (𝓝 (1 / (d.factorial : ℝ) * (Real.Gamma l * β ^ (-l)))) := by
  refine ((tendsto_gammaLogIntegral_div l d β hl hβ).const_mul _).congr' ?_
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with N hN
  rw [mixedBoxReal_const_eq d l β N hl (mul_pos hβ hN), mul_div_assoc]

/-- **Mixed-ratio weighted asymptotic**: for positive exponents with minimum `λ` attained,
`W_ℓ(N) / (N^{-λ} (log N)^{m-1}) → Γ(λ) β^{-λ}/(m-1)! · ∏_{ℓᵢ>λ} 1/(ℓᵢ-λ)`. -/
theorem mixedBoxReal_tendsto (l β : ℝ) (hl : 0 < l) (hβ : 0 < β) :
    ∀ (d : ℕ) (ℓ : Fin (d + 1) → ℝ), (∀ i, l ≤ ℓ i) → (∃ i, ℓ i = l) →
      Tendsto (fun N => mixedBoxReal (d + 1) ℓ β N /
          (N ^ (-l) * Real.log N ^ (multCount ℓ l - 1))) atTop (𝓝 (mixedConst ℓ l β)) := by
  intro d
  induction d with
  | zero =>
    intro ℓ hmin hatt
    have hall : ℓ = fun _ => l := by
      funext i
      obtain ⟨j, hj⟩ := hatt
      rw [show i = j from Fin.ext (by omega), hj]
    subst hall
    have h := mixedBoxReal_const_tendsto 0 l β hl hβ
    simp only [Nat.factorial_zero, Nat.cast_one, div_one, one_mul, pow_zero] at h
    unfold mixedConst
    rw [multCount_const, resFactor_const]
    simpa using h
  | succ d ih =>
    intro ℓ hmin hatt
    -- the key case: a nonminimal coordinate in position `0`
    have key : ∀ ℓ' : Fin (d + 2) → ℝ, (∀ i, l ≤ ℓ' i) → (∃ i, ℓ' i = l) → l < ℓ' 0 →
        Tendsto (fun N => mixedBoxReal (d + 2) ℓ' β N /
          (N ^ (-l) * Real.log N ^ (multCount ℓ' l - 1))) atTop (𝓝 (mixedConst ℓ' l β)) := by
      intro ℓ' hmin' hatt' h0
      have hne : ℓ' 0 ≠ l := h0.ne'
      have htail_att : ∃ i, Fin.tail ℓ' i = l := by
        obtain ⟨i₀, hi₀⟩ := hatt'
        have hi₀0 : i₀ ≠ 0 := fun h => hne (h ▸ hi₀)
        obtain ⟨i, rfl⟩ := Fin.eq_succ_of_ne_zero hi₀0
        exact ⟨i, hi₀⟩
      have hpos : ∀ i, 0 < Fin.tail ℓ' i := fun i => lt_of_lt_of_le hl (hmin' i.succ)
      have ihT := ih (Fin.tail ℓ') (fun i => hmin' i.succ) htail_att
      have hT := tendsto_weighted_scale_div (fun M => mixedBoxReal (d + 1) (Fin.tail ℓ') β M) l
        (ℓ' 0) (multCount (Fin.tail ℓ') l - 1) (mixedConst (Fin.tail ℓ') l β)
        (∏ i, 1 / Fin.tail ℓ' i) hl h0 (measurable_mixedBoxReal _ _ β)
        (fun M hM => abs_mixedBoxReal_le _ _ hpos β hβ M hM) ihT
      have hm : multCount ℓ' l = multCount (Fin.tail ℓ') l := by
        rw [multCount_succ, if_neg hne, zero_add]
      have hc : mixedConst ℓ' l β = mixedConst (Fin.tail ℓ') l β / (ℓ' 0 - l) := by
        unfold mixedConst
        rw [hm, resFactor_succ, if_neg hne]
        ring
      rw [hm, hc]
      refine hT.congr' ?_
      filter_upwards [eventually_gt_atTop (0 : ℝ)] with N hN
      rw [mixedBoxReal_succ (d + 1) ℓ' (fun i => lt_of_lt_of_le hl (hmin' i)) β N hβ hN]
    by_cases hall : ∀ i, ℓ i = l
    · have hℓ : ℓ = fun _ => l := funext hall
      subst hℓ
      have h := mixedBoxReal_const_tendsto (d + 1) l β hl hβ
      unfold mixedConst
      rw [multCount_const, resFactor_const, Nat.add_sub_cancel, mul_one, div_eq_mul_one_div,
        mul_comm]
      exact h
    · push Not at hall
      obtain ⟨j, hj⟩ := hall
      have hj' : l < ℓ j := lt_of_le_of_ne (hmin j) (Ne.symm hj)
      by_cases h0 : ℓ 0 = l
      · -- move coordinate `j` to position `0`
        set σ : Equiv.Perm (Fin (d + 2)) := Equiv.swap 0 j with hσ
        have h0' : l < (ℓ ∘ σ) 0 := by
          simp only [Function.comp, hσ, Equiv.swap_apply_left]
          exact hj'
        have hmin' : ∀ i, l ≤ (ℓ ∘ σ) i := fun i => hmin (σ i)
        have hatt' : ∃ i, (ℓ ∘ σ) i = l := by
          obtain ⟨i₀, hi₀⟩ := hatt
          exact ⟨σ.symm i₀, by simp only [Function.comp, Equiv.apply_symm_apply]; exact hi₀⟩
        have hkey := key (ℓ ∘ σ) hmin' hatt' h0'
        rw [mixedConst_comp, multCount_comp] at hkey
        refine hkey.congr' (Eventually.of_forall fun N => ?_)
        rw [mixedBoxReal_comp_perm]
      · exact key ℓ hmin hatt (lt_of_le_of_ne (hmin 0) (Ne.symm h0))

/-- **Mixed-ratio weighted asymptotic (equivalence form)** against the `powLog` normal form. -/
theorem mixedBoxReal_isEquivalent (l β : ℝ) (hl : 0 < l) (hβ : 0 < β) (d : ℕ)
    (ℓ : Fin (d + 1) → ℝ) (hmin : ∀ i, l ≤ ℓ i) (hatt : ∃ i, ℓ i = l) :
    (fun N => mixedBoxReal (d + 1) ℓ β N) ~[atTop]
      powLog (mixedConst ℓ l β) l (multCount ℓ l - 1) := by
  have hC := mixedConst_pos ℓ l β hl hβ hmin
  refine isEquivalent_of_tendsto_one ?_
  have h := (mixedBoxReal_tendsto l β hl hβ d ℓ hmin hatt).div_const (mixedConst ℓ l β)
  rw [div_self hC.ne'] at h
  refine h.congr' ?_
  filter_upwards [eventually_gt_atTop (1 : ℝ)] with N hN
  have hN0 : 0 < N := by linarith
  have hpow : N ^ (-l) ≠ 0 := (Real.rpow_pos_of_pos hN0 _).ne'
  have hlog : Real.log N ^ (multCount ℓ l - 1) ≠ 0 := pow_ne_zero _ (Real.log_pos hN).ne'
  simp only [Pi.div_apply, powLog]
  field_simp

end Laplace.Grammar
