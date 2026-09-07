/-
Copyright (c) 2026 Timaeus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Laplace.Grammar.CoeffFnBridge

/-!
# The coefficient kernel as an `ℓ¹`-continuous functional (Stage 5c)

Unit 253 (Taylor-tree programme; Astra #29 candidate A). The Stage 3 coefficient term
`coeffTerm_p(μ,j)(P) = K_k ∑_{(γ,c)∈P} c · S_p(μ,j;γ)`, with the **monomial kernel**
`S_p(μ,j;γ) = ∑_{q=j}^{n} coeffAt(ρ_{h+γ}, μ, q) C(q,j) fluctMoment_p(μ, q-j)`, depends on the list
only through its collected coefficients: `coeffTerm P = T_p(coeffFn P)` where
`T_p(f) = K_k ∑_γ f_γ S_p(γ)` (`coeffTerm_eq_kernelFunctional`). The kernel is bounded uniformly in
the monomial, `|S_p(γ)| ≤ D_{n,k} M_{μ,n,p}(a)` (`abs_kernelS_le`), so `T_p` is an `ℓ¹`-continuous
linear functional: `|T_p f| ≤ K_k D M_{μ,n,p}(a) · mass f` (`abs_kernelFunctional_le`). Also: the
fluctuation part and the box truncation collect to the constant-free family `fluctFamily` and the
restricted family `truncFamily` (`coeffFn_fluct`, `coeffFn_truncList`). No `sorry` and no additional
`axiom` declarations.
-/

open MeasureTheory Set Real Filter Topology

namespace Laplace.Grammar

open MonoRep CoeffFamily

/-! ### The monomial kernel -/

/-- The monomial kernel
`S_p(μ,j;γ) = ∑_{q=j}^{n} coeffAt(ρ_{h+γ},μ,q) C(q,j) fluctMoment_p(μ,q-j)`. -/
noncomputable def kernelS (n : ℕ) (h k : Fin (n + 1) → ℕ) (β a : ℝ) (p : ℕ) (μ : ℝ) (j : ℕ)
    (γ : Fin (n + 1) → ℕ) : ℝ :=
  ∑ q ∈ Finset.Ico j (n + 1),
    PowLogRep.coeffAt (stateDensityRep n (monoWeights (h + γ) k)) μ q * (q.choose j : ℝ) *
      fluctMoment β a p μ (q - j)

/-- The uniform budget `D_{n,k} = (n+1)(n+1)! Q^n 2^n`. -/
noncomputable def kernelBudget (n : ℕ) (k : Fin (n + 1) → ℕ) : ℝ :=
  (n + 1 : ℝ) * (((n + 1).factorial : ℝ) * (latticeQ k : ℝ) ^ n) * 2 ^ n

theorem kernelBudget_nonneg (n : ℕ) (k : Fin (n + 1) → ℕ) : 0 ≤ kernelBudget n k := by
  unfold kernelBudget; positivity

/-- `|S_p(μ,j;γ)| ≤ D M_{μ,n,p}(a)`, uniformly in the monomial `γ`. -/
theorem abs_kernelS_le (n : ℕ) (h k : Fin (n + 1) → ℕ) (hk : ∀ i, 0 < k i) (β a : ℝ) (hβ : 0 < β)
    (p : ℕ) {μ : ℝ} (hμ : 0 < μ) (j : ℕ) (γ : Fin (n + 1) → ℕ) :
    |kernelS n h k β a p μ j γ| ≤ kernelBudget n k * phaseLogMoment β a μ n p := by
  unfold kernelS kernelBudget
  set M := phaseLogMoment β a μ n p with hM
  have hM0 : 0 ≤ M := phaseLogMoment_nonneg β a μ n p
  refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
  have hterm : ∀ q ∈ Finset.Ico j (n + 1),
      |PowLogRep.coeffAt (stateDensityRep n (monoWeights (h + γ) k)) μ q * (q.choose j : ℝ) *
        fluctMoment β a p μ (q - j)| ≤
      (((n + 1).factorial : ℝ) * (latticeQ k : ℝ) ^ n) * 2 ^ n * M := by
    intro q hq
    have hqn : q ≤ n := Nat.lt_succ_iff.1 (Finset.mem_Ico.1 hq).2
    rw [abs_mul, abs_mul, Nat.abs_cast]
    refine mul_le_mul (mul_le_mul (abs_coeffAt_stateDensityRep_le n (h + γ) k hk μ q) ?_
      (by positivity) (by positivity)) (abs_fluctMoment_le β a hβ p hμ (by omega))
      (abs_nonneg _) (by positivity)
    calc (q.choose j : ℝ) ≤ (2 ^ q : ℕ) := by exact_mod_cast Nat.choose_le_two_pow q j
      _ ≤ 2 ^ n := by exact_mod_cast Nat.pow_le_pow_right two_pos hqn
  refine (Finset.sum_le_card_nsmul _ _ _ hterm).trans ?_
  rw [nsmul_eq_mul, Nat.card_Ico]
  have hcard : ((n + 1 - j : ℕ) : ℝ) ≤ n + 1 := by exact_mod_cast Nat.sub_le (n + 1) j
  calc ((n + 1 - j : ℕ) : ℝ) * ((((n + 1).factorial : ℝ) * (latticeQ k : ℝ) ^ n) * 2 ^ n * M)
      ≤ (n + 1 : ℝ) * ((((n + 1).factorial : ℝ) * (latticeQ k : ℝ) ^ n) * 2 ^ n * M) :=
        mul_le_mul_of_nonneg_right hcard (by positivity)
    _ = _ := by ring

/-! ### The kernel functional -/

/-- `T_p(f) = K_k ∑_γ f_γ S_p(μ,j;γ)`. -/
noncomputable def kernelFunctional (n : ℕ) (h k : Fin (n + 1) → ℕ) (β a : ℝ) (p : ℕ) (μ : ℝ)
    (j : ℕ) (f : CoeffFamily (n + 1)) : ℝ :=
  (∏ i, 1 / (2 * (k i : ℝ))) * ∑' γ, f γ * kernelS n h k β a p μ j γ

/-- The Stage 3 coefficient term is the kernel functional of the collected coefficients. -/
theorem coeffTerm_eq_kernelFunctional (n : ℕ) (h k : Fin (n + 1) → ℕ) (β a : ℝ) (p : ℕ) (μ : ℝ)
    (j : ℕ) (P : MonoRep (n + 1)) :
    coeffTerm n h k β a p μ j P = kernelFunctional n h k β a p μ j (coeffFn P) := by
  unfold coeffTerm kernelFunctional kernelS
  congr 1
  exact sum_map_eq_tsum_coeffFn P fun γ => ∑ q ∈ Finset.Ico j (n + 1),
    PowLogRep.coeffAt (stateDensityRep n (monoWeights (h + γ) k)) μ q * (q.choose j : ℝ) *
      fluctMoment β a p μ (q - j)

theorem summable_kernel_term (n : ℕ) (h k : Fin (n + 1) → ℕ) (hk : ∀ i, 0 < k i) (β a : ℝ)
    (hβ : 0 < β) (p : ℕ) {μ : ℝ} (hμ : 0 < μ) (j : ℕ) {f : CoeffFamily (n + 1)}
    (hf : AbsSummable f) :
    Summable fun γ => |f γ * kernelS n h k β a p μ j γ| := by
  refine Summable.of_nonneg_of_le (fun _ => abs_nonneg _) (fun γ => ?_)
    (hf.mul_right (kernelBudget n k * phaseLogMoment β a μ n p))
  rw [abs_mul]
  exact mul_le_mul_of_nonneg_left (abs_kernelS_le n h k hk β a hβ p hμ j γ) (abs_nonneg _)

/-- **`ℓ¹`-continuity of the kernel functional**: `|T_p f| ≤ K_k D M_{μ,n,p}(a) mass f`. -/
theorem abs_kernelFunctional_le (n : ℕ) (h k : Fin (n + 1) → ℕ) (hk : ∀ i, 0 < k i) (β a : ℝ)
    (hβ : 0 < β) (p : ℕ) {μ : ℝ} (hμ : 0 < μ) (j : ℕ) {f : CoeffFamily (n + 1)}
    (hf : AbsSummable f) :
    |kernelFunctional n h k β a p μ j f| ≤
      (∏ i, 1 / (2 * (k i : ℝ))) * kernelBudget n k * phaseLogMoment β a μ n p * mass f := by
  have hK : 0 ≤ ∏ i, 1 / (2 * (k i : ℝ)) := Finset.prod_nonneg fun i _ => by positivity
  have hDM : 0 ≤ kernelBudget n k * phaseLogMoment β a μ n p :=
    mul_nonneg (kernelBudget_nonneg n k) (phaseLogMoment_nonneg _ _ _ _ _)
  unfold kernelFunctional
  rw [abs_mul, abs_of_nonneg hK]
  have h1 : |∑' γ, f γ * kernelS n h k β a p μ j γ| ≤
      ∑' γ, |f γ| * (kernelBudget n k * phaseLogMoment β a μ n p) := by
    have hn := norm_tsum_le_tsum_norm (f := fun γ => f γ * kernelS n h k β a p μ j γ)
      (by simpa [Real.norm_eq_abs] using summable_kernel_term n h k hk β a hβ p hμ j hf)
    simp only [Real.norm_eq_abs] at hn
    refine hn.trans ?_
    refine Summable.tsum_le_tsum (fun γ => ?_) (summable_kernel_term n h k hk β a hβ p hμ j hf)
      (hf.mul_right _)
    rw [abs_mul]
    exact mul_le_mul_of_nonneg_left (abs_kernelS_le n h k hk β a hβ p hμ j γ) (abs_nonneg _)
  rw [tsum_mul_right] at h1
  calc (∏ i, 1 / (2 * (k i : ℝ))) * |∑' γ, f γ * kernelS n h k β a p μ j γ|
      ≤ (∏ i, 1 / (2 * (k i : ℝ))) * (mass f * (kernelBudget n k * phaseLogMoment β a μ n p)) :=
        mul_le_mul_of_nonneg_left h1 hK
    _ = _ := by ring

/-- Linearity of the kernel functional in the family (difference form). -/
theorem kernelFunctional_sub (n : ℕ) (h k : Fin (n + 1) → ℕ) (hk : ∀ i, 0 < k i) (β a : ℝ)
    (hβ : 0 < β) (p : ℕ) {μ : ℝ} (hμ : 0 < μ) (j : ℕ) {f g : CoeffFamily (n + 1)}
    (hf : AbsSummable f) (hg : AbsSummable g) :
    kernelFunctional n h k β a p μ j f - kernelFunctional n h k β a p μ j g =
      kernelFunctional n h k β a p μ j (f - g) := by
  unfold kernelFunctional
  rw [← mul_sub]
  congr 1
  have hf' : Summable fun γ => f γ * kernelS n h k β a p μ j γ :=
    Summable.of_norm
      (by simpa [Real.norm_eq_abs] using summable_kernel_term n h k hk β a hβ p hμ j hf)
  have hg' : Summable fun γ => g γ * kernelS n h k β a p μ j γ :=
    Summable.of_norm
      (by simpa [Real.norm_eq_abs] using summable_kernel_term n h k hk β a hβ p hμ j hg)
  rw [← hf'.tsum_sub hg']
  exact tsum_congr fun γ => by simp [Pi.sub_apply, sub_mul]

/-! ### Collected fluctuation part and truncation -/

namespace CoeffFamily

variable {d : ℕ}

/-- The constant-free part `J` of a family. -/
noncomputable def fluctFamily (c : CoeffFamily d) : CoeffFamily d :=
  fun γ => if γ = 0 then 0 else c γ

/-- The family restricted to the box `{γ | γᵢ ≤ m}`. -/
noncomputable def truncFamily (c : CoeffFamily d) (m : ℕ) : CoeffFamily d :=
  fun γ => if γ ∈ boxSet d m then c γ else 0

theorem abs_fluctFamily_le (c : CoeffFamily d) (γ : Fin d → ℕ) : |fluctFamily c γ| ≤ |c γ| := by
  unfold fluctFamily; split_ifs <;> simp

theorem AbsSummable.fluctFamily {c : CoeffFamily d} (hc : AbsSummable c) :
    AbsSummable (fluctFamily c) :=
  Summable.of_nonneg_of_le (fun _ => abs_nonneg _) (abs_fluctFamily_le c) hc

theorem mass_fluctFamily_le {c : CoeffFamily d} (hc : AbsSummable c) :
    mass (fluctFamily c) ≤ mass c :=
  Summable.tsum_le_tsum (abs_fluctFamily_le c) hc.fluctFamily hc

theorem abs_truncFamily_le (c : CoeffFamily d) (m : ℕ) (γ : Fin d → ℕ) :
    |truncFamily c m γ| ≤ |c γ| := by
  unfold truncFamily; split_ifs <;> simp

theorem AbsSummable.truncFamily {c : CoeffFamily d} (hc : AbsSummable c) (m : ℕ) :
    AbsSummable (truncFamily c m) :=
  Summable.of_nonneg_of_le (fun _ => abs_nonneg _) (abs_truncFamily_le c m) hc

theorem mass_truncFamily_le {c : CoeffFamily d} (hc : AbsSummable c) (m : ℕ) :
    mass (truncFamily c m) ≤ mass c :=
  Summable.tsum_le_tsum (abs_truncFamily_le c m) (hc.truncFamily m) hc

/-- `mass (c − truncFamily c m) = tailMass c m`. -/
theorem mass_sub_truncFamily {c : CoeffFamily d} (m : ℕ) :
    mass (c - truncFamily c m) = tailMass c m := by
  unfold mass tailMass
  refine tsum_congr fun γ => ?_
  simp only [Pi.sub_apply, truncFamily]
  split_ifs <;> simp

theorem fluctFamily_truncFamily (c : CoeffFamily d) (m : ℕ) :
    fluctFamily (truncFamily c m) = truncFamily (fluctFamily c) m := by
  funext γ
  simp only [fluctFamily, truncFamily]
  split_ifs <;> rfl

end CoeffFamily

namespace MonoRep

variable {d : ℕ}

theorem coeffFn_fluct (P : MonoRep d) : coeffFn (fluct P) = fluctFamily (coeffFn P) := by
  funext γ
  unfold fluctFamily
  induction P with
  | nil => simp [fluct]
  | cons s P ih =>
    by_cases hs : s.1 = 0
    · have e : fluct (s :: P) = fluct P := List.filter_cons_of_neg (by simp [hs])
      rw [e, ih, coeffFn_cons]
      by_cases hγ : γ = 0
      · simp [hγ]
      · rw [if_neg hγ, if_neg hγ, if_neg (fun h => hγ (h.symm.trans hs)), zero_add]
    · have e : fluct (s :: P) = s :: fluct P := List.filter_cons_of_pos (by simp [hs])
      rw [e, coeffFn_cons, ih, coeffFn_cons]
      by_cases hγ : γ = 0
      · subst hγ; rw [if_neg hs]; simp
      · rw [if_neg hγ, if_neg hγ]

theorem coeffFn_truncList (c : CoeffFamily d) (m : ℕ) :
    coeffFn (truncList c m) = truncFamily c m := by
  funext γ
  have h := sum_map_eq_tsum_coeffFn (truncList c m) fun γ' => if γ' = γ then (1 : ℝ) else 0
  have h2 : ∑' γ', coeffFn (truncList c m) γ' * (if γ' = γ then (1 : ℝ) else 0) =
      coeffFn (truncList c m) γ := by
    rw [tsum_eq_single γ fun γ' hγ' => by rw [if_neg hγ', mul_zero], if_pos rfl, mul_one]
  have e : ((truncList c m).map fun s => s.2 * if s.1 = γ then (1 : ℝ) else 0) =
      (boxSet d m).toList.map fun γ' => c γ' * if γ' = γ then (1 : ℝ) else 0 := by
    unfold truncList; rw [List.map_map]; rfl
  rw [h2, e, CoeffFamily.sum_map_toList] at h
  rw [← h]
  unfold truncFamily
  simp_rw [mul_ite, mul_one, mul_zero]
  rw [Finset.sum_ite_eq']

end MonoRep

end Laplace.Grammar
