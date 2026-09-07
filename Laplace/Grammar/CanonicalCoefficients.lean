/-
Copyright (c) 2026 Timaeus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Laplace.Grammar.LogMerge

/-!
# Canonical (cutoff-independent) coefficients of the `d = 2` expansion (grammar §4.2)

The face finite parts `FP^M_γ` of the reduced expansion carry a truncation order `M`. For `γ < M`
the value does not depend on `M` (`axisFinitePart_indep`): passing from `M` to `M+1` subtracts
`f_M v^M` under the regularised integral and adds `f_M · axisPrim γ b M`, and
`∫₀^b v^{M−1−γ} dv = axisPrim γ b M`. Hence canonical finite parts at the truncation order
`canonicalM γ = ⌈max γ 0⌉₊ + 1` (`faceFPCoeff_anaFaceU_canonical`, `_anaFaceV_`).

With `uExp h₁ k₁ i = (h₁+i+1)/k₁`, `vExp h₂ k₂ j = (h₂+j+1)/k₂` and the inverse index maps
`uIdx`, `vIdx`, we define the canonical coefficient FUNCTIONS of `s` at an exponent `α`
(`canonU`, `canonV`, `canonC`) and the pole coefficients `canonA α = M[α;0;C_α]`,
`canonB α = M[α;0;U_α] + M[α;0;V_α] − M[α;1;C_α]`, so that
`N^{−α}(A_α log N + B_α) = N^{−α}M[α;0;U_α] + N^{−α}M[α;0;V_α] + transferTerm(α, C_α)`
(`canon_term_eq`). Astra #8 rank 1. Zero `sorry`/`axiom`.
-/

open Real MeasureTheory Set Filter Asymptotics

namespace Laplace.Grammar

/-- `∫₀^b v^c dv = b^{c+1}/(c+1)` for `c > −1`. -/
theorem integral_rpow_Ioc_zero (b c : ℝ) (hb : 0 < b) (hc : -1 < c) :
    ∫ v in Ioc (0 : ℝ) b, v ^ c = b ^ (c + 1) / (c + 1) := by
  rw [← intervalIntegral.integral_of_le hb.le, integral_rpow (Or.inl hc),
    Real.zero_rpow (by linarith), sub_zero]

/-- Passing from truncation order `M` to `M+1` does not change the finite part. -/
theorem axisFinitePart_succ (γ b H : ℝ) (M : ℕ) (hM : γ < M) (hb : 0 < b) (f : ℝ → ℝ)
    (fm : ℕ → ℝ) (hf : Measurable f)
    (hrem : ∀ v ∈ Ioc (0 : ℝ) b, |taylorRem f fm M v| ≤ H * v ^ M) :
    axisFinitePart γ b f fm (M + 1) = axisFinitePart γ b f fm M := by
  have hR := weighted_taylorRem_integrableOn γ b H M hM f fm hf hrem
  have hpow : IntegrableOn (fun v : ℝ => v ^ ((M : ℝ) - 1 - γ)) (Ioc 0 b) :=
    (intervalIntegral.intervalIntegrable_rpow' (a := 0) (b := b) (by linarith)).1
  have hrem1 : ∀ v, taylorRem f fm (M + 1) v = taylorRem f fm M v - fm M * v ^ M := by
    intro v
    unfold taylorRem
    rw [Finset.sum_range_succ]
    ring
  have hint : ∀ v ∈ Ioc (0 : ℝ) b,
      v ^ (-1 - γ) * taylorRem f fm (M + 1) v
        = v ^ (-1 - γ) * taylorRem f fm M v - fm M * v ^ ((M : ℝ) - 1 - γ) := by
    intro v hv
    rw [hrem1, show ((M : ℝ) - 1 - γ) = (M : ℝ) + (-1 - γ) by ring, Real.rpow_add hv.1,
      Real.rpow_natCast]
    ring
  have hM' : (M : ℝ) ≠ γ := ne_of_gt hM
  unfold axisFinitePart regAxisIntegral
  rw [setIntegral_congr_fun measurableSet_Ioc hint, integral_sub hR (hpow.const_mul _),
    integral_const_mul, integral_rpow_Ioc_zero b _ hb (by linarith), Finset.sum_range_succ]
  unfold axisPrim
  rw [if_neg hM', show (M : ℝ) - 1 - γ + 1 = (M : ℝ) - γ by ring]
  ring

/-- **Cutoff independence of the finite part**: for `γ < M ≤ M'` and remainder envelopes at every
order, `FP^{M'}_γ = FP^M_γ`. -/
theorem axisFinitePart_indep (γ b : ℝ) (M M' : ℕ) (hM : γ < M) (hMM' : M ≤ M') (hb : 0 < b)
    (f : ℝ → ℝ) (fm : ℕ → ℝ) (hf : Measurable f) (H : ℕ → ℝ)
    (hrem : ∀ n, ∀ v ∈ Ioc (0 : ℝ) b, |taylorRem f fm n v| ≤ H n * v ^ n) :
    axisFinitePart γ b f fm M' = axisFinitePart γ b f fm M := by
  induction M', hMM' using Nat.le_induction with
  | base => rfl
  | succ n hn ih =>
    rw [axisFinitePart_succ γ b (H n) n (by
      have : (M : ℝ) ≤ n := by exact_mod_cast hn
      linarith) hb f fm hf (hrem n), ih]

/-- The canonical truncation order `⌈max γ 0⌉₊ + 1 > γ`. -/
noncomputable def canonicalM (γ : ℝ) : ℕ := ⌈max γ 0⌉₊ + 1

theorem lt_canonicalM (γ : ℝ) : γ < canonicalM γ := by
  unfold canonicalM
  push_cast
  have := Nat.le_ceil (max γ 0)
  linarith [le_max_left γ 0]

/-- Taylor remainders of the analytic `u`-faces at every order. -/
theorem anaFaceU_taylorRem_le (c : ℕ × ℕ → ℝ → ℝ) (b ρ : ℝ) (H : ℝ → ℝ) (hb : 0 < b)
    (hbρ : b < ρ) (hc : ∀ ij s, |c ij s| * ρ ^ (ij.1 + ij.2) ≤ H s) (i : ℕ) (s : ℝ) (M : ℕ) :
    ∀ v ∈ Ioc (0 : ℝ) b, |taylorRem (fun v => anaFaceU c b i v s) (fun m => c (i, m) s) M v|
      ≤ H s * (ρ ^ i)⁻¹ * (ρ ^ M)⁻¹ / (1 - b / ρ) * v ^ M :=
  fun v hv => anaFaceU_rem c b ρ H hb hbρ hc i M v s hv

theorem anaFaceV_taylorRem_le (c : ℕ × ℕ → ℝ → ℝ) (b ρ : ℝ) (H : ℝ → ℝ) (hb : 0 < b)
    (hbρ : b < ρ) (hc : ∀ ij s, |c ij s| * ρ ^ (ij.1 + ij.2) ≤ H s) (j : ℕ) (s : ℝ) (M : ℕ) :
    ∀ u ∈ Ioc (0 : ℝ) b, |taylorRem (fun u => anaFaceV c b j u s) (fun m => c (m, j) s) M u|
      ≤ H s * (ρ ^ j)⁻¹ * (ρ ^ M)⁻¹ / (1 - b / ρ) * u ^ M :=
  fun u hu => anaFaceV_rem c b ρ H hb hbρ hc j M u s hu

/-- The `u`-face finite-part coefficient at any admissible order equals the canonical one. -/
theorem faceFPCoeff_anaFaceU_canonical (c : ℕ × ℕ → ℝ → ℝ) (b ρ γ : ℝ) (H : ℝ → ℝ) (hb : 0 < b)
    (hbρ : b < ρ) (hcc : ∀ ij, Continuous (c ij)) (hH : Continuous H)
    (hc : ∀ ij s, |c ij s| * ρ ^ (ij.1 + ij.2) ≤ H s) (k : ℕ) (i M : ℕ) (hM : γ < M) :
    faceFPCoeff γ b k (anaFaceU c b i) (fun m => c (i, m)) M
      = faceFPCoeff γ b k (anaFaceU c b i) (fun m => c (i, m)) (canonicalM γ) := by
  funext s
  unfold faceFPCoeff
  have hmeas : Measurable fun v => anaFaceU c b i v s :=
    ((anaFaceU_continuous c b ρ H hb hbρ hcc hH hc i).comp
      (Continuous.prodMk continuous_id continuous_const)).measurable
  have hcan := lt_canonicalM γ
  rcases le_total M (canonicalM γ) with h | h
  · rw [axisFinitePart_indep γ b M (canonicalM γ) hM h hb _ _ hmeas _
      (fun n => anaFaceU_taylorRem_le c b ρ H hb hbρ hc i s n)]
  · rw [axisFinitePart_indep γ b (canonicalM γ) M hcan h hb _ _ hmeas _
      (fun n => anaFaceU_taylorRem_le c b ρ H hb hbρ hc i s n)]

theorem faceFPCoeff_anaFaceV_canonical (c : ℕ × ℕ → ℝ → ℝ) (b ρ γ : ℝ) (H : ℝ → ℝ) (hb : 0 < b)
    (hbρ : b < ρ) (hcc : ∀ ij, Continuous (c ij)) (hH : Continuous H)
    (hc : ∀ ij s, |c ij s| * ρ ^ (ij.1 + ij.2) ≤ H s) (k : ℕ) (j M : ℕ) (hM : γ < M) :
    faceFPCoeff γ b k (anaFaceV c b j) (fun m => c (m, j)) M
      = faceFPCoeff γ b k (anaFaceV c b j) (fun m => c (m, j)) (canonicalM γ) := by
  funext s
  unfold faceFPCoeff
  have hmeas : Measurable fun u => anaFaceV c b j u s :=
    ((anaFaceV_continuous c b ρ H hb hbρ hcc hH hc j).comp
      (Continuous.prodMk continuous_id continuous_const)).measurable
  have hcan := lt_canonicalM γ
  rcases le_total M (canonicalM γ) with h | h
  · rw [axisFinitePart_indep γ b M (canonicalM γ) hM h hb _ _ hmeas _
      (fun n => anaFaceV_taylorRem_le c b ρ H hb hbρ hc j s n)]
  · rw [axisFinitePart_indep γ b (canonicalM γ) M hcan h hb _ _ hmeas _
      (fun n => anaFaceV_taylorRem_le c b ρ H hb hbρ hc j s n)]

/-- The `v`-face exponent `(h₂+j+1)/k₂`. -/
noncomputable def vExp (h₂ k₂ j : ℕ) : ℝ := (((h₂ + j : ℕ) : ℝ) + 1) / k₂

/-- The inverse index map `α ↦ ⌊k₁α − h₁ − 1⌋₊` (recovers `i` from `uExp h₁ k₁ i`). -/
noncomputable def uIdx (h₁ k₁ : ℕ) (α : ℝ) : ℕ := ⌊(k₁ : ℝ) * α - h₁ - 1⌋₊

noncomputable def vIdx (h₂ k₂ : ℕ) (α : ℝ) : ℕ := ⌊(k₂ : ℝ) * α - h₂ - 1⌋₊

theorem uIdx_uExp (h₁ k₁ : ℕ) (hk₁ : 0 < k₁) (i : ℕ) : uIdx h₁ k₁ (uExp h₁ k₁ i) = i := by
  unfold uIdx uExp
  have hk : (k₁ : ℝ) ≠ 0 := by positivity
  rw [mul_div_cancel₀ _ hk]
  push_cast
  rw [show (h₁ : ℝ) + i + 1 - h₁ - 1 = (i : ℝ) by ring, Nat.floor_natCast]

theorem vIdx_vExp (h₂ k₂ : ℕ) (hk₂ : 0 < k₂) (j : ℕ) : vIdx h₂ k₂ (vExp h₂ k₂ j) = j := by
  unfold vIdx vExp
  have hk : (k₂ : ℝ) ≠ 0 := by positivity
  rw [mul_div_cancel₀ _ hk]
  push_cast
  rw [show (h₂ : ℝ) + j + 1 - h₂ - 1 = (j : ℝ) by ring, Nat.floor_natCast]

/-- `α` is a `u`-pole iff it is `uExp` of its recovered index. -/
theorem uExp_uIdx_iff (h₁ k₁ : ℕ) (hk₁ : 0 < k₁) (α : ℝ) :
    uExp h₁ k₁ (uIdx h₁ k₁ α) = α ↔ ∃ i, uExp h₁ k₁ i = α := by
  constructor
  · intro h; exact ⟨_, h⟩
  · rintro ⟨i, rfl⟩; rw [uIdx_uExp h₁ k₁ hk₁ i]

theorem vExp_vIdx_iff (h₂ k₂ : ℕ) (hk₂ : 0 < k₂) (α : ℝ) :
    vExp h₂ k₂ (vIdx h₂ k₂ α) = α ↔ ∃ j, vExp h₂ k₂ j = α := by
  constructor
  · intro h; exact ⟨_, h⟩
  · rintro ⟨j, rfl⟩; rw [vIdx_vExp h₂ k₂ hk₂ j]

/-- The canonical `u`-face coefficient function at exponent `α`:
`k₁⁻¹ FP_{k₂α−h₂−1}(a_i(·, s))` if `α = α_i`, else `0`. -/
noncomputable def canonU (b : ℝ) (h₁ h₂ k₁ k₂ : ℕ) (a : ℕ → ℝ → ℝ → ℝ) (c : ℕ → ℕ → ℝ → ℝ)
    (α : ℝ) : ℝ → ℝ :=
  if uExp h₁ k₁ (uIdx h₁ k₁ α) = α then
    faceFPCoeff ((k₂ : ℝ) * α - h₂ - 1) b k₁ (a (uIdx h₁ k₁ α)) (fun m => c (uIdx h₁ k₁ α) m)
      (canonicalM ((k₂ : ℝ) * α - h₂ - 1))
  else fun _ => 0

/-- The canonical `v`-face coefficient function at exponent `α`. -/
noncomputable def canonV (b : ℝ) (h₁ h₂ k₁ k₂ : ℕ) (bj : ℕ → ℝ → ℝ → ℝ) (c : ℕ → ℕ → ℝ → ℝ)
    (α : ℝ) : ℝ → ℝ :=
  if vExp h₂ k₂ (vIdx h₂ k₂ α) = α then
    faceFPCoeff ((k₁ : ℝ) * α - h₁ - 1) b k₂ (bj (vIdx h₂ k₂ α)) (fun m => c m (vIdx h₂ k₂ α))
      (canonicalM ((k₁ : ℝ) * α - h₁ - 1))
  else fun _ => 0

/-- The canonical collision coefficient `c_ij/(k₁k₂)` at `α = α_i = δ_j`, else `0`. -/
noncomputable def canonC (h₁ h₂ k₁ k₂ : ℕ) (c : ℕ → ℕ → ℝ → ℝ) (α : ℝ) : ℝ → ℝ :=
  if uExp h₁ k₁ (uIdx h₁ k₁ α) = α ∧ vExp h₂ k₂ (vIdx h₂ k₂ α) = α then
    fun s => c (uIdx h₁ k₁ α) (vIdx h₂ k₂ α) s / ((k₁ : ℝ) * k₂)
  else fun _ => 0

/-- The canonical log coefficient `A_α = M[α; 0; C_α]`. -/
noncomputable def canonA (β : ℝ) (h₁ h₂ k₁ k₂ : ℕ) (c : ℕ → ℕ → ℝ → ℝ) (α : ℝ) : ℝ :=
  logMoment β α 0 (canonC h₁ h₂ k₁ k₂ c α)

/-- The canonical constant coefficient `B_α = M[α;0;U_α] + M[α;0;V_α] − M[α;1;C_α]`. -/
noncomputable def canonB (β b : ℝ) (h₁ h₂ k₁ k₂ : ℕ) (a bj : ℕ → ℝ → ℝ → ℝ)
    (c : ℕ → ℕ → ℝ → ℝ) (α : ℝ) : ℝ :=
  logMoment β α 0 (canonU b h₁ h₂ k₁ k₂ a c α) + logMoment β α 0 (canonV b h₁ h₂ k₁ k₂ bj c α)
    - logMoment β α 1 (canonC h₁ h₂ k₁ k₂ c α)

/-- **The canonical pole term** equals the three grouped contributions. -/
theorem canon_term_eq (β b : ℝ) (h₁ h₂ k₁ k₂ : ℕ) (a bj : ℕ → ℝ → ℝ → ℝ) (c : ℕ → ℕ → ℝ → ℝ)
    (α N : ℝ) :
    N ^ (-α) * (canonA β h₁ h₂ k₁ k₂ c α * Real.log N + canonB β b h₁ h₂ k₁ k₂ a bj c α)
      = N ^ (-α) * logMoment β α 0 (canonU b h₁ h₂ k₁ k₂ a c α)
        + N ^ (-α) * logMoment β α 0 (canonV b h₁ h₂ k₁ k₂ bj c α)
        + transferTerm β α 1 (canonC h₁ h₂ k₁ k₂ c α) N := by
  rw [transferTerm_one]
  unfold canonA canonB
  ring

/-- `canonU` at a `u`-pole `α_i`. -/
theorem canonU_uExp (b : ℝ) (h₁ h₂ k₁ k₂ : ℕ) (hk₁ : 0 < k₁) (a : ℕ → ℝ → ℝ → ℝ)
    (c : ℕ → ℕ → ℝ → ℝ) (i : ℕ) :
    canonU b h₁ h₂ k₁ k₂ a c (uExp h₁ k₁ i)
      = faceFPCoeff ((k₂ : ℝ) * uExp h₁ k₁ i - h₂ - 1) b k₁ (a i) (fun m => c i m)
          (canonicalM ((k₂ : ℝ) * uExp h₁ k₁ i - h₂ - 1)) := by
  unfold canonU
  rw [uIdx_uExp h₁ k₁ hk₁ i, if_pos rfl]

/-- `canonU` vanishes off the `u`-poles. -/
theorem canonU_of_not (b : ℝ) (h₁ h₂ k₁ k₂ : ℕ) (a : ℕ → ℝ → ℝ → ℝ)
    (c : ℕ → ℕ → ℝ → ℝ) (α : ℝ) (h : ∀ i, uExp h₁ k₁ i ≠ α) :
    canonU b h₁ h₂ k₁ k₂ a c α = fun _ => 0 := by
  unfold canonU
  rw [if_neg]
  intro h'
  exact h _ h'

theorem canonV_vExp (b : ℝ) (h₁ h₂ k₁ k₂ : ℕ) (hk₂ : 0 < k₂) (bj : ℕ → ℝ → ℝ → ℝ)
    (c : ℕ → ℕ → ℝ → ℝ) (j : ℕ) :
    canonV b h₁ h₂ k₁ k₂ bj c (vExp h₂ k₂ j)
      = faceFPCoeff ((k₁ : ℝ) * vExp h₂ k₂ j - h₁ - 1) b k₂ (bj j) (fun m => c m j)
          (canonicalM ((k₁ : ℝ) * vExp h₂ k₂ j - h₁ - 1)) := by
  unfold canonV
  rw [vIdx_vExp h₂ k₂ hk₂ j, if_pos rfl]

theorem canonV_of_not (b : ℝ) (h₁ h₂ k₁ k₂ : ℕ) (bj : ℕ → ℝ → ℝ → ℝ)
    (c : ℕ → ℕ → ℝ → ℝ) (α : ℝ) (h : ∀ j, vExp h₂ k₂ j ≠ α) :
    canonV b h₁ h₂ k₁ k₂ bj c α = fun _ => 0 := by
  unfold canonV
  rw [if_neg]
  intro h'
  exact h _ h'

/-- `canonC` at a collision `α_i = δ_j`. -/
theorem canonC_collision (h₁ h₂ k₁ k₂ : ℕ) (hk₁ : 0 < k₁) (hk₂ : 0 < k₂) (c : ℕ → ℕ → ℝ → ℝ)
    (i j : ℕ) (hij : uExp h₁ k₁ i = vExp h₂ k₂ j) :
    canonC h₁ h₂ k₁ k₂ c (uExp h₁ k₁ i) = fun s => c i j s / ((k₁ : ℝ) * k₂) := by
  unfold canonC
  rw [uIdx_uExp h₁ k₁ hk₁ i, hij, vIdx_vExp h₂ k₂ hk₂ j, ← hij, if_pos ⟨rfl, rfl⟩]

/-- `canonC` at a `u`-pole that is not a `v`-pole vanishes. -/
theorem canonC_uExp_of_not (h₁ h₂ k₁ k₂ : ℕ) (c : ℕ → ℕ → ℝ → ℝ) (i : ℕ)
    (h : ∀ j, vExp h₂ k₂ j ≠ uExp h₁ k₁ i) :
    canonC h₁ h₂ k₁ k₂ c (uExp h₁ k₁ i) = fun _ => 0 := by
  unfold canonC
  rw [if_neg]
  rintro ⟨-, h'⟩
  exact h _ h'

/-- `canonC` vanishes off the `u`-poles. -/
theorem canonC_of_not (h₁ h₂ k₁ k₂ : ℕ) (c : ℕ → ℕ → ℝ → ℝ) (α : ℝ)
    (h : ∀ i, uExp h₁ k₁ i ≠ α) :
    canonC h₁ h₂ k₁ k₂ c α = fun _ => 0 := by
  unfold canonC
  rw [if_neg]
  rintro ⟨h', -⟩
  exact h _ h'

end Laplace.Grammar
