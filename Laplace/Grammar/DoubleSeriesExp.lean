/-
Copyright (c) 2026 Timaeus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Laplace.Grammar.DoubleSeriesConvolution

/-!
# The exponential of a double series (grammar §4.2, analytic bridge)

For a coefficient array `a` with vanishing constant term, the convolution powers `a^{*n}` vanish
below total degree `n`, so the exponential coefficients

  `E_k(t) = ∑_{n ≤ |k|} t^n/n! · (a^{*n})_k`   (`expCoeff`)

are finite sums. With `X = N_ρ(a)`: `N_ρ(a^{*n}) ≤ X^n`, the joint family
`(n, k) ↦ |t|^n/n! |(a^{*n})_k| ρ^{|k|}` is summable with majorant `(|t|X)^n/n!`, hence
`N_ρ(E(t)) ≤ e^{|t|X}` (`wnorm_expCoeff_le`), and evaluation gives
`∑_k E_k(t) u^i v^j = exp(t · ∑_k a_k u^i v^j)` for `|u|, |v| ≤ ρ` (`dblSum_expCoeff`). This is
module 2 of the coefficient closure for `η e^{βsξ}` (Astra #7(b)). Zero `sorry`/`axiom`.
-/

open Real

namespace Laplace.Grammar

/-- The unit of convolution: the array supported at `(0, 0)`. -/
def delta : ℕ × ℕ → ℝ := fun k => if k = (0, 0) then 1 else 0

theorem conv_delta (f : ℕ × ℕ → ℝ) : conv delta f = f := by
  funext k
  unfold conv
  rw [Finset.sum_eq_single (0, 0)]
  · simp [delta, psub]
  · intro b _ hb
    simp [delta, hb]
  · intro h
    exact absurd (mem_box.2 ⟨Nat.zero_le _, Nat.zero_le _⟩) h

theorem wsummable_delta (ρ : ℝ) : WSummable ρ delta := by
  unfold WSummable
  refine summable_of_ne_finset_zero (s := {(0, 0)}) fun k hk => ?_
  simp only [Finset.mem_singleton] at hk
  simp [delta, hk]

theorem wnorm_delta (ρ : ℝ) : wnorm ρ delta = 1 := by
  unfold wnorm
  rw [tsum_eq_sum (s := {(0, 0)}) fun k hk => by
    simp only [Finset.mem_singleton] at hk; simp [delta, hk]]
  simp [delta]

theorem dblSum_delta (u v : ℝ) : dblSum delta u v = 1 := by
  unfold dblSum
  rw [tsum_eq_sum (s := {(0, 0)}) fun k hk => by
    simp only [Finset.mem_singleton] at hk; simp [delta, hk]]
  simp [delta]

/-- Convolution powers `a^{*0} = δ`, `a^{*(n+1)} = a * a^{*n}`. -/
noncomputable def convPow (a : ℕ × ℕ → ℝ) : ℕ → (ℕ × ℕ → ℝ)
  | 0 => delta
  | n + 1 => conv a (convPow a n)

theorem wnorm_nonneg (ρ : ℝ) (hρ : 0 ≤ ρ) (f : ℕ × ℕ → ℝ) : 0 ≤ wnorm ρ f :=
  tsum_nonneg fun k => by positivity

/-- `N_ρ(a^{*n}) ≤ N_ρ(a)^n`, with weighted summability. -/
theorem wnorm_convPow_le (ρ : ℝ) (hρ : 0 < ρ) (a : ℕ × ℕ → ℝ) (ha : WSummable ρ a) (n : ℕ) :
    WSummable ρ (convPow a n) ∧ wnorm ρ (convPow a n) ≤ wnorm ρ a ^ n := by
  induction n with
  | zero => exact ⟨wsummable_delta ρ, by rw [convPow, wnorm_delta, pow_zero]⟩
  | succ n ih =>
    obtain ⟨hs, hle⟩ := wnorm_conv_le ρ hρ a (convPow a n) ha ih.1
    refine ⟨hs, hle.trans ?_⟩
    rw [pow_succ']
    exact mul_le_mul_of_nonneg_left ih.2 (wnorm_nonneg ρ hρ.le a)

/-- Evaluation of the powers. -/
theorem dblSum_convPow (ρ u v : ℝ) (hρ : 0 < ρ) (a : ℕ × ℕ → ℝ) (ha : WSummable ρ a)
    (hu : |u| ≤ ρ) (hv : |v| ≤ ρ) (n : ℕ) :
    dblSum (convPow a n) u v = dblSum a u v ^ n := by
  induction n with
  | zero => simp [convPow, dblSum_delta]
  | succ n ih =>
    rw [convPow, dblSum_conv ρ u v a (convPow a n) ha (wnorm_convPow_le ρ hρ a ha n).1 hu hv, ih,
      pow_succ, mul_comm]

/-- **Degree support**: with `a₀₀ = 0`, `(a^{*n})_k = 0` for `|k| < n`. -/
theorem convPow_eq_zero_of_lt (a : ℕ × ℕ → ℝ) (ha0 : a (0, 0) = 0) :
    ∀ n (k : ℕ × ℕ), k.1 + k.2 < n → convPow a n k = 0 := by
  intro n
  induction n with
  | zero => intro k hk; exact absurd hk (Nat.not_lt_zero _)
  | succ n ih =>
    intro k hk
    simp only [convPow, conv]
    refine Finset.sum_eq_zero fun b hb => ?_
    by_cases hb0 : b = (0, 0)
    · rw [hb0, ha0, zero_mul]
    · have hb' := mem_box.1 hb
      have hpos : 0 < b.1 + b.2 := by
        rcases Nat.eq_zero_or_pos (b.1 + b.2) with h | h
        · exfalso
          apply hb0
          ext <;> omega
        · exact h
      have : (psub k b).1 + (psub k b).2 < n := by
        simp only [psub]; omega
      rw [ih (psub k b) this, mul_zero]

/-- The exponential coefficients `E_k(t) = ∑_{n ≤ |k|} t^n/n! (a^{*n})_k`. -/
noncomputable def expCoeff (a : ℕ × ℕ → ℝ) (t : ℝ) (k : ℕ × ℕ) : ℝ :=
  ∑ n ∈ Finset.range (k.1 + k.2 + 1), t ^ n / (n.factorial : ℝ) * convPow a n k

theorem expCoeff_continuous (a : ℕ × ℕ → ℝ) (k : ℕ × ℕ) : Continuous fun t => expCoeff a t k := by
  unfold expCoeff
  exact continuous_finsetSum _ fun n _ => ((continuous_pow n).div_const _).mul continuous_const

/-- The real exponential as a power series. -/
theorem hasSum_exp_series (z : ℝ) :
    HasSum (fun n : ℕ => z ^ n / (n.factorial : ℝ)) (Real.exp z) := by
  have h := (Real.summable_pow_div_factorial z).hasSum
  rwa [show ∑' n : ℕ, z ^ n / (n.factorial : ℝ) = Real.exp z from by
    rw [Real.exp_eq_exp_ℝ, NormedSpace.exp_eq_tsum_div]] at h

/-- The exponential coefficient is the full series (the terms beyond `|k|` vanish). -/
theorem expCoeff_eq_tsum (a : ℕ × ℕ → ℝ) (ha0 : a (0, 0) = 0) (t : ℝ) (k : ℕ × ℕ) :
    expCoeff a t k = ∑' n : ℕ, t ^ n / (n.factorial : ℝ) * convPow a n k := by
  unfold expCoeff
  rw [tsum_eq_sum (s := Finset.range (k.1 + k.2 + 1))]
  intro n hn
  rw [Finset.mem_range, not_lt] at hn
  rw [convPow_eq_zero_of_lt a ha0 n k (by omega), mul_zero]

/-- The joint majorant `g(n,k) = |t|^n/n! |(a^{*n})_k| ρ^{|k|}`. -/
noncomputable def expMaj (ρ : ℝ) (a : ℕ × ℕ → ℝ) (t : ℝ) (p : ℕ × (ℕ × ℕ)) : ℝ :=
  |t| ^ p.1 / (p.1.factorial : ℝ) * (|convPow a p.1 p.2| * ρ ^ (p.2.1 + p.2.2))

theorem expMaj_nonneg (ρ : ℝ) (hρ : 0 < ρ) (a : ℕ × ℕ → ℝ) (t : ℝ) (p : ℕ × (ℕ × ℕ)) :
    0 ≤ expMaj ρ a t p := by
  unfold expMaj; positivity

/-- **Joint summability of the majorant**, with row sums bounded by `(|t| X)^n/n!`. -/
theorem expMaj_summable (ρ : ℝ) (hρ : 0 < ρ) (a : ℕ × ℕ → ℝ) (ha : WSummable ρ a) (t : ℝ) :
    Summable (expMaj ρ a t) ∧
      ∑' p, expMaj ρ a t p ≤ Real.exp (|t| * wnorm ρ a) := by
  have hrow : ∀ n, Summable fun k => expMaj ρ a t (n, k) := by
    intro n
    have h := (wnorm_convPow_le ρ hρ a ha n).1
    unfold WSummable at h
    exact (h.mul_left (|t| ^ n / (n.factorial : ℝ))).congr fun k => rfl
  have hrowsum : ∀ n, ∑' k, expMaj ρ a t (n, k)
      = |t| ^ n / (n.factorial : ℝ) * wnorm ρ (convPow a n) := by
    intro n
    unfold expMaj wnorm
    show ∑' k : ℕ × ℕ, |t| ^ n / (n.factorial : ℝ) * (|convPow a n k| * ρ ^ (k.1 + k.2)) = _
    rw [tsum_mul_left]
  have hrowle : ∀ n, ∑' k, expMaj ρ a t (n, k) ≤ (|t| * wnorm ρ a) ^ n / (n.factorial : ℝ) := by
    intro n
    rw [hrowsum n]
    have hf : (0 : ℝ) < n.factorial := Nat.cast_pos.2 (Nat.factorial_pos n)
    have e : (|t| * wnorm ρ a) ^ n / (n.factorial : ℝ)
        = |t| ^ n / (n.factorial : ℝ) * wnorm ρ a ^ n := by
      rw [mul_pow]; ring
    rw [e]
    exact mul_le_mul_of_nonneg_left (wnorm_convPow_le ρ hρ a ha n).2 (by positivity)
  have hexp := Real.summable_pow_div_factorial (|t| * wnorm ρ a)
  have hcol : Summable fun n => ∑' k, expMaj ρ a t (n, k) :=
    Summable.of_nonneg_of_le (fun n => tsum_nonneg fun k => expMaj_nonneg ρ hρ a t _) hrowle hexp
  have hs : Summable (expMaj ρ a t) :=
    (summable_prod_of_nonneg (expMaj_nonneg ρ hρ a t)).2 ⟨hrow, hcol⟩
  refine ⟨hs, ?_⟩
  rw [hs.tsum_prod]
  calc ∑' n, ∑' k, expMaj ρ a t (n, k)
      ≤ ∑' n : ℕ, (|t| * wnorm ρ a) ^ n / (n.factorial : ℝ) := hcol.tsum_le_tsum hrowle hexp
    _ = Real.exp (|t| * wnorm ρ a) := (hasSum_exp_series _).tsum_eq

/-- The pointwise bound `|E_k(t)| ρ^{|k|} ≤ ∑_n g(n,k)`. -/
theorem expCoeff_abs_le (ρ : ℝ) (hρ : 0 < ρ) (a : ℕ × ℕ → ℝ) (ha : WSummable ρ a)
    (ha0 : a (0, 0) = 0) (t : ℝ) (k : ℕ × ℕ) :
    |expCoeff a t k| * ρ ^ (k.1 + k.2) ≤ ∑' n, expMaj ρ a t (n, k) := by
  obtain ⟨hs, -⟩ := expMaj_summable ρ hρ a ha t
  have hs' : Summable fun q : (ℕ × ℕ) × ℕ => expMaj ρ a t (q.2, q.1) := hs.prod_symm
  have hcol : Summable fun n => expMaj ρ a t (n, k) :=
    ((summable_prod_of_nonneg fun q => expMaj_nonneg ρ hρ a t _).1 hs').1 k
  rw [expCoeff_eq_tsum a ha0 t k, ← abs_of_pos (pow_pos hρ (k.1 + k.2)), ← abs_mul,
    ← tsum_mul_right]
  have hnorm : Summable fun n => ‖t ^ n / (n.factorial : ℝ) * convPow a n k * ρ ^ (k.1 + k.2)‖ := by
    refine hcol.congr fun n => ?_
    simp only [expMaj, Real.norm_eq_abs, abs_mul, abs_div, abs_pow, abs_of_pos hρ, Nat.abs_cast]
    ring
  refine (norm_tsum_le_tsum_norm hnorm).trans (le_of_eq ?_)
  refine tsum_congr fun n => ?_
  simp only [expMaj, Real.norm_eq_abs, abs_mul, abs_div, abs_pow, abs_of_pos hρ, Nat.abs_cast]
  ring

/-- **The weighted norm of the exponential**: `N_ρ(E(t)) ≤ e^{|t| N_ρ(a)}`, with weighted
summability. -/
theorem wnorm_expCoeff_le (ρ : ℝ) (hρ : 0 < ρ) (a : ℕ × ℕ → ℝ) (ha : WSummable ρ a)
    (ha0 : a (0, 0) = 0) (t : ℝ) :
    WSummable ρ (expCoeff a t) ∧ wnorm ρ (expCoeff a t) ≤ Real.exp (|t| * wnorm ρ a) := by
  obtain ⟨hs, hle⟩ := expMaj_summable ρ hρ a ha t
  have hs' : Summable fun q : (ℕ × ℕ) × ℕ => expMaj ρ a t (q.2, q.1) := hs.prod_symm
  have hG : Summable fun k => ∑' n, expMaj ρ a t (n, k) :=
    ((summable_prod_of_nonneg fun q => expMaj_nonneg ρ hρ a t _).1 hs').2
  have hpt := expCoeff_abs_le ρ hρ a ha ha0 t
  have hW : WSummable ρ (expCoeff a t) :=
    Summable.of_nonneg_of_le (fun k => by positivity) hpt hG
  refine ⟨hW, ?_⟩
  calc wnorm ρ (expCoeff a t) ≤ ∑' k, ∑' n, expMaj ρ a t (n, k) := hW.tsum_le_tsum hpt hG
    _ = ∑' q : (ℕ × ℕ) × ℕ, expMaj ρ a t (q.2, q.1) := (hs'.tsum_prod).symm
    _ = ∑' p, expMaj ρ a t p := (Equiv.prodComm (ℕ × ℕ) ℕ).tsum_eq (expMaj ρ a t)
    _ ≤ _ := hle

/-- **Evaluation of the exponential**: `∑_k E_k(t) u^i v^j = exp(t · ∑_k a_k u^i v^j)` for
`|u|, |v| ≤ ρ`. -/
theorem dblSum_expCoeff (ρ u v : ℝ) (hρ : 0 < ρ) (a : ℕ × ℕ → ℝ) (ha : WSummable ρ a)
    (ha0 : a (0, 0) = 0) (hu : |u| ≤ ρ) (hv : |v| ≤ ρ) (t : ℝ) :
    dblSum (expCoeff a t) u v = Real.exp (t * dblSum a u v) := by
  obtain ⟨hs, -⟩ := expMaj_summable ρ hρ a ha t
  -- the signed joint family and its domination by the majorant
  set F : ℕ × (ℕ × ℕ) → ℝ :=
    fun p => t ^ p.1 / (p.1.factorial : ℝ) * convPow a p.1 p.2 * u ^ p.2.1 * v ^ p.2.2 with hF
  have hFle : ∀ p, ‖F p‖ ≤ expMaj ρ a t p := by
    intro p
    simp only [hF, expMaj, Real.norm_eq_abs, abs_mul, abs_div, abs_pow, Nat.abs_cast]
    have h1 : |u| ^ p.2.1 * |v| ^ p.2.2 ≤ ρ ^ (p.2.1 + p.2.2) := by
      rw [pow_add]
      exact mul_le_mul (pow_le_pow_left₀ (abs_nonneg _) hu _) (pow_le_pow_left₀ (abs_nonneg _) hv _)
        (by positivity) (by positivity)
    calc |t| ^ p.1 / (p.1.factorial : ℝ) * |convPow a p.1 p.2| * |u| ^ p.2.1 * |v| ^ p.2.2
        = |t| ^ p.1 / (p.1.factorial : ℝ) * |convPow a p.1 p.2| * (|u| ^ p.2.1 * |v| ^ p.2.2) := by
          ring
      _ ≤ |t| ^ p.1 / (p.1.factorial : ℝ) * |convPow a p.1 p.2| * ρ ^ (p.2.1 + p.2.2) :=
          mul_le_mul_of_nonneg_left h1 (by positivity)
      _ = _ := by ring
  have hFs : Summable F := Summable.of_norm_bounded hs hFle
  have hFrow : ∀ n, Summable fun k => F (n, k) := fun n => hFs.prod_factor n
  have hFcol : ∀ k, Summable fun n => F (n, k) := fun k => hFs.prod_symm.prod_factor k
  -- the evaluation of `E(t)` as the iterated sum in the order `k`, then `n`
  have h1 : dblSum (expCoeff a t) u v = ∑' k, ∑' n, F (n, k) := by
    unfold dblSum
    refine tsum_congr fun k => ?_
    rw [expCoeff_eq_tsum a ha0 t k, ← tsum_mul_right, ← tsum_mul_right]
  -- interchange and evaluate the powers
  have h2 : ∑' k, ∑' n, F (n, k) = ∑' n, ∑' k, F (n, k) := by
    have := hFs.tsum_comm' (f := fun n k => F (n, k)) hFrow hFcol
    exact this
  have h3 : ∀ n, ∑' k, F (n, k) = t ^ n / (n.factorial : ℝ) * dblSum a u v ^ n := by
    intro n
    rw [← dblSum_convPow ρ u v hρ a ha hu hv n]
    unfold dblSum
    rw [← tsum_mul_left]
    exact tsum_congr fun k => by simp only [hF]; ring
  rw [h1, h2, tsum_congr h3, ← (hasSum_exp_series (t * dblSum a u v)).tsum_eq]
  try exact tsum_congr fun n => by rw [mul_pow]; ring

end Laplace.Grammar
