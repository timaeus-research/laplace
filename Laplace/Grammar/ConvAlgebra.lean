/-
Copyright (c) 2026 Timaeus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Laplace.Grammar.CoeffDifference

/-!
# Linear algebra of the weighted convolution and the exponential difference (grammar §4.2, R6)

Bilinearity of `conv`, closure of weighted summability under sums and differences, the triangle
inequality for `wnorm`, and two Lipschitz estimates in the coefficient Banach algebra:

* `wnorm_convPow_sub_le`: `‖a^{*n} − a'^{*n}‖_ρ ≤ n M^{n−1} ‖a − a'‖_ρ` for `‖a‖_ρ, ‖a'‖_ρ ≤ M`
  (telescoping `a^{*(n+1)} − a'^{*(n+1)} = (a − a') * a^{*n} + a' * (a^{*n} − a'^{*n})`);
* `wnorm_expCoeff_sub_le`: `‖E_a(t) − E_{a'}(t)‖_ρ ≤ |t| e^{|t| M} ‖a − a'‖_ρ` (joint majorant with
  row sums `|t|^n/n! · n M^{n−1} ‖a − a'‖`, summing to `|t| e^{|t|M} ‖a − a'‖`).

These are the ingredients of the local Lipschitz estimate for the amplitude coefficient map
`(x, y) ↦ ampCoeff β x y` (Astra #10 rank 5). Zero `sorry`/`axiom`.
-/

open Real MeasureTheory Set Filter Asymptotics

namespace Laplace.Grammar

/-- `conv` is linear in the left slot. -/
theorem conv_sub_left (f g h : ℕ × ℕ → ℝ) :
    conv (fun k => f k - g k) h = fun k => conv f h k - conv g h k := by
  funext k
  unfold conv
  rw [← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun a _ => ?_
  ring

/-- `conv` is linear in the right slot. -/
theorem conv_sub_right (f g h : ℕ × ℕ → ℝ) :
    conv f (fun k => g k - h k) = fun k => conv f g k - conv f h k := by
  funext k
  unfold conv
  rw [← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun a _ => ?_
  ring

/-- `delta` is a right unit for `conv`. -/
theorem conv_delta_right (f : ℕ × ℕ → ℝ) : conv f delta = f := by
  funext k
  unfold conv
  rw [Finset.sum_eq_single k]
  · simp [delta, psub]
  · intro a ha hne
    have hmem := mem_box.1 ha
    have : psub k a ≠ (0, 0) := by
      intro h0
      apply hne
      simp only [psub, Prod.mk.injEq] at h0
      ext <;> omega
    simp [delta, this]
  · intro hk
    exact absurd (mem_box.2 ⟨le_rfl, le_rfl⟩) hk

theorem convPow_one (a : ℕ × ℕ → ℝ) : convPow a 1 = a := by
  show conv a (convPow a 0) = a
  rw [show convPow a 0 = delta from rfl, conv_delta_right]

theorem wsummable_add (ρ : ℝ) (hρ : 0 ≤ ρ) (f g : ℕ × ℕ → ℝ) (hf : WSummable ρ f)
    (hg : WSummable ρ g) : WSummable ρ (fun k => f k + g k) := by
  unfold WSummable at *
  refine Summable.of_nonneg_of_le (fun k => by positivity) (fun k => ?_) (hf.add hg)
  rw [← add_mul]
  exact mul_le_mul_of_nonneg_right (abs_add_le _ _) (by positivity)

theorem wsummable_sub (ρ : ℝ) (hρ : 0 ≤ ρ) (f g : ℕ × ℕ → ℝ) (hf : WSummable ρ f)
    (hg : WSummable ρ g) : WSummable ρ (fun k => f k - g k) := by
  unfold WSummable at *
  refine Summable.of_nonneg_of_le (fun k => by positivity) (fun k => ?_) (hf.add hg)
  rw [← add_mul]
  exact mul_le_mul_of_nonneg_right (abs_sub _ _) (by positivity)

/-- The triangle inequality for the weighted norm. -/
theorem wnorm_add_le (ρ : ℝ) (hρ : 0 ≤ ρ) (f g : ℕ × ℕ → ℝ) (hf : WSummable ρ f)
    (hg : WSummable ρ g) : wnorm ρ (fun k => f k + g k) ≤ wnorm ρ f + wnorm ρ g := by
  have hfg := wsummable_add ρ hρ f g hf hg
  unfold WSummable at hf hg hfg
  unfold wnorm
  rw [← hf.tsum_add hg]
  refine hfg.tsum_le_tsum (fun k => ?_) (hf.add hg)
  rw [← add_mul]
  exact mul_le_mul_of_nonneg_right (abs_add_le _ _) (by positivity)

theorem wnorm_zero_fun (ρ : ℝ) : wnorm ρ (fun _ => (0 : ℝ)) = 0 := by simp [wnorm]

theorem wsummable_zero_fun (ρ : ℝ) : WSummable ρ (fun _ => (0 : ℝ)) := by
  unfold WSummable; simp

/-- **Telescoping bound for convolution powers**:
`‖a^{*(n+1)} − a'^{*(n+1)}‖ ≤ (n+1) M^n ‖a − a'‖`. -/
theorem wnorm_convPow_succ_sub_le (ρ : ℝ) (hρ : 0 < ρ) (a a' : ℕ × ℕ → ℝ) (ha : WSummable ρ a)
    (ha' : WSummable ρ a') (M : ℝ) (hM : wnorm ρ a ≤ M) (hM' : wnorm ρ a' ≤ M) (n : ℕ) :
    WSummable ρ (fun k => convPow a (n + 1) k - convPow a' (n + 1) k) ∧
      wnorm ρ (fun k => convPow a (n + 1) k - convPow a' (n + 1) k)
        ≤ ((n : ℝ) + 1) * M ^ n * wnorm ρ (fun k => a k - a' k) := by
  have hM0 : 0 ≤ M := le_trans (wnorm_nonneg ρ hρ.le a) hM
  have hd := wsummable_sub ρ hρ.le a a' ha ha'
  have hD0 : 0 ≤ wnorm ρ (fun k => a k - a' k) := wnorm_nonneg ρ hρ.le _
  induction n with
  | zero =>
    rw [convPow_one, convPow_one]
    refine ⟨hd, ?_⟩
    simp
  | succ n ih =>
    -- the telescoping identity
    have hid : (fun k => convPow a (n + 1 + 1) k - convPow a' (n + 1 + 1) k)
        = fun k => conv (fun k => a k - a' k) (convPow a (n + 1)) k
          + conv a' (fun k => convPow a (n + 1) k - convPow a' (n + 1) k) k := by
      funext k
      rw [conv_sub_right, conv_sub_left]
      show conv a (convPow a (n + 1)) k - conv a' (convPow a' (n + 1)) k = _
      ring
    have hP := wnorm_convPow_le ρ hρ a ha (n + 1)
    have h1 := wnorm_conv_le ρ hρ (fun k => a k - a' k) (convPow a (n + 1)) hd hP.1
    have h2 := wnorm_conv_le ρ hρ a' _ ha' ih.1
    rw [hid]
    refine ⟨wsummable_add ρ hρ.le _ _ h1.1 h2.1, ?_⟩
    have hMn : wnorm ρ (convPow a (n + 1)) ≤ M ^ (n + 1) :=
      hP.2.trans (pow_le_pow_left₀ (wnorm_nonneg ρ hρ.le a) hM (n + 1))
    calc wnorm ρ (fun k => conv (fun k => a k - a' k) (convPow a (n + 1)) k
            + conv a' (fun k => convPow a (n + 1) k - convPow a' (n + 1) k) k)
        ≤ wnorm ρ (conv (fun k => a k - a' k) (convPow a (n + 1)))
          + wnorm ρ (conv a' (fun k => convPow a (n + 1) k - convPow a' (n + 1) k)) :=
          wnorm_add_le ρ hρ.le _ _ h1.1 h2.1
      _ ≤ wnorm ρ (fun k => a k - a' k) * M ^ (n + 1)
          + M * (((n : ℝ) + 1) * M ^ n * wnorm ρ (fun k => a k - a' k)) := by
          gcongr
          · exact h1.2.trans (mul_le_mul_of_nonneg_left hMn hD0)
          · exact h2.2.trans (mul_le_mul hM' ih.2 (wnorm_nonneg ρ hρ.le _) hM0)
      _ = (((n + 1 : ℕ) : ℝ) + 1) * M ^ (n + 1) * wnorm ρ (fun k => a k - a' k) := by
          push_cast; ring

/-- The row bound of the exponential difference majorant. -/
noncomputable def expDiffRow (t M D : ℝ) (n : ℕ) : ℝ :=
  if n = 0 then 0 else |t| ^ n / (n.factorial : ℝ) * ((n : ℝ) * M ^ (n - 1) * D)

theorem expDiffRow_succ (t M D : ℝ) (n : ℕ) :
    expDiffRow t M D (n + 1) = |t| * ((|t| * M) ^ n / (n.factorial : ℝ)) * D := by
  unfold expDiffRow
  rw [if_neg (Nat.succ_ne_zero n), Nat.factorial_succ, Nat.add_sub_cancel]
  push_cast
  have hf : (0 : ℝ) < n.factorial := Nat.cast_pos.2 (Nat.factorial_pos n)
  field_simp
  ring

/-- `∑_n expDiffRow = |t| e^{|t| M} D`, with summability. -/
theorem expDiffRow_hasSum (t M D : ℝ) :
    HasSum (expDiffRow t M D) (|t| * Real.exp (|t| * M) * D) := by
  have h := ((hasSum_exp_series (|t| * M)).mul_left |t|).mul_right D
  have h' : HasSum (fun n => expDiffRow t M D (n + 1)) (|t| * Real.exp (|t| * M) * D) :=
    h.congr_fun fun n => expDiffRow_succ t M D n
  have h0 : expDiffRow t M D 0 = 0 := by simp [expDiffRow]
  exact (hasSum_nat_add_iff' 1).1 (by simpa [h0] using h')

/-- The joint majorant of the exponential difference. -/
noncomputable def expDiffMaj (ρ : ℝ) (a a' : ℕ × ℕ → ℝ) (t : ℝ) (p : ℕ × (ℕ × ℕ)) : ℝ :=
  |t| ^ p.1 / (p.1.factorial : ℝ)
    * (|convPow a p.1 p.2 - convPow a' p.1 p.2| * ρ ^ (p.2.1 + p.2.2))

theorem expDiffMaj_nonneg (ρ : ℝ) (hρ : 0 < ρ) (a a' : ℕ × ℕ → ℝ) (t : ℝ) (p : ℕ × (ℕ × ℕ)) :
    0 ≤ expDiffMaj ρ a a' t p := by
  unfold expDiffMaj; positivity

/-- Weighted summability and norm bound of `a^{*n} − a'^{*n}` for every `n`. -/
theorem wnorm_convPow_sub_le (ρ : ℝ) (hρ : 0 < ρ) (a a' : ℕ × ℕ → ℝ) (ha : WSummable ρ a)
    (ha' : WSummable ρ a') (M : ℝ) (hM : wnorm ρ a ≤ M) (hM' : wnorm ρ a' ≤ M) (n : ℕ) :
    WSummable ρ (fun k => convPow a n k - convPow a' n k) ∧
      wnorm ρ (fun k => convPow a n k - convPow a' n k)
        ≤ (if n = 0 then 0 else (n : ℝ) * M ^ (n - 1) * wnorm ρ (fun k => a k - a' k)) := by
  cases n with
  | zero =>
    have h0 : (fun k => convPow a 0 k - convPow a' 0 k) = fun _ => (0 : ℝ) := by
      funext k; show delta k - delta k = 0; ring
    rw [h0, wnorm_zero_fun, if_pos rfl]
    exact ⟨wsummable_zero_fun ρ, le_rfl⟩
  | succ n =>
    have h := wnorm_convPow_succ_sub_le ρ hρ a a' ha ha' M hM hM' n
    rw [if_neg (Nat.succ_ne_zero n), Nat.add_sub_cancel]
    push_cast
    exact h

/-- **Joint summability of the difference majorant** with total `≤ |t| e^{|t|M} ‖a − a'‖`. -/
theorem expDiffMaj_summable (ρ : ℝ) (hρ : 0 < ρ) (a a' : ℕ × ℕ → ℝ) (ha : WSummable ρ a)
    (ha' : WSummable ρ a') (M : ℝ) (hM : wnorm ρ a ≤ M) (hM' : wnorm ρ a' ≤ M) (t : ℝ) :
    Summable (expDiffMaj ρ a a' t) ∧
      ∑' p, expDiffMaj ρ a a' t p
        ≤ |t| * Real.exp (|t| * M) * wnorm ρ (fun k => a k - a' k) := by
  set D := wnorm ρ (fun k => a k - a' k) with hD
  have hrow : ∀ n, Summable fun k => expDiffMaj ρ a a' t (n, k) := by
    intro n
    have h := (wnorm_convPow_sub_le ρ hρ a a' ha ha' M hM hM' n).1
    unfold WSummable at h
    exact (h.mul_left (|t| ^ n / (n.factorial : ℝ))).congr fun k => rfl
  have hrowsum : ∀ n, ∑' k, expDiffMaj ρ a a' t (n, k)
      = |t| ^ n / (n.factorial : ℝ) * wnorm ρ (fun k => convPow a n k - convPow a' n k) := by
    intro n
    unfold expDiffMaj wnorm
    show ∑' k : ℕ × ℕ, |t| ^ n / (n.factorial : ℝ)
      * (|convPow a n k - convPow a' n k| * ρ ^ (k.1 + k.2)) = _
    rw [tsum_mul_left]
  have hrowle : ∀ n, ∑' k, expDiffMaj ρ a a' t (n, k) ≤ expDiffRow t M D n := by
    intro n
    rw [hrowsum n]
    have h := (wnorm_convPow_sub_le ρ hρ a a' ha ha' M hM hM' n).2
    unfold expDiffRow
    split_ifs with hn
    · subst hn
      have h0 : (fun k => convPow a 0 k - convPow a' 0 k) = fun _ => (0 : ℝ) := by
        funext k; show delta k - delta k = 0; ring
      rw [h0, wnorm_zero_fun, mul_zero]
    · rw [if_neg hn] at h
      exact mul_le_mul_of_nonneg_left h (by positivity)
  have hexp := (expDiffRow_hasSum t M D).summable
  have hcol : Summable fun n => ∑' k, expDiffMaj ρ a a' t (n, k) :=
    Summable.of_nonneg_of_le (fun n => tsum_nonneg fun k => expDiffMaj_nonneg ρ hρ a a' t _)
      hrowle hexp
  have hs : Summable (expDiffMaj ρ a a' t) :=
    (summable_prod_of_nonneg (expDiffMaj_nonneg ρ hρ a a' t)).2 ⟨hrow, hcol⟩
  refine ⟨hs, ?_⟩
  rw [hs.tsum_prod]
  calc ∑' n, ∑' k, expDiffMaj ρ a a' t (n, k)
      ≤ ∑' n, expDiffRow t M D n := hcol.tsum_le_tsum hrowle hexp
    _ = |t| * Real.exp (|t| * M) * D := (expDiffRow_hasSum t M D).tsum_eq

/-- The exponential coefficients differ by a finite sum of power differences. -/
theorem expCoeff_sub (a a' : ℕ × ℕ → ℝ) (t : ℝ) (k : ℕ × ℕ) :
    expCoeff a t k - expCoeff a' t k
      = ∑ n ∈ Finset.range (k.1 + k.2 + 1),
          t ^ n / (n.factorial : ℝ) * (convPow a n k - convPow a' n k) := by
  unfold expCoeff
  rw [← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun n _ => ?_
  ring

/-- The pointwise bound `|E_a(t)_k − E_{a'}(t)_k| ρ^{|k|} ≤ ∑_n g(n,k)`. -/
theorem expCoeff_sub_abs_le (ρ : ℝ) (hρ : 0 < ρ) (a a' : ℕ × ℕ → ℝ) (ha : WSummable ρ a)
    (ha' : WSummable ρ a') (ha0 : a (0, 0) = 0) (ha0' : a' (0, 0) = 0) (M : ℝ)
    (hM : wnorm ρ a ≤ M) (hM' : wnorm ρ a' ≤ M) (t : ℝ) (k : ℕ × ℕ) :
    |expCoeff a t k - expCoeff a' t k| * ρ ^ (k.1 + k.2) ≤ ∑' n, expDiffMaj ρ a a' t (n, k) := by
  obtain ⟨hs, -⟩ := expDiffMaj_summable ρ hρ a a' ha ha' M hM hM' t
  have hs' : Summable fun q : (ℕ × ℕ) × ℕ => expDiffMaj ρ a a' t (q.2, q.1) := hs.prod_symm
  have hcol : Summable fun n => expDiffMaj ρ a a' t (n, k) :=
    ((summable_prod_of_nonneg fun q => expDiffMaj_nonneg ρ hρ a a' t _).1 hs').1 k
  -- the finite sum as a full tsum (terms beyond `|k|` vanish)
  have hfin : expCoeff a t k - expCoeff a' t k
      = ∑' n, t ^ n / (n.factorial : ℝ) * (convPow a n k - convPow a' n k) := by
    rw [expCoeff_sub]
    rw [tsum_eq_sum (s := Finset.range (k.1 + k.2 + 1))]
    intro n hn
    rw [Finset.mem_range, not_lt] at hn
    rw [convPow_eq_zero_of_lt a ha0 n k (by omega), convPow_eq_zero_of_lt a' ha0' n k (by omega),
      sub_zero, mul_zero]
  rw [hfin, ← abs_of_pos (pow_pos hρ (k.1 + k.2)), ← abs_mul, ← tsum_mul_right]
  have hnorm : Summable fun n => ‖t ^ n / (n.factorial : ℝ) * (convPow a n k - convPow a' n k)
      * ρ ^ (k.1 + k.2)‖ := by
    refine hcol.congr fun n => ?_
    simp only [expDiffMaj, Real.norm_eq_abs, abs_mul, abs_div, abs_pow, abs_of_pos hρ,
      Nat.abs_cast]
    ring
  refine (norm_tsum_le_tsum_norm hnorm).trans (le_of_eq ?_)
  refine tsum_congr fun n => ?_
  simp only [expDiffMaj, Real.norm_eq_abs, abs_mul, abs_div, abs_pow, abs_of_pos hρ, Nat.abs_cast]
  ring

/-- **Lipschitz estimate for the exponential**:
`‖E_a(t) − E_{a'}(t)‖_ρ ≤ |t| e^{|t|M} ‖a − a'‖_ρ`. -/
theorem wnorm_expCoeff_sub_le (ρ : ℝ) (hρ : 0 < ρ) (a a' : ℕ × ℕ → ℝ) (ha : WSummable ρ a)
    (ha' : WSummable ρ a') (ha0 : a (0, 0) = 0) (ha0' : a' (0, 0) = 0) (M : ℝ)
    (hM : wnorm ρ a ≤ M) (hM' : wnorm ρ a' ≤ M) (t : ℝ) :
    WSummable ρ (fun k => expCoeff a t k - expCoeff a' t k) ∧
      wnorm ρ (fun k => expCoeff a t k - expCoeff a' t k)
        ≤ |t| * Real.exp (|t| * M) * wnorm ρ (fun k => a k - a' k) := by
  obtain ⟨hs, hle⟩ := expDiffMaj_summable ρ hρ a a' ha ha' M hM hM' t
  have hs' : Summable fun q : (ℕ × ℕ) × ℕ => expDiffMaj ρ a a' t (q.2, q.1) := hs.prod_symm
  have hG : Summable fun k => ∑' n, expDiffMaj ρ a a' t (n, k) :=
    ((summable_prod_of_nonneg fun q => expDiffMaj_nonneg ρ hρ a a' t _).1 hs').2
  have hpt := expCoeff_sub_abs_le ρ hρ a a' ha ha' ha0 ha0' M hM hM' t
  have hW : WSummable ρ (fun k => expCoeff a t k - expCoeff a' t k) :=
    Summable.of_nonneg_of_le (fun k => by positivity) hpt hG
  refine ⟨hW, ?_⟩
  calc wnorm ρ (fun k => expCoeff a t k - expCoeff a' t k)
      ≤ ∑' k, ∑' n, expDiffMaj ρ a a' t (n, k) := hW.tsum_le_tsum hpt hG
    _ = ∑' q : (ℕ × ℕ) × ℕ, expDiffMaj ρ a a' t (q.2, q.1) := (hs'.tsum_prod).symm
    _ = ∑' p, expDiffMaj ρ a a' t p := (Equiv.prodComm (ℕ × ℕ) ℕ).tsum_eq (expDiffMaj ρ a a' t)
    _ ≤ _ := hle

end Laplace.Grammar
