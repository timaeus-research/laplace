/-
Copyright (c) 2026 Timaeus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Laplace.Grammar.ConvAlgebra

/-!
# Local Lipschitz estimate for the amplitude coefficient map (grammar §4.2, Astra #10 rank 5)

The amplitude coefficients `c_k(s) = ampCoeff β x y k s` of `η(u,v) e^{βs ξ(u,v)}` depend on the
data `(x, y)` (the double-series coefficients of `ξ` and `η`) through the convolution exponential.
We prove they are locally Lipschitz in the Banach-algebra norm `‖·‖_ρ = wnorm ρ`:

`‖c(x,y) − c(x',y')‖_ρ ≤ e^{2|βs| M_x} (‖y − y'‖_ρ + 2 M_y |βs| ‖x − x'‖_ρ)`

for `‖x‖_ρ, ‖x'‖_ρ ≤ M_x` and `‖y'‖_ρ ≤ M_y` (`ampCoeff_lipschitz`), together with the pointwise
consequence `|c_k(x,y)(s) − c_k(x',y')(s)| ρ^{|k|} ≤ (same)` (`ampCoeff_sub_abs_le`). The proof is
the three-term decomposition

`e^{u}(y − y') * E + e^{u} y' * (E − E') + (e^{u} − e^{u'}) y' * E'`

with `u = βs x₀₀`, `E = E_{dropConst x}(βs)`, estimated by `wnorm_conv_le`, `wnorm_expCoeff_le`,
`wnorm_expCoeff_sub_le` and `|e^u − e^{u'}| ≤ |u − u'| e^{max}`. Zero `sorry`/`axiom`.
-/

open Real MeasureTheory Set Filter Asymptotics

namespace Laplace.Grammar

theorem wsummable_const_mul (ρ c : ℝ) (f : ℕ × ℕ → ℝ) (hf : WSummable ρ f) :
    WSummable ρ (fun k => c * f k) := by
  unfold WSummable at hf ⊢
  exact (hf.mul_left |c|).congr fun k => by rw [abs_mul, mul_assoc]

theorem wnorm_const_mul (ρ c : ℝ) (f : ℕ × ℕ → ℝ) :
    wnorm ρ (fun k => c * f k) = |c| * wnorm ρ f := by
  unfold wnorm
  simp_rw [abs_mul, mul_assoc]
  exact tsum_mul_left

/-- Each weighted term is bounded by the weighted norm. -/
theorem term_le_wnorm (ρ : ℝ) (hρ : 0 ≤ ρ) (f : ℕ × ℕ → ℝ) (hf : WSummable ρ f) (k : ℕ × ℕ) :
    |f k| * ρ ^ (k.1 + k.2) ≤ wnorm ρ f := by
  unfold WSummable at hf
  exact hf.le_tsum k fun j _ => by positivity

theorem abs_apply_zero_le_wnorm (ρ : ℝ) (hρ : 0 ≤ ρ) (f : ℕ × ℕ → ℝ) (hf : WSummable ρ f) :
    |f (0, 0)| ≤ wnorm ρ f := by
  have := term_le_wnorm ρ hρ f hf (0, 0)
  simpa using this

theorem dropConst_sub (x x' : ℕ × ℕ → ℝ) :
    dropConst (fun k => x k - x' k) = fun k => dropConst x k - dropConst x' k := by
  funext k
  unfold dropConst
  split_ifs <;> simp

/-- The three-term decomposition of the amplitude difference. -/
theorem ampCoeff_sub_decomp (β : ℝ) (x x' y y' : ℕ × ℕ → ℝ) (s : ℝ) :
    (fun k => ampCoeff β x y k s - ampCoeff β x' y' k s)
      = fun k => Real.exp (β * s * x (0, 0))
            * (conv (fun k => y k - y' k) (expCoeff (dropConst x) (β * s)) k
              + conv y' (fun k => expCoeff (dropConst x) (β * s) k
                  - expCoeff (dropConst x') (β * s) k) k)
          + (Real.exp (β * s * x (0, 0)) - Real.exp (β * s * x' (0, 0)))
            * conv y' (expCoeff (dropConst x') (β * s)) k := by
  funext k
  unfold ampCoeff
  rw [conv_sub_left, conv_sub_right]
  ring

/-- The scalar factor `e^{βs x₀₀}` is bounded by `e^{|βs| M_x}`. -/
theorem exp_phase_le (ρ : ℝ) (hρ : 0 ≤ ρ) (x : ℕ × ℕ → ℝ) (hx : WSummable ρ x) (M t : ℝ)
    (hM : wnorm ρ x ≤ M) : Real.exp (t * x (0, 0)) ≤ Real.exp (|t| * M) := by
  apply Real.exp_le_exp.2
  calc t * x (0, 0) ≤ |t * x (0, 0)| := le_abs_self _
    _ = |t| * |x (0, 0)| := abs_mul _ _
    _ ≤ |t| * M :=
        mul_le_mul_of_nonneg_left ((abs_apply_zero_le_wnorm ρ hρ x hx).trans hM) (abs_nonneg t)

/-- The scalar factors differ by at most `e^{|βs| M_x} |βs| ‖x − x'‖_ρ`. -/
theorem exp_phase_sub_le (ρ : ℝ) (hρ : 0 ≤ ρ) (x x' : ℕ × ℕ → ℝ) (hx : WSummable ρ x)
    (hx' : WSummable ρ x') (M t : ℝ) (hM : wnorm ρ x ≤ M) (hM' : wnorm ρ x' ≤ M) :
    |Real.exp (t * x (0, 0)) - Real.exp (t * x' (0, 0))|
      ≤ Real.exp (|t| * M) * (|t| * wnorm ρ (fun k => x k - x' k)) := by
  have hd := wsummable_sub ρ hρ x x' hx hx'
  have h0 : |x (0, 0) - x' (0, 0)| ≤ wnorm ρ (fun k => x k - x' k) :=
    abs_apply_zero_le_wnorm ρ hρ _ hd
  have hmax : Real.exp (max (t * x (0, 0)) (t * x' (0, 0))) ≤ Real.exp (|t| * M) := by
    rcases le_total (t * x (0, 0)) (t * x' (0, 0)) with h | h
    · rw [max_eq_right h]; exact exp_phase_le ρ hρ x' hx' M t hM'
    · rw [max_eq_left h]; exact exp_phase_le ρ hρ x hx M t hM
  calc |Real.exp (t * x (0, 0)) - Real.exp (t * x' (0, 0))|
      ≤ |t * x (0, 0) - t * x' (0, 0)| * Real.exp (max (t * x (0, 0)) (t * x' (0, 0))) :=
        abs_exp_sub_exp_le _ _
    _ = Real.exp (max (t * x (0, 0)) (t * x' (0, 0))) * (|t| * |x (0, 0) - x' (0, 0)|) := by
        rw [← mul_sub, abs_mul]; ring
    _ ≤ Real.exp (|t| * M) * (|t| * wnorm ρ (fun k => x k - x' k)) := by
        gcongr

/-- **Local Lipschitz estimate for the amplitude coefficients** in the weighted norm:
`‖c(x,y) − c(x',y')‖_ρ ≤ e^{2|βs| M_x} (‖y − y'‖_ρ + 2 M_y |βs| ‖x − x'‖_ρ)`. -/
theorem ampCoeff_lipschitz (β ρ : ℝ) (hρ : 0 < ρ) (x x' y y' : ℕ × ℕ → ℝ) (hx : WSummable ρ x)
    (hx' : WSummable ρ x') (hy : WSummable ρ y) (hy' : WSummable ρ y') (Mx My : ℝ)
    (hMx : wnorm ρ x ≤ Mx) (hMx' : wnorm ρ x' ≤ Mx) (hMy' : wnorm ρ y' ≤ My) (s : ℝ) :
    WSummable ρ (fun k => ampCoeff β x y k s - ampCoeff β x' y' k s) ∧
      wnorm ρ (fun k => ampCoeff β x y k s - ampCoeff β x' y' k s)
        ≤ Real.exp (2 * |β * s| * Mx)
          * (wnorm ρ (fun k => y k - y' k) + 2 * My * |β * s| * wnorm ρ (fun k => x k - x' k)) := by
  set t := β * s with ht
  set E1 := Real.exp (|t| * Mx) with hE1
  set Dy := wnorm ρ (fun k => y k - y' k) with hDy
  set Dx := wnorm ρ (fun k => x k - x' k) with hDx
  have hMx0 : 0 ≤ Mx := (wnorm_nonneg ρ hρ.le x).trans hMx
  have hMy0 : 0 ≤ My := (wnorm_nonneg ρ hρ.le y').trans hMy'
  have hDy0 : 0 ≤ Dy := wnorm_nonneg ρ hρ.le _
  have hDx0 : 0 ≤ Dx := wnorm_nonneg ρ hρ.le _
  have hE10 : 0 < E1 := Real.exp_pos _
  -- the exponential arrays
  have hdx := wsummable_dropConst ρ hρ.le x hx
  have hdx' := wsummable_dropConst ρ hρ.le x' hx'
  have hdxn : wnorm ρ (dropConst x) ≤ Mx := (wnorm_dropConst_le ρ hρ.le x hx).trans hMx
  have hdxn' : wnorm ρ (dropConst x') ≤ Mx := (wnorm_dropConst_le ρ hρ.le x' hx').trans hMx'
  have hE := wnorm_expCoeff_le ρ hρ (dropConst x) hdx (dropConst_zero x) t
  have hE' := wnorm_expCoeff_le ρ hρ (dropConst x') hdx' (dropConst_zero x') t
  have hEn : wnorm ρ (expCoeff (dropConst x) t) ≤ E1 :=
    hE.2.trans (Real.exp_le_exp.2 (mul_le_mul_of_nonneg_left hdxn (abs_nonneg t)))
  have hEn' : wnorm ρ (expCoeff (dropConst x') t) ≤ E1 :=
    hE'.2.trans (Real.exp_le_exp.2 (mul_le_mul_of_nonneg_left hdxn' (abs_nonneg t)))
  have hED := wnorm_expCoeff_sub_le ρ hρ (dropConst x) (dropConst x') hdx hdx' (dropConst_zero x)
    (dropConst_zero x') Mx hdxn hdxn' t
  have hdd : wnorm ρ (fun k => dropConst x k - dropConst x' k) ≤ Dx := by
    rw [← dropConst_sub]
    exact wnorm_dropConst_le ρ hρ.le _ (wsummable_sub ρ hρ.le x x' hx hx')
  have hEDn : wnorm ρ (fun k => expCoeff (dropConst x) t k - expCoeff (dropConst x') t k)
      ≤ |t| * E1 * Dx :=
    hED.2.trans (mul_le_mul_of_nonneg_left hdd (by positivity))
  -- the three convolutions
  have hyy := wsummable_sub ρ hρ.le y y' hy hy'
  have h1 := wnorm_conv_le ρ hρ (fun k => y k - y' k) (expCoeff (dropConst x) t) hyy hE.1
  have h2 := wnorm_conv_le ρ hρ y' _ hy' hED.1
  have h3 := wnorm_conv_le ρ hρ y' (expCoeff (dropConst x') t) hy' hE'.1
  have h1n : wnorm ρ (conv (fun k => y k - y' k) (expCoeff (dropConst x) t)) ≤ Dy * E1 :=
    h1.2.trans (mul_le_mul_of_nonneg_left hEn hDy0)
  have h2n : wnorm ρ (conv y' (fun k => expCoeff (dropConst x) t k - expCoeff (dropConst x') t k))
      ≤ My * (|t| * E1 * Dx) :=
    h2.2.trans (mul_le_mul hMy' hEDn (wnorm_nonneg ρ hρ.le _) hMy0)
  have h3n : wnorm ρ (conv y' (expCoeff (dropConst x') t)) ≤ My * E1 :=
    h3.2.trans (mul_le_mul hMy' hEn' (wnorm_nonneg ρ hρ.le _) hMy0)
  -- the scalar factors
  have hu : Real.exp (t * x (0, 0)) ≤ E1 := exp_phase_le ρ hρ.le x hx Mx t hMx
  have hdu : |Real.exp (t * x (0, 0)) - Real.exp (t * x' (0, 0))| ≤ E1 * (|t| * Dx) :=
    exp_phase_sub_le ρ hρ.le x x' hx hx' Mx t hMx hMx'
  -- assemble
  have hPQ := wsummable_add ρ hρ.le _ _ h1.1 h2.1
  have hA := wsummable_const_mul ρ (Real.exp (t * x (0, 0))) _ hPQ
  have hB := wsummable_const_mul ρ (Real.exp (t * x (0, 0)) - Real.exp (t * x' (0, 0))) _ h3.1
  rw [ampCoeff_sub_decomp, ← ht]
  refine ⟨wsummable_add ρ hρ.le _ _ hA hB, ?_⟩
  have hPQn : wnorm ρ (fun k => conv (fun k => y k - y' k) (expCoeff (dropConst x) t) k
      + conv y' (fun k => expCoeff (dropConst x) t k - expCoeff (dropConst x') t k) k)
      ≤ Dy * E1 + My * (|t| * E1 * Dx) :=
    (wnorm_add_le ρ hρ.le _ _ h1.1 h2.1).trans (add_le_add h1n h2n)
  calc wnorm ρ (fun k => Real.exp (t * x (0, 0))
          * (conv (fun k => y k - y' k) (expCoeff (dropConst x) t) k
            + conv y' (fun k => expCoeff (dropConst x) t k - expCoeff (dropConst x') t k) k)
          + (Real.exp (t * x (0, 0)) - Real.exp (t * x' (0, 0)))
            * conv y' (expCoeff (dropConst x') t) k)
      ≤ wnorm ρ (fun k => Real.exp (t * x (0, 0))
          * (conv (fun k => y k - y' k) (expCoeff (dropConst x) t) k
            + conv y' (fun k => expCoeff (dropConst x) t k - expCoeff (dropConst x') t k) k))
        + wnorm ρ (fun k => (Real.exp (t * x (0, 0)) - Real.exp (t * x' (0, 0)))
            * conv y' (expCoeff (dropConst x') t) k) := wnorm_add_le ρ hρ.le _ _ hA hB
    _ = Real.exp (t * x (0, 0))
          * wnorm ρ (fun k => conv (fun k => y k - y' k) (expCoeff (dropConst x) t) k
            + conv y' (fun k => expCoeff (dropConst x) t k - expCoeff (dropConst x') t k) k)
        + |Real.exp (t * x (0, 0)) - Real.exp (t * x' (0, 0))|
          * wnorm ρ (conv y' (expCoeff (dropConst x') t)) := by
        rw [wnorm_const_mul, wnorm_const_mul, abs_of_pos (Real.exp_pos _)]
    _ ≤ E1 * (Dy * E1 + My * (|t| * E1 * Dx)) + E1 * (|t| * Dx) * (My * E1) :=
        add_le_add (mul_le_mul hu hPQn (wnorm_nonneg ρ hρ.le _) hE10.le)
          (mul_le_mul hdu h3n (wnorm_nonneg ρ hρ.le _) (by positivity))
    _ = Real.exp (2 * |t| * Mx) * (Dy + 2 * My * |t| * Dx) := by
        rw [show Real.exp (2 * |t| * Mx) = E1 * E1 by
          rw [hE1, ← Real.exp_add]; congr 1; ring]
        ring

/-- Pointwise form of the Lipschitz estimate. -/
theorem ampCoeff_sub_abs_le (β ρ : ℝ) (hρ : 0 < ρ) (x x' y y' : ℕ × ℕ → ℝ) (hx : WSummable ρ x)
    (hx' : WSummable ρ x') (hy : WSummable ρ y) (hy' : WSummable ρ y') (Mx My : ℝ)
    (hMx : wnorm ρ x ≤ Mx) (hMx' : wnorm ρ x' ≤ Mx) (hMy' : wnorm ρ y' ≤ My) (k : ℕ × ℕ)
    (s : ℝ) :
    |ampCoeff β x y k s - ampCoeff β x' y' k s| * ρ ^ (k.1 + k.2)
      ≤ Real.exp (2 * |β * s| * Mx)
        * (wnorm ρ (fun k => y k - y' k) + 2 * My * |β * s| * wnorm ρ (fun k => x k - x' k)) := by
  obtain ⟨hW, hle⟩ := ampCoeff_lipschitz β ρ hρ x x' y y' hx hx' hy hy' Mx My hMx hMx' hMy' s
  exact (term_le_wnorm ρ hρ.le _ hW k).trans hle

end Laplace.Grammar
