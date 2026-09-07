/-
Copyright (c) 2026 Timaeus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Laplace.Grammar.CauchyCoeff1D

/-!
# The analytic Taylor tree in one variable (Stage 6b)

Unit 258 (Astra #30 candidate C₁). For `f : ℂ → ℂ` holomorphic on the closed disc `|z| ≤ r`, the
**real coefficients** `realCoeff f r n = Re(discCoeff f r n)` satisfy
`∑_n realCoeff f r n · x^n = Re f(x)` for real `|x| < r` (`hasSum_realCoeff`; no reality
hypothesis is
needed — when `f` is real on the segment this is `f(x)`) and
`∑_n |realCoeff f r n| b^n < ∞` for every `b < r` (`summable_abs_realCoeff_mul_pow`). Packaging
them as
a one-variable coefficient family (`toFamily1`), the coefficient-family Taylor tree applies:

**Headline XXXI** (`thm_TaylorTree_analytic_1d`): for `fξ, fη` holomorphic on `|z| ≤ r` and
`0 < b < r`, the families `toFamily1 (realCoeff fξ r)`, `toFamily1 (realCoeff fη r)`
represent `Re fξ, Re fη` on `(0,b]` (`evalF_toFamily1_realCoeff`) and satisfy
`TaylorTreeConclusion`: the
Taylor-tree expansion on `(0,b]` with the paper's exponent set, explicit coefficient series and
derivative dictionary — `thm:TaylorTree` in dimension one under the paper's own hypothesis
(holomorphic extension to a disc of radius `r > b`). No `sorry` and no additional `axiom`
declarations.
-/

open MeasureTheory Set Real Filter Topology Complex

namespace Laplace.Grammar

open MonoRep CoeffFamily

/-- The real parts of the Cauchy coefficients. -/
noncomputable def realCoeff (f : ℂ → ℂ) (r : ℝ) (n : ℕ) : ℝ := (discCoeff f r n).re

theorem abs_realCoeff_le (f : ℂ → ℂ) (r : ℝ) (n : ℕ) : |realCoeff f r n| ≤ ‖discCoeff f r n‖ :=
  Complex.abs_re_le_norm _

/-- Weighted absolute summability of the real coefficients at every `0 ≤ b < r`. -/
theorem summable_abs_realCoeff_mul_pow (f : ℂ → ℂ) {r b : ℝ} (hr : 0 < r) (hb : 0 ≤ b) (hbr : b <
r) :
    Summable fun n => |realCoeff f r n| * b ^ n :=
  Summable.of_nonneg_of_le (fun n => by positivity)
    (fun n => mul_le_mul_of_nonneg_right (abs_realCoeff_le f r n) (pow_nonneg hb n))
    (summable_norm_discCoeff_mul_pow f hr hb hbr)

/-- **Real representation**: `∑_n realCoeff f r n · x^n = Re f(x)` for real `|x| < r`. -/
theorem hasSum_realCoeff {f : ℂ → ℂ} {r : NNReal} (hf : DifferentiableOn ℂ f (Metric.closedBall 0
r))
    (hr : 0 < r) {x : ℝ} (hx : |x| < r) :
    HasSum (fun n => realCoeff f r n * x ^ n) (f x).re := by
  have h := hasSum_discCoeff hf hr (z := (x : ℂ)) (by rwa [Complex.norm_real, Real.norm_eq_abs])
  have h2 := h.mapL Complex.reCLM
  refine h2.congr_fun fun n => ?_
  simp only [Complex.reCLM_apply, realCoeff]
  rw [← Complex.ofReal_pow, Complex.re_mul_ofReal]

/-! ### One-variable coefficient families -/

/-- A scalar coefficient sequence as a coefficient family in one variable. -/
def toFamily1 (c : ℕ → ℝ) : CoeffFamily 1 := fun γ => c (γ 0)

theorem mono_one_var (γ : Fin 1 → ℕ) (u : Fin 1 → ℝ) : mono γ u = u 0 ^ γ 0 := by
  unfold mono; rw [Fin.prod_univ_one]

theorem sum_one_var (γ : Fin 1 → ℕ) : ∑ i, γ i = γ 0 := by rw [Fin.sum_univ_one]

/-- The equivalence `(Fin 1 → ℕ) ≃ ℕ`. -/
def oneVarEquiv : (Fin 1 → ℕ) ≃ ℕ := Equiv.funUnique (Fin 1) ℕ

theorem absSummableAt_toFamily1 {c : ℕ → ℝ} {b : ℝ} (hc : Summable fun n => |c n| * b ^ n) :
    AbsSummableAt (toFamily1 c) b := by
  unfold AbsSummableAt toFamily1
  have := (oneVarEquiv.summable_iff (f := fun n => |c n| * b ^ n)).2 hc
  refine this.congr fun γ => ?_
  simp [oneVarEquiv, Equiv.funUnique, Function.comp]

/-- Evaluation of a one-variable family is the scalar power series. -/
theorem evalF_toFamily1 (c : ℕ → ℝ) (u : Fin 1 → ℝ) :
    evalF (toFamily1 c) u = ∑' n, c n * u 0 ^ n := by
  unfold evalF toFamily1
  rw [← oneVarEquiv.tsum_eq (fun n => c n * u 0 ^ n)]
  refine tsum_congr fun γ => ?_
  simp [oneVarEquiv, Equiv.funUnique, mono_one_var]

/-- The real-coefficient family represents `Re f` on `(0,b]`. -/
theorem evalF_toFamily1_realCoeff {f : ℂ → ℂ} {r : NNReal}
    (hf : DifferentiableOn ℂ f (Metric.closedBall 0 r)) (hr : 0 < r) {b : ℝ} (hbr : b < r)
    {u : Fin 1 → ℝ} (hu : u ∈ piBox 1 (Ioc 0 b)) :
    evalF (toFamily1 (realCoeff f r)) u = (f (u 0)).re := by
  rw [evalF_toFamily1]
  have hu0 : u 0 ∈ Ioc (0 : ℝ) b := hu 0 (Set.mem_univ _)
  have hx : |u 0| < r := by rw [abs_of_pos hu0.1]; linarith [hu0.2]
  exact (hasSum_realCoeff hf hr hx).tsum_eq

/-- **Headline XXXI — the analytic Taylor tree in one variable.** For `fξ, fη` holomorphic on the
closed disc of radius `r` and `0 < b < r`: the real Cauchy-coefficient families represent
`Re fξ, Re fη` on `(0,b]` (equal to `fξ, fη` when these are real on the segment), and the
coefficient-family Taylor tree (`TaylorTreeConclusion`) holds for them. -/
theorem thm_TaylorTree_analytic_1d (h k : Fin 1 → ℕ) (hk : ∀ i, 0 < k i) (β : ℝ) (hβ : 0 < β)
    {r : NNReal} (hr : 0 < r) {b : ℝ} (hb : 0 < b) (hbr : b < r) {fξ fη : ℂ → ℂ}
    (hξ : DifferentiableOn ℂ fξ (Metric.closedBall 0 r))
    (hη : DifferentiableOn ℂ fη (Metric.closedBall 0 r)) :
    (∀ u ∈ piBox 1 (Ioc 0 b), evalF (toFamily1 (realCoeff fξ r)) u = (fξ (u 0)).re ∧
        evalF (toFamily1 (realCoeff fη r)) u = (fη (u 0)).re) ∧
      ∃ C : ℝ → ℕ → ℝ,
        TaylorTreeConclusion 0 h k β b (toFamily1 (realCoeff fξ r)) (toFamily1 (realCoeff fη r))
            C := by
  have hr' : (0 : ℝ) < r := by exact_mod_cast hr
  refine ⟨fun u hu => ⟨evalF_toFamily1_realCoeff hξ hr hbr hu, evalF_toFamily1_realCoeff hη hr
      hbr hu⟩,
    ?_⟩
  exact thm_TaylorTree_coeffFamily 0 h k hk β hβ hb
    (absSummableAt_toFamily1 (summable_abs_realCoeff_mul_pow fξ hr' hb.le hbr))
    (absSummableAt_toFamily1 (summable_abs_realCoeff_mul_pow fη hr' hb.le hbr))

end Laplace.Grammar
