/-
Copyright (c) 2026 Timaeus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Laplace.Grammar.ParamHolo
import Laplace.Grammar.AnalyticTaylorTree

/-!
# The Cauchy coefficients are the normalised Taylor derivatives (Stage 8b)

Unit 267 (Astra #32, units 2–3 of the derivative-identification sprint). The several-variable
Cauchy coefficient `c_γ = A_r^{[d]}(F ∏ wᵢ^{-γᵢ})` of a function `F` holomorphic on the open
polydisc of radius `R > r` equals `∂^γ F(0)/γ!` with `γ! = ∏ᵢ γᵢ!`
(`polyCoeff_eq_coordDeriv_div`). Here `∂^γ F(0)` is the **fixed-order iterated coordinate
derivative** `coordDeriv d F γ`: recursively, differentiate the tail coordinates first and the head
coordinate `x` last, `∂^γ F(0) = ∂_x^{γ₀} [x ↦ ∂^{γ'} F(x, ·)(0)] (0)`; for holomorphic `F` this is
the usual mixed partial, but no permutation-invariance theorem is claimed. Ordinary `iteratedDeriv`
at `0` is used (the functions are holomorphic on an open neighbourhood of `0`).

The proof exploits the induction hypothesis as a *local identity*: by `polyCoeff_eq_discCoeff`
the head coefficient is the one-variable Cauchy coefficient of the parametric slice coefficient
`g(x) = polyCoeff d r (F(x, ·)) γ'`, which is holomorphic near the closed disc of radius `r`
(unit 266) — so `discCoeff_eq_iteratedDeriv_div` applies — and `g(x) = ∂^{γ'} F(x, ·)(0)/γ'!`
for every `x` in the parameter disc by the induction hypothesis, so `iteratedDeriv` may be taken
of the right-hand side (`Filter.EventuallyEq.iteratedDeriv_eq`). No differentiation under the
integral sign is needed.
-/

open MeasureTheory Set Real Filter Topology Complex

namespace Laplace.Grammar

/-- The coefficient operator `A_r(w ↦ w^{-n} g(w))` is the one-variable Cauchy coefficient. -/
theorem circleOp_eq_discCoeff (r : ℝ) (g : ℂ → ℂ) (n : ℕ) :
    circleOp r (fun w => w⁻¹ ^ n * g w) = discCoeff g r n := by
  unfold discCoeff circleOp
  rw [FormalMultilinearSeries.coeff, Pi.one_def, cauchyPowerSeries_apply]
  simp only [sub_zero, one_div, smul_eq_mul]
  congr 1
  congr 1
  funext z
  ring

/-- The head coefficient is the one-variable Cauchy coefficient of the parametric slice
coefficient. -/
theorem polyCoeff_eq_discCoeff {d : ℕ} (r : ℝ) (F : (Fin (d + 1) → ℂ) → ℂ)
    (γ : Fin (d + 1) → ℕ) :
    polyCoeff (d + 1) r F γ =
      discCoeff (fun x => polyCoeff d r (fun w' => F (Fin.cons x w')) (Fin.tail γ)) r (γ 0) := by
  conv_lhs => rw [← Fin.cons_self_tail γ]
  rw [polyCoeff_cons, circleOp_eq_discCoeff]

/-- **Fixed-order iterated coordinate derivative at `0`**: `∂^γ F(0)` with the tail coordinates
differentiated first and the head coordinate last. -/
noncomputable def coordDeriv : (d : ℕ) → ((Fin d → ℂ) → ℂ) → (Fin d → ℕ) → ℂ
  | 0, F, _ => F Fin.elim0
  | d + 1, F, γ =>
      iteratedDeriv (γ 0) (fun x => coordDeriv d (fun w' => F (Fin.cons x w')) (Fin.tail γ)) 0

/-- The multi-index factorial `γ! = ∏ᵢ γᵢ!`, as a complex number. -/
noncomputable def multiFactorial {d : ℕ} (γ : Fin d → ℕ) : ℂ := ∏ i, ((γ i).factorial : ℂ)

theorem multiFactorial_succ {d : ℕ} (γ : Fin (d + 1) → ℕ) :
    multiFactorial γ = ((γ 0).factorial : ℂ) * multiFactorial (Fin.tail γ) := by
  unfold multiFactorial
  rw [Fin.prod_univ_succ]
  rfl

theorem multiFactorial_ne_zero {d : ℕ} (γ : Fin d → ℕ) : multiFactorial γ ≠ 0 := by
  unfold multiFactorial
  exact Finset.prod_ne_zero_iff.2 fun i _ => Nat.cast_ne_zero.2 (Nat.factorial_ne_zero _)

/-- `∂^0 F(0) = F(0)`. -/
theorem coordDeriv_zero : ∀ (d : ℕ) (F : (Fin d → ℂ) → ℂ), coordDeriv d F 0 = F 0
  | 0, F => by
    simp only [coordDeriv]
    congr 1
    exact Subsingleton.elim _ _
  | d + 1, F => by
    simp only [coordDeriv, Pi.zero_apply, iteratedDeriv_zero]
    have : Fin.tail (0 : Fin (d + 1) → ℕ) = 0 := rfl
    rw [this, coordDeriv_zero d]
    congr 1
    funext i
    refine Fin.cases ?_ (fun j => ?_) i
    · simp
    · simp

/-- A slice of a function holomorphic on the open polydisc is holomorphic on the open polydisc of
one dimension less, for every head value inside the disc. -/
theorem differentiableOn_slice {d : ℕ} {R : ℝ} {F : (Fin (d + 1) → ℂ) → ℂ}
    (hF : DifferentiableOn ℂ F (openPolydisc (d + 1) R)) {x : ℂ} (hx : ‖x‖ < R) :
    DifferentiableOn ℂ (fun w' => F (Fin.cons x w')) (openPolydisc d R) := by
  refine hF.comp (differentiable_cons_right x).differentiableOn fun w' hw' => ?_
  exact cons_mem_openPolydisc hx hw'

/-- **The Cauchy coefficients are the normalised Taylor derivatives**: for `F` holomorphic on the
open polydisc of radius `R > r`, `c_γ = A_r^{[d]}(F ∏ wᵢ^{-γᵢ}) = ∂^γ F(0)/γ!`. -/
theorem polyCoeff_eq_coordDeriv_div : ∀ (d : ℕ) {r R : ℝ}, 0 < r → r < R →
    ∀ {F : (Fin d → ℂ) → ℂ}, DifferentiableOn ℂ F (openPolydisc d R) → ∀ γ : Fin d → ℕ,
      polyCoeff d r F γ = coordDeriv d F γ / multiFactorial γ
  | 0, r, R, _, _, F, _, γ => by
    simp only [polyCoeff, iterOp, coordDeriv, multiFactorial, Finset.univ_eq_empty,
      Finset.prod_empty, mul_one, div_one]
  | d + 1, r, R, hr, hrR, F, hF, γ => by
    have hR : 0 < R := hr.trans hrR
    set ρ : ℝ := (r + R) / 2 with hρ_def
    have hrρ : r < ρ := by rw [hρ_def]; linarith
    have hρR : ρ < R := by rw [hρ_def]; linarith
    -- the parametric slice coefficient
    set g : ℂ → ℂ := fun x => polyCoeff d r (fun w' => F (Fin.cons x w')) (Fin.tail γ) with hg_def
    have hg : DifferentiableOn ℂ g (Metric.ball 0 ρ) :=
      differentiableOn_polyCoeff_param hr hrρ hρR hF (Fin.tail γ)
    set rN : NNReal := ⟨r, hr.le⟩ with hrN
    have hrpos : 0 < rN := by
      rw [← NNReal.coe_pos]; exact hr
    have hg' : DifferentiableOn ℂ g (Metric.closedBall 0 (rN : ℝ)) :=
      hg.mono (Metric.closedBall_subset_ball hrρ)
    have hd : discCoeff g r (γ 0) = iteratedDeriv (γ 0) g 0 / ((γ 0).factorial : ℂ) :=
      discCoeff_eq_iteratedDeriv_div hg' hrpos (γ 0)
    rw [polyCoeff_eq_discCoeff]
    change discCoeff g r (γ 0) = _
    rw [hd]
    -- the induction hypothesis as a local identity near `0`
    have hev : g =ᶠ[𝓝 (0 : ℂ)]
        fun x => coordDeriv d (fun w' => F (Fin.cons x w')) (Fin.tail γ) / multiFactorial
          (Fin.tail γ) := by
      have hball : Metric.ball (0 : ℂ) R ∈ 𝓝 (0 : ℂ) := Metric.ball_mem_nhds 0 hR
      filter_upwards [hball] with x hx
      have hx' : ‖x‖ < R := by simpa using hx
      exact polyCoeff_eq_coordDeriv_div d hr hrR (differentiableOn_slice hF hx') (Fin.tail γ)
    rw [hev.iteratedDeriv_eq, iteratedDeriv_div_const]
    simp only [coordDeriv, multiFactorial_succ]
    rw [div_div, mul_comm (multiFactorial _)]

/-- The Cauchy coefficients do not depend on the admissible contour radius. -/
theorem polyCoeff_radius_indep {d : ℕ} {r r' R : ℝ} (hr : 0 < r) (hrR : r < R) (hr' : 0 < r')
    (hr'R : r' < R) {F : (Fin d → ℂ) → ℂ} (hF : DifferentiableOn ℂ F (openPolydisc d R))
    (γ : Fin d → ℕ) : polyCoeff d r F γ = polyCoeff d r' F γ := by
  rw [polyCoeff_eq_coordDeriv_div d hr hrR hF γ, polyCoeff_eq_coordDeriv_div d hr' hr'R hF γ]

/-- The real-part family used in Headline XXXII is `Re(∂^γ F(0)/γ!)`. -/
theorem polyRealCoeff_eq {d : ℕ} {r R : ℝ} (hr : 0 < r) (hrR : r < R) {F : (Fin d → ℂ) → ℂ}
    (hF : DifferentiableOn ℂ F (openPolydisc d R)) (γ : Fin d → ℕ) :
    polyRealCoeff d r F γ = (coordDeriv d F γ / multiFactorial γ).re := by
  unfold polyRealCoeff
  rw [polyCoeff_eq_coordDeriv_div d hr hrR hF γ]

end Laplace.Grammar
