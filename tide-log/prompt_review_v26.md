# Fidelity review v26 — Stage 8: derivative identification of the several-variable Cauchy coefficients (units 266–268)

You are an independent statement-level reviewer of a Lean 4 / Mathlib formalisation (project `laplace`, namespace `Laplace.Grammar`, pin `066b8c6`) of Section 4 of the paper "Grammar of the fluctuations" (`thm:TaylorTree`, `cor:standardintegralexp`). Previous reviews v18–v25 covered units 223–264; v25 passed the several-variable analytic bridge (Headline XXXII, `thm_TaylorTree_analytic`: the Taylor-tree conclusion for the real parts of the several-variable Cauchy coefficients `polyCoeff d r F γ = A_r^{[d]}(F ∏ wᵢ^{-γᵢ})`, `A_r(g) = (2πi)⁻¹ ∮_{|w|=r} w⁻¹ g(w) dw` iterated along `Fin.cons`) with the qualification that the coefficients were not identified with `∂^γ F(0)/γ!`.

Units 266–268 close that qualification. Please review the STATEMENTS (and the two short proofs reproduced in full) for mathematical correctness and fidelity to the paper's meaning. The excerpts below are extracted mechanically (docstring + statement up to `:=`); the extractor sometimes truncates or duplicates a declaration — the source has exactly one of each. All files compile with zero `sorry` and no additional axioms.

## Design (Astra #32)
- `coordDeriv d F γ` = fixed-order iterated coordinate derivative at 0: `coordDeriv 0 F _ = F ∅`; `coordDeriv (d+1) F γ = iteratedDeriv (γ 0) (fun x => coordDeriv d (F ∘ Fin.cons x) (Fin.tail γ)) 0` — tail coordinates first, head last; ordinary `iteratedDeriv` at `0` (functions holomorphic on an open neighbourhood). `multiFactorial γ = ∏ᵢ (γᵢ)!`.
- Unit 266 (gate): `x ↦ polyCoeff d r (F ∘ Fin.cons x) γ'` is holomorphic on `|x| < ρ`, `r < ρ < R`, for `F` holomorphic on the open polydisc of radius `R`. Proof: `circleOp` is the circle average `(2π)⁻¹ ∫₀^{2π} g(re^{iθ}) dθ`; slice Cauchy formula at radius ρ; Fubini `iterOp_circleOp_swap` (continuous integrands on compact tori); the Cauchy-type integral `x ↦ A_ρ((1 − x/z)⁻¹ g(z))` is holomorphic by Mathlib's `hasFPowerSeriesOn_cauchy_integral`. No differentiation under the integral.
- Unit 267: `polyCoeff (d+1) r F γ = discCoeff g r (γ 0)` with `g x = polyCoeff d r (F ∘ cons x) (tail γ)` and `discCoeff g r n = (cauchyPowerSeries g 0 r).coeff n`; one-variable `discCoeff_eq_iteratedDeriv_div` (u257, reviewed) gives `iteratedDeriv (γ 0) g 0 / (γ 0)!`; the induction hypothesis gives `g x = coordDeriv d (F ∘ cons x) (tail γ) / (tail γ)!` for `|x| < R`, used as an eventual equality at `𝓝 0` (`Filter.EventuallyEq.iteratedDeriv_eq`), then `iteratedDeriv_div_const`.
- Unit 268: `taylorFamily d F γ = Re(coordDeriv d F γ / γ!)`; `polyRealCoeff = taylorFamily`; Headline XXXIII `thm_TaylorTree_taylor` (paper-facing, `0 < b < R`).

## Statements

### Laplace/Grammar/ParamHolo.lean

```lean
/-!
# Holomorphy of the Cauchy coefficients in a parameter (Stage 8a — the gate)

Unit 266 (Astra #32, unit 1 of the derivative-identification sprint). The several-variable Cauchy
coefficient of the slice `F(x, ·)`, `x ↦ polyCoeff d r (F ∘ Fin.cons x) γ'`, is holomorphic in the
parameter `x` on a disc of radius `ρ ∈ (r, R)` when `F` is holomorphic on the open polydisc of
radius `R` (`differentiableOn_polyCoeff_param`). No differentiation under the integral is used: the
slice is represented by the one-variable Cauchy formula at radius `ρ`, the circle operator at radius
`ρ` is interchanged with the iterated operator at radius `r` (Fubini for continuous integrands,
`iterOp_circleOp_swap`), and the resulting Cauchy-type integral `x ↦ A_ρ((1 − x/z)⁻¹ g(z))` is
holomorphic by Mathlib's `hasFPowerSeriesOn_cauchy_integral`. Along the way `circleOp` is identified
with the circle average `(2π)⁻¹ ∫₀^{2π} g(ρe^{iθ}) dθ` (`circleOp_eq_integral`).
-/

/-- The normalised circle operator is the circle average. -/
theorem circleOp_eq_integral {r : ℝ} (hr : r ≠ 0) (g : ℂ → ℂ) :
    circleOp r g =
      ((2 * Real.pi : ℝ) : ℂ)⁻¹ * ∫ θ in (0 : ℝ)..2 * Real.pi, g (circleMap 0 r θ) := by
  unfold circleOp
  simp only [circleIntegral, deriv_circleMap, smul_eq_mul]
  have h : ∀ θ : ℝ, circleMap 0 r θ * I * ((circleMap 0 r θ)⁻¹ * g (circleMap 0 r θ)) =
      I * g (circleMap 0 r θ) := by
    intro θ
    have hne : circleMap 0 r θ ≠ 0 := circleMap_ne_center hr
    field_simp
  simp_rw [h]
  rw [intervalIntegral.integral_const_mul, ← mul_assoc]
  congr 1
  have hpi : (Real.pi : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 Real.pi_ne_zero
  push_cast
  field_simp

/-- Fubini for two interval integrals of a jointly continuous integrand. -/
theorem intervalIntegral_swap_of_continuous {a b c d : ℝ} (hab : a ≤ b) (hcd : c ≤ d)
    {f : ℝ → ℝ → ℂ} (hf : Continuous fun q : ℝ × ℝ => f q.1 q.2) :
    ∫ x in a..b, ∫ y in c..d, f x y = ∫ y in c..d, ∫ x in a..b, f x y := by
  simp only [intervalIntegral.integral_of_le hab, intervalIntegral.integral_of_le hcd]
  have hunc : Function.uncurry f = fun q : ℝ × ℝ => f q.1 q.2 := rfl
  have hint : Integrable (Function.uncurry f)
      ((volume.restrict (Ioc a b)).prod (volume.restrict (Ioc c d))) := by
    rw [Measure.prod_restrict]
    have h1 : IntegrableOn (Function.uncurry f) (Icc a b ×ˢ Icc c d) (volume.prod volume) := by
      rw [hunc]
      exact hf.continuousOn.integrableOn_compact (isCompact_Icc.prod isCompact_Icc)
    exact h1.mono_set (prod_mono Ioc_subset_Icc_self Ioc_subset_Icc_self)
  exact integral_integral_swap hint

/-- Two circle operators with a jointly continuous integrand commute. -/
theorem circleOp_circleOp_swap {r ρ : ℝ} (hr : 0 < r) (hρ : 0 < ρ) {K : ℂ → ℂ → ℂ}
    (hK : ContinuousOn (fun p : ℂ × ℂ => K p.1 p.2)
      (Metric.sphere (0 : ℂ) ρ ×ˢ Metric.sphere (0 : ℂ) r)) :
    circleOp r (fun w => circleOp ρ fun z => K z w) =
      circleOp ρ fun z => circleOp r fun w => K z w := by
  have hc : Continuous fun q : ℝ × ℝ => K (circleMap 0 ρ q.2) (circleMap 0 r q.1) := by
    refine hK.comp_continuous ((continuous_circleMap 0 ρ).comp continuous_snd |>.prodMk
      ((continuous_circleMap 0 r).comp continuous_fst)) fun q => ?_
    exact ⟨circleMap_mem_sphere 0 hρ.le _, circleMap_mem_sphere 0 hr.le _⟩
  simp only [circleOp_eq_integral hr.ne', circleOp_eq_integral hρ.ne',
    intervalIntegral.integral_const_mul]
  rw [mul_left_comm]
  congr 2
  exact intervalIntegral_swap_of_continuous (by positivity) (by positivity) hc

/-- The iterated operator at radius `r` commutes with a circle operator at radius `ρ`. -/
theorem iterOp_circleOp_swap : ∀ (d : ℕ) {r ρ : ℝ}, 0 < r → 0 < ρ → ∀ {K : ℂ → (Fin d → ℂ) → ℂ},
    ContinuousOn (fun p : ℂ × (Fin d → ℂ) => K p.1 p.2) (Metric.sphere (0 : ℂ) ρ ×ˢ torusSet d r) →
    iterOp d r (fun w => circleOp ρ fun z => K z w) = circleOp ρ fun z => iterOp d r (K z)

theorem differentiableOn_circleOp_cauchyKernel {ρ : ℝ} (hρ : 0 < ρ) {g : ℂ → ℂ}
    (hg : ContinuousOn g (Metric.sphere (0 : ℂ) ρ)) :
    DifferentiableOn ℂ (fun x => circleOp ρ fun z => (1 - x / z)⁻¹ * g z) (Metric.ball 0 ρ) := by
  have hint : CircleIntegrable g 0 ρ := hg.circleIntegrable hρ.le
  set R : NNReal := ⟨ρ, hρ.le⟩ with hR
  have hRρ : (R : ℝ) = ρ := rfl
  have hRpos : 0 < R := by
    rw [← NNReal.coe_pos, hRρ]; exact hρ
  have hps := hasFPowerSeriesOn_cauchy_integral (c := 0) (R := R) (by rw [hRρ]; exact hint) hRpos
  have hdiff := hps.differentiableOn
  rw [Metric.eball_coe, hRρ] at hdiff
  refine hdiff.congr fun x hx => ?_
  have hx' : ‖x‖ < ρ := by simpa using hx
  unfold circleOp
  rw [smul_eq_mul]
  congr 1
  refine circleIntegral.integral_congr hρ.le fun z hz => ?_
  have hz' : ‖z‖ = ρ := by simpa using hz
  have hz0 : z ≠ 0 := by
    intro h; rw [h, norm_zero] at hz'; exact hρ.ne hz'
  have hzx : z - x ≠ 0 := by
    intro h
    have : z = x := sub_eq_zero.1 h
    rw [this] at hz'; linarith
  simp only [smul_eq_mul]
  field_simp

/-- **The gate**: the several-variable Cauchy coefficient of the slice `F(x, ·)` is holomorphic in
the parameter `x` on the disc of radius `ρ ∈ (r, R)`. -/
theorem differentiableOn_polyCoeff_param {d : ℕ} {r ρ R : ℝ} (hr : 0 < r) (hrρ : r < ρ)
    (hρR : ρ < R) {F : (Fin (d + 1) → ℂ) → ℂ} (hF : DifferentiableOn ℂ F (openPolydisc (d + 1) R))
    (γ' : Fin d → ℕ) :
    DifferentiableOn ℂ (fun x => polyCoeff d r (fun w' => F (Fin.cons x w')) γ')
      (Metric.ball 0 ρ) := by
  have hρ : 0 < ρ := hr.trans hrρ
  have hrR : r < R := hrρ.trans hρR
  have htorus : ∀ w' ∈ torusSet d r, w' ∈ openPolydisc d R := by
    intro w' hw'
    rw [mem_torusSet] at hw'
    rw [mem_openPolydisc]
    intro i; rw [hw' i]; exact hrR
  have hP : ContinuousOn (fun w' : Fin d → ℂ => ∏ i, (w' i)⁻¹ ^ γ' i) (torusSet d r) := by
    refine continuousOn_finsetProd _ fun i _ => ?_
    refine ContinuousOn.pow ?_ _
    refine ContinuousOn.inv₀ (continuous_apply i).continuousOn fun w' hw' => ?_
    rw [mem_torusSet] at hw'
    intro h; have := hw' i; rw [h, norm_zero] at this; exact hr.ne this
  -- continuity of the slice integrand on `sphere ρ × torus r`
  have hGcont : ContinuousOn (fun p : ℂ × (Fin d → ℂ) => F (Fin.cons p.1 p.2) *
      ∏ i, (p.2 i)⁻¹ ^ γ' i) (Metric.sphere (0 : ℂ) ρ ×ˢ torusSet d r) := by
    refine ContinuousOn.mul ?_ (hP.comp continuous_snd.continuousOn fun p hp => hp.2)
    refine hF.continuousOn.comp continuous_fin_cons_pair.continuousOn fun p hp => ?_
    have h1 : ‖p.1‖ < R := by
      have : ‖p.1‖ = ρ := by simpa using hp.1
      rw [this]; exact hρR
    exact cons_mem_openPolydisc h1 (htorus _ hp.2)
  have hg : ContinuousOn (fun z => polyCoeff d r (fun w' => F (Fin.cons z w')) γ')
      (Metric.sphere (0 : ℂ) ρ) := by
    unfold polyCoeff
    exact continuousOn_iterOp_param d hr (S := Metric.sphere (0 : ℂ) ρ)
      (G := fun z w' => F (Fin.cons z w') * ∏ i, (w' i)⁻¹ ^ γ' i) hGcont
  have key : ∀ x ∈ Metric.ball (0 : ℂ) ρ, polyCoeff d r (fun w' => F (Fin.cons x w')) γ' =
      circleOp ρ fun z => (1 - x / z)⁻¹ * polyCoeff d r (fun w' => F (Fin.cons z w')) γ' := by
    intro x hx
    have hx' : ‖x‖ < ρ := by simpa using hx
    unfold polyCoeff
    have hA : ∀ w' ∈ torusSet d r, F (Fin.cons x w') * ∏ i, (w' i)⁻¹ ^ γ' i =
        circleOp ρ fun z => (1 - x / z)⁻¹ * (F (Fin.cons z w') * ∏ i, (w' i)⁻¹ ^ γ' i) := by
      intro w' hw'
      have hslice : DiffContOnCl ℂ (fun t : ℂ => F (Fin.cons t w')) (Metric.ball 0 ρ) := by
        have hd : DifferentiableOn ℂ (fun t : ℂ => F (Fin.cons t w')) (Metric.ball 0 R) := by
          refine hF.comp (differentiable_cons_left w').differentiableOn fun t ht => ?_
          exact cons_mem_openPolydisc (by simpa using ht) (htorus _ hw')
        exact hd.diffContOnCl_ball (Metric.closedBall_subset_ball hρR)
      have hc := circleOp_cauchy hρ hslice hx'
      rw [← hc, mul_comm, ← circleOp_const_mul]
      congr 1; funext z; ring
    rw [iterOp_congr d hr.le hA]
    have hK : ContinuousOn (fun p : ℂ × (Fin d → ℂ) => (1 - x / p.1)⁻¹ *
        (F (Fin.cons p.1 p.2) * ∏ i, (p.2 i)⁻¹ ^ γ' i))
        (Metric.sphere (0 : ℂ) ρ ×ˢ torusSet d r) := by
      refine ContinuousOn.mul ?_ hGcont
      refine ContinuousOn.inv₀ ?_ fun p hp => ?_
      · refine continuousOn_const.sub (continuousOn_const.div continuous_fst.continuousOn ?_)
        intro p hp
        have : ‖p.1‖ = ρ := by simpa using hp.1
        intro h; rw [h, norm_zero] at this; exact hρ.ne this
      · have hp1 : ‖p.1‖ = ρ := by simpa using hp.1
        have hp0 : p.1 ≠ 0 := by
          intro h; rw [h, norm_zero] at hp1; exact hρ.ne hp1
        intro h
        have : x = p.1 := by
          have h' : x / p.1 = 1 := by linear_combination -h
          rwa [div_eq_one_iff_eq hp0] at h'
        rw [this] at hx'; linarith
    rw [iterOp_circleOp_swap d hr hρ hK]
    congr 1; funext z
    exact iterOp_const_mul d r _ _
  exact (differentiableOn_circleOp_cauchyKernel hρ hg).congr key

end Laplace.Grammar

```
### Laplace/Grammar/CoordDeriv.lean

```lean
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

theorem is claimed. Ordinary `iteratedDeriv`
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

/-- The real-part family used in Headline XXXII is `Re(∂^γ F(0)/γ!)`. -/
theorem polyRealCoeff_eq {d : ℕ} {r R : ℝ} (hr : 0 < r) (hrR : r < R) {F : (Fin d → ℂ) → ℂ}
    (hF : DifferentiableOn ℂ F (openPolydisc d R)) (γ : Fin d → ℕ) :
    polyRealCoeff d r F γ = (coordDeriv d F γ / multiFactorial γ).re := by
  unfold polyRealCoeff
  rw [polyCoeff_eq_coordDeriv_div d hr hrR hF γ]

end Laplace.Grammar

```
### Laplace/Grammar/TaylorTreeDerivatives.lean

```lean
/-!
# The Taylor tree with Taylor-derivative coefficient families (Stage 8c — Headline XXXIII)

Unit 268 (Astra #32, unit 4 of the derivative-identification sprint). The coefficient families of
Headline XXXII are identified with the normalised Taylor derivatives: `taylorFamily d F γ =
Re(∂^γ F(0)/γ!)` (`polyRealCoeff_eq_taylorFamily`), and the paper-facing theorem
`thm_TaylorTree_taylor` states `thm:TaylorTree` / `cor:standardintegralexp` for these families
directly: for real `ξ, η` on `(0,b]^d` with holomorphic `Fξ, Fη` on the polydisc of radius `R > b`
agreeing with `ξ, η` in real part on the box, the Taylor-tree conclusion holds for the families
`γ ↦ Re(∂^γ Fξ(0)/γ!)`, `γ ↦ Re(∂^γ Fη(0)/γ!)`, and the family integral is the original `Z(N)`.

**Non-claims.** `∂^γ` is the fixed-order iterated coordinate derivative `coordDeriv` (no
permutation-invariance theorem). The families are the Taylor coefficients of the canonical
real-analytic representative `Re F` at `0`, not derivatives of the supplied real functions `ξ, η`,
which are constrained only on the positive box `(0,b]^d` (in particular `taylorFamily Fξ 0 =
Re Fξ(0)`, which need not equal the supplied value `ξ(0)`); when `Fξ` is a genuine holomorphic
extension of a real-analytic `ξ` from a real neighbourhood of `0`, these are the Taylor coefficients
of `ξ`.
-/

/-- The normalised Taylor-derivative family `γ ↦ Re(∂^γ F(0)/γ!)`. -/
noncomputable def taylorFamily (d : ℕ) (F : (Fin d → ℂ) → ℂ) : CoeffFamily d :=
  fun γ => (coordDeriv d F γ / multiFactorial γ).re

/-- The real Cauchy-coefficient family of Headline XXXII is the Taylor-derivative family. -/
theorem polyRealCoeff_eq_taylorFamily {d : ℕ} {r R : ℝ} (hr : 0 < r) (hrR : r < R)
    {F : (Fin d → ℂ) → ℂ} (hF : DifferentiableOn ℂ F (openPolydisc d R)) :
    polyRealCoeff d r F = taylorFamily d F :=
  funext (polyRealCoeff_eq hr hrR hF)

/-- The constant coefficient is `Re F(0)`. -/
theorem taylorFamily_zero (d : ℕ) (F : (Fin d → ℂ) → ℂ) : taylorFamily d F 0 = (F 0).re := by
  unfold taylorFamily
  rw [coordDeriv_zero]
  simp [multiFactorial]

/-- **Headline XXXIII — `thm:TaylorTree` with Taylor-derivative coefficients, every dimension.**
For real `ξ, η` on `(0,b]^d` with holomorphic `Fξ, Fη` on the polydisc `{|zᵢ| < R}`, `R > b`,
whose real parts agree with `ξ, η` on the box, the Taylor-tree conclusion holds for the families
`γ ↦ Re(∂^γ Fξ(0)/γ!)`, `γ ↦ Re(∂^γ Fη(0)/γ!)` and the family integral is the original
`Z(N) = ∫_{(0,b]^d} η u^h e^{-βN u^{2k} + β√N u^k ξ(u)} du`. -/
theorem thm_TaylorTree_taylor (n : ℕ) (h k : Fin (n + 1) → ℕ) (hk : ∀ i, 0 < k i) (β : ℝ)
    (hβ : 0 < β) {b R : ℝ} (hb : 0 < b) (hbR : b < R)
    {Fξ Fη : (Fin (n + 1) → ℂ) → ℂ} {ξ η : (Fin (n + 1) → ℝ) → ℝ}
    (hFξ : DifferentiableOn ℂ Fξ (openPolydisc (n + 1) R))
    (hFη : DifferentiableOn ℂ Fη (openPolydisc (n + 1) R))
    (hξ : ∀ u ∈ piBox (n + 1) (Ioc 0 b), (Fξ fun i => (u i : ℂ)).re = ξ u)
    (hη : ∀ u ∈ piBox (n + 1) (Ioc 0 b), (Fη fun i => (u i : ℂ)).re = η u) :
    ∃ C : ℝ → ℕ → ℝ,
      TaylorTreeConclusion n h k β b (taylorFamily (n + 1) Fξ) (taylorFamily (n + 1) Fη) C ∧
      ∀ N, familyPhaseIntegralBox n h k β N b (taylorFamily (n + 1) Fξ)
        (taylorFamily (n + 1) Fη) = origPhaseIntegral n h k β N b ξ η := by
  have hbr : b < (b + R) / 2 := by linarith
  have hrR : (b + R) / 2 < R := by linarith
  have hr : 0 < (b + R) / 2 := by linarith
  have H := thm_TaylorTree_analytic n h k hk β hβ hb hbr hrR hFξ hFη hξ hη
  rwa [polyRealCoeff_eq_taylorFamily hr hrR hFξ, polyRealCoeff_eq_taylorFamily hr hrR hFη] at H

end Laplace.Grammar

```


## Full source of the identification (unit 267)

```lean
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


```

## Questions
1. Is `polyCoeff_eq_coordDeriv_div` correct as stated (radii, hypotheses, the factorial `∏ γᵢ!`, the order convention), and is the proof sketch sound (in particular the use of the induction hypothesis as a local identity, and the radius margin `closedBall r ⊂ ball ρ`, `ρ < R`)?
2. Is `coordDeriv` (fixed order, tail first, head last, ordinary `iteratedDeriv` at 0) an honest rendering of the paper's `∂^γ F(0)`? What exact non-claim wording should accompany it?
3. Is the `circleOp_eq_integral` identity `A_r(g) = (2π)⁻¹ ∫₀^{2π} g(r e^{iθ}) dθ` correct, and is the Fubini lemma `iterOp_circleOp_swap` correctly hypothesised (continuity on `sphere ρ × torus r` only)?
4. Headline XXXIII: does `thm_TaylorTree_taylor` now state `thm:TaylorTree`/`cor:standardintegralexp` under the paper's own hypothesis with the paper's coefficient data? List precisely what remains a non-claim (we believe: fixed-order derivatives; families are Taylor coefficients of `Re F` at 0, not of the supplied `ξ, η` off the box; cutoff independence = independence from the spectral threshold; support containment ≠ nonvanishing; no resolution/general-domain/Mellin-continuation/posterior-weak-convergence claims).
5. Any defect, or wording to fix, before freezing the Taylor-tree programme at this pin? Verdict per unit (pass / qualified pass / fail) and an overall verdict.
