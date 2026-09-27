/-
Copyright (c) 2026 Timaeus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Timaeus
-/
import Laplace.Multi.DataDissipation
import Laplace.Multi.AngularBound
import Laplace.Multi.TiltVarianceComparison

/-!
# The normal-speed lower bound near a face (scalar Schur complement)

Let `q` be a probability law, `ℓ ≥ 0` a bounded slack with face `A = {ℓ = 0}` of mass `p = q(A)`
and off-face mass `ε = 1 − p`, and `f` a bounded tangential observable with `|f| ≤ K` and
`K² ≤ κ Var_q f` (tangential coercivity). Then for every `a₀`,

  `Var_q(a₀ ℓ + f) ≥ a₀² Var_q ℓ (1 − 4κ ε / p)`   (`facet_schur_bound`),

because `|Cov_q(ℓ, f)| ≤ 2K E_q ℓ` (one-sided centring), the cross term is absorbed by completing
the square, and the mass at zero gives `(E_q ℓ)² ≤ ε E_q ℓ² ≤ (ε/p) Var_q ℓ`. This is the Schur
complement estimate of the facet accessibility theorem without matrices: once the off-face mass is
small, the Fisher speed of any path is at least half the normal speed `|a₀| √Var_q ℓ`.
-/

open MeasureTheory Set

namespace Laplace.Multi

section Schur

variable {X : Type*} [MeasurableSpace X] [Nonempty X] (q : Measure X) [IsProbabilityMeasure q]

omit [Nonempty X] [IsProbabilityMeasure q] in
theorem lawCov_const_mul_left' (a : ℝ) (f g : X → ℝ) :
    lawCov q (fun x ↦ a * f x) g = a * lawCov q f g := by
  unfold lawCov
  simp only [mul_assoc, integral_const_mul]
  ring

omit [Nonempty X] [IsProbabilityMeasure q] in
theorem lawCov_const_mul_self (a : ℝ) (f : X → ℝ) :
    lawCov q (fun x ↦ a * f x) (fun x ↦ a * f x) = a ^ 2 * lawCov q f f := by
  rw [lawCov_const_mul_left', lawCov_comm, lawCov_const_mul_left', lawCov_comm]
  ring

omit [Nonempty X] in
/-- The variance of a sum. -/
theorem lawCov_add_self {φ ψ : X → ℝ} (hφ : Bdd φ) (hψ : Bdd ψ) :
    lawCov q (fun x ↦ φ x + ψ x) (fun x ↦ φ x + ψ x) =
      lawCov q φ φ + 2 * lawCov q φ ψ + lawCov q ψ ψ := by
  have e : (fun x ↦ φ x + ψ x) = fun x ↦ φ x - (-ψ x) := funext fun x ↦ by ring
  rw [e, lawCov_sub_self q hφ (bdd_neg hψ), lawCov_neg_right_eq, lawCov_neg_left,
    lawCov_neg_right_eq]
  ring

omit [Nonempty X] in
/-- **Cauchy–Schwarz on the off-face set**: `(E_q ℓ)² ≤ q(Aᶜ) E_q ℓ²` for `A = {ℓ = 0}`. -/
theorem sq_integral_le_compl_mul_integral_sq {ℓ : X → ℝ} (hℓ : Bdd ℓ) :
    (∫ x, ℓ x ∂q) ^ 2 ≤ q.real {x | ℓ x = 0}ᶜ * ∫ x, ℓ x * ℓ x ∂q := by
  have hA : MeasurableSet {x | ℓ x = 0} := measurableSet_eq_fun hℓ.1 measurable_const
  have hind : Bdd ({x | ℓ x = 0}ᶜ.indicator fun _ ↦ (1 : ℝ)) :=
    ⟨measurable_const.indicator hA.compl, 1, fun x ↦ by
      by_cases hx : x ∈ {x | ℓ x = 0}ᶜ <;> simp [hx]⟩
  have e : ∀ x, ℓ x = ℓ x * ({x | ℓ x = 0}ᶜ.indicator fun _ ↦ (1 : ℝ)) x := fun x ↦ by
    by_cases hx : ℓ x = 0
    · simp [hx]
    · have : x ∈ {x | ℓ x = 0}ᶜ := hx
      simp [this]
  have hsq : ∀ x, ({x | ℓ x = 0}ᶜ.indicator fun _ ↦ (1 : ℝ)) x *
      ({x | ℓ x = 0}ᶜ.indicator fun _ ↦ (1 : ℝ)) x = ({x | ℓ x = 0}ᶜ.indicator fun _ ↦ (1 : ℝ)) x :=
    fun x ↦ by by_cases hx : x ∈ {x | ℓ x = 0}ᶜ <;> simp [hx]
  calc (∫ x, ℓ x ∂q) ^ 2
      = (∫ x, ℓ x * ({x | ℓ x = 0}ᶜ.indicator fun _ ↦ (1 : ℝ)) x ∂q) ^ 2 := by
        congr 1
        exact integral_congr_ae (ae_of_all _ e)
    _ ≤ (∫ x, ℓ x * ℓ x ∂q) * ∫ x, ({x | ℓ x = 0}ᶜ.indicator fun _ ↦ (1 : ℝ)) x *
          ({x | ℓ x = 0}ᶜ.indicator fun _ ↦ (1 : ℝ)) x ∂q :=
        integral_mul_sq_le (integrable_of_bdd_prob q (hℓ.mul hℓ))
          (integrable_of_bdd_prob q (hind.mul hind)) (integrable_of_bdd_prob q (hℓ.mul hind))
    _ = q.real {x | ℓ x = 0}ᶜ * ∫ x, ℓ x * ℓ x ∂q := by
        rw [mul_comm]
        congr 1
        simp_rw [hsq]
        exact integral_indicator_one hA.compl

omit [Nonempty X] in
/-- **The mass at zero controls the second moment**: `q(A) E_q ℓ² ≤ Var_q ℓ`. -/
theorem mass_mul_integral_sq_le_lawCov {ℓ : X → ℝ} (hℓ : Bdd ℓ) :
    q.real {x | ℓ x = 0} * ∫ x, ℓ x * ℓ x ∂q ≤ lawCov q ℓ ℓ := by
  have hA : MeasurableSet {x | ℓ x = 0} := measurableSet_eq_fun hℓ.1 measurable_const
  have h1 := sq_integral_le_compl_mul_integral_sq q hℓ
  have h2 := measureReal_add_measureReal_compl (μ := q) hA
  rw [probReal_univ] at h2
  have h3 : q.real {x | ℓ x = 0} = 1 - q.real {x | ℓ x = 0}ᶜ := by linarith
  rw [h3, sub_mul, one_mul, lawCov, sq] at *
  linarith

omit [Nonempty X] in
/-- **The slack mean against the slack variance**: `(E_q ℓ)² ≤ (ε/p) Var_q ℓ`. -/
theorem sq_integral_le_div_mul_lawCov {ℓ : X → ℝ} (hℓ : Bdd ℓ)
    (hp : 0 < q.real {x | ℓ x = 0}) :
    (∫ x, ℓ x ∂q) ^ 2 ≤ q.real {x | ℓ x = 0}ᶜ / q.real {x | ℓ x = 0} * lawCov q ℓ ℓ := by
  have h1 := sq_integral_le_compl_mul_integral_sq q hℓ
  have h2 := mass_mul_integral_sq_le_lawCov q hℓ
  have hε : 0 ≤ q.real {x | ℓ x = 0}ᶜ := measureReal_nonneg
  rw [div_mul_eq_mul_div, le_div_iff₀ hp]
  calc (∫ x, ℓ x ∂q) ^ 2 * q.real {x | ℓ x = 0}
      ≤ q.real {x | ℓ x = 0}ᶜ * (∫ x, ℓ x * ℓ x ∂q) * q.real {x | ℓ x = 0} := by gcongr
    _ = q.real {x | ℓ x = 0}ᶜ * (q.real {x | ℓ x = 0} * ∫ x, ℓ x * ℓ x ∂q) := by ring
    _ ≤ q.real {x | ℓ x = 0}ᶜ * lawCov q ℓ ℓ := by gcongr

/-- **Completing the square**: with `|Cov_q(ℓ, f)| ≤ 2 K E_q ℓ` and `K² ≤ κ Var_q f`,
`Var_q(a₀ ℓ + f) ≥ a₀² (Var_q ℓ − 4κ (E_q ℓ)²)`. -/
theorem lawCov_add_self_ge {ℓ f : X → ℝ} (hℓ : Bdd ℓ) (hℓ0 : ∀ x, 0 ≤ ℓ x) (hf : Bdd f)
    {K : ℝ} (hK : ∀ x, |f x| ≤ K) {κ : ℝ} (hκ : 0 ≤ κ) (hKV : K ^ 2 ≤ κ * lawCov q f f)
    (a₀ : ℝ) :
    a₀ ^ 2 * (lawCov q ℓ ℓ - 4 * κ * (∫ x, ℓ x ∂q) ^ 2) ≤
      lawCov q (fun x ↦ a₀ * ℓ x + f x) (fun x ↦ a₀ * ℓ x + f x) := by
  have hcov : |lawCov q ℓ f| ≤ 2 * K * ∫ x, ℓ x ∂q := by
    rw [lawCov_comm]
    exact abs_lawCov_le_mul_integral_of_nonneg q hf hK hℓ hℓ0
  have hL : 0 ≤ ∫ x, ℓ x ∂q := integral_nonneg hℓ0
  have hVf : 0 ≤ lawCov q f f := lawCov_self_nonneg q hf
  have hK0 : 0 ≤ K := (abs_nonneg _).trans (hK (Classical.arbitrary X))
  rw [lawCov_add_self q (Bdd.const_mul a₀ hℓ) hf, lawCov_const_mul_self, lawCov_const_mul_left']
  -- the cross term: `2 a₀ Cov ≥ −4 |a₀| K L ≥ −(4 κ a₀² L² + Var f)`
  set L := ∫ x, ℓ x ∂q with hLdef
  set Vf := lawCov q f f with hVfdef
  have hcross : -(4 * κ * a₀ ^ 2 * L ^ 2 + Vf) ≤ 2 * (a₀ * lawCov q ℓ f) := by
    have h1 : -(2 * |a₀| * (2 * K * L)) ≤ 2 * (a₀ * lawCov q ℓ f) := by
      have := neg_abs_le (a₀ * lawCov q ℓ f)
      rw [abs_mul] at this
      nlinarith [mul_le_mul_of_nonneg_left hcov (abs_nonneg a₀)]
    have hu : 0 ≤ 2 * |a₀| * L := by positivity
    have hK' : K ≤ √κ * √Vf := by
      rw [← Real.sqrt_mul hκ]
      exact (Real.le_sqrt hK0 (mul_nonneg hκ hVf)).2 hKV
    have hkey : 2 * (2 * |a₀| * L) * (√κ * √Vf) ≤ κ * (2 * |a₀| * L) ^ 2 + Vf := by
      have h := sq_nonneg (√κ * (2 * |a₀| * L) - √Vf)
      have e : (√κ * (2 * |a₀| * L) - √Vf) ^ 2 =
          √κ ^ 2 * (2 * |a₀| * L) ^ 2 - 2 * (2 * |a₀| * L) * (√κ * √Vf) + √Vf ^ 2 := by ring
      rw [Real.sq_sqrt hκ, Real.sq_sqrt hVf] at e
      linarith
    have h2 : 2 * |a₀| * (2 * K * L) ≤ 4 * κ * a₀ ^ 2 * L ^ 2 + Vf := by
      have hsq : (2 * |a₀| * L) ^ 2 = 4 * a₀ ^ 2 * L ^ 2 := by rw [mul_pow, mul_pow, sq_abs]; ring
      have h3 : 2 * (2 * |a₀| * L) * K ≤ 2 * (2 * |a₀| * L) * (√κ * √Vf) :=
        mul_le_mul_of_nonneg_left hK' (by positivity)
      nlinarith [hkey, h3, hsq]
    linarith
  linarith

/-- **The scalar Schur complement bound**: `Var_q(a₀ ℓ + f) ≥ a₀² Var_q ℓ (1 − 4κ ε/p)`. -/
theorem facet_schur_bound {ℓ f : X → ℝ} (hℓ : Bdd ℓ) (hℓ0 : ∀ x, 0 ≤ ℓ x)
    (hp : 0 < q.real {x | ℓ x = 0}) (hf : Bdd f) {K : ℝ} (hK : ∀ x, |f x| ≤ K) {κ : ℝ}
    (hκ : 0 ≤ κ) (hKV : K ^ 2 ≤ κ * lawCov q f f) (a₀ : ℝ) :
    a₀ ^ 2 * lawCov q ℓ ℓ * (1 - 4 * κ * (q.real {x | ℓ x = 0}ᶜ / q.real {x | ℓ x = 0})) ≤
      lawCov q (fun x ↦ a₀ * ℓ x + f x) (fun x ↦ a₀ * ℓ x + f x) := by
  refine le_trans ?_ (lawCov_add_self_ge q hℓ hℓ0 hf hK hκ hKV a₀)
  have h := sq_integral_le_div_mul_lawCov q hℓ hp
  have h' := mul_le_mul_of_nonneg_left h (mul_nonneg (sq_nonneg a₀) hκ)
  nlinarith [h']

end Schur

end Laplace.Multi
