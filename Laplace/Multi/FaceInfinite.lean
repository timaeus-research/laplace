/-
Copyright (c) 2026 Timaeus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Timaeus
-/
import Mathlib
import Laplace.Multi.FaceLimit

/-!
# Boundary rays: the zero-mass face costs infinite information

In the setting of `FaceLimit` (tilt `q_λ ∝ e^{−λV}π` of a positive prior by a bounded statistic `V`
with essential lower bound `α`), if the supporting face `{V = α}` has zero prior mass while every
neighbourhood `{V < α + ε}` has positive mass (`α` is the essential infimum), then
`KL(q_λ ‖ π̄) → +∞` (`tendsto_mixKL_zero_face`). The proof is the two-event data-processing bound
in tangent-line form: for any measurable `A`, `KL(q_λ ‖ π̄) ≥ q_λ(A) log (q_λ(A)/π̄(A)) − 1`
(`mixKL_ge_two_event`), with the tilt concentrating on `A_ε = {V < α + ε}`
(`tendsto_tilt_mass_compl`) while `π̄(A_ε) → 0` (`tendsto_face_nbhd_mass`).
-/

open MeasureTheory Filter Topology Set

namespace Laplace.Multi

variable {X : Type*} [MeasurableSpace X] {μ : Measure X}

/-- The tangent-line inequality for `r log r` at `c`: `r log r ≥ r log c + r − c`. -/
theorem mul_log_ge_tangent {r c : ℝ} (hr : 0 < r) (hc : 0 < c) :
    r * Real.log c + r - c ≤ r * Real.log r := by
  have h := Real.log_le_sub_one_of_pos (div_pos hc hr)
  rw [Real.log_div hc.ne' hr.ne'] at h
  have h2 : r * (Real.log c - Real.log r) ≤ r * (c / r - 1) := mul_le_mul_of_nonneg_left h hr.le
  have h3 : r * (c / r) = c := by field_simp
  nlinarith [h2, h3]

section Face

variable [Nonempty X] {π : X → ℝ} (hπm : Measurable π) (hπi : Integrable π μ) (hπ : ∀ x, 0 < π x)
  (hπpos : 0 < ∫ x, π x ∂μ) {V : X → ℝ} (hVm : Measurable V) {M : ℝ} (hV : ∀ x, |V x| ≤ M)
  {α : ℝ} (hα : ∀ᵐ x ∂μ, α ≤ V x)
include hπm hπi hπ hπpos hVm hV

omit [Nonempty X] in
/-- The tilted weight `e^{−λV} π` as a `TiltData`. -/
theorem tiltData_face (lam : ℝ) : TiltData μ (baseWeight π V lam) V M :=
  tiltData_baseWeight_of_bounded (μ := μ) (L₀ := V) (Δ := V) hπm hπi (fun x ↦ (hπ x).le) hπpos
    hVm hV hVm hV lam

omit [Nonempty X] in
theorem priorZ_face_pos (lam : ℝ) : 0 < priorZ μ π V lam :=
  (tiltData_face hπm hπi hπ hπpos hVm hV lam).ν_pos

omit hπpos hV in
theorem integrable_face_weight (lam : ℝ) {f : X → ℝ} (hfm : Measurable f) {Mf : ℝ}
    (hf : ∀ x, |f x| ≤ Mf) (hπpos : 0 < ∫ x, π x ∂μ) (hV : ∀ x, |V x| ≤ M) :
    Integrable (fun x ↦ f x * (Real.exp (-(lam * V x)) * π x)) μ :=
  ((tiltData_face hπm hπi hπ hπpos hVm hV lam).integrable_tilt hfm hf lam 0).congr
    (Eventually.of_forall fun x ↦ by simp [baseWeight])

/-- **`KL(q_λ ‖ π̄)` as the `q_λ`-expectation of the log-ratio**
`ℓ_λ(x) = −λ V(x) + log ∫π − log Z_λ`. -/
theorem mixKL_face_eq_integral (lam : ℝ) :
    mixKL μ π (fun _ ↦ (0 : ℝ)) V lam 1 0 =
      (∫ x, (-(lam * V x) + (Real.log (∫ x, π x ∂μ) - Real.log (priorZ μ π V lam))) *
        (Real.exp (-(lam * V x)) * π x) ∂μ) / priorZ μ π V lam := by
  have hT : TiltData μ (baseWeight π (fun _ ↦ (0 : ℝ)) lam) V M :=
    tiltData_baseWeight_of_bounded (μ := μ) hπm hπi (fun x ↦ (hπ x).le) hπpos
      measurable_const (M₀ := 0) (fun _ ↦ by simp) hVm hV lam
  rw [hT.mixKL_eq (fun x ↦ (hπ x).le) 1 0]
  unfold mixLogZ mixExp
  have e0 : pathLoss (fun _ ↦ (0 : ℝ)) V 0 = fun _ ↦ (0 : ℝ) := by
    funext x; simp [pathLoss]
  have e1 : pathLoss (fun _ ↦ (0 : ℝ)) V 1 = V := by
    funext x; simp [pathLoss]
  rw [e0, e1]
  have hZ0 : priorZ μ π (fun _ ↦ (0 : ℝ)) lam = ∫ x, π x ∂μ := by
    unfold priorZ; simp
  have hZ := (priorZ_face_pos hπm hπi hπ hπpos hVm hV lam).ne'
  have hI1 := integrable_face_weight hπm hπi hπ hVm lam hVm hV hπpos hV
  have hI0 := integrable_face_weight hπm hπi hπ hVm lam (f := fun _ ↦ (1 : ℝ)) measurable_const
    (Mf := 1) (fun _ ↦ by simp) hπpos hV
  have hsplit : (∫ x, (-(lam * V x) + (Real.log (∫ x, π x ∂μ) - Real.log (priorZ μ π V lam))) *
      (Real.exp (-(lam * V x)) * π x) ∂μ) =
      -lam * (∫ x, V x * (Real.exp (-(lam * V x)) * π x) ∂μ) +
        (Real.log (∫ x, π x ∂μ) - Real.log (priorZ μ π V lam)) * priorZ μ π V lam := by
    have h1 : (∫ x, (-(lam * V x) + (Real.log (∫ x, π x ∂μ) - Real.log (priorZ μ π V lam))) *
        (Real.exp (-(lam * V x)) * π x) ∂μ) =
        ∫ x, (-lam * (V x * (Real.exp (-(lam * V x)) * π x)) +
          (Real.log (∫ x, π x ∂μ) - Real.log (priorZ μ π V lam)) *
            (1 * (Real.exp (-(lam * V x)) * π x))) ∂μ := by
      congr 1; funext x; ring
    rw [h1, integral_add (hI1.const_mul _) (hI0.const_mul _), integral_const_mul,
      integral_const_mul]
    unfold priorZ
    congr 2
    exact integral_congr_ae (Eventually.of_forall fun x ↦ one_mul _)
  rw [hZ0, hsplit]
  unfold priorExp priorZ at *
  have e2 : (∫ x, V x * Real.exp (-(lam * V x)) * π x ∂μ) =
      ∫ x, V x * (Real.exp (-(lam * V x)) * π x) ∂μ := by
    congr 1; funext x; ring
  rw [e2]
  field_simp
  ring

omit [Nonempty X] in
/-- The weighted tangent inequality for the log-ratio `ℓ_λ = log r`, `r = e^{−λV} Z₀ / Z_λ`:
`Z⁻¹ (log c + 1) w − c Z₀⁻¹ π ≤ Z⁻¹ ℓ w` pointwise, for every `c > 0`. -/
theorem tangent_weight_le (lam : ℝ) {c : ℝ} (hc : 0 < c) (x : X) :
    (priorZ μ π V lam)⁻¹ * (Real.log c + 1) * (Real.exp (-(lam * V x)) * π x) +
        (-(c * (∫ x, π x ∂μ)⁻¹)) * π x ≤
      (priorZ μ π V lam)⁻¹ *
        ((-(lam * V x) + (Real.log (∫ x, π x ∂μ) - Real.log (priorZ μ π V lam))) *
          (Real.exp (-(lam * V x)) * π x)) := by
  have hZ := priorZ_face_pos hπm hπi hπ hπpos hVm hV lam
  have hr : 0 < Real.exp (-(lam * V x)) * (∫ x, π x ∂μ) / priorZ μ π V lam := by positivity
  have hℓ : -(lam * V x) + (Real.log (∫ x, π x ∂μ) - Real.log (priorZ μ π V lam)) =
      Real.log (Real.exp (-(lam * V x)) * (∫ x, π x ∂μ) / priorZ μ π V lam) := by
    rw [Real.log_div (by positivity) hZ.ne', Real.log_mul (Real.exp_pos _).ne' hπpos.ne',
      Real.log_exp]
    ring
  have h := mul_le_mul_of_nonneg_left (mul_log_ge_tangent hr hc) (div_pos (hπ x) hπpos).le
  have e1 : (priorZ μ π V lam)⁻¹ * (Real.log c + 1) * (Real.exp (-(lam * V x)) * π x) +
      (-(c * (∫ x, π x ∂μ)⁻¹)) * π x =
      π x / (∫ x, π x ∂μ) *
        (Real.exp (-(lam * V x)) * (∫ x, π x ∂μ) / priorZ μ π V lam * Real.log c +
          Real.exp (-(lam * V x)) * (∫ x, π x ∂μ) / priorZ μ π V lam - c) := by
    field_simp
    ring
  have e2 : (priorZ μ π V lam)⁻¹ *
      (Real.log (Real.exp (-(lam * V x)) * (∫ x, π x ∂μ) / priorZ μ π V lam) *
        (Real.exp (-(lam * V x)) * π x)) =
      π x / (∫ x, π x ∂μ) * (Real.exp (-(lam * V x)) * (∫ x, π x ∂μ) / priorZ μ π V lam *
        Real.log (Real.exp (-(lam * V x)) * (∫ x, π x ∂μ) / priorZ μ π V lam)) := by
    field_simp
  rw [hℓ, e1, e2]
  exact h

omit [Nonempty X] hπm hπ hπpos hVm hV in
/-- Integral of a two-term linear form over a set. -/
theorem setIntegral_linear_form {w : X → ℝ} (hw : Integrable w μ) (A : Set X) (a b : ℝ) :
    ∫ x in A, (a * w x + b * π x) ∂μ = a * (∫ x in A, w x ∂μ) + b * ∫ x in A, π x ∂μ := by
  rw [integral_add (hw.integrableOn.const_mul a) (hπi.integrableOn.const_mul b),
    integral_const_mul, integral_const_mul]

/-- **The two-event lower bound**: for every measurable `A` with `π̄(A) > 0`,
`KL(q_λ ‖ π̄) ≥ q_λ(A) log (q_λ(A) / π̄(A)) − 1`, where `q_λ(A) = (∫_A e^{−λV}π)/Z_λ` and
`π̄(A) = (∫_A π)/(∫π)`. -/
theorem mixKL_ge_two_event (lam : ℝ) {A : Set X} (hA : MeasurableSet A)
    (hAπ : 0 < ∫ x in A, π x ∂μ) :
    ((∫ x in A, Real.exp (-(lam * V x)) * π x ∂μ) / priorZ μ π V lam) *
        Real.log (((∫ x in A, Real.exp (-(lam * V x)) * π x ∂μ) / priorZ μ π V lam) /
          ((∫ x in A, π x ∂μ) / ∫ x, π x ∂μ)) - 1 ≤
      mixKL μ π (fun _ ↦ (0 : ℝ)) V lam 1 0 := by
  rw [mixKL_face_eq_integral hπm hπi hπ hπpos hVm hV lam]
  have hZ := priorZ_face_pos hπm hπi hπ hπpos hVm hV lam
  have hw : Integrable (fun x ↦ Real.exp (-(lam * V x)) * π x) μ :=
    (integrable_face_weight hπm hπi hπ hVm lam (f := fun _ ↦ (1 : ℝ)) measurable_const (Mf := 1)
      (fun _ ↦ by simp) hπpos hV).congr (Eventually.of_forall fun x ↦ by simp)
  have hℓm : Measurable fun x ↦ -(lam * V x) + (Real.log (∫ x, π x ∂μ) -
      Real.log (priorZ μ π V lam)) := ((hVm.const_mul lam).neg).add_const _
  have hℓb : ∀ x, |-(lam * V x) + (Real.log (∫ x, π x ∂μ) - Real.log (priorZ μ π V lam))| ≤
      |lam| * M + |Real.log (∫ x, π x ∂μ) - Real.log (priorZ μ π V lam)| := fun x ↦ by
    calc _ ≤ |-(lam * V x)| + |Real.log (∫ x, π x ∂μ) - Real.log (priorZ μ π V lam)| :=
          abs_add_le _ _
      _ ≤ _ := by
          gcongr
          rw [abs_neg, abs_mul]
          exact mul_le_mul_of_nonneg_left (hV x) (abs_nonneg _)
  have hℓw := integrable_face_weight hπm hπi hπ hVm lam hℓm hℓb hπpos hV
  -- the face weight is bounded below by a multiple of the prior
  have hwpos : 0 < ∫ x in A, Real.exp (-(lam * V x)) * π x ∂μ := by
    have hlow : ∀ x ∈ A, Real.exp (-(|lam| * M)) * π x ≤ Real.exp (-(lam * V x)) * π x := by
      intro x _
      refine mul_le_mul_of_nonneg_right (Real.exp_le_exp.2 ?_) (hπ x).le
      have h1 : lam * V x ≤ |lam * V x| := le_abs_self _
      have h2 : |lam * V x| ≤ |lam| * M := by
        rw [abs_mul]; exact mul_le_mul_of_nonneg_left (hV x) (abs_nonneg _)
      linarith
    have := setIntegral_mono_on (hπi.integrableOn.const_mul _) hw.integrableOn hA hlow
    rw [integral_const_mul] at this
    exact lt_of_lt_of_le (mul_pos (Real.exp_pos _) hAπ) this
  -- abbreviations
  set Z := priorZ μ π V lam with hZdef
  set Z₀ := ∫ x, π x ∂μ with hZ₀def
  set qA := (∫ x in A, Real.exp (-(lam * V x)) * π x ∂μ) / Z with hqA
  set pA := (∫ x in A, π x ∂μ) / Z₀ with hpA
  have hqApos : 0 < qA := div_pos hwpos hZ
  have hpApos : 0 < pA := div_pos hAπ hπpos
  have hc : 0 < qA / pA := div_pos hqApos hpApos
  -- split the integral
  have hsplit : (∫ x, (-(lam * V x) + (Real.log Z₀ - Real.log Z)) *
      (Real.exp (-(lam * V x)) * π x) ∂μ) / Z =
      Z⁻¹ * (∫ x in A, (-(lam * V x) + (Real.log Z₀ - Real.log Z)) *
        (Real.exp (-(lam * V x)) * π x) ∂μ) +
      Z⁻¹ * ∫ x in Aᶜ, (-(lam * V x) + (Real.log Z₀ - Real.log Z)) *
        (Real.exp (-(lam * V x)) * π x) ∂μ := by
    rw [div_eq_inv_mul, ← integral_add_compl hA hℓw, mul_add]
  -- the `A` part
  have hApart : qA * Real.log (qA / pA) ≤ Z⁻¹ * ∫ x in A,
      (-(lam * V x) + (Real.log Z₀ - Real.log Z)) * (Real.exp (-(lam * V x)) * π x) ∂μ := by
    have hmono := setIntegral_mono_on
      ((hw.const_mul (Z⁻¹ * (Real.log (qA / pA) + 1))).add
        (hπi.const_mul (-(qA / pA * Z₀⁻¹)))).integrableOn (hℓw.const_mul Z⁻¹).integrableOn hA
      (fun x _ ↦ tangent_weight_le hπm hπi hπ hπpos hVm hV lam hc x)
    rw [integral_const_mul] at hmono
    have hlin := setIntegral_linear_form hπi hw A (Z⁻¹ * (Real.log (qA / pA) + 1))
      (-(qA / pA * Z₀⁻¹))
    simp only [Pi.add_apply] at hmono
    rw [hlin] at hmono
    have e : Z⁻¹ * (Real.log (qA / pA) + 1) * (∫ x in A, Real.exp (-(lam * V x)) * π x ∂μ) +
        (-(qA / pA * Z₀⁻¹)) * ∫ x in A, π x ∂μ = qA * Real.log (qA / pA) := by
      rw [hqA, hpA]
      field_simp
      ring
    linarith
  -- the `Aᶜ` part
  have hAcpart : -1 ≤ Z⁻¹ * ∫ x in Aᶜ,
      (-(lam * V x) + (Real.log Z₀ - Real.log Z)) * (Real.exp (-(lam * V x)) * π x) ∂μ := by
    have hmono := setIntegral_mono_on
      ((hw.const_mul (Z⁻¹ * (Real.log 1 + 1))).add (hπi.const_mul (-(1 * Z₀⁻¹)))).integrableOn
      (hℓw.const_mul Z⁻¹).integrableOn hA.compl
      (fun x _ ↦ tangent_weight_le hπm hπi hπ hπpos hVm hV lam one_pos x)
    rw [integral_const_mul] at hmono
    have hlin := setIntegral_linear_form hπi hw Aᶜ (Z⁻¹ * (Real.log 1 + 1)) (-(1 * Z₀⁻¹))
    simp only [Pi.add_apply] at hmono
    rw [hlin, Real.log_one] at hmono
    have h1 : 0 ≤ ∫ x in Aᶜ, Real.exp (-(lam * V x)) * π x ∂μ :=
      setIntegral_nonneg hA.compl fun x _ ↦ (mul_pos (Real.exp_pos _) (hπ x)).le
    have h2 : ∫ x in Aᶜ, π x ∂μ ≤ Z₀ :=
      setIntegral_le_integral hπi (ae_of_all _ fun x ↦ (hπ x).le)
    have h3 : Z₀⁻¹ * ∫ x in Aᶜ, π x ∂μ ≤ 1 := by
      rw [← div_eq_inv_mul, div_le_one hπpos]; exact h2
    have h4 : 0 ≤ Z⁻¹ * (0 + 1) * ∫ x in Aᶜ, Real.exp (-(lam * V x)) * π x ∂μ := by
      positivity
    linarith
  rw [hsplit]
  linarith

omit hπm hπi hπ hπpos hVm hV in
theorem exp_neg_mul_le_of_le {lam a b : ℝ} (hlam : 0 ≤ lam) (h : a ≤ b) :
    Real.exp (-(lam * b)) ≤ Real.exp (-(lam * a)) := by
  rw [Real.exp_le_exp]
  nlinarith

/-- **Concentration of the tilt on the ε-neighbourhood of the face**: for `λ ≥ 0`,
`q_λ({V < α + ε}ᶜ) ≤ e^{−λε/2} (∫π) / ∫_{V < α + ε/2} π`. -/
theorem tilt_mass_compl_le {ε : ℝ}
    (hm : 0 < ∫ x in {x | V x < α + ε / 2}, π x ∂μ) {lam : ℝ} (hlam : 0 ≤ lam) :
    (∫ x in {x | V x < α + ε}ᶜ, Real.exp (-(lam * V x)) * π x ∂μ) / priorZ μ π V lam ≤
      Real.exp (-(lam * (ε / 2))) * (∫ x, π x ∂μ) / ∫ x in {x | V x < α + ε / 2}, π x ∂μ := by
  have hZ := priorZ_face_pos hπm hπi hπ hπpos hVm hV lam
  have hw : Integrable (fun x ↦ Real.exp (-(lam * V x)) * π x) μ :=
    (integrable_face_weight hπm hπi hπ hVm lam (f := fun _ ↦ (1 : ℝ)) measurable_const (Mf := 1)
      (fun _ ↦ by simp) hπpos hV).congr (Eventually.of_forall fun x ↦ by simp)
  have hA : MeasurableSet {x | V x < α + ε} := hVm measurableSet_Iio
  have hB : MeasurableSet {x | V x < α + ε / 2} := hVm measurableSet_Iio
  -- numerator bound
  have hnum : (∫ x in {x | V x < α + ε}ᶜ, Real.exp (-(lam * V x)) * π x ∂μ) ≤
      Real.exp (-(lam * (α + ε))) * ∫ x, π x ∂μ := by
    calc (∫ x in {x | V x < α + ε}ᶜ, Real.exp (-(lam * V x)) * π x ∂μ)
        ≤ ∫ x in {x | V x < α + ε}ᶜ, Real.exp (-(lam * (α + ε))) * π x ∂μ := by
          refine setIntegral_mono_on hw.integrableOn (hπi.integrableOn.const_mul _) hA.compl
            fun x hx ↦ ?_
          have hx' : α + ε ≤ V x := not_lt.1 hx
          exact mul_le_mul_of_nonneg_right (exp_neg_mul_le_of_le hlam hx') (hπ x).le
      _ = Real.exp (-(lam * (α + ε))) * ∫ x in {x | V x < α + ε}ᶜ, π x ∂μ := integral_const_mul _ _
      _ ≤ Real.exp (-(lam * (α + ε))) * ∫ x, π x ∂μ :=
          mul_le_mul_of_nonneg_left (setIntegral_le_integral hπi (ae_of_all _ fun x ↦ (hπ x).le))
            (Real.exp_pos _).le
  -- denominator bound
  have hden : Real.exp (-(lam * (α + ε / 2))) * (∫ x in {x | V x < α + ε / 2}, π x ∂μ) ≤
      priorZ μ π V lam := by
    calc Real.exp (-(lam * (α + ε / 2))) * (∫ x in {x | V x < α + ε / 2}, π x ∂μ)
        = ∫ x in {x | V x < α + ε / 2}, Real.exp (-(lam * (α + ε / 2))) * π x ∂μ :=
          (integral_const_mul _ _).symm
      _ ≤ ∫ x in {x | V x < α + ε / 2}, Real.exp (-(lam * V x)) * π x ∂μ := by
          refine setIntegral_mono_on (hπi.integrableOn.const_mul _) hw.integrableOn hB
            fun x hx ↦ ?_
          have hx' : V x ≤ α + ε / 2 := le_of_lt hx
          exact mul_le_mul_of_nonneg_right (exp_neg_mul_le_of_le hlam hx') (hπ x).le
      _ ≤ priorZ μ π V lam :=
          setIntegral_le_integral hw (ae_of_all _ fun x ↦ (mul_pos (Real.exp_pos _) (hπ x)).le)
  have hpos : 0 < Real.exp (-(lam * (α + ε / 2))) * ∫ x in {x | V x < α + ε / 2}, π x ∂μ := by
    positivity
  calc (∫ x in {x | V x < α + ε}ᶜ, Real.exp (-(lam * V x)) * π x ∂μ) / priorZ μ π V lam
      ≤ (Real.exp (-(lam * (α + ε))) * ∫ x, π x ∂μ) /
          (Real.exp (-(lam * (α + ε / 2))) * ∫ x in {x | V x < α + ε / 2}, π x ∂μ) :=
        div_le_div₀ (by positivity) hnum hpos hden
    _ = _ := by
        have e : Real.exp (-(lam * (α + ε))) =
            Real.exp (-(lam * (ε / 2))) * Real.exp (-(lam * (α + ε / 2))) := by
          rw [← Real.exp_add]; congr 1; ring
        rw [e]
        field_simp

/-- The mass of the ε-neighbourhood under the tilt tends to `1`: its complement tends to `0`. -/
theorem tendsto_tilt_mass_compl {ε : ℝ} (hε : 0 < ε)
    (hm : 0 < ∫ x in {x | V x < α + ε / 2}, π x ∂μ) :
    Tendsto (fun lam : ℝ ↦ (∫ x in {x | V x < α + ε}ᶜ, Real.exp (-(lam * V x)) * π x ∂μ) /
      priorZ μ π V lam) atTop (𝓝 0) := by
  have hlim : Tendsto (fun lam : ℝ ↦ Real.exp (-(lam * (ε / 2))) * (∫ x, π x ∂μ) /
      ∫ x in {x | V x < α + ε / 2}, π x ∂μ) atTop (𝓝 0) := by
    have h1 : Tendsto (fun lam : ℝ ↦ lam * (ε / 2)) atTop atTop :=
      tendsto_id.atTop_mul_const (by positivity)
    have h2 := (Real.tendsto_exp_neg_atTop_nhds_zero.comp h1).mul_const (∫ x, π x ∂μ)
    have h3 := h2.div_const (∫ x in {x | V x < α + ε / 2}, π x ∂μ)
    simpa [Function.comp_def] using h3
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hlim ?_ ?_
  · exact Eventually.of_forall fun lam ↦ div_nonneg
      (setIntegral_nonneg (hVm measurableSet_Iio).compl fun x _ ↦
        (mul_pos (Real.exp_pos _) (hπ x)).le)
      (priorZ_face_pos hπm hπi hπ hπpos hVm hV lam).le
  · filter_upwards [eventually_ge_atTop (0 : ℝ)] with lam hlam
    exact tilt_mass_compl_le hπm hπi hπ hπpos hVm hV hm hlam

/-- `q_λ(A) = 1 − q_λ(Aᶜ)`. -/
theorem tilt_mass_eq_one_sub (lam : ℝ) {A : Set X} (hA : MeasurableSet A) :
    (∫ x in A, Real.exp (-(lam * V x)) * π x ∂μ) / priorZ μ π V lam =
      1 - (∫ x in Aᶜ, Real.exp (-(lam * V x)) * π x ∂μ) / priorZ μ π V lam := by
  have hZ := priorZ_face_pos hπm hπi hπ hπpos hVm hV lam
  have hw : Integrable (fun x ↦ Real.exp (-(lam * V x)) * π x) μ :=
    (integrable_face_weight hπm hπi hπ hVm lam (f := fun _ ↦ (1 : ℝ)) measurable_const (Mf := 1)
      (fun _ ↦ by simp) hπpos hV).congr (Eventually.of_forall fun x ↦ by simp)
  have h := integral_add_compl hA hw
  unfold priorZ at hZ ⊢
  rw [eq_sub_iff_add_eq, ← add_div, h, div_self hZ.ne']

omit [Nonempty X] hπpos hVm hV in
include hα in
/-- **The prior mass of the ε-neighbourhoods of a zero-mass face tends to `0`.** -/
theorem tendsto_face_nbhd_mass (hVm : Measurable V) (hp0 : ∫ x in {x | V x = α}, π x ∂μ = 0) :
    Tendsto (fun n : ℕ ↦ ∫ x in {x | V x < α + 1 / ((n : ℝ) + 1)}, π x ∂μ) atTop (𝓝 0) := by
  have hF : MeasurableSet {x | V x = α} := hVm (measurableSet_singleton α)
  have hlim : ∫ x, {x | V x = α}.indicator π x ∂μ = 0 := by rw [integral_indicator hF, hp0]
  rw [← hlim]
  have hmeas : ∀ n : ℕ, MeasurableSet {x | V x < α + 1 / ((n : ℝ) + 1)} := fun n ↦
    hVm measurableSet_Iio
  have h := tendsto_integral_of_dominated_convergence (μ := μ)
    (F := fun n x ↦ {x | V x < α + 1 / ((n : ℝ) + 1)}.indicator π x)
    (f := fun x ↦ {x | V x = α}.indicator π x) π
    (fun n ↦ (hπm.indicator (hmeas n)).aestronglyMeasurable) hπi ?_ ?_
  · refine h.congr fun n ↦ ?_
    rw [integral_indicator (hmeas n)]
  · intro n
    refine ae_of_all _ fun x ↦ ?_
    rw [Real.norm_eq_abs, abs_of_nonneg (Set.indicator_nonneg (fun y _ ↦ (hπ y).le) x)]
    exact Set.indicator_le_self' (fun y _ ↦ (hπ y).le) x
  · filter_upwards [hα] with x hx
    by_cases hxF : V x = α
    · have : ∀ n : ℕ, {x | V x < α + 1 / ((n : ℝ) + 1)}.indicator π x = π x := fun n ↦
        Set.indicator_of_mem (by
          change V x < α + 1 / ((n : ℝ) + 1)
          have : (0 : ℝ) < 1 / ((n : ℝ) + 1) := by positivity
          rw [hxF]
          linarith) π
      simp only [this, Set.indicator_of_mem (show x ∈ {x | V x = α} from hxF)]
      exact tendsto_const_nhds
    · have hpos : 0 < V x - α := sub_pos.2 (lt_of_le_of_ne hx fun h ↦ hxF h.symm)
      rw [Set.indicator_of_notMem (show x ∉ {x | V x = α} from hxF)]
      obtain ⟨N, hN⟩ := exists_nat_one_div_lt hpos
      refine tendsto_const_nhds.congr' ?_
      filter_upwards [eventually_ge_atTop N] with n hn
      rw [Set.indicator_of_notMem]
      intro hxn
      simp only [Set.mem_ofPred_eq] at hxn
      have h1 : 1 / ((n : ℝ) + 1) ≤ 1 / ((N : ℝ) + 1) := by
        gcongr
      linarith

include hα in
/-- **Reaching a zero-mass face costs infinite information**: if `∫_{V=α} π = 0` while every
`{V < α + ε}` has positive mass, then `KL(q_λ ‖ π̄) → +∞`. -/
theorem tendsto_mixKL_zero_face
    (hmass : ∀ ε > 0, 0 < ∫ x in {x | V x < α + ε}, π x ∂μ)
    (hp0 : ∫ x in {x | V x = α}, π x ∂μ = 0) :
    Tendsto (fun lam : ℝ ↦ mixKL μ π (fun _ ↦ (0 : ℝ)) V lam 1 0) atTop atTop := by
  rw [tendsto_atTop]
  intro K
  -- a neighbourhood of the face with tiny prior mass
  obtain ⟨n, hn⟩ : ∃ n : ℕ, ∫ x in {x | V x < α + 1 / ((n : ℝ) + 1)}, π x ∂μ <
      Real.exp (-(2 * (|K| + 2))) * ∫ x, π x ∂μ :=
    ((tendsto_face_nbhd_mass hπm hπi hπ hα hVm hp0).eventually
      (gt_mem_nhds (by positivity))).exists
  set ε : ℝ := 1 / ((n : ℝ) + 1) with hεdef
  have hε : 0 < ε := by positivity
  have hA : MeasurableSet {x | V x < α + ε} := hVm measurableSet_Iio
  have hAπ : 0 < ∫ x in {x | V x < α + ε}, π x ∂μ := hmass ε hε
  have hm : 0 < ∫ x in {x | V x < α + ε / 2}, π x ∂μ := hmass (ε / 2) (by positivity)
  have hpA : (∫ x in {x | V x < α + ε}, π x ∂μ) / (∫ x, π x ∂μ) < Real.exp (-(2 * (|K| + 2))) := by
    rw [div_lt_iff₀ hπpos]; exact hn
  have hq := tendsto_tilt_mass_compl hπm hπi hπ hπpos hVm hV hε hm
  filter_upwards [hq.eventually (gt_mem_nhds (by norm_num : (0 : ℝ) < 1 / 2))] with lam hlam
  have key := mixKL_ge_two_event hπm hπi hπ hπpos hVm hV lam hA hAπ
  set qA := (∫ x in {x | V x < α + ε}, Real.exp (-(lam * V x)) * π x ∂μ) / priorZ μ π V lam
    with hqA
  set pA := (∫ x in {x | V x < α + ε}, π x ∂μ) / ∫ x, π x ∂μ with hpAdef
  have hqA1 : 1 / 2 ≤ qA := by
    rw [hqA, tilt_mass_eq_one_sub hπm hπi hπ hπpos hVm hV lam hA]
    linarith
  have hZ := priorZ_face_pos hπm hπi hπ hπpos hVm hV lam
  have hqAc : 0 ≤ (∫ x in {x | V x < α + ε}ᶜ, Real.exp (-(lam * V x)) * π x ∂μ) /
      priorZ μ π V lam :=
    div_nonneg (setIntegral_nonneg hA.compl fun x _ ↦ (mul_pos (Real.exp_pos _) (hπ x)).le) hZ.le
  have hqA2 : qA ≤ 1 := by
    rw [hqA, tilt_mass_eq_one_sub hπm hπi hπ hπpos hVm hV lam hA]
    linarith
  have hpApos : 0 < pA := div_pos hAπ hπpos
  have hqApos : 0 < qA := by linarith
  have hlog : Real.log (qA / pA) = Real.log qA - Real.log pA :=
    Real.log_div hqApos.ne' hpApos.ne'
  have h1 : Real.log (1 / 2) ≤ Real.log qA := Real.log_le_log (by norm_num) hqA1
  have h2 : Real.log pA ≤ -(2 * (|K| + 2)) := by
    have := Real.log_le_log hpApos hpA.le
    rwa [Real.log_exp] at this
  have h3 : Real.log (1 / 2) = -Real.log 2 := by rw [one_div, Real.log_inv]
  have h4 : Real.log 2 ≤ 1 := by
    have := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)
    linarith
  have hlow : 2 * |K| + 3 ≤ Real.log (qA / pA) := by
    rw [hlog]
    linarith
  have h5 : 1 / 2 * Real.log (qA / pA) ≤ qA * Real.log (qA / pA) :=
    mul_le_mul_of_nonneg_right hqA1 (by linarith [abs_nonneg K])
  have h6 : K ≤ |K| := le_abs_self K
  calc K ≤ qA * Real.log (qA / pA) - 1 := by linarith
    _ ≤ _ := key

end Face

end Laplace.Multi
