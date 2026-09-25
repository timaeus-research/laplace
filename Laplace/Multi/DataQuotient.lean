/-
Copyright (c) 2026 Timaeus Research. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniel Murfet
-/
import Mathlib
import Laplace.Multi.MeanMapChart
import Laplace.Multi.InformationProjection

/-!
# The data-to-posterior quotient and response stability

For a finite data alphabet `ι` with per-datum losses `R i` and data weights `a : ι → ℝ`, the loss is
`L_a = L₀ + ∑ᵢ aᵢ Rᵢ` and a change of data `h` changes the loss by the contrast `R_h = dirLoss R h`.
This module makes precise which data directions the posterior sees (Astra round 27 item 1):

* **Kernel of the response form** (`responseForm_self_eq_zero_iff`): `G_a(h,h) = 0` iff `R_h` is
  constant `μ`-a.e. — a condition independent of `a`, so the statistically invisible directions form
  a fixed subspace of the data tangent space.
* **Posterior identifiability** (`gibbsDensity_eq_iff`): `P_a = P_b` iff `L_a − L_b` is constant.
* **Response stability** (`hasFDerivAt_obsMap`, `obsMapDeriv_apply`, `abs_obsMapDeriv_le`): for any
  bounded observable `O`, `D_a⟨O⟩[h] = −t Cov_a(O, R_h)` and `|D_a⟨O⟩[h]| ≤ √Var_a(O) · √G_a(h,h)`.
* **The path inequality** (`abs_priorExp_sub_le_integral`): along a `C¹` data path,
  `|⟨O⟩_{γ(1)} − ⟨O⟩_{γ(0)}| ≤ ∫₀¹ √Var_{γ(s)}(O) · |γ'(s)|_{G_{γ(s)}} ds`.
-/

open MeasureTheory Filter Topology Set

namespace Laplace.Multi

variable {X : Type*} [MeasurableSpace X] {μ : Measure X} {ι : Type*} [Fintype ι]

/-! ### The variance as a centred second moment, and its vanishing -/

/-- Posterior expectations only see observables up to a.e. equality. -/
theorem priorExp_congr_ae' (π L : X → ℝ) {φ ψ : X → ℝ} (h : ∀ᵐ x ∂μ, φ x = ψ x) (t : ℝ) :
    priorExp μ π L φ t = priorExp μ π L ψ t := by
  unfold priorExp
  congr 1
  exact integral_congr_ae (h.mono fun x hx ↦ by dsimp only; rw [hx])

/-- `Var_t(φ) = ∫ (φ − ⟨φ⟩)² e^{-tL} π / Z`. -/
theorem priorCov_self_eq_integral_sq {π L φ : X → ℝ} {t : ℝ} (hZ : priorZ μ π L t ≠ 0)
    (h0 : Integrable (fun x ↦ Real.exp (-(t * L x)) * π x) μ)
    (h1 : Integrable (fun x ↦ φ x * Real.exp (-(t * L x)) * π x) μ)
    (h2 : Integrable (fun x ↦ φ x * φ x * Real.exp (-(t * L x)) * π x) μ) :
    priorCov μ π L φ φ t =
      (∫ x, (φ x - priorExp μ π L φ t) ^ 2 * (Real.exp (-(t * L x)) * π x) ∂μ) /
        priorZ μ π L t := by
  set m := priorExp μ π L φ t with hm
  have e : ∀ x, (φ x - m) ^ 2 * (Real.exp (-(t * L x)) * π x) =
      φ x * φ x * Real.exp (-(t * L x)) * π x - 2 * m * (φ x * Real.exp (-(t * L x)) * π x) +
        m ^ 2 * (Real.exp (-(t * L x)) * π x) := fun x ↦ by ring
  simp_rw [e]
  have h21 : Integrable (fun x ↦ φ x * φ x * Real.exp (-(t * L x)) * π x -
      2 * m * (φ x * Real.exp (-(t * L x)) * π x)) μ := h2.sub (h1.const_mul _)
  rw [integral_add h21 (h0.const_mul _), integral_sub h2 (h1.const_mul _), integral_const_mul,
    integral_const_mul]
  unfold priorCov priorExp priorZ at hm ⊢
  unfold priorZ at hZ
  dsimp only at hm ⊢
  set N2 := ∫ x, φ x * φ x * Real.exp (-(t * L x)) * π x ∂μ with hN2
  set N1 := ∫ x, φ x * Real.exp (-(t * L x)) * π x ∂μ with hN1
  set Z := ∫ x, Real.exp (-(t * L x)) * π x ∂μ with hZ'
  clear_value N2 N1 Z
  rw [hm]
  field_simp
  ring

/-- A bounded observable with vanishing posterior variance is a.e. constant (positive prior). -/
theorem ae_eq_const_of_priorCov_self_eq_zero {π L φ : X → ℝ} (hπ : ∀ x, 0 < π x) {t : ℝ}
    (hZ : priorZ μ π L t ≠ 0)
    (h0 : Integrable (fun x ↦ Real.exp (-(t * L x)) * π x) μ)
    (h1 : Integrable (fun x ↦ φ x * Real.exp (-(t * L x)) * π x) μ)
    (h2 : Integrable (fun x ↦ φ x * φ x * Real.exp (-(t * L x)) * π x) μ)
    (hvar : priorCov μ π L φ φ t = 0) :
    ∀ᵐ x ∂μ, φ x = priorExp μ π L φ t := by
  rw [priorCov_self_eq_integral_sq hZ h0 h1 h2, div_eq_zero_iff] at hvar
  rcases hvar with h | h
  swap
  · exact absurd h hZ
  set m := priorExp μ π L φ t
  have hnn : 0 ≤ fun x ↦ (φ x - m) ^ 2 * (Real.exp (-(t * L x)) * π x) := fun x ↦
    mul_nonneg (sq_nonneg _) (mul_nonneg (Real.exp_pos _).le (hπ x).le)
  have hint : Integrable (fun x ↦ (φ x - m) ^ 2 * (Real.exp (-(t * L x)) * π x)) μ := by
    refine ((h2.sub (h1.const_mul (2 * m))).add (h0.const_mul (m ^ 2))).congr
      (Filter.Eventually.of_forall fun x ↦ ?_)
    simp only [Pi.add_apply, Pi.sub_apply]
    ring
  have hae := (integral_eq_zero_iff_of_nonneg hnn hint).mp h
  filter_upwards [hae] with x hx
  simp only [Pi.zero_apply] at hx
  rcases mul_eq_zero.mp hx with h' | h'
  · exact sub_eq_zero.mp ((pow_eq_zero_iff two_ne_zero).mp h')
  · exact absurd h' (mul_pos (Real.exp_pos _) (hπ x)).ne'

/-- The posterior expectation of a constant is the constant. -/
theorem priorExp_const_fun {π L : X → ℝ} {t : ℝ} (hZ : priorZ μ π L t ≠ 0) (c : ℝ) :
    priorExp μ π L (fun _ ↦ c) t = c := by
  unfold priorExp
  have e : (∫ x, c * Real.exp (-(t * L x)) * π x ∂μ) = c * priorZ μ π L t := by
    unfold priorZ
    rw [← integral_const_mul]
    exact integral_congr_ae (Filter.Eventually.of_forall fun x ↦ by ring)
  rw [e, mul_div_assoc, div_self hZ, mul_one]

/-- The variance of an a.e.-constant observable vanishes. -/
theorem priorCov_self_eq_zero_of_ae_const {π L φ : X → ℝ} {t : ℝ} (hZ : priorZ μ π L t ≠ 0)
    {c : ℝ} (hc : ∀ᵐ x ∂μ, φ x = c) : priorCov μ π L φ φ t = 0 := by
  unfold priorCov
  rw [priorExp_congr_ae' π L hc, priorExp_congr_ae' π L (φ := fun x ↦ φ x * φ x)
    (ψ := fun _ ↦ c * c) (by filter_upwards [hc] with x hx; rw [hx]),
    priorExp_const_fun hZ, priorExp_const_fun hZ, sub_self]

/-! ### The affine family: integrability, kernel, identifiability -/

section Affine

variable [Nonempty X] {π L₀ : X → ℝ} (hπm : Measurable π) (hπi : Integrable π μ)
  (hπ : ∀ x, 0 < π x) (hπpos : 0 < ∫ x, π x ∂μ) (hL₀m : Measurable L₀) {M₀ : ℝ}
  (hL₀ : ∀ x, |L₀ x| ≤ M₀) {R : ι → X → ℝ} (hR : ∀ i, Bdd (R i)) {t : ℝ}
include hπm hπi hπ hπpos hL₀m hL₀ hR

/-- Bounded observables are integrable against the affine Gibbs weight. -/
theorem integrable_mul_affWeight_of_bdd (a : ι → ℝ) {f : X → ℝ} (hf : Bdd f) :
    Integrable (fun x ↦ f x * Real.exp (-(t * affLoss L₀ R a x)) * π x) μ := by
  obtain ⟨_, h⟩ := tiltData_aff hπm hπi (fun x ↦ (hπ x).le) hπpos hL₀m hL₀ hR a a t
  refine (h.integrable_of_bdd hf t 0).congr (Filter.Eventually.of_forall fun x ↦ ?_)
  simp only [baseWeight, mul_zero, neg_zero, Real.exp_zero, mul_one]
  ring

omit [Nonempty X] in
theorem affZ_pos (a : ι → ℝ) : 0 < priorZ μ π (affLoss L₀ R a) t :=
  (tiltData_aff hπm hπi (fun x ↦ (hπ x).le) hπpos hL₀m hL₀ hR a a t).choose_spec.ν_pos

/-- **The kernel of the response form**: `G_a(v,v) = 0` iff the contrast `R_v` is a.e. constant.
The right-hand side does not mention `a`: the invisible data directions form one fixed subspace. -/
theorem responseForm_self_eq_zero_iff (ht : 0 < t) (a v : ι → ℝ) :
    responseForm μ π L₀ R a t v v = 0 ↔ ∃ c : ℝ, ∀ᵐ x ∂μ, dirLoss R v x = c := by
  have hZ := (affZ_pos hπm hπi hπ hπpos hL₀m hL₀ hR (t := t) a).ne'
  have hv := bdd_dirLoss hR v
  unfold responseForm
  rw [mul_eq_zero, or_iff_right (pow_ne_zero _ ht.ne')]
  have h0 : Integrable (fun x ↦ Real.exp (-(t * affLoss L₀ R a x)) * π x) μ :=
    (integrable_mul_affWeight_of_bdd hπm hπi hπ hπpos hL₀m hL₀ hR (t := t) a
      (Bdd.const 1)).congr (Filter.Eventually.of_forall fun x ↦ by simp)
  have h1 := integrable_mul_affWeight_of_bdd hπm hπi hπ hπpos hL₀m hL₀ hR (t := t) a hv
  have h2 := integrable_mul_affWeight_of_bdd hπm hπi hπ hπpos hL₀m hL₀ hR (t := t) a (hv.mul hv)
  constructor
  · intro h
    exact ⟨_, ae_eq_const_of_priorCov_self_eq_zero hπ hZ h0 h1 h2 h⟩
  · rintro ⟨c, hc⟩
    exact priorCov_self_eq_zero_of_ae_const hZ hc

/-- Invisibility is the same at every data point. -/
theorem responseForm_self_eq_zero_iff_of_ne (ht : 0 < t) (a b v : ι → ℝ) :
    responseForm μ π L₀ R a t v v = 0 ↔ responseForm μ π L₀ R b t v v = 0 := by
  rw [responseForm_self_eq_zero_iff hπm hπi hπ hπpos hL₀m hL₀ hR ht,
    responseForm_self_eq_zero_iff hπm hπi hπ hπpos hL₀m hL₀ hR ht]

omit [Nonempty X] hπm hπi hπpos hL₀m hL₀ hR in
/-- **Posterior identifiability**: `P_a = P_b` iff the loss contrast `R_{b−a} = L_b − L_a` is
constant. -/
theorem gibbsDensity_eq_iff (ht : t ≠ 0) {a b : ι → ℝ}
    (hZa : 0 < priorZ μ π (affLoss L₀ R a) t) (hZb : 0 < priorZ μ π (affLoss L₀ R b) t) :
    (∀ x, gibbsDensity μ π (affLoss L₀ R a) t x = gibbsDensity μ π (affLoss L₀ R b) t x) ↔
      ∃ c : ℝ, ∀ x, dirLoss R (b - a) x = c := by
  constructor
  · intro h
    refine ⟨(affLogZ μ π L₀ R t a - affLogZ μ π L₀ R t b) / t, fun x ↦ ?_⟩
    have := log_gibbsDensity_sub hπ hZa hZb x
    rw [h x, sub_self] at this
    field_simp
    linarith
  · rintro ⟨c, hc⟩ x
    have hL : ∀ y, affLoss L₀ R b y = affLoss L₀ R a y + c := fun y ↦ by
      have := hc y
      simp only [dirLoss, affLoss, Pi.sub_apply, sub_mul, Finset.sum_sub_distrib] at this ⊢
      linarith
    have hZ : priorZ μ π (affLoss L₀ R b) t =
        Real.exp (-(t * c)) * priorZ μ π (affLoss L₀ R a) t := by
      unfold priorZ
      rw [← integral_const_mul]
      refine integral_congr_ae (Filter.Eventually.of_forall fun y ↦ ?_)
      dsimp only
      rw [hL y, show -(t * (affLoss L₀ R a y + c)) = -(t * c) + -(t * affLoss L₀ R a y) by ring,
        Real.exp_add]
      ring
    have hA : affLogZ μ π L₀ R t b - affLogZ μ π L₀ R t a = -(t * c) := by
      unfold affLogZ
      rw [hZ, Real.log_mul (Real.exp_pos _).ne' hZa.ne', Real.log_exp]
      ring
    have hpa := gibbsDensity_pos (fun x ↦ (hπ x).le) hZa (hπ x).ne'
    have hpb := gibbsDensity_pos (fun x ↦ (hπ x).le) hZb (hπ x).ne'
    have hlog := log_gibbsDensity_sub hπ hZa hZb x
    rw [hc x, hA] at hlog
    exact Real.log_injOn_pos (Set.mem_Ioi.mpr hpa) (Set.mem_Ioi.mpr hpb) (by linarith)

/-! ### Response stability -/

/-- The derivative of `a ↦ ⟨φ⟩_a`, as a continuous linear map. -/
noncomputable def obsMapDeriv (μ : Measure X) (π L₀ φ : X → ℝ) (R : ι → X → ℝ) (t : ℝ)
    (a₀ : ι → ℝ) : (ι → ℝ) →L[ℝ] ℝ :=
  (priorZ μ π (affLoss L₀ R a₀) t)⁻¹ • affNumDeriv μ π L₀ φ R t a₀ -
    ((∫ x, φ x * Real.exp (-(t * affLoss L₀ R a₀ x)) * π x ∂μ) *
      (priorZ μ π (affLoss L₀ R a₀) t ^ 2)⁻¹) • affNumDeriv μ π L₀ (fun _ ↦ 1) R t a₀

/-- **The response map of a bounded observable is Fréchet differentiable.** -/
theorem hasFDerivAt_obsMap {φ : X → ℝ} (hφm : Measurable φ) {Mφ : ℝ} (hφ : ∀ x, |φ x| ≤ Mφ)
    (ht : 0 < t) (a₀ : ι → ℝ) :
    HasFDerivAt (fun a ↦ priorExp μ π (affLoss L₀ R a) φ t) (obsMapDeriv μ π L₀ φ R t a₀) a₀ := by
  have hπ' : ∀ x, 0 ≤ π x := fun x ↦ (hπ x).le
  have hZ := (affZ_pos hπm hπi hπ hπpos hL₀m hL₀ hR (t := t) a₀).ne'
  obtain ⟨_, hZ'⟩ := hasFDerivAt_affNum hπm hπi hπ' hL₀m hL₀ hR (φ := fun _ ↦ (1 : ℝ))
    measurable_const (Mφ := 1) (fun _ ↦ by simp) ht a₀
  obtain ⟨_, hN'⟩ := hasFDerivAt_affNum hπm hπi hπ' hL₀m hL₀ hR (φ := φ) hφm hφ ht a₀
  simp only [one_mul] at hZ'
  have hZ'' : HasFDerivAt (fun a ↦ priorZ μ π (affLoss L₀ R a) t)
      (affNumDeriv μ π L₀ (fun _ ↦ 1) R t a₀) a₀ := by
    unfold priorZ affNumDeriv
    simpa only [one_mul] using hZ'
  have hZinv := (hasDerivAt_inv hZ).comp_hasFDerivAt a₀ hZ''
  have hN'' : HasFDerivAt (fun a ↦ ∫ x, φ x * Real.exp (-(t * affLoss L₀ R a x)) * π x ∂μ)
      (affNumDeriv μ π L₀ φ R t a₀) a₀ := hN'
  have key := hN''.mul hZinv
  refine (key.congr_of_eventuallyEq (Filter.Eventually.of_forall fun a ↦ ?_)).congr_fderiv ?_
  · simp only [priorExp, Pi.mul_apply, Function.comp_apply, div_eq_mul_inv]
  · unfold obsMapDeriv
    ext v
    simp only [add_apply, smul_apply, sub_apply, smul_eq_mul, Function.comp_apply]
    ring

/-- **The influence formula**: `D_a⟨φ⟩[v] = −t Cov_a(φ, R_v)`. -/
theorem obsMapDeriv_apply {φ : X → ℝ} (hφm : Measurable φ) {Mφ : ℝ} (hφ : ∀ x, |φ x| ≤ Mφ)
    (ht : 0 < t) (a₀ v : ι → ℝ) :
    obsMapDeriv μ π L₀ φ R t a₀ v =
      -t * priorCov μ π (affLoss L₀ R a₀) φ (dirLoss R v) t := by
  have hπ' : ∀ x, 0 ≤ π x := fun x ↦ (hπ x).le
  have hZ := (affZ_pos hπm hπi hπ hπpos hL₀m hL₀ hR (t := t) a₀).ne'
  obtain ⟨hZint, _⟩ := hasFDerivAt_affNum hπm hπi hπ' hL₀m hL₀ hR (φ := fun _ ↦ (1 : ℝ))
    measurable_const (Mφ := 1) (fun _ ↦ by simp) ht a₀
  obtain ⟨hNint, _⟩ := hasFDerivAt_affNum hπm hπi hπ' hL₀m hL₀ hR (φ := φ) hφm hφ ht a₀
  simp only [obsMapDeriv, sub_apply, smul_apply, smul_eq_mul, affNumDeriv]
  rw [affNum_fderiv_apply hNint v, affNum_fderiv_apply hZint v]
  unfold priorCov priorExp priorZ
  simp only [one_mul]
  have hZ' : (∫ x, Real.exp (-(t * affLoss L₀ R a₀ x)) * π x ∂μ) ≠ 0 := hZ
  field_simp
  ring

/-- **Response stability**: `|D_a⟨φ⟩[v]| ≤ √Var_a(φ) · √G_a(v,v)`. -/
theorem abs_obsMapDeriv_le {φ : X → ℝ} (hφm : Measurable φ) {Mφ : ℝ} (hφ : ∀ x, |φ x| ≤ Mφ)
    (ht : 0 < t) (a₀ v : ι → ℝ) :
    |obsMapDeriv μ π L₀ φ R t a₀ v| ≤
      Real.sqrt (priorCov μ π (affLoss L₀ R a₀) φ φ t) *
        Real.sqrt (responseForm μ π L₀ R a₀ t v v) := by
  rw [obsMapDeriv_apply hπm hπi hπ hπpos hL₀m hL₀ hR hφm hφ ht a₀ v]
  obtain ⟨_, h⟩ := tiltData_aff hπm hπi (fun x ↦ (hπ x).le) hπpos hL₀m hL₀ hR a₀ v t
  have hcs := h.abs_tiltCov_le (f := φ) (g := dirLoss R v) ⟨hφm, Mφ, hφ⟩ (bdd_dirLoss hR v) t 0
  rw [← priorCov_eq_tiltCov_zero, ← priorCov_eq_tiltCov_zero, ← priorCov_eq_tiltCov_zero] at hcs
  unfold responseForm
  rw [Real.sqrt_mul (sq_nonneg t), Real.sqrt_sq ht.le, abs_mul, abs_neg, abs_of_pos ht]
  calc t * |priorCov μ π (affLoss L₀ R a₀) φ (dirLoss R v) t|
      ≤ t * (Real.sqrt (priorCov μ π (affLoss L₀ R a₀) φ φ t) *
        Real.sqrt (priorCov μ π (affLoss L₀ R a₀) (dirLoss R v) (dirLoss R v) t)) :=
        mul_le_mul_of_nonneg_left hcs ht.le
    _ = _ := by ring

/-! ### The path inequality -/

/-- Posterior expectations of bounded observables depend continuously on the data. -/
theorem continuous_obsMap {φ : X → ℝ} (hφm : Measurable φ) {Mφ : ℝ} (hφ : ∀ x, |φ x| ≤ Mφ)
    (ht : 0 < t) : Continuous (fun a ↦ priorExp μ π (affLoss L₀ R a) φ t) :=
  continuous_iff_continuousAt.mpr fun a ↦
    (hasFDerivAt_obsMap hπm hπi hπ hπpos hL₀m hL₀ hR hφm hφ ht a).continuousAt

/-- The derivative map `a ↦ D_a⟨φ⟩` is continuous. -/
theorem continuous_obsMapDeriv {φ : X → ℝ} (hφm : Measurable φ) {Mφ : ℝ} (hφ : ∀ x, |φ x| ≤ Mφ)
    (ht : 0 < t) : Continuous (fun a ↦ obsMapDeriv μ π L₀ φ R t a) := by
  have hπ' : ∀ x, 0 ≤ π x := fun x ↦ (hπ x).le
  refine continuous_iff_continuousAt.mpr fun a₀ ↦ ?_
  have hZ := (affZ_pos hπm hπi hπ hπpos hL₀m hL₀ hR (t := t) a₀).ne'
  have hD1 := continuousAt_affNumDeriv hπm hπi hπ' hL₀m hL₀ hR hφm hφ ht a₀
  have hD0 := continuousAt_affNumDeriv hπm hπi hπ' hL₀m hL₀ hR (φ := fun _ ↦ (1 : ℝ))
    measurable_const (Mφ := 1) (fun _ ↦ by simp) ht a₀
  obtain ⟨_, hZ'⟩ := hasFDerivAt_affNum hπm hπi hπ' hL₀m hL₀ hR (φ := fun _ ↦ (1 : ℝ))
    measurable_const (Mφ := 1) (fun _ ↦ by simp) ht a₀
  obtain ⟨_, hN'⟩ := hasFDerivAt_affNum hπm hπi hπ' hL₀m hL₀ hR (φ := φ) hφm hφ ht a₀
  have hZc : ContinuousAt (fun a ↦ priorZ μ π (affLoss L₀ R a) t) a₀ := by
    have := hZ'.continuousAt
    simp only [one_mul] at this
    exact this
  have hNc : ContinuousAt
      (fun a ↦ ∫ x, φ x * Real.exp (-(t * affLoss L₀ R a x)) * π x ∂μ) a₀ := hN'.continuousAt
  unfold obsMapDeriv
  exact ((hZc.inv₀ hZ).smul hD1).sub ((hNc.mul ((hZc.pow 2).inv₀ (pow_ne_zero _ hZ))).smul hD0)

/-- **The path inequality**: along a `C¹` data path `γ`, the change of any bounded posterior
expectation is bounded by the integrated product of the observable's posterior standard deviation
and the response speed `|γ'(s)|_{G_{γ(s)}}`. -/
theorem abs_priorExp_sub_le_integral {φ : X → ℝ} (hφm : Measurable φ) {Mφ : ℝ}
    (hφ : ∀ x, |φ x| ≤ Mφ) (ht : 0 < t) {γ γ' : ℝ → ι → ℝ} (hγ : ∀ s, HasDerivAt γ (γ' s) s)
    (hγ' : Continuous γ') :
    |priorExp μ π (affLoss L₀ R (γ 1)) φ t - priorExp μ π (affLoss L₀ R (γ 0)) φ t| ≤
      ∫ s in (0 : ℝ)..1, Real.sqrt (priorCov μ π (affLoss L₀ R (γ s)) φ φ t) *
        Real.sqrt (responseForm μ π L₀ R (γ s) t (γ' s) (γ' s)) := by
  have hγc : Continuous γ := continuous_iff_continuousAt.mpr fun s ↦ (hγ s).continuousAt
  -- the derivative along the path
  set F : ℝ → ℝ := fun s ↦ priorExp μ π (affLoss L₀ R (γ s)) φ t with hF
  set F' : ℝ → ℝ := fun s ↦ obsMapDeriv μ π L₀ φ R t (γ s) (γ' s) with hF'
  have hderiv : ∀ s, HasDerivAt F (F' s) s := fun s ↦
    (hasFDerivAt_obsMap hπm hπi hπ hπpos hL₀m hL₀ hR hφm hφ ht (γ s)).comp_hasDerivAt s (hγ s)
  have hF'c : Continuous F' :=
    ((continuous_obsMapDeriv hπm hπi hπ hπpos hL₀m hL₀ hR hφm hφ ht).comp hγc).clm_apply hγ'
  have hftc : ∫ s in (0 : ℝ)..1, F' s = F 1 - F 0 :=
    intervalIntegral.integral_eq_sub_of_hasDerivAt (fun s _ ↦ hderiv s)
      (hF'c.intervalIntegrable (μ := volume) 0 1)
  -- the pointwise bound and continuity of the bound
  have hbd : ∀ s, |F' s| ≤ Real.sqrt (priorCov μ π (affLoss L₀ R (γ s)) φ φ t) *
      Real.sqrt (responseForm μ π L₀ R (γ s) t (γ' s) (γ' s)) := fun s ↦
    abs_obsMapDeriv_le hπm hπi hπ hπpos hL₀m hL₀ hR hφm hφ ht (γ s) (γ' s)
  have hvar_c : Continuous (fun s ↦ priorCov μ π (affLoss L₀ R (γ s)) φ φ t) := by
    unfold priorCov
    exact ((continuous_obsMap hπm hπi hπ hπpos hL₀m hL₀ hR (φ := fun x ↦ φ x * φ x)
      (hφm.mul hφm) (Mφ := Mφ * Mφ) (fun x ↦ by
        rw [abs_mul]
        exact mul_le_mul (hφ x) (hφ x) (abs_nonneg _) (le_trans (abs_nonneg _) (hφ x))) ht).comp
      hγc).sub (((continuous_obsMap hπm hπi hπ hπpos hL₀m hL₀ hR hφm hφ ht).comp hγc).mul
      ((continuous_obsMap hπm hπi hπ hπpos hL₀m hL₀ hR hφm hφ ht).comp hγc))
  -- the response form along the path is a quadratic form in `γ'` with continuous coefficients
  have hG_c : Continuous (fun s ↦ responseForm μ π L₀ R (γ s) t (γ' s) (γ' s)) := by
    have hRij : ∀ i j, Continuous (fun s ↦ priorCov μ π (affLoss L₀ R (γ s)) (R i) (R j) t) := by
      intro i j
      obtain ⟨Mi, hMi⟩ := (hR i).2
      obtain ⟨Mj, hMj⟩ := (hR j).2
      unfold priorCov
      exact ((continuous_obsMap hπm hπi hπ hπpos hL₀m hL₀ hR (φ := fun x ↦ R i x * R j x)
        ((hR i).1.mul (hR j).1) (Mφ := Mi * Mj) (fun x ↦ by
          rw [abs_mul]
          exact mul_le_mul (hMi x) (hMj x) (abs_nonneg _) (le_trans (abs_nonneg _) (hMi x)))
        ht).comp hγc).sub
        (((continuous_obsMap hπm hπi hπ hπpos hL₀m hL₀ hR (hR i).1 hMi ht).comp hγc).mul
        ((continuous_obsMap hπm hπi hπ hπpos hL₀m hL₀ hR (hR j).1 hMj ht).comp hγc))
    have e : ∀ s, responseForm μ π L₀ R (γ s) t (γ' s) (γ' s) =
        t ^ 2 * ∑ i, γ' s i * ∑ j, γ' s j * priorCov μ π (affLoss L₀ R (γ s)) (R j) (R i) t := by
      intro s
      unfold responseForm
      congr 1
      have hν : Integrable (baseWeight π (affLoss L₀ R (γ s)) t) μ :=
        (tiltData_aff hπm hπi (fun x ↦ (hπ x).le) hπpos hL₀m hL₀ hR (γ s) (γ s) t).choose_spec.ν_int
      rw [← sum_mul_priorCov_eq hν hR (bdd_dirLoss hR (γ' s)) (γ' s)]
      refine Finset.sum_congr rfl fun i _ ↦ ?_
      congr 1
      have hsymm : priorCov μ π (affLoss L₀ R (γ s)) (R i) (dirLoss R (γ' s)) t =
          priorCov μ π (affLoss L₀ R (γ s)) (dirLoss R (γ' s)) (R i) t := by
        unfold priorCov
        rw [mul_comm (priorExp _ _ _ (R i) _)]
        congr 1
        exact priorExp_congr_ae' π _ (Filter.Eventually.of_forall fun x ↦ mul_comm _ _) t
      rw [hsymm, ← sum_mul_priorCov_eq hν hR (hR i) (γ' s)]
    simp_rw [e]
    exact continuous_const.mul (continuous_finsetSum _ fun i _ ↦
      ((continuous_apply i).comp hγ').mul (continuous_finsetSum _ fun j _ ↦
        ((continuous_apply j).comp hγ').mul (hRij j i)))
  have hbound_c : Continuous (fun s ↦ Real.sqrt (priorCov μ π (affLoss L₀ R (γ s)) φ φ t) *
      Real.sqrt (responseForm μ π L₀ R (γ s) t (γ' s) (γ' s))) :=
    (Real.continuous_sqrt.comp hvar_c).mul (Real.continuous_sqrt.comp hG_c)
  have hftc' : ∫ s in (0 : ℝ)..1, F' s =
      priorExp μ π (affLoss L₀ R (γ 1)) φ t - priorExp μ π (affLoss L₀ R (γ 0)) φ t := hftc
  rw [← hftc']
  have := intervalIntegral.norm_integral_le_of_norm_le (f := F')
    (g := fun s ↦ Real.sqrt (priorCov μ π (affLoss L₀ R (γ s)) φ φ t) *
      Real.sqrt (responseForm μ π L₀ R (γ s) t (γ' s) (γ' s))) zero_le_one
    (Filter.Eventually.of_forall fun s _ ↦ by rw [Real.norm_eq_abs]; exact hbd s)
    (hbound_c.intervalIntegrable (μ := volume) 0 1)
  simpa only [Real.norm_eq_abs] using this

end Affine

end Laplace.Multi
