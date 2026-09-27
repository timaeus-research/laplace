/-
Copyright (c) 2026 Timaeus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Timaeus
-/
import Laplace.Multi.ResponseObservableTransport

/-!
# The observable Hessian: mixed second responses and the variance Hessian

`ResponseObservableTransport` identified the second response of a bounded observable `F` along a
response line with the pairing `E[(F − EF) r_{uu}]` against the score residual. Here:

* the score residual is **bilinear** in its two directions (`scoreResidual_add_left`,
  `scoreResidual_smul_left`, symmetry), so the second response
  `secondResponse F θ u v = E_θ[(F − E_θF) r_{uv}]` is a symmetric bilinear form in `(u,v)` and
  the mixed second response is the **polarisation** of the diagonal one
  (`secondResponse_polarisation`), with the bilinear Cauchy–Schwarz bound
  (`abs_secondResponse_le`, from H1);
* **the variance Hessian along a response line** (`hasDerivAt_lineVarianceDeriv`):
  `d²/dt² Var_{θ_t}(F) = E[(F − EF)² r_{V_tV_t}] − 2 (d/dt E_{θ_t}F)²`;
* **residual-flat families have concave posterior variances** along mean segments
  (`concaveOn_lineVariance_of_pairing_nonpos`, `concaveOn_lineVariance_of_flat`): if the
  **variance–curvature pairing** `E[(F − EF)² r_{uu}]` (`varianceCurvaturePairing`) is `≤ 0`
  (in particular `= 0`, the residual-flat case) along the line, the variance
  has nonpositive second derivative `−2 (E F)'²` and is concave on every interval in the domain.
-/

open MeasureTheory Filter Topology Set

namespace Laplace.Multi

section Bilinear

variable {X : Type*} [MeasurableSpace X] [Nonempty X] {J : Type*} [Fintype J] [Nonempty J]
  {S : J → X → ℝ} (hS : ∀ j, Bdd (S j)) (ν : Measure X) [IsProbabilityMeasure ν]
include hS

/-- The reconstructed family. -/
local notation "Pfam" => familyMeasure ν (fun _ ↦ (1 : ℝ)) (fun _ ↦ (0 : ℝ)) S 1

/-- The direction space. -/
local notation "𝕍" => dirSpan ν (fun _ ↦ (1 : ℝ)) S

/-- The Fisher form. -/
local notation "G" => fisherInner S ν

/-- The centred score. -/
local notation "f" => modelScore S ν

omit [Nonempty J] in
theorem modelScore_add (θ u v : 𝕍) : f θ (u + v) = fun x ↦ f θ u x + f θ v x := by
  have hP := isProbabilityMeasure_family hS ν (θ : J → ℝ)
  funext x
  simp only [modelScore, Submodule.coe_add, dirLoss_add]
  rw [integral_add (integrable_of_bdd_prob _ (bdd_dirLoss hS _))
    (integrable_of_bdd_prob _ (bdd_dirLoss hS _))]
  ring

omit [Nonempty X] [Nonempty J] hS [IsProbabilityMeasure ν] in
theorem modelScore_smul (θ : 𝕍) (c : ℝ) (u : 𝕍) : f θ (c • u) = fun x ↦ c * f θ u x := by
  funext x
  simp only [modelScore, Submodule.coe_smul, dirLoss_smul, integral_const_mul]
  ring

theorem mChristoffel_add_right (θ u x y : 𝕍) :
    mChristoffel hS ν θ u (x + y) = mChristoffel hS ν θ u x + mChristoffel hS ν θ u y := by
  unfold mChristoffel
  rw [map_add, map_add]

theorem mChristoffel_add_left (θ x y u : 𝕍) :
    mChristoffel hS ν θ (x + y) u = mChristoffel hS ν θ x u + mChristoffel hS ν θ y u := by
  rw [mChristoffel_symm hS ν θ (x + y) u, mChristoffel_add_right hS ν, mChristoffel_symm hS ν θ x,
    mChristoffel_symm hS ν θ y]

theorem mChristoffel_smul_left (θ : 𝕍) (c : ℝ) (x u : 𝕍) :
    mChristoffel hS ν θ (c • x) u = c • mChristoffel hS ν θ x u := by
  rw [mChristoffel_symm hS ν θ (c • x) u, mChristoffel_smul_right hS ν, mChristoffel_symm hS ν θ x]

/-- The score residual is additive in its first direction. -/
theorem scoreResidual_add_left (θ u v w : 𝕍) :
    scoreResidual hS ν θ (u + v) w =
      fun x ↦ scoreResidual hS ν θ u w x + scoreResidual hS ν θ v w x := by
  funext x
  simp only [scoreResidual, modelScore_add hS ν, fisherInner_add_left hS ν,
    mChristoffel_add_left hS ν]
  ring

/-- The score residual is homogeneous in its first direction. -/
theorem scoreResidual_smul_left (θ : 𝕍) (c : ℝ) (u w : 𝕍) :
    scoreResidual hS ν θ (c • u) w = fun x ↦ c * scoreResidual hS ν θ u w x := by
  funext x
  simp only [scoreResidual, modelScore_smul ν, fisherInner_smul_left,
    mChristoffel_smul_left hS ν]
  ring

/-- **The second response of an observable as a bilinear pairing**:
`secondResponse F θ u v = E_θ[(F − E_θF) r_{uv}]`. -/
noncomputable def secondResponse (F : X → ℝ) (θ u v : 𝕍) : ℝ :=
  ∫ x, (F x - ∫ y, F y ∂Pfam (θ : J → ℝ)) * scoreResidual hS ν θ u v x ∂Pfam (θ : J → ℝ)

theorem secondResponse_symm (F : X → ℝ) (θ u v : 𝕍) :
    secondResponse hS ν F θ u v = secondResponse hS ν F θ v u := by
  unfold secondResponse
  rw [scoreResidual_symm hS ν θ u v]

theorem secondResponse_add_left {F : X → ℝ} (hF : Bdd F) (θ u v w : 𝕍) :
    secondResponse hS ν F θ (u + v) w =
      secondResponse hS ν F θ u w + secondResponse hS ν F θ v w := by
  have hP := isProbabilityMeasure_family hS ν (θ : J → ℝ)
  have hbF : Bdd fun x ↦ F x - ∫ y, F y ∂Pfam (θ : J → ℝ) := hF.sub (Bdd.const _)
  unfold secondResponse
  rw [scoreResidual_add_left hS ν, ← integral_add
    (integrable_of_bdd_prob _ (hbF.mul (bdd_scoreResidual hS ν θ u w)))
    (integrable_of_bdd_prob _ (hbF.mul (bdd_scoreResidual hS ν θ v w)))]
  exact integral_congr_ae (Eventually.of_forall fun x ↦ by ring)

theorem secondResponse_smul_left (F : X → ℝ) (θ : 𝕍) (c : ℝ) (u w : 𝕍) :
    secondResponse hS ν F θ (c • u) w = c * secondResponse hS ν F θ u w := by
  unfold secondResponse
  rw [scoreResidual_smul_left hS ν, ← integral_const_mul]
  exact integral_congr_ae (Eventually.of_forall fun x ↦ by ring)

/-- **Polarisation**: the mixed second response is determined by the diagonal ones. -/
theorem secondResponse_polarisation {F : X → ℝ} (hF : Bdd F) (θ u v : 𝕍) :
    secondResponse hS ν F θ u v = (1 / 2 : ℝ) * (secondResponse hS ν F θ (u + v) (u + v) -
      secondResponse hS ν F θ u u - secondResponse hS ν F θ v v) := by
  rw [secondResponse_add_left hS ν hF, secondResponse_symm hS ν F θ u (u + v),
    secondResponse_symm hS ν F θ v (u + v), secondResponse_add_left hS ν hF,
    secondResponse_add_left hS ν hF, secondResponse_symm hS ν F θ v u]
  ring

end Bilinear

section Variance

variable {X : Type*} [MeasurableSpace X] [Nonempty X] {J : Type*} [Fintype J] [Nonempty J]
  {S : J → X → ℝ} (hS : ∀ j, Bdd (S j)) (ν : Measure X) [IsProbabilityMeasure ν]
include hS

/-- The reconstructed family. -/
local notation "Pfam" => familyMeasure ν (fun _ ↦ (1 : ℝ)) (fun _ ↦ (0 : ℝ)) S 1

/-- The direction space. -/
local notation "𝕍" => dirSpan ν (fun _ ↦ (1 : ℝ)) S

/-- The response line. -/
local notation "θl" => responseLine hS ν

/-- The response line velocity. -/
local notation "Vl" => responseLineVel hS ν

/-- The posterior variance of `F` along a response line. -/
noncomputable def lineVariance (F : X → ℝ) (θ₀ e : 𝕍) (t : ℝ) : ℝ :=
  lawCov (Pfam (θl θ₀ e t : J → ℝ)) F F

/-- The derivative of the posterior variance along a response line, in observable form. -/
noncomputable def lineVarianceDeriv (F : X → ℝ) (θ₀ e : 𝕍) (t : ℝ) : ℝ :=
  -lawCov (Pfam (θl θ₀ e t : J → ℝ)) (fun x ↦ F x * F x) (dirLoss S (Vl θ₀ e t : J → ℝ)) -
    2 * lineObservable hS ν F θ₀ e t *
      -lawCov (Pfam (θl θ₀ e t : J → ℝ)) F (dirLoss S (Vl θ₀ e t : J → ℝ))

theorem lineVariance_eq (F : X → ℝ) (θ₀ e : 𝕍) :
    lineVariance hS ν F θ₀ e = fun t ↦ lineObservable hS ν (fun x ↦ F x * F x) θ₀ e t -
      lineObservable hS ν F θ₀ e t * lineObservable hS ν F θ₀ e t := by
  funext t
  rfl

theorem hasDerivAt_lineVariance' {F : X → ℝ} (hF : Bdd F) (θ₀ e : 𝕍) {t : ℝ}
    (ht : t ∈ responseLineDomain S ν θ₀ e) :
    HasDerivAt (lineVariance hS ν F θ₀ e) (lineVarianceDeriv hS ν F θ₀ e t) t := by
  rw [lineVariance_eq hS ν]
  have h1 := hasDerivAt_lineObservable hS ν (hF.mul hF) θ₀ e ht
  have h2 := hasDerivAt_lineObservable hS ν hF θ₀ e ht
  refine (h1.sub (h2.mul h2)).congr_deriv ?_
  unfold lineVarianceDeriv
  ring

/-- **The variance Hessian along a response line**:
`d²/dt² Var_{θ_t}(F) = E[(F − EF)² r_{V_tV_t}] − 2 (d/dt E_{θ_t}F)²`. -/
theorem hasDerivAt_lineVarianceDeriv {F : X → ℝ} (hF : Bdd F) (θ₀ e : 𝕍) {t : ℝ}
    (ht : t ∈ responseLineDomain S ν θ₀ e) :
    HasDerivAt (lineVarianceDeriv hS ν F θ₀ e)
      ((∫ x, (F x - ∫ y, F y ∂Pfam (θl θ₀ e t : J → ℝ)) ^ 2 *
          scoreResidual hS ν (θl θ₀ e t) (Vl θ₀ e t) (Vl θ₀ e t) x ∂Pfam (θl θ₀ e t : J → ℝ)) -
        2 * (lawCov (Pfam (θl θ₀ e t : J → ℝ)) F (dirLoss S (Vl θ₀ e t : J → ℝ))) ^ 2) t := by
  have hP := isProbabilityMeasure_family hS ν (θl θ₀ e t : J → ℝ)
  have h1 := hasDerivAt_deriv_lineObservable hS ν (hF.mul hF) θ₀ e ht
  have h2 := hasDerivAt_lineObservable hS ν hF θ₀ e ht
  have h3 := hasDerivAt_deriv_lineObservable hS ν hF θ₀ e ht
  have h := h1.sub (((h2.const_mul 2).mul h3))
  refine h.congr_deriv ?_
  -- abbreviations at time `t`
  set θ := θl θ₀ e t with hθ
  set V := Vl θ₀ e t with hV
  set r := scoreResidual hS ν θ V V with hr
  set m := ∫ y, F y ∂Pfam (θ : J → ℝ) with hm
  set m2 := ∫ y, F y * F y ∂Pfam (θ : J → ℝ) with hm2
  have hlin : lineObservable hS ν F θ₀ e t = m := rfl
  clear_value m m2
  -- the residual identity `∫ (F² − m₂) r − 2 m ∫ (F − m) r = ∫ (F − m)² r` (using `∫ r = 0`)
  have hbr := bdd_scoreResidual hS ν θ V V
  have i1 : Integrable (fun x ↦ F x * F x * r x) (Pfam (θ : J → ℝ)) :=
    integrable_of_bdd_prob _ ((hF.mul hF).mul hbr)
  have i2 : Integrable (fun x ↦ F x * r x) (Pfam (θ : J → ℝ)) :=
    integrable_of_bdd_prob _ (hF.mul hbr)
  have i3 : Integrable r (Pfam (θ : J → ℝ)) := integrable_of_bdd_prob _ hbr
  have hr0 : ∫ x, r x ∂Pfam (θ : J → ℝ) = 0 := integral_scoreResidual hS ν θ V V
  have i3' : Integrable (fun x ↦ m2 * r x) (Pfam (θ : J → ℝ)) := i3.const_mul m2
  have i3'' : Integrable (fun x ↦ m * r x) (Pfam (θ : J → ℝ)) := i3.const_mul m
  have i2' : Integrable (fun x ↦ 2 * m * (F x * r x)) (Pfam (θ : J → ℝ)) := i2.const_mul _
  have i3''' : Integrable (fun x ↦ m ^ 2 * r x) (Pfam (θ : J → ℝ)) := i3.const_mul _
  have i12 : Integrable (fun x ↦ F x * F x * r x - 2 * m * (F x * r x)) (Pfam (θ : J → ℝ)) :=
    i1.sub i2'
  have e1 : ∫ x, (F x * F x - m2) * r x ∂Pfam (θ : J → ℝ) =
      (∫ x, F x * F x * r x ∂Pfam (θ : J → ℝ)) - m2 * ∫ x, r x ∂Pfam (θ : J → ℝ) := by
    have e : (fun x ↦ (F x * F x - m2) * r x) = fun x ↦ F x * F x * r x - m2 * r x := by
      funext x; ring
    rw [e, integral_sub i1 i3', integral_const_mul]
  have e2 : ∫ x, (F x - m) * r x ∂Pfam (θ : J → ℝ) =
      (∫ x, F x * r x ∂Pfam (θ : J → ℝ)) - m * ∫ x, r x ∂Pfam (θ : J → ℝ) := by
    have e : (fun x ↦ (F x - m) * r x) = fun x ↦ F x * r x - m * r x := by funext x; ring
    rw [e, integral_sub i2 i3'', integral_const_mul]
  have e3 : ∫ x, (F x - m) ^ 2 * r x ∂Pfam (θ : J → ℝ) =
      (∫ x, F x * F x * r x ∂Pfam (θ : J → ℝ)) - 2 * m * (∫ x, F x * r x ∂Pfam (θ : J → ℝ)) +
        m ^ 2 * ∫ x, r x ∂Pfam (θ : J → ℝ) := by
    have e : (fun x ↦ (F x - m) ^ 2 * r x) =
        fun x ↦ F x * F x * r x - 2 * m * (F x * r x) + m ^ 2 * r x := by funext x; ring
    rw [e, integral_add i12 i3''', integral_sub i1 i2', integral_const_mul, integral_const_mul]
  rw [hlin, e1, e2, e3, hr0]
  ring

/-- **The variance–curvature pairing** of an observable along a response line:
`E_t[(F − E_t F)² r_{V_t V_t}]`, the pairing of the centred square of `F` with the diagonal
score residual of the line velocity. It is the only term of the second derivative of the
posterior variance that can be positive. -/
noncomputable def varianceCurvaturePairing (F : X → ℝ) (θ₀ e : 𝕍) (t : ℝ) : ℝ :=
  ∫ x, (F x - ∫ y, F y ∂Pfam (θl θ₀ e t : J → ℝ)) ^ 2 *
    scoreResidual hS ν (θl θ₀ e t) (Vl θ₀ e t) (Vl θ₀ e t) x ∂Pfam (θl θ₀ e t : J → ℝ)

/-- The second derivative of the posterior variance along a response line is the
variance–curvature pairing minus twice the squared covariance with the line score. -/
theorem hasDerivAt_lineVarianceDeriv' {F : X → ℝ} (hF : Bdd F) (θ₀ e : 𝕍) {t : ℝ}
    (ht : t ∈ responseLineDomain S ν θ₀ e) :
    HasDerivAt (lineVarianceDeriv hS ν F θ₀ e)
      (varianceCurvaturePairing hS ν F θ₀ e t -
        2 * (lawCov (Pfam (θl θ₀ e t : J → ℝ)) F (dirLoss S (Vl θ₀ e t : J → ℝ))) ^ 2) t :=
  hasDerivAt_lineVarianceDeriv hS ν hF θ₀ e ht

/-- **Nonpositive variance–curvature pairing gives concave posterior variances along mean
segments**: if `E_t[(F − E_t F)² r_{V_t V_t}] ≤ 0` along the line, the variance is concave on
every interval inside the domain. -/
theorem concaveOn_lineVariance_of_pairing_nonpos {F : X → ℝ} (hF : Bdd F) (θ₀ e : 𝕍) {a b : ℝ}
    (hab : Icc a b ⊆ responseLineDomain S ν θ₀ e)
    (hpair : ∀ t ∈ Icc a b, varianceCurvaturePairing hS ν F θ₀ e t ≤ 0) :
    ConcaveOn ℝ (Icc a b) (lineVariance hS ν F θ₀ e) := by
  have hU := isOpen_responseLineDomain hS ν θ₀ e
  have hderiv : ∀ t ∈ responseLineDomain S ν θ₀ e,
      deriv (lineVariance hS ν F θ₀ e) t = lineVarianceDeriv hS ν F θ₀ e t := fun t ht ↦
    (hasDerivAt_lineVariance' hS ν hF θ₀ e ht).deriv
  have hev : ∀ t ∈ responseLineDomain S ν θ₀ e,
      deriv (lineVariance hS ν F θ₀ e) =ᶠ[𝓝 t] lineVarianceDeriv hS ν F θ₀ e := fun t ht ↦ by
    filter_upwards [hU.mem_nhds ht] with s hs
    exact hderiv s hs
  refine concaveOn_of_deriv2_nonpos (convex_Icc a b) ?_ ?_ ?_ ?_
  · exact fun t ht ↦
      (hasDerivAt_lineVariance' hS ν hF θ₀ e (hab ht)).continuousAt.continuousWithinAt
  · intro t ht
    rw [interior_Icc] at ht
    exact (hasDerivAt_lineVariance' hS ν hF θ₀ e (hab (Ioo_subset_Icc_self ht))).differentiableAt
      |>.differentiableWithinAt
  · intro t ht
    rw [interior_Icc] at ht
    have hd := (hasDerivAt_lineVarianceDeriv' hS ν hF θ₀ e (hab (Ioo_subset_Icc_self ht)))
    exact (hd.congr_of_eventuallyEq (hev t (hab (Ioo_subset_Icc_self ht)))).differentiableAt
      |>.differentiableWithinAt
  · intro t ht
    rw [interior_Icc] at ht
    have hd := (hasDerivAt_lineVarianceDeriv' hS ν hF θ₀ e (hab (Ioo_subset_Icc_self ht)))
    have hd' := hd.congr_of_eventuallyEq (hev t (hab (Ioo_subset_Icc_self ht)))
    change deriv (deriv (lineVariance hS ν F θ₀ e)) t ≤ 0
    rw [hd'.deriv]
    have h1 := hpair t (Ioo_subset_Icc_self ht)
    have : 0 ≤ (lawCov (Pfam (θl θ₀ e t : J → ℝ)) F (dirLoss S (Vl θ₀ e t : J → ℝ))) ^ 2 :=
      sq_nonneg _
    linarith

/-- **Vanishing variance–curvature pairing gives concave posterior variances along mean
segments** (the residual-flat case): if `E_t[(F − E_t F)² r_{V_t V_t}] = 0` along the line, the
variance is concave on every interval inside the domain. -/
theorem concaveOn_lineVariance_of_flat {F : X → ℝ} (hF : Bdd F) (θ₀ e : 𝕍) {a b : ℝ}
    (hab : Icc a b ⊆ responseLineDomain S ν θ₀ e)
    (hflat : ∀ t ∈ Icc a b, varianceCurvaturePairing hS ν F θ₀ e t = 0) :
    ConcaveOn ℝ (Icc a b) (lineVariance hS ν F θ₀ e) :=
  concaveOn_lineVariance_of_pairing_nonpos hS ν hF θ₀ e hab fun t ht ↦ (hflat t ht).le

end Variance

end Laplace.Multi
