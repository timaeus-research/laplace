/-
Copyright (c) 2026 Timaeus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Timaeus
-/
import Mathlib
import Laplace.Multi.JointChartMetric
import Laplace.Multi.LossCurvature

/-!
# The mixture bending form of the fixed-temperature family

At a member `P_{t,a}` with centred features `Z = R − M` and feature covariance `C`, let
`V_v = (C⁻¹v)·R` be the whitened feature direction of a response direction `v`. The
**mixture bending form**

`𝓑(v, w) = V_v V_w − ⟨V_v V_w⟩ − Zᵀ C⁻¹ ⟨Z V_v V_w⟩`   (`mixBend`)

is the Fisher-normal, density-normalised mixture acceleration of the fixed-temperature family along
the response directions `v, w`: it is symmetric (`mixBend_comm`), centred (`priorExp_mixBend`), and
orthogonal to every feature (`priorExp_centredFeat_mul_mixBend`), and its pairing with the loss
residual `H = L₀ − b·R` is the response block of the loss Hessian,

`⟨H 𝓑(v, w)⟩ = κ₃(H, V_v, V_w)`   (`priorExp_residual_mul_mixBend`).

Thus the residual third cumulants of the unified Hessian measure the mixture bending of the
exponentially flat fixed-temperature leaf inside the joint family.
-/

open MeasureTheory Filter Topology Set

namespace Laplace.Multi

variable {X : Type*} [MeasurableSpace X] {μ : Measure X} {ι : Type*} [Fintype ι]

/-- The centred features `Zᵢ = Rᵢ − ⟨Rᵢ⟩`. -/
noncomputable def centredFeat (μ : Measure X) (π L₀ : X → ℝ) (R : ι → X → ℝ) (t : ℝ) (a : ι → ℝ)
    (i : ι) : X → ℝ :=
  fun x ↦ R i x - priorExp μ π (affLoss L₀ R a) (R i) t

/-- The whitened feature direction `V_v = (C⁻¹v)·R`. -/
noncomputable def whitenedDir [DecidableEq ι] (μ : Measure X) (π L₀ : X → ℝ) (R : ι → X → ℝ)
    (t : ℝ) (a v : ι → ℝ) : X → ℝ :=
  dirLoss R ((featCov μ π L₀ R t a)⁻¹.mulVec v)

/-- The product observable `V_v V_w`. -/
noncomputable def prodObs [DecidableEq ι] (μ : Measure X) (π L₀ : X → ℝ) (R : ι → X → ℝ)
    (t : ℝ) (a v w : ι → ℝ) : X → ℝ :=
  fun x ↦ whitenedDir μ π L₀ R t a v x * whitenedDir μ π L₀ R t a w x

/-- The mixture bending form `𝓑(v, w) = V_v V_w − ⟨V_v V_w⟩ − Zᵀ C⁻¹ ⟨Z V_v V_w⟩`. -/
noncomputable def mixBend [DecidableEq ι] (μ : Measure X) (π L₀ : X → ℝ) (R : ι → X → ℝ)
    (t : ℝ) (a v w : ι → ℝ) : X → ℝ :=
  fun x ↦ prodObs μ π L₀ R t a v w x - priorExp μ π (affLoss L₀ R a) (prodObs μ π L₀ R t a v w) t -
    dirLoss (centredFeat μ π L₀ R t a) ((featCov μ π L₀ R t a)⁻¹.mulVec
      (fun k ↦ priorExp μ π (affLoss L₀ R a)
        (fun x ↦ centredFeat μ π L₀ R t a k x * prodObs μ π L₀ R t a v w x) t)) x

theorem prodObs_comm [DecidableEq ι] (π L₀ : X → ℝ) (R : ι → X → ℝ) (t : ℝ) (a v w : ι → ℝ) :
    prodObs μ π L₀ R t a v w = prodObs μ π L₀ R t a w v :=
  funext fun _ ↦ mul_comm _ _

/-- The bending form is symmetric. -/
theorem mixBend_comm [DecidableEq ι] (π L₀ : X → ℝ) (R : ι → X → ℝ) (t : ℝ) (a v w : ι → ℝ) :
    mixBend μ π L₀ R t a v w = mixBend μ π L₀ R t a w v := by
  unfold mixBend
  rw [prodObs_comm π L₀ R t a v w]

section

variable [Nonempty X] {π L₀ : X → ℝ} (hπm : Measurable π) (hπi : Integrable π μ) (hπ : ∀ x, 0 < π x)
  (hπpos : 0 < ∫ x, π x ∂μ) (hL₀m : Measurable L₀) {M₀ : ℝ} (hL₀ : ∀ x, |L₀ x| ≤ M₀)
  {R : ι → X → ℝ} (hR : ∀ i, Bdd (R i)) {t : ℝ}
include hπm hπi hπ hπpos hL₀m hL₀ hR

omit [Nonempty X] hπm hπi hπ hπpos hL₀m hL₀ in
theorem bdd_centredFeat (a : ι → ℝ) (i : ι) : Bdd (centredFeat μ π L₀ R t a i) :=
  (hR i).sub (Bdd.const _)

/-- The centred features have mean zero. -/
theorem priorExp_centredFeat (a : ι → ℝ) (i : ι) :
    priorExp μ π (affLoss L₀ R a) (centredFeat μ π L₀ R t a i) t = 0 := by
  have hZ := (affZ_pos hπm hπi hπ hπpos hL₀m hL₀ hR (t := t) a).ne'
  have e : centredFeat μ π L₀ R t a i =
      fun x ↦ R i x + (-priorExp μ π (affLoss L₀ R a) (R i) t) := funext fun x ↦ by
    simp [centredFeat, sub_eq_add_neg]
  rw [e, priorExp_add_bdd hπm hπi hπ hπpos hL₀m hL₀ hR a (hR i) (Bdd.const _),
    priorExp_const_fun hZ]
  ring

/-- Expectations against a centred feature are covariances: `⟨Zᵢ φ⟩ = Cov(Rᵢ, φ)`. -/
theorem priorExp_centredFeat_mul (a : ι → ℝ) (i : ι) {φ : X → ℝ} (hφ : Bdd φ) :
    priorExp μ π (affLoss L₀ R a) (fun x ↦ centredFeat μ π L₀ R t a i x * φ x) t =
      priorCov μ π (affLoss L₀ R a) (R i) φ t := by
  have e : (fun x ↦ centredFeat μ π L₀ R t a i x * φ x) =
      fun x ↦ R i x * φ x + (-priorExp μ π (affLoss L₀ R a) (R i) t) * φ x :=
    funext fun x ↦ by simp only [centredFeat]; ring
  rw [e, priorExp_add_bdd hπm hπi hπ hπpos hL₀m hL₀ hR a ((hR i).mul hφ) (hφ.const_mul _),
    priorExp_const_mul_bdd]
  unfold priorCov
  ring

section Bend

variable [DecidableEq ι]
  (hnd : ∀ v : ι → ℝ, v ≠ 0 → ¬ ∃ c : ℝ, ∀ᵐ x ∂μ, π x ≠ 0 → dirLoss R v x = c) (ht : 0 < t)
include hnd ht

omit [Nonempty X] hπm hπi hπ hπpos hL₀m hL₀ hnd ht in
theorem bdd_prodObs (a v w : ι → ℝ) : Bdd (prodObs μ π L₀ R t a v w) :=
  (bdd_dirLoss hR _).mul (bdd_dirLoss hR _)

omit hnd ht in
/-- The bending form decomposes as `V_vV_w − c − dirLoss Z d`, exposing its linear structure. -/
theorem priorExp_mixBend_eq (a v w : ι → ℝ) {φ : X → ℝ} (hφ : Bdd φ) :
    priorExp μ π (affLoss L₀ R a) (fun x ↦ φ x * mixBend μ π L₀ R t a v w x) t =
      priorExp μ π (affLoss L₀ R a) (fun x ↦ φ x * prodObs μ π L₀ R t a v w x) t -
        priorExp μ π (affLoss L₀ R a) (prodObs μ π L₀ R t a v w) t *
          priorExp μ π (affLoss L₀ R a) φ t -
        ∑ i, (featCov μ π L₀ R t a)⁻¹.mulVec (fun k ↦ priorExp μ π (affLoss L₀ R a)
          (fun x ↦ centredFeat μ π L₀ R t a k x * prodObs μ π L₀ R t a v w x) t) i *
          priorExp μ π (affLoss L₀ R a) (fun x ↦ φ x * centredFeat μ π L₀ R t a i x) t := by
  have hν : Integrable (baseWeight π (affLoss L₀ R a) t) μ :=
    (tiltData_aff hπm hπi (fun x ↦ (hπ x).le) hπpos hL₀m hL₀ hR a a t).choose_spec.ν_int
  set c := priorExp μ π (affLoss L₀ R a) (prodObs μ π L₀ R t a v w) t with hc
  set d := (featCov μ π L₀ R t a)⁻¹.mulVec (fun k ↦ priorExp μ π (affLoss L₀ R a)
    (fun x ↦ centredFeat μ π L₀ R t a k x * prodObs μ π L₀ R t a v w x) t) with hd
  have e : (fun x ↦ φ x * mixBend μ π L₀ R t a v w x) =
      fun x ↦ φ x * prodObs μ π L₀ R t a v w x +
        ((-c) * φ x + dirLoss (fun i x ↦ φ x * centredFeat μ π L₀ R t a i x) (-d) x) := by
    funext x
    simp only [mixBend, dirLoss, Pi.neg_apply]
    rw [← hd, ← hc]
    have : ∑ i, -d i * (φ x * centredFeat μ π L₀ R t a i x) =
        -∑ i, φ x * (d i * centredFeat μ π L₀ R t a i x) := by
      rw [← Finset.sum_neg_distrib]
      exact Finset.sum_congr rfl fun i _ ↦ by ring
    rw [this, mul_sub, mul_sub, Finset.mul_sum]
    ring
  rw [e, priorExp_add_bdd hπm hπi hπ hπpos hL₀m hL₀ hR a (hφ.mul (bdd_prodObs hR a v w))
    ((hφ.const_mul _).add (bdd_dirLoss (fun i ↦ hφ.mul (bdd_centredFeat hR a i)) _)),
    priorExp_add_bdd hπm hπi hπ hπpos hL₀m hL₀ hR a (hφ.const_mul _)
      (bdd_dirLoss (fun i ↦ hφ.mul (bdd_centredFeat hR a i)) _),
    priorExp_const_mul_bdd, priorExp_dirLoss hν (fun i ↦ hφ.mul (bdd_centredFeat hR a i))]
  simp only [Pi.neg_apply, neg_mul, Finset.sum_neg_distrib]
  ring

omit hnd ht in
/-- **The bending form is centred**: `⟨𝓑(v, w)⟩ = 0`. -/
theorem priorExp_mixBend (a v w : ι → ℝ) :
    priorExp μ π (affLoss L₀ R a) (mixBend μ π L₀ R t a v w) t = 0 := by
  have hZ := (affZ_pos hπm hπi hπ hπpos hL₀m hL₀ hR (t := t) a).ne'
  have h := priorExp_mixBend_eq hπm hπi hπ hπpos hL₀m hL₀ hR (t := t) a v w
    (φ := fun _ ↦ (1 : ℝ)) (Bdd.const 1)
  simp only [one_mul] at h
  rw [priorExp_const_fun hZ] at h
  rw [h]
  simp only [mul_one]
  rw [Finset.sum_eq_zero fun i _ ↦ by rw [priorExp_centredFeat hπm hπi hπ hπpos hL₀m hL₀ hR,
    mul_zero]]
  ring

omit [DecidableEq ι] hnd ht in
/-- `⟨Zᵢ Zⱼ⟩ = Cᵢⱼ`. -/
theorem priorExp_centredFeat_mul_centredFeat (a : ι → ℝ) (i j : ι) :
    priorExp μ π (affLoss L₀ R a)
      (fun x ↦ centredFeat μ π L₀ R t a i x * centredFeat μ π L₀ R t a j x) t =
      featCov μ π L₀ R t a i j := by
  rw [priorExp_centredFeat_mul hπm hπi hπ hπpos hL₀m hL₀ hR a i (bdd_centredFeat hR a j)]
  unfold priorCov
  rw [priorExp_centredFeat hπm hπi hπ hπpos hL₀m hL₀ hR, mul_zero, sub_zero]
  have e : (fun x ↦ R i x * centredFeat μ π L₀ R t a j x) =
      fun x ↦ centredFeat μ π L₀ R t a j x * R i x := funext fun x ↦ mul_comm _ _
  rw [e, priorExp_centredFeat_mul hπm hπi hπ hπpos hL₀m hL₀ hR a j (hR i),
    priorCov_comm π _ (R j) (R i) t]
  rfl

/-- **The bending form is orthogonal to every feature**: `⟨Zⱼ 𝓑(v, w)⟩ = 0` (Fisher-normality). -/
theorem priorExp_centredFeat_mul_mixBend (a v w : ι → ℝ) (j : ι) :
    priorExp μ π (affLoss L₀ R a)
      (fun x ↦ centredFeat μ π L₀ R t a j x * mixBend μ π L₀ R t a v w x) t = 0 := by
  have h := priorExp_mixBend_eq hπm hπi hπ hπpos hL₀m hL₀ hR (t := t) a v w
    (φ := centredFeat μ π L₀ R t a j) (bdd_centredFeat hR a j)
  rw [h, priorExp_centredFeat hπm hπi hπ hπpos hL₀m hL₀ hR, mul_zero, sub_zero]
  simp only [priorExp_centredFeat_mul_centredFeat hπm hπi hπ hπpos hL₀m hL₀ hR]
  -- the sum is `(C d)ⱼ` with `d = C⁻¹ e`, i.e. `eⱼ`
  have hCd : (featCov μ π L₀ R t a).mulVec ((featCov μ π L₀ R t a)⁻¹.mulVec (fun k ↦
      priorExp μ π (affLoss L₀ R a)
        (fun x ↦ centredFeat μ π L₀ R t a k x * prodObs μ π L₀ R t a v w x) t)) =
      fun k ↦ priorExp μ π (affLoss L₀ R a)
        (fun x ↦ centredFeat μ π L₀ R t a k x * prodObs μ π L₀ R t a v w x) t := by
    rw [Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _ ((Matrix.isUnit_iff_isUnit_det _).1
      (isUnit_featCov hπm hπi hπ hπpos hL₀m hL₀ hR hnd ht a)), Matrix.one_mulVec]
  have hsum : ∑ i, (featCov μ π L₀ R t a)⁻¹.mulVec (fun k ↦ priorExp μ π (affLoss L₀ R a)
      (fun x ↦ centredFeat μ π L₀ R t a k x * prodObs μ π L₀ R t a v w x) t) i *
        featCov μ π L₀ R t a j i =
      (featCov μ π L₀ R t a).mulVec ((featCov μ π L₀ R t a)⁻¹.mulVec (fun k ↦
        priorExp μ π (affLoss L₀ R a)
          (fun x ↦ centredFeat μ π L₀ R t a k x * prodObs μ π L₀ R t a v w x) t)) j := by
    change _ = ∑ i, featCov μ π L₀ R t a j i * (featCov μ π L₀ R t a)⁻¹.mulVec (fun k ↦
      priorExp μ π (affLoss L₀ R a)
        (fun x ↦ centredFeat μ π L₀ R t a k x * prodObs μ π L₀ R t a v w x) t) i
    exact Finset.sum_congr rfl fun i _ ↦ mul_comm _ _
  rw [hsum, hCd, sub_self]

omit hnd ht in
/-- **The loss pairing of the bending form is the response block of the loss Hessian**:
`⟨H 𝓑(v, w)⟩ = κ₃(H, V_v, V_w)` for the residual `H = L₀ − b·R`, `C b = c`. -/
theorem priorExp_residual_mul_mixBend (a v w : ι → ℝ) {b : ι → ℝ}
    (hb : (featCov μ π L₀ R t a).mulVec b = featObsCov μ π L₀ R t a L₀) :
    priorExp μ π (affLoss L₀ R a)
        (fun x ↦ (L₀ x - dirLoss R b x) * mixBend μ π L₀ R t a v w x) t =
      priorCum3 μ π (affLoss L₀ R a) (fun x ↦ L₀ x - dirLoss R b x)
        (whitenedDir μ π L₀ R t a v) (whitenedDir μ π L₀ R t a w) t := by
  have hL : Bdd L₀ := ⟨hL₀m, M₀, hL₀⟩
  have hH : Bdd (fun x ↦ L₀ x - dirLoss R b x) := hL.sub (bdd_dirLoss hR b)
  have h := priorExp_mixBend_eq hπm hπi hπ hπpos hL₀m hL₀ hR (t := t) a v w hH
  rw [h]
  -- `⟨H Zᵢ⟩ = Cov(H, Rᵢ) = 0`
  have hHZ : ∀ i, priorExp μ π (affLoss L₀ R a)
      (fun x ↦ (L₀ x - dirLoss R b x) * centredFeat μ π L₀ R t a i x) t = 0 := by
    intro i
    have e : (fun x ↦ (L₀ x - dirLoss R b x) * centredFeat μ π L₀ R t a i x) =
        fun x ↦ centredFeat μ π L₀ R t a i x * (L₀ x - dirLoss R b x) :=
      funext fun x ↦ mul_comm _ _
    rw [e, priorExp_centredFeat_mul hπm hπi hπ hπpos hL₀m hL₀ hR a i hH, priorCov_comm π _ (R i),
      ← dirLoss_pi_single R i]
    exact priorCov_residual_dirLoss hπm hπi hπ hπpos hL₀m hL₀ hR a hb _
  simp only [hHZ, mul_zero, Finset.sum_const_zero, sub_zero]
  -- `Cov(H, V_v) = 0` and `Cov(H, V_w) = 0` reduce `κ₃` to a centred second moment
  have hv := priorCov_residual_dirLoss hπm hπi hπ hπpos hL₀m hL₀ hR a hb
    ((featCov μ π L₀ R t a)⁻¹.mulVec v)
  have hw := priorCov_residual_dirLoss hπm hπi hπ hπpos hL₀m hL₀ hR a hb
    ((featCov μ π L₀ R t a)⁻¹.mulVec w)
  unfold priorCov at hv hw
  beta_reduce at hv hw
  have hp : prodObs μ π L₀ R t a v w = fun x ↦ dirLoss R ((featCov μ π L₀ R t a)⁻¹.mulVec v) x *
      dirLoss R ((featCov μ π L₀ R t a)⁻¹.mulVec w) x := rfl
  have e2 : (fun x ↦ (L₀ x - dirLoss R b x) *
      (dirLoss R ((featCov μ π L₀ R t a)⁻¹.mulVec v) x *
        dirLoss R ((featCov μ π L₀ R t a)⁻¹.mulVec w) x)) =
      fun x ↦ (L₀ x - dirLoss R b x) * dirLoss R ((featCov μ π L₀ R t a)⁻¹.mulVec v) x *
        dirLoss R ((featCov μ π L₀ R t a)⁻¹.mulVec w) x := funext fun x ↦ by ring
  simp only [priorCum3, whitenedDir, hp]
  rw [e2]
  linear_combination
    (priorExp μ π (affLoss L₀ R a) (dirLoss R ((featCov μ π L₀ R t a)⁻¹.mulVec w)) t) * hv +
      (priorExp μ π (affLoss L₀ R a) (dirLoss R ((featCov μ π L₀ R t a)⁻¹.mulVec v)) t) * hw

end Bend

end

end Laplace.Multi
