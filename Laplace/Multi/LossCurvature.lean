/-
Copyright (c) 2026 Timaeus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Timaeus
-/
import Mathlib
import Laplace.Multi.ResidualFormDeriv
import Laplace.Multi.ReducedPotential
import Laplace.Multi.TwoAxisResponse

/-!
# The curvature of the loss surface in the temperature

At fixed feature response `M`, the loss surface `h(t, M)` descends at the rate of the unexplained
variance, `∂_t h = −σ²`, `σ² = Var(H)`, `H = L₀ − b·R` the regression residual (`LossSurface`). Its
curvature is the third cumulant of the residual:

  `∂_t² h(t, M) = κ₃(H, H, H)`   (`hasDerivAt_deriv_lossSurface`).

The proof runs through the residual-cumulant calculus: along the temperature path every covariance
moves by `−κ₃(·, ·, H)` (`hasDerivAt_priorCov_tempPath`), so `v = Var L₀`, `c = Cov(R, L₀)` and
`C = Cov(R, R)` all have third-cumulant derivatives; the regression coefficients `b = C⁻¹c` are
continuous (`continuousAt_regression`); the envelope lemma `hasDerivAt_residual_form` then gives
`(σ²)' = v' − 2⟨b, c'⟩ + ⟨b, C'b⟩ = −κ₃(H, H, H)` by multilinearity (`priorCum3_residual_expand`).
Unexplained variance drives the descent; unexplained skewness drives its curvature.
-/

open MeasureTheory Filter Topology Set

namespace Laplace.Multi

variable {X : Type*} [MeasurableSpace X] {μ : Measure X} {ι : Type*} [Fintype ι]

section Multilinear

variable [Nonempty X] {π L₀ : X → ℝ} (hπm : Measurable π) (hπi : Integrable π μ) (hπ : ∀ x, 0 < π x)
  (hπpos : 0 < ∫ x, π x ∂μ) (hL₀m : Measurable L₀) {M₀ : ℝ} (hL₀ : ∀ x, |L₀ x| ≤ M₀)
  {R : ι → X → ℝ} (hR : ∀ i, Bdd (R i)) {t : ℝ}
include hπm hπi hπ hπpos hL₀m hL₀ hR

omit [Nonempty X] in
/-- `κ₃(R_u, ψ, χ) = ∑ᵢ uᵢ κ₃(Rᵢ, ψ, χ)`. -/
theorem priorCum3_dirLoss_left (a : ι → ℝ) (u : ι → ℝ) {ψ χ : X → ℝ} (hψ : Bdd ψ) (hχ : Bdd χ) :
    priorCum3 μ π (affLoss L₀ R a) (dirLoss R u) ψ χ t =
      ∑ i, u i * priorCum3 μ π (affLoss L₀ R a) (R i) ψ χ t := by
  have hν : Integrable (baseWeight π (affLoss L₀ R a) t) μ :=
    (tiltData_aff hπm hπi (fun x ↦ (hπ x).le) hπpos hL₀m hL₀ hR a a t).choose_spec.ν_int
  have e1 : (fun x ↦ dirLoss R u x * ψ x * χ x) = dirLoss (fun i x ↦ R i x * ψ x * χ x) u := by
    funext x; simp only [dirLoss, Finset.sum_mul, mul_assoc]
  have e2 : (fun x ↦ dirLoss R u x * ψ x) = dirLoss (fun i x ↦ R i x * ψ x) u := by
    funext x; simp only [dirLoss, Finset.sum_mul, mul_assoc]
  have e3 : (fun x ↦ dirLoss R u x * χ x) = dirLoss (fun i x ↦ R i x * χ x) u := by
    funext x; simp only [dirLoss, Finset.sum_mul, mul_assoc]
  simp only [priorCum3]
  rw [e1, e2, e3, priorExp_dirLoss hν (fun i ↦ ((hR i).mul hψ).mul hχ) u,
    priorExp_dirLoss hν (fun i ↦ (hR i).mul hψ) u, priorExp_dirLoss hν (fun i ↦ (hR i).mul hχ) u,
    priorExp_dirLoss hν hR u]
  have h2 : (∑ i, u i * priorExp μ π (affLoss L₀ R a) (fun x ↦ R i x * ψ x) t) *
      priorExp μ π (affLoss L₀ R a) χ t =
      ∑ i, u i * (priorExp μ π (affLoss L₀ R a) (fun x ↦ R i x * ψ x) t *
        priorExp μ π (affLoss L₀ R a) χ t) := by
    rw [Finset.sum_mul]; exact Finset.sum_congr rfl fun i _ ↦ by ring
  have h3 : (∑ i, u i * priorExp μ π (affLoss L₀ R a) (fun x ↦ R i x * χ x) t) *
      priorExp μ π (affLoss L₀ R a) ψ t =
      ∑ i, u i * (priorExp μ π (affLoss L₀ R a) (fun x ↦ R i x * χ x) t *
        priorExp μ π (affLoss L₀ R a) ψ t) := by
    rw [Finset.sum_mul]; exact Finset.sum_congr rfl fun i _ ↦ by ring
  have h4 : priorExp μ π (affLoss L₀ R a) (fun x ↦ ψ x * χ x) t *
      (∑ i, u i * priorExp μ π (affLoss L₀ R a) (R i) t) =
      ∑ i, u i * (priorExp μ π (affLoss L₀ R a) (fun x ↦ ψ x * χ x) t *
        priorExp μ π (affLoss L₀ R a) (R i) t) := by
    rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun i _ ↦ by ring
  have h5 : 2 * (∑ i, u i * priorExp μ π (affLoss L₀ R a) (R i) t) *
      priorExp μ π (affLoss L₀ R a) ψ t * priorExp μ π (affLoss L₀ R a) χ t =
      ∑ i, u i * (2 * priorExp μ π (affLoss L₀ R a) (R i) t * priorExp μ π (affLoss L₀ R a) ψ t *
        priorExp μ π (affLoss L₀ R a) χ t) := by
    rw [Finset.mul_sum, Finset.sum_mul, Finset.sum_mul]
    exact Finset.sum_congr rfl fun i _ ↦ by ring
  rw [h2, h3, h4, h5]
  simp only [mul_sub, mul_add, Finset.sum_sub_distrib, Finset.sum_add_distrib]

/-- `κ₃(f − g, ψ, χ) = κ₃(f, ψ, χ) − κ₃(g, ψ, χ)` for bounded observables. -/
theorem priorCum3_sub_left (a : ι → ℝ) {f g ψ χ : X → ℝ} (hf : Bdd f) (hg : Bdd g) (hψ : Bdd ψ)
    (hχ : Bdd χ) :
    priorCum3 μ π (affLoss L₀ R a) (fun x ↦ f x - g x) ψ χ t =
      priorCum3 μ π (affLoss L₀ R a) f ψ χ t - priorCum3 μ π (affLoss L₀ R a) g ψ χ t := by
  simp only [priorCum3]
  have e1 : (fun x ↦ (f x - g x) * ψ x * χ x) =
      fun x ↦ f x * ψ x * χ x + (-1) * (g x * ψ x * χ x) :=
    funext fun x ↦ by ring
  have e2 : (fun x ↦ (f x - g x) * ψ x) = fun x ↦ f x * ψ x + (-1) * (g x * ψ x) :=
    funext fun x ↦ by ring
  have e3 : (fun x ↦ (f x - g x) * χ x) = fun x ↦ f x * χ x + (-1) * (g x * χ x) :=
    funext fun x ↦ by ring
  have e4 : (fun x ↦ f x - g x) = fun x ↦ f x + (-1) * g x := funext fun x ↦ by ring
  rw [e1, e2, e3, e4, priorExp_add_bdd hπm hπi hπ hπpos hL₀m hL₀ hR a ((hf.mul hψ).mul hχ)
    (((hg.mul hψ).mul hχ).const_mul _), priorExp_add_bdd hπm hπi hπ hπpos hL₀m hL₀ hR a
    (hf.mul hψ) ((hg.mul hψ).const_mul _), priorExp_add_bdd hπm hπi hπ hπpos hL₀m hL₀ hR a
    (hf.mul hχ) ((hg.mul hχ).const_mul _), priorExp_add_bdd hπm hπi hπ hπpos hL₀m hL₀ hR a hf
    (hg.const_mul _), priorExp_const_mul_bdd, priorExp_const_mul_bdd, priorExp_const_mul_bdd,
    priorExp_const_mul_bdd]
  ring

/-- **Expansion of the residual third cumulant**: with `H = L₀ − R_b`,
`κ₃(H, H, χ) = κ₃(L₀,L₀,χ) − 2 ∑ᵢ bᵢ κ₃(Rᵢ,L₀,χ) + ∑ᵢⱼ bᵢ bⱼ κ₃(Rᵢ,Rⱼ,χ)`. -/
theorem priorCum3_residual_expand (a : ι → ℝ) (b : ι → ℝ) {χ : X → ℝ} (hχ : Bdd χ) :
    priorCum3 μ π (affLoss L₀ R a) (fun x ↦ L₀ x - dirLoss R b x) (fun x ↦ L₀ x - dirLoss R b x)
        χ t =
      priorCum3 μ π (affLoss L₀ R a) L₀ L₀ χ t -
        2 * ∑ i, b i * priorCum3 μ π (affLoss L₀ R a) (R i) L₀ χ t +
        ∑ i, b i * ∑ j, b j * priorCum3 μ π (affLoss L₀ R a) (R i) (R j) χ t := by
  have hL : Bdd L₀ := ⟨hL₀m, M₀, hL₀⟩
  have hb := bdd_dirLoss hR b
  have hres : Bdd fun x ↦ L₀ x - dirLoss R b x := hL.sub hb
  rw [priorCum3_sub_left hπm hπi hπ hπpos hL₀m hL₀ hR a hL hb hres hχ,
    priorCum3_dirLoss_left hπm hπi hπ hπpos hL₀m hL₀ hR a b hres hχ]
  -- second slot via the swap
  have e0 : priorCum3 μ π (affLoss L₀ R a) L₀ (fun x ↦ L₀ x - dirLoss R b x) χ t =
      priorCum3 μ π (affLoss L₀ R a) L₀ L₀ χ t -
        ∑ i, b i * priorCum3 μ π (affLoss L₀ R a) (R i) L₀ χ t := by
    rw [priorCum3_swap₁₂, priorCum3_sub_left hπm hπi hπ hπpos hL₀m hL₀ hR a hL hb hL hχ,
      priorCum3_dirLoss_left hπm hπi hπ hπpos hL₀m hL₀ hR a b hL hχ]
  have e1 : ∀ i, priorCum3 μ π (affLoss L₀ R a) (R i) (fun x ↦ L₀ x - dirLoss R b x) χ t =
      priorCum3 μ π (affLoss L₀ R a) (R i) L₀ χ t -
        ∑ j, b j * priorCum3 μ π (affLoss L₀ R a) (R i) (R j) χ t := fun i ↦ by
    rw [priorCum3_swap₁₂, priorCum3_sub_left hπm hπi hπ hπpos hL₀m hL₀ hR a hL hb (hR i) hχ,
      priorCum3_dirLoss_left hπm hπi hπ hπpos hL₀m hL₀ hR a b (hR i) hχ]
    congr 1
    · exact priorCum3_swap₁₂ π _ _ _ _ _
    · exact Finset.sum_congr rfl fun j _ ↦ by rw [priorCum3_swap₁₂ π _ (R j) (R i) χ t]
  rw [e0]
  simp only [e1, mul_sub, Finset.sum_sub_distrib]
  ring

end Multilinear

section Curvature

variable [Nonempty X] {π L₀ : X → ℝ} (hπm : Measurable π) (hπi : Integrable π μ) (hπ : ∀ x, 0 < π x)
  (hπpos : 0 < ∫ x, π x ∂μ) (hL₀m : Measurable L₀) {M₀ : ℝ} (hL₀ : ∀ x, |L₀ x| ≤ M₀)
  {R : ι → X → ℝ} (hR : ∀ i, Bdd (R i))
  (hnd : ∀ v : ι → ℝ, v ≠ 0 → ¬ ∃ c : ℝ, ∀ᵐ x ∂μ, π x ≠ 0 → dirLoss R v x = c)
  [Nonempty ι] [DecidableEq ι]
include hπm hπi hπ hπpos hL₀m hL₀ hR hnd

omit [Nonempty X] hπm hπi hπ hπpos hL₀m hL₀ hR hnd [Nonempty ι] [DecidableEq ι] in
/-- The third cumulant in the joint family at `Θ(t, a)` is the third cumulant at `(t, a)`. -/
theorem priorCum3_natCoord (π L₀ : X → ℝ) (R : ι → X → ℝ) (t : ℝ) (a : ι → ℝ) (φ ψ χ : X → ℝ) :
    priorCum3 μ π (affLoss (fun _ ↦ (0 : ℝ)) (jointStat L₀ R) (natCoord t a)) φ ψ χ 1 =
      priorCum3 μ π (affLoss L₀ R a) φ ψ χ t := by
  simp only [priorCum3, priorExp_natCoord]

/-- The regression coefficients of the loss on the features at `(t, m_t⁻¹(M))`. -/
noncomputable def regCoeff (μ : Measure X) (π L₀ : X → ℝ) (R : ι → X → ℝ) (M : ι → ℝ) (t : ℝ) :
    ι → ℝ :=
  (featCov μ π L₀ R t (Function.invFun (meanMap μ π L₀ R t) M))⁻¹.mulVec
    (featObsCov μ π L₀ R t (Function.invFun (meanMap μ π L₀ R t) M) L₀)

omit [Nonempty ι] in
theorem isUnit_featCov {t : ℝ} (ht : 0 < t) (a : ι → ℝ) : IsUnit (featCov μ π L₀ R t a) := by
  classical
  exact Matrix.mulVec_injective_iff_isUnit.1
    (featCov_mulVec_injective hπm hπi hπ hπpos hL₀m hL₀ hR hnd ht a)

omit [Nonempty ι] in
/-- The regression coefficients solve the normal equations `C b = c`. -/
theorem featCov_mulVec_regCoeff {t : ℝ} (ht : 0 < t) (M : ι → ℝ) :
    (featCov μ π L₀ R t (Function.invFun (meanMap μ π L₀ R t) M)).mulVec (regCoeff μ π L₀ R M t) =
      featObsCov μ π L₀ R t (Function.invFun (meanMap μ π L₀ R t) M) L₀ := by
  unfold regCoeff
  rw [Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _
    ((Matrix.isUnit_iff_isUnit_det _).1 (isUnit_featCov hπm hπi hπ hπpos hL₀m hL₀ hR hnd ht _)),
    Matrix.one_mulVec]

omit [Nonempty X] hπm hπi hπ hπpos hL₀m hL₀ hR hnd [Nonempty ι] [DecidableEq ι] in
theorem featCov_symm (π L₀ : X → ℝ) (R : ι → X → ℝ) (t : ℝ) (a : ι → ℝ) (i j : ι) :
    featCov μ π L₀ R t a i j = featCov μ π L₀ R t a j i := by
  simp only [featCov, Matrix.of_apply]
  exact priorCov_comm π _ (R i) (R j) t

/-- The residual `H = L₀ − b·R` is the velocity contrast of the temperature path. -/
theorem dirLoss_jointStat_velocity {t₀ : ℝ} (ht₀ : 0 < t₀) {M : ι → ℝ}
    (hM : M ∈ interior (momentBody μ π R)) :
    dirLoss (jointStat L₀ R) ((sliceMapEquiv hπm hπi hπ hπpos hL₀m hL₀ hR hnd
      (tempPath μ π L₀ R M t₀)).symm (Pi.single none 1)) =
      fun x ↦ L₀ x - dirLoss R (regCoeff μ π L₀ R M t₀) x := by
  funext x
  have hu1 := tempPath_velocity_none hπm hπi hπ hπpos hL₀m hL₀ hR hnd (tempPath μ π L₀ R M t₀)
  have hus := tempPath_velocity_some hπm hπi hπ hπpos hL₀m hL₀ hR hnd ht₀ hM
    (featCov_mulVec_regCoeff hπm hπi hπ hπpos hL₀m hL₀ hR hnd ht₀ M)
  simp only [dirLoss, jointStat, Fintype.sum_option, Option.elim, hu1, hus, one_mul, neg_mul,
    Finset.sum_neg_distrib]
  ring

/-- **Every covariance moves by the residual third cumulant along the temperature path**:
`d/dt Cov_{t,M}(φ, ψ) = −κ₃(φ, ψ, H)`. -/
theorem hasDerivAt_priorCov_tempPath {t₀ : ℝ} (ht₀ : 0 < t₀) {M : ι → ℝ}
    (hM : M ∈ interior (momentBody μ π R)) {φ ψ : X → ℝ} (hφ : Bdd φ) (hψ : Bdd ψ) :
    HasDerivAt (fun t ↦ priorCov μ π (affLoss L₀ R (Function.invFun (meanMap μ π L₀ R t) M)) φ ψ t)
      (-priorCum3 μ π (affLoss L₀ R (Function.invFun (meanMap μ π L₀ R t₀) M)) φ ψ
        (fun x ↦ L₀ x - dirLoss R (regCoeff μ π L₀ R M t₀) x) t₀) t₀ := by
  have hS' := bdd_jointStat hL₀m hL₀ hR
  have h0 : ∀ x, |(fun _ : X ↦ (0 : ℝ)) x| ≤ 0 := fun x ↦ by simp
  have hpath := hasDerivAt_tempPath hπm hπi hπ hπpos hL₀m hL₀ hR hnd ht₀ hM
  -- every bounded expectation moves by `−Cov(f, S_u)` along the path
  have hE : ∀ f : X → ℝ, Bdd f → HasDerivAt
      (fun t ↦ priorExp μ π (affLoss (fun _ ↦ (0 : ℝ)) (jointStat L₀ R) (tempPath μ π L₀ R M t))
        f ((fun _ ↦ (1 : ℝ)) t))
      (-1 * priorCov μ π (affLoss (fun _ ↦ (0 : ℝ)) (jointStat L₀ R) (tempPath μ π L₀ R M t₀)) f
        (dirLoss (jointStat L₀ R) ((sliceMapEquiv hπm hπi hπ hπpos hL₀m hL₀ hR hnd
          (tempPath μ π L₀ R M t₀)).symm (Pi.single none 1))) ((fun _ ↦ (1 : ℝ)) t₀)) t₀ := by
    intro f hf
    obtain ⟨hfm, Mf, hfb⟩ := hf
    have h := (hasFDerivAt_obsMap hπm hπi hπ hπpos measurable_const h0 hS' hfm hfb one_pos
      (tempPath μ π L₀ R M t₀)).comp_hasDerivAt t₀ hpath
    refine h.congr_deriv ?_
    exact obsMapDeriv_apply hπm hπi hπ hπpos measurable_const h0 hS' hfm hfb one_pos _ _
  have key := hasDerivAt_cov_of_hasDerivAt_exp
    (L := fun t ↦ affLoss (fun _ ↦ (0 : ℝ)) (jointStat L₀ R) (tempPath μ π L₀ R M t))
    (τ := fun _ ↦ (1 : ℝ)) (c := 1) hE hφ hψ
  rw [dirLoss_jointStat_velocity hπm hπi hπ hπpos hL₀m hL₀ hR hnd ht₀ hM] at key
  have hfun : (fun t ↦ priorCov μ π (affLoss L₀ R (Function.invFun (meanMap μ π L₀ R t) M)) φ ψ t)
      =ᶠ[𝓝 t₀] fun t ↦ priorCov μ π (affLoss (fun _ ↦ (0 : ℝ)) (jointStat L₀ R)
        (tempPath μ π L₀ R M t)) φ ψ ((fun _ ↦ (1 : ℝ)) t) := by
    filter_upwards [lt_mem_nhds ht₀] with t ht
    rw [tempPath_eq_natCoord hπm hπi hπ hπpos hL₀m hL₀ hR hnd ht hM, priorCov_natCoord]
  refine (key.congr_of_eventuallyEq hfun).congr_deriv ?_
  rw [tempPath_eq_natCoord hπm hπi hπ hπpos hL₀m hL₀ hR hnd ht₀ hM, priorCum3_natCoord]
  ring

/-- The regression coefficients are continuous in the temperature. -/
theorem continuousAt_regCoeff {t₀ : ℝ} (ht₀ : 0 < t₀) {M : ι → ℝ}
    (hM : M ∈ interior (momentBody μ π R)) :
    ContinuousAt (regCoeff μ π L₀ R M) t₀ := by
  have hL : Bdd L₀ := ⟨hL₀m, M₀, hL₀⟩
  have hC : ContinuousAt (fun t ↦ featCov μ π L₀ R t (Function.invFun (meanMap μ π L₀ R t) M))
      t₀ := by
    refine continuousAt_pi.2 fun i ↦ continuousAt_pi.2 fun j ↦ ?_
    exact (hasDerivAt_priorCov_tempPath hπm hπi hπ hπpos hL₀m hL₀ hR hnd ht₀ hM (hR i)
      (hR j)).continuousAt
  have hc : ContinuousAt (fun t ↦ featObsCov μ π L₀ R t (Function.invFun (meanMap μ π L₀ R t) M)
      L₀) t₀ := by
    refine continuousAt_pi.2 fun i ↦ ?_
    exact (hasDerivAt_priorCov_tempPath hπm hπi hπ hπpos hL₀m hL₀ hR hnd ht₀ hM (hR i)
      hL).continuousAt
  have hdet : (featCov μ π L₀ R t₀ (Function.invFun (meanMap μ π L₀ R t₀) M)).det ≠ 0 :=
    ((Matrix.isUnit_iff_isUnit_det _).1
      (isUnit_featCov hπm hπi hπ hπpos hL₀m hL₀ hR hnd ht₀ _)).ne_zero
  have hinv : ContinuousAt (fun t ↦ (featCov μ π L₀ R t (Function.invFun (meanMap μ π L₀ R t) M))⁻¹)
      t₀ := by
    refine (continuousAt_matrix_inv _ ?_).comp hC
    rw [Ring.inverse_eq_inv']
    exact continuousAt_inv₀ hdet
  unfold regCoeff
  refine continuousAt_pi.2 fun i ↦ ?_
  simp only [Matrix.mulVec, dotProduct]
  refine tendsto_finsetSum _ fun j _ ↦ ?_
  have h1 : ContinuousAt (fun t ↦ (featCov μ π L₀ R t (Function.invFun (meanMap μ π L₀ R t) M))⁻¹
      i j) t₀ := (continuous_id.matrix_elem i j).continuousAt.comp hinv
  exact h1.mul ((continuous_apply j).continuousAt.comp hc)

omit [Nonempty ι] in
/-- The unexplained variance as the residual form `v − ⟨c, b⟩`. -/
theorem residual_var_eq_form {t : ℝ} (ht : 0 < t) (M : ι → ℝ) :
    priorCov μ π (affLoss L₀ R (Function.invFun (meanMap μ π L₀ R t) M))
        (fun x ↦ L₀ x - dirLoss R (regCoeff μ π L₀ R M t) x)
        (fun x ↦ L₀ x - dirLoss R (regCoeff μ π L₀ R M t) x) t =
      priorCov μ π (affLoss L₀ R (Function.invFun (meanMap μ π L₀ R t) M)) L₀ L₀ t -
        dotProduct (featObsCov μ π L₀ R t (Function.invFun (meanMap μ π L₀ R t) M) L₀)
          (regCoeff μ π L₀ R M t) := by
  have hb := featCov_mulVec_regCoeff hπm hπi hπ hπpos hL₀m hL₀ hR hnd ht M
  rw [featCov_eq_covMat, featObsCov_eq_covVec] at hb
  have h := residual_var hπm hπi hπ hπpos hL₀m hL₀ hR (t := t) _ (fun k ↦ Pi.single k 1)
    ⟨hL₀m, M₀, hL₀⟩ (regCoeff μ π L₀ R M t) hb
  rw [sum_smul_single_eq] at h
  rw [h]
  congr 1
  simp only [dotProduct, featObsCov]
  exact Finset.sum_congr rfl fun k _ ↦ by rw [dirLoss_pi_single, mul_comm]

/-- **The derivative of the unexplained variance**: `(σ²)' = −κ₃(H, H, H)`. -/
theorem hasDerivAt_residual_var {t₀ : ℝ} (ht₀ : 0 < t₀) {M : ι → ℝ}
    (hM : M ∈ interior (momentBody μ π R)) :
    HasDerivAt (fun t ↦ priorCov μ π (affLoss L₀ R (Function.invFun (meanMap μ π L₀ R t) M))
        (fun x ↦ L₀ x - dirLoss R (regCoeff μ π L₀ R M t) x)
        (fun x ↦ L₀ x - dirLoss R (regCoeff μ π L₀ R M t) x) t)
      (-priorCum3 μ π (affLoss L₀ R (Function.invFun (meanMap μ π L₀ R t₀) M))
        (fun x ↦ L₀ x - dirLoss R (regCoeff μ π L₀ R M t₀) x)
        (fun x ↦ L₀ x - dirLoss R (regCoeff μ π L₀ R M t₀) x)
        (fun x ↦ L₀ x - dirLoss R (regCoeff μ π L₀ R M t₀) x) t₀) t₀ := by
  have hL : Bdd L₀ := ⟨hL₀m, M₀, hL₀⟩
  have hfun : (fun t ↦ priorCov μ π (affLoss L₀ R (Function.invFun (meanMap μ π L₀ R t) M))
      (fun x ↦ L₀ x - dirLoss R (regCoeff μ π L₀ R M t) x)
      (fun x ↦ L₀ x - dirLoss R (regCoeff μ π L₀ R M t) x) t) =ᶠ[𝓝 t₀] fun t ↦
      priorCov μ π (affLoss L₀ R (Function.invFun (meanMap μ π L₀ R t) M)) L₀ L₀ t -
        dotProduct (featObsCov μ π L₀ R t (Function.invFun (meanMap μ π L₀ R t) M) L₀)
          (regCoeff μ π L₀ R M t) := by
    filter_upwards [lt_mem_nhds ht₀] with t ht
    exact residual_var_eq_form hπm hπi hπ hπpos hL₀m hL₀ hR hnd ht M
  -- the envelope derivative
  have hv := hasDerivAt_priorCov_tempPath hπm hπi hπ hπpos hL₀m hL₀ hR hnd ht₀ hM hL hL
  have hc : ∀ i, HasDerivAt (fun t ↦ featObsCov μ π L₀ R t (Function.invFun (meanMap μ π L₀ R t) M)
      L₀ i) (-priorCum3 μ π (affLoss L₀ R (Function.invFun (meanMap μ π L₀ R t₀) M)) (R i) L₀
        (fun x ↦ L₀ x - dirLoss R (regCoeff μ π L₀ R M t₀) x) t₀) t₀ := fun i ↦
    hasDerivAt_priorCov_tempPath hπm hπi hπ hπpos hL₀m hL₀ hR hnd ht₀ hM (hR i) hL
  have hC : ∀ i j, HasDerivAt (fun t ↦ featCov μ π L₀ R t (Function.invFun (meanMap μ π L₀ R t) M)
      i j) (-priorCum3 μ π (affLoss L₀ R (Function.invFun (meanMap μ π L₀ R t₀) M)) (R i) (R j)
        (fun x ↦ L₀ x - dirLoss R (regCoeff μ π L₀ R M t₀) x) t₀) t₀ := fun i j ↦
    hasDerivAt_priorCov_tempPath hπm hπi hπ hπpos hL₀m hL₀ hR hnd ht₀ hM (hR i) (hR j)
  have hsym : ∀ t i j, featCov μ π L₀ R t (Function.invFun (meanMap μ π L₀ R t) M) i j =
      featCov μ π L₀ R t (Function.invFun (meanMap μ π L₀ R t) M) j i := fun t i j ↦
    featCov_symm π L₀ R t _ i j
  -- the normal equations hold only for `t > 0`: reparametrise by `τ t = t` for `t > 0`,
  -- `τ t = t₀` otherwise
  have hbcont := continuousAt_regCoeff hπm hπi hπ hπpos hL₀m hL₀ hR hnd ht₀ hM
  obtain ⟨τ, hτdef⟩ : ∃ τ : ℝ → ℝ, τ = fun t ↦ if 0 < t then t else t₀ := ⟨_, rfl⟩
  have hτpos : ∀ t, 0 < τ t := fun t ↦ by
    rw [hτdef]
    dsimp only
    split_ifs with h
    · exact h
    · exact ht₀
  have hτeq : ∀ᶠ t in 𝓝 t₀, τ t = t := by
    filter_upwards [lt_mem_nhds ht₀] with t ht
    rw [hτdef]
    exact if_pos ht
  have hτt₀ : τ t₀ = t₀ := by rw [hτdef]; exact if_pos ht₀
  have hform := hasDerivAt_residual_form
    (v := fun t ↦ priorCov μ π (affLoss L₀ R (Function.invFun (meanMap μ π L₀ R (τ t)) M)) L₀ L₀
      (τ t))
    (c := fun t ↦ featObsCov μ π L₀ R (τ t) (Function.invFun (meanMap μ π L₀ R (τ t)) M) L₀)
    (C := fun t ↦ featCov μ π L₀ R (τ t) (Function.invFun (meanMap μ π L₀ R (τ t)) M))
    (b := fun t ↦ regCoeff μ π L₀ R M (τ t))
    (c' := fun i ↦ -priorCum3 μ π (affLoss L₀ R (Function.invFun (meanMap μ π L₀ R t₀) M)) (R i)
      L₀ (fun x ↦ L₀ x - dirLoss R (regCoeff μ π L₀ R M t₀) x) t₀)
    (C' := Matrix.of fun i j ↦ -priorCum3 μ π
      (affLoss L₀ R (Function.invFun (meanMap μ π L₀ R t₀) M)) (R i) (R j)
      (fun x ↦ L₀ x - dirLoss R (regCoeff μ π L₀ R M t₀) x) t₀)
    (hv.congr_of_eventuallyEq (hτeq.mono fun t h ↦ by simp only [h]))
    (fun i ↦ (hc i).congr_of_eventuallyEq (hτeq.mono fun t h ↦ by simp only [h]))
    (fun i j ↦ (hC i j).congr_of_eventuallyEq (hτeq.mono fun t h ↦ by simp only [h]))
    (hbcont.congr (hτeq.mono fun t h ↦ by simp only [h]))
    (fun t i j ↦ hsym (τ t) i j)
    (fun t ↦ featCov_mulVec_regCoeff hπm hπi hπ hπpos hL₀m hL₀ hR hnd (hτpos t) M)
  have hfun' : (fun t ↦ priorCov μ π (affLoss L₀ R (Function.invFun (meanMap μ π L₀ R t) M))
      (fun x ↦ L₀ x - dirLoss R (regCoeff μ π L₀ R M t) x)
      (fun x ↦ L₀ x - dirLoss R (regCoeff μ π L₀ R M t) x) t) =ᶠ[𝓝 t₀] fun t ↦
      priorCov μ π (affLoss L₀ R (Function.invFun (meanMap μ π L₀ R (τ t)) M)) L₀ L₀ (τ t) -
        dotProduct (featObsCov μ π L₀ R (τ t) (Function.invFun (meanMap μ π L₀ R (τ t)) M) L₀)
          (regCoeff μ π L₀ R M (τ t)) := by
    filter_upwards [hfun, hτeq] with t ht hτ
    rw [ht, hτ]
  refine (hform.congr_of_eventuallyEq hfun').congr_deriv ?_
  rw [hτt₀, priorCum3_residual_expand hπm hπi hπ hπpos hL₀m hL₀ hR _ _
    (hL.sub (bdd_dirLoss hR _))]
  have e1 : dotProduct (regCoeff μ π L₀ R M t₀) (fun i ↦ -priorCum3 μ π
      (affLoss L₀ R (Function.invFun (meanMap μ π L₀ R t₀) M)) (R i) L₀
      (fun x ↦ L₀ x - dirLoss R (regCoeff μ π L₀ R M t₀) x) t₀) =
      -∑ i, regCoeff μ π L₀ R M t₀ i * priorCum3 μ π
        (affLoss L₀ R (Function.invFun (meanMap μ π L₀ R t₀) M)) (R i) L₀
        (fun x ↦ L₀ x - dirLoss R (regCoeff μ π L₀ R M t₀) x) t₀ := by
    simp only [dotProduct, mul_neg, Finset.sum_neg_distrib]
  have e2 : dotProduct (regCoeff μ π L₀ R M t₀) ((Matrix.of fun i j ↦ -priorCum3 μ π
      (affLoss L₀ R (Function.invFun (meanMap μ π L₀ R t₀) M)) (R i) (R j)
      (fun x ↦ L₀ x - dirLoss R (regCoeff μ π L₀ R M t₀) x) t₀).mulVec
        (regCoeff μ π L₀ R M t₀)) =
      -∑ i, regCoeff μ π L₀ R M t₀ i * ∑ j, regCoeff μ π L₀ R M t₀ j * priorCum3 μ π
        (affLoss L₀ R (Function.invFun (meanMap μ π L₀ R t₀) M)) (R i) (R j)
        (fun x ↦ L₀ x - dirLoss R (regCoeff μ π L₀ R M t₀) x) t₀ := by
    simp only [dotProduct, Matrix.mulVec, Matrix.of_apply, neg_mul, Finset.sum_neg_distrib,
      mul_neg]
    congr 1
    refine Finset.sum_congr rfl fun i _ ↦ ?_
    congr 1
    exact Finset.sum_congr rfl fun j _ ↦ by ring
  rw [e1, e2]
  ring

/-- **The curvature of the loss surface in the temperature is the residual third cumulant**:
`∂_t² h(t, M) = κ₃(H, H, H)` with `H = L₀ − b·R` the regression residual. -/
theorem hasDerivAt_deriv_lossSurface {t₀ : ℝ} (ht₀ : 0 < t₀) {M : ι → ℝ}
    (hM : M ∈ interior (momentBody μ π R)) :
    HasDerivAt (deriv (fun t ↦ obsMean μ π L₀ L₀ R t M))
      (priorCum3 μ π (affLoss L₀ R (Function.invFun (meanMap μ π L₀ R t₀) M))
        (fun x ↦ L₀ x - dirLoss R (regCoeff μ π L₀ R M t₀) x)
        (fun x ↦ L₀ x - dirLoss R (regCoeff μ π L₀ R M t₀) x)
        (fun x ↦ L₀ x - dirLoss R (regCoeff μ π L₀ R M t₀) x) t₀) t₀ := by
  have hfun : deriv (fun t ↦ obsMean μ π L₀ L₀ R t M) =ᶠ[𝓝 t₀] fun t ↦
      -priorCov μ π (affLoss L₀ R (Function.invFun (meanMap μ π L₀ R t) M))
        (fun x ↦ L₀ x - dirLoss R (regCoeff μ π L₀ R M t) x)
        (fun x ↦ L₀ x - dirLoss R (regCoeff μ π L₀ R M t) x) t := by
    filter_upwards [lt_mem_nhds ht₀] with t ht
    exact (hasDerivAt_lossSurface hπm hπi hπ hπpos hL₀m hL₀ hR hnd ht hM
      (featCov_mulVec_regCoeff hπm hπi hπ hπpos hL₀m hL₀ hR hnd ht M)).deriv
  have h := (hasDerivAt_residual_var hπm hπi hπ hπpos hL₀m hL₀ hR hnd ht₀ hM).neg
  rw [neg_neg] at h
  exact h.congr_of_eventuallyEq hfun

end Curvature

end Laplace.Multi
