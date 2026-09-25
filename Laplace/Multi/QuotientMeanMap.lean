/-
Copyright (c) 2026 Timaeus Research. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniel Murfet
-/
import Mathlib
import Laplace.Multi.DataQuotient
import Laplace.Multi.MeanMapInjective

/-!
# The mean map on the quotient by the invisible directions

The invisible subspace `K = {v | R_v is a.e. constant}` of the data tangent space is a linear
subspace (`invisibleSubmodule`), and the mean map `M(a) = ⟨R⟩_a` of the affine family descends to
the quotient by it (Astra round 28 item 1):

* **Invariance**: `M(a + k) = M(a)` for `k ∈ K`  (`meanMap_add_of_invisible`).
* **Annihilator**: `⟨M(a) − M(b), k⟩ = 0` for `k ∈ K`  (`dot_meanMap_sub_of_invisible`).
* **Identifiability**: `M(a) = M(b) ↔ b − a ∈ K`  (`meanMap_eq_iff_invisible`).
* **Strict monotonicity**: `⟨M(b) − M(a), b − a⟩ = −t ∫₀¹ Var_{a+s(b−a)}(R_{b−a}) ds`, which is
  `< 0` unless `b − a ∈ K`  (`dot_meanMap_sub_eq_integral`, `dot_meanMap_sub_neg`).

So the posterior map `a ↦ P_a` and the response coordinates `a ↦ M(a)` have exactly the same
fibres, the cosets of `K`, and the response coordinates are strictly monotone across every coset.
-/

open MeasureTheory Filter Topology Set

namespace Laplace.Multi

variable {X : Type*} [MeasurableSpace X] {μ : Measure X} {ι : Type*} [Fintype ι]

/-! ### The invisible subspace -/

/-- The invisible data directions: those whose loss contrast is a.e. constant. -/
def invisibleSet (μ : Measure X) (R : ι → X → ℝ) : Set (ι → ℝ) :=
  {v | ∃ c : ℝ, ∀ᵐ x ∂μ, dirLoss R v x = c}

omit [MeasurableSpace X] in
theorem dirLoss_zero (R : ι → X → ℝ) (x : X) : dirLoss R (0 : ι → ℝ) x = 0 := by
  simp [dirLoss]

omit [MeasurableSpace X] in
set_option linter.unusedFintypeInType false in
/-- The derivative of the affine line `s ↦ a + s v` (the `Fintype` instance carries the norm). -/
theorem hasDerivAt_affineLine (a v : ι → ℝ) (s : ℝ) :
    HasDerivAt (fun s : ℝ ↦ a + s • v) v s := by
  simpa using ((hasDerivAt_id (s : ℝ)).smul_const v).const_add a

/-- The invisible directions form a linear subspace. -/
def invisibleSubmodule (μ : Measure X) (R : ι → X → ℝ) : Submodule ℝ (ι → ℝ) where
  carrier := invisibleSet μ R
  zero_mem' := ⟨0, Filter.Eventually.of_forall fun x ↦ dirLoss_zero R x⟩
  add_mem' := by
    rintro v w ⟨c, hc⟩ ⟨d, hd⟩
    refine ⟨c + d, ?_⟩
    filter_upwards [hc, hd] with x hx hy
    rw [dirLoss_add]
    simp only [hx, hy]
  smul_mem' := by
    rintro r v ⟨c, hc⟩
    refine ⟨r * c, ?_⟩
    filter_upwards [hc] with x hx
    rw [dirLoss_smul]
    simp only [hx]

theorem mem_invisibleSubmodule {R : ι → X → ℝ} {v : ι → ℝ} :
    v ∈ invisibleSubmodule μ R ↔ ∃ c : ℝ, ∀ᵐ x ∂μ, dirLoss R v x = c := Iff.rfl

/-! ### Posterior expectations under a.e. shifts of the loss -/

theorem priorExp_congr_loss_ae (π φ : X → ℝ) {L L' : X → ℝ} (h : ∀ᵐ x ∂μ, L x = L' x) (t : ℝ) :
    priorExp μ π L φ t = priorExp μ π L' φ t := by
  unfold priorExp priorZ
  congr 1
  · exact integral_congr_ae (h.mono fun x hx ↦ by dsimp only; rw [hx])
  · exact integral_congr_ae (h.mono fun x hx ↦ by dsimp only; rw [hx])

theorem priorExp_const_add' (π L φ : X → ℝ) (c u : ℝ) :
    priorExp μ π (fun x ↦ c + L x) φ u = priorExp μ π L φ u := by
  unfold priorExp priorZ
  have e1 : (∫ x, φ x * Real.exp (-(u * (c + L x))) * π x ∂μ) =
      Real.exp (-(u * c)) * ∫ x, φ x * Real.exp (-(u * L x)) * π x ∂μ := by
    rw [← integral_const_mul]
    refine integral_congr_ae (Filter.Eventually.of_forall fun x ↦ ?_)
    beta_reduce
    rw [show -(u * (c + L x)) = -(u * c) + -(u * L x) by ring, Real.exp_add]
    ring
  have e2 : (∫ x, Real.exp (-(u * (c + L x))) * π x ∂μ) =
      Real.exp (-(u * c)) * ∫ x, Real.exp (-(u * L x)) * π x ∂μ := by
    rw [← integral_const_mul]
    refine integral_congr_ae (Filter.Eventually.of_forall fun x ↦ ?_)
    beta_reduce
    rw [show -(u * (c + L x)) = -(u * c) + -(u * L x) by ring, Real.exp_add]
    ring
  rw [e1, e2, mul_div_mul_left _ _ (Real.exp_pos _).ne']

section Affine

variable [Nonempty X] {π L₀ : X → ℝ} (hπm : Measurable π) (hπi : Integrable π μ)
  (hπ : ∀ x, 0 < π x) (hπpos : 0 < ∫ x, π x ∂μ) (hL₀m : Measurable L₀) {M₀ : ℝ}
  (hL₀ : ∀ x, |L₀ x| ≤ M₀) {R : ι → X → ℝ} (hR : ∀ i, Bdd (R i)) {t : ℝ}
include hπm hπi hπ hπpos hL₀m hL₀ hR

omit [Nonempty X] hπm hπi hπ hπpos hL₀m hL₀ hR in
/-- **Invariance**: the posterior does not see invisible directions. -/
theorem priorExp_affLoss_add_of_invisible (a : ι → ℝ) {k : ι → ℝ} (hk : k ∈ invisibleSet μ R)
    (φ : X → ℝ) (t : ℝ) :
    priorExp μ π (affLoss L₀ R (a + k)) φ t = priorExp μ π (affLoss L₀ R a) φ t := by
  obtain ⟨c, hc⟩ := hk
  have hL : ∀ᵐ x ∂μ, affLoss L₀ R (a + k) x = c + affLoss L₀ R a x := by
    filter_upwards [hc] with x hx
    simp only [affLoss, dirLoss, Pi.add_apply, add_mul, Finset.sum_add_distrib] at hx ⊢
    linarith
  rw [priorExp_congr_loss_ae π φ hL, priorExp_const_add']

omit [Nonempty X] hπm hπi hπ hπpos hL₀m hL₀ hR in
theorem meanMap_add_of_invisible (a : ι → ℝ) {k : ι → ℝ} (hk : k ∈ invisibleSet μ R) :
    meanMap μ π L₀ R t (a + k) = meanMap μ π L₀ R t a := by
  funext i
  exact priorExp_affLoss_add_of_invisible a hk (R i) t

omit [Nonempty X] in
/-- **Annihilator**: an invisible direction pairs to the same constant with every response. -/
theorem sum_mul_meanMap_of_invisible (a : ι → ℝ) {k : ι → ℝ} {c : ℝ}
    (hk : ∀ᵐ x ∂μ, dirLoss R k x = c) :
    ∑ i, k i * meanMap μ π L₀ R t a i = c := by
  have hν : Integrable (baseWeight π (affLoss L₀ R a) t) μ :=
    (tiltData_aff hπm hπi (fun x ↦ (hπ x).le) hπpos hL₀m hL₀ hR a a t).choose_spec.ν_int
  have h := priorExp_dirLoss hν hR k
  unfold meanMap
  rw [← h, priorExp_congr_ae' π _ hk, priorExp_const_fun (affZ_pos hπm hπi hπ hπpos hL₀m hL₀ hR
    (t := t) a).ne']

omit [Nonempty X] in
theorem dot_meanMap_sub_of_invisible (a b : ι → ℝ) {k : ι → ℝ} (hk : k ∈ invisibleSet μ R) :
    ∑ i, k i * (meanMap μ π L₀ R t a i - meanMap μ π L₀ R t b i) = 0 := by
  obtain ⟨c, hc⟩ := hk
  simp only [mul_sub, Finset.sum_sub_distrib]
  rw [sum_mul_meanMap_of_invisible hπm hπi hπ hπpos hL₀m hL₀ hR a hc,
    sum_mul_meanMap_of_invisible hπm hπi hπ hπpos hL₀m hL₀ hR b hc, sub_self]

/-- **Identifiability in response coordinates**: `M(a) = M(b)` iff `b − a` is invisible. -/
theorem meanMap_eq_iff_invisible (ht : 0 < t) (a b : ι → ℝ) :
    meanMap μ π L₀ R t a = meanMap μ π L₀ R t b ↔ b - a ∈ invisibleSet μ R := by
  constructor
  · intro hab
    by_contra hv
    have hnd : ¬ ∃ c : ℝ, ∀ᵐ x ∂μ, π x ≠ 0 → dirLoss R (b - a) x = c := fun ⟨c, hc⟩ ↦
      hv ⟨c, hc.mono fun x hx ↦ hx (hπ x).ne'⟩
    obtain ⟨M, h⟩ := tiltData_aff hπm hπi (fun x ↦ (hπ x).le) hπpos hL₀m hL₀ hR a (b - a) t
    obtain ⟨M', h'⟩ := tiltData_aff hπm hπi (fun x ↦ (hπ x).le) hπpos hL₀m hL₀ hR b (b - a) t
    have hlt := h.mixExp_strictAnti ht hnd zero_lt_one
    have e0 : mixExp μ π (affLoss L₀ R a) (dirLoss R (b - a)) (dirLoss R (b - a)) t 0 =
        priorExp μ π (affLoss L₀ R a) (dirLoss R (b - a)) t := by
      unfold mixExp
      rw [show pathLoss (affLoss L₀ R a) (dirLoss R (b - a)) 0 = affLoss L₀ R a from
        funext fun x ↦ by simp [pathLoss]]
    have e1 : mixExp μ π (affLoss L₀ R a) (dirLoss R (b - a)) (dirLoss R (b - a)) t 1 =
        priorExp μ π (affLoss L₀ R b) (dirLoss R (b - a)) t := by
      unfold mixExp
      rw [← affLoss_add_smul, one_smul, add_sub_cancel]
    simp only at hlt
    rw [e0, e1, priorExp_dirLoss h.ν_int hR, priorExp_dirLoss h'.ν_int hR] at hlt
    have hm : ∀ i, priorExp μ π (affLoss L₀ R a) (R i) t =
        priorExp μ π (affLoss L₀ R b) (R i) t := fun i ↦ by
      simpa [meanMap] using congrFun hab i
    simp only [hm] at hlt
    exact lt_irrefl _ hlt
  · intro hk
    have := meanMap_add_of_invisible (π := π) (L₀ := L₀) (t := t) a hk
    rw [add_sub_cancel] at this
    exact this.symm

/-- **Strict monotonicity of the mean map**:
`⟨M(b) − M(a), b − a⟩ = −t ∫₀¹ Var_{a+s(b−a)}(R_{b−a}) ds`. -/
theorem dot_meanMap_sub_eq_integral (ht : 0 < t) (a b : ι → ℝ) :
    ∑ i, (b i - a i) * (meanMap μ π L₀ R t b i - meanMap μ π L₀ R t a i) =
      -t * ∫ s in (0 : ℝ)..1, priorCov μ π (affLoss L₀ R (a + s • (b - a))) (dirLoss R (b - a))
        (dirLoss R (b - a)) t := by
  set v := b - a with hv
  obtain ⟨hvm, Mv, hvb⟩ := bdd_dirLoss hR v
  have hg : ∀ s, HasDerivAt (fun s ↦ priorExp μ π (affLoss L₀ R (a + s • v)) (dirLoss R v) t)
      (obsMapDeriv μ π L₀ (dirLoss R v) R t (a + s • v) v) s := fun s ↦ by
    have h := (hasFDerivAt_obsMap hπm hπi hπ hπpos hL₀m hL₀ hR hvm hvb ht
      (a + s • v)).comp_hasDerivAt s (hasDerivAt_affineLine a v s)
    exact h
  have hlc : Continuous (fun s : ℝ ↦ a + s • v) :=
    continuous_const.add ((continuous_id : Continuous fun s : ℝ ↦ s).smul
      (continuous_const : Continuous fun _ : ℝ ↦ v))
  have hcont : Continuous (fun s ↦ obsMapDeriv μ π L₀ (dirLoss R v) R t (a + s • v) v) :=
    ((continuous_obsMapDeriv hπm hπi hπ hπpos hL₀m hL₀ hR hvm hvb ht).comp hlc).clm_apply
      continuous_const
  have hftc := intervalIntegral.integral_eq_sub_of_hasDerivAt (fun s _ ↦ hg s)
    (hcont.intervalIntegrable (μ := volume) 0 1)
  have hint : (∫ s in (0 : ℝ)..1, obsMapDeriv μ π L₀ (dirLoss R v) R t (a + s • v) v) =
      -t * ∫ s in (0 : ℝ)..1, priorCov μ π (affLoss L₀ R (a + s • v)) (dirLoss R v)
        (dirLoss R v) t := by
    rw [← intervalIntegral.integral_const_mul]
    exact intervalIntegral.integral_congr fun s _ ↦
      obsMapDeriv_apply hπm hπi hπ hπpos hL₀m hL₀ hR hvm hvb ht (a + s • v) v
  rw [← hint, hftc]
  simp only [one_smul, zero_smul, add_zero, hv, add_sub_cancel]
  have hνa : Integrable (baseWeight π (affLoss L₀ R a) t) μ :=
    (tiltData_aff hπm hπi (fun x ↦ (hπ x).le) hπpos hL₀m hL₀ hR a a t).choose_spec.ν_int
  have hνb : Integrable (baseWeight π (affLoss L₀ R b) t) μ :=
    (tiltData_aff hπm hπi (fun x ↦ (hπ x).le) hπpos hL₀m hL₀ hR b b t).choose_spec.ν_int
  rw [priorExp_dirLoss hνb hR, priorExp_dirLoss hνa hR]
  unfold meanMap
  simp only [mul_sub, Finset.sum_sub_distrib, Pi.sub_apply]

/-- Posterior variances are nonnegative. -/
theorem priorCov_self_nonneg' (a : ι → ℝ) {φ : X → ℝ} (hφ : Bdd φ) :
    0 ≤ priorCov μ π (affLoss L₀ R a) φ φ t := by
  obtain ⟨_, h⟩ := tiltData_aff hπm hπi (fun x ↦ (hπ x).le) hπpos hL₀m hL₀ hR a a t
  have := h.tiltCov_self_nonneg hφ t 0
  rwa [← priorCov_eq_tiltCov_zero] at this

/-- **The mean map is strictly monotone across visible directions**:
`⟨M(b) − M(a), b − a⟩ < 0` unless `b − a` is invisible. -/
theorem dot_meanMap_sub_neg (ht : 0 < t) {a b : ι → ℝ} (hv : b - a ∉ invisibleSet μ R) :
    ∑ i, (b i - a i) * (meanMap μ π L₀ R t b i - meanMap μ π L₀ R t a i) < 0 := by
  rw [dot_meanMap_sub_eq_integral hπm hπi hπ hπpos hL₀m hL₀ hR ht a b]
  set v := b - a with hvdef
  obtain ⟨hvm, Mv, hvb⟩ := bdd_dirLoss hR v
  have hpos : ∀ s : ℝ,
      0 < priorCov μ π (affLoss L₀ R (a + s • v)) (dirLoss R v) (dirLoss R v) t := by
    intro s
    refine lt_of_le_of_ne (priorCov_self_nonneg' hπm hπi hπ hπpos hL₀m hL₀ hR _ ⟨hvm, Mv, hvb⟩)
      fun h0 ↦ hv ?_
    have := (responseForm_self_eq_zero_iff hπm hπi hπ hπpos hL₀m hL₀ hR ht (a + s • v) v).mp
      (by unfold responseForm; rw [← h0, mul_zero])
    exact this
  have hlc : Continuous (fun s : ℝ ↦ a + s • v) :=
    continuous_const.add ((continuous_id : Continuous fun s : ℝ ↦ s).smul
      (continuous_const : Continuous fun _ : ℝ ↦ v))
  have hcont : Continuous
      (fun s : ℝ ↦ priorCov μ π (affLoss L₀ R (a + s • v)) (dirLoss R v) (dirLoss R v) t) := by
    unfold priorCov
    exact ((continuous_obsMap hπm hπi hπ hπpos hL₀m hL₀ hR (φ := fun x ↦ dirLoss R v x *
      dirLoss R v x) (hvm.mul hvm) (Mφ := Mv * Mv) (fun x ↦ by
        rw [abs_mul]
        exact mul_le_mul (hvb x) (hvb x) (abs_nonneg _) (le_trans (abs_nonneg _) (hvb x))) ht).comp
      hlc).sub (((continuous_obsMap hπm hπi hπ hπpos hL₀m hL₀ hR hvm hvb ht).comp hlc).mul
      ((continuous_obsMap hπm hπi hπ hπpos hL₀m hL₀ hR hvm hvb ht).comp hlc))
  have hI : 0 < ∫ s in (0 : ℝ)..1, priorCov μ π (affLoss L₀ R (a + s • v)) (dirLoss R v)
      (dirLoss R v) t :=
    intervalIntegral.intervalIntegral_pos_of_pos_on (hcont.intervalIntegrable (μ := volume) 0 1)
      (fun s _ ↦ hpos s) one_pos
  have : 0 < t * ∫ s in (0 : ℝ)..1, priorCov μ π (affLoss L₀ R (a + s • v)) (dirLoss R v)
      (dirLoss R v) t := mul_pos ht hI
  linarith

end Affine

end Laplace.Multi
