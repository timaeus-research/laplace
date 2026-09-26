/-
Copyright (c) 2026 Timaeus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Timaeus
-/
import Laplace.Multi.ResponseGeometry
import Laplace.Multi.CurveLength
import Laplace.Multi.TangentPythagoras

/-!
# The reconstruction as a retraction of the data manifold

The data manifold is the affine subspace of `L¹(ν)` of densities of fixed mass; the response map
`R(d) = [q_{m(d)}]`, `m(d) = ∫ S d dν`, sends it onto the family. Here `R` is packaged as a map on
`L¹(ν)` and shown to be a differentiable retraction:

* `momentL1`: the moment functional `d ↦ ∫ S d dν` as a continuous linear map `L¹(ν) → (J → ℝ)`;
* `visibleL1`: its projection onto the direction subspace `𝕍`, the **visible part** of a data
  direction;
* `dataRecon`: `R(d) = [q_{m(d)}]`;
* `momentL1_dataRecon` / `dataRecon_dataRecon`: `m ∘ R = m` and `R ∘ R = R`;
* `hasFDerivWithinAt_dataRecon`: on the fixed-mass affine subspace,
  `DR_d[h] = Dp_{m(d)}(π ∫ S h dν)`: the pushforward of a data tangent is the reconstruction
  derivative of its visible part;
* `dataReconDeriv_comp_self`, `dataReconDeriv_eq_zero_iff`, `momentL1_sub_dataReconDeriv`:
  `DR ∘ DR = DR`, `ker DR = {∫ S h dν = 0}` (the invisible data directions), and every zero-mass
  data direction splits as a visible tangent score plus an invisible remainder;
* `hasDerivAt_dataRecon_path`: the chain rule along any differentiable data path.
-/

open MeasureTheory Filter Topology Set ProbabilityTheory

namespace Laplace.Multi

variable {X : Type*} [MeasurableSpace X] [Nonempty X] {J : Type*} [Fintype J] [Nonempty J]
  {S : J → X → ℝ} (hS : ∀ j, Bdd (S j)) (ν : Measure X) [IsProbabilityMeasure ν]
include hS

/-- The direction subspace. -/
local notation "𝕍" => dirSpan ν (fun _ ↦ (1 : ℝ)) S

/-- The natural coordinate of a response. -/
local notation "θr" => responseTheta measurable_const (integrable_const 1) (fun _ ↦ one_pos)
  (one_integral_pos ν) hS

/-- The featureless response. -/
local notation "m₀" => meanMap ν (fun _ ↦ (1 : ℝ)) (fun _ ↦ (0 : ℝ)) S 1 0

omit [Nonempty X] [Fintype J] [Nonempty J] [IsProbabilityMeasure ν] in
/-- A uniform bound on the features. -/
theorem exists_feature_bound [Finite J] : ∃ B : ℝ, 0 ≤ B ∧ ∀ j x, |S j x| ≤ B := by
  cases nonempty_fintype J
  choose Mj hMj using fun j ↦ (hS j).2
  refine ⟨∑ j, |Mj j|, Finset.sum_nonneg fun _ _ ↦ abs_nonneg _, fun j x ↦ ?_⟩
  exact (hMj j x).trans ((le_abs_self _).trans
    (Finset.single_le_sum (fun i _ ↦ abs_nonneg (Mj i)) (Finset.mem_univ j)))

omit [Nonempty X] [Fintype J] [Nonempty J] [IsProbabilityMeasure ν] in
/-- A feature times an `L¹` function is integrable. -/
theorem integrable_stat_mul_L1 (j : J) (d : X →₁[ν] ℝ) :
    Integrable (fun x ↦ S j x * d x) ν :=
  (L1.integrable_coeFn d).bdd_mul (hS j).1.aestronglyMeasurable
    (Eventually.of_forall fun x ↦ by rw [Real.norm_eq_abs]; exact (hS j).2.choose_spec x)

omit [Nonempty X] [Nonempty J] [IsProbabilityMeasure ν] in
/-- The moment functional `d ↦ ∫ S d dν` on `L¹(ν)`, as a linear map. -/
noncomputable def momentLin : (X →₁[ν] ℝ) →ₗ[ℝ] (J → ℝ) where
  toFun d := fun j ↦ ∫ x, S j x * d x ∂ν
  map_add' d e := by
    funext j
    change ∫ x, S j x * (d + e) x ∂ν = (∫ x, S j x * d x ∂ν) + ∫ x, S j x * e x ∂ν
    rw [← integral_add (integrable_stat_mul_L1 hS ν j d) (integrable_stat_mul_L1 hS ν j e)]
    refine integral_congr_ae ?_
    filter_upwards [Lp.coeFn_add d e] with x hx
    rw [hx, Pi.add_apply]
    ring
  map_smul' c d := by
    funext j
    change ∫ x, S j x * (c • d) x ∂ν = c * ∫ x, S j x * d x ∂ν
    rw [← integral_const_mul]
    refine integral_congr_ae ?_
    filter_upwards [Lp.coeFn_smul c d] with x hx
    rw [hx, Pi.smul_apply, smul_eq_mul]
    ring

omit [Nonempty X] [Nonempty J] [IsProbabilityMeasure ν] in
/-- The moment functional is bounded by the feature bound. -/
theorem exists_bound_momentLin : ∃ C : ℝ, ∀ d : X →₁[ν] ℝ, ‖momentLin hS ν d‖ ≤ C * ‖d‖ := by
  obtain ⟨B, hB0, hB⟩ := exists_feature_bound hS
  refine ⟨B, fun d ↦ ?_⟩
  refine (pi_norm_le_iff_of_nonneg (mul_nonneg hB0 (norm_nonneg d))).2 fun j ↦ ?_
  change ‖∫ x, S j x * d x ∂ν‖ ≤ B * ‖d‖
  rw [L1.norm_eq_integral_norm, ← integral_const_mul]
  refine norm_integral_le_of_norm_le ((L1.integrable_coeFn d).norm.const_mul B)
    (Eventually.of_forall fun x ↦ ?_)
  rw [norm_mul]
  exact mul_le_mul_of_nonneg_right (by rw [Real.norm_eq_abs]; exact hB j x) (norm_nonneg _)

omit [Nonempty X] [Nonempty J] [IsProbabilityMeasure ν] in
/-- The moment functional `d ↦ ∫ S d dν` as a continuous linear map `L¹(ν) → (J → ℝ)`. -/
noncomputable def momentL1 : (X →₁[ν] ℝ) →L[ℝ] (J → ℝ) :=
  (momentLin hS ν).mkContinuousOfExistsBound (exists_bound_momentLin hS ν)

omit [Nonempty X] [Nonempty J] [IsProbabilityMeasure ν] in
theorem momentL1_apply (d : X →₁[ν] ℝ) (j : J) : momentL1 hS ν d j = ∫ x, S j x * d x ∂ν :=
  rfl

omit [Nonempty X] [Nonempty J] [IsProbabilityMeasure ν] in
variable (S) in
/-- The projection onto the direction subspace, as a continuous linear map. -/
noncomputable def dirProjL : (J → ℝ) →L[ℝ] 𝕍 := LinearMap.toContinuousLinearMap (dirProj S ν)

omit [Nonempty X] [Nonempty J] hS [IsProbabilityMeasure ν] in
theorem dirProjL_of_mem {v : J → ℝ} (hv : v ∈ 𝕍) : (dirProjL S ν v : J → ℝ) = v := by
  have := dirProj_coe S ν ⟨v, hv⟩
  change (dirProj S ν v : J → ℝ) = v
  rw [this]

/-- **The visible part of a data direction**: `h ↦ π(∫ S h dν) ∈ 𝕍`. -/
noncomputable def visibleL1 : (X →₁[ν] ℝ) →L[ℝ] 𝕍 := (dirProjL S ν).comp (momentL1 hS ν)

omit [Nonempty X] [Nonempty J] [IsProbabilityMeasure ν] in
theorem visibleL1_apply (d : X →₁[ν] ℝ) : visibleL1 hS ν d = dirProjL S ν (momentL1 hS ν d) :=
  rfl

/-- **The reconstruction as a map on `L¹(ν)`**: `R(d) = [q_{m(d)}]`. -/
noncomputable def dataRecon (d : X →₁[ν] ℝ) : X →₁[ν] ℝ :=
  reconstructionL1 hS ν (momentL1 hS ν d)

/-- The moment map inverts the reconstruction: `m([q_M]) = M`. -/
theorem momentL1_reconstructionL1 {M : J → ℝ}
    (hrel : M ∈ intrinsicInterior ℝ (momentBody ν (fun _ ↦ (1 : ℝ)) S)) :
    momentL1 hS ν (reconstructionL1 hS ν M) = M := by
  funext j
  rw [momentL1_apply]
  have h1 : ∫ x, S j x * (reconstructionL1 hS ν M) x ∂ν =
      ∫ x, famDens S ν (θr M) x * S j x ∂ν := by
    refine integral_congr_ae ?_
    filter_upwards [Integrable.coeFn_toL1 (integrable_famDens hS ν (θr M))] with x hx
    unfold reconstructionL1
    rw [hx, mul_comm]
  rw [h1, ← integral_famDens_mul hS ν]
  exact congrFun (integral_stat_responseTheta hS ν hrel) j

/-- `m ∘ R = m`: the reconstruction preserves the response. -/
theorem momentL1_dataRecon {d : X →₁[ν] ℝ}
    (hrel : momentL1 hS ν d ∈ intrinsicInterior ℝ (momentBody ν (fun _ ↦ (1 : ℝ)) S)) :
    momentL1 hS ν (dataRecon hS ν d) = momentL1 hS ν d :=
  momentL1_reconstructionL1 hS ν hrel

/-- `R ∘ R = R`: the reconstruction is idempotent. -/
theorem dataRecon_dataRecon {d : X →₁[ν] ℝ}
    (hrel : momentL1 hS ν d ∈ intrinsicInterior ℝ (momentBody ν (fun _ ↦ (1 : ℝ)) S)) :
    dataRecon hS ν (dataRecon hS ν d) = dataRecon hS ν d := by
  unfold dataRecon
  rw [momentL1_reconstructionL1 hS ν hrel]

/-- The moment map inverts the reconstruction derivative: `m(Dp_M u) = u`. -/
theorem momentL1_reconstructionDeriv {M : J → ℝ}
    (hrel : M ∈ intrinsicInterior ℝ (momentBody ν (fun _ ↦ (1 : ℝ)) S)) (u : 𝕍) :
    momentL1 hS ν (reconstructionDeriv hS ν M u) = (u : J → ℝ) := by
  rw [← famDens_mul_responseScore_moment_eq hS ν hrel u]
  funext j
  rw [momentL1_apply, reconstructionDeriv_apply]
  refine integral_congr_ae ?_
  filter_upwards [Integrable.coeFn_toL1 (integrable_famDens_mul_responseScore hS ν (M := M) u)]
    with x hx
  rw [hx]

/-- The visible part of a reconstruction derivative is its direction: `π m(Dp_M u) = u`. -/
theorem visibleL1_reconstructionDeriv {M : J → ℝ}
    (hrel : M ∈ intrinsicInterior ℝ (momentBody ν (fun _ ↦ (1 : ℝ)) S)) (u : 𝕍) :
    visibleL1 hS ν (reconstructionDeriv hS ν M u) = u := by
  rw [visibleL1_apply, momentL1_reconstructionDeriv hS ν hrel u]
  exact Subtype.ext (dirProjL_of_mem ν u.2)

/-- **Zero-mass data directions have visible moments in `𝕍`**: if `∫ d = ∫ e` then
`∫ S d dν − ∫ S e dν ∈ 𝕍`. -/
theorem momentL1_sub_mem_dirSpan {d e : X →₁[ν] ℝ} (h : ∫ x, d x ∂ν = ∫ x, e x ∂ν) :
    momentL1 hS ν d - momentL1 hS ν e ∈ 𝕍 := by
  have hm₀ : m₀ ∈ momentBody ν (fun _ ↦ (1 : ℝ)) S :=
    intrinsicInterior_subset (featureless_mem_intrinsicInterior hS ν)
  have hde : Integrable (fun x ↦ d x - e x) ν :=
    (L1.integrable_coeFn d).sub (L1.integrable_coeFn e)
  have hfj : ∀ j, Integrable (fun x ↦ (d x - e x) * (S j x - m₀ j)) ν := fun j ↦ by
    obtain ⟨B, hB⟩ := (hS j).2
    have := hde.bdd_mul (c := B + |m₀ j|) (f := fun x ↦ S j x - m₀ j)
      ((hS j).1.sub measurable_const).aestronglyMeasurable
      (Eventually.of_forall fun x ↦ by
        rw [Real.norm_eq_abs]
        exact (abs_sub _ _).trans (add_le_add (hB x) le_rfl))
    exact this.congr (Eventually.of_forall fun x ↦ mul_comm _ _)
  -- the vector-valued integrand `x ↦ (d x − e x) • (S x − m₀)`
  obtain ⟨f, hf⟩ : ∃ f : X → J → ℝ, f = fun x ↦ (d x - e x) • (statPoint S x - m₀) := ⟨_, rfl⟩
  have hfi : Integrable f ν := by
    rw [hf]
    refine integrable_pi_iff.2 fun j ↦ ?_
    simpa [statPoint] using hfj j
  -- the integrand lies in `𝕍` almost everywhere
  have hmem : ∀ᵐ x ∂ν, f x ∈ 𝕍 := by
    filter_upwards [ae_statPoint_mem_essRange measurable_const (fun _ ↦ one_pos) hS] with x hx
    rw [hf]
    exact Submodule.smul_mem _ _ (sub_mem_dirSpan_of_mem_momentBody' hS ν hm₀
      (essRange_subset_momentBody S hx))
  -- hence so does its integral
  have hint : ∫ x, f x ∂ν ∈ 𝕍 := by
    have e1 : ∫ x, f x ∂ν = ∫ x, (𝕍).subtypeL (dirProjL S ν (f x)) ∂ν := by
      refine integral_congr_ae ?_
      filter_upwards [hmem] with x hx
      rw [Submodule.subtypeL_apply, dirProjL_of_mem ν hx]
    rw [e1, ContinuousLinearMap.integral_comp_comm _ ((dirProjL S ν).integrable_comp hfi),
      ContinuousLinearMap.integral_comp_comm _ hfi, Submodule.subtypeL_apply]
    exact Submodule.coe_mem _
  -- identify the moment difference with that integral
  have e2 : momentL1 hS ν d - momentL1 hS ν e = ∫ x, f x ∂ν := by
    funext j
    have hj := ContinuousLinearMap.integral_comp_comm (ContinuousLinearMap.proj (R := ℝ)
      (φ := fun _ : J ↦ ℝ) j) hfi
    simp only [ContinuousLinearMap.proj_apply] at hj
    rw [Pi.sub_apply, momentL1_apply, momentL1_apply, ← hj]
    have e3 : ∫ x, f x j ∂ν = ∫ x, (S j x * d x - S j x * e x) - m₀ j * (d x - e x) ∂ν := by
      refine integral_congr_ae (Eventually.of_forall fun x ↦ ?_)
      simp only [hf, Pi.smul_apply, Pi.sub_apply, statPoint, smul_eq_mul]
      ring
    have i1 : Integrable (fun x ↦ S j x * d x - S j x * e x) ν :=
      (integrable_stat_mul_L1 hS ν j d).sub (integrable_stat_mul_L1 hS ν j e)
    have i2 : Integrable (fun x ↦ m₀ j * (d x - e x)) ν := hde.const_mul _
    rw [e3, integral_sub i1 i2, integral_sub (integrable_stat_mul_L1 hS ν j d)
      (integrable_stat_mul_L1 hS ν j e), integral_const_mul,
      integral_sub (L1.integrable_coeFn d) (L1.integrable_coeFn e), h, sub_self, mul_zero, sub_zero]
  rw [e2]
  exact hint

/-- A zero-mass data direction has visible moment in `𝕍`. -/
theorem momentL1_mem_dirSpan {h : X →₁[ν] ℝ} (hh : ∫ x, h x ∂ν = 0) : momentL1 hS ν h ∈ 𝕍 := by
  have := momentL1_sub_mem_dirSpan hS ν (d := h) (e := 0)
    (by rw [hh, integral_congr_ae (Lp.coeFn_zero (E := ℝ) (p := 1) (μ := ν))]; simp)
  rwa [map_zero, sub_zero] at this

/-- **The reconstruction is a differentiable retraction of the data manifold.** On the affine
subspace of `L¹(ν)` of fixed mass, at a base point `d₀` with interior response `M = m(d₀)`, the
reconstruction `R(d) = [q_{m(d)}]` is Fréchet differentiable with derivative
`DR_{d₀}[h] = Dp_M(π ∫ S h dν) = [q_M ℓ_{M, π∫Sh}]`: the pushforward of a data tangent is the
reconstruction derivative of its visible part. -/
theorem hasFDerivWithinAt_dataRecon {d₀ : X →₁[ν] ℝ}
    (hrel : momentL1 hS ν d₀ ∈ intrinsicInterior ℝ (momentBody ν (fun _ ↦ (1 : ℝ)) S)) :
    HasFDerivWithinAt (dataRecon hS ν)
      ((reconstructionDeriv hS ν (momentL1 hS ν d₀)).comp (visibleL1 hS ν))
      {d | ∫ x, d x ∂ν = ∫ x, d₀ x ∂ν} d₀ := by
  have hg : HasFDerivAt (fun d ↦ visibleL1 hS ν d - visibleL1 hS ν d₀) (visibleL1 hS ν) d₀ :=
    (visibleL1 hS ν).hasFDerivAt.sub_const _
  have hf : HasFDerivAt (fun z : 𝕍 ↦ reconstructionL1 hS ν (momentL1 hS ν d₀ + z))
      (reconstructionDeriv hS ν (momentL1 hS ν d₀))
      (visibleL1 hS ν d₀ - visibleL1 hS ν d₀) := by
    rw [sub_self]
    exact hasFDerivAt_reconstructionL1 hS ν hrel
  have hc := hf.comp d₀ hg
  refine hc.hasFDerivWithinAt.congr (fun d hd ↦ ?_) ?_
  · simp only [Function.comp_def, dataRecon]
    congr 1
    have hm := momentL1_sub_mem_dirSpan hS ν (hd : ∫ x, d x ∂ν = ∫ x, d₀ x ∂ν)
    rw [visibleL1_apply, visibleL1_apply, ← map_sub, dirProjL_of_mem ν hm]
    abel
  · simp only [Function.comp_def, dataRecon, sub_self, Submodule.coe_zero, add_zero]

/-- **The differential is idempotent**: `DR ∘ DR = DR` at every interior response. -/
theorem dataReconDeriv_comp_self {M : J → ℝ}
    (hrel : M ∈ intrinsicInterior ℝ (momentBody ν (fun _ ↦ (1 : ℝ)) S)) :
    ((reconstructionDeriv hS ν M).comp (visibleL1 hS ν)).comp
        ((reconstructionDeriv hS ν M).comp (visibleL1 hS ν)) =
      (reconstructionDeriv hS ν M).comp (visibleL1 hS ν) := by
  ext h
  simp only [ContinuousLinearMap.comp_apply, visibleL1_reconstructionDeriv hS ν hrel]
  rfl

/-- **The kernel of the differential is the invisible data directions**: for a zero-mass
direction `h`, `DR[h] = 0 ↔ ∫ S h dν = 0`. -/
theorem dataReconDeriv_eq_zero_iff {M : J → ℝ}
    (hrel : M ∈ intrinsicInterior ℝ (momentBody ν (fun _ ↦ (1 : ℝ)) S)) {h : X →₁[ν] ℝ}
    (hh : ∫ x, h x ∂ν = 0) :
    ((reconstructionDeriv hS ν M).comp (visibleL1 hS ν)) h = 0 ↔ momentL1 hS ν h = 0 := by
  have hv : (visibleL1 hS ν h : J → ℝ) = momentL1 hS ν h :=
    dirProjL_of_mem ν (momentL1_mem_dirSpan hS ν hh)
  constructor
  · intro h0
    have := congrArg (momentL1 hS ν) h0
    rw [ContinuousLinearMap.comp_apply, momentL1_reconstructionDeriv hS ν hrel, map_zero, hv]
      at this
    exact this
  · intro h0
    have : visibleL1 hS ν h = 0 := Subtype.ext (by rw [hv, h0]; rfl)
    rw [ContinuousLinearMap.comp_apply, this, map_zero]

/-- **Visible/invisible splitting of a data direction**: for a zero-mass direction `h`, the
remainder `h − DR[h]` has zero feature moments — `h` is a tangent score `[q_M ℓ_{M,π∫Sh}]` plus an
invisible direction. -/
theorem momentL1_sub_dataReconDeriv {M : J → ℝ}
    (hrel : M ∈ intrinsicInterior ℝ (momentBody ν (fun _ ↦ (1 : ℝ)) S)) {h : X →₁[ν] ℝ}
    (hh : ∫ x, h x ∂ν = 0) :
    momentL1 hS ν (h - ((reconstructionDeriv hS ν M).comp (visibleL1 hS ν)) h) = 0 := by
  rw [map_sub, ContinuousLinearMap.comp_apply, momentL1_reconstructionDeriv hS ν hrel,
    visibleL1_apply, dirProjL_of_mem ν (momentL1_mem_dirSpan hS ν hh), sub_self]

/-- **The `L¹` speed of the pushed-forward data direction is at most its visible Fisher length.** -/
theorem norm_dataReconDeriv_le (M : J → ℝ) (h : X →₁[ν] ℝ) :
    ‖((reconstructionDeriv hS ν M).comp (visibleL1 hS ν)) h‖ ≤
      √(fisherForm hS ν M (visibleL1 hS ν h) (visibleL1 hS ν h)) :=
  norm_reconstructionDeriv_apply_le hS ν M _

/-- **The chain rule along data paths**: for a differentiable path of `L¹` densities of constant
mass through interior responses, `d/dt [q_{m(d_t)}] = [q_{M_t} ℓ_{M_t, π∫S ḋ_t}]`. -/
theorem hasDerivAt_dataRecon_path {d : ℝ → X →₁[ν] ℝ} {d' : ℝ → X →₁[ν] ℝ} {t : ℝ}
    (hd : HasDerivAt d (d' t) t) (hmass : ∀ s, ∫ x, d s x ∂ν = ∫ x, d t x ∂ν)
    (hrel : momentL1 hS ν (d t) ∈ intrinsicInterior ℝ (momentBody ν (fun _ ↦ (1 : ℝ)) S)) :
    HasDerivAt (fun s ↦ dataRecon hS ν (d s))
      (reconstructionDeriv hS ν (momentL1 hS ν (d t)) (visibleL1 hS ν (d' t))) t := by
  have h1 := HasFDerivWithinAt.comp_hasDerivWithinAt (s := univ) (l := dataRecon hS ν)
    (f := d) (x := t) (hasFDerivWithinAt_dataRecon hS ν hrel) hd.hasDerivWithinAt
    (fun s _ ↦ hmass s)
  rw [hasDerivWithinAt_univ] at h1
  exact h1

end Laplace.Multi
