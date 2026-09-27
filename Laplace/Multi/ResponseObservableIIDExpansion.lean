/-
Copyright (c) 2026 Timaeus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Timaeus
-/
import Laplace.Multi.ResponseObservableSamplingGeometry
import Laplace.Multi.SmoothChart

/-!
# The observable delta method: bias of a posterior expectation under sampling

For a bounded observable `F` the posterior expectation in mean coordinates is
`f_F(m₀ + z) = E_{θ(m₀+z)} F` (`obsChart`). Its second-order structure around an interior mean:

* **the Hessian is the second response** (`fderiv_fderiv_obsChart_zero`):
  `D²f_F(m₀)[e, e] = E_{θ₀}[(F − E F) r_{V_e V_e}]`, `V_e = A⁻¹e`, with `r` the score residual —
  the observable counterpart of the m-connection curvature of the inverse chart;
* **the cubic expansion** (`exists_obsChart_cubic_remainder`): on a ball inside the chart domain,
  `|f_F(m₀+z) − f_F(m₀) − ⟨u_F, z⟩ − ½ H_F(z)| ≤ K ‖z‖³` with `u_F` the regression direction and
  `H_F(z) = secondResponse F θ₀ (A⁻¹z) (A⁻¹z)` (`obsHessForm`);
* **the localised observable bias on any centred displacement law** (`obsBias_hessian`):
  `|∫_{‖z‖≤δ} (f_F(m₀+z) − f_F(m₀)) dμ − ½ ∫ H_F dμ| ≤ (‖u_F‖/δ² + K + ½ C_H/δ) M₃`;
* **the i.i.d. observable bias** (`iid_obsBias_hessian`): for `n` i.i.d. samples from a data law
  `D` with interior mean `m₀ = m(θ₀)` (not necessarily the model law),
  `E[f̂_{F,loc}] − f_F(m₀) = (1/2n) hessContraction + O(n^{-3/2})`,
  `hessContraction = ∑_{ab} Cov_D(S_a,S_b) H_F(A⁻¹pe_a, A⁻¹pe_b) = tr(Σ_D D²f_F(m₀))`.

The sign is worth stressing: the observable bias is `+½` the Hessian contraction; the outer
observable's own curvature enters, not only the connection bias of the structural coordinate.
-/

open MeasureTheory ProbabilityTheory Filter Topology Set

namespace Laplace.Multi

section Chart

variable {X : Type*} [MeasurableSpace X] [Nonempty X] {J : Type*} [Fintype J] [Nonempty J]
  {S : J → X → ℝ} (hS : ∀ j, Bdd (S j)) (ν : Measure X) [IsProbabilityMeasure ν]
include hS

/-- The direction space. -/
local notation "𝕍" => dirSpan ν (fun _ ↦ (1 : ℝ)) S

/-- The reconstructed family. -/
local notation "Pfam" => familyMeasure ν (fun _ ↦ (1 : ℝ)) (fun _ ↦ (0 : ℝ)) S 1

/-- The chart derivative equivalence. -/
local notation "CDE" => chartDerivEquiv measurable_const (integrable_const 1) (fun _ ↦ one_pos)
  (one_integral_pos ν) hS

/-- The mean map. -/
local notation "mean" => meanMap ν (fun _ ↦ (1 : ℝ)) (fun _ ↦ (0 : ℝ)) S 1

/-- The natural coordinate of a response. -/
local notation "θr" => responseTheta measurable_const (integrable_const 1) (fun _ ↦ one_pos)
  (one_integral_pos ν) hS

/-- The interior response domain. -/
local notation "Ω" => intrinsicInterior ℝ (momentBody ν (fun _ ↦ (1 : ℝ)) S)

/-- **The posterior expectation in mean coordinates**: `f_F(m₀ + z) = E_{θ(m(θ₀)+z)} F`. -/
noncomputable def obsChart (F : X → ℝ) (θ₀ : 𝕍) (z : 𝕍) : ℝ :=
  ∫ x, F x ∂Pfam (θr (mean (θ₀ : J → ℝ) + (z : J → ℝ)) : J → ℝ)

theorem obsChart_zero (F : X → ℝ) (θ₀ : 𝕍) :
    obsChart hS ν F θ₀ 0 = ∫ x, F x ∂Pfam (θ₀ : J → ℝ) := by
  simp only [obsChart, Submodule.coe_zero, add_zero, responseTheta_meanMap hS ν]

/-- The observable along a response line is the observable chart on the ray. -/
theorem lineObservable_eq_obsChart (F : X → ℝ) (θ₀ e : 𝕍) :
    lineObservable hS ν F θ₀ e = fun t ↦ obsChart hS ν F θ₀ (t • e) := by
  funext t
  simp only [lineObservable, obsChart, responseLine, Submodule.coe_smul]

/-- The observable chart is `C^∞` on the ball domain. -/
theorem contDiffOn_obsChart {F : X → ℝ} (hF : Bdd F) (θ₀ : 𝕍) :
    ContDiffOn ℝ (⊤ : ℕ∞) (obsChart hS ν F θ₀) (responseBallDomain S ν θ₀) := by
  have h1 := contDiff_integral_familyMeasure hS ν hF
  have h2 := contDiffOn_responseTheta_meanAdd hS ν θ₀
  have h3 : ContDiffOn ℝ (⊤ : ℕ∞) (fun z : 𝕍 ↦ (θr (mean (θ₀ : J → ℝ) + (z : J → ℝ)) : J → ℝ))
      (responseBallDomain S ν θ₀) :=
    ((𝕍).subtypeL.contDiff.comp_contDiffOn h2)
  exact h1.comp_contDiffOn h3

/-- **The Hessian quadratic form of the posterior expectation**:
`H_F(z) = secondResponse F θ₀ (A⁻¹z) (A⁻¹z) = E_{θ₀}[(F − E F) r_{A⁻¹z, A⁻¹z}]`. -/
noncomputable def obsHessForm (F : X → ℝ) (θ₀ : 𝕍) (z : 𝕍) : ℝ :=
  secondResponse hS ν F θ₀ ((CDE θ₀).symm z) ((CDE θ₀).symm z)

/-- The second response as a bilinear map on the direction space. -/
noncomputable def secondResponseBilin {F : X → ℝ} (hF : Bdd F) (θ₀ : 𝕍) :
    𝕍 →ₗ[ℝ] 𝕍 →ₗ[ℝ] ℝ :=
  LinearMap.mk₂ ℝ (secondResponse hS ν F θ₀) (secondResponse_add_left hS ν hF θ₀)
    (fun c u v ↦ by rw [smul_eq_mul]; exact secondResponse_smul_left hS ν F θ₀ c u v)
    (fun u v w ↦ by
      rw [secondResponse_symm hS ν, secondResponse_add_left hS ν hF,
        secondResponse_symm hS ν F θ₀ v, secondResponse_symm hS ν F θ₀ w])
    (fun c u v ↦ by
      rw [smul_eq_mul, secondResponse_symm hS ν, secondResponse_smul_left hS ν,
        secondResponse_symm hS ν])

theorem secondResponseBilin_apply {F : X → ℝ} (hF : Bdd F) (θ₀ u v : 𝕍) :
    secondResponseBilin hS ν hF θ₀ u v = secondResponse hS ν F θ₀ u v := rfl

/-- The Hessian as a continuous bilinear map `(e, h) ↦ secondResponse F θ₀ (A⁻¹e) (A⁻¹h)`. -/
noncomputable def obsHessCLM {F : X → ℝ} (hF : Bdd F) (θ₀ : 𝕍) : 𝕍 →L[ℝ] 𝕍 →L[ℝ] ℝ :=
  LinearMap.toContinuousLinearMap
    (((LinearMap.toContinuousLinearMap : (𝕍 →ₗ[ℝ] ℝ) ≃ₗ[ℝ] (𝕍 →L[ℝ] ℝ)).toLinearMap) ∘ₗ
      (((secondResponseBilin hS ν hF θ₀).compl₂ ((CDE θ₀).symm : 𝕍 →ₗ[ℝ] 𝕍)) ∘ₗ
        ((CDE θ₀).symm : 𝕍 →ₗ[ℝ] 𝕍)))

theorem obsHessCLM_apply {F : X → ℝ} (hF : Bdd F) (θ₀ e h : 𝕍) :
    obsHessCLM hS ν hF θ₀ e h = secondResponse hS ν F θ₀ ((CDE θ₀).symm e) ((CDE θ₀).symm h) := by
  simp only [obsHessCLM, LinearMap.coe_toContinuousLinearMap', LinearMap.comp_apply,
    LinearEquiv.coe_coe, LinearMap.compl₂_apply, secondResponseBilin_apply]
  rfl

theorem obsHessForm_eq_obsHessCLM {F : X → ℝ} (hF : Bdd F) (θ₀ z : 𝕍) :
    obsHessForm hS ν F θ₀ z = obsHessCLM hS ν hF θ₀ z z := rfl

theorem continuous_obsHessForm {F : X → ℝ} (hF : Bdd F) (θ₀ : 𝕍) :
    Continuous (obsHessForm hS ν F θ₀) := by
  have e : obsHessForm hS ν F θ₀ = fun z ↦ obsHessCLM hS ν hF θ₀ z z := by
    funext z
    exact obsHessForm_eq_obsHessCLM hS ν hF θ₀ z
  rw [e]
  exact Continuous.clm_apply (obsHessCLM hS ν hF θ₀).continuous continuous_id

/-- The Hessian form is bounded by `‖H_F‖ ‖z‖²`. -/
theorem abs_obsHessForm_le {F : X → ℝ} (hF : Bdd F) (θ₀ z : 𝕍) :
    |obsHessForm hS ν F θ₀ z| ≤ ‖obsHessCLM hS ν hF θ₀‖ * ‖z‖ ^ 2 := by
  rw [obsHessForm_eq_obsHessCLM hS ν hF, ← Real.norm_eq_abs, sq, ← mul_assoc]
  exact (obsHessCLM hS ν hF θ₀).le_opNorm₂ z z

/-- **The Hessian of the posterior expectation is the second response**:
`D²f_F(m₀)[e, e] = E_{θ₀}[(F − E F) r_{A⁻¹e, A⁻¹e}]`. -/
theorem fderiv_fderiv_obsChart_zero {F : X → ℝ} (hF : Bdd F) (θ₀ e : 𝕍) :
    fderiv ℝ (fderiv ℝ (obsChart hS ν F θ₀)) 0 e e = obsHessForm hS ν F θ₀ e := by
  have hU := isOpen_responseBallDomain hS ν θ₀
  have hC := contDiffOn_obsChart hS ν hF θ₀
  have hF1 : ContDiffOn ℝ 2 (fderiv ℝ (obsChart hS ν F θ₀)) (responseBallDomain S ν θ₀) :=
    (hC.of_le (by exact_mod_cast natCast_le_infty 3)).fderiv_of_isOpen hU (by norm_num)
  -- first derivative along the line
  have h1 : ∀ t ∈ responseLineDomain S ν θ₀ e,
      HasDerivAt (fun t : ℝ ↦ obsChart hS ν F θ₀ (t • e))
        (fderiv ℝ (obsChart hS ν F θ₀) (t • e) e) t := by
    intro t ht
    have hd : DifferentiableAt ℝ (obsChart hS ν F θ₀) (t • e) :=
      (hC.differentiableOn (by simp)).differentiableAt
        (hU.mem_nhds ((smul_mem_responseBallDomain_iff ν θ₀ e t).2 ht))
    have := hd.hasFDerivAt.comp_hasDerivAt t ((hasDerivAt_id t).smul_const e)
    simpa [Function.comp_def] using this
  have hvel : ∀ t ∈ responseLineDomain S ν θ₀ e,
      fderiv ℝ (obsChart hS ν F θ₀) (t • e) e =
        -lawCov (Pfam (responseLine hS ν θ₀ e t : J → ℝ)) F
          (dirLoss S (responseLineVel hS ν θ₀ e t : J → ℝ)) := fun t ht ↦ by
    have h := hasDerivAt_lineObservable hS ν hF θ₀ e ht
    rw [lineObservable_eq_obsChart hS ν] at h
    exact (h1 t ht).unique h
  -- second derivative along the line
  have h2 : HasDerivAt (fun t : ℝ ↦ fderiv ℝ (obsChart hS ν F θ₀) (t • e) e)
      (fderiv ℝ (fderiv ℝ (obsChart hS ν F θ₀)) 0 e e) 0 := by
    have hd : DifferentiableAt ℝ (fderiv ℝ (obsChart hS ν F θ₀)) ((0 : ℝ) • e) := by
      rw [zero_smul]
      exact (hF1.differentiableOn (by norm_num)).differentiableAt
        (hU.mem_nhds (zero_mem_responseBallDomain hS ν θ₀))
    have h := (hd.hasFDerivAt.comp_hasDerivAt (0 : ℝ) ((hasDerivAt_id (0 : ℝ)).smul_const e))
    have h' := h.clm_apply (hasDerivAt_const (0 : ℝ) e)
    simp only [Function.comp_def, id_eq, one_smul, zero_smul, map_zero, add_zero] at h'
    exact h'
  have h3 : HasDerivAt (fun t : ℝ ↦ fderiv ℝ (obsChart hS ν F θ₀) (t • e) e)
      (∫ x, (F x - ∫ y, F y ∂Pfam (responseLine hS ν θ₀ e 0 : J → ℝ)) *
        scoreResidual hS ν (responseLine hS ν θ₀ e 0) (responseLineVel hS ν θ₀ e 0)
          (responseLineVel hS ν θ₀ e 0) x ∂Pfam (responseLine hS ν θ₀ e 0 : J → ℝ)) 0 := by
    refine (hasDerivAt_deriv_lineObservable hS ν hF θ₀ e (zero_mem_responseLineDomain hS ν θ₀ e))
      |>.congr_of_eventuallyEq ?_
    filter_upwards [(isOpen_responseLineDomain hS ν θ₀ e).mem_nhds
      (zero_mem_responseLineDomain hS ν θ₀ e)] with t ht
    exact hvel t ht
  rw [h2.unique h3, responseLineVel_zero hS ν θ₀ e, responseLine_zero hS ν θ₀ e]
  rfl

/-- The first derivative of the observable chart at the base point is the regression pairing. -/
theorem fderiv_obsChart_zero {F : X → ℝ} (hF : Bdd F) (θ₀ e : 𝕍) :
    fderiv ℝ (obsChart hS ν F θ₀) 0 e = dotJ (regressionDir hS ν F θ₀ : J → ℝ) (e : J → ℝ) := by
  have hU := isOpen_responseBallDomain hS ν θ₀
  have hC := contDiffOn_obsChart hS ν hF θ₀
  have hd : DifferentiableAt ℝ (obsChart hS ν F θ₀) ((0 : ℝ) • e) := by
    rw [zero_smul]
    exact (hC.differentiableOn (by simp)).differentiableAt
      (hU.mem_nhds (zero_mem_responseBallDomain hS ν θ₀))
  have h1 : HasDerivAt (fun t : ℝ ↦ obsChart hS ν F θ₀ (t • e))
      (fderiv ℝ (obsChart hS ν F θ₀) 0 e) 0 := by
    have := hd.hasFDerivAt.comp_hasDerivAt (0 : ℝ) ((hasDerivAt_id (0 : ℝ)).smul_const e)
    simpa [Function.comp_def] using this
  have h2 := hasDerivAt_lineObservable_zero hS ν hF θ₀ e
  rw [lineObservable_eq_obsChart hS ν] at h2
  exact h1.unique h2

/-- **The cubic expansion of the posterior expectation in a mean displacement**: on a ball inside
the chart domain, `|f_F(m₀+z) − f_F(m₀) − ⟨u_F, z⟩ − ½ H_F(z)| ≤ K ‖z‖³`. -/
theorem exists_obsChart_cubic_remainder {F : X → ℝ} (hF : Bdd F) (θ₀ : 𝕍) :
    ∃ δ > 0, (∀ z : 𝕍, ‖z‖ ≤ δ → mean (θ₀ : J → ℝ) + (z : J → ℝ) ∈ Ω) ∧
      ∃ K, 0 ≤ K ∧ ∀ z : 𝕍, ‖z‖ ≤ δ →
        |obsChart hS ν F θ₀ z - obsChart hS ν F θ₀ 0 -
          dotJ (regressionDir hS ν F θ₀ : J → ℝ) (z : J → ℝ) -
          (1 / 2 : ℝ) * obsHessForm hS ν F θ₀ z| ≤ K * ‖z‖ ^ 3 := by
  obtain ⟨δ, hδ, hsub, K, hK, h⟩ := exists_cubic_remainder (isOpen_responseBallDomain hS ν θ₀)
    (zero_mem_responseBallDomain hS ν θ₀)
    ((contDiffOn_obsChart hS ν hF θ₀).of_le (by exact_mod_cast natCast_le_infty 3))
  refine ⟨δ, hδ, fun z hz ↦ ?_, K, hK, fun z hz ↦ ?_⟩
  · have hz' : z ∈ Metric.closedBall (0 : 𝕍) δ := by
      rw [Metric.mem_closedBall, dist_zero_right]
      exact hz
    exact hsub hz'
  · have := h z hz
    rw [fderiv_obsChart_zero hS ν hF, fderiv_fderiv_obsChart_zero hS ν hF, Real.norm_eq_abs,
      smul_eq_mul] at this
    exact this

end Chart

section Law

variable {X : Type*} [MeasurableSpace X] [Nonempty X] {J : Type*} [Fintype J] [Nonempty J]
  {S : J → X → ℝ} (hS : ∀ j, Bdd (S j)) (ν : Measure X) [IsProbabilityMeasure ν]
include hS

/-- The direction space. -/
local notation "𝕍" => dirSpan ν (fun _ ↦ (1 : ℝ)) S

/-- The chart derivative equivalence. -/
local notation "CDE" => chartDerivEquiv measurable_const (integrable_const 1) (fun _ ↦ one_pos)
  (one_integral_pos ν) hS

/-- The mean map. -/
local notation "mean" => meanMap ν (fun _ ↦ (1 : ℝ)) (fun _ ↦ (0 : ℝ)) S 1

/-- The interior response domain. -/
local notation "Ω" => intrinsicInterior ℝ (momentBody ν (fun _ ↦ (1 : ℝ)) S)

variable {δ : ℝ}

/-- The localisation ball. -/
local notation "cball" => Metric.closedBall (0 : 𝕍) δ

/-- **The localised observable bias decomposition** on the law `μ` of the sampling displacement. -/
theorem obsBias_decomposition (μ : Measure 𝕍) [IsFiniteMeasure μ] {F : X → ℝ} (hF : Bdd F)
    (θ₀ : 𝕍) {K : ℝ}
    (hdom : ∀ z : 𝕍, ‖z‖ ≤ δ → mean (θ₀ : J → ℝ) + (z : J → ℝ) ∈ Ω)
    (hrem : ∀ z : 𝕍, ‖z‖ ≤ δ →
      |obsChart hS ν F θ₀ z - obsChart hS ν F θ₀ 0 -
        dotJ (regressionDir hS ν F θ₀ : J → ℝ) (z : J → ℝ) -
        (1 / 2 : ℝ) * obsHessForm hS ν F θ₀ z| ≤ K * ‖z‖ ^ 3) :
    |(∫ z in cball, (obsChart hS ν F θ₀ z - obsChart hS ν F θ₀ 0) ∂μ) -
        ((∫ z in cball, dotJ (regressionDir hS ν F θ₀ : J → ℝ) (z : J → ℝ) ∂μ) +
          (1 / 2 : ℝ) * ∫ z in cball, obsHessForm hS ν F θ₀ z ∂μ)| ≤
      K * ∫ z in cball, ‖z‖ ^ 3 ∂μ := by
  have hcpt : IsCompact (cball) := isCompact_closedBall (0 : 𝕍) δ
  have hballdom : cball ⊆ responseBallDomain S ν θ₀ := fun z hz ↦ by
    rw [Metric.mem_closedBall, dist_zero_right] at hz
    exact hdom z hz
  have hcont : ContinuousOn (obsChart hS ν F θ₀) (cball) :=
    (contDiffOn_obsChart hS ν hF θ₀).continuousOn.mono hballdom
  have hint : IntegrableOn (fun z : 𝕍 ↦ obsChart hS ν F θ₀ z - obsChart hS ν F θ₀ 0) cball μ :=
    (hcont.sub continuousOn_const).integrableOn_compact hcpt
  have hlin : IntegrableOn (fun z : 𝕍 ↦ dotJ (regressionDir hS ν F θ₀ : J → ℝ) (z : J → ℝ))
      cball μ := by
    have hc : ContinuousOn (fun z : 𝕍 ↦ dotJ (regressionDir hS ν F θ₀ : J → ℝ) (z : J → ℝ))
        cball :=
      ((continuous_dotJ_right (regressionDir hS ν F θ₀ : J → ℝ)).comp
        (𝕍).subtypeL.continuous).continuousOn
    exact hc.integrableOn_compact hcpt
  have hH : IntegrableOn (obsHessForm hS ν F θ₀) cball μ :=
    (continuous_obsHessForm hS ν hF θ₀).continuousOn.integrableOn_compact hcpt
  have h3 : IntegrableOn (fun z : 𝕍 ↦ ‖z‖ ^ 3) cball μ :=
    (continuous_norm.pow 3).continuousOn.integrableOn_compact hcpt
  have hH' : IntegrableOn (fun z : 𝕍 ↦ (1 / 2 : ℝ) * obsHessForm hS ν F θ₀ z) cball μ :=
    hH.const_mul _
  have hsum : IntegrableOn (fun z : 𝕍 ↦ dotJ (regressionDir hS ν F θ₀ : J → ℝ) (z : J → ℝ) +
      (1 / 2 : ℝ) * obsHessForm hS ν F θ₀ z) cball μ := hlin.add hH'
  rw [← integral_const_mul, ← integral_add hlin hH', ← integral_sub hint hsum, ← Real.norm_eq_abs]
  refine (norm_integral_le_of_norm_le (g := fun z : 𝕍 ↦ K * ‖z‖ ^ 3) ?_ ?_).trans ?_
  · exact h3.const_mul K
  · rw [ae_restrict_iff' Metric.isClosed_closedBall.measurableSet]
    refine Eventually.of_forall fun z hz ↦ ?_
    rw [Metric.mem_closedBall, dist_zero_right] at hz
    rw [Real.norm_eq_abs]
    have := hrem z hz
    rw [show obsChart hS ν F θ₀ z - obsChart hS ν F θ₀ 0 -
      (dotJ (regressionDir hS ν F θ₀ : J → ℝ) (z : J → ℝ) + 1 / 2 * obsHessForm hS ν F θ₀ z) =
      obsChart hS ν F θ₀ z - obsChart hS ν F θ₀ 0 -
        dotJ (regressionDir hS ν F θ₀ : J → ℝ) (z : J → ℝ) - 1 / 2 * obsHessForm hS ν F θ₀ z by
      ring]
    exact this
  · rw [integral_const_mul]

/-- The pairing with a fixed vector as a continuous linear functional on the direction space. -/
noncomputable def pairCLM (u : J → ℝ) : 𝕍 →L[ℝ] ℝ :=
  LinearMap.toContinuousLinearMap
    ((∑ j, u j • LinearMap.proj j : (J → ℝ) →ₗ[ℝ] ℝ) ∘ₗ (𝕍).subtype)

omit [Nonempty X] [Nonempty J] hS [IsProbabilityMeasure ν] in
theorem pairCLM_apply (u : J → ℝ) (z : 𝕍) : pairCLM ν u z = dotJ u (z : J → ℝ) := by
  simp only [pairCLM, LinearMap.coe_toContinuousLinearMap', LinearMap.comp_apply,
    Submodule.subtype_apply, LinearMap.sum_apply, LinearMap.smul_apply, LinearMap.proj_apply,
    smul_eq_mul, dotJ]

omit [Nonempty X] [Nonempty J] hS [IsProbabilityMeasure ν] in
/-- **The truncated linear term of a centred law is controlled by the third moment**:
`|∫_{‖z‖≤δ} ⟨u, z⟩ dμ| ≤ (∑_j |u_j|) M₃/δ²`. -/
theorem abs_setIntegral_dotJ_le_of_centred (μ : Measure 𝕍) [IsFiniteMeasure μ] (hδ : 0 < δ)
    (u : J → ℝ) (hcent : ∫ z, z ∂μ = 0) (hint : Integrable (fun z : 𝕍 ↦ z) μ)
    (h3 : Integrable (fun z : 𝕍 ↦ ‖z‖ ^ 3) μ) :
    |∫ z in cball, dotJ u (z : J → ℝ) ∂μ| ≤ (∑ j, |u j|) * ((∫ z, ‖z‖ ^ 3 ∂μ) / δ ^ 2) := by
  have e : ∫ z in cball, dotJ u (z : J → ℝ) ∂μ = dotJ u ((∫ z in cball, z ∂μ : 𝕍) : J → ℝ) := by
    have e' : ∀ z : 𝕍, dotJ u (z : J → ℝ) = pairCLM ν u z := fun z ↦ (pairCLM_apply ν u z).symm
    simp_rw [e']
    exact ContinuousLinearMap.integral_comp_comm (pairCLM ν u) hint.integrableOn
  rw [e]
  refine (abs_dotJ_le u _).trans (mul_le_mul_of_nonneg_left ?_
    (Finset.sum_nonneg fun j _ ↦ abs_nonneg _))
  rw [← Submodule.coe_norm]
  exact norm_setIntegral_id_le_of_centred ν μ hδ hcent hint h3

/-- **The tail of the Hessian term is controlled by the third moment**:
`|∫_{‖z‖≤δ} H_F dμ − E_μ H_F| ≤ ‖H_F‖ M₃/δ`. -/
theorem abs_setIntegral_obsHessForm_sub_le (μ : Measure 𝕍) [IsFiniteMeasure μ] {F : X → ℝ}
    (hF : Bdd F) (θ₀ : 𝕍) (hδ : 0 < δ) (h3 : Integrable (fun z : 𝕍 ↦ ‖z‖ ^ 3) μ) :
    |(∫ z in cball, obsHessForm hS ν F θ₀ z ∂μ) - ∫ z, obsHessForm hS ν F θ₀ z ∂μ| ≤
      ‖obsHessCLM hS ν hF θ₀‖ * (∫ z, ‖z‖ ^ 3 ∂μ) / δ := by
  set κ := ‖obsHessCLM hS ν hF θ₀‖ with hκ
  have hκ0 : 0 ≤ κ := norm_nonneg _
  have hs : MeasurableSet (cball) := Metric.isClosed_closedBall.measurableSet
  have hIH : Integrable (obsHessForm hS ν F θ₀) μ := by
    refine Integrable.mono' ((integrable_const (κ : ℝ)).add (h3.const_mul κ))
      (continuous_obsHessForm hS ν hF θ₀).aestronglyMeasurable (ae_of_all _ fun z ↦ ?_)
    have h := abs_obsHessForm_le hS ν hF θ₀ z
    have h2 : ‖z‖ ^ 2 ≤ 1 + ‖z‖ ^ 3 := by
      rcases le_or_gt ‖z‖ 1 with hz | hz
      · nlinarith [norm_nonneg z, pow_le_one₀ (norm_nonneg z) hz (n := 2),
          pow_nonneg (norm_nonneg z) 3]
      · nlinarith [norm_nonneg z, pow_le_pow_right₀ hz.le (by norm_num : (2 : ℕ) ≤ 3)]
    rw [Real.norm_eq_abs]
    calc |obsHessForm hS ν F θ₀ z| ≤ κ * ‖z‖ ^ 2 := h
      _ ≤ κ * (1 + ‖z‖ ^ 3) := mul_le_mul_of_nonneg_left h2 hκ0
      _ = κ + κ * ‖z‖ ^ 3 := by ring
  have hsplit := integral_add_compl hs hIH
  have e : (∫ z in cball, obsHessForm hS ν F θ₀ z ∂μ) - ∫ z, obsHessForm hS ν F θ₀ z ∂μ =
      -∫ z in (cball)ᶜ, obsHessForm hS ν F θ₀ z ∂μ := by
    rw [← hsplit]
    abel
  rw [e, abs_neg, ← Real.norm_eq_abs]
  have hbound : ∀ᵐ z ∂μ.restrict (cball)ᶜ, ‖obsHessForm hS ν F θ₀ z‖ ≤ κ * ‖z‖ ^ 3 / δ := by
    rw [ae_restrict_iff' hs.compl]
    refine ae_of_all _ fun z hz ↦ ?_
    rw [mem_compl_iff, Metric.mem_closedBall, dist_zero_right, not_le] at hz
    rw [Real.norm_eq_abs]
    refine (abs_obsHessForm_le hS ν hF θ₀ z).trans ?_
    rw [le_div_iff₀ hδ]
    have : ‖z‖ ^ 2 * δ ≤ ‖z‖ ^ 3 := by
      nlinarith [mul_nonneg (sq_nonneg ‖z‖) (sub_nonneg.2 hz.le)]
    calc κ * ‖z‖ ^ 2 * δ = κ * (‖z‖ ^ 2 * δ) := by ring
      _ ≤ κ * ‖z‖ ^ 3 := mul_le_mul_of_nonneg_left this hκ0
  calc ‖∫ z in (cball)ᶜ, obsHessForm hS ν F θ₀ z ∂μ‖
      ≤ ∫ z in (cball)ᶜ, κ * ‖z‖ ^ 3 / δ ∂μ :=
        norm_integral_le_of_norm_le ((h3.const_mul κ).div_const δ).integrableOn hbound
    _ ≤ ∫ z, κ * ‖z‖ ^ 3 / δ ∂μ :=
        setIntegral_le_integral ((h3.const_mul κ).div_const δ)
          (ae_of_all _ fun z ↦ by positivity)
    _ = κ * (∫ z, ‖z‖ ^ 3 ∂μ) / δ := by rw [integral_div, integral_const_mul]

/-- **THE LOCALISED OBSERVABLE BIAS IS THE HESSIAN TERM**: for a centred law `μ` of the sampling
displacement with third absolute moment `M₃`,
`| E[f̂_{F,loc} − f_F(m₀)] − ½ E_μ[H_F(Z)] | ≤ ((∑_j |u_{F,j}|)/δ² + K + ½ ‖H_F‖/δ) M₃`,
where `f̂_{F,loc} = f_F(m₀) + 1_{‖ξ‖≤δ}(f_F(m₀+ξ) − f_F(m₀))` is the reset-localised posterior
expectation. -/
theorem obsBias_hessian (μ : Measure 𝕍) [IsFiniteMeasure μ] {F : X → ℝ} (hF : Bdd F) (θ₀ : 𝕍)
    {K : ℝ} (hδ : 0 < δ) (hK : 0 ≤ K)
    (hdom : ∀ z : 𝕍, ‖z‖ ≤ δ → mean (θ₀ : J → ℝ) + (z : J → ℝ) ∈ Ω)
    (hrem : ∀ z : 𝕍, ‖z‖ ≤ δ →
      |obsChart hS ν F θ₀ z - obsChart hS ν F θ₀ 0 -
        dotJ (regressionDir hS ν F θ₀ : J → ℝ) (z : J → ℝ) -
        (1 / 2 : ℝ) * obsHessForm hS ν F θ₀ z| ≤ K * ‖z‖ ^ 3)
    (hcent : ∫ z, z ∂μ = 0) (hint : Integrable (fun z : 𝕍 ↦ z) μ)
    (h3 : Integrable (fun z : 𝕍 ↦ ‖z‖ ^ 3) μ) :
    |(∫ z in cball, (obsChart hS ν F θ₀ z - obsChart hS ν F θ₀ 0) ∂μ) -
        (1 / 2 : ℝ) * ∫ z, obsHessForm hS ν F θ₀ z ∂μ| ≤
      ((∑ j, |(regressionDir hS ν F θ₀ : J → ℝ) j|) / δ ^ 2 + K +
        (1 / 2 : ℝ) * ‖obsHessCLM hS ν hF θ₀‖ / δ) * ∫ z, ‖z‖ ^ 3 ∂μ := by
  have h1 := obsBias_decomposition hS ν μ hF θ₀ hdom hrem
  have h2 := abs_setIntegral_dotJ_le_of_centred ν μ hδ (regressionDir hS ν F θ₀ : J → ℝ) hcent
    hint h3
  have h3' := abs_setIntegral_obsHessForm_sub_le hS ν μ hF θ₀ hδ h3
  have hM : ∫ z in cball, ‖z‖ ^ 3 ∂μ ≤ ∫ z, ‖z‖ ^ 3 ∂μ :=
    setIntegral_le_integral h3 (ae_of_all _ fun z ↦ by positivity)
  have hM0 : 0 ≤ ∫ z, ‖z‖ ^ 3 ∂μ := integral_nonneg fun z ↦ by positivity
  set I := ∫ z in cball, (obsChart hS ν F θ₀ z - obsChart hS ν F θ₀ 0) ∂μ
  set L := ∫ z in cball, dotJ (regressionDir hS ν F θ₀ : J → ℝ) (z : J → ℝ) ∂μ
  set Hb := ∫ z in cball, obsHessForm hS ν F θ₀ z ∂μ
  set H := ∫ z, obsHessForm hS ν F θ₀ z ∂μ
  set M := ∫ z, ‖z‖ ^ 3 ∂μ
  set Mb := ∫ z in cball, ‖z‖ ^ 3 ∂μ
  have key : I - (1 / 2 : ℝ) * H = (I - (L + (1 / 2 : ℝ) * Hb)) + L + (1 / 2 : ℝ) * (Hb - H) := by
    ring
  rw [key]
  calc |(I - (L + (1 / 2 : ℝ) * Hb)) + L + (1 / 2 : ℝ) * (Hb - H)|
      ≤ |I - (L + (1 / 2 : ℝ) * Hb)| + |L| + |(1 / 2 : ℝ) * (Hb - H)| :=
        (abs_add_le _ _).trans (add_le_add (abs_add_le _ _) le_rfl)
    _ ≤ K * Mb + (∑ j, |(regressionDir hS ν F θ₀ : J → ℝ) j|) * (M / δ ^ 2) +
        (1 / 2 : ℝ) * (‖obsHessCLM hS ν hF θ₀‖ * M / δ) := by
        refine add_le_add (add_le_add h1 h2) ?_
        rw [abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 1 / 2)]
        exact mul_le_mul_of_nonneg_left h3' (by norm_num)
    _ ≤ K * M + (∑ j, |(regressionDir hS ν F θ₀ : J → ℝ) j|) * (M / δ ^ 2) +
        (1 / 2 : ℝ) * (‖obsHessCLM hS ν hF θ₀‖ * M / δ) :=
        add_le_add (add_le_add (mul_le_mul_of_nonneg_left hM hK) le_rfl) le_rfl
    _ = ((∑ j, |(regressionDir hS ν F θ₀ : J → ℝ) j|) / δ ^ 2 + K +
        (1 / 2 : ℝ) * ‖obsHessCLM hS ν hF θ₀‖ / δ) * M := by ring

end Law

section IID

variable {X : Type*} [MeasurableSpace X] [Nonempty X] {J : Type*} [Fintype J] [Nonempty J]
  [DecidableEq J] {Ω : Type*} {S : J → X → ℝ} (hS : ∀ j, Bdd (S j)) (ν : Measure X)
  [IsProbabilityMeasure ν] [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
  (D : Measure X) [IsProbabilityMeasure D] (hDν : D ≪ ν) (Xs : ℕ → Ω → X)
  (hXm : ∀ i, Measurable (Xs i)) (hid : ∀ i, IdentDistrib (Xs i) (Xs 0) P P)
  (hlaw : P.map (Xs 0) = D) (hind : iIndepFun Xs P)
include hS hXm hid hlaw hDν hind

set_option linter.unusedFintypeInType false
set_option linter.unusedDecidableInType false

/-- The direction space. -/
local notation "𝕍" => dirSpan ν (fun _ ↦ (1 : ℝ)) S

/-- The chart derivative equivalence. -/
local notation "CDE" => chartDerivEquiv measurable_const (integrable_const 1) (fun _ ↦ one_pos)
  (one_integral_pos ν) hS

/-- The mean map. -/
local notation "mean" => meanMap ν (fun _ ↦ (1 : ℝ)) (fun _ ↦ (0 : ℝ)) S 1

/-- The interior response domain (the sample space is `Ω`). -/
local notation "Ωm" => intrinsicInterior ℝ (momentBody ν (fun _ ↦ (1 : ℝ)) S)

/-- The raw empirical displacement `M̂_n − m_D`. -/
local notation "raw" n => (fun ω : Ω ↦ fun j : J ↦ sampleResponse S Xs n ω j - ∫ x, S j x ∂D)

omit [IsProbabilityMeasure P] [IsProbabilityMeasure D] hDν hXm hid hlaw hind in
/-- The Hessian form of a projected vector expands over the coordinate basis. -/
theorem obsHessForm_proj_eq_sum {F : X → ℝ} (hF : Bdd F) (p : (J → ℝ) →ₗ[ℝ] 𝕍) (θ₀ : 𝕍)
    (y : J → ℝ) :
    obsHessForm hS ν F θ₀ (p y) = ∑ a, ∑ b, (y a * y b) *
      obsHessCLM hS ν hF θ₀ (p (Pi.single a 1)) (p (Pi.single b 1)) := by
  rw [obsHessForm_eq_obsHessCLM hS ν hF]
  conv_lhs => rw [pi_eq_sum_univ' y, map_sum]
  simp only [map_sum, map_smul, _root_.sum_apply, _root_.smul_apply, smul_eq_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun a _ ↦ Finset.sum_congr rfl fun b _ ↦ by ring

omit [IsProbabilityMeasure P] hDν hXm hid hlaw hind in
/-- **The Hessian contracted with the data covariance**:
`∑_{a,b} Cov_D(S_a,S_b) H_F(A⁻¹ p e_a, A⁻¹ p e_b) = tr(Σ_D D²f_F(m₀))`. -/
noncomputable def hessContraction {F : X → ℝ} (hF : Bdd F) (p : (J → ℝ) →ₗ[ℝ] 𝕍) (θ₀ : 𝕍) :
    ℝ :=
  ∑ a, ∑ b, (∫ x, (S a x - ∫ y, S a y ∂D) * (S b x - ∫ y, S b y ∂D) ∂D) *
    obsHessCLM hS ν hF θ₀ (p (Pi.single a 1)) (p (Pi.single b 1))

variable {n : ℕ} (hn : 0 < n)
include hn

omit hDν hind in
/-- **The covariance contraction**: the expected Hessian form of the projected empirical
displacement is `(1/n)` times the Hessian contracted with the data covariance. -/
theorem integral_obsHessForm_sampleResponse {F : X → ℝ} (hF : Bdd F) (p : (J → ℝ) →ₗ[ℝ] 𝕍)
    (hind' : ∀ i k, i ≠ k → IndepFun (Xs i) (Xs k) P) (θ₀ : 𝕍) :
    ∫ ω, obsHessForm hS ν F θ₀ (p ((raw n) ω)) ∂P =
      (1 / n : ℝ) * hessContraction hS ν D hF p θ₀ := by
  simp_rw [obsHessForm_proj_eq_sum hS ν hF p θ₀]
  rw [integral_finsetSum _ fun a _ ↦ integrable_finsetSum _ fun b _ ↦
    (integrable_sampleResponse_sub_mul hS P D Xs hXm hn a b).mul_const _]
  have e2 : ∀ a, ∫ ω, ∑ b, ((sampleResponse S Xs n ω a - ∫ x, S a x ∂D) *
      (sampleResponse S Xs n ω b - ∫ x, S b x ∂D)) *
        obsHessCLM hS ν hF θ₀ (p (Pi.single a 1)) (p (Pi.single b 1)) ∂P =
      ∑ b, ((∫ x, (S a x - ∫ y, S a y ∂D) * (S b x - ∫ y, S b y ∂D) ∂D) / n) *
        obsHessCLM hS ν hF θ₀ (p (Pi.single a 1)) (p (Pi.single b 1)) := by
    intro a
    rw [integral_finsetSum _ fun b _ ↦
      (integrable_sampleResponse_sub_mul hS P D Xs hXm hn a b).mul_const _]
    refine Finset.sum_congr rfl fun b _ ↦ ?_
    rw [integral_mul_const, integral_sampleResponse_sub_mul_sub hS P D Xs hXm hid hlaw hind' hn]
  simp_rw [e2]
  unfold hessContraction
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun a _ ↦ ?_
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun b _ ↦ ?_
  ring

variable {B : ℝ} (hB0 : 0 ≤ B) (hB : ∀ j x, |S j x| ≤ B)
include hB0 hB

variable {δ : ℝ}

/-- The localisation ball. -/
local notation "cball" => Metric.closedBall (0 : 𝕍) δ

/-- **THE i.i.d. SAMPLING BIAS OF A LOCALISED POSTERIOR EXPECTATION**: for the reset-localised
posterior expectation of `n` i.i.d. samples from a data law `D` with mean `m(θ₀)`,
`| E[f̂_{F,loc}] − f_F(m₀) − (1/(2n)) ∑_{a,b} Cov_D(S_a,S_b) H_F(A⁻¹p e_a, A⁻¹p e_b) |
  ≤ ((∑_j |u_{F,j}|)/δ² + K + ½‖H_F‖/δ) · √3 |J|³ (2B)³ / n^{3/2}`. -/
theorem iid_obsBias_hessian (p : (J → ℝ) →ₗ[ℝ] 𝕍) (hp : ∀ w : 𝕍, p (w : J → ℝ) = w)
    {F : X → ℝ} (hF : Bdd F) (θ₀ : 𝕍) {K : ℝ} (hδ : 0 < δ) (hK : 0 ≤ K)
    (hdom : ∀ z : 𝕍, ‖z‖ ≤ δ → mean (θ₀ : J → ℝ) + (z : J → ℝ) ∈ Ωm)
    (hrem : ∀ z : 𝕍, ‖z‖ ≤ δ →
      |obsChart hS ν F θ₀ z - obsChart hS ν F θ₀ 0 -
        dotJ (regressionDir hS ν F θ₀ : J → ℝ) (z : J → ℝ) -
        (1 / 2 : ℝ) * obsHessForm hS ν F θ₀ z| ≤ K * ‖z‖ ^ 3) :
    |(∫ z in cball, (obsChart hS ν F θ₀ z - obsChart hS ν F θ₀ 0)
          ∂(P.map fun ω ↦ p ((raw n) ω))) -
        (1 / 2 : ℝ) * ((1 / n : ℝ) * hessContraction hS ν D hF p θ₀)| ≤
      ((∑ j, |(regressionDir hS ν F θ₀ : J → ℝ) j|) / δ ^ 2 + K +
        (1 / 2 : ℝ) * ‖obsHessCLM hS ν hF θ₀‖ / δ) *
        (Real.sqrt 3 * Fintype.card J ^ 3 * (2 * B) ^ 3 / (n * Real.sqrt n)) := by
  have hξm := measurable_proj_raw hS ν D Xs hXm (n := n) p
  have : IsProbabilityMeasure (P.map fun ω ↦ p ((raw n) ω)) :=
    Measure.isProbabilityMeasure_map hξm.aemeasurable
  have hidm : AEStronglyMeasurable (fun z : 𝕍 ↦ z) (P.map fun ω ↦ p ((raw n) ω)) :=
    aestronglyMeasurable_id
  have h3m : AEStronglyMeasurable (fun z : 𝕍 ↦ ‖z‖ ^ 3) (P.map fun ω ↦ p ((raw n) ω)) :=
    (by fun_prop : Continuous fun z : 𝕍 ↦ ‖z‖ ^ 3).aestronglyMeasurable
  have hHm : AEStronglyMeasurable (fun z : 𝕍 ↦ obsHessForm hS ν F θ₀ z)
      (P.map fun ω ↦ p ((raw n) ω)) := (continuous_obsHessForm hS ν hF θ₀).aestronglyMeasurable
  have hcent : ∫ z, z ∂(P.map fun ω ↦ p ((raw n) ω)) = 0 := by
    rw [integral_map hξm.aemeasurable hidm]
    exact integral_proj_raw_eq_zero hS ν P D Xs hXm hid hlaw hn hB p
  have hint : Integrable (fun z : 𝕍 ↦ z) (P.map fun ω ↦ p ((raw n) ω)) :=
    (integrable_map_measure hidm hξm.aemeasurable).2 (integrable_proj_raw hS ν P D Xs hXm hn hB p)
  have h3 : Integrable (fun z : 𝕍 ↦ ‖z‖ ^ 3) (P.map fun ω ↦ p ((raw n) ω)) :=
    (integrable_map_measure h3m hξm.aemeasurable).2
      (integrable_norm_pow_three_proj_raw hS ν P D Xs hXm hn hB p)
  have hM3 : ∫ z, ‖z‖ ^ 3 ∂(P.map fun ω ↦ p ((raw n) ω)) ≤
      Real.sqrt 3 * Fintype.card J ^ 3 * (2 * B) ^ 3 / (n * Real.sqrt n) := by
    rw [integral_map hξm.aemeasurable h3m]
    exact integral_norm_pow_three_proj_le hS ν P D hDν Xs hXm hid hlaw hind hn hB0 hB p hp
  have hhess : ∫ z, obsHessForm hS ν F θ₀ z ∂(P.map fun ω ↦ p ((raw n) ω)) =
      (1 / n : ℝ) * hessContraction hS ν D hF p θ₀ := by
    rw [integral_map hξm.aemeasurable hHm]
    exact integral_obsHessForm_sampleResponse hS ν P D Xs hXm hid hlaw hn hF p
      (fun i k hik ↦ hind.indepFun hik) θ₀
  have h := obsBias_hessian hS ν (P.map fun ω ↦ p ((raw n) ω)) hF θ₀ hδ hK hdom hrem hcent
    hint h3
  rw [hhess] at h
  refine h.trans (mul_le_mul_of_nonneg_left hM3 ?_)
  exact add_nonneg (add_nonneg (by positivity) hK) (by positivity)

end IID

end Laplace.Multi
