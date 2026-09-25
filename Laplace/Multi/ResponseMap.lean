/-
Copyright (c) 2026 Timaeus Research. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniel Murfet
-/
import Mathlib
import Laplace.Multi.TiltCauchySchwarz

/-!
# The response map over the data manifold: the exact layer on mixture paths

The loss of a model at a data distribution `q` is `L_q(w) = E_q[ℓ(w, ·)]`, so the posterior
expectation values `Φ_q(φ) = ∫ φ e^{-tL_q} π / ∫ e^{-tL_q} π` are a function of `q`: the
**response map** `q ↦ Φ_q` of the data manifold. This module records the exact (finite-`t`)
structure of that map along **mixture paths** `q_s = (1 − s) q₀ + s q₁`, along which the loss is
affine, `L_s = L₀ + sΔ` with `Δ = L₁ − L₀` (`pathLoss`):

* the mixture posteriors are the exponential tilts of the base posterior by `Δ`
  (`mixExp_eq_tiltExp`, `mixExp_eq_base_ratio`): a data m-geodesic is sent to a posterior
  e-geodesic, and the whole path is determined by the joint law of `(φ, Δ)` under the base
  posterior;
* a loss-neutral base (`L₀` constant in the parameter) makes the mixture path the temperature
  path, `⟨φ⟩_{t, q_s} = ⟨φ⟩_{ts, q₁}` and `Z_t(q_s) = e^{-t(1-s)c} Z_{ts}(q₁)`
  (`priorExp_neutral`, `mixExp_neutral`, `priorZ_neutral`);
* fluctuation–response, `d/ds ⟨φ⟩_s = −t Cov_s(φ, Δ)` (`TiltData.hasDerivAt_mixExp`), its second
  derivative `t² κ₃(φ, Δ, Δ)` (`TiltData.hasDerivAt_neg_mul_mixCov`), and the monotone descent of
  the loss contrast `s ↦ ⟨Δ⟩_s` (`TiltData.mixExp_antitone`);
* the log partition function `A(s) = log Z_t(L_s)` has `A' = −t⟨Δ⟩_s`, `A'' = t² Var_s(Δ)`, is
  convex, and the free energy `−A` is concave (`TiltData.mixLogZ_convexOn`,
  `TiltData.mixFreeEnergy_concaveOn`);
* the Kullback–Leibler divergence between two mixture posteriors is the Bregman divergence of `A`,
  `KL(ρ_s ‖ ρ_{s'}) = A(s') − A(s) − A'(s)(s' − s)` (`TiltData.mixKL_eq`);
* for a finite-dimensional affine family `L_a = L₀ + ∑ aᵢ Rᵢ` (a chart of the data manifold with
  `Rᵢ` the losses of the tangent directions) the differential of the response map in a direction
  `v` is `−t Cov_a(φ, R_v)` (`TiltData.hasDerivAt_affExp`), and the response form
  `g_a(v, u) = t² Cov_a(R_v, R_u)` is bilinear, symmetric, positive semidefinite, equals the
  second derivative of `A` along `v`, and bounds every standardised response through
  Cauchy–Schwarz (`responseForm_*`, `TiltData.sq_response_le`).

The standing hypotheses are those of `TiltInterpolation`: a nonnegative integrable base weight
with positive mass and bounded measurable observables, packaged as `TiltData μ (baseWeight π L₀ t)
Δ M`; `tiltData_baseWeight_of_bounded` produces them from an integrable prior and bounded losses.
-/

open MeasureTheory Filter Topology

namespace Laplace.Multi

variable {X : Type*} [MeasurableSpace X] (μ : Measure X)

/-! ### Posterior expectations with a prior density, and the mixture path -/

/-- The partition function `Z_t(L) = ∫ e^{-tL} π`. -/
noncomputable def priorZ (π L : X → ℝ) (t : ℝ) : ℝ := ∫ x, Real.exp (-(t * L x)) * π x ∂μ

/-- The posterior expectation `⟨φ⟩_{t,L} = ∫ φ e^{-tL} π / Z_t(L)`. -/
noncomputable def priorExp (π L φ : X → ℝ) (t : ℝ) : ℝ :=
  (∫ x, φ x * Real.exp (-(t * L x)) * π x ∂μ) / priorZ μ π L t

/-- The posterior covariance `Cov_{t,L}(φ, ψ)`. -/
noncomputable def priorCov (π L φ ψ : X → ℝ) (t : ℝ) : ℝ :=
  priorExp μ π L (fun x ↦ φ x * ψ x) t - priorExp μ π L φ t * priorExp μ π L ψ t

/-- The affine path of losses `L_s = L₀ + sΔ` of a mixture path of data distributions. -/
noncomputable def pathLoss (L₀ Δ : X → ℝ) (s : ℝ) : X → ℝ := fun x ↦ L₀ x + s * Δ x

/-- The base posterior weight `e^{-tL₀} π`. -/
noncomputable def baseWeight (π L₀ : X → ℝ) (t : ℝ) : X → ℝ :=
  fun x ↦ Real.exp (-(t * L₀ x)) * π x

/-- `⟨φ⟩_{t,s}`, the posterior expectation at the mixture `q_s`. -/
noncomputable def mixExp (π L₀ Δ φ : X → ℝ) (t s : ℝ) : ℝ := priorExp μ π (pathLoss L₀ Δ s) φ t

/-- `Cov_{t,s}(φ, ψ)` along the mixture path. -/
noncomputable def mixCov (π L₀ Δ φ ψ : X → ℝ) (t s : ℝ) : ℝ :=
  priorCov μ π (pathLoss L₀ Δ s) φ ψ t

/-- The log partition function `A(s) = log Z_t(L_s)` along the mixture path. -/
noncomputable def mixLogZ (π L₀ Δ : X → ℝ) (t s : ℝ) : ℝ :=
  Real.log (priorZ μ π (pathLoss L₀ Δ s) t)

/-- The log of the ratio of the normalised posterior densities at `s` and `s'`. -/
noncomputable def mixLogRatio (π L₀ Δ : X → ℝ) (t s s' : ℝ) (x : X) : ℝ :=
  Real.log (Real.exp (-(t * pathLoss L₀ Δ s x)) * π x / priorZ μ π (pathLoss L₀ Δ s) t) -
    Real.log (Real.exp (-(t * pathLoss L₀ Δ s' x)) * π x / priorZ μ π (pathLoss L₀ Δ s') t)

/-- The Kullback–Leibler divergence `KL(ρ_s ‖ ρ_{s'})` between two mixture posteriors, as the
`ρ_s`-expectation of the log-density ratio. -/
noncomputable def mixKL (π L₀ Δ : X → ℝ) (t s s' : ℝ) : ℝ :=
  mixExp μ π L₀ Δ (mixLogRatio μ π L₀ Δ t s s') t s

omit [MeasurableSpace X] in
theorem pathLoss_zero (L₀ Δ : X → ℝ) : pathLoss L₀ Δ 0 = L₀ :=
  funext fun x ↦ by simp [pathLoss]

omit [MeasurableSpace X] in
theorem exp_pathLoss_mul (π L₀ Δ : X → ℝ) (t s : ℝ) (x : X) :
    Real.exp (-(t * pathLoss L₀ Δ s x)) * π x =
      Real.exp (-(t * Δ x * s)) * baseWeight π L₀ t x := by
  simp only [pathLoss, baseWeight]
  rw [← mul_assoc, ← Real.exp_add]
  congr 2
  ring

theorem priorZ_pathLoss (π L₀ Δ : X → ℝ) (t s : ℝ) :
    priorZ μ π (pathLoss L₀ Δ s) t = tiltNum μ (baseWeight π L₀ t) (fun _ ↦ 1) Δ t s := by
  unfold priorZ tiltNum
  simp only [one_mul]
  exact integral_congr_ae (Filter.Eventually.of_forall fun x ↦ exp_pathLoss_mul π L₀ Δ t s x)

/-- **Mixture posteriors are exponential tilts of the base posterior**: `⟨φ⟩_{t,s}` is the tilted
expectation `P_s(φ)` of `TiltInterpolation` with base weight `e^{-tL₀} π` and residual `Δ`. -/
theorem mixExp_eq_tiltExp (π L₀ Δ φ : X → ℝ) (t s : ℝ) :
    mixExp μ π L₀ Δ φ t s = tiltExp μ (baseWeight π L₀ t) φ Δ t s := by
  unfold mixExp priorExp tiltExp
  rw [priorZ_pathLoss]
  congr 1
  unfold tiltNum
  exact integral_congr_ae (Filter.Eventually.of_forall fun x ↦ by
    simp only [mul_assoc, exp_pathLoss_mul])

theorem mixCov_eq_tiltCov (π L₀ Δ φ ψ : X → ℝ) (t s : ℝ) :
    mixCov μ π L₀ Δ φ ψ t s = tiltCov μ (baseWeight π L₀ t) φ ψ Δ t s := by
  simp only [mixCov, priorCov, tiltCov, ← mixExp_eq_tiltExp, mixExp]

theorem mixExp_zero (π L₀ Δ φ : X → ℝ) (t : ℝ) :
    mixExp μ π L₀ Δ φ t 0 = priorExp μ π L₀ φ t := by
  simp only [mixExp, pathLoss_zero]

theorem mixCov_zero (π L₀ Δ φ ψ : X → ℝ) (t : ℝ) :
    mixCov μ π L₀ Δ φ ψ t 0 = priorCov μ π L₀ φ ψ t := by
  simp only [mixCov, pathLoss_zero]

/-- The whole mixture path is determined by the base posterior:
`⟨φ⟩_{t,s} = ⟨φ e^{-tsΔ}⟩_{t,0} / ⟨e^{-tsΔ}⟩_{t,0}`. -/
theorem mixExp_eq_base_ratio (π L₀ Δ φ : X → ℝ) (t s : ℝ) (hZ : priorZ μ π L₀ t ≠ 0) :
    mixExp μ π L₀ Δ φ t s =
      priorExp μ π L₀ (fun x ↦ φ x * Real.exp (-(t * s * Δ x))) t /
        priorExp μ π L₀ (fun x ↦ Real.exp (-(t * s * Δ x))) t := by
  unfold priorExp
  rw [div_div_div_cancel_right₀ hZ, mixExp_eq_tiltExp]
  unfold tiltExp tiltNum
  simp only [one_mul]
  congr 1
  · exact integral_congr_ae (Filter.Eventually.of_forall fun x ↦ by
      beta_reduce
      simp only [baseWeight]
      rw [show t * Δ x * s = t * s * Δ x by ring]
      ring)
  · exact integral_congr_ae (Filter.Eventually.of_forall fun x ↦ by
      beta_reduce
      simp only [baseWeight]
      rw [show t * Δ x * s = t * s * Δ x by ring]
      ring)

/-! ### A loss-neutral base: the mixture path is the temperature path -/

/-- If the base loss is the constant `c`, the partition function along the mixture path towards
`L₁` is the partition function of `L₁` at inverse temperature `ts`, up to the factor
`e^{-t(1-s)c}`. -/
theorem priorZ_neutral (π L₁ : X → ℝ) (c t s : ℝ) :
    priorZ μ π (fun x ↦ (1 - s) * c + s * L₁ x) t =
      Real.exp (-(t * (1 - s) * c)) * priorZ μ π L₁ (t * s) := by
  unfold priorZ
  rw [← integral_const_mul]
  refine integral_congr_ae (Filter.Eventually.of_forall fun x ↦ ?_)
  beta_reduce
  rw [← mul_assoc, ← Real.exp_add]
  congr 2
  ring

/-- **Loss-neutral base = temperature path**: if `L_{q₀} = c` is constant in the parameter, the
posterior expectation at the mixture `(1 − s) q₀ + s q₁` is the posterior expectation for `q₁` at
inverse temperature `ts`. -/
theorem priorExp_neutral (π L₁ φ : X → ℝ) (c t s : ℝ) :
    priorExp μ π (fun x ↦ (1 - s) * c + s * L₁ x) φ t = priorExp μ π L₁ φ (t * s) := by
  unfold priorExp
  rw [priorZ_neutral]
  have hnum : (∫ x, φ x * Real.exp (-(t * ((1 - s) * c + s * L₁ x))) * π x ∂μ) =
      Real.exp (-(t * (1 - s) * c)) * ∫ x, φ x * Real.exp (-(t * s * L₁ x)) * π x ∂μ := by
    rw [← integral_const_mul]
    refine integral_congr_ae (Filter.Eventually.of_forall fun x ↦ ?_)
    beta_reduce
    rw [show Real.exp (-(t * ((1 - s) * c + s * L₁ x))) =
        Real.exp (-(t * (1 - s) * c)) * Real.exp (-(t * s * L₁ x)) by
      rw [← Real.exp_add]; congr 1; ring]
    ring
  rw [hnum, mul_div_mul_left _ _ (Real.exp_pos _).ne']

/-- The mixture path from a neutral base `L₀ = c` in the direction `Δ`, in the language of
`mixExp`: it is the temperature path of `c + Δ`. -/
theorem mixExp_neutral (π Δ φ : X → ℝ) (c t s : ℝ) :
    mixExp μ π (fun _ ↦ c) Δ φ t s = priorExp μ π (fun x ↦ c + Δ x) φ (t * s) := by
  rw [← priorExp_neutral (c := c)]
  unfold mixExp
  congr 1
  funext x
  simp only [pathLoss]
  ring

/-! ### The standing hypotheses from an integrable prior and bounded losses -/

/-- An integrable nonnegative prior of positive mass, a bounded measurable base loss and a bounded
measurable contrast give the `TiltData` hypotheses for the base weight `e^{-tL₀} π`. -/
theorem tiltData_baseWeight_of_bounded {π L₀ Δ : X → ℝ} (hπm : Measurable π)
    (hπi : Integrable π μ) (hπ : ∀ x, 0 ≤ π x) (hπpos : 0 < ∫ x, π x ∂μ) (hL₀m : Measurable L₀)
    {M₀ : ℝ} (hL₀ : ∀ x, |L₀ x| ≤ M₀) (hΔm : Measurable Δ) {M : ℝ} (hΔ : ∀ x, |Δ x| ≤ M)
    (t : ℝ) : TiltData μ (baseWeight π L₀ t) Δ M := by
  have hem : Measurable fun x ↦ Real.exp (-(t * L₀ x)) :=
    Real.measurable_exp.comp (hL₀m.const_mul t).neg
  have hνm : Measurable (baseWeight π L₀ t) := hem.mul hπm
  have hνi : Integrable (baseWeight π L₀ t) μ := by
    refine hπi.bdd_mul (c := Real.exp (|t| * M₀)) hem.aestronglyMeasurable
      (Filter.Eventually.of_forall fun x ↦ ?_)
    rw [Real.norm_eq_abs, Real.abs_exp, Real.exp_le_exp]
    calc -(t * L₀ x) ≤ |t * L₀ x| := neg_le_abs _
      _ = |t| * |L₀ x| := abs_mul _ _
      _ ≤ |t| * M₀ := mul_le_mul_of_nonneg_left (hL₀ x) (abs_nonneg t)
  have hνnn : ∀ x, 0 ≤ baseWeight π L₀ t x := fun x ↦ mul_nonneg (Real.exp_pos _).le (hπ x)
  have hνpos : 0 < ∫ x, baseWeight π L₀ t x ∂μ := by
    have hlow : Real.exp (-(|t| * M₀)) * ∫ x, π x ∂μ ≤ ∫ x, baseWeight π L₀ t x ∂μ := by
      rw [← integral_const_mul]
      refine integral_mono (hπi.const_mul _) hνi fun x ↦ ?_
      simp only [baseWeight]
      refine mul_le_mul_of_nonneg_right ?_ (hπ x)
      rw [Real.exp_le_exp]
      calc -(|t| * M₀) ≤ -|t * L₀ x| := by
            rw [abs_mul]
            exact neg_le_neg (mul_le_mul_of_nonneg_left (hL₀ x) (abs_nonneg t))
        _ ≤ -(t * L₀ x) := neg_le_neg (le_abs_self _)
    exact lt_of_lt_of_le (mul_pos (Real.exp_pos _) hπpos) hlow
  exact ⟨hνm, hνi, hνnn, hνpos, hΔm, hΔ⟩

variable {μ}

/-- The `TiltData` hypotheses do not depend on the residual beyond its bound: any bounded
measurable residual may replace it. -/
theorem TiltData.changeR {ν R₀ R : X → ℝ} {M₀ M : ℝ} (h : TiltData μ ν R₀ M₀)
    (hRm : Measurable R) (hR : ∀ x, |R x| ≤ M) : TiltData μ ν R M :=
  ⟨h.ν_meas, h.ν_int, h.ν_nonneg, h.ν_pos, hRm, hR⟩

/-! ### Fluctuation–response along the mixture path -/

section Derivatives

variable [Nonempty X] {π L₀ Δ : X → ℝ} {t M : ℝ}

/-- **Fluctuation–response along a mixture path**: `d/ds ⟨φ⟩_{t,s} = −t Cov_{t,s}(φ, Δ)`. -/
theorem TiltData.hasDerivAt_mixExp (h : TiltData μ (baseWeight π L₀ t) Δ M) {φ : X → ℝ}
    (hφ : Bdd φ) (s₀ : ℝ) :
    HasDerivAt (fun s ↦ mixExp μ π L₀ Δ φ t s) (-t * mixCov μ π L₀ Δ φ Δ t s₀) s₀ := by
  obtain ⟨hφm, Mφ, hφb⟩ := hφ
  simp only [mixExp_eq_tiltExp, mixCov_eq_tiltCov]
  exact h.hasDerivAt_tiltExp hφm hφb t s₀

theorem TiltData.mixCov_self_nonneg (h : TiltData μ (baseWeight π L₀ t) Δ M) {φ : X → ℝ}
    (hφ : Bdd φ) (s : ℝ) : 0 ≤ mixCov μ π L₀ Δ φ φ t s := by
  rw [mixCov_eq_tiltCov]
  exact h.tiltCov_self_nonneg hφ t s

/-- The second derivative of the response: `d²/ds² ⟨φ⟩_{t,s} = t² κ₃(φ, Δ, Δ)`, the joint third
cumulant `⟨φΔ²⟩ − 2⟨Δ⟩⟨φΔ⟩ − ⟨φ⟩⟨Δ²⟩ + 2⟨φ⟩⟨Δ⟩²`. -/
theorem TiltData.hasDerivAt_neg_mul_mixCov (h : TiltData μ (baseWeight π L₀ t) Δ M)
    {φ : X → ℝ} (hφ : Bdd φ) (s₀ : ℝ) :
    HasDerivAt (fun s ↦ -t * mixCov μ π L₀ Δ φ Δ t s)
      (t ^ 2 * (mixExp μ π L₀ Δ (fun x ↦ φ x * Δ x * Δ x) t s₀
        - 2 * mixExp μ π L₀ Δ Δ t s₀ * mixExp μ π L₀ Δ (fun x ↦ φ x * Δ x) t s₀
        - mixExp μ π L₀ Δ φ t s₀ * mixExp μ π L₀ Δ (fun x ↦ Δ x * Δ x) t s₀
        + 2 * mixExp μ π L₀ Δ φ t s₀ * mixExp μ π L₀ Δ Δ t s₀ ^ 2)) s₀ := by
  have hφΔ : Bdd fun x ↦ φ x * Δ x := hφ.mul h.bdd_R
  obtain ⟨hφm, Mφ, hφb⟩ := hφ
  obtain ⟨h1m, M1, h1b⟩ := hφΔ
  obtain ⟨hΔm, MΔ, hΔb⟩ := h.bdd_R
  have d1 := h.hasDerivAt_tiltExp h1m h1b t s₀
  have d2 := h.hasDerivAt_tiltExp hφm hφb t s₀
  have d3 := h.hasDerivAt_tiltExp hΔm hΔb t s₀
  simp only [mixCov_eq_tiltCov, mixExp_eq_tiltExp]
  unfold tiltCov
  refine ((d1.sub (d2.mul d3)).const_mul (-t)).congr_deriv ?_
  unfold tiltCov
  ring

/-- **The loss contrast descends**: `s ↦ ⟨Δ⟩_{t,s}` is antitone for `t ≥ 0`, since its derivative
is `−t Var_{t,s}(Δ) ≤ 0`. -/
theorem TiltData.mixExp_antitone (h : TiltData μ (baseWeight π L₀ t) Δ M) (ht : 0 ≤ t) :
    Antitone fun s ↦ mixExp μ π L₀ Δ Δ t s := by
  refine antitone_of_deriv_nonpos (fun s ↦ (h.hasDerivAt_mixExp h.bdd_R s).differentiableAt)
    fun s ↦ ?_
  rw [(h.hasDerivAt_mixExp h.bdd_R s).deriv, neg_mul]
  exact neg_nonpos.mpr (mul_nonneg ht (h.mixCov_self_nonneg h.bdd_R s))

/-! ### The log partition function is convex along mixture paths -/

/-- `A'(s) = −t ⟨Δ⟩_{t,s}`. -/
theorem TiltData.hasDerivAt_mixLogZ (h : TiltData μ (baseWeight π L₀ t) Δ M) (s₀ : ℝ) :
    HasDerivAt (fun s ↦ mixLogZ μ π L₀ Δ t s) (-t * mixExp μ π L₀ Δ Δ t s₀) s₀ := by
  have hZ := h.hasDerivAt_tiltNum (f := fun _ ↦ (1 : ℝ)) measurable_const (Mf := 1)
    (fun _ ↦ by simp) t s₀
  simp only [one_mul] at hZ
  have hpos := h.tiltNum_one_pos t s₀
  simp only [mixLogZ, priorZ_pathLoss, mixExp_eq_tiltExp]
  refine (hZ.log hpos.ne').congr_deriv ?_
  unfold tiltExp
  ring

/-- `A''(s) = t² Var_{t,s}(Δ)`. -/
theorem TiltData.hasDerivAt_deriv_mixLogZ (h : TiltData μ (baseWeight π L₀ t) Δ M) (s₀ : ℝ) :
    HasDerivAt (fun s ↦ -t * mixExp μ π L₀ Δ Δ t s) (t ^ 2 * mixCov μ π L₀ Δ Δ Δ t s₀) s₀ :=
  ((h.hasDerivAt_mixExp h.bdd_R s₀).const_mul (-t)).congr_deriv (by ring)

/-- **The log partition function is convex along mixture paths.** -/
theorem TiltData.mixLogZ_convexOn (h : TiltData μ (baseWeight π L₀ t) Δ M) :
    ConvexOn ℝ Set.univ fun s ↦ mixLogZ μ π L₀ Δ t s := by
  have hderiv : deriv (fun s ↦ mixLogZ μ π L₀ Δ t s) = fun s ↦ -t * mixExp μ π L₀ Δ Δ t s :=
    funext fun s ↦ (h.hasDerivAt_mixLogZ s).deriv
  refine convexOn_univ_of_deriv2_nonneg (fun s ↦ (h.hasDerivAt_mixLogZ s).differentiableAt) ?_ ?_
  · rw [hderiv]
    exact fun s ↦ (h.hasDerivAt_deriv_mixLogZ s).differentiableAt
  · intro s
    change 0 ≤ deriv (deriv fun s ↦ mixLogZ μ π L₀ Δ t s) s
    rw [hderiv, (h.hasDerivAt_deriv_mixLogZ s).deriv]
    exact mul_nonneg (sq_nonneg t) (h.mixCov_self_nonneg h.bdd_R s)

/-- **The free energy `−log Z` is concave along mixture paths.** -/
theorem TiltData.mixFreeEnergy_concaveOn (h : TiltData μ (baseWeight π L₀ t) Δ M) :
    ConcaveOn ℝ Set.univ fun s ↦ -mixLogZ μ π L₀ Δ t s :=
  h.mixLogZ_convexOn.neg

/-! ### Kullback–Leibler divergence is the Bregman divergence of `A` -/

theorem TiltData.mixLogRatio_eq (h : TiltData μ (baseWeight π L₀ t) Δ M) (hπ : ∀ x, 0 ≤ π x)
    (s s' : ℝ) {x : X} (hx : π x ≠ 0) :
    mixLogRatio μ π L₀ Δ t s s' x =
      -(t * (s - s')) * Δ x + (mixLogZ μ π L₀ Δ t s' - mixLogZ μ π L₀ Δ t s) := by
  have hxpos : 0 < π x := lt_of_le_of_ne (hπ x) (Ne.symm hx)
  have hZs : 0 < priorZ μ π (pathLoss L₀ Δ s) t := by
    rw [priorZ_pathLoss]; exact h.tiltNum_one_pos t s
  have hZs' : 0 < priorZ μ π (pathLoss L₀ Δ s') t := by
    rw [priorZ_pathLoss]; exact h.tiltNum_one_pos t s'
  unfold mixLogRatio mixLogZ
  rw [Real.log_div (mul_pos (Real.exp_pos _) hxpos).ne' hZs.ne',
    Real.log_div (mul_pos (Real.exp_pos _) hxpos).ne' hZs'.ne',
    Real.log_mul (Real.exp_pos _).ne' hx, Real.log_mul (Real.exp_pos _).ne' hx, Real.log_exp,
    Real.log_exp]
  simp only [pathLoss]
  ring

/-- **KL is the Bregman divergence of the log partition function** along a mixture path:
`KL(ρ_s ‖ ρ_{s'}) = A(s') − A(s) − A'(s) (s' − s)` with `A'(s) = −t ⟨Δ⟩_{t,s}`. -/
theorem TiltData.mixKL_eq (h : TiltData μ (baseWeight π L₀ t) Δ M) (hπ : ∀ x, 0 ≤ π x)
    (s s' : ℝ) :
    mixKL μ π L₀ Δ t s s' =
      mixLogZ μ π L₀ Δ t s' - mixLogZ μ π L₀ Δ t s - (-t * mixExp μ π L₀ Δ Δ t s) * (s' - s) := by
  have hint : mixKL μ π L₀ Δ t s s' = mixExp μ π L₀ Δ
      (fun x ↦ -(t * (s - s')) * Δ x + (mixLogZ μ π L₀ Δ t s' - mixLogZ μ π L₀ Δ t s)) t s := by
    unfold mixKL
    rw [mixExp_eq_tiltExp, mixExp_eq_tiltExp]
    unfold tiltExp tiltNum
    congr 1
    refine integral_congr_ae (Filter.Eventually.of_forall fun x ↦ ?_)
    beta_reduce
    by_cases hx : π x = 0
    · simp [baseWeight, hx]
    · rw [h.mixLogRatio_eq hπ s s' hx]
  rw [hint, mixExp_eq_tiltExp, h.tiltExp_add (h.bdd_R.const_mul _) (Bdd.const _),
    tiltExp_const_mul, h.tiltExp_const, ← mixExp_eq_tiltExp]
  ring

end Derivatives

/-! ### Finite-dimensional affine families: the influence operator and the response form -/

section Affine

variable {ι : Type*} [Fintype ι]

/-- The affine family `L_a = L₀ + ∑ᵢ aᵢ Rᵢ` (a chart of the data manifold). -/
noncomputable def affLoss (L₀ : X → ℝ) (R : ι → X → ℝ) (a : ι → ℝ) : X → ℝ :=
  fun x ↦ L₀ x + ∑ i, a i * R i x

/-- The loss of a tangent direction, `R_v = ∑ᵢ vᵢ Rᵢ`. -/
noncomputable def dirLoss (R : ι → X → ℝ) (v : ι → ℝ) : X → ℝ := fun x ↦ ∑ i, v i * R i x

/-- **The response form** `g_a(v, u) = t² Cov_a(R_v, R_u)`: the Fisher information of the posterior
family in the data directions `v, u`. -/
noncomputable def responseForm (μ : Measure X) (π L₀ : X → ℝ) (R : ι → X → ℝ) (a : ι → ℝ) (t : ℝ)
    (v u : ι → ℝ) : ℝ :=
  t ^ 2 * priorCov μ π (affLoss L₀ R a) (dirLoss R v) (dirLoss R u) t

omit [MeasurableSpace X] in
theorem affLoss_add_smul (L₀ : X → ℝ) (R : ι → X → ℝ) (a v : ι → ℝ) (ε : ℝ) :
    affLoss L₀ R (a + ε • v) = pathLoss (affLoss L₀ R a) (dirLoss R v) ε := by
  funext x
  simp only [affLoss, pathLoss, dirLoss, Pi.add_apply, Pi.smul_apply, smul_eq_mul, add_mul,
    Finset.sum_add_distrib, Finset.mul_sum, mul_assoc]
  ring

omit [MeasurableSpace X] in
theorem dirLoss_add (R : ι → X → ℝ) (v w : ι → ℝ) :
    dirLoss R (v + w) = fun x ↦ dirLoss R v x + dirLoss R w x := by
  funext x
  simp only [dirLoss, Pi.add_apply, add_mul, Finset.sum_add_distrib]

omit [MeasurableSpace X] in
theorem dirLoss_smul (R : ι → X → ℝ) (c : ℝ) (v : ι → ℝ) :
    dirLoss R (c • v) = fun x ↦ c * dirLoss R v x := by
  funext x
  simp only [dirLoss, Pi.smul_apply, smul_eq_mul, Finset.mul_sum, mul_assoc]

theorem bdd_dirLoss {R : ι → X → ℝ} (hR : ∀ i, Bdd (R i)) (v : ι → ℝ) : Bdd (dirLoss R v) := by
  have hm : ∀ i, Measurable (R i) := fun i ↦ (hR i).1
  choose M hM using fun i ↦ (hR i).2
  refine ⟨Finset.measurable_sum Finset.univ fun i _ ↦ (hm i).const_mul (v i),
    ∑ i, |v i| * M i, fun x ↦ ?_⟩
  unfold dirLoss
  refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun i _ ↦ ?_)
  rw [abs_mul]
  exact mul_le_mul_of_nonneg_left (hM i x) (abs_nonneg _)

theorem priorExp_eq_tiltExp_zero (π L φ R : X → ℝ) (t : ℝ) :
    priorExp μ π L φ t = tiltExp μ (baseWeight π L t) φ R t 0 := by
  rw [tiltExp_zero]
  unfold priorExp priorZ baseWeight
  congr 1
  exact integral_congr_ae (Filter.Eventually.of_forall fun x ↦ by beta_reduce; ring)

theorem priorCov_eq_tiltCov_zero (π L φ ψ R : X → ℝ) (t : ℝ) :
    priorCov μ π L φ ψ t = tiltCov μ (baseWeight π L t) φ ψ R t 0 := by
  simp only [priorCov, tiltCov, priorExp_eq_tiltExp_zero (R := R)]

theorem priorCov_comm (π L φ ψ : X → ℝ) (t : ℝ) : priorCov μ π L φ ψ t = priorCov μ π L ψ φ t := by
  unfold priorCov
  have e : (fun x ↦ φ x * ψ x) = fun x ↦ ψ x * φ x := funext fun x ↦ mul_comm _ _
  rw [e, mul_comm]

theorem priorCov_const_mul_left (π L φ ψ : X → ℝ) (c t : ℝ) :
    priorCov μ π L (fun x ↦ c * φ x) ψ t = c * priorCov μ π L φ ψ t := by
  simp only [priorCov, priorExp_eq_tiltExp_zero (R := fun _ ↦ (0 : ℝ))]
  have e : (fun x ↦ c * φ x * ψ x) = fun x ↦ c * (φ x * ψ x) := funext fun x ↦ mul_assoc _ _ _
  rw [e, tiltExp_const_mul, tiltExp_const_mul]
  ring

variable [Nonempty X] {π L₀ : X → ℝ} {R : ι → X → ℝ} {a : ι → ℝ} {t M₀ : ℝ}

theorem TiltData.priorCov_add_left {L : X → ℝ} (h : TiltData μ (baseWeight π L t) (fun _ ↦ 0) M₀)
    {f g ψ : X → ℝ} (hf : Bdd f) (hg : Bdd g) (hψ : Bdd ψ) :
    priorCov μ π L (fun x ↦ f x + g x) ψ t = priorCov μ π L f ψ t + priorCov μ π L g ψ t := by
  simp only [priorCov_eq_tiltCov_zero (R := fun _ ↦ (0 : ℝ))]
  unfold tiltCov
  have e : (fun x ↦ (f x + g x) * ψ x) = fun x ↦ f x * ψ x + g x * ψ x :=
    funext fun x ↦ add_mul _ _ _
  rw [e, h.tiltExp_add (hf.mul hψ) (hg.mul hψ), h.tiltExp_add hf hg]
  ring

/-- **The differential of the response map** in the data direction `v`:
`d/dε ⟨φ⟩_{a + εv} |_{ε = 0} = −t Cov_a(φ, R_v)`, the Bayesian influence of the direction on the
observable. -/
theorem TiltData.hasDerivAt_affExp (h : TiltData μ (baseWeight π (affLoss L₀ R a) t) (fun _ ↦ 0) M₀)
    (hR : ∀ i, Bdd (R i)) {φ : X → ℝ} (hφ : Bdd φ) (v : ι → ℝ) :
    HasDerivAt (fun ε : ℝ ↦ priorExp μ π (affLoss L₀ R (a + ε • v)) φ t)
      (-t * priorCov μ π (affLoss L₀ R a) φ (dirLoss R v) t) 0 := by
  obtain ⟨hvm, Mv, hvb⟩ := bdd_dirLoss hR v
  have key := (h.changeR hvm hvb).hasDerivAt_mixExp hφ 0
  simp only [affLoss_add_smul]
  rw [mixCov_zero] at key
  exact key

/-- The response form is the second derivative of the log partition function along the data
direction `v`: `D²A_a[v, v] = t² Var_a(R_v)`. -/
theorem TiltData.hasDerivAt_deriv_mixLogZ_dir
    (h : TiltData μ (baseWeight π (affLoss L₀ R a) t) (fun _ ↦ 0) M₀) (hR : ∀ i, Bdd (R i))
    (v : ι → ℝ) :
    HasDerivAt (deriv fun ε : ℝ ↦ mixLogZ μ π (affLoss L₀ R a) (dirLoss R v) t ε)
      (responseForm μ π L₀ R a t v v) 0 := by
  obtain ⟨hvm, Mv, hvb⟩ := bdd_dirLoss hR v
  have h' := h.changeR hvm hvb
  have hderiv : deriv (fun ε : ℝ ↦ mixLogZ μ π (affLoss L₀ R a) (dirLoss R v) t ε) =
      fun ε ↦ -t * mixExp μ π (affLoss L₀ R a) (dirLoss R v) (dirLoss R v) t ε :=
    funext fun ε ↦ (h'.hasDerivAt_mixLogZ ε).deriv
  rw [hderiv]
  have key := h'.hasDerivAt_deriv_mixLogZ 0
  rw [mixCov_zero] at key
  exact key

omit [Nonempty X] in
theorem responseForm_comm (v u : ι → ℝ) :
    responseForm μ π L₀ R a t v u = responseForm μ π L₀ R a t u v := by
  unfold responseForm
  rw [priorCov_comm]

theorem TiltData.responseForm_add_left
    (h : TiltData μ (baseWeight π (affLoss L₀ R a) t) (fun _ ↦ 0) M₀) (hR : ∀ i, Bdd (R i))
    (v w u : ι → ℝ) :
    responseForm μ π L₀ R a t (v + w) u =
      responseForm μ π L₀ R a t v u + responseForm μ π L₀ R a t w u := by
  unfold responseForm
  rw [dirLoss_add, h.priorCov_add_left (bdd_dirLoss hR v) (bdd_dirLoss hR w) (bdd_dirLoss hR u)]
  ring

omit [Nonempty X] in
theorem responseForm_smul_left (c : ℝ) (v u : ι → ℝ) :
    responseForm μ π L₀ R a t (c • v) u = c * responseForm μ π L₀ R a t v u := by
  unfold responseForm
  rw [dirLoss_smul, priorCov_const_mul_left]
  ring

/-- The response form is positive semidefinite. -/
theorem TiltData.responseForm_self_nonneg
    (h : TiltData μ (baseWeight π (affLoss L₀ R a) t) (fun _ ↦ 0) M₀) (hR : ∀ i, Bdd (R i))
    (v : ι → ℝ) : 0 ≤ responseForm μ π L₀ R a t v v := by
  unfold responseForm
  rw [priorCov_eq_tiltCov_zero (R := fun _ ↦ (0 : ℝ))]
  exact mul_nonneg (sq_nonneg t) (h.tiltCov_self_nonneg (bdd_dirLoss hR v) t 0)

/-- **The response bound**: the squared response of an observable to a data direction is at most
the observable's posterior variance times the response form,
`(t Cov_a(φ, R_v))² ≤ Var_a(φ) · g_a(v, v)`; the response form is the maximal standardised
response. -/
theorem TiltData.sq_response_le (h : TiltData μ (baseWeight π (affLoss L₀ R a) t) (fun _ ↦ 0) M₀)
    (hR : ∀ i, Bdd (R i)) {φ : X → ℝ} (hφ : Bdd φ) (v : ι → ℝ) :
    (t * priorCov μ π (affLoss L₀ R a) φ (dirLoss R v) t) ^ 2 ≤
      priorCov μ π (affLoss L₀ R a) φ φ t * responseForm μ π L₀ R a t v v := by
  have hv := bdd_dirLoss hR v
  have hcs := h.abs_tiltCov_le hφ hv t 0
  have hA := h.tiltCov_self_nonneg hφ t 0
  have hB := h.tiltCov_self_nonneg hv t 0
  simp only [responseForm, priorCov_eq_tiltCov_zero (R := fun _ ↦ (0 : ℝ))]
  have hsq : tiltCov μ (baseWeight π (affLoss L₀ R a) t) φ (dirLoss R v) (fun _ ↦ 0) t 0 ^ 2 ≤
      tiltCov μ (baseWeight π (affLoss L₀ R a) t) φ φ (fun _ ↦ 0) t 0 *
        tiltCov μ (baseWeight π (affLoss L₀ R a) t) (dirLoss R v) (dirLoss R v)
          (fun _ ↦ 0) t 0 := by
    calc _ = |tiltCov μ (baseWeight π (affLoss L₀ R a) t) φ (dirLoss R v) (fun _ ↦ 0) t 0| ^ 2 :=
          (sq_abs _).symm
      _ ≤ (Real.sqrt (tiltCov μ (baseWeight π (affLoss L₀ R a) t) φ φ (fun _ ↦ 0) t 0) *
            Real.sqrt (tiltCov μ (baseWeight π (affLoss L₀ R a) t) (dirLoss R v) (dirLoss R v)
              (fun _ ↦ 0) t 0)) ^ 2 := pow_le_pow_left₀ (abs_nonneg _) hcs 2
      _ = _ := by rw [mul_pow, Real.sq_sqrt hA, Real.sq_sqrt hB]
  calc (t * tiltCov μ (baseWeight π (affLoss L₀ R a) t) φ (dirLoss R v) (fun _ ↦ 0) t 0) ^ 2
      = t ^ 2 * tiltCov μ (baseWeight π (affLoss L₀ R a) t) φ (dirLoss R v) (fun _ ↦ 0) t 0 ^ 2 :=
        by ring
    _ ≤ t ^ 2 * (tiltCov μ (baseWeight π (affLoss L₀ R a) t) φ φ (fun _ ↦ 0) t 0 *
          tiltCov μ (baseWeight π (affLoss L₀ R a) t) (dirLoss R v) (dirLoss R v)
            (fun _ ↦ 0) t 0) := mul_le_mul_of_nonneg_left hsq (sq_nonneg t)
    _ = _ := by ring

end Affine

end Laplace.Multi
