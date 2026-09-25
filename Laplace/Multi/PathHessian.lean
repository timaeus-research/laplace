/-
Copyright (c) 2026 Timaeus Research. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniel Murfet
-/
import Mathlib
import Laplace.Multi.PathResponse

/-!
# Second derivatives along a path of losses: the path Hessian of the free energy

Along a `C²` path of bounded losses `s ↦ L_s` (`PathData2`) the free energy `F(s) = −log Z_t(L_s)`
has

  `F'(s) = t E_s[L̇_s]`,   `F''(s) = t E_s[L̈_s] − t² Var_s(L̇_s)`

(`PathData.hasDerivAt_pathFreeEnergy`, `PathData2.hasDerivAt_deriv_pathFreeEnergy`), and the
response of an observable has second derivative

  `d²/ds² ⟨φ⟩_s = t² κ₃(φ, L̇_s, L̇_s) − t Cov_s(φ, L̈_s)`
  (`PathData2.hasDerivAt_neg_mul_pathCov`):

the joint third cumulant of the mixture case plus the **curvature term** `−t Cov(φ, L̈_s)` of
a non-affine path. On a mixture line `L̈ = 0` and `F'' = −t² Var(Δ) ≤ 0` (the concavity of
`ResponseMap`); along a curved path the acceleration term `t E_s[L̈_s]` has no sign, so the free
energy need not be concave along e-geodesics of the data. For the e-geodesic `q_s ∝ e^{sa} q₀` the
acceleration is the joint data cumulant `L̈_s(w) = κ₃^{q_s}(ℓ(w,·), a, a)` (`eLoss'_hasDerivAt`),
and the path is a `PathData2` (`PathData2.eGeodesic`).
-/

open MeasureTheory Filter Topology

namespace Laplace.Multi

variable {X : Type*} [MeasurableSpace X] {μ : Measure X}

/-- A bounded pair of observables has a bounded tilted covariance, `|Cov(f, g)| ≤ 2 Mf Mg`. -/
theorem TiltData.abs_tiltCov_le_of_bound [Nonempty X] {ν R : X → ℝ} {M : ℝ}
    (h : TiltData μ ν R M) {f g : X → ℝ} (hfm : Measurable f) (hgm : Measurable g) {Mf Mg : ℝ}
    (hf : ∀ x, |f x| ≤ Mf) (hg : ∀ x, |g x| ≤ Mg) (t u : ℝ) :
    |tiltCov μ ν f g R t u| ≤ 2 * (Mf * Mg) := by
  have hMf : 0 ≤ Mf := le_trans (abs_nonneg _) (hf (Classical.arbitrary X))
  have hm : Measurable fun x ↦ f x * g x := hfm.mul hgm
  have h1 : |tiltExp μ ν (fun x ↦ f x * g x) R t u| ≤ Mf * Mg :=
    h.abs_tiltExp_le_of_bound hm
      (fun x ↦ by rw [abs_mul]; exact mul_le_mul (hf x) (hg x) (abs_nonneg _) hMf) t u
  have h2 := h.abs_tiltExp_le_of_bound hfm hf t u
  have h3 := h.abs_tiltExp_le_of_bound hgm hg t u
  unfold tiltCov
  calc _ ≤ |tiltExp μ ν (fun x ↦ f x * g x) R t u| +
        |tiltExp μ ν f R t u * tiltExp μ ν g R t u| := abs_sub _ _
    _ ≤ Mf * Mg + Mf * Mg := by
        rw [abs_mul]
        exact add_le_add h1 (mul_le_mul h2 h3 (abs_nonneg _) hMf)
    _ = 2 * (Mf * Mg) := by ring

/-- A `C²` path of bounded losses: a `PathData` whose derivative path is `C¹` with bounded
derivative `L''`. -/
structure PathData2 (μ : Measure X) (π : X → ℝ) (L L' L'' : ℝ → X → ℝ) (S ML M' M'' : ℝ) :
    Prop extends PathData μ π L L' S ML M' where
  L''_meas : ∀ s, Measurable (L'' s)
  L''_bound : ∀ s ∈ Set.Ioo (-S) S, ∀ x, |L'' s x| ≤ M''
  hasDeriv' : ∀ x, ∀ s ∈ Set.Ioo (-S) S, HasDerivAt (fun s ↦ L' s x) (L'' s x) s

namespace PathData

variable {π : X → ℝ} {L L' : ℝ → X → ℝ} {S ML M' : ℝ}

/-- `d/ds ∫ f_s e^{-tL_s} π = ∫ (ḟ_s − t f_s L̇_s) e^{-tL_s} π` for a `C¹` family of bounded
observables. -/
theorem hasDerivAt_num' (h : PathData μ π L L' S ML M') {f f' : ℝ → X → ℝ}
    (hf : ∀ s, Measurable (f s)) (hf' : ∀ s, Measurable (f' s)) {Mf Mf' : ℝ}
    (hfb : ∀ s ∈ Set.Ioo (-S) S, ∀ x, |f s x| ≤ Mf)
    (hf'b : ∀ s ∈ Set.Ioo (-S) S, ∀ x, |f' s x| ≤ Mf')
    (hfd : ∀ x, ∀ s ∈ Set.Ioo (-S) S, HasDerivAt (fun s ↦ f s x) (f' s x) s) (t : ℝ) {s₀ : ℝ}
    (hs₀ : s₀ ∈ Set.Ioo (-S) S) :
    HasDerivAt (fun s ↦ ∫ x, f s x * Real.exp (-(t * L s x)) * π x ∂μ)
      (∫ x, (f' s₀ x - t * (f s₀ x * L' s₀ x)) * Real.exp (-(t * L s₀ x)) * π x ∂μ) s₀ := by
  have hmeasF : ∀ᶠ s in 𝓝 s₀,
      AEStronglyMeasurable (fun x ↦ f s x * Real.exp (-(t * L s x)) * π x) μ :=
    Filter.Eventually.of_forall fun s ↦ (h.measurable_integrand (hf s) t s).aestronglyMeasurable
  have hint := h.integrable_integrand (hf s₀) (hfb s₀ hs₀) t hs₀
  have hmeasF' : AEStronglyMeasurable (fun x ↦
      (f' s₀ x * Real.exp (-(t * L s₀ x)) + f s₀ x * (Real.exp (-(t * L s₀ x)) *
        (-(t * L' s₀ x)))) * π x) μ := by
    have he : Measurable fun x ↦ Real.exp (-(t * L s₀ x)) :=
      Real.measurable_exp.comp ((h.L_meas s₀).const_mul t).neg
    exact (((hf' s₀).mul he).add ((hf s₀).mul (he.mul ((h.L'_meas s₀).const_mul t).neg))).mul
      h.π_meas |>.aestronglyMeasurable
  have hbound_int : Integrable
      (fun x ↦ (Mf' * Real.exp (|t| * ML) + Mf * (Real.exp (|t| * ML) * (|t| * M'))) * π x) μ :=
    h.π_int.const_mul _
  have hbound : ∀ᵐ x ∂μ, ∀ s ∈ Set.Ioo (-S) S,
      ‖(f' s x * Real.exp (-(t * L s x)) + f s x * (Real.exp (-(t * L s x)) *
        (-(t * L' s x)))) * π x‖ ≤
        (Mf' * Real.exp (|t| * ML) + Mf * (Real.exp (|t| * ML) * (|t| * M'))) * π x := by
    refine Filter.Eventually.of_forall fun x s hs ↦ ?_
    rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (h.π_nonneg x)]
    refine mul_le_mul_of_nonneg_right ?_ (h.π_nonneg x)
    have he := h.exp_le t hs x
    have hL' := h.L'_bound s hs x
    have hfx := hfb s hs x
    have hf'x := hf'b s hs x
    have hMf : 0 ≤ Mf := le_trans (abs_nonneg _) hfx
    have hMf' : 0 ≤ Mf' := le_trans (abs_nonneg _) hf'x
    calc |f' s x * Real.exp (-(t * L s x)) + f s x * (Real.exp (-(t * L s x)) * (-(t * L' s x)))|
        ≤ |f' s x * Real.exp (-(t * L s x))| +
          |f s x * (Real.exp (-(t * L s x)) * (-(t * L' s x)))| := abs_add_le _ _
      _ = |f' s x| * Real.exp (-(t * L s x)) +
          |f s x| * (Real.exp (-(t * L s x)) * (|t| * |L' s x|)) := by
          rw [abs_mul, abs_mul, abs_mul, abs_neg, abs_mul, Real.abs_exp]
      _ ≤ Mf' * Real.exp (|t| * ML) + Mf * (Real.exp (|t| * ML) * (|t| * M')) := by
          gcongr
  have hdiff : ∀ᵐ x ∂μ, ∀ s ∈ Set.Ioo (-S) S,
      HasDerivAt (fun s ↦ f s x * Real.exp (-(t * L s x)) * π x)
        ((f' s x * Real.exp (-(t * L s x)) + f s x * (Real.exp (-(t * L s x)) *
          (-(t * L' s x)))) * π x) s := by
    refine Filter.Eventually.of_forall fun x s hs ↦ ?_
    have h1 : HasDerivAt (fun s ↦ -(t * L s x)) (-(t * L' s x)) s :=
      ((h.hasDeriv x s hs).const_mul t).neg
    exact ((hfd x s hs).mul h1.exp).mul_const (π x)
  have key := hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (F := fun s x ↦ f s x * Real.exp (-(t * L s x)) * π x)
    (F' := fun s x ↦ (f' s x * Real.exp (-(t * L s x)) + f s x * (Real.exp (-(t * L s x)) *
      (-(t * L' s x)))) * π x)
    (s := Set.Ioo (-S) S) (Ioo_mem_nhds hs₀.1 hs₀.2) hmeasF hint hmeasF' hbound hbound_int hdiff
  refine key.2.congr_deriv ?_
  refine integral_congr_ae (Filter.Eventually.of_forall fun x ↦ ?_)
  beta_reduce
  ring

/-- `F'(s) = t E_s[L̇_s]` for the path free energy `F(s) = −log Z_t(L_s)`. -/
theorem hasDerivAt_pathFreeEnergy (h : PathData μ π L L' S ML M') (t : ℝ) {s₀ : ℝ}
    (hs₀ : s₀ ∈ Set.Ioo (-S) S) :
    HasDerivAt (fun s ↦ -Real.log (priorZ μ π (L s) t)) (t * priorExp μ π (L s₀) (L' s₀) t) s₀ := by
  have hZ := h.hasDerivAt_num (f := fun _ ↦ (1 : ℝ)) measurable_const (Mf := 1)
    (fun _ ↦ by simp) t hs₀
  simp only [one_mul] at hZ
  have hZpos := h.priorZ_pos t hs₀
  unfold priorZ at hZpos ⊢
  refine (hZ.log hZpos.ne').neg.congr_deriv ?_
  unfold priorExp priorZ
  field_simp

end PathData

namespace PathData2

variable {π : X → ℝ} {L L' L'' : ℝ → X → ℝ} {S ML M' M'' : ℝ}

/-- `d/ds E_s[L̇_s] = E_s[L̈_s] − t Var_s(L̇_s)`. -/
theorem hasDerivAt_pathMean (h : PathData2 μ π L L' L'' S ML M' M'') (t : ℝ) {s₀ : ℝ}
    (hs₀ : s₀ ∈ Set.Ioo (-S) S) :
    HasDerivAt (fun s ↦ priorExp μ π (L s) (L' s) t)
      (priorExp μ π (L s₀) (L'' s₀) t - t * priorCov μ π (L s₀) (L' s₀) (L' s₀) t) s₀ := by
  have hp := h.toPathData
  have hN := hp.hasDerivAt_num' (f := L') (f' := L'') hp.L'_meas h.L''_meas hp.L'_bound
    h.L''_bound h.hasDeriv' t hs₀
  have hZ := hp.hasDerivAt_num (f := fun _ ↦ (1 : ℝ)) measurable_const (Mf := 1)
    (fun _ ↦ by simp) t hs₀
  simp only [one_mul] at hZ
  have hZpos := hp.priorZ_pos t hs₀
  unfold priorZ at hZpos
  have hZne := hZpos.ne'
  have hsplit : (∫ x, (L'' s₀ x - t * (L' s₀ x * L' s₀ x)) * Real.exp (-(t * L s₀ x)) * π x ∂μ)
      = (∫ x, L'' s₀ x * Real.exp (-(t * L s₀ x)) * π x ∂μ) -
        t * ∫ x, (L' s₀ x * L' s₀ x) * Real.exp (-(t * L s₀ x)) * π x ∂μ := by
    have i1 := hp.integrable_integrand (h.L''_meas s₀) (h.L''_bound s₀ hs₀) t hs₀
    have hm : Measurable fun x ↦ L' s₀ x * L' s₀ x := (hp.L'_meas s₀).mul (hp.L'_meas s₀)
    have i2 := hp.integrable_integrand hm (Mf := M' * M')
      (fun x ↦ by
        rw [abs_mul]
        exact mul_le_mul (hp.L'_bound s₀ hs₀ x) (hp.L'_bound s₀ hs₀ x) (abs_nonneg _)
          (le_trans (abs_nonneg _) (hp.L'_bound s₀ hs₀ x))) t hs₀
    have i2' : Integrable (fun x ↦ t * (L' s₀ x * L' s₀ x * Real.exp (-(t * L s₀ x)) * π x)) μ :=
      i2.const_mul t
    rw [← integral_const_mul, ← integral_sub i1 i2']
    refine integral_congr_ae (Filter.Eventually.of_forall fun x ↦ ?_)
    beta_reduce
    ring
  rw [hsplit] at hN
  have hdiv := hN.div hZ hZne
  refine hdiv.congr_deriv ?_
  simp only [priorCov, priorExp, priorZ]
  set N := ∫ x, L' s₀ x * Real.exp (-(t * L s₀ x)) * π x ∂μ with hN'
  set N2 := ∫ x, L'' s₀ x * Real.exp (-(t * L s₀ x)) * π x ∂μ with hN2
  set NLL := ∫ x, L' s₀ x * L' s₀ x * Real.exp (-(t * L s₀ x)) * π x ∂μ with hNLL
  set Z := ∫ x, Real.exp (-(t * L s₀ x)) * π x ∂μ with hZ'
  clear_value N N2 NLL Z
  field_simp
  ring

/-- **The path Hessian of the free energy**: `F''(s) = t E_s[L̈_s] − t² Var_s(L̇_s)`. -/
theorem hasDerivAt_deriv_pathFreeEnergy (h : PathData2 μ π L L' L'' S ML M' M'') (t : ℝ)
    {s₀ : ℝ} (hs₀ : s₀ ∈ Set.Ioo (-S) S) :
    HasDerivAt (fun s ↦ t * priorExp μ π (L s) (L' s) t)
      (t * priorExp μ π (L s₀) (L'' s₀) t - t ^ 2 * priorCov μ π (L s₀) (L' s₀) (L' s₀) t) s₀ :=
  ((h.hasDerivAt_pathMean t hs₀).const_mul t).congr_deriv (by ring)

/-- **The second derivative of the response along a `C²` path**:
`d²/ds² ⟨φ⟩_s = t² κ₃(φ, L̇_s, L̇_s) − t Cov_s(φ, L̈_s)`. -/
theorem hasDerivAt_neg_mul_pathCov [Nonempty X] (h : PathData2 μ π L L' L'' S ML M' M'')
    {φ : X → ℝ}
    (hφm : Measurable φ) {Mφ : ℝ} (hφ : ∀ x, |φ x| ≤ Mφ) (t : ℝ) {s₀ : ℝ}
    (hs₀ : s₀ ∈ Set.Ioo (-S) S) :
    HasDerivAt (fun s ↦ -t * priorCov μ π (L s) φ (L' s) t)
      (t ^ 2 * (priorExp μ π (L s₀) (fun x ↦ φ x * L' s₀ x * L' s₀ x) t
        - 2 * priorExp μ π (L s₀) (L' s₀) t * priorExp μ π (L s₀) (fun x ↦ φ x * L' s₀ x) t
        - priorExp μ π (L s₀) φ t * priorExp μ π (L s₀) (fun x ↦ L' s₀ x * L' s₀ x) t
        + 2 * priorExp μ π (L s₀) φ t * priorExp μ π (L s₀) (L' s₀) t ^ 2)
        - t * priorCov μ π (L s₀) φ (L'' s₀) t) s₀ := by
  have hp := h.toPathData
  have hMφ : 0 ≤ Mφ := le_trans (abs_nonneg _) (hφ (Classical.arbitrary X))
  -- derivative of `E_s[φ L̇_s]`
  have hA : HasDerivAt (fun s ↦ priorExp μ π (L s) (fun x ↦ φ x * L' s x) t)
      (priorExp μ π (L s₀) (fun x ↦ φ x * L'' s₀ x) t -
        t * (priorExp μ π (L s₀) (fun x ↦ φ x * L' s₀ x * L' s₀ x) t -
          priorExp μ π (L s₀) (fun x ↦ φ x * L' s₀ x) t * priorExp μ π (L s₀) (L' s₀) t)) s₀ := by
    have hm1 : ∀ s, Measurable fun x ↦ φ x * L' s x := fun s ↦ hφm.mul (hp.L'_meas s)
    have hm2 : ∀ s, Measurable fun x ↦ φ x * L'' s x := fun s ↦ hφm.mul (h.L''_meas s)
    have hN := hp.hasDerivAt_num' (f := fun s x ↦ φ x * L' s x) (f' := fun s x ↦ φ x * L'' s x)
      hm1 hm2 (Mf := Mφ * M')
      (fun s hs x ↦ by
        rw [abs_mul]
        exact mul_le_mul (hφ x) (hp.L'_bound s hs x) (abs_nonneg _) hMφ) (Mf' := Mφ * M'')
      (fun s hs x ↦ by
        rw [abs_mul]
        exact mul_le_mul (hφ x) (h.L''_bound s hs x) (abs_nonneg _) hMφ)
      (fun x s hs ↦ (h.hasDeriv' x s hs).const_mul (φ x)) t hs₀
    have hZ := hp.hasDerivAt_num (f := fun _ ↦ (1 : ℝ)) measurable_const (Mf := 1)
      (fun _ ↦ by simp) t hs₀
    simp only [one_mul] at hZ
    have hZpos := hp.priorZ_pos t hs₀
    unfold priorZ at hZpos
    have hZne := hZpos.ne'
    have hsplit : (∫ x, (φ x * L'' s₀ x - t * (φ x * L' s₀ x * L' s₀ x)) *
        Real.exp (-(t * L s₀ x)) * π x ∂μ) =
        (∫ x, (φ x * L'' s₀ x) * Real.exp (-(t * L s₀ x)) * π x ∂μ) -
          t * ∫ x, (φ x * L' s₀ x * L' s₀ x) * Real.exp (-(t * L s₀ x)) * π x ∂μ := by
      have i1 := hp.integrable_integrand (hm2 s₀) (Mf := Mφ * M'')
        (fun x ↦ by
          rw [abs_mul]
          exact mul_le_mul (hφ x) (h.L''_bound s₀ hs₀ x) (abs_nonneg _) hMφ) t hs₀
      have hm3 : Measurable fun x ↦ φ x * L' s₀ x * L' s₀ x := (hm1 s₀).mul (hp.L'_meas s₀)
      have i2 := hp.integrable_integrand hm3 (Mf := Mφ * M' * M')
        (fun x ↦ by
          rw [abs_mul, abs_mul]
          exact mul_le_mul (mul_le_mul (hφ x) (hp.L'_bound s₀ hs₀ x) (abs_nonneg _) hMφ)
            (hp.L'_bound s₀ hs₀ x) (abs_nonneg _)
            (mul_nonneg hMφ (le_trans (abs_nonneg _) (hp.L'_bound s₀ hs₀ x)))) t hs₀
      have i2' : Integrable
          (fun x ↦ t * (φ x * L' s₀ x * L' s₀ x * Real.exp (-(t * L s₀ x)) * π x)) μ :=
        i2.const_mul t
      rw [← integral_const_mul, ← integral_sub i1 i2']
      refine integral_congr_ae (Filter.Eventually.of_forall fun x ↦ ?_)
      beta_reduce
      ring
    rw [hsplit] at hN
    have hdiv := hN.div hZ hZne
    refine hdiv.congr_deriv ?_
    simp only [priorExp, priorZ]
    set N := ∫ x, φ x * L' s₀ x * Real.exp (-(t * L s₀ x)) * π x ∂μ with hN'
    set N2 := ∫ x, φ x * L'' s₀ x * Real.exp (-(t * L s₀ x)) * π x ∂μ with hN2
    set NLL := ∫ x, φ x * L' s₀ x * L' s₀ x * Real.exp (-(t * L s₀ x)) * π x ∂μ with hNLL
    set NL := ∫ x, L' s₀ x * Real.exp (-(t * L s₀ x)) * π x ∂μ with hNL
    set Z := ∫ x, Real.exp (-(t * L s₀ x)) * π x ∂μ with hZ'
    clear_value N N2 NLL NL Z
    field_simp
    ring
  have hB := hp.hasDerivAt_priorExp hφm hφ t hs₀
  have hC := h.hasDerivAt_pathMean t hs₀
  have hfun : (fun s ↦ -t * priorCov μ π (L s) φ (L' s) t) = fun s ↦
      -t * (priorExp μ π (L s) (fun x ↦ φ x * L' s x) t -
        priorExp μ π (L s) φ t * priorExp μ π (L s) (L' s) t) := by
    funext s
    rfl
  rw [hfun]
  refine ((hA.sub (hB.mul hC)).const_mul (-t)).congr_deriv ?_
  unfold priorCov
  ring

end PathData2

/-! ### The e-geodesic is a `C²` path: the acceleration is a joint data cumulant -/

section EGeodesic

variable {Y : Type*} [MeasurableSpace Y] [Nonempty Y] {ν : Measure Y}

/-- The second derivative of the e-geodesic loss path: the joint third cumulant
`κ₃^{q_s}(ℓ(w,·), a, a) = Cov(ℓa, a) − Cov(ℓ, a) E[a] − E[ℓ] Var(a)`. -/
noncomputable def eLoss'' (ν : Measure Y) (q₀ a : Y → ℝ) (ℓ : X → Y → ℝ) (s : ℝ) (w : X) : ℝ :=
  tiltCov ν q₀ (fun y ↦ ℓ w y * a y) a a (-1) s -
    tiltCov ν q₀ (ℓ w) a a (-1) s * tiltExp ν q₀ a a (-1) s -
    tiltExp ν q₀ (ℓ w) a (-1) s * tiltCov ν q₀ a a a (-1) s

omit [MeasurableSpace X] in
/-- `L̈_s(w) = κ₃^{q_s}(ℓ(w,·), a, a)`. -/
theorem eLoss'_hasDerivAt {q₀ a : Y → ℝ} {Ma : ℝ} (hq : TiltData ν q₀ a Ma) {ℓ : X → Y → ℝ}
    (hℓ : ∀ w, Measurable (ℓ w)) {Mℓ : ℝ} (hℓb : ∀ w y, |ℓ w y| ≤ Mℓ) (w : X) (s : ℝ) :
    HasDerivAt (fun s ↦ eLoss' ν q₀ a ℓ s w) (eLoss'' ν q₀ a ℓ s w) s := by
  have hMℓ : 0 ≤ Mℓ := le_trans (abs_nonneg _) (hℓb w (Classical.arbitrary Y))
  have hm : Measurable fun y ↦ ℓ w y * a y := (hℓ w).mul hq.R_meas
  have d1 := hq.hasDerivAt_tiltExp hm (Mf := Mℓ * Ma)
    (fun y ↦ by
      rw [abs_mul]
      exact mul_le_mul (hℓb w y) (hq.R_bound y) (abs_nonneg _) hMℓ) (-1) s
  have d2 := hq.hasDerivAt_tiltExp (hℓ w) (hℓb w) (-1) s
  have d3 := hq.hasDerivAt_tiltExp hq.R_meas hq.R_bound (-1) s
  unfold eLoss' tiltCov
  refine (d1.sub (d2.mul d3)).congr_deriv ?_
  unfold eLoss'' tiltCov
  ring

omit [MeasurableSpace X] in
theorem abs_eLoss''_le {q₀ a : Y → ℝ} {Ma : ℝ} (hq : TiltData ν q₀ a Ma) {ℓ : X → Y → ℝ}
    (hℓ : ∀ w, Measurable (ℓ w)) {Mℓ : ℝ} (hℓb : ∀ w y, |ℓ w y| ≤ Mℓ) (s : ℝ) (w : X) :
    |eLoss'' ν q₀ a ℓ s w| ≤ 6 * (Mℓ * (Ma * Ma)) := by
  have hMℓ : 0 ≤ Mℓ := le_trans (abs_nonneg _) (hℓb w (Classical.arbitrary Y))
  have hMa := hq.M_nonneg
  have hm : Measurable fun y ↦ ℓ w y * a y := (hℓ w).mul hq.R_meas
  have hmb : ∀ y, |ℓ w y * a y| ≤ Mℓ * Ma := fun y ↦ by
    rw [abs_mul]
    exact mul_le_mul (hℓb w y) (hq.R_bound y) (abs_nonneg _) hMℓ
  have c1 := hq.abs_tiltCov_le_of_bound hm hq.R_meas hmb hq.R_bound (-1) s
  have c2 := hq.abs_tiltCov_le_of_bound (hℓ w) hq.R_meas (hℓb w) hq.R_bound (-1) s
  have e3 := hq.abs_tiltExp_le_of_bound hq.R_meas hq.R_bound (-1) s
  have e2 := hq.abs_tiltExp_le_of_bound (hℓ w) (hℓb w) (-1) s
  have c3 := hq.abs_tiltCov_le_of_bound hq.R_meas hq.R_meas hq.R_bound hq.R_bound (-1) s
  unfold eLoss''
  calc _ ≤ |tiltCov ν q₀ (fun y ↦ ℓ w y * a y) a a (-1) s -
        tiltCov ν q₀ (ℓ w) a a (-1) s * tiltExp ν q₀ a a (-1) s| +
        |tiltExp ν q₀ (ℓ w) a (-1) s * tiltCov ν q₀ a a a (-1) s| := abs_sub _ _
    _ ≤ (|tiltCov ν q₀ (fun y ↦ ℓ w y * a y) a a (-1) s| +
        |tiltCov ν q₀ (ℓ w) a a (-1) s * tiltExp ν q₀ a a (-1) s|) +
        |tiltExp ν q₀ (ℓ w) a (-1) s * tiltCov ν q₀ a a a (-1) s| :=
        add_le_add (abs_sub _ _) le_rfl
    _ ≤ (2 * (Mℓ * Ma * Ma) + 2 * (Mℓ * Ma) * Ma) + Mℓ * (2 * (Ma * Ma)) := by
        rw [abs_mul, abs_mul]
        refine add_le_add (add_le_add c1 (mul_le_mul c2 e3 (abs_nonneg _) (by positivity)))
          (mul_le_mul e2 c3 (abs_nonneg _) hMℓ)
    _ = 6 * (Mℓ * (Ma * Ma)) := by ring

/-- The e-geodesic loss path is a `PathData2`. -/
theorem PathData2.eGeodesic {π : X → ℝ} (hπm : Measurable π) (hπi : Integrable π μ)
    (hπ : ∀ x, 0 ≤ π x) (hπpos : 0 < ∫ x, π x ∂μ) {q₀ a : Y → ℝ} {Ma : ℝ}
    (hq : TiltData ν q₀ a Ma) {ℓ : X → Y → ℝ} (hℓ : ∀ w, Measurable (ℓ w)) {Mℓ : ℝ}
    (hℓb : ∀ w y, |ℓ w y| ≤ Mℓ) (hLm : ∀ s, Measurable (eLoss ν q₀ a ℓ s))
    (hL'm : ∀ s, Measurable (eLoss' ν q₀ a ℓ s)) (hL''m : ∀ s, Measurable (eLoss'' ν q₀ a ℓ s))
    (S : ℝ) :
    PathData2 μ π (eLoss ν q₀ a ℓ) (eLoss' ν q₀ a ℓ) (eLoss'' ν q₀ a ℓ) S Mℓ (2 * (Mℓ * Ma))
      (6 * (Mℓ * (Ma * Ma))) where
  toPathData := PathData.eGeodesic hπm hπi hπ hπpos hq hℓ hℓb hLm hL'm S
  L''_meas := hL''m
  L''_bound s _ w := abs_eLoss''_le hq hℓ hℓb s w
  hasDeriv' w s _ := eLoss'_hasDerivAt hq hℓ hℓb w s

end EGeodesic

end Laplace.Multi
