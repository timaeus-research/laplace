/-
Copyright (c) 2026 Timaeus Research. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniel Murfet
-/
import Mathlib
import Laplace.Multi.ResponseMap

/-!
# The response map along an arbitrary path of losses, and exponential-family data paths

The mixture (m-geodesic) paths of `ResponseMap` have affine losses. A general path `s ↦ q_s` on the
data manifold induces a general path of losses `s ↦ L_s = E_{q_s}[ℓ]`, and the **master
fluctuation–response identity** is

  `d/ds ⟨φ⟩_{t, L_s} = −t Cov_{t, L_s}(φ, L̇_s)`   (`PathData.hasDerivAt_priorExp`)

for any `C¹` path of bounded losses with bounded derivative (`PathData`). The mixture identity is
the case `L̇_s = Δ` (`PathData.mixture`).

The **e-geodesic** (exponential family) data path `q_s ∝ e^{s a} q₀` with sufficient statistic
`a` is itself an exponential tilt on the data side, so its loss path is a tilted data expectation,
`L_s(w) = E_{q_s}[ℓ(w, ·)]`, with derivative the data covariance
`L̇_s(w) = Cov_{q_s}(ℓ(w, ·), a)` (`eLoss_hasDerivAt`): the same interpolation identity governs
both sides of the response map. Consequently

  `d/ds ⟨φ⟩_{t, q_s} = −t Cov_{t, L_s}(φ, Cov_{q_s}(ℓ, a))`   (`hasDerivAt_priorExp_eGeodesic`):

the response of an observable to an exponential-family deformation of the data is minus `t` times
the posterior covariance of the observable with the data covariance of the loss and the sufficient
statistic. Unlike the mixture case the loss path is not affine, so `s ↦ ⟨φ⟩_s` is a curved path of
posteriors; its second derivative acquires the curvature term `−t Cov(φ, L̈_s)` on top of
`t² κ₃(φ, L̇_s, L̇_s)`.
-/

open MeasureTheory Filter Topology

namespace Laplace.Multi

variable {X : Type*} [MeasurableSpace X] {μ : Measure X}

/-- A bounded observable has a bounded tilted expectation. -/
theorem TiltData.abs_tiltExp_le_of_bound [Nonempty X] {ν R : X → ℝ} {M : ℝ}
    (h : TiltData μ ν R M) {f : X → ℝ} (hfm : Measurable f) {Mf : ℝ} (hf : ∀ x, |f x| ≤ Mf)
    (t u : ℝ) : |tiltExp μ ν f R t u| ≤ Mf := by
  have hZ := h.tiltNum_one_pos t u
  have hMf : 0 ≤ Mf := le_trans (abs_nonneg _) (hf (Classical.arbitrary X))
  unfold tiltExp
  rw [abs_div, abs_of_pos hZ, div_le_iff₀ hZ]
  calc |tiltNum μ ν f R t u| ≤ ∫ x, |f x * Real.exp (-(t * R x * u)) * ν x| ∂μ :=
        abs_integral_le_integral_abs
    _ ≤ ∫ x, Mf * ((fun _ ↦ (1 : ℝ)) x * Real.exp (-(t * R x * u)) * ν x) ∂μ := by
        refine integral_mono (h.integrable_tilt hfm hf t u).abs
          ((h.integrable_tilt measurable_const (Mf := 1) (fun _ ↦ by simp) t u).const_mul Mf)
          fun x ↦ ?_
        beta_reduce
        rw [abs_mul, abs_mul, Real.abs_exp, abs_of_nonneg (h.ν_nonneg x), one_mul]
        exact (mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_right (hf x) (Real.exp_pos _).le) (h.ν_nonneg x)).trans_eq
          (mul_assoc _ _ _)
    _ = Mf * tiltNum μ ν (fun _ ↦ 1) R t u := by rw [integral_const_mul]; rfl

/-! ### A `C¹` path of bounded losses -/

/-- A `C¹` path of losses `s ↦ L s` on the parameter interval `(−S, S)`, bounded by `ML`, with
derivative `L'` bounded by `M'`, over a nonnegative integrable prior `π` of positive mass. -/
structure PathData (μ : Measure X) (π : X → ℝ) (L L' : ℝ → X → ℝ) (S ML M' : ℝ) : Prop where
  π_meas : Measurable π
  π_int : Integrable π μ
  π_nonneg : ∀ x, 0 ≤ π x
  π_pos : 0 < ∫ x, π x ∂μ
  L_meas : ∀ s, Measurable (L s)
  L'_meas : ∀ s, Measurable (L' s)
  L_bound : ∀ s ∈ Set.Ioo (-S) S, ∀ x, |L s x| ≤ ML
  L'_bound : ∀ s ∈ Set.Ioo (-S) S, ∀ x, |L' s x| ≤ M'
  hasDeriv : ∀ x, ∀ s ∈ Set.Ioo (-S) S, HasDerivAt (fun s ↦ L s x) (L' s x) s

namespace PathData

variable {π : X → ℝ} {L L' : ℝ → X → ℝ} {S ML M' : ℝ}

theorem exp_le (h : PathData μ π L L' S ML M') (t : ℝ) {s : ℝ} (hs : s ∈ Set.Ioo (-S) S)
    (x : X) : Real.exp (-(t * L s x)) ≤ Real.exp (|t| * ML) := by
  rw [Real.exp_le_exp]
  calc -(t * L s x) ≤ |t * L s x| := neg_le_abs _
    _ = |t| * |L s x| := abs_mul _ _
    _ ≤ |t| * ML := mul_le_mul_of_nonneg_left (h.L_bound s hs x) (abs_nonneg t)

theorem measurable_integrand (h : PathData μ π L L' S ML M') {f : X → ℝ} (hf : Measurable f)
    (t s : ℝ) : Measurable fun x ↦ f x * Real.exp (-(t * L s x)) * π x :=
  (hf.mul (Real.measurable_exp.comp ((h.L_meas s).const_mul t).neg)).mul h.π_meas

theorem integrable_integrand (h : PathData μ π L L' S ML M') {f : X → ℝ} (hf : Measurable f)
    {Mf : ℝ} (hfb : ∀ x, |f x| ≤ Mf) (t : ℝ) {s : ℝ} (hs : s ∈ Set.Ioo (-S) S) :
    Integrable (fun x ↦ f x * Real.exp (-(t * L s x)) * π x) μ := by
  refine h.π_int.bdd_mul (c := Mf * Real.exp (|t| * ML))
    (hf.mul (Real.measurable_exp.comp ((h.L_meas s).const_mul t).neg)).aestronglyMeasurable
    (Filter.Eventually.of_forall fun x ↦ ?_)
  rw [Real.norm_eq_abs, abs_mul, Real.abs_exp]
  exact mul_le_mul (hfb x) (h.exp_le t hs x) (Real.exp_pos _).le
    (le_trans (abs_nonneg _) (hfb x))

/-- The path partition function is positive. -/
theorem priorZ_pos (h : PathData μ π L L' S ML M') (t : ℝ) {s : ℝ} (hs : s ∈ Set.Ioo (-S) S) :
    0 < priorZ μ π (L s) t := by
  unfold priorZ
  have hlow : Real.exp (-(|t| * ML)) * ∫ x, π x ∂μ ≤
      ∫ x, Real.exp (-(t * L s x)) * π x ∂μ := by
    rw [← integral_const_mul]
    have hint := h.integrable_integrand (f := fun _ ↦ (1 : ℝ)) measurable_const (Mf := 1)
      (fun _ ↦ by simp) t hs
    simp only [one_mul] at hint
    refine integral_mono (h.π_int.const_mul _) hint fun x ↦ ?_
    refine mul_le_mul_of_nonneg_right ?_ (h.π_nonneg x)
    rw [Real.exp_le_exp]
    calc -(|t| * ML) ≤ -|t * L s x| := by
          rw [abs_mul]
          exact neg_le_neg (mul_le_mul_of_nonneg_left (h.L_bound s hs x) (abs_nonneg t))
      _ ≤ -(t * L s x) := neg_le_neg (le_abs_self _)
  exact lt_of_lt_of_le (mul_pos (Real.exp_pos _) h.π_pos) hlow

/-- `d/ds ∫ f e^{-tL_s} π = −t ∫ f L̇_s e^{-tL_s} π`. -/
theorem hasDerivAt_num (h : PathData μ π L L' S ML M') {f : X → ℝ} (hf : Measurable f) {Mf : ℝ}
    (hfb : ∀ x, |f x| ≤ Mf) (t : ℝ) {s₀ : ℝ} (hs₀ : s₀ ∈ Set.Ioo (-S) S) :
    HasDerivAt (fun s ↦ ∫ x, f x * Real.exp (-(t * L s x)) * π x ∂μ)
      (-t * ∫ x, (f x * L' s₀ x) * Real.exp (-(t * L s₀ x)) * π x ∂μ) s₀ := by
  have hmeasF : ∀ᶠ s in 𝓝 s₀,
      AEStronglyMeasurable (fun x ↦ f x * Real.exp (-(t * L s x)) * π x) μ :=
    Filter.Eventually.of_forall fun s ↦ (h.measurable_integrand hf t s).aestronglyMeasurable
  have hint := h.integrable_integrand hf hfb t hs₀
  have hmeasF' : AEStronglyMeasurable
      (fun x ↦ f x * (Real.exp (-(t * L s₀ x)) * (-(t * L' s₀ x))) * π x) μ :=
    ((hf.mul ((Real.measurable_exp.comp ((h.L_meas s₀).const_mul t).neg).mul
      ((h.L'_meas s₀).const_mul t).neg)).mul h.π_meas).aestronglyMeasurable
  have hbound_int : Integrable (fun x ↦ (Mf * (Real.exp (|t| * ML) * (|t| * M'))) * π x) μ :=
    h.π_int.const_mul _
  have hbound : ∀ᵐ x ∂μ, ∀ s ∈ Set.Ioo (-S) S,
      ‖f x * (Real.exp (-(t * L s x)) * (-(t * L' s x))) * π x‖ ≤
        (Mf * (Real.exp (|t| * ML) * (|t| * M'))) * π x := by
    refine Filter.Eventually.of_forall fun x s hs ↦ ?_
    rw [Real.norm_eq_abs, abs_mul, abs_mul, abs_mul, Real.abs_exp, abs_neg, abs_mul,
      abs_of_nonneg (h.π_nonneg x)]
    have h1 : |f x| * (Real.exp (-(t * L s x)) * (|t| * |L' s x|)) ≤
        Mf * (Real.exp (|t| * ML) * (|t| * M')) := by
      have := h.exp_le t hs x
      have := h.L'_bound s hs x
      have := hfb x
      have hMf : 0 ≤ Mf := le_trans (abs_nonneg _) (hfb x)
      gcongr
    exact mul_le_mul_of_nonneg_right h1 (h.π_nonneg x)
  have hdiff : ∀ᵐ x ∂μ, ∀ s ∈ Set.Ioo (-S) S,
      HasDerivAt (fun s ↦ f x * Real.exp (-(t * L s x)) * π x)
        (f x * (Real.exp (-(t * L s x)) * (-(t * L' s x))) * π x) s := by
    refine Filter.Eventually.of_forall fun x s hs ↦ ?_
    have h1 : HasDerivAt (fun s ↦ -(t * L s x)) (-(t * L' s x)) s :=
      ((h.hasDeriv x s hs).const_mul t).neg
    exact (h1.exp.const_mul (f x)).mul_const (π x)
  have key := hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (F := fun s x ↦ f x * Real.exp (-(t * L s x)) * π x)
    (F' := fun s x ↦ f x * (Real.exp (-(t * L s x)) * (-(t * L' s x))) * π x)
    (s := Set.Ioo (-S) S) (Ioo_mem_nhds hs₀.1 hs₀.2) hmeasF hint hmeasF' hbound hbound_int hdiff
  have hderiv := key.2
  have hrw : (∫ x, f x * (Real.exp (-(t * L s₀ x)) * (-(t * L' s₀ x))) * π x ∂μ) =
      -t * ∫ x, (f x * L' s₀ x) * Real.exp (-(t * L s₀ x)) * π x ∂μ := by
    rw [← integral_const_mul]
    refine integral_congr_ae (Filter.Eventually.of_forall fun x ↦ ?_)
    beta_reduce
    ring
  rw [hrw] at hderiv
  exact hderiv

/-- **The master fluctuation–response identity along a path of losses**:
`d/ds ⟨φ⟩_{t, L_s} = −t Cov_{t, L_s}(φ, L̇_s)`. -/
theorem hasDerivAt_priorExp (h : PathData μ π L L' S ML M') {f : X → ℝ} (hf : Measurable f)
    {Mf : ℝ} (hfb : ∀ x, |f x| ≤ Mf) (t : ℝ) {s₀ : ℝ} (hs₀ : s₀ ∈ Set.Ioo (-S) S) :
    HasDerivAt (fun s ↦ priorExp μ π (L s) f t) (-t * priorCov μ π (L s₀) f (L' s₀) t) s₀ := by
  have hN := h.hasDerivAt_num hf hfb t hs₀
  have hZ := h.hasDerivAt_num (f := fun _ ↦ (1 : ℝ)) measurable_const (Mf := 1)
    (fun _ ↦ by simp) t hs₀
  simp only [one_mul] at hZ
  have hZpos := h.priorZ_pos t hs₀
  unfold priorZ at hZpos
  have hZne := hZpos.ne'
  have hdiv := hN.div hZ hZne
  refine hdiv.congr_deriv ?_
  simp only [priorCov, priorExp, priorZ]
  set N := ∫ x, f x * Real.exp (-(t * L s₀ x)) * π x ∂μ with hN'
  set NL := ∫ x, f x * L' s₀ x * Real.exp (-(t * L s₀ x)) * π x ∂μ with hNL
  set ZL := ∫ x, L' s₀ x * Real.exp (-(t * L s₀ x)) * π x ∂μ with hZL
  set Z := ∫ x, Real.exp (-(t * L s₀ x)) * π x ∂μ with hZ'
  clear_value N NL ZL Z
  field_simp
  ring

/-- The mixture path `L_s = L₀ + sΔ` is a `PathData` on every interval, with `L̇_s = Δ`. -/
theorem mixture {L₀ Δ : X → ℝ} (hπm : Measurable π) (hπi : Integrable π μ)
    (hπ : ∀ x, 0 ≤ π x) (hπpos : 0 < ∫ x, π x ∂μ) (hL₀m : Measurable L₀) {M₀ : ℝ}
    (hL₀ : ∀ x, |L₀ x| ≤ M₀) (hΔm : Measurable Δ) {MΔ : ℝ} (hΔ : ∀ x, |Δ x| ≤ MΔ) (S : ℝ) :
    PathData μ π (pathLoss L₀ Δ) (fun _ ↦ Δ) S (M₀ + S * MΔ) MΔ where
  π_meas := hπm
  π_int := hπi
  π_nonneg := hπ
  π_pos := hπpos
  L_meas s := hL₀m.add (hΔm.const_mul s)
  L'_meas _ := hΔm
  L_bound s hs x := by
    have hS0 : 0 ≤ S := by linarith [hs.1, hs.2]
    have hsS : |s| ≤ S := abs_le.mpr ⟨hs.1.le, hs.2.le⟩
    calc |pathLoss L₀ Δ s x| = |L₀ x + s * Δ x| := rfl
      _ ≤ |L₀ x| + |s| * |Δ x| := by rw [← abs_mul]; exact abs_add_le _ _
      _ ≤ M₀ + S * MΔ := add_le_add (hL₀ x) (mul_le_mul hsS (hΔ x) (abs_nonneg _) hS0)
  L'_bound _ _ x := hΔ x
  hasDeriv x s _ := by
    have h1 : HasDerivAt (fun s : ℝ ↦ s * Δ x) (Δ x) s := by
      simpa using (hasDerivAt_id s).mul_const (Δ x)
    exact (h1.const_add (L₀ x)).congr_deriv rfl

end PathData

/-! ### Exponential-family (e-geodesic) data paths -/

section EGeodesic

variable {Y : Type*} [MeasurableSpace Y] [Nonempty Y] {ν : Measure Y}

/-- The loss path of the e-geodesic `q_s ∝ e^{s a} q₀`: `L_s(w) = E_{q_s}[ℓ(w, ·)]`, as the
tilted data expectation with base density `q₀`, residual `a` and "temperature" `−1`. -/
noncomputable def eLoss (ν : Measure Y) (q₀ a : Y → ℝ) (ℓ : X → Y → ℝ) (s : ℝ) (w : X) : ℝ :=
  tiltExp ν q₀ (ℓ w) a (-1) s

/-- The derivative of the e-geodesic loss path: the data covariance `Cov_{q_s}(ℓ(w, ·), a)`. -/
noncomputable def eLoss' (ν : Measure Y) (q₀ a : Y → ℝ) (ℓ : X → Y → ℝ) (s : ℝ) (w : X) : ℝ :=
  tiltCov ν q₀ (ℓ w) a a (-1) s

omit [MeasurableSpace X] in
/-- `L̇_s(w) = Cov_{q_s}(ℓ(w, ·), a)`: the data side of the response map is the interpolation
identity at temperature `−1`. -/
theorem eLoss_hasDerivAt {q₀ a : Y → ℝ} {Ma : ℝ} (hq : TiltData ν q₀ a Ma) {ℓ : X → Y → ℝ}
    (hℓ : ∀ w, Measurable (ℓ w)) {Mℓ : ℝ} (hℓb : ∀ w y, |ℓ w y| ≤ Mℓ) (w : X) (s : ℝ) :
    HasDerivAt (fun s ↦ eLoss ν q₀ a ℓ s w) (eLoss' ν q₀ a ℓ s w) s := by
  have := hq.hasDerivAt_tiltExp (hℓ w) (hℓb w) (-1) s
  simp only [neg_neg, one_mul] at this
  exact this

omit [MeasurableSpace X] in
theorem abs_eLoss_le {q₀ a : Y → ℝ} {Ma : ℝ} (hq : TiltData ν q₀ a Ma) {ℓ : X → Y → ℝ}
    (hℓ : ∀ w, Measurable (ℓ w)) {Mℓ : ℝ} (hℓb : ∀ w y, |ℓ w y| ≤ Mℓ) (s : ℝ) (w : X) :
    |eLoss ν q₀ a ℓ s w| ≤ Mℓ :=
  hq.abs_tiltExp_le_of_bound (hℓ w) (hℓb w) (-1) s

omit [MeasurableSpace X] in
theorem abs_eLoss'_le {q₀ a : Y → ℝ} {Ma : ℝ} (hq : TiltData ν q₀ a Ma) {ℓ : X → Y → ℝ}
    (hℓ : ∀ w, Measurable (ℓ w)) {Mℓ : ℝ} (hℓb : ∀ w y, |ℓ w y| ≤ Mℓ) (s : ℝ) (w : X) :
    |eLoss' ν q₀ a ℓ s w| ≤ 2 * (Mℓ * Ma) := by
  have hMℓ : 0 ≤ Mℓ := le_trans (abs_nonneg _) (hℓb w (Classical.arbitrary Y))
  have hMa := hq.M_nonneg
  have hm : Measurable fun y ↦ ℓ w y * a y := (hℓ w).mul hq.R_meas
  have h1 : |tiltExp ν q₀ (fun y ↦ ℓ w y * a y) a (-1) s| ≤ Mℓ * Ma :=
    hq.abs_tiltExp_le_of_bound hm
      (fun y ↦ by
        rw [abs_mul]
        exact mul_le_mul (hℓb w y) (hq.R_bound y) (abs_nonneg _) hMℓ) (-1) s
  have h2 := hq.abs_tiltExp_le_of_bound (hℓ w) (hℓb w) (-1) s
  have h3 := hq.abs_tiltExp_le_of_bound hq.R_meas hq.R_bound (-1) s
  unfold eLoss' tiltCov
  calc _ ≤ |tiltExp ν q₀ (fun y ↦ ℓ w y * a y) a (-1) s| +
        |tiltExp ν q₀ (ℓ w) a (-1) s * tiltExp ν q₀ a a (-1) s| := abs_sub _ _
    _ ≤ Mℓ * Ma + Mℓ * Ma := by
        rw [abs_mul]
        exact add_le_add h1 (mul_le_mul h2 h3 (abs_nonneg _) hMℓ)
    _ = 2 * (Mℓ * Ma) := by ring

/-- The e-geodesic loss path is a `PathData`, given the measurability in the parameter of the
data-averaged losses (which follows from joint measurability of `ℓ` and is assumed here). -/
theorem PathData.eGeodesic {π : X → ℝ} (hπm : Measurable π) (hπi : Integrable π μ)
    (hπ : ∀ x, 0 ≤ π x) (hπpos : 0 < ∫ x, π x ∂μ) {q₀ a : Y → ℝ} {Ma : ℝ}
    (hq : TiltData ν q₀ a Ma) {ℓ : X → Y → ℝ} (hℓ : ∀ w, Measurable (ℓ w)) {Mℓ : ℝ}
    (hℓb : ∀ w y, |ℓ w y| ≤ Mℓ) (hLm : ∀ s, Measurable (eLoss ν q₀ a ℓ s))
    (hL'm : ∀ s, Measurable (eLoss' ν q₀ a ℓ s))
    (S : ℝ) : PathData μ π (eLoss ν q₀ a ℓ) (eLoss' ν q₀ a ℓ) S Mℓ (2 * (Mℓ * Ma)) where
  π_meas := hπm
  π_int := hπi
  π_nonneg := hπ
  π_pos := hπpos
  L_meas := hLm
  L'_meas := hL'm
  L_bound s _ w := abs_eLoss_le hq hℓ hℓb s w
  L'_bound s _ w := abs_eLoss'_le hq hℓ hℓb s w
  hasDeriv w s _ := eLoss_hasDerivAt hq hℓ hℓb w s

/-- **The response to an exponential-family deformation of the data**:
`d/ds ⟨φ⟩_{t, q_s} = −t Cov_{t, L_s}(φ, Cov_{q_s}(ℓ, a))`. -/
theorem hasDerivAt_priorExp_eGeodesic {π : X → ℝ} (hπm : Measurable π) (hπi : Integrable π μ)
    (hπ : ∀ x, 0 ≤ π x) (hπpos : 0 < ∫ x, π x ∂μ) {q₀ a : Y → ℝ} {Ma : ℝ}
    (hq : TiltData ν q₀ a Ma) {ℓ : X → Y → ℝ} (hℓ : ∀ w, Measurable (ℓ w)) {Mℓ : ℝ}
    (hℓb : ∀ w y, |ℓ w y| ≤ Mℓ) (hLm : ∀ s, Measurable (eLoss ν q₀ a ℓ s))
    (hL'm : ∀ s, Measurable (eLoss' ν q₀ a ℓ s)) {φ : X → ℝ} (hφ : Bdd φ) (t s₀ : ℝ) :
    HasDerivAt (fun s ↦ priorExp μ π (eLoss ν q₀ a ℓ s) φ t)
      (-t * priorCov μ π (eLoss ν q₀ a ℓ s₀) φ (eLoss' ν q₀ a ℓ s₀) t) s₀ := by
  obtain ⟨hφm, Mφ, hφb⟩ := hφ
  exact (PathData.eGeodesic hπm hπi hπ hπpos hq hℓ hℓb hLm hL'm (|s₀| + 1)).hasDerivAt_priorExp
    hφm hφb t ⟨by linarith [neg_abs_le s₀], by linarith [le_abs_self s₀]⟩

end EGeodesic

end Laplace.Multi
