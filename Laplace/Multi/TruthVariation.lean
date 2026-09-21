/-
Copyright (c) 2026 Timaeus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib
import Laplace.Multi.TiltCauchySchwarz
import Laplace.Multi.EmpiricalRelative

/-!
# Variations of the truth: the fixed-temperature map is differentiable, uniformly in the test

The population loss is affine in the true distribution, `L_q(w) = -∫ q log p_w`
(`popLoss_mix`), so a variation of the truth is a variation `L ↦ L + R` of the loss. At a fixed
temperature the normalised expectations respond through the tilt of `TiltInterpolation`:
`d/du ⟨f⟩_{L+uR,t} = -t Cov_{L+uR,t}(f, R)`. Here that one-directional identity is upgraded to the
quadratic remainder bound, uniform over bounded tests (`TiltData.abs_tiltExp_taylor_le`):
`|⟨f⟩_{L+R} - ⟨f⟩_L + t Cov_L(f, R)| ≤ 6 t² ‖f‖∞ ‖R‖∞²`.
Uniformity in `‖f‖∞ ≤ 1` is the total-variation form of Fréchet differentiability of
`L ↦ μ_{L,t}` with derivative `-t (R - μ(R)) μ` (Astra, `research_truth_variation_v1`, Level 1);
the proof is the second derivative of the tilt, `t² [Cov(fR,R) - Cov(f,R) E R - E f Var R]`, bounded
by `6 t² ‖f‖∞ ‖R‖∞²` (`TiltData.hasDerivAt_tiltCov`), and two mean-value steps.

In the window setting (`tiltExp_window_eq`) the tilt at parameter `u` is the normalised
expectation of `L + u(K - L)`, so the bound reads, for an empirical or perturbed loss `K` within `δ`
of `L` on the window (`nmoment_taylor_le`):
`|⟨φ⟩_{K,t} - ⟨φ⟩_{L,t} + t Cov_{L,t}(φ, K - L)| ≤ 6 t² ‖φ‖∞ δ²`,
and for a finite mixture of truths `q_θ = Σ θ_i q_i`, `L_θ = Σ θ_i L_i`, the partial derivatives are
`∂_{θ_i} ⟨φ⟩_{θ,t} = -t Cov_{θ,t}(φ, L_i)` (`hasDerivAt_nmoment_mixture`): the Bayesian influence
function of the mixture weights. All bounds carry the factor `t`: nothing here is uniform as
`t → ∞`, which is why S6's temperature windows are what they are.
-/

open MeasureTheory Set

namespace Laplace.Multi

variable {X : Type*} [MeasurableSpace X] {μ : Measure X} [Nonempty X]

/-! ### Bounded tests: bounds on the tilted expectation and covariance -/

theorem TiltData.abs_tiltExp_le {ν R : X → ℝ} {M : ℝ} (h : TiltData μ ν R M) {f : X → ℝ}
    (_hfm : Measurable f) {Mf : ℝ} (hf : ∀ x, |f x| ≤ Mf) (t u : ℝ) :
    |tiltExp μ ν f R t u| ≤ Mf := by
  have hMf : 0 ≤ Mf := le_trans (abs_nonneg _) (hf (Classical.arbitrary X))
  have hpos := h.tiltNum_one_pos t u
  unfold tiltExp
  rw [abs_div, abs_of_pos hpos, div_le_iff₀ hpos]
  have hone : Integrable (fun x ↦ Mf * ((fun _ ↦ (1 : ℝ)) x * Real.exp (-(t * R x * u)) * ν x)) μ :=
    (h.integrable_tilt (f := fun _ ↦ (1 : ℝ)) measurable_const (Mf := 1) (fun _ ↦ by simp) t u)
      |>.const_mul Mf
  have hb := norm_integral_le_of_norm_le (μ := μ)
    (f := fun x ↦ f x * Real.exp (-(t * R x * u)) * ν x) hone
    (Filter.Eventually.of_forall fun x ↦ by
      rw [Real.norm_eq_abs, abs_mul, abs_mul, Real.abs_exp, abs_of_nonneg (h.ν_nonneg x)]
      have := hf x
      have := h.ν_nonneg x
      have := (Real.exp_pos (-(t * R x * u))).le
      simp only [one_mul]
      nlinarith [mul_nonneg this (h.ν_nonneg x)])
  rw [Real.norm_eq_abs] at hb
  unfold tiltNum
  rw [integral_const_mul] at hb
  simpa using hb

theorem TiltData.abs_tiltCov_le_of_bdd {ν R : X → ℝ} {M : ℝ} (h : TiltData μ ν R M)
    {f g : X → ℝ} (hfm : Measurable f) {Mf : ℝ} (hf : ∀ x, |f x| ≤ Mf) (hgm : Measurable g)
    {Mg : ℝ} (hg : ∀ x, |g x| ≤ Mg) (t u : ℝ) :
    |tiltCov μ ν f g R t u| ≤ 2 * Mf * Mg := by
  have hMf : 0 ≤ Mf := le_trans (abs_nonneg _) (hf (Classical.arbitrary X))
  have hMg : 0 ≤ Mg := le_trans (abs_nonneg _) (hg (Classical.arbitrary X))
  have h1 : |tiltExp μ ν (fun x ↦ f x * g x) R t u| ≤ Mf * Mg :=
    h.abs_tiltExp_le (hfm.mul hgm) (fun x ↦ by
      simp only [Pi.mul_apply, abs_mul]
      exact mul_le_mul (hf x) (hg x) (abs_nonneg _) hMf) t u
  have h2 : |tiltExp μ ν f R t u * tiltExp μ ν g R t u| ≤ Mf * Mg := by
    rw [abs_mul]
    exact mul_le_mul (h.abs_tiltExp_le hfm hf t u) (h.abs_tiltExp_le hgm hg t u) (abs_nonneg _)
      hMf
  unfold tiltCov
  calc |tiltExp μ ν (fun x ↦ f x * g x) R t u - tiltExp μ ν f R t u * tiltExp μ ν g R t u|
      ≤ |tiltExp μ ν (fun x ↦ f x * g x) R t u| + |tiltExp μ ν f R t u * tiltExp μ ν g R t u| :=
        abs_sub _ _
    _ ≤ Mf * Mg + Mf * Mg := add_le_add h1 h2
    _ = 2 * Mf * Mg := by ring

/-! ### The second derivative of the tilt -/

/-- `d/du Cov_u(f, R) = -t [Cov_u(fR, R) - Cov_u(f, R) E_u R - E_u f Var_u R]`. -/
theorem TiltData.hasDerivAt_tiltCov {ν R : X → ℝ} {M : ℝ} (h : TiltData μ ν R M) {f : X → ℝ}
    (hfm : Measurable f) {Mf : ℝ} (hf : ∀ x, |f x| ≤ Mf) (t u₀ : ℝ) :
    HasDerivAt (fun u ↦ tiltCov μ ν f R R t u)
      (-t * (tiltCov μ ν (fun x ↦ f x * R x) R R t u₀ -
        tiltCov μ ν f R R t u₀ * tiltExp μ ν R R t u₀ -
        tiltExp μ ν f R t u₀ * tiltCov μ ν R R R t u₀)) u₀ := by
  have hMf : 0 ≤ Mf := le_trans (abs_nonneg _) (hf (Classical.arbitrary X))
  have hfR : HasDerivAt (fun u ↦ tiltExp μ ν (fun x ↦ f x * R x) R t u)
      (-t * tiltCov μ ν (fun x ↦ f x * R x) R R t u₀) u₀ :=
    h.hasDerivAt_tiltExp (hfm.mul h.R_meas) (Mf := Mf * M) (fun x ↦ by
      simp only [Pi.mul_apply, abs_mul]
      exact mul_le_mul (hf x) (h.R_bound x) (abs_nonneg _) hMf) t u₀
  have hff := h.hasDerivAt_tiltExp hfm hf t u₀
  have hRR := h.hasDerivAt_tiltExp h.R_meas h.R_bound t u₀
  have hd := hfR.sub (hff.mul hRR)
  refine (hd.congr_deriv ?_)
  ring

/-- The second derivative of the tilt is bounded by `6 t² ‖f‖∞ ‖R‖∞²`. -/
theorem TiltData.abs_second_deriv_le {ν R : X → ℝ} {M : ℝ} (h : TiltData μ ν R M) {f : X → ℝ}
    (hfm : Measurable f) {Mf : ℝ} (hf : ∀ x, |f x| ≤ Mf) (t u : ℝ) :
    |-t * (-t * (tiltCov μ ν (fun x ↦ f x * R x) R R t u -
        tiltCov μ ν f R R t u * tiltExp μ ν R R t u -
        tiltExp μ ν f R t u * tiltCov μ ν R R R t u))| ≤ t ^ 2 * (6 * Mf * M ^ 2) := by
  have hMf : 0 ≤ Mf := le_trans (abs_nonneg _) (hf (Classical.arbitrary X))
  have hM := h.M_nonneg
  have h1 : |tiltCov μ ν (fun x ↦ f x * R x) R R t u| ≤ 2 * (Mf * M) * M :=
    h.abs_tiltCov_le_of_bdd (hfm.mul h.R_meas) (fun x ↦ by
      simp only [Pi.mul_apply, abs_mul]
      exact mul_le_mul (hf x) (h.R_bound x) (abs_nonneg _) hMf) h.R_meas h.R_bound t u
  have h2 : |tiltCov μ ν f R R t u * tiltExp μ ν R R t u| ≤ 2 * Mf * M * M := by
    rw [abs_mul]
    exact mul_le_mul (h.abs_tiltCov_le_of_bdd hfm hf h.R_meas h.R_bound t u)
      (h.abs_tiltExp_le h.R_meas h.R_bound t u) (abs_nonneg _) (by positivity)
  have h3 : |tiltExp μ ν f R t u * tiltCov μ ν R R R t u| ≤ Mf * (2 * M * M) := by
    rw [abs_mul]
    exact mul_le_mul (h.abs_tiltExp_le hfm hf t u)
      (h.abs_tiltCov_le_of_bdd h.R_meas h.R_bound h.R_meas h.R_bound t u) (abs_nonneg _) hMf
  have hsum : |tiltCov μ ν (fun x ↦ f x * R x) R R t u -
      tiltCov μ ν f R R t u * tiltExp μ ν R R t u -
      tiltExp μ ν f R t u * tiltCov μ ν R R R t u| ≤ 6 * Mf * M ^ 2 := by
    calc _ ≤ |tiltCov μ ν (fun x ↦ f x * R x) R R t u -
          tiltCov μ ν f R R t u * tiltExp μ ν R R t u| +
          |tiltExp μ ν f R t u * tiltCov μ ν R R R t u| := abs_sub _ _
      _ ≤ (|tiltCov μ ν (fun x ↦ f x * R x) R R t u| +
          |tiltCov μ ν f R R t u * tiltExp μ ν R R t u|) +
          |tiltExp μ ν f R t u * tiltCov μ ν R R R t u| :=
          add_le_add (abs_sub _ _) le_rfl
      _ ≤ (2 * (Mf * M) * M + 2 * Mf * M * M) + Mf * (2 * M * M) := by gcongr
      _ = 6 * Mf * M ^ 2 := by ring
  have hsq : |-t * (-t * (tiltCov μ ν (fun x ↦ f x * R x) R R t u -
      tiltCov μ ν f R R t u * tiltExp μ ν R R t u -
      tiltExp μ ν f R t u * tiltCov μ ν R R R t u))| =
      t ^ 2 * |tiltCov μ ν (fun x ↦ f x * R x) R R t u -
      tiltCov μ ν f R R t u * tiltExp μ ν R R t u -
      tiltExp μ ν f R t u * tiltCov μ ν R R R t u| := by
    rw [show -t * (-t * (tiltCov μ ν (fun x ↦ f x * R x) R R t u -
      tiltCov μ ν f R R t u * tiltExp μ ν R R t u -
      tiltExp μ ν f R t u * tiltCov μ ν R R R t u)) =
      t ^ 2 * (tiltCov μ ν (fun x ↦ f x * R x) R R t u -
      tiltCov μ ν f R R t u * tiltExp μ ν R R t u -
      tiltExp μ ν f R t u * tiltCov μ ν R R R t u) by ring, abs_mul, abs_of_nonneg (sq_nonneg t)]
  rw [hsq]
  exact mul_le_mul_of_nonneg_left hsum (sq_nonneg t)

/-! ### The quadratic remainder: Fréchet differentiability, uniformly in the test -/

/-- **The fixed-temperature response is differentiable with an explicit quadratic remainder,
uniformly over bounded tests**:
`|⟨f⟩_{L+R} - ⟨f⟩_L - (-t Cov_L(f, R))| ≤ 6 t² ‖f‖∞ ‖R‖∞²`. -/
theorem TiltData.abs_tiltExp_taylor_le {ν R : X → ℝ} {M : ℝ} (h : TiltData μ ν R M) {f : X → ℝ}
    (hfm : Measurable f) {Mf : ℝ} (hf : ∀ x, |f x| ≤ Mf) (t : ℝ) :
    |tiltExp μ ν f R t 1 - tiltExp μ ν f R t 0 - (-t * tiltCov μ ν f R R t 0)| ≤
      6 * t ^ 2 * Mf * M ^ 2 := by
  set B : ℝ := t ^ 2 * (6 * Mf * M ^ 2) with hB
  have hMf : 0 ≤ Mf := le_trans (abs_nonneg _) (hf (Classical.arbitrary X))
  have hM := h.M_nonneg
  have hB0 : 0 ≤ B := by positivity
  -- step 1: the first derivative is `B`-Lipschitz on `[0, 1]`
  have hstep1 : ∀ u ∈ Icc (0 : ℝ) 1,
      ‖(-t * tiltCov μ ν f R R t u) - (-t * tiltCov μ ν f R R t 0)‖ ≤ B * (u - 0) := by
    intro u hu
    refine norm_image_sub_le_of_norm_deriv_le_segment' (a := 0) (b := 1)
      (f := fun u ↦ -t * tiltCov μ ν f R R t u)
      (f' := fun u ↦ -t * (-t * (tiltCov μ ν (fun x ↦ f x * R x) R R t u -
        tiltCov μ ν f R R t u * tiltExp μ ν R R t u -
        tiltExp μ ν f R t u * tiltCov μ ν R R R t u))) (C := B)
      (fun u _ ↦ ((h.hasDerivAt_tiltCov hfm hf t u).const_mul (-t)).hasDerivWithinAt)
      (fun u _ ↦ by
        rw [Real.norm_eq_abs]
        exact h.abs_second_deriv_le hfm hf t u) u hu
  -- step 2: mean value for `g(u) - g(0) - u g'(0)`
  have hstep2 := norm_image_sub_le_of_norm_deriv_le_segment' (a := 0) (b := 1)
    (f := fun u ↦ tiltExp μ ν f R t u - tiltExp μ ν f R t 0 - u * (-t * tiltCov μ ν f R R t 0))
    (f' := fun u ↦ (-t * tiltCov μ ν f R R t u) - (-t * tiltCov μ ν f R R t 0)) (C := B)
    (fun u _ ↦ by
      have hd := ((h.hasDerivAt_tiltExp hfm hf t u).sub_const (tiltExp μ ν f R t 0)).sub
        ((hasDerivAt_id u).mul_const (-t * tiltCov μ ν f R R t 0))
      simp only [id, one_mul] at hd
      exact hd.hasDerivWithinAt)
    (fun u hu ↦ by
      have := hstep1 u (Ico_subset_Icc_self hu)
      have hu1 : u - 0 ≤ 1 := by linarith [hu.2]
      calc _ ≤ B * (u - 0) := this
        _ ≤ B * 1 := mul_le_mul_of_nonneg_left hu1 hB0
        _ = B := mul_one B)
    1 (right_mem_Icc.mpr zero_le_one)
  simp only [zero_mul, sub_zero, sub_self, one_mul, Real.norm_eq_abs] at hstep2
  calc |tiltExp μ ν f R t 1 - tiltExp μ ν f R t 0 - (-t * tiltCov μ ν f R R t 0)|
      ≤ B * 1 := hstep2
    _ = 6 * t ^ 2 * Mf * M ^ 2 := by rw [hB]; ring

/-! ### The window setting: every `u` is a normalised expectation -/

variable {ι : Type*} [Fintype ι]

/-- The tilt at parameter `u` of the window weight `χ e^{-tL}` by the truncated residual
`1_{supp χ}(K - L)` is the normalised expectation of `L + u (K - L)`, for tests `φ` with
`φ χ = φ`. -/
theorem tiltExp_window_eq {K L φ χ : (ι → ℝ) → ℝ} (hφχ : ∀ w, φ w * χ w = φ w) (t u : ℝ) :
    tiltExp (volume : Measure (ι → ℝ)) (fun w ↦ χ w * Real.exp (-(t * L w))) φ
        ((tsupport χ).indicator fun w ↦ K w - L w) t u =
      nmoment (fun w ↦ L w + u * (K w - L w)) φ χ t := by
  have hpt : ∀ (g : (ι → ℝ) → ℝ), (∀ w, g w * χ w = g w) → ∀ w,
      g w * Real.exp (-(t * (tsupport χ).indicator (fun w ↦ K w - L w) w * u)) *
        (χ w * Real.exp (-(t * L w))) = g w * Real.exp (-(t * (L w + u * (K w - L w)))) := by
    intro g hg w
    by_cases hw : w ∈ tsupport χ
    · rw [Set.indicator_of_mem hw]
      have : g w * Real.exp (-(t * (K w - L w) * u)) * (χ w * Real.exp (-(t * L w))) =
          (g w * χ w) * (Real.exp (-(t * (K w - L w) * u)) * Real.exp (-(t * L w))) := by ring
      rw [this, hg w, ← Real.exp_add]
      congr 2
      ring
    · rw [image_eq_zero_of_notMem_tsupport hw]
      have : g w = 0 := by
        have := hg w
        rw [image_eq_zero_of_notMem_tsupport hw, mul_zero] at this
        exact this.symm
      simp [this]
  have hden : ∀ w, (fun _ ↦ (1 : ℝ)) w *
      Real.exp (-(t * (tsupport χ).indicator (fun w ↦ K w - L w) w * u)) *
        (χ w * Real.exp (-(t * L w))) = χ w * Real.exp (-(t * (L w + u * (K w - L w)))) := by
    intro w
    by_cases hw : w ∈ tsupport χ
    · rw [Set.indicator_of_mem hw]
      have : (fun _ ↦ (1 : ℝ)) w * Real.exp (-(t * (K w - L w) * u)) *
          (χ w * Real.exp (-(t * L w))) =
          χ w * (Real.exp (-(t * (K w - L w) * u)) * Real.exp (-(t * L w))) := by ring
      rw [this, ← Real.exp_add]
      congr 2
      ring
    · rw [image_eq_zero_of_notMem_tsupport hw]
      simp
  unfold tiltExp tiltNum nmoment
  congr 1
  · exact integral_congr_ae (Filter.Eventually.of_forall (hpt φ hφχ))
  · exact integral_congr_ae (Filter.Eventually.of_forall hden)

/-- The window data: `ν = χ e^{-tL}` with a continuous nonnegative compactly supported cutoff
that is nonzero somewhere, and the truncated residual bounded by `δ` on the window. -/
theorem tiltData_window {K L χ : (ι → ℝ) → ℝ} (hχc : Continuous χ) (hχs : HasCompactSupport χ)
    (hχ0 : ∀ w, 0 ≤ χ w) {w₀ : ι → ℝ} (hw₀ : χ w₀ ≠ 0) (hLc : Continuous L) (hKm : Measurable K)
    {δ : ℝ} (hclose : ∀ w ∈ tsupport χ, |K w - L w| ≤ δ) (t : ℝ) :
    TiltData (volume : Measure (ι → ℝ)) (fun w ↦ χ w * Real.exp (-(t * L w)))
      ((tsupport χ).indicator fun w ↦ K w - L w) δ := by
  have hνc : Continuous fun w ↦ χ w * Real.exp (-(t * L w)) :=
    hχc.mul (Real.continuous_exp.comp (continuous_const.mul hLc).neg)
  refine ⟨hνc.measurable, hνc.integrable_of_hasCompactSupport hχs.mul_right,
    fun w ↦ mul_nonneg (hχ0 w) (Real.exp_pos _).le, ?_,
    (hKm.sub hLc.measurable).indicator (isClosed_tsupport χ).measurableSet, fun w ↦ ?_⟩
  · exact hνc.integral_pos_of_hasCompactSupport_nonneg_nonzero hχs.mul_right
      (fun w ↦ mul_nonneg (hχ0 w) (Real.exp_pos _).le) (mul_ne_zero hw₀ (Real.exp_pos _).ne')
  · by_cases hw : w ∈ tsupport χ
    · rw [Set.indicator_of_mem hw]
      exact hclose w hw
    · rw [Set.indicator_of_notMem hw, abs_zero]
      exact (abs_nonneg _).trans (hclose w₀ (subset_tsupport χ hw₀))

/-- **Quadratic remainder for a perturbed loss on the window**: for `K` within `δ` of `L` on the
window and a bounded test supported where `χ = 1`,
`|⟨φ⟩_{K,t} - ⟨φ⟩_{L,t} + t Cov_{L,t}(φ, K - L)| ≤ 6 t² ‖φ‖∞ δ²`. -/
theorem nmoment_taylor_le {K L φ χ : (ι → ℝ) → ℝ} (hχc : Continuous χ)
    (hχs : HasCompactSupport χ) (hχ0 : ∀ w, 0 ≤ χ w) {w₀ : ι → ℝ} (hw₀ : χ w₀ ≠ 0)
    (hLc : Continuous L) (hKm : Measurable K) {δ : ℝ} (hclose : ∀ w ∈ tsupport χ, |K w - L w| ≤ δ)
    (hφm : Measurable φ) {Mφ : ℝ} (hφ : ∀ w, |φ w| ≤ Mφ) (hφχ : ∀ w, φ w * χ w = φ w) (t : ℝ) :
    |nmoment K φ χ t - nmoment L φ χ t -
      (-t * tiltCov (volume : Measure (ι → ℝ)) (fun w ↦ χ w * Real.exp (-(t * L w))) φ
        ((tsupport χ).indicator fun w ↦ K w - L w) ((tsupport χ).indicator fun w ↦ K w - L w)
        t 0)| ≤ 6 * t ^ 2 * Mφ * δ ^ 2 := by
  have h := tiltData_window hχc hχs hχ0 hw₀ hLc hKm hclose t
  have := h.abs_tiltExp_taylor_le hφm hφ t
  rw [tiltExp_window_eq hφχ t 1, tiltExp_window_eq hφχ t 0] at this
  have e1 : (fun w ↦ L w + 1 * (K w - L w)) = K := by
    funext w
    ring
  have e0 : (fun w ↦ L w + 0 * (K w - L w)) = L := by
    funext w
    ring
  rwa [e1, e0] at this

/-! ### Finite mixtures of truths -/

/-- The population loss of a truth `q` for the model `p`: `L_q(w) = -∫ q(x) log p_w(x) dx`. -/
noncomputable def popLoss {Y : Type*} [MeasurableSpace Y] (σ : Measure Y) (q : Y → ℝ)
    (p : (ι → ℝ) → Y → ℝ) (w : ι → ℝ) : ℝ :=
  -∫ x, q x * Real.log (p w x) ∂σ

omit [Fintype ι] in
/-- **The population loss is affine in the truth**: for a finite mixture `q_θ = Σ θ_i q_i` with
integrable `q_i log p_w`, `L_{q_θ} = Σ θ_i L_{q_i}`. -/
theorem popLoss_mix {Y : Type*} [MeasurableSpace Y] (σ : Measure Y) {m : ℕ} (q : Fin m → Y → ℝ)
    (p : (ι → ℝ) → Y → ℝ) (θ : Fin m → ℝ) (w : ι → ℝ)
    (hint : ∀ i, Integrable (fun x ↦ q i x * Real.log (p w x)) σ) :
    popLoss σ (fun x ↦ ∑ i, θ i * q i x) p w = ∑ i, θ i * popLoss σ (q i) p w := by
  unfold popLoss
  have : (fun x ↦ (∑ i, θ i * q i x) * Real.log (p w x)) =
      fun x ↦ ∑ i, θ i * (q i x * Real.log (p w x)) := by
    funext x
    rw [Finset.sum_mul]
    exact Finset.sum_congr rfl fun i _ ↦ by ring
  rw [this, integral_finsetSum _ fun i _ ↦ (hint i).const_mul _, ← Finset.sum_neg_distrib]
  exact Finset.sum_congr rfl fun i _ ↦ by rw [integral_const_mul]; ring

/-- The mixture loss `L_θ = Σ θ_i L_i`. -/
noncomputable def mixLoss {m : ℕ} (L : Fin m → (ι → ℝ) → ℝ) (θ : Fin m → ℝ) (w : ι → ℝ) : ℝ :=
  ∑ i, θ i * L i w

/-- **The Bayesian influence function of a mixture weight**: at fixed temperature,
`∂_{θ_i} ⟨φ⟩_{θ,t} = -t Cov_{θ,t}(φ, L_i)` (the covariance with the truncated component loss). -/
theorem hasDerivAt_nmoment_mixture {m : ℕ} {L : Fin m → (ι → ℝ) → ℝ} (hL : ∀ i, Continuous (L i))
    (θ : Fin m → ℝ) (i : Fin m) {φ χ : (ι → ℝ) → ℝ} (hχc : Continuous χ)
    (hχs : HasCompactSupport χ) (hχ0 : ∀ w, 0 ≤ χ w) {w₀ : ι → ℝ} (hw₀ : χ w₀ ≠ 0)
    (hφm : Measurable φ) {Mφ : ℝ} (hφ : ∀ w, |φ w| ≤ Mφ) (hφχ : ∀ w, φ w * χ w = φ w) (t : ℝ) :
    HasDerivAt (fun u ↦ nmoment (fun w ↦ mixLoss L θ w + u * L i w) φ χ t)
      (-t * tiltCov (volume : Measure (ι → ℝ))
        (fun w ↦ χ w * Real.exp (-(t * mixLoss L θ w))) φ
        ((tsupport χ).indicator (L i)) ((tsupport χ).indicator (L i)) t 0) 0 := by
  have hLθ : Continuous (mixLoss L θ) := by
    unfold mixLoss
    exact continuous_finsetSum _ fun j _ ↦ continuous_const.mul (hL j)
  -- `L_i` is bounded on the compact window
  obtain ⟨M, hM⟩ := hχs.exists_bound_of_continuousOn (hL i).continuousOn
  have hclose : ∀ w ∈ tsupport χ, |(mixLoss L θ w + L i w) - mixLoss L θ w| ≤ M := fun w hw ↦ by
    rw [add_sub_cancel_left, ← Real.norm_eq_abs]
    exact hM w hw
  have hKm : Measurable fun w ↦ mixLoss L θ w + L i w := (hLθ.add (hL i)).measurable
  have h := tiltData_window (K := fun w ↦ mixLoss L θ w + L i w) hχc hχs hχ0 hw₀ hLθ hKm hclose t
  have hind : ((tsupport χ).indicator fun w ↦ (mixLoss L θ w + L i w) - mixLoss L θ w) =
      (tsupport χ).indicator (L i) := by
    funext w
    simp [Set.indicator]
  have hd := h.hasDerivAt_tiltExp hφm hφ t 0
  rw [hind] at hd
  refine hd.congr_of_eventuallyEq (Filter.Eventually.of_forall fun u ↦ ?_)
  have := tiltExp_window_eq (K := fun w ↦ mixLoss L θ w + L i w) (L := mixLoss L θ) hφχ t u
  rw [hind] at this
  change nmoment (fun w ↦ mixLoss L θ w + u * L i w) φ χ t =
    tiltExp volume (fun w ↦ χ w * Real.exp (-(t * mixLoss L θ w))) φ
      ((tsupport χ).indicator (L i)) t u
  rw [this]
  congr 1
  funext w
  ring

end Laplace.Multi
