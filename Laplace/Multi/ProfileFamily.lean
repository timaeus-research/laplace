/-
Copyright (c) 2026 Timaeus Research. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniel Murfet
-/
import Mathlib
import Laplace.Multi.ProfileResponse

/-!
# The wall profile as an exponential family in the wall variable

The profile law `ρ_c ∝ e^{-(y^p + c y^q)} dy` on `(0,∞)` (`ProfileResponse`) is, as `c` varies,
a one-parameter **exponential family** with base measure `e^{-y^p} dy`, natural parameter `−c`
and sufficient statistic `y^q`:

  `ρ_c(y) = e^{-y^p} · exp(−c y^q − A(c))`,   `A(c) = log Z(c)`   (`profile_expFamily`).

This module records the consequences that make the wall crossing a *map*:

* all derivatives of the profile numerator in the wall variable are moments of the sufficient
  statistic, `∂_c^n N_ψ(c) = (−1)^n N_{ψ y^{nq}}(c)` (`iteratedDeriv_profileNum`), for observables
  of polynomial growth (`hasDerivAt_profileNum_poly`);
* the log-partition function is convex on `(0,∞)` with `A' = −⟨y^q⟩_c` and `A'' = Var_c(y^q)`
  (`hasDerivAt_profileLogZ`, `hasDerivAt_deriv_profileLogZ`, `profileLogZ_convexOn`);
* the variance of the sufficient statistic is strictly positive for `q > 0` (`profileVar_pos`),
  so the **mean map** `c ↦ ⟨y^q⟩_c` is strictly decreasing on `(0,∞)` (`profileMean_strictAntiOn`)
  and injective: the position along the wall is faithfully read off from the response.

In the language of the note: between the `p`-end (`c = 0`, the unperturbed monomial) and the
`q`-end (`c → ∞`) the wall is traversed monotonically by a single sufficient statistic, and the
finite-temperature posterior at `s = c t^{-σ*}` is exactly this family
(`wall_posterior_eq_profile`).
-/

open MeasureTheory Filter Topology Set

namespace Laplace.Multi

/-- Integrability of `ψ e^{-(y^p + c y^q)}` on `(0,∞)` for `ψ` of polynomial growth, `c ≥ 0`. -/
theorem integrableOn_profile {p q : ℝ} (hp : 0 < p) {c : ℝ} (hc : 0 ≤ c)
    {ψ : ℝ → ℝ} (hψm : Measurable ψ) {Mψ r : ℝ} (hr : 0 ≤ r)
    (hψ : ∀ y, 0 < y → |ψ y| ≤ Mψ * y ^ r) :
    IntegrableOn (fun y ↦ ψ y * Real.exp (-(y ^ p + c * y ^ q))) (Ioi 0) := by
  refine ((integrableOn_rpow_mul_exp_neg_rpow_nonneg hp hr).const_mul Mψ).mono' ?_ ?_
  · exact (hψm.mul (Real.measurable_exp.comp ((measurable_id.pow_const p).add
      ((measurable_id.pow_const q).const_mul c)).neg)).aestronglyMeasurable
  · refine (ae_restrict_iff' measurableSet_Ioi).mpr (Filter.Eventually.of_forall fun y hy ↦ ?_)
    have hy0 : (0 : ℝ) < y := hy
    rw [Real.norm_eq_abs, abs_mul, Real.abs_exp]
    have hbnd : Real.exp (-(y ^ p + c * y ^ q)) ≤ Real.exp (-(y ^ p)) := by
      rw [Real.exp_le_exp]
      have : 0 ≤ c * y ^ q := mul_nonneg hc (Real.rpow_nonneg hy0.le q)
      linarith
    calc |ψ y| * Real.exp (-(y ^ p + c * y ^ q)) ≤ (Mψ * y ^ r) * Real.exp (-(y ^ p)) :=
          mul_le_mul (hψ y hy0) hbnd (Real.exp_pos _).le (le_trans (abs_nonneg _) (hψ y hy0))
      _ = Mψ * (y ^ r * Real.exp (-(y ^ p))) := by ring

/-- `d/dc N_ψ(c) = −N_{ψ y^q}(c)` for `c > 0` and `ψ` of polynomial growth `|ψ y| ≤ M y^r`. -/
theorem hasDerivAt_profileNum_poly {p q : ℝ} (hp : 0 < p) (hq : 0 ≤ q) {ψ : ℝ → ℝ}
    (hψm : Measurable ψ) {Mψ r : ℝ} (hr : 0 ≤ r) (hψ : ∀ y, 0 < y → |ψ y| ≤ Mψ * y ^ r)
    {c₀ : ℝ} (hc₀ : 0 < c₀) :
    HasDerivAt (fun c ↦ profileNum p q ψ c)
      (-∫ y in Ioi (0 : ℝ), ψ y * y ^ q * Real.exp (-(y ^ p + c₀ * y ^ q))) c₀ := by
  have hball : Metric.ball c₀ (c₀ / 2) ∈ 𝓝 c₀ := Metric.ball_mem_nhds c₀ (by linarith)
  have hcpos : ∀ c ∈ Metric.ball c₀ (c₀ / 2), 0 < c := fun c hc ↦ by
    rw [Metric.mem_ball, Real.dist_eq, abs_lt] at hc
    linarith [hc.1]
  have hmeasF : ∀ c : ℝ, AEStronglyMeasurable (fun y ↦ ψ y * Real.exp (-(y ^ p + c * y ^ q)))
      (volume.restrict (Ioi 0)) := fun c ↦
    (hψm.mul (Real.measurable_exp.comp ((measurable_id.pow_const p).add
      ((measurable_id.pow_const q).const_mul c)).neg)).aestronglyMeasurable
  have hmeasF' : ∀ c : ℝ, AEStronglyMeasurable
      (fun y ↦ ψ y * (Real.exp (-(y ^ p + c * y ^ q)) * (-(y ^ q)))) (volume.restrict (Ioi 0)) :=
    fun c ↦ (hψm.mul ((Real.measurable_exp.comp ((measurable_id.pow_const p).add
      ((measurable_id.pow_const q).const_mul c)).neg).mul
      (measurable_id.pow_const q).neg)).aestronglyMeasurable
  have hbnd : ∀ c, 0 < c → ∀ y ∈ Ioi (0 : ℝ),
      Real.exp (-(y ^ p + c * y ^ q)) ≤ Real.exp (-(y ^ p)) := fun c hc y hy ↦ by
    rw [Real.exp_le_exp]
    have : 0 ≤ c * y ^ q := mul_nonneg hc.le (Real.rpow_nonneg (le_of_lt hy) q)
    linarith
  have hint : Integrable (fun y ↦ ψ y * Real.exp (-(y ^ p + c₀ * y ^ q)))
      (volume.restrict (Ioi 0)) := integrableOn_profile hp hc₀.le hψm hr hψ
  have hbound : ∀ᵐ y ∂(volume.restrict (Ioi (0 : ℝ))), ∀ c ∈ Metric.ball c₀ (c₀ / 2),
      ‖ψ y * (Real.exp (-(y ^ p + c * y ^ q)) * (-(y ^ q)))‖ ≤
        Mψ * (y ^ (r + q) * Real.exp (-(y ^ p))) := by
    refine (ae_restrict_iff' measurableSet_Ioi).mpr (Filter.Eventually.of_forall fun y hy c hc ↦ ?_)
    have hy0 : (0 : ℝ) < y := hy
    rw [Real.norm_eq_abs, abs_mul, abs_mul, abs_neg, Real.abs_exp,
      abs_of_pos (Real.rpow_pos_of_pos hy0 q)]
    have := hbnd c (hcpos c hc) y hy
    calc |ψ y| * (Real.exp (-(y ^ p + c * y ^ q)) * y ^ q)
        ≤ (Mψ * y ^ r) * (Real.exp (-(y ^ p)) * y ^ q) :=
          mul_le_mul (hψ y hy0) (mul_le_mul_of_nonneg_right this (Real.rpow_pos_of_pos hy0 q).le)
            (by positivity) (le_trans (abs_nonneg _) (hψ y hy0))
      _ = Mψ * (y ^ (r + q) * Real.exp (-(y ^ p))) := by rw [Real.rpow_add hy0]; ring
  have hdiff : ∀ᵐ y ∂(volume.restrict (Ioi (0 : ℝ))), ∀ c ∈ Metric.ball c₀ (c₀ / 2),
      HasDerivAt (fun c ↦ ψ y * Real.exp (-(y ^ p + c * y ^ q)))
        (ψ y * (Real.exp (-(y ^ p + c * y ^ q)) * (-(y ^ q)))) c := by
    refine Filter.Eventually.of_forall fun y c _ ↦ ?_
    have h1 : HasDerivAt (fun c ↦ -(y ^ p + c * y ^ q)) (-(y ^ q)) c := by
      have h0 := ((hasDerivAt_id c).mul_const (y ^ q)).const_add (y ^ p)
      simp only [id, one_mul] at h0
      exact h0.neg
    exact h1.exp.const_mul (ψ y)
  have key := hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (F := fun c y ↦ ψ y * Real.exp (-(y ^ p + c * y ^ q)))
    (F' := fun c y ↦ ψ y * (Real.exp (-(y ^ p + c * y ^ q)) * (-(y ^ q))))
    hball (Filter.Eventually.of_forall hmeasF) hint (hmeasF' c₀) hbound
    ((integrableOn_rpow_mul_exp_neg_rpow_nonneg hp (add_nonneg hr hq)).const_mul Mψ) hdiff
  unfold profileNum
  refine key.2.congr_deriv ?_
  rw [← integral_neg]
  refine integral_congr_ae (Filter.Eventually.of_forall fun y ↦ ?_)
  beta_reduce
  ring

/-- The wall response for observables of polynomial growth. -/
theorem hasDerivAt_profilePosterior_poly {p q : ℝ} (hp : 0 < p) (hq : 0 ≤ q) {ψ : ℝ → ℝ}
    (hψm : Measurable ψ) {Mψ r : ℝ} (hr : 0 ≤ r) (hψ : ∀ y, 0 < y → |ψ y| ≤ Mψ * y ^ r)
    {c₀ : ℝ} (hc₀ : 0 < c₀) (hZ : profileNum p q (fun _ ↦ 1) c₀ ≠ 0) :
    HasDerivAt (fun c ↦ profilePosterior p q ψ c)
      (-(profilePosterior p q (fun y ↦ ψ y * y ^ q) c₀ -
        profilePosterior p q ψ c₀ * profilePosterior p q (fun y ↦ y ^ q) c₀)) c₀ := by
  have hN := hasDerivAt_profileNum_poly hp hq hψm hr hψ hc₀
  have hZ' := hasDerivAt_profileNum hp hq (ψ := fun _ ↦ (1 : ℝ)) measurable_const (Mψ := 1)
    (fun _ ↦ by simp) hc₀
  have hdiv := hN.div hZ' hZ
  refine hdiv.congr_deriv ?_
  unfold profilePosterior profileNum
  simp only [one_mul]
  set N := ∫ y in Ioi (0 : ℝ), ψ y * Real.exp (-(y ^ p + c₀ * y ^ q)) with hN'
  set NS := ∫ y in Ioi (0 : ℝ), ψ y * y ^ q * Real.exp (-(y ^ p + c₀ * y ^ q)) with hNS
  set ZS := ∫ y in Ioi (0 : ℝ), y ^ q * Real.exp (-(y ^ p + c₀ * y ^ q)) with hZS
  set Z := ∫ y in Ioi (0 : ℝ), Real.exp (-(y ^ p + c₀ * y ^ q)) with hZ''
  clear_value N NS ZS Z
  field_simp
  ring

/-- **All wall derivatives are moments of the sufficient statistic**:
`∂_c^n N_ψ(c) = (−1)^n ∫₀^∞ ψ y^{nq} e^{-(y^p + c y^q)}` for `c > 0`. -/
theorem iteratedDeriv_profileNum {p q : ℝ} (hp : 0 < p) (hq : 0 ≤ q) (n : ℕ) :
    ∀ (ψ : ℝ → ℝ), Measurable ψ → ∀ (Mψ r : ℝ), 0 ≤ r → (∀ y, 0 < y → |ψ y| ≤ Mψ * y ^ r) →
      ∀ c, 0 < c → iteratedDeriv n (fun c ↦ profileNum p q ψ c) c =
        (-1) ^ n * profileNum p q (fun y ↦ ψ y * y ^ ((n : ℝ) * q)) c := by
  induction n with
  | zero =>
    intro ψ _ Mψ r _ _ c _
    rw [iteratedDeriv_zero]
    simp only [pow_zero, one_mul, Nat.cast_zero, zero_mul, Real.rpow_zero, mul_one]
  | succ n ih =>
    intro ψ hψm Mψ r hr hψ c hc
    rw [iteratedDeriv_succ]
    have hev : (iteratedDeriv n fun c ↦ profileNum p q ψ c) =ᶠ[𝓝 c]
        fun c' ↦ (-1) ^ n * profileNum p q (fun y ↦ ψ y * y ^ ((n : ℝ) * q)) c' := by
      filter_upwards [Ioi_mem_nhds hc] with c' hc'
      exact ih ψ hψm Mψ r hr hψ c' hc'
    rw [hev.deriv_eq]
    have hψn : Measurable fun y ↦ ψ y * y ^ ((n : ℝ) * q) :=
      hψm.mul (measurable_id.pow_const _)
    have hbnd : ∀ y, 0 < y → |ψ y * y ^ ((n : ℝ) * q)| ≤ Mψ * y ^ (r + n * q) := fun y hy ↦ by
      rw [abs_mul, abs_of_pos (Real.rpow_pos_of_pos hy _), Real.rpow_add hy, ← mul_assoc]
      exact mul_le_mul_of_nonneg_right (hψ y hy) (Real.rpow_pos_of_pos hy _).le
    have hd := (hasDerivAt_profileNum_poly hp hq hψn (r := r + n * q)
      (add_nonneg hr (mul_nonneg (Nat.cast_nonneg n) hq)) hbnd hc).const_mul ((-1 : ℝ) ^ n)
    rw [hd.deriv]
    have hX : ∫ y in Ioi (0 : ℝ), ψ y * y ^ ((n : ℝ) * q) * y ^ q *
        Real.exp (-(y ^ p + c * y ^ q)) =
        profileNum p q (fun y ↦ ψ y * y ^ (((n + 1 : ℕ) : ℝ) * q)) c := by
      unfold profileNum
      refine setIntegral_congr_fun measurableSet_Ioi fun y hy ↦ ?_
      have hy0 : (0 : ℝ) < y := hy
      rw [mul_assoc (ψ y), ← Real.rpow_add hy0, Nat.cast_succ,
        show (n : ℝ) * q + q = ((n : ℝ) + 1) * q by ring]
    rw [hX, pow_succ]
    ring

/-- `Z(c) = ∫₀^∞ e^{-(y^p + c y^q)} > 0` for `c ≥ 0`. -/
theorem profileNum_one_pos {p q : ℝ} (hp : 0 < p) {c : ℝ} (hc : 0 ≤ c) :
    0 < profileNum p q (fun _ ↦ 1) c := by
  have hint : IntegrableOn (fun y ↦ (1 : ℝ) * Real.exp (-(y ^ p + c * y ^ q))) (Ioi 0) :=
    integrableOn_profile hp hc measurable_const (Mψ := 1) (r := 0) le_rfl
      (fun y hy ↦ by simp)
  unfold profileNum
  rw [setIntegral_pos_iff_support_of_nonneg_ae
    (Filter.Eventually.of_forall fun y ↦ by simp [(Real.exp_pos _).le]) hint]
  have hsupp : Function.support (fun y : ℝ ↦ (1 : ℝ) * Real.exp (-(y ^ p + c * y ^ q))) = univ :=
    Set.eq_univ_of_forall fun y ↦ Function.mem_support.mpr (by simp [(Real.exp_pos _).ne'])
  rw [hsupp, univ_inter, Real.volume_Ioi]
  simp

/-- The wall log-partition function `A(c) = log Z(c)`. -/
noncomputable def profileLogZ (p q c : ℝ) : ℝ := Real.log (profileNum p q (fun _ ↦ 1) c)

/-- **The exponential-family form of the profile law**:
`e^{-(y^p + c y^q)}/Z(c) = e^{-y^p} · exp(−c y^q − A(c))`. -/
theorem profile_expFamily {p q : ℝ} (hp : 0 < p) {c : ℝ} (hc : 0 ≤ c) (y : ℝ) :
    Real.exp (-(y ^ p + c * y ^ q)) / profileNum p q (fun _ ↦ 1) c =
      Real.exp (-(y ^ p)) * Real.exp (-(c * y ^ q) - profileLogZ p q c) := by
  unfold profileLogZ
  rw [Real.exp_sub, Real.exp_log (profileNum_one_pos hp hc), ← mul_div_assoc, ← Real.exp_add]
  congr 2
  ring

/-- `A'(c) = −⟨y^q⟩_c`: the derivative of the log-partition function is minus the mean of the
sufficient statistic. -/
theorem hasDerivAt_profileLogZ {p q : ℝ} (hp : 0 < p) (hq : 0 ≤ q) {c : ℝ} (hc : 0 < c) :
    HasDerivAt (fun c ↦ profileLogZ p q c) (-(profilePosterior p q (fun y ↦ y ^ q) c)) c := by
  have hZ := hasDerivAt_profileNum hp hq (ψ := fun _ ↦ (1 : ℝ)) measurable_const (Mψ := 1)
    (fun _ ↦ by simp) hc
  have hpos := profileNum_one_pos (q := q) hp hc.le
  refine (hZ.log hpos.ne').congr_deriv ?_
  unfold profilePosterior profileNum
  simp only [one_mul]
  rw [neg_div]

/-- Polynomial growth of the sufficient statistic `y^q`. -/
theorem abs_rpow_le_self_rpow (q : ℝ) : ∀ y : ℝ, 0 < y → |y ^ q| ≤ 1 * y ^ q := fun y hy ↦ by
  rw [abs_of_pos (Real.rpow_pos_of_pos hy q), one_mul]

/-- The wall variance `Var_c(y^q) = ⟨y^q y^q⟩_c − ⟨y^q⟩_c²` is the expectation of a square. -/
theorem profileVar_eq {p q : ℝ} (hp : 0 < p) (hq : 0 ≤ q) {c : ℝ} (hc : 0 ≤ c) :
    profilePosterior p q (fun y ↦ y ^ q * y ^ q) c - profilePosterior p q (fun y ↦ y ^ q) c ^ 2 =
      profileNum p q (fun y ↦ (y ^ q - profilePosterior p q (fun y ↦ y ^ q) c) ^ 2) c /
        profileNum p q (fun _ ↦ 1) c := by
  have hZpos := profileNum_one_pos (q := q) hp hc
  have hI2 : Integrable (fun y ↦ y ^ q * y ^ q * Real.exp (-(y ^ p + c * y ^ q)))
      (volume.restrict (Ioi 0)) :=
    integrableOn_profile hp hc ((measurable_id.pow_const q).mul (measurable_id.pow_const q))
      (Mψ := 1) (r := q + q) (add_nonneg hq hq) fun y hy ↦ by
        rw [abs_of_pos (mul_pos (Real.rpow_pos_of_pos hy q) (Real.rpow_pos_of_pos hy q)),
          Real.rpow_add hy, one_mul]
  have hI1 : Integrable (fun y ↦ y ^ q * Real.exp (-(y ^ p + c * y ^ q)))
      (volume.restrict (Ioi 0)) :=
    integrableOn_profile hp hc (measurable_id.pow_const q) (Mψ := 1) (r := q) hq
      (abs_rpow_le_self_rpow q)
  have hI0 : Integrable (fun y ↦ (1 : ℝ) * Real.exp (-(y ^ p + c * y ^ q)))
      (volume.restrict (Ioi 0)) :=
    integrableOn_profile hp hc measurable_const (Mψ := 1) (r := 0) le_rfl (fun y hy ↦ by simp)
  set m := profilePosterior p q (fun y ↦ y ^ q) c with hm
  have hA : Integrable (fun y ↦ y ^ q * y ^ q * Real.exp (-(y ^ p + c * y ^ q)) -
      2 * m * (y ^ q * Real.exp (-(y ^ p + c * y ^ q)))) (volume.restrict (Ioi 0)) :=
    hI2.sub (hI1.const_mul _)
  have hexp : profileNum p q (fun y ↦ (y ^ q - m) ^ 2) c =
      profileNum p q (fun y ↦ y ^ q * y ^ q) c - 2 * m * profileNum p q (fun y ↦ y ^ q) c +
        m ^ 2 * profileNum p q (fun _ ↦ 1) c := by
    unfold profileNum
    rw [← MeasureTheory.integral_const_mul, ← MeasureTheory.integral_const_mul,
      ← integral_sub hI2 (hI1.const_mul _), ← integral_add hA (hI0.const_mul _)]
    exact setIntegral_congr_fun measurableSet_Ioi fun y _ ↦ by ring
  rw [hexp]
  have hmZ : m * profileNum p q (fun _ ↦ 1) c = profileNum p q (fun y ↦ y ^ q) c := by
    rw [hm]
    unfold profilePosterior
    exact div_mul_cancel₀ _ hZpos.ne'
  unfold profilePosterior
  rw [← hmZ]
  field_simp
  ring

/-- `Var_c(y^q) ≥ 0`. -/
theorem profileVar_nonneg {p q : ℝ} (hp : 0 < p) (hq : 0 ≤ q) {c : ℝ} (hc : 0 ≤ c) :
    0 ≤ profilePosterior p q (fun y ↦ y ^ q * y ^ q) c -
      profilePosterior p q (fun y ↦ y ^ q) c ^ 2 := by
  rw [profileVar_eq hp hq hc]
  refine div_nonneg ?_ (profileNum_one_pos hp hc).le
  unfold profileNum
  exact setIntegral_nonneg measurableSet_Ioi fun y _ ↦
    mul_nonneg (sq_nonneg _) (Real.exp_pos _).le

/-- **The sufficient statistic is never degenerate**: `Var_c(y^q) > 0` for `q > 0`, `c ≥ 0`. -/
theorem profileVar_pos {p q : ℝ} (hp : 0 < p) (hq : 0 < q) {c : ℝ} (hc : 0 ≤ c) :
    0 < profilePosterior p q (fun y ↦ y ^ q * y ^ q) c -
      profilePosterior p q (fun y ↦ y ^ q) c ^ 2 := by
  rw [profileVar_eq hp hq.le hc]
  refine div_pos ?_ (profileNum_one_pos hp hc)
  set m := profilePosterior p q (fun y ↦ y ^ q) c
  have hI2 : Integrable (fun y ↦ y ^ q * y ^ q * Real.exp (-(y ^ p + c * y ^ q)))
      (volume.restrict (Ioi 0)) :=
    integrableOn_profile hp hc ((measurable_id.pow_const q).mul (measurable_id.pow_const q))
      (Mψ := 1) (r := q + q) (add_nonneg hq.le hq.le) fun y hy ↦ by
        rw [abs_of_pos (mul_pos (Real.rpow_pos_of_pos hy q) (Real.rpow_pos_of_pos hy q)),
          Real.rpow_add hy, one_mul]
  have hI1 : Integrable (fun y ↦ y ^ q * Real.exp (-(y ^ p + c * y ^ q)))
      (volume.restrict (Ioi 0)) :=
    integrableOn_profile hp hc (measurable_id.pow_const q) (Mψ := 1) (r := q) hq.le
      (abs_rpow_le_self_rpow q)
  have hI0 : Integrable (fun y ↦ (1 : ℝ) * Real.exp (-(y ^ p + c * y ^ q)))
      (volume.restrict (Ioi 0)) :=
    integrableOn_profile hp hc measurable_const (Mψ := 1) (r := 0) le_rfl
      (fun y hy ↦ by simp)
  have hint : IntegrableOn (fun y ↦ (y ^ q - m) ^ 2 * Real.exp (-(y ^ p + c * y ^ q))) (Ioi 0) := by
    refine ((hI2.sub (hI1.const_mul (2 * m))).add (hI0.const_mul (m ^ 2))).congr
      (Filter.Eventually.of_forall fun y ↦ ?_)
    simp only [Pi.add_apply, Pi.sub_apply]
    ring
  unfold profileNum
  rw [setIntegral_pos_iff_support_of_nonneg_ae
    (Filter.Eventually.of_forall fun y ↦ by
      simp only [Pi.zero_apply]
      exact mul_nonneg (sq_nonneg _) (Real.exp_pos _).le) hint]
  -- beyond `max (m^{1/q}) 0 + 1` the integrand never vanishes
  have hsub : Ioi (max (m ^ q⁻¹) 0 + 1) ⊆
      Function.support (fun y ↦ (y ^ q - m) ^ 2 * Real.exp (-(y ^ p + c * y ^ q))) ∩ Ioi 0 := by
    intro y hy
    have hy1 : max (m ^ q⁻¹) 0 + 1 < y := hy
    have hy0 : (0 : ℝ) < y := by linarith [le_max_right (m ^ q⁻¹) 0]
    refine ⟨?_, hy0⟩
    rw [Function.mem_support]
    intro h0
    rcases mul_eq_zero.mp h0 with h0 | h0
    · have hyq : y ^ q = m := by
        have := pow_eq_zero_iff (n := 2) (by norm_num) |>.mp h0
        linarith
      have : y = m ^ q⁻¹ := by rw [← hyq, Real.rpow_rpow_inv hy0.le hq.ne']
      linarith [le_max_left (m ^ q⁻¹) 0]
    · exact (Real.exp_pos _).ne' h0
  refine lt_of_lt_of_le ?_ (measure_mono hsub)
  rw [Real.volume_Ioi]
  simp

/-- `A''(c) = Var_c(y^q)`: the second derivative of the log-partition function. -/
theorem hasDerivAt_deriv_profileLogZ {p q : ℝ} (hp : 0 < p) (hq : 0 ≤ q) {c : ℝ} (hc : 0 < c) :
    HasDerivAt (deriv fun c ↦ profileLogZ p q c)
      (profilePosterior p q (fun y ↦ y ^ q * y ^ q) c -
        profilePosterior p q (fun y ↦ y ^ q) c ^ 2) c := by
  have hZne := (profileNum_one_pos (q := q) hp hc.le).ne'
  have h := (hasDerivAt_profilePosterior_poly hp hq (ψ := fun y ↦ y ^ q) (measurable_id.pow_const q)
    (Mψ := 1) (r := q) hq (abs_rpow_le_self_rpow q) hc hZne).neg
  rw [neg_neg, ← sq] at h
  refine h.congr_of_eventuallyEq ?_
  filter_upwards [Ioi_mem_nhds hc] with c' hc'
  exact (hasDerivAt_profileLogZ hp hq hc').deriv

/-- **Log-convexity of the wall partition function**: `A = log Z` is convex on `(0,∞)`. -/
theorem profileLogZ_convexOn {p q : ℝ} (hp : 0 < p) (hq : 0 ≤ q) :
    ConvexOn ℝ (Ioi 0) (fun c ↦ profileLogZ p q c) := by
  refine convexOn_of_deriv2_nonneg (convex_Ioi 0) ?_ ?_ ?_ ?_
  · exact fun c hc ↦ (hasDerivAt_profileLogZ hp hq hc).continuousAt.continuousWithinAt
  · rw [interior_Ioi]
    exact fun c hc ↦ (hasDerivAt_profileLogZ hp hq hc).differentiableAt.differentiableWithinAt
  · rw [interior_Ioi]
    exact fun c hc ↦
      (hasDerivAt_deriv_profileLogZ hp hq hc).differentiableAt.differentiableWithinAt
  · rw [interior_Ioi]
    intro c hc
    change 0 ≤ deriv (deriv fun c ↦ profileLogZ p q c) c
    rw [(hasDerivAt_deriv_profileLogZ hp hq hc).deriv]
    exact profileVar_nonneg hp hq (le_of_lt hc)

/-- **The mean map is strictly decreasing**: `c ↦ ⟨y^q⟩_c` is strictly antitone on `(0,∞)` for
`q > 0`; the wall is traversed monotonically by the sufficient statistic. -/
theorem profileMean_strictAntiOn {p q : ℝ} (hp : 0 < p) (hq : 0 < q) :
    StrictAntiOn (fun c ↦ profilePosterior p q (fun y ↦ y ^ q) c) (Ioi 0) := by
  have hd : ∀ c ∈ Ioi (0 : ℝ), HasDerivAt (fun c ↦ profilePosterior p q (fun y ↦ y ^ q) c)
      (-(profilePosterior p q (fun y ↦ y ^ q * y ^ q) c -
        profilePosterior p q (fun y ↦ y ^ q) c * profilePosterior p q (fun y ↦ y ^ q) c)) c :=
    fun c hc ↦ hasDerivAt_profilePosterior_poly hp hq.le (ψ := fun y ↦ y ^ q)
      (measurable_id.pow_const q) (Mψ := 1) (r := q) hq.le (abs_rpow_le_self_rpow q) hc
      (profileNum_one_pos hp (le_of_lt hc)).ne'
  refine strictAntiOn_of_deriv_neg (convex_Ioi 0) ?_ ?_
  · exact fun c hc ↦ (hd c hc).continuousAt.continuousWithinAt
  · rw [interior_Ioi]
    intro c hc
    rw [(hd c hc).deriv, ← sq]
    linarith [profileVar_pos hp hq (le_of_lt (show (0 : ℝ) < c from hc))]

/-- The mean map is injective on `(0,∞)`: the position on the wall is determined by the
response `⟨y^q⟩_c`. -/
theorem profileMean_injOn {p q : ℝ} (hp : 0 < p) (hq : 0 < q) :
    InjOn (fun c ↦ profilePosterior p q (fun y ↦ y ^ q) c) (Ioi 0) :=
  (profileMean_strictAntiOn hp hq).injOn

end Laplace.Multi
