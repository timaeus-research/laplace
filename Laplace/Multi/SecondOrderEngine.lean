/-
Copyright (c) 2026 Timaeus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Timaeus
-/
import Mathlib

/-!
# The second-order comparison engine

Abstract analysis for the second-order term of a normalized Laplace moment.
A weight `w h` deforms a reference weight `w₀` through a correction `V h`,
`w h = w₀ e^{-V h}`, whose finite linear jet `S h = ∑_{ρ ≤ m < 2ρ} h^m B m` is
subtracted; the residual `(w h - w₀ + w₀ S h)/h^{2ρ}` converges pointwise to
`w₀ (½ Q² - R)` when `V h / h^ρ → Q` and `(V h - S h)/h^{2ρ} → R`
(`tendsto_exp_neg_sub_one_add_linear_div_pow`). Integrating against an
observable `A` (dominated convergence supplied by the caller) and normalizing
gives the second-order expansion of the moment `M h A = ∫ A w h / ∫ w h`:

  `(M h A - E₀ A + ∑ h^m Cov₀(A, B m)) / h^{2ρ} → Cov₀(A, ½Q² - R) - E₀(B ρ) Cov₀(A, B ρ)`

(`tendsto_normalizedMoment_linear_subtracted_div_pow`). The endpoint bound
`|e^{-v} - 1 + v| ≤ v² (1 + e^{-v})` (`abs_exp_neg_sub_one_add_le`) is the
domination tool for the Laplace instantiation: the residual is controlled by the
reference and the deformed weights, both Gaussian-dominated, with no positivity
of the perturbation required.
-/

open MeasureTheory Filter Topology Set

namespace Laplace.Multi

/-! ### The scalar exponential estimates -/

/-- `|e^u - 1 - u| ≤ e^u u²` for `u ≥ 0` (Taylor at `0` with the derivative bounded by `e^u`). -/
theorem abs_exp_sub_one_sub_le_of_nonneg {u : ℝ} (hu : 0 ≤ u) :
    |Real.exp u - 1 - u| ≤ Real.exp u * u ^ 2 := by
  rcases eq_or_lt_of_le hu with rfl | hu'
  · simp
  have hf : ContDiffOn ℝ (1 + 1) Real.exp (Icc 0 u) := Real.contDiff_exp.contDiffOn
  have hU : UniqueDiffOn ℝ (Icc (0 : ℝ) u) := uniqueDiffOn_Icc hu'
  have hC : ∀ y ∈ Icc (0 : ℝ) u,
      ‖iteratedDerivWithin (1 + 1) Real.exp (Icc 0 u) y‖ ≤ Real.exp u := by
    intro y hy
    rw [iteratedDerivWithin_eq_iteratedDeriv hU Real.contDiff_exp.contDiffAt hy,
      iteratedDeriv_eq_iterate, Real.iter_deriv_exp, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
    exact Real.exp_le_exp.mpr hy.2
  have h := taylor_mean_remainder_bound (f := Real.exp) (a := 0) (b := u) (x := u) hu
    hf (right_mem_Icc.mpr hu) hC
  rw [taylor_within_apply] at h
  have h0 : iteratedDerivWithin 0 Real.exp (Icc 0 u) 0 = 1 := by simp
  have h1 : iteratedDerivWithin 1 Real.exp (Icc 0 u) 0 = 1 := by
    rw [iteratedDerivWithin_eq_iteratedDeriv hU Real.contDiff_exp.contDiffAt
      (left_mem_Icc.mpr hu), iteratedDeriv_eq_iterate, Real.iter_deriv_exp, Real.exp_zero]
  simp only [Finset.sum_range_succ, h1, Nat.factorial, Nat.cast_one,
    inv_one, sub_zero, pow_one, one_mul, mul_one, smul_eq_mul, Real.norm_eq_abs] at h
  calc |Real.exp u - 1 - u| = |Real.exp u - (1 + u)| := by ring_nf
    _ ≤ Real.exp u * u ^ 2 / 1 := by
        convert h using 2
        norm_num
    _ = Real.exp u * u ^ 2 := by ring

/-- **Endpoint bound**: `|e^{-v} - 1 + v| ≤ v² (1 + e^{-v})`. -/
theorem abs_exp_neg_sub_one_add_le (v : ℝ) :
    |Real.exp (-v) - 1 + v| ≤ v ^ 2 * (1 + Real.exp (-v)) := by
  rcases le_or_gt 0 v with hv | hv
  · -- `v ≥ 0`: `e^{-v} ≤ 1/(1+v) ≤ 1 - v + v²`
    have h1 : 1 - v ≤ Real.exp (-v) := by
      have := Real.add_one_le_exp (-v)
      linarith
    have h3 : 1 + v ≤ Real.exp v := by
      have := Real.add_one_le_exp v
      linarith
    have h1v : 0 < 1 + v := by linarith
    have hinv : Real.exp (-v) ≤ (1 + v)⁻¹ := by
      rw [Real.exp_neg]
      exact inv_anti₀ h1v h3
    have h2 : (1 + v)⁻¹ ≤ 1 - v + v ^ 2 := by
      rw [inv_le_iff_one_le_mul₀ h1v]
      nlinarith [pow_nonneg hv 3]
    rw [abs_le]
    constructor
    · nlinarith [Real.exp_pos (-v), sq_nonneg v]
    · nlinarith [Real.exp_pos (-v), sq_nonneg v]
  · -- `v < 0`: apply the Taylor bound to `u = -v`
    have hu : 0 ≤ -v := by linarith
    have hk := abs_exp_sub_one_sub_le_of_nonneg hu
    have heq : |Real.exp (-v) - 1 + v| = |Real.exp (-v) - 1 - -v| := by ring_nf
    rw [heq]
    calc |Real.exp (-v) - 1 - -v| ≤ Real.exp (-v) * (-v) ^ 2 := hk
      _ = v ^ 2 * Real.exp (-v) := by ring
      _ ≤ v ^ 2 * (1 + Real.exp (-v)) := by nlinarith [sq_nonneg v, Real.exp_pos (-v)]

/-- The second-order quotient `(e^{-w} - 1 + w)/w²`, filled in by its limit `1/2` at `0`. -/
noncomputable def expQuot (w : ℝ) : ℝ :=
  if w = 0 then 1 / 2 else (Real.exp (-w) - 1 + w) / w ^ 2

theorem exp_neg_sub_one_add_eq_expQuot_mul (w : ℝ) :
    Real.exp (-w) - 1 + w = expQuot w * w ^ 2 := by
  unfold expQuot
  split_ifs with h
  · subst h
    simp
  · field_simp

/-- `|e^{-w} - 1 + w - w²/2| ≤ (2/9) |w|³` for `|w| ≤ 1`. -/
theorem abs_exp_neg_sub_one_add_sub_half_sq_le {w : ℝ} (hw : |w| ≤ 1) :
    |Real.exp (-w) - 1 + w - w ^ 2 / 2| ≤ 2 / 9 * |w| ^ 3 := by
  have h := Real.exp_bound (x := -w) (by rwa [abs_neg]) (n := 3) (by norm_num)
  norm_num [Finset.sum_range_succ, Nat.factorial] at h
  have heq : |Real.exp (-w) - 1 + w - w ^ 2 / 2| = |Real.exp (-w) - (1 - w + w ^ 2 / 2)| := by
    ring_nf
  rw [heq]
  calc |Real.exp (-w) - (1 - w + w ^ 2 / 2)| ≤ |w| ^ 3 * (2 / 9) := by
        convert h using 2
        ring
    _ = 2 / 9 * |w| ^ 3 := by ring

/-- `expQuot → 1/2` at `0`. -/
theorem tendsto_expQuot_zero : Tendsto expQuot (𝓝 0) (𝓝 (1 / 2)) := by
  rw [Metric.tendsto_nhds]
  intro ε hε
  rw [Metric.eventually_nhds_iff]
  refine ⟨min 1 ε, lt_min one_pos hε, fun w hw ↦ ?_⟩
  rw [dist_zero_right, Real.norm_eq_abs] at hw
  have hw1 : |w| ≤ 1 := (le_of_lt hw).trans (min_le_left _ _)
  have hwε : |w| < ε := lt_of_lt_of_le hw (min_le_right _ _)
  unfold expQuot
  split_ifs with h0
  · simpa using hε
  · rw [Real.dist_eq]
    have hw2 : 0 < w ^ 2 := by positivity
    have hq : (Real.exp (-w) - 1 + w) / w ^ 2 - 1 / 2 =
        (Real.exp (-w) - 1 + w - w ^ 2 / 2) / w ^ 2 := by
      field_simp
    rw [hq, abs_div, abs_of_pos hw2]
    calc |Real.exp (-w) - 1 + w - w ^ 2 / 2| / w ^ 2 ≤ 2 / 9 * |w| ^ 3 / w ^ 2 :=
          div_le_div_of_nonneg_right (abs_exp_neg_sub_one_add_sub_half_sq_le hw1) hw2.le
      _ = 2 / 9 * |w| := by
          have : w ^ 2 = |w| ^ 2 := (sq_abs w).symm
          rw [this]
          have hwne : |w| ≠ 0 := abs_ne_zero.mpr h0
          field_simp
      _ < ε := by
          have : 2 / 9 * |w| ≤ |w| := by nlinarith [abs_nonneg w]
          linarith

/-! ### The pointwise second-order engine -/

/-- **Pointwise engine**: if `V h / h^ρ → Q` and `(V h - S h)/h^{2ρ} → R`, then
`(e^{-V h} - 1 + S h)/h^{2ρ} → ½ Q² - R`. -/
theorem tendsto_exp_neg_sub_one_add_linear_div_pow {V S : ℝ → ℝ} {ρ : ℕ} (hρ : 0 < ρ) {Q R : ℝ}
    (hV : Tendsto (fun h ↦ V h / h ^ ρ) (𝓝[>] (0 : ℝ)) (𝓝 Q))
    (hR : Tendsto (fun h ↦ (V h - S h) / h ^ (2 * ρ)) (𝓝[>] (0 : ℝ)) (𝓝 R)) :
    Tendsto (fun h ↦ (Real.exp (-V h) - 1 + S h) / h ^ (2 * ρ)) (𝓝[>] (0 : ℝ))
      (𝓝 (1 / 2 * Q ^ 2 - R)) := by
  have hpow : Tendsto (fun h : ℝ ↦ h ^ ρ) (𝓝[>] (0 : ℝ)) (𝓝 0) := by
    have := ((continuous_pow ρ).tendsto (0 : ℝ)).mono_left (nhdsWithin_le_nhds (s := Set.Ioi 0))
    rwa [zero_pow hρ.ne'] at this
  have hV0 : Tendsto V (𝓝[>] (0 : ℝ)) (𝓝 0) := by
    have := hV.mul hpow
    rw [mul_zero] at this
    refine this.congr' ?_
    filter_upwards [self_mem_nhdsWithin] with h hh
    have : (h : ℝ) ≠ 0 := ne_of_gt hh
    field_simp
  have hG : Tendsto (fun h ↦ expQuot (V h)) (𝓝[>] (0 : ℝ)) (𝓝 (1 / 2)) :=
    tendsto_expQuot_zero.comp hV0
  have hmain := (hG.mul (hV.pow 2)).sub hR
  refine hmain.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with h hh
  have hne : (h : ℝ) ≠ 0 := ne_of_gt hh
  have hpne : h ^ ρ ≠ 0 := pow_ne_zero _ hne
  rw [show Real.exp (-V h) - 1 + S h = (Real.exp (-V h) - 1 + V h) - (V h - S h) by ring,
    exp_neg_sub_one_add_eq_expQuot_mul, show h ^ (2 * ρ) = (h ^ ρ) ^ 2 by rw [mul_comm, pow_mul]]
  field_simp

/-! ### The integral layer -/

/-- **Dominated convergence for the linear-subtracted residual.** With
`F h x = (w h x - w₀ x + w₀ x · ∑_{j<ρ} h^{ρ+j} B (ρ+j) x) / h^{2ρ}` converging a.e. to
`w₀ T` and dominated after multiplication by `A`, the residual moments converge:
`(∫ A w h - ∫ A w₀ + ∑ h^{ρ+j} ∫ A w₀ B) / h^{2ρ} → ∫ A w₀ T`. -/
theorem tendsto_integral_linear_subtracted {X : Type*} [MeasurableSpace X] {μ : Measure X}
    (A w₀ T : X → ℝ) (w : ℝ → X → ℝ) (B : ℕ → X → ℝ) (ρ : ℕ)
    (hlim : ∀ᵐ x ∂μ, Tendsto (fun h : ℝ ↦ A x * ((w h x - w₀ x +
      w₀ x * ∑ j ∈ Finset.range ρ, h ^ (ρ + j) * B (ρ + j) x) / h ^ (2 * ρ)))
      (𝓝[>] (0 : ℝ)) (𝓝 (A x * (w₀ x * T x))))
    (hmeas : ∀ᶠ h in 𝓝[>] (0 : ℝ), AEStronglyMeasurable (fun x ↦ A x * ((w h x - w₀ x +
      w₀ x * ∑ j ∈ Finset.range ρ, h ^ (ρ + j) * B (ρ + j) x) / h ^ (2 * ρ))) μ)
    {G : X → ℝ} (hG : Integrable G μ)
    (hdom : ∀ᶠ h in 𝓝[>] (0 : ℝ), ∀ᵐ x ∂μ, ‖A x * ((w h x - w₀ x +
      w₀ x * ∑ j ∈ Finset.range ρ, h ^ (ρ + j) * B (ρ + j) x) / h ^ (2 * ρ))‖ ≤ G x)
    (hintw : ∀ᶠ h in 𝓝[>] (0 : ℝ), Integrable (fun x ↦ A x * w h x) μ)
    (hintw₀ : Integrable (fun x ↦ A x * w₀ x) μ)
    (hintB : ∀ j, Integrable (fun x ↦ A x * (w₀ x * B (ρ + j) x)) μ) :
    Tendsto (fun h : ℝ ↦ ((∫ x, A x * w h x ∂μ) - (∫ x, A x * w₀ x ∂μ) +
        ∑ j ∈ Finset.range ρ, h ^ (ρ + j) * ∫ x, A x * (w₀ x * B (ρ + j) x) ∂μ) / h ^ (2 * ρ))
      (𝓝[>] (0 : ℝ)) (𝓝 (∫ x, A x * (w₀ x * T x) ∂μ)) := by
  have hdct := tendsto_integral_filter_of_dominated_convergence G hmeas hdom hG hlim
  refine hdct.congr' ?_
  filter_upwards [hintw, self_mem_nhdsWithin] with h hint hh
  have hsum_int : Integrable (fun x ↦ A x * (w₀ x *
      ∑ j ∈ Finset.range ρ, h ^ (ρ + j) * B (ρ + j) x)) μ := by
    have : (fun x ↦ A x * (w₀ x * ∑ j ∈ Finset.range ρ, h ^ (ρ + j) * B (ρ + j) x)) =
        fun x ↦ ∑ j ∈ Finset.range ρ, h ^ (ρ + j) * (A x * (w₀ x * B (ρ + j) x)) := by
      funext x
      rw [Finset.mul_sum, Finset.mul_sum]
      refine Finset.sum_congr rfl fun j _ ↦ ?_
      ring
    rw [this]
    exact integrable_finsetSum _ fun j _ ↦ (hintB j).const_mul _
  have hsum_val : ∫ x, A x * (w₀ x * ∑ j ∈ Finset.range ρ, h ^ (ρ + j) * B (ρ + j) x) ∂μ =
      ∑ j ∈ Finset.range ρ, h ^ (ρ + j) * ∫ x, A x * (w₀ x * B (ρ + j) x) ∂μ := by
    have : (fun x ↦ A x * (w₀ x * ∑ j ∈ Finset.range ρ, h ^ (ρ + j) * B (ρ + j) x)) =
        fun x ↦ ∑ j ∈ Finset.range ρ, h ^ (ρ + j) * (A x * (w₀ x * B (ρ + j) x)) := by
      funext x
      rw [Finset.mul_sum, Finset.mul_sum]
      refine Finset.sum_congr rfl fun j _ ↦ ?_
      ring
    rw [this, integral_finsetSum _ fun j _ ↦ (hintB j).const_mul _]
    refine Finset.sum_congr rfl fun j _ ↦ ?_
    rw [integral_const_mul]
  have hpt : (fun x ↦ A x * ((w h x - w₀ x +
      w₀ x * ∑ j ∈ Finset.range ρ, h ^ (ρ + j) * B (ρ + j) x) / h ^ (2 * ρ))) =
      fun x ↦ (A x * w h x - A x * w₀ x +
        A x * (w₀ x * ∑ j ∈ Finset.range ρ, h ^ (ρ + j) * B (ρ + j) x)) / h ^ (2 * ρ) := by
    funext x
    ring
  have hsub : Integrable (fun x ↦ A x * w h x - A x * w₀ x) μ := hint.sub hintw₀
  rw [hpt, integral_div, integral_add hsub hsum_int, integral_sub hint hintw₀, hsum_val]

/-! ### The normalization layer -/

/-- Sums `∑_{j<ρ} h^j c_j → c_0` as `h → 0⁺` (`ρ > 0`). -/
theorem tendsto_sum_pow_mul {ρ : ℕ} (hρ : 0 < ρ) (c : ℕ → ℝ) :
    Tendsto (fun h : ℝ ↦ ∑ j ∈ Finset.range ρ, h ^ j * c (ρ + j)) (𝓝[>] (0 : ℝ)) (𝓝 (c ρ)) := by
  have hcont : Continuous fun h : ℝ ↦ ∑ j ∈ Finset.range ρ, h ^ j * c (ρ + j) :=
    continuous_finsetSum _ fun j _ ↦ (continuous_pow j).mul continuous_const
  have h0 : (∑ j ∈ Finset.range ρ, (0 : ℝ) ^ j * c (ρ + j)) = c ρ := by
    rw [Finset.sum_eq_single 0]
    · simp
    · intro j _ hj
      rw [zero_pow hj, zero_mul]
    · intro h
      exact absurd (Finset.mem_range.mpr hρ) h
  have := (hcont.tendsto 0).mono_left (nhdsWithin_le_nhds (s := Set.Ioi 0))
  rwa [h0] at this

/-- **Normalization of the second-order expansion.** From the residual expansions of the
numerator `N` and the partition `Z` (both to order `h^{2ρ}` after subtracting the linear
jets `a`, `b`), the normalized moment satisfies
`(N/Z - N₀/Z₀ + ∑ h^{ρ+j} c_{ρ+j}) / h^{2ρ} → (α - (N₀/Z₀) β)/Z₀ - (b ρ / Z₀) c ρ`, where
`c m = (a m - (N₀/Z₀) b m)/Z₀` are the covariance coefficients. -/
theorem tendsto_normalized_div_pow_of_linear_subtracted {N Z : ℝ → ℝ} {N₀ Z₀ α β : ℝ}
    {a b : ℕ → ℝ} {ρ : ℕ} (hρ : 0 < ρ) (hZ₀ : 0 < Z₀)
    (hN : Tendsto (fun h : ℝ ↦ (N h - N₀ + ∑ j ∈ Finset.range ρ, h ^ (ρ + j) * a (ρ + j)) /
      h ^ (2 * ρ)) (𝓝[>] (0 : ℝ)) (𝓝 α))
    (hZ : Tendsto (fun h : ℝ ↦ (Z h - Z₀ + ∑ j ∈ Finset.range ρ, h ^ (ρ + j) * b (ρ + j)) /
      h ^ (2 * ρ)) (𝓝[>] (0 : ℝ)) (𝓝 β)) :
    Tendsto (fun h : ℝ ↦ (N h / Z h - N₀ / Z₀ +
        ∑ j ∈ Finset.range ρ, h ^ (ρ + j) * ((a (ρ + j) - N₀ / Z₀ * b (ρ + j)) / Z₀)) /
        h ^ (2 * ρ)) (𝓝[>] (0 : ℝ))
      (𝓝 ((α - N₀ / Z₀ * β) / Z₀ - b ρ / Z₀ * ((a ρ - N₀ / Z₀ * b ρ) / Z₀))) := by
  set c : ℕ → ℝ := fun m ↦ (a m - N₀ / Z₀ * b m) / Z₀ with hc_def
  have hpow : Tendsto (fun h : ℝ ↦ h ^ ρ) (𝓝[>] (0 : ℝ)) (𝓝 0) := by
    have := ((continuous_pow ρ).tendsto (0 : ℝ)).mono_left (nhdsWithin_le_nhds (s := Set.Ioi 0))
    rwa [zero_pow hρ.ne'] at this
  have hsb := tendsto_sum_pow_mul hρ b
  have hsc := tendsto_sum_pow_mul hρ c
  -- the partition converges and its first-order rate is `-b ρ`
  have hZrate : Tendsto (fun h : ℝ ↦ (Z h - Z₀) / h ^ ρ) (𝓝[>] (0 : ℝ)) (𝓝 (-b ρ)) := by
    have := (hZ.mul hpow).sub hsb
    rw [mul_zero, zero_sub] at this
    refine this.congr' ?_
    filter_upwards [self_mem_nhdsWithin] with h hh
    have hne : (h : ℝ) ≠ 0 := ne_of_gt hh
    have hpne : h ^ ρ ≠ 0 := pow_ne_zero _ hne
    have hsum : (∑ j ∈ Finset.range ρ, h ^ (ρ + j) * b (ρ + j)) =
        h ^ ρ * ∑ j ∈ Finset.range ρ, h ^ j * b (ρ + j) := by
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun j _ ↦ ?_
      rw [pow_add]
      ring
    rw [hsum, show h ^ (2 * ρ) = (h ^ ρ) ^ 2 by rw [mul_comm, pow_mul]]
    field_simp
    ring
  have hZlim : Tendsto Z (𝓝[>] (0 : ℝ)) (𝓝 Z₀) := by
    have := (hZrate.mul hpow)
    rw [mul_zero] at this
    have h2 : Tendsto (fun h : ℝ ↦ (Z h - Z₀) / h ^ ρ * h ^ ρ + Z₀) (𝓝[>] (0 : ℝ)) (𝓝 (0 + Z₀)) :=
      this.add tendsto_const_nhds
    rw [zero_add] at h2
    refine h2.congr' ?_
    filter_upwards [self_mem_nhdsWithin] with h hh
    have hpne : h ^ ρ ≠ 0 := pow_ne_zero _ (ne_of_gt hh)
    rw [div_mul_cancel₀ _ hpne, sub_add_cancel]
  have hZpos : ∀ᶠ h in 𝓝[>] (0 : ℝ), 0 < Z h := hZlim.eventually (lt_mem_nhds hZ₀)
  -- the two limiting pieces
  have hfirst : Tendsto (fun h : ℝ ↦
      ((N h - N₀ + ∑ j ∈ Finset.range ρ, h ^ (ρ + j) * a (ρ + j)) / h ^ (2 * ρ) -
        N₀ / Z₀ * ((Z h - Z₀ + ∑ j ∈ Finset.range ρ, h ^ (ρ + j) * b (ρ + j)) / h ^ (2 * ρ))) / Z h)
      (𝓝[>] (0 : ℝ)) (𝓝 ((α - N₀ / Z₀ * β) / Z₀)) :=
    (hN.sub (hZ.const_mul _)).div hZlim hZ₀.ne'
  have hsecond : Tendsto (fun h : ℝ ↦ (Z h - Z₀) / h ^ ρ / Z h *
      ∑ j ∈ Finset.range ρ, h ^ j * c (ρ + j)) (𝓝[>] (0 : ℝ)) (𝓝 (-b ρ / Z₀ * c ρ)) :=
    (hZrate.div hZlim hZ₀.ne').mul hsc
  have hmain := hfirst.add hsecond
  have hlimeq : (α - N₀ / Z₀ * β) / Z₀ + -b ρ / Z₀ * c ρ =
      (α - N₀ / Z₀ * β) / Z₀ - b ρ / Z₀ * ((a ρ - N₀ / Z₀ * b ρ) / Z₀) := by
    simp only [hc_def]
    ring
  rw [hlimeq] at hmain
  refine hmain.congr' ?_
  filter_upwards [self_mem_nhdsWithin, hZpos] with h hh hZh
  have hne : (h : ℝ) ≠ 0 := ne_of_gt hh
  have hpne : h ^ ρ ≠ 0 := pow_ne_zero _ hne
  have hZne : Z h ≠ 0 := hZh.ne'
  -- rewrite the three sums through the leading power
  have hsa : (∑ j ∈ Finset.range ρ, h ^ (ρ + j) * a (ρ + j)) =
      h ^ ρ * ∑ j ∈ Finset.range ρ, h ^ j * a (ρ + j) := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ ↦ ?_
    rw [pow_add]
    ring
  have hsb' : (∑ j ∈ Finset.range ρ, h ^ (ρ + j) * b (ρ + j)) =
      h ^ ρ * ∑ j ∈ Finset.range ρ, h ^ j * b (ρ + j) := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ ↦ ?_
    rw [pow_add]
    ring
  have hsc' : (∑ j ∈ Finset.range ρ, h ^ (ρ + j) * ((a (ρ + j) - N₀ / Z₀ * b (ρ + j)) / Z₀)) =
      h ^ ρ * ∑ j ∈ Finset.range ρ, h ^ j * c (ρ + j) := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ ↦ ?_
    simp only [hc_def]
    rw [pow_add]
    ring
  have hcsum : (∑ j ∈ Finset.range ρ, h ^ j * c (ρ + j)) =
      ((∑ j ∈ Finset.range ρ, h ^ j * a (ρ + j)) -
        N₀ / Z₀ * ∑ j ∈ Finset.range ρ, h ^ j * b (ρ + j)) / Z₀ := by
    rw [Finset.mul_sum, ← Finset.sum_sub_distrib, Finset.sum_div]
    refine Finset.sum_congr rfl fun j _ ↦ ?_
    simp only [hc_def]
    ring
  rw [hsa, hsb', hsc', hcsum, show h ^ (2 * ρ) = (h ^ ρ) ^ 2 by rw [mul_comm, pow_mul]]
  field_simp
  ring

end Laplace.Multi
