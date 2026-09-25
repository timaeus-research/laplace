/-
Copyright (c) 2026 Timaeus Research. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniel Murfet
-/
import Mathlib
import Laplace.Multi.ProfileFamily

/-!
# The Gamma tail of the wall profile: `c² Var_c(y^q) → 1/q`

Far from the wall (`c → ∞`) the profile law `ρ_c ∝ e^{-(y^p + c y^q)}` is dominated by the
`q`-monomial, and the rescaled statistic `X = c y^q` converges to the Gamma law of shape `1/q`:
substituting `x = y^q` and `x = z/c`,

  `∫₀^∞ (y^q)^k e^{-(y^p + c y^q)} dy
      = (1/q) c^{-(k + 1/q)} ∫₀^∞ z^{k + 1/q − 1} e^{-z} e^{-(z/c)^{p/q}} dz`

(`profileMoment_eq_tail`), and the last integral tends to `Γ(k + 1/q)` by dominated convergence
(`tendsto_tailIntegral`). Hence `c ⟨y^q⟩_c → 1/q`, `c² ⟨y^q y^q⟩_c → (1/q)(1/q + 1)` and

  `c² Var_c(y^q) → 1/q`   (`tendsto_sq_mul_profileVar`):

the **response-active exponent** of the wall is `κ = 1/q`, the RLCT of the dominant monomial `w^q`
on the half-line. With `ProfileTailLength` and `WallWindowLength` this gives the receding-wall law
`ℓ_t(c₀ t^{-σ*}, a₁) / log t → σ* /√q` (`WallRecedes`).
-/

open MeasureTheory Filter Topology Set

namespace Laplace.Multi

/-- The `k`-th profile moment of the wall statistic,
`N_k(c) = ∫₀^∞ (y^q)^k e^{-(y^p + c y^q)} dy`. -/
noncomputable def profileMoment (p q k c : ℝ) : ℝ :=
  ∫ y in Ioi (0 : ℝ), (y ^ q) ^ k * Real.exp (-(y ^ p + c * y ^ q))

/-- The tail integral `I_k(c) = ∫₀^∞ z^{k + 1/q − 1} e^{-z} e^{-(z/c)^{p/q}} dz`. -/
noncomputable def tailIntegral (p q k c : ℝ) : ℝ :=
  ∫ z in Ioi (0 : ℝ), z ^ (k + 1 / q - 1) * Real.exp (-z) * Real.exp (-((z / c) ^ (p / q)))

/-- Substitution `x = y^q`. -/
theorem profileMoment_subst {p q : ℝ} (hq : 0 < q) (k c : ℝ) :
    profileMoment p q k c =
      ∫ x in Ioi (0 : ℝ), (1 / q) * (x ^ (1 / q - 1) *
        (x ^ k * Real.exp (-(x ^ (p / q) + c * x)))) := by
  unfold profileMoment
  have key := integral_comp_rpow_Ioi_of_pos
    (g := fun y ↦ (y ^ q) ^ k * Real.exp (-(y ^ p + c * y ^ q))) (one_div_pos.mpr hq)
  rw [← key]
  refine setIntegral_congr_fun measurableSet_Ioi fun x hx ↦ ?_
  have hx0 : (0 : ℝ) < x := hx
  simp only [smul_eq_mul]
  rw [← Real.rpow_mul hx0.le (1 / q) q, one_div_mul_cancel hq.ne', Real.rpow_one,
    ← Real.rpow_mul hx0.le (1 / q) p, show 1 / q * p = p / q by ring]
  ring

/-- Scaling `x = z/c`. -/
theorem tail_scale {s r c : ℝ} (hc : 0 < c) :
    ∫ x in Ioi (0 : ℝ), x ^ s * Real.exp (-(x ^ r + c * x)) =
      c ^ (-(s + 1)) * ∫ z in Ioi (0 : ℝ), z ^ s * Real.exp (-z) * Real.exp (-((z / c) ^ r)) := by
  have key := integral_comp_mul_left_Ioi
    (fun z ↦ z ^ s * Real.exp (-z) * Real.exp (-((z / c) ^ r))) (0 : ℝ) hc
  rw [mul_zero, smul_eq_mul] at key
  have e : ∫ x in Ioi (0 : ℝ), (c * x) ^ s * Real.exp (-(c * x)) * Real.exp (-((c * x / c) ^ r)) =
      c ^ s * ∫ x in Ioi (0 : ℝ), x ^ s * Real.exp (-(x ^ r + c * x)) := by
    rw [← MeasureTheory.integral_const_mul]
    refine setIntegral_congr_fun measurableSet_Ioi fun x hx ↦ ?_
    have hx0 : (0 : ℝ) < x := hx
    rw [Real.mul_rpow hc.le hx0.le, mul_div_cancel_left₀ _ hc.ne', neg_add, Real.exp_add]
    ring
  rw [e] at key
  have hcs : c ^ s ≠ 0 := (Real.rpow_pos_of_pos hc _).ne'
  rw [show c ^ (-(s + 1)) = (c ^ s)⁻¹ * c⁻¹ by
    rw [Real.rpow_neg hc.le, Real.rpow_add hc, Real.rpow_one, mul_inv], mul_assoc, ← key,
    inv_mul_cancel_left₀ hcs]

/-- The profile moment as a rescaled tail integral. -/
theorem profileMoment_eq_tail {p q : ℝ} (hq : 0 < q) (k : ℝ) {c : ℝ} (hc : 0 < c) :
    profileMoment p q k c = (1 / q) * (c ^ (-(k + 1 / q)) * tailIntegral p q k c) := by
  rw [profileMoment_subst hq, MeasureTheory.integral_const_mul]
  congr 1
  have e : ∀ x ∈ Ioi (0 : ℝ), x ^ (1 / q - 1) * (x ^ k * Real.exp (-(x ^ (p / q) + c * x))) =
      x ^ (k + 1 / q - 1) * Real.exp (-(x ^ (p / q) + c * x)) := fun x hx ↦ by
    have hx0 : (0 : ℝ) < x := hx
    rw [← mul_assoc, ← Real.rpow_add hx0]
    congr 2
    ring
  rw [setIntegral_congr_fun measurableSet_Ioi e, tail_scale hc]
  unfold tailIntegral
  congr 2
  ring

/-- `∫₀^∞ z^s e^{-z} = Γ(s + 1)`. -/
theorem integral_rpow_mul_exp_neg_eq_Gamma {s : ℝ} (hs : -1 < s) :
    ∫ z in Ioi (0 : ℝ), z ^ s * Real.exp (-z) = Real.Gamma (s + 1) := by
  rw [Real.Gamma_eq_integral (by linarith), add_sub_cancel_right]
  exact setIntegral_congr_fun measurableSet_Ioi fun z _ ↦ mul_comm _ _

/-- **The tail integral tends to the Gamma function**: `I_k(c) → Γ(k + 1/q)` as `c → ∞`. -/
theorem tendsto_tailIntegral {p q : ℝ} (hp : 0 < p) (hq : 0 < q) {k : ℝ} (hk : 0 ≤ k) :
    Tendsto (fun c ↦ tailIntegral p q k c) atTop (𝓝 (Real.Gamma (k + 1 / q))) := by
  have hs : -1 < k + 1 / q - 1 := by
    have : 0 < 1 / q := one_div_pos.mpr hq
    linarith
  have hr : 0 < p / q := div_pos hp hq
  have hG : Real.Gamma (k + 1 / q) = ∫ z in Ioi (0 : ℝ), z ^ (k + 1 / q - 1) * Real.exp (-z) := by
    rw [integral_rpow_mul_exp_neg_eq_Gamma hs, sub_add_cancel]
  rw [hG]
  unfold tailIntegral
  have hint : IntegrableOn (fun z : ℝ ↦ z ^ (k + 1 / q - 1) * Real.exp (-z)) (Ioi 0) := by
    have := integrableOn_rpow_mul_exp_neg_rpow (p := 1) (s := k + 1 / q - 1) hs one_pos
    simpa only [Real.rpow_one] using this
  refine tendsto_integral_filter_of_dominated_convergence
    (fun z ↦ z ^ (k + 1 / q - 1) * Real.exp (-z)) ?_ ?_ hint ?_
  · exact Filter.Eventually.of_forall fun c ↦ (Measurable.aestronglyMeasurable (by fun_prop))
  · filter_upwards [eventually_gt_atTop (0 : ℝ)] with c hc
    refine (ae_restrict_iff' measurableSet_Ioi).mpr (Filter.Eventually.of_forall fun z hz ↦ ?_)
    have hz0 : (0 : ℝ) < z := hz
    rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    refine mul_le_of_le_one_right (by positivity) ?_
    rw [Real.exp_le_one_iff, neg_nonpos]
    exact Real.rpow_nonneg (by positivity) _
  · refine (ae_restrict_iff' measurableSet_Ioi).mpr (Filter.Eventually.of_forall fun z _ ↦ ?_)
    have h1 : Tendsto (fun c : ℝ ↦ (z / c) ^ (p / q)) atTop (𝓝 0) := by
      have := ((Real.continuous_rpow_const hr.le).tendsto 0).comp
        ((tendsto_const_nhds (x := z)).div_atTop (tendsto_id (x := atTop)))
      simpa [Real.zero_rpow hr.ne', Function.comp_def] using this
    have h2 : Tendsto (fun c : ℝ ↦ Real.exp (-((z / c) ^ (p / q)))) atTop (𝓝 1) := by
      have h1' := h1.neg
      rw [neg_zero] at h1'
      have := (Real.continuous_exp.tendsto 0).comp h1'
      simpa [Function.comp_def] using this
    simpa using (tendsto_const_nhds (x := z ^ (k + 1 / q - 1) * Real.exp (-z))).mul h2

/-- The profile partition function is the zeroth moment. -/
theorem profileNum_one_eq_moment (p q c : ℝ) :
    profileNum p q (fun _ ↦ 1) c = profileMoment p q 0 c := by
  unfold profileNum profileMoment
  simp

/-- The profile mean of `y^q` is the first moment ratio. -/
theorem profileNum_score_eq_moment (p q c : ℝ) :
    profileNum p q (fun y ↦ y ^ q) c = profileMoment p q 1 c := by
  unfold profileNum profileMoment
  simp

/-- The profile second moment of `y^q`. -/
theorem profileNum_score_sq_eq_moment (p q c : ℝ) :
    profileNum p q (fun y ↦ y ^ q * y ^ q) c = profileMoment p q 2 c := by
  unfold profileNum profileMoment
  refine setIntegral_congr_fun measurableSet_Ioi fun y _ ↦ ?_
  rw [Real.rpow_two, sq]

/-- `Γ(1/q) > 0`. -/
theorem Gamma_one_div_pos {q : ℝ} (hq : 0 < q) : 0 < Real.Gamma (1 / q) :=
  Real.Gamma_pos_of_pos (one_div_pos.mpr hq)

/-- **`c ⟨y^q⟩_c → 1/q`**. -/
theorem tendsto_mul_profileMean {p q : ℝ} (hp : 0 < p) (hq : 0 < q) :
    Tendsto (fun c ↦ c * profilePosterior p q (fun y ↦ y ^ q) c) atTop (𝓝 (1 / q)) := by
  have h1 := tendsto_tailIntegral hp hq (k := 1) zero_le_one
  have h0 := tendsto_tailIntegral hp hq (k := 0) le_rfl
  have hG0 : Real.Gamma (0 + 1 / q) ≠ 0 := by rw [zero_add]; exact (Gamma_one_div_pos hq).ne'
  have key := h1.div h0 hG0
  have hval : Real.Gamma (1 + 1 / q) / Real.Gamma (0 + 1 / q) = 1 / q := by
    rw [zero_add, add_comm, Real.Gamma_add_one (one_div_pos.mpr hq).ne',
      mul_div_assoc, div_self (Gamma_one_div_pos hq).ne', mul_one]
  rw [hval] at key
  refine key.congr' ?_
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with c hc
  simp only [Pi.div_apply]
  unfold profilePosterior
  rw [profileNum_score_eq_moment, profileNum_one_eq_moment, profileMoment_eq_tail hq 1 hc,
    profileMoment_eq_tail hq 0 hc]
  have hq' : (1 / q : ℝ) ≠ 0 := (one_div_pos.mpr hq).ne'
  have e : c * (1 / q * (c ^ (-(1 + 1 / q)) * tailIntegral p q 1 c) /
      (1 / q * (c ^ (-(0 + 1 / q)) * tailIntegral p q 0 c))) =
      (c * c ^ (-(1 + 1 / q)) / c ^ (-(0 + 1 / q))) *
        (tailIntegral p q 1 c / tailIntegral p q 0 c) := by
    have hc0 : c ^ (-(0 + 1 / q)) ≠ 0 := (Real.rpow_pos_of_pos hc _).ne'
    field_simp
  rw [e, zero_add, show c * c ^ (-(1 + 1 / q)) / c ^ (-(1 / q)) = 1 by
    rw [Real.rpow_neg hc.le, Real.rpow_neg hc.le, Real.rpow_add hc, Real.rpow_one, mul_inv,
      ← mul_assoc, mul_inv_cancel₀ hc.ne', one_mul, div_inv_eq_mul, inv_mul_cancel₀
      (Real.rpow_pos_of_pos hc _).ne'], one_mul]

/-- **`c² ⟨y^q y^q⟩_c → (1/q)(1/q + 1)`**. -/
theorem tendsto_sq_mul_profileSecond {p q : ℝ} (hp : 0 < p) (hq : 0 < q) :
    Tendsto (fun c ↦ c ^ 2 * profilePosterior p q (fun y ↦ y ^ q * y ^ q) c) atTop
      (𝓝 (1 / q * (1 / q + 1))) := by
  have h2 := tendsto_tailIntegral hp hq (k := 2) zero_le_two
  have h0 := tendsto_tailIntegral hp hq (k := 0) le_rfl
  have hG0 : Real.Gamma (0 + 1 / q) ≠ 0 := by rw [zero_add]; exact (Gamma_one_div_pos hq).ne'
  have key := h2.div h0 hG0
  have hq0 : (1 / q : ℝ) ≠ 0 := (one_div_pos.mpr hq).ne'
  have hval : Real.Gamma (2 + 1 / q) / Real.Gamma (0 + 1 / q) = 1 / q * (1 / q + 1) := by
    rw [zero_add, show (2 : ℝ) + 1 / q = (1 / q + 1) + 1 by ring,
      Real.Gamma_add_one (by positivity), Real.Gamma_add_one hq0,
      div_eq_iff (Gamma_one_div_pos hq).ne']
    ring
  rw [hval] at key
  refine key.congr' ?_
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with c hc
  simp only [Pi.div_apply]
  unfold profilePosterior
  rw [profileNum_score_sq_eq_moment, profileNum_one_eq_moment, profileMoment_eq_tail hq 2 hc,
    profileMoment_eq_tail hq 0 hc]
  have e : c ^ 2 * (1 / q * (c ^ (-(2 + 1 / q)) * tailIntegral p q 2 c) /
      (1 / q * (c ^ (-(0 + 1 / q)) * tailIntegral p q 0 c))) =
      (c ^ 2 * c ^ (-(2 + 1 / q)) / c ^ (-(0 + 1 / q))) *
        (tailIntegral p q 2 c / tailIntegral p q 0 c) := by
    have hc0 : c ^ (-(0 + 1 / q)) ≠ 0 := (Real.rpow_pos_of_pos hc _).ne'
    field_simp
  rw [e, zero_add, show c ^ 2 * c ^ (-(2 + 1 / q)) / c ^ (-(1 / q)) = 1 by
    rw [Real.rpow_neg hc.le, Real.rpow_neg hc.le, Real.rpow_add hc, mul_inv, ← mul_assoc,
      Real.rpow_two, mul_inv_cancel₀ (pow_ne_zero 2 hc.ne'), one_mul, div_inv_eq_mul,
      inv_mul_cancel₀ (Real.rpow_pos_of_pos hc _).ne'], one_mul]

/-- **The response-active exponent of the wall**: `c² Var_c(y^q) → 1/q`. -/
theorem tendsto_sq_mul_profileVar {p q : ℝ} (hp : 0 < p) (hq : 0 < q) :
    Tendsto (fun c ↦ c ^ 2 * (profilePosterior p q (fun y ↦ y ^ q * y ^ q) c -
      profilePosterior p q (fun y ↦ y ^ q) c ^ 2)) atTop (𝓝 (1 / q)) := by
  have h2 := tendsto_sq_mul_profileSecond hp hq
  have h1 := (tendsto_mul_profileMean hp hq).pow 2
  have key := h2.sub h1
  have e : 1 / q * (1 / q + 1) - (1 / q) ^ 2 = 1 / q := by ring
  rw [e] at key
  refine key.congr' (Filter.Eventually.of_forall fun c ↦ ?_)
  ring

end Laplace.Multi
