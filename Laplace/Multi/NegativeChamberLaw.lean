/-
Copyright (c) 2026 Timaeus Research. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniel Murfet
-/
import Mathlib
import Laplace.Multi.NegativeChamber
import Laplace.Multi.WallRecedes

/-!
# The `√t` chamber law from the exact wall profile

The negative chamber `a ∈ [−A, 0]` of the two-monomial wall, read through the window isometry
`wall_window_length`, has thermodynamic length `∫₀^{A t^σ} √Var_{-b}(y^q) db`, `σ = 1 − q/p`.
Profile matching (`NegativeChamber`) gives `√Var_{-b}(y^q) ~ L_{p,q} b^γ` with
`γ = (2q−p)/(2(p−q))`, and a power-law Cesàro lemma turns this into

  `ℓ_t(−A, 0) / √t → K₋(A) = L_{p,q} A^β / β`,   `β = γ + 1 = p/(2(p−q))`
  (`negative_chamber_law`),

since `σ β = 1/2`. Together with `wall_recedes` (`ℓ_t(0, a₁) ~ σ√(1/q) log t`) this is the
two-sided law of the wall: logarithmic on the side where the wall exponent is `1/q`, `√t` on the
side where the posterior sits at an interior minimiser of the profile.
-/

open MeasureTheory Filter Topology Set

namespace Laplace.Multi

/-! ### A power-law Cesàro lemma -/

/-- **Power-law Cesàro**: if `g(u) u^{-γ} → L` with `γ > −1`, then `(∫₀ᵗ g) / t^{γ+1} → L/(γ+1)`. -/
theorem tendsto_intervalIntegral_div_rpow {g : ℝ → ℝ} {L γ : ℝ} (hγ : -1 < γ)
    (hg : ∀ a b : ℝ, 0 ≤ a → 0 ≤ b → IntervalIntegrable g volume a b)
    (hlim : Tendsto (fun u ↦ g u * u ^ (-γ)) atTop (𝓝 L)) :
    Tendsto (fun t ↦ (∫ u in (0 : ℝ)..t, g u) / t ^ (γ + 1)) atTop (𝓝 (L / (γ + 1))) := by
  have hβ : 0 < γ + 1 := by linarith
  rw [Metric.tendsto_atTop]
  intro ε hε
  have hε4 : 0 < ε / 4 := by positivity
  set δ : ℝ := ε * (γ + 1) / 4 with hδ
  have hδpos : 0 < δ := by positivity
  obtain ⟨U₁, hU₁⟩ := Metric.tendsto_atTop.1 hlim δ hδpos
  set U₀ : ℝ := max U₁ 1 with hU₀
  have hU₀1 : 1 ≤ U₀ := le_max_right _ _
  have hU₀pos : 0 < U₀ := by linarith
  have hbnd : ∀ u, U₀ ≤ u → |g u * u ^ (-γ) - L| ≤ δ := fun u hu ↦ by
    have := hU₁ u (le_trans (le_max_left _ _) hu)
    rw [Real.dist_eq] at this
    exact this.le
  set K : ℝ := ∫ u in (0 : ℝ)..U₀, g u with hK
  set U : ℝ := U₀ ^ (γ + 1) with hU
  have hU0 : 0 ≤ U := Real.rpow_nonneg hU₀pos.le _
  set A : ℝ := |K| + |L| / (γ + 1) * U with hA
  have hA0 : 0 ≤ A :=
    add_nonneg (abs_nonneg _) (mul_nonneg (div_nonneg (abs_nonneg _) hβ.le) hU0)
  refine ⟨max U₀ ((A * 4 / ε + 1) ^ (1 / (γ + 1))), fun t ht ↦ ?_⟩
  have htU : U₀ ≤ t := le_trans (le_max_left _ _) ht
  have htpos : 0 < t := lt_of_lt_of_le hU₀pos htU
  have hA4 : 0 ≤ A * 4 / ε := by positivity
  have hpowT : A * 4 / ε + 1 ≤ t ^ (γ + 1) := by
    have h2 := Real.rpow_le_rpow (Real.rpow_nonneg (by linarith) _)
      (le_trans (le_max_right _ _) ht) hβ.le
    rwa [← Real.rpow_mul (by linarith), one_div_mul_cancel hβ.ne', Real.rpow_one] at h2
  have hTpos : 0 < t ^ (γ + 1) := Real.rpow_pos_of_pos htpos _
  have hsplit : ∫ u in (0 : ℝ)..t, g u = K + ∫ u in U₀..t, g u :=
    (intervalIntegral.integral_add_adjacent_intervals (hg 0 U₀ le_rfl hU₀pos.le)
      (hg U₀ t hU₀pos.le htpos.le)).symm
  have hpow_int : IntervalIntegrable (fun u : ℝ ↦ u ^ γ) volume U₀ t :=
    intervalIntegral.intervalIntegrable_rpow' hγ
  have hint_pow : ∫ u in U₀..t, u ^ γ = (t ^ (γ + 1) - U₀ ^ (γ + 1)) / (γ + 1) :=
    integral_rpow (Or.inl hγ)
  have hsub : ∫ u in U₀..t, g u =
      (∫ u in U₀..t, (g u - L * u ^ γ)) + L * ((t ^ (γ + 1) - U₀ ^ (γ + 1)) / (γ + 1)) := by
    rw [← hint_pow, ← intervalIntegral.integral_const_mul,
      ← intervalIntegral.integral_add ((hg U₀ t hU₀pos.le htpos.le).sub (hpow_int.const_mul L))
        (hpow_int.const_mul L)]
    exact intervalIntegral.integral_congr fun u _ ↦ by simp only [sub_add_cancel]
  have hR : |∫ u in U₀..t, (g u - L * u ^ γ)| ≤ δ * ((t ^ (γ + 1) - U₀ ^ (γ + 1)) / (γ + 1)) := by
    have := intervalIntegral.norm_integral_le_of_norm_le (f := fun u ↦ g u - L * u ^ γ)
      (g := fun u ↦ δ * u ^ γ) htU ?_ (hpow_int.const_mul _)
    · rw [intervalIntegral.integral_const_mul, hint_pow] at this
      simpa only [Real.norm_eq_abs] using this
    · refine Filter.Eventually.of_forall fun u hu ↦ ?_
      have hu0 : 0 < u := lt_of_lt_of_le hU₀pos hu.1.le
      rw [Real.norm_eq_abs]
      have e : g u - L * u ^ γ = (g u * u ^ (-γ) - L) * u ^ γ := by
        rw [sub_mul, mul_assoc, ← Real.rpow_add hu0, neg_add_cancel, Real.rpow_zero, mul_one]
      rw [e, abs_mul, abs_of_pos (Real.rpow_pos_of_pos hu0 _)]
      exact mul_le_mul_of_nonneg_right (hbnd u hu.1.le) (Real.rpow_pos_of_pos hu0 _).le
  rw [Real.dist_eq, hsplit, hsub]
  set R := ∫ u in U₀..t, (g u - L * u ^ γ) with hR'
  set T := t ^ (γ + 1) with hT
  have e : (K + (R + L * ((T - U) / (γ + 1)))) / T - L / (γ + 1) =
      (K + R - L * U / (γ + 1)) / T := by
    field_simp
    ring
  rw [e, abs_div, abs_of_pos hTpos, div_lt_iff₀ hTpos]
  have h1 : |K + R - L * U / (γ + 1)| ≤ |K| + |R| + |L| / (γ + 1) * U := by
    calc |K + R - L * U / (γ + 1)| ≤ |K + R| + |L * U / (γ + 1)| := abs_sub _ _
      _ ≤ |K| + |R| + |L| / (γ + 1) * U := by
          rw [abs_div, abs_mul, abs_of_pos hβ, abs_of_nonneg hU0, mul_div_right_comm]
          linarith [abs_add_le K R]
  have hR2 : |R| ≤ ε / 4 * T := by
    refine le_trans hR ?_
    have : δ * ((T - U₀ ^ (γ + 1)) / (γ + 1)) = ε / 4 * (T - U₀ ^ (γ + 1)) := by
      rw [hδ]
      field_simp
    rw [this]
    exact mul_le_mul_of_nonneg_left (by linarith [Real.rpow_nonneg hU₀pos.le (γ + 1)]) hε4.le
  have h2 : A ≤ ε / 4 * (T - 1) := by
    have h3 : A * 4 / ε ≤ T - 1 := by rw [hT]; linarith
    rw [div_le_iff₀ hε] at h3
    linarith
  calc |K + R - L * U / (γ + 1)| ≤ |K| + |R| + |L| / (γ + 1) * U := h1
    _ = A + |R| := by rw [hA]; ring
    _ ≤ ε / 4 * (T - 1) + ε / 4 * T := add_le_add h2 hR2
    _ < ε * T := by linarith

/-! ### Continuity of the profile for negative couplings -/

/-- `b y^q ≤ ½ y^p + b (2b)^{q/(p−q)}` for `0 < q < p`, `b > 0`, `y > 0`. -/
theorem mul_rpow_le_half_rpow_add {p q : ℝ} (hq : 0 < q) (hqp : q < p) {b : ℝ} (hb : 0 < b)
    {y : ℝ} (hy : 0 < y) :
    b * y ^ q ≤ 1 / 2 * y ^ p + b * (2 * b) ^ (q / (p - q)) := by
  have hr : 0 < p - q := by linarith
  set Y₀ := (2 * b) ^ (1 / (p - q)) with hY₀
  have hY₀pos : 0 < Y₀ := Real.rpow_pos_of_pos (by positivity) _
  have hY₀q : Y₀ ^ q = (2 * b) ^ (q / (p - q)) := by
    rw [hY₀, ← Real.rpow_mul (by positivity)]; congr 1; ring
  have hY₀r : Y₀ ^ (p - q) = 2 * b := by
    rw [hY₀, ← Real.rpow_mul (by positivity), one_div_mul_cancel hr.ne', Real.rpow_one]
  rcases le_or_gt y Y₀ with h | h
  · have h1 : y ^ q ≤ Y₀ ^ q := Real.rpow_le_rpow hy.le h hq.le
    have h0 : 0 ≤ 1 / 2 * y ^ p := by positivity
    rw [hY₀q] at h1
    nlinarith [mul_le_mul_of_nonneg_left h1 hb.le]
  · have h1 : 2 * b < y ^ (p - q) := by rw [← hY₀r]; exact Real.rpow_lt_rpow hY₀pos.le h hr
    have e : y ^ p = y ^ q * y ^ (p - q) := by rw [← Real.rpow_add hy]; congr 1; ring
    have hyq : 0 < y ^ q := Real.rpow_pos_of_pos hy _
    have h2 : 0 ≤ b * (2 * b) ^ (q / (p - q)) := by positivity
    rw [e]
    nlinarith [mul_lt_mul_of_pos_left h1 hyq]

/-- The uniform majorant of the profile integrand on `c ≥ −b₁`. -/
theorem abs_profile_integrand_le {p q : ℝ} (hq : 0 < q) (hqp : q < p) {ψ : ℝ → ℝ} {Mψ r : ℝ}
    (hψ : ∀ y, 0 < y → |ψ y| ≤ Mψ * y ^ r) {b₁ : ℝ} (hb₁ : 0 < b₁) {c : ℝ} (hc : -b₁ ≤ c)
    {y : ℝ} (hy : 0 < y) :
    |ψ y * Real.exp (-(y ^ p + c * y ^ q))| ≤
      Mψ * Real.exp (b₁ * (2 * b₁) ^ (q / (p - q))) * (y ^ r * Real.exp (-(1 / 2) * y ^ p)) := by
  rw [abs_mul, Real.abs_exp]
  have hbnd : Real.exp (-(y ^ p + c * y ^ q)) ≤
      Real.exp (b₁ * (2 * b₁) ^ (q / (p - q))) * Real.exp (-(1 / 2) * y ^ p) := by
    rw [← Real.exp_add, Real.exp_le_exp]
    have h1 := mul_rpow_le_half_rpow_add hq hqp hb₁ hy
    have h2 : -c * y ^ q ≤ b₁ * y ^ q :=
      mul_le_mul_of_nonneg_right (by linarith) (Real.rpow_nonneg hy.le q)
    linarith
  calc |ψ y| * Real.exp (-(y ^ p + c * y ^ q))
      ≤ (Mψ * y ^ r) * (Real.exp (b₁ * (2 * b₁) ^ (q / (p - q))) * Real.exp (-(1 / 2) * y ^ p)) :=
        mul_le_mul (hψ y hy) hbnd (Real.exp_pos _).le (le_trans (abs_nonneg _) (hψ y hy))
    _ = _ := by ring

/-- The profile integrand is integrable for every coupling `c ∈ ℝ` (observables of polynomial
growth). -/
theorem integrableOn_profile' {p q : ℝ} (hq : 0 < q) (hqp : q < p) (c : ℝ) {ψ : ℝ → ℝ}
    (hψm : Measurable ψ) {Mψ r : ℝ} (hr : 0 ≤ r) (hψ : ∀ y, 0 < y → |ψ y| ≤ Mψ * y ^ r) :
    IntegrableOn (fun y ↦ ψ y * Real.exp (-(y ^ p + c * y ^ q))) (Ioi 0) := by
  have hp : 0 < p := by linarith
  have hb₁ : 0 < |c| + 1 := by positivity
  refine ((integrableOn_rpow_mul_exp_neg_mul_rpow (s := r) (b := 1 / 2) (by linarith) hp
    (by norm_num)).const_mul
    (Mψ * Real.exp ((|c| + 1) * (2 * (|c| + 1)) ^ (q / (p - q))))).mono' ?_ ?_
  · exact (hψm.mul (Real.measurable_exp.comp ((measurable_id.pow_const p).add
      ((measurable_id.pow_const q).const_mul c)).neg)).aestronglyMeasurable
  · refine (ae_restrict_iff' measurableSet_Ioi).mpr (Filter.Eventually.of_forall fun y hy ↦ ?_)
    have hy0 : (0 : ℝ) < y := hy
    rw [Real.norm_eq_abs]
    exact abs_profile_integrand_le hq hqp hψ hb₁ (by linarith [neg_abs_le c]) hy0

/-- The profile numerator is continuous in the coupling on all of `ℝ`. -/
theorem continuous_profileNum {p q : ℝ} (hq : 0 < q) (hqp : q < p) {ψ : ℝ → ℝ}
    (hψm : Measurable ψ) {Mψ r : ℝ} (hr : 0 ≤ r) (hψ : ∀ y, 0 < y → |ψ y| ≤ Mψ * y ^ r) :
    Continuous (fun c ↦ profileNum p q ψ c) := by
  have hp : 0 < p := by linarith
  refine continuous_iff_continuousAt.mpr fun c₀ ↦ ?_
  have hb₁ : 0 < |c₀| + 1 := by positivity
  have hcont : ContinuousOn (fun c ↦ profileNum p q ψ c) (Ici (-(|c₀| + 1))) := by
    unfold profileNum
    refine continuousOn_of_dominated (bound := fun y ↦
      Mψ * Real.exp ((|c₀| + 1) * (2 * (|c₀| + 1)) ^ (q / (p - q))) *
        (y ^ r * Real.exp (-(1 / 2) * y ^ p))) ?_ ?_ ?_ ?_
    · intro c _
      exact (hψm.mul (Real.measurable_exp.comp ((measurable_id.pow_const p).add
        ((measurable_id.pow_const q).const_mul c)).neg)).aestronglyMeasurable
    · intro c hc
      refine (ae_restrict_iff' measurableSet_Ioi).mpr
        (Filter.Eventually.of_forall fun y hy ↦ ?_)
      have hy0 : (0 : ℝ) < y := hy
      rw [Real.norm_eq_abs]
      exact abs_profile_integrand_le hq hqp hψ hb₁ (mem_Ici.mp hc) hy0
    · exact (integrableOn_rpow_mul_exp_neg_mul_rpow (by linarith) hp (by norm_num)).const_mul _
    · exact Filter.Eventually.of_forall fun y ↦ Continuous.continuousOn (by fun_prop)
  exact hcont.continuousAt (Ici_mem_nhds (by linarith [neg_abs_le c₀]))

/-- The profile partition function is positive for every coupling. -/
theorem profileNum_one_pos' {p q : ℝ} (hq : 0 < q) (hqp : q < p) (c : ℝ) :
    0 < profileNum p q (fun _ ↦ 1) c := by
  have hint : IntegrableOn (fun y ↦ (1 : ℝ) * Real.exp (-(y ^ p + c * y ^ q))) (Ioi 0) :=
    integrableOn_profile' hq hqp c measurable_const (Mψ := 1) (r := 0) le_rfl (fun y _ ↦ by simp)
  unfold profileNum
  rw [setIntegral_pos_iff_support_of_nonneg_ae
    (Filter.Eventually.of_forall fun y ↦ by simp [(Real.exp_pos _).le]) hint]
  have hsupp : Function.support (fun y : ℝ ↦ (1 : ℝ) * Real.exp (-(y ^ p + c * y ^ q))) = univ :=
    Set.eq_univ_of_forall fun y ↦ Function.mem_support.mpr (by simp [(Real.exp_pos _).ne'])
  rw [hsupp, univ_inter, Real.volume_Ioi]
  simp

/-- The profile variance of `y^q` is continuous in the coupling on all of `ℝ`. -/
theorem continuous_profileVar {p q : ℝ} (hq : 0 < q) (hqp : q < p) :
    Continuous (fun c ↦ profilePosterior p q (fun y ↦ y ^ q * y ^ q) c -
      profilePosterior p q (fun y ↦ y ^ q) c ^ 2) := by
  have h0 := continuous_profileNum hq hqp (ψ := fun _ ↦ (1 : ℝ)) measurable_const (Mψ := 1)
    (r := 0) le_rfl (fun y _ ↦ by simp)
  have h1 := continuous_profileNum hq hqp (ψ := fun y ↦ y ^ q) (measurable_id.pow_const q)
    (Mψ := 1) (r := q) hq.le (abs_rpow_le_self_rpow q)
  have h2 := continuous_profileNum hq hqp (ψ := fun y ↦ y ^ q * y ^ q)
    ((measurable_id.pow_const q).mul (measurable_id.pow_const q)) (Mψ := 1) (r := q + q)
    (by linarith) fun y hy ↦ by
      rw [abs_of_pos (mul_pos (Real.rpow_pos_of_pos hy q) (Real.rpow_pos_of_pos hy q)),
        Real.rpow_add hy, one_mul]
  have hne : ∀ c, profileNum p q (fun _ ↦ 1) c ≠ 0 := fun c ↦ (profileNum_one_pos' hq hqp c).ne'
  unfold profilePosterior
  exact (h2.div h0 hne).sub ((h1.div h0 hne).pow 2)

/-! ### The chamber law -/

/-- The chamber exponent `β = p/(2(p−q))`. -/
noncomputable def negBeta (p q : ℝ) : ℝ := p / (2 * (p - q))

/-- The profile speed exponent `γ = β − 1 = (2q−p)/(2(p−q))`. -/
noncomputable def negGamma (p q : ℝ) : ℝ := (2 * q - p) / (2 * (p - q))

/-- The profile speed coefficient `L_{p,q} = (q/√(p(p−q))) (q/p)^γ`, so that
`√Var_{-b}(y^q) ~ L_{p,q} b^γ`. -/
noncomputable def negSpeedCoeff (p q : ℝ) : ℝ :=
  q / Real.sqrt (p * (p - q)) * (q / p) ^ negGamma p q

/-- The chamber constant `K₋(A) = L_{p,q} A^β / β`. -/
noncomputable def negChamberConst (p q A : ℝ) : ℝ :=
  negSpeedCoeff p q * A ^ negBeta p q / negBeta p q

section Law

variable {p q : ℝ} (hq : 0 < q) (hqp : q < p)
include hq hqp

theorem negBeta_pos : 0 < negBeta p q := by
  unfold negBeta
  have : 0 < p := by linarith
  positivity

omit hq in
theorem negGamma_add_one : negGamma p q + 1 = negBeta p q := by
  unfold negGamma negBeta
  have hr : (2 : ℝ) * (p - q) ≠ 0 := by
    have : 0 < p - q := by linarith
    positivity
  rw [div_add_one hr]
  congr 1
  ring

theorem neg_one_lt_negGamma : -1 < negGamma p q := by
  have := negBeta_pos hq hqp
  linarith [negGamma_add_one hqp]

/-- `σ β = ½` with `σ = 1 − q/p`. -/
theorem sigma_mul_negBeta : (1 - q / p) * negBeta p q = 1 / 2 := by
  unfold negBeta
  have hp : p ≠ 0 := by linarith
  have hr : p - q ≠ 0 := by linarith
  have hr' : -q + p ≠ 0 := by intro h; apply hr; linarith
  field_simp

/-- **Profile speed asymptotics**: `√Var_{-b}(y^q) · b^{-γ} → L_{p,q}`. -/
theorem tendsto_sqrt_negVar_mul_rpow :
    Tendsto (fun b ↦ Real.sqrt (negVar p q b) * b ^ (-negGamma p q)) atTop
      (𝓝 (negSpeedCoeff p q)) := by
  have hp : 0 < p := by linarith
  have hκ : 0 < p * (p - q) := mul_pos hp (by linarith)
  have hqp0 : 0 < q / p := by positivity
  set γ := negGamma p q with hγ
  have hexp : (p - 2 * q) / (p - q) = -(2 * γ) := by
    rw [hγ]; unfold negGamma
    have hr : p - q ≠ 0 := by linarith
    field_simp
    ring
  -- `negVar b · b^{-2γ} → (q²/(p(p−q))) (q/p)^{2γ}`
  have h1 : Tendsto (fun b ↦ negVar p q b * b ^ (-(2 * γ))) atTop
      (𝓝 (q ^ 2 / (p * (p - q)) * (q / p) ^ (2 * γ))) := by
    have h := (tendsto_negVar_mul_rpow' hq hqp).div_const ((q / p) ^ (-(2 * γ)))
    have hne : (q / p) ^ (-(2 * γ)) ≠ 0 := (Real.rpow_pos_of_pos hqp0 _).ne'
    have e : q ^ 2 / (p * (p - q)) / (q / p) ^ (-(2 * γ)) =
        q ^ 2 / (p * (p - q)) * (q / p) ^ (2 * γ) := by
      rw [Real.rpow_neg hqp0.le, div_inv_eq_mul]
    rw [e] at h
    refine h.congr' ?_
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with b hb
    rw [hexp, show q * b / p = q / p * b by ring, Real.mul_rpow hqp0.le hb.le]
    field_simp
  have h2 := (Real.continuous_sqrt.tendsto _).comp h1
  have e2 : Real.sqrt (q ^ 2 / (p * (p - q)) * (q / p) ^ (2 * γ)) = negSpeedCoeff p q := by
    unfold negSpeedCoeff
    rw [Real.sqrt_mul (by positivity), Real.sqrt_div' _ hκ.le, Real.sqrt_sq hq.le,
      show (2 : ℝ) * γ = γ * 2 by ring, Real.rpow_mul hqp0.le, Real.rpow_two,
      Real.sqrt_sq (Real.rpow_nonneg hqp0.le _)]
  rw [e2] at h2
  refine h2.congr' ?_
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with b hb
  simp only [Function.comp_apply]
  rw [show -(2 * γ) = -γ * 2 by ring, Real.rpow_mul hb.le, Real.rpow_two,
    Real.sqrt_mul' _ (sq_nonneg _), Real.sqrt_sq (Real.rpow_nonneg hb.le _)]

/-- **The `√t` chamber law**: the thermodynamic length of the negative chamber `a ∈ [−A, 0]` of
the two-monomial wall satisfies `ℓ_t(−A, 0)/√t → K₋(A) = L_{p,q} A^β/β`, `β = p/(2(p−q))`. -/
theorem negative_chamber_law {A : ℝ} (hA : 0 < A) :
    Tendsto (fun t ↦ (∫ a in (-A)..0, Real.sqrt (fisherSpeed
      (volume.restrict (Ioi 0)) (fun _ ↦ 1) (twoMonoPath p q) (twoMonoVel q) t a)) /
        Real.sqrt t) atTop (𝓝 (negChamberConst p q A)) := by
  have hp : 0 < p := by linarith
  set σ : ℝ := 1 - q / p with hσ
  have hσpos : 0 < σ := by
    rw [hσ, sub_pos, div_lt_one hp]; exact hqp
  set β := negBeta p q with hβ
  have hβpos : 0 < β := negBeta_pos hq hqp
  set V : ℝ → ℝ := fun c ↦ profilePosterior p q (fun y ↦ y ^ q * y ^ q) c -
    profilePosterior p q (fun y ↦ y ^ q) c ^ 2 with hV
  have hVcont : Continuous V := continuous_profileVar hq hqp
  -- the speed on the negative side is `√negVar`
  have hg : ∀ a b : ℝ, 0 ≤ a → 0 ≤ b →
      IntervalIntegrable (fun b ↦ Real.sqrt (negVar p q b)) volume a b := fun a b _ _ ↦ by
    have : Continuous fun b ↦ Real.sqrt (negVar p q b) := by
      have : (fun b ↦ Real.sqrt (negVar p q b)) = fun b ↦ Real.sqrt (V (-b)) := by
        funext b; rfl
      rw [this]
      exact Real.continuous_sqrt.comp (hVcont.comp continuous_neg)
    exact this.intervalIntegrable a b
  -- Cesàro
  have hces := tendsto_intervalIntegral_div_rpow (neg_one_lt_negGamma hq hqp) hg
    (tendsto_sqrt_negVar_mul_rpow hq hqp)
  rw [negGamma_add_one hqp, ← hβ] at hces
  have hX : Tendsto (fun t : ℝ ↦ A * t ^ σ) atTop atTop :=
    (tendsto_rpow_atTop hσpos).const_mul_atTop hA
  have hcomp := (hces.comp hX).const_mul (A ^ β)
  have hc : negChamberConst p q A = A ^ β * (negSpeedCoeff p q / β) := by
    unfold negChamberConst
    rw [← hβ]
    ring
  rw [hc]
  refine hcomp.congr' ?_
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with t ht
  simp only [Function.comp_apply]
  -- the window isometry and the reflection
  have hw := wall_window_length (q := q) hp ht (-A * t ^ σ) 0
  have e1 : -A * t ^ σ * t ^ (-σ) = -A := by
    rw [mul_assoc, ← Real.rpow_add ht, add_neg_cancel, Real.rpow_zero, mul_one]
  rw [e1, zero_mul] at hw
  have e2 : (∫ c in (-A * t ^ σ)..0, Real.sqrt (V c)) =
      ∫ b in (0 : ℝ)..(A * t ^ σ), Real.sqrt (negVar p q b) := by
    have := intervalIntegral.integral_comp_neg (f := fun c ↦ Real.sqrt (V c)) (a := 0)
      (b := A * t ^ σ)
    rw [neg_zero, ← neg_mul] at this
    rw [← this]
    rfl
  have e3 : (A * t ^ σ) ^ β = A ^ β * Real.sqrt t := by
    rw [Real.mul_rpow hA.le (Real.rpow_pos_of_pos ht _).le, ← Real.rpow_mul ht.le,
      show σ * β = 1 / 2 from sigma_mul_negBeta hq hqp, Real.sqrt_eq_rpow]
  have hAβ : A ^ β ≠ 0 := (Real.rpow_pos_of_pos hA _).ne'
  have hst : Real.sqrt t ≠ 0 := (Real.sqrt_pos.mpr ht).ne'
  rw [hw, e2, e3]
  field_simp

end Law

end Laplace.Multi
