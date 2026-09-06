/-
Copyright (c) 2026 Timaeus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Laplace.Grammar.LogTwoDProduct

/-!
# No `log n` when the candidate exponents differ: the `d = 2`, `h = (0,1)` chart (grammar §4.2)

Companion to the first-`log n` theorem. For `k = (1,1)`, `h = (0,1)` the two candidate exponents are
`μ₁ = 1/2 < μ₂ = 1`, so the paper predicts leading exponent `min = 1/2` with multiplicity `1` — no
logarithm. We prove the **exact chart formula**

  `Z(n) = ∫₀^b ∫₀^b v e^{-βn(uv)² + β√n uv a} dv du = b n^{-1/2} F₀(L) - n^{-1} F₁(L)/b`,
  `L = √n b²`,

with `F₀ = ∫₀^x f`, `F₁ = ∫₀^x s f(s) ds`, and deduce `Z(n) ~ (b S_{1/2}(a)/2) n^{-1/2}` with error
`O(n^{-1})`. The mechanism is the identity `∫₀^L x^{-2} F₁(x) dx = F₀(L) - F₁(L)/L` (the noncritical
case of the general power-primitive identity), proved by showing the difference has zero derivative
on `(0, ∞)` and vanishes at `0⁺`. Zero `sorry`/`axiom`.
-/

open Real MeasureTheory Set Asymptotics Filter

namespace Laplace.Grammar

/-- The first-moment primitive `F₁(x) = ∫₀^x s f(s) ds`. -/
noncomputable def quadMomentPrimitive (β a x : ℝ) : ℝ := ∫ s in (0 : ℝ)..x, s * quadKernel β a s

/-- The noncritical power primitive `K(L) = ∫₀^L x⁻² F₁(x) dx`. -/
noncomputable def quadPowerPrimitive (β a L : ℝ) : ℝ :=
  ∫ x in (0 : ℝ)..L, (x ^ 2)⁻¹ * quadMomentPrimitive β a x

/-- The `d = 2`, `k = (1,1)`, `h = (0,1)` chart standard integral, as an iterated integral. -/
noncomputable def twoDIntegralH01 (β a b n : ℝ) : ℝ :=
  ∫ u in Ioc (0 : ℝ) b, ∫ v in Ioc (0 : ℝ) b,
    v * Real.exp (-β * n * (u * v) ^ 2 + β * Real.sqrt n * (u * v) * a)

theorem quadMomentKernel_continuous (β a : ℝ) : Continuous (fun s => s * quadKernel β a s) :=
  continuous_id.mul (quadKernel_continuous β a)

theorem quadMomentPrimitive_continuous (β a : ℝ) : Continuous (quadMomentPrimitive β a) :=
  intervalIntegral.continuous_primitive
    (fun c d => (quadMomentKernel_continuous β a).intervalIntegrable c d) 0

theorem quadMomentPrimitive_nonneg (β a x : ℝ) (hx : 0 ≤ x) : 0 ≤ quadMomentPrimitive β a x :=
  intervalIntegral.integral_nonneg hx fun s hs => mul_nonneg hs.1 (quadKernel_pos β a s).le

/-- `F₁(x) ≤ E x²/2`. -/
theorem quadMomentPrimitive_le (β a x : ℝ) (hβ : 0 < β) (hx : 0 ≤ x) :
    quadMomentPrimitive β a x ≤ Real.exp (β * a ^ 2 / 2) * x ^ 2 / 2 := by
  unfold quadMomentPrimitive
  calc (∫ s in (0 : ℝ)..x, s * quadKernel β a s)
      ≤ ∫ s in (0 : ℝ)..x, Real.exp (β * a ^ 2 / 2) * s :=
        intervalIntegral.integral_mono_on hx
          ((quadMomentKernel_continuous β a).intervalIntegrable _ _)
          ((continuous_const.mul continuous_id).intervalIntegrable _ _) fun s hs => by
            have := quadKernel_le_const β a s hβ
            nlinarith [hs.1, (quadKernel_pos β a s).le]
    _ = Real.exp (β * a ^ 2 / 2) * x ^ 2 / 2 := by
        rw [intervalIntegral.integral_const_mul, integral_id]; ring

/-- `F₁(x) ≤ M`. -/
theorem quadMomentPrimitive_le_moment (β a x : ℝ) (hβ : 0 < β) (hx : 0 ≤ x) :
    quadMomentPrimitive β a x ≤ quadMoment β a := by
  rw [quadMomentPrimitive, intervalIntegral.integral_of_le hx]
  apply setIntegral_mono_set (quadMoment_integrand_integrableOn β a hβ)
  · rw [Filter.EventuallyLE, ae_restrict_iff' measurableSet_Ioi]
    exact Filter.Eventually.of_forall fun s hs => mul_nonneg (le_of_lt hs) (quadKernel_pos β a s).le
  · exact Ioc_subset_Ioi_self.eventuallyLE

theorem hasDerivAt_quadPrimitive (β a L : ℝ) :
    HasDerivAt (quadPrimitive β a) (quadKernel β a L) L :=
  ((quadKernel_continuous β a).integral_hasStrictDerivAt 0 L).hasDerivAt

theorem hasDerivAt_quadMomentPrimitive (β a L : ℝ) :
    HasDerivAt (quadMomentPrimitive β a) (L * quadKernel β a L) L :=
  ((quadMomentKernel_continuous β a).integral_hasStrictDerivAt 0 L).hasDerivAt

/-- The integrand of `K` is bounded by `E/2` on `(0, ∞)`. -/
theorem quadPowerPrimitive_integrand_le (β a x : ℝ) (hβ : 0 < β) (hx : 0 < x) :
    (x ^ 2)⁻¹ * quadMomentPrimitive β a x ≤ Real.exp (β * a ^ 2 / 2) / 2 := by
  rw [inv_mul_le_iff₀ (by positivity)]
  have := quadMomentPrimitive_le β a x hβ hx.le
  linarith

theorem quadPowerPrimitive_integrand_intervalIntegrable (β a L : ℝ) (hβ : 0 < β) (hL : 0 ≤ L) :
    IntervalIntegrable (fun x => (x ^ 2)⁻¹ * quadMomentPrimitive β a x) volume 0 L := by
  refine (intervalIntegrable_const (c := Real.exp (β * a ^ 2 / 2) / 2)).mono_fun
    (((measurable_id.pow_const 2).inv.mul
      (quadMomentPrimitive_continuous β a).measurable).aestronglyMeasurable) ?_
  refine (ae_restrict_iff' measurableSet_uIoc).2 (Filter.Eventually.of_forall fun x hx => ?_)
  rw [Set.uIoc_of_le hL] at hx
  have hx0 : (0 : ℝ) < x := hx.1
  beta_reduce
  rw [Real.norm_eq_abs, Real.norm_eq_abs,
    abs_of_nonneg (mul_nonneg (by positivity) (quadMomentPrimitive_nonneg β a x hx0.le)),
    abs_of_pos (by positivity : (0 : ℝ) < Real.exp (β * a ^ 2 / 2) / 2)]
  exact quadPowerPrimitive_integrand_le β a x hβ hx0

theorem hasDerivAt_quadPowerPrimitive (β a L : ℝ) (hβ : 0 < β) (hL : 0 < L) :
    HasDerivAt (quadPowerPrimitive β a) ((L ^ 2)⁻¹ * quadMomentPrimitive β a L) L := by
  have hcont : ∀ x ∈ Ioi (0 : ℝ),
      ContinuousAt (fun x => (x ^ 2)⁻¹ * quadMomentPrimitive β a x) x := by
    intro x hx
    have hx0 : (0 : ℝ) < x := hx
    exact ((continuousAt_id.pow 2).inv₀ (pow_ne_zero 2 hx0.ne')).mul
      (quadMomentPrimitive_continuous β a).continuousAt
  exact intervalIntegral.integral_hasDerivAt_right
    (quadPowerPrimitive_integrand_intervalIntegrable β a L hβ hL.le)
    (ContinuousAt.stronglyMeasurableAtFilter isOpen_Ioi hcont L hL) (hcont L hL)

/-- `|K(t)| ≤ (E/2) t` for `t ≥ 0`. -/
theorem abs_quadPowerPrimitive_le (β a t : ℝ) (hβ : 0 < β) (ht : 0 ≤ t) :
    |quadPowerPrimitive β a t| ≤ Real.exp (β * a ^ 2 / 2) / 2 * t := by
  have := intervalIntegral.norm_integral_le_of_norm_le_const (a := (0 : ℝ)) (b := t)
    (C := Real.exp (β * a ^ 2 / 2) / 2)
    (f := fun x => (x ^ 2)⁻¹ * quadMomentPrimitive β a x) fun x hx => by
      rw [Set.uIoc_of_le ht] at hx
      have hx0 : (0 : ℝ) < x := hx.1
      rw [Real.norm_eq_abs,
        abs_of_nonneg (mul_nonneg (by positivity) (quadMomentPrimitive_nonneg β a x hx0.le))]
      exact quadPowerPrimitive_integrand_le β a x hβ hx0
  rw [Real.norm_eq_abs, sub_zero, abs_of_nonneg ht] at this
  exact this

/-- **The noncritical identity** `∫₀^L x⁻² F₁(x) dx = F₀(L) - F₁(L)/L` for `L > 0`. -/
theorem quadPowerPrimitive_eq (β a L : ℝ) (hβ : 0 < β) (hL : 0 < L) :
    quadPowerPrimitive β a L = quadPrimitive β a L - quadMomentPrimitive β a L / L := by
  set E := Real.exp (β * a ^ 2 / 2) with hE
  have hE0 : 0 < E := Real.exp_pos _
  obtain ⟨G, hG⟩ : ∃ G : ℝ → ℝ,
      G = (quadPowerPrimitive β a - quadPrimitive β a) + quadMomentPrimitive β a / id := ⟨_, rfl⟩
  have hGapp : ∀ t, G t = quadPowerPrimitive β a t - quadPrimitive β a t
      + quadMomentPrimitive β a t / t := fun t => by rw [hG]; rfl
  -- zero derivative on `(0, ∞)`
  have hderiv : ∀ t, 0 < t → HasDerivAt G 0 t := by
    intro t ht
    have h1 := hasDerivAt_quadPowerPrimitive β a t hβ ht
    have h2 := hasDerivAt_quadPrimitive β a t
    have h3 := (hasDerivAt_quadMomentPrimitive β a t).div (hasDerivAt_id t) ht.ne'
    have h := (h1.sub h2).add h3
    rw [hG]
    refine h.congr_deriv ?_
    simp only [id]
    field_simp
    ring
  -- hence constant on `(0, ∞)`
  have hconst : ∀ t, 0 < t → G t = G 1 := by
    intro t ht
    have hmin : 0 < min 1 t := lt_min one_pos ht
    have hon : ∀ x ∈ Set.uIcc 1 t, HasDerivAt G ((fun _ : ℝ => (0 : ℝ)) x) x := fun x hx =>
      hderiv x (lt_of_lt_of_le hmin hx.1)
    have := intervalIntegral.integral_eq_sub_of_hasDerivAt hon intervalIntegrable_const
    simp only [intervalIntegral.integral_const, smul_zero] at this
    linarith
  -- `G(1) = 0` since `|G(t)| ≤ 2E t` on `(0, 1]`
  have hbound : ∀ t, 0 < t → t ≤ 1 → |G t| ≤ 2 * E * t := by
    intro t ht _
    rw [hGapp]
    have hK := abs_quadPowerPrimitive_le β a t hβ ht.le
    have hF0 : |quadPrimitive β a t| ≤ E * t := by
      rw [abs_of_nonneg (quadPrimitive_nonneg β a t ht.le)]; exact quadPrimitive_le β a t hβ ht.le
    have hF1 : |quadMomentPrimitive β a t / t| ≤ E * t / 2 := by
      rw [abs_of_nonneg (div_nonneg (quadMomentPrimitive_nonneg β a t ht.le) ht.le),
        div_le_iff₀ ht]
      have := quadMomentPrimitive_le β a t hβ ht.le
      nlinarith
    calc |quadPowerPrimitive β a t - quadPrimitive β a t + quadMomentPrimitive β a t / t|
        ≤ |quadPowerPrimitive β a t - quadPrimitive β a t| + |quadMomentPrimitive β a t / t| :=
          abs_add_le _ _
      _ ≤ |quadPowerPrimitive β a t| + |quadPrimitive β a t| + |quadMomentPrimitive β a t / t| :=
          add_le_add (abs_sub _ _) le_rfl
      _ ≤ E / 2 * t + E * t + E * t / 2 := add_le_add (add_le_add hK hF0) hF1
      _ = 2 * E * t := by ring
  have hG1 : G 1 = 0 := by
    by_contra hne
    have hpos : 0 < |G 1| := abs_pos.2 hne
    set t := min 1 (|G 1| / (4 * E)) with ht
    have ht0 : 0 < t := lt_min one_pos (by positivity)
    have ht1 : t ≤ 1 := min_le_left _ _
    have ht2 : t ≤ |G 1| / (4 * E) := min_le_right _ _
    have h1 := hbound t ht0 ht1
    rw [hconst t ht0] at h1
    have : 2 * E * t ≤ |G 1| / 2 := by
      calc 2 * E * t ≤ 2 * E * (|G 1| / (4 * E)) := by gcongr
        _ = |G 1| / 2 := by field_simp; ring
    linarith
  have := hconst L hL
  rw [hG1, hGapp] at this
  linarith

/-- **Inner substitution with the weight `v`**: `∫₀^b v f(cv) dv = c⁻² F₁(cb)`, `c = √n u`. -/
theorem twoDH01_inner (β a b n u : ℝ) (hn : 0 < n) (hu : 0 < u) (hb : 0 < b) :
    (∫ v in Ioc (0 : ℝ) b, v * Real.exp (-β * n * (u * v) ^ 2 + β * Real.sqrt n * (u * v) * a))
      = ((Real.sqrt n * u) ^ 2)⁻¹ * quadMomentPrimitive β a (Real.sqrt n * u * b) := by
  have hc : Real.sqrt n * u ≠ 0 := by positivity
  have hfun : ∀ v, v * Real.exp (-β * n * (u * v) ^ 2 + β * Real.sqrt n * (u * v) * a)
      = (Real.sqrt n * u)⁻¹
        * ((Real.sqrt n * u * v) * quadKernel β a (Real.sqrt n * u * v)) := by
    intro v
    have hk : Real.exp (-β * n * (u * v) ^ 2 + β * Real.sqrt n * (u * v) * a)
        = quadKernel β a (Real.sqrt n * u * v) := by
      unfold quadKernel
      congr 1
      rw [show (Real.sqrt n * u * v) ^ 2 = Real.sqrt n ^ 2 * (u * v) ^ 2 by ring,
        Real.sq_sqrt hn.le]
      ring
    rw [hk]; field_simp
  simp_rw [hfun]
  have hsub : (∫ v in (0 : ℝ)..b, (Real.sqrt n * u * v) * quadKernel β a (Real.sqrt n * u * v))
      = (Real.sqrt n * u)⁻¹ • ∫ x in (Real.sqrt n * u * 0)..(Real.sqrt n * u * b),
          x * quadKernel β a x :=
    intervalIntegral.integral_comp_mul_left (fun x => x * quadKernel β a x) hc
  rw [← intervalIntegral.integral_of_le hb.le, intervalIntegral.integral_const_mul, hsub, mul_zero,
    smul_eq_mul, quadMomentPrimitive]
  ring

/-- **Outer substitution**: `Z(n) = (b/√n) K(√n b²)`. -/
theorem twoDIntegralH01_eq (β a b n : ℝ) (hn : 0 < n) (hb : 0 < b) :
    twoDIntegralH01 β a b n = b / Real.sqrt n * quadPowerPrimitive β a (Real.sqrt n * b ^ 2) := by
  unfold twoDIntegralH01
  have hsn : 0 < Real.sqrt n := Real.sqrt_pos.2 hn
  have hc' : Real.sqrt n * b ≠ 0 := by positivity
  have hin : ∀ u ∈ Ioc (0 : ℝ) b,
      (∫ v in Ioc (0 : ℝ) b, v * Real.exp (-β * n * (u * v) ^ 2 + β * Real.sqrt n * (u * v) * a))
        = (1 / n) * ((u ^ 2)⁻¹ * quadMomentPrimitive β a (Real.sqrt n * b * u)) := by
    intro u hu
    rw [twoDH01_inner β a b n u hn hu.1 hb, show Real.sqrt n * u * b = Real.sqrt n * b * u by ring,
      mul_pow, Real.sq_sqrt hn.le]
    field_simp
  rw [setIntegral_congr_fun measurableSet_Ioc hin, MeasureTheory.integral_const_mul]
  have hpt : ∀ u, (u ^ 2)⁻¹ * quadMomentPrimitive β a (Real.sqrt n * b * u)
      = (Real.sqrt n * b) ^ 2 * (((Real.sqrt n * b * u) ^ 2)⁻¹
        * quadMomentPrimitive β a (Real.sqrt n * b * u)) := by
    intro u
    rcases eq_or_ne u 0 with h0 | h0
    · simp [h0]
    · field_simp
  simp_rw [hpt]
  have hsub : (∫ u in (0 : ℝ)..b,
      ((Real.sqrt n * b * u) ^ 2)⁻¹ * quadMomentPrimitive β a (Real.sqrt n * b * u))
      = (Real.sqrt n * b)⁻¹ • ∫ x in (Real.sqrt n * b * 0)..(Real.sqrt n * b * b),
          (x ^ 2)⁻¹ * quadMomentPrimitive β a x :=
    intervalIntegral.integral_comp_mul_left (fun x => (x ^ 2)⁻¹ * quadMomentPrimitive β a x) hc'
  rw [← intervalIntegral.integral_of_le hb.le, intervalIntegral.integral_const_mul, hsub, mul_zero,
    smul_eq_mul, show Real.sqrt n * b * b = Real.sqrt n * b ^ 2 by ring, mul_pow,
    Real.sq_sqrt hn.le, intervalIntegral.integral_of_le (by positivity)]
  unfold quadPowerPrimitive
  rw [intervalIntegral.integral_of_le (by positivity)]
  field_simp

/-- **Exact chart formula**: `Z(n) = b n^{-1/2} F₀(L) - n^{-1} F₁(L)/b`, `L = √n b²`. -/
theorem twoDIntegralH01_exact (β a b n : ℝ) (hβ : 0 < β) (hn : 0 < n) (hb : 0 < b) :
    twoDIntegralH01 β a b n
      = b * (Real.sqrt n)⁻¹ * quadPrimitive β a (Real.sqrt n * b ^ 2)
        - n⁻¹ * b⁻¹ * quadMomentPrimitive β a (Real.sqrt n * b ^ 2) := by
  have hsn : 0 < Real.sqrt n := Real.sqrt_pos.2 hn
  have hss : Real.sqrt n * Real.sqrt n = n := Real.mul_self_sqrt hn.le
  rw [twoDIntegralH01_eq β a b n hn hb, quadPowerPrimitive_eq β a _ hβ (by positivity)]
  field_simp
  ring_nf
  rw [Real.sq_sqrt hn.le]; ring

/-- **Explicit error**: `|Z(n) - b A n^{-1/2}| ≤ (2M/b) n^{-1}`. -/
theorem twoDIntegralH01_sub_le (β a b n : ℝ) (hβ : 0 < β) (hn : 0 < n) (hb : 0 < b) :
    |twoDIntegralH01 β a b n - b * quadMass β a * (Real.sqrt n)⁻¹|
      ≤ 2 * quadMoment β a / b * n⁻¹ := by
  have hsn : 0 < Real.sqrt n := Real.sqrt_pos.2 hn
  have hss : Real.sqrt n * Real.sqrt n = n := Real.mul_self_sqrt hn.le
  rw [twoDIntegralH01_exact β a b n hβ hn hb]
  set L := Real.sqrt n * b ^ 2 with hL
  have hL0 : 0 < L := by positivity
  have h1 : |quadPrimitive β a L - quadMass β a| ≤ quadMoment β a / L := by
    rw [abs_sub_comm, abs_of_nonneg (quadMass_sub_primitive_nonneg β a L hβ hL0.le)]
    exact quadMass_sub_primitive_le β a L hβ hL0
  have h2 : |quadMomentPrimitive β a L| ≤ quadMoment β a := by
    rw [abs_of_nonneg (quadMomentPrimitive_nonneg β a L hL0.le)]
    exact quadMomentPrimitive_le_moment β a L hβ hL0.le
  have hM0 := quadMoment_nonneg β a
  calc |b * (Real.sqrt n)⁻¹ * quadPrimitive β a L - n⁻¹ * b⁻¹ * quadMomentPrimitive β a L
        - b * quadMass β a * (Real.sqrt n)⁻¹|
      = |b * (Real.sqrt n)⁻¹ * (quadPrimitive β a L - quadMass β a)
          - n⁻¹ * b⁻¹ * quadMomentPrimitive β a L| := by congr 1; ring
    _ ≤ |b * (Real.sqrt n)⁻¹ * (quadPrimitive β a L - quadMass β a)|
          + |n⁻¹ * b⁻¹ * quadMomentPrimitive β a L| := abs_sub _ _
    _ = b * (Real.sqrt n)⁻¹ * |quadPrimitive β a L - quadMass β a|
          + n⁻¹ * b⁻¹ * |quadMomentPrimitive β a L| := by
        simp only [abs_mul, abs_of_pos hb, abs_of_pos (inv_pos.2 hsn), abs_of_pos (inv_pos.2 hn),
          abs_of_pos (inv_pos.2 hb)]
    _ ≤ b * (Real.sqrt n)⁻¹ * (quadMoment β a / L) + n⁻¹ * b⁻¹ * quadMoment β a :=
        add_le_add (mul_le_mul_of_nonneg_left h1 (by positivity))
          (mul_le_mul_of_nonneg_left h2 (by positivity))
    _ = 2 * quadMoment β a / b * n⁻¹ := by
        rw [hL]; field_simp; simp only [Real.sq_sqrt hn.le]; ring

/-- **No `log n` when the candidate exponents differ** (grammar §4.2, `d = 2`, `k = (1,1)`,
`h = (0,1)`, `μ₁ = 1/2 < μ₂ = 1`): `Z(n) ~ (b S_{1/2}(a)/2) · n^{-1/2}` — leading exponent
`min(μ₁, μ₂)` with multiplicity `1`. -/
theorem twoDIntegralH01_isEquivalent (β a b : ℝ) (hβ : 0 < β) (hb : 0 < b) :
    (fun n : ℝ => twoDIntegralH01 β a b n) ~[atTop]
      fun n : ℝ => b * fluctuation β (1 / 2) a / 2 * n ^ (-(1 / 2 : ℝ)) := by
  have hA : b * quadMass β a = b * fluctuation β (1 / 2) a / 2 := by rw [quadMass_eq]; ring
  have hS := fluctuation_pos β (1 / 2) a hβ (by norm_num)
  apply IsLittleO.isEquivalent
  have hbig : (fun n : ℝ => twoDIntegralH01 β a b n
      - b * fluctuation β (1 / 2) a / 2 * n ^ (-(1 / 2 : ℝ)))
      =O[atTop] fun n : ℝ => n ^ (-(1 : ℝ)) := by
    apply IsBigO.of_bound (2 * quadMoment β a / b)
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with n hn
    have hsn : 0 < Real.sqrt n := Real.sqrt_pos.2 hn
    have := twoDIntegralH01_sub_le β a b n hβ hn hb
    rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_pos (Real.rpow_pos_of_pos hn _),
      Real.rpow_neg_one, ← hA,
      show (n : ℝ) ^ (-(1 / 2 : ℝ)) = (Real.sqrt n)⁻¹ by
        rw [Real.sqrt_eq_rpow, ← Real.rpow_neg hn.le]]
    exact this
  have hlit := hbig.trans_isLittleO (isLittleO_rpow_neg_rpow_neg (by norm_num : (1 / 2 : ℝ) < 1))
  exact hlit.const_mul_right (by positivity)

end Laplace.Grammar
