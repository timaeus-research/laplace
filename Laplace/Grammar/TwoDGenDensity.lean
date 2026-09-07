/-
Copyright (c) 2026 Timaeus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Laplace.Grammar.OneDSecondOrder

/-!
# The two-dimensional amplitude integral and its one-variable density (grammar §4.2, `d = 2`)

For an amplitude `Φ(u, v, s)` the two-dimensional chart integral is

  `Z_Φ(N) = ∫₀^b u^{h₁} ∫₀^b v^{h₂} e^{-β(N u^{k₁} v^{k₂})²} Φ(u, v, N u^{k₁} v^{k₂}) dv du`

(`twoDAmp`). It is symmetric under exchanging the two coordinates (`twoDAmp_swap`), and when the
amplitude depends on `u` only, `Φ(u, v, s) = Ψ(u, s)`, with equal exponents
`(h₁+1)/k₁ = (h₂+1)/k₂ = p`, it is the transfer integral of the exact one-variable density

  `ρ_Ψ(r, s) = k₂⁻¹ r^{p-1} ∫_{(r/b^{k₂})^{1/k₁}}^{b} u⁻¹ Ψ(u, s) du`,   `R = b^{k₁+k₂}`

(`twoDAmp_uOnly_eq_transferZ`): inner substitution `r = u^{k₁} v^{k₂}` and Fubini on the region
`{r ≤ u^{k₁} b^{k₂}}`. This is the mechanism behind the anchored subtraction of the `d = 2` theorem.
Zero `sorry`/`axiom`.
-/

open Real MeasureTheory Set Filter Topology

namespace Laplace.Grammar

/-- The two-dimensional chart integral with general amplitude `Φ(u, v, s)`,
`s = N u^{k₁} v^{k₂}`. -/
noncomputable def twoDAmp (β b N : ℝ) (h₁ h₂ k₁ k₂ : ℕ) (Φ : ℝ → ℝ → ℝ → ℝ) : ℝ :=
  ∫ u in Ioc (0 : ℝ) b, u ^ h₁ * ∫ v in Ioc (0 : ℝ) b, v ^ h₂
    * (Real.exp (-β * (N * (u ^ k₁ * v ^ k₂)) ^ 2) * Φ u v (N * (u ^ k₁ * v ^ k₂)))

/-- The one-variable density `ρ_Ψ(r, s) = k₂⁻¹ r^{p-1} ∫_{(r/b^{k₂})^{1/k₁}}^{b} u⁻¹ Ψ(u, s) du`. -/
noncomputable def uDensity (p b : ℝ) (k₁ k₂ : ℕ) (Ψ : ℝ → ℝ → ℝ) (r s : ℝ) : ℝ :=
  1 / (k₂ : ℝ) * r ^ (p - 1)
    * ∫ u in Icc ((r / b ^ k₂) ^ ((k₁ : ℝ)⁻¹)) b, u⁻¹ * Ψ u s

/-- **Symmetry**: exchanging the two coordinates. -/
theorem twoDAmp_swap (β b N : ℝ) (h₁ h₂ k₁ k₂ : ℕ) (Φ : ℝ → ℝ → ℝ → ℝ)
    (hΦ : Continuous fun x : ℝ × ℝ × ℝ => Φ x.1 x.2.1 x.2.2) :
    twoDAmp β b N h₁ h₂ k₁ k₂ Φ = twoDAmp β b N h₂ h₁ k₂ k₁ (fun v u s => Φ u v s) := by
  unfold twoDAmp
  have hcont : Continuous (fun z : ℝ × ℝ => z.1 ^ h₁ * (z.2 ^ h₂
      * (Real.exp (-β * (N * (z.1 ^ k₁ * z.2 ^ k₂)) ^ 2)
        * Φ z.1 z.2 (N * (z.1 ^ k₁ * z.2 ^ k₂))))) := by
    have h1 : Continuous fun z : ℝ × ℝ => Φ z.1 z.2 (N * (z.1 ^ k₁ * z.2 ^ k₂)) :=
      hΦ.comp (continuous_fst.prodMk (continuous_snd.prodMk (by fun_prop)))
    fun_prop
  have hint : Integrable (Function.uncurry fun u v : ℝ => u ^ h₁ * (v ^ h₂
      * (Real.exp (-β * (N * (u ^ k₁ * v ^ k₂)) ^ 2) * Φ u v (N * (u ^ k₁ * v ^ k₂)))))
      (((volume : Measure ℝ).restrict (Ioc 0 b)).prod
        ((volume : Measure ℝ).restrict (Ioc 0 b))) := by
    rw [Measure.prod_restrict]
    exact (hcont.continuousOn.integrableOn_compact (isCompact_Icc.prod isCompact_Icc)).mono_set
      (prod_mono Ioc_subset_Icc_self Ioc_subset_Icc_self)
  have hL : ∀ u : ℝ, u ^ h₁ * ∫ v in Ioc (0 : ℝ) b, v ^ h₂
      * (Real.exp (-β * (N * (u ^ k₁ * v ^ k₂)) ^ 2) * Φ u v (N * (u ^ k₁ * v ^ k₂)))
      = ∫ v in Ioc (0 : ℝ) b, u ^ h₁ * (v ^ h₂
        * (Real.exp (-β * (N * (u ^ k₁ * v ^ k₂)) ^ 2) * Φ u v (N * (u ^ k₁ * v ^ k₂)))) :=
    fun u => (integral_const_mul _ _).symm
  simp_rw [hL]
  rw [integral_integral_swap hint]
  refine setIntegral_congr_fun measurableSet_Ioc fun v _ => ?_
  rw [← integral_const_mul]
  refine setIntegral_congr_fun measurableSet_Ioc fun u _ => ?_
  rw [show u ^ k₁ * v ^ k₂ = v ^ k₂ * u ^ k₁ by ring]
  ring

/-- **Inner substitution**: for `u > 0`,
`∫₀^b v^{h₂} g(u^{k₁} v^{k₂}) dv = k₂⁻¹ (u^{k₁})^{-p} ∫₀^{u^{k₁} b^{k₂}} r^{p-1} g(r) dr`. -/
theorem inner_subst (h₂ k₂ : ℕ) (b u : ℝ) (hk₂ : 0 < k₂) (hb : 0 < b) (hu : 0 < u) (k₁ : ℕ)
    (g : ℝ → ℝ) :
    (∫ v in Ioc (0 : ℝ) b, v ^ h₂ * g (u ^ k₁ * v ^ k₂))
      = 1 / (k₂ : ℝ) * ((u ^ k₁) ^ (-(((h₂ : ℝ) + 1) / k₂))
        * ∫ r in Ioc (0 : ℝ) (u ^ k₁ * b ^ k₂), r ^ (((h₂ : ℝ) + 1) / k₂ - 1) * g r) := by
  rw [integral_Ioc_pow_mul_comp_pow h₂ k₂ b (fun x => g (u ^ k₁ * x)) hk₂ hb]
  have hu' : 0 < u ^ k₁ := pow_pos hu _
  rw [integral_Ioc_rpow_mul_comp_mul_left (((h₂ : ℝ) + 1) / k₂ - 1) (u ^ k₁) (b ^ k₂) g hu'
    (by positivity)]
  congr 2
  ring_nf

/-- The region integrand `f(u, r) = 1_{r ≤ u^{k₁} b^{k₂}} u⁻¹ r^{p-1} e^{-β(Nr)²} Ψ(u, Nr)`. -/
noncomputable def regionIntegrand (β b N p : ℝ) (k₁ k₂ : ℕ) (Ψ : ℝ → ℝ → ℝ) (u r : ℝ) : ℝ :=
  if r ≤ u ^ k₁ * b ^ k₂ then u⁻¹ * (r ^ (p - 1) * (Real.exp (-β * (N * r) ^ 2) * Ψ u (N * r)))
  else 0

theorem regionIntegrand_measurable (β b N p : ℝ) (k₁ k₂ : ℕ) (Ψ : ℝ → ℝ → ℝ)
    (hΨ : Measurable (Function.uncurry Ψ)) :
    Measurable (Function.uncurry (regionIntegrand β b N p k₁ k₂ Ψ)) := by
  unfold regionIntegrand Function.uncurry
  refine Measurable.ite (measurableSet_le measurable_snd ((measurable_fst.pow_const _).mul
    measurable_const)) ?_ measurable_const
  refine measurable_fst.inv.mul ((measurable_snd.pow_const _).mul
    ((Real.measurable_exp.comp (measurable_const.mul
      ((measurable_const.mul measurable_snd).pow_const _))).mul ?_))
  exact hΨ.comp (measurable_fst.prodMk (measurable_const.mul measurable_snd))

/-- For `u ∈ (0, b]`, the `r`-section over `(0, R]` is the integral over `(0, u^{k₁} b^{k₂}]`. -/
theorem regionIntegrand_integral_r (β b N p : ℝ) (k₁ k₂ : ℕ) (hb : 0 < b) (Ψ : ℝ → ℝ → ℝ) (u : ℝ)
    (hu : u ∈ Ioc (0 : ℝ) b) :
    ∫ r in Ioc (0 : ℝ) (b ^ (k₁ + k₂)), regionIntegrand β b N p k₁ k₂ Ψ u r
      = u⁻¹ * ∫ r in Ioc (0 : ℝ) (u ^ k₁ * b ^ k₂),
          r ^ (p - 1) * (Real.exp (-β * (N * r) ^ 2) * Ψ u (N * r)) := by
  have h1 : ∀ r, regionIntegrand β b N p k₁ k₂ Ψ u r
      = (Iic (u ^ k₁ * b ^ k₂)).indicator
          (fun r => u⁻¹ * (r ^ (p - 1) * (Real.exp (-β * (N * r) ^ 2) * Ψ u (N * r)))) r := by
    intro r; simp only [regionIntegrand, indicator_apply, mem_Iic]
  simp_rw [h1]
  have hub : u ^ k₁ * b ^ k₂ ≤ b ^ (k₁ + k₂) := by
    rw [pow_add]
    exact mul_le_mul_of_nonneg_right (pow_le_pow_left₀ hu.1.le hu.2 _) (by positivity)
  have hset : Ioc (0 : ℝ) (b ^ (k₁ + k₂)) ∩ Iic (u ^ k₁ * b ^ k₂) = Ioc 0 (u ^ k₁ * b ^ k₂) := by
    ext r; simp only [mem_inter_iff, mem_Ioc, mem_Iic]
    constructor
    · rintro ⟨⟨h1, _⟩, h3⟩; exact ⟨h1, h3⟩
    · rintro ⟨h1, h2⟩; exact ⟨⟨h1, h2.trans hub⟩, h2⟩
  rw [setIntegral_indicator measurableSet_Iic, hset, ← integral_const_mul]

/-- For `r ∈ (0, R]`, the `u`-section over `(0, b]` is the integral over
`[(r/b^{k₂})^{1/k₁}, b]`. -/
theorem regionIntegrand_integral_u (β b N p : ℝ) (k₁ k₂ : ℕ) (hk₁ : 0 < k₁) (hb : 0 < b)
    (Ψ : ℝ → ℝ → ℝ) (r : ℝ) (hr : r ∈ Ioc (0 : ℝ) (b ^ (k₁ + k₂))) :
    ∫ u in Ioc (0 : ℝ) b, regionIntegrand β b N p k₁ k₂ Ψ u r
      = r ^ (p - 1) * (Real.exp (-β * (N * r) ^ 2)
        * ∫ u in Icc ((r / b ^ k₂) ^ ((k₁ : ℝ)⁻¹)) b, u⁻¹ * Ψ u (N * r)) := by
  set m : ℝ := (r / b ^ k₂) ^ ((k₁ : ℝ)⁻¹) with hm
  have hbk : 0 < b ^ k₂ := by positivity
  have hm0 : 0 < m := Real.rpow_pos_of_pos (div_pos hr.1 hbk) _
  -- the condition `r ≤ u^{k₁} b^{k₂}` is `m ≤ u` for `u > 0`
  have hcond : ∀ u, 0 < u → (r ≤ u ^ k₁ * b ^ k₂ ↔ m ≤ u) := by
    intro u hu
    rw [hm, ← Real.rpow_natCast u k₁, ← Real.rpow_le_rpow_iff (z := (k₁ : ℝ)) (by positivity)
      hu.le (by positivity), ← Real.rpow_mul (div_pos hr.1 hbk).le, inv_mul_cancel₀
      (by positivity : (k₁ : ℝ) ≠ 0), Real.rpow_one, div_le_iff₀ hbk]
  have h1 : ∀ u ∈ Ioc (0 : ℝ) b, regionIntegrand β b N p k₁ k₂ Ψ u r
      = (Ici m).indicator
          (fun u => r ^ (p - 1) * (Real.exp (-β * (N * r) ^ 2) * (u⁻¹ * Ψ u (N * r)))) u := by
    intro u hu
    simp only [regionIntegrand, indicator_apply, mem_Ici, hcond u hu.1]
    split_ifs <;> ring_nf
  rw [setIntegral_congr_fun measurableSet_Ioc h1, setIntegral_indicator measurableSet_Ici]
  have hmb : m ≤ b := by
    have : (r / b ^ k₂) ^ ((k₁ : ℝ)⁻¹) ≤ (b ^ k₁) ^ ((k₁ : ℝ)⁻¹) := by
      refine Real.rpow_le_rpow (div_pos hr.1 hbk).le ?_ (by positivity)
      rw [div_le_iff₀ hbk, ← pow_add]; exact hr.2
    rwa [Real.pow_rpow_inv_natCast hb.le hk₁.ne'] at this
  have hset : Ioc (0 : ℝ) b ∩ Ici m = Icc m b := by
    ext u; simp only [mem_inter_iff, mem_Ioc, mem_Ici, mem_Icc]
    constructor
    · rintro ⟨⟨_, h2⟩, h3⟩; exact ⟨h3, h2⟩
    · rintro ⟨h1, h2⟩; exact ⟨⟨lt_of_lt_of_le hm0 h1, h2⟩, h1⟩
  rw [hset, integral_const_mul, integral_const_mul]

/-- Integrability of the region integrand on `(0, b] × (0, R]` for measurable `Ψ` bounded on the
relevant compact set. -/
theorem regionIntegrand_integrable (β b N p : ℝ) (k₁ k₂ : ℕ) (hβ : 0 ≤ β) (hp : 0 < p) (hb : 0 < b)
    (hk₁ : 0 < k₁) (Ψ : ℝ → ℝ → ℝ) (hΨ : Measurable (Function.uncurry Ψ)) (M : ℝ)
    (hΨM : ∀ u ∈ Ioc (0 : ℝ) b, ∀ r ∈ Ioc (0 : ℝ) (b ^ (k₁ + k₂)), |Ψ u (N * r)| ≤ M) :
    Integrable (Function.uncurry (regionIntegrand β b N p k₁ k₂ Ψ))
      (((volume : Measure ℝ).restrict (Ioc 0 b)).prod
        ((volume : Measure ℝ).restrict (Ioc 0 (b ^ (k₁ + k₂))))) := by
  have hmeas := regionIntegrand_measurable β b N p k₁ k₂ Ψ hΨ
  rw [integrable_prod_iff hmeas.aestronglyMeasurable]
  set R : ℝ := b ^ (k₁ + k₂) with hR
  have hbk : 0 < b ^ k₂ := by positivity
  -- pointwise domination of the section integrand
  have hsec : ∀ u ∈ Ioc (0 : ℝ) b, ∀ r ∈ Ioc (0 : ℝ) R,
      ‖regionIntegrand β b N p k₁ k₂ Ψ u r‖
        ≤ (Iic (u ^ k₁ * b ^ k₂)).indicator (fun r => u⁻¹ * M * r ^ (p - 1)) r := by
    intro u hu r hr
    simp only [regionIntegrand, indicator_apply, mem_Iic]
    split_ifs with hle
    · have hu0 : 0 < u := hu.1
      have hr0 : 0 < r := hr.1
      rw [Real.norm_eq_abs, abs_mul, abs_mul, abs_mul, abs_of_pos (inv_pos.2 hu.1),
        abs_of_nonneg (Real.rpow_nonneg hr.1.le _), abs_of_pos (Real.exp_pos _)]
      have hE : Real.exp (-β * (N * r) ^ 2) ≤ 1 := by
        rw [Real.exp_le_one_iff]; nlinarith [sq_nonneg (N * r)]
      have hΨ' := hΨM u hu r hr
      calc u⁻¹ * (r ^ (p - 1) * (Real.exp (-β * (N * r) ^ 2) * |Ψ u (N * r)|))
          ≤ u⁻¹ * (r ^ (p - 1) * (1 * M)) := by gcongr
        _ = u⁻¹ * M * r ^ (p - 1) := by ring
    · simp
  have hsec_int : ∀ u ∈ Ioc (0 : ℝ) b,
      IntegrableOn (fun r => (Iic (u ^ k₁ * b ^ k₂)).indicator (fun r => u⁻¹ * M * r ^ (p - 1)) r)
        (Ioc 0 R) := by
    intro u hu
    rw [IntegrableOn, integrable_indicator_iff measurableSet_Iic, IntegrableOn,
      Measure.restrict_restrict measurableSet_Iic]
    have hset : Iic (u ^ k₁ * b ^ k₂) ∩ Ioc (0 : ℝ) R = Ioc 0 (u ^ k₁ * b ^ k₂) := by
      have hub : u ^ k₁ * b ^ k₂ ≤ R := by
        rw [hR, pow_add]
        exact mul_le_mul_of_nonneg_right (pow_le_pow_left₀ hu.1.le hu.2 _) hbk.le
      ext r; simp only [mem_inter_iff, mem_Ioc, mem_Iic]
      constructor
      · rintro ⟨h1, ⟨h2, _⟩⟩; exact ⟨h2, h1⟩
      · rintro ⟨h1, h2⟩; exact ⟨h2, ⟨h1, h2.trans hub⟩⟩
    rw [hset]
    exact ((intervalIntegral.intervalIntegrable_rpow' (by linarith : (-1 : ℝ) < p - 1) (a := 0)
      (b := u ^ k₁ * b ^ k₂)).1).const_mul _
  refine ⟨?_, ?_⟩
  · -- sections in `r`
    rw [ae_restrict_iff' measurableSet_Ioc]
    refine Filter.Eventually.of_forall fun u hu => ?_
    refine Integrable.mono' (hsec_int u hu) ?_ ?_
    · exact (hmeas.comp (measurable_const.prodMk measurable_id)).aestronglyMeasurable
    · exact (ae_restrict_iff' measurableSet_Ioc).2 (Filter.Eventually.of_forall fun r hr =>
        hsec u hu r hr)
  · -- integrability of `u ↦ ∫ ‖f(u, r)‖ dr`
    have hdom : IntegrableOn (fun u : ℝ => (M * (b ^ k₂) ^ p / p) * u ^ (p * k₁ - 1))
        (Ioc 0 b) := by
      have hpk : (-1 : ℝ) < p * k₁ - 1 := by
        have : 0 < p * k₁ := by positivity
        linarith
      exact ((intervalIntegral.intervalIntegrable_rpow' hpk (a := 0) (b := b)).1).const_mul _
    refine Integrable.mono' hdom ?_ ?_
    · exact (hmeas.norm.stronglyMeasurable.integral_prod_right').aestronglyMeasurable
    · rw [ae_restrict_iff' measurableSet_Ioc]
      refine Filter.Eventually.of_forall fun u hu => ?_
      have hu0 := hu.1
      have hint := hsec_int u hu
      have h1 : ‖∫ r in Ioc (0 : ℝ) R, ‖regionIntegrand β b N p k₁ k₂ Ψ u r‖‖
          ≤ ∫ r in Ioc (0 : ℝ) R,
              (Iic (u ^ k₁ * b ^ k₂)).indicator (fun r => u⁻¹ * M * r ^ (p - 1)) r := by
        refine norm_integral_le_of_norm_le hint ((ae_restrict_iff' measurableSet_Ioc).2
          (Filter.Eventually.of_forall fun r hr => ?_))
        rw [norm_norm]; exact hsec u hu r hr
      have hset : Ioc (0 : ℝ) R ∩ Iic (u ^ k₁ * b ^ k₂) = Ioc 0 (u ^ k₁ * b ^ k₂) := by
        have hub : u ^ k₁ * b ^ k₂ ≤ R := by
          rw [hR, pow_add]
          exact mul_le_mul_of_nonneg_right (pow_le_pow_left₀ hu.1.le hu.2 _) hbk.le
        ext r; simp only [mem_inter_iff, mem_Ioc, mem_Iic]
        constructor
        · rintro ⟨⟨h1, _⟩, h3⟩; exact ⟨h1, h3⟩
        · rintro ⟨h1, h2⟩; exact ⟨⟨h1, h2.trans hub⟩, h2⟩
      have h2 : ∫ r in Ioc (0 : ℝ) R,
          (Iic (u ^ k₁ * b ^ k₂)).indicator (fun r => u⁻¹ * M * r ^ (p - 1)) r
          = u⁻¹ * M * ((u ^ k₁ * b ^ k₂) ^ p / p) := by
        rw [setIntegral_indicator measurableSet_Iic, hset, integral_const_mul,
          integral_Ioc_rpow_sub_one p _ hp (by positivity)]
      have h3 : u⁻¹ * M * ((u ^ k₁ * b ^ k₂) ^ p / p)
          = (M * (b ^ k₂) ^ p / p) * u ^ (p * k₁ - 1) := by
        rw [Real.mul_rpow (by positivity) hbk.le, ← Real.rpow_natCast u k₁, ← Real.rpow_mul hu0.le,
          Real.rpow_sub hu0, Real.rpow_one, mul_comm (k₁ : ℝ) p]
        field_simp
      calc ‖∫ r in Ioc (0 : ℝ) R, ‖regionIntegrand β b N p k₁ k₂ Ψ u r‖‖
          ≤ u⁻¹ * M * ((u ^ k₁ * b ^ k₂) ^ p / p) := h1.trans (le_of_eq h2)
        _ = _ := h3

/-- **The exact one-variable density**: for `Φ(u, v, s) = Ψ(u, s)` and equal exponents
`(h₁+1)/k₁ = (h₂+1)/k₂ = p`, `Z_Φ(N) = ∫₀^R e^{-β(Nr)²} ρ_Ψ(r, Nr) dr`. -/
theorem twoDAmp_uOnly_eq_transferZ (β b N p : ℝ) (h₁ h₂ k₁ k₂ : ℕ) (hβ : 0 ≤ β) (hb : 0 < b)
    (hN : 0 ≤ N) (hk₁ : 0 < k₁) (hk₂ : 0 < k₂) (hp₁ : ((h₁ : ℝ) + 1) / k₁ = p)
    (hp₂ : ((h₂ : ℝ) + 1) / k₂ = p) (Ψ : ℝ → ℝ → ℝ) (hΨc : Continuous (Function.uncurry Ψ)) :
    twoDAmp β b N h₁ h₂ k₁ k₂ (fun u _ s => Ψ u s)
      = transferZ (uDensity p b k₁ k₂ Ψ) β (b ^ (k₁ + k₂)) N := by
  have hk₁' : (0 : ℝ) < k₁ := Nat.cast_pos.2 hk₁
  have hp0 : 0 < p := by rw [← hp₁]; positivity
  set R : ℝ := b ^ (k₁ + k₂) with hR
  have hR0 : 0 < R := by positivity
  -- boundedness of `Ψ` on the compact set
  have hcpt : IsCompact (Icc (0 : ℝ) b ×ˢ Icc (0 : ℝ) (N * R)) := isCompact_Icc.prod isCompact_Icc
  obtain ⟨M₀, hM₀⟩ := hcpt.exists_bound_of_continuousOn hΨc.continuousOn
  set M : ℝ := max M₀ 0 with hMdef
  have hM : 0 ≤ M := le_max_right _ _
  have hΨM : ∀ u ∈ Ioc (0 : ℝ) b, ∀ r ∈ Ioc (0 : ℝ) R, |Ψ u (N * r)| ≤ M := by
    intro u hu r hr
    have hmem : (u, N * r) ∈ Icc (0 : ℝ) b ×ˢ Icc (0 : ℝ) (N * R) :=
      ⟨⟨hu.1.le, hu.2⟩, ⟨mul_nonneg hN hr.1.le, mul_le_mul_of_nonneg_left hr.2 hN⟩⟩
    have := hM₀ (u, N * r) hmem
    rw [Function.uncurry_apply_pair, Real.norm_eq_abs] at this
    exact this.trans (le_max_left _ _)
  have hint := regionIntegrand_integrable β b N p k₁ k₂ hβ hp0 hb hk₁ Ψ hΨc.measurable M hΨM
  -- Step 1: inner substitution and the power identity
  have hstep1 : twoDAmp β b N h₁ h₂ k₁ k₂ (fun u _ s => Ψ u s)
      = 1 / (k₂ : ℝ) * ∫ u in Ioc (0 : ℝ) b, ∫ r in Ioc (0 : ℝ) R,
          regionIntegrand β b N p k₁ k₂ Ψ u r := by
    unfold twoDAmp
    rw [← integral_const_mul]
    refine setIntegral_congr_fun measurableSet_Ioc fun u hu => ?_
    rw [regionIntegrand_integral_r β b N p k₁ k₂ hb Ψ u hu]
    have hsub := inner_subst h₂ k₂ b u hk₂ hb hu.1 k₁
      (fun x => Real.exp (-β * (N * x) ^ 2) * Ψ u (N * x))
    rw [hp₂] at hsub
    have hpt : ∀ v : ℝ, v ^ h₂ * (Real.exp (-β * (N * (u ^ k₁ * v ^ k₂)) ^ 2)
        * Ψ u (N * (u ^ k₁ * v ^ k₂)))
        = v ^ h₂ * (fun x => Real.exp (-β * (N * x) ^ 2) * Ψ u (N * x)) (u ^ k₁ * v ^ k₂) :=
      fun v => rfl
    simp_rw [hpt]
    rw [hsub]
    -- `u^{h₁} (u^{k₁})^{-p} = u⁻¹`
    have hpow : (u : ℝ) ^ h₁ * (u ^ k₁) ^ (-p) = u⁻¹ := by
      rw [← Real.rpow_natCast u h₁, ← Real.rpow_natCast u k₁, ← Real.rpow_mul hu.1.le,
        ← Real.rpow_add hu.1, ← Real.rpow_neg_one]
      congr 1
      have : (k₁ : ℝ) * p = (h₁ : ℝ) + 1 := by rw [← hp₁]; field_simp
      linarith
    calc u ^ h₁ * (1 / (k₂ : ℝ) * ((u ^ k₁) ^ (-p) * ∫ r in Ioc (0 : ℝ) (u ^ k₁ * b ^ k₂),
          r ^ (p - 1) * (Real.exp (-β * (N * r) ^ 2) * Ψ u (N * r))))
        = 1 / (k₂ : ℝ) * ((u ^ h₁ * (u ^ k₁) ^ (-p)) * ∫ r in Ioc (0 : ℝ) (u ^ k₁ * b ^ k₂),
          r ^ (p - 1) * (Real.exp (-β * (N * r) ^ 2) * Ψ u (N * r))) := by ring
      _ = _ := by rw [hpow]
  -- Step 2: Fubini and the `u`-sections
  rw [hstep1, integral_integral_swap hint]
  unfold transferZ
  rw [← integral_const_mul]
  refine setIntegral_congr_fun measurableSet_Ioc fun r hr => ?_
  rw [regionIntegrand_integral_u β b N p k₁ k₂ hk₁ hb Ψ r hr]
  unfold uDensity
  ring

end Laplace.Grammar
