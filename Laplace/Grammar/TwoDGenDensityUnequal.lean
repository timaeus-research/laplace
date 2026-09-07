/-
Copyright (c) 2026 Timaeus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Laplace.Grammar.JetIdentification

/-!
# The one-variable density for unequal exponents (grammar §4.2, higher-order `d = 2`)

Unit 86 gave the exact one-variable density of
`∫∫ u^{h₁} v^{h₂} e^{-β(Nu^{k₁}v^{k₂})²} Ψ(u, Nu^{k₁}v^{k₂})` when the two exponents
`(h_i+1)/k_i` agree. Here the restriction is dropped: with
`p₂ = (h₂+1)/k₂` the density in `r = u^{k₁} v^{k₂}` is

  `ρ(r, s) = k₂⁻¹ r^{p₂-1} ∫_{(r/b^{k₂})^{1/k₁}}^{b} u^{h₁ - k₁ p₂} Ψ(u, s) du`   (`genDensity`),

i.e. a weighted axis integral with weight `u^{-1-γ}`, `γ = k₁(p₂ − p₁)`. This is exactly the shape
consumed by the weighted finite-part axis lemma (unit 100): the face terms `u^i a_i(v, s)` of the
rectangular decomposition have exponents `p + i/k₁ ≠ p`. Zero `sorry`/`axiom`.
-/

open Real MeasureTheory Set

namespace Laplace.Grammar

/-- The one-variable density for unequal exponents:
`ρ(r, s) = k₂⁻¹ r^{p₂-1} ∫_{(r/b^{k₂})^{1/k₁}}^{b} u^{h₁ - k₁ p₂} Ψ(u, s) du`. -/
noncomputable def genDensity (p₂ b : ℝ) (h₁ k₁ k₂ : ℕ) (Ψ : ℝ → ℝ → ℝ) (r s : ℝ) : ℝ :=
  1 / (k₂ : ℝ) * r ^ (p₂ - 1)
    * ∫ u in Icc ((r / b ^ k₂) ^ ((k₁ : ℝ)⁻¹)) b, u ^ ((h₁ : ℝ) - k₁ * p₂) * Ψ u s

/-- The region integrand with the weight `u^{h₁ - k₁ p₂}`. -/
noncomputable def regionIntegrand' (β b N p₂ : ℝ) (h₁ k₁ k₂ : ℕ) (Ψ : ℝ → ℝ → ℝ) (u r : ℝ) : ℝ :=
  if r ≤ u ^ k₁ * b ^ k₂ then
    u ^ ((h₁ : ℝ) - k₁ * p₂) * (r ^ (p₂ - 1) * (Real.exp (-β * (N * r) ^ 2) * Ψ u (N * r)))
  else 0

theorem regionIntegrand'_measurable (β b N p₂ : ℝ) (h₁ k₁ k₂ : ℕ) (Ψ : ℝ → ℝ → ℝ)
    (hΨ : Measurable (Function.uncurry Ψ)) :
    Measurable (Function.uncurry (regionIntegrand' β b N p₂ h₁ k₁ k₂ Ψ)) := by
  unfold regionIntegrand' Function.uncurry
  refine Measurable.ite (measurableSet_le measurable_snd ((measurable_fst.pow_const _).mul
    measurable_const)) ?_ measurable_const
  refine (measurable_fst.pow_const _).mul ((measurable_snd.pow_const _).mul
    ((Real.measurable_exp.comp (measurable_const.mul
      ((measurable_const.mul measurable_snd).pow_const _))).mul ?_))
  exact hΨ.comp (measurable_fst.prodMk (measurable_const.mul measurable_snd))

theorem regionIntegrand'_integral_r (β b N p₂ : ℝ) (h₁ k₁ k₂ : ℕ) (hb : 0 < b) (Ψ : ℝ → ℝ → ℝ)
    (u : ℝ) (hu : u ∈ Ioc (0 : ℝ) b) :
    ∫ r in Ioc (0 : ℝ) (b ^ (k₁ + k₂)), regionIntegrand' β b N p₂ h₁ k₁ k₂ Ψ u r
      = u ^ ((h₁ : ℝ) - k₁ * p₂) * ∫ r in Ioc (0 : ℝ) (u ^ k₁ * b ^ k₂),
          r ^ (p₂ - 1) * (Real.exp (-β * (N * r) ^ 2) * Ψ u (N * r)) := by
  have h1 : ∀ r, regionIntegrand' β b N p₂ h₁ k₁ k₂ Ψ u r
      = (Iic (u ^ k₁ * b ^ k₂)).indicator
          (fun r => u ^ ((h₁ : ℝ) - k₁ * p₂)
            * (r ^ (p₂ - 1) * (Real.exp (-β * (N * r) ^ 2) * Ψ u (N * r)))) r := by
    intro r; simp only [regionIntegrand', indicator_apply, mem_Iic]
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

theorem regionIntegrand'_integral_u (β b N p₂ : ℝ) (h₁ k₁ k₂ : ℕ) (hk₁ : 0 < k₁) (hb : 0 < b)
    (Ψ : ℝ → ℝ → ℝ) (r : ℝ) (hr : r ∈ Ioc (0 : ℝ) (b ^ (k₁ + k₂))) :
    ∫ u in Ioc (0 : ℝ) b, regionIntegrand' β b N p₂ h₁ k₁ k₂ Ψ u r
      = r ^ (p₂ - 1) * (Real.exp (-β * (N * r) ^ 2)
        * ∫ u in Icc ((r / b ^ k₂) ^ ((k₁ : ℝ)⁻¹)) b, u ^ ((h₁ : ℝ) - k₁ * p₂) * Ψ u (N * r)) := by
  set m : ℝ := (r / b ^ k₂) ^ ((k₁ : ℝ)⁻¹) with hm
  have hbk : 0 < b ^ k₂ := by positivity
  have hm0 : 0 < m := Real.rpow_pos_of_pos (div_pos hr.1 hbk) _
  have hcond : ∀ u, 0 < u → (r ≤ u ^ k₁ * b ^ k₂ ↔ m ≤ u) := by
    intro u hu
    rw [hm, ← Real.rpow_natCast u k₁, ← Real.rpow_le_rpow_iff (z := (k₁ : ℝ)) (by positivity)
      hu.le (by positivity), ← Real.rpow_mul (div_pos hr.1 hbk).le, inv_mul_cancel₀
      (by positivity : (k₁ : ℝ) ≠ 0), Real.rpow_one, div_le_iff₀ hbk]
  have h1 : ∀ u ∈ Ioc (0 : ℝ) b, regionIntegrand' β b N p₂ h₁ k₁ k₂ Ψ u r
      = (Ici m).indicator
          (fun u => r ^ (p₂ - 1) * (Real.exp (-β * (N * r) ^ 2)
            * (u ^ ((h₁ : ℝ) - k₁ * p₂) * Ψ u (N * r)))) u := by
    intro u hu
    simp only [regionIntegrand', indicator_apply, mem_Ici, hcond u hu.1]
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

/-- The power identity `u^{h₁ - k₁ p₂} (u^{k₁})^{p₂} = u^{h₁}`. -/
theorem rpow_weight_mul_pow (u p₂ : ℝ) (h₁ k₁ : ℕ) (hu : 0 < u) :
    u ^ ((h₁ : ℝ) - k₁ * p₂) * (u ^ k₁) ^ p₂ = u ^ h₁ := by
  rw [← Real.rpow_natCast u k₁, ← Real.rpow_mul hu.le, ← Real.rpow_add hu, ← Real.rpow_natCast u h₁]
  congr 1
  ring

theorem regionIntegrand'_integrable (β b N p₂ : ℝ) (h₁ k₁ k₂ : ℕ) (hβ : 0 ≤ β) (hp : 0 < p₂)
    (hb : 0 < b) (Ψ : ℝ → ℝ → ℝ) (hΨ : Measurable (Function.uncurry Ψ)) (M : ℝ)
    (hΨM : ∀ u ∈ Ioc (0 : ℝ) b, ∀ r ∈ Ioc (0 : ℝ) (b ^ (k₁ + k₂)), |Ψ u (N * r)| ≤ M) :
    Integrable (Function.uncurry (regionIntegrand' β b N p₂ h₁ k₁ k₂ Ψ))
      (((volume : Measure ℝ).restrict (Ioc 0 b)).prod
        ((volume : Measure ℝ).restrict (Ioc 0 (b ^ (k₁ + k₂))))) := by
  have hmeas := regionIntegrand'_measurable β b N p₂ h₁ k₁ k₂ Ψ hΨ
  rw [integrable_prod_iff hmeas.aestronglyMeasurable]
  set R : ℝ := b ^ (k₁ + k₂) with hR
  have hbk : 0 < b ^ k₂ := by positivity
  have hsec : ∀ u ∈ Ioc (0 : ℝ) b, ∀ r ∈ Ioc (0 : ℝ) R,
      ‖regionIntegrand' β b N p₂ h₁ k₁ k₂ Ψ u r‖
        ≤ (Iic (u ^ k₁ * b ^ k₂)).indicator
            (fun r => u ^ ((h₁ : ℝ) - k₁ * p₂) * M * r ^ (p₂ - 1)) r := by
    intro u hu r hr
    simp only [regionIntegrand', indicator_apply, mem_Iic]
    split_ifs with hle
    · have hu0 : 0 < u := hu.1
      have hr0 : 0 < r := hr.1
      rw [Real.norm_eq_abs, abs_mul, abs_mul, abs_mul, abs_of_nonneg (Real.rpow_nonneg hu0.le _),
        abs_of_nonneg (Real.rpow_nonneg hr.1.le _), abs_of_pos (Real.exp_pos _)]
      have hE : Real.exp (-β * (N * r) ^ 2) ≤ 1 := by
        rw [Real.exp_le_one_iff]; nlinarith [sq_nonneg (N * r)]
      have hΨ' := hΨM u hu r hr
      have hw : 0 ≤ u ^ ((h₁ : ℝ) - k₁ * p₂) := Real.rpow_nonneg hu0.le _
      calc u ^ ((h₁ : ℝ) - k₁ * p₂) * (r ^ (p₂ - 1) * (Real.exp (-β * (N * r) ^ 2) * |Ψ u (N * r)|))
          ≤ u ^ ((h₁ : ℝ) - k₁ * p₂) * (r ^ (p₂ - 1) * (1 * M)) := by gcongr
        _ = _ := by ring
    · simp
  have hsec_int : ∀ u ∈ Ioc (0 : ℝ) b,
      IntegrableOn (fun r => (Iic (u ^ k₁ * b ^ k₂)).indicator
        (fun r => u ^ ((h₁ : ℝ) - k₁ * p₂) * M * r ^ (p₂ - 1)) r) (Ioc 0 R) := by
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
    exact ((intervalIntegral.intervalIntegrable_rpow' (by linarith : (-1 : ℝ) < p₂ - 1) (a := 0)
      (b := u ^ k₁ * b ^ k₂)).1).const_mul _
  refine ⟨?_, ?_⟩
  · rw [ae_restrict_iff' measurableSet_Ioc]
    refine Filter.Eventually.of_forall fun u hu => ?_
    refine Integrable.mono' (hsec_int u hu) ?_ ?_
    · exact (hmeas.comp (measurable_const.prodMk measurable_id)).aestronglyMeasurable
    · exact (ae_restrict_iff' measurableSet_Ioc).2 (Filter.Eventually.of_forall fun r hr =>
        hsec u hu r hr)
  · have hdom : IntegrableOn (fun u : ℝ => (M * (b ^ k₂) ^ p₂ / p₂) * u ^ (h₁ : ℝ)) (Ioc 0 b) := by
      have hpk : (-1 : ℝ) < (h₁ : ℝ) := by
        have : (0 : ℝ) ≤ h₁ := Nat.cast_nonneg h₁
        linarith
      exact ((intervalIntegral.intervalIntegrable_rpow' hpk (a := 0) (b := b)).1).const_mul _
    refine Integrable.mono' hdom ?_ ?_
    · exact (hmeas.norm.stronglyMeasurable.integral_prod_right').aestronglyMeasurable
    · rw [ae_restrict_iff' measurableSet_Ioc]
      refine Filter.Eventually.of_forall fun u hu => ?_
      have hu0 := hu.1
      have hint := hsec_int u hu
      have h1 : ‖∫ r in Ioc (0 : ℝ) R, ‖regionIntegrand' β b N p₂ h₁ k₁ k₂ Ψ u r‖‖
          ≤ ∫ r in Ioc (0 : ℝ) R, (Iic (u ^ k₁ * b ^ k₂)).indicator
              (fun r => u ^ ((h₁ : ℝ) - k₁ * p₂) * M * r ^ (p₂ - 1)) r := by
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
      have h2 : ∫ r in Ioc (0 : ℝ) R, (Iic (u ^ k₁ * b ^ k₂)).indicator
            (fun r => u ^ ((h₁ : ℝ) - k₁ * p₂) * M * r ^ (p₂ - 1)) r
          = u ^ ((h₁ : ℝ) - k₁ * p₂) * M * ((u ^ k₁ * b ^ k₂) ^ p₂ / p₂) := by
        rw [setIntegral_indicator measurableSet_Iic, hset, integral_const_mul,
          integral_Ioc_rpow_sub_one p₂ _ hp (by positivity)]
      have h3 : u ^ ((h₁ : ℝ) - k₁ * p₂) * M * ((u ^ k₁ * b ^ k₂) ^ p₂ / p₂)
          = (M * (b ^ k₂) ^ p₂ / p₂) * u ^ (h₁ : ℝ) := by
        rw [Real.mul_rpow (by positivity) hbk.le, Real.rpow_natCast u h₁,
          ← rpow_weight_mul_pow u p₂ h₁ k₁ hu0]
        ring
      calc ‖∫ r in Ioc (0 : ℝ) R, ‖regionIntegrand' β b N p₂ h₁ k₁ k₂ Ψ u r‖‖
          ≤ u ^ ((h₁ : ℝ) - k₁ * p₂) * M * ((u ^ k₁ * b ^ k₂) ^ p₂ / p₂) := h1.trans (le_of_eq h2)
        _ = _ := h3

/-- **The exact one-variable density for unequal exponents**: for `Φ(u, v, s) = Ψ(u, s)` and
`p₂ = (h₂+1)/k₂`, `Z_Φ(N) = ∫₀^R e^{-β(Nr)²} ρ(r, Nr) dr` with `ρ = genDensity`. -/
theorem twoDAmp_uOnly_eq_transferZ' (β b N p₂ : ℝ) (h₁ h₂ k₁ k₂ : ℕ) (hβ : 0 ≤ β) (hb : 0 < b)
    (hN : 0 ≤ N) (hk₁ : 0 < k₁) (hk₂ : 0 < k₂) (hp₂ : ((h₂ : ℝ) + 1) / k₂ = p₂)
    (Ψ : ℝ → ℝ → ℝ) (hΨc : Continuous (Function.uncurry Ψ)) :
    twoDAmp β b N h₁ h₂ k₁ k₂ (fun u _ s => Ψ u s)
      = transferZ (genDensity p₂ b h₁ k₁ k₂ Ψ) β (b ^ (k₁ + k₂)) N := by
  have hp0 : 0 < p₂ := by rw [← hp₂]; positivity
  set R : ℝ := b ^ (k₁ + k₂) with hR
  have hR0 : 0 < R := by positivity
  have hcpt : IsCompact (Icc (0 : ℝ) b ×ˢ Icc (0 : ℝ) (N * R)) := isCompact_Icc.prod isCompact_Icc
  obtain ⟨M₀, hM₀⟩ := hcpt.exists_bound_of_continuousOn hΨc.continuousOn
  set M : ℝ := max M₀ 0 with hMdef
  have hΨM : ∀ u ∈ Ioc (0 : ℝ) b, ∀ r ∈ Ioc (0 : ℝ) R, |Ψ u (N * r)| ≤ M := by
    intro u hu r hr
    have hmem : (u, N * r) ∈ Icc (0 : ℝ) b ×ˢ Icc (0 : ℝ) (N * R) :=
      ⟨⟨hu.1.le, hu.2⟩, ⟨mul_nonneg hN hr.1.le, mul_le_mul_of_nonneg_left hr.2 hN⟩⟩
    have := hM₀ (u, N * r) hmem
    rw [Function.uncurry_apply_pair, Real.norm_eq_abs] at this
    exact this.trans (le_max_left _ _)
  have hint := regionIntegrand'_integrable β b N p₂ h₁ k₁ k₂ hβ hp0 hb Ψ hΨc.measurable M hΨM
  have hstep1 : twoDAmp β b N h₁ h₂ k₁ k₂ (fun u _ s => Ψ u s)
      = 1 / (k₂ : ℝ) * ∫ u in Ioc (0 : ℝ) b, ∫ r in Ioc (0 : ℝ) R,
          regionIntegrand' β b N p₂ h₁ k₁ k₂ Ψ u r := by
    unfold twoDAmp
    rw [← integral_const_mul]
    refine setIntegral_congr_fun measurableSet_Ioc fun u hu => ?_
    rw [regionIntegrand'_integral_r β b N p₂ h₁ k₁ k₂ hb Ψ u hu]
    have hsub := inner_subst h₂ k₂ b u hk₂ hb hu.1 k₁
      (fun x => Real.exp (-β * (N * x) ^ 2) * Ψ u (N * x))
    rw [hp₂] at hsub
    have hpt : ∀ v : ℝ, v ^ h₂ * (Real.exp (-β * (N * (u ^ k₁ * v ^ k₂)) ^ 2)
        * Ψ u (N * (u ^ k₁ * v ^ k₂)))
        = v ^ h₂ * (fun x => Real.exp (-β * (N * x) ^ 2) * Ψ u (N * x)) (u ^ k₁ * v ^ k₂) :=
      fun v => rfl
    simp_rw [hpt]
    rw [hsub]
    have hpow : (u : ℝ) ^ h₁ * (u ^ k₁) ^ (-p₂) = u ^ ((h₁ : ℝ) - k₁ * p₂) := by
      rw [← Real.rpow_natCast u h₁, ← Real.rpow_natCast u k₁, ← Real.rpow_mul hu.1.le,
        ← Real.rpow_add hu.1]
      congr 1
      ring
    calc u ^ h₁ * (1 / (k₂ : ℝ) * ((u ^ k₁) ^ (-p₂) * ∫ r in Ioc (0 : ℝ) (u ^ k₁ * b ^ k₂),
          r ^ (p₂ - 1) * (Real.exp (-β * (N * r) ^ 2) * Ψ u (N * r))))
        = 1 / (k₂ : ℝ) * ((u ^ h₁ * (u ^ k₁) ^ (-p₂)) * ∫ r in Ioc (0 : ℝ) (u ^ k₁ * b ^ k₂),
          r ^ (p₂ - 1) * (Real.exp (-β * (N * r) ^ 2) * Ψ u (N * r))) := by ring
      _ = _ := by rw [hpow]
  rw [hstep1, integral_integral_swap hint]
  unfold transferZ
  rw [← integral_const_mul]
  refine setIntegral_congr_fun measurableSet_Ioc fun r hr => ?_
  rw [regionIntegrand'_integral_u β b N p₂ h₁ k₁ k₂ hk₁ hb Ψ r hr]
  unfold genDensity
  ring

/-- The inner integral of `genDensity` is the weighted axis integral of unit 100 with
`γ = k₁ p₂ − h₁ − 1` and `ε = (r/b^{k₂})^{1/k₁}`. -/
theorem genDensity_eq_axis (p₂ b : ℝ) (h₁ k₁ k₂ : ℕ) (Ψ : ℝ → ℝ → ℝ) (r s : ℝ) :
    genDensity p₂ b h₁ k₁ k₂ Ψ r s
      = 1 / (k₂ : ℝ) * r ^ (p₂ - 1)
        * ∫ u in Ioc ((r / b ^ k₂) ^ ((k₁ : ℝ)⁻¹)) b,
            u ^ (-1 - ((k₁ : ℝ) * p₂ - h₁ - 1)) * Ψ u s := by
  unfold genDensity
  have h := integral_Icc_eq_integral_Ioc (μ := (volume : Measure ℝ))
    (f := fun u : ℝ => u ^ ((h₁ : ℝ) - k₁ * p₂) * Ψ u s) (x := (r / b ^ k₂) ^ ((k₁ : ℝ)⁻¹)) (y := b)
  rw [h, show (-1 - ((k₁ : ℝ) * p₂ - h₁ - 1)) = (h₁ : ℝ) - k₁ * p₂ by ring]

end Laplace.Grammar
