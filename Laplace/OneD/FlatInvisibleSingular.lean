/-
Copyright (c) 2026 Timaeus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Timaeus
-/
import Mathlib
import Laplace.OneD.FlatWitness

/-!
# Flat perturbations are invisible at singular minima too

The singular counterpart of `flat_perturbation_invisible` (Astra round 16, item 5): the base
loss is no longer harmonic but any continuous `L₁` with `c x^{2k} ≤ L₁ x` near `0` and
`L₁ ≥ c₁ > 0` away from `0`, with `k` arbitrary. A nonnegative bounded perturbation `f` flat at
`0` still changes every compactly-supported-observable integral by less than any power of `1/t`
(`singular_flat_perturbation_invisible`, `singular_flat_perturbation_superpolynomial`), and the
explicit witness `e^{-1/x²}` realises this for the pure power `x^{2k}`
(`singular_flat_witness_superpolynomial`): two smooth nonnegative losses with a common singular
minimum of every order `2k`, different germs, and unnormalised Laplace families agreeing beyond
all orders. This is the exact scope of the note's Proposition on flat perturbations extended to
the singular case, and it brackets the singular identifiability theorem
(`pencil_families_force_eq_near`): analyticity, not nondegeneracy, is what the identifiability
argument uses.

The proof is the pointwise identity `e^{-tL₁} - e^{-t(L₁+f)} = e^{-tL₁}(1 - e^{-tf})` with
`0 ≤ 1 - e^{-tf} ≤ t f`, flatness at order `2km` near `0` where
`t f e^{-tL₁} ≤ t C (x^{2k})^m e^{-tc x^{2k}} ≤ C m! c^{-m} t^{1-m}` (from `y^m e^{-y} ≤ m!`),
and the uniform exponential decay `t M e^{-tc₂}` away from `0`; the integrand is dominated by a
constant multiple of the indicator of the support of `φ`, so no closed-form integral is needed.
-/

open Real MeasureTheory

namespace Laplace.OneD

/-- `y^m e^{-y} ≤ m!` for `y ≥ 0`. -/
theorem pow_mul_exp_neg_le_factorial {y : ℝ} (hy : 0 ≤ y) (m : ℕ) :
    y ^ m * Real.exp (-y) ≤ m.factorial := by
  have h := Real.pow_div_factorial_le_exp _ hy m
  rw [div_le_iff₀ (Nat.cast_pos.mpr m.factorial_pos : (0 : ℝ) < m.factorial)] at h
  rw [Real.exp_neg, ← div_eq_mul_inv, div_le_iff₀ (exp_pos y)]
  linarith

/-- **Flat perturbations are invisible at a singular minimum.** If `L₁` is continuous with
`c x^{2k} ≤ L₁ x` for `|x| ≤ δ₀` and `c₁ ≤ L₁ x` for `|x| > δ₀`, and `f` is continuous,
`0 ≤ f ≤ M`, flat at `0`, then for every continuous compactly supported `φ` and every `N` the
perturbed and unperturbed integrals differ by `O(t^{-N})`. -/
theorem singular_flat_perturbation_invisible {k : ℕ} {L₁ f φ : ℝ → ℝ}
    {c c₁ δ₀ M : ℝ} (hc : 0 < c) (hc₁ : 0 < c₁) (hδ₀ : 0 < δ₀) (hL_c : Continuous L₁)
    (hlow : ∀ x, |x| ≤ δ₀ → c * x ^ (2 * k) ≤ L₁ x) (hfar : ∀ x, δ₀ < |x| → c₁ ≤ L₁ x)
    (hf_c : Continuous f) (hf0 : ∀ x, 0 ≤ f x) (hf_bdd : ∀ x, f x ≤ M)
    (hflat : ∀ n : ℕ, ∃ C δ : ℝ, 0 ≤ C ∧ 0 < δ ∧ ∀ x : ℝ, |x| ≤ δ → f x ≤ C * x ^ (2 * n))
    (hφ_c : Continuous φ) (hφ_s : HasCompactSupport φ) :
    ∀ N : ℕ, ∃ K T : ℝ, 0 ≤ K ∧ 1 ≤ T ∧ ∀ t : ℝ, T ≤ t →
      |(∫ x : ℝ, φ x * Real.exp (-(t * L₁ x))) -
        ∫ x : ℝ, φ x * Real.exp (-(t * (L₁ x + f x)))| ≤ K / t ^ N := by
  intro N
  obtain ⟨C, δ, hC, hδ, hnear⟩ := hflat (k * (N + 1))
  -- a global bound for `|φ|`
  obtain ⟨B, hB⟩ := hφ_s.exists_bound_of_continuousOn hφ_c.continuousOn
  set Mφ : ℝ := max B 0 with hMφ_def
  have hMφ : ∀ x, |φ x| ≤ Mφ := fun x ↦ by
    by_cases hx : x ∈ tsupport φ
    · exact le_sup_of_le_left (hB x hx)
    · rw [image_eq_zero_of_notMem_tsupport hx, abs_zero]
      exact le_max_right _ _
  have hMφ0 : 0 ≤ Mφ := le_max_right _ _
  have hM0 : 0 ≤ M := (hf0 0).trans (hf_bdd 0)
  -- the near radius and the far floor
  set δ' : ℝ := min δ δ₀ with hδ'_def
  have hδ' : 0 < δ' := lt_min hδ hδ₀
  set c₂ : ℝ := min c₁ (c * δ' ^ (2 * k)) with hc₂_def
  have hc₂ : 0 < c₂ := lt_min hc₁ (mul_pos hc (pow_pos hδ' _))
  have hfloor : ∀ x, δ' < |x| → c₂ ≤ L₁ x := by
    intro x hx
    by_cases hx₀ : |x| ≤ δ₀
    · refine (min_le_right _ _).trans ((hlow x hx₀).trans' ?_)
      refine mul_le_mul_of_nonneg_left ?_ hc.le
      rw [← Even.pow_abs (even_two_mul k) x]
      exact pow_le_pow_left₀ hδ'.le hx.le _
    · exact (min_le_left _ _).trans (hfar x (not_le.mp hx₀))
  -- the far decay: `t e^{-c₂ t} ≤ t^{-N}` eventually
  have hlim := tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero ((N : ℝ) + 1) c₂ hc₂
  obtain ⟨T₂, hT₂⟩ := Filter.eventually_atTop.mp (hlim.eventually (gt_mem_nhds one_pos))
  -- the constant
  set K₁ : ℝ := (volume (tsupport φ)).toReal with hK₁_def
  set A : ℝ := C * c⁻¹ ^ (N + 1) * ((N + 1).factorial : ℝ) + M with hA_def
  have hA0 : 0 ≤ A := add_nonneg (mul_nonneg (mul_nonneg hC (pow_nonneg (inv_nonneg.mpr hc.le) _))
    (Nat.cast_nonneg _)) hM0
  refine ⟨K₁ * (Mφ * A), max 1 T₂, mul_nonneg ENNReal.toReal_nonneg (mul_nonneg hMφ0 hA0),
    le_max_left _ _, fun t ht ↦ ?_⟩
  have ht1 : 1 ≤ t := (le_max_left _ _).trans ht
  have ht0 : 0 < t := zero_lt_one.trans_le ht1
  have htN : 0 < t ^ N := pow_pos ht0 N
  have hfarN : t * Real.exp (-(t * c₂)) ≤ 1 / t ^ N := by
    have h := hT₂ t ((le_max_right _ _).trans ht)
    have e : t ^ ((N : ℝ) + 1) = t ^ N * t := by
      rw [show ((N : ℝ) + 1) = ((N + 1 : ℕ) : ℝ) by push_cast; rfl, Real.rpow_natCast, pow_succ]
    rw [e, mul_comm (-c₂) t] at h
    rw [le_div_iff₀ htN]
    have : exp (-(t * c₂)) = exp (t * -c₂) := by ring_nf
    rw [this]
    nlinarith [h]
  -- the pointwise bound
  have hK : IsCompact (tsupport φ) := hφ_s
  have hpt : ∀ x, ‖φ x * (Real.exp (-(t * L₁ x)) - Real.exp (-(t * (L₁ x + f x))))‖ ≤
      (tsupport φ).indicator (fun _ ↦ Mφ * A / t ^ N) x := by
    intro x
    by_cases hx : x ∈ tsupport φ
    · rw [Set.indicator_of_mem hx, Real.norm_eq_abs, abs_mul]
      have hsplit : Real.exp (-(t * L₁ x)) - Real.exp (-(t * (L₁ x + f x))) =
          Real.exp (-(t * L₁ x)) * (1 - Real.exp (-(t * f x))) := by
        rw [mul_add, neg_add, Real.exp_add]
        ring
      have h1 : 0 ≤ 1 - Real.exp (-(t * f x)) := by
        have := Real.exp_le_one_iff.mpr (neg_nonpos.mpr (mul_nonneg ht0.le (hf0 x)))
        linarith
      have h2 : 1 - Real.exp (-(t * f x)) ≤ t * f x := by
        have := Real.add_one_le_exp (-(t * f x))
        linarith
      rw [hsplit, abs_mul, abs_of_pos (exp_pos _), abs_of_nonneg h1]
      -- `|φ| e^{-tL₁} (1 - e^{-tf}) ≤ Mφ · (t f e^{-tL₁})`
      have hcore : Real.exp (-(t * L₁ x)) * (1 - Real.exp (-(t * f x))) ≤ A / t ^ N := by
        by_cases hxδ : |x| ≤ δ'
        · -- near `0`
          have hxδ₀ : |x| ≤ δ₀ := hxδ.trans (min_le_right _ _)
          have hxδ₁ : |x| ≤ δ := hxδ.trans (min_le_left _ _)
          have hf : f x ≤ C * x ^ (2 * (k * (N + 1))) := hnear x hxδ₁
          have hL : Real.exp (-(t * L₁ x)) ≤ Real.exp (-(t * (c * x ^ (2 * k)))) :=
            Real.exp_le_exp.mpr (neg_le_neg (mul_le_mul_of_nonneg_left (hlow x hxδ₀) ht0.le))
          have hxp : 0 ≤ x ^ (2 * k) := (even_two_mul k).pow_nonneg x
          set y : ℝ := t * c * x ^ (2 * k) with hy_def
          have hy : 0 ≤ y := mul_nonneg (mul_nonneg ht0.le hc.le) hxp
          have hpow : x ^ (2 * (k * (N + 1))) = (y / (t * c)) ^ (N + 1) := by
            rw [hy_def, mul_div_cancel_left₀ _ (mul_pos ht0 hc).ne',
              show 2 * (k * (N + 1)) = 2 * k * (N + 1) by ring, pow_mul]
          have hbound : y ^ (N + 1) * Real.exp (-y) ≤ (N + 1).factorial :=
            pow_mul_exp_neg_le_factorial hy (N + 1)
          have hexp : Real.exp (-(t * (c * x ^ (2 * k)))) = Real.exp (-y) := by
            rw [hy_def, mul_assoc]
          have htne : t ≠ 0 := ht0.ne'
          have hcne : c ≠ 0 := hc.ne'
          clear_value y
          calc Real.exp (-(t * L₁ x)) * (1 - Real.exp (-(t * f x)))
              ≤ Real.exp (-(t * (c * x ^ (2 * k)))) * (t * (C * x ^ (2 * (k * (N + 1))))) := by
                refine mul_le_mul hL (h2.trans (mul_le_mul_of_nonneg_left hf ht0.le)) h1
                  (exp_pos _).le
            _ = t * C * (y / (t * c)) ^ (N + 1) * Real.exp (-y) := by
                rw [hpow, hexp]
                ring
            _ = C * c⁻¹ ^ (N + 1) * (y ^ (N + 1) * Real.exp (-y)) / t ^ N := by
                rw [div_pow, mul_pow, inv_pow]
                field_simp
                ring
            _ ≤ C * c⁻¹ ^ (N + 1) * ((N + 1).factorial : ℝ) / t ^ N := by
                gcongr
            _ ≤ A / t ^ N := by
                rw [hA_def]
                gcongr
                linarith
        · -- away from `0`
          have hL : Real.exp (-(t * L₁ x)) ≤ Real.exp (-(t * c₂)) :=
            Real.exp_le_exp.mpr (neg_le_neg
              (mul_le_mul_of_nonneg_left (hfloor x (not_le.mp hxδ)) ht0.le))
          calc Real.exp (-(t * L₁ x)) * (1 - Real.exp (-(t * f x)))
              ≤ Real.exp (-(t * c₂)) * (t * M) := by
                refine mul_le_mul hL (h2.trans (mul_le_mul_of_nonneg_left (hf_bdd x) ht0.le)) h1
                  (exp_pos _).le
            _ = M * (t * Real.exp (-(t * c₂))) := by ring
            _ ≤ M * (1 / t ^ N) := mul_le_mul_of_nonneg_left hfarN hM0
            _ ≤ A / t ^ N := by
                rw [hA_def, mul_one_div]
                gcongr
                exact le_add_of_nonneg_left (mul_nonneg (mul_nonneg hC
                  (pow_nonneg (inv_nonneg.mpr hc.le) _)) (Nat.cast_nonneg _))
      calc |φ x| * (Real.exp (-(t * L₁ x)) * (1 - Real.exp (-(t * f x))))
          ≤ Mφ * (A / t ^ N) :=
            mul_le_mul (hMφ x) hcore (mul_nonneg (exp_pos _).le h1) hMφ0
        _ = Mφ * A / t ^ N := by ring
    · rw [Set.indicator_of_notMem hx, image_eq_zero_of_notMem_tsupport hx, zero_mul, norm_zero]
  -- integrate the bound
  have hint₁ : Integrable fun x ↦ φ x * Real.exp (-(t * L₁ x)) :=
    (hφ_c.mul (by fun_prop)).integrable_of_hasCompactSupport hφ_s.mul_right
  have hint₂ : Integrable fun x ↦ φ x * Real.exp (-(t * (L₁ x + f x))) :=
    (hφ_c.mul (by fun_prop)).integrable_of_hasCompactSupport hφ_s.mul_right
  have hg : Integrable fun x ↦ (tsupport φ).indicator (fun _ ↦ Mφ * A / t ^ N) x :=
    (integrable_indicator_iff hK.measurableSet).mpr (integrableOn_const hK.measure_lt_top.ne)
  rw [← integral_sub hint₁ hint₂]
  have h := norm_integral_le_of_norm_le
    (f := fun x ↦ φ x * Real.exp (-(t * L₁ x)) - φ x * Real.exp (-(t * (L₁ x + f x)))) hg
    (Filter.Eventually.of_forall fun x ↦ by
      rw [← mul_sub]
      exact hpt x)
  rw [integral_indicator_const _ hK.measurableSet, smul_eq_mul, Real.norm_eq_abs] at h
  calc _ ≤ K₁ * (Mφ * A / t ^ N) := h
    _ = K₁ * (Mφ * A) / t ^ N := by ring

/-- The singular flat-perturbation difference decays superpolynomially. -/
theorem singular_flat_perturbation_superpolynomial {k : ℕ} {L₁ f φ : ℝ → ℝ}
    {c c₁ δ₀ M : ℝ} (hc : 0 < c) (hc₁ : 0 < c₁) (hδ₀ : 0 < δ₀) (hL_c : Continuous L₁)
    (hlow : ∀ x, |x| ≤ δ₀ → c * x ^ (2 * k) ≤ L₁ x) (hfar : ∀ x, δ₀ < |x| → c₁ ≤ L₁ x)
    (hf_c : Continuous f) (hf0 : ∀ x, 0 ≤ f x) (hf_bdd : ∀ x, f x ≤ M)
    (hflat : ∀ n : ℕ, ∃ C δ : ℝ, 0 ≤ C ∧ 0 < δ ∧ ∀ x : ℝ, |x| ≤ δ → f x ≤ C * x ^ (2 * n))
    (hφ_c : Continuous φ) (hφ_s : HasCompactSupport φ) :
    ∀ N : ℕ,
      (fun t : ℝ ↦ (∫ x : ℝ, φ x * Real.exp (-(t * L₁ x))) -
        ∫ x : ℝ, φ x * Real.exp (-(t * (L₁ x + f x)))) =o[Filter.atTop]
      fun t : ℝ ↦ t ^ (-(N : ℝ)) := by
  intro N
  obtain ⟨K, T, hK, hT, hbound⟩ := singular_flat_perturbation_invisible hc hc₁ hδ₀ hL_c hlow
    hfar hf_c hf0 hf_bdd hflat hφ_c hφ_s (N + 1)
  have h1 : (fun t : ℝ ↦ (∫ x : ℝ, φ x * Real.exp (-(t * L₁ x))) -
      ∫ x : ℝ, φ x * Real.exp (-(t * (L₁ x + f x)))) =O[Filter.atTop]
      fun t : ℝ ↦ t ^ (-((N : ℝ) + 1)) := by
    rw [Asymptotics.isBigO_iff]
    refine ⟨K, ?_⟩
    filter_upwards [Filter.eventually_ge_atTop T,
      Filter.eventually_ge_atTop (1 : ℝ)] with t htT ht1
    have ht0 : (0 : ℝ) < t := lt_of_lt_of_le one_pos ht1
    have hrw : K / t ^ (N + 1) = K * ‖t ^ (-((N : ℝ) + 1))‖ := by
      rw [Real.norm_of_nonneg (Real.rpow_nonneg ht0.le _),
        Real.rpow_neg ht0.le,
        show ((N : ℝ) + 1) = (((N + 1 : ℕ) : ℕ) : ℝ) by push_cast; rfl,
        Real.rpow_natCast, div_eq_mul_inv]
    exact le_of_le_of_eq (hbound t htT) hrw
  have h2 : (fun t : ℝ ↦ t ^ (-((N : ℝ) + 1))) =o[Filter.atTop]
      fun t : ℝ ↦ t ^ (-(N : ℝ)) := by
    refine (Asymptotics.isLittleO_iff_tendsto' ?_).mpr ?_
    · filter_upwards [Filter.eventually_gt_atTop (0 : ℝ)] with t ht h0
      exact absurd h0 (Real.rpow_pos_of_pos ht _).ne'
    · have hratio : ∀ᶠ t : ℝ in Filter.atTop,
          t ^ (-((N : ℝ) + 1)) / t ^ (-(N : ℝ)) = t⁻¹ := by
        filter_upwards [Filter.eventually_gt_atTop (0 : ℝ)] with t ht
        rw [← Real.rpow_sub ht, show -((N : ℝ) + 1) - -(N : ℝ) = -1 by ring, Real.rpow_neg_one]
      rw [Filter.tendsto_congr' hratio]
      exact tendsto_inv_atTop_zero
  exact h1.trans_isLittleO h2

/-- **The singular witness.** For every `k` (`k ≥ 1` for a singular minimum), the losses `x^{2k}` and `x^{2k} + e^{-1/x²}`
have the same singular minimum of order `2k` at `0`, different germs, and unnormalised Laplace
families that agree beyond all orders against every continuous compactly supported observable. -/
theorem singular_flat_witness_superpolynomial (k : ℕ) {φ : ℝ → ℝ}
    (hφ_c : Continuous φ) (hφ_s : HasCompactSupport φ) :
    ∀ N : ℕ,
      (fun t : ℝ ↦ (∫ x : ℝ, φ x * Real.exp (-(t * x ^ (2 * k)))) -
        ∫ x : ℝ, φ x * Real.exp (-(t * (x ^ (2 * k) + flatWitness x))))
        =o[Filter.atTop] fun t : ℝ ↦ t ^ (-(N : ℝ)) :=
  singular_flat_perturbation_superpolynomial (c := 1) (c₁ := 1) (δ₀ := 1) one_pos one_pos
    one_pos (by fun_prop) (fun x _ ↦ by rw [one_mul]) (fun x hx ↦ by
      rw [← Even.pow_abs (even_two_mul k)]
      exact one_le_pow₀ hx.le)
    flatWitness_continuous flatWitness_nonneg flatWitness_le_one flatWitness_flat hφ_c hφ_s

end Laplace.OneD
