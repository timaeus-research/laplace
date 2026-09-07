/-
Copyright (c) 2026 Timaeus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Laplace.Grammar.TwoDGenDensityUnequal
import Laplace.Grammar.AxisSeries

/-!
# The density expansion of a face term (grammar §4.2, higher-order `d = 2`)

For a one-variable amplitude `Ψ(u, s)` with `u`-Taylor data `f_m(s)` to order `M` and the weights
`u^{h₁} v^{h₂}` with `p₂ = (h₂+1)/k₂`, the density `genDensity` (unit 103) is, by the weighted
finite-part axis lemma (unit 100) with `γ = k₁p₂ − h₁ − 1 < M`,

  `ρ(r, s) = ∑_{m<M} r^{p₂ + (m−γ)/k₁ − 1} c_m(s) + r^{p₂−1} k₂⁻¹ FP_γ(Ψ(·,s))
             + r^{p₂−1} log(1/r) · (k₁k₂)⁻¹ f_γ(s) + O(r^{p₂ + (M−γ)/k₁ − 1} H(s))`,

with the logarithm present exactly when `γ` is an integer `< M` (a collision of exponents), and
`c_m` explicit (`faceCoeff`). This is packaged as a `DensityExpansion` (`faceDensity_expansion`)
indexed by `Fin M ⊕ Fin 2`, and transferred to the `N`-expansion of the face term
(`face_transfer_bound`). Zero `sorry`/`axiom`.
-/

open Real MeasureTheory Set Finset

namespace Laplace.Grammar

/-- The exponent `p₂ + (m − γ)/k₁` of the `m`-th monomial term. -/
noncomputable def faceExp (p₂ γ : ℝ) (k₁ : ℕ) (m : ℕ) : ℝ := p₂ + ((m : ℝ) - γ) / k₁

/-- The coefficient of the `m`-th monomial term: `(k₁k₂)⁻¹ log A · f_m` at the resonance,
`−k₂⁻¹ A^{-(m-γ)/k₁} f_m/(m−γ)` otherwise. -/
noncomputable def faceCoeff (γ A : ℝ) (k₁ k₂ : ℕ) (f : ℕ → ℝ → ℝ) (m : ℕ) (s : ℝ) : ℝ :=
  if (m : ℝ) = γ then 1 / ((k₁ : ℝ) * k₂) * Real.log A * f m s
  else -(1 / (k₂ : ℝ)) * A ^ (-(((m : ℝ) - γ) / k₁)) / ((m : ℝ) - γ) * f m s

/-- The coefficient of the logarithmic term: `(k₁k₂)⁻¹ f_γ` if `γ` is an integer `< M`, else `0`. -/
noncomputable def faceLogCoeff (γ : ℝ) (k₁ k₂ : ℕ) (f : ℕ → ℝ → ℝ) (M : ℕ) (s : ℝ) : ℝ :=
  ∑ m ∈ range M, if (m : ℝ) = γ then 1 / ((k₁ : ℝ) * k₂) * f m s else 0

/-- The finite-part coefficient `k₂⁻¹ FP_γ(Ψ(·, s))`. -/
noncomputable def faceFPCoeff (γ b : ℝ) (k₂ : ℕ) (Ψ : ℝ → ℝ → ℝ) (f : ℕ → ℝ → ℝ) (M : ℕ)
    (s : ℝ) : ℝ :=
  1 / (k₂ : ℝ) * axisFinitePart γ b (fun u => Ψ u s) (fun m => f m s) M

/-- The exponents of the face expansion, indexed by `Fin M ⊕ Fin 2`. -/
noncomputable def faceα (p₂ γ : ℝ) (k₁ M : ℕ) : Fin M ⊕ Fin 2 → ℝ :=
  Sum.elim (fun m => faceExp p₂ γ k₁ m) ![p₂, p₂]

/-- The log degrees of the face expansion. -/
def faceJ (M : ℕ) : Fin M ⊕ Fin 2 → ℕ := Sum.elim (fun _ => 0) ![0, 1]

/-- The coefficient functions of the face expansion. -/
noncomputable def faceC (γ b : ℝ) (k₁ k₂ : ℕ) (Ψ : ℝ → ℝ → ℝ) (f : ℕ → ℝ → ℝ) (M : ℕ) :
    Fin M ⊕ Fin 2 → ℝ → ℝ :=
  Sum.elim (fun m => faceCoeff γ (b ^ k₂) k₁ k₂ f m)
    ![faceFPCoeff γ b k₂ Ψ f M, faceLogCoeff γ k₁ k₂ f M]

/-- One monomial term of the axis expansion in the density variable. -/
theorem face_monomial_eq (p₂ γ b : ℝ) (k₁ k₂ : ℕ) (hb : 0 < b) (hk₁ : 0 < k₁) (f : ℕ → ℝ → ℝ)
    (m : ℕ) (r s : ℝ) (hr : 0 < r) :
    -(1 / (k₂ : ℝ)) * r ^ (p₂ - 1) * (f m s * axisPrim γ ((r / b ^ k₂) ^ ((k₁ : ℝ)⁻¹)) m)
      = r ^ (faceExp p₂ γ k₁ m - 1) * faceCoeff γ (b ^ k₂) k₁ k₂ f m s
        + r ^ (p₂ - 1) * Real.log (1 / r)
          * (if (m : ℝ) = γ then 1 / ((k₁ : ℝ) * k₂) * f m s else 0) := by
  have hA : 0 < b ^ k₂ := by positivity
  have hk₁' : (0 : ℝ) < k₁ := Nat.cast_pos.2 hk₁
  rw [← one_div, axisPrim_rpow γ (b ^ k₂) r k₁ m hA hr]
  unfold faceExp faceCoeff
  rw [one_div r, Real.log_inv]
  split_ifs with h
  · rw [h, sub_self, zero_div, add_zero]
    field_simp
    ring
  · have hmγ : (m : ℝ) - γ ≠ 0 := sub_ne_zero.2 h
    have hrA : (r / b ^ k₂) ^ (((m : ℝ) - γ) / k₁)
        = r ^ (((m : ℝ) - γ) / k₁) * (b ^ k₂) ^ (-(((m : ℝ) - γ) / k₁)) := by
      rw [Real.div_rpow hr.le hA.le, Real.rpow_neg hA.le, div_eq_mul_inv]
    rw [hrA, show p₂ + ((m : ℝ) - γ) / k₁ - 1 = (p₂ - 1) + ((m : ℝ) - γ) / k₁ by ring,
      Real.rpow_add hr, mul_zero, add_zero]
    ring

/-- The local expression of the axis expansion equals the sum of the indexed terms. -/
theorem face_terms_eq (p₂ γ b : ℝ) (k₁ k₂ : ℕ) (hb : 0 < b) (hk₁ : 0 < k₁) (Ψ : ℝ → ℝ → ℝ)
    (f : ℕ → ℝ → ℝ) (M : ℕ) (r s : ℝ) (hr : 0 < r) :
    1 / (k₂ : ℝ) * r ^ (p₂ - 1)
        * (axisFinitePart γ b (fun u => Ψ u s) (fun m => f m s) M
          - ∑ m ∈ range M, f m s * axisPrim γ ((r / b ^ k₂) ^ ((k₁ : ℝ)⁻¹)) m)
      = ∑ i, r ^ (faceα p₂ γ k₁ M i - 1) * Real.log (1 / r) ^ faceJ M i
          * faceC γ b k₁ k₂ Ψ f M i s := by
  rw [Fintype.sum_sum_type, Fin.sum_univ_two]
  simp only [faceα, faceJ, faceC, Sum.elim_inl, Sum.elim_inr, Matrix.cons_val_zero,
    Matrix.cons_val_one, pow_zero, pow_one, mul_one]
  unfold faceFPCoeff faceLogCoeff
  have hS : (∑ m : Fin M, r ^ (faceExp p₂ γ k₁ m - 1) * faceCoeff γ (b ^ k₂) k₁ k₂ f m s)
      + ∑ m ∈ range M, r ^ (p₂ - 1) * Real.log (1 / r)
          * (if (m : ℝ) = γ then 1 / ((k₁ : ℝ) * k₂) * f m s else 0)
      = -(1 / (k₂ : ℝ) * r ^ (p₂ - 1)
          * ∑ m ∈ range M, f m s * axisPrim γ ((r / b ^ k₂) ^ ((k₁ : ℝ)⁻¹)) m) := by
    rw [Fin.sum_univ_eq_sum_range
      (fun m => r ^ (faceExp p₂ γ k₁ m - 1) * faceCoeff γ (b ^ k₂) k₁ k₂ f m s) M,
      ← Finset.sum_add_distrib, Finset.mul_sum, ← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun m _ => ?_
    rw [← face_monomial_eq p₂ γ b k₁ k₂ hb hk₁ f m r s hr]
    ring
  rw [Finset.mul_sum]
  linear_combination (-1 : ℝ) * hS

/-- Measurability of `genDensity` in `(r, s)`. -/
theorem genDensity_measurable (p₂ b : ℝ) (h₁ k₁ k₂ : ℕ) (Ψ : ℝ → ℝ → ℝ)
    (hΨc : Continuous (Function.uncurry Ψ)) :
    Measurable (Function.uncurry (genDensity p₂ b h₁ k₁ k₂ Ψ)) := by
  set F : (ℝ × ℝ) × ℝ → ℝ := fun w =>
    if (w.1.1 / b ^ k₂) ^ ((k₁ : ℝ)⁻¹) ≤ w.2 ∧ w.2 ≤ b then
      w.2 ^ ((h₁ : ℝ) - k₁ * p₂) * Ψ w.2 w.1.2 else 0 with hF
  have hFm : Measurable F := by
    refine Measurable.ite ?_ ?_ measurable_const
    · exact (measurableSet_le (((measurable_fst.comp measurable_fst).div_const _).pow_const _)
        measurable_snd).inter (measurableSet_le measurable_snd measurable_const)
    · exact (measurable_snd.pow_const _).mul (hΨc.measurable.comp
        (measurable_snd.prodMk (measurable_snd.comp measurable_fst)))
  have heq : (fun z : ℝ × ℝ => ∫ u in Icc ((z.1 / b ^ k₂) ^ ((k₁ : ℝ)⁻¹)) b,
      u ^ ((h₁ : ℝ) - k₁ * p₂) * Ψ u z.2) = fun z => ∫ u, F (z, u) := by
    funext z
    rw [← integral_indicator (μ := (volume : Measure ℝ))
      (f := fun u : ℝ => u ^ ((h₁ : ℝ) - k₁ * p₂) * Ψ u z.2) measurableSet_Icc]
    refine integral_congr_ae (Filter.Eventually.of_forall fun u => ?_)
    simp only [hF, indicator_apply, Set.mem_Icc]
  have hI : Measurable fun z : ℝ × ℝ => ∫ u in Icc ((z.1 / b ^ k₂) ^ ((k₁ : ℝ)⁻¹)) b,
      u ^ ((h₁ : ℝ) - k₁ * p₂) * Ψ u z.2 := by
    rw [heq]
    exact (StronglyMeasurable.integral_prod_right' (ν := (volume : Measure ℝ))
      hFm.stronglyMeasurable).measurable
  exact ((measurable_const.mul (measurable_fst.pow_const _)).mul hI)

/-- Measurability of the finite-part coefficient in `s`. -/
theorem faceFPCoeff_measurable (γ b : ℝ) (k₂ : ℕ) (Ψ : ℝ → ℝ → ℝ)
    (hΨc : Continuous (Function.uncurry Ψ)) (f : ℕ → ℝ → ℝ) (hf : ∀ m, Measurable (f m))
    (M : ℕ) : Measurable (faceFPCoeff γ b k₂ Ψ f M) := by
  unfold faceFPCoeff axisFinitePart regAxisIntegral taylorRem
  refine measurable_const.mul (Measurable.add ?_ ?_)
  · set F : ℝ × ℝ → ℝ := fun w =>
      w.2 ^ (-1 - γ) * (Ψ w.2 w.1 - ∑ m ∈ range M, f m w.1 * w.2 ^ m) with hF
    have hFm : Measurable F :=
      (measurable_snd.pow_const _).mul
        ((hΨc.measurable.comp (measurable_snd.prodMk measurable_fst)).sub
          (Finset.measurable_sum _ fun m _ => ((hf m).comp measurable_fst).mul
            (measurable_snd.pow_const m)))
    have : (fun s => ∫ u in Ioc (0 : ℝ) b,
        u ^ (-1 - γ) * (Ψ u s - ∑ m ∈ range M, f m s * u ^ m))
        = fun s => ∫ u, F (s, u) ∂((volume : Measure ℝ).restrict (Ioc 0 b)) := by
      funext s; rfl
    rw [this]
    exact (StronglyMeasurable.integral_prod_right'
      (ν := (volume : Measure ℝ).restrict (Ioc 0 b)) hFm.stronglyMeasurable).measurable
  · exact Finset.measurable_sum _ fun m _ => (hf m).mul_const _

theorem faceC_measurable (γ b : ℝ) (k₁ k₂ : ℕ) (Ψ : ℝ → ℝ → ℝ)
    (hΨc : Continuous (Function.uncurry Ψ)) (f : ℕ → ℝ → ℝ) (hf : ∀ m, Measurable (f m))
    (M : ℕ) : ∀ i, Measurable (faceC γ b k₁ k₂ Ψ f M i) := by
  intro i
  rcases i with m | i
  · simp only [faceC, Sum.elim_inl]
    unfold faceCoeff
    split_ifs
    · exact (hf m).const_mul _
    · exact (hf m).const_mul _
  · fin_cases i
    · simpa [faceC] using faceFPCoeff_measurable γ b k₂ Ψ hΨc f hf M
    · simp only [faceC, Sum.elim_inr, Fin.mk_one, Matrix.cons_val_one, Matrix.cons_val_zero]
      unfold faceLogCoeff
      refine Finset.measurable_sum _ fun m _ => ?_
      split_ifs
      · exact (hf m).const_mul _
      · exact measurable_const

/-- The remainder envelope `k₂⁻¹ A^{-(M-γ)/k₁}/(M−γ) · H(s)`. -/
noncomputable def faceEnv (γ A : ℝ) (k₁ k₂ M : ℕ) (H : ℝ → ℝ) (s : ℝ) : ℝ :=
  1 / (k₂ : ℝ) * (A ^ (-(((M : ℝ) - γ) / k₁)) / ((M : ℝ) - γ)) * H s

/-- **The density expansion of a face term.** -/
theorem faceDensity_expansion (p₂ b : ℝ) (h₁ k₁ k₂ M : ℕ) (hb : 0 < b) (hk₁ : 0 < k₁)
    (Ψ : ℝ → ℝ → ℝ) (hΨc : Continuous (Function.uncurry Ψ)) (f : ℕ → ℝ → ℝ)
    (hf : ∀ m, Measurable (f m)) (H : ℝ → ℝ) (hH : Measurable H) (hH0 : ∀ s, 0 ≤ H s)
    (hγ : (k₁ : ℝ) * p₂ - h₁ - 1 < M)
    (hrem : ∀ s, 0 < s → ∀ u ∈ Ioc (0 : ℝ) b,
      |Ψ u s - ∑ m ∈ range M, f m s * u ^ m| ≤ H s * u ^ M) :
    DensityExpansion (genDensity p₂ b h₁ k₁ k₂ Ψ)
      (faceα p₂ ((k₁ : ℝ) * p₂ - h₁ - 1) k₁ M) (faceJ M)
      (faceC ((k₁ : ℝ) * p₂ - h₁ - 1) b k₁ k₂ Ψ f M)
      (p₂ + ((M : ℝ) - ((k₁ : ℝ) * p₂ - h₁ - 1)) / k₁) (b ^ (k₁ + k₂)) 1
      (faceEnv ((k₁ : ℝ) * p₂ - h₁ - 1) (b ^ k₂) k₁ k₂ M H) := by
  set γ : ℝ := (k₁ : ℝ) * p₂ - h₁ - 1 with hγdef
  have hk₁' : (0 : ℝ) < k₁ := Nat.cast_pos.2 hk₁
  have hMγ : 0 < (M : ℝ) - γ := by linarith
  have hA : 0 < b ^ k₂ := by positivity
  have hq : 0 < ((M : ℝ) - γ) / k₁ := by positivity
  have henv0 : 0 ≤ 1 / (k₂ : ℝ) * ((b ^ k₂) ^ (-(((M : ℝ) - γ) / k₁)) / ((M : ℝ) - γ)) := by
    have := Real.rpow_nonneg hA.le (-(((M : ℝ) - γ) / k₁))
    positivity
  refine ⟨by positivity, ?_, ?_, genDensity_measurable p₂ b h₁ k₁ k₂ Ψ hΨc,
    faceC_measurable γ b k₁ k₂ Ψ hΨc f hf M, ?_, fun s => mul_nonneg henv0 (hH0 s), ?_⟩
  · -- exponents below the remainder exponent
    intro i
    rcases i with m | i
    · simp only [faceα, Sum.elim_inl, faceExp]
      have hm : (m : ℝ) < M := by exact_mod_cast m.isLt
      have : ((m : ℝ) - γ) / k₁ < ((M : ℝ) - γ) / k₁ := by
        rw [div_lt_div_iff_of_pos_right hk₁']; linarith
      linarith
    · fin_cases i <;> simp [faceα] <;> linarith
  · intro i
    rcases i with m | i
    · simp [faceJ]
    · fin_cases i <;> simp [faceJ]
  · unfold faceEnv
    exact measurable_const.mul hH
  · -- the remainder bound
    intro r hr s hs
    have hr0 : 0 < r := hr.1
    set ε : ℝ := (r / b ^ k₂) ^ ((k₁ : ℝ)⁻¹) with hε
    have hε0 : 0 < ε := Real.rpow_pos_of_pos (div_pos hr0 hA) _
    have hεb : ε ≤ b := by
      have : (r / b ^ k₂) ^ ((k₁ : ℝ)⁻¹) ≤ (b ^ k₁) ^ ((k₁ : ℝ)⁻¹) := by
        refine Real.rpow_le_rpow (div_pos hr0 hA).le ?_ (by positivity)
        rw [div_le_iff₀ hA, ← pow_add]; exact hr.2
      rwa [Real.pow_rpow_inv_natCast hb.le hk₁.ne'] at this
    have haxis := axis_finite_part_expansion γ b (H s) M hγ (fun u => Ψ u s) (fun m => f m s)
      (hΨc.measurable.comp (measurable_id.prodMk measurable_const))
      (fun u hu => by simpa [taylorRem] using hrem s hs u hu) ε hε0 hεb
    rw [← face_terms_eq p₂ γ b k₁ k₂ hb hk₁ Ψ f M r s hr0, genDensity_eq_axis]
    rw [show (-1 - ((k₁ : ℝ) * p₂ - h₁ - 1)) = -1 - γ by rw [hγdef], ← mul_sub, abs_mul,
      abs_of_nonneg (by positivity : 0 ≤ 1 / (k₂ : ℝ) * r ^ (p₂ - 1))]
    have hεpow : ε ^ ((M : ℝ) - γ)
        = r ^ (((M : ℝ) - γ) / k₁) * (b ^ k₂) ^ (-(((M : ℝ) - γ) / k₁)) := by
      rw [hε, ← one_div, rpow_one_div_rpow _ _ _ (div_pos hr0 hA).le, Real.div_rpow hr0.le hA.le,
        Real.rpow_neg hA.le, div_eq_mul_inv]
    have hlog : (1 : ℝ) ≤ (1 + |Real.log r|) ^ 1 := by
      rw [pow_one]; linarith [abs_nonneg (Real.log r)]
    calc 1 / (k₂ : ℝ) * r ^ (p₂ - 1)
          * |(∫ u in Ioc ε b, u ^ (-1 - γ) * Ψ u s)
            - (axisFinitePart γ b (fun u => Ψ u s) (fun m => f m s) M
              - ∑ m ∈ range M, f m s * axisPrim γ ε m)|
        ≤ 1 / (k₂ : ℝ) * r ^ (p₂ - 1) * (H s / ((M : ℝ) - γ) * ε ^ ((M : ℝ) - γ)) :=
          mul_le_mul_of_nonneg_left haxis (by positivity)
      _ = r ^ (p₂ + ((M : ℝ) - γ) / k₁ - 1) * 1 * faceEnv γ (b ^ k₂) k₁ k₂ M H s := by
          rw [hεpow, show p₂ + ((M : ℝ) - γ) / k₁ - 1 = (p₂ - 1) + ((M : ℝ) - γ) / k₁ by ring,
            Real.rpow_add hr0]
          unfold faceEnv
          ring
      _ ≤ _ := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hlog (by positivity))
          (mul_nonneg henv0 (hH0 s))

/-- **The `N`-expansion of a face term**: with `p₂ = (h₂+1)/k₂`, for `N ≥ 1`,
`|Z(N) − ∑ᵢ transferTerm_i(N)| ≤ N^{-a}(1 + log N)(M_H + ∑ᵢ R^{αᵢ-a} T_i)`, `a = p₂ + (M−γ)/k₁`. -/
theorem face_transfer_bound (β b p₂ : ℝ) (h₁ h₂ k₁ k₂ M : ℕ) (hβ : 0 ≤ β) (hb : 0 < b)
    (hk₁ : 0 < k₁) (hk₂ : 0 < k₂) (hp₂ : ((h₂ : ℝ) + 1) / k₂ = p₂)
    (Ψ : ℝ → ℝ → ℝ) (hΨc : Continuous (Function.uncurry Ψ)) (f : ℕ → ℝ → ℝ)
    (hf : ∀ m, Measurable (f m)) (H : ℝ → ℝ) (hH : Measurable H) (hH0 : ∀ s, 0 ≤ H s)
    (hγ : (k₁ : ℝ) * p₂ - h₁ - 1 < M)
    (hrem : ∀ s, 0 < s → ∀ u ∈ Ioc (0 : ℝ) b,
      |Ψ u s - ∑ m ∈ range M, f m s * u ^ m| ≤ H s * u ^ M)
    (hMc : ∀ i, IntegrableOn (fun s => s ^ (faceα p₂ ((k₁ : ℝ) * p₂ - h₁ - 1) k₁ M i - 1)
      * (1 + |Real.log s|) ^ faceJ M i
      * (Real.exp (-β * s ^ 2) * |faceC ((k₁ : ℝ) * p₂ - h₁ - 1) b k₁ k₂ Ψ f M i s|)) (Ioi 0))
    (hMt : ∀ i, IntegrableOn (fun s => s ^ (p₂ + ((M : ℝ) - ((k₁ : ℝ) * p₂ - h₁ - 1)) / k₁ - 1)
      * (1 + |Real.log s|) ^ faceJ M i
      * (Real.exp (-β * s ^ 2) * |faceC ((k₁ : ℝ) * p₂ - h₁ - 1) b k₁ k₂ Ψ f M i s|)) (Ioi 0))
    (hMH : IntegrableOn (fun s => s ^ (p₂ + ((M : ℝ) - ((k₁ : ℝ) * p₂ - h₁ - 1)) / k₁ - 1)
      * (1 + |Real.log s|) ^ 1
      * (Real.exp (-β * s ^ 2) * faceEnv ((k₁ : ℝ) * p₂ - h₁ - 1) (b ^ k₂) k₁ k₂ M H s)) (Ioi 0))
    (N : ℝ) (hN : 1 ≤ N) :
    |twoDAmp β b N h₁ h₂ k₁ k₂ (fun u _ s => Ψ u s)
        - ∑ i, transferTerm β (faceα p₂ ((k₁ : ℝ) * p₂ - h₁ - 1) k₁ M i) (faceJ M i)
            (faceC ((k₁ : ℝ) * p₂ - h₁ - 1) b k₁ k₂ Ψ f M i) N|
      ≤ N ^ (-(p₂ + ((M : ℝ) - ((k₁ : ℝ) * p₂ - h₁ - 1)) / k₁)) * (1 + Real.log N) ^ 1
        * (envMoment β (p₂ + ((M : ℝ) - ((k₁ : ℝ) * p₂ - h₁ - 1)) / k₁) 1
            (faceEnv ((k₁ : ℝ) * p₂ - h₁ - 1) (b ^ k₂) k₁ k₂ M H)
          + ∑ i, (b ^ (k₁ + k₂)) ^ (faceα p₂ ((k₁ : ℝ) * p₂ - h₁ - 1) k₁ M i
              - (p₂ + ((M : ℝ) - ((k₁ : ℝ) * p₂ - h₁ - 1)) / k₁))
            * tailMoment β (p₂ + ((M : ℝ) - ((k₁ : ℝ) * p₂ - h₁ - 1)) / k₁) (faceJ M i)
              (faceC ((k₁ : ℝ) * p₂ - h₁ - 1) b k₁ k₂ Ψ f M i)) := by
  rw [twoDAmp_uOnly_eq_transferZ' β b N p₂ h₁ h₂ k₁ k₂ hβ hb (by linarith) hk₁ hk₂ hp₂ Ψ hΨc]
  exact densityTransfer_bound
    (faceDensity_expansion p₂ b h₁ k₁ k₂ M hb hk₁ Ψ hΨc f hf H hH hH0 hγ hrem) β hMc hMt hMH N hN

/-- The transferred sum written out: monomial terms `N^{-α_m} M₀(c_m)`, the finite-part term
`N^{-p₂} M₀(k₂⁻¹ FP)`, and the logarithmic term `N^{-p₂}(log N · M₀(c_log) − M₁(c_log))`. -/
theorem face_transfer_sum_eq (β p₂ γ b : ℝ) (k₁ k₂ M : ℕ) (Ψ : ℝ → ℝ → ℝ) (f : ℕ → ℝ → ℝ)
    (N : ℝ) :
    ∑ i, transferTerm β (faceα p₂ γ k₁ M i) (faceJ M i) (faceC γ b k₁ k₂ Ψ f M i) N
      = (∑ m : Fin M, N ^ (-(faceExp p₂ γ k₁ m))
          * logMoment β (faceExp p₂ γ k₁ m) 0 (faceCoeff γ (b ^ k₂) k₁ k₂ f m))
        + N ^ (-p₂) * logMoment β p₂ 0 (faceFPCoeff γ b k₂ Ψ f M)
        + N ^ (-p₂) * (Real.log N * logMoment β p₂ 0 (faceLogCoeff γ k₁ k₂ f M)
          - logMoment β p₂ 1 (faceLogCoeff γ k₁ k₂ f M)) := by
  rw [Fintype.sum_sum_type, Fin.sum_univ_two]
  simp only [faceα, faceJ, faceC, Sum.elim_inl, Sum.elim_inr, Matrix.cons_val_zero,
    Matrix.cons_val_one, transferTerm_zero, transferTerm_one]
  ring

end Laplace.Grammar
