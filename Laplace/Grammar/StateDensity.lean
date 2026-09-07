/-
Copyright (c) 2026 Timaeus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Laplace.Grammar.PowLogCalculus
import Laplace.Grammar.MonomialBoxBridge
import Laplace.Grammar.ProductDensityHelpers

/-!
# The exact state density of a monomial on the unit box

Unit 224 (Taylor-tree programme, Stage 1b). For weights `w : Fin (n+1) → ℝ` the weighted box
integral `∫_{(0,1]^{n+1}} ∏ aᵢ^{wᵢ} g(∏ aᵢ) da` (`weightedBoxIntegral`) equals `∫₀¹ v(z) g(z) dz`
for an **explicit power–log density** `v = eval (stateDensityRep n w)`
(`weightedBoxIntegral_eq_stateDensity`), for every measurable `g : ℝ → ℝ≥0∞`. The representation is
built by the one-coordinate convolution calculus of unit 223: one coordinate has density `a^{w₀}`,
and each further coordinate acts by `PowLogRep.conv`. Consequently (`stateDensityRep_exponent_mem`,
`stateDensityRep_degree_lt`) every term `c · z^{μ-1} (-log z)^j` of the density has `μ = wᵢ + 1` for
some coordinate and `j` strictly less than the number of coordinates with that value: the exact
multivariate state density `v(τ) = ∑_{μ} ∑_{j < r(μ)} c_{μ,j} τ^{μ-1} (-log τ)^j` of the paper, on
`(0,1]`, without any Mellin inversion. Through the coordinatewise power substitution
(`monomialBoxIntegral_eq_weighted`) this is the state density of the monomial `u^h` under
`τ = u^{2k}`: `μ = (hᵢ+1)/(2kᵢ)` (`monomialBoxIntegral_eq_stateDensity`). Zero `sorry`/`axiom`.
-/

open MeasureTheory Set Real

namespace Laplace.Grammar

/-- The state-density representation for weights `w` on `n+1` coordinates. -/
noncomputable def stateDensityRep : (n : ℕ) → (Fin (n + 1) → ℝ) → PowLogRep
  | 0, w => [(w 0 + 1, 0, 1)]
  | n + 1, w => PowLogRep.conv (w 0) (stateDensityRep n (Fin.tail w))

theorem stateDensityRep_zero (w : Fin 1 → ℝ) : stateDensityRep 0 w = [(w 0 + 1, 0, 1)] := rfl

theorem stateDensityRep_succ (n : ℕ) (w : Fin (n + 2) → ℝ) :
    stateDensityRep (n + 1) w = PowLogRep.conv (w 0) (stateDensityRep n (Fin.tail w)) := rfl

theorem div_mem_Ioc_of_mem_Icc {z t : ℝ} (hz : 0 < z) (ht : t ∈ Icc z 1) :
    z / t ∈ Ioc (0 : ℝ) 1 := by
  have ht0 : 0 < t := hz.trans_le ht.1
  exact ⟨div_pos hz ht0, (div_le_one ht0).2 ht.1⟩

theorem measurable_powLogBasis (μ : ℝ) (j : ℕ) : Measurable (powLogBasis μ j) := by
  unfold powLogBasis
  exact (measurable_id.pow_const _).mul (Real.measurable_log.neg.pow_const _)

theorem PowLogRep.measurable_eval (c : PowLogRep) : Measurable (PowLogRep.eval c) := by
  induction c with
  | nil =>
    have : PowLogRep.eval ([] : PowLogRep) = fun _ => 0 := rfl
    rw [this]
    exact measurable_const
  | cons t c ih =>
    have : PowLogRep.eval (t :: c) =
        fun τ => t.2.2 * powLogBasis t.1 t.2.1 τ + PowLogRep.eval c τ := rfl
    rw [this]
    exact (measurable_const.mul (measurable_powLogBasis _ _)).add ih

/-- The density is nonnegative on `(0,1]`. -/
theorem stateDensityRep_nonneg : ∀ (n : ℕ) (w : Fin (n + 1) → ℝ), ∀ z ∈ Ioc (0 : ℝ) 1,
    0 ≤ PowLogRep.eval (stateDensityRep n w) z := by
  intro n
  induction n with
  | zero =>
    intro w z hz
    simp only [stateDensityRep_zero, PowLogRep.eval_cons, PowLogRep.eval_nil, powLogBasis,
      pow_zero, mul_one, one_mul, add_zero]
    exact Real.rpow_nonneg hz.1.le _
  | succ n ih =>
    intro w z hz
    rw [stateDensityRep_succ, PowLogRep.eval_conv _ _ hz.1 hz.2]
    unfold powLogConv
    refine setIntegral_nonneg measurableSet_Icc fun t ht => ?_
    exact mul_nonneg (Real.rpow_nonneg (hz.1.trans_le ht.1).le _)
      (ih (Fin.tail w) _ (div_mem_Ioc_of_mem_Icc hz.1 ht))

/-- **Exact state density**: `∫_{(0,1]^{n+1}} ∏ aᵢ^{wᵢ} g(∏ aᵢ) = ∫₀¹ v(z) g(z) dz` with
`v = eval (stateDensityRep n w)`. -/
theorem weightedBoxIntegral_eq_stateDensity :
    ∀ (n : ℕ) (w : Fin (n + 1) → ℝ) (g : ℝ → ENNReal), Measurable g →
      weightedBoxIntegral (n + 1) w g =
        ∫⁻ z in Ioc (0 : ℝ) 1, ENNReal.ofReal (PowLogRep.eval (stateDensityRep n w) z) * g z := by
  intro n
  induction n with
  | zero =>
    intro w g hg
    rw [weightedBoxIntegral_succ 0 w g hg]
    refine setLIntegral_congr_fun measurableSet_Ioc fun a _ => ?_
    rw [weightedBoxIntegral_zero, mul_one]
    simp only [stateDensityRep_zero, PowLogRep.eval_cons, PowLogRep.eval_nil, powLogBasis,
      pow_zero, mul_one, one_mul, add_zero, add_sub_cancel_right]
  | succ n ih =>
    intro w g hg
    set v := PowLogRep.eval (stateDensityRep n (Fin.tail w)) with hv
    have hvnn : ∀ z ∈ Ioc (0 : ℝ) 1, 0 ≤ v z := stateDensityRep_nonneg n (Fin.tail w)
    have hvm : Measurable v := PowLogRep.measurable_eval _
    rw [weightedBoxIntegral_succ (n + 1) w g hg]
    have hinner : ∀ a : ℝ, weightedBoxIntegral (n + 1) (Fin.tail w) (fun z => g (a * z)) =
        ∫⁻ z in Ioc (0 : ℝ) 1, ENNReal.ofReal (v z) * g (a * z) := fun a =>
      ih (Fin.tail w) _ (hg.comp (measurable_const.mul measurable_id))
    simp_rw [hinner]
    -- the outer integrand as a triangle integral
    have hstep : ∀ a ∈ Ioc (0 : ℝ) 1,
        ENNReal.ofReal (a ^ w 0) * ∫⁻ z in Ioc (0 : ℝ) 1, ENNReal.ofReal (v z) * g (a * z) =
          ∫⁻ u in Ioc (0 : ℝ) a, ENNReal.ofReal (a ^ (w 0 - 1) * v (u / a)) * g u := by
      intro a ha
      have ha0 : 0 < a := ha.1
      have hsub : ∫⁻ z in Ioc (0 : ℝ) 1, ENNReal.ofReal (v z) * g (a * z) =
          ENNReal.ofReal (1 / a) * ∫⁻ u in Ioc (0 : ℝ) a, ENNReal.ofReal (v (u / a)) * g u := by
        rw [← lintegral_Ioc_scale a ha0 (fun u => ENNReal.ofReal (v (u / a)) * g u)]
        refine setLIntegral_congr_fun measurableSet_Ioc fun z _ => ?_
        rw [mul_div_cancel_left₀ z ha0.ne']
      rw [hsub, ← mul_assoc, ← ENNReal.ofReal_mul (Real.rpow_nonneg ha0.le _),
        ← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
      refine setLIntegral_congr_fun measurableSet_Ioc fun u hu => ?_
      have hua : u / a ∈ Ioc (0 : ℝ) 1 := ⟨div_pos hu.1 ha0, (div_le_one ha0).2 hu.2⟩
      rw [← mul_assoc, ← ENNReal.ofReal_mul (by positivity), Real.rpow_sub_one ha0.ne', one_div,
        div_eq_mul_inv (a ^ w 0) a]
    rw [setLIntegral_congr_fun measurableSet_Ioc hstep]
    have hmeas : Measurable fun q : ℝ × ℝ =>
        ENNReal.ofReal (q.1 ^ (w 0 - 1) * v (q.2 / q.1)) * g q.2 :=
      (ENNReal.measurable_ofReal.comp ((measurable_fst.pow_const _).mul
        (hvm.comp (measurable_snd.div measurable_fst)))).mul (hg.comp measurable_snd)
    rw [lintegral_triangle_swap (fun a u => ENNReal.ofReal (a ^ (w 0 - 1) * v (u / a)) * g u)
      hmeas]
    refine setLIntegral_congr_fun measurableSet_Ioc fun u hu => ?_
    have hmeas' : Measurable fun a : ℝ => ENNReal.ofReal (a ^ (w 0 - 1) * v (u / a)) :=
      ENNReal.measurable_ofReal.comp ((measurable_id.pow_const _).mul
        (hvm.comp (measurable_const.div measurable_id)))
    rw [lintegral_mul_const _ hmeas', ← ofReal_integral_eq_lintegral_ofReal
      (integrableOn_kernel_eval (w 0) _ hu.1)
      (ae_restrict_of_forall_mem measurableSet_Icc fun a ha => mul_nonneg
        (Real.rpow_nonneg (hu.1.trans_le ha.1).le _) (hvnn _ (div_mem_Ioc_of_mem_Icc hu.1 ha)))]
    rw [stateDensityRep_succ, PowLogRep.eval_conv _ _ hu.1 hu.2]
    rfl

/-- **Monomial form**: `∫_{(0,1]^{n+1}} u^h g(u^{2k}) du = ∏ 1/(2kᵢ) ∫₀¹ v(z) g(z) dz` with the state
density of weights `(hᵢ+1)/(2kᵢ) - 1`. -/
theorem monomialBoxIntegral_eq_stateDensity (n : ℕ) (h k : Fin (n + 1) → ℕ) (hk : ∀ i, 0 < k i)
    (g : ℝ → ENNReal) (hg : Measurable g) :
    monomialBoxIntegral (n + 1) h k g =
      ENNReal.ofReal (∏ i, 1 / (2 * (k i : ℝ))) *
        ∫⁻ z in Ioc (0 : ℝ) 1, ENNReal.ofReal (PowLogRep.eval
          (stateDensityRep n fun i => ((h i : ℝ) + 1) / (2 * (k i : ℝ)) - 1) z) * g z := by
  rw [monomialBoxIntegral_eq_weighted (n + 1) h k hk g hg,
    weightedBoxIntegral_eq_stateDensity n _ g hg]

/-! ### Exponents and logarithmic degrees -/

/-- Every exponent of the density is `wᵢ + 1` for some coordinate. -/
theorem stateDensityRep_exponent_mem : ∀ (n : ℕ) (w : Fin (n + 1) → ℝ),
    ∀ t ∈ stateDensityRep n w, ∃ i, t.1 = w i + 1 := by
  intro n
  induction n with
  | zero =>
    intro w t ht
    simp only [stateDensityRep_zero, List.mem_singleton] at ht
    exact ⟨0, by rw [ht]⟩
  | succ n ih =>
    intro w t ht
    rw [stateDensityRep_succ] at ht
    have h := PowLogRep.conv_exponent_mem (w 0) (stateDensityRep n (Fin.tail w))
      (Set.range fun i => Fin.tail w i + 1) (fun t ht => by
        obtain ⟨i, hi⟩ := ih (Fin.tail w) t ht
        exact ⟨i, hi.symm⟩) t ht
    rcases h with h | ⟨i, hi⟩
    · exact ⟨0, h⟩
    · exact ⟨i.succ, hi.symm⟩

/-- The multiplicity of an exponent `μ`: the number of coordinates with `wᵢ + 1 = μ`. -/
noncomputable def expMult {n : ℕ} (w : Fin n → ℝ) (μ : ℝ) : ℕ :=
  (Finset.univ.filter fun i => w i + 1 = μ).card

theorem expMult_succ {n : ℕ} (w : Fin (n + 1) → ℝ) (μ : ℝ) :
    expMult w μ = expMult (Fin.tail w) μ + (if μ = w 0 + 1 then 1 else 0) := by
  unfold expMult
  rw [Finset.card_filter, Finset.card_filter, Fin.sum_univ_succ, add_comm]
  congr 1
  by_cases h : w 0 + 1 = μ
  · rw [if_pos h, if_pos h.symm]
  · rw [if_neg h, if_neg (Ne.symm h)]

/-- Every term `(μ, j, c)` of the density has `j < expMult w μ`. -/
theorem stateDensityRep_degree_lt : ∀ (n : ℕ) (w : Fin (n + 1) → ℝ),
    ∀ t ∈ stateDensityRep n w, t.2.1 < expMult w t.1 := by
  intro n
  induction n with
  | zero =>
    intro w t ht
    simp only [stateDensityRep_zero, List.mem_singleton] at ht
    subst ht
    simp only [expMult]
    rw [Finset.card_pos]
    exact ⟨0, by simp⟩
  | succ n ih =>
    intro w t ht
    rw [stateDensityRep_succ] at ht
    have h := PowLogRep.conv_degree_lt (w 0) (stateDensityRep n (Fin.tail w))
      (expMult (Fin.tail w)) (ih (Fin.tail w)) t ht
    rwa [expMult_succ]

end Laplace.Grammar
