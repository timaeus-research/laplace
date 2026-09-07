/-
Copyright (c) 2026 Daniel Murfet. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniel Murfet
-/
import Laplace.Grammar.MonomialBoxBridge
import Laplace.Grammar.GammaLogAsymptotic

/-!
# The equal-ratio monomial asymptotic in general dimension

Assembly of the general-`d` equal-ratio monomial milestone (Astra #14). For exponents
`h k : Fin (m+1) → ℕ` with `k i > 0` and the common ratio `(h i + 1)/(2 k i) = λ`, the monomial
box integral

  `I(N) = ∫_{(0,1]^{m+1}} ∏ xᵢ^{hᵢ} e^{-βN ∏ xᵢ^{2kᵢ}} dx`

is **exactly** `(∏ 1/(2kᵢ)) · (1/m!) · ∫₀¹ z^{λ-1} (-log z)^m e^{-βNz} dz`
(`monomialBoxIntegral_exp_eq`, `monomialBoxReal_eq`), and therefore

  `I(N) ~ Γ(λ) β^{-λ} / (m! ∏ᵢ 2kᵢ) · N^{-λ} (log N)^m`

(`monomialBoxReal_isEquivalent`, `monomialBoxReal_isEquivalent'`), with the logarithmic
multiplicity `d = m + 1` coming entirely from the product density of unit 172 and the constant
from the Gamma/log asymptotic of unit 173.
-/

open MeasureTheory Set Filter Topology Asymptotics

namespace Laplace.Grammar

/-- The exponential test function `z ↦ e^{-βNz}` as an `ℝ≥0∞`-valued function. -/
noncomputable def expKernel (β N : ℝ) (z : ℝ) : ENNReal := ENNReal.ofReal (Real.exp (-(β * N * z)))

theorem measurable_expKernel (β N : ℝ) : Measurable (expKernel β N) := by
  unfold expKernel
  fun_prop

/-- **Exact `ℝ≥0∞` reduction** of the equal-ratio monomial box integral to the Gamma/log
integral. -/
theorem monomialBoxIntegral_exp_eq (m : ℕ) (h k : Fin (m + 1) → ℕ) (hk : ∀ i, 0 < k i)
    (l β N : ℝ) (hl : 0 < l) (hratio : ∀ i, ((h i : ℝ) + 1) / (2 * (k i : ℝ)) = l)
    (hβN : 0 < β * N) :
    monomialBoxIntegral (m + 1) h k (expKernel β N) =
      ENNReal.ofReal ((∏ i, 1 / (2 * (k i : ℝ))) * (1 / (m.factorial : ℝ)) *
        gammaLogIntegral l m β N) := by
  have hP : 0 ≤ ∏ i : Fin (m + 1), 1 / (2 * (k i : ℝ)) :=
    Finset.prod_nonneg fun i _ => by positivity
  rw [monomialBoxIntegral_eq_weighted (m + 1) h k hk _ (measurable_expKernel β N)]
  have hw : (fun i : Fin (m + 1) => ((h i : ℝ) + 1) / (2 * (k i : ℝ)) - 1) = fun _ => l - 1 := by
    funext i
    rw [hratio i]
  rw [hw, weightedBoxIntegral_const_eq_productIntegral l (m + 1) _ (measurable_expKernel β N),
    productIntegral_succ_eq l m _ (measurable_expKernel β N)]
  simp only [expKernel]
  rw [lintegral_logDensity_mul_exp l m β N hl hβN,
    ENNReal.ofReal_mul (mul_nonneg hP (by positivity)), ENNReal.ofReal_mul hP, mul_assoc]

/-- The paper's monomial box integral
`I(N) = ∫_{(0,1]^d} ∏ xᵢ^{hᵢ} e^{-βN ∏ xᵢ^{2kᵢ}} dx` as a real Bochner integral. -/
noncomputable def monomialBoxReal (d : ℕ) (h k : Fin d → ℕ) (β N : ℝ) : ℝ :=
  ∫ x in unitBox d, (∏ i, x i ^ h i) * Real.exp (-(β * N * ∏ i, x i ^ (2 * k i)))

theorem monomialBox_integrand_nonneg (d : ℕ) (h k : Fin d → ℕ) (β N : ℝ) (x : Fin d → ℝ)
    (hx : x ∈ unitBox d) :
    0 ≤ (∏ i, x i ^ h i) * Real.exp (-(β * N * ∏ i, x i ^ (2 * k i))) :=
  mul_nonneg (Finset.prod_nonneg fun i _ => pow_nonneg (hx i (mem_univ i)).1.le _)
    (Real.exp_pos _).le

theorem monomialBoxReal_nonneg (d : ℕ) (h k : Fin d → ℕ) (β N : ℝ) :
    0 ≤ monomialBoxReal d h k β N :=
  setIntegral_nonneg (measurableSet_unitBox d) (monomialBox_integrand_nonneg d h k β N)

theorem monomialBox_integrableOn (d : ℕ) (h k : Fin d → ℕ) (β N : ℝ) :
    IntegrableOn (fun x : Fin d → ℝ => (∏ i, x i ^ h i) * Real.exp (-(β * N * ∏ i, x i ^ (2 * k i))))
      (unitBox d) := by
  have hcont : Continuous fun x : Fin d → ℝ =>
      (∏ i, x i ^ h i) * Real.exp (-(β * N * ∏ i, x i ^ (2 * k i))) :=
    (continuous_finsetProd _ fun i _ => (continuous_apply i).pow _).mul
      (Real.continuous_exp.comp (continuous_const.mul
        (continuous_finsetProd _ fun i _ => (continuous_apply i).pow _)).neg)
  have hcpt : IsCompact (Set.pi univ fun _ : Fin d => Icc (0 : ℝ) 1) :=
    isCompact_univ_pi fun _ => isCompact_Icc
  exact (hcont.continuousOn.integrableOn_compact hcpt).mono_set
    (pi_mono fun _ _ => Ioc_subset_Icc_self)

/-- The Bochner and `ℝ≥0∞` monomial box integrals agree. -/
theorem ofReal_monomialBoxReal (d : ℕ) (h k : Fin d → ℕ) (β N : ℝ) :
    ENNReal.ofReal (monomialBoxReal d h k β N) = monomialBoxIntegral d h k (expKernel β N) := by
  unfold monomialBoxReal monomialBoxIntegral
  rw [ofReal_integral_eq_lintegral_ofReal (monomialBox_integrableOn d h k β N)
    ((ae_restrict_iff' (measurableSet_unitBox d)).2
      (Eventually.of_forall (monomialBox_integrand_nonneg d h k β N)))]
  refine setLIntegral_congr_fun (measurableSet_unitBox d) fun x hx => ?_
  rw [ENNReal.ofReal_mul (Finset.prod_nonneg fun i _ => pow_nonneg (hx i (mem_univ i)).1.le _),
    ENNReal.ofReal_prod_of_nonneg fun i _ => pow_nonneg (hx i (mem_univ i)).1.le _]
  rfl

theorem gammaLogIntegral_nonneg (l : ℝ) (m : ℕ) (β N : ℝ) : 0 ≤ gammaLogIntegral l m β N :=
  setIntegral_nonneg measurableSet_Ioc fun z hz =>
    mul_nonneg (logDensity_nonneg l m z hz.1 hz.2) (Real.exp_pos _).le

/-- **Exact real reduction**: `I(N) = (∏ 1/(2kᵢ)) (1/m!) ∫₀¹ z^{λ-1} (-log z)^m e^{-βNz} dz`. -/
theorem monomialBoxReal_eq (m : ℕ) (h k : Fin (m + 1) → ℕ) (hk : ∀ i, 0 < k i) (l β N : ℝ)
    (hl : 0 < l) (hratio : ∀ i, ((h i : ℝ) + 1) / (2 * (k i : ℝ)) = l) (hβN : 0 < β * N) :
    monomialBoxReal (m + 1) h k β N =
      (∏ i, 1 / (2 * (k i : ℝ))) * (1 / (m.factorial : ℝ)) * gammaLogIntegral l m β N := by
  have hP : 0 ≤ ∏ i : Fin (m + 1), 1 / (2 * (k i : ℝ)) :=
    Finset.prod_nonneg fun i _ => by positivity
  refine (ENNReal.ofReal_eq_ofReal_iff (monomialBoxReal_nonneg _ h k β N)
    (mul_nonneg (mul_nonneg hP (by positivity)) (gammaLogIntegral_nonneg l m β N))).1 ?_
  rw [ofReal_monomialBoxReal, monomialBoxIntegral_exp_eq m h k hk l β N hl hratio hβN]

/-- **Equal-ratio monomial asymptotic (ratio form)**:
`I(N) / (N^{-λ} (log N)^m) → (∏ 1/(2kᵢ)) (1/m!) Γ(λ) β^{-λ}`. -/
theorem monomialBoxReal_tendsto (m : ℕ) (h k : Fin (m + 1) → ℕ) (hk : ∀ i, 0 < k i) (l β : ℝ)
    (hl : 0 < l) (hβ : 0 < β) (hratio : ∀ i, ((h i : ℝ) + 1) / (2 * (k i : ℝ)) = l) :
    Tendsto (fun N => monomialBoxReal (m + 1) h k β N / (N ^ (-l) * Real.log N ^ m)) atTop
      (𝓝 ((∏ i, 1 / (2 * (k i : ℝ))) * (1 / (m.factorial : ℝ)) * (Real.Gamma l * β ^ (-l)))) := by
  refine ((tendsto_gammaLogIntegral_div l m β hl hβ).const_mul _).congr' ?_
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with N hN
  rw [monomialBoxReal_eq m h k hk l β N hl hratio (mul_pos hβ hN), mul_div_assoc]

/-- **Equal-ratio monomial asymptotic (equivalence form)** against the `powLog` normal form. -/
theorem monomialBoxReal_isEquivalent (m : ℕ) (h k : Fin (m + 1) → ℕ) (hk : ∀ i, 0 < k i)
    (l β : ℝ) (hl : 0 < l) (hβ : 0 < β)
    (hratio : ∀ i, ((h i : ℝ) + 1) / (2 * (k i : ℝ)) = l) :
    (fun N => monomialBoxReal (m + 1) h k β N) ~[atTop]
      powLog ((∏ i, 1 / (2 * (k i : ℝ))) * (1 / (m.factorial : ℝ)) * (Real.Gamma l * β ^ (-l)))
        l m := by
  have hC : 0 < (∏ i : Fin (m + 1), 1 / (2 * (k i : ℝ))) * (1 / (m.factorial : ℝ)) *
      (Real.Gamma l * β ^ (-l)) := by
    have h1 : 0 < ∏ i : Fin (m + 1), 1 / (2 * (k i : ℝ)) :=
      Finset.prod_pos fun i _ => by have := hk i; positivity
    have h2 : 0 < Real.Gamma l * β ^ (-l) :=
      mul_pos (Real.Gamma_pos_of_pos hl) (Real.rpow_pos_of_pos hβ _)
    positivity
  refine isEquivalent_of_tendsto_one ?_
  have h := (monomialBoxReal_tendsto m h k hk l β hl hβ hratio).div_const
    ((∏ i, 1 / (2 * (k i : ℝ))) * (1 / (m.factorial : ℝ)) * (Real.Gamma l * β ^ (-l)))
  rw [div_self hC.ne'] at h
  refine h.congr' ?_
  filter_upwards [eventually_gt_atTop (1 : ℝ)] with N hN
  have hN0 : 0 < N := by linarith
  have hpow : N ^ (-l) ≠ 0 := (Real.rpow_pos_of_pos hN0 _).ne'
  have hlog : Real.log N ^ m ≠ 0 := pow_ne_zero _ (Real.log_pos hN).ne'
  simp only [Pi.div_apply, powLog]
  field_simp

/-- **Paper form**: `I_d(N) ~ Γ(λ) β^{-λ} / ((d-1)! ∏ᵢ 2kᵢ) · N^{-λ} (log N)^{d-1}` with `d = m+1`. -/
theorem monomialBoxReal_isEquivalent' (m : ℕ) (h k : Fin (m + 1) → ℕ) (hk : ∀ i, 0 < k i)
    (l β : ℝ) (hl : 0 < l) (hβ : 0 < β)
    (hratio : ∀ i, ((h i : ℝ) + 1) / (2 * (k i : ℝ)) = l) :
    (fun N => monomialBoxReal (m + 1) h k β N) ~[atTop]
      fun N => Real.Gamma l * β ^ (-l) / ((m.factorial : ℝ) * ∏ i, 2 * (k i : ℝ)) *
        N ^ (-l) * Real.log N ^ m := by
  refine (monomialBoxReal_isEquivalent m h k hk l β hl hβ hratio).congr_right
    (Eventually.of_forall fun N => ?_)
  have hprod : (∏ i : Fin (m + 1), 2 * (k i : ℝ)) ≠ 0 :=
    Finset.prod_ne_zero_iff.2 fun i _ => by have := hk i; positivity
  have hfact : (m.factorial : ℝ) ≠ 0 := by positivity
  have hinv : (∏ i : Fin (m + 1), 1 / (2 * (k i : ℝ))) = (∏ i : Fin (m + 1), 2 * (k i : ℝ))⁻¹ := by
    rw [← Finset.prod_inv_distrib]
    simp only [one_div]
  simp only [powLog]
  rw [hinv]
  field_simp

end Laplace.Grammar
