/-
Copyright (c) 2026 Daniel Murfet. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniel Murfet
-/
import Laplace.Grammar.SymmetricBox
import Laplace.Grammar.CutoffScaling
import Laplace.Grammar.LeadingTermExtraction

/-!
# The quadratic chart at zero phase is the monomial model at `N²`

Cross-validation of the two programmes (Astra #17's dictionary request). The 2D random-phase
Taylor tree works with the quadratic kernel `exp(-β (N u^{k₁} v^{k₂})² + β N u^{k₁}v^{k₂} ξ)` in the
variable `N = √n`; the monomial programme with `exp(-β M ∏ uᵢ^{2kᵢ})`. At zero phase `ξ ≡ 0` and
constant amplitude `η ≡ 1` the two integrands coincide with `M = N²`:

* the Taylor data `x = 0`, `y = δ₀₀` produce the constant amplitude `1`
  (`ampCoeff_zero_delta`, `anaAmp_delta`);
* `twoDAmp β b N h₁ h₂ k₁ k₂ 1 = monomialBoxRealCutoff 2 ![h₁,h₂] ![k₁,k₂] b β (N²)`
  (`twoDAmp_const_eq_monomialCutoff`);
* hence, by uniqueness of limits, the Taylor-tree leading log coefficient at zero phase equals
  **twice** the monomial mixed constant at `λ = p/2`, the factor `2` being `log N² = 2 log N`
  (`canonA_zeroPhase_eq_two_mul_monomialMixedConst`, `y₀₀ = 1`):
  `½ β^{-p/2} Γ(p/2)/(k₁k₂) = 2 · Γ(p/2) β^{-p/2}/(1! · 2k₁ · 2k₂)`.

This ties the fluctuation-function normalisation `S_{p/2}(0) = β^{-p/2}Γ(p/2)` of the first
programme to the Gamma constant of the second at the level of theorems, not just formulas.
-/

open MeasureTheory Set Filter Topology Asymptotics

namespace Laplace.Grammar

theorem conv_zero_left (g : ℕ × ℕ → ℝ) : conv (fun _ => (0 : ℝ)) g = fun _ => 0 := by
  funext k
  simp [conv]

theorem convPow_zero_fun_succ (n : ℕ) : convPow (fun _ => (0 : ℝ)) (n + 1) = fun _ => 0 := by
  simp [convPow, conv_zero_left]

theorem expCoeff_zero_fun (t : ℝ) (k : ℕ × ℕ) : expCoeff (fun _ => (0 : ℝ)) t k = delta k := by
  unfold expCoeff
  rw [Finset.sum_range_succ', Finset.sum_eq_zero fun n _ => by rw [convPow_zero_fun_succ]; simp]
  simp [convPow]

theorem dropConst_zero_fun : dropConst (fun _ => (0 : ℝ)) = fun _ => 0 := by
  funext k
  simp [dropConst]

/-- Zero phase and the constant amplitude `1` give the constant coefficient array `δ₀₀`. -/
theorem ampCoeff_zero_delta (β : ℝ) (k : ℕ × ℕ) (s : ℝ) :
    ampCoeff β (fun _ => 0) delta k s = delta k := by
  unfold ampCoeff
  rw [dropConst_zero_fun]
  have h : expCoeff (fun _ => (0 : ℝ)) (β * s) = delta := funext fun k => expCoeff_zero_fun _ k
  rw [h, conv_delta_right]
  simp

/-- The analytic amplitude of `δ₀₀` is the constant `1`. -/
theorem anaAmp_delta (b u v s : ℝ) : anaAmp (fun k _ => delta k) b u v s = 1 := by
  unfold anaAmp
  exact dblSum_delta _ _

theorem anaAmp_ampCoeff_zero_delta (β b u v s : ℝ) :
    anaAmp (ampCoeff β (fun _ => 0) delta) b u v s = 1 := by
  have h : ampCoeff β (fun _ => 0) delta = fun k _ => delta k :=
    funext fun k => funext fun s => ampCoeff_zero_delta β k s
  rw [h]
  exact anaAmp_delta b u v s

theorem monomialBox_integrableOn_cutoff (d : ℕ) (h k : Fin d → ℕ) (b β N : ℝ) :
    IntegrableOn (fun x : Fin d → ℝ =>
      (∏ i, x i ^ h i) * Real.exp (-(β * N * ∏ i, x i ^ (2 * k i)))) (cutoffBox d b) := by
  have hcont : Continuous fun x : Fin d → ℝ =>
      (∏ i, x i ^ h i) * Real.exp (-(β * N * ∏ i, x i ^ (2 * k i))) :=
    (continuous_finsetProd _ fun i _ => (continuous_apply i).pow _).mul
      (Real.continuous_exp.comp (continuous_const.mul
        (continuous_finsetProd _ fun i _ => (continuous_apply i).pow _)).neg)
  have hcpt : IsCompact (Set.pi univ fun _ : Fin d => Icc (0 : ℝ) b) :=
    isCompact_univ_pi fun _ => isCompact_Icc
  exact (hcont.continuousOn.integrableOn_compact hcpt).mono_set
    (pi_mono fun _ _ => Ioc_subset_Icc_self)

theorem continuous_finCons (d : ℕ) (u : ℝ) :
    Continuous fun w : Fin d → ℝ => (Fin.cons u w : Fin (d + 1) → ℝ) := by
  refine continuous_pi fun i => ?_
  refine Fin.cases ?_ (fun j => ?_) i
  · simp only [Fin.cons_zero]
    exact continuous_const
  · simp only [Fin.cons_succ]
    exact continuous_apply j

/-- **The identification**: the zero-phase, unit-amplitude quadratic chart integral over `(0,b]²`
is the monomial cutoff integral at parameter `N²`. -/
theorem twoDAmp_const_eq_monomialCutoff (β b N : ℝ) (h₁ h₂ k₁ k₂ : ℕ) :
    twoDAmp β b N h₁ h₂ k₁ k₂ (fun _ _ _ => 1) =
      monomialBoxRealCutoff 2 ![h₁, h₂] ![k₁, k₂] b β (N ^ 2) := by
  unfold twoDAmp monomialBoxRealCutoff
  have hbox : cutoffBox 2 b = piBox 2 (Ioc 0 b) := rfl
  set F : (Fin 2 → ℝ) → ℝ := fun x =>
    (∏ i, x i ^ (![h₁, h₂] : Fin 2 → ℕ) i) *
      Real.exp (-(β * N ^ 2 * ∏ i, x i ^ (2 * (![k₁, k₂] : Fin 2 → ℕ) i))) with hF
  have hFint : IntegrableOn F (piBox 2 (Ioc 0 b)) := by
    have := monomialBox_integrableOn_cutoff 2 ![h₁, h₂] ![k₁, k₂] b β (N ^ 2)
    rwa [hbox] at this
  have hFcont : Continuous F := by
    simp only [hF]
    exact (continuous_finsetProd _ fun i _ => (continuous_apply i).pow _).mul
      (Real.continuous_exp.comp (continuous_const.mul
        (continuous_finsetProd _ fun i _ => (continuous_apply i).pow _)).neg)
  change integral (volume.restrict (Ioc 0 b)) (fun u => u ^ h₁ * ∫ v in Ioc (0 : ℝ) b, v ^ h₂ *
    (Real.exp (-β * (N * (u ^ k₁ * v ^ k₂)) ^ 2) * 1)) = ∫ x in piBox 2 (Ioc 0 b), F x
  rw [integral_pi_box_succ 1 _ F hFint]
  refine setIntegral_congr_fun measurableSet_Ioc fun u _ => ?_
  have hsec : IntegrableOn (fun w : Fin 1 → ℝ => F (Fin.cons u w)) (piBox 1 (Ioc 0 b)) := by
    have hcpt : IsCompact (Set.pi univ fun _ : Fin 1 => Icc (0 : ℝ) b) :=
      isCompact_univ_pi fun _ => isCompact_Icc
    exact ((hFcont.comp (continuous_finCons 1 u)).continuousOn.integrableOn_compact hcpt).mono_set
      (pi_mono fun _ _ => Ioc_subset_Icc_self)
  rw [integral_pi_box_succ 0 _ _ hsec, ← integral_const_mul]
  refine setIntegral_congr_fun measurableSet_Ioc fun v _ => ?_
  rw [integral_piBox_zero]
  simp only [hF, Fin.prod_univ_two, Fin.cons_zero, Matrix.cons_val_zero, Matrix.cons_val_one,
    mul_one]
  rw [← Fin.succ_zero_eq_one, Fin.cons_succ, Fin.cons_zero, mul_pow, mul_pow, ← pow_mul,
    ← pow_mul, mul_comm k₁ 2, mul_comm k₂ 2]
  ring_nf

/-- At unit cutoff the monomial cutoff integral is the unit-box integral. -/
theorem monomialBoxRealCutoff_one (d : ℕ) (h k : Fin d → ℕ) (β N : ℝ) :
    monomialBoxRealCutoff d h k 1 β N = monomialBoxReal d h k β N := rfl

/-- **Zero-phase dictionary**: the unit-cutoff zero-phase quadratic chart with the Taylor data
`x = 0`, `y = δ₀₀` is the unit-box monomial integral at parameter `N²`. -/
theorem twoDAmp_zeroPhase_eq_monomial_sq (β N : ℝ) (h₁ h₂ k₁ k₂ : ℕ) :
    twoDAmp β 1 N h₁ h₂ k₁ k₂ (anaAmp (ampCoeff β (fun _ => 0) delta) 1) =
      monomialBoxReal 2 ![h₁, h₂] ![k₁, k₂] β (N ^ 2) := by
  have h : anaAmp (ampCoeff β (fun _ => 0) delta) 1 = fun _ _ _ => 1 :=
    funext fun u => funext fun v => funext fun s => anaAmp_ampCoeff_zero_delta β 1 u v s
  rw [h, twoDAmp_const_eq_monomialCutoff, monomialBoxRealCutoff_one]

/-- **Square-parameter transport**: a power–log limit in `T` becomes one in `N = √T` with the
logarithmic coefficient multiplied by `2^r`. -/
theorem tendsto_powLog_comp_sq (F : ℝ → ℝ) (l C : ℝ) (r : ℕ)
    (hF : Tendsto (fun T => F T / (T ^ (-l) * Real.log T ^ r)) atTop (𝓝 C)) :
    Tendsto (fun N => F (N ^ 2) / (N ^ (-(2 * l)) * Real.log N ^ r)) atTop
      (𝓝 ((2 : ℝ) ^ r * C)) := by
  have hsq : Tendsto (fun N : ℝ => N ^ 2) atTop atTop := tendsto_pow_atTop two_ne_zero
  have h := (hF.comp hsq).const_mul ((2 : ℝ) ^ r)
  refine h.congr' ?_
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with N hN
  simp only [Function.comp]
  have h1 : (N ^ 2 : ℝ) ^ (-l) = N ^ (-(2 * l)) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hN.le]
    congr 1
    push_cast
    ring
  have h2 : Real.log (N ^ 2) = 2 * Real.log N := by
    rw [Real.log_pow]
    push_cast
    ring
  rw [h1, h2, mul_pow]
  have hpow : N ^ (-(2 * l)) ≠ 0 := (Real.rpow_pos_of_pos hN _).ne'
  field_simp

theorem ratioExp_vecCons_zero (h₁ h₂ k₁ k₂ : ℕ) :
    ratioExp (![h₁, h₂] : Fin 2 → ℕ) ![k₁, k₂] 0 = ((h₁ : ℝ) + 1) / (2 * (k₁ : ℝ)) := rfl

theorem ratioExp_vecCons_one (h₁ h₂ k₁ k₂ : ℕ) :
    ratioExp (![h₁, h₂] : Fin 2 → ℕ) ![k₁, k₂] 1 = ((h₂ : ℝ) + 1) / (2 * (k₂ : ℝ)) := rfl

/-- **Constant cross-validation**: the Taylor-tree leading log coefficient at zero phase and unit
amplitude equals twice the monomial mixed constant at `λ = p/2`:
`y₀₀/(k₁k₂) · ∫₀^∞ s^{p-1} e^{-βs²} ds = 2 · Γ(p/2) β^{-p/2} / (1! · 2k₁ · 2k₂)`. -/
theorem canonA_zeroPhase_eq_two_mul_monomialMixedConst (β : ℝ) (h₁ h₂ k₁ k₂ : ℕ) (hβ : 0 < β)
    (hk₁ : 0 < k₁) (hk₂ : 0 < k₂) (p : ℝ) (hp₁ : ((h₁ : ℝ) + 1) / k₁ = p)
    (hp₂ : ((h₂ : ℝ) + 1) / k₂ = p) :
    canonA β h₁ h₂ k₁ k₂ (fun i j s => ampCoeff β (fun _ => 0) delta (i, j) s) p =
      2 * monomialMixedConst (![h₁, h₂] : Fin 2 → ℕ) ![k₁, k₂] (p / 2) β := by
  set A := canonA β h₁ h₂ k₁ k₂ (fun i j s => ampCoeff β (fun _ => 0) delta (i, j) s) p with hA
  have hApos : 0 < A :=
    leading_log_coeff_pos β h₁ h₂ k₁ k₂ hβ hk₁ hk₂ p hp₁ hp₂ (fun _ => 0) delta (by simp [delta])
  -- Taylor-tree side: `twoDAmp / (N^{-p} log N) → A`
  have hE := chart_isEquivalent_log β 1 p 2 h₁ h₂ k₁ k₂ hβ one_pos one_lt_two hk₁ hk₂ hp₁ hp₂
    (fun _ => 0) delta (wsummable_zero_fun 2) (wsummable_delta 2) hApos.ne'
  have hT1 : Tendsto (fun N => twoDAmp β 1 N h₁ h₂ k₁ k₂ (anaAmp (ampCoeff β (fun _ => 0) delta) 1)
      / (N ^ (-p) * Real.log N)) atTop (𝓝 A) := by
    have hz : ∀ᶠ N in atTop, powLog A p 1 N ≠ 0 := by
      filter_upwards [eventually_gt_atTop (1 : ℝ)] with N hN
      exact (powLog_pos A p 1 hApos N hN).ne'
    have h1 := (isEquivalent_iff_tendsto_one hz).1 hE
    have h2 := h1.const_mul A
    rw [mul_one] at h2
    refine h2.congr' ?_
    filter_upwards [eventually_gt_atTop (1 : ℝ)] with N hN
    have hN0 : 0 < N := by linarith
    have hpow : N ^ (-p) ≠ 0 := (Real.rpow_pos_of_pos hN0 _).ne'
    have hlog : Real.log N ≠ 0 := (Real.log_pos hN).ne'
    simp only [Pi.div_apply, powLog, pow_one]
    field_simp
  -- monomial side at `T = N²`
  have hk : ∀ i, 0 < (![k₁, k₂] : Fin 2 → ℕ) i := by
    intro i
    fin_cases i <;> simp [hk₁, hk₂]
  have hl : 0 < p / 2 := by
    have : 0 < p := by
      rw [← hp₁]
      have := hk₁
      positivity
    positivity
  have hr₀ : ratioExp (![h₁, h₂] : Fin 2 → ℕ) ![k₁, k₂] 0 = p / 2 := by
    rw [ratioExp_vecCons_zero, ← hp₁]
    have : (k₁ : ℝ) ≠ 0 := Nat.cast_ne_zero.2 hk₁.ne'
    field_simp
  have hr₁ : ratioExp (![h₁, h₂] : Fin 2 → ℕ) ![k₁, k₂] 1 = p / 2 := by
    rw [ratioExp_vecCons_one, ← hp₂]
    have : (k₂ : ℝ) ≠ 0 := Nat.cast_ne_zero.2 hk₂.ne'
    field_simp
  have hratio : ∀ i, ratioExp (![h₁, h₂] : Fin 2 → ℕ) ![k₁, k₂] i = p / 2 := by
    intro i
    fin_cases i
    · exact hr₀
    · exact hr₁
  have hm : multCount (ratioExp (![h₁, h₂] : Fin 2 → ℕ) ![k₁, k₂]) (p / 2) = 2 := by
    unfold multCount
    rw [Fin.sum_univ_two, if_pos hr₀, if_pos hr₁]
  have hM := monomialBoxReal_mixed_tendsto 1 (![h₁, h₂] : Fin 2 → ℕ) ![k₁, k₂] hk (p / 2) β hl hβ
    (fun i => (hratio i).symm.le) ⟨0, hr₀⟩
  rw [hm] at hM
  have hT2 := tendsto_powLog_comp_sq _ (p / 2) _ 1 hM
  simp only [pow_one, show 2 * (p / 2) = p by ring] at hT2
  have hT2' : Tendsto (fun N => twoDAmp β 1 N h₁ h₂ k₁ k₂ (anaAmp (ampCoeff β (fun _ => 0) delta) 1)
      / (N ^ (-p) * Real.log N)) atTop
      (𝓝 (2 * monomialMixedConst (![h₁, h₂] : Fin 2 → ℕ) ![k₁, k₂] (p / 2) β)) := by
    refine hT2.congr' (Eventually.of_forall fun N => ?_)
    beta_reduce
    rw [twoDAmp_zeroPhase_eq_monomial_sq]
  exact tendsto_nhds_unique hT1 hT2'

end Laplace.Grammar
