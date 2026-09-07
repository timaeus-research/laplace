/-
Copyright (c) 2026 Timaeus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Laplace.Grammar.StateDensityAPI

/-!
# Exact monomial moments with a constant phase (Stage 2a)

Unit 227 (Taylor-tree programme). The Taylor-tree terms are monomial integrals with a constant phase
`a = ξ(0)` and a phase power `p`:
```
T(N) = ∫_{(0,1]^d} u^h (√N u^k)^p exp(-βN u^{2k} + β√N u^k a) du,
```
`N` the sample size. In the state-density variable `τ = u^{2k}` the kernel is `g(Nτ)` with the
**phase kernel** `g(t) = (√t)^p e^{-βt + β√t a}`, so `T(N) = ∏ 1/(2kᵢ) ∫₀¹ v(τ) g(Nτ) dτ` with the
exact density `v` of unit 224. This file provides the two ingredients of the exact moment identity:
* `integral_unitBox_monomial_eq_stateDensity`: the real monomial bridge carrying the Jacobian;
* `basis_scaling`: for one basis term, the substitution `t = Nτ` and the binomial expansion of
  `(log N - log t)^j` give
  `∫₀¹ τ^{μ-1}(-log τ)^j g(Nτ) dτ =
     N^{-μ} ∑_{i≤j} C(j,i) (log N)^{j-i} ∫₀^N t^{μ-1}(-log t)^i g(t) dt`
  (`truncMoment`: the truncated log-weighted fluctuation moment).
Integrability of the signed integrands `t^{μ-1}(-log t)^i g(t)` on `(0,N]`
(`integrableOn_truncMoment`) is what licenses splitting the finite sums inside the integral.
Zero `sorry`/`axiom`.
-/

open MeasureTheory Set Real

namespace Laplace.Grammar

/-- The phase kernel `g(t) = (√t)^p exp(-βt + β√t a)`. -/
noncomputable def phaseKernel (β a : ℝ) (p : ℕ) (t : ℝ) : ℝ :=
  Real.sqrt t ^ p * Real.exp (-(β * t) + β * Real.sqrt t * a)

theorem continuous_phaseKernel (β a : ℝ) (p : ℕ) : Continuous (phaseKernel β a p) := by
  unfold phaseKernel
  fun_prop

theorem phaseKernel_nonneg (β a : ℝ) (p : ℕ) (t : ℝ) : 0 ≤ phaseKernel β a p t :=
  mul_nonneg (pow_nonneg (Real.sqrt_nonneg _) _) (Real.exp_pos _).le

/-- The truncated log-weighted fluctuation moment `∫₀^N t^{ν-1} (-log t)^i g(t) dt`. -/
noncomputable def truncMoment (β a : ℝ) (p : ℕ) (ν : ℝ) (i : ℕ) (N : ℝ) : ℝ :=
  ∫ t in Ioc (0 : ℝ) N, t ^ (ν - 1) * (-Real.log t) ^ i * phaseKernel β a p t

/-- Integrability of `t^{ν-1} (-log t)^i g(t)` on `(0,N]` for `ν > 0`. -/
theorem integrableOn_truncMoment (β a : ℝ) (p : ℕ) {ν : ℝ} (hν : 0 < ν) (i : ℕ) (N : ℝ) :
    IntegrableOn (fun t => t ^ (ν - 1) * (-Real.log t) ^ i * phaseKernel β a p t) (Ioc 0 N) := by
  -- on `(0,1]`: basis term times a bounded continuous factor; on `(1,N]`: continuous on a compact
  have hbdd : ∀ M : ℝ, ∃ C, ∀ t ∈ Icc (0 : ℝ) M, |phaseKernel β a p t| ≤ C := fun M => by
    obtain ⟨C, hC⟩ := (isCompact_Icc (a := (0 : ℝ)) (b := M)).exists_bound_of_continuousOn
      (continuous_phaseKernel β a p).continuousOn
    exact ⟨C, fun t ht => by simpa using hC t ht⟩
  have h01 : IntegrableOn (fun t => t ^ (ν - 1) * (-Real.log t) ^ i * phaseKernel β a p t)
      (Ioc 0 1) := by
    obtain ⟨C, hC⟩ := hbdd 1
    have this : IntegrableOn (fun x => phaseKernel β a p x * powLogBasis ν i x) (Ioc 0 1) :=
      (integrableOn_powLogBasis ν hν i).bdd_mul
        (c := C) (continuous_phaseKernel β a p).aestronglyMeasurable
        (ae_restrict_of_forall_mem measurableSet_Ioc fun t ht => by
          rw [Real.norm_eq_abs]; exact hC t ⟨ht.1.le, ht.2⟩)
    refine this.congr_fun (fun t _ => ?_) measurableSet_Ioc
    beta_reduce
    unfold powLogBasis
    ring
  by_cases hN1 : N ≤ 1
  · exact h01.mono_set (Ioc_subset_Ioc_right hN1)
  · push Not at hN1
    have h1N : IntegrableOn (fun t => t ^ (ν - 1) * (-Real.log t) ^ i * phaseKernel β a p t)
        (Ioc 1 N) := by
      refine (ContinuousOn.integrableOn_Icc ?_).mono_set Ioc_subset_Icc_self
      refine ContinuousOn.mul (ContinuousOn.mul (continuousOn_id.rpow_const fun t ht =>
        Or.inl (by linarith [ht.1] : t ≠ 0)) ((Real.continuousOn_log.mono fun t ht =>
        (by linarith [ht.1] : t ≠ 0)).neg.pow i)) (continuous_phaseKernel β a p).continuousOn
    rw [← Ioc_union_Ioc_eq_Ioc zero_le_one hN1.le]
    exact h01.union h1N

/-- Pointwise: `(t/N)^{μ-1} (-log(t/N))^j = N^{1-μ} t^{μ-1} ∑ C(j,i) (-log t)^i (log N)^{j-i}`. -/
theorem powLogBasis_div (μ : ℝ) (j : ℕ) {t N : ℝ} (ht : 0 < t) (hN : 0 < N) :
    powLogBasis μ j (t / N) = N ^ (1 - μ) * (t ^ (μ - 1) *
      ∑ i ∈ Finset.range (j + 1),
        (j.choose i : ℝ) * (Real.log N) ^ (j - i) * (-Real.log t) ^ i) := by
  unfold powLogBasis
  rw [Real.div_rpow ht.le hN.le, Real.log_div ht.ne' hN.ne', neg_sub,
    show Real.log N - Real.log t = -Real.log t + Real.log N by ring, add_pow, Finset.mul_sum,
    Finset.mul_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [show (1 : ℝ) - μ = -(μ - 1) by ring, Real.rpow_neg hN.le]
  field_simp

/-- **Scaling of a basis term**:
`∫₀¹ τ^{μ-1}(-log τ)^j g(Nτ) dτ =
  N^{-μ} ∑_{i≤j} C(j,i) (log N)^{j-i} ∫₀^N t^{μ-1}(-log t)^i g(t) dt`. -/
theorem basis_scaling (β a : ℝ) (p : ℕ) {μ : ℝ} (hμ : 0 < μ) (j : ℕ) {N : ℝ} (hN : 0 < N) :
    ∫ τ in Ioc (0 : ℝ) 1, powLogBasis μ j τ * phaseKernel β a p (N * τ) =
      N ^ (-μ) * ∑ i ∈ Finset.range (j + 1),
        (j.choose i : ℝ) * (Real.log N) ^ (j - i) * truncMoment β a p μ i N := by
  -- substitution `t = Nτ` on the interval integral
  have hsub : ∫ τ in Ioc (0 : ℝ) 1, powLogBasis μ j τ * phaseKernel β a p (N * τ) =
      N⁻¹ * ∫ t in Ioc (0 : ℝ) N, powLogBasis μ j (t / N) * phaseKernel β a p t := by
    have h := intervalIntegral.integral_comp_mul_left
      (fun t => powLogBasis μ j (t / N) * phaseKernel β a p t) hN.ne' (a := 0) (b := 1)
    simp only [mul_zero, mul_one, smul_eq_mul] at h
    rw [intervalIntegral.integral_of_le zero_le_one, intervalIntegral.integral_of_le hN.le] at h
    rw [← h]
    refine setIntegral_congr_fun measurableSet_Ioc fun τ _ => ?_
    rw [mul_div_cancel_left₀ τ hN.ne']
  rw [hsub]
  have hpt : ∀ t ∈ Ioc (0 : ℝ) N, powLogBasis μ j (t / N) * phaseKernel β a p t =
      ∑ i ∈ Finset.range (j + 1), N ^ (1 - μ) * ((j.choose i : ℝ) * (Real.log N) ^ (j - i)) *
        (t ^ (μ - 1) * (-Real.log t) ^ i * phaseKernel β a p t) := by
    intro t ht
    rw [powLogBasis_div μ j ht.1 hN]
    simp only [Finset.mul_sum, Finset.sum_mul]
    refine Finset.sum_congr rfl fun i _ => ?_
    ring
  rw [setIntegral_congr_fun measurableSet_Ioc hpt, integral_finsetSum _ fun i _ =>
    (integrableOn_truncMoment β a p hμ i N).const_mul _]
  unfold truncMoment
  rw [Finset.mul_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [integral_const_mul, show (1 : ℝ) - μ = -μ + 1 by ring, Real.rpow_add hN, Real.rpow_one]
  field_simp

/-! ### The real monomial bridge -/

/-- **Real monomial state-density identity**: for measurable `f ≥ 0` on `(0,1]`,
`∫_{(0,1]^{n+1}} u^h f(u^{2k}) du = ∏ 1/(2kᵢ) ∫₀¹ v(z) f(z) dz` with the density of weights
`(hᵢ+1)/(2kᵢ) - 1`. -/
theorem integral_unitBox_monomial_eq_stateDensity (n : ℕ) (h k : Fin (n + 1) → ℕ)
    (hk : ∀ i, 0 < k i) (f : ℝ → ℝ) (hf : Measurable f) (hf0 : ∀ z ∈ Ioc (0 : ℝ) 1, 0 ≤ f z) :
    ∫ u in unitBox (n + 1), (∏ i, u i ^ h i) * f (∏ i, u i ^ (2 * k i)) =
      (∏ i, 1 / (2 * (k i : ℝ))) * ∫ z in Ioc (0 : ℝ) 1,
        PowLogRep.eval (stateDensityRep n fun i => ((h i : ℝ) + 1) / (2 * (k i : ℝ)) - 1) z *
          f z := by
  have hprod : ∀ u ∈ unitBox (n + 1), ∏ i, u i ^ (2 * k i) ∈ Ioc (0 : ℝ) 1 := fun u hu =>
    ⟨Finset.prod_pos fun i _ => pow_pos (hu i (mem_univ i)).1 _,
      Finset.prod_le_one (fun i _ => pow_nonneg (hu i (mem_univ i)).1.le _)
        fun i _ => pow_le_one₀ (hu i (mem_univ i)).1.le (hu i (mem_univ i)).2⟩
  have hmeasL : Measurable fun u : Fin (n + 1) → ℝ =>
      (∏ i, u i ^ h i) * f (∏ i, u i ^ (2 * k i)) :=
    (Finset.measurable_prod _ fun i _ => (measurable_pi_apply i).pow_const _).mul
      (hf.comp (Finset.measurable_prod _ fun i _ => (measurable_pi_apply i).pow_const _))
  have hP : 0 ≤ ∏ i, 1 / (2 * (k i : ℝ)) := Finset.prod_nonneg fun i _ => by positivity
  set w : Fin (n + 1) → ℝ := fun i => ((h i : ℝ) + 1) / (2 * (k i : ℝ)) - 1 with hw
  rw [integral_eq_lintegral_of_nonneg_ae (ae_restrict_of_forall_mem (measurableSet_unitBox _)
      fun u hu => mul_nonneg
        (Finset.prod_nonneg fun i _ => pow_nonneg (hu i (mem_univ i)).1.le _)
        (hf0 _ (hprod u hu))) hmeasL.aestronglyMeasurable,
    integral_eq_lintegral_of_nonneg_ae (ae_restrict_of_forall_mem measurableSet_Ioc
      fun z hz => mul_nonneg (stateDensityRep_nonneg n w z hz) (hf0 z hz))
      ((PowLogRep.measurable_eval _).mul hf).aestronglyMeasurable]
  have hM := monomialBoxIntegral_eq_stateDensity n h k hk (fun z => ENNReal.ofReal (f z))
    (ENNReal.measurable_ofReal.comp hf)
  unfold monomialBoxIntegral at hM
  have hL : ∫⁻ u in unitBox (n + 1),
      ENNReal.ofReal ((∏ i, u i ^ h i) * f (∏ i, u i ^ (2 * k i))) =
      ∫⁻ u in unitBox (n + 1), (∏ i, ENNReal.ofReal (u i ^ h i)) *
        ENNReal.ofReal (f (∏ i, u i ^ (2 * k i))) :=
    setLIntegral_congr_fun (measurableSet_unitBox _) fun u hu => by
      rw [ENNReal.ofReal_mul (Finset.prod_nonneg fun i _ => pow_nonneg (hu i (mem_univ i)).1.le _),
        ENNReal.ofReal_prod_of_nonneg fun i _ => pow_nonneg (hu i (mem_univ i)).1.le _]
  have hR : ∫⁻ z in Ioc (0 : ℝ) 1, ENNReal.ofReal (PowLogRep.eval (stateDensityRep n w) z * f z) =
      ∫⁻ z in Ioc (0 : ℝ) 1, ENNReal.ofReal (PowLogRep.eval (stateDensityRep n w) z) *
        ENNReal.ofReal (f z) :=
    setLIntegral_congr_fun measurableSet_Ioc fun z hz =>
      ENNReal.ofReal_mul (stateDensityRep_nonneg n w z hz)
  rw [hL, hM, hR, ENNReal.toReal_mul, ENNReal.toReal_ofReal hP]

end Laplace.Grammar
