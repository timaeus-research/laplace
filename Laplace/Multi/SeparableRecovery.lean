/-
Copyright (c) 2026 Timaeus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib
import Laplace.Multi.Defs
import Laplace.Multi.StdGaussian
import Laplace.OneD.MonomialPotential
import Laplace.OneD.Recovery

/-!
# Separable weighted-monomial recovery

The first constructive recovery statement at a degenerate minimum in
dimension greater than one (germbij §7.4(b), the exact separable
germ). For `L(w) = ∑ i, a i · w i ^ (2 k i) / (2 k i)!` the Gibbs
measure is a product of one-dimensional measures: the partition
function factorizes, each normalized coordinate moment reduces to its
one-dimensional counterpart, and the exact power law
`⟨w i ^ 2⟩_t = C(k i, a i) · t^(-1/k i)` recovers first the weight
(degree) and then the scale, coordinate by coordinate.
-/

open Real MeasureTheory Filter

namespace Laplace

namespace OneD

/-- Temperature-scale absorption: the Gibbs expectation against the
scaled monomial potential `a · L_k` at temperature `t` is the Gibbs
expectation against `L_k` at temperature `t · a`. -/
theorem gibbsExpectation_smul_kthPotential
    {k : ℕ} (a t : ℝ) (φ : ℝ → ℝ) :
    gibbsExpectation (fun x ↦ a * kthPotential k x) t φ =
      gibbsExpectation (kthPotential k) (t * a) φ := by
  unfold gibbsExpectation partitionFunction
  have harg : ∀ x : ℝ, -(t * (a * kthPotential k x)) =
      -(t * a * kthPotential k x) := fun x ↦ by ring
  simp only [harg]

/-- The second moment of the scaled monomial potential is an exact
power law: `⟨x²⟩_{a·L_k, t} = ((2k)!/a)^(1/k) · Γratio · t^(-1/k)`. -/
theorem secondMoment_smul_kthPotential
    {k : ℕ} (hk : 1 ≤ k) {a t : ℝ} (ha : 0 < a) (ht : 0 < t) :
    gibbsExpectation (fun x ↦ a * kthPotential k x) t
        (fun x ↦ x ^ 2) =
      (((Nat.factorial (2 * k) : ℝ) / a) ^ ((1 : ℝ) / (k : ℝ)) *
          (Real.Gamma ((2 * 1 + 1 : ℝ) / ((2 * k : ℕ) : ℝ)) /
            Real.Gamma ((1 : ℝ) / ((2 * k : ℕ) : ℝ)))) *
        t ^ (-(1 : ℝ) / (k : ℝ)) := by
  rw [gibbsExpectation_smul_kthPotential]
  have hta : 0 < t * a := mul_pos ht ha
  have h := gibbsExpectation_kthPotential_even hk 1 (t := t * a) hta
  have hφ : (fun x : ℝ ↦ x ^ (2 * 1)) = fun x : ℝ ↦ x ^ 2 := by
    funext x; norm_num
  rw [hφ] at h
  rw [h]
  have hk0 : (0 : ℝ) < (k : ℝ) := by
    exact_mod_cast Nat.lt_of_lt_of_le Nat.zero_lt_one hk
  have hfac : (0 : ℝ) < (Nat.factorial (2 * k) : ℝ) := by
    exact_mod_cast Nat.factorial_pos _
  have hsplit : ((Nat.factorial (2 * k) : ℝ) / (t * a)) ^
      (((1 : ℕ) : ℝ) / (k : ℝ)) =
      ((Nat.factorial (2 * k) : ℝ) / a) ^ ((1 : ℝ) / (k : ℝ)) *
        t ^ (-(1 : ℝ) / (k : ℝ)) := by
    have h1 : (Nat.factorial (2 * k) : ℝ) / (t * a) =
        ((Nat.factorial (2 * k) : ℝ) / a) * t⁻¹ := by
      rw [mul_comm t a, ← div_div, div_eq_mul_inv]
    have hinv : t⁻¹ = t ^ (-1 : ℝ) := by
      rw [Real.rpow_neg ht.le, Real.rpow_one]
    rw [h1, Real.mul_rpow (by positivity) (by positivity), hinv,
      ← Real.rpow_mul ht.le]
    norm_num [neg_div]
  rw [hsplit]
  ring

/-- The power-law coefficient of the scaled second moment is
positive. -/
theorem secondMoment_coeff_pos {k : ℕ} (hk : 1 ≤ k) {a : ℝ}
    (ha : 0 < a) :
    0 < ((Nat.factorial (2 * k) : ℝ) / a) ^ ((1 : ℝ) / (k : ℝ)) *
      (Real.Gamma ((2 * 1 + 1 : ℝ) / ((2 * k : ℕ) : ℝ)) /
        Real.Gamma ((1 : ℝ) / ((2 * k : ℕ) : ℝ))) := by
  have hfac : (0 : ℝ) < (Nat.factorial (2 * k) : ℝ) := by
    exact_mod_cast Nat.factorial_pos _
  have h2k : (0 : ℝ) < ((2 * k : ℕ) : ℝ) := by
    have : (0 : ℕ) < 2 * k := by omega
    exact_mod_cast this
  have hΓ₁ : 0 < Real.Gamma ((2 * 1 + 1 : ℝ) / ((2 * k : ℕ) : ℝ)) :=
    Real.Gamma_pos_of_pos (by positivity)
  have hΓ₂ : 0 < Real.Gamma ((1 : ℝ) / ((2 * k : ℕ) : ℝ)) :=
    Real.Gamma_pos_of_pos (by positivity)
  have hrpow : 0 < ((Nat.factorial (2 * k) : ℝ) / a) ^
      ((1 : ℝ) / (k : ℝ)) :=
    Real.rpow_pos_of_pos (by positivity) _
  positivity

/-- **One-dimensional second-moment recovery** for scaled monomial
potentials: ray equality of the normalized second moments forces
equal degrees and equal scales. -/
theorem kth_secondMoment_recovery
    {k₁ k₂ : ℕ} (hk₁ : 1 ≤ k₁) (hk₂ : 1 ≤ k₂)
    {a₁ a₂ T : ℝ} (ha₁ : 0 < a₁) (ha₂ : 0 < a₂) (hT : 0 < T)
    (h : ∀ t : ℝ, T ≤ t →
      gibbsExpectation (fun x ↦ a₁ * kthPotential k₁ x) t
          (fun x ↦ x ^ 2) =
        gibbsExpectation (fun x ↦ a₂ * kthPotential k₂ x) t
          (fun x ↦ x ^ 2)) :
    k₁ = k₂ ∧ a₁ = a₂ := by
  have hk₁0 : (0 : ℝ) < (k₁ : ℝ) := by exact_mod_cast hk₁
  have hk₂0 : (0 : ℝ) < (k₂ : ℝ) := by exact_mod_cast hk₂
  obtain ⟨hβ, hα⟩ := eventual_power_eq
    (α₁ := ((Nat.factorial (2 * k₁) : ℝ) / a₁) ^
        ((1 : ℝ) / (k₁ : ℝ)) *
      (Real.Gamma ((2 * 1 + 1 : ℝ) / ((2 * k₁ : ℕ) : ℝ)) /
        Real.Gamma ((1 : ℝ) / ((2 * k₁ : ℕ) : ℝ))))
    (α₂ := ((Nat.factorial (2 * k₂) : ℝ) / a₂) ^
        ((1 : ℝ) / (k₂ : ℝ)) *
      (Real.Gamma ((2 * 1 + 1 : ℝ) / ((2 * k₂ : ℕ) : ℝ)) /
        Real.Gamma ((1 : ℝ) / ((2 * k₂ : ℕ) : ℝ))))
    (β₁ := -(1 : ℝ) / (k₁ : ℝ)) (β₂ := -(1 : ℝ) / (k₂ : ℝ))
    (secondMoment_coeff_pos hk₁ ha₁)
    (fun t ht ↦ by
      have ht0 : 0 < t := lt_of_lt_of_le hT ht
      rw [← secondMoment_smul_kthPotential hk₁ ha₁ ht0,
        ← secondMoment_smul_kthPotential hk₂ ha₂ ht0]
      exact h t ht)
  have hkk : k₁ = k₂ := by
    have : (k₁ : ℝ) = (k₂ : ℝ) := by
      field_simp at hβ
      linarith
    exact_mod_cast this
  refine ⟨hkk, ?_⟩
  subst hkk
  have hΓratio : 0 <
      Real.Gamma ((2 * 1 + 1 : ℝ) / ((2 * k₁ : ℕ) : ℝ)) /
        Real.Gamma ((1 : ℝ) / ((2 * k₁ : ℕ) : ℝ)) := by
    have h2k : (0 : ℝ) < ((2 * k₁ : ℕ) : ℝ) := by
      have : (0 : ℕ) < 2 * k₁ := by omega
      exact_mod_cast this
    have hΓ₁ : 0 < Real.Gamma ((2 * 1 + 1 : ℝ) / ((2 * k₁ : ℕ) : ℝ)) :=
      Real.Gamma_pos_of_pos (by positivity)
    have hΓ₂ : 0 < Real.Gamma ((1 : ℝ) / ((2 * k₁ : ℕ) : ℝ)) :=
      Real.Gamma_pos_of_pos (by positivity)
    positivity
  have hrpow_eq : ((Nat.factorial (2 * k₁) : ℝ) / a₁) ^
      ((1 : ℝ) / (k₁ : ℝ)) =
      ((Nat.factorial (2 * k₁) : ℝ) / a₂) ^ ((1 : ℝ) / (k₁ : ℝ)) :=
    mul_right_cancel₀ hΓratio.ne' hα
  have hexp : ((1 : ℝ) / (k₁ : ℝ)) ≠ 0 := by positivity
  have hbase : (Nat.factorial (2 * k₁) : ℝ) / a₁ =
      (Nat.factorial (2 * k₁) : ℝ) / a₂ :=
    Real.rpow_left_injOn hexp
      (Set.mem_setOf_eq ▸ div_nonneg (Nat.cast_nonneg _) ha₁.le)
      (Set.mem_setOf_eq ▸ div_nonneg (Nat.cast_nonneg _) ha₂.le)
      hrpow_eq
  have hfac : (0 : ℝ) < (Nat.factorial (2 * k₁) : ℝ) := by
    exact_mod_cast Nat.factorial_pos _
  have hmul := (div_eq_div_iff ha₁.ne' ha₂.ne').mp hbase
  exact (mul_left_cancel₀ hfac.ne' hmul).symm

end OneD

namespace Multi

variable {ι : Type*} [Fintype ι]

/-- The separable weighted-monomial potential
`L(w) = ∑ i, a i · w i ^ (2 k i) / (2 k i)!`. -/
noncomputable def separableMonomial (a : ι → ℝ) (k : ι → ℕ) :
    (ι → ℝ) → ℝ :=
  fun w ↦ ∑ i, a i * OneD.kthPotential (k i) (w i)

/-- The Boltzmann factor of a separable potential is a product of
one-dimensional Boltzmann factors. -/
theorem exp_separableMonomial (a : ι → ℝ) (k : ι → ℕ) (t : ℝ)
    (w : ι → ℝ) :
    Real.exp (-(t * separableMonomial a k w)) =
      ∏ i, Real.exp (-(t * (a i * OneD.kthPotential (k i) (w i)))) := by
  rw [← Real.exp_sum]
  congr 1
  rw [separableMonomial, Finset.mul_sum, ← Finset.sum_neg_distrib]

/-- The partition function of a separable potential factorizes into
the one-dimensional partition functions. -/
theorem partitionFunction_separableMonomial (a : ι → ℝ) (k : ι → ℕ)
    (t : ℝ) :
    partitionFunction (separableMonomial a k) t =
      ∏ i, _root_.Laplace.partitionFunction
        (fun x ↦ a i * OneD.kthPotential (k i) x) t := by
  unfold partitionFunction _root_.Laplace.partitionFunction
  calc ∫ w : ι → ℝ, Real.exp (-(t * separableMonomial a k w))
      = ∫ w : ι → ℝ, ∏ i,
          Real.exp (-(t * (a i * OneD.kthPotential (k i) (w i)))) :=
        integral_congr_ae (Filter.Eventually.of_forall fun w ↦
          exp_separableMonomial a k t w)
    _ = ∏ i, ∫ x : ℝ,
          Real.exp (-(t * (a i * OneD.kthPotential (k i) x))) :=
        integral_fintype_prod_volume_eq_prod
          (f := fun i x ↦
            Real.exp (-(t * (a i * OneD.kthPotential (k i) x))))

/-- The coordinate second-moment numerator of a separable potential
factorizes: the distinguished coordinate carries the moment, the
others contribute their partition functions. -/
theorem coordSq_integral_separableMonomial [DecidableEq ι]
    (a : ι → ℝ) (k : ι → ℕ) (t : ℝ) (i₀ : ι) :
    ∫ w : ι → ℝ, (w i₀) ^ 2 *
        Real.exp (-(t * separableMonomial a k w)) =
      (∫ x : ℝ, x ^ 2 *
          Real.exp (-(t * (a i₀ * OneD.kthPotential (k i₀) x)))) *
        ∏ i ∈ Finset.univ.erase i₀, _root_.Laplace.partitionFunction
          (fun x ↦ a i * OneD.kthPotential (k i) x) t := by
  have hpt : ∀ w : ι → ℝ, (w i₀) ^ 2 *
      Real.exp (-(t * separableMonomial a k w)) =
      ∏ i, (if i = i₀ then (w i) ^ 2 else 1) *
        Real.exp (-(t * (a i * OneD.kthPotential (k i) (w i)))) := by
    intro w
    rw [exp_separableMonomial a k t w, Finset.prod_mul_distrib,
      Finset.prod_ite_eq', if_pos (Finset.mem_univ i₀)]
  calc ∫ w : ι → ℝ, (w i₀) ^ 2 *
        Real.exp (-(t * separableMonomial a k w))
      = ∫ w : ι → ℝ, ∏ i, (if i = i₀ then (w i) ^ 2 else 1) *
          Real.exp (-(t * (a i * OneD.kthPotential (k i) (w i)))) :=
        integral_congr_ae (Filter.Eventually.of_forall hpt)
    _ = ∏ i, ∫ x : ℝ, (if i = i₀ then x ^ 2 else 1) *
          Real.exp (-(t * (a i * OneD.kthPotential (k i) x))) :=
        integral_fintype_prod_volume_eq_prod
          (f := fun i x ↦ (if i = i₀ then x ^ 2 else 1) *
            Real.exp (-(t * (a i * OneD.kthPotential (k i) x))))
    _ = (∫ x : ℝ, x ^ 2 *
          Real.exp (-(t * (a i₀ * OneD.kthPotential (k i₀) x)))) *
        ∏ i ∈ Finset.univ.erase i₀, _root_.Laplace.partitionFunction
          (fun x ↦ a i * OneD.kthPotential (k i) x) t := by
        rw [← Finset.mul_prod_erase Finset.univ _
          (Finset.mem_univ i₀)]
        congr 1
        · congr 1
          funext x
          rw [if_pos rfl]
        · refine Finset.prod_congr rfl fun i hi ↦ ?_
          unfold _root_.Laplace.partitionFunction
          congr 1
          funext x
          rw [if_neg (Finset.ne_of_mem_erase hi), one_mul]

/-- **Coordinate reduction**: the normalized coordinate second moment
of a separable potential equals its one-dimensional counterpart (the
spectator factors cancel between numerator and denominator). -/
theorem gibbsExpectation_coordSq_separableMonomial
    {a : ι → ℝ} {k : ι → ℕ} (ha : ∀ i, 0 < a i) (hk : ∀ i, 1 ≤ k i)
    {t : ℝ} (ht : 0 < t) (i₀ : ι) :
    gibbsExpectation (separableMonomial a k) t (fun w ↦ (w i₀) ^ 2) =
      _root_.Laplace.gibbsExpectation
        (fun x ↦ a i₀ * OneD.kthPotential (k i₀) x) t
        (fun x ↦ x ^ 2) := by
  classical
  have hZpos : ∀ i : ι, 0 < _root_.Laplace.partitionFunction
      (fun x ↦ a i * OneD.kthPotential (k i) x) t := by
    intro i
    have h := OneD.partitionFunction_kthPotential_pos (hk i)
      (t := t * a i) (mul_pos ht (ha i))
    unfold _root_.Laplace.partitionFunction at h ⊢
    have harg : ∀ x : ℝ, -(t * (a i * OneD.kthPotential (k i) x)) =
        -(t * a i * OneD.kthPotential (k i) x) := fun x ↦ by ring
    simp only [harg]
    exact h
  unfold gibbsExpectation _root_.Laplace.gibbsExpectation
  rw [coordSq_integral_separableMonomial,
    partitionFunction_separableMonomial,
    ← Finset.mul_prod_erase Finset.univ _ (Finset.mem_univ i₀)]
  have hprod_pos : 0 < ∏ i ∈ Finset.univ.erase i₀,
      _root_.Laplace.partitionFunction
        (fun x ↦ a i * OneD.kthPotential (k i) x) t :=
    Finset.prod_pos fun i _ ↦ hZpos i
  rw [mul_div_mul_right _ _ hprod_pos.ne']

/-- **Separable degenerate recovery** (germbij §7.4(b), exact
separable germ): two separable weighted-monomial potentials whose
normalized coordinate second moments agree on a temperature ray have
equal degrees and equal scales in every coordinate — the first
constructive recovery at a degenerate minimum in dimension greater
than one. -/
theorem separableMonomial_recovery
    {a₁ a₂ : ι → ℝ} {k₁ k₂ : ι → ℕ}
    (ha₁ : ∀ i, 0 < a₁ i) (ha₂ : ∀ i, 0 < a₂ i)
    (hk₁ : ∀ i, 1 ≤ k₁ i) (hk₂ : ∀ i, 1 ≤ k₂ i)
    {T : ℝ} (hT : 0 < T)
    (h : ∀ (i : ι) (t : ℝ), T ≤ t →
      gibbsExpectation (separableMonomial a₁ k₁) t
          (fun w ↦ (w i) ^ 2) =
        gibbsExpectation (separableMonomial a₂ k₂) t
          (fun w ↦ (w i) ^ 2)) :
    k₁ = k₂ ∧ a₁ = a₂ := by
  have hcoord : ∀ i : ι, k₁ i = k₂ i ∧ a₁ i = a₂ i := by
    intro i
    refine OneD.kth_secondMoment_recovery (hk₁ i) (hk₂ i)
      (ha₁ i) (ha₂ i) hT fun t ht ↦ ?_
    have ht0 : 0 < t := lt_of_lt_of_le hT ht
    rw [← gibbsExpectation_coordSq_separableMonomial ha₁ hk₁ ht0 i,
      ← gibbsExpectation_coordSq_separableMonomial ha₂ hk₂ ht0 i]
    exact h i t ht
  exact ⟨funext fun i ↦ (hcoord i).1, funext fun i ↦ (hcoord i).2⟩

end Multi

end Laplace
