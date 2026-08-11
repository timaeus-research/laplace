/-
Copyright (c) 2026 Timaeus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib
import Laplace.OneD.MonomialPotential

/-!
# The finite jet potential and its exact scaling identity

Stage 2 of the weighted-jet recovery programme (germbij note §7.4).
The degenerate finite-jet potential
`L(x) = a·x^(2k) + ∑ c_r·x^(2k+r)` factors through its *profile*:
`L_q(u) = u^(2k)·P(q·u)` with `P(y) = a + ∑ c_r·y^r`
(`jetPotential_eq_pow_mul_profile`), so the correct integrability
envelope is a uniformly positive profile (`HasPositiveJetProfile`),
giving the global bound `ρ·u^(2k) ≤ L_q(u)` for **every** real `q`
(`jetPotential_lower_bound`) — small `q` alone cannot help, since
`q·u` still ranges over all of `ℝ`. Under the envelope every
polynomial moment is integrable with a `q`-independent dominating
function (`integrable_pow_mul_exp_neg_jetPotential`), and the exact
scaling identity holds: substituting `x = q·u` with `t·q^(2k) = 1`,
`t^(s/(2k))·⟨x^s⟩_t` equals the normalized moment of the reference
jet measure at `q` (`normalized_polynomialJet_scale`,
`gibbsExpectation_polynomialJet_scale`). The `R = 2` discriminant
certificate `hasPositiveJetProfile_two` is the quadratic-profile
analogue of the anharmonic `α² < 3λγ` condition.
-/

open Real MeasureTheory

namespace Laplace.OneD

open Laplace

/-- The profile of the finite jet: `P(y) = a + ∑_{r=1}^R c_r·y^r`,
with `c` indexed by `Fin R` (index `i` carries degree `i+1`). -/
noncomputable def jetProfile (R : ℕ) (a : ℝ) (c : Fin R → ℝ) (y : ℝ) : ℝ :=
  a + ∑ i : Fin R, c i * y ^ (i.1 + 1)

/-- The rescaled jet potential
`L_q(u) = a·u^(2k) + ∑_r c_r·q^r·u^(2k+r)`. -/
noncomputable def jetPotential
    (k R : ℕ) (a q : ℝ) (c : Fin R → ℝ) (u : ℝ) : ℝ :=
  a * u ^ (2 * k) +
    ∑ i : Fin R, c i * q ^ (i.1 + 1) * u ^ (2 * k + (i.1 + 1))

/-- The original unscaled polynomial potential (the jet at `q = 1`). -/
noncomputable def polynomialJet
    (k R : ℕ) (a : ℝ) (c : Fin R → ℝ) (x : ℝ) : ℝ :=
  jetPotential k R a 1 c x

/-- The jet potential factors through its profile:
`L_q(u) = u^(2k)·P(q·u)`. This is why smallness of `q` alone is no
envelope: `q·u` ranges over all of `ℝ` regardless of `q`. -/
theorem jetPotential_eq_pow_mul_profile
    (k R : ℕ) (a q : ℝ) (c : Fin R → ℝ) (u : ℝ) :
    jetPotential k R a q c u =
      u ^ (2 * k) * jetProfile R a c (q * u) := by
  unfold jetPotential jetProfile
  rw [mul_add, Finset.mul_sum]
  congr 1
  · ring
  · refine Finset.sum_congr rfl fun i _ ↦ ?_
    rw [mul_pow, pow_add]
    ring

/-- The integrability envelope: the profile is bounded below by a
positive constant, uniformly on all of `ℝ`. -/
def HasPositiveJetProfile (R : ℕ) (a ρ : ℝ) (c : Fin R → ℝ) : Prop :=
  0 < ρ ∧ ∀ y : ℝ, ρ ≤ jetProfile R a c y

/-- Under the envelope, `ρ·u^(2k) ≤ L_q(u)` for **every** real `q`. -/
theorem jetPotential_lower_bound
    {k R : ℕ} {a ρ q : ℝ} {c : Fin R → ℝ}
    (hprof : HasPositiveJetProfile R a ρ c) (u : ℝ) :
    ρ * u ^ (2 * k) ≤ jetPotential k R a q c u := by
  rw [jetPotential_eq_pow_mul_profile]
  have hu : (0 : ℝ) ≤ u ^ (2 * k) := by
    rw [pow_mul]
    positivity
  calc ρ * u ^ (2 * k) = u ^ (2 * k) * ρ := by ring
    _ ≤ u ^ (2 * k) * jetProfile R a c (q * u) :=
        mul_le_mul_of_nonneg_left (hprof.2 (q * u)) hu

/-- Continuity of the jet potential in `u`. -/
theorem jetPotential_continuous
    (k R : ℕ) (a q : ℝ) (c : Fin R → ℝ) :
    Continuous (fun u : ℝ ↦ jetPotential k R a q c u) := by
  unfold jetPotential
  exact ((continuous_const.mul (continuous_pow _)).add
    (continuous_finset_sum _ fun i _ ↦
      continuous_const.mul (continuous_pow _)))

/-- The `q`-independent dominating estimate for polynomial moments. -/
theorem norm_pow_mul_exp_neg_jetPotential_le
    {k R : ℕ} {a ρ q : ℝ} {c : Fin R → ℝ} (n : ℕ)
    (hprof : HasPositiveJetProfile R a ρ c) (u : ℝ) :
    ‖u ^ n * Real.exp (-jetPotential k R a q c u)‖ ≤
      |u| ^ n * Real.exp (-(ρ * u ^ (2 * k))) := by
  rw [Real.norm_eq_abs, abs_mul, abs_pow,
    abs_of_pos (Real.exp_pos _)]
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  apply Real.exp_le_exp.mpr
  have := jetPotential_lower_bound (q := q) (k := k) hprof u
  linarith

/-- Every polynomial moment of the jet Gibbs weight is integrable,
uniformly in `q` (the dominating function does not involve `q`). -/
theorem integrable_pow_mul_exp_neg_jetPotential
    {k R : ℕ} {a ρ q : ℝ} {c : Fin R → ℝ} (hk : 1 ≤ k) (n : ℕ)
    (hprof : HasPositiveJetProfile R a ρ c) :
    Integrable (fun u : ℝ ↦
      u ^ n * Real.exp (-jetPotential k R a q c u)) := by
  have hρfac : (0 : ℝ) < ρ * (Nat.factorial (2 * k) : ℝ) := by
    have := hprof.1
    positivity
  have hdom : Integrable (fun u : ℝ ↦
      |u ^ n * Real.exp (-(ρ * u ^ (2 * k)))|) := by
    have h := kth_integrable_pow hk n hρfac
    refine (h.congr (Filter.Eventually.of_forall fun u ↦ ?_)).abs
    have hfac : (Nat.factorial (2 * k) : ℝ) ≠ 0 := by
      exact_mod_cast (Nat.factorial_pos _).ne'
    field_simp
  have hbound : ∀ u : ℝ,
      ‖u ^ n * Real.exp (-jetPotential k R a q c u)‖ ≤
        |u ^ n * Real.exp (-(ρ * u ^ (2 * k)))| := by
    intro u
    have h2 : |u ^ n * Real.exp (-(ρ * u ^ (2 * k)))| =
        |u| ^ n * Real.exp (-(ρ * u ^ (2 * k))) := by
      rw [abs_mul, abs_pow, abs_of_pos (Real.exp_pos _)]
    rw [h2]
    exact norm_pow_mul_exp_neg_jetPotential_le n hprof u
  have hmeas : AEStronglyMeasurable (fun u : ℝ ↦
      u ^ n * Real.exp (-jetPotential k R a q c u)) volume := by
    apply Continuous.aestronglyMeasurable
    exact (continuous_pow n).mul
      (Real.continuous_exp.comp (jetPotential_continuous k R a q c).neg)
  exact hdom.mono' hmeas (Filter.Eventually.of_forall hbound)

/-- Partition-function specialization of the integrability lemma. -/
theorem integrable_exp_neg_jetPotential
    {k R : ℕ} {a ρ q : ℝ} {c : Fin R → ℝ} (hk : 1 ≤ k)
    (hprof : HasPositiveJetProfile R a ρ c) :
    Integrable (fun u : ℝ ↦
      Real.exp (-jetPotential k R a q c u)) := by
  have h := integrable_pow_mul_exp_neg_jetPotential (q := q) hk 0 hprof
  exact h.congr (Filter.Eventually.of_forall fun u ↦ by simp)

/-- The jet partition function is positive. -/
theorem integral_exp_neg_jetPotential_pos
    {k R : ℕ} {a ρ q : ℝ} {c : Fin R → ℝ} (hk : 1 ≤ k)
    (hprof : HasPositiveJetProfile R a ρ c) :
    0 < ∫ u : ℝ, Real.exp (-jetPotential k R a q c u) := by
  rw [integral_pos_iff_support_of_nonneg
    (fun u ↦ (Real.exp_pos _).le)
    (integrable_exp_neg_jetPotential hk hprof)]
  have : Function.support (fun u : ℝ ↦
      Real.exp (-jetPotential k R a q c u)) = Set.univ := by
    ext u
    simp [Function.mem_support, (Real.exp_pos _).ne']
  rw [this]
  simp

/-- The normalized moment of the reference jet measure. -/
noncomputable def normalizedJetMoment
    (k R s : ℕ) (a q : ℝ) (c : Fin R → ℝ) : ℝ :=
  (∫ u : ℝ, u ^ s * Real.exp (-jetPotential k R a q c u)) /
    ∫ u : ℝ, Real.exp (-jetPotential k R a q c u)

/-- The pointwise substitution identity: with `t·q^(2k) = 1`,
`t·L(q·u)` is exactly the rescaled jet potential at `q`. -/
theorem mul_polynomialJet_comp_mul
    {k R : ℕ} {a q t : ℝ} {c : Fin R → ℝ}
    (hqt : t * q ^ (2 * k) = 1) (u : ℝ) :
    t * polynomialJet k R a c (u * q) =
      jetPotential k R a q c u := by
  unfold polynomialJet jetPotential
  rw [mul_add, Finset.mul_sum]
  congr 1
  · rw [mul_pow]
    linear_combination a * u ^ (2 * k) * hqt
  · refine Finset.sum_congr rfl fun i _ ↦ ?_
    rw [one_pow, mul_pow, pow_add]
    linear_combination c i * u ^ (2 * k + (i.1 + 1)) *
      q ^ (i.1 + 1) * hqt

/-- **Exact unnormalized scaling.** With `q > 0` and `t·q^(2k) = 1`,
`∫ x^s·e^(-t·L(x)) dx = q^(s+1)·∫ u^s·e^(-L_q(u)) du`. -/
theorem integral_polynomialJet_scale
    {k R : ℕ} {a q t : ℝ} {c : Fin R → ℝ} (s : ℕ)
    (hq : 0 < q) (hqt : t * q ^ (2 * k) = 1) :
    (∫ x : ℝ, x ^ s * Real.exp (-(t * polynomialJet k R a c x))) =
      q ^ (s + 1) *
        ∫ u : ℝ, u ^ s * Real.exp (-jetPotential k R a q c u) := by
  have hsub := MeasureTheory.Measure.integral_comp_mul_right
    (g := fun x : ℝ ↦ x ^ s * Real.exp (-(t * polynomialJet k R a c x)))
    (a := q)
  rw [smul_eq_mul, abs_of_pos (inv_pos.mpr hq)] at hsub
  have hpt : ∀ u : ℝ,
      (u * q) ^ s * Real.exp (-(t * polynomialJet k R a c (u * q))) =
      q ^ s * (u ^ s * Real.exp (-jetPotential k R a q c u)) := by
    intro u
    rw [mul_polynomialJet_comp_mul hqt u, mul_pow]
    ring
  calc (∫ x : ℝ, x ^ s * Real.exp (-(t * polynomialJet k R a c x)))
      = q * ∫ u : ℝ, (u * q) ^ s *
          Real.exp (-(t * polynomialJet k R a c (u * q))) := by
        rw [hsub]
        field_simp
    _ = q * ∫ u : ℝ, q ^ s *
          (u ^ s * Real.exp (-jetPotential k R a q c u)) := by
        congr 1
        exact integral_congr_ae (Filter.Eventually.of_forall hpt)
    _ = q ^ (s + 1) *
          ∫ u : ℝ, u ^ s * Real.exp (-jetPotential k R a q c u) := by
        rw [integral_const_mul, pow_succ]
        ring

/-- **Exact normalized scaling** in ratio form: with `t·q^(2k) = 1`,
`(1/q^s)·(∫x^s·e^(-tL))/(∫e^(-tL))` is the normalized jet moment.
Multiplying by `1/q^s = t^(s/(2k))` is the familiar rescaling. -/
theorem normalized_polynomialJet_scale
    {k R : ℕ} {a ρ q t : ℝ} {c : Fin R → ℝ} (s : ℕ) (hk : 1 ≤ k)
    (hprof : HasPositiveJetProfile R a ρ c)
    (hq : 0 < q) (hqt : t * q ^ (2 * k) = 1) :
    (∫ x : ℝ, x ^ s * Real.exp (-(t * polynomialJet k R a c x))) /
      (∫ x : ℝ, Real.exp (-(t * polynomialJet k R a c x))) =
    q ^ s * normalizedJetMoment k R s a q c := by
  have hs := integral_polynomialJet_scale (a := a) (c := c) s hq hqt
  have h0 := integral_polynomialJet_scale (a := a) (c := c) 0 hq hqt
  simp only [pow_zero, one_mul, zero_add, pow_one] at h0
  have hZ := integral_exp_neg_jetPotential_pos (q := q) hk hprof
  rw [hs, h0, normalizedJetMoment]
  field_simp
  ring

/-- The public corollary in `gibbsExpectation` form. -/
theorem gibbsExpectation_polynomialJet_scale
    {k R : ℕ} {a ρ q t : ℝ} {c : Fin R → ℝ} (s : ℕ) (hk : 1 ≤ k)
    (hprof : HasPositiveJetProfile R a ρ c)
    (hq : 0 < q) (hqt : t * q ^ (2 * k) = 1) :
    gibbsExpectation (polynomialJet k R a c) t (fun x ↦ x ^ s) =
      q ^ s * normalizedJetMoment k R s a q c := by
  rw [← normalized_polynomialJet_scale s hk hprof hq hqt]
  rfl

/-- The `R = 2` certificate: a quadratic profile with positive leading
coefficient and discriminant condition `c₁² < 4ac₂` is uniformly
positive with `ρ = a - c₁²/(4c₂)` — the quadratic-profile analogue of
the anharmonic discriminant `α² < 3λγ`. -/
theorem hasPositiveJetProfile_two
    {a c₁ c₂ : ℝ} (hc₂ : 0 < c₂) (hdisc : c₁ ^ 2 < 4 * a * c₂) :
    HasPositiveJetProfile 2 a (a - c₁ ^ 2 / (4 * c₂)) ![c₁, c₂] := by
  constructor
  · rw [sub_pos, div_lt_iff₀ (by positivity)]
    linarith
  · intro y
    unfold jetProfile
    rw [Fin.sum_univ_two]
    norm_num [Matrix.cons_val_zero, Matrix.cons_val_one]
    have h4c : (0 : ℝ) < 4 * c₂ := by positivity
    have key : -(c₁ * y + c₂ * y ^ 2) ≤ c₁ ^ 2 / (4 * c₂) := by
      rw [le_div_iff₀ h4c]
      nlinarith [sq_nonneg (2 * c₂ * y + c₁)]
    linarith

end Laplace.OneD
