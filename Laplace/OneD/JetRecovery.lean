/-
Copyright (c) 2026 Timaeus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib
import Laplace.OneD.JetDifference
import Laplace.OneD.MonomialVariance

/-!
# The weighted-jet recovery theorem

Stages 3D-3G of the weighted-jet programme, closing the germbij §7.4
comparison recovery. From the pairwise difference limit of the
previous stage, a generic quotient-difference lemma
(`quotient_difference_tendsto`) produces the normalized covariance
limit; at the matching observable `s = 2k + r` the covariance is the
reference variance, whose strict positivity (stage 1) forces the
rung-`r` coefficients equal (`jet_one_rung_recovery`); finite strong
induction over rungs recovers the whole coefficient vector
(`jet_recovery`); and the stage-2 scaling identity transfers the
hypothesis back to the original Gibbs data: **two enveloped jets
whose normalized moments eventually agree have equal coefficients**
(`polynomialJet_recovery`).
-/

open Real MeasureTheory Filter Topology

namespace Laplace.OneD

open Laplace

/-- Base-point limit: each unnormalized jet moment converges to the
reference moment as `q → 0⁺` (dominated convergence, same majorant
as the difference limit). -/
theorem jet_integral_tendsto
    {k R : ℕ} {a ρ : ℝ} {c : Fin R → ℝ} (hk : 1 ≤ k) (s : ℕ)
    (h : HasPositiveJetProfile R a ρ c) :
    Tendsto (fun q : ℝ ↦
      ∫ u : ℝ, u ^ s * Real.exp (-jetPotential k R a q c u))
      (𝓝[>] 0)
      (𝓝 (∫ u : ℝ, u ^ s * Real.exp (-(a * u ^ (2 * k))))) := by
  apply tendsto_integral_filter_of_dominated_convergence
    (fun u : ℝ ↦ |u| ^ s * Real.exp (-(ρ * u ^ (2 * k))))
  · filter_upwards [self_mem_nhdsWithin] with q _
    exact ((continuous_pow s).mul (Real.continuous_exp.comp
      (jetPotential_continuous k R a q c).neg)).aestronglyMeasurable
  · filter_upwards [self_mem_nhdsWithin] with q _
    exact Filter.Eventually.of_forall fun u ↦
      norm_pow_mul_exp_neg_jetPotential_le s h u
  · exact integrable_abs_pow_mul_exp_neg_kth hk s h.1
  · refine Filter.Eventually.of_forall fun u ↦ ?_
    have hc : Continuous (fun q : ℝ ↦
        u ^ s * Real.exp (-jetPotential k R a q c u)) :=
      continuous_const.mul (Real.continuous_exp.comp
        (jetPotential_continuous_q k R a c u).neg)
    have := (hc.tendsto 0).mono_left
      (nhdsWithin_le_nhds (s := Set.Ioi (0 : ℝ)))
    rwa [jetPotential_zero] at this

/-- **The quotient-difference lemma** (stage 3D): scaled limits of
numerator and denominator differences produce the scaled limit of the
quotient difference. -/
theorem quotient_difference_tendsto {l : Filter ℝ}
    {σ A₁ A₂ B₁ B₂ : ℝ → ℝ} {α β A B : ℝ} (hB : B ≠ 0)
    (hA2 : Tendsto A₂ l (𝓝 A))
    (hB1 : Tendsto B₁ l (𝓝 B)) (hB2 : Tendsto B₂ l (𝓝 B))
    (hα : Tendsto (fun q ↦ (A₁ q - A₂ q) / σ q) l (𝓝 α))
    (hβ : Tendsto (fun q ↦ (B₁ q - B₂ q) / σ q) l (𝓝 β)) :
    Tendsto (fun q ↦ (A₁ q / B₁ q - A₂ q / B₂ q) / σ q) l
      (𝓝 ((α * B - A * β) / B ^ 2)) := by
  have hB1ne : ∀ᶠ q in l, B₁ q ≠ 0 := hB1.eventually_ne hB
  have hB2ne : ∀ᶠ q in l, B₂ q ≠ 0 := hB2.eventually_ne hB
  have hkey : Tendsto (fun q ↦
      (((A₁ q - A₂ q) / σ q) * B₂ q -
        A₂ q * ((B₁ q - B₂ q) / σ q)) / (B₁ q * B₂ q)) l
      (𝓝 ((α * B - A * β) / (B * B))) :=
    ((hα.mul hB2).sub (hA2.mul hβ)).div (hB1.mul hB2)
      (mul_ne_zero hB hB)
  have hev : ∀ᶠ q in l,
      (((A₁ q - A₂ q) / σ q) * B₂ q -
        A₂ q * ((B₁ q - B₂ q) / σ q)) / (B₁ q * B₂ q) =
      (A₁ q / B₁ q - A₂ q / B₂ q) / σ q := by
    filter_upwards [hB1ne, hB2ne] with q h1 h2
    rcases eq_or_ne (σ q) 0 with hσ | hσ
    · simp [hσ]
    · field_simp
      ring
  rw [show (α * B - A * β) / B ^ 2 = (α * B - A * β) / (B * B) by
    rw [sq]]
  exact hkey.congr' hev

/-- Positivity of the reference variance combination
`A_{2m}·A₀ - A_m²`, bridged from stage 1's Gibbs-variance positivity
at `t = a·(2k)!`. -/
theorem jet_reference_variance_pos
    {k : ℕ} (hk : 1 ≤ k) {a : ℝ} (ha : 0 < a) {m : ℕ} (hm : 1 ≤ m) :
    0 < (∫ u : ℝ, u ^ (2 * m) * Real.exp (-(a * u ^ (2 * k)))) *
        (∫ u : ℝ, Real.exp (-(a * u ^ (2 * k)))) -
      (∫ u : ℝ, u ^ m * Real.exp (-(a * u ^ (2 * k)))) ^ 2 := by
  set t : ℝ := a * (Nat.factorial (2 * k) : ℝ) with ht_def
  have hfac : (0 : ℝ) < (Nat.factorial (2 * k) : ℝ) := by
    exact_mod_cast Nat.factorial_pos _
  have ht : 0 < t := by
    rw [ht_def]
    positivity
  have hVar := monomial_variance_pos (k := k) (n := m) hk hm ht
  have harg : ∀ u : ℝ, -(t * kthPotential k u) =
      -(a * u ^ (2 * k)) := by
    intro u
    rw [kthPotential_apply, ht_def]
    field_simp
  simp only [gibbsCov, gibbsExpectation, partitionFunction,
    harg] at hVar
  have hsq : (∫ x : ℝ, x ^ m * x ^ m *
      Real.exp (-(a * x ^ (2 * k)))) =
      ∫ x : ℝ, x ^ (2 * m) * Real.exp (-(a * x ^ (2 * k))) := by
    refine integral_congr_ae (Filter.Eventually.of_forall fun x ↦ ?_)
    ring
  rw [hsq, ← pow_two ((∫ x : ℝ, x ^ m * Real.exp (-(a * x ^ (2 * k)))) /
    (∫ x : ℝ, Real.exp (-(a * x ^ (2 * k)))))] at hVar
  have hint0 : Integrable (fun u : ℝ ↦
      Real.exp (-(a * u ^ (2 * k)))) := by
    have := integrable_abs_pow_mul_exp_neg_kth hk 0 ha
    exact this.congr (Filter.Eventually.of_forall fun u ↦ by simp)
  have hZpos : 0 < ∫ u : ℝ, Real.exp (-(a * u ^ (2 * k))) := by
    rw [integral_pos_iff_support_of_nonneg
      (fun u ↦ (Real.exp_pos _).le) hint0]
    have hs : Function.support (fun u : ℝ ↦
        Real.exp (-(a * u ^ (2 * k)))) = Set.univ := by
      ext u
      simp [(Real.exp_pos _).ne']
    rw [hs]
    simp
  have hexpand : (∫ u : ℝ, u ^ (2 * m) *
        Real.exp (-(a * u ^ (2 * k)))) *
        (∫ u : ℝ, Real.exp (-(a * u ^ (2 * k)))) -
      (∫ u : ℝ, u ^ m * Real.exp (-(a * u ^ (2 * k)))) ^ 2 =
      ((∫ u : ℝ, u ^ (2 * m) * Real.exp (-(a * u ^ (2 * k)))) /
          (∫ u : ℝ, Real.exp (-(a * u ^ (2 * k)))) -
        ((∫ u : ℝ, u ^ m * Real.exp (-(a * u ^ (2 * k)))) /
          (∫ u : ℝ, Real.exp (-(a * u ^ (2 * k))))) ^ 2) *
        (∫ u : ℝ, Real.exp (-(a * u ^ (2 * k)))) ^ 2 := by
    field_simp
  rw [hexpand]
  exact mul_pos hVar (by positivity)

/-- **One-rung recovery** (stage 3E): if two enveloped jets agree
below rung `r = i₀ + 1` and the scaled difference of their normalized
moments at the matching observable `s = 2k + r` tends to `0`, then
the rung-`r` coefficients agree. -/
theorem jet_one_rung_recovery
    {k R : ℕ} {a ρ₁ ρ₂ : ℝ} {c₁ c₂ : Fin R → ℝ}
    (hk : 1 ≤ k) (ha : 0 < a) (i₀ : Fin R)
    (h1 : HasPositiveJetProfile R a ρ₁ c₁)
    (h2 : HasPositiveJetProfile R a ρ₂ c₂)
    (hlow : ∀ j : Fin R, j < i₀ → c₁ j = c₂ j)
    (hdata : Tendsto (fun q : ℝ ↦
      (normalizedJetMoment k R (2 * k + (i₀.1 + 1)) a q c₁ -
        normalizedJetMoment k R (2 * k + (i₀.1 + 1)) a q c₂) /
        q ^ (i₀.1 + 1)) (𝓝[>] 0) (𝓝 0)) :
    c₁ i₀ = c₂ i₀ := by
  set m : ℕ := 2 * k + (i₀.1 + 1) with hm_def
  set A0 : ℝ := ∫ u : ℝ, Real.exp (-(a * u ^ (2 * k))) with hA0_def
  set Am : ℝ := ∫ u : ℝ, u ^ m * Real.exp (-(a * u ^ (2 * k)))
    with hAm_def
  set A2m : ℝ := ∫ u : ℝ, u ^ (m + m) *
    Real.exp (-(a * u ^ (2 * k))) with hA2m_def
  have hint0 : Integrable (fun u : ℝ ↦
      Real.exp (-(a * u ^ (2 * k)))) := by
    have := integrable_abs_pow_mul_exp_neg_kth hk 0 ha
    exact this.congr (Filter.Eventually.of_forall fun u ↦ by simp)
  have hA0pos : 0 < A0 := by
    rw [hA0_def, integral_pos_iff_support_of_nonneg
      (fun u ↦ (Real.exp_pos _).le) hint0]
    have hs : Function.support (fun u : ℝ ↦
        Real.exp (-(a * u ^ (2 * k)))) = Set.univ := by
      ext u
      simp [(Real.exp_pos _).ne']
    rw [hs]
    simp
  -- Denominators in u^0 form, to match the s = 0 instances.
  have hzero_form : ∀ (c : Fin R → ℝ) (q : ℝ),
      (∫ u : ℝ, Real.exp (-jetPotential k R a q c u)) =
      ∫ u : ℝ, u ^ 0 * Real.exp (-jetPotential k R a q c u) :=
    fun c q ↦ integral_congr_ae
      (Filter.Eventually.of_forall fun u ↦ by simp)
  have hzero_ref : A0 = ∫ u : ℝ, u ^ 0 *
      Real.exp (-(a * u ^ (2 * k))) := by
    rw [hA0_def]
    exact integral_congr_ae
      (Filter.Eventually.of_forall fun u ↦ by simp)
  -- Assemble the 3D quotient limit.
  have hquot := quotient_difference_tendsto
    (l := 𝓝[>] (0 : ℝ)) (σ := fun q ↦ q ^ (i₀.1 + 1))
    (A₁ := fun q ↦ ∫ u : ℝ, u ^ m *
      Real.exp (-jetPotential k R a q c₁ u))
    (A₂ := fun q ↦ ∫ u : ℝ, u ^ m *
      Real.exp (-jetPotential k R a q c₂ u))
    (B₁ := fun q ↦ ∫ u : ℝ, Real.exp (-jetPotential k R a q c₁ u))
    (B₂ := fun q ↦ ∫ u : ℝ, Real.exp (-jetPotential k R a q c₂ u))
    (A := Am) (B := A0) hA0pos.ne'
    (jet_integral_tendsto hk m h2)
    (by
      have h := jet_integral_tendsto hk 0 h1
      rw [← hzero_ref] at h
      have heq : (fun q : ℝ ↦ ∫ u : ℝ, u ^ 0 *
          Real.exp (-jetPotential k R a q c₁ u)) = fun q : ℝ ↦
          ∫ u : ℝ, Real.exp (-jetPotential k R a q c₁ u) := by
        funext q
        exact (hzero_form c₁ q).symm
      rwa [heq] at h)
    (by
      have h := jet_integral_tendsto hk 0 h2
      rw [← hzero_ref] at h
      have heq : (fun q : ℝ ↦ ∫ u : ℝ, u ^ 0 *
          Real.exp (-jetPotential k R a q c₂ u)) = fun q : ℝ ↦
          ∫ u : ℝ, Real.exp (-jetPotential k R a q c₂ u) := by
        funext q
        exact (hzero_form c₂ q).symm
      rwa [heq] at h)
    (by
      have := jet_difference_integral_limit hk m i₀ h1 h2 hlow
      rwa [show m + (2 * k + (i₀.1 + 1)) = m + m by
        rw [hm_def]] at this)
    (by
      have := jet_difference_integral_limit hk 0 i₀ h1 h2 hlow
      rw [show 0 + (2 * k + (i₀.1 + 1)) = m by
        rw [hm_def]; ring] at this
      have heq : (fun q : ℝ ↦
          ((∫ u : ℝ, u ^ 0 * Real.exp (-jetPotential k R a q c₁ u)) -
            ∫ u : ℝ, u ^ 0 * Real.exp (-jetPotential k R a q c₂ u)) /
            q ^ (i₀.1 + 1)) = fun q : ℝ ↦
          ((∫ u : ℝ, Real.exp (-jetPotential k R a q c₁ u)) -
            ∫ u : ℝ, Real.exp (-jetPotential k R a q c₂ u)) /
            q ^ (i₀.1 + 1) := by
        funext q
        rw [hzero_form c₁ q, hzero_form c₂ q]
      rwa [heq] at this)
  -- Identify the two limits.
  have hFq : (fun q : ℝ ↦
      (normalizedJetMoment k R m a q c₁ -
        normalizedJetMoment k R m a q c₂) / q ^ (i₀.1 + 1)) =
      fun q : ℝ ↦
      ((∫ u : ℝ, u ^ m * Real.exp (-jetPotential k R a q c₁ u)) /
          (∫ u : ℝ, Real.exp (-jetPotential k R a q c₁ u)) -
        (∫ u : ℝ, u ^ m * Real.exp (-jetPotential k R a q c₂ u)) /
          (∫ u : ℝ, Real.exp (-jetPotential k R a q c₂ u))) /
        q ^ (i₀.1 + 1) := by
    funext q
    rw [normalizedJetMoment, normalizedJetMoment]
  rw [hFq] at hdata
  have huniq := tendsto_nhds_unique hquot hdata
  -- Extract δ = 0 from the vanishing limit.
  have hvar := jet_reference_variance_pos hk ha
    (m := m) (by omega : 1 ≤ m)
  have hbracket : 0 < A2m * A0 - Am ^ 2 := by
    rw [hA2m_def, hAm_def, hA0_def, show m + m = 2 * m by ring]
    exact hvar
  have hδ : (c₁ i₀ - c₂ i₀) * (A2m * A0 - Am ^ 2) = 0 := by
    have hnum := (div_eq_zero_iff.mp huniq).resolve_right
      (by positivity : (0 : ℝ) < A0 ^ 2).ne'
    rw [← hA2m_def, ← hAm_def] at hnum
    linear_combination -hnum
  have := (mul_eq_zero.mp hδ).resolve_right hbracket.ne'
  linarith [this]

/-- **Finite strong induction** (stage 3F): equal scaled moment data
at every rung forces equal coefficient vectors. -/
theorem jet_recovery
    {k R : ℕ} {a ρ₁ ρ₂ : ℝ} {c₁ c₂ : Fin R → ℝ}
    (hk : 1 ≤ k) (ha : 0 < a)
    (h1 : HasPositiveJetProfile R a ρ₁ c₁)
    (h2 : HasPositiveJetProfile R a ρ₂ c₂)
    (hdata : ∀ i : Fin R, Tendsto (fun q : ℝ ↦
      (normalizedJetMoment k R (2 * k + (i.1 + 1)) a q c₁ -
        normalizedJetMoment k R (2 * k + (i.1 + 1)) a q c₂) /
        q ^ (i.1 + 1)) (𝓝[>] 0) (𝓝 0)) :
    c₁ = c₂ := by
  have key : ∀ n : ℕ, ∀ i : Fin R, i.1 ≤ n → c₁ i = c₂ i := by
    intro n
    induction n using Nat.strong_induction_on with
    | _ n ih =>
      intro i _
      refine jet_one_rung_recovery hk ha i h1 h2 ?_ (hdata i)
      intro j hj
      have hji : j.1 < i.1 := hj
      rcases Nat.eq_zero_or_pos n with hn | hn
      · omega
      · exact ih j.1 (by omega) j le_rfl
  funext i
  exact key i.1 i le_rfl

/-- **The §7.4 comparison recovery theorem** (stage 3G): two
enveloped finite jets over the same base `a·x^(2k)` whose Gibbs
moments at the observables `x^(2k+r)`, `1 ≤ r ≤ R`, eventually agree
as `t → ∞` have equal coefficient vectors. -/
theorem polynomialJet_recovery
    {k R : ℕ} {a ρ₁ ρ₂ : ℝ} {c₁ c₂ : Fin R → ℝ}
    (hk : 1 ≤ k) (ha : 0 < a)
    (h1 : HasPositiveJetProfile R a ρ₁ c₁)
    (h2 : HasPositiveJetProfile R a ρ₂ c₂)
    (hdata : ∀ i : Fin R, ∀ᶠ t : ℝ in atTop,
      gibbsExpectation (polynomialJet k R a c₁) t
        (fun x ↦ x ^ (2 * k + (i.1 + 1))) =
      gibbsExpectation (polynomialJet k R a c₂) t
        (fun x ↦ x ^ (2 * k + (i.1 + 1)))) :
    c₁ = c₂ := by
  apply jet_recovery hk ha h1 h2
  intro i
  -- The inverse scale map sends q → 0⁺ to t → ∞.
  have htend : Tendsto (fun q : ℝ ↦ (q ^ (2 * k))⁻¹)
      (𝓝[>] 0) atTop := by
    apply Filter.Tendsto.inv_tendsto_nhdsGT_zero
    apply tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within
    · have := ((continuous_pow (2 * k)).tendsto (0 : ℝ)).mono_left
        (nhdsWithin_le_nhds (s := Set.Ioi (0 : ℝ)))
      simpa [zero_pow (by omega : 2 * k ≠ 0)] using this
    · filter_upwards [self_mem_nhdsWithin] with q hq
      exact pow_pos (Set.mem_Ioi.mp hq) _
  obtain ⟨t₀, ht₀⟩ := Filter.eventually_atTop.mp (hdata i)
  have hzero : ∀ᶠ q in 𝓝[>] (0 : ℝ),
      (normalizedJetMoment k R (2 * k + (i.1 + 1)) a q c₁ -
        normalizedJetMoment k R (2 * k + (i.1 + 1)) a q c₂) /
        q ^ (i.1 + 1) = 0 := by
    filter_upwards [htend.eventually (eventually_ge_atTop t₀),
      self_mem_nhdsWithin] with q hqt₀ hq
    have hq0 : (0 : ℝ) < q := hq
    have hqt : (q ^ (2 * k))⁻¹ * q ^ (2 * k) = 1 :=
      inv_mul_cancel₀ (by positivity)
    have hs1 := gibbsExpectation_polynomialJet_scale
      (t := (q ^ (2 * k))⁻¹) (2 * k + (i.1 + 1)) hk h1 hq0 hqt
    have hs2 := gibbsExpectation_polynomialJet_scale
      (t := (q ^ (2 * k))⁻¹) (2 * k + (i.1 + 1)) hk h2 hq0 hqt
    have hEq := ht₀ _ hqt₀
    have hmom : normalizedJetMoment k R (2 * k + (i.1 + 1)) a q c₁ =
        normalizedJetMoment k R (2 * k + (i.1 + 1)) a q c₂ := by
      have hchain := hs1.symm.trans (hEq.trans hs2)
      exact mul_left_cancel₀
        (by positivity : (q : ℝ) ^ (2 * k + (i.1 + 1)) ≠ 0) hchain
    rw [hmom, sub_self, zero_div]
  have hzero' : (fun _ : ℝ ↦ (0 : ℝ)) =ᶠ[𝓝[>] (0 : ℝ)]
      fun q : ℝ ↦
      (normalizedJetMoment k R (2 * k + (i.1 + 1)) a q c₁ -
        normalizedJetMoment k R (2 * k + (i.1 + 1)) a q c₂) /
        q ^ (i.1 + 1) := by
    filter_upwards [hzero] with q h
    exact h.symm
  exact tendsto_const_nhds.congr' hzero'

end Laplace.OneD
