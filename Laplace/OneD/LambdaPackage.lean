/-
Copyright (c) 2026 Timaeus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib
import Laplace.OneD.BaseRecovery

/-!
# The nondegenerate λ-package

Stages B3-B5, closing the unequal-base programme. The `t`-to-`q`
data transfer (`gibbs_data_to_jet_data`) converts eventually-equal
Gibbs moments into eventually-equal jet moments through the exact
scaling identity; composing base recovery with the comparison theorem
gives the variable-base recovery
(`polynomialJet_recovery_variableBase`); specialising to `k = 1` with
the quadratic coefficient written `λ/2` gives the nondegenerate
package (`nondegenerateJet_recovery`); and the second moment's rate
is the familiar `t·⟨x²⟩_t → 1/λ` (`gibbs_secondMoment_rate`), the
germbij Theorem 3.1 opening move in its native normalisation.
-/

open Real MeasureTheory Filter Topology

namespace Laplace.OneD

open Laplace

/-- The inverse-scale map carries `q → 0⁺` data to `t → ∞` data:
eventually-equal Gibbs moments at `x^s` give eventually-equal
normalized jet moments. -/
theorem gibbs_data_to_jet_data
    {k R s : ℕ} {a₁ a₂ ρ₁ ρ₂ : ℝ} {c₁ c₂ : Fin R → ℝ} (hk : 1 ≤ k)
    (h1 : HasPositiveJetProfile R a₁ ρ₁ c₁)
    (h2 : HasPositiveJetProfile R a₂ ρ₂ c₂)
    (hdata : ∀ᶠ t : ℝ in atTop,
      gibbsExpectation (polynomialJet k R a₁ c₁) t (fun x ↦ x ^ s) =
      gibbsExpectation (polynomialJet k R a₂ c₂) t (fun x ↦ x ^ s)) :
    ∀ᶠ q in 𝓝[>] (0 : ℝ),
      normalizedJetMoment k R s a₁ q c₁ =
        normalizedJetMoment k R s a₂ q c₂ := by
  have htend : Tendsto (fun q : ℝ ↦ (q ^ (2 * k))⁻¹)
      (𝓝[>] 0) atTop := by
    apply Filter.Tendsto.inv_tendsto_nhdsGT_zero
    apply tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within
    · have := ((continuous_pow (2 * k)).tendsto (0 : ℝ)).mono_left
        (nhdsWithin_le_nhds (s := Set.Ioi (0 : ℝ)))
      simpa [zero_pow (by omega : 2 * k ≠ 0)] using this
    · filter_upwards [self_mem_nhdsWithin] with q hq
      exact pow_pos (Set.mem_Ioi.mp hq) _
  obtain ⟨t₀, ht₀⟩ := Filter.eventually_atTop.mp hdata
  filter_upwards [htend.eventually (eventually_ge_atTop t₀),
    self_mem_nhdsWithin] with q hqt₀ hq
  have hq0 : (0 : ℝ) < q := hq
  have hqt : (q ^ (2 * k))⁻¹ * q ^ (2 * k) = 1 :=
    inv_mul_cancel₀ (by positivity)
  have hs1 := gibbsExpectation_polynomialJet_scale
    (t := (q ^ (2 * k))⁻¹) s hk h1 hq0 hqt
  have hs2 := gibbsExpectation_polynomialJet_scale
    (t := (q ^ (2 * k))⁻¹) s hk h2 hq0 hqt
  have hEq := ht₀ _ hqt₀
  have hchain := hs1.symm.trans (hEq.trans hs2)
  exact mul_left_cancel₀
    (by positivity : (q : ℝ) ^ s ≠ 0) hchain

/-- **B3: variable-base recovery.** Two enveloped jets whose Gibbs
moments at `x²` and at every `x^(2k+r)` eventually agree have equal
bases and equal coefficients. -/
theorem polynomialJet_recovery_variableBase
    {k R : ℕ} {a₁ a₂ ρ₁ ρ₂ : ℝ} {c₁ c₂ : Fin R → ℝ} (hk : 1 ≤ k)
    (h1 : HasPositiveJetProfile R a₁ ρ₁ c₁)
    (h2 : HasPositiveJetProfile R a₂ ρ₂ c₂)
    (hdata2 : ∀ᶠ t : ℝ in atTop,
      gibbsExpectation (polynomialJet k R a₁ c₁) t (fun x ↦ x ^ 2) =
      gibbsExpectation (polynomialJet k R a₂ c₂) t (fun x ↦ x ^ 2))
    (hdataR : ∀ i : Fin R, ∀ᶠ t : ℝ in atTop,
      gibbsExpectation (polynomialJet k R a₁ c₁) t
        (fun x ↦ x ^ (2 * k + (i.1 + 1))) =
      gibbsExpectation (polynomialJet k R a₂ c₂) t
        (fun x ↦ x ^ (2 * k + (i.1 + 1)))) :
    a₁ = a₂ ∧ c₁ = c₂ := by
  have hq2 := gibbs_data_to_jet_data hk h1 h2 hdata2
  have ha := base_recovery hk h1 h2 hq2
  subst ha
  exact ⟨rfl, polynomialJet_recovery hk h1.base_pos h1 h2 hdataR⟩

/-- The nondegenerate potential `(λ/2)·x² + ∑ c_r·x^(2+r)`. -/
noncomputable def nondegenerateJet
    (R : ℕ) (lam : ℝ) (c : Fin R → ℝ) : ℝ → ℝ :=
  polynomialJet 1 R (lam / 2) c

/-- **B4: the nondegenerate package** (`k = 1`, germbij Theorem 3.1
normalisation). Eventually-equal Gibbs moments at `x²` and at every
`x^(2+r)` recover `λ` and every higher coefficient. -/
theorem nondegenerateJet_recovery
    {R : ℕ} {lam₁ lam₂ ρ₁ ρ₂ : ℝ} {c₁ c₂ : Fin R → ℝ}
    (h1 : HasPositiveJetProfile R (lam₁ / 2) ρ₁ c₁)
    (h2 : HasPositiveJetProfile R (lam₂ / 2) ρ₂ c₂)
    (hdata2 : ∀ᶠ t : ℝ in atTop,
      gibbsExpectation (nondegenerateJet R lam₁ c₁) t (fun x ↦ x ^ 2) =
      gibbsExpectation (nondegenerateJet R lam₂ c₂) t (fun x ↦ x ^ 2))
    (hdataR : ∀ i : Fin R, ∀ᶠ t : ℝ in atTop,
      gibbsExpectation (nondegenerateJet R lam₁ c₁) t
        (fun x ↦ x ^ (2 + (i.1 + 1))) =
      gibbsExpectation (nondegenerateJet R lam₂ c₂) t
        (fun x ↦ x ^ (2 + (i.1 + 1)))) :
    lam₁ = lam₂ ∧ c₁ = c₂ := by
  have h := polynomialJet_recovery_variableBase (k := 1) le_rfl
    h1 h2 hdata2 hdataR
  exact ⟨by linarith [h.1], h.2⟩

/-- The `k = 1` reference second-moment constant: `M₂(λ/2) = 1/λ`. -/
theorem reference_secondMoment_k_one
    {lam : ℝ} (hlam : 0 < lam) :
    (∫ u : ℝ, u ^ 2 * Real.exp (-(lam / 2 * u ^ (2 * 1)))) /
      (∫ u : ℝ, Real.exp (-(lam / 2 * u ^ (2 * 1)))) = 1 / lam := by
  rw [reference_secondMoment_gamma le_rfl (by positivity)]
  have h32 : ((2 * 1 + 1 : ℝ) / ((2 * 1 : ℕ) : ℝ)) = 3 / 2 := by
    norm_num
  have h12 : ((1 : ℝ) / ((2 * 1 : ℕ) : ℝ)) = 1 / 2 := by
    norm_num
  rw [h32, h12]
  have hΓ32 : Real.Gamma (3 / 2) = 1 / 2 * Real.Gamma (1 / 2) := by
    rw [show (3 / 2 : ℝ) = 1 / 2 + 1 by norm_num,
      Real.Gamma_add_one (by norm_num : (1 / 2 : ℝ) ≠ 0)]
  rw [hΓ32, Real.Gamma_one_half_eq]
  have hπ : Real.sqrt π ≠ 0 := by
    have : (0 : ℝ) < Real.sqrt π := Real.sqrt_pos.mpr Real.pi_pos
    exact this.ne'
  have hexp : ((1 : ℝ) / ((1 : ℕ) : ℝ)) = (1 : ℝ) := by norm_num
  rw [hexp, Real.rpow_one]
  field_simp

/-- **B5: the second-moment rate** — `t·⟨x²⟩_t → 1/λ` for the
nondegenerate jet, the germbij Theorem 3.1 opening move. -/
theorem gibbs_secondMoment_rate
    {R : ℕ} {lam ρ : ℝ} {c : Fin R → ℝ}
    (h : HasPositiveJetProfile R (lam / 2) ρ c)
    (hlam : 0 < lam) :
    Tendsto (fun t : ℝ ↦ t *
      gibbsExpectation (nondegenerateJet R lam c) t (fun x ↦ x ^ 2))
      atTop (𝓝 (1 / lam)) := by
  -- The scale map t ↦ (√t)⁻¹ carries atTop to 𝓝[>] 0.
  have hqmap : Tendsto (fun t : ℝ ↦ (Real.sqrt t)⁻¹)
      atTop (𝓝[>] (0 : ℝ)) := by
    apply tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within
    · exact Real.tendsto_sqrt_atTop.inv_tendsto_atTop
    · filter_upwards [eventually_gt_atTop (0 : ℝ)] with t ht
      exact Set.mem_Ioi.mpr (inv_pos.mpr (Real.sqrt_pos.mpr ht))
  -- Compose with the second-moment limit, then rewrite the constant.
  have hlim := (jet_secondMoment_tendsto (k := 1) le_rfl h).comp hqmap
  rw [reference_secondMoment_k_one hlam] at hlim
  -- The eventual identity t·⟨x²⟩_t = F₂((√t)⁻¹).
  have hev : (fun t : ℝ ↦ normalizedJetMoment 1 R 2 (lam / 2)
      ((Real.sqrt t)⁻¹) c) =ᶠ[atTop] fun t : ℝ ↦ t *
      gibbsExpectation (nondegenerateJet R lam c) t
        (fun x ↦ x ^ 2) := by
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with t ht
    have hst : (0 : ℝ) < Real.sqrt t := Real.sqrt_pos.mpr ht
    have hq0 : (0 : ℝ) < (Real.sqrt t)⁻¹ := inv_pos.mpr hst
    have hqt : t * ((Real.sqrt t)⁻¹) ^ (2 * 1) = 1 := by
      set st : ℝ := Real.sqrt t with hst_def
      have hst2 : st * st = t := Real.mul_self_sqrt ht.le
      have hstne : st ≠ 0 := hst.ne'
      rw [pow_mul, pow_one, ← hst2]
      field_simp
    have hs := gibbsExpectation_polynomialJet_scale
      (t := t) 2 le_rfl h hq0 hqt
    unfold nondegenerateJet
    rw [hs]
    have hq2 : ((Real.sqrt t)⁻¹) ^ 2 = t⁻¹ := by
      set st : ℝ := Real.sqrt t with hst_def
      have hst2 : st * st = t := Real.mul_self_sqrt ht.le
      have hstne : st ≠ 0 := hst.ne'
      rw [← hst2]
      field_simp
    rw [hq2]
    field_simp
  exact hlim.congr' hev

end Laplace.OneD
