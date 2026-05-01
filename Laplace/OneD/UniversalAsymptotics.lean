import Laplace.Gibbs
import Laplace.OneD.Anharmonic
import Laplace.OneD.NearDegenerate
import Laplace.OneD.IntegralRemainder

/-!
# Asymptotics of the universal scaling function `f_1`

The universal scaling function for the near-degenerate posterior, defined in
`NearDegenerate.lean`, is `f_n(T) := ⟨y^{2n}⟩_T` against
`V(y) = y²/2 + y⁴/24` (the universal potential, equal to
`anharmonicPotential 1 0 1`). This file formalises the *large-T* asymptotic
at `n = 1`: the standard Laplace expansion against the quadratic core gives
`T · f_1(T) → 1` as `T → ∞`, with rate `O(1/T)`.

The proof bridges to the seabed's `I_0_asymptotic` and `I_2_asymptotic` for
the anharmonic potential at `α = 0`, `λ = γ = 1` (which is exactly `V`).
The discriminant condition `α² < 3λγ` becomes `0 < 3`, trivially.

## Headline

* `gibbsExpectation_universal_sq_large_t_rate`:
    `∃ K T₀, 0 ≤ K ∧ 1 ≤ T₀ ∧ ∀ T ≥ T₀, |T · ⟨y²⟩_{V, T} - 1| ≤ K / T`.
* `gibbsExpectation_universal_sq_tendsto`:
    Tendsto-form corollary, `T · ⟨y²⟩_{V, T} → 1` at `atTop`.

## Tide-step provenance

Tide step 4, formalised on `tide/f1-large-t` (branched off `main`). See
`sri/projects/automation/log/2026-05-01-tide-fn-asymptotics.md`.
-/

open Real MeasureTheory

namespace Laplace.OneD

/-- The discriminant condition `α² < 3·λ·γ` of the seabed's anharmonic family
holds trivially for the universal potential `V = anharmonicPotential 1 0 1`. -/
private lemma universal_disc : (0 : ℝ) ^ 2 < 3 * 1 * 1 := by norm_num

/-- **Rate-aware large-T asymptotic for the universal `f_1`.** For
`V(y) = y²/2 + y⁴/24` and `f_1(T) := ⟨y²⟩_{V, T}`,
`|T · f_1(T) - 1| ≤ K / T` for some constant `K ≥ 0` and all sufficiently
large `T`. -/
theorem gibbsExpectation_universal_sq_large_t_rate :
    ∃ K T₀ : ℝ, 0 ≤ K ∧ 1 ≤ T₀ ∧ ∀ {T : ℝ}, T₀ ≤ T →
      |T * Laplace.gibbsExpectation universalPotential T (fun y => y ^ 2) - 1|
        ≤ K / T := by
  obtain ⟨K₀, hK₀_nn, hI0⟩ :=
    I_0_asymptotic (lam := 1) (alpha := 0) (gamma := 1)
      (by norm_num) (by norm_num) universal_disc
  obtain ⟨K₂, hK₂_nn, hI2⟩ :=
    I_2_asymptotic (lam := 1) (alpha := 0) (gamma := 1)
      (by norm_num) (by norm_num) universal_disc
  set a : ℝ := Real.sqrt (2 * Real.pi) with ha_def
  have ha_pos : 0 < a := by positivity
  set T₀ : ℝ := max 1 (1 + 2 * K₀ / a) with hT₀_def
  have hT₀_ge_one : (1 : ℝ) ≤ T₀ := le_max_left _ _
  have hT₀_ge_other : 1 + 2 * K₀ / a ≤ T₀ := le_max_right _ _
  refine ⟨2 * (K₀ + K₂) / a, T₀, by positivity, hT₀_ge_one, ?_⟩
  intro T hT
  have hT_ge_one : (1 : ℝ) ≤ T := le_trans hT₀_ge_one hT
  have hT_pos : (0 : ℝ) < T := by linarith
  have hT_ne : T ≠ 0 := hT_pos.ne'
  have hsqrt_T_pos : (0 : ℝ) < Real.sqrt T := Real.sqrt_pos.mpr hT_pos
  have hsqrt_T_ne : Real.sqrt T ≠ 0 := hsqrt_T_pos.ne'
  have hsq : Real.sqrt T * Real.sqrt T = T := Real.mul_self_sqrt hT_pos.le
  have hI0_T := hI0 hT_ge_one
  have hI2_T := hI2 hT_ge_one
  simp only [one_mul] at hI0_T hI2_T
  set D : ℝ := ∫ x : ℝ, Real.exp (-(T * anharmonicPotential 1 0 1 x)) with hD_def
  set N : ℝ := ∫ x : ℝ, x ^ 2 * Real.exp (-(T * anharmonicPotential 1 0 1 x)) with hN_def
  -- Rescaled bounds: |√T · D - a| ≤ K₀/T and |T√T · N - a| ≤ K₂/T.
  have hδ : |Real.sqrt T * D - a| ≤ K₀ / T := by
    have hkey : Real.sqrt T * D - a = Real.sqrt T * (D - a / Real.sqrt T) := by
      field_simp
    rw [hkey, abs_mul, abs_of_pos hsqrt_T_pos]
    have hrhs_eq : K₀ / T = Real.sqrt T * (K₀ / (T * Real.sqrt T)) := by
      field_simp
    rw [hrhs_eq]
    exact mul_le_mul_of_nonneg_left hI0_T hsqrt_T_pos.le
  have hε : |T * Real.sqrt T * N - a| ≤ K₂ / T := by
    have hTsqrt_pos : (0 : ℝ) < T * Real.sqrt T := mul_pos hT_pos hsqrt_T_pos
    have hkey : T * Real.sqrt T * N - a = T * Real.sqrt T * (N - a / (T * Real.sqrt T)) := by
      field_simp
    rw [hkey, abs_mul, abs_of_pos hTsqrt_pos]
    have hrhs_eq : K₂ / T = T * Real.sqrt T * (K₂ / (T * Real.sqrt T * T)) := by
      field_simp
    rw [hrhs_eq]
    exact mul_le_mul_of_nonneg_left hI2_T hTsqrt_pos.le
  -- Lower bound on √T · D: K₀/T ≤ a/2 ⟹ √T · D ≥ a/2.
  have hK₀T_le : K₀ / T ≤ a / 2 := by
    rcases lt_or_eq_of_le hK₀_nn with hK₀_pos | hK₀_zero
    · rw [div_le_div_iff₀ hT_pos (by norm_num : (0:ℝ) < 2)]
      have hT_big : 1 + 2 * K₀ / a ≤ T := le_trans hT₀_ge_other hT
      have h2K₀_le : 2 * K₀ ≤ a * (T - 1) := by
        have hsub : 2 * K₀ / a ≤ T - 1 := by linarith
        have : a * (2 * K₀ / a) ≤ a * (T - 1) :=
          mul_le_mul_of_nonneg_left hsub ha_pos.le
        have heq : a * (2 * K₀ / a) = 2 * K₀ := by field_simp
        linarith
      nlinarith
    · rw [← hK₀_zero, zero_div]; linarith
  have hsqrtTD_lb : a / 2 ≤ Real.sqrt T * D := by
    have habs := abs_sub_le_iff.mp hδ
    linarith [habs.1, habs.2]
  have hsqrtTD_pos : (0 : ℝ) < Real.sqrt T * D := by linarith
  have hD_pos : 0 < D := by
    rcases lt_or_ge 0 D with h | h
    · exact h
    · exfalso
      have : Real.sqrt T * D ≤ 0 := mul_nonpos_iff.mpr (Or.inl ⟨hsqrt_T_pos.le, h⟩)
      linarith
  have hD_ne : D ≠ 0 := hD_pos.ne'
  unfold Laplace.gibbsExpectation Laplace.partitionFunction
  change |T * (N / D) - 1| ≤ 2 * (K₀ + K₂) / a / T
  have hreshape : T * (N / D) = (T * Real.sqrt T * N) / (Real.sqrt T * D) := by
    field_simp
  rw [hreshape]
  -- Reframe in (a + perturbation) form.
  set ε : ℝ := T * Real.sqrt T * N - a with hε_def
  set δ : ℝ := Real.sqrt T * D - a with hδ_def
  have hN_form : T * Real.sqrt T * N = a + ε := by simp [hε_def]
  have hD_form : Real.sqrt T * D = a + δ := by simp [hδ_def]
  rw [hN_form, hD_form]
  have h_aδ_pos : 0 < a + δ := by
    rw [show a + δ = Real.sqrt T * D from (hD_form).symm]
    exact hsqrtTD_pos
  have h_aδ_lb : a / 2 ≤ a + δ := by
    rw [show a + δ = Real.sqrt T * D from (hD_form).symm]
    exact hsqrtTD_lb
  have h_a2_pos : (0 : ℝ) < a / 2 := by linarith
  have hratio_eq : (a + ε) / (a + δ) - 1 = (ε - δ) / (a + δ) := by
    field_simp
    ring
  rw [hratio_eq, abs_div, abs_of_pos h_aδ_pos]
  have h_num_bound : |ε - δ| ≤ (K₀ + K₂) / T := by
    calc |ε - δ| ≤ |ε| + |δ| := abs_sub _ _
      _ ≤ K₂ / T + K₀ / T := add_le_add hε hδ
      _ = (K₀ + K₂) / T := by ring
  have h_target_eq : 2 * (K₀ + K₂) / a / T = ((K₀ + K₂) / T) / (a / 2) := by
    field_simp
  rw [h_target_eq]
  -- Two-step calc: |ε-δ|/(a+δ) ≤ ((K₀+K₂)/T)/(a+δ) ≤ ((K₀+K₂)/T)/(a/2).
  calc |ε - δ| / (a + δ)
      ≤ ((K₀ + K₂) / T) / (a + δ) :=
        div_le_div_of_nonneg_right h_num_bound h_aδ_pos.le
    _ ≤ ((K₀ + K₂) / T) / (a / 2) := by
        have h_num_nn : (0 : ℝ) ≤ (K₀ + K₂) / T :=
          div_nonneg (by linarith [hK₀_nn, hK₂_nn]) hT_pos.le
        exact div_le_div_of_nonneg_left h_num_nn h_a2_pos h_aδ_lb

/-- **Tendsto corollary.** `T · f_1(T) → 1` as `T → ∞`. -/
theorem gibbsExpectation_universal_sq_tendsto :
    Filter.Tendsto
      (fun T : ℝ => T * Laplace.gibbsExpectation universalPotential T (fun y => y ^ 2))
      Filter.atTop (nhds 1) := by
  obtain ⟨K, T₀, hK_nn, hT₀_ge_one, hbound⟩ :=
    gibbsExpectation_universal_sq_large_t_rate
  rw [Metric.tendsto_atTop]
  intro ε hε
  -- Choose T large enough that K / T < ε.
  rcases lt_or_eq_of_le hK_nn with hK_pos | hK_zero
  · refine ⟨max T₀ (K / ε + 1), ?_⟩
    intro T hT
    have hT_ge_T₀ : T₀ ≤ T := le_trans (le_max_left _ _) hT
    have hT_ge_other : K / ε + 1 ≤ T := le_trans (le_max_right _ _) hT
    have hT_pos : (0 : ℝ) < T := by linarith [le_trans hT₀_ge_one hT_ge_T₀]
    have hbnd := hbound hT_ge_T₀
    -- |T · f_1(T) - 1| ≤ K/T < ε.
    rw [Real.dist_eq]
    calc |T * Laplace.gibbsExpectation universalPotential T (fun y => y ^ 2) - 1|
        ≤ K / T := hbnd
      _ < ε := by
          rw [div_lt_iff₀ hT_pos]
          have hKε_lt : K / ε < T := by linarith
          rw [div_lt_iff₀ hε] at hKε_lt
          linarith
  · -- K = 0 case: bound is trivially 0 ≤ K/T = 0/T = 0 < ε.
    refine ⟨T₀, ?_⟩
    intro T hT
    have hT_pos : (0 : ℝ) < T := by linarith [le_trans hT₀_ge_one hT]
    have hbnd := hbound hT
    rw [← hK_zero, zero_div] at hbnd
    rw [Real.dist_eq]
    linarith [abs_nonneg
      (T * Laplace.gibbsExpectation universalPotential T (fun y => y ^ 2) - 1)]

end Laplace.OneD
