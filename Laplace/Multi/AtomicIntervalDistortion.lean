/-
Copyright (c) 2026 Timaeus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Timaeus
-/
import Laplace.Multi.ScalarResponseRay

/-!
# Finite data motion, infinite response motion

A one-dimensional charged interval: the reference law `νA` on `ℕ` puts mass `1/2` at the point `0`
(where `S = 0`) and masses `w_{k+1} = 1/(2(k+1)(k+2))` at the points `k + 1` (where `S = 2^{−k}`),
so the atoms of the statistic accumulate at the endpoint `0` of the moment interval `[0, 1]` with
`Σ_k √w_{k+1} = ∞`. The data direction `h = 1_{\{0\}}` is bounded and its data path
`ρ_t = νA.tilted (t h)` merely reweights the two conditional laws on `{0}` and its complement; its
means decrease to `0`, the endpoint response. In one dimension the response path is at least as long
as the natural ray towards the endpoint (`ScalarResponseRay`), and the dyadic shell masses of that
ray are exactly the `w_{k+1}`, whose square roots are not summable; hence the response path has
infinite Fisher length (`tendsto_responseLength_atTop`), while the data path has length
`2 arccos √(1/2) < π`. No finite constant can bound the response length by the data length.
-/

open MeasureTheory Filter Topology Set Real

namespace Laplace.Multi

section General

variable {X : Type*} [MeasurableSpace X] [MeasurableSingletonClass X]

/-- The mass of a singleton under a tilt. -/
theorem measureReal_tilted_singleton (μ : Measure X) (f : X → ℝ) (x : X) :
    (μ.tilted f).real {x} = μ.real {x} * (exp (f x) / ∫ y, exp (f y) ∂μ) := by
  rw [measureReal_def, tilted_apply_eq_ofReal_integral' f (measurableSet_singleton x),
    integral_singleton, ENNReal.toReal_ofReal, smul_eq_mul]
  exact mul_nonneg measureReal_nonneg
    (div_nonneg (exp_pos _).le (integral_nonneg fun _ ↦ (exp_pos _).le))

/-- **Two charged atoms force a positive variance**:
`Var_P f ≥ P{x₀} P{x₁} (f x₀ − f x₁)² / (P{x₀} + P{x₁})`. -/
theorem two_atoms_le_lawCov_self (P : Measure X) [IsProbabilityMeasure P] {f : X → ℝ}
    (hf : Bdd f) {x₀ x₁ : X} (hne : x₀ ≠ x₁) :
    P.real {x₀} * P.real {x₁} * (f x₀ - f x₁) ^ 2 / (P.real {x₀} + P.real {x₁}) ≤
      lawCov P f f := by
  set m := ∫ y, f y ∂P with hm
  have hint : Integrable (fun x ↦ (f x - m) * (f x - m)) P :=
    integrable_of_bdd_prob P ((hf.sub (Bdd.const m)).mul (hf.sub (Bdd.const m)))
  have h1 : ∫ x in ({x₀, x₁} : Set X), (f x - m) * (f x - m) ∂P ≤ lawCov P f f := by
    rw [lawCov_eq_integral_centred P hf hf, ← hm]
    exact setIntegral_le_integral hint (ae_of_all _ fun x ↦ mul_self_nonneg _)
  have h2 : ∫ x in ({x₀, x₁} : Set X), (f x - m) * (f x - m) ∂P =
      P.real {x₀} * ((f x₀ - m) * (f x₀ - m)) + P.real {x₁} * ((f x₁ - m) * (f x₁ - m)) := by
    rw [Set.insert_eq, setIntegral_union (Set.disjoint_singleton.2 hne) (measurableSet_singleton x₁)
      hint.integrableOn hint.integrableOn, integral_singleton, integral_singleton, smul_eq_mul,
      smul_eq_mul]
  refine le_trans ?_ (h2 ▸ h1)
  have ha : 0 ≤ P.real {x₀} := measureReal_nonneg
  have hb : 0 ≤ P.real {x₁} := measureReal_nonneg
  rcases eq_or_lt_of_le (add_nonneg ha hb) with h0 | hpos
  · rw [← h0, div_zero]
    exact add_nonneg (mul_nonneg ha (mul_self_nonneg _)) (mul_nonneg hb (mul_self_nonneg _))
  · rw [div_le_iff₀ hpos]
    nlinarith [sq_nonneg (P.real {x₀} * (f x₀ - m) + P.real {x₁} * (f x₁ - m)), mul_nonneg ha hb]

end General

namespace AtomicInterval

/-- The atom masses `w_0 = 1/2`, `w_{k+1} = 1/(2(k+1)(k+2))`. -/
noncomputable def atomW : ℕ → ℝ
  | 0 => 1 / 2
  | k + 1 => 1 / (2 * ((k : ℝ) + 1) * ((k : ℝ) + 2))

theorem atomW_pos (k : ℕ) : 0 < atomW k := by
  cases k with
  | zero => norm_num [atomW]
  | succ k => unfold atomW; positivity

theorem atomW_succ (k : ℕ) :
    atomW (k + 1) = 1 / (2 * ((k : ℝ) + 1)) - 1 / (2 * ((k : ℝ) + 2)) := by
  unfold atomW
  field_simp
  ring

theorem sum_range_atomW_succ (n : ℕ) :
    ∑ i ∈ Finset.range n, atomW (i + 1) = 1 / 2 - 1 / (2 * ((n : ℝ) + 1)) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Finset.sum_range_succ, ih, atomW_succ]
    push_cast
    ring

theorem hasSum_atomW_succ : HasSum (fun k ↦ atomW (k + 1)) (1 / 2) := by
  rw [hasSum_iff_tendsto_nat_of_nonneg (fun k ↦ (atomW_pos _).le)]
  simp_rw [sum_range_atomW_succ]
  have h : Tendsto (fun n : ℕ ↦ 1 / (2 * ((n : ℝ) + 1))) atTop (𝓝 0) := by
    have := (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).div_const 2
    refine (this.congr' (Eventually.of_forall fun n ↦ ?_)).trans (by simp)
    rw [div_div, mul_comm]
  simpa using (tendsto_const_nhds (x := (1 / 2 : ℝ))).sub h

theorem hasSum_atomW : HasSum atomW 1 := by
  have h := hasSum_atomW_succ
  rw [show (1 / 2 : ℝ) = 1 - ∑ i ∈ Finset.range 1, atomW i by simp [atomW]; norm_num] at h
  exact (hasSum_nat_add_iff' 1).1 h

/-- The reference law: atoms at every natural number. -/
noncomputable def νA : Measure ℕ := Measure.sum fun k ↦ ENNReal.ofReal (atomW k) • Measure.dirac k

theorem νA_singleton (k : ℕ) : νA {k} = ENNReal.ofReal (atomW k) := by
  rw [νA, Measure.sum_apply _ (measurableSet_singleton k), tsum_eq_single k]
  · rw [Measure.smul_apply, Measure.dirac_apply_of_mem (Set.mem_singleton k), smul_eq_mul, mul_one]
  · intro j hj
    rw [Measure.smul_apply, Measure.dirac_apply' _ (measurableSet_singleton k),
      Set.indicator_of_notMem (by simpa using hj), smul_zero]

theorem νA_real_singleton (k : ℕ) : νA.real {k} = atomW k := by
  rw [measureReal_def, νA_singleton, ENNReal.toReal_ofReal (atomW_pos k).le]

instance : IsProbabilityMeasure νA := ⟨by
  rw [νA, Measure.sum_apply _ MeasurableSet.univ]
  simp only [Measure.smul_apply, measure_univ, smul_eq_mul, mul_one]
  rw [← ENNReal.ofReal_tsum_of_nonneg (fun k ↦ (atomW_pos k).le) hasSum_atomW.summable,
    hasSum_atomW.tsum_eq, ENNReal.ofReal_one]⟩

/-- The statistic: `S 0 = 0`, `S (k+1) = 2^{−k}`. -/
noncomputable def atomS : ℕ → ℝ
  | 0 => 0
  | k + 1 => (1 / 2) ^ k

theorem atomS_nonneg (k : ℕ) : 0 ≤ atomS k := by
  cases k with
  | zero => simp [atomS]
  | succ k => unfold atomS; positivity

theorem atomS_le_one (k : ℕ) : atomS k ≤ 1 := by
  cases k with
  | zero => simp [atomS]
  | succ k => exact pow_le_one₀ (by norm_num) (by norm_num)

theorem atomS_succ_pos (k : ℕ) : 0 < atomS (k + 1) := by unfold atomS; positivity

theorem atomS_eq_zero_iff (k : ℕ) : atomS k = 0 ↔ k = 0 := by
  cases k with
  | zero => simp [atomS]
  | succ k => simp only [(atomS_succ_pos k).ne', Nat.succ_ne_zero]

/-- The statistic as a family indexed by `Unit`. -/
noncomputable def SA : Unit → ℕ → ℝ := fun _ ↦ atomS

theorem bdd_SA : ∀ j, Bdd (SA j) := fun _ ↦
  ⟨measurable_of_countable _, 1, fun k ↦ by
    rw [SA, abs_of_nonneg (atomS_nonneg k)]; exact atomS_le_one k⟩

/-- The data direction `h = 1_{\{0\}}`. -/
def hA : ℕ → ℝ := fun k ↦ if k = 0 then 1 else 0

theorem bdd_hA : Bdd hA :=
  ⟨measurable_of_countable _, 1, fun k ↦ by unfold hA; split_ifs <;> simp⟩

theorem hA_le_one (k : ℕ) : hA k ≤ 1 := by unfold hA; split_ifs <;> norm_num

theorem topSet_eq : {k : ℕ | hA k = 1} = {0} := by
  ext k
  simp only [hA, Set.mem_ofPred_eq, Set.mem_singleton_iff]
  split_ifs with h <;> simp [h]

/-- The scalar family of tilts. -/
local notation "Pf" θ =>
  familyMeasure νA (fun _ ↦ (1 : ℝ)) (fun _ ↦ (0 : ℝ)) SA 1 (fun _ : Unit ↦ θ)

theorem family_real_singleton_pos (θ : ℝ) (k : ℕ) : 0 < (Pf θ).real {k} := by
  rw [family_scalar_eq_tilted νA bdd_SA θ, measureReal_tilted_singleton, νA_real_singleton]
  have hint : Integrable (fun x ↦ exp (θ * -SA default x)) νA :=
    integrable_exp_of_bdd νA ((bdd_neg (bdd_SA default)).const_mul θ)
  exact mul_pos (atomW_pos k) (div_pos (exp_pos _) (integral_exp_pos hint))

/-- The family has positive variance everywhere. -/
theorem var_pos (θ : ℝ) : 0 < lawCov (Pf θ) (SA default) (SA default) := by
  have := isProbabilityMeasure_family_scalar νA bdd_SA θ
  have h := two_atoms_le_lawCov_self (Pf θ) (bdd_SA default) (x₀ := 0) (x₁ := 1) (by norm_num)
  refine lt_of_lt_of_le ?_ h
  have h0 := family_real_singleton_pos θ 0
  have h1 := family_real_singleton_pos θ 1
  have e : SA default 0 - SA default 1 = -1 := by simp [SA, atomS]
  rw [e]
  positivity

/-- The data means converge to the endpoint `0`. -/
theorem tendsto_mean_zero :
    Tendsto (fun t ↦ ∫ x, SA default x ∂νA.tilted (fun x ↦ t * hA x)) atTop (𝓝 0) := by
  have hp : 0 < νA.real {x | hA x = 1} := by
    rw [topSet_eq, νA_real_singleton]; exact atomW_pos 0
  have h := tendsto_integral_dataPath_atTop νA bdd_hA hA_le_one hp (bdd_SA default)
  rw [topSet_eq, integral_singleton] at h
  simpa [SA, atomS] using h

/-- Every family mean is positive. -/
theorem scalarMean_pos (θ : ℝ) : 0 < scalarMean SA νA θ := by
  have := isProbabilityMeasure_family_scalar νA bdd_SA θ
  have h : ∫ x in ({1} : Set ℕ), SA default x ∂(Pf θ) ≤ scalarMean SA νA θ :=
    setIntegral_le_integral (integrable_of_bdd_prob _ (bdd_SA default))
      (ae_of_all _ fun x ↦ atomS_nonneg x)
  refine lt_of_lt_of_le ?_ h
  rw [integral_singleton, smul_eq_mul]
  have e : SA default 1 = 1 := by simp [SA, atomS]
  rw [e, mul_one]
  exact family_real_singleton_pos θ 1

theorem tendsto_scalarTheta : Tendsto (scalarTheta νA bdd_SA bdd_hA) atTop atTop :=
  tendsto_scalarTheta_atTop νA bdd_SA bdd_hA var_pos tendsto_mean_zero scalarMean_pos

/-- The normal direction towards the endpoint. -/
def uA : Unit → ℝ := fun _ ↦ -1

theorem dirLoss_uA (x : ℕ) : dirLoss SA uA x = -atomS x := by
  rw [dirLoss_unique]; simp [uA, SA]

theorem slack_eq (x : ℕ) : (0 : ℝ) - dirLoss SA uA x = atomS x := by rw [dirLoss_uA]; ring

theorem famWeight_zero (x : ℕ) : famWeight SA 0 x = 1 := by
  rw [famWeight, dirLoss_unique]; simp

/-- The dyadic shells of the slack are the single atoms. -/
theorem dyadicShell_eq (k : ℕ) : dyadicShell (fun x ↦ (0 : ℝ) - dirLoss SA uA x) 1 k = {k + 1} := by
  ext x
  simp only [dyadicShell, Set.mem_preimage, Set.mem_Ioc, slack_eq, Set.mem_singleton_iff]
  cases x with
  | zero =>
    simp only [atomS, Nat.zero_ne_add_one, iff_false, not_and, not_le]
    intro h
    exact absurd h (not_lt.2 (by positivity))
  | succ j =>
    simp only [atomS, Nat.add_right_cancel_iff]
    simp only [← one_div_pow]
    constructor
    · rintro ⟨h1, h2⟩
      have := (pow_lt_pow_iff_right_of_lt_one₀ (by norm_num : (0 : ℝ) < 1 / 2) (by norm_num)).1 h1
      have := (pow_le_pow_iff_right_of_lt_one₀ (by norm_num : (0 : ℝ) < 1 / 2) (by norm_num)).1 h2
      omega
    · rintro rfl
      exact ⟨pow_lt_pow_right_of_lt_one₀ (by norm_num) (by norm_num) (Nat.lt_succ_self _), le_rfl⟩

theorem shellMass_eq (k : ℕ) :
    shellMass νA (famWeight SA 0) (fun x ↦ (0 : ℝ) - dirLoss SA uA x) 1 k =
      ENNReal.ofReal (atomW (k + 1)) := by
  rw [shellMass, dyadicShell_eq, lintegral_singleton, famWeight_zero, νA_singleton]
  simp

theorem sqrt_atomW_ge (k : ℕ) : 1 / (2 * ((k : ℝ) + 2)) ≤ √(atomW (k + 1)) := by
  rw [Real.le_sqrt (by positivity) (atomW_pos _).le]
  unfold atomW
  rw [div_pow, one_pow, div_le_div_iff₀ (by positivity) (by positivity)]
  nlinarith [(Nat.cast_nonneg k : (0 : ℝ) ≤ k)]

theorem not_summable_shifted : ¬ Summable (fun k : ℕ ↦ 1 / (2 * ((k : ℝ) + 2))) := by
  intro h
  have h2 : Summable (fun k : ℕ ↦ 1 / ((k : ℝ) + 2)) := by
    refine (h.mul_left 2).congr fun k ↦ ?_
    field_simp
  have h3 : Summable (fun n : ℕ ↦ 1 / (n : ℝ)) := by
    refine (summable_nat_add_iff 2).1 (h2.congr fun k ↦ ?_)
    push_cast
    ring
  exact not_summable_one_div_natCast h3

theorem tsum_shifted_eq_top :
    (∑' k : ℕ, ENNReal.ofReal (1 / (2 * ((k : ℝ) + 2)))) = ⊤ := by
  by_contra hne
  have hs : Summable (fun k : ℕ ↦ Real.toNNReal (1 / (2 * ((k : ℝ) + 2)))) :=
    ENNReal.tsum_coe_ne_top_iff_summable.1 hne
  have hs' : Summable (fun k : ℕ ↦ 1 / (2 * ((k : ℝ) + 2))) := by
    refine (NNReal.summable_coe.2 hs).congr fun k ↦ ?_
    rw [Real.coe_toNNReal _ (by positivity)]
  exact not_summable_shifted hs'

/-- **The shell series diverges.** -/
theorem tsum_sqrt_shellMass_eq_top :
    (∑' k, shellMass νA (famWeight SA 0) (fun x ↦ (0 : ℝ) - dirLoss SA uA x) 1 k ^ (1 / 2 : ℝ)) =
      ⊤ := by
  simp_rw [shellMass_eq]
  refine top_unique ?_
  calc (⊤ : ENNReal) = ∑' k : ℕ, ENNReal.ofReal (1 / (2 * ((k : ℝ) + 2))) :=
        tsum_shifted_eq_top.symm
    _ ≤ ∑' k, ENNReal.ofReal (atomW (k + 1)) ^ (1 / 2 : ℝ) := ENNReal.tsum_le_tsum fun k ↦ ?_
  rw [ENNReal.ofReal_rpow_of_nonneg (atomW_pos _).le (by norm_num), ← Real.sqrt_eq_rpow]
  exact ENNReal.ofReal_le_ofReal (sqrt_atomW_ge k)

theorem ae_dirLoss_uA_le : ∀ᵐ x ∂νA, dirLoss SA uA x ≤ 0 :=
  ae_of_all _ fun x ↦ by rw [dirLoss_uA]; linarith [atomS_nonneg x]

theorem faceSet_eq : {x : ℕ | dirLoss SA uA x = 0} = {0} := by
  ext x
  simp [dirLoss_uA, atomS_eq_zero_iff]

theorem endpointMass_pos : 0 < νA.real {x | dirLoss SA uA x = 0} := by
  rw [faceSet_eq, νA_real_singleton]
  exact atomW_pos 0

theorem slack_le_one (x : ℕ) : (0 : ℝ) - dirLoss SA uA x ≤ 1 := by
  rw [slack_eq]
  exact atomS_le_one x

/-- **The ray towards the endpoint has infinite Fisher length.** -/
theorem lintegral_sqrt_raySpeedSq_eq_top :
    (∫⁻ t in Ioi (0 : ℝ), ENNReal.ofReal (√(raySpeedSq SA νA (0 : Unit → ℝ) uA t))) = ⊤ := by
  by_contra hne
  have hlt := lt_top_iff_ne_top.2 hne
  have := (lintegral_sqrt_raySpeedSq_lt_top_iff bdd_SA νA (θ := 0) (u := uA) (β := 0)
    ae_dirLoss_uA_le endpointMass_pos one_pos slack_le_one).1 hlt
  rw [tsum_sqrt_shellMass_eq_top] at this
  exact absurd this (lt_irrefl _)

/-- **The response path from the featureless law has infinite Fisher length**: no bound on the
window lengths. -/
theorem not_length_bounded :
    ¬ ∃ I : ℝ, ∀ b, 0 ≤ b → ∫ t in (0 : ℝ)..b, √(responseSpeedSq bdd_SA νA bdd_hA t) ≤ I := by
  rintro ⟨I, hI⟩
  have h := lintegral_sqrt_raySpeedSq_lt_top_of_length_le νA bdd_SA bdd_hA var_pos
    tendsto_scalarTheta hI
  have e : (fun _ : Unit ↦ (-1 : ℝ)) = uA := rfl
  rw [e, lintegral_sqrt_raySpeedSq_eq_top] at h
  exact absurd h (lt_irrefl _)

theorem continuous_sqrt_responseSpeedSq :
    Continuous fun t ↦ √(responseSpeedSq bdd_SA νA bdd_hA t) := by
  have e : (fun t ↦ √(responseSpeedSq bdd_SA νA bdd_hA t)) = fun t ↦
      |scalarThetaVel νA bdd_SA bdd_hA t| *
        scalarFisherWeight SA νA (scalarTheta νA bdd_SA bdd_hA t) :=
    funext (sqrt_responseSpeedSq_eq νA bdd_SA bdd_hA)
  rw [e]
  exact (continuous_scalarThetaVel νA bdd_SA bdd_hA var_pos).abs.mul
    ((continuous_scalarFisherWeight νA bdd_SA).comp (continuous_scalarTheta νA bdd_SA bdd_hA))

/-- **Finite data motion, infinite response motion**: the Fisher length of the response path
`t ↦ q_{m_t}` from the featureless law diverges. -/
theorem tendsto_responseLength_atTop :
    Tendsto (fun b ↦ ∫ t in (0 : ℝ)..b, √(responseSpeedSq bdd_SA νA bdd_hA t)) atTop atTop := by
  have hc := continuous_sqrt_responseSpeedSq
  refine tendsto_atTop_atTop_of_monotone (fun b b' hbb' ↦ ?_) fun I ↦ ?_
  · rw [← intervalIntegral.integral_add_adjacent_intervals (hc.intervalIntegrable 0 b)
      (hc.intervalIntegrable b b')]
    exact le_add_of_nonneg_right
      (intervalIntegral.integral_nonneg hbb' fun _ _ ↦ Real.sqrt_nonneg _)
  · by_contra hcon
    exact not_length_bounded ⟨I, fun b _ ↦ (not_le.1 (not_exists.1 hcon b)).le⟩

end AtomicInterval

end Laplace.Multi
