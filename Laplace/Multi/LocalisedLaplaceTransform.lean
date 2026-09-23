/-
Copyright (c) 2026 Timaeus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Timaeus
-/
import Laplace.Multi.LocalisedEnergyCumulant4
import Laplace.OneD.MomentThirdOrder

/-!
# The Laplace transform of the localised energy: the Gamma(d/2, t) law as a transform statement

On E2's exact localised measure, per frame coordinate, the Laplace transform
`Λ_t(s) := ⟨exp(−s·t·ℓ)⟩_loc(t)` of the scaled energy `tℓ` is *exactly* a partition-function
ratio at the changed temperature `(1+s)t` with the same localiser,
`Λ_t(s) = Z_loc((1+s)t)/Z_loc(t)` (the localiser `g(x − x₀)²/2` is fixed in the `t·locPotential1(t)`
normalisation), hence `Λ_t(s) = (1+s)^{−1/2}·[J₀((1+s)t)/J₀(t)]·[D((1+s)t)/D(t)]` with `J₀ → √(2π)`
and the localiser denominator `D → 1`; so `|√(1+s)·Λ_t(s) − 1| ≤ K/t` and
`|Λ_t(s) − 1/√(1+s)| ≤ K/t`, uniformly over `s ≥ −1 + δ` for each fixed `δ > 0`. On E2 the
transform factorises over the frame coordinates (rotation invariance and the separable product of
partition functions), `⟨exp(−s·t·L∘A)⟩_loc = ∏ᵢ Λ_{t,i}(s)`, and
`|⟨exp(−s·t·L∘A)⟩_loc − (1/√(1+s))^d| ≤ K/t`.

`(1+s)^{−d/2}` is the Laplace transform of the `Gamma(d/2, rate 1)` law at `s`; its domain `s > −1`
is the domain of the limiting transform. By the continuity theorem for Laplace transforms (stated
in prose, not formalised here), for `d ≥ 1` the law of `t·(L∘A)` under the exact localised Gibbs
measure converges to `Gamma(d/2, 1)` — the fixed-localiser large-`t` Gamma regime of the note's §14,
complementing the cumulant hierarchy of `LocalisedEnergyInvariant`, `LocalisedEnergyCumulant3`,
`LocalisedEnergyCumulant4`. All parameters (quartic coefficients, frame, `g`, `w₀`, `d`) are fixed;
the observable is the unlocalised energy `t·(L∘A)`.
-/

open Matrix MeasureTheory Filter Topology Laplace.OneD

namespace Laplace.Multi

/-- A quotient `F((1+s)t)/F(t)` of a function with `|F(u) − L| ≤ K/u` for `u ≥ T₀` is `1 + O(1/t)`,
uniformly over `s ≥ −1 + δ`. -/
theorem scaled_ratio_rate {F : ℝ → ℝ} {L K T₀ δ : ℝ} (hL : 0 < L) (hK : 0 ≤ K) (hT₀ : 1 ≤ T₀)
    (hδ : 0 < δ) (hF : ∀ {u : ℝ}, T₀ ≤ u → |F u - L| ≤ K / u) :
    ∃ K' T : ℝ, 0 ≤ K' ∧ 1 ≤ T ∧ ∀ {t : ℝ}, T ≤ t → ∀ {s : ℝ}, -1 + δ ≤ s →
      |F ((1 + s) * t) / F t - 1| ≤ K' / t := by
  have hδ' : 1 ≤ 1 + 1 / δ := by
    have : 0 < 1 / δ := by positivity
    linarith
  have hT₀' : T₀ ≤ T₀ * (1 + 1 / δ) := le_mul_of_one_le_right (by linarith) hδ'
  have hKL : 0 ≤ 2 * K / L := by positivity
  refine ⟨2 * (K / δ) / L + 2 * |L| * K / L ^ 2, T₀ * (1 + 1 / δ) + 2 * K / L, by positivity,
    by linarith, fun {t} ht {s} hs => ?_⟩
  have ha : δ ≤ 1 + s := by linarith
  have ht0 : 0 < t := by linarith
  have htT : T₀ ≤ t := by linarith
  have hatT : T₀ ≤ (1 + s) * t := by
    have h1 : δ * (T₀ * (1 + 1 / δ)) = δ * T₀ + T₀ := by
      field_simp
    have h2 : δ * (T₀ * (1 + 1 / δ)) ≤ (1 + s) * t := by
      calc δ * (T₀ * (1 + 1 / δ)) ≤ δ * t := by gcongr; linarith
        _ ≤ (1 + s) * t := by gcongr
    rw [h1] at h2
    linarith [mul_nonneg hδ.le (show (0 : ℝ) ≤ T₀ by linarith)]
  have hFt := hF htT
  have hFat : |F ((1 + s) * t) - L| ≤ K / δ / t := by
    refine (hF hatT).trans ?_
    rw [div_div]
    exact div_le_div_of_nonneg_left hK (by positivity) (mul_le_mul_of_nonneg_right ha ht0.le)
  have hFlow : L / 2 ≤ F t := by
    have h1 : K / t ≤ L / 2 := by
      rw [div_le_iff₀ ht0]
      have h2 : 2 * K / L ≤ t := by linarith
      rw [div_le_iff₀ hL] at h2
      linarith
    have := (abs_le.mp (hFt.trans h1)).1
    linarith
  have h := ratio_rate (a := F ((1 + s) * t)) (b := F t) (a₀ := L) (L := L) hL (by positivity) hK
    ht0 hFlow hFat hFt
  rwa [div_self hL.ne'] at h

/-- `|∏ᵢ Rᵢ − 1| ≤ 2^{|s|}(∑ᵢ Kᵢ)/t` when `|Rᵢ − 1| ≤ Kᵢ/t` and `Kᵢ ≤ t`. -/
theorem prod_one_rate {ι : Type*} (s : Finset ι) (R K : ι → ℝ) {t : ℝ}
    (ht : 0 < t) (hK : ∀ i, 0 ≤ K i) (hKt : ∀ i, K i ≤ t) (h : ∀ i, |R i - 1| ≤ K i / t) :
    |∏ i ∈ s, R i - 1| ≤ 2 ^ s.card * (∑ i ∈ s, K i) / t := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert j s hj ih =>
    rw [Finset.prod_insert hj, Finset.sum_insert hj, Finset.card_insert_of_notMem hj]
    have hRj : |R j| ≤ 2 := by
      have h1 := abs_sub_abs_le_abs_sub (R j) 1
      rw [abs_one] at h1
      have h2 : K j / t ≤ 1 := by
        rw [div_le_one ht]
        exact hKt j
      linarith [h j]
    have hsum : 0 ≤ ∑ i ∈ s, K i := Finset.sum_nonneg fun i _ => hK i
    have h2n : (1 : ℝ) ≤ 2 ^ s.card := one_le_pow₀ (by norm_num)
    have e : R j * ∏ i ∈ s, R i - 1 = R j * (∏ i ∈ s, R i - 1) + (R j - 1) := by ring
    rw [e]
    calc |R j * (∏ i ∈ s, R i - 1) + (R j - 1)|
        ≤ |R j| * |∏ i ∈ s, R i - 1| + |R j - 1| := by
          rw [← abs_mul]
          exact abs_add_le _ _
      _ ≤ 2 * (2 ^ s.card * (∑ i ∈ s, K i) / t) + K j / t := by
          gcongr
          exact h j
      _ = (2 * (2 ^ s.card * ∑ i ∈ s, K i) + K j) / t := by ring
      _ ≤ 2 ^ (s.card + 1) * (K j + ∑ i ∈ s, K i) / t := by
          rw [pow_succ]
          apply div_le_div_of_nonneg_right _ ht.le
          nlinarith [mul_nonneg (hK j) (by linarith : (0 : ℝ) ≤ 2 * 2 ^ s.card - 1)]

section OneD

variable {lam alpha gamma g x₀ : ℝ} (hlam : 0 < lam) (hgamma : 0 < gamma)
  (hdisc : alpha ^ 2 < 3 * lam * gamma)
include hlam hgamma hdisc

omit hlam hgamma hdisc in
/-- The temperature change `t ↦ (1+s)t` at fixed localiser:
`e^{−stℓ} e^{−t·locPotential1(t)} = e^{−(1+s)t·locPotential1((1+s)t)}`. -/
theorem exp_locPotential1_scale {s t : ℝ} (hs : -1 < s) (ht : 0 < t) (x : ℝ) :
    Real.exp (-(s * t * anharmonicPotential lam alpha gamma x)) * Real.exp (-(t * locPotential1 lam
      alpha gamma g x₀ t x)) = Real.exp (-((1 + s) * t * locPotential1 lam alpha gamma g x₀ ((1 + s)
      * t) x)) := by
  have ha : 0 < 1 + s := by linarith
  have h1 : (1 + s) * t ≠ 0 := (mul_pos ha ht).ne'
  rw [← Real.exp_add]
  congr 1
  unfold locPotential1
  field_simp
  ring

omit hlam hgamma hdisc in
/-- **The Laplace transform is a partition-function ratio**:
`⟨e^{−stℓ}⟩_loc(t) = Z_loc((1+s)t)/Z_loc(t)` with the same localiser. -/
theorem locLaplace_eq_partition_ratio {s t : ℝ} (hs : -1 < s) (ht : 0 < t) :
    _root_.Laplace.gibbsExpectation (locPotential1 lam alpha gamma g x₀ t) t (fun x => Real.exp (-(s
      * t * anharmonicPotential lam alpha gamma x))) = _root_.Laplace.partitionFunction
      (locPotential1 lam alpha gamma g x₀ ((1 + s) * t)) ((1 + s) * t) /
      _root_.Laplace.partitionFunction (locPotential1 lam alpha gamma g x₀ t) t := by
  unfold _root_.Laplace.gibbsExpectation
  congr 1
  unfold _root_.Laplace.partitionFunction
  exact integral_congr_ae (Eventually.of_forall fun x => exp_locPotential1_scale hs ht x)

/-- `Z_loc(u) = e^{−gx₀²/2}·D(u)·Z(u)` with `D(u) = ⟨φ⟩_u` the localiser denominator. -/
theorem locPartition_eq {u : ℝ} (hu : 0 < u) :
    _root_.Laplace.partitionFunction (locPotential1 lam alpha gamma g x₀ u) u = Real.exp (-(g * x₀ ^
      2 / 2)) * (_root_.Laplace.gibbsExpectation (anharmonicPotential lam alpha gamma) u (locWeight
      g x₀) * _root_.Laplace.partitionFunction (anharmonicPotential lam alpha gamma) u) := by
  have hZ := partition_pos' hlam hgamma hdisc hu
  have e : ∀ x, Real.exp (-(u * locPotential1 lam alpha gamma g x₀ u x)) =
      Real.exp (-(g * x₀ ^ 2 / 2)) *
        (locWeight g x₀ x * Real.exp (-(u * anharmonicPotential lam alpha gamma x))) := by
    intro x
    unfold locPotential1 locWeight
    rw [← Real.exp_add, ← Real.exp_add]
    congr 1
    field_simp
    ring
  unfold _root_.Laplace.gibbsExpectation
  rw [div_mul_cancel₀ _ hZ.ne']
  unfold _root_.Laplace.partitionFunction
  rw [← integral_const_mul]
  exact integral_congr_ae (Eventually.of_forall fun x => e x)

omit hgamma hdisc in
/-- `Z(u) = J₀(u)/√(λu)`. -/
theorem partition_eq_J0 {u : ℝ} (hu : 0 < u) :
    _root_.Laplace.partitionFunction (anharmonicPotential lam alpha gamma) u = J_n lam alpha gamma 0
      u / Real.sqrt (lam * u) := by
  have h := I_n_J_n_relation lam alpha gamma 0 hlam hu
  have hsq : 0 < Real.sqrt (lam * u) := Real.sqrt_pos.mpr (by positivity)
  rw [eq_div_iff hsq.ne', mul_comm]
  simp only [zero_add, pow_one, pow_zero, one_mul] at h
  unfold J_n
  simp only [pow_zero, one_mul]
  unfold _root_.Laplace.partitionFunction
  exact h

theorem locDenominator_pos (hg : 0 ≤ g) {u : ℝ} (hu : 0 < u) :
    0 < _root_.Laplace.gibbsExpectation (anharmonicPotential lam alpha gamma) u (locWeight g x₀) :=
      by
  have h := partitionFunction_locPotential1_pos hlam hgamma hdisc hg hu (x₀ := x₀)
  rw [locPartition_eq hlam hgamma hdisc hu] at h
  have h2 := (mul_pos_iff_of_pos_left (Real.exp_pos _)).mp h
  exact (mul_pos_iff_of_pos_right (partition_pos' hlam hgamma hdisc hu)).mp h2

theorem J0_pos {u : ℝ} (hu : 0 < u) : 0 < J_n lam alpha gamma 0 u := by
  have h := partition_pos' hlam hgamma hdisc hu
  rw [partition_eq_J0 hlam hu] at h
  exact (div_pos_iff_of_pos_right (Real.sqrt_pos.mpr (by positivity))).mp h

/-- **The exact factorisation**: `√(1+s)·Λ_t(s) = [J₀((1+s)t)/J₀(t)]·[D((1+s)t)/D(t)]`. -/
theorem locLaplace_scaled_eq (hg : 0 ≤ g) {s t : ℝ} (hs : -1 < s) (ht : 0 < t) :
    Real.sqrt (1 + s) * _root_.Laplace.gibbsExpectation (locPotential1 lam alpha gamma g x₀ t) t
      (fun x => Real.exp (-(s * t * anharmonicPotential lam alpha gamma x))) = J_n lam alpha gamma 0
      ((1 + s) * t) / J_n lam alpha gamma 0 t * (_root_.Laplace.gibbsExpectation
      (anharmonicPotential lam alpha gamma) ((1 + s) * t) (locWeight g x₀) /
      _root_.Laplace.gibbsExpectation (anharmonicPotential lam alpha gamma) t (locWeight g x₀)) :=
      by
  have ha : 0 < 1 + s := by linarith
  have hat : 0 < (1 + s) * t := mul_pos ha ht
  rw [locLaplace_eq_partition_ratio hs ht, locPartition_eq hlam hgamma hdisc hat,
    locPartition_eq hlam hgamma hdisc ht, partition_eq_J0 hlam hat,
    partition_eq_J0 hlam ht]
  have hsq : Real.sqrt (lam * ((1 + s) * t)) = Real.sqrt (1 + s) * Real.sqrt (lam * t) := by
    rw [← Real.sqrt_mul ha.le]
    congr 1
    ring
  rw [hsq]
  have hc : Real.exp (-(g * x₀ ^ 2 / 2)) ≠ 0 := (Real.exp_pos _).ne'
  have hD := (locDenominator_pos hlam hgamma hdisc hg ht (x₀ := x₀)).ne'
  have hJ := (J0_pos hlam hgamma hdisc ht).ne'
  have hs1 : Real.sqrt (1 + s) ≠ 0 := (Real.sqrt_pos.mpr ha).ne'
  have hs2 : Real.sqrt (lam * t) ≠ 0 := (Real.sqrt_pos.mpr (by positivity)).ne'
  field_simp

/-- **The normalised Laplace transform of the localised energy**:
`|√(1+s)·⟨e^{−stℓ}⟩_loc − 1| ≤ K/t`, uniformly over `s ≥ −1 + δ`. -/
theorem locLaplace_scaled_rate (hg : 0 ≤ g) {δ : ℝ} (hδ : 0 < δ) :
    ∃ K T : ℝ, 0 ≤ K ∧ 1 ≤ T ∧ ∀ {t : ℝ}, T ≤ t → ∀ {s : ℝ}, -1 + δ ≤ s →
      |Real.sqrt (1 + s) * _root_.Laplace.gibbsExpectation (locPotential1 lam alpha gamma g x₀ t) t
        (fun x => Real.exp (-(s * t * anharmonicPotential lam alpha gamma x))) - 1| ≤ K / t := by
  obtain ⟨KJ, hKJ, hJ⟩ := J0_delta_order1 hlam hgamma hdisc
  obtain ⟨KD, TD, hKD, hTD, hD⟩ := locDenominator_rate hlam hgamma hdisc hg (x₀ := x₀)
  obtain ⟨K₁, T₁, hK₁, hT₁, h₁⟩ := scaled_ratio_rate (F := J_n lam alpha gamma 0)
    (Real.sqrt_pos.mpr (by positivity : (0 : ℝ) < 2 * Real.pi)) hKJ le_rfl hδ
    (fun {u} hu => hJ hu)
  obtain ⟨K₂, T₂, hK₂, hT₂, h₂⟩ := scaled_ratio_rate
    (F := fun u => _root_.Laplace.gibbsExpectation (anharmonicPotential lam alpha gamma) u
      (locWeight g x₀)) one_pos hKD hTD hδ (fun {u} hu => hD hu)
  refine ⟨K₁ * (|(1 : ℝ)| + K₂) + |(1 : ℝ)| * K₂, T₁ + T₂, by positivity, by linarith,
    fun {t} ht {s} hs => ?_⟩
  have ht1 : 1 ≤ t := by linarith
  have ht0 : 0 < t := by linarith
  have ha : -1 < s := by linarith
  rw [locLaplace_scaled_eq hlam hgamma hdisc hg ha ht0]
  have e1 := h₁ (t := t) (by linarith) hs
  have e2 := h₂ (t := t) (by linarith) hs
  have h := prod_rate t _ _ 1 1 K₁ K₂ ht1 hK₁ hK₂ e1 e2
  rw [mul_one] at h
  exact h

/-- **The Laplace transform of the localised energy**: `|⟨e^{−stℓ}⟩_loc − 1/√(1+s)| ≤ K/t`,
uniformly over `s ≥ −1 + δ` — the `Gamma(½, 1)` transform `(1+s)^{−1/2}` of the scaled energy
`tℓ`. -/
theorem locLaplace_rate (hg : 0 ≤ g) {δ : ℝ} (hδ : 0 < δ) :
    ∃ K T : ℝ, 0 ≤ K ∧ 1 ≤ T ∧ ∀ {t : ℝ}, T ≤ t → ∀ {s : ℝ}, -1 + δ ≤ s →
      |_root_.Laplace.gibbsExpectation (locPotential1 lam alpha gamma g x₀ t) t (fun x => Real.exp
        (-(s * t * anharmonicPotential lam alpha gamma x))) - 1 / Real.sqrt (1 + s)| ≤ K / t := by
  obtain ⟨K, T, hK, hT, h⟩ := locLaplace_scaled_rate hlam hgamma hdisc hg hδ
  refine ⟨1 / Real.sqrt δ * K, T, by positivity, hT, fun {t} ht {s} hs => ?_⟩
  have ha : 0 < 1 + s := by linarith
  have hsa : 0 < Real.sqrt (1 + s) := Real.sqrt_pos.mpr ha
  have e : 1 / Real.sqrt (1 + s) * (Real.sqrt (1 + s) * _root_.Laplace.gibbsExpectation
      (locPotential1 lam alpha gamma g x₀ t) t (fun x => Real.exp (-(s * t * anharmonicPotential lam
      alpha gamma x))) - 1) = _root_.Laplace.gibbsExpectation (locPotential1 lam alpha gamma g x₀ t)
      t (fun x => Real.exp (-(s * t * anharmonicPotential lam alpha gamma x))) - 1 / Real.sqrt (1 +
      s) := by
    rw [mul_sub, ← mul_assoc, one_div_mul_cancel hsa.ne', one_mul, mul_one]
  rw [← e, abs_mul, abs_of_pos (by positivity : (0 : ℝ) < 1 / Real.sqrt (1 + s))]
  have hle : 1 / Real.sqrt (1 + s) ≤ 1 / Real.sqrt δ :=
    one_div_le_one_div_of_le (Real.sqrt_pos.mpr hδ) (Real.sqrt_le_sqrt (by linarith))
  calc _ ≤ 1 / Real.sqrt δ * (K / t) := mul_le_mul hle (h ht hs) (abs_nonneg _) (by positivity)
    _ = _ := by ring

/-- Pointwise form: for each fixed `s > −1`, `|⟨e^{−stℓ}⟩_loc − 1/√(1+s)| ≤ K/t`. -/
theorem locLaplace_rate_pointwise (hg : 0 ≤ g) {s : ℝ} (hs : -1 < s) :
    ∃ K T : ℝ, 0 ≤ K ∧ 1 ≤ T ∧ ∀ {t : ℝ}, T ≤ t →
      |_root_.Laplace.gibbsExpectation (locPotential1 lam alpha gamma g x₀ t) t (fun x => Real.exp
        (-(s * t * anharmonicPotential lam alpha gamma x))) - 1 / Real.sqrt (1 + s)| ≤ K / t := by
  obtain ⟨K, T, hK, hT, h⟩ := locLaplace_rate hlam hgamma hdisc hg (by linarith : (0 : ℝ) < 1 + s)
  exact ⟨K, T, hK, hT, fun {t} ht => h ht (by linarith)⟩

end OneD

section Multi

variable {d : ℕ} {Q : Matrix (Fin d) (Fin d) ℝ} {lam alpha gamma : Fin d → ℝ} {g : ℝ}
variable (hlam : ∀ i, 0 < lam i) (hgamma : ∀ i, 0 < gamma i)
  (hdisc : ∀ i, alpha i ^ 2 < 3 * lam i * gamma i)
include hlam hgamma hdisc

omit hlam hgamma hdisc in
/-- The temperature change `t ↦ (1+s)t` at fixed isotropic localiser, on E2. -/
theorem exp_localisedRotated_scale (c w₀ : Fin d → ℝ) {s t : ℝ} (hs : -1 < s) (ht : 0 < t)
    (w : Fin d → ℝ) :
    Real.exp (-(s * t * rotatedAnharmonic Q c lam alpha gamma w)) * Real.exp (-(t *
      localisedRotatedAnharmonic Q c lam alpha gamma g w₀ t w)) = Real.exp (-((1 + s) * t *
      localisedRotatedAnharmonic Q c lam alpha gamma g w₀ ((1 + s) * t) w)) := by
  have ha : 0 < 1 + s := by linarith
  have ha1 : 1 + s ≠ 0 := ha.ne'
  have ht1 : t ≠ 0 := ht.ne'
  rw [← Real.exp_add]
  congr 1
  unfold localisedRotatedAnharmonic localisedPotential localiser
  set A := ∑ j, (w j - w₀ j) ^ 2 with hA
  field_simp
  ring

omit hlam hgamma hdisc in
/-- `⟨e^{−st·L∘A}⟩_loc(t) = Z_loc((1+s)t)/Z_loc(t)` on E2. -/
theorem localisedLaplace_eq_partition_ratio (c w₀ : Fin d → ℝ) {s t : ℝ} (hs : -1 < s)
    (ht : 0 < t) :
    gibbsExpectation (localisedRotatedAnharmonic Q c lam alpha gamma g w₀ t) t (fun w => Real.exp
      (-(s * t * rotatedAnharmonic Q c lam alpha gamma w))) = partitionFunction
      (localisedRotatedAnharmonic Q c lam alpha gamma g w₀ ((1 + s) * t)) ((1 + s) * t) /
      partitionFunction (localisedRotatedAnharmonic Q c lam alpha gamma g w₀ t) t := by
  unfold gibbsExpectation
  congr 1
  unfold partitionFunction
  exact integral_congr_ae (Eventually.of_forall fun w => exp_localisedRotated_scale c w₀ hs ht w)

omit hlam hgamma hdisc in
/-- The localised rotated partition function is the product of the frame-coordinate ones. -/
theorem partitionFunction_localisedRotated_eq_prod (hQ : Qᵀ * Q = 1) (c w₀ : Fin d → ℝ) (u : ℝ) :
    partitionFunction (localisedRotatedAnharmonic Q c lam alpha gamma g w₀ u) u = ∏ i,
      _root_.Laplace.partitionFunction (locPotential1 (lam i) (alpha i) (gamma i) g (affineFrame Q c
      w₀ i) u) u := by
  have hcont : Continuous fun w : Fin d → ℝ =>
      Real.exp (-(u * separablePotential (locFamily lam alpha gamma g (affineFrame Q c w₀) u) w)) :=
    Real.continuous_exp.comp
      ((continuous_const.mul (continuous_separablePotential_locFamily _ u)).neg)
  rw [localisedRotatedAnharmonic_eq_rotated_locFamily hQ c w₀ u,
    partitionFunction_rotated hQ c _ u hcont.aestronglyMeasurable, partitionFunction_separable]
  rfl

omit hlam hgamma hdisc in
/-- **The E2 Laplace transform factorises over the frame coordinates**:
`⟨e^{−st·L∘A}⟩_loc = ∏ᵢ ⟨e^{−stℓᵢ}⟩_loc,ᵢ`. -/
theorem localisedLaplace_eq_prod (hQ : Qᵀ * Q = 1) (c w₀ : Fin d → ℝ) {s t : ℝ} (hs : -1 < s)
    (ht : 0 < t) :
    gibbsExpectation (localisedRotatedAnharmonic Q c lam alpha gamma g w₀ t) t (fun w => Real.exp
      (-(s * t * rotatedAnharmonic Q c lam alpha gamma w))) = ∏ i, _root_.Laplace.gibbsExpectation
      (locPotential1 (lam i) (alpha i) (gamma i) g (affineFrame Q c w₀ i) t) t (fun x => Real.exp
      (-(s * t * anharmonicPotential (lam i) (alpha i) (gamma i) x))) := by
  rw [localisedLaplace_eq_partition_ratio c w₀ hs ht,
    partitionFunction_localisedRotated_eq_prod hQ c w₀,
    partitionFunction_localisedRotated_eq_prod hQ c w₀, ← Finset.prod_div_distrib]
  exact Finset.prod_congr rfl fun i _ => (locLaplace_eq_partition_ratio hs ht).symm

/-- **The Laplace transform of the localised energy on E2**:
`|⟨e^{−st·L∘A}⟩_loc − (1/√(1+s))^d| ≤ K/t`, uniformly over `s ≥ −1 + δ` — the `Gamma(d/2, 1)`
transform `(1+s)^{−d/2}` of the scaled energy `t·(L∘A)`. -/
theorem localisedLaplace_rate (hQ : Qᵀ * Q = 1) (c w₀ : Fin d → ℝ) (hg : 0 ≤ g) {δ : ℝ}
    (hδ : 0 < δ) :
    ∃ K T : ℝ, 0 ≤ K ∧ 1 ≤ T ∧ ∀ {t : ℝ}, T ≤ t → ∀ {s : ℝ}, -1 + δ ≤ s →
      |gibbsExpectation (localisedRotatedAnharmonic Q c lam alpha gamma g w₀ t) t (fun w => Real.exp
        (-(s * t * rotatedAnharmonic Q c lam alpha gamma w))) - (1 / Real.sqrt (1 + s)) ^ d| ≤ K / t
        := by
  choose K T hK hT h using fun i =>
    locLaplace_scaled_rate (hlam i) (hgamma i) (hdisc i) hg hδ (x₀ := affineFrame Q c w₀ i)
  have hT0 : ∀ i, 0 ≤ T i := fun i => by linarith [hT i]
  have hsumT : 0 ≤ ∑ i, T i := Finset.sum_nonneg fun i _ => hT0 i
  have hsumK : 0 ≤ ∑ i, K i := Finset.sum_nonneg fun i _ => hK i
  refine ⟨(1 / Real.sqrt δ) ^ d * (2 ^ d * ∑ i, K i), 1 + ∑ i, T i + ∑ i, K i, by positivity,
    by linarith, fun {t} ht {s} hs => ?_⟩
  have ht0 : 0 < t := by linarith
  have ha : -1 < s := by linarith
  have hsa : 0 < Real.sqrt (1 + s) := Real.sqrt_pos.mpr (by linarith)
  rw [localisedLaplace_eq_prod hQ c w₀ ha ht0]
  have e : (1 / Real.sqrt (1 + s)) ^ d * ∏ i, (Real.sqrt (1 + s) * _root_.Laplace.gibbsExpectation
      (locPotential1 (lam i) (alpha i) (gamma i) g (affineFrame Q c w₀ i) t) t (fun x => Real.exp
      (-(s * t * anharmonicPotential (lam i) (alpha i) (gamma i) x)))) = ∏ i,
      _root_.Laplace.gibbsExpectation (locPotential1 (lam i) (alpha i) (gamma i) g (affineFrame Q c
      w₀ i) t) t (fun x => Real.exp (-(s * t * anharmonicPotential (lam i) (alpha i) (gamma i) x)))
      := by
    rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ, Fintype.card_fin, ← mul_assoc,
      ← mul_pow, one_div_mul_cancel hsa.ne', one_pow, one_mul]
  rw [← e]
  have hprod := prod_one_rate Finset.univ (fun i => Real.sqrt (1 + s) *
    _root_.Laplace.gibbsExpectation (locPotential1 (lam i) (alpha i) (gamma i) g (affineFrame Q c w₀
    i) t) t (fun x => Real.exp (-(s * t * anharmonicPotential (lam i) (alpha i) (gamma i) x)))) K
    ht0 hK (fun i => (Finset.single_le_sum (fun j _ => hK j) (Finset.mem_univ i)).trans (by
    linarith)) (fun i => h i (by linarith [Finset.single_le_sum (fun j _ => hT0 j) (Finset.mem_univ
    i)]) hs)
  rw [Finset.card_univ, Fintype.card_fin] at hprod
  have hle : (1 / Real.sqrt (1 + s)) ^ d ≤ (1 / Real.sqrt δ) ^ d :=
    pow_le_pow_left₀ (by positivity)
      (one_div_le_one_div_of_le (Real.sqrt_pos.mpr hδ) (Real.sqrt_le_sqrt (by linarith))) d
  rw [← mul_sub_one, abs_mul, abs_of_pos (by positivity : (0 : ℝ) < (1 / Real.sqrt (1 + s)) ^ d)]
  calc _ ≤ (1 / Real.sqrt δ) ^ d * (2 ^ d * (∑ i, K i) / t) :=
        mul_le_mul hle hprod (abs_nonneg _) (by positivity)
    _ = _ := by ring

/-- Pointwise form on E2: for each fixed `s > −1`,
`|⟨e^{−st·L∘A}⟩_loc − (1/√(1+s))^d| ≤ K/t`. -/
theorem localisedLaplace_rate_pointwise (hQ : Qᵀ * Q = 1) (c w₀ : Fin d → ℝ) (hg : 0 ≤ g) {s : ℝ}
    (hs : -1 < s) :
    ∃ K T : ℝ, 0 ≤ K ∧ 1 ≤ T ∧ ∀ {t : ℝ}, T ≤ t →
      |gibbsExpectation (localisedRotatedAnharmonic Q c lam alpha gamma g w₀ t) t (fun w => Real.exp
        (-(s * t * rotatedAnharmonic Q c lam alpha gamma w))) - (1 / Real.sqrt (1 + s)) ^ d| ≤ K / t
        := by
  obtain ⟨K, T, hK, hT, h⟩ := localisedLaplace_rate hlam hgamma hdisc hQ c w₀ hg
    (by linarith : (0 : ℝ) < 1 + s)
  exact ⟨K, T, hK, hT, fun {t} ht => h ht (by linarith)⟩

end Multi

end Laplace.Multi
