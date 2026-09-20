/-
Copyright (c) 2026 Timaeus Research. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniel Murfet
-/
import Mathlib
import Laplace.Multi.SecondOrderEngine
import Laplace.Multi.ShiftNormalization
import Laplace.Multi.NormalizedRate
import Laplace.Multi.LocationRecovery
import Laplace.Multi.KernelInstance
import Laplace.Multi.SpanningCriterion
import Laplace.Multi.GaussianStein

/-!
# Second-order Laplace expansion of a rescaled moment (germbij Q2, Laplace layer)

Instantiation of the abstract second-order engine (`SecondOrderEngine`) at the
rescaled Boltzmann integrand of a `HigherLaplaceDomain` package. Fix a loss `L`
with a package at grade `2ρ + 3` whose Taylor terms of degree `3, …, ρ + 1`
vanish (so the first non-Gaussian term is `Q := T_{ρ+2} L`). Write

* `pertV L H h x = (L(hx) − L 0)/h² − qform H x / 2` — the rescaled perturbation,
* `linJet L ρ h x = ∑_{j<ρ} h^{ρ+j} T_{ρ+j+2} L x` — the linear Taylor jet,
* `taylorTail L m y = L y − ∑_{j<m} T_j L y` — the Taylor tail from degree `m`.

The two pointwise inputs of the engine are `pertV / h^ρ → Q` and
`(pertV − linJet)/h^{2ρ} → R := T_{2ρ+2} L`, both from the grade-`(2ρ+3)`
remainder bound (`tendsto_taylorTail_succ_div_pow`). The residual
`(w_h − w₀ + w₀ · linJet)/h^{2ρ}` then converges pointwise to
`w₀ · (½ Q² − R)` (`tendsto_residual`) and is dominated by a polynomial times a
Gaussian (`exists_residual_bound`), with the inner region handled through the
endpoint bound `|e^{-v} − 1 + v| ≤ v²(1 + e^{-v})` and the outer region through
`h^{-2ρ} ≤ (‖x‖/r)^{2ρ}`.

The integral, normalisation and elimination layers follow in
`SecondOrderRadial`.
-/

open MeasureTheory Filter Topology Set

namespace Laplace.Multi

variable {d : ℕ}

/-! ### The Taylor tail and its bounds from a package -/

/-- The Taylor tail of `L` from degree `m`: `L y − ∑_{j<m} T_j L y`. -/
noncomputable def taylorTail (L : EuclidD d → ℝ) (m : ℕ) (y : EuclidD d) : ℝ :=
  L y - ∑ j ∈ Finset.range m, taylorHomogeneousTerm j L y

theorem taylorTail_succ (L : EuclidD d → ℝ) (m : ℕ) (y : EuclidD d) :
    taylorTail L m y = taylorTail L (m + 1) y + taylorHomogeneousTerm m L y := by
  unfold taylorTail
  rw [Finset.sum_range_succ]
  ring

theorem taylorTail_smul_succ (L : EuclidD d → ℝ) (m : ℕ) (a : ℝ) (x : EuclidD d) :
    taylorTail L m (a • x) =
      taylorTail L (m + 1) (a • x) + a ^ m * taylorHomogeneousTerm m L x := by
  rw [taylorTail_succ, taylorHomogeneousTerm_smul]

/-- Eventually the dilated point lies in any fixed ball about the origin. -/
theorem eventually_smul_mem_ball {r : ℝ} (hr : 0 < r) (x : EuclidD d) :
    ∀ᶠ h in 𝓝[>] (0 : ℝ), h • x ∈ Metric.ball (0 : EuclidD d) r := by
  have hlt : ∀ᶠ h in 𝓝[>] (0 : ℝ), h < r / (‖x‖ + 1) :=
    eventually_nhdsWithin_of_eventually_nhds
      (eventually_lt_nhds (div_pos hr (by positivity)))
  filter_upwards [hlt, self_mem_nhdsWithin] with h hh hh0
  have hh0' : (0 : ℝ) < h := hh0
  rw [Metric.mem_ball, dist_zero_right, norm_smul, Real.norm_eq_abs, abs_of_pos hh0']
  calc h * ‖x‖ ≤ h * (‖x‖ + 1) := by
        apply mul_le_mul_of_nonneg_left _ hh0'.le
        linarith
    _ < r / (‖x‖ + 1) * (‖x‖ + 1) := mul_lt_mul_of_pos_right hh (by positivity)
    _ = r := by field_simp

namespace HigherLaplaceDomain

variable {n : ℕ} {L : EuclidD d → ℝ} {H : Matrix (Fin d) (Fin d) ℝ}

/-- **Lower-grade Taylor bounds from a package**: on the Taylor ball the tail
from any degree `m ≤ n` is `O(‖y‖^m)`. -/
theorem exists_taylorTail_bound (A : HigherLaplaceDomain n L H) {m : ℕ} (hm : m ≤ n) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ y ∈ Metric.ball (0 : EuclidD d) A.taylorRadius,
      |taylorTail L m y| ≤ C * ‖y‖ ^ m := by
  have hr := A.taylorRadius_pos
  have hC0 := A.taylorRemainderConst_nonneg
  refine ⟨A.taylorRemainderConst * A.taylorRadius ^ (n - m) + ∑ j ∈ Finset.Ico m n,
    (j.factorial : ℝ)⁻¹ * ‖iteratedFDeriv ℝ j L 0‖ * A.taylorRadius ^ (j - m), by positivity,
    fun y hy ↦ ?_⟩
  have hy' : ‖y‖ < A.taylorRadius := by simpa [Metric.mem_ball, dist_zero_right] using hy
  have hy0 : 0 ≤ ‖y‖ := norm_nonneg y
  have hpow : ∀ j, m ≤ j → ‖y‖ ^ j ≤ A.taylorRadius ^ (j - m) * ‖y‖ ^ m := by
    intro j hj
    rw [show ‖y‖ ^ j = ‖y‖ ^ (j - m) * ‖y‖ ^ m by rw [← pow_add, Nat.sub_add_cancel hj]]
    exact mul_le_mul_of_nonneg_right (pow_le_pow_left₀ hy0 hy'.le _) (by positivity)
  have hsplit : taylorTail L m y = taylorTail L n y +
      ∑ j ∈ Finset.Ico m n, taylorHomogeneousTerm j L y := by
    unfold taylorTail
    rw [← Finset.sum_range_add_sum_Ico _ hm]
    ring
  have h1 : |taylorTail L n y| ≤
      A.taylorRemainderConst * (A.taylorRadius ^ (n - m) * ‖y‖ ^ m) :=
    (A.taylorRemainder_bound y hy).trans (mul_le_mul_of_nonneg_left (hpow n hm) hC0)
  have h2 : ∀ j ∈ Finset.Ico m n, |taylorHomogeneousTerm j L y| ≤
      (j.factorial : ℝ)⁻¹ * ‖iteratedFDeriv ℝ j L 0‖ * (A.taylorRadius ^ (j - m) * ‖y‖ ^ m) :=
    fun j hj ↦ (abs_taylorHomogeneousTerm_le j L y).trans
      (mul_le_mul_of_nonneg_left (hpow j (Finset.mem_Ico.mp hj).1) (by positivity))
  rw [hsplit]
  calc |taylorTail L n y + ∑ j ∈ Finset.Ico m n, taylorHomogeneousTerm j L y|
      ≤ |taylorTail L n y| + ∑ j ∈ Finset.Ico m n, |taylorHomogeneousTerm j L y| :=
        (abs_add_le _ _).trans (add_le_add le_rfl (Finset.abs_sum_le_sum_abs _ _))
    _ ≤ A.taylorRemainderConst * (A.taylorRadius ^ (n - m) * ‖y‖ ^ m) +
        ∑ j ∈ Finset.Ico m n, (j.factorial : ℝ)⁻¹ * ‖iteratedFDeriv ℝ j L 0‖ *
          (A.taylorRadius ^ (j - m) * ‖y‖ ^ m) := add_le_add h1 (Finset.sum_le_sum h2)
    _ = _ := by
        rw [add_mul, Finset.sum_mul]
        congr 1
        · ring
        · exact Finset.sum_congr rfl fun j _ ↦ by ring

/-- The rate-divided Taylor tail of one degree higher vanishes along dilations. -/
theorem tendsto_taylorTail_succ_div_pow (A : HigherLaplaceDomain n L H) {m : ℕ}
    (hm : m + 1 ≤ n) (x : EuclidD d) :
    Tendsto (fun h : ℝ ↦ taylorTail L (m + 1) (h • x) / h ^ m) (𝓝[>] (0 : ℝ)) (𝓝 0) := by
  obtain ⟨C, hC0, hC⟩ := A.exists_taylorTail_bound hm
  have hcont : Continuous fun h : ℝ ↦ C * ‖x‖ ^ (m + 1) * h := by fun_prop
  have hbound : Tendsto (fun h : ℝ ↦ C * ‖x‖ ^ (m + 1) * h) (𝓝[>] (0 : ℝ)) (𝓝 0) := by
    have := (hcont.tendsto 0).mono_left (nhdsWithin_le_nhds (s := Set.Ioi 0))
    rwa [mul_zero] at this
  refine squeeze_zero_norm' ?_ hbound
  filter_upwards [eventually_smul_mem_ball A.taylorRadius_pos x, self_mem_nhdsWithin]
    with h hmem hh
  have hh0 : (0 : ℝ) < h := hh
  rw [Real.norm_eq_abs, abs_div, abs_of_pos (pow_pos hh0 m), div_le_iff₀ (pow_pos hh0 m)]
  calc |taylorTail L (m + 1) (h • x)| ≤ C * ‖h • x‖ ^ (m + 1) := hC _ hmem
    _ = C * ‖x‖ ^ (m + 1) * h * h ^ m := by
        rw [norm_smul, Real.norm_eq_abs, abs_of_pos hh0, mul_pow, pow_succ]
        ring

/-- The rate-divided Taylor tail is bounded by a polynomial on the Taylor ball. -/
theorem exists_abs_taylorTail_div_pow_le (A : HigherLaplaceDomain n L H) {m : ℕ}
    (hm : m ≤ n) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ {h : ℝ}, 0 < h → ∀ {x : EuclidD d},
      h • x ∈ Metric.ball (0 : EuclidD d) A.taylorRadius →
      |taylorTail L m (h • x)| / h ^ m ≤ C * ‖x‖ ^ m := by
  obtain ⟨C, hC0, hC⟩ := A.exists_taylorTail_bound hm
  refine ⟨C, hC0, fun {h} hh {x} hmem ↦ ?_⟩
  rw [div_le_iff₀ (pow_pos hh m)]
  calc |taylorTail L m (h • x)| ≤ C * ‖h • x‖ ^ m := hC _ hmem
    _ = C * ‖x‖ ^ m * h ^ m := by
        rw [norm_smul, Real.norm_eq_abs, abs_of_pos hh, mul_pow]
        ring

end HigherLaplaceDomain

/-! ### The rescaled perturbation and the linear jet -/

/-- The rescaled perturbation of the loss relative to its Gaussian part. -/
noncomputable def pertV (L : EuclidD d → ℝ) (H : Matrix (Fin d) (Fin d) ℝ) (h : ℝ)
    (x : EuclidD d) : ℝ :=
  (L (h • x) - L 0) / h ^ 2 - qform H x / 2

/-- The linear Taylor jet `∑_{j<ρ} h^{ρ+j} T_{ρ+j+2} L`. -/
noncomputable def linJet (L : EuclidD d → ℝ) (ρ : ℕ) (h : ℝ) (x : EuclidD d) : ℝ :=
  ∑ j ∈ Finset.range ρ, h ^ (ρ + j) * taylorHomogeneousTerm (ρ + j + 2) L x

section Identities

variable {L : EuclidD d → ℝ} {H : Matrix (Fin d) (Fin d) ℝ} {ρ : ℕ}

/-- Under the vanishing hypotheses the Taylor sum through degree `ρ + 1` along a
dilation is `L 0 + h² · qform/2`. -/
theorem sum_taylor_low (hρ : 0 < ρ) (hT1 : taylorHomogeneousTerm 1 L = fun _ ↦ (0 : ℝ))
    (hT2 : ∀ z, taylorHomogeneousTerm 2 L z = qform H z / 2)
    (hvanish : ∀ j, 3 ≤ j → j < ρ + 2 → taylorHomogeneousTerm j L = 0)
    (h : ℝ) (x : EuclidD d) :
    ∑ j ∈ Finset.range (ρ + 2), taylorHomogeneousTerm j L (h • x) =
      L 0 + h ^ 2 * (qform H x / 2) := by
  rw [Finset.sum_eq_add_of_mem 0 2 (Finset.mem_range.mpr (by omega))
    (Finset.mem_range.mpr (by omega)) (by norm_num)]
  · rw [taylorHomogeneousTerm_zero, taylorHomogeneousTerm_smul, hT2]
  · rintro c hc ⟨hc0, hc2⟩
    rcases Nat.lt_or_ge c 3 with h3 | h3
    · interval_cases c
      · exact absurd rfl hc0
      · rw [hT1]
      · exact absurd rfl hc2
    · rw [hvanish c h3 (Finset.mem_range.mp hc)]
      rfl

theorem sum_taylor_high (L : EuclidD d → ℝ) (ρ : ℕ) (h : ℝ) (x : EuclidD d) :
    ∑ j ∈ Finset.range ρ, taylorHomogeneousTerm (ρ + 2 + j) L (h • x) =
      h ^ 2 * linJet L ρ h x := by
  unfold linJet
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun j _ ↦ ?_
  rw [taylorHomogeneousTerm_smul, show ρ + 2 + j = ρ + j + 2 by ring]
  ring

theorem pertV_eq (hρ : 0 < ρ) (hT1 : taylorHomogeneousTerm 1 L = fun _ ↦ (0 : ℝ))
    (hT2 : ∀ z, taylorHomogeneousTerm 2 L z = qform H z / 2)
    (hvanish : ∀ j, 3 ≤ j → j < ρ + 2 → taylorHomogeneousTerm j L = 0)
    {h : ℝ} (hh : h ≠ 0) (x : EuclidD d) :
    pertV L H h x = taylorTail L (ρ + 2) (h • x) / h ^ 2 := by
  unfold pertV taylorTail
  rw [sum_taylor_low hρ hT1 hT2 hvanish h x]
  field_simp
  ring

theorem pertV_sub_linJet_eq (hρ : 0 < ρ) (hT1 : taylorHomogeneousTerm 1 L = fun _ ↦ (0 : ℝ))
    (hT2 : ∀ z, taylorHomogeneousTerm 2 L z = qform H z / 2)
    (hvanish : ∀ j, 3 ≤ j → j < ρ + 2 → taylorHomogeneousTerm j L = 0)
    {h : ℝ} (hh : h ≠ 0) (x : EuclidD d) :
    pertV L H h x - linJet L ρ h x = taylorTail L (2 * ρ + 2) (h • x) / h ^ 2 := by
  unfold pertV taylorTail
  have hsplit : ∑ j ∈ Finset.range (2 * ρ + 2), taylorHomogeneousTerm j L (h • x) =
      (∑ j ∈ Finset.range (ρ + 2), taylorHomogeneousTerm j L (h • x)) +
      ∑ j ∈ Finset.range ρ, taylorHomogeneousTerm (ρ + 2 + j) L (h • x) := by
    rw [← Finset.sum_range_add, show ρ + 2 + ρ = 2 * ρ + 2 by ring]
  rw [hsplit, sum_taylor_low hρ hT1 hT2 hvanish, sum_taylor_high]
  field_simp
  ring

/-- The linear jet is bounded by the sum of the absolute Taylor terms for `0 < h ≤ 1`. -/
theorem abs_linJet_le {h : ℝ} (hh0 : 0 ≤ h) (hh1 : h ≤ 1) (x : EuclidD d) :
    |linJet L ρ h x| ≤
      ∑ j ∈ Finset.range ρ, |taylorHomogeneousTerm (ρ + j + 2) L x| := by
  unfold linJet
  refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun j _ ↦ ?_)
  rw [abs_mul, abs_of_nonneg (pow_nonneg hh0 _)]
  exact mul_le_of_le_one_left (abs_nonneg _) (pow_le_one₀ hh0 hh1)

theorem continuous_linJet (L : EuclidD d → ℝ) (ρ : ℕ) (h : ℝ) :
    Continuous fun x ↦ linJet L ρ h x :=
  continuous_finsetSum _ fun _ _ ↦ continuous_const.mul (taylorHomogeneousTerm_continuous _ L)

end Identities

namespace HigherLaplaceDomain

variable {ρ : ℕ} {L : EuclidD d → ℝ} {H : Matrix (Fin d) (Fin d) ℝ}

/-- **First pointwise input**: `pertV / h^ρ → T_{ρ+2} L`. -/
theorem tendsto_pertV_div_pow (A : HigherLaplaceDomain (2 * ρ + 3) L H) (hρ : 0 < ρ)
    (hvanish : ∀ j, 3 ≤ j → j < ρ + 2 → taylorHomogeneousTerm j L = 0) (x : EuclidD d) :
    Tendsto (fun h : ℝ ↦ pertV L H h x / h ^ ρ) (𝓝[>] (0 : ℝ))
      (𝓝 (taylorHomogeneousTerm (ρ + 2) L x)) := by
  have hT1 := A.taylorHomogeneousTerm_one_eq_zero (by omega)
  have hT2 := A.taylorHomogeneousTerm_two_eq_qform (by omega)
  have hlim := A.tendsto_taylorTail_succ_div_pow (m := ρ + 2) (by omega) x
  have := hlim.add_const (taylorHomogeneousTerm (ρ + 2) L x)
  rw [zero_add] at this
  refine this.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with h hh
  have hh0 : (h : ℝ) ≠ 0 := ne_of_gt hh
  rw [pertV_eq hρ hT1 hT2 hvanish hh0, taylorTail_smul_succ L (ρ + 2) h x]
  field_simp
  ring

/-- **Second pointwise input**: `(pertV − linJet)/h^{2ρ} → T_{2ρ+2} L`. -/
theorem tendsto_pertV_sub_linJet_div_pow (A : HigherLaplaceDomain (2 * ρ + 3) L H)
    (hρ : 0 < ρ)
    (hvanish : ∀ j, 3 ≤ j → j < ρ + 2 → taylorHomogeneousTerm j L = 0) (x : EuclidD d) :
    Tendsto (fun h : ℝ ↦ (pertV L H h x - linJet L ρ h x) / h ^ (2 * ρ)) (𝓝[>] (0 : ℝ))
      (𝓝 (taylorHomogeneousTerm (2 * ρ + 2) L x)) := by
  have hT1 := A.taylorHomogeneousTerm_one_eq_zero (by omega)
  have hT2 := A.taylorHomogeneousTerm_two_eq_qform (by omega)
  have hlim := A.tendsto_taylorTail_succ_div_pow (m := 2 * ρ + 2) (by omega) x
  have := hlim.add_const (taylorHomogeneousTerm (2 * ρ + 2) L x)
  rw [zero_add] at this
  refine this.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with h hh
  have hh0 : (h : ℝ) ≠ 0 := ne_of_gt hh
  rw [pertV_sub_linJet_eq hρ hT1 hT2 hvanish hh0, taylorTail_smul_succ L (2 * ρ + 2) h x]
  field_simp
  ring

/-- Inner-region bound for the first rescaled input. -/
theorem exists_abs_pertV_div_pow_le (A : HigherLaplaceDomain (2 * ρ + 3) L H) (hρ : 0 < ρ)
    (hvanish : ∀ j, 3 ≤ j → j < ρ + 2 → taylorHomogeneousTerm j L = 0) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ {h : ℝ}, 0 < h → ∀ {x : EuclidD d},
      h • x ∈ Metric.ball (0 : EuclidD d) A.taylorRadius →
      |pertV L H h x| / h ^ ρ ≤ C * ‖x‖ ^ (ρ + 2) := by
  have hT1 := A.taylorHomogeneousTerm_one_eq_zero (by omega)
  have hT2 := A.taylorHomogeneousTerm_two_eq_qform (by omega)
  obtain ⟨C, hC0, hC⟩ := A.exists_abs_taylorTail_div_pow_le (m := ρ + 2) (by omega)
  refine ⟨C, hC0, fun {h} hh {x} hmem ↦ ?_⟩
  rw [pertV_eq hρ hT1 hT2 hvanish hh.ne', abs_div, abs_of_pos (pow_pos hh 2), div_div,
    ← pow_add, show (2 : ℕ) + ρ = ρ + 2 by ring]
  exact hC hh hmem

/-- Inner-region bound for the second rescaled input. -/
theorem exists_abs_pertV_sub_linJet_div_pow_le (A : HigherLaplaceDomain (2 * ρ + 3) L H)
    (hρ : 0 < ρ)
    (hvanish : ∀ j, 3 ≤ j → j < ρ + 2 → taylorHomogeneousTerm j L = 0) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ {h : ℝ}, 0 < h → ∀ {x : EuclidD d},
      h • x ∈ Metric.ball (0 : EuclidD d) A.taylorRadius →
      |pertV L H h x - linJet L ρ h x| / h ^ (2 * ρ) ≤ C * ‖x‖ ^ (2 * ρ + 2) := by
  have hT1 := A.taylorHomogeneousTerm_one_eq_zero (by omega)
  have hT2 := A.taylorHomogeneousTerm_two_eq_qform (by omega)
  obtain ⟨C, hC0, hC⟩ := A.exists_abs_taylorTail_div_pow_le (m := 2 * ρ + 2) (by omega)
  refine ⟨C, hC0, fun {h} hh {x} hmem ↦ ?_⟩
  rw [pertV_sub_linJet_eq hρ hT1 hT2 hvanish hh.ne', abs_div, abs_of_pos (pow_pos hh 2),
    div_div, ← pow_add, show (2 : ℕ) + 2 * ρ = 2 * ρ + 2 by ring]
  exact hC hh hmem

end HigherLaplaceDomain

/-! ### The rescaled Boltzmann weight -/

namespace LocalLaplaceDomain

variable {L : EuclidD d → ℝ} {H : Matrix (Fin d) (Fin d) ℝ}

/-- The rescaled Boltzmann weight (the observable-free rescaled integrand). -/
noncomputable def weight (A : LocalLaplaceDomain L H) (h : ℝ) (x : EuclidD d) : ℝ :=
  Set.indicator {x : EuclidD d | h • x ∈ A.U}
    (fun x ↦ Real.exp (-((L (h • x) - L 0) / h ^ 2))) x

theorem integrand_eq_mul_weight (A : LocalLaplaceDomain L H) (P : EuclidD d → ℝ) (h : ℝ)
    (x : EuclidD d) : A.integrand P h x = P x * A.weight h x := by
  unfold integrand weight
  exact Set.indicator_mul_right _ _ _

theorem weight_nonneg (A : LocalLaplaceDomain L H) (h : ℝ) (x : EuclidD d) :
    0 ≤ A.weight h x :=
  Set.indicator_nonneg (fun _ _ ↦ (Real.exp_pos _).le) _

theorem weight_le (A : LocalLaplaceDomain L H) {h : ℝ} (hh : 0 < h) (x : EuclidD d) :
    A.weight h x ≤ Real.exp (-(A.c * ‖x‖ ^ 2)) := by
  unfold weight
  by_cases hmem : x ∈ {x : EuclidD d | h • x ∈ A.U}
  · rw [Set.indicator_of_mem hmem]
    exact Real.exp_le_exp.mpr (neg_le_neg (A.rescaled_lower hh hmem))
  · rw [Set.indicator_of_notMem hmem]
    positivity

theorem weight_eq_quadKernel_mul (A : LocalLaplaceDomain L H) {h : ℝ} {x : EuclidD d}
    (hmem : h • x ∈ A.U) :
    A.weight h x = quadKernel H x * Real.exp (-(pertV L H h x)) := by
  unfold weight
  rw [Set.indicator_of_mem (show x ∈ {x : EuclidD d | h • x ∈ A.U} from hmem)]
  unfold quadKernel pertV
  rw [← Real.exp_add]
  congr 1
  ring

theorem quadKernel_le (A : LocalLaplaceDomain L H) (x : EuclidD d) :
    quadKernel H x ≤ Real.exp (-(A.lambda / 2 * ‖x‖ ^ 2)) := by
  unfold quadKernel
  have := A.qform_lower x
  exact Real.exp_le_exp.mpr (by linarith)

theorem measurable_weight (A : LocalLaplaceDomain L H) (h : ℝ) :
    Measurable fun x ↦ A.weight h x := by
  unfold weight
  refine Measurable.indicator ?_ ((measurable_const_smul h) A.measurableSet_U)
  have hm : Measurable fun x : EuclidD d ↦ L (h • x) :=
    A.measurable_L.comp (measurable_const_smul h)
  exact Real.measurable_exp.comp (((hm.sub measurable_const).div_const _).neg)

end LocalLaplaceDomain

/-! ### The residual and its pointwise limit -/

namespace HigherLaplaceDomain

variable {n ρ : ℕ} {L : EuclidD d → ℝ} {H : Matrix (Fin d) (Fin d) ℝ}

/-- The linear-subtracted second-order residual
`(w_h − w₀ + w₀ · linJet)/h^{2ρ}` with `w₀ = quadKernel H`. -/
noncomputable def residual (A : HigherLaplaceDomain n L H) (ρ : ℕ) (h : ℝ) (x : EuclidD d) :
    ℝ :=
  (A.weight h x - quadKernel H x + quadKernel H x * linJet L ρ h x) / h ^ (2 * ρ)

/-- **Pointwise limit of the residual**: `w₀ · (½ Q² − R)` with `Q = T_{ρ+2} L`,
`R = T_{2ρ+2} L`. -/
theorem tendsto_residual (A : HigherLaplaceDomain (2 * ρ + 3) L H) (hρ : 0 < ρ)
    (hvanish : ∀ j, 3 ≤ j → j < ρ + 2 → taylorHomogeneousTerm j L = 0) (x : EuclidD d) :
    Tendsto (fun h : ℝ ↦ A.residual ρ h x) (𝓝[>] (0 : ℝ))
      (𝓝 (quadKernel H x * (1 / 2 * taylorHomogeneousTerm (ρ + 2) L x ^ 2 -
        taylorHomogeneousTerm (2 * ρ + 2) L x))) := by
  have hV := A.tendsto_pertV_div_pow hρ hvanish x
  have hR := A.tendsto_pertV_sub_linJet_div_pow hρ hvanish x
  have hengine := tendsto_exp_neg_sub_one_add_linear_div_pow hρ hV hR
  have := hengine.const_mul (quadKernel H x)
  refine this.congr' ?_
  filter_upwards [eventually_smul_mem_ball A.taylorRadius_pos x] with h hmem
  unfold residual
  rw [A.weight_eq_quadKernel_mul (A.taylorBall_subset hmem)]
  ring

end HigherLaplaceDomain

/-! ### Domination of the residual -/

/-- Polynomial growth is stable under absolute values. -/
theorem HasPolynomialGrowth.abs {f : EuclidD d → ℝ} (hf : HasPolynomialGrowth f) :
    HasPolynomialGrowth fun x ↦ |f x| := by
  obtain ⟨C, n, hC, h⟩ := hf
  exact ⟨C, n, hC, fun x ↦ by rw [abs_abs]; exact h x⟩

theorem hasPolynomialGrowth_of_eq {f g : EuclidD d → ℝ} (hg : HasPolynomialGrowth g)
    (h : ∀ x, f x = g x) : HasPolynomialGrowth f := by
  obtain ⟨C, n, hC, hb⟩ := hg
  exact ⟨C, n, hC, fun x ↦ by rw [h x]; exact hb x⟩

/-- The sum of the absolute Taylor terms entering the linear jet. -/
noncomputable def absJetSum (L : EuclidD d → ℝ) (ρ : ℕ) (x : EuclidD d) : ℝ :=
  ∑ j ∈ Finset.range ρ, |taylorHomogeneousTerm (ρ + j + 2) L x|

theorem absJetSum_nonneg (L : EuclidD d → ℝ) (ρ : ℕ) (x : EuclidD d) : 0 ≤ absJetSum L ρ x :=
  Finset.sum_nonneg fun _ _ ↦ abs_nonneg _

theorem continuous_absJetSum (L : EuclidD d → ℝ) (ρ : ℕ) : Continuous (absJetSum L ρ) :=
  continuous_finsetSum _ fun _ _ ↦ (taylorHomogeneousTerm_continuous _ L).abs

theorem hasPolynomialGrowth_absJetSum (L : EuclidD d → ℝ) (ρ : ℕ) :
    HasPolynomialGrowth (absJetSum L ρ) := by
  have := hasPolynomialGrowth_finset_combo
    (fun j x ↦ |taylorHomogeneousTerm (ρ + j + 2) L x|)
    (fun j ↦ (taylorHomogeneousTerm_hasPolynomialGrowth _ L).abs) (fun _ ↦ 1) (Finset.range ρ)
  refine hasPolynomialGrowth_of_eq this fun x ↦ ?_
  unfold absJetSum
  simp only [one_mul]

theorem abs_linJet_le_absJetSum {L : EuclidD d → ℝ} {ρ : ℕ} {h : ℝ} (hh0 : 0 ≤ h) (hh1 : h ≤ 1)
    (x : EuclidD d) : |linJet L ρ h x| ≤ absJetSum L ρ x :=
  abs_linJet_le hh0 hh1 x

namespace HigherLaplaceDomain

variable {ρ : ℕ} {L : EuclidD d → ℝ} {H : Matrix (Fin d) (Fin d) ℝ}

/-- The polynomial majorant of the residual. -/
noncomputable def residualMajorant (L : EuclidD d → ℝ) (ρ : ℕ) (C₁ C₂ r : ℝ) (x : EuclidD d) :
    ℝ :=
  2 * C₁ ^ 2 * ‖x‖ ^ (2 * ρ + 4) + C₂ * ‖x‖ ^ (2 * ρ + 2) +
    r⁻¹ ^ (2 * ρ) * ‖x‖ ^ (2 * ρ) * (2 + absJetSum L ρ x)

theorem continuous_residualMajorant (L : EuclidD d → ℝ) (ρ : ℕ) (C₁ C₂ r : ℝ) :
    Continuous (residualMajorant L ρ C₁ C₂ r) := by
  unfold residualMajorant
  have := continuous_absJetSum L ρ
  fun_prop

theorem hasPolynomialGrowth_residualMajorant (L : EuclidD d → ℝ) (ρ : ℕ) (C₁ C₂ r : ℝ) :
    HasPolynomialGrowth (residualMajorant L ρ C₁ C₂ r) := by
  have hg : HasPolynomialGrowth
      ((2 * C₁ ^ 2) • (fun x : EuclidD d ↦ ‖x‖ ^ (2 * ρ + 4)) +
        C₂ • (fun x : EuclidD d ↦ ‖x‖ ^ (2 * ρ + 2)) +
        fun x ↦ (r⁻¹ ^ (2 * ρ) • fun x : EuclidD d ↦ ‖x‖ ^ (2 * ρ)) x *
          ((fun _ : EuclidD d ↦ (2 : ℝ)) + absJetSum L ρ) x) :=
    (((hasPolynomialGrowth_norm_pow _).const_smul _).add
      ((hasPolynomialGrowth_norm_pow _).const_smul _)).add
      (((hasPolynomialGrowth_norm_pow _).const_smul _).mul
        ((hasPolynomialGrowth_const 2).add (hasPolynomialGrowth_absJetSum L ρ)))
  refine hasPolynomialGrowth_of_eq hg fun x ↦ ?_
  unfold residualMajorant
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]

/-- **Domination of the residual**: uniformly for small `h`, the residual is bounded
by a polynomial times a Gaussian. -/
theorem exists_residual_bound (A : HigherLaplaceDomain (2 * ρ + 3) L H) (hρ : 0 < ρ)
    (hvanish : ∀ j, 3 ≤ j → j < ρ + 2 → taylorHomogeneousTerm j L = 0) :
    ∃ (Φ : EuclidD d → ℝ) (c : ℝ), 0 < c ∧ Continuous Φ ∧ HasPolynomialGrowth Φ ∧
      ∀ᶠ h in 𝓝[>] (0 : ℝ), ∀ x : EuclidD d,
        |A.residual ρ h x| ≤ Φ x * Real.exp (-(c * ‖x‖ ^ 2)) := by
  obtain ⟨C₁, hC₁0, hC₁⟩ := A.exists_abs_pertV_div_pow_le hρ hvanish
  obtain ⟨C₂, hC₂0, hC₂⟩ := A.exists_abs_pertV_sub_linJet_div_pow_le hρ hvanish
  have hr : 0 < A.taylorRadius := A.taylorRadius_pos
  have hc : 0 < min A.c (A.lambda / 2) := lt_min A.c_pos (by linarith [A.lambda_pos])
  refine ⟨residualMajorant L ρ C₁ C₂ A.taylorRadius, min A.c (A.lambda / 2), hc,
    continuous_residualMajorant L ρ C₁ C₂ _, hasPolynomialGrowth_residualMajorant L ρ C₁ C₂ _,
    ?_⟩
  filter_upwards [Ioo_mem_nhdsGT (zero_lt_one' ℝ)] with h hh x
  obtain ⟨hh0, hh1⟩ := hh
  have hE0 : 0 ≤ Real.exp (-(min A.c (A.lambda / 2) * ‖x‖ ^ 2)) := (Real.exp_pos _).le
  have hK : quadKernel H x ≤ Real.exp (-(min A.c (A.lambda / 2) * ‖x‖ ^ 2)) :=
    (A.quadKernel_le x).trans (Real.exp_le_exp.mpr (neg_le_neg
      (mul_le_mul_of_nonneg_right (min_le_right _ _) (sq_nonneg _))))
  have hW : A.weight h x ≤ Real.exp (-(min A.c (A.lambda / 2) * ‖x‖ ^ 2)) :=
    (A.weight_le hh0 x).trans (Real.exp_le_exp.mpr (neg_le_neg
      (mul_le_mul_of_nonneg_right (min_le_left _ _) (sq_nonneg _))))
  have hK0 : 0 ≤ quadKernel H x := (quadKernel_pos H x).le
  have hW0 := A.weight_nonneg h x
  have hp : 0 < h ^ (2 * ρ) := pow_pos hh0 _
  have hJ0 := absJetSum_nonneg L ρ x
  set E := Real.exp (-(min A.c (A.lambda / 2) * ‖x‖ ^ 2)) with hE_def
  have hΦsplit : residualMajorant L ρ C₁ C₂ A.taylorRadius x * E =
      E * (2 * C₁ ^ 2 * ‖x‖ ^ (2 * ρ + 4)) + E * (C₂ * ‖x‖ ^ (2 * ρ + 2)) +
        E * (A.taylorRadius⁻¹ ^ (2 * ρ) * ‖x‖ ^ (2 * ρ) * (2 + absJetSum L ρ x)) := by
    unfold residualMajorant
    ring
  have hterm1 : 0 ≤ E * (2 * C₁ ^ 2 * ‖x‖ ^ (2 * ρ + 4)) := by positivity
  have hterm2 : 0 ≤ E * (C₂ * ‖x‖ ^ (2 * ρ + 2)) := by positivity
  have hterm3 : 0 ≤ E * (A.taylorRadius⁻¹ ^ (2 * ρ) * ‖x‖ ^ (2 * ρ) * (2 + absJetSum L ρ x)) :=
    mul_nonneg hE0 (mul_nonneg (by positivity) (by linarith))
  rw [hΦsplit]
  by_cases hmem : h • x ∈ Metric.ball (0 : EuclidD d) A.taylorRadius
  · -- inner region
    have hU : h • x ∈ A.U := A.taylorBall_subset hmem
    have hV := hC₁ hh0 hmem
    have hVS := hC₂ hh0 hmem
    have hres : A.residual ρ h x = quadKernel H x *
        ((Real.exp (-(pertV L H h x)) - 1 + linJet L ρ h x) / h ^ (2 * ρ)) := by
      unfold residual
      rw [A.weight_eq_quadKernel_mul hU]
      ring
    have hexp := abs_exp_neg_sub_one_add_le_endpoint (pertV L H h x)
    have hsq : pertV L H h x ^ 2 / h ^ (2 * ρ) = (|pertV L H h x| / h ^ ρ) ^ 2 := by
      rw [div_pow, sq_abs, ← pow_mul, mul_comm ρ 2]
    have ha0 : 0 ≤ |pertV L H h x| / h ^ ρ := by positivity
    have hVsq : (|pertV L H h x| / h ^ ρ) ^ 2 ≤ (C₁ * ‖x‖ ^ (ρ + 2)) ^ 2 :=
      pow_le_pow_left₀ ha0 hV 2
    have hpow : (C₁ * ‖x‖ ^ (ρ + 2)) ^ 2 = C₁ ^ 2 * ‖x‖ ^ (2 * ρ + 4) := by ring
    have hb0 : 0 ≤ |pertV L H h x - linJet L ρ h x| / h ^ (2 * ρ) := by positivity
    have hnum : |Real.exp (-(pertV L H h x)) - 1 + linJet L ρ h x| ≤
        pertV L H h x ^ 2 * (1 + Real.exp (-(pertV L H h x))) +
          |pertV L H h x - linJet L ρ h x| := by
      calc |Real.exp (-(pertV L H h x)) - 1 + linJet L ρ h x|
          = |(Real.exp (-(pertV L H h x)) - 1 + pertV L H h x) -
              (pertV L H h x - linJet L ρ h x)| := by ring_nf
        _ ≤ |Real.exp (-(pertV L H h x)) - 1 + pertV L H h x| +
              |pertV L H h x - linJet L ρ h x| := abs_sub _ _
        _ ≤ _ := add_le_add hexp le_rfl
    have h1 : |A.residual ρ h x| ≤
        quadKernel H x * (pertV L H h x ^ 2 / h ^ (2 * ρ)) +
          (quadKernel H x * Real.exp (-(pertV L H h x))) * (pertV L H h x ^ 2 / h ^ (2 * ρ)) +
          quadKernel H x * (|pertV L H h x - linJet L ρ h x| / h ^ (2 * ρ)) := by
      rw [hres, abs_mul, abs_of_nonneg hK0, abs_div, abs_of_pos hp]
      calc quadKernel H x * (|Real.exp (-(pertV L H h x)) - 1 + linJet L ρ h x| / h ^ (2 * ρ))
          ≤ quadKernel H x * ((pertV L H h x ^ 2 * (1 + Real.exp (-(pertV L H h x))) +
              |pertV L H h x - linJet L ρ h x|) / h ^ (2 * ρ)) :=
            mul_le_mul_of_nonneg_left (div_le_div_of_nonneg_right hnum hp.le) hK0
        _ = _ := by ring
    have hWK : quadKernel H x * Real.exp (-(pertV L H h x)) ≤ E := by
      rw [← A.weight_eq_quadKernel_mul hU]
      exact hW
    have h2 : quadKernel H x * (pertV L H h x ^ 2 / h ^ (2 * ρ)) ≤
        E * (C₁ ^ 2 * ‖x‖ ^ (2 * ρ + 4)) := by
      rw [hsq, ← hpow]
      exact mul_le_mul hK hVsq (by positivity) hE0
    have h3 : (quadKernel H x * Real.exp (-(pertV L H h x))) * (pertV L H h x ^ 2 / h ^ (2 * ρ)) ≤
        E * (C₁ ^ 2 * ‖x‖ ^ (2 * ρ + 4)) := by
      rw [hsq, ← hpow]
      exact mul_le_mul hWK hVsq (by positivity) hE0
    have h4 : quadKernel H x * (|pertV L H h x - linJet L ρ h x| / h ^ (2 * ρ)) ≤
        E * (C₂ * ‖x‖ ^ (2 * ρ + 2)) := mul_le_mul hK hVS hb0 hE0
    have hsum : E * (2 * C₁ ^ 2 * ‖x‖ ^ (2 * ρ + 4)) =
        E * (C₁ ^ 2 * ‖x‖ ^ (2 * ρ + 4)) + E * (C₁ ^ 2 * ‖x‖ ^ (2 * ρ + 4)) := by ring
    linarith [h1, h2, h3, h4, hterm3, hsum]
  · -- outer region
    have hr_le : A.taylorRadius ≤ h * ‖x‖ := by
      rw [Metric.mem_ball, dist_zero_right, norm_smul, Real.norm_eq_abs, abs_of_pos hh0] at hmem
      exact not_lt.mp hmem
    have hinv : 1 / h ≤ ‖x‖ / A.taylorRadius := by
      rw [div_le_div_iff₀ hh0 hr]
      linarith
    have hinvpow : (1 / h) ^ (2 * ρ) ≤ (‖x‖ / A.taylorRadius) ^ (2 * ρ) :=
      pow_le_pow_left₀ (by positivity) hinv _
    have hS := abs_linJet_le_absJetSum (L := L) (ρ := ρ) hh0.le hh1.le x
    have hnum : |A.weight h x - quadKernel H x + quadKernel H x * linJet L ρ h x| ≤
        E + E + E * absJetSum L ρ x := by
      calc |A.weight h x - quadKernel H x + quadKernel H x * linJet L ρ h x|
          ≤ |A.weight h x - quadKernel H x| + |quadKernel H x * linJet L ρ h x| :=
            abs_add_le _ _
        _ ≤ (A.weight h x + quadKernel H x) + quadKernel H x * absJetSum L ρ x := by
            refine add_le_add ?_ ?_
            · calc |A.weight h x - quadKernel H x| ≤ |A.weight h x| + |quadKernel H x| :=
                    abs_sub _ _
                _ = _ := by rw [abs_of_nonneg hW0, abs_of_nonneg hK0]
            · rw [abs_mul, abs_of_nonneg hK0]
              exact mul_le_mul_of_nonneg_left hS hK0
        _ ≤ E + E + E * absJetSum L ρ x :=
            add_le_add (add_le_add hW hK) (mul_le_mul_of_nonneg_right hK hJ0)
    have hres : |A.residual ρ h x| =
        |A.weight h x - quadKernel H x + quadKernel H x * linJet L ρ h x| * (1 / h) ^ (2 * ρ) := by
      unfold residual
      rw [abs_div, abs_of_pos hp, div_eq_mul_inv, one_div, inv_pow]
    have hnum0 : 0 ≤ E + E + E * absJetSum L ρ x := by positivity
    rw [hres]
    calc |A.weight h x - quadKernel H x + quadKernel H x * linJet L ρ h x| * (1 / h) ^ (2 * ρ)
        ≤ (E + E + E * absJetSum L ρ x) * (‖x‖ / A.taylorRadius) ^ (2 * ρ) :=
          mul_le_mul hnum hinvpow (by positivity) hnum0
      _ = E * (A.taylorRadius⁻¹ ^ (2 * ρ) * ‖x‖ ^ (2 * ρ) * (2 + absJetSum L ρ x)) := by
          rw [div_pow, div_eq_mul_inv, ← inv_pow]
          ring
      _ ≤ _ := by linarith [hterm1, hterm2]

/-! ### The integral layer at the rescaled integrand -/

/-- **Second-order expansion of the unnormalised rescaled integral**: with the linear
jet subtracted, the rate-`h^{2ρ}` limit is the Gaussian integral of `P · (½ Q² − R)`. -/
theorem tendsto_integral_residual (A : HigherLaplaceDomain (2 * ρ + 3) L H) (hρ : 0 < ρ)
    (hvanish : ∀ j, 3 ≤ j → j < ρ + 2 → taylorHomogeneousTerm j L = 0)
    {P : EuclidD d → ℝ} (hP_cont : Continuous P) (hP_growth : HasPolynomialGrowth P) :
    Tendsto (fun h : ℝ ↦ ((∫ x : EuclidD d, A.toLocalLaplaceDomain.integrand P h x) -
        (∫ x : EuclidD d, P x * quadKernel H x) +
        ∑ j ∈ Finset.range ρ, h ^ (ρ + j) * ∫ x : EuclidD d,
          P x * (quadKernel H x * taylorHomogeneousTerm (ρ + j + 2) L x)) / h ^ (2 * ρ))
      (𝓝[>] (0 : ℝ))
      (𝓝 (∫ x : EuclidD d, P x * (quadKernel H x *
        (1 / 2 * taylorHomogeneousTerm (ρ + 2) L x ^ 2 -
          taylorHomogeneousTerm (2 * ρ + 2) L x)))) := by
  have hH := A.hH_posDef
  obtain ⟨Φ, c, hc, hΦc, hΦg, hbound⟩ := A.exists_residual_bound hρ hvanish
  have hlim : ∀ᵐ x ∂(volume : Measure (EuclidD d)),
      Tendsto (fun h : ℝ ↦ P x * ((A.weight h x - quadKernel H x +
        quadKernel H x * ∑ j ∈ Finset.range ρ, h ^ (ρ + j) *
          taylorHomogeneousTerm (ρ + j + 2) L x) / h ^ (2 * ρ)))
        (𝓝[>] (0 : ℝ)) (𝓝 (P x * (quadKernel H x *
          (1 / 2 * taylorHomogeneousTerm (ρ + 2) L x ^ 2 -
            taylorHomogeneousTerm (2 * ρ + 2) L x)))) :=
    Eventually.of_forall fun x ↦ (A.tendsto_residual hρ hvanish x).const_mul (P x)
  have hmeas : ∀ᶠ h in 𝓝[>] (0 : ℝ), AEStronglyMeasurable
      (fun x ↦ P x * ((A.weight h x - quadKernel H x +
        quadKernel H x * ∑ j ∈ Finset.range ρ, h ^ (ρ + j) *
          taylorHomogeneousTerm (ρ + j + 2) L x) / h ^ (2 * ρ)))
        (volume : Measure (EuclidD d)) := by
    filter_upwards with h
    exact (hP_cont.measurable.mul ((((A.measurable_weight h).sub
      (quadKernel_continuous H).measurable).add ((quadKernel_continuous H).measurable.mul
        (continuous_linJet L ρ h).measurable)).div_const _)).aestronglyMeasurable
  have hG : Integrable (fun x : EuclidD d ↦ (|P x| * Φ x) * Real.exp (-c * ‖x‖ ^ 2)) :=
    integrable_mul_exp_neg_mul_sq_of_polynomialGrowth hc
      (hP_cont.abs.mul hΦc).aestronglyMeasurable (hP_growth.abs.mul hΦg)
  have hdom : ∀ᶠ h in 𝓝[>] (0 : ℝ), ∀ᵐ x ∂(volume : Measure (EuclidD d)),
      ‖P x * ((A.weight h x - quadKernel H x +
        quadKernel H x * ∑ j ∈ Finset.range ρ, h ^ (ρ + j) *
          taylorHomogeneousTerm (ρ + j + 2) L x) / h ^ (2 * ρ))‖ ≤
        (|P x| * Φ x) * Real.exp (-c * ‖x‖ ^ 2) := by
    filter_upwards [hbound] with h hb
    refine Eventually.of_forall fun x ↦ ?_
    have := mul_le_mul_of_nonneg_left (hb x) (abs_nonneg (P x))
    rw [Real.norm_eq_abs, abs_mul, neg_mul, mul_assoc]
    exact this
  have hintw : ∀ᶠ h in 𝓝[>] (0 : ℝ),
      Integrable (fun x ↦ P x * A.weight h x) (volume : Measure (EuclidD d)) := by
    filter_upwards [self_mem_nhdsWithin] with h hh
    exact (A.toLocalLaplaceDomain.integrable_integrand hP_cont hP_growth hh).congr
      (Eventually.of_forall fun x ↦ A.toLocalLaplaceDomain.integrand_eq_mul_weight P h x)
  have hintw₀ : Integrable (fun x ↦ P x * quadKernel H x) (volume : Measure (EuclidD d)) :=
    integrable_mul_quadKernel_of_polynomialGrowth hH hP_cont.aestronglyMeasurable hP_growth
  have hintB : ∀ j, Integrable
      (fun x ↦ P x * (quadKernel H x * taylorHomogeneousTerm (ρ + j + 2) L x))
      (volume : Measure (EuclidD d)) := by
    intro j
    have := integrable_mul_quadKernel_of_polynomialGrowth hH
      (hP_cont.mul (taylorHomogeneousTerm_continuous (ρ + j + 2) L)).aestronglyMeasurable
      (hP_growth.mul (taylorHomogeneousTerm_hasPolynomialGrowth (ρ + j + 2) L))
    exact this.congr (Eventually.of_forall fun x ↦ by simp only [Pi.mul_apply]; ring)
  have hmain := tendsto_integral_linear_subtracted (μ := (volume : Measure (EuclidD d))) P
    (quadKernel H) (fun x ↦ 1 / 2 * taylorHomogeneousTerm (ρ + 2) L x ^ 2 -
      taylorHomogeneousTerm (2 * ρ + 2) L x)
    (fun h x ↦ A.weight h x) (fun m x ↦ taylorHomogeneousTerm (m + 2) L x) ρ
    hlim hmeas hG hdom hintw hintw₀ hintB
  refine hmain.congr' (Eventually.of_forall fun h ↦ ?_)
  simp only [← A.toLocalLaplaceDomain.integrand_eq_mul_weight]

/-! ### The normalisation layer -/

/-- The covariance coefficient in integral form. -/
theorem cov_coeff_eq {H : Matrix (Fin d) (Fin d) ℝ} (hH : H.PosDef) (P Q : EuclidD d → ℝ) :
    ((∫ x : EuclidD d, P x * (quadKernel H x * Q x)) -
        gaussianExpectation H P * ∫ x : EuclidD d, (1 : ℝ) * (quadKernel H x * Q x)) /
      (∫ x : EuclidD d, (1 : ℝ) * quadKernel H x) = gaussianCovariance H P Q := by
  simp only [one_mul]
  unfold gaussianCovariance gaussianExpectation
  have h1 : (∫ x : EuclidD d, P x * (quadKernel H x * Q x)) =
      ∫ x : EuclidD d, (P x * Q x) * quadKernel H x :=
    integral_congr_ae (Eventually.of_forall fun x ↦ by ring)
  have h2 : (∫ x : EuclidD d, quadKernel H x * Q x) = ∫ x : EuclidD d, Q x * quadKernel H x :=
    integral_congr_ae (Eventually.of_forall fun x ↦ by ring)
  rw [h1, h2]
  have hZ := (integral_quadKernel_pos hH).ne'
  field_simp

theorem gaussianExpectation_eq_div_one {H : Matrix (Fin d) (Fin d) ℝ} (P : EuclidD d → ℝ) :
    (∫ x : EuclidD d, P x * quadKernel H x) / (∫ x : EuclidD d, (1 : ℝ) * quadKernel H x) =
      gaussianExpectation H P := by
  simp only [one_mul]
  rfl

theorem gaussianExpectation_eq_div_one' {H : Matrix (Fin d) (Fin d) ℝ} (Q : EuclidD d → ℝ) :
    (∫ x : EuclidD d, (1 : ℝ) * (quadKernel H x * Q x)) /
      (∫ x : EuclidD d, (1 : ℝ) * quadKernel H x) = gaussianExpectation H Q := by
  simp only [one_mul]
  unfold gaussianExpectation
  congr 1
  exact integral_congr_ae (Eventually.of_forall fun x ↦ by ring)

/-- **The second-order expansion of the rescaled moment** (germbij Q2, Laplace
layer): for a loss whose Taylor terms of degree `3, …, ρ+1` vanish, with
`Q = T_{ρ+2} L` and `R = T_{2ρ+2} L`,
`(M_h(P) − E_γ P + ∑_{j<ρ} h^{ρ+j} Cov_γ(P, T_{ρ+j+2})) / h^{2ρ}
  → Cov_γ(P, ½Q² − R) − E_γ Q · Cov_γ(P, Q)`. -/
theorem tendsto_rescaledMoment_second_order (A : HigherLaplaceDomain (2 * ρ + 3) L H)
    (hρ : 0 < ρ)
    (hvanish : ∀ j, 3 ≤ j → j < ρ + 2 → taylorHomogeneousTerm j L = 0)
    {P : EuclidD d → ℝ} (hP_cont : Continuous P) (hP_growth : HasPolynomialGrowth P) :
    Tendsto (fun h : ℝ ↦ (A.rescaledMoment P h - gaussianExpectation H P +
        ∑ j ∈ Finset.range ρ, h ^ (ρ + j) *
          gaussianCovariance H P (taylorHomogeneousTerm (ρ + j + 2) L)) / h ^ (2 * ρ))
      (𝓝[>] (0 : ℝ))
      (𝓝 (gaussianCovariance H P (fun x ↦ 1 / 2 * taylorHomogeneousTerm (ρ + 2) L x ^ 2 -
          taylorHomogeneousTerm (2 * ρ + 2) L x) -
        gaussianExpectation H (taylorHomogeneousTerm (ρ + 2) L) *
          gaussianCovariance H P (taylorHomogeneousTerm (ρ + 2) L))) := by
  have hH := A.hH_posDef
  have hN := A.tendsto_integral_residual hρ hvanish hP_cont hP_growth
  have hZ := A.tendsto_integral_residual hρ hvanish (P := fun _ ↦ (1 : ℝ)) continuous_const
    (hasPolynomialGrowth_const 1)
  have hZ₀ : 0 < ∫ x : EuclidD d, (1 : ℝ) * quadKernel H x := by
    simp only [one_mul]
    exact integral_quadKernel_pos hH
  have key := tendsto_normalized_div_pow_of_linear_subtracted
    (N := fun h ↦ ∫ x : EuclidD d, A.toLocalLaplaceDomain.integrand P h x)
    (Z := fun h ↦ ∫ x : EuclidD d, A.toLocalLaplaceDomain.integrand (fun _ ↦ (1 : ℝ)) h x)
    (a := fun m ↦ ∫ x : EuclidD d, P x * (quadKernel H x * taylorHomogeneousTerm (m + 2) L x))
    (b := fun m ↦ ∫ x : EuclidD d, (1 : ℝ) * (quadKernel H x * taylorHomogeneousTerm (m + 2) L x))
    hρ hZ₀ hN hZ
  rw [gaussianExpectation_eq_div_one] at key
  simp only [cov_coeff_eq hH, gaussianExpectation_eq_div_one'] at key
  exact key

end HigherLaplaceDomain

end Laplace.Multi
