/-
Copyright (c) 2026 Timaeus Research. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniel Murfet
-/
import Mathlib
import Laplace.Multi.WeightedLocalization

/-!
# Weighted-jet induction for losses with a weighted Taylor package (germbij §7.4(b))

The analytic (all-orders) version of the weighted-jet induction. A loss `L` carries a
*weighted jet* relative to the leading part `P`: coefficients `coeff α` for the exponents of
weighted degree `> D`, such that for every `N` the difference between `L − P` and the
weighted polynomial over the finitely many exponents of total degree `< N`
(`sBelow W N`) is `O(‖x‖^N)` on the localization region `U`. This is the ordinary Taylor
expansion of `L − P` regrouped by weighted degree, and it is all that the induction uses:
at grade `k` one works with `N = k + 1`, where the remainder rescales to
`O(ε^{k+1−D} ‖u‖^{k+1})` — one order below the grade — because every weight is at least one.

The one-grade engine of `KernelComparison` is applied to the exact rescaled correction
`Vgen P L ε u = L (dil ε u)/ε^D − P u` (so the masked moments do not depend on the grade),
decomposed as `corr (sBelow (k+1)) coeff ε u + remainder`. The strong induction yields equal
weighted jets (`weightedJet_coeff_eq_of_superPoly`), hence `L₁ − L₂ = O(‖x‖^N)` for every `N`
on `U` (`weightedJet_sub_isBigO_of_superPoly`).
-/

open Real MeasureTheory Filter Topology

namespace Laplace.Multi

namespace IntWeights

variable {ι : Type*} [Fintype ι] (W : IntWeights ι)

/-! ### Finite exponent sets -/

theorem totalDeg_le_wdeg (α : ι → ℕ) : totalDeg α ≤ W.wdeg α :=
  Finset.sum_le_sum fun i _ ↦ Nat.le_mul_of_pos_left (α i) (W.a_pos i)

open Classical in
/-- The exponents of weighted degree `> D` and total degree `< N`. -/
noncomputable def sBelow (N : ℕ) : Finset (ι → ℕ) :=
  (Fintype.piFinset fun _ : ι ↦ Finset.range N).filter
    (fun α ↦ W.D < W.wdeg α ∧ totalDeg α < N)

theorem mem_sBelow {N : ℕ} {α : ι → ℕ} :
    α ∈ W.sBelow N ↔ W.D < W.wdeg α ∧ totalDeg α < N := by
  classical
  unfold sBelow
  rw [Finset.mem_filter, Fintype.mem_piFinset]
  constructor
  · rintro ⟨_, h⟩
    exact h
  · rintro ⟨h1, h2⟩
    refine ⟨fun i ↦ Finset.mem_range.mpr ?_, h1, h2⟩
    exact lt_of_le_of_lt (Finset.single_le_sum (f := α) (fun j _ ↦ Nat.zero_le _)
      (Finset.mem_univ i)) h2

theorem sBelow_wdeg_pos {N : ℕ} : ∀ α ∈ W.sBelow N, W.D < W.wdeg α :=
  fun _ hα ↦ (W.mem_sBelow.mp hα).1

/-- Every exponent of weighted degree in `(D, k]` lies in `sBelow (k + 1)`. -/
theorem mem_sBelow_succ_of_wdeg_le {k : ℕ} {α : ι → ℕ} (hD : W.D < W.wdeg α)
    (hk : W.wdeg α ≤ k) : α ∈ W.sBelow (k + 1) :=
  W.mem_sBelow.mpr ⟨hD, lt_of_le_of_lt (W.totalDeg_le_wdeg α) (Nat.lt_succ_of_le hk)⟩

/-! ### The weighted jet package -/

/-- A weighted Taylor package for `L` relative to the leading part `P` on `U`: coefficients
of the corrections, with the truncation at total degree `< N` leaving an `O(‖x‖^N)`
remainder on `U`. -/
structure WeightedJet (P L : (ι → ℝ) → ℝ) (U : Set (ι → ℝ)) where
  /-- The weighted Taylor coefficients of `L − P` (only exponents of weighted degree `> D`
  are used). -/
  coeff : (ι → ℕ) → ℝ
  remainder_bound : ∀ N : ℕ, ∃ C : ℝ, 0 ≤ C ∧ ∀ x ∈ U,
    |L x - P x - wpoly (W.sBelow N) coeff x| ≤ C * ‖x‖ ^ N

/-- The exact rescaled correction `L (dil ε u)/ε^D − P u`. -/
noncomputable def Vgen (P L : (ι → ℝ) → ℝ) (ε : ℝ) (u : ι → ℝ) : ℝ :=
  L (W.dil ε u) / ε ^ W.D - P u

omit [Fintype ι] in
theorem measurable_Vgen {P L : (ι → ℝ) → ℝ} (hPm : Measurable P) (hLm : Measurable L)
    (ε : ℝ) : Measurable (W.Vgen P L ε) :=
  ((hLm.comp (W.measurable_dil ε)).div_const _).sub hPm

omit W in
/-- The truncated remainder `L − P − wpoly (sBelow N) coeff`. -/
noncomputable def WeightedJet.rem {W : IntWeights ι} {P L : (ι → ℝ) → ℝ} {U : Set (ι → ℝ)}
    (J : W.WeightedJet P L U) (N : ℕ) (x : ι → ℝ) : ℝ :=
  L x - P x - wpoly (W.sBelow N) J.coeff x

/-- The decomposition of the rescaled correction into the polynomial correction and the
rescaled remainder. -/
theorem Vgen_eq {P L : (ι → ℝ) → ℝ} {U : Set (ι → ℝ)}
    (hPqh : ∀ ε : ℝ, 0 < ε → ∀ u, P (W.dil ε u) = ε ^ W.D * P u)
    (J : W.WeightedJet P L U) (N : ℕ) {ε : ℝ} (hε : 0 < ε) (u : ι → ℝ) :
    W.Vgen P L ε u = W.corr (W.sBelow N) J.coeff ε u + J.rem N (W.dil ε u) / ε ^ W.D := by
  unfold Vgen WeightedJet.rem
  rw [hPqh ε hε, W.wpoly_dil _ _ W.sBelow_wdeg_pos]
  have hne : (ε ^ W.D : ℝ) ≠ 0 := (pow_pos hε _).ne'
  field_simp
  ring

/-- The dilation contracts the sup norm for `ε ≤ 1`. -/
theorem norm_dil_le {ε : ℝ} (hε : 0 ≤ ε) (hε1 : ε ≤ 1) (u : ι → ℝ) :
    ‖W.dil ε u‖ ≤ ε * ‖u‖ := by
  rw [pi_norm_le_iff_of_nonneg (by positivity)]
  intro i
  rw [dil_apply, Real.norm_eq_abs, abs_mul, abs_of_nonneg (pow_nonneg hε _)]
  have h1 : ε ^ W.a i ≤ ε := by
    have := pow_le_pow_of_le_one hε hε1 (W.a_pos i)
    rwa [pow_one] at this
  calc ε ^ W.a i * |u i| ≤ ε * |u i| := mul_le_mul_of_nonneg_right h1 (abs_nonneg _)
    _ ≤ ε * ‖u‖ := mul_le_mul_of_nonneg_left (norm_le_pi_norm u i) hε

/-- **Rescaled remainder bound**: on the mask, for `0 < ε ≤ 1`,
`|rem N (dil ε u)| / ε^D ≤ C ε^{N−D} ‖u‖^N`. -/
theorem exists_rem_dil_div_le {P L : (ι → ℝ) → ℝ} {U : Set (ι → ℝ)} (J : W.WeightedJet P L U)
    {N : ℕ} (hN : W.D ≤ N) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ ε : ℝ, 0 < ε → ε ≤ 1 → ∀ u ∈ W.mask U ε,
      |J.rem N (W.dil ε u)| / ε ^ W.D ≤ C * ε ^ (N - W.D) * ‖u‖ ^ N := by
  obtain ⟨C, hC0, hC⟩ := J.remainder_bound N
  refine ⟨C, hC0, fun ε hε hε1 u hu ↦ ?_⟩
  have hpos : (0 : ℝ) < ε ^ W.D := pow_pos hε _
  rw [div_le_iff₀ hpos]
  calc |J.rem N (W.dil ε u)| ≤ C * ‖W.dil ε u‖ ^ N := hC _ hu
    _ ≤ C * (ε * ‖u‖) ^ N :=
        mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (norm_nonneg _) (W.norm_dil_le hε.le hε1 u) N)
          hC0
    _ = C * ε ^ (N - W.D) * ‖u‖ ^ N * ε ^ W.D := by
        rw [mul_pow, show ε ^ N = ε ^ (N - W.D) * ε ^ W.D by
          rw [← pow_add, Nat.sub_add_cancel hN]]
        ring

/-! ### Pointwise limits and uniform bounds of the exact correction -/

theorem polyBoundedBy_norm_pow {P : (ι → ℝ) → ℝ} {κ : ℝ} (hκ : 0 ≤ κ) (hP0 : ∀ u, 0 ≤ P u)
    (hcoer : ∀ u i, |u i| ^ W.D ≤ κ * P u ^ W.a i) (N : ℕ) :
    PolyBoundedBy P fun u : ι → ℝ ↦ ‖u‖ ^ N := by
  have hnorm : PolyBoundedBy P fun u : ι → ℝ ↦ ‖u‖ := by
    have hsum : PolyBoundedBy P fun u : ι → ℝ ↦ ∑ i, |u i| :=
      PolyBoundedBy.finset_sum hP0 Finset.univ fun i _ ↦
        (W.polyBoundedBy_coord hκ hP0 hcoer i).abs
    refine hsum.of_le fun u ↦ ?_
    rw [abs_norm, abs_of_nonneg (Finset.sum_nonneg fun i _ ↦ abs_nonneg _)]
    rw [pi_norm_le_iff_of_nonneg (Finset.sum_nonneg fun i _ ↦ abs_nonneg _)]
    intro i
    rw [Real.norm_eq_abs]
    exact Finset.single_le_sum (f := fun j ↦ |u j|) (fun j _ ↦ abs_nonneg _) (Finset.mem_univ i)
  induction N with
  | zero => exact ⟨1, 0, zero_le_one, fun u ↦ by simp⟩
  | succ n ih =>
    refine (hnorm.mul hP0 ih).of_le fun u ↦ ?_
    rw [pow_succ']

variable {P L₁ L₂ : (ι → ℝ) → ℝ} {U : Set (ι → ℝ)}

/-- The exact correction vanishes pointwise. -/
theorem tendsto_Vgen (hPqh : ∀ ε : ℝ, 0 < ε → ∀ u, P (W.dil ε u) = ε ^ W.D * P u)
    (hU0 : U ∈ 𝓝 (0 : ι → ℝ)) (J : W.WeightedJet P L₁ U) (u : ι → ℝ) :
    Tendsto (fun ε : ℝ ↦ W.Vgen P L₁ ε u) (𝓝[>] (0 : ℝ)) (𝓝 0) := by
  obtain ⟨C, hC0, hC⟩ := W.exists_rem_dil_div_le J (N := W.D + 1) (by omega)
  have hcorr := W.tendsto_corr (W.sBelow (W.D + 1)) J.coeff W.sBelow_wdeg_pos u
  have hrem : Tendsto (fun ε : ℝ ↦ J.rem (W.D + 1) (W.dil ε u) / ε ^ W.D) (𝓝[>] (0 : ℝ))
      (𝓝 0) := by
    have hcont : Continuous fun ε : ℝ ↦ C * ε * ‖u‖ ^ (W.D + 1) := by
      fun_prop
    have hb := (hcont.tendsto 0).mono_left (nhdsWithin_le_nhds (s := Set.Ioi 0))
    rw [mul_zero, zero_mul] at hb
    refine squeeze_zero_norm' ?_ hb
    filter_upwards [W.eventually_mem_mask hU0 u, Ioc_mem_nhdsGT (zero_lt_one' ℝ)] with ε hu hε
    rw [Real.norm_eq_abs, abs_div, abs_of_pos (pow_pos hε.1 _)]
    have := hC ε hε.1 hε.2 u hu
    rwa [show W.D + 1 - W.D = 1 by omega, pow_one] at this
  have := hcorr.add hrem
  rw [add_zero] at this
  refine this.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with ε hε
  exact (W.Vgen_eq hPqh J (W.D + 1) hε u).symm

/-- **Pointwise leading-grade limit** of the exact correction difference. -/
theorem tendsto_Vgen_sub_div_pow (hPqh : ∀ ε : ℝ, 0 < ε → ∀ u, P (W.dil ε u) = ε ^ W.D * P u)
    (hU0 : U ∈ 𝓝 (0 : ι → ℝ)) (J₁ : W.WeightedJet P L₁ U) (J₂ : W.WeightedJet P L₂ U)
    {k : ℕ} (hk : W.D < k)
    (hlower : ∀ α ∈ W.sBelow (k + 1), W.wdeg α < k → J₁.coeff α = J₂.coeff α) (u : ι → ℝ) :
    Tendsto (fun ε : ℝ ↦ (W.Vgen P L₂ ε u - W.Vgen P L₁ ε u) / ε ^ (k - W.D))
      (𝓝[>] (0 : ℝ))
      (𝓝 (W.gradePart (W.sBelow (k + 1)) (fun α ↦ J₂.coeff α - J₁.coeff α) k u)) := by
  obtain ⟨C₁, hC₁0, hC₁⟩ := W.exists_rem_dil_div_le J₁ (N := k + 1) (by omega)
  obtain ⟨C₂, hC₂0, hC₂⟩ := W.exists_rem_dil_div_le J₂ (N := k + 1) (by omega)
  have hcorr := W.tendsto_corr_sub_div_pow (W.sBelow (k + 1)) J₁.coeff J₂.coeff hk hlower u
  have hrem : Tendsto (fun ε : ℝ ↦
      (J₂.rem (k + 1) (W.dil ε u) / ε ^ W.D - J₁.rem (k + 1) (W.dil ε u) / ε ^ W.D) /
        ε ^ (k - W.D)) (𝓝[>] (0 : ℝ)) (𝓝 0) := by
    have hcont : Continuous fun ε : ℝ ↦ (C₁ + C₂) * ε * ‖u‖ ^ (k + 1) := by fun_prop
    have hb := (hcont.tendsto 0).mono_left (nhdsWithin_le_nhds (s := Set.Ioi 0))
    rw [mul_zero, zero_mul] at hb
    refine squeeze_zero_norm' ?_ hb
    filter_upwards [W.eventually_mem_mask hU0 u, Ioc_mem_nhdsGT (zero_lt_one' ℝ)] with ε hu hε
    have hε0 := hε.1
    have hp : (0 : ℝ) < ε ^ (k - W.D) := pow_pos hε0 _
    have h1 := hC₁ ε hε0 hε.2 u hu
    have h2 := hC₂ ε hε0 hε.2 u hu
    have hkey : ε ^ (k + 1 - W.D) = ε * ε ^ (k - W.D) := by
      rw [← pow_succ', show k + 1 - W.D = k - W.D + 1 by omega]
    rw [hkey] at h1 h2
    rw [Real.norm_eq_abs, abs_div, abs_of_pos hp, div_le_iff₀ hp]
    calc |J₂.rem (k + 1) (W.dil ε u) / ε ^ W.D - J₁.rem (k + 1) (W.dil ε u) / ε ^ W.D|
        ≤ |J₂.rem (k + 1) (W.dil ε u)| / ε ^ W.D + |J₁.rem (k + 1) (W.dil ε u)| / ε ^ W.D := by
          have hpD : (0 : ℝ) < ε ^ W.D := pow_pos hε0 _
          rw [← sub_div, abs_div, abs_of_pos hpD, ← add_div]
          exact div_le_div_of_nonneg_right (abs_sub _ _) hpD.le
      _ ≤ C₂ * (ε * ε ^ (k - W.D)) * ‖u‖ ^ (k + 1) + C₁ * (ε * ε ^ (k - W.D)) * ‖u‖ ^ (k + 1) :=
          add_le_add h2 h1
      _ = (C₁ + C₂) * ε * ‖u‖ ^ (k + 1) * ε ^ (k - W.D) := by ring
  have := hcorr.add hrem
  rw [add_zero] at this
  refine this.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with ε hε
  rw [W.Vgen_eq hPqh J₁ (k + 1) hε u, W.Vgen_eq hPqh J₂ (k + 1) hε u]
  ring

/-- The uniform majorant of the divided exact correction difference. -/
noncomputable def VgenBound (J₁ : W.WeightedJet P L₁ U) (J₂ : W.WeightedJet P L₂ U) (k : ℕ)
    (C : ℝ) (u : ι → ℝ) : ℝ :=
  corrBound (W.sBelow (k + 1)) J₁.coeff J₂.coeff u + C * ‖u‖ ^ (k + 1)

theorem exists_abs_Vgen_sub_div_pow_le
    (hPqh : ∀ ε : ℝ, 0 < ε → ∀ u, P (W.dil ε u) = ε ^ W.D * P u)
    (J₁ : W.WeightedJet P L₁ U) (J₂ : W.WeightedJet P L₂ U) {k : ℕ} (hk : W.D < k)
    (hlower : ∀ α ∈ W.sBelow (k + 1), W.wdeg α < k → J₁.coeff α = J₂.coeff α) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ ε : ℝ, 0 < ε → ε ≤ 1 → ∀ u ∈ W.mask U ε,
      |W.Vgen P L₂ ε u - W.Vgen P L₁ ε u| / ε ^ (k - W.D) ≤ W.VgenBound J₁ J₂ k C u := by
  obtain ⟨C₁, hC₁0, hC₁⟩ := W.exists_rem_dil_div_le J₁ (N := k + 1) (by omega)
  obtain ⟨C₂, hC₂0, hC₂⟩ := W.exists_rem_dil_div_le J₂ (N := k + 1) (by omega)
  refine ⟨C₁ + C₂, by positivity, fun ε hε hε1 u hu ↦ ?_⟩
  have hp : (0 : ℝ) < ε ^ (k - W.D) := pow_pos hε _
  have hcorr := W.abs_corr_sub_div_pow_le (W.sBelow (k + 1)) J₁.coeff J₂.coeff hk hlower hε hε1 u
  have h1 := hC₁ ε hε hε1 u hu
  have h2 := hC₂ ε hε hε1 u hu
  have hkey : ε ^ (k + 1 - W.D) = ε * ε ^ (k - W.D) := by
    rw [← pow_succ', show k + 1 - W.D = k - W.D + 1 by omega]
  rw [hkey] at h1 h2
  have hε' : ε * ε ^ (k - W.D) ≤ 1 * ε ^ (k - W.D) := mul_le_mul_of_nonneg_right hε1 hp.le
  unfold VgenBound
  rw [W.Vgen_eq hPqh J₁ (k + 1) hε u, W.Vgen_eq hPqh J₂ (k + 1) hε u]
  have hsplit : |W.corr (W.sBelow (k + 1)) J₂.coeff ε u + J₂.rem (k + 1) (W.dil ε u) / ε ^ W.D -
      (W.corr (W.sBelow (k + 1)) J₁.coeff ε u + J₁.rem (k + 1) (W.dil ε u) / ε ^ W.D)| ≤
      |W.corr (W.sBelow (k + 1)) J₂.coeff ε u - W.corr (W.sBelow (k + 1)) J₁.coeff ε u| +
        (|J₂.rem (k + 1) (W.dil ε u)| / ε ^ W.D + |J₁.rem (k + 1) (W.dil ε u)| / ε ^ W.D) := by
    have hpD : (0 : ℝ) < ε ^ W.D := pow_pos hε _
    have hsub : |J₂.rem (k + 1) (W.dil ε u) / ε ^ W.D - J₁.rem (k + 1) (W.dil ε u) / ε ^ W.D| ≤
        |J₂.rem (k + 1) (W.dil ε u)| / ε ^ W.D + |J₁.rem (k + 1) (W.dil ε u)| / ε ^ W.D := by
      rw [← sub_div, abs_div, abs_of_pos hpD, ← add_div]
      exact div_le_div_of_nonneg_right (abs_sub _ _) hpD.le
    calc _ = |(W.corr (W.sBelow (k + 1)) J₂.coeff ε u - W.corr (W.sBelow (k + 1)) J₁.coeff ε u) +
          (J₂.rem (k + 1) (W.dil ε u) / ε ^ W.D - J₁.rem (k + 1) (W.dil ε u) / ε ^ W.D)| := by
          ring_nf
      _ ≤ _ := (abs_add_le _ _).trans (add_le_add le_rfl hsub)
  calc _ ≤ (|W.corr (W.sBelow (k + 1)) J₂.coeff ε u - W.corr (W.sBelow (k + 1)) J₁.coeff ε u| +
        (|J₂.rem (k + 1) (W.dil ε u)| / ε ^ W.D + |J₁.rem (k + 1) (W.dil ε u)| / ε ^ W.D)) /
          ε ^ (k - W.D) := div_le_div_of_nonneg_right hsplit hp.le
    _ = |W.corr (W.sBelow (k + 1)) J₂.coeff ε u - W.corr (W.sBelow (k + 1)) J₁.coeff ε u| /
          ε ^ (k - W.D) +
        (|J₂.rem (k + 1) (W.dil ε u)| / ε ^ W.D + |J₁.rem (k + 1) (W.dil ε u)| / ε ^ W.D) /
          ε ^ (k - W.D) := add_div _ _ _
    _ ≤ corrBound (W.sBelow (k + 1)) J₁.coeff J₂.coeff u + (C₁ + C₂) * ‖u‖ ^ (k + 1) := by
        refine add_le_add hcorr ?_
        rw [div_le_iff₀ hp]
        calc |J₂.rem (k + 1) (W.dil ε u)| / ε ^ W.D + |J₁.rem (k + 1) (W.dil ε u)| / ε ^ W.D
            ≤ C₂ * (ε * ε ^ (k - W.D)) * ‖u‖ ^ (k + 1) +
              C₁ * (ε * ε ^ (k - W.D)) * ‖u‖ ^ (k + 1) := add_le_add h2 h1
          _ = (C₁ + C₂) * ‖u‖ ^ (k + 1) * (ε * ε ^ (k - W.D)) := by ring
          _ ≤ (C₁ + C₂) * ‖u‖ ^ (k + 1) * (1 * ε ^ (k - W.D)) :=
              mul_le_mul_of_nonneg_left hε' (by positivity)
          _ = (C₁ + C₂) * ‖u‖ ^ (k + 1) * ε ^ (k - W.D) := by ring

theorem measurable_VgenBound (J₁ : W.WeightedJet P L₁ U) (J₂ : W.WeightedJet P L₂ U) (k : ℕ)
    (C : ℝ) : Measurable (W.VgenBound J₁ J₂ k C) :=
  (measurable_corrBound _ _ _).add ((measurable_norm.pow_const _).const_mul _)

theorem VgenBound_nonneg (J₁ : W.WeightedJet P L₁ U) (J₂ : W.WeightedJet P L₂ U) (k : ℕ)
    {C : ℝ} (hC : 0 ≤ C) (u : ι → ℝ) : 0 ≤ W.VgenBound J₁ J₂ k C u :=
  add_nonneg (corrBound_nonneg _ _ _ u) (by positivity)

theorem polyBoundedBy_VgenBound {κ : ℝ} (hκ : 0 ≤ κ) (hP0 : ∀ u, 0 ≤ P u)
    (hcoer : ∀ u i, |u i| ^ W.D ≤ κ * P u ^ W.a i) (J₁ : W.WeightedJet P L₁ U)
    (J₂ : W.WeightedJet P L₂ U) (k : ℕ) (C : ℝ) :
    PolyBoundedBy P (W.VgenBound J₁ J₂ k C) :=
  (W.polyBoundedBy_corrBound hκ hP0 hcoer _ _ _).add hP0
    ((W.polyBoundedBy_norm_pow hκ hP0 hcoer (k + 1)).const_mul C)

omit [Fintype ι] in
/-- The lower bound from domination of `L − P` by `(1 − c₀) P` on `U`. -/
theorem lower_Vgen_of_dominated (hPqh : ∀ ε : ℝ, 0 < ε → ∀ u, P (W.dil ε u) = ε ^ W.D * P u)
    {c₀ : ℝ} (hdom : ∀ x ∈ U, |L₁ x - P x| ≤ (1 - c₀) * P x) {ε : ℝ} (hε : 0 < ε) :
    ∀ u ∈ W.mask U ε, c₀ * P u ≤ P u + W.Vgen P L₁ ε u := by
  intro u hu
  have h := hdom _ hu
  have hpos : (0 : ℝ) < ε ^ W.D := pow_pos hε _
  have hV : W.Vgen P L₁ ε u = (L₁ (W.dil ε u) - P (W.dil ε u)) / ε ^ W.D := by
    unfold Vgen
    rw [hPqh ε hε]
    field_simp
  rw [hPqh ε hε] at h
  have h2 : |L₁ (W.dil ε u) - P (W.dil ε u)| / ε ^ W.D ≤ (1 - c₀) * P u := by
    rw [div_le_iff₀ hpos]
    rw [hPqh ε hε]
    linarith [h]
  rw [← abs_of_pos hpos, ← abs_div] at h2
  rw [hV]
  have := (abs_le.mp h2).1
  linarith

/-! ### The masked moment of a general loss -/

/-- The masked normalized rescaled moment of a general loss `L`. -/
noncomputable def maskedMomentL (U : Set (ι → ℝ)) (P L A : (ι → ℝ) → ℝ) (ε : ℝ) : ℝ :=
  (∫ u, A u * maskedKernel (W.mask U) P (W.Vgen P L) ε u) /
    ∫ u, maskedKernel (W.mask U) P (W.Vgen P L) ε u

/-! ### The grade step and the induction -/

/-- **The grade step for weighted jets.** -/
theorem weightedJet_coeff_eq_at_grade_of_lower_eq (hPm : Measurable P) (hP0 : ∀ u, 0 ≤ P u)
    (hPqh : ∀ ε : ℝ, 0 < ε → ∀ u, P (W.dil ε u) = ε ^ W.D * P u)
    (hint : ∀ c : ℝ, 0 < c → Integrable fun u : ι → ℝ ↦ Real.exp (-(c * P u)))
    {κ : ℝ} (hκ : 0 ≤ κ) (hcoer : ∀ u i, |u i| ^ W.D ≤ κ * P u ^ W.a i)
    (hU : MeasurableSet U) (hU0 : U ∈ 𝓝 (0 : ι → ℝ))
    (hL₁ : Measurable L₁) (hL₂ : Measurable L₂)
    (J₁ : W.WeightedJet P L₁ U) (J₂ : W.WeightedJet P L₂ U)
    {c₀ : ℝ} (hc₀ : 0 < c₀)
    (hdom₁ : ∀ x ∈ U, |L₁ x - P x| ≤ (1 - c₀) * P x)
    (hdom₂ : ∀ x ∈ U, |L₂ x - P x| ≤ (1 - c₀) * P x)
    {k : ℕ} (hk : W.D < k)
    (hlower : ∀ α, W.D < W.wdeg α → W.wdeg α < k → J₁.coeff α = J₂.coeff α)
    (hdata : ∀ α, W.wdeg α = k → Tendsto (fun ε : ℝ ↦
      (W.maskedMomentL U P L₂ (mvMonomial α) ε - W.maskedMomentL U P L₁ (mvMonomial α) ε) /
        ε ^ (k - W.D)) (𝓝[>] (0 : ℝ)) (𝓝 0)) :
    ∀ α, W.wdeg α = k → J₁.coeff α = J₂.coeff α := by
  set S := W.sBelow (k + 1) with hS_def
  have hlower' : ∀ α ∈ S, W.wdeg α < k → J₁.coeff α = J₂.coeff α :=
    fun α hα hαk ↦ hlower α (W.sBelow_wdeg_pos α hα) hαk
  set Sk := S.filter (fun α ↦ W.wdeg α = k) with hSk_def
  set Q : (ι → ℝ) → ℝ := fun u ↦ ∑ β ∈ Sk, (J₂.coeff β - J₁.coeff β) * mvMonomial β u
    with hQ_def
  have hQ_eq : W.gradePart S (fun α ↦ J₂.coeff α - J₁.coeff α) k = Q := rfl
  have he1 : Integrable fun u : ι → ℝ ↦ Real.exp (-P u) := by
    have := hint 1 one_pos
    simpa using this
  have hZpos : 0 < ∫ u : ι → ℝ, Real.exp (-P u) := integral_exp_neg_pos he1
  obtain ⟨CB, hCB0, hCB⟩ := W.exists_abs_Vgen_sub_div_pow_le hPqh J₁ J₂ hk hlower'
  have hlow₁ : ∀ᶠ ε in 𝓝[>] (0 : ℝ), ∀ u ∈ W.mask U ε, c₀ * P u ≤ P u + W.Vgen P L₁ ε u := by
    filter_upwards [self_mem_nhdsWithin] with ε hε
    exact W.lower_Vgen_of_dominated hPqh hdom₁ hε
  have hlow₂ : ∀ᶠ ε in 𝓝[>] (0 : ℝ), ∀ u ∈ W.mask U ε, c₀ * P u ≤ P u + W.Vgen P L₂ ε u := by
    filter_upwards [self_mem_nhdsWithin] with ε hε
    exact W.lower_Vgen_of_dominated hPqh hdom₂ hε
  have hbound : ∀ᶠ ε in 𝓝[>] (0 : ℝ), ∀ u ∈ W.mask U ε,
      |W.Vgen P L₂ ε u - W.Vgen P L₁ ε u| / ε ^ (k - W.D) ≤ W.VgenBound J₁ J₂ k CB u := by
    filter_upwards [Ioc_mem_nhdsGT (zero_lt_one' ℝ)] with ε hε u hu
    exact hCB ε hε.1 hε.2 u hu
  have hBpb : PolyBoundedBy P (W.VgenBound J₁ J₂ k CB) :=
    W.polyBoundedBy_VgenBound hκ hP0 hcoer J₁ J₂ k CB
  have hBm : Measurable (W.VgenBound J₁ J₂ k CB) := W.measurable_VgenBound J₁ J₂ k CB
  -- the covariance limit at each grade-`k` monomial
  have hcov : ∀ α ∈ Sk, covarianceUnder volume P (mvMonomial α) Q = 0 := by
    intro α hα
    have hαk : W.wdeg α = k := (Finset.mem_filter.mp hα).2
    have hAm : Measurable (mvMonomial α) := mvMonomial_measurable α
    have hApb : PolyBoundedBy P (mvMonomial α) := W.polyBoundedBy_mvMonomial hκ hP0 hcoer α
    have hlim := tendsto_masked_normalized_difference_div_pow (μ := volume)
      (E := W.mask U) (P := P) (V₁ := W.Vgen P L₁) (V₂ := W.Vgen P L₂) (A := mvMonomial α)
      (Q := Q) (B := W.VgenBound J₁ J₂ k CB) (c := c₀) (ρ := k - W.D)
      (W.measurableSet_mask hU) (W.eventually_mem_mask hU0) hPm (W.measurable_Vgen hPm hL₁)
      (W.measurable_Vgen hPm hL₂) hAm (W.tendsto_Vgen hPqh hU0 J₁) (W.tendsto_Vgen hPqh hU0 J₂)
      (fun u ↦ by rw [← hQ_eq]; exact W.tendsto_Vgen_sub_div_pow hPqh hU0 J₁ J₂ hk hlower' u)
      hlow₁ hlow₂ (W.VgenBound_nonneg J₁ J₂ k hCB0) hbound
      (integrable_mul_exp_neg_of_polyBoundedBy hPm hP0 hint hApb.abs
        hAm.abs.aestronglyMeasurable hc₀)
      (integrable_mul_exp_neg_of_polyBoundedBy hPm hP0 hint (hApb.abs.mul hP0 hBpb)
        (hAm.abs.mul hBm).aestronglyMeasurable hc₀)
      (hint c₀ hc₀)
      (integrable_mul_exp_neg_of_polyBoundedBy hPm hP0 hint hBpb hBm.aestronglyMeasurable hc₀)
      hZpos
    have hzero := hdata α hαk
    have huniq := tendsto_nhds_unique hlim hzero
    exact neg_eq_zero.mp huniq
  -- Stage C: the grade component vanishes as a function
  have hfun : ∀ u, ∑ β ∈ Sk, (J₂.coeff β - J₁.coeff β) * mvMonomial β u = 0 := by
    refine monomialCombo_eq_zero_of_covariance_monomials_zero P Sk
      (fun β ↦ J₂.coeff β - J₁.coeff β) ?_ he1 ?_ ?_ hZpos hcov
    · intro α hα
      have hαk : W.wdeg α = k := (Finset.mem_filter.mp hα).2
      intro h0
      rw [h0] at hαk
      have : W.wdeg (0 : ι → ℕ) = 0 := by
        unfold wdeg
        simp
      omega
    · intro α _
      have := integrable_mul_exp_neg_of_polyBoundedBy hPm hP0 hint
        (W.polyBoundedBy_mvMonomial hκ hP0 hcoer α) (mvMonomial_measurable α).aestronglyMeasurable
        one_pos
      simpa using this
    · intro α _
      have hQpb : PolyBoundedBy P Q :=
        PolyBoundedBy.finset_sum hP0 Sk fun β _ ↦
          (W.polyBoundedBy_mvMonomial hκ hP0 hcoer β).const_mul _
      have hQm : Measurable Q :=
        Finset.measurable_sum _ fun β _ ↦ (mvMonomial_measurable β).const_mul _
      have := integrable_mul_exp_neg_of_polyBoundedBy hPm hP0 hint
        ((W.polyBoundedBy_mvMonomial hκ hP0 hcoer α).mul hP0 hQpb)
        ((mvMonomial_measurable α).mul hQm).aestronglyMeasurable one_pos
      simpa using this
  -- coefficient uniqueness
  have hcoef := coefficients_zero_of_monomialCombo_eq_zero Sk
    (fun β ↦ J₂.coeff β - J₁.coeff β) hfun
  intro α hαk
  have hαS : α ∈ S := W.mem_sBelow_succ_of_wdeg_le (hαk ▸ hk) hαk.le
  have := hcoef α (Finset.mem_filter.mpr ⟨hαS, hαk⟩)
  linarith

/-- **Weighted-jet induction**: all coefficients of weighted degree `> D` agree. -/
theorem weightedJet_coeff_eq_of_rates (hPm : Measurable P) (hP0 : ∀ u, 0 ≤ P u)
    (hPqh : ∀ ε : ℝ, 0 < ε → ∀ u, P (W.dil ε u) = ε ^ W.D * P u)
    (hint : ∀ c : ℝ, 0 < c → Integrable fun u : ι → ℝ ↦ Real.exp (-(c * P u)))
    {κ : ℝ} (hκ : 0 ≤ κ) (hcoer : ∀ u i, |u i| ^ W.D ≤ κ * P u ^ W.a i)
    (hU : MeasurableSet U) (hU0 : U ∈ 𝓝 (0 : ι → ℝ))
    (hL₁ : Measurable L₁) (hL₂ : Measurable L₂)
    (J₁ : W.WeightedJet P L₁ U) (J₂ : W.WeightedJet P L₂ U)
    {c₀ : ℝ} (hc₀ : 0 < c₀)
    (hdom₁ : ∀ x ∈ U, |L₁ x - P x| ≤ (1 - c₀) * P x)
    (hdom₂ : ∀ x ∈ U, |L₂ x - P x| ≤ (1 - c₀) * P x)
    (hdata : ∀ k, W.D < k → ∀ α, W.wdeg α = k → Tendsto (fun ε : ℝ ↦
      (W.maskedMomentL U P L₂ (mvMonomial α) ε - W.maskedMomentL U P L₁ (mvMonomial α) ε) /
        ε ^ (k - W.D)) (𝓝[>] (0 : ℝ)) (𝓝 0)) :
    ∀ α, W.D < W.wdeg α → J₁.coeff α = J₂.coeff α := by
  have hgrade : ∀ k, W.D < k → ∀ α, W.wdeg α = k → J₁.coeff α = J₂.coeff α := by
    intro k
    induction k using Nat.strong_induction_on with
    | _ k ih =>
      intro hk α hαk
      exact W.weightedJet_coeff_eq_at_grade_of_lower_eq hPm hP0 hPqh hint hκ hcoer hU hU0 hL₁ hL₂
        J₁ J₂ hc₀ hdom₁ hdom₂ hk (fun β hβD hβk ↦ ih (W.wdeg β) hβk hβD β rfl) (hdata k hk) α hαk
  exact fun α hα ↦ hgrade (W.wdeg α) hα α rfl

/-! ### Temperature-level data -/

/-- Along the dilation, the localized integrand of a general loss becomes `ε^{wdeg α}` times
the masked rescaled integrand. -/
theorem indicator_dil_eq_L (α : ι → ℕ) {ε : ℝ} (hε : 0 < ε) (u : ι → ℝ) :
    U.indicator (fun x ↦ mvMonomial α x * Real.exp (-((ε ^ W.D)⁻¹ * L₁ x))) (W.dil ε u) =
      ε ^ W.wdeg α * (mvMonomial α u * maskedKernel (W.mask U) P (W.Vgen P L₁) ε u) := by
  have hne : (ε ^ W.D : ℝ) ≠ 0 := (pow_pos hε _).ne'
  by_cases hmem : W.dil ε u ∈ U
  · rw [Set.indicator_of_mem hmem, maskedKernel_of_mem (show u ∈ W.mask U ε from hmem),
      W.mvMonomial_dil]
    unfold Vgen
    rw [show P u + (L₁ (W.dil ε u) / ε ^ W.D - P u) = (ε ^ W.D)⁻¹ * L₁ (W.dil ε u) by
      field_simp
      ring]
    ring
  · rw [Set.indicator_of_notMem hmem, maskedKernel_of_notMem (show u ∉ W.mask U ε from hmem)]
    ring

/-- **The temperature adapter for a general loss.** -/
theorem tempMoment_dil_L (hL : Measurable L₁) (hU : MeasurableSet U)
    (α : ι → ℕ) {ε : ℝ} (hε : 0 < ε) :
    tempMoment U L₁ (mvMonomial α) (ε ^ W.D)⁻¹ =
      ε ^ W.wdeg α * W.maskedMomentL U P L₁ (mvMonomial α) ε := by
  have hnum := W.integral_dil hε (f := U.indicator
    (fun x ↦ mvMonomial α x * Real.exp (-((ε ^ W.D)⁻¹ * L₁ x))))
    (((mvMonomial_measurable α).mul
      (Real.measurable_exp.comp ((hL.const_mul _).neg))).indicator hU).aestronglyMeasurable
  have hden := W.integral_dil hε (f := U.indicator
    (fun x ↦ Real.exp (-((ε ^ W.D)⁻¹ * L₁ x))))
    ((Real.measurable_exp.comp ((hL.const_mul _).neg)).indicator hU).aestronglyMeasurable
  have hnum' : (∫ u, U.indicator
      (fun x ↦ mvMonomial α x * Real.exp (-((ε ^ W.D)⁻¹ * L₁ x))) (W.dil ε u)) =
      ε ^ W.wdeg α * ∫ u, mvMonomial α u * maskedKernel (W.mask U) P (W.Vgen P L₁) ε u := by
    rw [← integral_const_mul]
    exact integral_congr_ae (Filter.Eventually.of_forall fun u ↦
      W.indicator_dil_eq_L (P := P) α hε u)
  have hden' : (∫ u, U.indicator (fun x ↦ Real.exp (-((ε ^ W.D)⁻¹ * L₁ x)))
      (W.dil ε u)) = ∫ u, maskedKernel (W.mask U) P (W.Vgen P L₁) ε u := by
    refine integral_congr_ae (Filter.Eventually.of_forall fun u ↦ ?_)
    have h := W.indicator_dil_eq_L (P := P) (L₁ := L₁) (U := U) (fun _ ↦ 0) hε u
    simp only [mvMonomial, Finset.prod_const_one, wdeg, mul_zero, Finset.sum_const_zero,
      pow_zero, one_mul] at h
    exact h
  unfold tempMoment maskedMomentL
  rw [hnum, hden, hnum', hden']
  have hpos : (ε ^ W.total : ℝ) ≠ 0 := (pow_pos hε _).ne'
  rw [mul_div_mul_left _ _ hpos, mul_div_assoc]

/-- **Weighted jets agree beyond all orders** (germbij §7.4(b), all-orders form): two losses
with weighted Taylor packages relative to the same leading part, whose localized normalized
monomial moments agree beyond all orders in the temperature, have equal weighted jets. -/
theorem weightedJet_coeff_eq_of_superPoly (hPm : Measurable P) (hP0 : ∀ u, 0 ≤ P u)
    (hPqh : ∀ ε : ℝ, 0 < ε → ∀ u, P (W.dil ε u) = ε ^ W.D * P u)
    (hint : ∀ c : ℝ, 0 < c → Integrable fun u : ι → ℝ ↦ Real.exp (-(c * P u)))
    {κ : ℝ} (hκ : 0 ≤ κ) (hcoer : ∀ u i, |u i| ^ W.D ≤ κ * P u ^ W.a i)
    (hU : MeasurableSet U) (hU0 : U ∈ 𝓝 (0 : ι → ℝ))
    (hL₁ : Measurable L₁) (hL₂ : Measurable L₂)
    (J₁ : W.WeightedJet P L₁ U) (J₂ : W.WeightedJet P L₂ U)
    {c₀ : ℝ} (hc₀ : 0 < c₀)
    (hdom₁ : ∀ x ∈ U, |L₁ x - P x| ≤ (1 - c₀) * P x)
    (hdom₂ : ∀ x ∈ U, |L₂ x - P x| ≤ (1 - c₀) * P x)
    (hdata : ∀ α : ι → ℕ, W.D < W.wdeg α → Laplace.SuperPoly fun t : ℝ ↦
      tempMoment U L₂ (mvMonomial α) t - tempMoment U L₁ (mvMonomial α) t) :
    ∀ α, W.D < W.wdeg α → J₁.coeff α = J₂.coeff α := by
  refine W.weightedJet_coeff_eq_of_rates hPm hP0 hPqh hint hκ hcoer hU hU0 hL₁ hL₂ J₁ J₂ hc₀
    hdom₁ hdom₂ ?_
  intro k hk α hαk
  have hlim := tendsto_div_pow_of_superPoly_pow (hdata α (hαk ▸ hk)) W.D_pos
    (W.wdeg α + (k - W.D))
  refine hlim.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with ε hε
  have hε0 : (0 : ℝ) < ε := hε
  rw [W.tempMoment_dil_L (P := P) hL₂ hU α hε0, W.tempMoment_dil_L (P := P) hL₁ hU α hε0,
    pow_add, ← mul_sub, mul_div_mul_left _ _ (pow_pos hε0 _).ne']

/-- **Flatness of the difference**: equal weighted jets make `L₁ − L₂ = O(‖x‖^N)` on `U` for
every `N`. -/
theorem weightedJet_sub_isBigO_of_coeff_eq (J₁ : W.WeightedJet P L₁ U) (J₂ : W.WeightedJet P L₂ U)
    (hcoeff : ∀ α, W.D < W.wdeg α → J₁.coeff α = J₂.coeff α) (N : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ x ∈ U, |L₁ x - L₂ x| ≤ C * ‖x‖ ^ N := by
  obtain ⟨C₁, hC₁0, hC₁⟩ := J₁.remainder_bound N
  obtain ⟨C₂, hC₂0, hC₂⟩ := J₂.remainder_bound N
  refine ⟨C₁ + C₂, by positivity, fun x hx ↦ ?_⟩
  have hpoly : wpoly (W.sBelow N) J₁.coeff x = wpoly (W.sBelow N) J₂.coeff x := by
    unfold wpoly
    exact Finset.sum_congr rfl fun α hα ↦ by rw [hcoeff α (W.sBelow_wdeg_pos α hα)]
  have h1 := hC₁ x hx
  have h2 := hC₂ x hx
  calc |L₁ x - L₂ x| = |(L₁ x - P x - wpoly (W.sBelow N) J₁.coeff x) -
        (L₂ x - P x - wpoly (W.sBelow N) J₂.coeff x)| := by rw [hpoly]; ring_nf
    _ ≤ |L₁ x - P x - wpoly (W.sBelow N) J₁.coeff x| +
        |L₂ x - P x - wpoly (W.sBelow N) J₂.coeff x| := abs_sub _ _
    _ ≤ C₁ * ‖x‖ ^ N + C₂ * ‖x‖ ^ N := add_le_add h1 h2
    _ = (C₁ + C₂) * ‖x‖ ^ N := by ring

end IntWeights

end Laplace.Multi
