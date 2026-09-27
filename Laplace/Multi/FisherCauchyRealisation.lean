/-
Copyright (c) 2026 Timaeus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Timaeus
-/
import Laplace.Multi.FisherTopology
import Laplace.Multi.ResponseSusceptibility

/-!
# Realising a Fisher–Cauchy sequence by one finite-length `C¹` path

Given flat `C¹` paths `p n` from `u n` to `u (n+1)`, `realise p` traverses `p n` on `[n, n+1]` and
is constant before time `0`. It is globally `C¹` (the junction velocities vanish), its velocity is
continuous, its Fisher length on `(0,∞)` is at most `Σ L(p n)`, and if the lengths are dominated
by a null sequence and the means `m(u n)` converge to `M`, then the means along the whole path
converge to `M` (mean control on each piece).

Also: the Fisher distance between two points of a global `C¹` path in `W` is at most the Fisher
length of the path between them (`fisherDist_le_integral`), and a Fisher–Cauchy sequence has a
subsequence with `d_F(u_n, u_{n+1}) ≤ 2^{−n}`.
-/

open MeasureTheory Filter Topology Set Real

namespace Laplace.Multi

section Realise

set_option linter.unusedFintypeInType false
set_option linter.unusedSectionVars false

variable {X : Type*} [MeasurableSpace X] {J : Type*} [Fintype J] {S : J → X → ℝ} {ν : Measure X}
  {u : ℕ → dirSpan ν (fun _ ↦ (1 : ℝ)) S} (p : ∀ n, FisherPath S ν (u n) (u (n + 1)))

/-- The realised path: piece `n` on `[n, n+1]`, constant before `0`. -/
noncomputable def realise (t : ℝ) : dirSpan ν (fun _ ↦ (1 : ℝ)) S :=
  if 0 ≤ t then (p ⌊t⌋₊).toFun (t - ⌊t⌋₊) else u 0

/-- The velocity of the realised path. -/
noncomputable def realiseVel (t : ℝ) : dirSpan ν (fun _ ↦ (1 : ℝ)) S :=
  if 0 ≤ t then (p ⌊t⌋₊).vel (t - ⌊t⌋₊) else 0

theorem realise_of_mem_Ico {n : ℕ} {t : ℝ} (ht : t ∈ Ico (n : ℝ) (n + 1)) :
    realise p t = (p n).toFun (t - n) := by
  rw [realise, if_pos ((Nat.cast_nonneg n).trans ht.1), Nat.floor_eq_on_Ico n t ht]

theorem realiseVel_of_mem_Ico {n : ℕ} {t : ℝ} (ht : t ∈ Ico (n : ℝ) (n + 1)) :
    realiseVel p t = (p n).vel (t - n) := by
  rw [realiseVel, if_pos ((Nat.cast_nonneg n).trans ht.1), Nat.floor_eq_on_Ico n t ht]

theorem realise_natCast (n : ℕ) : realise p n = u n := by
  rw [realise_of_mem_Ico p ⟨le_rfl, by linarith⟩, sub_self, (p n).source]

theorem realiseVel_natCast (n : ℕ) : realiseVel p n = 0 := by
  rw [realiseVel_of_mem_Ico p ⟨le_rfl, by linarith⟩, sub_self, (p n).vel_zero]

theorem realise_of_mem_Ioc {n : ℕ} {t : ℝ} (ht : t ∈ Ioc (n : ℝ) (n + 1)) :
    realise p t = (p n).toFun (t - n) := by
  rcases eq_or_lt_of_le ht.2 with h | h
  · have e : realise p ((n : ℝ) + 1) = u (n + 1) := by
      have := realise_natCast p (n + 1)
      push_cast at this
      exact this
    rw [h, e]
    calc u (n + 1) = (p n).toFun 1 := (p n).target.symm
      _ = (p n).toFun ((n : ℝ) + 1 - n) := by congr 1; ring
  · exact realise_of_mem_Ico p ⟨ht.1.le, h⟩

theorem realiseVel_of_mem_Ioc {n : ℕ} {t : ℝ} (ht : t ∈ Ioc (n : ℝ) (n + 1)) :
    realiseVel p t = (p n).vel (t - n) := by
  rcases eq_or_lt_of_le ht.2 with h | h
  · have e : realiseVel p ((n : ℝ) + 1) = 0 := by
      have := realiseVel_natCast p (n + 1)
      push_cast at this
      exact this
    rw [h, e]
    calc (0 : dirSpan ν (fun _ ↦ (1 : ℝ)) S) = (p n).vel 1 := (p n).vel_one.symm
      _ = (p n).vel ((n : ℝ) + 1 - n) := by congr 1; ring
  · exact realiseVel_of_mem_Ico p ⟨ht.1.le, h⟩

theorem realise_of_nonpos {t : ℝ} (ht : t ≤ 0) : realise p t = u 0 := by
  rcases eq_or_lt_of_le ht with h | h
  · rw [h]
    exact_mod_cast realise_natCast p 0
  · rw [realise, if_neg (not_le.2 h)]

theorem realiseVel_of_nonpos {t : ℝ} (ht : t ≤ 0) : realiseVel p t = 0 := by
  rcases eq_or_lt_of_le ht with h | h
  · rw [h]
    exact_mod_cast realiseVel_natCast p 0
  · rw [realiseVel, if_neg (not_le.2 h)]

theorem hasDerivAt_piece (n : ℕ) (s : ℝ) :
    HasDerivAt (fun s ↦ (p n).toFun (s - n)) ((p n).vel (s - n)) s := by
  have h := ((p n).hasDerivAt (s - n)).scomp s ((hasDerivAt_id s).sub_const (n : ℝ))
  rw [one_smul] at h
  exact h

/-- **The realised path is globally `C¹`.** -/
theorem hasDerivAt_realise (t : ℝ) : HasDerivAt (realise p) (realiseVel p t) t := by
  rcases lt_or_ge t 0 with ht | ht
  · have hev : realise p =ᶠ[𝓝 t] fun _ ↦ u 0 :=
      Filter.eventuallyEq_of_mem (Iio_mem_nhds ht) fun s hs ↦ realise_of_nonpos p (le_of_lt hs)
    rw [realiseVel_of_nonpos p ht.le]
    exact (hasDerivAt_const t (u 0)).congr_of_eventuallyEq hev
  · obtain ⟨n, hn⟩ : ∃ n : ℕ, ⌊t⌋₊ = n := ⟨_, rfl⟩
    have hnt : (n : ℝ) ≤ t := hn ▸ Nat.floor_le ht
    have htn : t < n + 1 := hn ▸ Nat.lt_floor_add_one t
    rcases eq_or_lt_of_le hnt with h | h
    · subst h
      have hR : HasDerivWithinAt (realise p) ((p n).vel ((n : ℝ) - n)) (Ici (n : ℝ)) n :=
        (hasDerivAt_piece p n n).hasDerivWithinAt.congr_of_eventuallyEq
          (Filter.eventuallyEq_of_mem (Ico_mem_nhdsGE (by linarith)) fun s hs ↦
            realise_of_mem_Ico p hs)
          (realise_of_mem_Ico p ⟨le_rfl, by linarith⟩)
      rw [sub_self, (p n).vel_zero] at hR
      have hL : HasDerivWithinAt (realise p) 0 (Iic (n : ℝ)) n := by
        rcases n with _ | m
        · refine (hasDerivWithinAt_const _ _ (u 0)).congr_of_eventuallyEq ?_ ?_
          · exact Filter.eventuallyEq_of_mem self_mem_nhdsWithin fun s hs ↦
              realise_of_nonpos p (by simpa using hs)
          · exact realise_of_nonpos p (by simp)
        · have h1 := (hasDerivAt_piece p m ((m + 1 : ℕ) : ℝ)).hasDerivWithinAt
            (s := Iic ((m + 1 : ℕ) : ℝ))
          have e : ((m + 1 : ℕ) : ℝ) - m = 1 := by push_cast; ring
          rw [e, (p m).vel_one] at h1
          refine h1.congr_of_eventuallyEq ?_ ?_
          · refine Filter.eventuallyEq_of_mem
              (Ioc_mem_nhdsLE (by push_cast; linarith : (m : ℝ) < ((m + 1 : ℕ) : ℝ))) fun s hs ↦ ?_
            exact realise_of_mem_Ioc p (by push_cast at hs; exact hs)
          · rw [realise_natCast p (m + 1)]
            calc u (m + 1) = (p m).toFun 1 := (p m).target.symm
              _ = (p m).toFun (((m + 1 : ℕ) : ℝ) - m) := by congr 1; push_cast; ring
      rw [realiseVel, if_pos (Nat.cast_nonneg n), hn, sub_self, (p n).vel_zero,
        ← hasDerivWithinAt_univ, ← Set.Iic_union_Ici]
      exact hL.union hR
    · have hev : realise p =ᶠ[𝓝 t] fun s ↦ (p n).toFun (s - n) :=
        Filter.eventuallyEq_of_mem (Ioo_mem_nhds h htn) fun s hs ↦
          realise_of_mem_Ico p ⟨hs.1.le, hs.2⟩
      rw [realiseVel, if_pos ht, hn]
      exact (hasDerivAt_piece p n t).congr_of_eventuallyEq hev

/-- **The velocity of the realised path is continuous.** -/
theorem continuous_realiseVel : Continuous (realiseVel p) := by
  refine continuous_iff_continuousAt.2 fun t ↦ ?_
  have hpc : ∀ n : ℕ, Continuous fun s ↦ (p n).vel (s - n) := fun n ↦
    (p n).continuous_vel.comp (continuous_sub_right _)
  rcases lt_or_ge t 0 with ht | ht
  · exact continuousAt_const.congr (Filter.eventuallyEq_of_mem (Iio_mem_nhds ht) fun s hs ↦
      (realiseVel_of_nonpos p (le_of_lt hs)).symm)
  · obtain ⟨n, hn⟩ : ∃ n : ℕ, ⌊t⌋₊ = n := ⟨_, rfl⟩
    have hnt : (n : ℝ) ≤ t := hn ▸ Nat.floor_le ht
    have htn : t < n + 1 := hn ▸ Nat.lt_floor_add_one t
    rcases eq_or_lt_of_le hnt with h | h
    · subst h
      refine continuousAt_iff_continuous_left_right.2 ⟨?_, ?_⟩
      · rcases n with _ | m
        · refine ContinuousWithinAt.congr_of_eventuallyEq
            (f := fun _ ↦ (0 : dirSpan ν (fun _ ↦ (1 : ℝ)) S)) continuousWithinAt_const ?_ ?_
          · exact Filter.eventuallyEq_of_mem self_mem_nhdsWithin fun s hs ↦
              realiseVel_of_nonpos p (by simpa using hs)
          · exact realiseVel_of_nonpos p (by simp)
        · refine (hpc m).continuousWithinAt.congr_of_eventuallyEq ?_ ?_
          · refine Filter.eventuallyEq_of_mem
              (Ioc_mem_nhdsLE (by push_cast; linarith : (m : ℝ) < ((m + 1 : ℕ) : ℝ))) fun s hs ↦ ?_
            exact realiseVel_of_mem_Ioc p (by push_cast at hs; exact hs)
          · rw [realiseVel_natCast p (m + 1)]
            calc (0 : dirSpan ν (fun _ ↦ (1 : ℝ)) S) = (p m).vel 1 := (p m).vel_one.symm
              _ = (p m).vel (((m + 1 : ℕ) : ℝ) - m) := by congr 1; push_cast; ring
      · refine (hpc n).continuousWithinAt.congr_of_eventuallyEq ?_ ?_
        · exact Filter.eventuallyEq_of_mem (Ico_mem_nhdsGE (by linarith)) fun s hs ↦
            realiseVel_of_mem_Ico p hs
        · exact realiseVel_of_mem_Ico p ⟨le_rfl, by linarith⟩
    · exact (hpc n).continuousAt.congr (Filter.eventuallyEq_of_mem (Ioo_mem_nhds h htn)
        fun s hs ↦ (realiseVel_of_mem_Ico p ⟨hs.1.le, hs.2⟩).symm)

end Realise

section Coe

variable {X : Type*} [MeasurableSpace X] {J : Type*} [Fintype J] {S : J → X → ℝ} {ν : Measure X}
  {u : ℕ → dirSpan ν (fun _ ↦ (1 : ℝ)) S} (p : ∀ n, FisherPath S ν (u n) (u (n + 1)))

set_option linter.unusedFintypeInType false in
theorem hasDerivAt_coe_realise (t : ℝ) :
    HasDerivAt (fun s ↦ (realise p s : J → ℝ)) (realiseVel p t : J → ℝ) t :=
  (dirSpan ν (fun _ ↦ (1 : ℝ)) S).subtypeL.hasFDerivAt.comp_hasDerivAt t (hasDerivAt_realise p t)

end Coe

section Length

variable {X : Type*} [MeasurableSpace X] [Nonempty X] {J : Type*} [Fintype J]
  {S : J → X → ℝ} (hS : ∀ j, Bdd (S j)) (ν : Measure X) [IsProbabilityMeasure ν]
  {u : ℕ → dirSpan ν (fun _ ↦ (1 : ℝ)) S} (p : ∀ n, FisherPath S ν (u n) (u (n + 1)))
include hS

/-- The mean map. -/
local notation "mean" => meanMap ν (fun _ ↦ (1 : ℝ)) (fun _ ↦ (0 : ℝ)) S 1

/-- **The Fisher length of the realised path is at most the sum of the piece lengths.** -/
theorem lintegral_realise_le :
    (∫⁻ s in Ioi (0 : ℝ), ENNReal.ofReal
      (fisherNorm S ν (realise p s : J → ℝ) (realiseVel p s : J → ℝ))) ≤
      ∑' n, ENNReal.ofReal (p n).length := by
  have hsub : Ioi (0 : ℝ) ⊆ ⋃ n : ℕ, Ico (n : ℝ) (n + 1) := fun t ht ↦
    Set.mem_iUnion.2 ⟨⌊t⌋₊, Nat.floor_le ht.le, Nat.lt_floor_add_one t⟩
  refine (lintegral_mono_set hsub).trans ((lintegral_iUnion_le _ _).trans
    (ENNReal.tsum_le_tsum fun n ↦ ?_))
  have hcont : Continuous fun s ↦
      fisherNorm S ν ((p n).toFun (s - n) : J → ℝ) ((p n).vel (s - n) : J → ℝ) :=
    ((p n).continuous_speed hS ν).comp (continuous_sub_right _)
  refine le_of_eq ?_
  calc ∫⁻ s in Ico (n : ℝ) (n + 1), ENNReal.ofReal
        (fisherNorm S ν (realise p s : J → ℝ) (realiseVel p s : J → ℝ))
      = ∫⁻ s in Ico (n : ℝ) (n + 1), ENNReal.ofReal
        (fisherNorm S ν ((p n).toFun (s - n) : J → ℝ) ((p n).vel (s - n) : J → ℝ)) := by
        refine setLIntegral_congr_fun measurableSet_Ico fun s hs ↦ ?_
        rw [realise_of_mem_Ico p hs, realiseVel_of_mem_Ico p hs]
    _ = ENNReal.ofReal (∫ s in Ico (n : ℝ) (n + 1),
        fisherNorm S ν ((p n).toFun (s - n) : J → ℝ) ((p n).vel (s - n) : J → ℝ)) :=
        (ofReal_integral_eq_lintegral_ofReal (hcont.integrableOn_Icc.mono_set Ico_subset_Icc_self)
          (ae_of_all _ fun s ↦ fisherNorm_nonneg S ν _ _)).symm
    _ = ENNReal.ofReal (∫ s in (n : ℝ)..(n + 1),
        fisherNorm S ν ((p n).toFun (s - n) : J → ℝ) ((p n).vel (s - n) : J → ℝ)) := by
        rw [integral_Ico_eq_integral_Ioc, intervalIntegral.integral_of_le (by linarith)]
    _ = ENNReal.ofReal (p n).length := by
        rw [intervalIntegral.integral_comp_sub_right
          (fun s ↦ fisherNorm S ν ((p n).toFun s : J → ℝ) ((p n).vel s : J → ℝ)) (n : ℝ)]
        simp only [sub_self, add_sub_cancel_left, FisherPath.length]

/-- **Summable piece lengths give a finite Fisher length.** -/
theorem lintegral_realise_lt_top {d : ℕ → ℝ} (hlen : ∀ n, (p n).length ≤ d n)
    (hd0 : ∀ n, 0 ≤ d n) (hd : Summable d) :
    (∫⁻ s in Ioi (0 : ℝ), ENNReal.ofReal
      (fisherNorm S ν (realise p s : J → ℝ) (realiseVel p s : J → ℝ))) < ⊤ := by
  calc (∫⁻ s in Ioi (0 : ℝ), ENNReal.ofReal
        (fisherNorm S ν (realise p s : J → ℝ) (realiseVel p s : J → ℝ)))
      ≤ ∑' n, ENNReal.ofReal (p n).length := lintegral_realise_le hS ν p
    _ ≤ ∑' n, ENNReal.ofReal (d n) := ENNReal.tsum_le_tsum fun n ↦ ENNReal.ofReal_le_ofReal (hlen n)
    _ = ENNReal.ofReal (∑' n, d n) := (ENNReal.ofReal_tsum_of_nonneg hd0 hd).symm
    _ < ⊤ := ENNReal.ofReal_lt_top

/-- On the piece `[n, n+1]` the mean stays within `B L(p n)` of `m(u n)`. -/
theorem norm_meanMap_realise_sub_le {B : ℝ} (hB : ∀ i x, |S i x| ≤ B) (hB0 : 0 ≤ B) {t : ℝ}
    (ht : 0 ≤ t) :
    ‖mean (realise p t : J → ℝ) - mean (u ⌊t⌋₊ : J → ℝ)‖ ≤ B * (p ⌊t⌋₊).length := by
  obtain ⟨n, hn⟩ : ∃ n : ℕ, ⌊t⌋₊ = n := ⟨_, rfl⟩
  have hnt : (n : ℝ) ≤ t := hn ▸ Nat.floor_le ht
  have htn : t < n + 1 := hn ▸ Nat.lt_floor_add_one t
  rw [hn, realise_of_mem_Ico p ⟨hnt, htn⟩]
  have h := norm_meanMap_sub_le_integral hS ν (γ := fun s ↦ ((p n).toFun s : J → ℝ))
    (γ' := fun s ↦ ((p n).vel s : J → ℝ)) ((p n).hasDerivAt_coe ν)
    (continuous_subtype_val.comp (p n).continuous_vel) hB hB0 (a := 0) (b := t - n)
    (by linarith)
  rw [(p n).source] at h
  refine h.trans (mul_le_mul_of_nonneg_left ?_ hB0)
  exact intervalIntegral.integral_mono_interval le_rfl (by linarith) (by linarith)
    (ae_of_all _ fun s ↦ fisherNorm_nonneg S ν _ _)
    (((p n).continuous_speed hS ν).intervalIntegrable _ _)

/-- **The means along the realised path converge** when the piece lengths are dominated by a
null sequence and the means of the vertices converge. -/
theorem tendsto_meanMap_realise {B : ℝ} (hB : ∀ i x, |S i x| ≤ B) (hB0 : 0 ≤ B) {d : ℕ → ℝ}
    (hlen : ∀ n, (p n).length ≤ d n) (hd : Tendsto d atTop (𝓝 0)) {M : J → ℝ}
    (hM : Tendsto (fun n ↦ mean (u n : J → ℝ)) atTop (𝓝 M)) :
    Tendsto (fun t ↦ mean (realise p t : J → ℝ)) atTop (𝓝 M) := by
  rw [Metric.tendsto_atTop]
  intro ε hε
  have h1 := Metric.tendsto_atTop.1 hM (ε / 2) (half_pos hε)
  have h2 := (tendsto_order.1 (hd.const_mul B)).2 (ε / 2) (by rw [mul_zero]; exact half_pos hε)
  obtain ⟨N, hN⟩ := Filter.eventually_atTop.1 ((Filter.eventually_atTop.2 h1).and h2)
  refine ⟨N, fun t ht ↦ ?_⟩
  have ht0 : 0 ≤ t := (Nat.cast_nonneg N).trans ht
  have hNt : N ≤ ⌊t⌋₊ := Nat.le_floor ht
  obtain ⟨hm, hl⟩ := hN _ hNt
  rw [dist_eq_norm] at hm ⊢
  calc ‖mean (realise p t : J → ℝ) - M‖
      ≤ ‖mean (realise p t : J → ℝ) - mean (u ⌊t⌋₊ : J → ℝ)‖ +
        ‖mean (u ⌊t⌋₊ : J → ℝ) - M‖ := norm_sub_le_norm_sub_add_norm_sub _ _ _
    _ ≤ B * (p ⌊t⌋₊).length + ‖mean (u ⌊t⌋₊ : J → ℝ) - M‖ :=
        add_le_add (norm_meanMap_realise_sub_le hS ν p hB hB0 ht0) le_rfl
    _ ≤ B * d ⌊t⌋₊ + ‖mean (u ⌊t⌋₊ : J → ℝ) - M‖ :=
        add_le_add (mul_le_mul_of_nonneg_left (hlen _) hB0) le_rfl
    _ < ε := by linarith

end Length

section Paths

variable {X : Type*} [MeasurableSpace X] [Nonempty X] {J : Type*} [Fintype J]
  {S : J → X → ℝ} (hS : ∀ j, Bdd (S j)) (ν : Measure X) [IsProbabilityMeasure ν]
include hS

/-- **The Fisher distance is bounded by the Fisher length of any global `C¹` path in `W`.** -/
theorem fisherDist_le_integral {η η' : ℝ → J → ℝ} (hη : ∀ s, η s ∈ dirSpan ν (fun _ ↦ (1 : ℝ)) S)
    (hd : ∀ s, HasDerivAt η (η' s) s) (hd' : Continuous η') {a b : ℝ} (hab : a ≤ b) :
    fisherDist S ν ⟨η a, hη a⟩ ⟨η b, hη b⟩ ≤ ∫ s in a..b, fisherNorm S ν (η s) (η' s) := by
  rcases eq_or_lt_of_le hab with h | h
  · subst h
    rw [fisherDist_self hS ν, intervalIntegral.integral_same]
  have hclosed : IsClosed ((dirSpan ν (fun _ ↦ (1 : ℝ)) S : Submodule ℝ (J → ℝ)) : Set (J → ℝ)) :=
    Submodule.closed_of_finiteDimensional _
  have hη'W : ∀ s, η' s ∈ dirSpan ν (fun _ ↦ (1 : ℝ)) S := fun s ↦
    mem_of_hasDerivAt_subtype hclosed
      (γ := fun s ↦ (⟨η s, hη s⟩ : dirSpan ν (fun _ ↦ (1 : ℝ)) S)) (hd s)
  set c : ℝ := b - a with hc
  have hc0 : 0 < c := sub_pos.2 h
  let γ : ℝ → dirSpan ν (fun _ ↦ (1 : ℝ)) S := fun t ↦ ⟨η (a + c * t), hη _⟩
  let γ' : ℝ → dirSpan ν (fun _ ↦ (1 : ℝ)) S := fun t ↦
    ⟨c • η' (a + c * t), Submodule.smul_mem _ _ (hη'W _)⟩
  have hγ : ∀ t, HasDerivAt γ (γ' t) t := fun t ↦ by
    refine hasDerivAt_subtype_of_hasDerivAt _ ?_
    have h1 := (hd (a + c * t)).scomp t (((hasDerivAt_id t).const_mul c).const_add a)
    rw [mul_one] at h1
    exact h1
  have hlin : Continuous fun t : ℝ ↦ a + c * t := by fun_prop
  have hγ'0 : Continuous fun t ↦ c • η' (a + c * t) := (hd'.comp hlin).const_smul c
  have hγ' : Continuous γ' := Continuous.subtype_mk hγ'0 _
  have h0 : γ 0 = ⟨η a, hη a⟩ := Subtype.ext (by simp [γ])
  have h1 : γ 1 = ⟨η b, hη b⟩ := Subtype.ext (by simp [γ, hc])
  refine (fisherDist_le_length (FisherPath.flat hγ hγ' h0 h1)).trans ?_
  rw [FisherPath.length_flat hS ν]
  have e : ∀ t, fisherNorm S ν (γ t : J → ℝ) (γ' t : J → ℝ) =
      c * fisherNorm S ν (η (a + c * t)) (η' (a + c * t)) := fun t ↦ by
    simp only [γ, γ']
    rw [fisherNorm_smul hS ν, abs_of_pos hc0]
  simp_rw [e]
  rw [intervalIntegral.integral_const_mul, intervalIntegral.integral_comp_add_mul
    (fun s ↦ fisherNorm S ν (η s) (η' s)) hc0.ne' a, smul_eq_mul, ← mul_assoc,
    mul_inv_cancel₀ hc0.ne', one_mul, mul_zero, add_zero, mul_one, hc, add_sub_cancel]

variable [Nonempty J]

/-- **A Fisher–Cauchy sequence has a subsequence with `d_F(u_n, u_{n+1}) ≤ 2^{−n}`.** -/
theorem exists_subseq_fisherDist_le {u : ℕ → FisherPoint hS ν} (hu : CauchySeq u) :
    ∃ φ : ℕ → ℕ, StrictMono φ ∧
      ∀ n, fisherDist S ν (u (φ n)).param (u (φ (n + 1))).param ≤ (1 / 2) ^ n := by
  obtain ⟨φ, hφ, hd⟩ := CauchySeq.subseq_mem
    (V := fun n ↦ {q : FisherPoint hS ν × FisherPoint hS ν | dist q.1 q.2 < (1 / 2) ^ n})
    (fun n ↦ Metric.dist_mem_uniformity (by positivity)) hu
  refine ⟨φ, hφ, fun n ↦ ?_⟩
  have h := hd n
  rw [Set.mem_ofPred_eq, FisherPoint.dist_eq, fisherDist_comm hS ν] at h
  exact h.le

end Paths

end Laplace.Multi
