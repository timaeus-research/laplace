/-
Copyright (c) 2026 Timaeus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Laplace.Grammar.TwoDChart

/-!
# Variants of the leading theorem: `C ≠ 0` and nonnegative face amplitudes (grammar §4.2)

The asymptotic equivalence `Z ~ C N^{-p} (log N)^{d₀}` only needs `C ≠ 0`
(`blockStateIntegral_isEquivalent_of_ne`), and `C > 0` holds as soon as `η(0,·) ≥ 0` on the
noncritical box and `η(0, v₀) > 0` at one interior point
(`integral_blockDivisorDensity_pos_of_nonneg`, `blockStateIntegral_isEquivalent_of_nonneg`): the
positive kernel and weights make the coefficient a positive integral over a set of positive
measure. Zero `sorry`/`axiom`.
-/

open Real MeasureTheory Set Filter Topology Asymptotics

namespace Laplace.Grammar

/-- **Asymptotic equivalence from `C ≠ 0`.** -/
theorem blockStateIntegral_isEquivalent_of_ne (β b p : ℝ) (hβ : 0 < β) (hb : 0 < b) {d₀ d' : ℕ}
    (k h : Fin (d₀ + 1) → ℕ) (hk : ∀ j, 0 < k j) (hp : ∀ j, finExp k h j = p)
    (k' h' : Fin d' → ℕ) (hk' : ∀ i, 0 < k' i) (hq : ∀ i, p < ((h' i : ℝ) + 1) / k' i)
    (ξ η : (Fin (d₀ + 1) → ℝ) → (Fin d' → ℝ) → ℝ)
    (hξc : Continuous fun x : (Fin (d₀ + 1) → ℝ) × (Fin d' → ℝ) => ξ x.1 x.2)
    (hηc : Continuous fun x : (Fin (d₀ + 1) → ℝ) × (Fin d' → ℝ) => η x.1 x.2)
    (hC : blockCoeff β b p k k' h' ξ η ≠ 0) :
    (fun N : ℝ => blockStateIntegral β b N k h k' h' ξ η) ~[atTop]
      fun N : ℝ => blockCoeff β b p k k' h' ξ η * (N ^ (-p) * Real.log N ^ d₀) := by
  have ht := blockStateIntegral_tendsto β b p hβ hb k h hk hp k' h' hk' hq ξ η hξc hηc
  have h1 : (fun N : ℝ => N ^ p / Real.log N ^ d₀ * blockStateIntegral β b N k h k' h' ξ η)
      ~[atTop] Function.const ℝ (blockCoeff β b p k k' h' ξ η) :=
    (isEquivalent_const_iff_tendsto hC).2 ht
  have h2 := (IsEquivalent.refl (u := fun N : ℝ => N ^ (-p) * Real.log N ^ d₀)
    (l := atTop)).mul h1
  refine (h2.congr_left ?_).congr_right ?_
  · filter_upwards [eventually_gt_atTop (1 : ℝ)] with N hN
    have hN0 : 0 < N := by linarith
    have hlog : 0 < Real.log N := Real.log_pos hN
    simp only [Pi.mul_apply]
    have hNN : N ^ (-p) * N ^ p = 1 := by rw [← Real.rpow_add hN0]; simp
    have hlogne : Real.log N ^ d₀ ≠ 0 := pow_ne_zero _ hlog.ne'
    rw [show N ^ (-p) * Real.log N ^ d₀
        * (N ^ p / Real.log N ^ d₀ * blockStateIntegral β b N k h k' h' ξ η)
      = (N ^ (-p) * N ^ p) * (Real.log N ^ d₀ / Real.log N ^ d₀)
        * blockStateIntegral β b N k h k' h' ξ η by ring, hNN, div_self hlogne, one_mul, one_mul]
  · filter_upwards with N
    simp only [Pi.mul_apply, Function.const_apply]
    ring

/-- **Positivity of the block coefficient from a nonnegative face amplitude** which is positive at
one interior point. -/
theorem integral_blockDivisorDensity_pos_of_nonneg (β b p : ℝ) (hβ : 0 < β)
    (hp : 0 < p) (k : ℕ → ℕ) (hk : ∀ i, 0 < k i) (d : ℕ) {d' : ℕ} (k' h' : Fin d' → ℕ)
    (hk' : ∀ i, 0 < k' i) (hq : ∀ i, p < ((h' i : ℝ) + 1) / k' i) (a e : (Fin d' → ℝ) → ℝ)
    (hac : Continuous a) (hec : Continuous e)
    (henn : ∀ v : Fin d' → ℝ, (∀ i, 0 < v i ∧ v i ≤ b) → 0 ≤ e v)
    (v₀ : Fin d' → ℝ) (hv₀ : ∀ i, 0 < v₀ i ∧ v₀ i < b) (hpos : 0 < e v₀) :
    0 < ∫ v, blockDivisorDensity β p k d k' h' a e v ∂(boxMeasure b d') := by
  have hγ : -1 < p - 1 := by linarith
  have hmem : ∀ᵐ v ∂(boxMeasure b d'), v ∈ Set.pi univ fun _ : Fin d' => Ioc (0 : ℝ) b := by
    rw [boxMeasure_eq_restrict]
    exact ae_restrict_mem (MeasurableSet.univ_pi fun _ => measurableSet_Ioc)
  have hP : 0 < ∏ i ∈ Finset.range (d + 1), (1 : ℝ) / k i :=
    Finset.prod_pos fun i _ => by have := hk i; positivity
  -- the density is nonnegative on the box and positive where `e > 0`
  have hnn : ∀ v : Fin d' → ℝ, v ∈ (Set.pi univ fun _ : Fin d' => Ioc (0 : ℝ) b) →
      0 ≤ blockDivisorDensity β p k d k' h' a e v := by
    intro v hv
    rw [Set.mem_univ_pi] at hv
    have hv' : ∀ i, 0 < v i := fun i => (hv i).1
    have he := henn v fun i => ⟨(hv i).1, (hv i).2⟩
    have hA := weightedMass_pos β (a v) (p - 1) hβ hγ
    have hV : 0 < ∏ i, v i ^ k' i := Finset.prod_pos fun i _ => pow_pos (hv' i) _
    have hH : 0 < ∏ i, v i ^ h' i := Finset.prod_pos fun i _ => pow_pos (hv' i) _
    unfold blockDivisorDensity
    positivity
  have hpos' : ∀ v : Fin d' → ℝ, v ∈ (Set.pi univ fun _ : Fin d' => Ioc (0 : ℝ) b) → 0 < e v →
      0 < blockDivisorDensity β p k d k' h' a e v := by
    intro v hv he
    rw [Set.mem_univ_pi] at hv
    have hv' : ∀ i, 0 < v i := fun i => (hv i).1
    have hA := weightedMass_pos β (a v) (p - 1) hβ hγ
    have hV : 0 < ∏ i, v i ^ k' i := Finset.prod_pos fun i _ => pow_pos (hv' i) _
    have hH : 0 < ∏ i, v i ^ h' i := Finset.prod_pos fun i _ => pow_pos (hv' i) _
    unfold blockDivisorDensity
    positivity
  rw [integral_pos_iff_support_of_nonneg_ae ?_
    (blockDivisorDensity_integrable β b p hβ hp k d k' h' hk' hq a e hac hec)]
  · -- the open set `{e > 0} ∩ (0,b)^{d'}` has positive measure and lies in the support
    set S : Set (Fin d' → ℝ) := {v | 0 < e v} ∩ Set.pi univ fun _ : Fin d' => Ioo (0 : ℝ) b
      with hS
    have hSopen : IsOpen S :=
      (isOpen_lt continuous_const hec).inter (isOpen_set_pi finite_univ fun _ _ => isOpen_Ioo)
    have hv₀S : v₀ ∈ S := ⟨hpos, by rw [Set.mem_univ_pi]; exact hv₀⟩
    have hSsub : S ⊆ Set.pi univ fun _ : Fin d' => Ioc (0 : ℝ) b := by
      intro v hv
      have hv2 := hv.2
      rw [Set.mem_univ_pi] at hv2 ⊢
      exact fun i => ⟨(hv2 i).1, (hv2 i).2.le⟩
    have hsupp : S ⊆ Function.support (blockDivisorDensity β p k d k' h' a e) :=
      fun v hv => (hpos' v (hSsub hv) hv.1).ne'
    refine lt_of_lt_of_le ?_ (measure_mono hsupp)
    rw [boxMeasure_eq_restrict, Measure.restrict_apply hSopen.measurableSet,
      inter_eq_left.2 hSsub]
    exact hSopen.measure_pos volume ⟨v₀, hv₀S⟩
  · filter_upwards [hmem] with v hv
    exact hnn v hv

/-- **Asymptotic equivalence under a nonnegative face amplitude** positive at an interior point. -/
theorem blockStateIntegral_isEquivalent_of_nonneg (β b p : ℝ) (hβ : 0 < β) (hb : 0 < b) {d₀ d' : ℕ}
    (k h : Fin (d₀ + 1) → ℕ) (hk : ∀ j, 0 < k j) (hp : ∀ j, finExp k h j = p)
    (k' h' : Fin d' → ℕ) (hk' : ∀ i, 0 < k' i) (hq : ∀ i, p < ((h' i : ℝ) + 1) / k' i)
    (ξ η : (Fin (d₀ + 1) → ℝ) → (Fin d' → ℝ) → ℝ)
    (hξc : Continuous fun x : (Fin (d₀ + 1) → ℝ) × (Fin d' → ℝ) => ξ x.1 x.2)
    (hηc : Continuous fun x : (Fin (d₀ + 1) → ℝ) × (Fin d' → ℝ) => η x.1 x.2)
    (henn : ∀ v : Fin d' → ℝ, (∀ i, 0 < v i ∧ v i ≤ b) → 0 ≤ η 0 v)
    (v₀ : Fin d' → ℝ) (hv₀ : ∀ i, 0 < v₀ i ∧ v₀ i < b) (hpos : 0 < η 0 v₀) :
    0 < blockCoeff β b p k k' h' ξ η ∧
    (fun N : ℝ => blockStateIntegral β b N k h k' h' ξ η) ~[atTop]
      fun N : ℝ => blockCoeff β b p k k' h' ξ η * (N ^ (-p) * Real.log N ^ d₀) := by
  have hp0 : 0 < p := by rw [← hp 0]; exact finExp_pos k h hk 0
  have hC : 0 < blockCoeff β b p k k' h' ξ η :=
    integral_blockDivisorDensity_pos_of_nonneg β b p hβ hp0 (toNatFun k 1) (toNatFun_pos k hk) d₀
      k' h' hk' hq (fun v => ξ 0 v) (fun v => η 0 v)
      (hξc.comp (continuous_const.prodMk continuous_id))
      (hηc.comp (continuous_const.prodMk continuous_id)) henn v₀ hv₀ hpos
  exact ⟨hC, blockStateIntegral_isEquivalent_of_ne β b p hβ hb k h hk hp k' h' hk' hq ξ η hξc hηc
    hC.ne'⟩

end Laplace.Grammar
