/-
Copyright (c) 2026 Timaeus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Timaeus
-/
import Mathlib
import Laplace.Multi.LocalizedSingular
import Laplace.Multi.TaylorMonomialExpansion
import Laplace.Multi.ProjectiveClosure
import Laplace.Multi.TotalVariation
import Laplace.OnePointAnchoring

/-!
# A fixed sufficient family in the singular case: one cutoff times all monomials

The singular sufficient-test theorem of `SingularSufficientTests` uses a family
depending on the unknown loss. Here the family is fixed in advance: a smooth
cutoff `χ` equal to `1` near the zero `p` times the coordinate monomials
`x ↦ ∏ⱼ (x (m j) - p (m j))`, over all words `m`. Under an isolated-zero
coercivity bound `L₁ ≥ c ‖x - p‖^ν` on the support of `χ`, projective agreement
beyond all orders on this countable family forces `L₁ = L₂` near `p`
(`normalized_families_force_germ_eq_at_of_cutoff_monomials`).

The mechanism (GPT-6 Astra, planning consult): the degree-zero member bounds the
scalar `C(t)` polynomially; a smooth test supported near `p` equals `χ` times its
Taylor polynomial at `p` plus a remainder `O(‖x-p‖^{2N})`; the Taylor polynomial is
a finite combination of the family, and the remainder is dominated by the
polynomial majorant `∑ᵢ (xᵢ - pᵢ)^{2N}`, itself a combination of the family. Under
`L₁` the majorant's Boltzmann mass is `O(t^{-2N/ν})` by the pointwise bound
`r^{2N} e^{-tcr^ν} ≤ K t^{-2N/ν}`, and the family transfers this bound to `L₂` up
to `C(t)` and beyond-all-orders errors. Taking `N` large gives superpolynomial
agreement for every smooth test supported near `p`, and the localised singular
theorem finishes. Ordinary density of polynomials would give no rate; the
high-moment concentration does.
-/

open Asymptotics Filter MeasureTheory
open scoped ENNReal Topology ContDiff

namespace Laplace

variable {ι : Type*} [Fintype ι]

/-! ### The projective difference functional -/

/-- The projective difference `∫ φ e^{-tL₂} - C(t) ∫ φ e^{-tL₁}`. -/
noncomputable def projDiff (L₁ L₂ : (ι → ℝ) → ℝ) (C : ℝ → ℝ) (φ : (ι → ℝ) → ℝ) (t : ℝ) : ℝ :=
  (∫ w, φ w * Real.exp (-(t * L₂ w))) - C t * ∫ w, φ w * Real.exp (-(t * L₁ w))

variable {L₁ L₂ : (ι → ℝ) → ℝ} {C : ℝ → ℝ}

theorem projDiff_const_mul (c : ℝ) (φ : (ι → ℝ) → ℝ) (t : ℝ) :
    projDiff L₁ L₂ C (fun w ↦ c * φ w) t = c * projDiff L₁ L₂ C φ t := by
  unfold projDiff
  simp only [mul_assoc, integral_const_mul]
  ring

theorem projDiff_add (hL1c : Continuous L₁) (hL2c : Continuous L₂) {φ ψ : (ι → ℝ) → ℝ}
    (hφc : Continuous φ) (hφs : HasCompactSupport φ) (hψc : Continuous ψ)
    (hψs : HasCompactSupport ψ) (t : ℝ) :
    projDiff L₁ L₂ C (fun w ↦ φ w + ψ w) t = projDiff L₁ L₂ C φ t + projDiff L₁ L₂ C ψ t := by
  unfold projDiff
  have h2 : ∫ w, (φ w + ψ w) * Real.exp (-(t * L₂ w)) =
      (∫ w, φ w * Real.exp (-(t * L₂ w))) + ∫ w, ψ w * Real.exp (-(t * L₂ w)) := by
    rw [← integral_add (integrable_mul_exp_neg_of_compactSupport hφc hφs hL2c t)
      (integrable_mul_exp_neg_of_compactSupport hψc hψs hL2c t)]
    congr 1
    funext w
    ring
  have h1 : ∫ w, (φ w + ψ w) * Real.exp (-(t * L₁ w)) =
      (∫ w, φ w * Real.exp (-(t * L₁ w))) + ∫ w, ψ w * Real.exp (-(t * L₁ w)) := by
    rw [← integral_add (integrable_mul_exp_neg_of_compactSupport hφc hφs hL1c t)
      (integrable_mul_exp_neg_of_compactSupport hψc hψs hL1c t)]
    congr 1
    funext w
    ring
  rw [h1, h2]
  ring

theorem projDiff_sub (hL1c : Continuous L₁) (hL2c : Continuous L₂) {φ ψ : (ι → ℝ) → ℝ}
    (hφc : Continuous φ) (hφs : HasCompactSupport φ) (hψc : Continuous ψ)
    (hψs : HasCompactSupport ψ) (t : ℝ) :
    projDiff L₁ L₂ C (fun w ↦ φ w - ψ w) t = projDiff L₁ L₂ C φ t - projDiff L₁ L₂ C ψ t := by
  have hnc : Continuous fun w ↦ -ψ w := hψc.neg
  have hns : HasCompactSupport fun w ↦ -ψ w := hψs.neg
  have hadd : projDiff L₁ L₂ C (fun w ↦ φ w + -ψ w) t =
      projDiff L₁ L₂ C φ t + projDiff L₁ L₂ C (fun w ↦ -ψ w) t :=
    projDiff_add hL1c hL2c hφc hφs hnc hns t
  have hneg : projDiff L₁ L₂ C (fun w ↦ -ψ w) t = -projDiff L₁ L₂ C ψ t := by
    have := projDiff_const_mul (L₁ := L₁) (L₂ := L₂) (C := C) (-1) ψ t
    simp only [neg_one_mul] at this
    exact this
  simp only [sub_eq_add_neg]
  rw [hadd, hneg]

omit [Fintype ι] in
/-- A finite sum of compactly supported functions is compactly supported. -/
theorem hasCompactSupport_finset_sum' {α : Type*} (s : Finset α) (f : α → (ι → ℝ) → ℝ)
    (hs : ∀ a, HasCompactSupport (f a)) :
    HasCompactSupport fun w ↦ ∑ a ∈ s, f a w := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    simp only [Finset.sum_empty]
    exact HasCompactSupport.zero
  | insert a s ha ih =>
    simp only [Finset.sum_insert ha]
    exact (hs a).add ih

theorem projDiff_finset_sum {α : Type*} (s : Finset α) (hL1c : Continuous L₁)
    (hL2c : Continuous L₂) (f : α → (ι → ℝ) → ℝ) (hc : ∀ a, Continuous (f a))
    (hs : ∀ a, HasCompactSupport (f a)) (t : ℝ) :
    projDiff L₁ L₂ C (fun w ↦ ∑ a ∈ s, f a w) t = ∑ a ∈ s, projDiff L₁ L₂ C (f a) t := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    simp only [Finset.sum_empty]
    unfold projDiff
    simp
  | insert a s ha ih =>
    rw [Finset.sum_insert ha]
    have hsum_c : Continuous fun w ↦ ∑ b ∈ s, f b w :=
      continuous_finsetSum _ fun b _ ↦ hc b
    have hsum_s : HasCompactSupport fun w ↦ ∑ b ∈ s, f b w :=
      hasCompactSupport_finset_sum' s f hs
    have := projDiff_add (C := C) hL1c hL2c (hc a) (hs a) hsum_c hsum_s t
    simp only [Finset.sum_insert ha]
    rw [this, ih]

/-! ### `SuperPoly` closure -/

theorem SuperPoly.const_mul {f : ℝ → ℝ} (hf : SuperPoly f) (c : ℝ) :
    SuperPoly fun t ↦ c * f t := fun N ↦ (hf N).const_mul_left c

theorem SuperPoly.finset_sum {α : Type*} (s : Finset α) {f : α → ℝ → ℝ}
    (hf : ∀ a ∈ s, SuperPoly (f a)) : SuperPoly fun t ↦ ∑ a ∈ s, f a t := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    intro N
    simp only [Finset.sum_empty]
    exact isLittleO_zero _ _
  | insert a s ha ih =>
    have h1 := hf a (Finset.mem_insert_self a s)
    have h2 := ih fun b hb ↦ hf b (Finset.mem_insert_of_mem hb)
    have := h1.add h2
    intro N
    refine (this N).congr' (Eventually.of_forall fun t ↦ ?_) EventuallyEq.rfl
    simp [Finset.sum_insert ha]

/-! ### The scalar is polynomially bounded, from the degree-zero member -/

/-- From `SuperPoly (projDiff χ)` for a window `χ` equal to `1` near a `C²` zero of `L₁`:
`|C(t)| ≤ A t^d` eventually. -/
theorem exists_scalar_upper_bound_of_lower_bound {χ : (ι → ℝ) → ℝ}
    (hL2c : Continuous L₂) (hL2 : ∀ w, 0 ≤ L₂ w)
    (hχc : Continuous χ) (hχs : HasCompactSupport χ) {κ : ℝ} (hκ : 0 < κ)
    (hlow : ∀ᶠ t in atTop,
      κ * t ^ (-(Fintype.card ι : ℝ)) ≤ ∫ w, χ w * Real.exp (-(t * L₁ w)))
    (h0 : SuperPoly (projDiff L₁ L₂ C χ)) :
    ∃ A : ℝ, 0 ≤ A ∧ ∀ᶠ t in atTop, |C t| ≤ A * t ^ (Fintype.card ι) := by
  obtain ⟨M, hM⟩ := isBigO_iff.mp (laplace_moment_bounded hχc hχs hL2c hL2)
  have hR1 : ∀ᶠ t in atTop, |(∫ w, χ w * Real.exp (-(t * L₂ w))) -
      C t * ∫ w, χ w * Real.exp (-(t * L₁ w))| ≤ 1 := by
    have := isLittleO_iff.mp (h0 0) one_pos
    filter_upwards [this] with t ht
    simpa [projDiff] using ht
  have hM0 : 0 ≤ M := by
    obtain ⟨t, ht⟩ := hM.exists
    have h := ht
    simp only [norm_one, mul_one] at h
    exact le_trans (norm_nonneg _) h
  refine ⟨(M + 1) / κ, by positivity, ?_⟩
  filter_upwards [hlow, hM, hR1, eventually_gt_atTop (0 : ℝ)] with t hlow_t hM_t hR_t htpos
  set I₁ := ∫ w, χ w * Real.exp (-(t * L₁ w)) with hI₁
  set I₂ := ∫ w, χ w * Real.exp (-(t * L₂ w)) with hI₂
  have hI₁pos : 0 < I₁ := lt_of_lt_of_le (by positivity) hlow_t
  have hM_t' : |I₂| ≤ M := by simpa using hM_t
  have hCI : |C t| * I₁ ≤ M + 1 := by
    calc |C t| * I₁ = |C t * I₁| := by rw [abs_mul, abs_of_pos hI₁pos]
      _ = |I₂ - (I₂ - C t * I₁)| := by ring_nf
      _ ≤ |I₂| + |I₂ - C t * I₁| := abs_sub _ _
      _ ≤ M + 1 := add_le_add hM_t' hR_t
  have key : |C t| * (κ * t ^ (-(Fintype.card ι : ℝ))) ≤ M + 1 :=
    le_trans (mul_le_mul_of_nonneg_left hlow_t (abs_nonneg _)) hCI
  have hrpow : t ^ (-(Fintype.card ι : ℝ)) * t ^ (Fintype.card ι) = 1 := by
    rw [← Real.rpow_natCast, ← Real.rpow_add htpos]
    simp
  have hunit : κ * t ^ (-(Fintype.card ι : ℝ)) * (t ^ (Fintype.card ι) / κ) = 1 := by
    calc κ * t ^ (-(Fintype.card ι : ℝ)) * (t ^ (Fintype.card ι) / κ)
        = (t ^ (-(Fintype.card ι : ℝ)) * t ^ (Fintype.card ι)) * (κ / κ) := by ring
      _ = 1 := by rw [hrpow, div_self hκ.ne', mul_one]
  have hfrac : 0 ≤ t ^ (Fintype.card ι) / κ := by positivity
  calc |C t| = |C t| * (κ * t ^ (-(Fintype.card ι : ℝ)) * (t ^ (Fintype.card ι) / κ)) := by
        rw [hunit, mul_one]
    _ = |C t| * (κ * t ^ (-(Fintype.card ι : ℝ))) * (t ^ (Fintype.card ι) / κ) := by ring
    _ ≤ (M + 1) * (t ^ (Fintype.card ι) / κ) := mul_le_mul_of_nonneg_right key hfrac
    _ = (M + 1) / κ * t ^ (Fintype.card ι) := by ring

/-- From `SuperPoly (projDiff χ)` for a window `χ` equal to `1` near a `C²` zero of `L₁`:
`|C(t)| ≤ A t^d` eventually. -/
theorem exists_scalar_upper_bound_of_window {χ : (ι → ℝ) → ℝ} {p : ι → ℝ}
    (hL1c : Continuous L₁) (hL2c : Continuous L₂)
    (hL1 : ∀ w, 0 ≤ L₁ w) (hL2 : ∀ w, 0 ≤ L₂ w)
    (hp : L₁ p = 0) (hC1 : ContDiffAt ℝ 2 L₁ p)
    (hχc : Continuous χ) (hχs : HasCompactSupport χ) (hχ0 : ∀ w, 0 ≤ χ w)
    (hχ1 : ∀ᶠ w in 𝓝 p, χ w = 1) (h0 : SuperPoly (projDiff L₁ L₂ C χ)) :
    ∃ A : ℝ, 0 ≤ A ∧ ∀ᶠ t in atTop, |C t| ≤ A * t ^ (Fintype.card ι) := by
  obtain ⟨κ, hκ, hlow⟩ := anchor_lower_bound_eventually hL1c hL1 hp hC1 hχc hχs hχ0 hχ1
  exact exists_scalar_upper_bound_of_lower_bound hL2c hL2 hχc hχs hκ hlow h0

/-- **Positive weights anchor as well as windows**: a continuous compactly supported weight
`χ ≥ a₀ > 0` near a `C²` zero of `L₁` dominates `a₀` times a bump equal to `1` near the zero,
so `∫ χ e^{-tL₁} ≥ κ t^{-d}` eventually and `|C(t)| ≤ A t^d`. -/
theorem exists_scalar_upper_bound_of_weight {χ : (ι → ℝ) → ℝ} {p : ι → ℝ}
    (hL1c : Continuous L₁) (hL2c : Continuous L₂)
    (hL1 : ∀ w, 0 ≤ L₁ w) (hL2 : ∀ w, 0 ≤ L₂ w)
    (hp : L₁ p = 0) (hC1 : ContDiffAt ℝ 2 L₁ p)
    (hχc : Continuous χ) (hχs : HasCompactSupport χ) (hχ0 : ∀ w, 0 ≤ χ w)
    {a₀ : ℝ} (ha₀ : 0 < a₀) (hχ1 : ∀ᶠ w in 𝓝 p, a₀ ≤ χ w)
    (h0 : SuperPoly (projDiff L₁ L₂ C χ)) :
    ∃ A : ℝ, 0 ≤ A ∧ ∀ᶠ t in atTop, |C t| ≤ A * t ^ (Fintype.card ι) := by
  obtain ⟨r, hr, hball⟩ := Metric.eventually_nhds_iff.mp hχ1
  let f : ContDiffBump p := ⟨r / 2, r, by positivity, by linarith⟩
  have hf1 : ∀ᶠ w in 𝓝 p, f w = 1 :=
    f.eventuallyEq_one_of_mem_ball (Metric.mem_ball_self (by positivity))
  obtain ⟨κ, hκ, hlow⟩ := anchor_lower_bound_eventually hL1c hL1 hp hC1 f.continuous
    f.hasCompactSupport f.nonneg' hf1
  have hdom : ∀ w, a₀ * f w ≤ χ w := by
    intro w
    by_cases hw : dist w p < r
    · calc a₀ * f w ≤ a₀ * 1 := mul_le_mul_of_nonneg_left f.le_one ha₀.le
        _ = a₀ := mul_one _
        _ ≤ χ w := hball hw
    · rw [f.zero_of_le_dist (not_lt.mp hw), mul_zero]
      exact hχ0 w
  have hlow' : ∀ᶠ t in atTop,
      (a₀ * κ) * t ^ (-(Fintype.card ι : ℝ)) ≤ ∫ w, χ w * Real.exp (-(t * L₁ w)) := by
    filter_upwards [hlow] with t ht
    calc (a₀ * κ) * t ^ (-(Fintype.card ι : ℝ)) = a₀ * (κ * t ^ (-(Fintype.card ι : ℝ))) := by
          ring
      _ ≤ a₀ * ∫ w, f w * Real.exp (-(t * L₁ w)) := mul_le_mul_of_nonneg_left ht ha₀.le
      _ = ∫ w, a₀ * f w * Real.exp (-(t * L₁ w)) := by
          rw [← integral_const_mul]
          refine integral_congr_ae (Filter.Eventually.of_forall fun w ↦ ?_)
          beta_reduce
          ring
      _ ≤ ∫ w, χ w * Real.exp (-(t * L₁ w)) := by
          refine integral_mono (integrable_mul_exp_neg_of_compactSupport
            (continuous_const.mul f.continuous) f.hasCompactSupport.mul_left hL1c t)
            (integrable_mul_exp_neg_of_compactSupport hχc hχs hL1c t) fun w ↦ ?_
          exact mul_le_mul_of_nonneg_right (hdom w) (Real.exp_pos _).le
  exact exists_scalar_upper_bound_of_lower_bound hL2c hL2 hχc hχs (by positivity) hlow' h0

/-! ### The coercivity sup bound -/

/-- `y^a e^{-y} ≤ ⌈a⌉! + 1` for `y ≥ 0`, `a ≥ 0`. -/
theorem rpow_mul_exp_neg_le {y a : ℝ} (hy : 0 ≤ y) (ha : 0 ≤ a) :
    y ^ a * Real.exp (-y) ≤ (Nat.ceil a).factorial + 1 := by
  set k : ℕ := Nat.ceil a with hk_def
  have hak : a ≤ k := Nat.le_ceil a
  have hexp : Real.exp (-y) ≤ 1 := Real.exp_le_one_iff.mpr (by linarith)
  have hfac : (0 : ℝ) ≤ k.factorial := by positivity
  rcases le_or_gt y 1 with hy1 | hy1
  · have h1 : y ^ a ≤ 1 := Real.rpow_le_one hy hy1 ha
    calc y ^ a * Real.exp (-y) ≤ 1 * 1 :=
          mul_le_mul h1 hexp (Real.exp_pos _).le zero_le_one
      _ ≤ k.factorial + 1 := by linarith
  · have h1 : y ^ a ≤ y ^ (k : ℝ) := Real.rpow_le_rpow_of_exponent_le hy1.le hak
    rw [Real.rpow_natCast] at h1
    have h2 : y ^ k * Real.exp (-y) ≤ k.factorial := by
      have h3 := Real.pow_div_factorial_le_exp y hy k
      have hpos : (0 : ℝ) < k.factorial := by positivity
      rw [div_le_iff₀ hpos] at h3
      rw [Real.exp_neg, ← div_eq_mul_inv, div_le_iff₀ (Real.exp_pos _)]
      linarith
    calc y ^ a * Real.exp (-y) ≤ y ^ k * Real.exp (-y) :=
          mul_le_mul_of_nonneg_right h1 (Real.exp_pos _).le
      _ ≤ k.factorial := h2
      _ ≤ k.factorial + 1 := by linarith

/-- **Coercivity sup bound**: `r^{2N} e^{-t c r^ν} ≤ K t^{-2N/ν}` uniformly in `r ≥ 0`. -/
theorem exists_pow_mul_exp_neg_rpow_bound {c ν : ℝ} (hc : 0 < c) (hν : 0 < ν) (N : ℕ) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ t : ℝ, 0 < t → ∀ r : ℝ, 0 ≤ r →
      r ^ (2 * N) * Real.exp (-(t * (c * r ^ ν))) ≤ K * t ^ (-(((2 * N : ℕ) : ℝ) / ν)) := by
  set a : ℝ := ((2 * N : ℕ) : ℝ) / ν with ha_def
  have ha : 0 ≤ a := by positivity
  set K : ℝ := ((Nat.ceil a).factorial + 1) * c ^ (-a) with hK_def
  refine ⟨K, by positivity, fun t ht r hr ↦ ?_⟩
  rcases eq_or_lt_of_le hr with hr0 | hr0
  · subst hr0
    rcases Nat.eq_zero_or_pos N with hN | hN
    · subst hN
      simp only [mul_zero, pow_zero, Real.zero_rpow hν.ne', Real.exp_zero, hK_def, ha_def,
        Nat.cast_zero, zero_div, neg_zero, Real.rpow_zero, mul_one, Nat.ceil_zero,
        Nat.factorial_zero, Nat.cast_one]
      norm_num
    · rw [zero_pow (by omega), zero_mul]
      positivity
  · set y : ℝ := t * (c * r ^ ν) with hy_def
    have hrν : 0 < r ^ ν := Real.rpow_pos_of_pos hr0 _
    have hy : 0 < y := by positivity
    have htc : 0 < t * c := mul_pos ht hc
    -- `r^{2N} = y^a (tc)^{-a}`
    have hpow : r ^ (2 * N) = y ^ a * (t * c) ^ (-a) := by
      have h1 : r ^ (2 * N) = (r ^ ν) ^ a := by
        rw [← Real.rpow_natCast, ← Real.rpow_mul hr0.le]
        congr 1
        rw [ha_def]
        field_simp
      have h2 : r ^ ν = y / (t * c) := by
        rw [hy_def]
        field_simp
      rw [h1, h2, Real.div_rpow hy.le htc.le, Real.rpow_neg htc.le, div_eq_mul_inv]
    have hmain := rpow_mul_exp_neg_le hy.le ha
    have hK' : K * t ^ (-a) = ((Nat.ceil a).factorial + 1) * (t * c) ^ (-a) := by
      rw [hK_def, Real.mul_rpow ht.le hc.le]
      ring
    calc r ^ (2 * N) * Real.exp (-(t * (c * r ^ ν)))
        = (y ^ a * Real.exp (-y)) * (t * c) ^ (-a) := by
          rw [hpow, ← hy_def]
          ring
      _ ≤ ((Nat.ceil a).factorial + 1) * (t * c) ^ (-a) :=
          mul_le_mul_of_nonneg_right hmain (Real.rpow_nonneg htc.le _)
      _ = K * t ^ (-a) := hK'.symm

/-! ### The polynomial majorant of the remainder -/

/-- `‖v‖^{2N} ≤ ∑ᵢ vᵢ^{2N}` for `N ≥ 1` (sup norm on `ι → ℝ`). -/
theorem norm_pow_le_sum_pow (v : ι → ℝ) {N : ℕ} (hN : 0 < N) :
    ‖v‖ ^ (2 * N) ≤ ∑ i, (v i) ^ (2 * N) := by
  set S : ℝ := ∑ i, (v i) ^ (2 * N) with hS_def
  have hS : 0 ≤ S := Finset.sum_nonneg fun i _ ↦ Even.pow_nonneg (even_two_mul N) _
  have hn : 2 * N ≠ 0 := by omega
  set r : ℝ := S ^ (((2 * N : ℕ) : ℝ)⁻¹) with hr_def
  have hr : 0 ≤ r := Real.rpow_nonneg hS _
  have hrpow : r ^ (2 * N) = S := Real.rpow_inv_natCast_pow hS hn
  have hle : ∀ i, |v i| ≤ r := by
    intro i
    have h1 : |v i| ^ (2 * N) ≤ S := by
      rw [Even.pow_abs (even_two_mul N)]
      exact Finset.single_le_sum (f := fun i ↦ (v i) ^ (2 * N))
        (fun i _ ↦ Even.pow_nonneg (even_two_mul N) _) (Finset.mem_univ i)
    rw [← hrpow] at h1
    exact (pow_le_pow_iff_left₀ (abs_nonneg _) hr hn).mp h1
  have hnorm : ‖v‖ ≤ r := by
    rw [pi_norm_le_iff_of_nonneg hr]
    intro i
    rw [Real.norm_eq_abs]
    exact hle i
  calc ‖v‖ ^ (2 * N) ≤ r ^ (2 * N) := pow_le_pow_left₀ (norm_nonneg _) hnorm _
    _ = S := hrpow

/-- `∑ᵢ vᵢ^{2N} ≤ d ‖v‖^{2N}`. -/
theorem sum_pow_le_card_mul_norm_pow (v : ι → ℝ) (N : ℕ) :
    ∑ i, (v i) ^ (2 * N) ≤ Fintype.card ι * ‖v‖ ^ (2 * N) := by
  have h : ∀ i, (v i) ^ (2 * N) ≤ ‖v‖ ^ (2 * N) := fun i ↦ by
    rw [← Even.pow_abs (even_two_mul N), ← Real.norm_eq_abs]
    exact pow_le_pow_left₀ (norm_nonneg _) (norm_le_pi_norm v i) _
  calc ∑ i, (v i) ^ (2 * N) ≤ ∑ _i : ι, ‖v‖ ^ (2 * N) := Finset.sum_le_sum fun i _ ↦ h i
    _ = Fintype.card ι * ‖v‖ ^ (2 * N) := by
        rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]

/-- The majorant `∑ᵢ (xᵢ - pᵢ)^{2N}` is the sum of the constant-word monomials. -/
theorem sum_pow_eq_sum_coordMonomial (p x : ι → ℝ) (N : ℕ) :
    ∑ i, (x i - p i) ^ (2 * N) = ∑ i, coordMonomial p (fun _ : Fin (2 * N) ↦ i) x := by
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  unfold coordMonomial
  rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin]

/-! ### From the family to every test supported near `p` -/

/-- **Transfer from the cutoff monomials to all smooth tests near `p`.** Under the
coercivity of `L₁` on `tsupport χ`, a polynomial bound on `C`, and superpolynomial
projective agreement on the family `χ · coordMonomial p m`, every smooth compactly
supported test with support in `ball p ρ` (where `χ = 1`) has superpolynomial
projective agreement. -/
theorem superPoly_projDiff_weight_mul_of_monomials
    (h1c : Continuous L₁) (h2c : Continuous L₂)
    {χ : (ι → ℝ) → ℝ} (hχc : Continuous χ) (hχs : HasCompactSupport χ) (hχ0 : ∀ w, 0 ≤ χ w)
    {p : ι → ℝ}
    {c ν : ℝ} (hc : 0 < c) (hν : 0 < ν) (hcoer : ∀ w ∈ tsupport χ, c * ‖w - p‖ ^ ν ≤ L₁ w)
    {A : ℝ} (hA : 0 ≤ A) (hCbound : ∀ᶠ t in atTop, |C t| ≤ A * t ^ (Fintype.card ι))
    (hfam : ∀ (k : ℕ) (m : Fin k → ι),
      SuperPoly (projDiff L₁ L₂ C fun w ↦ χ w * coordMonomial p m w))
    {φ : (ι → ℝ) → ℝ} (hφ : ContDiff ℝ ∞ φ) (hφs : HasCompactSupport φ) :
    SuperPoly (projDiff L₁ L₂ C fun w ↦ χ w * φ w) := by
  classical
  refine superPoly_of_forall_eventually_le fun N₀ ↦ ?_
  set d : ℕ := Fintype.card ι with hd_def
  -- the Taylor order
  obtain ⟨N, hN1, hNa⟩ : ∃ N : ℕ, 0 < N ∧ (N₀ : ℝ) + d + 1 ≤ ((2 * N : ℕ) : ℝ) / ν := by
    refine ⟨⌈ν * ((N₀ : ℝ) + d + 1) / 2⌉₊ + 1, Nat.succ_pos _, ?_⟩
    rw [le_div_iff₀ hν]
    have := Nat.le_ceil (ν * ((N₀ : ℝ) + d + 1) / 2)
    push_cast
    linarith
  set n : ℕ := 2 * N - 1 with hn_def
  have hn1 : n + 1 = 2 * N := by omega
  obtain ⟨M, hM0, hM⟩ := exists_taylor_remainder_bound hφ hφs p n
  rw [hn1] at hM
  set T : (ι → ℝ) → ℝ := fun x ↦ ∑ k ∈ Finset.range (2 * N),
    ((k.factorial : ℝ)⁻¹) * iteratedFDeriv ℝ k φ p (fun _ ↦ x - p) with hT_def
  have hTc : Continuous T := by
    refine continuous_finsetSum _ fun k _ ↦ continuous_const.mul ?_
    exact (iteratedFDeriv ℝ k φ p).coe_continuous.comp
      (continuous_pi fun _ ↦ continuous_id.sub continuous_const)
  -- the decomposition of the weighted test
  have hsplit : (fun w ↦ χ w * φ w) = fun x ↦ χ x * T x + χ x * (φ x - T x) := by
    funext x
    ring
  have hχT_c : Continuous fun w ↦ χ w * T w := hχc.mul hTc
  have hχT_s : HasCompactSupport fun w ↦ χ w * T w := hχs.mul_right
  have hrem_c : Continuous fun w ↦ χ w * (φ w - T w) := hχc.mul (hφ.continuous.sub hTc)
  have hrem_s : HasCompactSupport fun w ↦ χ w * (φ w - T w) := hχs.mul_right
  have hdecomp : ∀ t, projDiff L₁ L₂ C (fun w ↦ χ w * φ w) t =
      projDiff L₁ L₂ C (fun w ↦ χ w * T w) t +
      projDiff L₁ L₂ C (fun w ↦ χ w * (φ w - T w)) t := by
    intro t
    rw [← projDiff_add h1c h2c hχT_c hχT_s hrem_c hrem_s]
    conv_lhs => rw [hsplit]
  -- (1) the Taylor part is a finite combination of the family
  set coef : (k : ℕ) → (Fin k → ι) → ℝ := fun k m ↦
    (k.factorial : ℝ)⁻¹ * iteratedFDeriv ℝ k φ p (fun j ↦ Pi.single (m j) (1 : ℝ)) with hcoef_def
  have hTexp : (fun w ↦ χ w * T w) = fun w ↦ ∑ k ∈ Finset.range (2 * N),
      ∑ m : Fin k → ι, coef k m * (χ w * coordMonomial p m w) := by
    funext w
    simp only [hT_def, Finset.mul_sum]
    refine Finset.sum_congr rfl fun k _ ↦ ?_
    rw [iteratedFDeriv_apply_const_eq_sum_words, Finset.mul_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun m _ ↦ ?_
    simp only [hcoef_def]
    ring
  have hmono_c : ∀ (k : ℕ) (m : Fin k → ι), Continuous fun w ↦ χ w * coordMonomial p m w :=
    fun k m ↦ hχc.mul (coordMonomial_continuous p m)
  have hmono_s : ∀ (k : ℕ) (m : Fin k → ι), HasCompactSupport fun w ↦ χ w * coordMonomial p m w :=
    fun k m ↦ hχs.mul_right
  have hTpart : SuperPoly (projDiff L₁ L₂ C fun w ↦ χ w * T w) := by
    have key : ∀ t, projDiff L₁ L₂ C (fun w ↦ ∑ k ∈ Finset.range (2 * N),
        ∑ m : Fin k → ι, coef k m * (χ w * coordMonomial p m w)) t =
        ∑ k ∈ Finset.range (2 * N), ∑ m : Fin k → ι,
          coef k m * projDiff L₁ L₂ C (fun w ↦ χ w * coordMonomial p m w) t := by
      intro t
      rw [projDiff_finset_sum _ h1c h2c
        (fun k w ↦ ∑ m : Fin k → ι, coef k m * (χ w * coordMonomial p m w))
        (fun k ↦ continuous_finsetSum _ fun m _ ↦ continuous_const.mul (hmono_c k m))
        (fun k ↦ hasCompactSupport_finset_sum' _ _ fun m ↦ (hmono_s k m).mul_left)]
      refine Finset.sum_congr rfl fun k _ ↦ ?_
      rw [projDiff_finset_sum _ h1c h2c (fun m w ↦ coef k m * (χ w * coordMonomial p m w))
        (fun m ↦ continuous_const.mul (hmono_c k m)) (fun m ↦ (hmono_s k m).mul_left)]
      refine Finset.sum_congr rfl fun m _ ↦ ?_
      exact projDiff_const_mul _ _ _
    have hS : SuperPoly fun t ↦ ∑ k ∈ Finset.range (2 * N), ∑ m : Fin k → ι,
        coef k m * projDiff L₁ L₂ C (fun w ↦ χ w * coordMonomial p m w) t :=
      SuperPoly.finset_sum _ fun k _ ↦ SuperPoly.finset_sum _ fun m _ ↦ (hfam k m).const_mul _
    rw [hTexp]
    intro N'
    exact (hS N').congr' (Eventually.of_forall fun t ↦ (key t).symm) EventuallyEq.rfl
  -- (2) the remainder part, via the polynomial majorant
  obtain ⟨K, hK0, hK⟩ := exists_pow_mul_exp_neg_rpow_bound hc hν N
  set a : ℝ := ((2 * N : ℕ) : ℝ) / ν with ha_def
  set ρ' : (ι → ℝ) → ℝ := fun w ↦ ∑ i, (w i - p i) ^ (2 * N) with hρ'_def
  have hρ'c : Continuous ρ' := by
    simp only [hρ'_def]
    fun_prop
  have hρ'0 : ∀ w, 0 ≤ ρ' w := fun w ↦
    Finset.sum_nonneg fun i _ ↦ Even.pow_nonneg (even_two_mul N) _
  have hremle : ∀ w, |χ w * (φ w - T w)| ≤ M * (χ w * ρ' w) := by
    intro w
    have h1 : ‖w - p‖ ^ (2 * N) ≤ ρ' w := by
      have := norm_pow_le_sum_pow (w - p) hN1
      simpa [hρ'_def] using this
    rw [abs_mul, abs_of_nonneg (hχ0 w)]
    calc χ w * |φ w - T w| ≤ χ w * (M * ‖w - p‖ ^ (2 * N)) :=
          mul_le_mul_of_nonneg_left (hM w) (hχ0 w)
      _ ≤ χ w * (M * ρ' w) :=
          mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left h1 hM0) (hχ0 w)
      _ = M * (χ w * ρ' w) := by ring
  have hχint : Integrable χ := hχc.integrable_of_hasCompactSupport hχs
  have hχnn : 0 ≤ ∫ w, χ w := integral_nonneg hχ0
  -- the `L₁`-mass of the majorant
  have hL1maj : ∀ t : ℝ, 0 < t →
      ∫ w, χ w * ρ' w * Real.exp (-(t * L₁ w)) ≤ d * K * t ^ (-a) * ∫ w, χ w := by
    intro t ht
    have hpt : ∀ w, χ w * ρ' w * Real.exp (-(t * L₁ w)) ≤ (d * K * t ^ (-a)) * χ w := by
      intro w
      by_cases hw : χ w = 0
      · simp [hw]
      · have hwsupp : w ∈ tsupport χ := subset_tsupport χ hw
        have hco := hcoer w hwsupp
        have hρ'le : ρ' w ≤ d * ‖w - p‖ ^ (2 * N) := by
          have := sum_pow_le_card_mul_norm_pow (w - p) N
          simpa [hρ'_def, hd_def] using this
        have hexple : Real.exp (-(t * L₁ w)) ≤ Real.exp (-(t * (c * ‖w - p‖ ^ ν))) :=
          Real.exp_le_exp.mpr (neg_le_neg (mul_le_mul_of_nonneg_left hco ht.le))
        have hsup := hK t ht ‖w - p‖ (norm_nonneg _)
        have hd0 : (0 : ℝ) ≤ d := by positivity
        calc χ w * ρ' w * Real.exp (-(t * L₁ w))
            ≤ χ w * (d * ‖w - p‖ ^ (2 * N)) * Real.exp (-(t * (c * ‖w - p‖ ^ ν))) :=
              mul_le_mul (mul_le_mul_of_nonneg_left hρ'le (hχ0 w)) hexple (Real.exp_pos _).le
                (mul_nonneg (hχ0 w) (by positivity))
          _ = χ w * d * (‖w - p‖ ^ (2 * N) * Real.exp (-(t * (c * ‖w - p‖ ^ ν)))) := by ring
          _ ≤ χ w * d * (K * t ^ (-a)) :=
              mul_le_mul_of_nonneg_left hsup (mul_nonneg (hχ0 w) hd0)
          _ = (d * K * t ^ (-a)) * χ w := by ring
    calc ∫ w, χ w * ρ' w * Real.exp (-(t * L₁ w))
        ≤ ∫ w, (d * K * t ^ (-a)) * χ w :=
          integral_mono (integrable_mul_exp_neg_of_compactSupport (hχc.mul hρ'c)
            hχs.mul_right h1c t) (hχint.const_mul _) hpt
      _ = d * K * t ^ (-a) * ∫ w, χ w := integral_const_mul _ _
  -- the `L₂`-mass of the majorant via the family
  have hmaj_eq : ∀ w, χ w * ρ' w =
      ∑ i, χ w * coordMonomial p (fun _ : Fin (2 * N) ↦ i) w := by
    intro w
    simp only [hρ'_def, sum_pow_eq_sum_coordMonomial, Finset.mul_sum]
  have hL2maj : ∀ t : ℝ, ∫ w, χ w * ρ' w * Real.exp (-(t * L₂ w)) =
      C t * (∫ w, χ w * ρ' w * Real.exp (-(t * L₁ w))) +
        ∑ i, projDiff L₁ L₂ C (fun w ↦ χ w * coordMonomial p (fun _ : Fin (2 * N) ↦ i) w) t := by
    intro t
    have h2 : ∫ w, χ w * ρ' w * Real.exp (-(t * L₂ w)) =
        ∑ i, ∫ w, χ w * coordMonomial p (fun _ : Fin (2 * N) ↦ i) w * Real.exp (-(t * L₂ w)) := by
      rw [← integral_finsetSum _ fun i _ ↦
        integrable_mul_exp_neg_of_compactSupport (hmono_c _ _) (hmono_s _ _) h2c t]
      congr 1
      funext w
      rw [hmaj_eq w, Finset.sum_mul]
    have h1 : ∫ w, χ w * ρ' w * Real.exp (-(t * L₁ w)) =
        ∑ i, ∫ w, χ w * coordMonomial p (fun _ : Fin (2 * N) ↦ i) w * Real.exp (-(t * L₁ w)) := by
      rw [← integral_finsetSum _ fun i _ ↦
        integrable_mul_exp_neg_of_compactSupport (hmono_c _ _) (hmono_s _ _) h1c t]
      congr 1
      funext w
      rw [hmaj_eq w, Finset.sum_mul]
    rw [h2, h1, Finset.mul_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun i _ ↦ ?_
    unfold projDiff
    ring
  have hfamsum : SuperPoly fun t ↦
      ∑ i, projDiff L₁ L₂ C (fun w ↦ χ w * coordMonomial p (fun _ : Fin (2 * N) ↦ i) w) t :=
    SuperPoly.finset_sum _ fun i _ ↦ hfam (2 * N) _
  -- eventual bounds on the two superpolynomial pieces
  have hTev : ∀ᶠ t in atTop, |projDiff L₁ L₂ C (fun w ↦ χ w * T w) t| ≤ t ^ (-(N₀ : ℝ)) := by
    have := isLittleO_iff.mp (hTpart N₀) one_pos
    filter_upwards [this, eventually_gt_atTop (0 : ℝ)] with t ht htpos
    rw [Real.norm_eq_abs, Real.norm_of_nonneg (Real.rpow_nonneg htpos.le _), one_mul] at ht
    exact ht
  have hFev : ∀ᶠ t in atTop, |∑ i, projDiff L₁ L₂ C
      (fun w ↦ χ w * coordMonomial p (fun _ : Fin (2 * N) ↦ i) w) t| ≤ t ^ (-(N₀ : ℝ)) := by
    have := isLittleO_iff.mp (hfamsum N₀) one_pos
    filter_upwards [this, eventually_gt_atTop (0 : ℝ)] with t ht htpos
    rw [Real.norm_eq_abs, Real.norm_of_nonneg (Real.rpow_nonneg htpos.le _), one_mul] at ht
    exact ht
  refine ⟨1 + 2 * M * A * d * K * (∫ w, χ w) + M, ?_⟩
  filter_upwards [hTev, hFev, hCbound, eventually_ge_atTop (1 : ℝ)] with t hT hF hCt ht1
  have htpos : 0 < t := lt_of_lt_of_le one_pos ht1
  have htN : 0 ≤ t ^ (-(N₀ : ℝ)) := Real.rpow_nonneg htpos.le _
  -- `t^d t^{-a} ≤ t^{-N₀}`
  have hpow : (t : ℝ) ^ d * t ^ (-a) ≤ t ^ (-(N₀ : ℝ)) := by
    rw [← Real.rpow_natCast, ← Real.rpow_add htpos]
    exact Real.rpow_le_rpow_of_exponent_le ht1 (by linarith)
  -- the remainder part
  set R₂ : ℝ := ∫ w, χ w * (φ w - T w) * Real.exp (-(t * L₂ w)) with hR₂_def
  set R₁ : ℝ := ∫ w, χ w * (φ w - T w) * Real.exp (-(t * L₁ w)) with hR₁_def
  set J₂ : ℝ := ∫ w, χ w * ρ' w * Real.exp (-(t * L₂ w)) with hJ₂_def
  set J₁ : ℝ := ∫ w, χ w * ρ' w * Real.exp (-(t * L₁ w)) with hJ₁_def
  have hJ₁0 : 0 ≤ J₁ := integral_nonneg fun w ↦
    mul_nonneg (mul_nonneg (hχ0 w) (hρ'0 w)) (Real.exp_pos _).le
  have hRle : ∀ (L : (ι → ℝ) → ℝ), Continuous L →
      |∫ w, χ w * (φ w - T w) * Real.exp (-(t * L w))| ≤
        M * ∫ w, χ w * ρ' w * Real.exp (-(t * L w)) := by
    intro L hLc
    calc |∫ w, χ w * (φ w - T w) * Real.exp (-(t * L w))|
        ≤ ∫ w, |χ w * (φ w - T w) * Real.exp (-(t * L w))| := abs_integral_le_integral_abs
      _ ≤ ∫ w, M * (χ w * ρ' w * Real.exp (-(t * L w))) := by
          refine integral_mono (integrable_mul_exp_neg_of_compactSupport hrem_c hrem_s hLc t).abs
            ((integrable_mul_exp_neg_of_compactSupport (hχc.mul hρ'c) hχs.mul_right hLc t).const_mul
              M) fun w ↦ ?_
          rw [abs_mul, abs_of_pos (Real.exp_pos _)]
          calc |χ w * (φ w - T w)| * Real.exp (-(t * L w))
              ≤ M * (χ w * ρ' w) * Real.exp (-(t * L w)) :=
                mul_le_mul_of_nonneg_right (hremle w) (Real.exp_pos _).le
            _ = M * (χ w * ρ' w * Real.exp (-(t * L w))) := by ring
      _ = M * ∫ w, χ w * ρ' w * Real.exp (-(t * L w)) := integral_const_mul _ _
  have hR₂le : |R₂| ≤ M * J₂ := hRle L₂ h2c
  have hR₁le : |R₁| ≤ M * J₁ := hRle L₁ h1c
  have hJ₁le : J₁ ≤ d * K * t ^ (-a) * ∫ w, χ w := hL1maj t htpos
  have hJ₂le : J₂ ≤ |C t| * J₁ + t ^ (-(N₀ : ℝ)) := by
    have := hL2maj t
    rw [← hJ₂_def, ← hJ₁_def] at this
    rw [this]
    have h1 : C t * J₁ ≤ |C t| * J₁ := mul_le_mul_of_nonneg_right (le_abs_self _) hJ₁0
    have h2 := le_abs_self (∑ i, projDiff L₁ L₂ C
      (fun w ↦ χ w * coordMonomial p (fun _ : Fin (2 * N) ↦ i) w) t)
    linarith
  have hCJ : |C t| * J₁ ≤ A * d * K * (∫ w, χ w) * t ^ (-(N₀ : ℝ)) := by
    calc |C t| * J₁ ≤ (A * t ^ d) * (d * K * t ^ (-a) * ∫ w, χ w) :=
          mul_le_mul hCt hJ₁le hJ₁0 (by positivity)
      _ = A * d * K * (∫ w, χ w) * (t ^ d * t ^ (-a)) := by ring
      _ ≤ A * d * K * (∫ w, χ w) * t ^ (-(N₀ : ℝ)) := by gcongr
  have hRpart : |projDiff L₁ L₂ C (fun w ↦ χ w * (φ w - T w)) t| ≤
      (2 * M * A * d * K * (∫ w, χ w) + M) * t ^ (-(N₀ : ℝ)) := by
    have hexpand : projDiff L₁ L₂ C (fun w ↦ χ w * (φ w - T w)) t = R₂ - C t * R₁ := rfl
    rw [hexpand]
    calc |R₂ - C t * R₁| ≤ |R₂| + |C t| * |R₁| := by
          rw [← abs_mul]
          exact abs_sub _ _
      _ ≤ M * J₂ + |C t| * (M * J₁) :=
          add_le_add hR₂le (mul_le_mul_of_nonneg_left hR₁le (abs_nonneg _))
      _ ≤ M * (|C t| * J₁ + t ^ (-(N₀ : ℝ))) + M * (|C t| * J₁) := by
          have := mul_le_mul_of_nonneg_left hJ₂le hM0
          nlinarith [mul_nonneg (abs_nonneg (C t)) hJ₁0]
      _ = 2 * M * (|C t| * J₁) + M * t ^ (-(N₀ : ℝ)) := by ring
      _ ≤ 2 * M * (A * d * K * (∫ w, χ w) * t ^ (-(N₀ : ℝ))) + M * t ^ (-(N₀ : ℝ)) := by
          gcongr
      _ = (2 * M * A * d * K * (∫ w, χ w) + M) * t ^ (-(N₀ : ℝ)) := by ring
  rw [hdecomp t]
  calc |projDiff L₁ L₂ C (fun w ↦ χ w * T w) t +
        projDiff L₁ L₂ C (fun w ↦ χ w * (φ w - T w)) t|
      ≤ |projDiff L₁ L₂ C (fun w ↦ χ w * T w) t| +
        |projDiff L₁ L₂ C (fun w ↦ χ w * (φ w - T w)) t| := abs_add_le _ _
    _ ≤ t ^ (-(N₀ : ℝ)) + (2 * M * A * d * K * (∫ w, χ w) + M) * t ^ (-(N₀ : ℝ)) :=
        add_le_add hT hRpart
    _ = (1 + 2 * M * A * d * K * (∫ w, χ w) + M) * t ^ (-(N₀ : ℝ)) := by ring

/-- The cutoff form: for a window `χ = 1` on `ball p ρ` and a smooth test supported in that
ball, the weighted test is the test itself. -/
theorem superPoly_projDiff_of_cutoff_monomials
    (h1c : Continuous L₁) (h2c : Continuous L₂)
    {χ : (ι → ℝ) → ℝ} (hχc : Continuous χ) (hχs : HasCompactSupport χ) (hχ0 : ∀ w, 0 ≤ χ w)
    {p : ι → ℝ} {ρ : ℝ} (hχ1 : ∀ w ∈ Metric.ball p ρ, χ w = 1)
    {c ν : ℝ} (hc : 0 < c) (hν : 0 < ν) (hcoer : ∀ w ∈ tsupport χ, c * ‖w - p‖ ^ ν ≤ L₁ w)
    {A : ℝ} (hA : 0 ≤ A) (hCbound : ∀ᶠ t in atTop, |C t| ≤ A * t ^ (Fintype.card ι))
    (hfam : ∀ (k : ℕ) (m : Fin k → ι),
      SuperPoly (projDiff L₁ L₂ C fun w ↦ χ w * coordMonomial p m w))
    {φ : (ι → ℝ) → ℝ} (hφ : ContDiff ℝ ∞ φ) (hφs : HasCompactSupport φ)
    (hφsupp : tsupport φ ⊆ Metric.ball p ρ) :
    SuperPoly (projDiff L₁ L₂ C φ) := by
  have hχφ : (fun w ↦ χ w * φ w) = φ := by
    funext x
    by_cases hx : x ∈ tsupport φ
    · rw [hχ1 x (hφsupp hx), one_mul]
    · rw [image_eq_zero_of_notMem_tsupport hx, mul_zero]
  have := superPoly_projDiff_weight_mul_of_monomials h1c h2c hχc hχs hχ0 hc hν hcoer hA hCbound
    hfam hφ hφs
  rwa [hχφ] at this

/-! ### The fixed-family theorem -/

/-- **A fixed sufficient family in the singular case.** Let `χ` be a smooth compactly
supported nonnegative cutoff equal to `1` on `ball p ρ`, and let `L₁ ≥ c ‖x - p‖^ν` on its
support (an isolated zero at `p`, quantitatively). If the projective hypothesis holds beyond
all orders for the family `χ · ∏ⱼ (x (m j) - p (m j))` over all words `m` (countably many
observables, fixed in advance), then `L₁ = L₂` near `p`. -/
theorem normalized_families_force_germ_eq_at_of_cutoff_monomials
    (h1 : ContDiff ℝ ∞ L₁) (h2 : ContDiff ℝ ∞ L₂)
    (hL1 : ∀ w, 0 ≤ L₁ w) (hL2 : ∀ w, 0 ≤ L₂ w) {p : ι → ℝ}
    (hA1 : AnalyticAt ℝ L₁ p) (hA2 : AnalyticAt ℝ L₂ p) (hp1 : L₁ p = 0) (hp2 : L₂ p = 0)
    {χ : (ι → ℝ) → ℝ} (hχ : ContDiff ℝ ∞ χ) (hχs : HasCompactSupport χ) (hχ0 : ∀ w, 0 ≤ χ w)
    {ρ : ℝ} (hρ : 0 < ρ) (hχ1 : ∀ w ∈ Metric.ball p ρ, χ w = 1)
    {c ν : ℝ} (hc : 0 < c) (hν : 0 < ν) (hcoer : ∀ w ∈ tsupport χ, c * ‖w - p‖ ^ ν ≤ L₁ w)
    (hfam : ∀ (k : ℕ) (m : Fin k → ι),
      SuperPoly (projDiff L₁ L₂ C fun w ↦ χ w * coordMonomial p m w)) :
    ∀ᶠ w in 𝓝 p, L₁ w = L₂ w := by
  have hχ1' : ∀ᶠ w in 𝓝 p, χ w = 1 :=
    (Metric.isOpen_ball.eventually_mem (Metric.mem_ball_self hρ)).mono hχ1
  -- the degree-zero member is `χ` itself
  have h0 : SuperPoly (projDiff L₁ L₂ C χ) := by
    have := hfam 0 Fin.elim0
    have hχeq : (fun w ↦ χ w * coordMonomial p Fin.elim0 w) = χ := by
      funext w
      simp [coordMonomial, Finset.univ_eq_empty]
    rwa [hχeq] at this
  obtain ⟨A, hA, hCbound⟩ := exists_scalar_upper_bound_of_window h1.continuous h2.continuous
    hL1 hL2 hp1 hA1.contDiffAt hχ.continuous hχs hχ0 hχ1' h0
  refine normalized_families_force_germ_eq_at_local (C := C) h1 h2 hL1 hL2 hA1 hA2 hp1 hp2 hρ ?_
  intro φ hφ hφs hφsupp
  exact superPoly_projDiff_of_cutoff_monomials h1.continuous h2.continuous hχ.continuous hχs
    hχ0 hχ1 hc hν hcoer hA hCbound hfam hφ hφs hφsupp

end Laplace
