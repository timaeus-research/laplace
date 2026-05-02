import Laplace.OneD.Quartic
import Laplace.OneD.TailBound

/-!
# Bounded-prior quartic partition function

This file refines the pure-quartic partition function `quartic_partition` (in
`Laplace.OneD.Quartic`) by replacing the integration domain `ℝ` with a bounded
interval `[-a, a]` and quantifying the resulting boundary correction.

## Headline result

* `quartic_partition_bounded_prior`: for `t > 0` and `a > 0`,

  ```
  | ∫_{[-a,a]} exp(-(t · w⁴/24)) dw  −  (1/2) · (24/t)^{1/4} · Γ(1/4) |
      ≤ (24/(t · a³)) · exp(-(t · a⁴/24)).
  ```

  The leading term is exact `quartic_partition`; the remainder is the doubled
  half-line tail bounded by `quartic_tail_Ioi` below.

## Key sublemma

* `quartic_tail_Ioi`: for `t > 0` and `a > 0`,

  ```
  ∫_{Ioi a} exp(-(t · w⁴/24)) dw  ≤  (12/(t · a³)) · exp(-(t · a⁴/24)).
  ```

  Proof strategy (GPT-5.5 Pro): the pointwise bound `w⁴ ≥ a²·w²` for `w ≥ a`
  gives `exp(-(t · w⁴/24)) ≤ exp(-((t · a²/12) · w²)/2)`. Apply the existing
  `gaussian_tail_bound_rescaled_Ioi` at `b = t · a²/12`, `M = a` to get the
  exponential bound `exp(-(t · a⁴/24)) / ((t · a²/12) · a) = (12/(t · a³))
  · exp(-(t · a⁴/24))`.

## Why this is a tide step

This is the smallest possible step toward the grammar paper's
`Z_n[φ] = ∫ φ(w) e^{-n K(w)} π(w) dw` machinery: it adds **only** the bounded
prior ingredient, leaving the test function `φ` and the explicit asymptotic
remainder for follow-up tide steps. See
`projects/automation/log/2026-05-02-tide-grammar-precursor.md` in the SRI repo
for the deliberation log.
-/

open Real MeasureTheory Set
open scoped Nat

namespace Laplace.OneD

/-! ## The key tail sublemma -/

/-- **Quartic half-line tail bound**: for `t, a > 0`,

  `∫_{Ioi a} exp(-(t · w⁴/24)) dw ≤ (12/(t · a³)) · exp(-(t · a⁴/24))`.

Proven by the comparison `w⁴ ≥ a²·w²` for `w ≥ a`, reducing the quartic tail
to the existing Gaussian tail `gaussian_tail_bound_rescaled_Ioi`. -/
theorem quartic_tail_Ioi {t a : ℝ} (ht : 0 < t) (ha : 0 < a) :
    ∫ w in Ioi a, Real.exp (-(t * w ^ 4 / 24)) ≤
      (12 / (t * a ^ 3)) * Real.exp (-(t * a ^ 4 / 24)) := by
  -- Comparator Gaussian rate: b = t · a² / 12.
  set b : ℝ := t * a ^ 2 / 12 with hb_def
  have hb_pos : 0 < b := by
    have ha2 : 0 < a ^ 2 := pow_pos ha 2
    positivity
  -- Pointwise: for w ≥ a, exp(-(t·w⁴/24)) ≤ exp(-(b·w²)/2).
  have hpw : ∀ w ∈ Ioi a, Real.exp (-(t * w ^ 4 / 24)) ≤
      Real.exp (-(b * w ^ 2) / 2) := by
    intro w hw
    apply Real.exp_le_exp.mpr
    have hw_ge : a ≤ w := le_of_lt hw
    have hw2_ge : a ^ 2 ≤ w ^ 2 := by
      rw [sq, sq]; exact mul_self_le_mul_self ha.le hw_ge
    have hw2_nn : (0 : ℝ) ≤ w ^ 2 := sq_nonneg w
    have hw4_ge : a ^ 2 * w ^ 2 ≤ w ^ 4 := by
      have h : (w : ℝ) ^ 4 = w ^ 2 * w ^ 2 := by ring
      rw [h]; exact mul_le_mul_of_nonneg_right hw2_ge hw2_nn
    have htw4 : t * (a ^ 2 * w ^ 2) ≤ t * w ^ 4 :=
      mul_le_mul_of_nonneg_left hw4_ge ht.le
    have heq : (b * w ^ 2) / 2 = t * (a ^ 2 * w ^ 2) / 24 := by
      rw [hb_def]; ring
    linarith
  -- Integrability of the LHS on Ioi a (via existing seabed integrability on ℝ).
  have hint_lhs : IntegrableOn
      (fun w : ℝ => Real.exp (-(t * w ^ 4 / 24))) (Ioi a) volume := by
    have h := quartic_integrable_pow 0 ht
    have heq : (fun w : ℝ => w ^ 0 * Real.exp (-(t * w ^ 4 / 24))) =
               (fun w : ℝ => Real.exp (-(t * w ^ 4 / 24))) := by
      ext w; rw [pow_zero, one_mul]
    rw [heq] at h
    exact h.integrableOn
  -- Integrability of the comparator on Ioi a (via Mathlib's Gaussian integrability).
  have hint_rhs : IntegrableOn
      (fun w : ℝ => Real.exp (-(b * w ^ 2) / 2)) (Ioi a) volume := by
    have hb2 : (0 : ℝ) < b / 2 := by positivity
    have h := integrable_exp_neg_mul_sq hb2
    have heq : (fun w : ℝ => Real.exp (-(b / 2) * w ^ 2)) =
               (fun w : ℝ => Real.exp (-(b * w ^ 2) / 2)) := by
      ext w; congr 1; ring
    rw [heq] at h
    exact h.integrableOn
  -- Combine: pointwise bound + Mill's-ratio bound on the Gaussian.
  calc ∫ w in Ioi a, Real.exp (-(t * w ^ 4 / 24))
      ≤ ∫ w in Ioi a, Real.exp (-(b * w ^ 2) / 2) :=
        setIntegral_mono_on hint_lhs hint_rhs measurableSet_Ioi hpw
    _ ≤ Real.exp (-(b * a ^ 2) / 2) / (b * a) :=
        gaussian_tail_bound_rescaled_Ioi ha hb_pos
    _ = (12 / (t * a ^ 3)) * Real.exp (-(t * a ^ 4 / 24)) := by
        rw [hb_def]
        have h_arg : (-(t * a ^ 2 / 12 * a ^ 2) / 2 : ℝ) = -(t * a ^ 4 / 24) := by ring
        rw [h_arg]
        have ha_ne : (a : ℝ) ≠ 0 := ne_of_gt ha
        have ht_ne : (t : ℝ) ≠ 0 := ne_of_gt ht
        field_simp

/-! ## Tail symmetry -/

/-- The lower-tail integral equals the upper-tail integral by evenness of
`exp(-(t · w⁴/24))`. -/
theorem quartic_integral_Iio_neg_eq_integral_Ioi (t a : ℝ) :
    ∫ w in Iio (-a), Real.exp (-(t * w ^ 4 / 24)) =
      ∫ w in Ioi a, Real.exp (-(t * w ^ 4 / 24)) := by
  rw [← integral_Iic_eq_integral_Iio]
  have hsub := integral_comp_neg_Iic (-a) (fun y : ℝ => Real.exp (-(t * y ^ 4 / 24)))
  rw [show (-(-a) : ℝ) = a from neg_neg a] at hsub
  rw [show (fun w : ℝ => Real.exp (-(t * (-w) ^ 4 / 24))) =
        (fun w : ℝ => Real.exp (-(t * w ^ 4 / 24))) from by
        ext w
        rw [show ((-w) : ℝ) ^ 4 = w ^ 4 from by ring]] at hsub
  exact hsub

/-! ## Splitting the full-line partition function -/

/-- The full-line partition function decomposes as the bounded-prior integral
plus two equal tails. -/
theorem quartic_partition_split {t a : ℝ} (ht : 0 < t) (ha : 0 < a) :
    ∫ w : ℝ, Real.exp (-(t * w ^ 4 / 24)) =
      (∫ w in Icc (-a) a, Real.exp (-(t * w ^ 4 / 24))) +
        2 * ∫ w in Ioi a, Real.exp (-(t * w ^ 4 / 24)) := by
  -- Integrability over ℝ comes from the seabed.
  have hint_full : Integrable (fun w : ℝ => Real.exp (-(t * w ^ 4 / 24))) := by
    have h := quartic_integrable_pow 0 ht
    have heq : (fun w : ℝ => w ^ 0 * Real.exp (-(t * w ^ 4 / 24))) =
               (fun w : ℝ => Real.exp (-(t * w ^ 4 / 24))) := by
      ext w; rw [pow_zero, one_mul]
    rwa [heq] at h
  -- Step 1: ℝ = Iic a ∪ Ioi a (disjoint, measurable).
  have h1 : ∫ w : ℝ, Real.exp (-(t * w ^ 4 / 24)) =
      (∫ w in Iic a, Real.exp (-(t * w ^ 4 / 24))) +
        ∫ w in Ioi a, Real.exp (-(t * w ^ 4 / 24)) := by
    rw [← intervalIntegral.integral_Iic_add_Ioi
          hint_full.integrableOn hint_full.integrableOn]
  -- Step 2: Iic a = Iio (-a) ∪ Icc (-a) a (disjoint, measurable).
  have hunion : Iio (-a) ∪ Icc (-a) a = Iic a := by
    ext x
    simp only [Set.mem_union, Set.mem_Iio, Set.mem_Icc, Set.mem_Iic]
    constructor
    · rintro (hlt | ⟨_, hub⟩)
      · linarith
      · exact hub
    · intro hub
      rcases lt_or_ge x (-a) with hlt | hge
      · exact Or.inl hlt
      · exact Or.inr ⟨hge, hub⟩
  have hdisj : Disjoint (Iio (-a)) (Icc (-a) a) := by
    rw [Set.disjoint_iff_inter_eq_empty]
    ext x
    simp only [Set.mem_inter_iff, Set.mem_Iio, Set.mem_Icc, Set.mem_empty_iff_false, iff_false]
    rintro ⟨hlt, hge, _⟩
    linarith
  have h2 : ∫ w in Iic a, Real.exp (-(t * w ^ 4 / 24)) =
      (∫ w in Iio (-a), Real.exp (-(t * w ^ 4 / 24))) +
        ∫ w in Icc (-a) a, Real.exp (-(t * w ^ 4 / 24)) := by
    rw [← hunion]
    exact setIntegral_union hdisj measurableSet_Icc
      hint_full.integrableOn hint_full.integrableOn
  -- Combine + tail symmetry collapses ∫_{Iio (-a)} = ∫_{Ioi a}.
  rw [h1, h2, quartic_integral_Iio_neg_eq_integral_Ioi]
  ring

/-! ## Headline result -/

/-- **Bounded-prior quartic partition function**: for `t, a > 0`,

  `| ∫_{[-a,a]} exp(-(t·w⁴/24)) dw  −  (1/2)·(24/t)^{1/4}·Γ(1/4) |
      ≤ (24/(t·a³)) · exp(-(t·a⁴/24))`.

The leading term is the exact full-line partition function `quartic_partition`;
the remainder is the doubled half-line tail bounded by `quartic_tail_Ioi`. -/
theorem quartic_partition_bounded_prior {t a : ℝ} (ht : 0 < t) (ha : 0 < a) :
    |(∫ w in Icc (-a) a, Real.exp (-(t * w ^ 4 / 24))) -
        (1/2) * (24/t) ^ ((1 : ℝ) / 4) * Real.Gamma ((1 : ℝ) / 4)| ≤
      (24 / (t * a ^ 3)) * Real.exp (-(t * a ^ 4 / 24)) := by
  -- The full-line integral equals `quartic_partition`'s value.
  have hpart_int : ∫ w : ℝ, Real.exp (-(t * w ^ 4 / 24)) =
      (1/2) * (24/t) ^ ((1 : ℝ) / 4) * Real.Gamma ((1 : ℝ) / 4) := by
    have h := quartic_moment_even 0 ht
    have heq : (fun x : ℝ => x ^ (2 * 0) * Real.exp (-(t * x ^ 4 / 24))) =
               (fun x : ℝ => Real.exp (-(t * x ^ 4 / 24))) := by
      ext x; rw [Nat.mul_zero, pow_zero, one_mul]
    rw [heq] at h
    simp only [Nat.cast_zero, mul_zero, zero_add] at h
    exact h
  -- The split: ∫_ℝ = ∫_{[-a,a]} + 2·∫_{Ioi a}.
  have hsplit := quartic_partition_split ht ha
  -- Therefore ∫_{[-a,a]} - leading = -(2·∫_{Ioi a}).
  have hdiff : (∫ w in Icc (-a) a, Real.exp (-(t * w ^ 4 / 24))) -
        ((1/2) * (24/t) ^ ((1 : ℝ) / 4) * Real.Gamma ((1 : ℝ) / 4)) =
      -(2 * ∫ w in Ioi a, Real.exp (-(t * w ^ 4 / 24))) := by
    rw [← hpart_int, hsplit]; ring
  rw [hdiff, abs_neg]
  -- Tail is nonneg, so |2·∫| = 2·∫.
  have htail_nn : 0 ≤ ∫ w in Ioi a, Real.exp (-(t * w ^ 4 / 24)) :=
    MeasureTheory.setIntegral_nonneg measurableSet_Ioi
      (fun w _ => (Real.exp_pos _).le)
  rw [abs_of_nonneg (by positivity : (0 : ℝ) ≤ 2 * _)]
  -- Combine with quartic_tail_Ioi: 2·∫ ≤ 2·(12/(ta³))·exp(-ta⁴/24) = (24/(ta³))·exp.
  have htail := quartic_tail_Ioi ht ha
  have h2 : 2 * ∫ w in Ioi a, Real.exp (-(t * w ^ 4 / 24)) ≤
      2 * ((12 / (t * a ^ 3)) * Real.exp (-(t * a ^ 4 / 24))) :=
    mul_le_mul_of_nonneg_left htail (by norm_num)
  have heq2 : (2 : ℝ) * ((12 / (t * a ^ 3)) * Real.exp (-(t * a ^ 4 / 24))) =
      (24 / (t * a ^ 3)) * Real.exp (-(t * a ^ 4 / 24)) := by
    have ha_ne : (a : ℝ) ≠ 0 := ne_of_gt ha
    have ht_ne : (t : ℝ) ≠ 0 := ne_of_gt ht
    field_simp
    ring
  linarith

end Laplace.OneD
