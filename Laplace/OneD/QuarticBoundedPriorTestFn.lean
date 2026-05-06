import Laplace.OneD.QuarticBoundedPrior
import Mathlib.Analysis.Asymptotics.Defs

/-!
# Bounded-prior expectation against a continuous test function (in progress)

Working towards the leading-order asymptotic
\[
  \int_{-a}^{a} \varphi(w)\,e^{-t w^4/24}\,dw
    \;\sim\; \varphi(0) \cdot Z_a(t)
  \quad (t \to \infty)
\]
for `φ ∈ ContinuousOn (Icc (-a) a)`, where `Z_a(t)` is the bounded-prior
partition function from `Laplace.OneD.QuarticBoundedPrior`. The headline
deliverable is the `Asymptotics.IsLittleO`-packaged form
`(t ↦ ∫ φ·e - φ(0)·Z) =o[atTop] (t ↦ Z)`.

## Status

This file currently provides the two foundational primitives needed for the
bounded-prior localisation argument:

- `quartic_bounded_prior_partition_pos`: `Z_a(t) > 0` for `0 < a, t : ℝ`.
- `quartic_bounded_prior_partition_lower_bound_inner`: `Z_a(t) ≥ 2δ ·
  exp(-(t·δ⁴/24))` for `0 < δ ≤ a, 0 ≤ t` (by restriction to the inner
  shell `[-δ, δ]` and a uniform integrand bound).

The remaining helpers and the headline theorem are sketched in the handoff
note `notes/bounded_prior_test_fn_handoff.md` and will land in a follow-up
session. Both primitives proven here are immediately useful as building
blocks for that follow-up.

## Tide-step provenance

Tide step 11 (Candidate B1 from the 6 May candidates survey),
`tide/bounded-prior-test-function` branch, off laplace `main` at
commit `1e3802a`. Tide log:
`sri/projects/grammar/tide-log/2026-05-06-tide-bounded-prior-test-function.md`.
-/

open MeasureTheory Filter Topology Set

namespace Laplace.OneD

/-! ## Positivity of the bounded-prior partition -/

/-- The bounded-prior partition function `Z_a(t) = ∫_{[-a,a]} exp(-(t·w⁴/24))`
is strictly positive whenever `0 < a` (and any `t : ℝ`). The integrand is
strictly positive everywhere. -/
theorem quartic_bounded_prior_partition_pos {a t : ℝ} (ha : 0 < a) :
    0 < ∫ w in Icc (-a) a, Real.exp (-(t * w ^ 4 / 24)) := by
  have h_int : IntegrableOn (fun w : ℝ => Real.exp (-(t * w ^ 4 / 24)))
      (Icc (-a) a) volume :=
    ContinuousOn.integrableOn_compact isCompact_Icc (by fun_prop)
  have h_nonneg : 0 ≤ᵐ[volume.restrict (Icc (-a) a)]
      (fun w : ℝ => Real.exp (-(t * w ^ 4 / 24))) :=
    Filter.Eventually.of_forall (fun w => (Real.exp_pos _).le)
  rw [setIntegral_pos_iff_support_of_nonneg_ae h_nonneg h_int]
  -- Goal: 0 < volume (support (fun w => exp ...) ∩ Icc (-a) a).
  have h_supp : Function.support (fun w : ℝ => Real.exp (-(t * w ^ 4 / 24)))
      = Set.univ := by
    ext w
    simp [Function.mem_support, (Real.exp_pos _).ne']
  rw [h_supp, Set.univ_inter, Real.volume_Icc]
  exact ENNReal.ofReal_pos.mpr (by linarith)

/-! ## Inner-shell lower bound -/

/-- Lower bound on the bounded-prior partition by restricting to the inner
shell `[-δ, δ]`: for `0 < δ ≤ a` and `0 ≤ t`,
`Z_a(t) ≥ 2δ · exp(-(t·δ⁴/24))`.

Holds because the integrand `exp(-(t·w⁴/24))` is uniformly bounded below by
`exp(-(t·δ⁴/24))` on `[-δ, δ]` (since `w⁴ ≤ δ⁴` and `t ≥ 0`), and the
inner shell has length `2δ`. -/
theorem quartic_bounded_prior_partition_lower_bound_inner
    {a δ t : ℝ} (hδ : 0 < δ) (hδa : δ ≤ a) (ht : 0 ≤ t) :
    2 * δ * Real.exp (-(t * δ ^ 4 / 24)) ≤
      ∫ w in Icc (-a) a, Real.exp (-(t * w ^ 4 / 24)) := by
  -- Step 1: Reduce by subset monotonicity to the inner integral over [-δ, δ].
  have h_subset : Icc (-δ) δ ⊆ Icc (-a) a := by
    intro w hw
    refine ⟨?_, ?_⟩
    · linarith [hw.1]
    · linarith [hw.2]
  have h_int_full : IntegrableOn (fun w : ℝ => Real.exp (-(t * w ^ 4 / 24)))
      (Icc (-a) a) volume :=
    ContinuousOn.integrableOn_compact isCompact_Icc (by fun_prop)
  have h_int_inner : IntegrableOn (fun w : ℝ => Real.exp (-(t * w ^ 4 / 24)))
      (Icc (-δ) δ) volume :=
    ContinuousOn.integrableOn_compact isCompact_Icc (by fun_prop)
  have h_inner_le : ∫ w in Icc (-δ) δ, Real.exp (-(t * w ^ 4 / 24)) ≤
      ∫ w in Icc (-a) a, Real.exp (-(t * w ^ 4 / 24)) := by
    apply setIntegral_mono_set h_int_full
      (Filter.Eventually.of_forall (fun w => (Real.exp_pos _).le))
    exact Filter.Eventually.of_forall h_subset
  -- Step 2: On [-δ, δ], exp(-(t·w⁴/24)) ≥ exp(-(t·δ⁴/24)) since w⁴ ≤ δ⁴ and t ≥ 0.
  have h_pointwise : ∀ w ∈ Icc (-δ) δ,
      Real.exp (-(t * δ ^ 4 / 24)) ≤ Real.exp (-(t * w ^ 4 / 24)) := by
    intro w hw
    apply Real.exp_le_exp.mpr
    have habs : |w| ≤ δ := abs_le.mpr ⟨hw.1, hw.2⟩
    have hw4 : w ^ 4 ≤ δ ^ 4 := by
      have h_abs_pow : |w| ^ 4 ≤ δ ^ 4 := pow_le_pow_left₀ (abs_nonneg w) habs 4
      have h_abs_eq : |w| ^ 4 = w ^ 4 := by
        rw [show (4 : ℕ) = 2 * 2 from rfl, pow_mul, sq_abs, ← pow_mul]
      linarith
    nlinarith [hw4, ht, sq_nonneg w, sq_nonneg δ]
  -- Step 3: Use setIntegral_mono_on with the pointwise lower bound.
  have h_lower :
      ∫ w in Icc (-δ) δ, Real.exp (-(t * δ ^ 4 / 24)) ≤
      ∫ w in Icc (-δ) δ, Real.exp (-(t * w ^ 4 / 24)) := by
    apply setIntegral_mono_on
    · exact integrableOn_const (by
        rw [Real.volume_Icc]; exact ENNReal.ofReal_ne_top)
    · exact h_int_inner
    · exact measurableSet_Icc
    · exact h_pointwise
  -- Step 4: setIntegral_const gives ∫_{[-δ,δ]} c = (2δ) · c.
  have h_const : ∫ w in Icc (-δ) δ, Real.exp (-(t * δ ^ 4 / 24)) =
      2 * δ * Real.exp (-(t * δ ^ 4 / 24)) := by
    rw [setIntegral_const, Real.volume_real_Icc]
    have h2δ : max (δ - (-δ)) 0 = 2 * δ := by
      rw [max_eq_left (by linarith : (0 : ℝ) ≤ δ - (-δ))]
      ring
    rw [h2δ, smul_eq_mul]
  linarith [h_const ▸ h_lower, h_inner_le]

end Laplace.OneD
