import Laplace.OneD.Quartic
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.MeasureTheory.Measure.Haar.NormedSpace

/-!
# J-function asymptotic for the quartic potential

For the quartic potential `K(w) = w^4/24` and a continuous (at 0)
bounded prior `prior : ℝ → ℝ`, the J-function
$$J(t) := \int_{\mathbb R} e^{-t\,K(w)}\,\pi(w)\,dw$$
satisfies
$$\lim_{t \to \infty} t^{1/4} \cdot J(t)
  \;=\; \pi(0) \cdot \tfrac{1}{2} \cdot 24^{1/4} \cdot \Gamma(1/4).$$

This is Step 2 of the grammar paper precursor sequence (single-component
blow-up at one specific potential class). The headline theorem here is
*not* `quartic_jfunction_asymptotic` (the user-facing form) but the
**centered** version `quartic_jfunction_centered_tendsto_zero` — the DCT
core that says the prior-perturbation `prior(w) − prior(0)` is asymptotically
negligible against the concentrating Gibbs weight. The user-facing
`asymptotic` form drops out as a 2-line corollary using the closed-form
`quartic_partition`.

The Step-2 deliberation (Claude ↔ GPT-5.5 Pro) chose the centered form
over the direct form for cleanness: less algebra in the statement (no
explicit Γ-constant in the headline), and "prior perturbation is
negligible" is exactly the structural content the grammar paper uses.

## Strategy

The proof is substitute-then-DCT. With `a := t^{1/4}` (so `a^4 = t`),
the change of variables `u = a · w` turns
$$
  t^{1/4} \int_{\mathbb R} e^{-t\,w^4/24}\,(\pi(w) - \pi(0))\,dw
$$
into
$$
  \int_{\mathbb R} e^{-u^4/24}\,(\pi(u/a) - \pi(0))\,du,
$$
which has a `t`-independent envelope `2M · e^{-u^4/24}` (integrable by
`quartic_integrable_pow 0`) and a pointwise limit `0` (by `ContinuousAt
prior 0` and `(u/a) → 0` as `a → ∞`). The dominated-convergence theorem
closes.

## Tide-step provenance

Tide step (Candidate G1 from the May 7 candidates survey, candidate "X"
after the GPT-reshape from "A"). Branch `tide/grammar-j-function`,
worktree at `sri/lean/laplace-tide-grammar-j-function/`. Tide log at
`sri/projects/primer/tide-log/2026-05-07-tide-grammar-j-function.md`.
-/

open MeasureTheory Filter Topology Real

namespace Laplace.OneD

/-! ## Substitution and dominator integrability -/

/-- The substitution `u = t^{1/4} · w` reshapes
`t^{1/4} · ∫ exp(-(t·w^4)/24) · ψ(w) dw` into the `t`-independent-integrand form
`∫ exp(-(u^4)/24) · ψ(u/t^{1/4}) du` (for `t > 0`). Stated for the centered
prior factor `ψ(w) = prior(w) - prior(0)`. -/
private lemma jfunction_centered_subst (prior : ℝ → ℝ) {t : ℝ} (ht : 0 < t) :
    t ^ ((1:ℝ)/4) * ∫ w : ℝ, Real.exp (-(t * w^4 / 24)) * (prior w - prior 0)
      = ∫ u : ℝ, Real.exp (-(u^4 / 24)) * (prior (u / t^((1:ℝ)/4)) - prior 0) := by
  set a : ℝ := t ^ ((1:ℝ)/4) with ha_def
  have ha_pos : 0 < a := Real.rpow_pos_of_pos ht _
  have ha_ne : a ≠ 0 := ne_of_gt ha_pos
  -- Compute a^4 = t.
  have ha4 : a ^ (4 : ℕ) = t := by
    have hcast : ((4 : ℕ) : ℝ) = 4 := by norm_num
    calc a ^ (4 : ℕ)
        = a ^ ((4 : ℕ) : ℝ) := by rw [Real.rpow_natCast]
      _ = (t ^ ((1:ℝ)/4)) ^ ((4 : ℕ) : ℝ) := by rw [ha_def]
      _ = t ^ (((1:ℝ)/4) * ((4 : ℕ) : ℝ)) := by
            rw [← Real.rpow_mul (le_of_lt ht)]
      _ = t ^ ((1:ℝ)) := by rw [hcast]; norm_num
      _ = t := Real.rpow_one t
  -- Define g(u) := exp(-u^4/24) · (prior(u/a) - prior(0)).
  set g : ℝ → ℝ := fun u => Real.exp (-(u^4 / 24)) * (prior (u / a) - prior 0)
    with hg_def
  -- Pointwise: g(w · a) = exp(-(t·w^4)/24) · (prior(w) - prior(0)).
  have hg_eq : (fun w : ℝ => g (w * a))
      = (fun w : ℝ => Real.exp (-(t * w^4 / 24)) * (prior w - prior 0)) := by
    funext w
    change Real.exp (-((w * a)^4 / 24)) * (prior ((w * a) / a) - prior 0)
        = Real.exp (-(t * w^4 / 24)) * (prior w - prior 0)
    have hwa : (w * a) / a = w := by
      field_simp
    have hpow : (w * a)^4 = t * w^4 := by
      have : (w * a)^4 = w^4 * a^4 := by ring
      rw [this, ha4]; ring
    rw [hwa, hpow]
  -- Apply Measure.integral_comp_mul_right: ∫ w, g(w · a) dw = |a⁻¹| · ∫ y, g(y) dy.
  have h_change : (∫ w : ℝ, g (w * a)) = |a⁻¹| * ∫ y : ℝ, g y := by
    have := MeasureTheory.Measure.integral_comp_mul_right g a
    simpa [smul_eq_mul] using this
  -- |a⁻¹| = 1/a since a > 0.
  have habs : |a⁻¹| = 1 / a := by
    rw [abs_of_pos (inv_pos.mpr ha_pos), inv_eq_one_div]
  -- Combine.
  calc a * ∫ w : ℝ, Real.exp (-(t * w^4 / 24)) * (prior w - prior 0)
      = a * ∫ w : ℝ, g (w * a) := by rw [hg_eq]
    _ = a * (|a⁻¹| * ∫ y : ℝ, g y) := by rw [h_change]
    _ = a * (1/a * ∫ y : ℝ, g y) := by rw [habs]
    _ = ∫ y : ℝ, g y := by field_simp

/-- The dominator `2M · exp(-u^4/24)` is integrable on `ℝ`. -/
private lemma quartic_dominator_integrable (M : ℝ) :
    Integrable (fun u : ℝ => 2 * M * Real.exp (-(u^4 / 24))) := by
  -- `quartic_integrable_pow 0` (with t = 1) gives `Integrable (fun x => x^0 * exp(-(x^4/24)))`.
  have h := quartic_integrable_pow 0 (by norm_num : (0:ℝ) < 1)
  have heq : (fun x : ℝ => x ^ 0 * Real.exp (-(1 * x ^ 4 / 24)))
              = (fun x : ℝ => Real.exp (-(x^4 / 24))) := by
    funext x
    simp
  rw [heq] at h
  exact h.const_mul (2 * M)

/-- **J-function centered DCT theorem (E4 Candidate X).**

For the quartic potential and a continuous-at-zero, globally bounded,
a.e.-measurable prior `prior`, the centered J-function vanishes faster than
`t^{-1/4}`:
$$
  \lim_{t \to \infty} t^{1/4} \cdot \int_{\mathbb R} e^{-t\,w^4/24}\,(\pi(w) - \pi(0))\,dw \;=\; 0.
$$
-/
theorem quartic_jfunction_centered_tendsto_zero
    {prior : ℝ → ℝ} (hprior_cont : Continuous prior)
    {M : ℝ} (hprior_bd : ∀ x, |prior x| ≤ M) :
    Tendsto (fun t : ℝ =>
        t ^ ((1:ℝ)/4) * ∫ w : ℝ, Real.exp (-(t * w^4 / 24)) * (prior w - prior 0))
      atTop (𝓝 0) := by
  -- The substituted-form integrand `F t u := exp(-u^4/24) · (prior(u/t^{1/4}) - prior(0))`.
  set F : ℝ → ℝ → ℝ :=
    fun t u => Real.exp (-(u^4 / 24)) * (prior (u / t^((1:ℝ)/4)) - prior 0) with hF_def
  set bound : ℝ → ℝ := fun u => 2 * M * Real.exp (-(u^4 / 24)) with hbound_def
  -- DCT: `∫ F t u du → 0` as `t → ∞`.
  have h_dct : Tendsto (fun t : ℝ => ∫ u : ℝ, F t u) atTop (𝓝 0) := by
    have h_zero_eq : (0 : ℝ) = ∫ _u : ℝ, (0 : ℝ) := by simp
    rw [h_zero_eq]
    refine MeasureTheory.tendsto_integral_filter_of_dominated_convergence bound
      ?_ ?_ ?_ ?_
    · -- Eventually: AEStronglyMeasurable (F t).
      filter_upwards [Filter.eventually_gt_atTop (0:ℝ)] with t _ht
      have hcomp : Continuous (fun u : ℝ => prior (u / t^((1:ℝ)/4))) :=
        hprior_cont.comp (by fun_prop)
      have h1 : Continuous (fun u : ℝ => Real.exp (-(u^4 / 24))) := by fun_prop
      exact (h1.mul (hcomp.sub continuous_const)).aestronglyMeasurable
    · -- Eventually: ‖F t u‖ ≤ bound u for a.e. u.
      filter_upwards [Filter.eventually_gt_atTop (0:ℝ)] with t _ht
      filter_upwards with u
      have hexp_nn : 0 ≤ Real.exp (-(u^4 / 24)) := le_of_lt (Real.exp_pos _)
      have hbnd : |prior (u / t^((1:ℝ)/4)) - prior 0| ≤ 2 * M := by
        calc |prior (u / t^((1:ℝ)/4)) - prior 0|
            ≤ |prior (u / t^((1:ℝ)/4))| + |prior 0| := abs_sub _ _
          _ ≤ M + M := add_le_add (hprior_bd _) (hprior_bd _)
          _ = 2 * M := by ring
      simp only [hF_def, hbound_def, Real.norm_eq_abs, abs_mul, abs_of_pos (Real.exp_pos _)]
      calc Real.exp (-(u^4 / 24)) * |prior (u / t^((1:ℝ)/4)) - prior 0|
          ≤ Real.exp (-(u^4 / 24)) * (2 * M) := by
                exact mul_le_mul_of_nonneg_left hbnd hexp_nn
        _ = 2 * M * Real.exp (-(u^4 / 24)) := by ring
    · -- Bound is integrable.
      exact quartic_dominator_integrable M
    · -- For a.e. u, F t u → 0 as t → ∞.
      filter_upwards with u
      have h_div_zero : Tendsto (fun t : ℝ => u / t^((1:ℝ)/4)) atTop (𝓝 0) := by
        have h_inf : Tendsto (fun t : ℝ => t^((1:ℝ)/4)) atTop atTop :=
          tendsto_rpow_atTop (by norm_num : (0:ℝ) < (1:ℝ)/4)
        exact (tendsto_const_nhds (x := u)).div_atTop h_inf
      have h_prior_lim : Tendsto (fun t : ℝ => prior (u / t^((1:ℝ)/4))) atTop (𝓝 (prior 0)) :=
        (hprior_cont.tendsto 0).comp h_div_zero
      have h_diff_lim : Tendsto (fun t : ℝ => prior (u / t^((1:ℝ)/4)) - prior 0)
          atTop (𝓝 0) := by
        have : Tendsto (fun t : ℝ => prior (u / t^((1:ℝ)/4)) - prior 0)
            atTop (𝓝 (prior 0 - prior 0)) := h_prior_lim.sub_const _
        simpa using this
      simp only [hF_def]
      have := h_diff_lim.const_mul (Real.exp (-(u^4 / 24)))
      simpa using this
  -- Connect LHS to the substituted form for `t > 0`.
  refine Tendsto.congr' ?_ h_dct
  filter_upwards [Filter.eventually_gt_atTop (0:ℝ)] with t ht
  exact (jfunction_centered_subst prior ht).symm

/-- **J-function asymptotic (E4 Candidate A, as a corollary of X).**

For the quartic potential `K(w) = w^4/24` and a continuous-at-zero,
globally bounded prior `prior`, the J-function `J(t) := ∫ e^{-tK(w)} prior(w) dw`
has the leading-order asymptotic
$$
  t^{1/4} \cdot J(t) \;\longrightarrow\; \pi(0) \cdot \tfrac{1}{2} \cdot 24^{1/4} \cdot \Gamma(1/4)
$$
as `t → ∞`. -/
theorem quartic_jfunction_asymptotic
    {prior : ℝ → ℝ} (hprior_cont : Continuous prior)
    {M : ℝ} (hprior_bd : ∀ x, |prior x| ≤ M) :
    Tendsto (fun t : ℝ =>
        t ^ ((1:ℝ)/4) * ∫ w : ℝ, Real.exp (-(t * w^4 / 24)) * prior w)
      atTop (𝓝 (prior 0 * (1/2) * (24:ℝ) ^ ((1:ℝ)/4) * Real.Gamma (1/4))) := by
  set C : ℝ := prior 0 * (1/2) * (24:ℝ) ^ ((1:ℝ)/4) * Real.Gamma (1/4) with hC_def
  -- LHS = (centered piece) + C eventually (for `t > 0`).
  have h_decomp : ∀ᶠ t in atTop,
      t ^ ((1:ℝ)/4) * ∫ w : ℝ, Real.exp (-(t * w^4 / 24)) * prior w
      = (t ^ ((1:ℝ)/4) * ∫ w : ℝ, Real.exp (-(t * w^4 / 24)) * (prior w - prior 0)) + C := by
    filter_upwards [Filter.eventually_gt_atTop (0:ℝ)] with t ht
    -- Integrability of both pieces.
    have h_exp_int : Integrable (fun w : ℝ => Real.exp (-(t * w^4 / 24))) := by
      have := quartic_integrable_pow 0 ht
      simpa using this
    have h_int_centered :
        Integrable (fun w : ℝ => Real.exp (-(t * w^4 / 24)) * (prior w - prior 0)) := by
      have h_meas : AEStronglyMeasurable
          (fun w : ℝ => Real.exp (-(t * w^4 / 24)) * (prior w - prior 0)) volume := by
        have h1 : Continuous (fun w : ℝ => Real.exp (-(t * w^4 / 24))) := by fun_prop
        exact (h1.mul (hprior_cont.sub continuous_const)).aestronglyMeasurable
      have h_bd : ∀ w, ‖Real.exp (-(t * w^4 / 24)) * (prior w - prior 0)‖ ≤
                       Real.exp (-(t * w^4 / 24)) * (2 * M) := by
        intro w
        rw [Real.norm_eq_abs, abs_mul, abs_of_pos (Real.exp_pos _)]
        apply mul_le_mul_of_nonneg_left _ (le_of_lt (Real.exp_pos _))
        calc |prior w - prior 0|
            ≤ |prior w| + |prior 0| := abs_sub _ _
          _ ≤ M + M := add_le_add (hprior_bd _) (hprior_bd _)
          _ = 2 * M := by ring
      exact (h_exp_int.mul_const (2 * M)).mono' h_meas (Filter.Eventually.of_forall h_bd)
    have h_int_const : Integrable (fun w : ℝ => Real.exp (-(t * w^4 / 24)) * prior 0) :=
      h_exp_int.mul_const (prior 0)
    -- Split the integral via integral_add.
    have h_split :
        (∫ w : ℝ, Real.exp (-(t * w^4 / 24)) * prior w)
        = (∫ w : ℝ, Real.exp (-(t * w^4 / 24)) * (prior w - prior 0))
          + (∫ w : ℝ, Real.exp (-(t * w^4 / 24)) * prior 0) := by
      have heq : (fun w : ℝ => Real.exp (-(t * w^4 / 24)) * prior w)
        = (fun w : ℝ => Real.exp (-(t * w^4 / 24)) * (prior w - prior 0)
            + Real.exp (-(t * w^4 / 24)) * prior 0) := by
        funext w; ring
      rw [heq]
      exact MeasureTheory.integral_add h_int_centered h_int_const
    -- Closed form for the constant piece via quartic_partition.
    have h_part : (∫ w : ℝ, Real.exp (-(t * w^4 / 24)))
        = (1/2) * (24/t)^((1:ℝ)/4) * Real.Gamma (1/4) := by
      have hp := quartic_partition ht
      unfold partitionFunction at hp
      have hint_eq : (fun x : ℝ => Real.exp (-(t * quarticPotential x)))
          = (fun x : ℝ => Real.exp (-(t * x^4 / 24))) := by
        funext x
        rw [quarticPotential_apply]
        congr 1; ring
      rw [hint_eq] at hp
      exact hp
    have h_const_int : (∫ w : ℝ, Real.exp (-(t * w^4 / 24)) * prior 0)
        = prior 0 * ((1/2) * (24/t)^((1:ℝ)/4) * Real.Gamma (1/4)) := by
      rw [MeasureTheory.integral_mul_const, h_part]
      ring
    -- t^(1/4) · (24/t)^(1/4) = 24^(1/4).
    have hcanc : t^((1:ℝ)/4) * (24/t)^((1:ℝ)/4) = (24:ℝ)^((1:ℝ)/4) := by
      rw [← Real.mul_rpow (le_of_lt ht) (by positivity : (0:ℝ) ≤ 24/t)]
      congr 1; field_simp
    -- Combine.
    rw [h_split, mul_add, h_const_int]
    -- Goal: ... + t^(1/4) * (prior 0 * ((1/2) * (24/t)^(1/4) * Γ(1/4))) = ... + C
    congr 1
    calc t^((1:ℝ)/4) * (prior 0 * ((1/2) * (24/t)^((1:ℝ)/4) * Real.Gamma (1/4)))
        = prior 0 * (1/2) * (t^((1:ℝ)/4) * (24/t)^((1:ℝ)/4)) * Real.Gamma (1/4) := by ring
      _ = prior 0 * (1/2) * (24:ℝ)^((1:ℝ)/4) * Real.Gamma (1/4) := by rw [hcanc]
      _ = C := by rw [hC_def]
  -- Centered piece tends to 0; constant piece is constant; sum tends to C.
  have h_centered := quartic_jfunction_centered_tendsto_zero hprior_cont hprior_bd
  have h_sum_C : Tendsto (fun t : ℝ =>
        (t ^ ((1:ℝ)/4) * ∫ w : ℝ, Real.exp (-(t * w^4 / 24)) * (prior w - prior 0)) + C)
      atTop (𝓝 C) := by
    have := h_centered.add (tendsto_const_nhds (x := C))
    simpa using this
  exact Tendsto.congr' (h_decomp.mono fun _ h => h.symm) h_sum_C

end Laplace.OneD
