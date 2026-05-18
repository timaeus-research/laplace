import Laplace.Gibbs
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
import Mathlib.MeasureTheory.Integral.Gamma
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.MeasureTheory.Measure.Lebesgue.Integral
import Mathlib.MeasureTheory.Measure.Haar.NormedSpace

/-!
# Generic-`k` J-function asymptotic for monomial potentials

For the single-monomial potential `K(w) = w^(2k)/(2k)!` with `k ≥ 1`
and a continuous, globally bounded prior `prior : ℝ → ℝ`, the
J-function
$$J_k(t) := \int_{\mathbb R} e^{-t\,K(w)}\,\pi(w)\,dw$$
satisfies
$$\lim_{t \to \infty} t^{1/(2k)} \cdot J_k(t)
  \;=\; \pi(0) \cdot \tfrac{1}{k} \cdot ((2k)!)^{1/(2k)} \cdot \Gamma(1/(2k)).$$

This file folds the `k = 2` (`JFunctionQuartic.lean`, E4) and `k = 3`
(`JFunctionSextic.lean`, L1) special cases into a single parametric
theorem.

## Headline results

* `kth_partition` — closed-form partition for the monomial potential:
  $\int e^{-t\,w^{2k}/(2k)!}\,dw = \tfrac{1}{k}\cdot ((2k)!/t)^{1/(2k)}\cdot \Gamma(1/(2k))$.
* `kth_jfunction_centered_tendsto_zero` — the centred DCT theorem.
* `kth_jfunction_asymptotic` — the user-facing asymptotic.

## Strategy

The proof is substitute-then-DCT, identical in structure to the `k = 2`
and `k = 3` cases. With `a := t^(1/(2k))` (so `a^(2k) = t`), the
change of variables `u = a · w` reshapes the centred J-function into a
`t`-independent-integrand form, after which the dominated convergence
theorem closes via the envelope `2M · exp(-u^(2k)/(2k)!)`.

The Mathlib master theorem `integral_rpow_mul_exp_neg_mul_rpow` is
used twice: once to evaluate the half-line partition integral (full
line via `integral_comp_abs`), and indirectly via Gaussian comparison
for full-line integrability. The Gaussian comparison uses
$x^2 \le 1 + x^{2k}$ for $k \ge 1$, which holds via case-split on
$|x| \le 1$ vs $|x| \ge 1$.
-/

open MeasureTheory Filter Topology Real Set

namespace Laplace.OneD

/-! ## Universal pointwise inequality `x^2 ≤ 1 + x^(2k)` -/

/-- For `k ≥ 1` and any real `x`, `x^2 ≤ 1 + x^(2k)`.
Trivial for `k = 1`; for `k ≥ 2`, case-split on `|x| ≤ 1` (where `x^2 ≤ 1`)
vs `|x| ≥ 1` (where `x^(2k) ≥ x^2`). -/
private lemma sq_le_one_add_pow_two_mul {k : ℕ} (hk : 1 ≤ k) (x : ℝ) :
    x ^ 2 ≤ 1 + x ^ (2 * k) := by
  have hxsq : (0 : ℝ) ≤ x ^ 2 := sq_nonneg x
  have hpow_eq : x ^ (2 * k) = (x ^ 2) ^ k := by rw [pow_mul]
  rw [hpow_eq]
  set y : ℝ := x ^ 2 with hy_def
  -- Goal: y ≤ 1 + y^k, given 0 ≤ y, 1 ≤ k.
  rcases le_or_gt y 1 with h | h
  · -- y ≤ 1: y^k ≥ 0, so 1 + y^k ≥ 1 ≥ y.
    have hyk : (0 : ℝ) ≤ y ^ k := pow_nonneg hxsq k
    linarith
  · -- y > 1: y^k ≥ y, so 1 + y^k ≥ 1 + y ≥ y.
    have hyk : y ≤ y ^ k := by
      calc y = y ^ 1 := (pow_one y).symm
        _ ≤ y ^ k := pow_le_pow_right₀ (le_of_lt h) hk
    linarith

/-! ## Integrability for the monomial Gibbs weight -/

/-- For `k ≥ 1` and `t > 0`, `exp(-t·x^(2k)/(2k)!)` is Lebesgue integrable on `ℝ`.

Gaussian comparison via `x^2 ≤ 1 + x^(2k)`, which gives
`t·x^(2k)/(2k)! ≥ (t/(2k)!)·x^2 - t/(2k)!`, hence
`exp(-t·x^(2k)/(2k)!) ≤ exp(t/(2k)!) · exp(-(t/(2k)!)·x^2)`. The dominator
is integrable by Mathlib's `integrable_exp_neg_mul_sq` with `b = t/(2k)!`. -/
private theorem kth_integrable {k : ℕ} (hk : 1 ≤ k) {t : ℝ} (ht : 0 < t) :
    Integrable
      (fun x : ℝ => Real.exp (-(t * x ^ (2 * k) / (Nat.factorial (2 * k) : ℝ)))) := by
  set fac : ℝ := (Nat.factorial (2 * k) : ℝ) with hfac_def
  have hfac_pos : 0 < fac := by
    change (0 : ℝ) < (Nat.factorial (2 * k) : ℝ)
    exact_mod_cast Nat.factorial_pos _
  have ht_fac : (0 : ℝ) < t / fac := div_pos ht hfac_pos
  have hmeas : AEStronglyMeasurable
      (fun x : ℝ => Real.exp (-(t * x ^ (2 * k) / fac))) volume :=
    (by fun_prop : Continuous _).aestronglyMeasurable
  -- Dominator: exp(t/fac) · exp(-(t/fac · x²)) is integrable.
  have hdom : Integrable
      (fun x : ℝ => Real.exp (t / fac) * Real.exp (-(t / fac * x ^ 2))) volume := by
    have hg : Integrable (fun x : ℝ => Real.exp (-(t / fac * x ^ 2))) volume := by
      have h0 := integrable_exp_neg_mul_sq ht_fac
      -- h0 : Integrable (fun x ↦ rexp (-(t/fac) * x^2)). Massage parenthesization.
      have heq : (fun x : ℝ => Real.exp (-(t / fac) * x ^ 2))
                = (fun x : ℝ => Real.exp (-(t / fac * x ^ 2))) := by
        funext x; congr 1; ring
      rw [heq] at h0
      exact h0
    exact hg.const_mul (Real.exp (t / fac))
  -- Pointwise bound: exp(-t·x^(2k)/fac) ≤ exp(t/fac) · exp(-(t/fac · x²)).
  have hbound : ∀ x : ℝ,
      Real.exp (-(t * x ^ (2 * k) / fac)) ≤
        Real.exp (t / fac) * Real.exp (-(t / fac * x ^ 2)) := by
    intro x
    rw [← Real.exp_add]
    apply Real.exp_le_exp.mpr
    have hkey : x ^ 2 ≤ 1 + x ^ (2 * k) := sq_le_one_add_pow_two_mul hk x
    -- Want: -(t·x^(2k)/fac) ≤ t/fac + (-(t/fac · x²))
    -- Equivalently: (t/fac) · x² - t/fac ≤ t·x^(2k)/fac
    -- i.e., (t/fac) · (x² - 1) ≤ t · x^(2k) / fac  (using fac > 0).
    have h_xpow_nn : (0 : ℝ) ≤ x ^ (2 * k) - x ^ 2 + 1 := by linarith [hkey]
    have h_div : t / fac * (x ^ (2 * k) - x ^ 2 + 1) =
                 t * x ^ (2 * k) / fac - t / fac * x ^ 2 + t / fac := by
      field_simp
    have h_prod_nn : (0 : ℝ) ≤ t / fac * (x ^ (2 * k) - x ^ 2 + 1) :=
      mul_nonneg ht_fac.le h_xpow_nn
    linarith [h_div ▸ h_prod_nn]
  -- Apply mono.
  have habs : ∀ x : ℝ,
      ‖Real.exp (-(t * x ^ (2 * k) / fac))‖ ≤
        ‖Real.exp (t / fac) * Real.exp (-(t / fac * x ^ 2))‖ := by
    intro x
    rw [Real.norm_eq_abs, Real.norm_eq_abs,
        abs_of_pos (Real.exp_pos _),
        abs_of_pos (mul_pos (Real.exp_pos _) (Real.exp_pos _))]
    exact hbound x
  exact hdom.mono hmeas (Filter.Eventually.of_forall habs)

/-! ## Substitution and dominator integrability -/

/-- Substitution `u = t^(1/(2k)) · w` reshapes
`t^(1/(2k)) · ∫ exp(-(t · w^(2k))/(2k)!) · ψ(w) dw`
into the `t`-independent-integrand form
`∫ exp(-(u^(2k))/(2k)!) · ψ(u/t^(1/(2k))) du` (for `t > 0`),
stated for the centred prior factor `ψ(w) = prior(w) - prior(0)`. -/
private lemma kth_jfunction_centered_subst {k : ℕ} (hk : 1 ≤ k)
    (prior : ℝ → ℝ) {t : ℝ} (ht : 0 < t) :
    t ^ ((1 : ℝ) / ((2 * k : ℕ) : ℝ)) *
      ∫ w : ℝ, Real.exp (-(t * w ^ (2 * k) / (Nat.factorial (2 * k) : ℝ)))
                  * (prior w - prior 0)
      = ∫ u : ℝ, Real.exp (-(u ^ (2 * k) / (Nat.factorial (2 * k) : ℝ)))
                    * (prior (u / t ^ ((1 : ℝ) / ((2 * k : ℕ) : ℝ))) - prior 0) := by
  set p : ℕ := 2 * k with hp_def
  have hp_pos : 0 < p := by
    have : 0 < 2 * k := by omega
    exact this
  set pR : ℝ := (p : ℝ) with hpR_def
  have hpR_pos : (0 : ℝ) < pR := by
    change (0 : ℝ) < (p : ℝ)
    exact_mod_cast hp_pos
  have hpR_ne : pR ≠ 0 := ne_of_gt hpR_pos
  set α : ℝ := 1 / pR with hα_def
  set a : ℝ := t ^ α with ha_def
  have ha_pos : 0 < a := Real.rpow_pos_of_pos ht _
  have ha_ne : a ≠ 0 := ne_of_gt ha_pos
  set fac : ℝ := (Nat.factorial p : ℝ) with hfac_def
  have hfac_pos : 0 < fac := by
    change (0 : ℝ) < (Nat.factorial p : ℝ)
    exact_mod_cast Nat.factorial_pos _
  -- α * p = 1 (used twice: in ha_p and elsewhere).
  have hα_p : α * (p : ℝ) = 1 := by
    rw [hα_def, hpR_def]
    field_simp
  -- Compute a^p = t.
  have ha_p : a ^ p = t := by
    calc a ^ p
        = a ^ (p : ℝ) := by rw [Real.rpow_natCast]
      _ = (t ^ α) ^ (p : ℝ) := by rw [ha_def]
      _ = t ^ (α * (p : ℝ)) := by rw [← Real.rpow_mul (le_of_lt ht)]
      _ = t ^ (1 : ℝ) := by rw [hα_p]
      _ = t := Real.rpow_one t
  -- Define g(u) := exp(-u^p/fac) · (prior(u/a) - prior(0)).
  set g : ℝ → ℝ := fun u => Real.exp (-(u ^ p / fac)) * (prior (u / a) - prior 0)
    with hg_def
  -- Pointwise: g(w · a) = exp(-(t·w^p)/fac) · (prior(w) - prior(0)).
  have hg_eq : (fun w : ℝ => g (w * a))
      = (fun w : ℝ => Real.exp (-(t * w ^ p / fac)) * (prior w - prior 0)) := by
    funext w
    change Real.exp (-((w * a) ^ p / fac)) * (prior ((w * a) / a) - prior 0)
        = Real.exp (-(t * w ^ p / fac)) * (prior w - prior 0)
    have hwa : (w * a) / a = w := by field_simp
    -- Crucial: use mul_pow for (w·a)^p = w^p · a^p (NOT ring; generic p won't unify).
    have hpow : (w * a) ^ p = t * w ^ p := by
      rw [mul_pow, ha_p]
      ring
    rw [hwa, hpow]
  -- Apply Measure.integral_comp_mul_right: ∫ w, g(w · a) dw = |a⁻¹| · ∫ y, g(y) dy.
  have h_change : (∫ w : ℝ, g (w * a)) = |a⁻¹| * ∫ y : ℝ, g y := by
    have := MeasureTheory.Measure.integral_comp_mul_right g a
    simpa [smul_eq_mul] using this
  have habs : |a⁻¹| = 1 / a := by
    rw [abs_of_pos (inv_pos.mpr ha_pos), inv_eq_one_div]
  -- Combine.
  -- LHS goal uses `t ^ (1 / ((2 * k : ℕ) : ℝ))` which is exactly `a` after unfolding.
  change a * ∫ w : ℝ, Real.exp (-(t * w ^ p / fac)) * (prior w - prior 0)
      = ∫ y : ℝ, Real.exp (-(y ^ p / fac)) * (prior (y / a) - prior 0)
  calc a * ∫ w : ℝ, Real.exp (-(t * w ^ p / fac)) * (prior w - prior 0)
      = a * ∫ w : ℝ, g (w * a) := by rw [hg_eq]
    _ = a * (|a⁻¹| * ∫ y : ℝ, g y) := by rw [h_change]
    _ = a * (1 / a * ∫ y : ℝ, g y) := by rw [habs]
    _ = ∫ y : ℝ, g y := by field_simp

/-- The dominator `2M · exp(-u^(2k)/(2k)!)` is integrable on `ℝ`. -/
private lemma kth_dominator_integrable {k : ℕ} (hk : 1 ≤ k) (M : ℝ) :
    Integrable
      (fun u : ℝ => 2 * M * Real.exp (-(u ^ (2 * k) / (Nat.factorial (2 * k) : ℝ)))) := by
  -- `kth_integrable` at `t = 1` gives `Integrable (fun x => exp(-(1·x^(2k)/(2k)!)))`.
  have h := kth_integrable hk (by norm_num : (0 : ℝ) < 1)
  have heq : (fun x : ℝ => Real.exp (-(1 * x ^ (2 * k) / (Nat.factorial (2 * k) : ℝ))))
              = (fun x : ℝ => Real.exp (-(x ^ (2 * k) / (Nat.factorial (2 * k) : ℝ)))) := by
    funext x
    congr 1
    ring
  rw [heq] at h
  exact h.const_mul (2 * M)

/-! ## Centred DCT theorem -/

/-- **J-function centred DCT theorem (generic `k`).**

For the single-monomial potential `K(w) = w^(2k)/(2k)!` with `k ≥ 1`
and a globally bounded prior `prior` that is `AEMeasurable` and
continuous at `0`, the centred J-function vanishes faster than
`t^(-1/(2k))`:
$$
  \lim_{t \to \infty} t^{1/(2k)} \cdot \int_{\mathbb R}
    e^{-t\,w^{2k}/(2k)!}\,(\pi(w) - \pi(0))\,dw \;=\; 0.
$$

The hypothesis class is the mathematically-minimal one identified at
the original E4 deliberation: AE measurability handles integrability
and dominated convergence's strong-measurability requirement; pointwise
continuity at `0` handles the DCT's pointwise limit; the global bound
underwrites the dominator. -/
theorem kth_jfunction_centered_tendsto_zero
    {k : ℕ} (hk : 1 ≤ k)
    {prior : ℝ → ℝ}
    (hprior_meas : AEMeasurable prior volume)
    (hprior_cont0 : ContinuousAt prior 0)
    {M : ℝ} (hprior_bd : ∀ x, |prior x| ≤ M) :
    Tendsto (fun t : ℝ =>
        t ^ ((1 : ℝ) / ((2 * k : ℕ) : ℝ)) *
        ∫ w : ℝ, Real.exp (-(t * w ^ (2 * k) / (Nat.factorial (2 * k) : ℝ)))
                  * (prior w - prior 0))
      atTop (𝓝 0) := by
  set p : ℕ := 2 * k with hp_def
  set fac : ℝ := (Nat.factorial p : ℝ) with hfac_def
  set α : ℝ := 1 / ((p : ℕ) : ℝ) with hα_def
  -- The substituted-form integrand `F t u := exp(-u^p/fac) · (prior(u/t^α) - prior(0))`.
  set F : ℝ → ℝ → ℝ :=
    fun t u => Real.exp (-(u ^ p / fac)) * (prior (u / t ^ α) - prior 0) with hF_def
  set bound : ℝ → ℝ := fun u => 2 * M * Real.exp (-(u ^ p / fac)) with hbound_def
  have hα_pos : 0 < α := by
    have hp_pos : 0 < p := by change 0 < 2 * k; omega
    have hpR_pos : (0 : ℝ) < ((p : ℕ) : ℝ) := by exact_mod_cast hp_pos
    exact div_pos (by norm_num) hpR_pos
  -- DCT: `∫ F t u du → 0` as `t → ∞`.
  have h_dct : Tendsto (fun t : ℝ => ∫ u : ℝ, F t u) atTop (𝓝 0) := by
    have h_zero_eq : (0 : ℝ) = ∫ _u : ℝ, (0 : ℝ) := by simp
    rw [h_zero_eq]
    refine MeasureTheory.tendsto_integral_filter_of_dominated_convergence bound
      ?_ ?_ ?_ ?_
    · -- Eventually: AEStronglyMeasurable (F t).
      filter_upwards [Filter.eventually_gt_atTop (0 : ℝ)] with t ht
      -- AE measurability of u ↦ prior(u / t^α) via comp_quasiMeasurePreserving:
      -- u / t^α = (t^α)⁻¹ • u, scaling by a nonzero constant on volume.
      have htα_pos : 0 < t ^ α := Real.rpow_pos_of_pos ht α
      have htα_inv_ne : (t ^ α : ℝ)⁻¹ ≠ 0 := inv_ne_zero htα_pos.ne'
      -- The scaling map u ↦ (t^α)⁻¹ • u is quasi-MP on volume.
      have h_qmp : MeasureTheory.Measure.QuasiMeasurePreserving
          (fun u : ℝ => (t ^ α)⁻¹ • u) (volume : Measure ℝ) volume :=
        MeasureTheory.Measure.quasiMeasurePreserving_smul (volume : Measure ℝ) htα_inv_ne
      -- Reshape u / t^α = (t^α)⁻¹ • u.
      have hreshape : (fun u : ℝ => prior (u / t ^ α)) =
          prior ∘ (fun u : ℝ => (t ^ α)⁻¹ • u) := by
        funext u
        show prior (u / t ^ α) = prior ((t ^ α)⁻¹ * u)
        congr 1
        rw [div_eq_mul_inv, mul_comm]
      have h_aem : AEMeasurable (fun u : ℝ => prior (u / t ^ α)) volume := by
        rw [hreshape]
        exact hprior_meas.comp_quasiMeasurePreserving h_qmp
      have h_aesm_prior : AEStronglyMeasurable
          (fun u : ℝ => prior (u / t ^ α)) volume :=
        h_aem.aestronglyMeasurable
      have h1 : Continuous (fun u : ℝ => Real.exp (-(u ^ p / fac))) := by fun_prop
      exact (h1.aestronglyMeasurable.mul
        (h_aesm_prior.sub aestronglyMeasurable_const))
    · -- Eventually: ‖F t u‖ ≤ bound u for a.e. u.
      filter_upwards [Filter.eventually_gt_atTop (0 : ℝ)] with t _ht
      filter_upwards with u
      have hexp_nn : 0 ≤ Real.exp (-(u ^ p / fac)) := le_of_lt (Real.exp_pos _)
      have hbnd : |prior (u / t ^ α) - prior 0| ≤ 2 * M := by
        calc |prior (u / t ^ α) - prior 0|
            ≤ |prior (u / t ^ α)| + |prior 0| := abs_sub _ _
          _ ≤ M + M := add_le_add (hprior_bd _) (hprior_bd _)
          _ = 2 * M := by ring
      simp only [hF_def, hbound_def, Real.norm_eq_abs, abs_mul,
        abs_of_pos (Real.exp_pos _)]
      calc Real.exp (-(u ^ p / fac)) * |prior (u / t ^ α) - prior 0|
          ≤ Real.exp (-(u ^ p / fac)) * (2 * M) := by
                exact mul_le_mul_of_nonneg_left hbnd hexp_nn
        _ = 2 * M * Real.exp (-(u ^ p / fac)) := by ring
    · -- Bound is integrable.
      exact kth_dominator_integrable hk M
    · -- For a.e. u, F t u → 0 as t → ∞.
      filter_upwards with u
      have h_div_zero : Tendsto (fun t : ℝ => u / t ^ α) atTop (𝓝 0) := by
        have h_inf : Tendsto (fun t : ℝ => t ^ α) atTop atTop :=
          tendsto_rpow_atTop hα_pos
        exact (tendsto_const_nhds (x := u)).div_atTop h_inf
      have h_prior_lim : Tendsto (fun t : ℝ => prior (u / t ^ α)) atTop (𝓝 (prior 0)) :=
        hprior_cont0.tendsto.comp h_div_zero
      have h_diff_lim : Tendsto (fun t : ℝ => prior (u / t ^ α) - prior 0)
          atTop (𝓝 0) := by
        have : Tendsto (fun t : ℝ => prior (u / t ^ α) - prior 0)
            atTop (𝓝 (prior 0 - prior 0)) := h_prior_lim.sub_const _
        simpa using this
      simp only [hF_def]
      have := h_diff_lim.const_mul (Real.exp (-(u ^ p / fac)))
      simpa using this
  -- Connect LHS to the substituted form for `t > 0`.
  refine Tendsto.congr' ?_ h_dct
  filter_upwards [Filter.eventually_gt_atTop (0 : ℝ)] with t ht
  exact (kth_jfunction_centered_subst hk prior ht).symm

/-! ## Closed-form partition function -/

/-- **Closed-form partition function for the monomial potential.**

For the potential `K(w) = w^(2k)/(2k)!` with `k ≥ 1` and `t > 0`,
$$
  \int_{\mathbb R} e^{-t\,w^{2k}/(2k)!}\,dw
  \;=\; \tfrac{1}{k}\cdot ((2k)!/t)^{1/(2k)}\cdot \Gamma(1/(2k)).
$$ -/
theorem kth_partition {k : ℕ} (hk : 1 ≤ k) {t : ℝ} (ht : 0 < t) :
    ∫ x : ℝ, Real.exp (-(t * x ^ (2 * k) / (Nat.factorial (2 * k) : ℝ))) =
      (1 / (k : ℝ))
        * ((Nat.factorial (2 * k) : ℝ) / t) ^ ((1 : ℝ) / ((2 * k : ℕ) : ℝ))
        * Real.Gamma ((1 : ℝ) / ((2 * k : ℕ) : ℝ)) := by
  set p : ℕ := 2 * k with hp_def
  have hp_pos : 0 < p := by change 0 < 2 * k; omega
  set pR : ℝ := (p : ℝ) with hpR_def
  have hpR_pos : (0 : ℝ) < pR := by
    change (0 : ℝ) < (p : ℝ)
    exact_mod_cast hp_pos
  have hpR_ne : pR ≠ 0 := ne_of_gt hpR_pos
  set fac : ℝ := (Nat.factorial p : ℝ) with hfac_def
  have hfac_pos : (0 : ℝ) < fac := by
    change (0 : ℝ) < (Nat.factorial p : ℝ)
    exact_mod_cast Nat.factorial_pos _
  have hfac_ne : fac ≠ 0 := ne_of_gt hfac_pos
  have ht_fac : (0 : ℝ) < t / fac := div_pos ht hfac_pos
  -- Step 1: write integrand as `f(|x|)` and apply `integral_comp_abs` to get 2 × half-line.
  have heven : (fun x : ℝ => Real.exp (-(t * x ^ p / fac)))
                = (fun x : ℝ => Real.exp (-(t * |x| ^ p / fac))) := by
    funext x
    have hpow_abs : |x| ^ p = x ^ p := by
      rw [show p = 2 * k from rfl, pow_mul, pow_mul, sq_abs]
    rw [hpow_abs]
  rw [heven]
  rw [integral_comp_abs (f := fun y => Real.exp (-(t * y ^ p / fac)))]
  -- Step 2: the half-line integral via `integral_rpow_mul_exp_neg_mul_rpow` at q = 0.
  have hq : (-1 : ℝ) < (0 : ℝ) := by norm_num
  have key := integral_rpow_mul_exp_neg_mul_rpow
    (p := pR) (q := (0 : ℝ)) (b := t / fac)
    hpR_pos hq ht_fac
  -- key : ∫ x in Ioi 0, x^0 * exp(-(t/fac) * x^pR) = (t/fac)^(-(0+1)/pR) * (1/pR) * Γ((0+1)/pR)
  -- Massage half-line integrand to the rpow form.
  have hhalf : (∫ x in Ioi (0 : ℝ), Real.exp (-(t * x ^ p / fac))) =
      ∫ x in Ioi (0 : ℝ), x ^ (0 : ℝ) * Real.exp (-(t / fac) * x ^ pR) := by
    refine setIntegral_congr_fun measurableSet_Ioi (fun x hx => ?_)
    rw [mem_Ioi] at hx
    have hxnn : (0 : ℝ) ≤ x := le_of_lt hx
    have hxR : x ^ pR = x ^ p := by
      rw [hpR_def, Real.rpow_natCast]
    rw [hxR, Real.rpow_zero, one_mul]
    congr 1
    field_simp
  rw [hhalf, key]
  -- key gives: (t/fac)^(-(0+1)/pR) * (1/pR) * Γ((0+1)/pR)
  -- Simplify exponent (0+1)/pR = 1/pR (also covers the negated form -(0+1)/pR = -(1/pR)).
  have hexp_pos : ((0 : ℝ) + 1) / pR = 1 / pR := by ring
  have hexp_neg : -((0 : ℝ) + 1) / pR = -(1 / pR) := by ring
  rw [hexp_pos, hexp_neg]
  -- Convert (t/fac)^(-(1/pR)) to (fac/t)^(1/pR).
  have hinv : (t / fac : ℝ) ^ (-(1 / pR)) = (fac / t : ℝ) ^ (1 / pR) := by
    rw [show (fac / t : ℝ) = (t / fac)⁻¹ by field_simp]
    rw [inv_rpow ht_fac.le, ← Real.rpow_neg ht_fac.le]
  -- Goal at this point:
  --   2 * ((t/fac)^(-(1/pR)) * (1/pR) * Γ(1/pR))
  --   = (1/k) * (fac/t)^(1/pR) * Γ(1/pR)
  rw [hinv]
  -- Show 2 * (1/pR) = 1/k. Since pR = (2*k:ℕ:ℝ) = 2*k (as real), 2/pR = 2/(2k) = 1/k.
  have hk_pos : (0 : ℝ) < k := by exact_mod_cast (Nat.lt_of_lt_of_le (by norm_num : 0 < 1) hk)
  have hk_ne : (k : ℝ) ≠ 0 := ne_of_gt hk_pos
  have h_two_over_pR : (2 : ℝ) / pR = 1 / (k : ℝ) := by
    rw [hpR_def, hp_def]
    push_cast
    field_simp
  -- Final algebraic massage.
  rw [show ((1 : ℝ) / ((2 * k : ℕ) : ℝ)) = 1 / pR from by rw [hpR_def, hp_def]]
  -- Now goal: 2 * ((fac/t)^(1/pR) * (1/pR) * Γ(1/pR))
  --        = (1/k) * (fac/t)^(1/pR) * Γ(1/pR)
  have : (2 : ℝ) * ((fac / t) ^ (1 / pR) * (1 / pR) * Real.Gamma (1 / pR))
       = (2 / pR) * ((fac / t) ^ (1 / pR) * Real.Gamma (1 / pR)) := by ring
  rw [this, h_two_over_pR]
  ring

/-! ## Asymptotic corollary -/

/-- **J-function asymptotic (generic `k`).**

For the single-monomial potential `K(w) = w^(2k)/(2k)!` with `k ≥ 1`
and a continuous, globally bounded prior `prior`, the J-function
$J_k(t) := \int e^{-t\,K(w)}\,\pi(w)\,dw$ has the leading-order
asymptotic
$$
  t^{1/(2k)} \cdot J_k(t) \;\longrightarrow\;
  \pi(0) \cdot \tfrac{1}{k} \cdot ((2k)!)^{1/(2k)} \cdot \Gamma(1/(2k))
$$
as `t → ∞`. -/
theorem kth_jfunction_asymptotic
    {k : ℕ} (hk : 1 ≤ k)
    {prior : ℝ → ℝ}
    (hprior_meas : AEMeasurable prior volume)
    (hprior_cont0 : ContinuousAt prior 0)
    {M : ℝ} (hprior_bd : ∀ x, |prior x| ≤ M) :
    Tendsto (fun t : ℝ =>
        t ^ ((1 : ℝ) / ((2 * k : ℕ) : ℝ)) *
        ∫ w : ℝ, Real.exp (-(t * w ^ (2 * k) / (Nat.factorial (2 * k) : ℝ)))
                  * prior w)
      atTop
      (𝓝 (prior 0 * (1 / (k : ℝ))
            * ((Nat.factorial (2 * k) : ℝ)) ^ ((1 : ℝ) / ((2 * k : ℕ) : ℝ))
            * Real.Gamma ((1 : ℝ) / ((2 * k : ℕ) : ℝ)))) := by
  set p : ℕ := 2 * k with hp_def
  set fac : ℝ := (Nat.factorial p : ℝ) with hfac_def
  have hfac_pos : 0 < fac := by
    change (0 : ℝ) < (Nat.factorial p : ℝ)
    exact_mod_cast Nat.factorial_pos _
  set α : ℝ := 1 / ((p : ℕ) : ℝ) with hα_def
  set C : ℝ := prior 0 * (1 / (k : ℝ)) * fac ^ α * Real.Gamma α with hC_def
  -- LHS = (centered piece) + C eventually (for `t > 0`).
  have h_decomp : ∀ᶠ t in atTop,
      t ^ α * ∫ w : ℝ, Real.exp (-(t * w ^ p / fac)) * prior w
      = (t ^ α * ∫ w : ℝ, Real.exp (-(t * w ^ p / fac)) * (prior w - prior 0)) + C := by
    filter_upwards [Filter.eventually_gt_atTop (0 : ℝ)] with t ht
    -- Integrability of both pieces.
    have h_exp_int : Integrable (fun w : ℝ => Real.exp (-(t * w ^ p / fac))) :=
      kth_integrable hk ht
    have h_int_centered :
        Integrable (fun w : ℝ => Real.exp (-(t * w ^ p / fac)) * (prior w - prior 0)) := by
      have h_meas : AEStronglyMeasurable
          (fun w : ℝ => Real.exp (-(t * w ^ p / fac)) * (prior w - prior 0)) volume := by
        have h1 : Continuous (fun w : ℝ => Real.exp (-(t * w ^ p / fac))) := by fun_prop
        exact h1.aestronglyMeasurable.mul
          (hprior_meas.aestronglyMeasurable.sub aestronglyMeasurable_const)
      have h_bd : ∀ w, ‖Real.exp (-(t * w ^ p / fac)) * (prior w - prior 0)‖ ≤
                       Real.exp (-(t * w ^ p / fac)) * (2 * M) := by
        intro w
        rw [Real.norm_eq_abs, abs_mul, abs_of_pos (Real.exp_pos _)]
        apply mul_le_mul_of_nonneg_left _ (le_of_lt (Real.exp_pos _))
        calc |prior w - prior 0|
            ≤ |prior w| + |prior 0| := abs_sub _ _
          _ ≤ M + M := add_le_add (hprior_bd _) (hprior_bd _)
          _ = 2 * M := by ring
      exact (h_exp_int.mul_const (2 * M)).mono' h_meas (Filter.Eventually.of_forall h_bd)
    have h_int_const : Integrable (fun w : ℝ => Real.exp (-(t * w ^ p / fac)) * prior 0) :=
      h_exp_int.mul_const (prior 0)
    -- Split the integral via integral_add.
    have h_split :
        (∫ w : ℝ, Real.exp (-(t * w ^ p / fac)) * prior w)
        = (∫ w : ℝ, Real.exp (-(t * w ^ p / fac)) * (prior w - prior 0))
          + (∫ w : ℝ, Real.exp (-(t * w ^ p / fac)) * prior 0) := by
      have heq : (fun w : ℝ => Real.exp (-(t * w ^ p / fac)) * prior w)
        = (fun w : ℝ => Real.exp (-(t * w ^ p / fac)) * (prior w - prior 0)
            + Real.exp (-(t * w ^ p / fac)) * prior 0) := by
        funext w; ring
      rw [heq]
      exact MeasureTheory.integral_add h_int_centered h_int_const
    -- Closed form for the constant piece via kth_partition.
    have h_part : (∫ w : ℝ, Real.exp (-(t * w ^ p / fac)))
        = (1 / (k : ℝ)) * (fac / t) ^ α * Real.Gamma α := by
      have hpart := kth_partition hk ht
      -- hpart uses `(1 : ℝ) / ((2 * k : ℕ) : ℝ)` which equals α.
      have : ((1 : ℝ) / ((2 * k : ℕ) : ℝ)) = α := by rw [hα_def, hp_def]
      rw [this] at hpart
      -- hpart goal-side uses `(Nat.factorial (2 * k) : ℝ)` which is fac.
      have : ((Nat.factorial (2 * k) : ℝ)) = fac := by rw [hfac_def, hp_def]
      rw [this] at hpart
      exact hpart
    have h_const_int : (∫ w : ℝ, Real.exp (-(t * w ^ p / fac)) * prior 0)
        = prior 0 * ((1 / (k : ℝ)) * (fac / t) ^ α * Real.Gamma α) := by
      rw [MeasureTheory.integral_mul_const, h_part]
      ring
    -- t^α · (fac/t)^α = fac^α.
    have hcanc : t ^ α * (fac / t) ^ α = fac ^ α := by
      rw [← Real.mul_rpow (le_of_lt ht) (by positivity : (0 : ℝ) ≤ fac / t)]
      congr 1
      field_simp
    -- Combine.
    rw [h_split, mul_add, h_const_int]
    congr 1
    calc t ^ α * (prior 0 * ((1 / (k : ℝ)) * (fac / t) ^ α * Real.Gamma α))
        = prior 0 * (1 / (k : ℝ)) * (t ^ α * (fac / t) ^ α) * Real.Gamma α := by ring
      _ = prior 0 * (1 / (k : ℝ)) * fac ^ α * Real.Gamma α := by rw [hcanc]
      _ = C := by rw [hC_def]
  -- Centered piece tends to 0; constant piece is constant; sum tends to C.
  -- Since `p := 2 * k`, `α := 1 / ((p : ℕ) : ℝ)`, `fac := (Nat.factorial p : ℝ)`
  -- via `set`, the centred piece's statement under these abbreviations is
  -- definitionally equal to `kth_jfunction_centered_tendsto_zero`'s public form.
  have h_centered : Tendsto (fun t : ℝ =>
        t ^ α * ∫ w : ℝ, Real.exp (-(t * w ^ p / fac)) * (prior w - prior 0))
      atTop (𝓝 0) :=
    kth_jfunction_centered_tendsto_zero hk hprior_meas hprior_cont0 hprior_bd
  have h_sum_C : Tendsto (fun t : ℝ =>
        (t ^ α * ∫ w : ℝ, Real.exp (-(t * w ^ p / fac)) * (prior w - prior 0)) + C)
      atTop (𝓝 C) := by
    have := h_centered.add (tendsto_const_nhds (x := C))
    simpa using this
  -- The goal's public form is definitionally equal to the abbreviated form.
  exact Tendsto.congr' (h_decomp.mono fun _ h => h.symm) h_sum_C

end Laplace.OneD
