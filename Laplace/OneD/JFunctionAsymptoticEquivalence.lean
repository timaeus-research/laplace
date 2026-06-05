import Laplace.OneD.JFunctionMonomial
import Mathlib.Analysis.Asymptotics.AsymptoticEquivalent

/-!
# J-function asymptotic-equivalence wrapper

For the single-monomial potential `K(w) = w^(2k)/(2k)!` with `k ≥ 1`,
the J-function and its matching partition function satisfy the
asymptotic-equivalence form
$$
  J_k(t) \;\sim\; \pi(0) \cdot Z_k(t) \qquad (t \to \infty)
$$
in the sense that the ratio `J_k(t) / Z_k(t) → π(0)` as `t → ∞`. This
wraps the asymptotics established in `JFunctionMonomial.lean` into the
user-facing statement form actually used in the grammar paper.

Two public theorems:

* `kth_jfunction_div_partition` — the unconditional form: the ratio
  converges to `prior 0` regardless of whether `prior 0` is zero.
  This is the building block.

* `kth_jfunction_isEquivalent` — the asymptotic-equivalence form
  `J_k ~[atTop] (fun t => prior 0 · Z_k(t))`, valid when
  `prior 0 ≠ 0`. Direct corollary of the ratio form via
  `Asymptotics.isEquivalent_iff_tendsto_one`.
-/

open MeasureTheory Filter Asymptotics
open scoped Topology

namespace Laplace.OneD

/-- **J-function ratio convergence (generic `k`).**

For the single-monomial potential `K(w) = w^(2k)/(2k)!` with `k ≥ 1`
and a continuous, globally bounded prior `prior`, the ratio of the
J-function to the matching partition function converges to `prior 0`:
$$
  \lim_{t \to \infty}
    \frac{\int e^{-t\,w^{2k}/(2k)!}\,\pi(w)\,dw}
         {\int e^{-t\,w^{2k}/(2k)!}\,dw}
  \;=\; \pi(0).
$$
Holds unconditionally — when `prior 0 = 0`, the ratio still converges to
zero because the centred J-function vanishes faster than the partition. -/
theorem kth_jfunction_div_partition
    {k : ℕ} (hk : 1 ≤ k)
    {prior : ℝ → ℝ} (hprior_cont : Continuous prior)
    {M : ℝ} (hprior_bd : ∀ x, |prior x| ≤ M) :
    Tendsto (fun t : ℝ =>
        (∫ w : ℝ, Real.exp (-(t * w ^ (2 * k) / (Nat.factorial (2 * k) : ℝ))) * prior w) /
        (∫ w : ℝ, Real.exp (-(t * w ^ (2 * k) / (Nat.factorial (2 * k) : ℝ)))))
      atTop (𝓝 (prior 0)) := by
  set α : ℝ := (1 : ℝ) / ((2 * k : ℕ) : ℝ) with hα_def
  set CONST : ℝ :=
    (1 / (k : ℝ)) * ((Nat.factorial (2 * k) : ℝ)) ^ α * Real.Gamma α with hCONST_def
  -- Positivity of the closed-form constant.
  have hk_pos : 0 < (k : ℝ) := by
    exact_mod_cast (Nat.lt_of_lt_of_le (by norm_num : 0 < 1) hk)
  have h2k_pos : 0 < ((2 * k : ℕ) : ℝ) := by
    have : (0 : ℕ) < 2 * k := by omega
    exact_mod_cast this
  have hα_pos : 0 < α := by
    rw [hα_def]; exact div_pos one_pos h2k_pos
  have hfac_pos : (0 : ℝ) < (Nat.factorial (2 * k) : ℝ) := by
    exact_mod_cast Nat.factorial_pos _
  have hfac_rpow_pos : 0 < ((Nat.factorial (2 * k) : ℝ)) ^ α :=
    Real.rpow_pos_of_pos hfac_pos α
  have hΓ_pos : 0 < Real.Gamma α := Real.Gamma_pos_of_pos hα_pos
  have hCONST_pos : 0 < CONST := by
    rw [hCONST_def]; positivity
  have hCONST_ne : CONST ≠ 0 := ne_of_gt hCONST_pos
  -- N1's J_k asymptotic, in the form  t^α · J_k(t) → prior 0 · CONST.
  have hJ : Tendsto (fun t : ℝ =>
      t ^ α *
      ∫ w : ℝ, Real.exp (-(t * w ^ (2 * k) / (Nat.factorial (2 * k) : ℝ))) * prior w)
      atTop (𝓝 (prior 0 * CONST)) := by
    have h := kth_jfunction_asymptotic hk hprior_cont.aemeasurable
      hprior_cont.continuousAt hprior_bd
    -- The N1 limit reads `prior 0 * (1/k) * (2k)!^α * Γ(α)`, which is `prior 0 * CONST`.
    have heq : prior 0 * (1 / (k : ℝ))
                * ((Nat.factorial (2 * k) : ℝ)) ^ ((1 : ℝ) / ((2 * k : ℕ) : ℝ))
                * Real.Gamma ((1 : ℝ) / ((2 * k : ℕ) : ℝ))
              = prior 0 * CONST := by
      rw [hCONST_def, hα_def]; ring
    rw [← heq]
    exact h
  -- Z_k(t) closed form, in the form  t^α · Z_k(t) = CONST  (for t > 0).
  have hZ : ∀ t : ℝ, 0 < t →
      t ^ α *
      (∫ w : ℝ, Real.exp (-(t * w ^ (2 * k) / (Nat.factorial (2 * k) : ℝ))))
      = CONST := by
    intro t ht
    rw [kth_partition hk ht]
    -- After the rewrite, the goal is purely algebraic:
    --   t^α * ((1/k) * ((2k)!/t)^α * Γ(α)) = (1/k) * (2k)!^α * Γ(α).
    rw [hCONST_def, hα_def]
    have htnn : (0 : ℝ) ≤ t := le_of_lt ht
    have hfacnn : (0 : ℝ) ≤ (Nat.factorial (2 * k) : ℝ) := le_of_lt hfac_pos
    rw [Real.div_rpow hfacnn htnn]
    -- Goal:  t^α * ((1/k) * ((2k)!^α / t^α) * Γ(α)) = (1/k) * (2k)!^α * Γ(α)
    have ht_rpow_ne : t ^ α ≠ 0 := ne_of_gt (Real.rpow_pos_of_pos ht α)
    field_simp
  -- Eventually-on-{t > 0}: J_k(t) / Z_k(t) = (t^α · J_k(t)) / CONST.
  have heq_ratio : ∀ᶠ t : ℝ in atTop,
      (∫ w : ℝ, Real.exp (-(t * w ^ (2 * k) / (Nat.factorial (2 * k) : ℝ))) * prior w) /
        (∫ w : ℝ, Real.exp (-(t * w ^ (2 * k) / (Nat.factorial (2 * k) : ℝ))))
      = (t ^ α *
          ∫ w : ℝ, Real.exp (-(t * w ^ (2 * k) / (Nat.factorial (2 * k) : ℝ))) * prior w) /
        CONST := by
    filter_upwards [Filter.eventually_gt_atTop (0 : ℝ)] with t ht
    have hZt := hZ t ht
    -- Z_k(t) = CONST / t^α (rearranging hZt; t^α > 0 so divide).
    have ht_rpow_pos : 0 < t ^ α := Real.rpow_pos_of_pos ht α
    have ht_rpow_ne : t ^ α ≠ 0 := ne_of_gt ht_rpow_pos
    have hZt_eq : (∫ w : ℝ, Real.exp (-(t * w ^ (2 * k) / (Nat.factorial (2 * k) : ℝ))))
                  = CONST / t ^ α := by
      rw [eq_div_iff ht_rpow_ne, mul_comm]
      exact hZt
    rw [hZt_eq]
    field_simp
  -- The right-hand side of `heq_ratio` tends to (prior 0 · CONST) / CONST = prior 0.
  have hRHS : Tendsto (fun t : ℝ =>
      (t ^ α *
        ∫ w : ℝ, Real.exp (-(t * w ^ (2 * k) / (Nat.factorial (2 * k) : ℝ))) * prior w) /
      CONST) atTop (𝓝 (prior 0)) := by
    have := hJ.div_const CONST
    -- this : Tendsto (fun t => (t^α · J_k(t)) / CONST) atTop (𝓝 ((prior 0 · CONST) / CONST))
    have hsimp : prior 0 * CONST / CONST = prior 0 := by
      field_simp
    rw [hsimp] at this
    exact this
  exact (Tendsto.congr' (heq_ratio.mono fun _ h => h.symm) hRHS)

/-- **J-function asymptotic-equivalence (generic `k`).**

For the single-monomial potential `K(w) = w^(2k)/(2k)!` with `k ≥ 1`
and a continuous, globally bounded prior `prior` with `prior 0 ≠ 0`,
the J-function is asymptotically equivalent to `prior 0` times the
matching partition:
$$
  J_k(t) \;\sim\; \pi(0) \cdot Z_k(t) \qquad (t \to \infty).
$$
This is the user-facing statement form used in the grammar paper. -/
theorem kth_jfunction_isEquivalent
    {k : ℕ} (hk : 1 ≤ k)
    {prior : ℝ → ℝ} (hprior_cont : Continuous prior)
    {M : ℝ} (hprior_bd : ∀ x, |prior x| ≤ M)
    (hprior0 : prior 0 ≠ 0) :
    (fun t : ℝ =>
        ∫ w : ℝ, Real.exp (-(t * w ^ (2 * k) / (Nat.factorial (2 * k) : ℝ))) * prior w)
      ~[atTop]
    (fun t : ℝ => prior 0 *
        ∫ w : ℝ, Real.exp (-(t * w ^ (2 * k) / (Nat.factorial (2 * k) : ℝ)))) := by
  -- Reduce to the ratio form via `isEquivalent_iff_tendsto_one`.
  -- The denominator `prior 0 · Z_k(t)` is non-zero eventually because
  -- `Z_k(t) > 0` for all `t > 0` (positive integrand) and `prior 0 ≠ 0`.
  have hZ_pos : ∀ᶠ t : ℝ in atTop,
      (0 : ℝ) <
      ∫ w : ℝ, Real.exp (-(t * w ^ (2 * k) / (Nat.factorial (2 * k) : ℝ))) := by
    -- For any t, the integrand is positive and integrable, so the integral is positive.
    -- We only need eventually; trivial for all t since `exp > 0` and integrability is global
    -- (modulo t > 0, which is needed for integrability of the Gaussian envelope).
    filter_upwards [Filter.eventually_gt_atTop (0 : ℝ)] with t ht
    -- Use `kth_partition` to evaluate Z_k(t) explicitly; the closed form is positive.
    rw [kth_partition hk ht]
    have hk_pos : 0 < (k : ℝ) := by
      exact_mod_cast (Nat.lt_of_lt_of_le (by norm_num : 0 < 1) hk)
    have h2k_pos : 0 < ((2 * k : ℕ) : ℝ) := by
      have : (0 : ℕ) < 2 * k := by omega
      exact_mod_cast this
    have hα_pos : 0 < (1 : ℝ) / ((2 * k : ℕ) : ℝ) := div_pos one_pos h2k_pos
    have hfac_pos : (0 : ℝ) < (Nat.factorial (2 * k) : ℝ) := by
      exact_mod_cast Nat.factorial_pos _
    have hfac_div_t_pos : (0 : ℝ) < (Nat.factorial (2 * k) : ℝ) / t := div_pos hfac_pos ht
    have h_rpow_pos : (0 : ℝ) <
        ((Nat.factorial (2 * k) : ℝ) / t) ^ ((1 : ℝ) / ((2 * k : ℕ) : ℝ)) :=
      Real.rpow_pos_of_pos hfac_div_t_pos _
    have hΓ_pos : 0 < Real.Gamma ((1 : ℝ) / ((2 * k : ℕ) : ℝ)) :=
      Real.Gamma_pos_of_pos hα_pos
    positivity
  have hDenom_ne : ∀ᶠ t : ℝ in atTop,
      prior 0 *
      (∫ w : ℝ, Real.exp (-(t * w ^ (2 * k) / (Nat.factorial (2 * k) : ℝ)))) ≠ 0 := by
    filter_upwards [hZ_pos] with t hZt
    exact mul_ne_zero hprior0 (ne_of_gt hZt)
  rw [isEquivalent_iff_tendsto_one hDenom_ne]
  -- Goal: Tendsto (J_k / (prior 0 · Z_k)) atTop (𝓝 1).
  -- From `kth_jfunction_div_partition`: J_k / Z_k → prior 0.
  -- So (J_k / Z_k) / prior 0 → 1, i.e., J_k / (prior 0 · Z_k) → 1.
  have h_ratio := kth_jfunction_div_partition hk hprior_cont hprior_bd
  have h_div := h_ratio.div_const (prior 0)
  -- h_div : Tendsto ((J_k / Z_k) / prior 0) atTop (𝓝 (prior 0 / prior 0))
  have hsimp : prior 0 / prior 0 = 1 := div_self hprior0
  rw [hsimp] at h_div
  -- Massage `(J_k / Z_k) / prior 0 = J_k / (prior 0 · Z_k)` eventually.
  apply Tendsto.congr' _ h_div
  filter_upwards [hZ_pos] with t hZt
  -- Goal: (J_k(t) / Z_k(t)) / prior 0 = (J_k / (prior 0 · Z_k)) t   (Pi.div form)
  simp only [Pi.div_apply]
  field_simp

end Laplace.OneD
