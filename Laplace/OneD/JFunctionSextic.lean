import Laplace.OneD.JFunctionMonomial

/-!
# J-function asymptotic for the sextic potential (specialisation of N1)

For the sextic potential `K(w) = w^6/720` and a globally bounded prior
`prior : ℝ → ℝ` that is `AEMeasurable` and `ContinuousAt 0`, the
J-function
$$J(t) := \int_{\mathbb R} e^{-t\,K(w)}\,\pi(w)\,dw$$
satisfies
$$\lim_{t \to \infty} t^{1/6} \cdot J(t)
  \;=\; \pi(0) \cdot \tfrac{1}{3} \cdot 720^{1/6} \cdot \Gamma(1/6).$$

## Refactor history (L3, 2026-05-07)

This file originally (L1, 2026-05-07) carried independent proofs of
its two theorems with hypothesis `Continuous prior`. The L1 retrospective
itself flagged this as a follow-up: *"the two existing files become
5-line specialisations [of the parametric form]"*. Once N1 (generic-`k`
J-function abstraction) landed and the parametric form was weakened
in this tide (L3, hypothesis weakening), both sextic theorems became
thin specialisations of `kth_*` at `k = 3`, inheriting the
mathematically-minimal hypothesis class
`AEMeasurable + ContinuousAt 0 + global bound`.

The constant bridging is mechanical: `2 * 3 = 6` (definitional in ℕ),
`Nat.factorial 6 = 720` (`decide`/`norm_num`), and
`(1 : ℝ) / ((6 : ℕ) : ℝ) = 1/6` (`norm_num`). The `1/3` partition
prefactor in the asymptotic limit reflects `1/k` at `k = 3`.

## Tide-step provenance

L1 (sextic-j-function), 2026-05-07. Refactored in L3
(jfunction-hypothesis-weakening), 2026-05-07. See
`sri/projects/primer/tide-log/2026-05-07-tide-jfunction-hypothesis-weakening.md`.
-/

open MeasureTheory Filter Topology Real

namespace Laplace.OneD

/-! ## Constant-bridging lemmas -/

private lemma sextic_kth_eq_const_six : (2 * 3 : ℕ) = 6 := rfl

private lemma sextic_kth_factorial : (Nat.factorial (2 * 3) : ℝ) = 720 := by
  show (Nat.factorial 6 : ℝ) = 720
  norm_num [Nat.factorial]

private lemma sextic_kth_inv : ((1 : ℝ) / ((2 * 3 : ℕ) : ℝ)) = (1 : ℝ) / 6 := by
  norm_num

/-! ## The two sextic theorems as specialisations of `kth_*` -/

/-- **J-function centered DCT theorem (sextic).**

5-line specialisation of `kth_jfunction_centered_tendsto_zero` at `k = 3`. -/
theorem sextic_jfunction_centered_tendsto_zero
    {prior : ℝ → ℝ}
    (hprior_meas : AEMeasurable prior volume)
    (hprior_cont0 : ContinuousAt prior 0)
    {M : ℝ} (hprior_bd : ∀ x, |prior x| ≤ M) :
    Tendsto (fun t : ℝ =>
        t ^ ((1:ℝ)/6) * ∫ w : ℝ, Real.exp (-(t * w^6 / 720)) * (prior w - prior 0))
      atTop (𝓝 0) := by
  have h := kth_jfunction_centered_tendsto_zero
    (k := 3) (by norm_num) hprior_meas hprior_cont0 hprior_bd
  -- Bridge constants: 1/((2*3:ℕ):ℝ) = 1/6 and (Nat.factorial (2*3):ℝ) = 720.
  rw [sextic_kth_inv] at h
  -- After the inv rewrite the only remaining gap is the factorial; rewrite under
  -- the integrand via `simp_rw`.
  simp_rw [sextic_kth_factorial] at h
  exact h

/-- **J-function asymptotic (sextic).**

5-line specialisation of `kth_jfunction_asymptotic` at `k = 3`. The
limit value `π(0) · (1/3) · 720^(1/6) · Γ(1/6)` is the parametric
`π(0) · (1/k) · ((2k)!)^(1/(2k)) · Γ(1/(2k))` at `k = 3`. -/
theorem sextic_jfunction_asymptotic
    {prior : ℝ → ℝ}
    (hprior_meas : AEMeasurable prior volume)
    (hprior_cont0 : ContinuousAt prior 0)
    {M : ℝ} (hprior_bd : ∀ x, |prior x| ≤ M) :
    Tendsto (fun t : ℝ =>
        t ^ ((1:ℝ)/6) * ∫ w : ℝ, Real.exp (-(t * w^6 / 720)) * prior w)
      atTop (𝓝 (prior 0 * (1/3) * (720:ℝ) ^ ((1:ℝ)/6) * Real.Gamma (1/6))) := by
  have h := kth_jfunction_asymptotic
    (k := 3) (by norm_num) hprior_meas hprior_cont0 hprior_bd
  -- Bridge constants: 1/((2*3:ℕ):ℝ) = 1/6, ((3:ℕ):ℝ) = 3, (Nat.factorial (2*3):ℝ) = 720.
  rw [sextic_kth_inv] at h
  rw [show ((3 : ℕ) : ℝ) = (3 : ℝ) from by norm_num] at h
  simp_rw [sextic_kth_factorial] at h
  exact h

end Laplace.OneD
