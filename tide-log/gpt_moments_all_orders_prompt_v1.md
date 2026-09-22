# Tide `moments-all-orders` (seabed: laplace, off main) — candidates v1

Context. The Sanity-on-Sampling note's E2 compares four Laplace predictions with exact quadrature for the anharmonic oscillator
`ℓ(x) = λx²/2 + αx³/6 + γx⁴/24` (`λ, γ > 0`, `α² < 3λγ`); the fourth, `Cov[K, ψ]` (eq:covK, "the primer's canonical experiment"), needs the
asymptotics of moments up to degree six (`Cov[ℓ, x²]` involves `⟨x⁶⟩`, `Cov[ℓ, x]` involves `⟨x⁵⟩`). The seabed has `t⟨x⟩ → −α/(2λ²)`,
`t⟨x²⟩ → 1/λ`, `t²⟨x³⟩ → −5α/(2λ³)`, `t²⟨x⁴⟩ → 3/λ²` (each proved separately through the rescaled integrals) but nothing for `n ≥ 5`. The
missing piece is the Laplace scaling of *all* moments, `(λt)^{n/2}⟨xⁿ⟩ → E[gⁿ]` (standard Gaussian moments: `(n−1)‼` for even `n`, `0` for
odd `n`).

Seabed (Lean 4 / Mathlib, all proved). `J_n lam alpha gamma n t = ∫ u, uⁿ e^{−u²/2} e^{−r(t,u)}` with the rescaled perturbation
`r(t,u) = A u³/√t + B u⁴/t`, `A = α/(6λ√λ)`, `B = γ/(24λ²)`; `I_n_J_n_relation : √(λt)^{n+1} · ∫ xⁿ e^{−tℓ} = J_n` (`t > 0`);
`integrable_J_n` (for every `n`, `t > 0`), proved from `rescaled_boltzmann_decay : ∃ c₀ > 0, … e^{−u²/2} e^{−r(t,u)} ≤ e^{−c₀u²}` (a
`t`-uniform Gaussian domination from the discriminant condition); `tendsto_J_0`, `tendsto_J_2` (both `→ √(2π)`, via explicit `K/t` rate bounds
`J_0_asymptotic`, `J_2_asymptotic`); Gaussian moments `integral_pow_mul_exp_neg_sq_half (k) : ∫ x^{2k} e^{−x²/2} = (2k−1)‼ √(2π)`,
`integral_pow_mul_exp_neg_sq_odd (k) : ∫ x^{2k+1} e^{−x²/2} = 0`, `gaussian_moment_normalized`; Mathlib's
`tendsto_integral_filter_of_dominated_convergence`.

Candidates.

A. **`tendsto_J_n`**: for every `n`, `J_n(t) → ∫ uⁿ e^{−u²/2}` as `t → ∞`, by dominated convergence: pointwise `r(t,u) → 0` (so
   `e^{−r} → 1`), and the uniform bound `|uⁿ e^{−u²/2} e^{−r(t,u)}| ≤ |u|ⁿ e^{−c₀u²}` from `rescaled_boltzmann_decay` (integrable). No rate.
B. **All moments scale** (`moment_anharmonic_asymptotic`): `√(λt)^n ⟨xⁿ⟩_t → (∫ uⁿ e^{−u²/2})/√(2π)`, from `J_n/J_0` via `I_n_J_n_relation`
   (`√(λt)^n · I_n/I_0 = J_n/J_0`) and `tendsto_J_0`; even/odd forms `t^k ⟨x^{2k}⟩ → (2k−1)‼/λ^k` and `√(λt)^{2k+1}⟨x^{2k+1}⟩ → 0`
   (`evenMoment_anharmonic_asymptotic`, `oddMoment_anharmonic_tendsto_zero`).
C. **The bounds covK will need** (`sixthMoment_t_sq_tendsto_zero : t²⟨x⁶⟩ → 0`, `fifthMoment_t_sq_tendsto_zero : t²⟨x⁵⟩ → 0`,
   `sixthMoment_asymptotic : t³⟨x⁶⟩ → 15/λ³`), and eventual boundedness `∃ C T, ∀ t ≥ T, |√(λt)^n ⟨xⁿ⟩| ≤ C`.

Numerical check done (`numcheck47.py`, `λ = 2`, `a = ½`): `t^{n/2}⟨xⁿ⟩ → 0.5, 0.75, 1.875, 6.5625` for `n = 2, 4, 6, 8` (= `(n−1)‼/λ^{n/2}`) to
three digits at `t = 1000`; odd moments `t^{(n+1)/2}⟨xⁿ⟩` converge (`−0.1768`, `−0.4419`, `−1.546` for `n = 1, 3, 5`), consistent with
`√(λt)^n⟨xⁿ⟩ → 0` for odd `n`.

Questions. (1) Is A the right level — dominated convergence with the existing `t`-uniform Gaussian bound — or does the seabed's `K/t`
rate machinery (`J_0_asymptotic`) generalise more cheaply to all `n` (giving rates too)? For the pointwise limit, is there any subtlety in
`e^{−(Au³/√t + Bu⁴/t)} → 1` (continuity of `exp` at 0 plus `1/√t, 1/t → 0`)? (2) In B, `√(λt)^n ⟨xⁿ⟩ = J_n/J_0` needs `I_0 ≠ 0` (`Z > 0`) and the
division of two limits with `J_0 → √(2π) ≠ 0` — anything else? Should the statement be in `(λt)^{n/2}` (real power) or `√(λt)^n` (natural power
of a square root, as the seabed's relation is stated)? (3) Which odd-moment statement is most useful downstream: `√(λt)^n⟨xⁿ⟩ → 0`, or the
sharper `t^{(n+1)/2}⟨xⁿ⟩ → c_n` (which needs a first-order expansion in `A`, not just dominated convergence)? Please end with a vote on A–C.
