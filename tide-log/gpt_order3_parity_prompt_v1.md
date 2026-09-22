# Tide `order3-parity` (laplace seabed, commit 490d753): candidates for GPT-6 Astra

## Context

The Sanity-on-Sampling note's E7 claims that adding the one-loop term to the Laplace covariance takes the relative remainder from
`O(1/t)` to `O(1/t²)`; E2 quotes the exact LLC `t⟨ℓ⟩ = ½ + c/t + …`. The seabed certifies both only to `t^{-3/2}`:

```lean
-- Laplace/OneD/Rescaling.lean
noncomputable def cubicScale (lam alpha : ℝ) : ℝ := alpha / (6 * lam * Real.sqrt lam)      -- A
noncomputable def quarticScale (lam gamma : ℝ) : ℝ := gamma / (24 * lam ^ 2)               -- B
noncomputable def rescaledPerturbation (lam alpha gamma t u : ℝ) : ℝ :=
  cubicScale lam alpha * u ^ 3 / Real.sqrt t + quarticScale lam gamma * u ^ 4 / t          -- s_t(u)
theorem rescaled_max_decay (hlam) (hgamma) (hdisc : alpha ^ 2 < 3 * lam * gamma) :
    ∃ c₀ > 0, ∀ {t : ℝ}, 0 < t → ∀ u : ℝ,
      Real.exp (-(u ^ 2) / 2) * max 1 (Real.exp (-rescaledPerturbation lam alpha gamma t u)) ≤ Real.exp (-(c₀ * u ^ 2))
-- Laplace/OneD/RecoveryAllOrder.lean / ExpRemainderSigned.lean
noncomputable def expRemainder (n : ℕ) (s : ℝ) : ℝ := Real.exp (-s) - ∑ j ∈ Finset.range n, (-s) ^ j / (Nat.factorial j : ℝ)
theorem abs_expRemainder_le_max (n : ℕ) (s : ℝ) : |expRemainder n s| ≤ |s| ^ n / (Nat.factorial n : ℝ) * max 1 (Real.exp (-s))
-- Laplace/OneD/IntegralRemainder.lean
noncomputable def J_n (lam alpha gamma : ℝ) (n : ℕ) (t : ℝ) : ℝ :=
  ∫ u : ℝ, u ^ n * Real.exp (-(u ^ 2) / 2) * Real.exp (-rescaledPerturbation lam alpha gamma t u)
theorem mean_anharmonic_O2_rate … : ∃ K T, 0 ≤ K ∧ 1 ≤ T ∧ ∀ {t}, T ≤ t → |t * ⟨x⟩_t - (-alpha / (2 * lam ^ 2))| ≤ K / t
-- Laplace/OneD/IntegralRemainder2.lean  (cubic-order remainder, O(1/(t√t)))
theorem rescaled_cube_bound (hlam) (hgamma) {t} (ht : 1 ≤ t) (u) :
    |rescaledPerturbation lam alpha gamma t u| ^ 3 ≤ 4 * (|A| ^ 3 + B ^ 3) * (u ^ 8 + u ^ 10 + u ^ 12) / (t * Real.sqrt t)
theorem perturbation_remainder3_combined … : ∃ C₀ c₀, 0 ≤ C₀ ∧ 0 < c₀ ∧ ∀ {t}, 1 ≤ t → ∀ n u,
    |u ^ n * exp (-(u ^ 2) / 2) * (exp (-s_t u) - (1 - s_t u + s_t u ^ 2 / 2))| ≤ (C₀ / (t * √t)) * |u| ^ n * (u ^ 8 + u ^ 10 + u ^ 12) * exp (-(c₀ * u ^ 2))
theorem integrable_pow_add3_mul_exp_neg_mul_sq (hc : 0 < c) (n) : Integrable (fun u => |u| ^ n * (u ^ 8 + u ^ 10 + u ^ 12) * exp (-(c * u ^ 2)))
theorem perturbation_remainder3_integral_bound … (n) : ∃ K, 0 ≤ K ∧ ∀ {t}, 1 ≤ t →
    |∫ u, u ^ n * exp (-(u ^ 2) / 2) * (exp (-s_t u) - (1 - s_t u + s_t u ^ 2 / 2))| ≤ K / (t * √t)
-- Laplace/OneD/JnSecondOrder.lean
theorem quadratised_integral_decomposition (lam alpha gamma) (n) (ht : 0 < t) :
    ∫ u, u ^ n * exp (-(u ^ 2) / 2) * (1 - s_t u + s_t u ^ 2 / 2) =
      m n - A / √t * m (n+3) - B / t * m (n+4) + A ^ 2 / (2 * t) * m (n+6) + A * B / (t * √t) * m (n+7) + B ^ 2 / (2 * t ^ 2) * m (n+8)
    -- with m k := ∫ u, u ^ k * exp (-(u ^ 2) / 2)
theorem J_n_asymptotic_order2 … (n) : ∃ K, 0 ≤ K ∧ ∀ {t}, 1 ≤ t →
    |J_n − (m n − A/√t * m (n+3) − B/t * m (n+4) + A²/(2t) * m (n+6))| ≤ K / (t * √t)
-- Laplace/OneD/GaussianMoments.lean
theorem integral_pow_mul_exp_neg_sq_half (k) : ∫ u, u ^ (2k) * exp (-(u ^ 2) / 2) = (2k-1)‼ * √(2π)   -- (shape approximately)
theorem integral_pow_mul_exp_neg_sq_odd (k) : ∫ u, u ^ (2k+1) * exp (-(u ^ 2) / 2) = 0
-- Laplace/OneD/MomentSecondOrder.lean
theorem secondMoment_anharmonic_order2_rate … : ∃ K T, … → |t * ⟨x²⟩ - 1/lam - (45 A² - 12 B)/(lam * t)| ≤ K / (t * √t)
theorem fourthMoment_anharmonic_order2_rate … : |t² ⟨x⁴⟩ - 3/lam² - (450 A² - 96 B)/(lam² t)| ≤ K / (t √t)
theorem thirdMoment_anharmonic_rate … : |t² ⟨x³⟩ + 15 A / √lam ^ 3| ≤ K / √t
-- Laplace/Multi/VarianceOrder2.lean
theorem var_anharmonic_order2_rate … : |t Var_t[x] - 1/lam - (alpha²/lam⁴ - gamma/(2 lam³))/t| ≤ K / (t √t)
theorem var_relative_rate_order2 … : |t (lam t Var - 1) - (alpha²/lam³ - gamma/(2 lam²))| ≤ K / √t
theorem var_relative_rate_order2_note (hgamma : gamma = lam^2) (halpha : alpha^2 = a^2 lam^3) (ha : a^2 < 3) : |…-(a² - 1/2)| ≤ K/√t
theorem energy_anharmonic_order1_rate … : |t ⟨ℓ⟩ - 1/2 - (5 alpha²/(24 lam³) - gamma/(8 lam²))/t| ≤ K / (t √t)
(+ separable / rotated forms of the note statements)
```

The proofs of the moment rates go through "delta" lemmas `|J_r − c_r (1 + d_r/t)| ≤ K/(t√t)` for `r = 0, 2, 4` and `|J_3 + 15A√(2π)/√t| ≤ K/(t√t)`,
then the exact cancellation of the `1/t` term in `J_r − (leading + coeff/t) J_0`, then division by `J_0 ≥ c > 0` (`J_0_eventually_bounded`).

## Candidates

**A. Fourth-order integral remainder.** For `t ≥ 1`,
`|∫ uⁿ e^{−u²/2} (e^{−s_t} − (1 − s_t + s_t²/2 − s_t³/6))| ≤ K/t²`.
Pointwise: `abs_expRemainder_le_max 4` gives `|s|⁴/24 · max 1 e^{−s}`; `s_t⁴ = (Au³/√t + Bu⁴/t)⁴ ≤ 8(A⁴u¹²/t² + B⁴u¹⁶/t⁴) ≤ 8(A⁴ + B⁴)(u¹² + u¹⁶)/t²`
(no odd absolute powers this time, `(x+y)⁴ ≤ 8(x⁴ + y⁴)`); `rescaled_max_decay`; integrability of `|u|ⁿ(u¹² + u¹⁶)e^{−cu²}`. A copy of
`IntegralRemainder2` with the exponent bumped.

**B. Cubised decomposition and the third-order `J_n` expansion.**
`∫ uⁿ e^{−u²/2} s_t³ = A³ m_{n+9}/(t√t) + 3A²B m_{n+10}/t² + 3AB² m_{n+11}/(t²√t) + B³ m_{n+12}/t³`, hence with `quadratised_integral_decomposition`
and A:
`|J_n − (m_n − (A/√t) m_{n+3} − (B/t) m_{n+4} + (A²/(2t)) m_{n+6} + (AB/(t√t)) m_{n+7} − (A³/(6t√t)) m_{n+9})| ≤ K/t²` for `t ≥ 1`
(the `B²/(2t²) m_{n+8}`, `A²B/(2t²) m_{n+10}`, `AB²/(2t²√t) m_{n+11}`, `B³/(6t³) m_{n+12}` terms absorbed into `K`).
**Parity corollaries**: for even `n` the odd moments vanish and
`|J_n − (m_n − (B/t) m_{n+4} + (A²/(2t)) m_{n+6})| ≤ K/t²` (the second-order formula with a `t⁻²` remainder); for odd `n`
`|J_n + (A/√t) m_{n+3} − (AB m_{n+7} − A³ m_{n+9}/6)/(t√t)| ≤ K/t²`.

**C. Sharp second-moment and variance rates (E7's `t⁻²`).**
`|t⟨x²⟩ − 1/λ − C₂/t| ≤ K/t²` with the same `C₂ = (45A² − 12B)/λ` (the delta lemmas for `J_0`, `J_2` re-proved from B's even corollary, the
existing assembly otherwise unchanged); then with `mean_anharmonic_O2_rate` (`|t⟨x⟩ − m₀| ≤ K/t`, so the `(tM − m₀)(tM + m₀)/t` term is `O(t⁻²)`):
`|t Var − 1/λ − (α²/λ⁴ − γ/(2λ³))/t| ≤ K/t²`, `|t(λ t Var − 1) − (α²/λ³ − γ/(2λ²))| ≤ K/t`, the note form `|… − (a² − ½)| ≤ K/t`, and the
separable / rotated forms. This is E7's claim as stated.

**D. Sharp energy rate.** `|t²⟨x³⟩ + 5α/(2λ³)| ≤ K/t` (from the existing order-2 `J_3` delta — its `1/t` terms vanish by parity — and
`|J_0/m_0 − 1| ≤ K/t`), `|t⟨x⁴⟩ − 3/(λ²t)| ≤ K/t²` (from the existing fourth-moment rate divided by `t`), and then
`|t⟨ℓ⟩ − ½ − (5α²/(24λ³) − γ/(8λ²))/t| ≤ K/t²` with the note / separable / rotated forms (E2's LLC to `O(t⁻²)`).

**E (follow-up, not this tide).** The explicit `t⁻²` coefficients (need the `ε⁴` terms, i.e. a fifth-order remainder).

## Numerical check (λ = 2, a = ½, γ = λ²; `numcheck_order3_parity.py`)

`t²(J_n − 3-term)` for `n = 0, 2, 4` converges to `−0.0615, −1.027, −16.08`; `t²(J_n − 2-term)` for `n = 1, 3` decays like `t^{-1/2}`
(as parity predicts: the odd-`n` remainder is really `O(t^{-5/2})`); `t·[t(λtVar − 1) − (a² − ½)] → −0.2715` (the note's "≈ 0.27/t");
`t²·[t⟨ℓ⟩ − ½ − (5a²/24 − 1/8)/t] → −0.0542`; `t·[t²⟨x³⟩ + 5α/(2λ³)] → 0.772`.

## Questions

1. Are A–D correct as stated? In particular the cubised coefficients (`s³/6` terms), the parity corollaries, and the claim that D's
   third-moment rate needs no new expansion (only the existing `J_3` delta and a first-order `J_0` bound).
2. For A, is `(x + y)⁴ ≤ 8(x⁴ + y⁴)` plus `u¹²/t² + u¹⁶/t⁴ ≤ (u¹² + u¹⁶)/t²` (for `t ≥ 1`) the right shape, or is there a cleaner route
   to the `K/t²` remainder (e.g. via the existing cubic bound times `|s_t| ≤ (|A|(|u|³ + u⁴) + B u⁴)/√t`… that only gives `t⁻²` if
   the extra factor is `O(1/√t)` uniformly in `u`, which it is not; comment)?
3. Is there a cheaper way to organise C than re-proving the `J_0`, `J_2` delta lemmas with the sharper remainder — e.g. a generic
   "ratio of two expansions" lemma `|X − a − b/t| ≤ K/r(t)`, `|Y − c − d/t| ≤ K'/r(t)`, `c > 0` ⟹ `|X/Y − a/c − (bc − ad)/(c²t)| ≤ K''/r(t)`
   for `r(t) ≥ t` that would also serve D and later tides?
4. Scope: is A+B+C one coherent tide (with D as a stretch) or should D be a separate tide? Any statement you would sharpen or
   correct? Vote for a single candidate cluster.
