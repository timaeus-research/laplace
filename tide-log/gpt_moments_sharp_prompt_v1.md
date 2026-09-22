# Tide `moments-sharp` (laplace seabed): candidates for GPT-6 Astra

## Context

The seabed has, for the one-dimensional anharmonic Gibbs law `ℓ(x) = λx²/2 + αx³/6 + γx⁴/24` (`λ, γ > 0`, `α² < 3λγ`), with
`A = α/(6λ^{3/2})`, `B = γ/(24λ²)`, `m_k = ∫ u^k e^{−u²/2}` (`m_{2j} = (2j−1)‼ √(2π)`, odd `m` vanish):

```lean
-- Laplace/OneD/JnThirdOrder.lean (tide order3-parity)
theorem J_n_even_asymptotic_order3 (hlam) (hgamma) (hdisc) (k : ℕ) : ∃ K, 0 ≤ K ∧ ∀ {t}, 1 ≤ t →
    |J_n lam alpha gamma (2 * k) t - (m (2k) - B / t * m (2k+4) + A ^ 2 / (2 * t) * m (2k+6))| ≤ K / t ^ 2
theorem J_n_odd_asymptotic_order3 (k : ℕ) : … |J_n lam alpha gamma (2 * k + 1) t - (-(A / √t * m (2k+4)) + A * B / (t * √t) * m (2k+8) - A ^ 3 / (6 * (t * √t)) * m (2k+10))| ≤ K / t ^ 2
-- Laplace/OneD/MomentThirdOrder.lean
theorem ratio_rate_order2 (ht : 1 ≤ t) (hc : 0 < c) (hY : c / 2 ≤ Y) (hX : |X - (a + b / t)| ≤ KX / t ^ 2) (hYe : |Y - (c + d / t)| ≤ KY / t ^ 2) :
    |X / Y - a / c - (b * c - a * d) / c ^ 2 / t| ≤ 2 / c * (KX + (|a / c| + |(b * c - a * d) / c ^ 2|) * KY + |(b * c - a * d) / c ^ 2 * d|) / t ^ 2
theorem ratio_rate_order1 (ht : 0 < t) (hc : 0 < c) (hY : c / 2 ≤ Y) (hX : |X - a| ≤ KX / t) (hYe : |Y - c| ≤ KY / t) : |X / Y - a / c| ≤ 2 / c * (KX + |a / c| * KY) / t
theorem J0_delta_order3 : … |J₀ − (√(2π) + √(2π)(15A²/2 − 3B)/t)| ≤ K/t²;   theorem J0_delta_order1 : … |J₀ − √(2π)| ≤ K/t
theorem secondMoment_anharmonic_order3_rate : … |t⟨x²⟩ − 1/λ − (45A² − 12B)/(λt)| ≤ K/t²
theorem thirdMoment_anharmonic_rate_sharp : … |t²⟨x³⟩ + 5α/(2λ³)| ≤ K/t
-- Laplace/OneD/MomentsAllOrders.lean (tide moments-all-orders)
theorem sqrt_pow_mul_moment_eq (hlam hgamma hdisc) (n) (ht : 0 < t) : √(λt)^n * ⟨xⁿ⟩_t = J_n lam alpha gamma n t / J_n lam alpha gamma 0 t
theorem moment_anharmonic_asymptotic (n) : Tendsto (fun t => √(λt)^n * ⟨xⁿ⟩_t) atTop (𝓝 (m n / m 0))      -- leading order, all n
theorem evenMoment_anharmonic_asymptotic (k) : Tendsto (fun t => t^k ⟨x^{2k}⟩) atTop (𝓝 ((2k−1)‼/λ^k));  oddMoment_anharmonic_tendsto_zero
-- Laplace/OneD/GaussianMoments.lean
theorem integral_pow_mul_exp_neg_sq_half (k) : ∫ x, x ^ (2 * k) * exp (-x ^ 2 / 2) = ((2 * k - 1)‼ : ℝ) * √(2π)
theorem integral_pow_mul_exp_neg_sq_odd (k) : ∫ x, x ^ (2 * k + 1) * exp (-x ^ 2 / 2) = 0
-- the seabed's order-2 rates exist only for n = 2, 3, 4 (secondMoment/thirdMoment/fourthMoment_anharmonic_*).
```

## Candidates

**A. All odd moments at leading order, with a rate.** For every `k`,
`|t^{k+1} ⟨x^{2k+1}⟩ + α(2k+3)‼/(6λ^{k+2})| ≤ K/t` for `t ≥ T`, hence `t^{k+1}⟨x^{2k+1}⟩ → −α(2k+3)‼/(6λ^{k+2})`
(`k = 0`: `−α/(2λ²)`, `k = 1`: `−5α/(2λ³)`, both already in the seabed). Proof: `√t J_{2k+1} = −A m_{2k+4} + O(1/t)` from
`J_n_odd_asymptotic_order3` (the `1/(t√t)` terms become `1/t` after multiplying by `√t`), `J₀ = √(2π) + O(1/t)`, `ratio_rate_order1`, and the
bridge `t^{k+1}⟨x^{2k+1}⟩ = √t J_{2k+1}/(λ^{k+1/2} J₀)` from `sqrt_pow_mul_moment_eq`; `A m_{2k+4}/(λ^{k+1/2}√(2π)) = α(2k+3)‼/(6λ^{k+2})`
(handle `√λ` by the substitution `λ = s²`).

**B. All even moments to second order, with a `t⁻²` remainder.** For every `k`,
`|t^k ⟨x^{2k}⟩ − (2k−1)‼/λ^k − C_k/(λ^k t)| ≤ K/t²` for `t ≥ T`, with
`C_k = (A²/2)((2k+5)‼ − 15(2k−1)‼) − B((2k+3)‼ − 3(2k−1)‼)`
(`C_1 = 45A² − 12B`, `C_2 = 450A² − 96B`, matching the seabed's second and fourth moments). Proof: `J_n_even_asymptotic_order3 k` with the
Gaussian moments evaluated (`m_{2k+4} = (2k+3)‼√(2π)` needs `2k+4 = 2(k+2)`), `J0_delta_order3`, `ratio_rate_order2` with
`a = m_{2k}`, `b = −B m_{2k+4} + (A²/2) m_{2k+6}`, `c = m_0`, `d = √(2π)(15A²/2 − 3B)`, so `(bc − ad)/c² = C_k`, and the bridge
`(λt)^k ⟨x^{2k}⟩ = J_{2k}/J₀`.

**C (optional).** Corollaries: the general-`k` limits `t^k⟨x^{2k}⟩ → (2k−1)‼/λ^k` re-derived with a rate (`|…| ≤ K/t`), and the cumulant
consequences are *not* attempted.

## Numerical check (`numcheck_moments_sharp.py`, `λ = 2`, `a = ½`, `γ = λ²`, `t = 50 … 800`)

`t·(t^{k+1}⟨x^{2k+1}⟩ − limit)` for `k = 0..3` converges to `0.180, 0.772, 3.96, 23.7` (bounded, so the rate is `1/t` and the limits
`−0.1768, −0.4419, −1.5468, −6.9606 = −α(2k+3)‼/(6λ^{k+2})` are right); `t²·(t^k⟨x^{2k}⟩ − (2k−1)‼/λ^k − C_k/(λ^k t))` for `k = 1..3`
converges to `−0.199, −1.60, −13.2` (bounded); `C_1 = −0.1875 = 45A² − 12B`, `C_2 = −0.875 = 450A² − 96B`.

## Questions

1. Are A and B correct as stated, in particular the closed form of `C_k` and the constant in A?
2. Lean: the Gaussian moment lemma is stated for exponents `2 * k`; the `J_n` expansions produce `2 * k + 4`, `2 * k + 6` (even) and
   `2 * k + 1 + 3 = 2 * k + 4`, … (odd). Is `rw [show 2 * k + 4 = 2 * (k + 2) by ring]` inside the integrals (or `Finset`-free `have`
   statements with `Nat.doubleFactorial` evaluated as `(2 * (k + 2) − 1)‼ = (2k+3)‼`) the right way, and is there a cleaner way to
   organise the `(2k+3)‼`, `(2k+5)‼` bookkeeping (e.g. `Nat.doubleFactorial_add_two : (n+2)‼ = (n+2) * n‼`) so that `C_k` can be
   stated with double factorials rather than expanded?
3. `√λ` bookkeeping in A: `√(λt)^{2k+1} = λ^k √λ · t^k √t`; is the substitution `λ = s²` (as in `thirdMoment_anharmonic_rate_sharp`) still
   the cleanest, or should A be stated with `Real.sqrt lam ^ (2k+1)` in the constant?
4. Scope and vote (A+B, C optional)?
