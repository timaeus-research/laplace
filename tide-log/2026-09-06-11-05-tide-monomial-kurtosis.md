# Tide: monomial-kurtosis

**Direction (user):** Continue with what you think best (auto). Pivoted off the greybook §5.4
Gaussian corner to the laplace seabed; an Explore survey identified this as the top clean target.
**Seabed:** laplace, commit (branch base, Sep 2026)
**Started:** 2026-09-06

## Candidate

The excess kurtosis (connected four-point function) `⟨x⁴⟩ − 3⟨x²⟩²` of `x` against the symmetric
reference weight `exp(-t·x^(2k)/(2k)!)`, in Gamma-ratio closed form — the fourth-cumulant analogue
of the landed `monomial_variance_even` (the second cumulant). For a symmetric weight the mean
vanishes, so the fourth cumulant of `x` is exactly `⟨x⁴⟩ − 3⟨x²⟩²`.

## Numerical check

Gaussian reference `k = 1`: bracket = `Γ(5/2)/Γ(1/2) − 3(Γ(3/2)/Γ(1/2))² = 3/4 − 3·(1/2)² = 0`,
the correct vanishing excess kurtosis of a Gaussian. ✓

## Result

`monomial_excess_kurtosis (hk : 1 ≤ k)(ht : 0 < t)`:
`⟨x⁴⟩ − 3⟨x²⟩² = ((2k)!/t)^(2/k) · (Γ(5/(2k))/Γ(1/(2k)) − 3·(Γ(3/(2k))/Γ(1/(2k)))²)`.
Zero-sorry, full build clean (8883 jobs). Proof mirrors `monomial_variance_even` verbatim in shape:
rewrite `x⁴ = x^(2·2)`, `x² = x^(2·1)` (defeq `rfl`), substitute
`gibbsExpectation_kthPotential_even` at `j = 2` and `j = 1`, split the common power
`((2k)!/t)^(2/k) = (((2k)!/t)^(1/k))²` via `Real.rpow_add`, then `push_cast; rw [hpow]; ring`.
Compiled on the first attempt. No GPT.

New file `Laplace/OneD/MonomialKurtosis.lean`; first laplace tide of this session (pivot from
greybook). The `t^{-2/k}` `IsEquivalent` scaling corollary (the documented KthKth packaging pattern)
is a natural clean follow-up, not attempted here.
