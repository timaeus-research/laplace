# Tide: llc-variance

**Direction (user):** auto mode ("Just proceed on auto. You can bite off big chunks here to formalise and don't worry about retrospectives"); this tide chosen by the agent: the E4 LLC-estimator variance law.
**Seabed:** laplace, commit 7f7c17e (main, after `gaussian-table`)
**Started:** 2026-09-21 (UTC, see filename)

## Context

E4 of the sanity note ("chains, draws and dimension") finds that "the LLC is far cheaper than the covariance":
the pooled covariance's relative Frobenius error follows `sqrt(d/(CN))` while the LLC is within 2% of `d/2`
for every budget above `10^4` draws. Tides `frobenius-law` and `gaussian-table` formalised the covariance side:
`frobenius_pooledSecondMoment_le` (conditional on a `FourthMomentTable` and a diagonal Gram table) and
`frobenius_ula_le` (unconditional, for the ULA chain driven by iid standard Gaussians). The LLC side of E4 has
only its mean so far (`integral_llc_running_mean`, `llc_running_mean_shortfall` in `LLCClosures.lean`).
This tide adds the variance of the pooled LLC statistic and the quantitative version of "far cheaper".

Seabed pieces in play: `cov_mul_mul_of_isLinComb` (four-way Wick for linear combinations of a
`FourthMomentTable` family), `pooledSecondMoment` and `variance_pooledSecondMoment` (FrobeniusLaw.lean),
`half_inner_euclid_eq_sum_eigen` (½⟨x,Hx⟩ = Σ_i p_i/(2t) ⟨u_i,x⟩²), `inner_ulaChain_eq_realChain`,
`gram_realChain_dir`, `isLinComb_realChain_dir`, `fourthMomentTable_projNoise_dir`, `toeplitz_sum_le`,
`sum_pow_two_mul_le'`.

## Candidates v1 (Claude)

Setting as in `FrobeniusLaw.lean`: `x : Fin C → ι → ℕ → Ω → ℝ` with every window value `x c i (b+1+k)`
a linear combination (`IsLinComb g s`) of a `FourthMomentTable g P v` family, and a Gram table
`∫ x c i k · x c' j l = if c = c' ∧ i = j then G i k l else 0`.

**A. Cross-covariance of pooled second-moment entries (abstract Wick layer).**
```
cov_pooledSecondMoment (i j i' j' : ι) :
  ∫ pSM i j · pSM i' j' − (∫ pSM i j)(∫ pSM i' j')
    = ((if i = i' ∧ j = j' then 1 else 0) + (if i = j' ∧ j = i' then 1 else 0)) / (C N²)
        Σ_{k,l<N} G i (b+1+k) (b+1+l) · G j (b+1+k) (b+1+l)
```
This generalises `variance_pooledSecondMoment` (the case `i' = i, j' = j` gives the `(1 + δ_ij)` factor) and
gives the diagonal cross term `Cov(pSM_ii, pSM_jj) = 2 δ_ij/(CN²) Σ G_i²`, which is what the LLC needs.

**B. Variance of a weighted diagonal statistic (the LLC shape).**
For weights `w : ι → ℝ`, the statistic `Σ_i w i · pSM i i` (this is the pooled LLC once `w i = p_i/2`) has
```
variance_pooledQuad :
  Var(Σ_i w i · pSM i i) = 2/(C N²) Σ_i (w i)² Σ_{k,l<N} G i (b+1+k) (b+1+l)²
```
and, under the zero-start AR(1) Gram table `G i k l = s₂ i (ρ_i^{|k−l|} − ρ_i^{k+l})` with `0 ≤ ρ_i < 1`,
the stationary envelope
```
variance_pooledQuad_le :
  Var(Σ_i w i · pSM i i) ≤ 2/(C N) Σ_i (w i)² (s₂ i)² (1 + ρ_i²)/(1 − ρ_i²).
```

**C. The ULA instance (unconditional, E4 LLC side).**
For `P = t H` positive definite, `0 < h`, `h p_i ≤ 1`, iid standard Gaussian noise `ξ c k` (as in
`frobenius_ula_le`), with `ρ_i = 1 − h p_i` and the ULA law `s₂ i = 2h/(1 − ρ_i²) = 1/(p_i(1 − h p_i/2))`:
```
variance_llc_ula_le :
  Var( t · (1/(CN)) Σ_c Σ_{k<N} ½⟨x_c(b+1+k), H x_c(b+1+k)⟩ )
    ≤ 1/(2 C N) Σ_i (1 + ρ_i²) / ((1 − ρ_i²) (1 − h p_i/2)²).
```
(Exact version: `= 1/(2 C N²) Σ_i p_i² Σ_{k,l} H_i(k,l)²`.) The statistic is exactly the one whose mean is
`integral_llc_running_mean`.

**D. "The LLC is far cheaper than the covariance" (isotropic comparison).**
In the isotropic case `p_i = p` for all `i`, with `τ = (1+ρ²)/(1−ρ²)`, the relative bounds are
`Var(LLC)/⟨LLC⟩² ≤ 2τ/(d·CN)` (from C and `⟨LLC⟩ = d/(2(1 − hp/2))`) against the relative Frobenius bound
`(d+1)τ/(CN)` (from `frobenius_ula_le` divided by `‖Σ_ULA‖_F² = d s₂²`); their ratio is exactly
`2/(d(d+1))`. Stated as an algebraic identity between the two right-hand sides (no new probability).

Vote intention: A+B+C, with D as a cheap closing corollary if C lands cleanly.

## Numerical check

Monte Carlo (`numcheck28.py`, 40 000 replications, `p = (1, 0.3, 0.1)`, `h = 0.5`, `C = 2`, `N = 40`, `b = 5`):

```
Var(LLC est) MC = 0.129422   formula = 0.128995   envelope = 0.192149
Cov(pSM_01, pSM_10) MC = 0.142196   formula = 0.143076
Cov(pSM_00, pSM_11) MC = -0.000734   formula = 0
Var(pSM_00) MC = 0.0725069   formula = 0.0730852
d=2: rel_llc/rel_frob = 0.333333   2/(d(d+1)) = 0.333333
d=5: rel_llc/rel_frob = 0.0666667   2/(d(d+1)) = 0.0666667
d=10: rel_llc/rel_frob = 0.0181818   2/(d(d+1)) = 0.0181818
```
All agree to Monte Carlo precision; the envelope is an upper bound as claimed.

## GPT-6 Astra v1

Saved verbatim in `tide-log/gpt_llc_variance_v1.md` (prompt in `gpt_llc_variance_prompt_v1.md`). Summary: A–C correct as stated; D correct as a ratio of the two *bound* expressions provided both are normalised by the *stationary* targets (the finite-window mean carries the zero-start factor `a_{b,N} = 1 − (1/N) Σ_k ρ^{2(b+1+k)}`, so the variance bound divided by the actual finite-window mean squared is the conservative `2τ/(d·CN·a²)`). Architecture: prove A generally and re-derive `variance_pooledSecondMoment` from it; state B on `fun ω => Σ_i w i * pooledSecondMoment x N b i i ω` with an explicit weighted covariance identity; for C prove the pointwise statistic identity `t·(1/(CN))ΣΣ ½⟨x,Hx⟩ = Σ_i (p_i/2) pSM_ii` first, then reuse the Gaussian-table → real-chain → Gram route unchanged, and export both the exact ULA variance and its envelope. Suggested cheap addition: the mean-square error `E[(LLĈ − d/2)²] = Var + (E LLĈ − d/2)²` from the existing mean theorem.

## Vote
- Claude: A+B+C+D (D normalised by the stationary LLC mean and the stationary Frobenius norm, as GPT specified)
- GPT-6 Astra: A+B+C+D

Agreed. Proceeding to Step 3.
