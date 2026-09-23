# Tide: lagweight-longrun

**Direction (user):** auto mode — close the loop between tide 111's fixed-`n` average and tide 103's long-run variance: the exact lag-weight identity and `n·W_{η,n} → L_η`.
**Seabed:** laplace, commit afbc007 (tide 111 `BurnInAverage` (`lagWeight`), tide 103 `AutocovScaled` (`L_η`))
**Started:** 2026-09-23-11-02 UTC

## Candidates v1 (Claude)

`F_n(z) = (n + 2∑_{j<n}(n−(j+1))z^{j+1})/n²` (tide 111's `lagWeight`), `αᵢ = 1−ηλᵢ`, `aᵢ = 1−ηλᵢ/2`, `W_{η,n} = ½∑ᵢaᵢ⁻²F_n(αᵢ²)` (the limiting scaled
variance of the `n`-draw average), `L_η = ∑ᵢ(1+αᵢ²)/(4ηλᵢaᵢ³)` (tide 103's long-run variance limit).

- **A** (`sum_range_sub_succ_mul_pow`, `lagWeight_eq`): `∑_{j<n}(n−(j+1))z^{j+1} = nz/(1−z) − z(1−z^n)/(1−z)²` and hence
  `F_n(z) = (1+z)/(n(1−z)) − 2z(1−z^n)/(n²(1−z)²)` for `n ≥ 1`, `z ≠ 1` (GPT's suggested exact identity; the IAT bound of tide 111 is its first term).
- **B** (`lagWeight_mul_tendsto`): `n·F_n(z) → (1+z)/(1−z)` as `n → ∞` for `0 ≤ z < 1`.
- **C** (`Leta_eq_lagWeight_limit`, `avgLimit_mul_tendsto_Leta`): `½∑ᵢaᵢ⁻²(1+αᵢ²)/(1−αᵢ²) = L_η` and **`n·W_{η,n} → L_η`**: the variance of the
  `n`-draw post-burn-in average, scaled by `n`, recovers the stationary long-run variance — an `n → ∞` statement about the limiting coefficients
  (no simultaneous `n(t)` claim).

## Numerical check

`numcheck112.py`: identity to `1e-13` over `n ≤ 11`, `z ∈ {0, .1, .5, .9, .99}`; `L_η = 6.1694 = ½∑a⁻²(1+α²)/(1−α²)`; `n·W_n → L_η` (6.1686 at `n = 10⁴`),
`n·F_n(½) → 3`.
```
identity check |F_n - closed| : 1.035838081975271e-13
L_eta (tide 103) = 6.169410555640505  ½∑a⁻²(1+α²)/(1−α²) = 6.169410555640505
  n=     1  n*W_n = 2.596242   n*F_n(0.5) = 1.000000 -> 3.0
  n=     5  n*W_n = 4.627864   n*F_n(0.5) = 2.225000 -> 3.0
  n=    20  n*W_n = 5.754260   n*F_n(0.5) = 2.800000 -> 3.0
  n=   100  n*W_n = 6.086376   n*F_n(0.5) = 2.960000 -> 3.0
  n=  1000  n*W_n = 6.161107   n*F_n(0.5) = 2.996000 -> 3.0
  n= 10000  n*W_n = 6.168580   n*F_n(0.5) = 2.999600 -> 3.0
```

## GPT-6 Astra v1

Full response in `gpt_lagweight-longrun_v1.md`. Summary: **A–C correct** (`n ≥ 1`, `z ≠ 1`; at `z = 1` the definition gives `F_n(1) = 1`; C needs the
finite spectrum and `0 < ηλᵢ < 2`, and `1 − αᵢ² = 2ηλᵢaᵢ`). Cheap strengthenings, all adopted: the exact deficit `0 ≤ (1+z)/(1−z) − nF_n(z) =
2z(1−z^n)/(n(1−z)²) ≤ 2z/(n(1−z)²)`, summed to `0 ≤ L_η − nW_{η,n} ≤ D_η/n` with `D_η = ∑ᵢaᵢ⁻²zᵢ/(1−zᵢ)²` (so `W_{η,n} = L_η/n + O(n⁻²)` with a
nonpositive correction); monotonicity `nF_n(z) ≤ (n+1)F_{n+1}(z)` (`= (2/(n(n+1)))∑_{k≤n}kz^k ≥ 0`), so `nW_{η,n} ↑ L_η`. **Wording correction**:
`nW_{η,n} ≤ L_η` means the fixed-window variance is *at most the long-run approximation `L_η/n`* (the normalised variance approaches the long-run
constant from below), not that the average "never beats the long-run rate". Suggested line: "for fixed strictly stable `η`, the limiting
fixed-window variance recovers tide 103's long-run variance as `nW_{η,n} ↑ L_η`, with deficit `O(n⁻¹)`; a sequential limit after the anchored
post-burn-in limit, not a limit interchange."

## Candidates v2 (Claude, adopting the additions)

- **D** (`mul_lagWeight_eq`, `lagWeight_mul_deficit_le`, `Leta_sub_avgLimit_mul_le`, `lagWeight_mul_le`, `avgLimit_mul_le_Leta`): the exact deficit and its
  `O(1/n)` bounds, scalar and summed.
- **E** (`pow_mul_one_add_le_one`, `mul_lagWeight_succ_le`): Bernoulli `z^n(1 + n(1−z)) ≤ 1` and the monotonicity `nF_n(z) ≤ (n+1)F_{n+1}(z)`.

## Vote
- Claude: A + B + C + D + E
- GPT-6 Astra: "approve A–C. Add the exact finite-n correction and its upper bound; monotonicity is also cheap."
