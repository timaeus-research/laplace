# Tide: fulllaw-upper

**Direction (user):** auto mode — E8, full law: the state-dependent minibatch correction is `O(c)` two-sided — the contraction gives `‖Σ_full − Σ^{mb}‖ ≤ c‖B(Σ^{mb})‖/(1−L)`, hence an upper bound on the LLC mean complementing tide 107's lower bound.
**Seabed:** laplace, commit 39060df (tide 107 `FullLawLLC`, `Sampler/FullStep` (`contractingWith_fullStep`, `fullFixed`, `norm_stateTerm_le`))
**Started:** 2026-09-23-13-12 UTC

## Candidates v1 (Claude)

Setting (tide 107): the full law `X ↦ AXAᵀ + N + c∑ᵢDᵢXDᵢᵀ` (`fullStep`), Lipschitz constant `L = ‖A‖‖Aᵀ‖ + c∑ᵢ‖Dᵢ‖‖Dᵢᵀ‖` in the `ℓ∞` operator
norm, contraction for `L < 1`, fixed point `Σ_full` (`fullFixed`); `Σ^{mb}` the additive fixed point (`covStep A N Σ^{mb} = Σ^{mb}`);
`B(X) = ∑ᵢDᵢXDᵢᵀ` (`stateTerm`). Tide 107 proved the lower bound `tr(HΣ_full) ≥ tr(HΣ^{mb}) + c·tr(HB(Σ^{mb}))`.

- **A** (`abs_entry_le_linfty_opNorm`, `abs_trace_le`, `abs_trace_mul_le`): `|Mᵢⱼ| ≤ ‖M‖`, `|tr M| ≤ d‖M‖`, `|tr(HX)| ≤ d‖H‖‖X‖` for the `ℓ∞`
  operator norm.
- **B** (`fullFixed_sub_norm_le`, `fullFixed_sub_norm_le'`, `abs_fullFixed_sub_entry_le`): from Banach's a-priori estimate
  `dist(S, fix) ≤ dist(S, f(S))/(1−L)` with `f(Σ^{mb}) − Σ^{mb} = c·B(Σ^{mb})`: **`‖Σ_full − Σ^{mb}‖ ≤ c‖B(Σ^{mb})‖/(1−L) ≤ c(∑ᵢ‖Dᵢ‖‖Dᵢᵀ‖)‖Σ^{mb}‖/(1−L)`**,
  entrywise too: the state-dependent correction to the stationary covariance is `O(c)`.
- **C** (`trace_fullFixed_le`, `fullLaw_llc_le`): **`(t/2)tr(HΣ_full) ≤ (t/2)∑λᵢ(1+ht²Ĉᵢᵢ/2)/(pᵢκᵢ) + (t/2)·d‖H‖·c‖B(Σ^{mb})‖/(1−L)`**; with tide 107,
  the full-law LLC mean lies between `LLC^{mb} + (t/2)c·tr(HB(Σ^{mb}))` and `LLC^{mb} + (t/2)d‖H‖c‖B(Σ^{mb})‖/(1−L)`.
- **D** (`e8_fullFixed_sub_norm_le`): the note's instance `c = h²t²(1−m/n)/(m(n−1))`, `Dᵢ = Hᵢ − H`: the Hessian-fluctuation correction to the
  stationary covariance is at most `c(∑ᵢ‖Hᵢ−H‖‖(Hᵢ−H)ᵀ‖)‖Σ^{mb}‖/(1−L) = O(h²t²/m)`.

## Numerical check

`numcheck114.py` (3D diagonal frame so that `L < 1` in the `ℓ∞` operator norm, 5 per-sample Hessians, `m = 2`, `t = 20`, `h = 0.1/t`):
```
L = 0.8628 (<1)  ‖Σ_full − Σ_mb‖ = 1.663e-03  ≤  c‖B(Σ_mb)‖/(1−L) = 3.178e-03   ratio 0.523
LLC bounds: lower 4.709823 ≤ full 4.730111 ≤ upper 4.937900
```

## GPT-6 Astra v1

Full response in `gpt_fulllaw-upper_v1.md`. Summary: **accept A–C** (conditional on `c ≥ 0`, `L < 1`; `Δ = (T + cB)Δ + cB(S)` gives the Banach
residual estimate; the entrywise version must keep absolute values since PSD order is not entrywise; C needs `H ⪰ 0` for the lower bound); **revise D**:
the actual estimate is `‖Δ‖ ≤ h²t²(1−m/n)/(m(n−1))·b‖S‖/(1−L)` and the contraction gap is `1 − L = Θ(h)` at small step, so the stationary correction
is typically `O(ht²/m)`, not `O(h²t²/m)` (scalar check: `A = 1−hp`, `N = 2h`, `cB(x) = h²qx` gives `Δ = hq/(2p²) + O(h²)`); D is a fixed-gap
perturbation statement. Norm: the `ℓ∞` operator norm is legitimate, the theorem should be conditional on its `L < 1`; in the eigenbasis of `P`,
`‖A′‖‖A′ᵀ‖ = max|1−hpᵢ|² < 1`, which removes the deterministic obstruction (not automatically `a′ + cb′ < 1`); traces are frame-invariant, the
`ℓ∞` norm is not. Cheap additions: the relative estimate `‖Δ‖/‖S‖ ≤ cb/(1−L)` (adopted; `b = ∑‖Dᵢ‖²` for symmetric `Dᵢ`). Strongest refinement
(deferred): the exact identity `Δ = cRB(Σ_full)`, `R = (1−T)⁻¹`, `‖R‖ ≤ 1/(1−a)`, giving `‖Δ − cRB(S)‖ ≤ c²b‖B(S)‖/((1−a)(1−L))` and the sharper
lower bound `Δ ⪰ cRB(S) ⪰ cB(S)`; a trace-only version under `AᵀA + c∑DᵢᵀDᵢ ⪯ ℓI`. Reminder: a covariance fixed point does not establish a
Gaussian stationary law; `(t/2)tr(HΣ)` is the quadratic expectation of any centred law with covariance `Σ`.

## Candidates v2 (Claude)

- **D′** (`e8_fullFixed_sub_norm_le`, reworded): the note's coefficient gives `‖Δ‖ ≤ c b ‖Σ^{mb}‖/(1−L)` with `c = O(h²t²/m)`, hence `O(ht²/m)` once
  `1 − L = Θ(h)` is accounted for.
- **E** (`fullFixed_sub_norm_div_le`): the relative estimate.
- **F** (`fullLaw_llc_bounds`): the two-sided LLC statement packaged with tide 107.

## Vote
- Claude: A + B + C + D′ + E + F
- GPT-6 Astra: "formalize A → B → C, add the relative estimate cheaply, and pursue (ii) as the strongest natural refinement. Reject D's current unqualified small-h wording."
