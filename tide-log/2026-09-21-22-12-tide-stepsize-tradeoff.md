# Tide: stepsize-tradeoff

**Direction (user):** auto mode on the Sanity-on-Sampling note; E1's step-size trade-off: the zero-start bias against Σ_ULA falls with
the step, the bias against Q⁻¹ changes sign (discretisation inflation against zero-start deflation), and E1's inflation numerics.
**Seabed:** laplace, branch `tide/frobenius-target-raw` at commit 43c56f1 (chained: needs `FrobeniusTarget.lean`)
**Started:** 2026-09-21T22:15Z

## Candidates v1 (Claude)

See `gpt_stepsize_tradeoff_prompt_v1.md` (A–C verbatim).

- A: per-direction bias `s₂(h) a(h)` against Σ_ULA is antitone in `h` on `(0, 1/p]` (termwise
  `(1 − u')^{2m}(1 − u/2) ≤ (1 − u)^{2m}(1 − u'/2)`); squared-bias sum antitone.
- B: per-direction bias against Q⁻¹, `f(h) = h/(2 − hp) − s₂(h) a(h)`, has `f(0) = −1/p`, `f(1/p) = 1/p`, hence an interior zero (IVT).
- C: E1 numerics `1/(1 − hp/2) = 2, 4, 20` at `hp = 1, 3/2, 19/10`; isotropic LLC `(d/2)/(1 − hp/2) = 10, 20, 100` for `d = 10`.

## GPT-6 Astra v1

Saved verbatim in `gpt_stepsize_tradeoff_v1.md`. Summary: A, C correct (A including the endpoint `hp = 1`; the restriction
`h ≤ 1/p_max` matters, beyond it even powers of negative `ρ` grow again). B correct with two repairs: use the continuous form
`s₂ = 1/(p(1 − hp/2))` and the finite-sum `a` at `h = 0` (the `2h/(1 − ρ²)` form is `0/0` there); the useful simplification is
`f(h) = (hp − 2a(h))/(p(2 − hp))`, so `f < 0 ⇔ a > hp/2`, and since `a` is antitone `hp − 2a(h)` is strictly increasing: the zero is
**unique** with `f < 0` below and `f > 0` above. Interpretation: a rigorous per-direction cancellation mechanism, not the full empirical
Frobenius trade-off (different directions cancel at different steps; the centred variance also depends on `h`; the optimum near
`hp_max ≈ 0.5–1` is not located). Q3: neither the absolute nor the normalised centred envelope is monotone in `h` in general
(counterexamples given); the spectrum-free bound `(d+1)τ(r²)/(CN)` of tide `frobenius-free` is the antitone upper bound (optional add-on).

## Vote
- Claude: A+B+C, with B strengthened to uniqueness and signs via the strictly increasing gap `hp − 2a(h)`
- GPT-6 Astra: A+B+C (same strengthening)

## Numerical check

`numcheck_stepsize_tradeoff.py`: `s₂a` and `a` antitone on a 400-point grid of `h ∈ (0, 1/p]` for three `(p, N, b)`;
`f(0⁺) = −1/p`, `f(1/p) = 1/p` to four digits; the unique zero at `h*p ≈ 0.11–0.18`; the termwise inequality on a grid over
`u ≤ u' ≤ 1`, `m = 1..7`; the E1 numerics 2/4/20 and 10/20/100.
