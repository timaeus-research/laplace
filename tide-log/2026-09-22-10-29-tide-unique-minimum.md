# Tide: unique-minimum

**Direction (user):** Just proceed on auto. You can bite off big chunks here to formalise and don't worry about retrospectives.
(Auto-mode continuation: the untagged Setup sentence "`a² < 3` keeps the minimum unique", made sharp.)
**Seabed:** laplace, main e07d147
**Started:** 2026-09-22T10:30Z

## Candidates v1 (Claude)

See `gpt_unique_minimum_prompt_v1.md` (A–C verbatim).

- A: `ℓ(x) > 0` for `x ≠ 0` iff `α² < 3λγ` (sharp: `ℓ(−2α/γ) = 0` at equality, `ℓ(−2α/γ) < 0` beyond); note's `a² < 3`.
- B: nonzero critical points iff `8λγ/3 ≤ α²` (`a² ≥ 8/3`): unimodality is lost before uniqueness of the global minimiser.
- C: `rotatedAnharmonic Q c λ α γ w > 0` for `w ≠ c`: `c` is the unique global minimiser of E2's potential.

## Numerical check

`numcheck_unique_minimum.py` (sympy): `ℓ/x² = (γx² + 4αx + 12λ)/24` with discriminant `α²/36 − λγ/12`; `ℓ'/x = (γx² + 3αx +
6λ)/6` with discriminant `α²/4 − 2λγ/3`; `ℓ(−2α/γ) = 0` at `α² = 3λγ`. At `λ = γ = 1`: `a² = 2.5` no extra critical points; `a² =
2.8` critical points `−1.96, −3.06` with `ℓ ≥ 0` (min `0` at `0`); `a² = 3` a second zero at `−2a`; `a² = 3.2` negative values.

## GPT-6 Astra v1

Verbatim in `gpt_unique_minimum_v1.md`. Summary: thresholds `3` and `8/3` and the witness `x₀ = −2α/γ` are right
(`q(x) = (γ/24)(x + 2α/γ)² + (3λγ − α²)/(6γ)`, `ℓ(x₀) = 2α²(3λγ − α²)/(3γ³)`); two corrections: (i) the headline must be "`0` is the
unique global minimiser iff `α² < 3λγ`" (above the threshold the potential has a unique global minimiser *elsewhere*; the negative
theorem shows `0` ceases to be globally minimising), and the equality case should be stated as *two* global minimisers (`0` and
`−2α/γ ≠ 0`, with `ℓ ≥ 0` everywhere); (ii) at `α² = 8λγ/3` the extra critical point `x* = −3α/(2γ)` is a stationary inflection
(`ℓ'' (x*) = 0`, `ℓ''' (x*) = −α/2`), not an extremum; two extra extrema appear for `8/3 < a² < 3` (open interval). "Keeps the
minimum unique" = "keeps the designated centre the unique global minimiser"; unique critical point needs `a² < 8/3`. E2's `a ∈
{½, 1}` is below both thresholds, and in fact `ℓ'' ≥ λ − α²/(2γ) = λ(1 − a²/2)`: globally strongly convex for `a² < 2`. Do not
claim "Morse everywhere" under `hdisc` (the `8/3` boundary has a degenerate critical point). Lean: denominator-cleared square
identities with `ring`, then sign lemmas; `sq_pos_of_ne_zero`/`mul_pos`; for C isolate `Qᵀ(w − c) = 0 → w = c` (square `Q`).

## Vote
- Claude: A+B+C (with GPT's two corrections)
- GPT-6 Astra: "yes to A+B+C, with A explicitly about the minimiser at `0`, and B separating the stationary-inflection boundary
  from the two-extra-extrema regime"

Adopted: `anharmonicPotential_two_minimisers` (equality case as two minimisers with `ℓ ≥ 0`), `anharmonic_inflection` (`ℓ' = ℓ'' = 0`
at `x*` when `α² = 8λγ/3`), `anhD2_ge` (the convexity bound), `rotatedHess_posDef` (Morse at `c` only); staging text uses the
open interval `8/3 < a² < 3`.
