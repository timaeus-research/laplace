# Tide: localised-mean-1d

**Direction (user):** Just proceed on auto. You can bite off big chunks here to formalise and don't worry about retrospectives.
(Auto-mode continuation: the open reviewer caveat "eq:mean's localisation term for the anharmonic localised measure has not been
analysed", one dimension, leading order.)
**Seabed:** laplace, main 6f2b20a (local; GitHub seabed archived, patch to be exported)
**Started:** 2026-09-22 (UTC)

## Candidates v1 (Claude)

See `gpt_localised_mean_prompt_v1.md` (A–C verbatim): the localised mean as the ratio `⟨xφ⟩/⟨φ⟩` under the anharmonic Gibbs
measure with the bounded weight `φ = e^{g x₀ x − (g/2)x²}`; its expansion `|φ − 1 − g x₀ x| ≤ C₁x² + C₂x⁴`; odd absolute moments by
Young with `ε = t^{−1/2}`; the theorem `|t⟨x⟩_loc − (−α/(2λ²) + g x₀/λ)| ≤ K/√t`.

## Numerical check

`numcheck_localised_mean.py` (`λ = 1.3, α = 0.7, γ = 1.1, g = 0.8, x₀ = 0.6`): `t²(⟨x⟩_loc − eq:mean(S = (tλ + g)⁻¹)) → 0.047` and
`t^{3/2}(⟨x⟩_loc − lead) = 0.015, 0.011, 0.006, 0.003` at `t = 10, 40, 160, 640` (so the leading-order remainder is `O(t⁻²)`, better
than the `t^{−3/2}` the parity-free argument proves).

## GPT-6 Astra v1

Verbatim in `gpt_localised_mean_v1.md`. Summary: bounded reweighting is the right first route (the moving-minimum and
`d/dg` alternatives need uniformity the seabed lacks); require `g ≥ 0`; `φ = M e^{−g(x−x₀)²/2}` with `M = e^{g x₀²/2}`, so
`0 < φ ≤ M` and polynomial integrability transfers by domination. Expansion: the global `|e^y − 1 − y| ≤ ½ y² e^{max(y,0)}` gives
`|φ − 1 − ax| ≤ (g/2 + Ma²)x² + (Mg²/4)x⁴`; alternatively bounded `φ'' ` (`|φ''| ≤ 3gM`) gives `|φ − 1 − ax| ≤ (3/2)gM x²` and removes
the fifth/sixth-moment inputs. Weighted Young with `ε = t^{−1/2}` is sound (`⟨|x|³⟩ = O(t^{−3/2})`, `⟨|x|⁵⟩ = O(t^{−5/2})`); the
denominator estimate uses the signed mean bound. Main theorem: `|t⟨x⟩_loc − (−α/(2λ²) + g x₀/λ)| ≤ K/√t`, dividing with
`D ≥ ½`: `|tN/D − c| ≤ 2|tN − c| + 2|c||D − 1|`; call it a rate for the scaled mean, not a relative remainder (`c` can vanish).
Corollary in the note's notation: `|⟨x⟩_loc − P_t| ≤ K'/t^{3/2}` with `P_t = −αt/(2(tλ+g)²) + g x₀/(tλ+g)`. Scope: leading-order
certification only; narrow the reviewer caveat, do not remove it. Optional sharper follow-up via the integration-by-parts identity
`0 = λ⟨x⟩ + (α/2)⟨x²⟩ + (γ/6)⟨x³⟩` (so `⟨x³⟩ = O(t⁻²)`) and a second-order weight expansion, giving `K/t`.

## Vote
- Claude: A+B+C (elementary `C₁x² + C₂x⁴` expansion, since the seabed's even-moment rates are general in `k`)
- GPT-6 Astra: "YES on A+B+C" (prefers the `Cx²` bound if cheap; either is acceptable)

Adopted: elementary expansion with the sixth moment (no Taylor theorem needed); the `P_t` corollary if time permits; wording
"leading-order certification".
