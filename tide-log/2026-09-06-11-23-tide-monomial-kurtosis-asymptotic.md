# Tide: monomial-kurtosis-asymptotic

**Direction (user):** Continue with what you think best (auto). Third laplace tide; the clean
spin-off flagged in memory — the excess-kurtosis t^(-2/k) asymptotic scaling.
**Seabed:** laplace, commit 5eb62c1 (branch base)
**Started:** 2026-09-06

## Candidate

The asymptotic scaling of the excess kurtosis landed earlier (`monomial_excess_kurtosis`):
`⟨x⁴⟩ − 3⟨x²⟩² ~[atTop] K(k)·t^(-2/k)`. Since the excess kurtosis is a DIFFERENCE of two even
moments that share the common power `((2k)!/t)^(2/k)`, it is *exactly* `K(k)·t^(-2/k)` for all
`t>0` — so the same 4-step lift pattern (closed form → const·t^(-...) → rescaled tendsto →
IsEquivalent) applies directly, extending `MonomialKurtosis.lean`.

## Numerical / structural check

Exactly `K(k)·t^(-2/k)` for every t>0 (from `monomial_excess_kurtosis` + `Real.div_rpow`); at k=1
`K(1)=0` (Gaussian), the trivial power law. No quad check needed.

## Result

Three theorems added to `Laplace/OneD/MonomialKurtosis.lean`: `kurtosisConst`,
`monomial_excess_kurtosis_eq_const_mul_rpow`, `_rescaled_tendsto`, `_isEquivalent_rpow`. Zero-sorry,
full build clean (8884 jobs). Mirrors `MonomialMomentAsymptotic` (single power `2/k`):
`Real.div_rpow`+`Real.rpow_neg`+`ring` for the closed form; `rpow_add`+`add_neg_cancel`+`rpow_zero`
for the tendsto; `IsEquivalent.refl.congr_left` for the equivalence. Compiled first try.
★ ONE gotcha: the `linter.style.header` "Copyright too short!" warning fired on fresh elaboration
because the file's copyright block lacked an `Authors:` line — added `Authors: Timaeus` (Mathlib-standard
form) to silence it (most sibling files predate the linter and carry the warning latent). No GPT.
