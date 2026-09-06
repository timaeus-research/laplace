# Tide: monomial-moment-asymptotic

**Direction (user):** Continue with what you think best (auto). Second laplace tide; the Explore
survey's top remaining pick — the missing 1D base that the 2D moment lift assumed.
**Seabed:** laplace, commit 57df415 (branch base)
**Started:** 2026-09-06

## Candidate

The 1D even-monomial Gibbs-moment asymptotic: `⟨x^(2j)⟩_t ~[atTop] C(k,j)·t^(-j/k)` against
`exp(-t·x^(2k)/(2k)!)`. Confirmed genuinely missing (grep: no 1D moment `isEquivalent` existed);
`TwoD/KthKthMomentAsymptotic` had the 2D lift with the four-step pattern but no standalone 1D base.

## Numerical / structural check

The even moment is EXACTLY `C(k,j)·t^(-j/k)` for every `t>0` (from
`gibbsExpectation_kthPotential_even` + `Real.div_rpow`), so the equivalence is eventual (indeed
pointwise for t>0) equality — no genuine asymptotics content beyond the closed form. Not feasible /
needed as a numeric quad check.

## Result

Four theorems in `Laplace/OneD/MonomialMomentAsymptotic.lean`, single-factor mirror of the 2D
`KthKth` trio: `kthMomentConst` (the prefactor `(2k)!^(j/k)·Γ((2j+1)/(2k))/Γ(1/(2k))`),
`gibbsExpectation_kthPotential_even_eq_const_mul_rpow` (exact `const·t^(-j/k)`),
`_rescaled_tendsto` (× `t^(j/k)` → `C` at atTop), `_isEquivalent_rpow` (`~[atTop]` the power law).
Zero-sorry, full build clean (8884 jobs). Proof mirrors `KthKthMomentAsymptotic` verbatim with one
factor: `Real.div_rpow`+`Real.rpow_neg`+`ring` for the closed form; `eventually_gt_atTop`+`rpow_add`+
`add_neg_cancel`+`rpow_zero` for the tendsto; `IsEquivalent.refl.congr_left` for the equivalence.
Compiled on the first attempt. No GPT.

This is the missing 1D base of `KthKthMomentAsymptotic`; a natural follow-up is to retro-fit that 2D
file (and QuarticSextic) to cite this base rather than re-deriving inline.
