# Tide: grammar §4 fluctuation ladder lowering

**Direction (user):** continue on auto to autoformalise grammar. Unit 5 of §4 (ladder algebra).
**Seabed:** laplace, branch tide/grammar-fluctuation-ladder off tide/grammar-fluctuation-one.
**Started:** 2026-09-06

## Target (lem:oscillator_algebra, lowering)

`fluctuation_lowering` (λ>1/2): 2·S'_λ(a) − βa·S_λ(a) = (2λ−1)·S_{λ−1/2}(a).
(The β-power-free form of b·S_λ = (2λ−1)β^{-1/2}S_{λ-1/2}; the raising b†·S_λ = β^{1/2}S_{λ+1/2} is
already `deriv_fluctuation`.)

## Proof plan

Corollary of (i) + recurrence. deriv S_λ = β S_{λ+1/2} (deriv_fluctuation). Recurrence at λ'=λ-1/2
(needs λ>1/2): S_{λ+1/2} = (a/2)S_λ + ((λ-1/2)/β)S_{λ-1/2}. Substitute, field_simp+ring. No consult.

## Result
Committed on `tide/grammar-fluctuation-ladder`. Theorem: `fluctuation_lowering`. `lake build` green
(2751 jobs), sorries clean. Proven first-try: deriv_fluctuation + recurrence(λ-1/2) + field_simp/ring.
The β-power-free statement (multiply the paper's b-action through by β^{1/2}) avoids all rpow-on-β.
