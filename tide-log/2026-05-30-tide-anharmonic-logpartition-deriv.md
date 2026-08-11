# Tide: anharmonic log-partition first derivative (cumulant generating function)

**Direction (user):** Open the connected-cumulant direction of the anharmonic
partition arc: prove the first derivative of the cumulant generating function
`K(h) = log Z(h)` at `h=0`, `K'(0) = Z'(0)/Z(0) = ⟨-(t x)⟩₀`, the unperturbed
Gibbs mean of the perturbation observable. Survey v4 #2 (foundation step).

**Seabed:** lean/laplace, commit c06ea8f (main, post moment-normalisation).
**Started:** 2026-05-30

## Seabed snapshot

- `weightedPartition lam alpha gamma t n h = ∫ (-(t·x))^n · exp(-(t(L+h·x)))`;
  `Z = weightedPartition … 0`.
- `weightedPartition_hasDerivAt n {|h₀|<1}`: HasDerivAt (G n) (G (n+1) h₀) h₀.
- `anharmonic_partition_pos`: `0 < ∫ exp(-(t·L))`.
- `iteratedDeriv_partition_div_eq_gibbsExp n` (moment-normalisation):
  `iteratedDeriv n (wP 0) 0 / wP 0 0 = gibbsExp … 0 (fun x => (-(t·x))^n)`.
- `iteratedDeriv_weightedPartition_zero`: `iteratedDeriv n (wP 0) h = wP n h` (|h|<1).
- Mathlib `HasDerivAt.log (hf) (f x ≠ 0) : HasDerivAt (log∘f) (f'/f x) x`.

## Candidate (agreed) — proceed-without-GPT

**A. Helper.** `weightedPartition … 0 0 = ∫ exp(-(t·L))` (pow_zero) hence `> 0`.
**B. Main.** `HasDerivAt (fun h => log (wP 0 h)) (wP 1 0 / wP 0 0) 0` — the
CGF first derivative `K'(0)`, by `HasDerivAt.log` on `weightedPartition_hasDerivAt 0`.
**C. Corollary.** `deriv (fun h => log (wP 0 h)) 0 = gibbsExp … 0 (fun x => -(t·x))`
— `K'(0)` IS the unperturbed Gibbs mean of `-(t x)`, via moment-normalisation
(n=1) + `pow_one`.

**Proceed-without-GPT:** mechanical — one `HasDerivAt.log` application plus
definitional bridges to already-formalised lemmas; the underlying derivative
(`Z'(0) = G_1(0)`) was GPT-confirmed and numerically validated in the
higher-deriv tide. No fresh consult adds value.

## Numerical check

Not needed: `K'(0) = Z'(0)/Z(0)` is the quotient of two already-validated
integrals; the identity `= ⟨-(t x)⟩₀` is definitional (gibbsExp). The
`G_n(0)` integrals were numerically validated in the higher-deriv tide-log.

## Result

New file `Laplace/OneD/AnharmonicLogPartitionDeriv.lean`:
`weightedPartition_zero_zero_eq` / `_pos` (Z(0) = ∫exp(-tL) > 0),
`logPartition_hasDerivAt` (K'(0) = Z'(0)/Z(0)), and
`logPartition_deriv_eq_gibbsExp_mean` (K'(0) = ⟨-(t·x)⟩₀). ~70 lines,
first-try build, no sorries.

## Retrospective

Retrospective: `retrospectives/2026-05-30-tide-anharmonic-logpartition-deriv.tex`
