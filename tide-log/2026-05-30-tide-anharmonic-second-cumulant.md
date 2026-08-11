# Tide: anharmonic second cumulant / susceptibility

**Direction (user):** Next rung of the cumulant ladder (toward survey v4 #2):
the connected second cumulant `κ₂ = ⟨u²⟩₀ - ⟨u⟩₀²` of the perturbation
observable `u = -(t x)`, realised as the **susceptibility** — the derivative
of the perturbed mean `⟨u⟩_h = G_1(h)/G_0(h)` at `h=0`.

**Seabed:** lean/laplace, commit 17bd150 (main, post log-partition K'(0)).
**Started:** 2026-05-30

## Seabed snapshot

- `weightedPartition_hasDerivAt n {|h₀|<1}`: HasDerivAt (G n) (G (n+1) h₀) h₀
  (pointwise — exactly what `HasDerivAt.div` needs at `h₀=0`).
- `weightedPartition_zero_zero_pos`: `Z(0) = G_0(0) > 0`.
- `iteratedDeriv_partition_div_eq_gibbsExp n` + `iteratedDeriv_weightedPartition_zero`:
  `G_n(0)/G_0(0) = ⟨(-(t x))^n⟩₀` (moment-normalisation).
- Mathlib `HasDerivAt.div (hc) (hd) (d x ≠ 0) : HasDerivAt (c/d) ((c'·d x − c x·d')/d x²) x`.

## Candidate (agreed) — proceed-without-GPT

**A. Susceptibility.** `HasDerivAt (fun h => G_1 h / G_0 h)
((G_2(0)·G_0(0) − G_1(0)²)/G_0(0)²) 0` — pointwise `HasDerivAt.div` on
`weightedPartition_hasDerivAt 1` and `… 0` (the perturbed mean
`⟨u⟩_h = G_1(h)/G_0(h)`, so this is `∂_h⟨u⟩_h|_0`).
**B. Connected-variance form.** That derivative equals
`⟨u²⟩₀ − ⟨u⟩₀²` (`gibbsExp` of `(-(t x))²` minus the square of the
`gibbsExp` of `(-(t x))`), via moment-normalisation + `field_simp`/`ring`.

**Proceed-without-GPT:** mechanical — pointwise `HasDerivAt.div` plus a
`field_simp`/`ring` algebra identity, both on already-formalised lemmas; the
FDT/susceptibility relation `∂_h⟨u⟩ = Var` is standard. No fresh consult adds
value. (The `G_n(0)` integrals were numerically validated in the higher-deriv
tide; the FDT structure was GPT-confirmed in the FDT-capstone tide.)

## Numerical check

Not needed: `∂_h⟨u⟩_h|_0 = ⟨u²⟩₀ − ⟨u⟩₀²` is the standard
fluctuation–dissipation identity; here it is an algebraic consequence
(`field_simp`/`ring`) of moment-normalisation on already-validated integrals.

## Result

New file `Laplace/OneD/AnharmonicSecondCumulant.lean`:
`anharmonic_mean_hasDerivAt` (susceptibility = d/dh of the perturbed mean
G_1/G_0 at 0) and `anharmonic_susceptibility_eq_connected_variance`
(= ⟨u²⟩₀ - ⟨u⟩₀²). Pointwise `HasDerivAt.div` + explicit denominator
clearing (robust to field_simp drift). ~75 lines, no sorries.

## Retrospective

Retrospective: `retrospectives/2026-05-30-tide-anharmonic-second-cumulant.tex`
