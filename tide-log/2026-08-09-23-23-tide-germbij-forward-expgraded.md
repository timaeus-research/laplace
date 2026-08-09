# Tide: germbij forward programme stage 4 (ExpGraded)

**Direction (user):** "Yes continue with germbij, and do not switch into
another seabed. Consult with 5.6 Sol to make sure there aren't higher
value targets for autoformalisation remaining, the main core concern
being the recovery of all coefficients in the nondegenerate case and
the main theorem in the nondegenerate case. The quasi-homogeneous case
and other examples are less crucial."

**Seabed:** laplace, branch tide/germbij-forward-domain at b71bc71
(stacked; stage A3 in PR #98). Design consult archived as
`tide-log/gpt56_forwardA_shape_v1.md` (stage-1 tide).

**Started:** 2026-08-09T23:23Z

## Candidates (per the design consult, section 2-3)

Stage 4 of the forward programme: the graded expansion of the
exponential correction factor. Scalar level only (function-valued /
mesoscopic quantitative form is stage 5 work, per the consult's own
remark that the quantitative lemma is easier stated there).

1. `gradedExpPoly a N : Polynomial ℝ` — the collection mechanism —
   and `expCorrectionCoeff a N j` as its coefficients, with
   `expCorrectionCoeff_zero = 1`.
2. `exp_graded_expansion`: for `ρ → 0` at `0⁺`,
   `exp(-(Σ_{s∈Icc 1 N} q^s a_s + q^N ρ_q)) - Σ_{j∈range(N+1)} q^j c_j
   = o(q^N)` at `0⁺`.

## Deviation from the consult's internal design (noted)

The consult prescribed the log-derivative recursion
`P_j = -(1/j) Σ s V_s P_{j-s}` as the internal collection mechanism,
while itself noting "The proof may use the ordinary Taylor remainder
for `Real.exp`. The recursive coefficients are only the collection
mechanism." We substitute a cheaper collection mechanism with the same
interface: `gradedExpPoly a N := Σ_{i∈range(N+1)} C((-1)^i/i!) ·
(Σ_{s∈Icc 1 N} C(a_s)·X^s)^i` — exp's Taylor truncation composed with
the exponent polynomial — and take coefficients of that. The little-o
proof then needs no coefficient identities at all: (I) strip `ρ` via
`|e^x - 1| ≤ 2|x|`; (II) exp's Taylor remainder at `x = -A(q)` with
`|A(q)| ≤ q·Σ|a_s|` for `q ≤ 1`; (III) the polynomial tail above
degree `N` carries `q^{N+1}`. Measurability and polynomial growth in
`z` (needed at stage 5) follow by induction on `i` through
`Polynomial.coeff_mul`, replacing the recursion induction. Public API
unchanged. If stage 5's growth bounds resist this route, revisit with
a fresh consult.

## Numerical check

Feasible and done before writing Lean: N=3, a=(0.7, -0.3, 0.2),
ρ_q = q^0.5. Compare exp(-(Σ q^s a_s + q^3 ρ)) against
Σ_{j≤3} q^j·coeff_j(gradedExpPoly) at q = 10^-1..10^-4 and check the
difference scales below q^3. (Executed in the scratchpad; see Result.)
