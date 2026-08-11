# Tide: germbij-pencil

**Direction (user):** formalise the germbij identifiability results (sri/local/germbij/germbij.tex). The target chain, in increasing difficulty: (1) the pencil identity e^{-tL1} - e^{-tL2} = t * integral_0^1 g e^{-tLs} ds with g = L2 - L1, Ls = (1-s)L1 + sL2 (Lemma 7.1); (2) the sector lower bound for int a^2 psi e^{-tK} with K >= 0 C^2 vanishing at p and a analytic with nonzero germ (Lemma 7.2); (3) the singular identifiability theorem (Theorem 7.3). Start minimal per the tide discipline; the pencil identity or a 1D version of the sector bound are natural first steps outward from the existing Laplace/Gibbs expectation material. Run autonomously.

**Seabed:** laplace, commit 4cd5e23 (main)
**Started:** 2026-08-08T19:11Z
**Worktree/branch:** laplace-tide-germbij-pencil / tide/germbij-pencil

## Seabed snapshot

Relevant existing material (signatures only, not proof bodies):

- `Laplace/Gibbs.lean`: `partitionFunction (L : R -> R) (t : R) : R := integral e^{-tL}`,
  `gibbsExpectation`, `gibbsCov`, basic algebraic identities. 1D, Lebesgue on R.
- `Laplace/ScalarBound.lean`: scalar exponential inequalities (`1 - z <= exp(-z)`,
  second/third-order bounds on `exp(-z) - 1 + z` etc.). The mean-value-flavoured
  machinery for comparing exponentials lives here.
- `Laplace/OneD/TailBound.lean`, `Localisation.lean`: Gaussian tail bounds, harmonic
  localisation (integrals over Ioi M, two-sided).
- `Laplace/OneD/Rescaling.lean`, `UniversalAsymptotics.lean`, `Quartic*.lean`,
  `Sextic.lean`: rescaled Laplace integrals for specific potentials, bounded-prior
  variants with test functions (`QuarticBoundedPriorTestFn.lean`).
- `Laplace/Multi/*`: multivariate covariance expansions (not needed for this tide).

Nothing in the seabed yet concerns *pairs* of potentials or lower bounds on
differences; this tide opens that direction. Mathematical source: the germbij note
(`sri/local/germbij/germbij.tex`), Lemma 7.1 (pencil identity), Lemma 7.2 (sector
bound), Theorem 7.3 (identifiability). The proofs there are elementary (FTC, Fubini,
an interval lower bound); the analytic-germ input enters only through a
finite-vanishing-order factorisation, which we take as a hypothesis in Lean.

## Candidates v1 (Claude)

**Candidate A (pencil identity, 1D).** Two parts.
(A1, pointwise; pure FTC, no measure theory):
for `L1 L2 : R -> R`, `t w : R`, writing `g = fun w => L2 w - L1 w`,
```
exp (-(t * L1 w)) - exp (-(t * L2 w))
  = t * intervalIntegral (fun s => g w * exp (-(t * (L1 w + s * g w)))) 0 1 volume
```
Proof: `s -> exp (-(t * (L1 w + s * g w)))` has derivative
`-(t * g w) * exp (...)`; apply `intervalIntegral.integral_deriv_eq_sub` and
rearrange. Rationale: the exact identity behind germbij Lemma 7.1; zero
infrastructure delta; closed form is the identity itself.
(A2, integrated; Fubini): for `phi : R -> R` with suitable hypotheses (continuous
with compact support, say, and `L1, L2` continuous), the integrated form
```
integral (fun w => phi w * (exp (-(t * L1 w)) - exp (-(t * L2 w))))
  = t * intervalIntegral (fun s => integral (fun w => g w * phi w * exp (-(t * (L1 w + s * g w))))) 0 1
```
Rationale: this is the form Theorem 7.3 uses. Risk: Fubini bookkeeping
(`MeasureTheory.integral_integral_swap`) needs an integrability hypothesis on
`(s, w) -> g w * phi w * exp (...)`; manageable with compact support + continuity.

**Candidate B (sector lower bound, 1D, factored hypotheses).** For
`K a : R -> R`, `m : N`, `c C0 r0 t : R` with `0 < c`, `0 <= C0`, `0 < r0`,
hypotheses on the interval `Icc 0 r0`: `0 <= K w <= C0 * w^2` and
`|a w| >= c * w^m` (this is what "analytic with nonzero germ, after shrinking and
choosing the good side" gives; we take it as a hypothesis), `4 <= r0^2 * t`. Then
```
integral over Icc (t^(-1/2)) (2 * t^(-1/2)) of (a w)^2 * exp (-(t * K w))
  >= c^2 * exp (-(4 * C0)) * t^(-(m : R) - 1/2)
```
Proof: on the interval, `t * K w <= t * C0 * (2 t^{-1/2})^2 = 4 C0`,
`(a w)^2 >= c^2 * w^(2m) >= c^2 * t^(-m)`, interval length `t^(-1/2)`; conclude by
`setIntegral` monotonicity against the constant lower bound. Rationale: the 1D case
of germbij Lemma 7.2 with the analytic input factored out; elementary; explicit
constant.

**Candidate C (composite: the identifiability lower bound, 1D).** Assuming A2 and B:
for `L1 L2 >= 0` with `L1 + L2 <= C0 w^2` on `Icc (-r0) r0`, `g = L2 - L1` with
`|g w| >= c * w^m` on `Icc 0 r0`, `psi` a nonneg bump `= 1` on `Icc (-r0) r0`:
```
integral (fun w => g w * psi w * (exp (-(t * L1 w)) - exp (-(t * L2 w))))
  >= c^2 * exp (-(4 * C0)) * t^(1 - (m : R) - 1/2)   for large t
```
i.e. the quantity the germbij Theorem 7.3 contradiction runs on. Rationale: the
headline-shaped statement; but it needs both A2 and B plus `exp (-(t*Ls)) >=
exp (-(t*(L1+L2)))` glue, so it is a full program, not a minimal step.

My assessment: A1 + B are each minimal and independently valuable; A2 is the
riskiest single piece (Fubini hypotheses); C is out of scope for one tide. I lean
toward **A (A1 with A2 attempted, falling back to A1 + the e^{-tLs} >= e^{-t(L1+L2)}
comparison lemma if Fubini fights)** as the tide target, with B as the natural next
tide.

## Numerical check

Pencil identity (A2) verified numerically in `sri/local/germbij/check_pencil.py`
during the note's drafting: for L1 = w^4, g = w^6, phi a Gaussian bump, t = 200,
lhs = 7.029636537452e-03 vs rhs = 7.029636537412e-03 (rel err 5.6e-12).
Sector bound (B): at t = 100, K = w^2 (C0 = 1), a = w^2 (m = 2, c = 1), r0 = 1:
integral_{0.1}^{0.2} w^4 e^{-100 w^2} dw = 4.606e-06 >= e^{-4} * 100^{-2.5}
= 1.832e-07. Checked by quadrature (scipy), holds with margin ~25.1x.

## GPT-5.6 Sol v1

Saved verbatim: `gpt55_germbij-pencil_v1.md` (same directory). Operational note:
the consult hung for ~5.5 hours on a network read (known failure mode of the
query helper) before completing; the formalisation of candidate A was carried
out while it ran. A leaner re-ask launched just before the original returned is
saved as `gpt55_germbij-pencil_v2.md`; the two responses agree.

Verdict summary: A1 correct as stated (no regularity needed); A2 correct under
the explicit joint-integrability hypothesis (exactly as formalised); B correct
including the constant c^2 e^{-4C0} t^{-m-1/2} and side condition 4 <= r0^2 t,
but should carry measurability/continuity hypotheses when formalised, and its
Lean cost is higher than it looks (rpow/sqrt bookkeeping, set-integral
monotonicity). Proposed 7-step chain toward Theorem 7.3 recorded in the saved
response; its step 4 (convex-pencil comparison) and step 3 (integrated identity
under direct product integrability) match what was built.

## Vote

- Claude: candidate A (A1 + A2, with the comparison lemma as glue).
- GPT-5.6 Sol: candidate A1, stated scalar-first with the functional version
  as a corollary.

Agreed candidate: A1. Micro-divergence on scope: A2, the comparison lemma
`exp_pencil_ge`, and the `partitionFunction` corollary were already proven
during the deliberation window and are included; GPT's scalar-first
architecture was adopted in a refactor (`exp_sub_exp_pencil` is now the root
statement, `exp_pencil_identity` a one-line corollary).

## Step 3 hand-off

File: `Laplace/Pencil.lean` (new module, registered in `Laplace.lean`).
Declarations, all sorry-free:
- `Laplace.exp_sub_exp_pencil` (scalar pencil identity, FTC)
- `Laplace.exp_pencil_identity` (pointwise, corollary)
- `Laplace.pencil_identity_integrated` (Fubini form, explicit
  product-integrability hypothesis)
- `Laplace.exp_pencil_ge` (comparison along the pencil, positivity input)
- `Laplace.partitionFunction_pencil` (phi = 1 specialisation, in terms of
  the seabed's partitionFunction)

## Result

Full `lake build` passes (8283 jobs); `scripts/sorries` reports 0/0/0/0.
Surprises: (i) the whole chain went through on essentially the first attempt;
the only real friction was hypothesis transport under `Function.uncurry`,
which wants an explicit `funext` equality rather than `simpa [one_mul]`.
(ii) `MeasureTheory.intervalIntegral_integral_swap` matches the needed Fubini
form exactly, including the `uIoc` restriction, so no new integration
infrastructure was required. Committed on branch tide/germbij-pencil (merge SHA recorded in the active-tides ledger at release).

## Retrospective

Retrospective: laplace/retrospectives/2026-08-08-19-11-tide-germbij-pencil.tex
