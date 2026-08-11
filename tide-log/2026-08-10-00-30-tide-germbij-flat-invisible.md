# Tide: germbij-flat-invisible

**Direction (user):** the germbij note's Proposition 4.1 quantitative
core (auto mode, standing delegation): a flat nonnegative perturbation
of the harmonic potential changes the compactly-supported-observable
integrals by o(t^-infty) — the analyticity-necessity half of the note's
story, and the exact counterpoint to Theorem 7.3 (whose sector bound
needs the finite vanishing order that flatness destroys).

**Seabed:** laplace, main at bd0f4a8 (gamma programme complete).
Scoping insight: no expansion theory needed — the pointwise identity
e^{-tL} - e^{-t(L+f)} = e^{-tL}(1 - e^{-tf}) with 1 - e^{-tf} <= tf,
plus a GLOBAL polynomial domination of f (flatness near 0, boundedness
absorbed polynomially via M(x/delta)^{2N+2} >= M off the flat
neighborhood), reduces everything to one closed-form Gaussian moment.
**Worktree/branch:** laplace-tide-germbij-flat-invisible /
tide/germbij-flat-invisible
**Started:** 2026-08-10T00:30Z

## Candidate v1 (Claude)

flat_perturbation_invisible: f continuous, 0 <= f <= M, flat at 0
(∀ n, ∃ C >= 0, δ > 0: |x| <= δ → f x <= C x^{2n}); φ continuous with
compact support. Then ∀ N, ∃ K T: ∀ t >= T,
|∫φ e^{-t x²/2} − ∫φ e^{-t(x²/2 + f)}| <= K / t^N.
(Optional second declaration: the classic witness e^{-1/x²} satisfies
the hypotheses, via s^n/n! <= e^s.)

## Numerical check

Run before the consult (scipy; f = e^{-1/x²}, φ = max(0, 1-x²)):
|diff| at t = 20, 80, 320: 8.4e-3, 5.1e-5, 4.2e-10; diff·t³:
67 → 26 → 0.014; diff·t⁵: 2.7e4 → 1.7e5 → 1.4e3 (collapse after
onset). Superpolynomial decay confirmed.

## GPT-5.6 Sol v1

Saved verbatim: `tide-log/gpt56_germbij_flat_invisible_v1.md`.
Summary: endorses the statement exactly as drafted — even-power
flatness hypothesis (composes with the Gaussian moment lemmas, no
rpow leakage), T = 1 suffices, all-orders K/t^N is the right
quantitative core with the IsLittleO packaging as a short corollary in
the Laplace.Decay vocabulary. Endorses the file name
Laplace/OneD/FlatInvisible.lean. Suggests (optionally) isolating three
helpers (sup-bound for continuous compactly supported functions,
local-to-global even-power domination, moment-to-plain-pow wrapper) and
deferring the e^{-1/x²} witness to a follow-up declaration. Confirms
the witness route via s^n/n! <= e^s with C = n! and any δ.

## Vote

- Claude: flat_perturbation_invisible as drafted (monolithic proof;
  helpers inline since each is used once), plus the Decay-vocabulary
  corollary GPT recommended.
- GPT-5.6 Sol: same candidate, same file.

Agreed. The e^{-1/x²} witness is deferred to a possible follow-up tide.

## Result

- Theorems: `flat_perturbation_invisible` (∀ N, ∃ K T, |∫φe^{-tx²/2} −
  ∫φe^{-t(x²/2+f)}| ≤ K/t^N for t ≥ T) and
  `flat_perturbation_superpolynomial` (the same difference is
  =o[atTop] t^(-N) for every N — the exact hypothesis shape that
  `lower_bound_not_superpolynomial` in Laplace/Decay.lean refutes for
  analytic pencils, here satisfied by a flat perturbation).
- File: Laplace/OneD/FlatInvisible.lean (~260 lines). Zero sorries.
- Surprises: (1) `open scoped Nat` (wanted for the ‼ notation) broke
  the theorem binder `{f φ : ℝ → ℝ}` — the Nat scope defines `φ` as
  notation for Nat.totient, so the binder no longer parses. Fix: spell
  out Nat.doubleFactorial and skip the scoped open. New error-catalogue
  entry. (2) The seabed's integrability lemma is
  `integrable_pow_mul_exp_neg_mul_sq` at c = t/2 (not the guessed
  kth_integrable_pow); a one-line ring-congr bridges -(t/2·x²) to
  -(t·x²)/2. (3) The corollary's rpow bookkeeping (npow/rpow bridge +
  ratio-to-t⁻¹) went through first try with isLittleO_iff_tendsto'.
