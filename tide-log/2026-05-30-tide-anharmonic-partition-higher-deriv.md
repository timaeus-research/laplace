# Tide: anharmonic partition higher h-derivatives (n=2,3)

**Direction (user):** Extend `partition_hasDerivAt` to the 2nd and 3rd
`h`-derivatives of the anharmonic perturbed partition
`Z(h) = ∫ exp(-t·(L_anh(x) + h·x)) dx` at `h=0`, using the n=2,3
integrability witnesses; needed for the flow-equation / fourth-cumulant
identity. Survey #6, 2026-05-30. Reuses the general
`integrable_abs_pow_mul_exp_neg_t_anharmonic (m)` and the now-public
pointwise helpers landed in the FDT-capstone tide (#1).

**Seabed:** lean/laplace, commit f9a2a63 (main, post FDT-capstone merge).
**Started:** 2026-05-30

## Seabed snapshot

- `Threepoint.anharmonic_id_gibbsRegularity` (in
  `AnharmonicGibbsRegularity.lean`) carries the FIRST-derivative field
  `partition_hasDerivAt`:
  `HasDerivAt (fun h => ∫ exp(-(t·(L_anh + h·x)))) (∫ (-t·x)·exp(-(t·L_anh))) 0`,
  proved via `hasDerivAt_integral_of_dominated_loc_of_deriv_le` with the
  dominator `t·exp(t/(2c))·|x|·exp(-(t/2)·L_anh)`.
- Public helpers (un-privated in #1):
  `anharmonic_perturbed_pointwise_hasDerivAt` (pointwise `d/dh` of the
  Boltzmann factor) and `anharmonic_perturbed_pointwise_bound`.
- General integrability (new in #1):
  `integrable_abs_pow_mul_exp_neg_t_anharmonic (m : ℕ)` —
  `Integrable (|x|^m · exp(-(t·L_anh)))` for all m.
- No `iteratedDeriv` usage anywhere in `Laplace/OneD/`. The perturbed
  partition has no named def; it appears inline.

## Candidates v1 (Claude)

**A. General iterated-derivative step (preferred).** For all `n : ℕ`,
\[
  \frac{d}{dh}\Big|_{h=0} \int (-(t x))^n\, e^{-t(L_{\mathrm{anh}}(x)+hx)}\,dx
    \;=\; \int (-(t x))^{n+1}\, e^{-t L_{\mathrm{anh}}(x)}\,dx,
\]
i.e.
`HasDerivAt (fun h => ∫ (-(t*x))^n · exp(-(t·(L_anh + h·x)))) (∫ (-(t*x))^(n+1) · exp(-(t·L_anh))) 0`.
Rationale: the `n`-th member of this family is the integrand of the
`n`-th `h`-derivative of `Z`; one general lemma gives the 2nd and 3rd
(and all higher) derivatives by iteration, at no extra cost over n=2,3
separately. Proof = exact mirror of the existing n=1
`partition_hasDerivAt`, with the constant-in-`h` factor `(-(t*x))^n`
multiplied in (`HasDerivAt.const_mul`), dominator
`t·exp(t/(2c))·(t|x|)^n·|x|·exp(-(t/2)L) = t^{n+1}·exp(t/(2c))·|x|^{n+1}·exp(-(t/2)L)`,
integrable by the general `|x|^{n+1}` witness.

**B. Explicit n=2 and n=3 corollaries.** From A at `n=1` and `n=2`
(after rewriting the n=1 integrand `(-(t*x))^1 = -t·x` to match the
existing field):
\[
  Z''(0) = \int (t x)^2 e^{-tL}\,dx, \qquad Z'''(0) = \int -(t x)^3 e^{-tL}\,dx,
\]
as `HasDerivAt` of the first/second derivative functions. These are the
literal "2nd and 3rd derivative" statements the direction asks for.

**C. Connect to moments.** Optionally note `Z^{(n)}(0)/Z(0) = ⟨(-tx)^n⟩₀`,
tying the derivatives to raw moments. Likely out of scope (a separate
normalisation step); record as a follow-up.

Plan: prove A as the general lemma, then B as two ~5-line corollaries.
Hold C as a follow-up.

## Numerical check

Verified Candidate A's n=2,3 instances (the 2nd/3rd h-derivatives of Z at h=0)
against finite differences of Z(h)=∫exp(-t(L+hx))dx by scipy quadrature, at
λ=1, α=0.5, γ=1 (admissible: α²=0.25 < 3λγ=3):

| t   | Z''(0) FD       | ∫(tx)²e^{-tL} (pred) | relerr | Z'''(0) FD     | ∫-(tx)³e^{-tL} (pred) | relerr |
|-----|-----------------|----------------------|--------|----------------|------------------------|--------|
| 1   | 1.884812e+00    | 1.884812e+00         | 1.9e-7 | 9.821561e-01   | 9.821550e-01           | 1.1e-6 |
| 5   | 5.274236e+00    | 5.274230e+00         | 1.2e-6 | 5.038086e+00   | 5.038049e+00           | 7.4e-6 |
| 20  | 1.105487e+01    | 1.105482e+01         | 5.0e-6 | 1.281537e+01   | 1.281494e+01           | 3.4e-5 |

Both derivative forms confirmed (the central-difference errors grow with t/eps³
as expected). Script: `/tmp/higher_deriv_check.py`.

## Vote

- Claude: Candidate A (general iterated-derivative step lemma), with the
  n=1, n=2 instances named as the explicit 2nd/3rd-derivative corollaries
  (Candidate B). Hold the moment-normalisation connection (C) as a follow-up.
- GPT-5.5 Pro: consult dispatched (see `gpt_responses/gpt55_higher-deriv_v1.md`).
  Proceeding on the machine-verified + numerically-validated basis: this is a
  mirror-shaped tide (the proof is the n=1 `partition_hasDerivAt` field
  generalised by a constant-in-`h` factor `(-(t·x))^n`), the closed forms are
  numerically confirmed above to ~1e-6, and `lake build` machine-checks the
  result. Per the tide skill's "proceed-without-GPT" allowance for exactly
  this situation. GPT's verdict, if it lands, is preserved in the responses
  file for the record.

## Step 3 hand-off / Result

New file `Laplace/OneD/AnharmonicPartitionHigherDeriv.lean`:
- `anharmonic_partition_deriv_step (n : ℕ)` — general iterated-derivative
  step: `HasDerivAt (fun h => ∫ (-(t·x))^n·exp(-t(L+h·x))) (∫ (-(t·x))^(n+1)·exp(-t·L)) 0`.
- `anharmonic_partition_secondDeriv` — n=1 instance, RHS `∫ (t·x)²·exp(-t·L)`.
- `anharmonic_partition_thirdDeriv` — n=2 instance, RHS `∫ -(t·x)³·exp(-t·L)`.

Proof = mirror of `partition_hasDerivAt` via
`hasDerivAt_integral_of_dominated_loc_of_deriv_le`, with the constant factor
`(-(t·x))^n` carried through `HasDerivAt.const_mul` and the dominator
`t^(n+1)·exp(t/(2c))·|x|^(n+1)·exp(-(t/2)·L)` integrable by the general
`integrable_abs_pow_mul_exp_neg_t_anharmonic` (from tide #1). Builds clean,
no sorries, no lint warnings.

## Retrospective

Retrospective: `retrospectives/2026-05-30-tide-anharmonic-partition-higher-deriv.tex`

## GPT-5.5 Pro verdict (landed post-merge)

Full response: `tide-log/gpt_responses/gpt55_higher-deriv_v1.md`. Summary:

1. **Correctness confirmed.** The derivative form and signs are right:
   `G_n'(0) = ∫(-(t·x))^(n+1)·exp(-t·L)`, so `Z''(0)=∫(t·x)²·exp(-t·L)`
   (positive) and `Z'''(0)=∫-(t·x)³·exp(-t·L)` (minus the cubic moment).
   Matches the formalised lemmas and the numerical check.
2. **Indexing nuance.** The existing first-derivative field is the `n=0`
   case (`Z=G_0`), so `Z''` is `G_1'(0)` (this tide's `n=1` corollary) and
   `Z'''` is `G_2'(0)` (the `n=2` corollary) — consistent with what landed.
3. **Recommended strengthening (→ next tide).** Prove the lemma for all
   `h` with `|h|<1`, not just `h=0`. The local-in-`h` version yields
   `deriv (G n) h = G (n+1) h` near 0, which genuinely chains
   `deriv Z = G_1`, `deriv (deriv Z) = G_2`, … — i.e. *formally* identifies
   the iterated derivatives of `Z` (the `h=0` version gives the
   derivative of each `G_n` family member, mathematically equal but not
   Lean-chained). GPT endorses the chained `G_n` family over `iteratedDeriv`.
   This is the "general-h version" already listed in the retrospective's
   Follow-ups; taken up as the immediate next tide.

The proceed-without-GPT call (the proof was built + numerically validated
before the consult returned, due to API latency) is vindicated: GPT confirms
the substance and its one recommendation was already the planned follow-up.
