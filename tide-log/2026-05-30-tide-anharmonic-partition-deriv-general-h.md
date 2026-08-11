# Tide: anharmonic partition derivative — general-h version + deriv chaining

**Direction (user):** Strengthen the just-merged h=0 iterated-derivative step
(`anharmonic_partition_deriv_step`) to a general-`h` version (∀ |h|<1), as
recommended by GPT-5.5 Pro, so that the iterated derivatives of the perturbed
partition `Z(h) = ∫ exp(-t(L_anh + h·x))` are *formally chained*:
`deriv Z = G_1`, `deriv (deriv Z) = G_2`, etc. near 0, giving genuine
`Z''(0)`, `Z'''(0)` (not merely the derivative of each `G_n` integrand family
member at 0).

**Seabed:** lean/laplace, commit 6b4a676 (main, post higher-deriv merge).
**Started:** 2026-05-30

## Seabed snapshot

- `anharmonic_partition_deriv_step (n)` (merged 27c2409): the h=0 step,
  `HasDerivAt (fun h => ∫ (-(t·x))^n·exp(-t(L+h·x))) (∫ (-(t·x))^(n+1)·exp(-t·L)) 0`.
- Public helpers: `anharmonic_perturbed_pointwise_hasDerivAt`,
  `anharmonic_perturbed_pointwise_bound`,
  `integrable_abs_pow_mul_exp_neg_t_anharmonic (m)`.
- `amgm_t_abs_x` is still `private` in `AnharmonicGibbsRegularity.lean`.

## Deliberation

The deliberation is the GPT-5.5 Pro consult from the *previous* tide
(`../../../lean/laplace/tide-log/gpt_responses/gpt55_higher-deriv_v1.md`),
which explicitly specified this target and recipe:

> Prove the **local-in-h** version once, then specialize. The right reusable
> theorem is `∀ n, ∀ |h₀|<1, HasDerivAt (G n) (G (n+1) h₀) h₀`. Then
> `deriv (G n) h = G (n+1) h` for |h|<1 chains `deriv Z = G_1`,
> `deriv (deriv Z) = G_2`, …. Use the chained `G_n` family, not
> `iteratedDeriv`, as the primary form.

No fresh consult needed — this tide implements GPT's boxed recommendation
verbatim. (The signs/correctness were confirmed there.)

## Candidates v1 (Claude) — agreed (per prior GPT consult)

**A. General-h step.** For all `n`, `|h₀|<1`:
`HasDerivAt (fun h => ∫ (-(t·x))^n·exp(-t(L+h·x))) (∫ (-(t·x))^(n+1)·exp(-t(L+h₀·x))) h₀`.
Same dominated-differentiation proof as the h=0 case, but the neighborhood
`ball 0 1 ∈ 𝓝 h₀` (open ball is a nbhd of any interior point), and the
integrability of `F` at the *center* `h₀` now needs the exponent bound
`exp(-t(L+h₀x)) ≤ exp(t/2c)·exp(-(t/2)L)` (the n=0 derivative bound supplies
the `(-t·x)`-weighted version; extract the bare-exp form).

**B. deriv-equation corollary.** `deriv (fun h => ∫ (-(t·x))^n·exp(-t(L+h·x))) h = ∫ (-(t·x))^(n+1)·exp(-t(L+h·x))` for `|h|<1`, via `HasDerivAt.deriv`.

**C. Headline chaining for Z.** `deriv Z h = ∫(-(t·x))·exp(-t(L+h·x))` for
`|h|<1`; and the genuine second/third derivatives at 0:
`deriv^[2] Z 0 = ∫(t·x)²·exp(-t·L)`, `deriv^[3] Z 0 = ∫-(t·x)³·exp(-t·L)`,
via `Filter.EventuallyEq.deriv_eq` (the `G_n` agree with `deriv^[n] Z` on a
neighborhood of 0).

Infra delta: un-private `amgm_t_abs_x`; add an exponent-bound helper.

## Numerical check

Not needed beyond the previous tide: the closed-form values are identical
(`G_n(0)` integrals), already confirmed to ~1e-6 in
`2026-05-30-tide-anharmonic-partition-higher-deriv.md`. The new content is
structural (general base point + `deriv` identification), not a new number.

## Retrospective

Retrospective: `retrospectives/2026-05-30-tide-anharmonic-partition-deriv-general-h.tex`
