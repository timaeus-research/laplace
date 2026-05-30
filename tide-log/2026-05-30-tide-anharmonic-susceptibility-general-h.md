# Tide: anharmonic susceptibility at general h (linear response)

**Direction (user):** Generalise the `κ₂` susceptibility to an arbitrary
perturbation point `|h₀|<1`: `∂_h⟨u⟩_h|_{h₀} = Var_{h₀}(u)`-style linear
response for `u = -(t x)`, the FDT at any `h`. Foundation for `κ₃` (which is
the second derivative of the mean, needing the mean's derivative as a
function).

**Seabed:** lean/laplace, commit ec8cac2 (main, post κ₂).
**Started:** 2026-05-30

## Seabed snapshot

- `weightedPartition_hasDerivAt n {|h₀|<1}`: HasDerivAt (G n) (G (n+1) h₀) h₀
  (general base point — exactly what general-h `HasDerivAt.div` needs).
- `integrable_weightedPartition_integrand n {|h₀|<1}`: integrability at any centre.
- `anharmonic_partition_pos`: positivity at `h=0` (template for general h).
- Mathlib `HasDerivAt.div`, `integral_pos_iff_support_of_nonneg_ae`.

## Candidate (agreed) — proceed-without-GPT

**A. General-h positivity.** `0 < weightedPartition … 0 h₀ = ∫ exp(-(t(L+h₀x)))`
for `|h₀|<1` — mirror `anharmonic_partition_pos` (integrand `>0` everywhere,
support `univ`, integrable via `integrable_weightedPartition_integrand 0`).
**B. General-h susceptibility.** `HasDerivAt (fun h => G_1 h/G_0 h)
((G_2(h₀)·G_0(h₀) − G_1(h₀)²)/G_0(h₀)²) h₀` for `|h₀|<1` — pointwise
`HasDerivAt.div` on the general-h partition derivatives. The `h₀=0` instance
is the previous tide's `κ₂` susceptibility.

**Proceed-without-GPT:** mechanical — a positivity proof mirroring an existing
one, plus one `HasDerivAt.div`. No new analytic content; FDT structure already
GPT-confirmed. No fresh consult adds value.

## Numerical check

Not feasible / not needed: structural (linear-response identity at a general
base point); the constituent `G_n(h₀)` integrals were validated in the
higher-deriv tide.

## Result

New file `Laplace/OneD/AnharmonicSusceptibilityGeneralH.lean`:
`partition_perturbed_pos` / `weightedPartition_zero_pos` (Z(h)>0 for |h|<1)
and `anharmonic_mean_hasDerivAt_general` (susceptibility at any |h₀|<1 via
general-h `HasDerivAt.div`). ~70 lines, first-try build, no sorries. The h₀=0
instance is the previous tide's κ₂.

## Retrospective

Retrospective: `retrospectives/2026-05-30-tide-anharmonic-susceptibility-general-h.tex`
