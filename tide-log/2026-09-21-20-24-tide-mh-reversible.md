# Tide: mh-reversible

**Direction (user):** auto mode ("Just proceed on auto. You can bite off big chunks here to formalise and don't worry about retrospectives"); this tide chosen by the agent: reversibility of the Metropolis–Hastings kernel, completing the Metropolis arc (tides `mala-invariance`, `mala-kernel`).
**Seabed:** laplace, main after `autocorrelation-time` (c03b14e)
**Started:** 2026-09-21 (UTC, see filename)

## Context

The sanity note's Setup: "the reference is MALA preconditioned by `P⁻¹` (pMALA) … The preconditioner only shapes proposals; the accept–reject
step makes the stationary law exact regardless." Tides `mala-invariance` and `mala-kernel` formalised the invariance (`mh_invariant`,
`mh_invariant_law`, the Markov kernel `mhKernel` with `bind_mhKernel`) from the pointwise detailed balance `mh_detailed_balance` and the
symmetric accepted flux `mhFlux_comm`. The textbook reason the accept–reject step works is *reversibility*: the joint law `π(dx) K(x, dy)` is
symmetric, `∫_A K(x, B) π(dx) = ∫_B K(x, A) π(dx)`, of which invariance is the case `A = X`. This tide proves that, at the level of the
seabed's `mhKernelSet`/`mhKernel`, for the unnormalised target and for the probability law, with the MALA and pMALA instances.

## Candidates v1 (Claude)

With the seabed's standing hypotheses (`π, q > 0` measurable, `∫ q(x, ·) dμ = Z ∈ (0, ∞)`), `K(x, E) = mhKernelSet π q μ Z x E =
(1/Z)∫_E q(x,y) α(x,y) dμ(y) + 1_E(x)(1 − a(x))`:

**A. Decomposition of the rectangle mass.** For measurable `A, B`,
```
∫⁻ x in A, π(x) K(x, B) dμ = Z⁻¹ ∫⁻ x in A, ∫⁻ y in B, flux(x, y) dμ dμ + ∫⁻ x in A ∩ B, π(x)(1 − a(x)) dμ
```
with `flux(x, y) = min(π(x) q(x,y), π(y) q(y,x))` (`mhFlux`).

**B. Reversibility for the unnormalised target** (`mh_reversible`):
```
∫⁻ x in A, π(x) K(x, B) dμ = ∫⁻ x in B, π(x) K(x, A) dμ
```
(Tonelli on the restricted measures + `mhFlux_comm`; the rejection term is symmetric because `A ∩ B = B ∩ A`).

**C. Reversibility for the probability law and the kernel** (`mh_reversible_law`, `mhKernel_reversible`):
```
∫⁻ x in A, K(x, B) ∂(mhTargetLaw π μ T) = ∫⁻ x in B, K(x, A) ∂(mhTargetLaw π μ T)
∫⁻ x in A, mhKernel … x B ∂ν = ∫⁻ x in B, mhKernel … x A ∂ν
```
and the MALA / pMALA instances (`mala_reversible`, `pmala_reversible`, and their `_law` forms). Invariance is recovered as `A = univ`
(`mh_invariant_of_reversible`, a one-line corollary, as a consistency check against `mh_invariant`).

**D. (Optional) The symmetric joint law.** `(ν ⊗ₘ K).map Prod.swap = ν ⊗ₘ K` as measures on `X × X` — needs the π-system/rectangle
extensionality for the product σ-algebra; propose to leave as a follow-up unless Mathlib's `Measure.ext_of_generateFrom_of_iUnion`-style
API makes it a short step.

Vote intention: A+B+C.

## Numerical check

`numcheck36.py`: MALA on the 1D Gaussian target `exp(−x²/2)` with proposal `N(x − hx, 2h)`, `h = 0.3`, on a grid of 1601 points on `[−8, 8]`:
```
A=[-1,0.5] B=[0.2,2]: int_A K(x,B) pi = 0.439121   int_B K(x,A) pi = 0.439121   rel diff = 3.79e-16
A=[-3,-1] B=[1,3]: int_A K(x,B) pi = 0.002319   int_B K(x,A) pi = 0.002319   rel diff = 7.48e-16
A=[-0.5,0.5] B=[-2,2]: int_A K(x,B) pi = 0.960587   int_B K(x,A) pi = 0.960587   rel diff = 1.16e-16
flux symmetry max |pi q alpha - (pi q alpha)^T| = 1.1102230246251565e-16
```
The rectangle masses agree to rounding, including overlapping `A, B` (where the rejection term contributes).

## GPT-6 Astra v1

Saved verbatim in `tide-log/gpt_mh_reversible_v1.md`. Summary: A–C correct under the standing measurability and `SFinite μ` (needed by Tonelli; supplied by the seabed's section variable); C needs `0 < T < ∞` and, for the probability reading, `T = ∫ π dμ`. "Reversibility" is the standard name for the rectangle identity, and for finite joint measures it is equivalent to the symmetric joint law D (rectangles form a generating π-system; no standard-Borel assumption). Lean: instantiate Tonelli on `μ.restrict A`, `μ.restrict B` (restrictions inherit `SFinite`; give the measures explicitly), `Measure.restrict_restrict hB` for the rejection term, restriction through `withDensity` for the law version with typed measurability facts. D: 20–50 lines if a rectangle-extensionality helper exists, substantially more otherwise — a short exploratory attempt at most; self-adjointness on `L²` deferred (after D it is Fubini on bounded functions).

## Vote
- Claude: A+B+C (D only if the rectangle extensionality is at hand — recorded as a follow-up)
- GPT-6 Astra: A+B+C

Agreed. Proceeding to Step 3.

## Result

Committed on `tide/mh-reversible` at b553fc5 (`lake build` clean, `scripts/sorries`: 0 sorry, 0 axiom, 0 native_decide). New module `Laplace/Sampler/MetropolisReversible.lean` (214 lines): `mh_rectangle_mass`, `mh_reversible`, `mh_invariant_of_reversible`, `mh_reversible_law`, `mhKernel_reversible`, `mhKernel_compProd_swap`, `mala_reversible`, `mala_reversible_law`, `pmala_reversible`, `pmala_reversible_law`.

Surprises: (i) the optional joint-law symmetry (D) went through in a dozen lines with `ext_of_generate_finite`, `generateFrom_prod`, `isPiSystem_prod` and `Measure.compProd_apply_prod` — the rectangle extensionality for finite measures is exactly what Mathlib provides; (ii) `lintegral_lintegral_swap` inside `rw` leaves the measures as metavariables and the `SFinite` search sticks — a typed `have` with explicit measures fixes it; (iii) the `⊗ₘ` notation is scoped to `ProbabilityTheory`.
