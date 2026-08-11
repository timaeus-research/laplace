# Tide: germbij-sector-multi

**Direction (user):** continuation of the germbij arc in auto mode: the
multivariate sector lower bound (germbij Lemma 7.2 in R^d), toward the full
d-dimensional Theorem 7.3.

**Seabed:** laplace, main at 24503a2 (contains the full 1D germbij arc:
Laplace/Pencil.lean, Laplace/Sector.lean, Laplace/Identifiability.lean).
**Started:** 2026-08-09T01:55Z (prefix chosen to sort after the previous
tide's; wall clock a few minutes earlier)
**Worktree/branch:** laplace-tide-germbij-sector-multi /
tide/germbij-sector-multi

## Seabed snapshot

The 1D arc as merged. The 1D sector bound integrates over the interval window
[u, 2u]; the d-dimensional statement in the germbij note integrates over a
spherical-cap sector. Key design idea for Lean: replace the spherical cap by a
*scaled set*: a measurable S inside the (sup-norm) unit annulus
{1 <= ||x|| <= 2} with 0 < vol S < infinity, windows u . S (pointwise smul),
and the volume scaling law vol(u . S) = u^d vol(S)
(`MeasureTheory.Measure.addHaar_smul` on `iota -> R`; `finrank R (iota -> R)
= Fintype.card iota`). This avoids sphere measure and polar coordinates
entirely; the analytic input (a nonvanishing leading homogeneous part on a
cap, giving |a(u . x)| >= c u^m for x in S and small u) is factored into a
hypothesis exactly as in the 1D tide.

## Candidates v1 (Claude)

**Candidate A (window lemma, direct hypotheses).** On `iota -> R` (Fintype),
S measurable, vol S nonzero and finite, u > 0:
hypotheses `ha : forall x in S, c * u^m <= |a (u . x)|`,
`hK : forall x in S, K (u . x) <= 4 * (C0 * u^2)`, integrand integrable on
u . S. Conclusion:
```
(volume S).toReal * u ^ (Fintype.card iota)
    * (c^2 * u^(2*m) * Real.exp (-(4 * (C0 * (t * u^2)))))
  <= integral over (u . S) of (a w)^2 * Real.exp (-(t * K w))
```
Wait: hK should bound K itself, with the t-multiplication downstream; fix in
the Lean statement: `hK : forall x in S, t * K (u . x) <= 4 * (C0 * (t * u^2))`
or keep K-level bound and require `ht : 0 <= t`. Rationale: minimal, the
scaling law is the only new ingredient.

**Candidate B (Laplace-scale corollary, annulus form).** With
`hSnorm : S subset {x | 1 <= ||x|| and ||x|| <= 2}`,
`hK : forall w, ||w|| <= r0 -> K w <= C0 * ||w||^2`,
`ha` at the single scale u = (sqrt t)^{-1}, `hrt : 4 <= r0^2 * t`:
```
(volume S).toReal * (c^2 * Real.exp (-(4*C0))
    * t ^ (-(m : R) - (Fintype.card iota : R) / 2))
  <= integral over ((sqrt t)^{-1} . S) of (a w)^2 * Real.exp (-(t * K w))
```
Rationale: the exact d-dimensional analogue of the 1D `sector_lower_bound`,
specialising to it (up to the vol factor) at d = 1, S = [1,2].

Both in one file `Laplace/Multi/Sector.lean`; A is the engine, B the
packaged form. This mirrors the 1D tide's window/corollary split, which the
prior deliberation endorsed (its steps 5-6).

## Numerical check

d = 2, S = [1,2]^2 (inside the sup-norm annulus), a(w) = w1 w2 (m = 2, c = 1
at scale u: |a(u x)| = u^2 |x1 x2| >= u^2 on S), K(w) = w1^2 + w2^2
(C0 = 2 in sup norm), t = 100, u = 0.1: window integral over [0.1,0.2]^2 of
(w1 w2)^2 e^{-100(w1^2+w2^2)} = 5.441e-08 >= vol(S) * c^2 * e^{-8} *
100^{-3} = 3.355e-10 (margin ~162x, scipy dblquad).

## GPT-5.6 Sol v1

(consult launched; response saved as gpt55_germbij-sector-multi_v1.md when it
returns; per the arc's precedent the formalisation proceeds concurrently and
integrates corrections on arrival)

## GPT-5.6 Sol v1 (returned)

Saved verbatim: `gpt55_germbij-sector-multi_v1.md`. Verdict: A and B correct
including the u^d volume factor and the exponent -(m) - d/2; the scaled-set
model "faithfully captures the spherical-cap argument"; repairs requested
(positivity hypotheses, integrability, t > 0, guard against negative r0) were
all already present in the draft statements (0 < r0 is a hypothesis; t > 0 is
derived). VOTE: A (with B as corollary).

## Vote

- Claude: A + B in one file (window engine + Laplace-scale corollary),
  mirroring the 1D tide split.
- GPT-5.6 Sol: A, with B as corollary.

Agreed: A (B included as its corollary).

## Result

`Laplace/Multi/Sector.lean`, registered in `Laplace.lean`. Declarations,
sorry-free:
- `Laplace.sector_window_lower_bound_multi`
- `Laplace.sector_lower_bound_multi`

Full `lake build` passes; `scripts/sorries` 0/0/0/0. Three compile fixes:
`open Pointwise` needed for the set-smul notation `u • S`; one staged
nlinarith hint (`hx4 : ||x||^2 <= 4` first, then the product hint); the
window lemma's `hC0` was unused (the packaged `hK` bound absorbs it) and was
dropped, as in the 1D tide. `Measure.addHaar_smul` +
`Module.finrank_pi` gave the volume scaling with no friction;
`MeasurableSet.const_smul_of_ne_zero` the measurability.

## Retrospective

Retrospective: laplace/retrospectives/2026-08-09-01-55-tide-germbij-sector-multi.tex
