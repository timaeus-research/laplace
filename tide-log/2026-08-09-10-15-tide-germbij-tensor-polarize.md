# Tide: germbij tensor programme J3 (multilinear polarization)

**Direction (user):** standing auto-mode commission on the germbij
note; stage J3 of the tensor programme (the scoping consult's
"genuinely new versus 1D" stage).
**Seabed:** laplace main at c3d1747 (J2 merged, PR #74).
**Started:** 2026-08-09T10:15 local

## Candidates

Target (scoping consult J3): a symmetric k-linear form is determined
by its diagonal — the bridge from the diagonal function Q (which J2's
rigidity recovers) to the Taylor tensor iteratedFDeriv ℝ k L 0
(which J6 must identify).

Mathlib survey findings (sent to the shape consult):

- NO polarization lemma exists (only QuadraticMap.polar and
  functional-analytic polar sets).
- `MultilinearMap.map_sum_finset` provides the expansion
  f(fun i ↦ Σ_{j ∈ A i} g i j) = Σ_{r ∈ piFinset A} f(fun i ↦ g i (r i)).
- **Regularity fork**: `ContDiffAt.iteratedFDeriv_comp_perm` (order-n
  symmetry of the iterated derivative) requires ANALYTIC (ω)
  regularity; for merely C^k, Mathlib has only order-2 symmetry.
  Options sent to consult: (a) assume analytic losses (germbij §5
  argues analyticity anyway), (b) prove C^k symmetry by induction,
  (c) state J3 abstractly with a symmetry hypothesis.

Candidate routes sent: subset-sum polarization
(k!·A(x₁..x_k) = Σ_{S⊆[k]} (−1)^{k−|S|} A(diag Σ_{i∈S} xᵢ)),
mixed directional derivatives, or slicker Mathlib routes if any.

## Numerical check

Executed before this log was written (k = 3, d = 3, random
symmetrized tensor, random arguments). Output quoted verbatim:

    k!A(x1,x2,x3) = 2.2151541896
    subset-sum    = 2.2151541896
    diff          = 8.88e-15

The subset-sum polarization identity holds to machine precision.

## Vote

(pending the shape consult — appended below when it lands)
