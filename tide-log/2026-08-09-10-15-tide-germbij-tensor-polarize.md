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

## Shape consult

Archived verbatim: `tide-log/gpt56_j3_shape_v1.md`. Rulings adopted:
(1) the REGULARITY FORK resolves to option (c): polarization is
algebraic — state it for `ContinuousMultilinearMap` with a pointwise
`IsSymm` hypothesis (∀ σ v, A (v ∘ σ) = A v), and provide an
ω-regularity convenience wrapper via
`ContDiffAt.iteratedFDeriv_comp_perm`; proving C^k symmetry is a
separate library project, not a J3 prerequisite. (Caveat noted:
ContDiff ℝ ω is smoothness in Mathlib's grading here — analyticity
implies it.) (2) Subset-sum proof skeleton: expand diagonals with
`MultilinearMap.map_sum_finset` over `Fintype.piFinset (fun _ ↦ S)`,
extend to all r with an ite, swap with `Finset.sum_comm`, compute the
coefficient by a LOCAL alternating-supersets lemma (reindex supersets
of R as R ∪ T with T ⊆ Rᶜ, reduce to Σ_{T⊆D}(-1)^|T| by finset
induction — do NOT hunt for a one-shot Mathlib alternating-powerset
theorem), keep bijective r via image = univ ↔ surjective ↔ bijective
(`Finite.injective_iff_surjective`), convert with `Equiv.ofBijective`
and count with `Fintype.card_perm`. (3) No slicker route exists in
Mathlib (mkPiRing/divided powers cost more; mixed directional
derivatives are polarization plus more differentiability API).
(4) Public API: `IsSymm`, `eq_zero_of_diag_eq_zero`, `eq_of_diag_eq`,
`iteratedFDeriv_eq_of_diag_eq` + the ω wrapper.

## Vote

- Claude: J3 as ruled (abstract polarization + ω wrapper).
- GPT-5.6 Sol: same (its own shape ruling, archived).

Agreed.
