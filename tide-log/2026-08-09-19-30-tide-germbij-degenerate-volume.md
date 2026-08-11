# Tide: germbij degenerate volume instance

**Direction (user):** standing auto-mode commission; the deferred
infrastructure piece of the scaling tide (its shape consult, archived
in the parent tide's log, staged this separately as "the most brittle
piece of Mathlib determinant plumbing").
**Seabed:** laplace, stacked on tide/germbij-degenerate-scaling
(PR #88, unmerged at start).
**Started:** 2026-08-09T19:30 local

## Candidates

Per the deliberation of record:

1. **Diagonal map determinant**: the diagonal linear map
   `LinearMap.pi (fun i => c i • LinearMap.proj i)` on `iota -> R`
   has determinant `prod_i c i` (LinearMap.det_pi + det_smul at
   finrank R R = 1).
2. **`ScalesMeasure` instance**: pi-volume satisfies the interface
   for the diagonal dilation qhDilation q with total homogeneity
   `Q = sum_i q i` (map_linearMap_addHaar_pi_eq_smul_addHaar +
   rpow_sum_of_pos: |det|^{-1} = s^{-sum q_i}).
3. **Unconditional recovery on Lebesgue**: the scaling tide's
   weight-recovery theorem with the ScalesMeasure hypotheses
   discharged.
4. **Concrete capstone**: x^4 + x^2 y^2 + y^4 is quasi-homogeneous
   for q = (1/4, 1/4) (the rpow-npow bridge per term), so its
   weights are recoverable — the note's mixed example, end to end.

## Vote

- Claude: 1-4 as one tide. - GPT-5.6 Sol: staged so in the archived
  scaling shape consult (implementation order item 4). Agreed on
  record.

## Numerical check

The parent tide's check already ran the law on the concrete
mixed-quartic example (ten digits); this tide adds no new analytic
formula (the determinant identity is algebraic).

## Result

Committed on tide/germbij-degenerate-volume:
`Laplace/Multi/DiagonalVolume.lean` (~140 lines). Theorems:
`diagonalMap` + `det_diagonalMap` (LinearMap.det_pi + det_smul at
finrank R R = 1 — the predicted determinant plumbing came to five
lines), `scalesMeasure_qhDilation_volume` (pi-volume satisfies the
interface; map_linearMap_addHaar_pi_eq_smul_addHaar +
rpow_sum_of_pos), `weights_eq_of_coordSq_moments_eq_volume`
(unconditional recovery on Lebesgue measure), and the concrete
capstone `mixedQuartic` + `mixedQuartic_quasiHomogeneous`: the
note's non-separable example x^4 + x^2 y^2 + y^4 is
quasi-homogeneous for q = (1/4, 1/4), so its weights are recoverable
end to end. Zero sorries, zero warnings; compiled first pass modulo
instance-hygiene warnings (over-included section variables,
tightened per theorem).

The consult's "most brittle piece" warning did not materialize: the
det computation was LinearMap.det_pi + det_smul + finrank_self
exactly, and the qhDilation/diagonalMap bridge is a rfl.
