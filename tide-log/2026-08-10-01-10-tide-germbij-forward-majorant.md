# Tide: germbij forward programme stage 5c-i (the q-uniform majorant)

**Direction (user):** "Yes continue with germbij, and do not switch into
another seabed... the main core concern being the recovery of all
coefficients in the nondegenerate case and the main theorem in the
nondegenerate case."

**Seabed:** laplace, branch tide/germbij-forward-absorb at 8d4b5db
(stacked; stage 5c-pre in PR #102). Architecture consult archived as
`tide-log/gpt56_stage5_shape_v1.md`; this tide is its item 6 (the
"key hidden dependency": the single majorant theorem the DCT
consumes).

**Started:** 2026-08-10T01:10Z

## Candidate

One theorem plus the scalar reindexing bridge:

1. `sum_Icc_exponent_eq`: Σ_{s∈range N} q^(s+1)·V_(s+1)(z) =
   Σ_{s∈Icc 1 N} V_s(z)·q^s (aligning exponent_split's shape with
   exp_graded_expansion's).
2. `normalized_window_remainder_bound` (D : ForwardExpansionDomain,
   with observable growth data): ∃ C ≥ 0, K, γ > 0 with, eventually
   in q, for all z in the window,
   |P z · e^{-(L(qz)-L0)/q²} - P z · e^{-T₂(z)} · Σ_{j≤N} q^j P_j(z)|
     / q^N ≤ C·(1+‖z‖)^K·e^{-γ‖z‖²}.
   Proof: exponent_split (hgrad now a theorem) factors the true
   integrand as e^{-T₂}·exp(-(A+q^Nρ)); the difference splits into
   the three 5b pieces (perturbation strip, unrestricted exp Taylor
   remainder at -A with the multinomial q-power extraction, graded
   polynomial tail with 5a growth); each ×e^{-T₂} absorbs via
   gaussian_absorb (γ = λ/4).

## Assembly plan (per the archived consult + the 5c-pre follow-ups)

- Piece (i)/q^N ≤ C_rem‖z‖^(N+2)·e^{Σq^s|V_s|+|q^Nρ|}; ×e^{-T₂} ≤
  C_rem‖z‖^(N+2) e^{-(λ/4)‖z‖²} via abs_scaledRem_le (constant form,
  q•z in the Taylor ball via smul_mem_ball_of_mesoscopic) +
  abs_exp_neg_add_sub_exp_neg_le + gaussian_absorb.
- Piece (ii)/q^N ≤ (Σ_s|V_s(z)|)^(N+1)·e^{|A|}/(N+1)!·q; |A| ≤
  Σ q^s|V_s| pointwise so e^{|A|}e^{-T₂} absorbs the same way;
  (Σ|V_s|)^(N+1) ≤ poly(1+‖z‖) via abs_taylorHomogeneousTerm_le.
- Piece (iii)/q^N ≤ q·Σ_{j∈Ico(N+1)(N²+1)}|P_j(z)| ≤ poly(1+‖z‖) via
  abs_correctionCoeffFn_le; e^{-T₂} ≤ e^{-(λ/2)‖z‖²} via t2_lower.

## Numerical check

Not feasible: eventual bound with existential constants. The three
scalar pieces were checked numerically in the 5b tide.

## Result

`Laplace/Multi/WindowMajorant.lean` (~310 lines), all gates green:

- `sum_range_shift_eq_sum_Icc` (the exponent-split/graded-expansion
  index bridge, by induction via Finset.sum_Icc_succ_top).
- `normalized_window_remainder_bound`: ∃ C ≥ 0, eventually on the
  window, |e^{-(L(qz)-L0)/q²} - e^{-T₂(z)}·Σ_{j≤N} P_j(z)q^j| ≤
  C(1+‖z‖)^{(N+2)(N+1)} q^N e^{-(λ/4)‖z‖²}. The three-piece telescope
  through gradedExpPoly's evaluation, with C = remConst +
  M^{N+1}/(N+1)! + Ctail explicit.

Compiled on the second build attempt (six small fixes, no
restructuring). New catalogue entries: `add_le_add_right` adds on the
LEFT in this Mathlib (use `add_le_add h le_rfl`); positivity cannot
see nonnegativity of opaque structure fields (D.remConst) — derive a
local `hrem0` once; `Metric.mem_ball_zero_iff` does not exist here
(rw [Metric.mem_ball, dist_zero_right]); the `set ... with` folding of
R := q^N·scaledRem must happen AFTER obtaining gaussian_absorb's
instance so the fold hits its statement.

### Suggested follow-ups

- Stage 5c-ii (next, final integration): pointwise convergence of the
  normalized window remainder (exp_graded_expansion +
  tendsto_scaledRem + eventually_mem_mesoscopicSet), the DCT via
  MeasureTheory.tendsto_integral_filter_of_dominated_convergence with
  the indicator folded in, the two outer-tail removals, coefficient
  integrability, and numerator_hasExpansion.
