# Tide: anharmonic FDT cross-susceptibility asymptote (t→∞)

**Direction (user):** Close the asymptotic capstone deferred by the FDT-capstone
tide: the `t→∞` limit of the cross-susceptibility. The unconditional identity
`∂_h Cov_h(x,x)|_0 = -t·κ₃` (tide #1) composed with the κ₃ asymptotic gives
`t · ∂_h Cov_h(x,x)|_0 = -t²·κ₃ → α/λ³`. This is the empirically-validated
asymptote (the 1D FDT experiment measured `∂_h Cov ~ α/(λ³t)`, i.e. the rescaled
limit α/λ³).

**Seabed:** lean/laplace, commit b81d730 (main).
**Started:** 2026-05-31

## Seabed snapshot

- `gibbsCov_deriv_anharmonic_id_id_id_eq` (FDT capstone, unconditional):
  `HasDerivAt (Cov_h) (-t·Threepoint.kappa3 …) 0`.
- `kappa3_anharmonic_id_id_id_asymptotic`:
  `Tendsto (fun t => t²·Threepoint.kappa3 …) atTop (nhds (-α/λ³))`.
- Both use `Threepoint.kappa3` — compose directly, no Threepoint↔Laplace bridge.

## Candidate (agreed) — proceed-without-GPT

`Tendsto (fun t => t · deriv (Cov_h) 0) atTop (nhds (α/λ³))`. For `t>0`,
`deriv (Cov_h) 0 = -t·κ₃`, so `t·deriv = -(t²·κ₃)`; and `t²·κ₃ → -α/λ³`, so
`-(t²·κ₃) → α/λ³`. `Tendsto.congr'` (eventually-equal on `t>0`) + `.neg`.

**Proceed-without-GPT:** Tendsto composition of two existing results; the
asymptote α/λ³ is the empirically-validated value (FDT experiment, 2026-05-23).
No fresh consult adds value.

## Numerical check

Not needed: composition of the (validated) κ₃ asymptotic with the (machine-
checked) FDT identity. The α/λ³ value was confirmed by HMC in the 1D
FDT-identity experiment (0.005 at (1,0.5,1,100), matched within 2.5σ).

## Result

New file `Laplace/OneD/AnharmonicFDTAsymptotic.lean`:
`gibbsCov_deriv_anharmonic_asymptotic` — `t·∂_h Cov_h(x,x)|_0 → α/λ³` as t→∞,
via `Tendsto.congr'` over `eventually_gt_atTop 0` composing the FDT three-point
identity (`-t·κ₃`) with `kappa3_anharmonic_id_id_id_asymptotic` (`t²κ₃→-α/λ³`).
~30 lines, first-try build, no sorries. Closes the FDT-capstone tide's deferred
asymptotic TODO; matches the HMC-validated experiment value.

## Retrospective

Retrospective: `retrospectives/2026-05-31-tide-anharmonic-fdt-asymptotic.tex`
