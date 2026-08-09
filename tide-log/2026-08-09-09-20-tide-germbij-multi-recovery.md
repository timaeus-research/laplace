# Tide: germbij multivariate H6 (pairwise Hessian recovery)

**Direction (user):** standing auto-mode commission on the germbij
note; stage H6, the last of the scoped H-recovery milestone.
**Seabed:** laplace, branch tide/germbij-multi-normalize at 018385b
(stacked on unmerged H5, PR #72).
**Started:** 2026-08-09T09:20 local

## Candidates

Per the scoping consult's Stage H6 ("if two admissible losses have
covariance matrices differing by o(q²), then H₁⁻¹ = H₂⁻¹, hence
H₁ = H₂ — the multivariate analogue of base_recovery"):

1. `covariance A i j q` abbreviation (the H5 covariance form).
2. `hessian_inv_entry_recovery`: if
   (fun q ↦ Cov₁ i j q - Cov₂ i j q) =o[𝓝[>]0] (fun q ↦ q²), then
   H₁⁻¹ i j = H₂⁻¹ i j — IsLittleO.tendsto_div_nhds_zero +
   Tendsto.sub + tendsto_nhds_unique (𝓝[>]0 is NeBot).
3. `hessian_recovery`: the matrix statement H₁ = H₂ via
   Matrix.ext and double inversion (nonsing_inv_nonsing_inv with
   IsUnit det from PosDef.det_pos).

## Numerical check

Not feasible beyond the H2/H5 checks already recorded: the statement
is an identifiability implication (limits equal ⇒ matrices equal),
not a closed form.

## Vote

- Claude: as staged (the scoping consult's own H6 brief).
- GPT-5.6 Sol: same (archived).

Agreed.

## Result

One file (`Laplace/Multi/HessianRecovery.lean`, ~100 lines,
sorry-free, CLEAN ON THE FIRST DIAGNOSTIC PASS — the first
zero-repair file of the arc):

- `covariance` (the H5 covariance form named), `tendsto_covariance`.
- `hessian_inv_entry_recovery`: o(q²)-agreeing covariance data give
  H₁⁻¹ᵢⱼ = H₂⁻¹ᵢⱼ (IsLittleO.tendsto_div_nhds_zero + Tendsto.sub +
  tendsto_nhds_unique).
- `hessian_recovery`: H₁ = H₂ by Matrix.ext + double nonsingular
  inversion from PosDef determinants.

The multivariate H-recovery milestone (stages H0-H6 of the scoping
consult) is COMPLETE: from C² losses with positive-definite Hessians
at the minimum, posterior covariance data at scale q⁻² recover H,
and matching data force equal Hessians — germbij's multivariate
Hessian step, end to end, PRs #66-#72 + this.
