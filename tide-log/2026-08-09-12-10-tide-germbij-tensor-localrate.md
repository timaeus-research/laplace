# Tide: germbij tensor J5c (HigherLaplaceDomain + local rate-DCT)

**Direction (user):** standing auto-mode commission on the germbij
note; the third J5 sub-stage per the shape consult (archived in the
J5a/J5b tide log directory on this branch's history).
**Seabed:** laplace, branch tide/germbij-tensor-ratecalc at b80d7f0
(stacked on unmerged J5a/J5b, PR #77).
**Started:** 2026-08-09T12:10 local

## Candidates

Consult J5c plus the structure it specified:

1. `HigherLaplaceDomain k L H extends LocalLaplaceDomain L H` with
   the engineering-choice fields (direct remainder bound, smaller
   proof surface): `contDiff_k : ContDiff ℝ k L` (global, matching
   J4's consumption and the 1D admissible pattern),
   `taylorRadius/pos`, `taylorBall_subset : ball 0 taylorRadius ⊆ U`,
   `taylorRemainderConst/nonneg`, and `taylorRemainder_bound`:
   |L y − Σ_{j<k} taylorHomogeneousTerm j L y| ≤ C‖y‖^k on the ball.
2. The pairwise difference bound: with matched jets below k, the
   two remainder bounds give |ΔL(y)| ≤ (C₁+C₂)‖y‖^k on the common
   ball (the jet sum telescopes away, including j = 0 so ΔL(0) = 0),
   hence |a₁(q,x) − a₂(q,x)|/q^{k−2} ≤ (C₁+C₂)‖x‖^k for ‖qx‖ < ρ.
3. **The local rate-DCT** (`tendsto_local_rate_integral`): the
   ball-indicator integral of P·(e^{-a₁} − e^{-a₂})/q^{k−2}
   converges to −∫ P·Q·quadKernel, with pointwise convergence from
   J5a's scalar limit fed by H3b's rescaled_tendsto (both exponents
   → qform/2) and J4's pairwise limit ((a₁−a₂)/q^{k−2} → Q x), and
   domination C·|P|·‖x‖^k·e^{-c‖x‖²} from the secant bound + the
   rescaled lower bounds + the difference bound, integrable by the
   J5a general-rate layer.

## Numerical check

The pointwise inputs were verified in the J4 tide (Δ_k limit) and
the H2a tide (Gaussian integrals); the new content is an
integrated-limit assembly with no separate closed form. Structural.

## Vote

- Claude: J5c as staged (the consult's own section, structure per
  its "reasonable engineering choice" ruling).
- GPT-5.6 Sol: same (archived).

Agreed.
