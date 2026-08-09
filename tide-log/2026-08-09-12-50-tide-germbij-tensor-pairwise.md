# Tide: germbij tensor J5d (unnormalized pairwise integral theorem)

**Direction (user):** standing auto-mode commission; the consult's
"genuinely load-bearing J5 theorem" — once it exists, normalization
is routine algebra.
**Seabed:** laplace, branch tide/germbij-tensor-localrate at 901d587
(stacked on unmerged J5c, PR #78).
**Started:** 2026-08-09T12:50 local

## Candidates

Consult J5d: with I_j(P,q) = ∫ A_j.integrand P q (the H4 integrand),

    (I₁(P,q) − I₂(P,q))/q^{k−2} → −∫ P·Q·quadKernel H,

by the three-term decomposition (B := common ball of radius
ρ = min taylorRadius, contained in both U's):

    χ_{U₁}e^{-a₁} − χ_{U₂}e^{-a₂}
      = χ_B(e^{-a₁} − e^{-a₂}) + (χ_{U₁} − χ_B)e^{-a₁}
        − (χ_{U₂} − χ_B)e^{-a₂},

pointwise by membership cases. The local term is J5c's
tendsto_local_rate_integral; each tail has support inside
{ρ ≤ q‖x‖}, is bounded by |P|e^{-c_j‖x‖²} there (rescaled_lower on
all of U_j), and vanishes at rate q^{k−2} by squeeze against J5b's
retreating-tail lemma. Per-q integrability of every piece from the
J5a general-rate layer (each piece is an indicator inside
{x | q•x ∈ U_j} of P·e^{-a_j}, dominated by |P|e^{-c_j‖x‖²}).

## Numerical check

Structural assembly of already-verified limits (J4 pointwise, H2a
integrals); no new closed form.

## Vote

- Claude: J5d as staged (the consult's own section).
- GPT-5.6 Sol: same (archived on this branch's history).

Agreed.

## Result

One file (`Laplace/Multi/PairwiseRate.lean`, ~330 lines, sorry-free):

- `integrable_indicator_slice` (any sub-domain slice of the posterior
  integrand, dominated by the coercive Gaussian).
- `tendsto_tail_slice`: the retreating domain tail at every rate, by
  squeeze against J5b — importantly WITHOUT .norm/simpa massaging
  (which renormalizes -c*‖x‖² to -(c*‖x‖²) inside binders and breaks
  the squeeze's syntactic matching; feed J5b's raw statement).
- **`tendsto_pairwise_integral_difference`** (the consult's
  load-bearing checkpoint): (I₁(P,q) − I₂(P,q))/q^{k−2} →
  −∫ P·Q·quadKernel. Three-term decomposition per q (ball slice +
  domain tail for each loss, by membership cases), the ball-slice
  difference re-expressed as q^{k−2} times J5c's integrand, and the
  limits assembled by Tendsto.add/sub with the per-q identity proven
  after folding the six integrals into SCALAR atoms with `set` — the
  session's set-folding discipline inverted: fold scalars (safe,
  binder-free) exactly where field_simp would otherwise rewrite
  inside integrand binders and desynchronize atoms.

New catalogue entry: field_simp inside goals containing integrals
rewrites under the integral binders too, silently splitting what
should be one atom into mismatched forms (mul/div reassociation);
fold integral VALUES into scalars with `set` before any field_simp
/ linarith on equations between integrals.
