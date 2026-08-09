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
