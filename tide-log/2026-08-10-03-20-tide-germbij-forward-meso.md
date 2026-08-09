# Tide: germbij forward programme, stage 2 (Gaussian mesoscopics)

**Direction (user):** the nondegenerate core, forward direction;
implementation order item 2 of the archived programme-A design
consult (in the stage-1 tide log).
**Seabed:** laplace, stacked on tide/germbij-forward-asympoly
(PR #96, unmerged at start).
**Started:** 2026-08-10T03:20 local

## Candidates (per the design consult, section D)

1. mesoscopicSet q = {z | sqrt(q) ||z|| <= 1} (the inverse-free
   formulation), measurability, eventual pointwise membership, and
   eventual containment of q-scaled points in every fixed ball
   (||q.z|| <= sqrt q on the set).
2. exp_neg_inv_isLittleO_pow: e^{-c'/q} is o(q^M) at 0+ for every M
   (compose Mathlib's t^M e^{-t} -> 0 along q -> q^{-1}).
3. Gaussian tail: outside the mesoscopic set, rate-halving gives
   int ||z||^p e^{-c||z||^2} <= e^{-(c/2)/q} * (full-line Gaussian
   moment at c/2), hence o(q^M) for every M.
4. Coercivity transfer: the same bound for the rescaled Boltzmann
   integrand (|integrand| <= e^{-c||z||^2} from rescaled_lower), the
   statement every later numerator stage consumes.

## Vote

- Claude: as staged. - GPT-5.6 Sol: its own section D. Agreed.

## Numerical check

Not feasible: inequality/limit infrastructure.
