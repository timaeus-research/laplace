# Tide: germbij-turnkey-multi

**Direction (user):** continue the germbij arc (auto mode): the multivariate
turnkey, generalising the 1D turnkey's three integrability lemmas to
iota -> R and composing with the leading-part corollary, so both chains end
in statements whose every hypothesis is mathematical.

**Seabed:** laplace, main at 1c40e22 (both chains complete through the
composed corollaries).
**Started:** 2026-08-09T05:40Z
**Worktree/branch:** laplace-tide-germbij-turnkey-multi /
tide/germbij-turnkey-multi

## Deliberation (carried over)

The 1D turnkey tide's consult supplied the idiom set for the product
integrability lemma; its proofs contain nothing 1D-specific (the compact
cylinder is Icc 0 1 x tsupport psi in any proper space; the
product-restriction identity and domination are measure-generic). The
generalisation is a parametrised copy with iota -> R in place of R; the
composition mirrors the 1D turnkey against the leading-part corollary. No
fresh consult.

## Numerical check

Not feasible (integrability + existential constants); unchanged underlying
inequality.

## Result

- Branch tide/germbij-turnkey-multi, file Laplace/Multi/Turnkey.lean:
  integrable_minorant_multi, integrable_slice_multi,
  integrable_pencil_product_multi, leading_part_pencil_difference_lower_bound'.
- lake build clean on first attempt; scripts/sorries: 0/0/0/0.
- Surprise: none. The 1D turnkey proofs were measure-generic as predicted;
  the only edits were the ambient type (iota -> R) and hypothesis names.
  This closes the germbij arc: both chains now end in statements whose
  every hypothesis is mathematical.
