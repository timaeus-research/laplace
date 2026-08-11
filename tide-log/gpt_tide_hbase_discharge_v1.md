1. **Candidate A is sound**, with a few statement-level details to pin down.

- **(a) Moment shift invariance:** exact for every `q : ℝ`, not merely `q > 0`. Writing  
  `s := exp (-(c / q²))`, the shifted numerator and denominator are `s * num` and `s * den`. Since `s ≠ 0`, field cancellation works even when `den = 0`. Lean’s totalized division also causes no issue at `q = 0`; the exponential factor remains nonzero. Keep `U` unchanged when shifting the package.

- **(b) Higher-domain ray uniqueness:** the fixed-ball remainder bound suffices. For each fixed `z`, `t • z` is eventually in the Taylor ball as `t → 0⁺`. The remainder is then `O(t^k) = o(t²)` for `k > 2`, while terms of degrees `3,…,k-1` are individually `o(t²)`. Thus the GaussAbsorb coefficient-uniqueness argument mirrors cleanly.

- **(c) `j = 1`:** valid. Every `v : Fin 1 → EuclidD d` is the constant family `fun _ ↦ v 0`; hence vanishing on constant diagonals means the one-multilinear map is zero. No symmetry hypothesis is needed.

- **(d) Recomposition:** no mathematical obstruction. Positive-order iterated derivatives are unchanged by adding a constant, so both `hsymm` and the final unshifting transport by rewriting. Moment data transports by exact posterior-moment equality. After `H₁ = H₂`, the degree-two diagonal identities and order-two symmetry identify the tensors.

  The new theorem should specify which local packages carry `hdata₂`, for example the local projections of `A 3` and `B 3`, or explicit additional local packages. Otherwise the family may contain different `U` fields at different orders.

2. **A is the minimal good target.** Keep order-two `IsSymm` as an explicit hypothesis, naturally by strengthening to
   `∀ k, 1 < k → ...IsSymm`. Deriving it from `ContDiff` is mathematically routine but likely not Lean-routine: connecting Mathlib’s second-derivative symmetry theorem to `iteratedFDeriv 2` is avoidable API work. It can be attempted opportunistically, but should not gate this tide.

3. No cheaper robust route stands out. A positive-order rewrite of the underlying recovery theorem might avoid exposing the constant, but would move the same anchoring work deeper into the stack. Shifting `L₂` by `L₁ 0 - L₂ 0` has the correct sign; shifting `L₁` is equally valid, and symmetrizing gives no benefit.

**Vote: A.**