## 1. Correctness and hypotheses

**Yes: A and B are valid without symmetry of `T` or `Q₄`.** They are equivariance identities for tensor contractions, not identities that require the tensors to be derivatives of a scalar function.

Work over finite square real matrices and assume `Qᵀ * Q = 1`. Then also `Q * Qᵀ = 1`. The fundamental identity is
\[
\sum_{k,l}Q_{kc}(QSQ^\top)_{kl}Q_{le}
=(Q^\top(QSQ^\top)Q)_{ce}=S_{ce}.
\]
This requires neither symmetry nor invertibility of `S`. Each contracted pair of tensor slots can therefore be eliminated independently. Uncontracted slots retain their factors of `Q`, giving the stated vector, matrix, and scalar transformation laws.

In particular:

- `contractT` has one free slot;
- `contractQ`, `bubble`, `tadpoleLine`, and `oneLoopPi` have two;
- `meanShift` has one;
- `covKFormula` and `twoLoopEnergy` have none.

The same reasoning applies to the disconnected/tadpole contractions: no permutation of tensor slots is necessary.

**Important nonsymmetric-case warning:** retain the actual slot order in every auxiliary representation. For example, your bubble representation uses
\[
S\,(\operatorname{slice}T\,j)\,S^\top,
\]
not `S * slice T j * S`. Replacing the transpose using an unstated symmetry assumption would weaken the result.

### The inverse identity is unconditional

For Mathlib’s totalized inverse of square real matrices,
\[
\bigl(t\mathbin{\bullet}(QHQ^\top)\bigr)^{-1}
=Q\bigl(t\mathbin{\bullet}H\bigr)^{-1}Q^\top
\]
needs **no** `IsUnit H.det`, positivity of `t`, or symmetry of `H`.

Indeed, put `A := t • H`. Then
\[
(QAQ^\top)^{-1}
=(Q^\top)^{-1}A^{-1}Q^{-1}
=QA^{-1}Q^\top.
\]
`Matrix.mul_inv_rev` is unconditional in this square real-matrix setting. The determinant/unit hypotheses belong to cancellation results such as `A * A⁻¹ = 1`, not to this reverse-product identity. Orthogonality supplies the needed inverse identities for `Q`.

Equivalently, if `A` is singular, so is `QAQᵀ`, and both totalized inverses are zero. Thus the theorem includes `t = 0` and singular `H`. Prefer proving this as a separate reusable lemma, without expanding the inverse or dividing by `t`.

There is a distinction worth documenting: **the formula’s algebraic covariance holds unconditionally; its interpretation as a Laplace approximation does not.**

### One correction to the motivation

Covariance is a useful regression test, but it does **not** detect every misplaced index. Different complete contractions are themselves invariant; permuting tensor slots can produce a different but still equivariant formula. Incorrect coefficients also preserve covariance.

So these theorems test the tensorial structure, while the diagonal evaluations and independent contraction checks test additional aspects of the intended formulas.

## 2. Proof strategy: a hybrid, with the matrix route for the bubble

I would use **(ii) for the bubble**, and small contraction lemmas for the simpler expressions. Avoid making a fully distributed six-index sum the main proof interface.

### Shared infrastructure

Define a matrix conjugation operation, say
\[
C_Q(X):=QXQ^\top.
\]
Establish its compatibility with addition, scalar multiplication, finite sums, transpose, multiplication under orthogonality, and matrix–vector multiplication. Include the inverse lemma above.

Then prove the two-index contraction identity once. Prefer obtaining it by expanding the entries of
\[
Q^\top(C_Q(S))Q=S
\]
rather than proving it from scratch through a large sum calculation.

This gives direct, manageable proofs for `contractT` and `contractQ`. The tadpole can then be handled compositionally through its vector contraction and matrix–vector products, rather than by another complete expansion.

### Bubble-specific infrastructure

Use
\[
\operatorname{frob}(X,Y):=\operatorname{tr}(X^\top Y).
\]
Prove:

1. Bilinearity, including finite-sum versions.
2. Orthogonal invariance:
   \[
   \operatorname{frob}(C_Q(X),C_Q(Y))
   =\operatorname{frob}(X,Y).
   \]
3. Slice transport:
   \[
   \operatorname{slice}(\operatorname{rotateT}Q\,T)\,i
   =\sum_a Q_{ia}\mathbin{\bullet}C_Q(\operatorname{slice}T\,a).
   \]
4. The bridge from the existing definition:
   \[
   \operatorname{bubble}(T,S)_{ij}
   =\operatorname{frob}\!\left(
      \operatorname{slice}T\,i,\,
      S(\operatorname{slice}T\,j)S^\top
     \right).
   \]

The bubble proof then reduces to bilinearity and
\[
C_Q(S)\,C_Q(X)\,C_Q(S)^\top=C_Q(SXS^\top).
\]
The remaining sum is just
\[
\sum_{a,b}Q_{ia}Q_{jb}\operatorname{bubble}(T,S)_{ab},
\]
the entry of the desired conjugated matrix.

This is less sensitive to dummy-index bookkeeping, and the transpose remains visible throughout.

**Lean engineering recommendation:** keep the index expansion inside the bridge and slice lemmas. Use matrix equalities, proved by `ext` only where necessary, above that layer. If a local sum proof is needed, distribute one selected product, arrange the sum order explicitly, and discharge the local contraction before expanding further. Do not globally normalize products of nested sums with unrestricted `Finset.mul_sum`/`Finset.sum_mul`.

Once these building blocks exist, `oneLoopPi`, `oneLoopCov`, and `meanShift` should be compositional proofs. Treat the scalar contractions in B as named invariant building blocks too, rather than unfolding an entire energy formula at once.

## 3. Low-cost additions

I would include these, in this order:

### Identity and composition of rotations

For both tensor ranks:
\[
\operatorname{rotateT}1\,T=T,
\qquad
\operatorname{rotateT}Q_1(\operatorname{rotateT}Q_2T)
=\operatorname{rotateT}(Q_1Q_2)T.
\]
These require no orthogonality. They validate the chosen action convention and give inverse transport under `Qᵀ` essentially for free.

Linearity in the tensor is also cheap and useful.

### Symmetry preservation

Yes, include it if the repository already has a convenient symmetry predicate. More generally, rotation commutes with permutation of tensor slots, so it preserves any specified slot-permutation symmetry, not merely full symmetry.

Do not introduce a large new symmetry framework just for this result.

### C’s diagonal compatibility

Definitely include
```text
rotateT Q (diagT α) = rotT Q α
rotateQ Q (diagQ γ) = rotQ Q γ
```
and, if needed, the corresponding matrix identity.

These are inexpensive bridges to the existing E2 development. More precisely, A+B transport the **diagonal evaluations** into the rotated closed forms; covariance alone does not supply those diagonal evaluations.

### Taylor transport: optional

For an existing polynomial/Taylor identity written as explicit tensor contractions, transport under an orthogonal substitution should be inexpensive.

A theorem identifying arbitrary transformed derivatives under `w = Q u + c` is a separate chain-rule development unless suitable infrastructure already exists. I would not put that on the critical path. Translation disappears from the tensor algebra once the expansion points have been matched.

## 4. Scope

**A is the core deliverable; B is the payoff; C connects it to the existing seabed.** I would organize the work as:

1. Tensor rotations, conjugation, identity/composition, and inverse transport.
2. Contraction covariance, including the bubble bridge.
3. Public covariance/invariance theorems for all four formulas.
4. Diagonal compatibility and a small integration theorem demonstrating reuse of an existing diagonal evaluation.

Keep the core algebraic results free of symmetry, nonsingularity, and positivity assumptions. Add those only in downstream analytic interpretation theorems.

**Vote: A + B + C.** Use the hybrid proof strategy, include identity/composition and inexpensive symmetry preservation, and leave general derivative/Taylor transport as an optional follow-up.