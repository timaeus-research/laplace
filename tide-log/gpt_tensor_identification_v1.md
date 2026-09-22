## 1. Is A sufficient, and are the factors correct?

**A is sufficient as a Taylor-coefficient certificate, matching the Rosenbrock precedent.** It is not, by itself, a Lean theorem identifying an expression involving `deriv`, `fderiv`, or `iteratedFDeriv`. The staging notes should preserve that distinction.

The factors are correct:
\[
L(c+v)=\frac12 v^\top Hv+\frac1{3!}T[v,v,v]+\frac1{4!}R[v,v,v,v].
\]
Here \(T=\mathrm{rotT}\) and \(R=\mathrm{rotQ}\), with all ordered index tuples included in the contractions. **No additional multiplicity factors are needed.**

I would include symmetry in A’s deliverables:

- \(H=Q\operatorname{diag}(\lambda)Q^\top\) is symmetric;
- `rotT` is symmetric in its three indices;
- `rotQ` is symmetric in its four indices.

This matters conceptually: a diagonal contraction \(T[v,v,v]\) determines only the symmetric part of an arbitrary tensor. In this case symmetry is immediate from the definitions—prove adjacent transpositions by `Finset.sum_congr` and `ring`. Together with symmetry, the exact polynomial identity mathematically identifies the derivative tensors, though the formal bridge to Lean’s differentiation operators remains separate.

Two useful scope observations:

- **Orthogonality of `Q` is unnecessary** for A, B, and these symmetry statements.
- No positivity assumptions are needed either. These results certify expansion at a stationary centre, not that `c` is a minimizer.

`rotatedAnharmonic … c = 0` follows by taking `v = 0`, or directly by simplifying the affine frame.

## 2. How should A’s sums be handled?

I recommend **three contraction lemmas**, followed by a short assembly proof. Set
\[
u=Q^\top v.
\]
Prove:
\[
\begin{aligned}
v^\top(Q\operatorname{diag}(\lambda)Q^\top v)
  &=\sum_l\lambda_lu_l^2,\\
\sum_{i,j,k}\mathrm{rotT}_{ijk}v_iv_jv_k
  &=\sum_l\alpha_lu_l^3,\\
\sum_{i,j,k,m}\mathrm{rotQ}_{ijkm}v_iv_jv_kv_m
  &=\sum_l\gamma_lu_l^4.
\end{aligned}
\]

### Quadratic term

Use matrix/vector identities rather than expanding both matrix multiplications:
\[
v^\top Q(\operatorname{diag}(\lambda)u)
=(Q^\top v)^\top\operatorname{diag}(\lambda)u
=\sum_l\lambda_lu_l^2.
\]

The relevant API is `Matrix.mulVec_mulVec`, `Matrix.dotProduct_mulVec`, the transpose relation between `vecMul` and `mulVec`, and simplification of diagonal multiplication. Exact rewrite directions depend on the statement orientations in your Mathlib revision.

### Cubic and quartic terms

For these fixed small degrees, **finite-sum distributivity and controlled reordering are the cleanest route**:

1. Unfold `rotT` or `rotQ`.
2. Move the `l` sum outward using `Finset.sum_comm`.
3. For each fixed `l`, factor the independent index sums.
4. Recognize the resulting product as \(u_l^3\) or \(u_l^4\).

`Finset.sum_mul_sum`, `Finset.sum_mul`, and `Finset.mul_sum` are enough. Normalize individual summands with `ring`, under `Finset.sum_congr`.

An equally reasonable proof expands the powers on the right into products of sums and distributes them. Either way, use explicit sum reordering rather than a large, uncontrolled commutativity simplification.

I would **not** introduce tuple-indexed sums merely for these two lemmas:

- `Fintype.sum_prod_type` changes the indexing representation but does not eliminate the distributive algebra.
- A power-of-a-sum lemma necessarily accounts for mixed terms; it is not a simple replacement by a sum of powers.
- A general arbitrary-order tensor contraction lemma is worthwhile only if more degrees or tensor families are imminent.

Once the contraction lemmas exist, A reduces to simplifying
`affineFrame Q c (c + v)`, distributing the outer sum over the three polynomial terms, and normalizing coefficients.

## 3. Is coordinate-line `deriv` right for B?

**Yes, for a coordinate tensor interface.** It avoids introducing continuous multilinear maps when all the downstream data are indexed arrays. If downstream results eventually consume Fréchet derivatives, B is an intermediate interface, not a replacement for that connection.

### Prove a `HasDerivAt` helper first

The clean helper has the form below, with `[Fintype ι]` understood:

```lean
(hg : ∀ l, HasDerivAt (g l) (gp l) (a l)) :
HasDerivAt
  (fun s : ℝ => ∑ l, g l (a l + s * b l))
  (∑ l, gp l * b l)
  0
```

Build it using:

- `hasDerivAt_const`, `hasDerivAt_id`;
- `HasDerivAt.add` and `HasDerivAt.mul_const` for the affine inner function;
- `HasDerivAt.comp` for each summand;
- `HasDerivAt.sum` for the finite sum;
- `.deriv` to obtain the desired `deriv` equality.

Thus your displayed formula follows under
```lean
hg : ∀ l, DifferentiableAt ℝ (g l) (a l)
```
by using `(hg l).hasDerivAt`.

**Keep the differentiability hypotheses.** Lean’s `deriv` is totalized, so an unconditional sum/chain-rule statement using it is not valid in general.

For the coordinate line, prove separately:
\[
\bigl(Q^\top((w+s e_k)-c)\bigr)_l
=\bigl(Q^\top(w-c)\bigr)_l+sQ_{kl}.
\]
This is finite linear algebra and simplification of `Pi.single`; it needs no orthogonality.

### Differentiate an explicit polynomial tower

Define or locally name
\[
\begin{aligned}
P_0(x)&=\lambda x^2/2+\alpha x^3/6+\gamma x^4/24,\\
P_1(x)&=\lambda x+\alpha x^2/2+\gamma x^3/6,\\
P_2(x)&=\lambda+\alpha x+\gamma x^2/2,\\
P_3(x)&=\alpha+\gamma x,\\
P_4(x)&=\gamma.
\end{aligned}
\]

Prove
```lean
HasDerivAt P₀ (P₁ x) x
HasDerivAt P₁ (P₂ x) x
HasDerivAt P₂ (P₃ x) x
HasDerivAt P₃ (P₄ x) x
```
using the addition, scalar-multiplication, and power rules, followed by coefficient normalization.

`fun_prop` is useful for differentiability or smoothness side conditions. It does **not** replace proving the specified derivative values.

### The important nested-`partialD` pitfall

Do not prove only the derivative at `c` and then attempt to differentiate that equality. Prove identities **for every `w`**:
\[
\begin{aligned}
D_kL(w)&=\sum_lP_{1,l}(u_l(w))Q_{kl},\\
D_jD_kL(w)&=\sum_lP_{2,l}(u_l(w))Q_{jl}Q_{kl},\\
D_iD_jD_kL(w)&=\sum_lP_{3,l}(u_l(w))Q_{il}Q_{jl}Q_{kl}.
\end{aligned}
\]
The fourth derivative similarly has \(P_{4,l}=\gamma_l\).

A weighted version of the helper,
\[
D_k\!\left(\sum_l A_lP_{r,l}(u_l(w))\right)
=\sum_l A_lP_{r+1,l}(u_l(w))Q_{kl},
\]
handles each step, since the previously accumulated matrix entries are constants with respect to `w`.

Rewrite the inner `partialD` functions to these explicit polynomial expressions before differentiating again. This avoids any separate need to reason abstractly about differentiability of `deriv`.

At `c`, use \(u(c)=0\). The results are exactly zero gradient, the stated Hessian, `rotT`, and `rotQ`. No mixed-partial commutation theorem is needed.

## 4. Scope: A, A+B, or A+B+C?

A should be the first milestone: it is algebraic, robust, and directly matches the existing precedent.

B adds a genuinely useful guarantee: it removes the qualification that these are derivative tensors only “in the Taylor-coefficient sense.” With the affine-line helper and the four explicit polynomial derivative rules, it is a bounded extension rather than a general higher-calculus project.

C has a viable route through continuous linear coordinate maps, affine composition, finite sums, and products. Smoothness is easy; the additional work is expressing the tensors as continuous multilinear maps and matching the `iteratedFDeriv` API, slot conventions, and evaluations. I would not assume a short proof without checking the pinned Mathlib version. Defer it until a downstream theorem actually requires that interface.

**Vote: A+B, with A as the independently shippable milestone and C deferred.**