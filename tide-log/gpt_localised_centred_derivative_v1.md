## 1. A and B are correct, with two wording corrections

Assume throughout that the localiser parameters \(g,w_0\), the frame \(Q\), and the energy are fixed as \(t\) varies. The claimed mathematical statements follow from the cited identities and rates; this does not independently verify the proposed Lean proofs.

### A: exact identities

Write \(M_{2,i}=\langle u_i^2\rangle_{\rm loc}\) and \(\mu_i=\langle u_i\rangle_{\rm loc}\). Then
\[
\partial_t\mu_i=-\operatorname{Cov}_{\rm loc}(L,u_i),
\qquad
\partial_tM_{2,i}=-\operatorname{Cov}_{\rm loc}(L,u_i^2).
\]
Consequently,
\[
\boxed{
-\partial_t\operatorname{Var}_{\rm loc}(u_i)
=\operatorname{Cov}_{\rm loc}(L,u_i^2)
-2\mu_i\operatorname{Cov}_{\rm loc}(L,u_i).
}
\]
Here and below \(L\) denotes the appropriate pulled-back energy \(L\circ A\).

More generally,
\[
-\partial_t\operatorname{Cov}_{\rm loc}(u_i,u_j)
=\operatorname{Cov}_{\rm loc}(L,u_iu_j)
-\mu_j\operatorname{Cov}_{\rm loc}(L,u_i)
-\mu_i\operatorname{Cov}_{\rm loc}(L,u_j).
\]
For \(i\ne j\), separability gives the exact pair identity
\[
\operatorname{Cov}_{\rm loc}(L,u_iu_j)
=\mu_j\operatorname{Cov}_{\rm loc}(L,u_i)
+\mu_i\operatorname{Cov}_{\rm loc}(L,u_j),
\]
so this expression vanishes **exactly**, not merely asymptotically.

**Correction to A’s wording:** \(2c_ic_j/t\) is the leading off-diagonal term in the **\(t^2\)-scaled** raw energy covariance:
\[
t^2\operatorname{Cov}_{\rm loc}(L,u_iu_j)
=\frac{2c_ic_j}{t}+O(t^{-2}).
\]
The unscaled quantity is \(2c_ic_j/t^3+O(t^{-4})\). Also, the exact equality is with the two mean–energy-covariance products above, not with their leading asymptotic coefficient.

The rotated identity is correct:
\[
-\partial_t\operatorname{Cov}_{\rm loc}(w_j,w_k)
=\sum_iQ_{ji}Q_{ki}
\left[
\operatorname{Cov}_{\rm loc}(L,u_i^2)
-2\mu_i\operatorname{Cov}_{\rm loc}(L,u_i)
\right].
\]

### B: coefficient and remainder

Set
\[
a_i(t)=t\mu_i(t),\qquad
b_i(t)=t^2\operatorname{Cov}_{\rm loc}(L,u_i).
\]
The stated rates give
\[
a_i=c_i+O(t^{-1}),\qquad b_i=c_i+O(t^{-1}),
\]
hence
\[
a_ib_i=c_i^2+O(t^{-1}).
\]
The crucial scaling is
\[
t^2\mu_i\operatorname{Cov}_{\rm loc}(L,u_i)
=\frac{a_ib_i}{t}
=\frac{c_i^2}{t}+O(t^{-2}).
\]
Therefore
\[
t^2(-\partial_t\operatorname{Var}_{\rm loc}(u_i))
=\frac1{\lambda_i}
+\frac{2(c'_{2,i}-c_i^2)}t+O(t^{-2})
=\frac1{\lambda_i}+\frac{2v_i}t+O(t^{-2}).
\]

For a concrete product estimate, if the two errors are bounded by \(A/t\) and \(B/t\), then
\[
|a_ib_i-c_i^2|
\le \frac{|c_i|(A+B)}t+\frac{AB}{t^2}.
\]
On \(t\ge1\), the final term can be absorbed into an \(O(t^{-1})\) bound. No higher-order mean expansion is needed.

Thus the rotated tensor statement in B is correct. **Do not justify it merely by differentiating tide 74’s big-\(O\) remainder:** an \(O(t^{-3})\) remainder need not have derivative \(O(t^{-4})\). A plus the direct energy-covariance rates supplies the missing justification.

## 2. C is right, with precise qualifications

C correctly describes the cancellation. Two refinements are important:

- The relevant mean-product contribution is **\(-\partial_t(\mu^\top\widetilde B\mu)\)** in the negative derivative of the raw second moment; centring subtracts it.
- “Off-diagonal terms vanish” refers to the **separable \(u\)-frame**. Off-diagonal entries in physical \(w\)-coordinates generally remain after rotation.

### Sign and normalisation of “twice tide 74’s coefficient”

Let
\[
V=Q\operatorname{diag}(v_i)Q^\top,\qquad
D=Q\operatorname{diag}(v_i+g/\lambda_i^2)Q^\top
=V+gH^{-2}.
\]
Tide 74 states
\[
C(t):=\operatorname{Cov}_{\rm loc}(w,w)
=S(t)+\frac D{t^2}+O(t^{-3}),
\qquad S(t)=(tH+gI)^{-1}.
\]
Since
\[
S(t)=\frac{H^{-1}}t-\frac{gH^{-2}}{t^2}+O(t^{-3}),
\]
the **total** \(t^{-2}\) coefficient of \(C(t)\) is \(V\), not \(D\).

With the derivative remainder justified by A–B,
\[
\begin{aligned}
-\partial_tC(t)
&=S(t)HS(t)+\frac{2D}{t^3}+O(t^{-4})\\
&=\frac{H^{-1}}{t^2}
-\frac{2gH^{-2}}{t^3}
+\frac{2(V+gH^{-2})}{t^3}
+O(t^{-4})\\
&=\boxed{\frac{H^{-1}}{t^2}+\frac{2V}{t^3}+O(t^{-4}).}
\end{aligned}
\]
This matches B exactly. The sign is positive because
\(-\partial_t(t^{-2})=2t^{-3}\). “Twice the coefficient” is correct for the **total covariance coefficient**, after expanding \(S\), not for the displayed correction \(D\) alone.

### Suggested wording for the note

> Equation (cov) concerns the centred covariance, rather than the raw second moment. For fixed localiser parameters, its negative time derivative satisfies
> \[
> -\partial_t\operatorname{Cov}_{\rm loc}(w_j,w_k)
> =\frac{(H^{-1})_{jk}}{t^2}
> +\frac{2}{t^3}\sum_iQ_{ji}Q_{ki}v_i
> +O(t^{-4}).
> \]
> In the separable frame, off-diagonal centred covariances and their derivatives vanish exactly: the raw off-diagonal energy-covariance terms cancel against the differentiated mean products. On the diagonal, centring replaces \(2c'_{2,i}\) by \(2(c'_{2,i}-c_i^2)=2v_i\). After rotation, physical-coordinate off-diagonal entries need not vanish. The derivative expansion is established using the exact expectation-derivative identity and direct remainder estimates, rather than by formally differentiating an asymptotic remainder.

## 3. Best next target

**Close the E3 arc with a note-facing, invariant centred quadratic-probe theorem.** For every fixed symmetric physical-coordinate matrix \(B\), package
\[
-\partial_t\operatorname{tr}\!\bigl(B\,C(t)\bigr)
=\frac{\operatorname{tr}(BH^{-1})}{t^2}
+\frac{2\operatorname{tr}(BV)}{t^3}
+O(t^{-4}),
\]
together with the exact bridge
\[
-\partial_t\operatorname{tr}(BC(t))
=\operatorname{Cov}_{\rm loc}
\!\left(L,(w-m(t))^\top B(w-m(t))\right),
\quad m(t)=\langle w\rangle_{\rm loc}.
\]

The probe on the right depends on \(t\), so prove this bridge by expanding the centred quadratic—or explicitly show that its extra derivative term has zero expectation. Do not apply the fixed-probe lemma directly to it.

This would turn A–B into the actual E3 statement, reconcile raw eq:covK with centred eq:cov, and isolate the cancellation for arbitrary quadratic contractions. It should require little new analysis beyond finite sums and the existing exact identities.

## 4. Vote

**Vote: accept A + B; retain C as an explanatory remark after correcting the scaling, derivative sign wording, and frame qualification.**