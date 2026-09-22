## 1. Correctness and hypotheses

**A–D are correct**, subject to the standing hypotheses: finite orthogonal frame, \(\lambda_i>0\), fixed parameters, and eventual \(t\ge T\ge1\). **B’s displayed bound additionally uses \(g\ge0\).** C needs positive dimension.

For B, the identity is exactly right:
\[
t^3\left(\frac{\lambda}{(t\lambda+g)^2}-\frac1{\lambda t^2}\right)
+\frac{2g}{\lambda^2}
=\frac{g^2(3t\lambda+2g)}{\lambda^2(t\lambda+g)^2}.
\]
For \(\lambda>0,\ g\ge0,\ t\ge1\), its right side is nonnegative and
\[
\frac{g^2(3t\lambda+2g)}{\lambda^2(t\lambda+g)^2}
\le \frac{g^2(3\lambda+2g)}{\lambda^4t}.
\]
Use \(t\lambda+g\ge t\lambda\) and \(3t\lambda+2g\le t(3\lambda+2g)\). If negative \(g\) is permitted, the identity survives, but this bound must be replaced by an eventual bound using absolute values and a larger threshold.

The proposed subtraction of the two coordinate errors is also correct, since \(w_i=v_i+g/\lambda_i^2\).

**Signs:** write
\[
S'=-Q\operatorname{diag}\!\left(\frac{\lambda_i}{(t\lambda_i+g)^2}\right)Q^\top.
\]
Thus \(-C'+S'=-(C-S)'\), with the same squared Frobenius norm as \((C-S)'\). Do not identify the positive diagonal expression with \(S'\).

For C, set \(L=\sum_i\lambda_i^{-2}>0\). Its normalized quantity is exactly
\[
\frac{t^6\|-C'-H^{-1}/t^2\|_F^2}{L},
\]
so divide A’s constant by \(L\).

For D, with \(a=\sum_i v_i^2>0\), enlarge the threshold until \(K/t\le2a\).

## 2. Wording against the note

Prefer naming the exact residual rather than “differentiating an \(O\)-term”:

> For \(R(t)=C(t)-S(t)\), the independently established derivative expansion gives  
> \[
> R'(t)=-2W/t^3+O_F(t^{-4}),
> \qquad
> \|R'(t)\|_F=2\|W\|_F/t^3+O(t^{-4}).
> \]
> Against the unlocalised negative Laplace derivative \(H^{-1}/t^2\), the corresponding discrepancy coefficient is \(2\|V\|_F\).

Yes, note agreement with the formal derivative of the earlier expansion, **as a consistency check only**. Neither `eq:cov` nor the Gaussian-prior interpretation alone justifies differentiating the remainder.

**Important proof distinction:** the norm statement, including when \(W=0\), follows from the coordinate/matrix derivative expansion and reverse triangle inequality. B’s *squared-norm rate alone* does not yield that norm remainder when \(W=0\).

## 3. Lean route

**Cheapest route: reuse `frobenius_conj_rate`; no power-\(n\) generalisation is needed this tide.**

Given
\[
|t^3f_i-w_i|\le K/t,
\]
apply the existing lemma to \(\widetilde f_i(t)=t f_i(t)\). Then
\[
t^2\widetilde f_i=t^3f_i,\qquad
t^4\sum_{jk}\left(\sum_iQ_{ji}Q_{ki}\widetilde f_i\right)^2
=t^6\sum_{jk}\left(\sum_iQ_{ji}Q_{ki}f_i\right)^2.
\]
Make this a small \(t^3\)-wrapper, shared by A and B. Reserve a general transport refactor for later.

For the resolvent derivative:

- Prove the finite-sum rational formula’s `HasDerivAt` directly.
- Supply \(t\lambda_i+g\ne0\) explicitly to the inverse rule.
- Transfer to `locS` using local eventual equality on \(t>0\), as proposed.
- Keep the derivative initially as \(-\lambda_i/(t\lambda_i+g)^2\); normalize signs afterward.

Avoid differentiating the matrix-inverse API: the entry formula is simpler.

## 4. Scope, next target, and vote

**Vote: A+B+C+D**, with A+B the protected core; C and D are cheap corollaries. The scaling wrapper makes this more realistic than the proposed generalisation.

A useful small addition is the **unsquared norm rate**, proved from the already available coordinate rates—not merely by taking square roots of A/B. It directly supports the note’s wording.

**Best next target:** the mean’s squared discrepancy against the matching Gaussian/resolvent mean, **if `meanLocResidual2` already supplies the required vector coefficient and quantitative remainder**. This should reuse the same squared-norm transport pattern and extend the covariance/mean comparison coherently.

Defer second derivatives until independent second-derivative identities and remainder estimates exist. A uniform-on-\([T,\infty)\) statement is already what these eventual bounds provide; parameter-uniformity would be genuinely new. ULA/SGLD is a larger pivot requiring explicit step-size, stability, and gradient-noise assumptions—not the next cheap corollary.