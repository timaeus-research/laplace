## 1. Correctness of A, B, and C

**A and B are correct for fixed parameters and sufficiently large positive \(t\). C is also correct as an asymptotic energy statement, with a small correction to its proposed expansion and a qualification about “E3’s LLC formula.”** Constants and thresholds may depend on the oscillator parameters, \(g\), the anchor, and dimension.

### A: localised variance

Write
\[
D=\langle\phi\rangle,\qquad N_1=\langle x\phi\rangle,\qquad
N_2=\langle x^2\phi\rangle.
\]
Suppose, for \(t\ge T\ge1\),
\[
|tN_2-1/\lambda|\le K_2/t,\quad |D-1|\le K_D/t,\quad
D\ge\tfrac12,\quad |tN_1|\le B.
\]
Then your identity is exactly right:
\[
t\operatorname{Var}_{\rm loc}
=\frac{tN_2}{D}-\frac{(tN_1)^2}{tD^2}.
\]
In particular,
\[
\left|t\operatorname{Var}_{\rm loc}-\frac1\lambda\right|
\le \frac{2K_2+2K_D/\lambda+4B^2}{t}.
\]
Thus tide 67’s boundedness of \(tN_1\), together with the denominator bound, is sufficient.

The second-moment expansion also works. Put
\[
a=gx_0,\qquad b=g/2,\qquad y=ax-bx^2.
\]
Then
\[
x^2e^y=x^2+ax^3+(a^2/2-b)x^4+R',
\]
where
\[
R'=-abx^5+\frac{b^2}{2}x^6
+x^2(e^y-1-y-y^2/2).
\]
Since \(y\le M=gx_0^2/2\), tide 67 gives
\[
|R'|\le A'|x|^4+B'|x|^6+C'|x|^8
\]
after using \(|x|^5\le (x^4+x^6)/2\). The signed cubic estimate is important: using only an absolute third-moment bound would lose the desired rate.

Finally,
\[
\left|\frac1{\lambda t}-\frac1{t\lambda+g}\right|
=\frac{g}{\lambda t(t\lambda+g)}
\le\frac{g}{\lambda^2t^2},
\]
so the second displayed conclusion follows.

**Lean suggestion:** expose the `N₂` rate as a separate theorem before proving the variance rate. It is independently useful for C.

### B: exact covariance decomposition

Yes: the frame off-diagonal covariances vanish **exactly**, not merely asymptotically.

In frame coordinates \(u\), with transformed anchor \(u_0\), the exponent is
\[
-\sum_i\left(t\ell_i(u_i)+\frac g2(u_i-u_{0,i})^2\right).
\]
Consequently the normalised measure is a product measure. Once the required integrability and nonzero-normaliser facts are supplied,
\[
\operatorname{Cov}_{\rm loc}(u_i,u_m)
=\begin{cases}
\operatorname{Var}_{{\rm loc},i},&i=m,\\
0,&i\ne m.
\end{cases}
\]
For \(w=a+Qu\), translation invariance and bilinearity give exactly
\[
\operatorname{Cov}_{\rm loc}(w_j,w_k)
=\sum_iQ_{ji}Q_{ki}\operatorname{Var}_{{\rm loc},i}.
\]
Together with `locS_rot`, this proves both proposed rates. For example, an entrywise remainder constant is
\[
K_{jk}=\sum_i|Q_{ji}Q_{ki}|K_i,
\]
after taking a common threshold over the finitely many coordinates.

### C: localised expected energy

The proposed rate is correct:
\[
\left|t\langle L\circ A\rangle_{\rm loc}
-\frac12\sum_i\frac{t\lambda_i}{t\lambda_i+g}\right|
\le\frac Kt.
\]
Here the observable must be the **original, unlocalised energy**, normalised to have minimum zero—not the \(t\)-dependent potential including the localiser.

There is one missing term in the proposed cubic expansion:
\[
x^3\phi=x^3+ax^4-bx^5+x^3(\phi-1-y).
\]
The omitted \(-bx^5\) is harmless at the required rate, but must appear in the identity.

Indeed, the global Taylor bound
\[
|e^y-1-y|\le \frac{e^M}{2}y^2
\]
gives
\[
|x^3(\phi-1-y)|\le C_1|x|^5+C_2|x|^7.
\]
Use
\[
|x|^5\le\tfrac12(x^4+x^6),\qquad
|x|^7\le\tfrac12(x^6+x^8).
\]
Together with the signed unlocalised cubic rate and \(D\ge1/2\), this proves
\[
t|\langle x^3\rangle_{\rm loc}|=O(t^{-1}).
\]
The quartic term follows directly from \(\phi\le e^M\).

An even shorter analytic route, if convenient in the API, is
\[
|\phi-1|\le e^M|y|,
\]
which bounds \(|x^3(\phi-1)|\) by a combination of \(x^4\) and \(|x|^5\).

**Qualification about E3:** C matches E3’s trace expression **up to \(O(t^{-1})\)**. It does not establish an exact finite-\(t\) LLC identity. Even for a Gaussian target, a displaced anchor generally contributes
\[
t\mathbb E[L]
=\frac12\operatorname{tr}(tHS)+\frac t2\mu^\top H\mu,
\qquad
\mu=gS w_0
\]
in minimum-centred coordinates. For fixed \(g,w_0\), the extra term is \(O(t^{-1})\). Also, since the trace expression itself is \(d/2+O(t^{-1})\), C does not identify the first correction coefficient.

## 2. Reachable bundle in one tide

**Make A + B the committed bundle; C a stretch goal.**

A + B already includes meaningful formalisation work:

- the weighted second-moment estimate;
- normalisation and mean-square bookkeeping;
- localised covariance integrability;
- exact product covariance and rotation transport;
- alignment with `locS_rot`.

C is analytically inexpensive, especially if A exposes its second-moment theorem. But its likely cost is proving the localised energy decomposition and discharging expectation linearity/integrability obligations: the existing unlocalised energy theorem does not automatically supply these for the \(t\)-dependent localised potential.

I would not make completion of C a condition for accepting the tide.

## 3. What A + B certifies against the note

A + B certifies, on the **exact localised Gibbs measure** of the fixed-dimensional rotated separable anharmonic family,
\[
\Sigma(t)=(tH+gI)^{-1}+R(t),\qquad
|R_{jk}(t)|\le K_{jk}t^{-2}.
\]
It also certifies
\[
t\Sigma(t)=H^{-1}+O(t^{-1}).
\]

For fixed positive-definite \(H\), fixed \(g\ge0\), and fixed dimension,
\[
\|S(t)\|\asymp t^{-1}.
\]
Thus the result implies
\[
\|\Sigma(t)-S(t)\|=O(\|S(t)\|^2),
\]
a precise normwise interpretation of the note’s \(O(S^2)\).

It does **not** certify:

- arbitrary nonseparable multivariate anharmonic targets;
- uniform estimates for \(g=g(t)\), moving anchors, or varying dimension;
- an exact Gaussian covariance formula or the \(t^{-2}\) correction coefficient;
- a literal entrywise inequality against the entries of \(S^2\), which may vanish;
- the expected-energy/LLC statement without C;
- any sampling or ULA guarantee.

Suggested wording:

> Establishes eq:cov, with an entrywise \(O(t^{-2})\) remainder, for the exact isotropically localised rotated separable anharmonic Gibbs measure; equivalently, a normwise \(O(\|S\|^2)\) remainder for fixed model parameters.

## 4. Pitfalls and implementation advice

- **Require \(t>0\) explicitly.** The \(g/(2t)\) potential representation and all divisions need it. Use a final threshold \(T\ge1\).
- **Treat the potential pointwise in \(t\).** A \(t\)-dependent argument to `gibbsCov` is harmless, but do not apply a fixed-potential asymptotic theorem to it without justification. Obtain the rates through the weighting identities.
- **Keep original energy and localised potential distinct.** C takes expectation of the former under the latter’s Gibbs measure.
- **Transform the anchor correctly.** If \(w=a+Qu\), the frame anchor is \(Q^\top(w_0-a)\).
- **Track the discarded constant.** The full localiser is
  \[
  e^{-g(x-x_0)^2/2}=e^{-gx_0^2/2}\phi.
  \]
  The constant cancels in normalised expectations, but the relevant normalisers must be nonzero.
- **No \(g>0\) assumption is needed.** At \(g=0\), \(\phi=1\); use \(y\le gx_0^2/2\) without dividing by \(g\).
- **Separate integrability from rates.** Boundedness of \(\phi\) transfers weighted absolute integrability of the required polynomial moments.
- **Check inverse conventions.** Match `locS_rot`’s invertibility hypotheses and the coordinate orientation used in the covariance transport.

**Vote: approve A + B as tide 68’s core. Approve C as an optional, explicitly \(O(t^{-1})\)-accurate localised-energy corollary—not an exact finite-temperature LLC identity.**