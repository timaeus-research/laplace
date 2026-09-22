## 1. Is this the right first step?

**Yes: bounded reweighting is the cleanest first route using the stated seabed results.** It keeps the potential fixed, so all existing constants remain valid. Neither alternative is obviously cheaper:

- **Moving minimum / \(t\)-dependent coefficients:** pointwise asymptotic theorems do not provide the uniformity needed to substitute varying coefficients.
- **Differentiating in \(g\):** the covariance identity is correct, but integrating it requires localised moment bounds uniform over the integration interval. That largely recreates the reweighting argument.

State explicitly that **\(g\ge0\)** is fixed and \(x_0\in\mathbb R\). The bounded-weight argument fails for \(g<0\).

Write
\[
a=gx_0,\qquad M=e^{gx_0^2/2}.
\]
Completing the square gives
\[
\phi(x)=M e^{-g(x-x_0)^2/2},\qquad 0<\phi(x)\le M.
\]
Thus polynomial integrability transfers immediately by domination. The ratio identity follows from
\[
e^{-t\ell(x)-(g/2)(x-x_0)^2}
=e^{-gx_0^2/2}\phi(x)e^{-t\ell(x)}.
\]
Its denominator is strictly positive, not merely asymptotically nonzero.

There is also a useful simplification: **a global bounded-second-derivative estimate for \(\phi\) gives a remainder \(C x^2\)**, eliminating the fifth absolute moment and sixth-moment input entirely.

## 2. The global expansion bound

### Your proposed bound is correct

For every real \(y\),
\[
0\le e^y-1-y
=y^2\int_0^1(1-s)e^{sy}\,ds
\le \frac12 y^2e^{\max(y,0)}.
\]
This handles negative \(y\) without any lower bound on \(y\). If implementing a reusable exponential lemma, this integral Taylor formula—or a second-order Taylor theorem on the segment joining \(0\) and \(y\)—is cleaner than splitting into several exponential inequalities.

Here
\[
y=ax-\frac g2x^2\le \frac{gx_0^2}{2},
\]
and \(M\ge1\). Since
\[
y^2\le 2a^2x^2+\frac{g^2}{2}x^4,
\]
we obtain
\[
\boxed{
|\phi(x)-1-ax|
\le \left(\frac g2+Ma^2\right)x^2+\frac{Mg^2}{4}x^4.
}
\]
So explicit valid constants are
\[
C_1=\frac g2+Ma^2,\qquad C_2=\frac{Mg^2}{4}.
\]

For integration, I would retain **\(C_1x^2+C_2x^4\)**: it matches the available moment lemmas directly. A single constant multiplying \(x^2+x^4=x^2(1+x^2)\) is equivalent but provides no mathematical advantage.

I would not assume that the named Mathlib lemmas already give the unrestricted result; check their actual signatures. The mathematical helper lemma should state the unrestricted bound above.

### A cleaner bound specific to this weight

Differentiation gives
\[
\phi''(x)=\bigl((a-gx)^2-g\bigr)\phi(x).
\]
Set \(z=g(x-x_0)^2/2\ge0\). Then
\[
|\phi''(x)|=gM|2z-1|e^{-z}
\le gM(2z+1)e^{-z}\le 3gM,
\]
using \(e^{-z}\le1\) and \(ze^{-z}\le1\). Taylor’s theorem therefore yields
\[
\boxed{|\phi(x)-1-ax|\le \frac32gM\,x^2.}
\]
This also covers \(g=0\), where the weight is identically one.

**Recommendation:** use whichever helper is cheaper in the local Mathlib environment. The exponential remainder lemma is more reusable; the bounded-\(\phi''\) argument produces the simpler downstream proof.

## 3. Absolute moments and the remainder orders

The Young argument is sound. For \(t>0\), take \(\varepsilon=t^{-1/2}\). Pointwise,
\[
2|x|^3\le \varepsilon x^2+\varepsilon^{-1}x^4,
\qquad
2|x|^5\le \varepsilon x^4+\varepsilon^{-1}x^6.
\]
After integration,
\[
\begin{aligned}
\langle|x|^3\rangle_t
&\le \tfrac12\left(t^{-1/2}\langle x^2\rangle_t+
t^{1/2}\langle x^4\rangle_t\right)
=O(t^{-3/2}),\\
\langle|x|^5\rangle_t
&\le \tfrac12\left(t^{-1/2}\langle x^4\rangle_t+
t^{1/2}\langle x^6\rangle_t\right)
=O(t^{-5/2}).
\end{aligned}
\]
Convergence of \(t^3\langle x^6\rangle_t\) suffices: only an eventual bound is needed.

The seabed having “signed moments” is no obstruction: even powers are nonnegative and equal the corresponding absolute powers. Integrability of the odd absolute powers also follows by polynomial domination.

Cauchy–Schwarz gives the same orders:
\[
\langle|x|^3\rangle_t
\le\sqrt{\langle x^2\rangle_t\langle x^4\rangle_t},
\quad
\langle|x|^5\rangle_t
\le\sqrt{\langle x^4\rangle_t\langle x^6\rangle_t}.
\]
For Lean, weighted Young is an excellent choice when expectations are expressed directly as normalised integrals: it avoids setting up an \(L^2\) or probability-measure interface.

**I cannot determine from the name alone whether `abs_moment_scaling` already supplies these estimates.** A scaling identity is not itself an eventual bound; check whether its hypotheses and conclusion include the necessary control of the rescaled integral. Nothing beyond the documented moments is needed here.

### Checking the proposed numerator and denominator

Let
\[
m=-\frac{\alpha}{2\lambda^2},\qquad
c=m+\frac a\lambda,\qquad
N_t=\langle x\phi\rangle_t,\quad D_t=\langle\phi\rangle_t.
\]
The existing rates imply
\[
\langle x\rangle_t=\frac mt+O(t^{-2}),
\qquad
\langle x^2\rangle_t=\frac1{\lambda t}+O(t^{-2}).
\]
Your expansion therefore gives
\[
N_t=\frac ct+O(t^{-3/2}),\qquad D_t=1+O(t^{-1}).
\]
Both claimed remainder orders are correct. In particular, **the denominator estimate uses the signed mean bound**
\(\langle x\rangle_t=O(t^{-1})\), not the weaker absolute-first-moment bound.

Using the \(Cx^2\) weight remainder gives exactly these conclusions with only \(\langle|x|^3\rangle_t\), hence only the second and fourth moments.

## 4. The most useful theorem for the note

I would make the leading-order quantitative theorem the main result:
\[
\boxed{
\exists K\ge0,\ \exists T\ge1,\ \forall t\ge T,\quad
\left|t\langle x\rangle_{\rm loc}
-\left(-\frac{\alpha}{2\lambda^2}+\frac{gx_0}{\lambda}\right)\right|
\le \frac K{\sqrt t}.
}
\]

For the final division step, choose \(T\) so that \(D_t\ge1/2\), and use
\[
\left|t\frac{N_t}{D_t}-c\right|
=\frac{|(tN_t-c)-c(D_t-1)|}{D_t}
\le 2|tN_t-c|+2|c|\,|D_t-1|.
\]
This makes the dependence on the denominator estimate explicit.

I would call this a **rate for the scaled mean**, rather than a “relative remainder”: \(c\) can vanish.

### Add a corollary in the note’s exact notation

For \(S=(t\lambda+g)^{-1}\), set
\[
P_t=-\frac{\alpha t}{2(t\lambda+g)^2}+\frac{gx_0}{t\lambda+g}.
\]
Direct expansion gives
\[
P_t=\frac ct+
\frac1{t^2}\left(\frac{\alpha g}{\lambda^3}
-\frac{g^2x_0}{\lambda^2}\right)+O(t^{-3}).
\]
Consequently your theorem implies
\[
\boxed{
|\langle x\rangle_{\rm loc}-P_t|
\le K' t^{-3/2}
}
\]
eventually. This is the most direct bridge to eq:mean.

**Scope matters:** this certifies the localisation contribution at leading order for the anharmonic measure. It does **not** certify eq:mean’s stated \(O(S^2)=O(t^{-2})\) remainder. The reviewer caveat should be narrowed accordingly, not removed wholesale.

### Optional stronger follow-up

The sharper rate is accessible with an additional integration-by-parts lemma. Indeed,
\[
0=\lambda\langle x\rangle_t+
\frac{\alpha}{2}\langle x^2\rangle_t+
\frac{\gamma}{6}\langle x^3\rangle_t.
\]
The leading terms cancel, so the existing mean and second-moment rates imply
\[
\langle x^3\rangle_t=O(t^{-2}).
\]
A second-order expansion
\[
\phi(x)=1+ax+\frac{a^2-g}{2}x^2+O(|x|^3)
\]
with a global remainder bound—available from bounded \(\phi'''\)—then yields
\[
N_t=\frac ct+O(t^{-2}),
\]
using the signed third and fourth moments. This would upgrade the scaled-mean rate to \(K/t\), and the note-form remainder to \(O(t^{-2})\). It is a reasonable separate target, not a prerequisite for the first result.

## Vote

**YES on A+B+C**, with these refinements:

- **A:** preferably prove the stronger \(Cx^2\) weight bound.
- **B:** use weighted Young with the second and fourth moments; omit the sixth-moment dependency if A is strengthened.
- **C:** prove the scaled-mean theorem and add the \(S=(t\lambda+g)^{-1}\) corollary, explicitly labelling this as leading-order certification rather than the full \(O(S^2)\) claim.