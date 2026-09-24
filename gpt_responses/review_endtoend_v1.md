## Executive assessment

The statement looks mathematically sound **as a conditional pure-power theorem**, subject to a few implementation checks below. Its main limitation is not an obviously false conclusion: it is that its analytic hypotheses can exclude irrelevant charts, logarithmic charts, and amplitudes whose leading restriction vanishes.

In particular:

- Feasibility alone is not an asymptotic certificate; your integrability hypothesis supplies the missing coercivity.
- The mixed scaled/unscaled limiting domain and the limiting face-point unit are correct.
- The denominator condition is not circular, but it is substantial.
- For logarithmic faces, the general answer is **optimal-face volume times a transverse profile integral**, not universally your displayed Gamma product.
- A useful short next theorem is a two-sided logarithmic comparison for a separable tied block. A general moving-cutoff exact constant requires an additional polyhedral tube argument.

I cannot certify the Lean dependencies from the statement alone. The comments below concern the mathematical content represented by the records.

---

# 1. Adversarial review

## 1.1 What the theorem actually certifies

For each term, your assumptions certify
\[
K_p(t)=t^{-\lambda_p}(C_p+o(1)).
\]
Finite assembly then gives the ratio conclusion when the common leading denominator coefficient is nonzero.

This does **not** yet assert that every resolved analytic loss admits such a certificate. In particular, it does not automatically cover:

1. logarithmic leading terms;
2. exponentially small terms;
3. weights vanishing on the relevant limiting strata;
4. charts whose unweighted profile is nonintegrable although their actual weighted kernel is harmless.

That distinction should appear prominently in the theorem documentation.

### A significant strength of the current hypotheses

You require integrability for **every admissible term**, not just the terms relevant to the leading scale.

Consequently, a subleading logarithmic chart can prevent application of this theorem even if its contribution is negligible relative to the leading pure-power terms. An identically zero weighted chart can do the same, because `ProfileIntegrableOf` does not see the weight.

A later assembly theorem should allow each term either:

- a normalized limit at the chosen scale; or
- a proof that it is negligible at that scale.

It should not require a full nonzero asymptotic description of every term.

## 1.2 Profile integrability versus LP uniqueness

Write
\[
c_j=r_j+1,\qquad
P=\{\alpha\ge0:Q\cdot\alpha\le\gamma,\ \kappa\cdot\alpha\ge\delta\}.
\]
The relevant LP is minimizing \(c\cdot\alpha\) on \(P\).

Your expectation is essentially right in the standard nondegenerate, full-positive-profile setting:

> A feasible rescaling has an integrable positive transverse profile precisely when it is an isolated optimal scale, rather than belonging to a nontrivial optimal face.

But I would **not state this equivalence yet for your actual record** without specifying its scope.

The underlying recession argument is straightforward. A competing feasible direction becomes an unbounded logarithmic direction in the \(u\)-domain:

- if it improves the objective, the profile grows along that direction;
- if it preserves the objective, the profile has a nondecaying logarithmic direction;
- either behavior obstructs integrability.

The equivalence needs hypotheses ensuring that this recession analysis really describes the profile: positive bounded units on the relevant profile domain, a nonempty domain, and suitable attainment/coercivity conditions.

Three qualifications matter.

### First: the record tests an unweighted profile

Your hypothesis deliberately ignores \(W_0\). Thus it may fail although
\[
W_0(u)\prod u_j^{r_j}e^{-\Phi_0(u)}
\]
is integrable, or identically zero.

A vanishing partition weight or amplitude can kill a troublesome stratum. The unweighted LP need not describe the actual weighted kernel sharply.

### Second: the unit bounds must cover the domain used in the test

Your profile domain is a box with a monomial cutoff, whereas the geometric chart is supported in a Euclidean ball. Points satisfying
\[
0<u_j<\rho,\qquad 0<v<\rho
\]
need not lie in that ball.

Check exactly where `a`, `b`, and `wt` have their asserted bounds and support properties. One clean implementation is:

- globally extend the positive unit with uniform positive bounds;
- extend the weight by zero;
- integrate on the box.

If the unit bounds hold only on the ball, an equivalence involving the **unweighted box profile** needs extra care.

### Third: nonattainment is a separate issue

For a general abstract LP, “not a positive-dimensional optimal face” does not by itself imply a good pure-power profile. One should separately establish existence of an optimum and the required transverse coercivity.

**Recommended standalone theorem:** a recession-cone characterization of profile integrability, followed by LP uniqueness as a corollary under explicit assumptions.

## 1.3 The limiting domain is correct

Your rescaling gives
\[
x_j=t^{-\alpha_j}u_j,\qquad
v_t=D\,t^{(-\gamma+Q\cdot\alpha)/q_k}
       \prod_j u_j^{-Q_j/q_k}.
\]

Hence:

- if \(\alpha_j=0\), the constraint \(x_j<\rho\) remains \(u_j<\rho\);
- if \(\alpha_j>0\), it disappears in the limit;
- if \(Q\cdot\alpha<\gamma\), then \(v_t\to0\);
- if \(Q\cdot\alpha=\gamma\), the remaining cutoff is exactly
  \[
  D\prod_j u_j^{-Q_j/q_k}<\rho.
  \]

The mixing of scaled and unscaled coordinates in this final inequality is necessary, not suspicious.

Two proof obligations deserve explicit tests:

1. convergence of domain indicators away from cutoff boundaries;
2. nullity of those boundaries.

In the tied-cutoff case, \(\gamma>0\) ensures that some positive-\(\alpha\) coordinate has positive \(Q_j\). This gives a genuinely nonconstant monomial cutoff and the expected null boundary.

The Euclidean-ball support should remain encoded in \(W\), not silently replaced by the box.

## 1.4 The limiting unit is also correct

Yes:
\[
a_0(u)=|a(u_\infty)|
\]
is the correct limiting unit.

Replacing this by \(a(0)\) would generally be wrong. Coordinates with \(\alpha_j=0\) survive, and the solved coordinate also survives when the cutoff is tied.

This matters even for an isolated LP optimum: the coefficient can be a genuine integral of a nonconstant face-restricted unit.

Also check that the phase identity justifies replacing the signed unit by its absolute value on every branch. Nonnegativity of \(F\) gives the needed compatibility, but that compatibility should be a proved part of the branch reduction.

## 1.5 The denominator condition is not circular

With nonnegative data, all term constants are nonnegative. Your condition means at least one selected denominator profile contributes positively.

It is a condition on explicit limiting chart data, not on the unknown asymptotic ratio. So there is no circularity.

It is nevertheless stronger than “\(\chi\) is not identically zero.” The amplitude must be nonzero on a leading limiting stratum, on a set of positive profile measure.

If \(\chi\) vanishes there, its next asymptotic scale can be quite arbitrary for merely continuous \(\chi\). There is no general finite power-log expansion for arbitrary continuous amplitudes.

A useful sufficient-condition lemma would say:

> If \(W_0^\chi>0\) on a positive-measure subset of one dominant admissible profile domain, then the denominator coefficient is positive.

## 1.6 Other concrete checks

### Inadmissible terms in the lower-bound condition

You require
```lean
∀ p, lam₀ ≤ P.termLam γ α p
```
even for inadmissible terms whose constants and kernels are zero.

This is sound but unnecessarily restrictive. Prefer the inequality only for admissible terms, or directly require negligibility/limits at `lam₀`.

### Thin \(A'\)

Because \(\psi,\chi\) are globally continuous and supported inside the cylinder over \(A'\), they must vanish if that cylinder has empty interior.

Thus some allowed compact sets \(A'\), including nonempty ones, make the nonzero-denominator premise impossible. This is harmless logically, but worth documenting.

### Strictly positive losses

If \(F\) is bounded away from zero on the relevant support, polynomial normalization cannot yield a positive coefficient. The antecedents must then fail somewhere. Again: correct conditional behavior, not a universal asymptotic theorem.

### Pointwise versus almost-everywhere fibre transport

An ambient push-forward identity generally gives a fibre identity only almost everywhere in the truth parameter. Your theorem follows the particular curve \(s=\sigma t^{-\gamma}\), so it needs a **pointwise identity at nonzero \(s\)**.

If `WallChartsData` already proves precisely that, excellent. If it was obtained solely by disintegration, this is a critical gap to check. Zero `sorry` does not distinguish these two mathematical statements.

---

# 2. Toy chart

For the identity-chart integral
\[
I_\phi(t)=\int_{A'}
 e^{-\sigma^2t^{1-2\gamma}(1+x^2)x^2}
 \phi(\sigma t^{-\gamma},x)\,dx,
\]
you have \(p=0\), \(r=0\), \(Q=0\), \(\kappa=2\).

## \(0<\gamma<1/2\)

The scale is
\[
\alpha=\frac{1-2\gamma}{2},\qquad \lambda=\alpha.
\]
Assuming the integration/support geometry contains the origin with both sides,
\[
I_\phi(t)\sim
\frac{\sqrt\pi}{|\sigma|}\phi(0,0)\,
t^{-(1-2\gamma)/2},
\]
when \(\phi(0,0)>0\). Without that positivity, the safe statement is convergence of the normalized integral to the displayed coefficient.

## \(\gamma=1/2\)

Choose \(\alpha=0\). Then \(\delta=0\), and the phase survives without concentration:
\[
I_\phi(t)\longrightarrow
\int_{A'}e^{-\sigma^2(1+x^2)x^2}\phi(0,x)\,dx.
\]

Your limiting profile is on the bounded, unscaled domain and retains the nonconstant unit \(1+x^2\). This is exactly what it should do.

## \(\gamma>1/2\)

Again choose \(\alpha=0\). Now \(\delta<0\), so the limiting phase is zero:
\[
I_\phi(t)\longrightarrow\int_{A'}\phi(0,x)\,dx.
\]

Thus the theorem is **not vacuous** here. The profile integrability conditions hold on the bounded domain in this toy, and the ratio theorem gives the corresponding ratios of these integrals whenever the denominator limit is positive.

---

# 3. Logarithmic faces: the general exact constant

## 3.1 Use logarithmic coordinates, not one chosen power rescaling

Set
\[
L=\log t,\qquad x_j=\rho e^{-z_j},\qquad c_j=r_j+1.
\]
The kernel becomes
\[
K(t)=A\,t^{-\gamma p}\rho^{\sum c_j}
\int_{\substack{z\ge0\\Q\cdot z<\gamma L+d_Q}}
W_t(z)e^{-c\cdot z}
\exp\!\left[-B\rho^{\sum\kappa_j}
a_t(z)e^{\delta L-\kappa\cdot z}\right]dz,
\]
where
\[
d_Q=q_k\log(\rho/D)+\Bigl(\sum_jQ_j\Bigr)\log\rho.
\]

Let
\[
\mu=\min_{\alpha\in P}c\cdot\alpha,\qquad
\mathcal F=\{\alpha\in P:c\cdot\alpha=\mu\}.
\]
Assume for now that \(\mathcal F\) is nonempty, compact, and has dimension \(k\).

The expected normalization is
\[
t^{\gamma p+\mu}(\log t)^{-k}.
\]

This makes the source of the logarithm explicit: the dominant \(z\)-region extends a distance of order \(L\) in each of the \(k\) face directions.

## 3.2 Tangential and transverse coordinates

Let
\[
T=\operatorname{span}(\mathcal F-\mathcal F),\qquad N=T^\perp.
\]
Use the orthogonal decomposition
\[
z=L\alpha+y,\qquad \alpha\in\operatorname{aff}\mathcal F,\quad y\in N.
\]
Its Jacobian is \(L^k\), with the induced Euclidean measures.

For relative-interior points of \(\mathcal F\), the active constraints are constant. Define

- \(I_0=\{j:\alpha_j=0\text{ throughout }\mathcal F\}\);
- \(E_Q\): \(Q\cdot\alpha=\gamma\) throughout \(\mathcal F\);
- \(E_\kappa\): \(\kappa\cdot\alpha=\delta\) throughout \(\mathcal F\).

The limiting transverse domain is
\[
\mathcal Y=
\{y\in N:y_j\ge0\ (j\in I_0),\
             Q\cdot y<d_Q\text{ if }E_Q\}.
\]

The physical limiting point has unsolved magnitudes
\[
x_{\infty,j}(y)=
\begin{cases}
\rho e^{-y_j},&j\in I_0,\\
0,&j\notin I_0,
\end{cases}
\]
and solved magnitude
\[
v_\infty(y)=
\begin{cases}
D\rho^{-\sum Q_j/q_k}e^{Q\cdot y/q_k},&E_Q,\\
0,&\neg E_Q.
\end{cases}
\]
Insert the orthant and branch signs as usual.

The limiting phase is
\[
H(y)=
\begin{cases}
B\rho^{\sum\kappa_j}|a(u_\infty(y))|e^{-\kappa\cdot y},
   &E_\kappa,\\
0,&\neg E_\kappa.
\end{cases}
\]

Subject to a suitable domination/localization theorem, the exact coefficient is
\[
\boxed{
A\rho^{\sum c_j}\,
\operatorname{Vol}_k(\mathcal F)
\int_{\mathcal Y}
W_\infty(y)e^{-c\cdot y}e^{-H(y)}\,dy_N.
}
\]

The Euclidean face volume and transverse measure must use compatible normalization. With another linear coordinate system, include its determinant.

## 3.3 Does the unit average over the face?

For these chart kernels, generally **not over the relative interior of the logarithmic face**.

Every relative-interior exponent vector collapses exactly the same physical coordinates. Thus, for fixed transverse \(y\), it produces the same \(u_\infty(y)\).

The tangential integration contributes face volume. The unit remains inside the **transverse integral**.

Boundary subfaces can have different physical limiting points. They are lower-dimensional and should not affect the leading coefficient **provided the transverse integrability and boundary-tail estimates hold**. Proving that proviso is one of the substantive analytic tasks.

## 3.4 Why the Gamma product is not universal

Your `tendsto_general` is the case where the transverse integral separates.

Even there, a constant phase multiplier \(a_*\) contributes \(a_*^{-\eta}\), not \(a_*\), where \(\eta\) is the tied monomial ratio.

For effective parameter \(B t^\delta\), the coefficient also acquires
\[
B^{-\eta}\delta^k.
\]
Indeed,
\[
(Bt^\delta)^{-\eta}
\bigl(\log(Bt^\delta)\bigr)^k
\sim B^{-\eta}\delta^k t^{-\delta\eta}(\log t)^k
\]
when \(\delta>0\).

Crucially, the Gamma argument \(\eta\) is not generally the total chart exponent
\[
\gamma p+\mu.
\]

If unscaled coordinates survive, the exact answer can contain an integral of
\[
W_\infty(u)\,a_\infty(u)^{-\eta}
\]
against a nontrivial transverse density. With an active moving cutoff, even that simplification need not survive.

## 3.5 Moving cutoff with \(Q_j>0\)

There are three cases.

1. **Strict on the relative interior:**  
   \(Q\cdot\alpha<\gamma\).  
   The solved coordinate tends to zero. The cutoff can still truncate the allowable optimal face, thereby changing its volume.

2. **Active throughout the optimal face:**  
   \(Q\cdot\alpha=\gamma\).  
   The cutoff survives in \(\mathcal Y\), and \(v_\infty(y)\) may be nonzero. Both the unit and the weight retain dependence on it.

3. **Active only on a boundary subface:**  
   It contributes no additional leading transverse constraint on the relative interior, but boundary localization must show that its neighborhood is negligible at the leading normalization.

For example, an unconstrained optimal segment
\[
\alpha_1+\alpha_2=\delta,\qquad \alpha_i\ge0
\]
cut by \(\alpha_1\le\gamma\) has its leading logarithmic length changed from the full segment to the truncated one. A universal unchanged \(1/k!\) coefficient would miss this.

## 3.6 The appropriate `DominantScaleHyp` analogue

A useful `LogFaceScaleHyp` should package:

1. a compact \(k\)-dimensional optimal polytope;
2. a tangential/transverse coordinate map and Jacobian;
3. almost-everywhere convergence of the normalized pulled-back integrand to
   \[
   1_{\mathcal F}(\alpha)\,G(y);
   \]
4. an integrable domination, **or** local domination plus uniform control of transverse tails and face-boundary neighborhoods;
5. identification of \(G\) with the chart profile.

Then dominated convergence gives
\[
t^{\gamma p+\mu}(\log t)^{-k}K(t)
\to \operatorname{Vol}_k(\mathcal F)\int G.
\]

The abstract convergence theorem can be short. Constructing this record from arbitrary constrained monomial data is the substantial new theorem.

---

# 4. A realistic short logarithmic theorem

For a first result using `tendsto_general`, I would restrict to \(Q=0\): truth depends only on the solved coordinate. Then \(v_t=D t^{-\gamma/q_k}\), and the moving cutoff is eventually automatic.

Assume:

- \(\delta>0\);
- all \(\kappa_j>0\);
- \(c_j=r_j+1\);
- a tied set \(J\) has cardinality \(k+1\), with
  \[
  c_i/\kappa_i=\eta>0\quad(i\in J);
  \]
- \(c_j/\kappa_j>\eta\) off \(J\);
- \(a_-\le |a|\le a_+\);
- \(0\le W_t\le w_+\) on the whole box;
- \(W_t\ge w_->0\) eventually on a smaller box \((0,R_-)^m\).

Define
\[
\mathcal C(R,a,w)=
A w\,\delta^k(Ba)^{-\eta}
R^{\sum_j(c_j-\eta\kappa_j)}
\frac{\Gamma(\eta)}{k!}
\prod_{i\in J}\frac1{\kappa_i}
\prod_{j\notin J}\frac1{c_j-\eta\kappa_j}.
\]
Set
\[
\Lambda=\gamma p+\delta\eta.
\]

Then prove
\[
\mathcal C(R_-,a_+,w_-)
\le
\liminf_{t\to\infty}\frac{t^\Lambda}{(\log t)^k}K(t)
\le
\limsup_{t\to\infty}\frac{t^\Lambda}{(\log t)^k}K(t)
\le
\mathcal C(\rho,a_-,w_+).
\]

The bounds follow directly from
\[
w_-e^{-Ba_+t^\delta\prod x^\kappa}
\le W_t e^{-Bt^\delta a_t\prod x^\kappa}
\le w_+e^{-Ba_-t^\delta\prod x^\kappa},
\]
using the smaller box for the lower bound, followed by box scaling and `tendsto_general`.

For Lean, an eventual \(\varepsilon\)-sandwich may be easier than `liminf`:
\[
\forall\varepsilon>0,\quad
\forall^\infty t,\quad
C_- -\varepsilon
\le \frac{t^\Lambda}{(\log t)^k}K(t)
\le C_+ +\varepsilon.
\]

This looks like a plausible few-hundred-line target with your existing infrastructure. I would not promise the same bound for the arbitrary active-cutoff polyhedral theorem.

The lower weight assumption is realistic on a small chart core where the limiting amplitude and partition weight are positive; it should not be imposed on the whole chart box.

---

# 5. Most valuable next theorem

My recommendation is:

> **Finite power-log assembly allowing negligible terms, with lexicographic dominance.**

Normalize each term by \(t^{\lambda_p}/(\log t)^{k_p}\). The dominant pair has:

1. smallest \(\lambda_p\);
2. among those, largest \(k_p\).

Allow other terms to be supplied merely with an \(o\)-bound at that common normalization. Then prove the expectation-ratio theorem from the summed dominant coefficients.

This has immediate value:

- it contains your existing pure-power assembly;
- it removes the requirement to certify irrelevant charts at their own scales;
- it accepts `tendsto_general` terms immediately;
- it cleanly separates geometric chart reduction from increasingly sophisticated analytic certificates.

After that, prove the \(Q=0\) logarithmic comparison above. The general polyhedral `LogFaceScaleHyp` construction should be the next research milestone—not a small corollary of the existing monomial theorem.