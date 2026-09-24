The partially tied formula is right, with an explicit **\(\delta^k\)** in the constant when the normalization uses \((\log t)^k\). There is also a useful exact product identity. For tied truth, the cutoff really does supply a second independent coercive constraint: two scaled coordinates can then be integrable, and their constant-unit model has an explicit formula.

My main soundness flags are: **integrability versus merely measurable observables**, **carried-by versus topological support**, and the **source domains of the stated two-chart partition**.

## (a) Partially tied faces

Write
\[
a_j=r_j+1,\qquad
\lambda=\min_j\frac{a_j}{\kappa_j},\qquad
T=\{j:a_j=\lambda\kappa_j\},\qquad |T|=k+1.
\]
Assume \(\delta,c,\rho>0\), \(\kappa_j>0\), and \(\lambda>0\). Then
\[
\boxed{
\lim_{t\to\infty}
\frac{t^{\delta\lambda}}{(\log t)^k}K(t)
=
\frac{\delta^k\Gamma(\lambda)}
{k!\prod_{i\in T}\kappa_i}\,
c^{-\lambda}
\prod_{j\in N}
\frac{\rho^{a_j-\lambda\kappa_j}}
{a_j-\lambda\kappa_j}.
}
\]
Thus your formulation is correct if \(C_{\rm tied}(T)\) includes that \(\delta^k\).

### Exact identity for the tied block

Define
\[
TB(s)=\int_{(0,\rho)^T}
\prod_{i\in T}x_i^{a_i-1}
e^{-s\prod_{i\in T}x_i^{\kappa_i}}\,dx_T,
\qquad
R=\rho^{\sum_{i\in T}\kappa_i}.
\]
The product substitution gives
\[
\boxed{
TB(s)=
\frac1{k!\prod_{i\in T}\kappa_i}
\int_0^R
v^{\lambda-1}
\bigl(\log(R/v)\bigr)^k e^{-sv}\,dv.
}
\]
This is probably the cleanest reusable analytic lemma. It yields both
\[
TB(s)\sim
\frac{\Gamma(\lambda)}{k!\prod_{i\in T}\kappa_i}
s^{-\lambda}(\log s)^k
\]
and your all-scale estimate
\[
TB(s)\le C\,s^{-\lambda}\bigl(\log(2+s)\bigr)^k,
\qquad s>0.
\]

Your dominated-convergence argument then works exactly as proposed. Put
\[
P(x_N)=\prod_{j\in N}x_j^{\kappa_j}.
\]
Because \(P\) is bounded above, for \(t\ge2\),
\[
\frac{t^{\delta\lambda}}{(\log t)^k}
TB(ct^\delta P)
\le C'P^{-\lambda}.
\]
After multiplying by the remaining monomial density, the majorant is
\[
C'\prod_{j\in N}x_j^{a_j-\lambda\kappa_j-1},
\]
which is integrable precisely because the gaps are strict. **No additional \(|\log x_N|\) majorant is needed.**

### LP meaning

For the box-only model, the relevant LP is
\[
\min a\cdot\alpha
\quad\text{subject to}\quad
\alpha\ge0,\quad \kappa\cdot\alpha\ge\delta.
\]
Its minimizing face is
\[
\alpha_N=0,\qquad
\sum_{i\in T}\kappa_i\alpha_i=\delta,\qquad
\alpha_T\ge0.
\]
It has dimension \(k\). This is the geometric meaning of partial tying here: a positive-dimensional minimizing face, with the strictly worse coordinates fixed at zero.

### What changes with scaled coordinates?

A crucial distinction is between:

* a finite-\(t\) integral whose scales range over a minimizing face; and
* a single limiting branch integral with some coordinates already extended to \((0,\infty)\).

The second need not exist when the first has a perfectly good logarithmic asymptotic.

For example, take exactly one scaled coordinate \(s\), with \(\kappa_s>0\), and boxed coordinates \(B\). Put
\[
\eta=\frac{a_s}{\kappa_s}.
\]
Then the constant-unit limiting integral is exactly
\[
\int_{(0,\infty)\times(0,\rho)^B}
u^{a-1}e^{-c u^\kappa}\,du
=
\frac{\Gamma(\eta)}{\kappa_s}c^{-\eta}
\prod_{j\in B}
\frac{\rho^{a_j-\eta\kappa_j}}
{a_j-\eta\kappa_j},
\]
provided
\[
\eta>0,\qquad a_j-\eta\kappa_j>0\quad(j\in B).
\]
A tie with any boxed coordinate makes this integral diverge logarithmically. It is then a signal to **assemble a face asymptotic**, not to certify that individual branch by dominated convergence.

So the strict-truth obstruction is a little broader than “two scaled coordinates fail”:

* two scaled coordinates give the kernel-direction obstruction you proved;
* one scaled coordinate tied with a boxed coordinate also gives a nondecaying recession direction;
* neither statement rules out logarithmic asymptotics of the original finite-\(t\) integral.

## (b) Tied truth: a two-constraint certificate

Here is a concrete formulation that avoids ambiguity about signs.

Assume \(q>0\), \(D,\rho>0\), and write the cutoff as
\[
D\prod_j u_j^{-Q_j/q}<\rho
\quad\Longleftrightarrow\quad
Q\cdot v>h_0,
\qquad
v_j=\log u_j,\quad h_0=q\log(D/\rho).
\]
Let \(S\) be the scaled coordinates and \(B\) the boxed coordinates. In logarithmic coordinates the constant-unit integral has density
\[
e^{a\cdot v}e^{-c e^{\kappa\cdot v}},
\]
on
\[
v_j<\log\rho_j\quad(j\in B),\qquad Q\cdot v>h_0.
\]

### Recession obstruction

The cone on which the exponential does not supply growing suppression is
\[
\boxed{
\mathcal C=
\{d:\ d_B\le0,\ \kappa\cdot d\le0,\ Q\cdot d\ge0\}.
}
\]
The integrability condition to target is
\[
a\cdot d<0
\qquad\text{for every nonzero }d\in\mathcal C.
\]

The old kernel direction remains an obstruction only if its chosen orientation also satisfies \(Q\cdot d\ge0\). You can no longer independently choose its orientation to make \(a\cdot d\ge0\).

In particular:

* with two scaled coordinates, \(\kappa\cdot d=0\) need not imply \(Q\cdot d=0\), so the cutoff can remove the bad orientation;
* with at least three scaled coordinates, there is a nonzero direction supported there satisfying both
  \[
  \kappa\cdot d=Q\cdot d=0.
  \]
  Both orientations remain in the cone, so one has \(a\cdot d\ge0\).

Thus, for this constant-unit model with one exponential monomial and one cutoff, the obstruction moves from **two scaled coordinates to three**. Additional decay in the amplitude could change that conclusion.

### Explicit two-scaled-coordinate theorem

Suppose \(S=\{s_1,s_2\}\) and
\[
\Delta=
\det\begin{pmatrix}
\kappa_{s_1}&\kappa_{s_2}\\
Q_{s_1}&Q_{s_2}
\end{pmatrix}\ne0.
\]
Solve uniquely for \(\eta,\theta\) from
\[
a_S=\eta\kappa_S-\theta Q_S,
\]
and define
\[
\beta_j=a_j-\eta\kappa_j+\theta Q_j,\qquad j\in B.
\]
A particularly tractable certificate is
\[
\boxed{\eta>0,\qquad\theta>0,\qquad\beta_j>0\ \text{for every }j\in B.}
\]

Indeed, substitute
\[
w=\kappa\cdot v,\qquad h=Q\cdot v,
\]
retaining \(v_B\). The integral factors completely:
\[
\boxed{
\int_{\substack{u_S>0,\ 0<u_j<\rho_j\\Q\cdot\log u>h_0}}
u^{a-1}e^{-c u^\kappa}\,du
=
\frac{\Gamma(\eta)c^{-\eta}}{|\Delta|}
\frac{e^{-\theta h_0}}{\theta}
\prod_{j\in B}\frac{\rho_j^{\beta_j}}{\beta_j}.
}
\]
For this exact model, these strict inequalities are also necessary for finiteness.

This is an excellent certificate theorem because the same calculation supplies:

1. integrability;
2. the exact constant;
3. a recession interpretation;
4. a domination theorem for bounded amplitudes and units bounded below.

In the LP convention
\[
\kappa\cdot\alpha\ge\delta,\qquad Q\cdot\alpha\le\gamma,
\]
the decomposition
\[
a=\eta\kappa-\theta Q+\sum_{j\in B}\beta_j e_j
\]
is precisely the corresponding strict dual certificate. Two independent active constraints can isolate two scaled coordinates. If your truth inequality uses the opposite convention, reverse the \(Q\)-sign accordingly.

## (c) Soundness pass on 1–5

This is a mathematical interface audit, not an audit of the Lean declarations or their assumptions.

### 1. Limiting measure

The construction is the right one. I would inspect four interfaces.

* **Measurable versus integrable observables.** “For measurable \(\varphi\)” can be appropriate for a pushforward identity, especially for nonnegative functions. It does not by itself justify a finite signed integral or asymptotic convergence. In Lean, totalized integrals make explicit integrability hypotheses particularly important.
* **Finite mass.** Establish `IsFiniteMeasure μ` or its equivalent, rather than leaving finiteness implicit in the individual constants.
* **Denominator positivity.** The ratio theorem needs \(\int\chi\,d\mu\ne0\), usually established as strict positivity.
* **Carried-by versus support.** “Vanishes off the face images” is a concentration statement. Topological support is generally contained in the **closure** of their union, not necessarily in the images themselves. Measurability of those images also deserves attention.

For point evaluation, your hypothesis is sufficient but stronger than necessary: it is enough that every dominant face map equals the **same** \(z_0\) almost everywhere for its source measure. Constancy term by term at potentially different points instead yields a weighted atomic measure.

### 2. Exact log constant

The global bounds and local continuity are exactly the right separation of responsibilities.

Check explicitly:

* the power of the effective large parameter, hence the \(\delta^k\) factor;
* positivity of the limiting unit and \(\lambda>0\);
* branch multiplicities and Jacobian constants;
* the precise meaning of continuity when the original box is open and the face lies on its boundary.

Also, “the indicator is invisible” should be an explicit implication on the support of the observable, or a proved almost-everywhere statement. Support in \(L'\) alone is not a substitute unless the relevant map into \(L\) has been connected to it.

### 3. Lexicographic assembly

Sound, provided the term family is finite and each expansion is certified at its own scale.

Two caveats are worth exposing in the API:

* dominance means smaller power exponent first, then larger log degree;
* signed leading constants can cancel.

The denominator should therefore select a genuinely nonzero dominant total. Positive amplitudes and a nonnegative reference observable make this much cleaner.

### 4. Two scaled coordinates

The stated direction argument is sound when:

* scaled logarithmic coordinates really are unrestricted;
* strict truth supplies no surviving cutoff;
* no additional amplitude decay suppresses the direction.

The result should be advertised as an obstruction to that branch certificate or limiting monomial integral—not as an obstruction to an asymptotic expansion of the original integral.

### 5. Two-chart example

There is one concrete domain issue to check.

If **both chart source boxes are literally \((0,1)^2\)**, then
\[
(x,xy)
\]
only covers \(z_1<z_0\), but your \(\omega_A\) is positive throughout \(z_1<2z_0\). For instance, it is positive where \(z_0<z_1<2z_0\), outside that chart image.

Thus the specified partition requires a larger ratio domain for chart A, together with the physical unit-box cutoff. There is no problem if “over the unit box” refers to the target and this enlarged source domain is already implemented.

Beyond that:

* \(\sigma>0\) is substantive; nothing stated implies uniformity as \(\sigma\downarrow0\).
* Chart B’s \(x^{-2}\) profile needs its own domination argument near \(x=0\); calling the vertex collapsed does not remove that singularity.
* Using only the \(+\) branch to prove positive mass is fine if its contribution is strictly positive and all remaining denominator contributions are nonnegative. It is a positivity witness, not permission to omit other leading branches from the total constant.

## (d) What I would rank next

### 1. A variable-unit partially tied face measure theorem

This is now the highest-value target for the expectation-value story.

For
\[
K_W(t)=
\int_{(0,\rho)^n}
W(x)x^{a-1}e^{-t^\delta c(x)x^\kappa}\,dx,
\]
under boundedness, \(c\ge c_{\min}>0\), and appropriate transverse face limits, target
\[
\boxed{
\frac{t^{\delta\lambda}}{(\log t)^k}K_W(t)
\longrightarrow
\frac{\delta^k\Gamma(\lambda)}
{k!\prod_{i\in T}\kappa_i}
\int_{(0,\rho)^N}
W(0_T,x_N)c(0_T,x_N)^{-\lambda}
\prod_{j\in N}x_j^{a_j-\lambda\kappa_j-1}\,dx_N.
}
\]

With
\[
W(x)=\text{amplitude}(x)\,\varphi(\operatorname{rep}(x)),
\]
this gives an explicit residual-face measure.

That is a qualitative advance over another point-collapse example: normalized expectations can retain a **distribution along a face**, weighted by the loss unit, density, and transverse exponents—not merely identify the limiting point or the lexicographic scale.

### 2. The two-scaled, tied-truth certificate above

It has a compact statement, an exact constant, and a sharp connection to the recession theorem. It closes a genuine structural gap rather than adding a special case.

### 3. An observable distinguishability theorem

Once the measure interface is stable, formalize that two landscapes have the same limiting normalized expectations precisely when their normalized limiting measures agree, using an appropriate measure-determining observable class.

That makes the interpretation explicit: **leading expectations know the normalized limiting measure; they need not know the overall mass, the dominant power/log scale, or landscape features erased by the face map.**