## 1. Audit

### Degenerate face

The analytic chain checks out, including the constant.

After collapsing \(s=xy\),
\[
I(t)=\int_0^1\!\int_0^1
(-\log s)\mathbf1_{sz>t^{-2}}z^2e^{-t^3sz^2}\,ds\,dz.
\]
Putting \(u=ts,\ v=tz\) gives exactly
\[
I(t)=t^{-4}\int_{(0,t)^2}
(\log t-\log u)\mathbf1_{uv>1}v^2e^{-uv^2}\,du\,dv.
\]
Then \(w=uv^2\) cancels the factor \(v^2\), and the domain becomes
\[
0<v<t,\qquad v<w<v^2t.
\]
The weight is \(\log t-\log w+2\log v\), nonnegative on this domain.

For \(t\ge e\), its normalized absolute value is bounded by
\[
1+|\log w|+2|\log v|
 \le 1+3w+2w^{-1/2}+4v^{-1/2}
\]
on \(0<v<w\). Your inner integral is exactly
\[
(w+3w^2+10\sqrt w)e^{-w},
\]
and the total majorant integral is \(7+5\sqrt\pi\). Thus both domination and the limiting constant \(1\) are correct.

A useful numerical cross-check: the next constant is **\(1+\gamma_E\approx1.57722\)**, rather than \(1.56\):
\[
t^4I(t)=\log t-(1+\gamma_E)+o(1).
\]
Indeed, the limiting log-correction integral is
\[
\int_0^\infty e^{-w}\int_0^w(-\log w+2\log v)\,dv\,dw
=-(1+\gamma_E).
\]
Obtaining this refinement requires controlling the moving-domain remainder; it does not follow from the displayed first-order DCT alone. Your numerical values are consistent with it.

### Expectation iff

The mathematical statement is sound, provided—as presumably supplied by the certificates—the leading measures are **finite Borel measures**.

The essential argument is:

1. Each fibre ratio converges to
   \[
   \frac{\int\psi\,d\mu_i}{\int\chi\,d\mu_i}.
   \]
   Thus convergence of the difference to zero is equivalent to equality of these limiting ratios.

2. Since both observables vanish outside \(L'\), these integrals depend only on \(\mu_i|_{L'}\). Equality of all ratios says those restricted measures are proportional; normalization removes precisely that proportionality.

For the separation direction, nonnegative compactly supported continuous functions inside \(L'\) already suffice. Openness permits their continuous extension by zero. Positivity of the two \(\chi\)-integrals supplies the nonzero anchor; \(\chi\) need not be positive throughout \(L'\).

Two points worth recording in the API documentation:

- This identifies **restricted measures up to scale**, not boundary mass or the unrestricted measures.
- “Vanishes off \(L'\)” is the correct condition. It should not silently be strengthened to `tsupport ψ ⊆ L'`.

This is a mathematical audit of the statements and route, not a verification of the omitted Lean proof bodies.

---

## 2. The next general theorem

**The logarithmic exponent is \(\dim(\mathrm{Opt})\) in the transverse active-truth case.** Strict truth truncation does not subtract one logarithm. But “independent normals” must mean independence **after restricting to the coordinates positive on the relative interior of the optimal face**.

Here is a sufficiently general, explicit theorem to formalise next.

### Transverse active-truth face theorem

Use the unit box; fixed positive side lengths can first be absorbed into constants and units. Write
\[
c_i=r_i+1.
\]
Assume
\[
A,B,D,\rho,q,\gamma,\delta>0,\qquad c_i>0,\qquad
\kappa_i,Q_i\ge0.
\]

Let
\[
P=\{\alpha\ge0:\ Q\cdot\alpha\le\gamma,\quad
\kappa\cdot\alpha\ge\delta\}.
\]

Partition the coordinates into \(J\sqcup I\). Assume there exist \(\beta,\eta>0\) such that

\[
\begin{aligned}
c_j&=\beta\kappa_j-\eta Q_j &&(j\in J),\\
d_i&:=c_i-\beta\kappa_i+\eta Q_i>0 &&(i\in I).
\end{aligned}
\tag{Dual certificate}
\]

Assume also:

- \(\kappa_J,Q_J\) are linearly independent;
- the set
  \[
  F_J=\{\alpha_J\ge0:
       \kappa_J\cdot\alpha_J=\delta,\quad
       Q_J\cdot\alpha_J=\gamma\}
  \]
  contains a point with every coordinate strictly positive.

Define
\[
k=|J|-2,\qquad
m=\beta\delta-\eta\gamma,\qquad
\lambda=\gamma p+m,
\]
and the coarea factor
\[
\mathcal J=
\sqrt{\|\kappa_J\|^2\|Q_J\|^2-
                 \langle\kappa_J,Q_J\rangle^2}.
\]

Then the LP optimal set is
\[
F=\{\alpha_I=0,\ \alpha_J\in F_J\},
\qquad \dim F=k,\qquad \min_P c\cdot\alpha=m.
\]

For the units, assume measurability and bounds
\[
0\le W\le M,\qquad 0<a_-\le a\le a_+,
\]
on the relevant box times \(0<v<\rho\). Assume face traces exist for almost every \((y,v)\):
\[
\begin{aligned}
W(x_J,y,v)&\longrightarrow W_0(y,v),\\
a(x_J,y,v)&\longrightarrow a_0(y,v)
\end{aligned}
\quad\text{as every }x_j\to0,\ j\in J.
\tag{Face traces}
\]

For
\[
v_t(x)=D\,t^{-\gamma/q}\prod_i x_i^{-Q_i/q}
\]
and
\[
K(t)=A t^{-\gamma p}
 \int_{\substack{x\in(0,1)^n\\v_t(x)<\rho}}
 W(x,v_t(x))\prod_i x_i^{r_i}
 e^{-B t^\delta a(x,v_t(x))\prod_i x_i^{\kappa_i}}\,dx,
\]
one has
\[
\boxed{
\frac{t^\lambda}{(\log t)^k}K(t)
\longrightarrow
\frac{AqD^{-q\eta}\Gamma(\beta)}
     {\mathcal J B^\beta}
\,\mathcal H^k(F_J)
\int_{(0,1)^I}\!\prod_{i\in I}y_i^{d_i-1}
 \int_0^\rho
 v^{q\eta-1}\frac{W_0(y,v)}{a_0(y,v)^\beta}
 \,dv\,dy .
}
\tag{AT}
\]

For \(I=\varnothing\), omit the \(y\)-integral. For \(k=0\), use the usual counting convention for \(\mathcal H^0\).

The limit is positive if \(W_0>0\) on a set of positive weighted measure. Without a nonvanishing hypothesis, the convergence theorem remains true, but its limit can be zero.

### Why this is the right LP package

The dual identity is
\[
c\cdot\alpha-m
=
\beta(\kappa\cdot\alpha-\delta)
+\eta(\gamma-Q\cdot\alpha)
+\sum_{i\in I}d_i\alpha_i.
\]
Every term is nonnegative on \(P\), and equality forces exactly the stated face. This explicit certificate is better for Lean than beginning with abstract LP duality.

The two independent equations on \(\mathbb R^J\), together with a strictly positive point, give
\[
\dim F_J=|J|-2.
\]
Independence in the full ambient space alone is not sufficient for this conclusion or for formula (AT).

### Which variables survive, and what is the limiting measure?

The useful variables are
\[
\alpha_j=-\frac{\log x_j}{\log t}\quad(j\in J),\qquad
y=x_I,\qquad
v=v_t(x),\qquad
w=t^\delta\prod_i x_i^{\kappa_i}.
\]

- The \(I\)-coordinates remain ordinary, unscaled coordinates \(y\).
- The \(J\)-coordinates collapse physically to zero, but retain a logarithmic position \(\alpha\in F_J\).
- \(v\in(0,\rho)\) resolves the truth boundary layer.
- \(w\in(0,\infty)\) resolves the loss boundary layer.

Before integrating out \(w\), the limiting **unnormalized** measure is
\[
\boxed{
\frac{AqD^{-q\eta}}{\mathcal J}
\,d\mathcal H^k_{F_J}(\alpha)\,
\prod_{i\in I}y_i^{d_i-1}\,dy\,
v^{q\eta-1}\,dv\,
w^{\beta-1}
W_0(y,v)e^{-Ba_0(y,v)w}\,dw .
}
\tag{LM}
\]
Thus the face density is **constant relative to Euclidean Hausdorff measure**, with the coarea normalization \(1/\mathcal J\). Integrating \(w\) gives (AT).

For the scalar theorem, there is no need to formalise the full joint measure convergence immediately. But (LM) is the correct target for later observable theorems.

### Why the truth boundary does not change the log power

Put \(L=\log t\) and \(z_J=-\log x_J\). The two transverse coordinates can be taken as
\[
s=\kappa_J\cdot z_J-\delta L,\qquad
h=\gamma L-Q_J\cdot z_J.
\]
The remaining \(k\) directions have length scale \(L\), hence volume scale \(L^k\).

Strict truth truncation becomes the fixed interval \(0<v<\rho\), not a missing face-volume factor. Its contribution is the integrable Mellin weight \(v^{q\eta-1}\); the boundary itself has zero measure.

### Why the proof is manageable

For fixed \((y,v,w)\), logarithmic coarea leaves the fibre
\[
\begin{split}
z_J\ge0,\qquad
\kappa_J\cdot z_J
 &=\delta L-\log w+\kappa_I\cdot\log y,\\
Q_J\cdot z_J
 &=\gamma L+q\log(v/D)+Q_I\cdot\log y.
\end{split}
\tag{Fibre}
\]
Its \(k\)-volume divided by \(L^k\) tends to \(\mathcal H^k(F_J)\). Away from the relative boundary of \(F_J\), all \(x_j=e^{-z_j}\) tend to zero, so the unit traces apply.

A sufficient dominating factor is a constant times
\[
\left(1+|\log w|+|\log v|+\sum_{i\in I}|\log y_i|\right)^k
\prod_{i\in I}y_i^{d_i-1}
v^{q\eta-1}w^{\beta-1}e^{-Ba_-w}.
\]
All its logarithmic moments are finite because \(d_i,\eta,\beta>0\). This is the reusable general counterpart of your explicit plane majorant.

### Check against the landed example

Here
\[
c=(1,1,3),\quad \kappa=(1,1,2),\quad Q=(1,1,1),
\quad \delta=3,\quad\gamma=2.
\]
Take \(J=\{x,y,z\}\), \(I=\varnothing\), \(\beta=2,\eta=1\). Then
\[
F=\{\alpha_z=1,\ \alpha_x+\alpha_y=1\},\qquad
k=1,\qquad \lambda=4.
\]
Moreover
\[
\mathcal H^1(F)=\sqrt2,\qquad \mathcal J=\sqrt2.
\]
With all remaining constants and units equal to one, (AT) gives
\[
\Gamma(2)\int_0^1v^{0}\,dv=1.
\]

### Does this reduce to `tendsto_modelKernel_partial` with \(Q=0\)?

**Not directly under these hypotheses.** There is an exact monomial substitution, but it generally does not preserve a rectangular domain or the existing partial theorem’s kernel form.

Choose \(a,b\in J\) with
\[
R=\begin{pmatrix}\kappa_a&\kappa_b\\Q_a&Q_b\end{pmatrix}
\]
invertible. Keeping the other coordinates, solve
\[
R\binom{\log x_a}{\log x_b}
=
\binom{
\log w-\delta\log t-\sum_{j\ne a,b}\kappa_j\log x_j
}{
q\log(D/v)-\gamma\log t-\sum_{j\ne a,b}Q_j\log x_j
}.
\tag{Substitution}
\]
This fixes the truth range to \(0<v<\rho\) and the exponential variable to \(w\), but the conditions \(0<x_a,x_b<1\) become **moving coupled inequalities** on the remaining coordinates.

For units independent of \(x_J\), coarea gives an exact fibre-volume factor. For variable units, it gives a fibre integral. Neither is generally the single product-fibre identity used in the example.

So:

- special configurations can reduce to the existing partial theorem;
- a general reduction would require additional cone/chart decomposition and domain lemmas;
- the logarithmic coarea theorem above is likely the shorter and cleaner general proof.

I would not spend this round trying to force a universal \(Q=0\) reduction.

---

## 3. Ranking and scope

### 1. General transverse active-truth theorem — **do next**

First prove (AT) with \(W,a\) independent of \(x_J\), isolating the polytope-fibre asymptotic and its logarithmic-moment bound. Then add face traces using localization away from the relative boundary.

Package the explicit dual data
\[
(J,I,\beta,\eta,(d_i))
\]
as a certificate. This is a useful new interface between the LP/combinatorial and analytic layers.

### 2. General-truth Hironaka export — **next integration milestone**

Resolving \(F\cdot T\) supplies simultaneous monomialization of loss and truth, but export must still retain both units and verify which analytic case each chart occupies.

In particular, do not let the export imply that every active-truth chart is transverse in the restricted sense above. Dependent-normal cases need another theorem or an explicit exclusion. Build the general chart data first; apply the strongest available analytic theorem conditionally.

### 3. Variable-unit partial faces with moving parameters — **worth doing narrowly**

For fixed parameters, pointwise face traces plus domination and localization are enough, and this work fits naturally into item 1.

For moving parameters, localization alone does **not** manufacture uniformity. Require something like:

- joint continuity at the relevant face points, including the parameter;
- or almost-everywhere compact-uniform face convergence;
- or an equicontinuity condition permitting that conclusion.

Without such a hypothesis, moving parameter sequences can follow shrinking spikes even though every fixed parameter has the required face limit. Do not promise the moving-parameter theorem from fixed-parameter face continuity alone.

### 4. Compact-uniform packaging — **after the hypotheses stabilize**

Do it once the parameter dependence of units, LP certificates and positivity margins is explicit. Uniform lower bounds on \(\beta,\eta,d_i,a_-\), together with controlled face geometry, make the domination reusable.

Avoid a large uniform wrapper before deciding what happens near changes of optimal face or loss of transversality.

### Skip for now

- A universal active-truth-to-\(Q=0\) reduction.
- Simultaneous treatment of transverse and dependent-normal active faces.
- Second-order asymptotics for the example, despite the attractive \(1+\gamma_E\) constant.
- Broad compact-uniform claims based only on pointwise face continuity.

**Recommended round-7 deliverable:** the dual face certificate, the logarithmic coarea/fibre-volume lemma, and the scalar transverse active-truth limit. Those are the smallest coherent additions that turn the completed example into reusable analytic infrastructure.