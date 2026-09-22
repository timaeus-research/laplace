## Bottom line

For a Lean development, I would use:

1. **Unique minimum:** integrate out the variable with the **smallest** \(e_j\), using your existing one-variable theorem and a uniform bound valid for every positive effective temperature.
2. **Tied minimum:** prove an exact **product-of-powers box identity**, then localize and freeze the continuous coefficients. This is simpler than Mellin transforms and avoids a full sector decomposition.
3. **Sublevel volumes:** use these if \(\Theta\)-bounds suffice, but they are not necessary to obtain the leading coefficient.

Two qualifications matter:

- With signed amplitudes, or an amplitude vanishing on the relevant stratum, the correct assertion is a **normalized limit**, possibly zero—not necessarily an asymptotic equivalence with a nonzero constant.
- A positive coefficient \(a(u,s)\), bounded away from zero, cannot change \((\lambda,\theta)\) while the monomial and nonvanishing amplitude remain fixed. A genuine wall must change something else.

---

## 1. Precise two-variable statements

Write \(f=\chi b\), and suppose
\[
I(t)=\int_{\mathbb R^2}
 f(x,y)|x|^{h_1}|y|^{h_2}
 e^{-t a(x,y)|x|^{2k_1}|y|^{2k_2}}\,dx\,dy,
\]
where:

- \(k_i\ge1\);
- \(h_i>-1\);
- \(f\) is continuous and compactly supported;
- \(a\) is continuous and \(a\ge a_0>0\) on a neighborhood of the support;
- \(e_i=(h_i+1)/(2k_i)\).

Real-valued \(f\) is allowed.

### Untied: \(e_1<e_2\)

Then
\[
\boxed{
\lim_{t\to\infty}t^{e_1}I(t)
=
\frac{\Gamma(e_1)}{k_1}
\int_{\mathbb R}
 |y|^{h_2-2k_2e_1}
 f(0,y)a(0,y)^{-e_1}\,dy .
}
\]

Thus the leading coefficient lives on the divisor \(x=0\).

### Tied: \(e_1=e_2=\lambda\)

Then
\[
\boxed{
\lim_{t\to\infty}\frac{t^\lambda}{\log t}I(t)
=
\frac{\Gamma(\lambda)}{k_1k_2}
f(0,0)a(0,0)^{-\lambda}.
}
\]

Here the leading coefficient lives on the **intersection** of the two divisors.

With passive variables \(z\), the formulas acquire an integral in \(z\). In particular, the tied coefficient becomes
\[
\boxed{
\frac{\Gamma(\lambda)}{k_1k_2}
\int f(0,0,z)a(0,0,z)^{-\lambda}\,dz .
}
\]

These constants include all four sign quadrants.

### General pattern

Let \(M=\{j:e_j=\lambda\}\), \(|M|=\theta\). Under the analogous assumptions,
\[
\boxed{
C=
\frac{\Gamma(\lambda)}
 {(\theta-1)!\prod_{j\in M}k_j}
\int_{\{u_j=0:j\in M\}}
 f(u)a(u)^{-\lambda}
 \prod_{i\notin M}|u_i|^{h_i-2k_i\lambda}\,du_{\notin M}.
}
\]

The general normalized limit is
\[
\frac{t^\lambda}{(\log t)^{\theta-1}}I(t)\longrightarrow C.
\]

If \(C>0\), this gives the usual asymptotic equivalence.

---

## 2. Untied case: the effective temperature issue is inexpensive

Your integrability criterion is exactly right:
\[
h_2-2k_2e_1>-1
\iff e_2>e_1.
\]

Choose \(R,M\) so that the support of \(f\) lies in \([-R,R]^2\) and \(|f|\le M\). Put
\[
J(T,y)=
\int_{\mathbb R}f(x,y)|x|^{h_1}
e^{-T a(x,y)|x|^{2k_1}}\,dx.
\]

The key estimate is valid for **every \(T>0\)**:
\[
\begin{aligned}
T^{e_1}|J(T,y)|
&\le
M T^{e_1}\int_{\mathbb R}|x|^{h_1}
 e^{-Ta_0|x|^{2k_1}}\,dx\\
&=
M a_0^{-e_1}\frac{\Gamma(e_1)}{k_1}.
\end{aligned}
\]

No lower bound on \(T\) is needed. The full-line integral gives precisely the scale-invariant estimate you want.

For \(y\ne0\), take \(T=t|y|^{2k_2}\). Then
\[
t^{e_1}|y|^{h_2}|J(t|y|^{2k_2},y)|
\le
K\,1_{\{|y|\le R\}}
|y|^{h_2-2k_2e_1}.
\]
The right-hand side is integrable exactly in the untied case.

For each fixed \(y\ne0\), \(T\to\infty\), so your existing one-variable theorem applies. Dominated convergence in \(y\) finishes the proof. The exceptional set \(y=0\) is null.

**Lean assessment:** this is the cheapest substantial next theorem. The main work is plumbing:

- sectional measurability and integrability;
- extracting a bounded rectangular support;
- `rpow` identities away from \(y=0\);
- integrability of a power on a bounded interval.

### Why not integrate out the largest exponent?

Naively applying the one-dimensional leading term to the largest \(e_j\) produces nonintegrable powers in the smaller-exponent coordinates. That method can be repaired by retaining a truncated, finite-temperature formula, but it recreates the boundary-layer analysis.

For the unique-minimum theorem, integrate out the **minimum** first.

---

## 3. Tied case: an exact identity and a short analytic proof

The missing reusable lemma is a product integration identity.

For a symmetric box \(|x|\le r_1,\ |y|\le r_2\), put
\[
R_i=r_i^{2k_i},\qquad B=R_1R_2.
\]
When \(e_1=e_2=\lambda\),
\[
\boxed{
\begin{aligned}
&\int_{|x|\le r_1,\ |y|\le r_2}
 |x|^{h_1}|y|^{h_2}
 e^{-ta|x|^{2k_1}|y|^{2k_2}}\,dx\,dy\\
&\qquad=
\frac1{k_1k_2}
\int_0^B w^{\lambda-1}e^{-ta w}
\log\frac Bw\,dw .
\end{aligned}
}
\]

### Derivation

First substitute
\[
r=|x|^{2k_1},\qquad s=|y|^{2k_2}.
\]
The integral becomes
\[
\frac1{k_1k_2}
\int_0^{R_1}\int_0^{R_2}
r^{\lambda-1}s^{\lambda-1}e^{-ta rs}\,ds\,dr.
\]

Now use \(w=rs\) in the inner integral and swap the order. For fixed \(w\), the remaining integral is
\[
\int_{w/R_2}^{R_1}\frac{dr}{r}
=\log\frac{R_1R_2}{w}.
\]

This is the log multiplicity in its most elementary form.

Scaling \(q=tw\) gives
\[
\frac{t^\lambda}{\log t}J(t)
=
\frac1{k_1k_2}
\int_0^{tB}
q^{\lambda-1}e^{-aq}
\frac{\log(tB/q)}{\log t}\,dq.
\]
Dominated convergence yields
\[
\frac{\Gamma(\lambda)}{k_1k_2a^\lambda}.
\]

One convenient majorant uses
\[
q^{\lambda-1}e^{-aq}(1+|\log q|),
\]
whose integrability follows from elementary power bounds near zero and exponential decay at infinity.

### From the box model to continuous \(f,a\)

Fix a small square around the origin.

1. **Outside the square:** at least one coordinate is bounded away from zero. The one-dimensional bound gives an \(O(t^{-\lambda})\) contribution.
2. **Inside the square:** continuity makes \(f\) and \(a\) uniformly close to their values at the origin.
3. Control the amplitude error by its supremum times the positive box model.
4. Squeeze the phase between the constant coefficients \(a(0,0)\pm\eta\).
5. First let \(t\to\infty\), then shrink the square.

This works for signed \(f\) by estimating errors absolutely.

So the sharp inexpensive result is the **exact normalized limit**, not merely a \(\Theta\)-bound.

### Where Lean work concentrates

The hard part is not the limit itself. It is packaging:

- power substitutions on positive intervals;
- changing the order on the region \(0<w<R_2r\);
- the integral of \(1/r\);
- a reusable logarithmic Gamma-integrability lemma.

For \(\theta\) tied variables, the corresponding identity is
\[
\int_{\prod(0,R_j)}
 \Bigl(\prod r_j^{\lambda-1}\Bigr)F\Bigl(\prod r_j\Bigr)\,dr
=
\frac1{(\theta-1)!}
\int_0^B w^{\lambda-1}F(w)
\left(\log\frac Bw\right)^{\theta-1}dw.
\]
Induction on this identity is a clean route to the general theorem.

---

## 4. Walls: distinguish three different mechanisms

### A. A strictly positive varying \(a(u,s)\) creates no multiplicity wall

If \(a(u,s)\) stays positive, and the monomial and nonvanishing amplitude remain fixed, then \(\lambda,\theta\) remain fixed. Only \(C(s)\) changes.

Likewise, fixed integer resolution exponents cannot continuously approach a tie.

### B. A genuine exponent-gap crossover has variable \(\delta\log t\)

This is meaningful if one permits a continuously varying weight, rather than insisting that the weight come from fixed integer resolution data.

In positive power coordinates, consider
\[
J_\delta(t)=
\int_0^1\int_0^1
r^{\lambda-1}s^{\lambda+\delta-1}e^{-trs}\,dr\,ds.
\]
There is an exact identity
\[
J_\delta(t)=
\int_0^1w^{\lambda-1}e^{-tw}
\frac{1-w^\delta}{\delta}\,dw,
\]
with the continuous extension \(-\log w\) at \(\delta=0\).

For \(\delta\to0\) with \(z=\delta\log t\) bounded,
\[
\boxed{
J_\delta(t)\sim
\Gamma(\lambda)t^{-\lambda}\log t\,
\Phi(z),\qquad
\Phi(z)=\frac{1-e^{-z}}z,\quad \Phi(0)=1.
}
\]

Thus **\(\delta\log t\)** is exactly the crossover variable for a closing exponent gap.

For the energy statistic, differentiating with \(\delta\) held fixed gives, in this model,
\[
\boxed{
t\mathbb E[L]
=
\lambda-\frac1{\log t}\frac{z}{e^z-1}
+o\!\left(\frac1{\log t}\right).
}
\]
At \(z=0\), the correction is \(-1/\log t\).

This is an excellent model theorem, but it is not a continuously varying integer-exponent resolution family.

### C. A natural log wall with fixed exponents: a coefficient on the intersection vanishes

Take, for illustration, the box model
\[
I_s(t)=\int_{[-1,1]^2}
(x^2+y^2+s^2)e^{-tx^2y^2}\,dx\,dy.
\]

- At \(s=0\), the density vanishes on the intersection. The \(x^2\) and \(y^2\) terms each have a unique minimum exponent.
- For \(s\ne0\), the \(s^2\) term contributes the tied leading term.

Explicitly,
\[
I_s(t)
=
\sqrt\pi\,t^{-1/2}
\left[
2+s^2\bigl(\log t-\psi(1/2)\bigr)+O(t^{-1})
\right]
\]
for bounded \(s\), where \(\psi=\Gamma'/\Gamma\).

Therefore the crossover is
\[
\boxed{z=s^2\log t.}
\]

The energy satisfies, at leading crossover order,
\[
t\mathbb E_s[L]
=
\frac12-
\frac{s^2}{2+s^2(\log t-\psi(1/2))}
+O(t^{-1}),
\]
and hence, when \(s^2\log t\to z\ge0\),
\[
\boxed{
\log t\left(\frac12-t\mathbb E_s[L]\right)
\longrightarrow \frac{z}{2+z}.
}
\]

A smooth compact cutoff equal to one near the origin gives the same mechanism, with cutoff-dependent constants replacing \(2\sqrt\pi\).

This is a genuine log-multiplicity wall of the **weighted integral**. It requires allowing the density to vanish, or an equivalent competition between contributions.

### Phase-degeneration walls need not have a purely logarithmic crossover

For example,
\[
L_s(x,y)=x^2(y^2+s),\qquad s\ge0,
\]
has a tied product at \(s=0\), but a single active quadratic direction for fixed \(s>0\).

In power coordinates, the corresponding model is
\[
J_s(t)=\int_0^1\int_0^1
r^{\lambda-1}w^{\lambda-1}e^{-tr(w+s)}\,dr\,dw.
\]
It has the exact identity
\[
t^\lambda J_s(t)=
F_s(t):=\int_0^t e^{-sv}\frac{\gamma(\lambda,v)}v\,dv.
\]
Consequently,
\[
\boxed{
t\mathbb E_s[L]
=
\lambda-
\frac{e^{-st}\gamma(\lambda,t)}{F_s(t)}.
}
\]

Here the boundary-layer variable is **\(st\)**, while the accumulated logarithm behaves as
\[
F_s(t)=\Gamma(\lambda)\log\min(t,1/s)+O(1)
\]
when \(t\) is large and \(s\) is small.

So “a multiplicity wall must have crossover variable involving only \(\log t\)” is too strong. It depends on the wall mechanism.

**Important:** energy derivatives here hold the model parameter fixed. Do not differentiate along a path \(s=s(t)\).

---

## 5. Sublevel volumes: what is lost?

If you know only
\[
V(\varepsilon)
=\Theta\!\left(
\varepsilon^\lambda
(\log(1/\varepsilon))^{\theta-1}
\right),
\]
then Abelian transfer gives the corresponding \(\Theta\)-bound for \(I(t)\). That establishes the scale, but not normalized convergence.

If instead you prove
\[
V(\varepsilon)\sim
D\varepsilon^\lambda
(\log(1/\varepsilon))^{\theta-1},
\]
then
\[
I(t)\sim
D\Gamma(\lambda+1)t^{-\lambda}(\log t)^{\theta-1}.
\]
Thus the **sublevel route itself loses nothing**; giving up the sublevel coefficient loses information.

For the germbij application, \(\Theta\)-bounds alone generally lose:

- limiting mixture weights between equally dominant charts;
- limiting expectations of observables;
- numerical crossover locations;
- coefficient-sensitive cancellations.

With coefficient theorems, an observable \(g\) can be handled by replacing \(f\) with \(fg\):
\[
\mathbb E_t[g]\longrightarrow \frac{C_{fg}}{C_f},
\qquad C_f>0.
\]

For energy, a parallel theorem with kernel \(q e^{-q}\) gives \(t\mathbb E[L]\to\lambda\). But the correction
\[
\lambda-\frac{\theta-1}{\log t}
\]
should **not** be justified by differentiating a bare leading asymptotic. Under merely continuous amplitudes, further remainder control is needed for such a correction.

---

## 6. Ranking and a first Lean milestone

### Recommended ranking

| Goal | Best route |
|---|---|
| Unique-minimum coefficient | Existing 1D theorem + uniform bound + DCT |
| Two-variable tied coefficient | Exact product-box identity + localization |
| Arbitrarily many ties | Induct the product-box identity / logarithmic simplex formula |
| Only growth order | Sublevel \(\Theta\) + existing Abelian transfer |
| Full expansions and pole calculus | Mellin transforms, later |

A full sector decomposition is unnecessary for a single already-normal-crossings chart. Mellin transforms encode the answer beautifully, but introduce substantially more infrastructure than the leading-term problem requires.

### First theorem to implement

I would start with the signed, untied theorem:
\[
e_1<e_2
\quad\Longrightarrow\quad
t^{e_1}I(t)\longrightarrow
\frac{\Gamma(e_1)}{k_1}
\int |y|^{h_2-2k_2e_1}
f(0,y)a(0,y)^{-e_1}\,dy.
\]

First extract a standalone lemma:
\[
\boxed{
T^e
\left|\int g(x)|x|^h e^{-TA(x)|x|^{2k}}dx\right|
\le \|g\|_\infty a_0^{-e}\frac{\Gamma(e)}k
\qquad(T>0).
}
\]
It will be reused in almost every multi-variable argument.

### Rough line-count estimates

Without inspecting the repository, and assuming your one-dimensional theorem and scaling lemmas are reusable:

- **Uniform bound:** 40–100 Lean lines.
- **Untied two-variable theorem:** another 150–350 lines.
- **Product-box identity and logarithmic integrability:** 200–500 lines.
- **Tied localization theorem:** another 200–400 lines.

These are planning estimates, not audited counts. The biggest uncertainty is interval-substitution and Fubini-region infrastructure.

**My suggested milestone:** untied coefficient theorem first, tied constant-coefficient box theorem second, tied continuous-chart theorem third. That sequence gives useful results early while building exactly the infrastructure needed for arbitrary log multiplicity.