**The facet route is correct.** The main additions needed are:

1. require a **nonempty proper exposed face** and normalize the exposing vector inside \(W\);
2. prove that the **conditional moment body really is \(F\)**, using vertex charging—not merely the minimal-face identity;
3. prove \(q_s(A)\to1\), rather than deducing it from mean convergence alone;
4. handle \(T'=\{0\}\) separately when choosing the tangential coercivity constant;
5. distinguish **existence of a finite-length approach** from finiteness of every approaching path.

Your constants in Lemma D are correct. The data-response strengthening is also reachable, but needs an additional one-sided radial-variation argument.

## 1. The first `FacetFisherAccess` statement

Here is the mathematical specification I would formalize first.

Let \(E\) be the finite-dimensional Euclidean statistic space, and assume:

- \(\nu\) is a probability measure;
- \(S:X\to E\) is measurable and essentially bounded;
- \(P=\operatorname{conv}V\) is its moment body, with every vertex of \(P\) charged;
- \(W=\operatorname{dir}(P)\);
- \(u\in W\setminus\{0\}\), and
  \[
  \langle u,v\rangle\le\beta\qquad(v\in V);
  \]
- \(F=P\cap\{\langle u,\cdot\rangle=\beta\}\) is nonempty and proper;
- \(A=\{x:\langle u,S(x)\rangle=\beta\}\);
- \(T'=\operatorname{dirSpan}(\nu(\cdot\mid A),1,S)\), and
  \[
  T'=W\cap u^\perp;
  \]
- \(M\in\operatorname{ri}F\).

Set
\[
v_M=\operatorname{chartVInv}_A(M-m'_0)\in T'\subseteq W,
\qquad
g_M(r)=\sqrt{\operatorname{raySpeedSq}(v_M,u,r)}.
\]

Then:
\[
\boxed{
\begin{aligned}
&\exists\eta:[0,1)\to W,\quad
  \eta\text{ is }C^1,\quad
  \operatorname{meanMap}(\eta(s))\longrightarrow M,\\
&\hspace{35mm}
  \int_0^1
  \sqrt{\operatorname{Var}_{P_{\eta(s)}}
        \langle\eta'(s),S\rangle}\,ds<\infty\\
&\quad\Longleftrightarrow\quad
  \int_0^\infty g_M(r)\,dr<\infty.
\end{aligned}}
\]

For Lean, use a function on \(\mathbb R\) with the appropriate \(C^1\)-on-\(\operatorname{Ico}(0,1)\) hypothesis, and integrate its within-derivative speed over \(\operatorname{Ioo}(0,1)\). The endpoint convention does not affect length.

I would leave the starting parameter unspecified in the first theorem. A prescribed starting point \(\eta(0)=\eta_*\) is a subsequent corollary: attach a compact \(C^1\) connector and use a flat-ended reparametrization to join it to the ray.

**This is an existence theorem.** Ray finiteness does not imply that every \(C^1\) path approaching \(M\) has finite length; oscillatory paths can have infinite length.

---

## 2. Lemma B

### B1. The facet condition and the projected normal

Your inclusion
\[
T'\subseteq W\cap u^\perp
\]
is correct. Formally, use the a.e.-constant/annihilator characterization of `dirSpan`; avoid claiming that all pointwise differences \(S(x)-S(y)\), including exceptional points, generate the relevant space.

For a nonempty proper exposed face, the functional
\[
w\mapsto\langle u,w\rangle\quad\text{on }W
\]
is nonzero. Consequently,
\[
\dim(W\cap u^\perp)=\dim W-1.
\]
Given the inclusion above,
\[
T'=W\cap u^\perp
\quad\Longleftrightarrow\quad
\dim T'+1=\dim W.
\]

Thus your condition is exactly right once properness is included.

You do **not** need \(u\in W\) to state this kernel condition. You **do** need it to obtain the decomposition with normal vector \(u\):
\[
W\cap T'^\perp=\mathbb Ru.
\]

Without \(u\in W\), use
\[
u_W=\operatorname{proj}_W u.
\]
Then
\[
W\cap T'^\perp=\mathbb Ru_W.
\]

There is also a necessary adjustment to the exposing level. If \(S-m_0\in W\) a.e., then
\[
\langle u,S\rangle
=\langle u_W,S\rangle+\langle u-u_W,m_0\rangle
\quad\text{a.e.}
\]
Hence the projected exposing pair is
\[
u_W,\qquad
\beta_W=\beta-\langle u-u_W,m_0\rangle.
\]
Projection preserves the exposure **after this constant adjustment**.

With \(u\in W\setminus\{0\}\), define
\[
v(\eta)=\operatorname{proj}_{T'}\eta,\qquad
r(\eta)=-\frac{\langle\eta,u\rangle}{\|u\|^2}.
\]
For \(\eta\in W\),
\[
\eta=v(\eta)-r(\eta)u.
\]

### B2. Face-family gauge invariance

Correct, and this part does not require the facet hypothesis.

For \(w\in T'^\perp\), \(\langle w,S\rangle\) is constant a.e. under \(\nu(\cdot\mid A)\). Therefore
\[
P^A_\eta=P^A_{\operatorname{proj}_{T'}\eta}.
\]
Thus
\[
\operatorname{meanMap}_A(\eta)
=\operatorname{meanMap}_A(\operatorname{proj}_{T'}\eta),
\]
and
\[
\operatorname{proj}_{T'}\eta
=\operatorname{chartVInv}_A
  \bigl(\operatorname{meanMap}_A(\eta)-m'_0\bigr).
\]

This is a useful standalone lemma.

### B3. Identifying the conditional moment body

Under your **vertex-charging hypothesis**, the conditional moment body is indeed \(F\).

The proof has two directions:

1. Since \(S\in P\) a.e., on \(A\) one has
   \[
   S\in P\cap\{\langle u,\cdot\rangle=\beta\}=F
   \quad\text{a.e.}
   \]
   Thus the conditional moment body is contained in \(F\).

2. Every vertex of \(F\) is a vertex of \(P\), hence has positive \(\nu\)-mass. It belongs to \(A\), so it retains positive mass after conditioning. The conditional moment body therefore contains all vertices of \(F\), hence their convex hull \(F\).

In particular, \(\nu(A)>0\), and
\[
\operatorname{momentBody}(\nu(\cdot\mid A),S)=F.
\]

**The minimal-face identity and a.e. support alone are insufficient.** For example, a uniform square measure plus an atom at the midpoint of one edge has that midpoint in the relative interior of the edge, but conditioning on the edge gives only the midpoint.

Also, use the **essential moment body**, not the literal convex hull of every pointwise value on \(A\); null-set values need not respect the claimed geometry.

With the body identity proved, your convergence argument is correct:
\[
v_n
=\operatorname{chartVInv}_A
   \bigl(\operatorname{meanMap}_A(\eta_n)-m'_0\bigr)
\longrightarrow
\operatorname{chartVInv}_A(M-m'_0)=v_M.
\]
The centered chart condition is
\[
M-m'_0\in\operatorname{ri}(F-m'_0),
\]
in the appropriate face-coordinate space.

### B4. Normal divergence

Correct, including the sign.

Choose \(z\in V\setminus F\) and \(z_0\in V\cap F\), and write
\[
\delta_z=\beta-\langle u,z\rangle>0.
\]
Then
\[
\langle\eta_n,z-z_0\rangle
=\langle v_n,z-z_0\rangle+r_n\delta_z.
\]
The first term converges, while the left side tends to \(+\infty\). Hence
\[
r_n\to+\infty.
\]

Here “off-face vertex” is less ambiguous than “uncharged vertex,” since these vertices are charged by \(\nu\).

For assembly, a filter-level version of B is convenient:
\[
\operatorname{meanMap}(\eta)\to M
\implies
v(\eta)\to v_M,\quad r(\eta)\to+\infty.
\]

### An additional conclusion needed for D: \(p_n\to1\)

Do not infer this from mean convergence alone. Measures can have small expected gap while keeping mass just outside the face.

Here it follows from
\[
v_n\to v_M,\qquad r_n\to\infty,\qquad \nu(A)>0.
\]
Indeed, after dropping the constant \(r_n\beta\), the density is proportional to
\[
e^{-\langle v_n,S\rangle}e^{-r_n\ell},
\qquad
\ell=\beta-\langle u,S\rangle\ge0.
\]
Dominated convergence gives concentration on \(A\). Equivalently, first prove concentration for the fixed-\(v_M\) ray and transfer it through a uniformly bounded tilt.

Thus
\[
p_n=P_{\eta_n}(A)\to1.
\]

---

## 3. Lemma D: exact scalar chain

Let \(q\) be a probability measure, with:

- \(\ell\ge0\) a.e.;
- \(A=\{\ell=0\}\), \(p=q(A)>0\), \(\varepsilon=1-p\);
- \(\|S\|\le B\) a.e.;
- \(\lambda>0\), and
  \[
  \lambda\|z\|^2\le
  \operatorname{Var}_q\langle z,S\rangle
  \qquad(z\in T').
  \]

Put
\[
L=E_q\ell,\qquad V_\ell=\operatorname{Var}_q\ell.
\]

A fixed centering of \(S\) is also allowed: it suffices to have \(\|S-s_c\|\le B\), since all relevant variances and covariances are invariant under that translation.

### Covariance bound

For \(f_z=\langle z,S\rangle\),
\[
\begin{aligned}
|\operatorname{Cov}_q(\ell,f_z)|
&=\left|E_q\bigl[\ell(f_z-E_qf_z)\bigr]\right|\\
&\le E_q\bigl[\ell\,|f_z-E_qf_z|\bigr]\\
&\le 2B\|z\|L.
\end{aligned}
\]

### Completion of squares

For \(a_0\in\mathbb R\),
\[
\begin{aligned}
\operatorname{Var}_q(a_0\ell+f_z)
&=a_0^2V_\ell
  +2a_0\operatorname{Cov}_q(\ell,f_z)
  +\operatorname{Var}_q f_z\\
&\ge a_0^2V_\ell
  -4B|a_0|\|z\|L+\lambda\|z\|^2\\
&=
a_0^2\left(V_\ell-\frac{4B^2L^2}{\lambda}\right)
+\left(\sqrt\lambda\,\|z\|
       -\frac{2B|a_0|L}{\sqrt\lambda}\right)^2\\
&\ge
a_0^2\left(V_\ell-\frac{4B^2L^2}{\lambda}\right).
\end{aligned}
\]

### Using the mass at zero

Cauchy–Schwarz on \(A^c\) gives
\[
L^2
=\left(E_q[\ell\,1_{A^c}]\right)^2
\le\varepsilon E_q\ell^2.
\]
Consequently,
\[
V_\ell=E_q\ell^2-L^2
\ge pE_q\ell^2,
\]
so, exactly as you wrote,
\[
E_q\ell^2\le\frac{V_\ell}{p},
\qquad
L^2\le\frac{\varepsilon}{p}V_\ell.
\]
Therefore
\[
\boxed{
\operatorname{Var}_q(a_0\ell+\langle z,S\rangle)
\ge
a_0^2V_\ell
\left(1-\frac{4B^2\varepsilon}{\lambda p}\right).
}
\]

In particular, if
\[
\frac{4B^2\varepsilon}{\lambda p}\le\frac12,
\]
then
\[
\operatorname{Var}_q(a_0\ell+\langle z,S\rangle)
\ge\frac12a_0^2V_\ell.
\]

**All your constants are correct.**

For the first Lean lemma, I would use this scalar version. It avoids both matrices and the empty-unit-sphere issue. If a covariance vector is later useful, define the Riesz representative of
\[
z\longmapsto\operatorname{Cov}_q(\ell,\langle z,S\rangle)
\quad\text{on }T'.
\]

### Uniform tangential coercivity

Your argument is correct:
\[
\operatorname{Var}_q\langle z,S\rangle
\ge p\operatorname{Var}_{q(\cdot\mid A)}\langle z,S\rangle,
\]
and
\[
q(\cdot\mid A)=P^A_v.
\]

For \(T'\ne\{0\}\), compactness of its unit sphere and strict positivity of face covariance give
\[
\operatorname{Var}_{P^A_{v_M}}\langle z,S\rangle
\ge\lambda_M\|z\|^2
\]
for some \(\lambda_M>0\). Tilt comparison gives, eventually,
\[
\operatorname{Var}_{P^A_v}\langle z,S\rangle
\ge e^{-2c}\lambda_M\|z\|^2.
\]
Together with \(p\ge p_0>0\), choose
\[
\lambda=p_0e^{-2c}\lambda_M.
\]

If \(T'=\{0\}\), the unit sphere is empty. Simply choose any \(\lambda>0\): the coercivity statement is vacuous, and D reduces to the normal variance identity.

---

## 4. Assembly

Let
\[
\eta_s=v_s-r_su.
\]
Because \(v\) and \(r\) are fixed linear maps of \(\eta\), both are \(C^1\), with \(v'_s\in T'\).

The speed identity is
\[
\begin{aligned}
|\eta'_s|_F^2
&=\operatorname{Var}_{q_s}
  \bigl(-r'_s\langle u,S\rangle+\langle v'_s,S\rangle\bigr)\\
&=\operatorname{Var}_{q_s}
  \bigl(r'_s\ell+\langle v'_s,S\rangle\bigr).
\end{aligned}
\]

By B, \(v_s\to v_M\), \(r_s\to\infty\), and \(p_s\to1\). Thus D applies eventually:
\[
|\eta'_s|_F^2
\ge\frac12(r'_s)^2\operatorname{Var}_{q_s}\ell.
\]

The actual relative tilt from \(P_{v_M-r_su}\) to \(q_s\) is
\[
-\langle v_s-v_M,S\rangle.
\]
The minus sign does not affect the absolute bound, but it should be correct in the tilt identity. Lemma C gives
\[
\operatorname{Var}_{q_s}\ell
\ge e^{-2c}\operatorname{Var}_{P_{v_M-r_su}}\ell.
\]
Hence
\[
|\eta'_s|_F
\ge\frac{e^{-c}}{\sqrt2}|r'_s|\,g_M(r_s).
\]

Finite path length therefore implies finite weighted parameter length. Lemma E, together with \(r_s\to\infty\), gives an integrable ray tail.

Two small assembly details:

- \(g_M\) is continuous: bounded statistics give continuous ray variance, and square root is continuous.
- A finite ray tail is equivalent to integrability over \((0,\infty)\), since \(g_M\) is locally integrable everywhere.

If the landed E only handles parameter time tending to \(+\infty\), first replace \(s\) by \(t/(1+t)\).

For the converse, the ray converges to \(P^A_{v_M}\), whose mean is \(M\), and
\[
\eta(s)=v_M-\frac{s}{1-s}u
\]
has precisely the ray length under change of variables. This completes both directions.

---

## 5. The data-response strengthening

This is a good next theorem:

> **Facet data-response length criterion.**  
> Under the facet hypotheses above, let \(h\) be bounded measurable, \(h\le H\) a.e., and
> \[
> p_*=\nu(h=H)>0.
> \]
> Define
> \[
> \rho_t=\nu.\operatorname{tilted}(th),\qquad
> M=E_\nu[S\mid h=H]\in\operatorname{ri}F,
> \]
> and let
> \[
> \eta(t)=\operatorname{chartVInv}(E_{\rho_t}S-m_0).
> \]
> Then
> \[
> \boxed{
> \int_0^\infty|\eta'(t)|_F\,dt<\infty
> \quad\Longleftrightarrow\quad
> \int_0^\infty g_M(r)\,dr<\infty.
> }
> \]

The response path is \(C^1\) using the chart regularity and the bounded-tilt differentiation formulas. Reparametrizing gives the corresponding statement on \([0,1)\).

The forward implication is the accessibility theorem. **The reverse implication needs more than finite variation of the moment curve.** Here is the missing, reachable argument.

### One-sided radial control from the data tilt

Write
\[
\eta=v-ru,\qquad q=P_\eta,\qquad
L=E_q\ell=E_{\rho_t}\ell,\qquad
V_\ell=\operatorname{Var}_q\ell.
\]
Let \(m_T=\operatorname{proj}_{T'}E_qS\). On \(T'\), denote tangential covariance by \(C\), and let \(b\in T'\) represent
\[
\langle b,z\rangle
=\operatorname{Cov}_q(\ell,\langle z,S\rangle).
\]

Eventually,
\[
C\ge\lambda I,\qquad \|b\|\le2BL,
\]
and the Schur complement satisfies
\[
D:=V_\ell-\langle b,C^{-1}b\rangle\ge\frac12V_\ell.
\]

Differentiating the response means gives
\[
m_T'=-Cv'-r'b,
\]
and
\[
L'=\langle b,C^{-1}m_T'\rangle-Dr'.
\]

Now put \(d=H-h\ge0\). The **data** identity gives
\[
L'
=-E_{\rho_t}[\ell d]+L\,E_{\rho_t}d
\le L\,E_{\rho_t}d.
\]
Consequently, with \((r')_-=\max(-r',0)\),
\[
D(r')_-
\le
L\left(E_{\rho_t}d+\frac{2B}{\lambda}\|m_T'\|\right).
\]
Thus
\[
\sqrt{V_\ell}(r')_-
\le
2\frac{L}{\sqrt{V_\ell}}
\left(E_{\rho_t}d+\frac{2B}{\lambda}\|m_T'\|\right).
\]
But
\[
\frac{L}{\sqrt{V_\ell}}\le\sqrt{\frac{\varepsilon}{p}}
\]
is eventually bounded. `DataDissipation` supplies
\[
\int_0^\infty E_{\rho_t}d\,dt<\infty,
\qquad
\int_0^\infty\|m_T'\|\,dt<\infty.
\]
Therefore the weighted **backward radial variation** is finite:
\[
\int^\infty g_M(r(t))(r'(t))_-\,dt<\infty.
\]

If the ray is integrable, its primitive \(G\) has a finite limit at infinity. Using
\[
g_M(r)|r'|
=\frac{d}{dt}G(r)+2g_M(r)(r')_-,
\]
we obtain
\[
\int^\infty g_M(r(t))|r'(t)|\,dt<\infty.
\]

Finally,
\[
\|v'\|
\le\lambda^{-1}\|m_T'\|
  +\frac{2B}{\lambda}L|r'|,
\]
so \(v'\) is integrable as well. The upper speed bound
\[
|\eta'|_F
\le |r'|\sqrt{V_\ell}+B\|v'\|
\]
finishes the proof.

This argument neither assumes nor needs eventual monotonicity of \(r\).

## 6. A very cheap additional corollary

**Accessibility is all-or-nothing on the relative interior of a facet.**

For any two fixed tangential parameters \(v,w\), the rays
\[
P_{v-ru},\qquad P_{w-ru}
\]
differ by the uniformly bounded tilt \(-\langle v-w,S\rangle\), independently of \(r\). Lemma C therefore compares their ray speeds by fixed positive constants.

So ray integrability is independent of \(v_M\). Once `FacetFisherAccess` lands, either every point of \(\operatorname{ri}F\) is accessible or none is. This is probably the quickest geometric corollary to formalize before the data-response strengthening.