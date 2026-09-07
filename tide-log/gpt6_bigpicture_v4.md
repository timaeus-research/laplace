Querying gpt-6-astra (timeout: 540s)...
Response received in 172.4s
## Executive recommendation

Your 1D result now supports a materially stronger paper-facing claim: **a smooth, finite-order asymptotic expansion to arbitrary order, with explicit coefficients**. The remaining qualification is identification with the paper’s particular tree indexing—not the existence or error estimate of the expansion.

For the next stretch:

1. **Use parameter integration for the strict-gap face theorem.** Your existing block theorem already contains the hard local analysis. Do not rebuild it through a composed density merely to integrate out noncritical variables.
2. **Develop the weighted finite-part lemma as the gateway to higher-order \(d=2\).** It gives a clean, explicit coefficient calculus.
3. **Keep the analytic bridge separate and small.** The infinite axis-series formula for \(B\) is an excellent first application.
4. **Do not pursue general multiplicity-\(m\), all-order expansions through the constant-kernel product identity alone.** General amplitudes require higher face data; the equal-\(k\) case simplifies the indexing but does not remove that issue.

Below, densities use an **unscaled product variable \(x\)**, with the kernel evaluated at \(s=Nx\). This avoids confusing a density variable with your convention \(s=N\prod u_i^{k_i}\).

---

# (a) A \(d=2\) block with noncritical face parameters

## Recommended architecture: an abstract integration wrapper

Let
\[
q=p+\delta,\qquad \delta>0,
\]
and write
\[
t(w)=\prod_{\ell=1}^{d'}w_\ell^{k_\ell},\qquad
d\mu(w)=\prod_\ell w_\ell^{h_\ell}\,dw.
\]
Work almost everywhere on the positive interior of the box, so \(t(w)>0\).

Suppose the parameterized block integral \(Z_w(n)\) satisfies:

1. **Large-parameter expansion**, for \(n\ge1\):
   \[
   \left|Z_w(n)-n^{-p}\bigl(A(w)\log n+B(w)\bigr)\right|
   \le K(w)n^{-q}(1+\log n).
   \]
2. **Small-parameter bound**, for \(0<n<1\):
   \[
   |Z_w(n)|\le G(w).
   \]
3. \(t(w)\le T<\infty\), and the functions involved are measurable.
4. The envelope moment
   \[
   \int t(w)^{-q}
   \bigl(G(w)+K(w)+|A(w)|+|B(w)|\bigr)\,d\mu(w)<\infty.
   \tag{A1}
   \]

Then, for
\[
Z(N)=\int Z_w(Nt(w))\,d\mu(w),
\]
prove
\[
\left|Z(N)-N^{-p}\bigl(\bar A\log N+\bar B\bigr)\right|
\le C N^{-q}(1+\log N),\qquad N\ge1,
\]
where
\[
\boxed{\bar A=\int t^{-p}A\,d\mu,}
\]
\[
\boxed{\bar B=\int t^{-p}(B+A\log t)\,d\mu.}
\]

This wrapper should know nothing about anchored decompositions, Gaussian kernels, or derivatives.

### The bad region \(Nt<1\)

This is simpler than estimating its measure.

For \(0<n<1\),
\[
n^{-p}\le n^{-q},
\qquad
n^{-p}|\log n|
\le \frac{1}{e\delta}n^{-q}.
\]
Consequently,
\[
\left|Z_w(n)-n^{-p}(A\log n+B)\right|
\le n^{-q}\left(G+|B|+\frac{|A|}{e\delta}\right).
\]
With \(n=Nt(w)\), integration over the bad region gives directly
\[
O(N^{-q})
\]
using (A1).

**Crucial point:** on the bad region, subtract the complete local expression
\[
(Nt)^{-p}\bigl(A\log(Nt)+B\bigr).
\]
Do not separately estimate its \(\log N\) and \(\log t\) pieces. Their combined logarithm gives the clean gain above.

On the good region,
\[
1+\log(Nt)\le 1+\log N+\log^+T,
\]
which gives the desired \(O(N^{-q}(1+\log N))\).

### Why the strict gap supplies the envelope moment

Put
\[
p_\ell=\frac{h_\ell+1}{k_\ell}.
\]
For bounded \(G,K,A,B\),
\[
\int t^{-q}\,d\mu
=\prod_\ell\int_0^{b_\ell}
w_\ell^{h_\ell-k_\ell q}\,dw_\ell<\infty
\]
exactly when
\[
p_\ell>q=p+\delta.
\]

Moreover, (A1) already implies finiteness of \(\bar A,\bar B\), because on \(0<t\le T\),
\[
t^\delta(1+|\log t|)
\]
is bounded. Thus you need not separately assume a logarithmic moment, although exposing that consequence as a helper lemma will be useful.

## Instantiating this for \(\Phi\), or for \(\xi,\eta\)

Define
\[
Z_w(n)=
\int_{[0,b_1]\times[0,b_2]}
u^{k_1p-1}v^{k_2p-1}
e^{-\beta(nu^{k_1}v^{k_2})^2}
\Phi(u,v,w,nu^{k_1}v^{k_2})\,du\,dv.
\]

For your physical application,
\[
\Phi(u,v,w,s)=\eta(u,v,w)e^{+\beta s\xi(u,v,w)}.
\]

The most Lean-friendly theorem should assume **exactly your existing anchored-decomposition envelope hypotheses**, uniformly in \(w\), or with measurable envelope constants depending on \(w\). Package their consequences as measurable \(A,B,K\).

A simple sufficient smooth specialization is:

- \(\beta>0,\ p>0,\ k_i>0,\ b_i>0\);
- \(\xi,\eta\) have bounded compatible axis and mixed derivatives on the closed box sufficient for your existing anchored theorem;
- choose
  \[
  0<\delta<\min\{1/k_1,1/k_2,\min_\ell(p_\ell-p)\}
  \]
  for a first-order anchored implementation;
- the resulting \(s\)-envelopes have the form
  \[
  C(1+s)^D e^{Bs}.
  \]

Compactness then gives uniform \(A,B,K,G\). For \(G\), only a bound for \(\Phi\) on
\[
0\le s\le b_1^{k_1}b_2^{k_2}
\]
is needed.

If your existing block theorem permits a larger \(\delta\), use that theorem’s admissible range rather than imposing the first-order restriction.

## The density route: exact formula and its cost

Let \(\rho_w(x,s)\) be the unscaled \(d=2\) density. Writing
\[
B_*=b_1^{k_1}b_2^{k_2},
\]
the full density is
\[
\boxed{
\rho_{\mathrm{full}}(x,s)
=
\int_{\{w:x<B_*t(w)\}}
t(w)^{-1}\rho_w(x/t(w),s)\,d\mu(w).
}
\]
Then
\[
Z(N)=\int_0^\infty e^{-\beta(Nx)^2}
\rho_{\mathrm{full}}(x,Nx)\,dx.
\]

If
\[
\rho_w(x,s)
=x^{p-1}\bigl(L(w,s)\log(1/x)+D(w,s)\bigr)
+R_w(x,s),
\]
the full leading density coefficients are
\[
\bar L(s)=\int t^{-p}L(w,s)\,d\mu,
\]
\[
\bar D(s)=\int t^{-p}\bigl(D(w,s)+L(w,s)\log t\bigr)\,d\mu.
\]

Sufficient envelope hypotheses are:

- \(|L|+|D|\le E(w,s)\);
- \(|R_w(x,s)|\le x^{q-1}(1+|\log x|)H(w,s)\);
- integrability of the corresponding \(w\)-weighted envelopes, for example
  \[
  \int t^{-q}(1+|\log t|)(E+H)(w,s)\,d\mu(w),
  \]
  followed by the \(s\)-moment and tail hypotheses of your transfer theorem.

The extra logarithmic \(w\)-weight is a convenient sufficient assumption, not always necessary. In the uniformly bounded-parameter case, the strict gap also supplies it.

**Important limitation:** for general \(w\)-dependent \(\Phi\), there is no scalar “noncritical product density” that by itself captures the composition. The formula above retains the full \(w\)-dependence. Replacing it by a scalar product density requires independence from \(w\), dependence only through \(t(w)\), or an additional disintegration theorem.

That is another reason to prefer route (i).

### Sign and normalization check

With
\[
\mathcal M_{\lambda,j}(F)
=\int_0^\infty s^{\lambda-1}e^{-\beta s^2}
(\log s)^jF(s)\,ds,
\]
the block coefficients are
\[
A(w)=\mathcal M_{p,0}(L(w,\cdot)),
\qquad
B(w)=\mathcal M_{p,0}(D(w,\cdot))
-\mathcal M_{p,1}(L(w,\cdot)).
\]
Thus the \(+\log t\) in \(\bar B\) is correct, as is the minus sign on the \(\log s\) moment.

---

# (b) Weighted finite parts and the \(d=2\) cutoff density

## First prove an exact identity with a bounded remainder

Fix \(b,A,k>0\), \(\gamma\ge0\), and an integer \(M>\gamma\). Suppose
\[
f(v,s)=\sum_{m=0}^{M-1}f_m(s)v^m+R_M(v,s),
\qquad
|R_M(v,s)|\le H(s)v^M
\]
for \(0<v\le b\).

Put
\[
\varepsilon=(r/A)^{1/k},\qquad 0<r\le Ab^k.
\]

Define
\[
\begin{aligned}
\operatorname{FP}_\gamma f(s)
={}&
\int_0^b v^{-1-\gamma}
\left(f(v,s)-\sum_{m=0}^{\lfloor\gamma\rfloor}f_m(s)v^m\right)\,dv\\
&+\sum_{\substack{0\le m\le\lfloor\gamma\rfloor\\m\ne\gamma}}
\frac{f_m(s)b^{m-\gamma}}{m-\gamma}
+\mathbf1_{\gamma\in\mathbb N}f_\gamma(s)\log b.
\end{aligned}
\tag{B1}
\]

Then
\[
\begin{aligned}
J(r,s)
={}&\operatorname{FP}_\gamma f(s)
-\sum_{\substack{0\le m<M\\m\ne\gamma}}
\frac{f_m(s)}{m-\gamma}
(r/A)^{(m-\gamma)/k}\\
&+\mathbf1_{\gamma\in\mathbb N}\frac{f_\gamma(s)}k\log(A/r)
+E_M(r,s),
\end{aligned}
\tag{B2}
\]
with
\[
\boxed{
|E_M(r,s)|
\le \frac{H(s)}{M-\gamma}
(r/A)^{(M-\gamma)/k}.
}
\tag{B3}
\]

Here the integer-resonance term is present only when \(\gamma\) is an integer; automatically \(\gamma<M\).

### A terminology correction worth making explicit

The integral mentioned in your question—the first line of (B1)—is the **regularized integral part**. It is not by itself the full constant coefficient of \(J\). The upper-endpoint counterterms in the second line are necessary.

You can define both objects, but reserve `finitePart` for their sum, or make the distinction explicit in names.

### How this plugs into `DensityExpansion`

After multiplication by \(r^{a_0-1}\):

- the finite-part term has exponent \(a_0\);
- the \(m\)-th monomial term has exponent
  \[
  a_0+(m-\gamma)/k;
  \]
- resonance produces exponent \(a_0\) with log degree \(1\);
- the remainder has exponent
  \[
  a_0+(M-\gamma)/k
  \]
  and log degree \(0\).

If you permit the endpoint case \(M=\gamma\), the residual integration gives a logarithmic bound rather than (B3). I would **not** include that case in the first lemma. Choose \(M>\gamma\), then weaken remainder orders when assembling the cutoff theorem.

## Exact coefficient list for the equal-exponent \(d=2\) block

Allow \(k_1,k_2\) to differ, but retain
\[
h_i=k_ip-1.
\]

Define compatible face jets
\[
a_i(v,s)=[u^i]\Phi(u,v,s),\qquad
b_j(u,s)=[v^j]\Phi(u,v,s),
\]
and corner jets \(c_{ij}(s)\). These should initially be **explicit jet data**, not derivative definitions.

For a shift cutoff \(\tau>0\), set
\[
Q_\tau=
\{i/k_1:i\in\mathbb N,\ i/k_1<\tau\}
\cup
\{j/k_2:j\in\mathbb N,\ j/k_2<\tau\},
\]
\[
\Lambda_\tau=\{p+q:q\in Q_\tau\}.
\]

For each \(q\in Q_\tau\), define
\[
L_q(s)=
\begin{cases}
c_{ij}(s)/(k_1k_2),
& q=i/k_1=j/k_2,\\
0,&\text{otherwise},
\end{cases}
\tag{B4}
\]
and
\[
\boxed{
D_q(s)=
\mathbf1_{q=i/k_1}\frac1{k_1}
\operatorname{FP}_{k_2q}\bigl(a_i(\cdot,s)\bigr)
+
\mathbf1_{q=j/k_2}\frac1{k_2}
\operatorname{FP}_{k_1q}\bigl(b_j(\cdot,s)\bigr).
}
\tag{B5}
\]

The indicators mean “include the term if such an integer exists”; there is at most one integer on each side.

The density theorem should conclude
\[
\boxed{
\rho_\Phi(r,s)=
\sum_{q\in Q_\tau}
r^{p+q-1}\bigl(L_q(s)\log(1/r)+D_q(s)\bigr)
+R_\tau(r,s),
}
\]
with
\[
|R_\tau(r,s)|
\le C r^{p+\tau-1}(1+|\log r|)H_*(s),
\qquad 0<r\le B_*.
\tag{B6}
\]

Thus **logs occur precisely at collisions**
\[
i/k_1=j/k_2,
\]
subject, of course, to the relevant corner coefficient being nonzero.

The safe uniform remainder log degree is \(1\). If \(\tau\) is not a resonant omitted exponent, sharper versions can often use degree \(0\); do not optimize that initially.

### Sufficient jet hypotheses

Choose integers
\[
M_1/k_1>\tau,\qquad M_2/k_2>\tau.
\]
Require:

- compatible Taylor remainders of \(a_i\) in \(v\), through order \(M_2\);
- compatible Taylor remainders of \(b_j\) in \(u\), through order \(M_1\);
- the rectangular anchored identity
  \[
  \Phi=
  \sum_{i<M_1}u^ia_i(v)
  +\sum_{j<M_2}v^jb_j(u)
  -\sum_{i<M_1,j<M_2}c_{ij}u^iv^j
  +R,
  \]
  with
  \[
  |R(u,v,s)|\le H(s)u^{M_1}v^{M_2}.
  \]

Include envelopes for the finitely many jets and axis remainders. This gives \(H_*\), to which your existing transfer moment hypotheses apply.

## Lean construction order

1. **Monomial block density**, in nonresonant and resonant forms:
   \[
   \rho_{u^iv^j}(r)
   =
   \frac{r^{p+i/k_1-1}}{k_1}
   \frac{
   b_2^{j-k_2i/k_1}
   -(r/b_1^{k_1})^{(j-k_2i/k_1)/k_2}
   }{j-k_2i/k_1},
   \]
   or, at resonance \(q=i/k_1=j/k_2\),
   \[
   \rho_{u^iv^j}(r)
   =\frac{r^{p+q-1}}{k_1k_2}\log(B_*/r).
   \]
2. Weighted finite-part axis lemma.
3. Explicit facewise Taylor operators and compatibility records.
4. Rectangular decomposition plus shifted constant-block remainder estimate.
5. Cutoff bookkeeping and `DensityExpansion` packaging.
6. Smooth specialization last.

For initial packaging, use tagged axis indices and allow duplicate exponents if `DensityExpansion` permits that. Prove the grouped formulas (B4)–(B5) afterward. Avoid making finite-set collision arithmetic the first obstacle.

---

# (c) The analytic bridge

## Reusable weighted interchange theorem

First expose a theorem for an arbitrary measurable weight \(W\), not specifically a Gaussian.

If \(f_t\) are measurable and
\[
\sum_t\int |W(s)f_t(s)|\,ds<\infty,
\]
then
\[
\int W(s)\left(\sum_t f_t(s)\right)\,ds
=
\sum_t\int W(s)f_t(s)\,ds,
\]
with the appropriate a.e. summability/integrability conclusions.

Then specialize to
\[
W_{\lambda,j}(s)
=\mathbf1_{s>0}s^{\lambda-1}e^{-\beta s^2}(\log s)^j.
\]

The useful domination corollary is:

> If \(\beta>0,\lambda>0\), \(j\in\mathbb N\), the \(f_t\) are measurable, and
> \[
> \sum_t|f_t(s)|\le C(1+s)^D e^{Bs}
> \]
> almost everywhere on \(s>0\), then
> \[
> \sum_t\|W_{\lambda,j}f_t\|_{L^1}<\infty,
> \]
> and \(\mathcal M_{\lambda,j}\) commutes with the series.

Here \(D\ge0\), \(B\in\mathbb R\). Tonelli plus your Gaussian envelope moments proves the corollary. In Lean, an `ENNReal` formulation of the absolute-sum domination may avoid premature summability obligations.

## First genuine infinite series: yes, use the axis contribution to \(B\)

Suppose
\[
\Psi(u,s)=\sum_{i=0}^\infty\Psi_i(s)u^i,
\qquad 0\le u\le b,
\]
and choose a radius margin
\[
0<b<\rho.
\]
A convenient sufficient hypothesis is
\[
|\Psi_i(s)|\rho^i\le H(s)
\quad\text{for every }i,
\]
where \(H\) has the necessary Gaussian log moments.

Then
\[
\boxed{
I_\Psi(s)=
\int_0^b\frac{\Psi(u,s)-\Psi_0(s)}u\,du
=
\sum_{i=1}^\infty\frac{b^i}{i}\Psi_i(s).
}
\]
Both the axis interchange and the subsequent log-moment interchange are absolutely justified. Indeed,
\[
\sum_{i\ge1}\frac{b^i}{i}|\Psi_i(s)|
\le H(s)\sum_{i\ge1}(b/\rho)^i
=\frac{b/\rho}{1-b/\rho}H(s).
\]

For the full \(d=2\) constant coefficient, suppose
\[
\Phi(u,0,s)=\sum_{i\ge0}a_i(s)u^i,\qquad
\Phi(0,v,s)=\sum_{j\ge0}b_j(s)v^j,
\]
with respective radius margins, and \(a_0=b_0=c\). Then
\[
\boxed{
\begin{aligned}
B={}&
\frac{\log B_*}{k_1k_2}\mathcal M_{p,0}(c)
-\frac1{k_1k_2}\mathcal M_{p,1}(c)\\
&+\frac1{k_2}\sum_{i\ge1}\frac{b_1^i}{i}\mathcal M_{p,0}(a_i)
+\frac1{k_1}\sum_{j\ge1}\frac{b_2^j}{j}\mathcal M_{p,0}(b_j).
\end{aligned}
}
\]

This is genuinely infinite, directly relevant to an already formalized coefficient, and does **not** claim convergence of the \(N\)-asymptotic expansion.

Initially formulate it from supplied series and majorants. Deriving those majorants from complex analyticity can be a later bridge.

---

# (d) All orders for multiplicity \(m\)

For **general** \(\xi,\eta\), there is no clean reduction to your scalar 1D engine through the constant-kernel product density.

The obstruction is substantive: higher coefficients depend on jets along faces of all codimensions, not merely corner Taylor data. Even in \(d=2\), \(B\) already contains complete axis integrals.

The honest possibilities are:

- **Restricted product-dependent amplitude:** if the amplitude depends only on
  \[
  z=\prod_i u_i^{k_i},
  \]
  the exact product density reduces the problem to a 1D expansion with a fixed polynomial in \(\log z\). Your transfer machinery should handle this cleanly.
- **Finite sums of separable amplitudes:** potentially useful, but a distinct restricted theorem.
- **General amplitudes:** develop higher facewise finite-part calculus. Equal \(k_i\) gives the clean lattice \(p+n/k\), with log degrees at most \(m-1\), but still requires that calculus.

So: the \(d=2\) \(\tau\)-cutoff theorem is not logically the only route, but **some equivalent higher-order face machinery is unavoidable**. I would not open a separate general-\(m\) project now.

---

# (e) Updated paper-facing annotations

### `thm:TaylorTree`

> The smooth one-dimensional asymptotic expansion is formalized to every finite order, with an explicit finite-order remainder bound. Its coefficients are given by finite coefficient extractions from truncated exponential jets. Identification of this coefficient formula with the theorem’s tree-indexed formula remains an unformalized finite combinatorial identity.

You may say:

> “The one-dimensional case of the tree expansion is formalized to every finite order, modulo identification of the coefficient indexing.”

Without that final qualification, the phrase suggests that the actual tree formula has been checked.

### `cor:standardintegralexp`

> In one dimension, the expansion through any prescribed finite order is formalized under \(C^R\) hypotheses, with remainder \(O(N^{-(p+R/k)})\). Each coefficient is an explicit finite linear combination of standard integrals \(S_\lambda(x_0)\), with polynomial weights in \(\beta\) and the Taylor data. No convergence of the full asymptotic series is asserted.

### `eq:flucttreeterms`

> The one-dimensional fluctuation coefficients are formalized in the equivalent-looking polynomial-exponential form
> \[
> e_{j,m}=\sum_{\ell\le j}y_\ell[u^{j-\ell}](g_R^m),
> \qquad
> c_j=\frac1k\sum_{m<R}\frac{\beta^m}{m!}
> e_{j,m}S_{p+j/k+m}(x_0).
> \]
> Equality with the displayed tree sum has not yet been formally proved.

I would replace “equivalent-looking” in final publication prose by “an alternative”; reserve “equivalent” for the proved identification.

---

# (f) Jet identities: priorities and costs

## First: derivative identification

Prove
\[
F_j(s)=\frac1{j!}
\left.\partial_u^j\bigl(\eta(u)e^{\beta s\xi(u)}\bigr)\right|_{u=0},
\qquad j<R.
\]

This is the most useful next identity. It establishes a canonical, truncation-independent interpretation of the coefficients.

**Cheapest route:** use uniqueness of Taylor coefficients.

You already have an order-\(R\) remainder for the supplied polynomial. Smooth Taylor theory gives another. Their difference is a polynomial \(O(u^R)\) as \(u\to0^+\), so its coefficients below \(R\) vanish.

That may be substantially cheaper than formalizing repeated chain-rule expressions. It also avoids Faà di Bruno entirely.

Expected cost: **low–medium**, depending on your polynomial/Taylor uniqueness library.

## Second: recursion, if you want a computational interface

For \(1\le n<R\),
\[
nE_n(s)=\beta s\sum_{i=1}^n i x_iE_{n-i}(s).
\]

Prove it with **finite polynomial algebra**, not a new `PowerSeries` exponential development.

Let
\[
T_R=\sum_{m<R}\frac{(\beta s)^m}{m!}g_R^m.
\]
The polynomial
\[
T_R'-\beta s g_R'T_R
\]
is divisible by \(X^{R-1}\), because \(g_R\) is divisible by \(X\). Comparing coefficients below degree \(R-1\) gives the recurrence.

Expected cost: **medium**. It is useful but not needed for the asymptotic theorem.

## Third: partition formula

For \(n<R\),
\[
E_n(s)=
\sum_{\substack{a_1,\dots,a_n\ge0\\
\sum i a_i=n}}
\prod_{i=1}^n\frac{(\beta s x_i)^{a_i}}{a_i!}.
\]

This is mathematically straightforward but Lean-expensive: constrained finite index types, multinomial factors, and reindexing.

Expected cost: **medium–high**.

## Last: tree reindexing

This is the only item that closes the paper’s literal tree-indexing gap. Its cost depends heavily on the paper’s tree conventions and automorphism factors.

Expected cost: **high and uncertain**.

**Recommended order:** derivative identification → recursion if useful → partition formula when starting the tree bridge → tree reindexing. None is a prerequisite for targets 3–5.

---

# (g) Next five bounded units

I would distinguish a 150–300-line **unit** from a completed headline theorem. The full \(d=2\) cutoff theorem is several units, not one.

| Rank | Unit | Precise deliverable |
|---|---|---|
| **1** | Strict-gap parameter integration | From the large-\(n\) expansion, small-\(n\) bound, bounded \(t\), and (A1), prove the integrated expansion with the displayed \(\bar A,\bar B\). |
| **2** | Weighted finite-part axis lemma | Prove (B1)–(B3), preferably first as an exact integral identity plus a separate remainder estimate. |
| **3** | Weighted series interchange | Abstract weighted \(L^1\) interchange, then the Gaussian log-moment normal-domination corollary. |
| **4** | Infinite axis-series coefficient | Prove \(I_\Psi=\sum_{i\ge1}\Psi_i b^i/i\) under a radius margin and majorant; derive the absolutely convergent series formula for the existing \(d=2\) coefficient \(B\). |
| **5** | Canonical identification of 1D jets | Identify \(F_j\) with the normalized derivative, preferably through Taylor uniqueness; derive independence from the chosen truncation order for \(j<R\). |

Two scheduling qualifications:

- If uniformity/measurability of your parameterized block constants is not already exposed, rank 1 may need a preparatory unit. Do not hide that work inside the abstract wrapper.
- Immediately after these five, do **monomial block densities**, then the rectangular face-jet decomposition. Those are the next concrete steps toward the full cutoff theorem.

The strongest near-term portfolio is therefore: **all-order 1D + strict-gap face parameters + one genuinely infinite coefficient identity**, while building the finite-part infrastructure needed for honest higher-order \(d=2\).
