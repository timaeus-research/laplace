## Executive assessment

The response identities are mathematically right, subject to the usual nonzero-normalizer and fixed-stratum hypotheses. The most important remaining gap is not another scalar derivative formula: it is connecting the **actual atlas leading measure** to a differentiable, normalized response map.

Two corrections matter for the proposed wall theory:

1. `τ = σ log t` is not a universal wall coordinate, and the logarithmic example’s displayed profile needs a restriction on how `τ` grows.
2. In **offset coordinates**, both examples have a transverse scale of order `1 / log t`. The apparent “power scale versus logarithmic scale” distinction comes partly from switching between coefficient coordinates and valuation coordinates.

I can audit the mathematics described here, not whether each Lean declaration contains all the hypotheses mentioned below.

---

## 1. Audit of the landed statements

### 1.1 Singular fluctuation–response

Write
\[
Z(a)=\int U_a^{-\lambda}\,d\nu,\qquad
d\nu_a=Z(a)^{-1}U_a^{-\lambda}\,d\nu,
\qquad R_v=\sum_i v_i h_i.
\]
Then
\[
D_v\log U_a^{-\lambda}
=-\lambda\,\frac{R_v}{U_a}.
\]
Consequently,
\[
D_v\operatorname{faceCoef}(\phi)
=-\lambda\int \phi U_a^{-\lambda-1}R_v\,d\nu
\]
and
\[
D_v\mathbb E_{\nu_a}[\phi]
=-\lambda\operatorname{Cov}_{\nu_a}
       \left(\phi,\frac{R_v}{U_a}\right).
\]

**The sign, ratio, and normalization are all correct.** The ratio is essential.

Audit these hypothesis details:

- **Nonzero measure:** require \(0<Z(a)<\infty\), normally obtained from finite, nonzero \(\nu\) and uniform positivity of \(U_a\). Totalized division can make a Lean statement true for zero measure without making it a posterior theorem.
- **Local positivity:** bounded \(R_v\) and \(U_a\ge c>0\) provide positivity in an open interval around zero. This is what licenses a two-sided derivative.
- **Mixture constraints:** within a probability simplex, physical directions satisfy \(\sum_i v_i=0\). At its boundary, some directions are only one-sided. The ambient coefficient derivative remains useful, but distinguish it from an admissible mixture derivative.
- **Fixed observable:** if \(\phi\) also changes with the weights, add \(\mathbb E_{\nu_a}[D_v\phi]\).
- **Fixed face:** this is smooth response inside a region with uniform positivity. It does not by itself control approach to a wall where the unit vanishes or the dominant face changes.

Calling it “singular fluctuation–response” is reasonable, provided the theorem is presented as response of the **singular leading law**, not as a finite-\(t\) identity without an asymptotic bridge.

### 1.2 Is the resolved mixture unit affine?

**Yes, exactly—not merely to leading order—when the resolved phase itself is affine and the resolution and extracted monomial are fixed.**

Suppose
\[
L_a=\sum_i a_iL_i,\qquad
L_i\circ\pi=Mh_i
\]
on a common chart. Then
\[
L_a\circ\pi=M\sum_i a_i h_i=M U_a
\]
exactly. Taking a fixed boundary restriction or scaling limit also preserves this affinity:
\[
U_{a,\infty}=\sum_i a_i h_{i,\infty}.
\]

But “common resolution” alone needs unpacking:

- The populations might initially have different exceptional monomial factors. After extracting a common factor, the remaining \(h_i\) need not individually be units.
- Uniform positivity of their weighted sum may hold only on a selected coefficient region.
- If the resolution, truth segment, centering, or extracted factor depends on \(a\), differentiation introduces additional terms.
- A population loss expressed as a **data-dependent excess loss** need not be affine. For example, entropy terms or subtracting an \(a\)-dependent minimum can destroy literal affinity even when the uncentered expected loss is affine.

Thus the trace bridge is faithful under a **fixed common-factor representation**, not automatically for every mixture of populations.

Also check that the trace hypotheses explicitly give
\[
0<\rho<\infty,\qquad q\eta>0
\]
for the asserted finite measure \(u^{q\eta-1}du\), and that \(w\) is integrable for that measure. The derivative formula for the leading constant presumes that \(C_0,\beta,\rho\), and the trace measure are independent of the differentiated weights.

### 1.3 The wall example

For \(s,t>0\), the exact identity and remainder estimate give
\[
tZ(t,s)=\log(1+s^{-1})+O\!\left(\frac{e^{-ts}}{ts}\right).
\]
Therefore, with \(s=e^{-\tau}\),
\[
tZ(t,e^{-\tau})
=\log(1+e^\tau)
+O\!\left(\frac{e^{-t e^{-\tau}}}{t e^{-\tau}}\right).
\]

This gives the profile uniformly for bounded \(\tau\), and more generally gives an additive \(o(1)\) whenever
\[
t e^{-\tau}\longrightarrow\infty.
\]

In particular, for fixed \(0<\sigma<1\),
\[
tZ(t,t^{-\sigma})=\sigma\log t+o(1).
\]
So the claimed \(\sigma\log t\)-scale behavior is genuine.

**Hidden weakness:** the same additive profile approximation is not valid across \(\tau\sim\log t\). There is a second crossover at \(ts\asymp1\). Indeed, for \(s=c/t\), \(c>0\),
\[
tZ(t,c/t)-\log t
\longrightarrow -\log c-E_1(c),
\qquad
E_1(c)=\int_c^\infty \frac{e^{-u}}u\,du.
\]
The right side extends to Euler’s constant at \(c=0\). In particular, the leading logarithmic coefficient saturates at \(1\) for fixed \(\sigma\ge1\), rather than continuing as \(\sigma\).

The \(s=e^{-\sqrt{\log t}}\) result is especially useful: it shows that arbitrary moving paths can produce scales not described by a fixed integer log multiplicity.

### 1.4 Other landed packages

- **`offsetLP`:** convexity and antitonicity have the right directions. Check feasibility and finiteness assumptions if the infimum is real-valued rather than extended-real-valued; empty or unbounded feasible problems should not acquire misleading totalized values.
- **Gibbs variational:** the gap identity is correct. Distinguish “equality attained at \(\rho_t\)” from “equality iff \(\rho=\rho_t\) a.e.” The latter is a useful separate result. Support and integrability hypotheses are substantive, especially with totalized real logarithms.
- **Path Hessian:** all displayed formulas are correct for \(F=-\log Z\), fixed observables, and a fixed reference measure. The e-geodesic formula requires a fixed loss and a normalized exponential tilt with sufficient statistic \(a\).
- **Thermodynamic length:** the covariance estimate is correct. The endpoint theorem currently described is a **uniform-speed Lipschitz corollary**, rather than the full integrated thermodynamic-length estimate.
- **Base-point continuity:** `tendsto_mixExp_zero` is an important endpoint anchor, but says nothing yet about uniformity in direction or singular-limit interchange.

---

## 2. General representation: differentiate first, marginalize second

### Recommended architecture

Use **(i) exponential-form differentiation as the foundational theorem**, then **(ii) face marginalization as a structural corollary**.

Write a term measure as
\[
d\mu_a(x)=H(x)e^{-B U_a(u_\infty(x))P(x)}\,dm(x),
\qquad P(x)=\prod_j u_j^{\kappa_j},
\]
where \(H\), the domain, and the scaling map are fixed. Define
\[
S_v(x)=B R_v(u_\infty(x))P(x).
\]
Then the basic theorem is
\[
D_v\int\phi\,d\mu_a=-\int\phi S_v\,d\mu_a.
\]

This is the natural target on top of `termMeasure`: it does not require the limit domain to factor, or the observable to ignore the scaled coordinate.

### The domination caveat

“Profile times a polynomial” is the right heuristic, but not an automatic integrable bound.

If \(U_{a+\varepsilon v}\ge c>0\), differentiation is dominated using an envelope such as
\[
|\phi|\,|H|\,|R_v|P\,e^{-BcP}.
\]
One typically absorbs the polynomial by weakening the exponential:
\[
P^k e^{-BcP}\le C_k e^{-(Bc/2)P}.
\]
You still need integrability of the weakened profile against the remaining atlas factors.

### What the measure derivative actually says

For the unnormalized measure,
\[
D_v\mu_a=-S_v\,\mu_a
\]
in a specified sense: weak differentiation against a test class, or, with sufficiently strong domination, differentiation in total variation.

For its normalization \(\bar\mu_a=\mu_a/\mu_a(X)\),
\[
D_v\mathbb E_{\bar\mu_a}[\phi]
=-\operatorname{Cov}_{\bar\mu_a}(\phi,S_v).
\]

Thus:

- **unnormalized:** derivative is an integral against a signed score-weighted measure;
- **normalized:** covariance remains covariance.

It is not quite right to say the covariance “becomes an expectation”; that happens only because one has stopped normalizing.

### Why still prove the face reduction?

When the scaled coordinate has a genuine Gamma integral,
\[
\int_0^\infty z^{\beta-1}e^{-BU_a(u)z}\,dz
=\Gamma(\beta)(BU_a(u))^{-\beta},
\]
the exponential score conditionally averages to
\[
\mathbb E[B R_v(u)z\mid u]
=\beta\,\frac{R_v(u)}{U_a(u)}.
\]
This is the exact bridge between the two response formulas.

But it requires the appropriate product domain and radial factorization. It is not automatic for every atlas term. Nor does it reduce an arbitrary observable depending on \(z\) to the same fixed \(\phi(u)\).

**Important separation:** differentiability of the leading measure does not yet prove convergence of differentiated finite-\(t\) posteriors. That needs uniform asymptotics or a separate dominated derivative-limit theorem.

---

## 3. Analyticity: power series are the cheaper route

For these particular integrands, I would avoid building a complex-analysis infrastructure unless the project already needs it.

### Face coefficients

At \(a_0\), put \(U_0=U_{a_0}\). For a coefficient increment \(b\),
\[
U_{a_0+b}^{-\lambda}
=U_0^{-\lambda}
\sum_{n=0}^{\infty}
\frac{(-1)^n(\lambda)_n}{n!}
\left(\frac{R_b}{U_0}\right)^n.
\]
If
\[
|R_b|/U_0\le q<1
\]
uniformly, dominated summation gives the integrated series. The domination is simply an integrable multiple of \(|\phi|\), since \(U_0\ge c>0\).

The coefficient bounds give a positive convergence radius. For the full finite-dimensional coefficient map, the homogeneous terms are integrated products of the linear map \(b\mapsto R_b\).

### Exponential tilts

For bounded \(\Delta\),
\[
\int\phi e^{-ts\Delta}\,d\nu
=\sum_{n=0}^{\infty}
\frac{(-t)^n s^n}{n!}\int\phi\Delta^n\,d\nu.
\]
The factorial makes this particularly cheap: the unnormalized map is entire, and its real normalized posterior is locally analytic because its denominator is positive.

### Is it worth doing now?

Not before the leading-measure response bridge.

If the immediate goal is response tensors, an all-orders differentiation API is likely cheaper and more useful:
\[
\frac{d^n}{ds^n}\mathbb E_s[\phi]
=(-t)^n\kappa_s(\phi,\underbrace{\Delta,\ldots,\Delta}_{n}).
\]
For \(F=-\log Z\),
\[
F^{(n)}=(-1)^{n+1}t^n\kappa_n(\Delta).
\]

These formulas apply directly to a **linear exponential tilt**. For \(U_a^{-\lambda}\), the log-density is nonlinear in \(a\); higher derivatives include higher derivatives of \(\log U_a\), not just repeated copies of one fixed score.

A practical order is:

1. explicit unnormalized higher derivatives;
2. normalized recursive response formulas;
3. cumulant identification;
4. analytic packaging.

Smoothness alone does not establish analyticity; retain the quantitative coefficient bounds if analyticity is a later target.

---

## 4. Wall crossover: revise the organizing principle

### Both examples have logarithmic offset width

For the quartic example, the wall is \(\sigma_*=\tfrac12\), and
\[
c=s\sqrt t=t^{1/2-\sigma}.
\]
Setting
\[
\sigma=\frac12+\frac{\tau}{\log t}
\]
gives \(c=e^{-\tau}\), hence
\[
t^{1/4}Z\!\left(t,t^{-1/2-\tau/\log t}\right)
=\int_{\mathbb R}e^{-(y^4+e^{-\tau}y^2)}\,dy.
\]

For the logarithmic example, near \(\sigma_*=0\),
\[
\sigma=\frac{\tau}{\log t}
\quad\Longrightarrow\quad s=e^{-\tau}.
\]

So **both use a \(1/\log t\) window in valuation space**. A power of \(t\) enters when expressing the same window in the original coefficient.

### What does optimal-face geometry determine?

Under suitable Newton nondegeneracy and amplitude assumptions:

- the LP value identifies the power exponent;
- optimal-face geometry helps identify logarithmic multiplicity;
- changes of that geometry signal failures of a fixed-stratum expansion.

But it does **not** determine the entire crossover profile. That also depends on coefficients, units, amplitudes, chart boundaries, and how adjacent asymptotic regions match.

“Face-dimension change versus active-set change” is therefore useful combinatorial information, not a complete profile-type classification. The logarithmic example already has a further crossover at \(\sigma=1\) without changing the generic optimal-face dimension.

### A realistic next general theorem

Prove a **fixed-wall rescaling theorem with locally uniform profile convergence**, initially without logarithmic multiplicity.

For a positive monomial phase, choose:

- wall offsets \(\sigma_*\);
- a feasible scaling \(r_*\);
- active indices
  \[
  J_*=\{j:\alpha_j\cdot r_*+\sigma_{*,j}=1\};
  \]
- a transverse direction \(v\);
- offsets
  \[
  \sigma(t,\tau)=\sigma_*+\frac{\tau v}{\log t}.
  \]

After \(x_i=t^{-r_{*,i}}y_i\), active terms retain factors \(e^{-\tau v_j}\), while inactive terms vanish. Under a common integrable envelope, prove
\[
t^{b\cdot r_*}Z(t,\sigma(t,\tau))
\longrightarrow
\Phi(\tau)
\]
locally uniformly in \(\tau\), where
\[
\Phi(\tau)=
\int_{D_\infty}
W_\infty(y)y^{b-1}
\exp\!\left(
-\sum_{j\in J_*}e^{-\tau v_j}
h_{j,\infty}(y)y^{\alpha_j}
\right)\,dy.
\]

Coordinates with \(r_{*,i}=0\) retain their bounded chart range; positively scaled coordinates acquire an unbounded range.

Then use `offsetLP` separately to certify that
\[
b\cdot r_*=\operatorname{offsetLP}(\alpha,b,\sigma_*).
\]

This is a clean division of labor:

- **LP:** selects and certifies the scaling;
- **analysis:** proves the profile and uniform domination.

Do not yet promise a universal \((\lambda,d,\Phi)\) theorem from `offsetLP` alone. Logarithmic faces require integration along scale directions and, sometimes, additive centering such as \(tZ-\log t\), rather than only multiplicative normalization.

---

## 5. Ranked next five packages

Ranked by project value, with a small first landing for each.

| Rank | Package | Cheapest useful first statement |
|---|---|---|
| **1** | **`TermScoreResponse`** | For one fixed atlas term and fixed integrable observable, prove \(D_v\int\phi\,d\mu_a=-\int\phi S_v\,d\mu_a\); then normalized covariance. |
| **2** | **`GammaFaceMarginal`** | Prove one product-domain Gamma marginalization lemma and the score identity \(\mathbb E[S_v\mid u]=\beta R_v/U_a\). Connect it explicitly to `faceCoef`. |
| **3** | **`HigherResponse`** | Prove all-order unnormalized derivatives for bounded exponential tilts, followed by a recursive normalized response API. Avoid starting with general partition combinatorics. |
| **4** | **`WallProfileUniform`** | Upgrade one wall example to convergence uniform on compact \(\tau\)-sets. Then abstract the fixed-active-set rescaling theorem above. |
| **5** | **`ResponseAnalytic`** | Prove a local scalar power-series expansion along one direction; only afterward package the multivariate `HasFPowerSeriesOnBall` statement. |

Two inexpensive side landings would also pay off: the integrated thermodynamic-length inequality, and the logarithmic example’s second wall \(s=c/t\).

### Single most valuable next theorem

**A normalized response theorem for the assembled atlas leading measure.**

On the disjoint union of the dominant chart terms, let
\[
\mu_a=\sum_k\mu_{k,a},
\qquad
S_v|_k=B_kR_{k,v}P_k.
\]
For a fixed dominant stratum and fixed observable, prove
\[
D_v
\frac{\int\phi\,d\mu_a}{\mu_a(X)}
=
-\operatorname{Cov}_{\bar\mu_a}(\phi,S_v).
\]

This must include changes in the relative masses of the chart terms—not merely average their separately normalized covariance formulas.

That theorem turns the representation formula into a genuine **local map of leading responses**. Combined with the base-posterior endpoint and subsequent uniform asymptotic bridges, it is the strongest next step toward mapping responses from the featureless reference to the data.