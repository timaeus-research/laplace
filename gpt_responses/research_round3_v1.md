## A. Statement audit

**Bottom line:** I see no sign or constant error in the displayed formulas. The main qualifications concern interpretation: a profile certificate is not the actual weighted kernel; the distinguishability result is local and normalised; and “isolated-optimum count is closed” is stronger than what the displayed existence/obstruction theorems alone establish.

This audit is conditional on the inherited chart hypotheses and the definitions of the envelopes and kernels. Those definitions matter especially for converting analytic certificates into claims about LP optima.

### 1. `tendsto_modelKernel_partial_var`

The limiting density is the expected one:
\[
W(0_T,z,0)\,[B a(0_T,z,0)]^{-\lambda}
\prod_{j\in N}z_j^{r_j-\lambda\kappa_j}.
\]
The strict gaps give precisely
\[
r_j-\lambda\kappa_j>-1,
\]
so the residual face integral is integrable under the stated boundedness and unit lower bound.

The constant also has the expected structure:
\[
A\,\frac{\delta^k\Gamma(\lambda)}{k!}
\prod_{i\in T}\kappa_i^{-1}.
\]
In particular:

- There are \(k+1\) tied coordinates and a \((\log t)^k\) factor.
- Replacing the large parameter by \(t^\delta\) produces \(\delta^k\).
- The tied coordinates’ upper cutoff does not enter this leading constant; the remaining cutoff dependence is in the face integral.

**Hypothesis qualifications:**

- `ha₀` appears redundant: continuity at each face point and the uniform lower bound on the approaching interior imply \(a(0_T,z,0)\ge a_L>0\). Keeping it for theorem usability is harmless.
- Full `ContinuousAt` is stronger than necessary; continuity along the relevant positive orthant would suffice.
- Global measurability, nonnegativity and boundedness of `W` are also stronger than needed, but not misleading.
- No positivity assumption on `A` is needed for this scalar limit. Positivity **is** needed when interpreting its right-hand side as a positive measure.
- `hγq` is an analytic shrinking-coordinate condition. It should not be paraphrased as separately asserting \(\gamma>0\) and \(q>0\).
- The theorem permits a zero coefficient, including when the face weight vanishes identically. It then gives an upper asymptotic order, not a nonzero leading term.

Thus the theorem is well suited to **“coefficient at the candidate order”** language. Reserve “leading asymptotic” for an additional positivity/nonvanishing conclusion.

### 2. `tendsto_modelKernelOf_partial`

This is the correct chart-level interpretation of the previous result. The observable is evaluated at the represented face point, and the density contains the frozen geometric weight and phase unit.

The note should advertise:

> On a partially tied chart, the coefficient measure is the push-forward of the residual face density, multiplied by the tied-block Gamma/logarithmic constant.

Two qualifications are important.

1. **It is a parameter-space density before push-forward.**  
   It is not generally a density with respect to a canonical volume measure on the represented wall face. The representation map may identify points or lower dimension.

2. **It is a chart contribution, not yet the global limiting measure.**  
   The global coefficient measure requires the atlas weights, admissible branches, and selection of the lexicographically dominant \((\lambda,k)\).

The condition `hQ : D.Qexp i = 0` is substantive. This is the continuously extending, pure-truth-bridge setting, not yet the mixed-truth logarithmic endpoint.

Also, `hφL` says that the **nonzero set** of \(\varphi\) lies in \(L'\). It does not say that its topological support is contained in \(L'\). The distinction matters when documenting the observable class.

### 3. `integral_tiedDom_twoScaled`

The signs and the factor involving \(D/\rho\) are correct.

Write
\[
K=\kappa_S\cdot\log y,\qquad V=Q_S\cdot\log y.
\]
After including the logarithmic Jacobian, the scaled-coordinate power is
\[
e^{\eta K-\theta V}.
\]
The surviving cutoff becomes
\[
V>q\log(D/\rho)-Q_N\cdot\log z.
\]
Consequently,
\[
\int_{V>h(z)}e^{-\theta V}\,dV
=\frac1\theta(D/\rho)^{-q\theta}\prod_N z_j^{\theta Q_j},
\]
while the \(K\)-integral contributes
\[
\Gamma(\eta)c_0^{-\eta}\prod_N z_j^{-\eta\kappa_j}.
\]
The Jacobian is \(1/|\Delta|\).

This verifies:

- the dual sign \(a_S=\eta\kappa_S-\theta Q_S\);
- the **plus** sign \(+\theta Q_j\) in the residual exponent;
- the exponent \(-q\theta\) on \(D/\rho\);
- the absence of an additional factor \(q\) outside that power.

The absence of a separate hypothesis \(\kappa\cdot\alpha=\delta\) is appropriate here: this theorem evaluates a specified limiting-domain integral. Matching that integral to the actual asymptotic scaling belongs to the chart theorem.

### 4. `ProfileIntegrableOf.of_twoScaled`

This is a sound sufficient certificate. Its hypotheses have a clean LP interpretation.

Putting \(a_j=r_j+1\), the decomposition is
\[
a=\eta\kappa-\theta Q+\beta,\qquad
\beta_S=0,\quad \beta_N>0,
\]
with \(\eta,\theta>0\). For feasible \(\alpha'\), compared with the displayed \(\alpha\),
\[
a\cdot(\alpha'-\alpha)
=
\eta(\kappa\cdot\alpha'-\delta)
+\theta(\gamma-Q\cdot\alpha')
+\sum_N\beta_j\alpha'_j.
\]
Every term is nonnegative. Equality forces both active equalities and zero unscaled coordinates; the nonzero determinant then forces \(\alpha'=\alpha\).

So these hypotheses imply a **unique LP minimiser**, not merely a feasible scaling.

For the second certificate integral, multiplication by the monomial phase corresponds to
\[
r\mapsto r+\kappa,\qquad \eta\mapsto\eta+1,
\]
leaving the residual exponents unchanged. This explains why no additional gap condition is needed, assuming the stated chart bounds handle the moving unit.

What is not yet supplied by this theorem is necessity.

### 5. `not_profileIntegrableOf_of_three_scaled`

`hne` is the right hypothesis for this obstruction.

In the stated finite-dimensional setting, the domain is an intersection of positive open boxes/orthants with either no extra condition or a strict inequality involving continuous monomials. Hence it is open. Nonempty therefore implies positive Lebesgue measure. Without `hne`, the zero function on an empty limiting domain would indeed be integrable.

The rank–nullity argument also has the right scope. With at least three unbounded logarithmic coordinates, there is a nonzero direction preserving both
\[
\kappa\cdot\log u,\qquad Q\cdot\log u.
\]
Along its full real orbit, the remaining power/Jacobian factor is exponential in one real parameter. Its integral over the whole line diverges, including when the exponent is zero.

Three interpretation cautions:

- `α l ≠ 0` agrees with “scaled coordinate” by the definition of `limitDomain`. Its interpretation as a coordinate shrinking towards zero additionally uses feasibility/nonnegativity of \(\alpha\).
- Failure of the **envelope certificate** does not imply divergence of an actual observable-weighted integral. A weight can vanish in the troublesome directions.
- It does not rule out a logarithmically renormalised asymptotic. Positive-dimensional optimal faces are exactly where that possibility should be expected.

I would replace “the isolated-optimum count is closed” by:

> The certificate obstruction excludes three or more scaled coordinates; the nondegenerate one- and two-coordinate cases now have explicit certificates.

A complete count/classification still needs the converses and the degenerate two-constraint cases.

### 6. `normalise_restrict_limitMeasure_eq_of_forall_tendsto`

The conclusion is appropriately local and normalised.

The positivity assumptions on the reference integrals prevent the important vacuities: zero limit measure, reference invisible to the limit measure, and a candidate exponent selecting no nonzero coefficient. In particular, although `hmin` alone permits a lower bound below every actual exponent, `hpos` should exclude that possibility for the selected coefficient measure.

`IsOpen L'` is doing genuine work. For continuous functions whose nonzero set lies in \(L'\), points outside the interior cannot be detected. Indeed, any point where such a function is nonzero has an open neighbourhood contained in \(L'\).

Without openness, the natural conclusion from this observable class is about
\[
\mu|_{\operatorname{int}L'},
\]
not automatically \(\mu|_{L'}\). A boundary-nullness hypothesis could bridge that gap.

Thus:

- Openness is not merely an inconvenience of the cutoff proof.
- It is not logically necessary for every particular pair of measures.
- It is an appropriate clean sufficient condition for the advertised conclusion.

I would **not** make it a field of the core atlas record merely to support this theorem. Prefer an optional open-region wrapper or a theorem-level hypothesis unless all intended atlases are open by construction.

Finally, the conclusion identifies neither absolute mass nor asymptotic rate. Equal limiting expectations can coexist with different \(\lambda\), different logarithmic orders, and different overall amplitudes. This limitation belongs prominently in the note’s thesis.

---

## B. Ranked next targets

### 1. Package partially tied coefficients as measures

This is the best next target: relatively low analytic risk and the most direct connection to what expectations actually know.

For a partial chart, define
\[
g(z)=D.\mathrm{rep}_i\bigl(D.\mathrm{bridgePt}_i(\mathrm{partialFace}(e,z),0)\bigr),
\]
and, writing the frozen weight and unit as \(w_F(z)\) and \(a_F(z)\), define
\[
d\nu(z)=
w_F(z)\,[B a_F(z)]^{-\lambda}
\prod_Nz_j^{r_j-\lambda\kappa_j}\,
1_{(0,\rho)^N}(z)\,dz.
\]
Then set
\[
\mu_i=C_i\,g_*\nu,\qquad
C_i=A_i\frac{\delta_i^k\Gamma(\lambda)}{k!}
\prod_T\kappa_j^{-1}.
\]

**Precise target:**

1. \(\mu_i\) is a finite positive Borel measure.
2. For every allowed bounded continuous nonnegative \(\varphi\),
   \[
   \frac{t^{\gamma p_i+\delta_i\lambda}}{(\log t)^k}
   K_{i,\varphi}(t)\longrightarrow\int\varphi\,d\mu_i.
   \]
3. For a finite collection of measure-valued term certificates, let
   \[
   \lambda_*=\min_i\lambda_i,\qquad
   k_*=\max\{k_i:\lambda_i=\lambda_*\},
   \]
   and
   \[
   \mu_*=\sum_{(\lambda_i,k_i)=(\lambda_*,k_*)}\mu_i.
   \]
   If \(\int\chi\,d\mu_*>0\), prove
   \[
   \langle\psi\rangle_\chi(t)\longrightarrow
   \frac{\int\psi\,d\mu_*}{\int\chi\,d\mu_*}.
   \]

Then lift the distinguishability theorem from isolated-profile measures to these lexicographic coefficient measures.

**Why it matters:** It turns the partial-face formula into the actual object identified by expectation limits and unifies logarithmic and nonlogarithmic cases.

**Main risk:** Boundary observability. Convergence against continuous functions vanishing outside \(L'\) is not automatically ordinary weak convergence of restricted measures: mass may approach \(\partial L'\). State the observable-class convergence first; add tightness/boundary control only if claiming more.

---

### 2. Prove a canonical mixed-truth logarithmic endpoint

I would start with a sharply specified `xy = s` theorem rather than a general mixed-truth framework.

Let \(\rho>0\), \(\sigma>0\), and \(f\) be continuous on \([0,\rho]^2\). Define, eventually in \(t\),
\[
J_f(t,\sigma)
=\int_{\sigma/(\rho t)}^\rho
 f\!\left(x,\frac{\sigma}{tx}\right)\frac{dx}{x}.
\]

**Core target:**
\[
\frac{J_f(t,\sigma)}{\log t}\longrightarrow f(0,0).
\]

For positive continuous \(a\), continuous \(w\ge0\), and continuous \(\psi\), take
\[
f_\sigma(x,y)=e^{-\sigma a(x,y)}w(x,y)\psi(x,y).
\]
This gives the fibre asymptotic for \(F(x,y)=xy\,a(x,y)\):
\[
\frac1{\log t}
\int_{\sigma/(\rho t)}^\rho
e^{-tF(x,\sigma/(tx))}
w(x,\sigma/(tx))\psi(x,\sigma/(tx))\,\frac{dx}{x}
\longrightarrow
e^{-\sigma a(0,0)}w(0,0)\psi(0,0).
\]
If \(w(0,0)\chi(0,0)>0\), the associated ratio tends to
\[
\frac{\psi(0,0)}{\chi(0,0)}.
\]

The useful substitution is
\[
L=\log(\rho^2t/\sigma),\qquad
x=\rho e^{-Lu},\quad y=\rho e^{-L(1-u)}.
\]
It transforms the integral into
\[
L\int_0^1 f(\rho e^{-Lu},\rho e^{-L(1-u)})\,du.
\]
For \(0<u<1\), both coordinates tend to zero. The exceptional endpoint layers have negligible logarithmic mass.

**Why it matters:** It demonstrates that failure of bridge continuity does not imply failure of a limiting measure. Concentration can arise after logarithmic averaging, rather than pointwise extension of the bridge.

**Main risk:** Translating the elementary \(dx/x\) theorem into the existing `totalKernel` convention, including Jacobians, branches and atlas weights. Keep the core lemma separate so that these bookkeeping issues do not obscure the analytic mechanism.

---

### 3. Prove a nondegenerate certificate–LP equivalence

Do this in an abstract constant-unit model first. Avoid promising a blanket equivalence before treating degenerate active constraints.

Let
\[
\mathcal P=\{\beta\ge0:\kappa\cdot\beta\ge\delta,\ Q\cdot\beta\le\gamma\},
\qquad a_j=r_j+1,
\]
with \(\kappa_j>0\), \(Q_j\ge0\), and positive analytic constants. Fix \(\alpha\in\mathcal P\) satisfying \(\kappa\cdot\alpha=\delta\).

Restrict initially to either:

- **Strict truth:** \(\operatorname{supp}\alpha=\{s\}\) and \(Q\cdot\alpha<\gamma\).
- **Nondegenerate tied truth:** \(\operatorname{supp}\alpha=\{s_0,s_1\}\), \(Q\cdot\alpha=\gamma\), and \(\Delta\ne0\).

Let \(\Omega_\alpha\) be the stated limiting domain and
\[
\Phi(u)=\prod_j u_j^{\kappa_j},\qquad
H(u)=1_{\Omega_\alpha}(u)\prod_j u_j^{r_j}e^{-c\Phi(u)}.
\]

**Precise target:**
\[
\bigl(H\in L^1\ \text{and}\ H\Phi\in L^1\bigr)
\quad\Longleftrightarrow\quad
\alpha\text{ uniquely minimises }a\cdot\beta\text{ on }\mathcal P.
\]

Also expose the explicit intermediate equivalences:

- Strict truth:
  \[
  \eta=\frac{a_s}{\kappa_s}>0,\qquad
  a_j-\eta\kappa_j>0\quad(j\ne s).
  \]
- Tied truth:
  \[
  a_S=\eta\kappa_S-\theta Q_S,\quad
  \eta,\theta>0,\quad
  a_j-\eta\kappa_j+\theta Q_j>0\quad(j\notin S).
  \]

Then transfer to chart certificates using the positive bounded-unit comparisons.

**Why it matters:** It establishes exactly when the power-only profile method is complete and turns the certificate API into a geometric classification rather than a collection of sufficient tests.

**Main risk:** Necessity and degeneracy. A tied one-coordinate vertex, dependent active constraints, and zero reduced costs must not be silently folded into the nondegenerate theorem. Distinguish a vertex from a unique minimiser; every point of an optimal edge can be optimal, including its vertices.

---

### 4. Local uniformity in \(\sigma\), away from transition loci

Start with a compact interval \(K\subset(0,\infty)\), or one contained in the negative half-line with fixed branch data. Keep \(\gamma\), the active face, and the lexicographic dominant type fixed.

For a partial-face or isolated-profile coefficient \(C_\psi(\sigma)\), target
\[
\sup_{\sigma\in K}
\left|
\frac{t^\lambda}{(\log t)^k}K_\psi(t,\sigma)
-C_\psi(\sigma)
\right|\longrightarrow0.
\]
Assuming
\[
\inf_{\sigma\in K}C_\chi(\sigma)>0,
\]
deduce
\[
\sup_{\sigma\in K}
\left|
\langle\psi\rangle_{\chi,\sigma}(t)
-\frac{C_\psi(\sigma)}{C_\chi(\sigma)}
\right|\longrightarrow0.
\]

Use explicit hypotheses ensuring:

- fixed admissibility/branch type on \(K\);
- uniform positive unit bounds;
- joint continuity in \(\sigma\) at the relevant faces;
- a common integrable majorant;
- fixed strict residual gaps.

A useful immediate corollary is the variable-parameter statement: if \(\sigma(t)\in K\) and \(\sigma(t)\to\sigma_0\), then the corresponding ratio converges to \(C_\psi(\sigma_0)/C_\chi(\sigma_0)\).

**Why it matters:** This is the justified route from fixed-truth asymptotics to variable-truth families.

**Main risk:** Confusing local uniformity with uniformity through a transition. Allowing \(\sigma\to0\), changing active LP faces, or losing a residual gap can change the logarithmic order or require a new scaling regime. Those should be separate theorems.

---

## What I would defer

- **Empirical versions:** First specify how samples are drawn on, or near, shrinking fibres. An empirical estimator of the limiting measure is much easier than an empirical version of the original fibre expectation; the latter introduces bandwidth, rarity and denominator-stability issues.
- **Making \(L'\) open in the core record:** This is API policy, not a research milestone. Preserve the more general record unless openness is intrinsic to every intended construction.
- **An unrestricted “certificate iff isolated optimum”:** Worth pursuing after target 3, but only with explicit treatment of degenerate vertices and the distinction between envelope integrability and observable-specific cancellations.

The immediate sequence I would choose is therefore: **measure-valued partial faces → canonical mixed-truth endpoint → nondegenerate iff classification → compact-parameter uniformity.**