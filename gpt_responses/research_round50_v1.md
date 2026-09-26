## First: an essential consistency check

Several formulas in the summary conflate **mean velocity** with **natural-parameter velocity**. These must be separated before adding more geometry.

Write
\[
Q_M=\Pi(M),\qquad q(M)=-\theta(M),\qquad
\Sigma_M=\operatorname{Cov}_{Q_M}(S,S),
\]
with \(\Sigma_M\) restricted to \(\mathbb V\). For a mean-space velocity \(u\), define
\[
w_M(u)=\Sigma_M^{-1}u,\qquad
\ell_{M,u}(x)=\langle w_M(u),S(x)-M\rangle .
\]
Then
\[
D_Mq[u]=\Sigma_M^{-1}u,\qquad D_\theta m=-\Sigma,
\]
and the Fisher metric in mean coordinates is
\[
g_M(u,z)=\langle u,\Sigma_M^{-1}z\rangle
        =E_{Q_M}[\ell_{M,u}\ell_{M,z}].
\]

Consequently, along \(M_s=m_0+sv\),
\[
\boxed{\kappa(s)=g_{M_s}(v,v)
=\operatorname{Var}_{Q_s}\langle\Sigma_{M_s}^{-1}v,S\rangle,}
\]
not generally \(\operatorname{Var}_{Q_s}\langle v,S\rangle\). Likewise,
\[
F_\varphi'(s)=\operatorname{Cov}_{Q_s}
  \bigl(\varphi,\langle\Sigma_{M_s}^{-1}v,S\rangle\bigr).
\]

The stated integral formulas are correct with this corrected \(\kappa\). The variational Fisher identity in your summary already points to this correction: \(-\theta_s'=\Sigma_{M_s}^{-1}v\).

Also, with \(P_\theta\propto e^{-\langle\theta,S\rangle}\), it is \(q=-\theta\) that approaches the usual **outward** normal cone. These may merely be notation slips in the summary, but they are foundational.

---

# 1. The deepest formulation: a response atlas with an exact information remainder

The most compelling endpoint is not just a collection of curves. It is:

> **A finite-dimensional statistical retraction, equipped with its exact nonlinear information defect and its infinitesimal orthogonal decomposition.**

There are three layers.

1. **Response coordinates:** \(D\mapsto M_D\).
2. **Canonical reconstruction:** \(M\mapsto Q_M\).
3. **Information not reconstructed:** fibre information plus non-exponential statistic information.

The canonical map
\[
\mathcal R(D)=Q_{M_D}
\]
is a retraction onto the exponential family on the interior. It preserves all selected expectations, but generally not other expectations.

The decisive pair of identities should be:

### Nonlinear information decomposition
\[
\boxed{
\mathrm{KL}(D\|\nu)
=
\mathcal I(M_D)
+\underbrace{\mathrm{KL}(D\|D^\uparrow)}_{L(D)}
+\underbrace{\mathrm{KL}(S_*D\|S_*Q_{M_D})}_{R(D)}.
}
\tag{N}
\]

### Infinitesimal Fisher decomposition
At a reconstructed law \(Q=Q_M\), let \(h\in L^2_0(Q)\) be a density score. Let
\[
C_Mh=E_Q[h\mid \sigma(S)]
\]
and let \(B_M\) be orthogonal projection onto
\[
\mathcal T_M
=\{\langle b,S-M\rangle:b\in\mathbb V\}.
\]
Then
\[
\boxed{
\|h\|_2^2
=
\|B_Mh\|_2^2
+\|(C_M-B_M)h\|_2^2
+\|(I-C_M)h\|_2^2.
}
\tag{T}
\]

The three terms in (T) are precisely the quadratic versions of the three terms in (N). That is the central unification worth pursuing.

## The three paths: right idea, but not literally a triangle

For an interior endpoint \(M_D\), consider
\[
D_s=(1-s)\nu+sD,\qquad
Q_s=\Pi(m_0+sv),\qquad
E_s=P_{s\theta_D}.
\]

Their roles differ:

- \(D_s\): straight line in the full space of laws;
- \(Q_s\): straight line in **mean coordinates**, lifted through the atlas;
- \(E_s\): straight line in **natural coordinates**.

But \(D_s\) ends at \(D\), whereas the other two end at \(Q_D\). The better picture is a commuting projection diagram:
\[
\begin{array}{ccc}
\nu & \xrightarrow{\ D_s\ } & D\\
\downarrow\mathcal R && \downarrow\mathcal R\\
\nu & \xrightarrow{\ Q_s\ } & Q_D,
\end{array}
\]
together with a second lower route \(E_s\).

An illuminating auxiliary fact is
\[
\mathcal R\bigl((1-s)\nu+sD\bigr)
=
\mathcal R\bigl((1-s)\nu+sD^\uparrow\bigr)
=
\mathcal R\bigl((1-s)\nu+sQ_D\bigr).
\]
The projection forgets everything except the endpoint mean.

## The main pathwise Pythagorean theorem

Assume \(\mathrm{KL}(D\|\nu)<\infty\). Put
\[
L_s=\mathrm{KL}(D_s\|D_s^\uparrow),\qquad
R_s=\mathrm{KL}(S_*D_s\|S_*Q_s).
\]

For any interior target \(N\),
\[
\boxed{
\mathrm{KL}(D_s\|Q_N)
=L_s+R_s+\mathrm{KL}(Q_s\|Q_N).
}
\tag{P}
\]

In particular,
\[
\mathrm{KL}(D_s\|Q_s)=L_s+R_s,
\]
and
\[
\boxed{
\mathrm{KL}(D_s\|\nu)
=L_s+R_s+\int_0^s(s-u)\kappa(u)\,du.
}
\tag{P\(_0\)}
\]

Thus **fibre information alone is not the projection defect**. The defect is \(L_s+R_s\). Fibre information is the defect of retaining the entire statistic law; \(R_s\) is the further defect of retaining only its mean.

## The exact geometry between atlas points

For interior \(A,B\),
\[
\mathrm{KL}(Q_A\|Q_B)
=
\mathcal I(A)-\mathcal I(B)
-\langle q(B),A-B\rangle.
\tag{B}
\]
Hence the three-point identity is
\[
\boxed{
\begin{aligned}
\mathrm{KL}(Q_A\|Q_C)
={}&\mathrm{KL}(Q_A\|Q_B)
+\mathrm{KL}(Q_B\|Q_C)\\
&+\langle A-B,q(B)-q(C)\rangle .
\end{aligned}}
\tag{3P}
\]

This is the useful “area term”: a mixed mean/natural-coordinate pairing. It is preferable to introducing an unspecified curvature correction.

Indeed,
\[
d\mathcal I=\langle q,dM\rangle.
\]
Consequently, the integral of this one-form between two atlas points is path-independent. There is **no nonzero loop-area correction** for this exact differential. Dual affine flatness and Levi-Civita curvature should not be conflated.

---

# 2. The missing response theory

## 2a. Exact actual-versus-projected observable gap

For bounded measurable \(\varphi\), choose
\[
\psi=E_\nu[\varphi\mid\sigma(S)].
\]
Every reconstructed law has a \(\sigma(S)\)-measurable density relative to \(\nu\), so
\[
E_{Q_s}\varphi=E_{Q_s}\psi.
\]

Define
\[
\Delta_\varphi(s)=E_{D_s}\varphi-E_{Q_s}\varphi.
\]
Then the exact decomposition is
\[
\boxed{
\Delta_\varphi(s)
=
\underbrace{s\,E_D(\varphi-\psi)}_{\text{fibre response defect}}
+
\underbrace{E_{D_s}\psi-E_{Q_s}\psi}_{\text{statistic-law response defect}}.
}
\tag{G}
\]

This is the observable analogue of (N), but it is a **signed additive decomposition**, not a positive information decomposition.

For interior \(M_s\),
\[
\boxed{
\Delta_\varphi'(s)
=
E_D\varphi-E_\nu\varphi
-\operatorname{Cov}_{Q_s}(\varphi,S)\Sigma_{M_s}^{-1}v.
}
\tag{G'}
\]

In particular, the initial susceptibility defect is
\[
\Delta_\varphi'(0)
=
E_D\varphi-E_\nu\varphi
-\operatorname{Cov}_{\nu}(\varphi,S)\Sigma_0^{-1}v.
\]

If \(f=dD/d\nu\in L^2(\nu)\), set \(h=f-1\). Then
\[
\boxed{
\Delta_\varphi'(0)
=\langle h,(I-B_0)(\varphi-E_\nu\varphi)\rangle_{L^2(\nu)}.
}
\]
This says exactly which component of the actual change is invisible to first-order mean reconstruction.

At \(s=1\), the same derivative formula holds if \(M_D\in\operatorname{relint}K\). At a boundary endpoint, a finite derivative must not be asserted without additional hypotheses.

There are also useful quantitative versions. If
\(\operatorname{osc}(\varphi)\le b-a\), Pinsker gives
\[
|\Delta_\varphi(s)|
\le (b-a)\sqrt{\frac{L_s+R_s}{2}},
\]
and separately
\[
|\Delta_\varphi(s)|
\le (b-a)\sqrt{\frac{L_s}{2}}
+\operatorname{osc}(\psi)\sqrt{\frac{R_s}{2}}.
\]
These turn information residuals into simultaneous response-error certificates.

## 2b. A response Jacobian for all observables

The natural object is the **measure-valued derivative**
\[
\boxed{
D_MQ_M[u]=\ell_{M,u}\,Q_M.
}
\tag{J}
\]
Pairing it with any bounded \(\varphi\) gives
\[
D_M E_{Q_M}\varphi[u]
=E_{Q_M}[\varphi\ell_{M,u}]
=\operatorname{Cov}_{Q_M}(\varphi,S)\Sigma_M^{-1}u.
\]

The derivative measure has mass zero, and
\[
\|D_MQ_M[u]\|_{\mathrm{TV\ norm}}
=E_{Q_M}|\ell_{M,u}|
\le \sqrt{g_M(u,u)}.
\]
Here “TV norm” means total variation mass, without the probability-distance factor \(1/2\).

This is stronger and cleaner than separately proving the derivative for each observable.

### The complete mixed Hessian

Let
\[
a_\varphi=\Sigma_M^{-1}\operatorname{Cov}_{Q_M}(S,\varphi),
\]
and define the centered regression residual
\[
r_{\varphi,M}
=\varphi-E_{Q_M}\varphi-\langle a_\varphi,S-M\rangle.
\]
Then
\[
\boxed{
D_M^2 E_{Q_M}\varphi[u,z]
=
E_{Q_M}[r_{\varphi,M}\ell_{M,u}\ell_{M,z}].
}
\tag{H}
\]

This is the coordinate-free frozen-residual theorem. It immediately shows:

- symmetry of the response Hessian;
- affine observables in \(S\) have zero response Hessian;
- all nonlinear response comes from the component outside the linear sufficient-statistic span.

For the bridge,
\[
\Delta_\varphi''(s)
=-E_{Q_s}[r_{\varphi,M_s}\ell_{M_s,v}^2].
\]

### The transport equation is not a heat equation

Along an arbitrary \(C^1\) mean path,
\[
\boxed{
\partial_sQ_s
=
\langle\Sigma_{M_s}^{-1}\dot M_s,S-M_s\rangle\,Q_s.
}
\tag{Transport}
\]
This is a multiplicative **score/replicator equation**. It has no spatial diffusion operator and is not, without extra structure, a Fokker–Planck equation.

For a data-law perturbation with signed derivative \(\dot D\),
\[
\dot M=\int S\,d\dot D,
\]
and therefore
\[
\frac d{ds}E_{\mathcal R(D_s)}\varphi
=
\operatorname{Cov}_{Q_s}(\varphi,S)
\Sigma_{M_s}^{-1}\int S\,d\dot D_s.
\]
That is the actual “response to change in data” chain rule.

At \(D=Q_M\), its score-level derivative is exactly \(B_M\), an orthogonal projection. Away from the reconstructed family, it is not an orthogonal projection in \(L^2(D)\).

## 2c. What the endpoint distances mean

The exact endpoint identity is
\[
\boxed{
\mathrm{KL}(D\|\nu)
=
\int_0^1(1-s)\,
\langle v,\Sigma_{M_s}^{-1}v\rangle\,ds
+L_1+R_1.
}
\tag{Distance}
\]

For a finite-rate boundary endpoint, the integral is improper. This extension is important: it completes the featureless-to-data story without pretending that the natural parameter stays finite.

Interpretation:

- \(\mathcal I(M_D)\): minimum information needed to produce the observed mean response;
- \(L_1\): changes inside statistic fibres;
- \(R_1\): changes in the statistic distribution not determined by its mean.

Also, \(\nu\) is automatically the unique maximizer of **relative entropy**
\[
-\mathrm{KL}(\rho\|\nu).
\]
It is not automatically a maximizer of absolute Shannon or differential entropy. “Maximal entropy” needs a specified reference measure and admissible class.

## 2d. Fisher energy: a particularly beautiful exact identity

For an interior endpoint, the affine-parameterized mean and natural paths have the **same Fisher energy**:
\[
\boxed{
\begin{aligned}
\int_0^1 g_{M_s}(v,v)\,ds
&=
\int_0^1
\operatorname{Var}_{E_s}\langle\theta_D,S\rangle\,ds\\
&=
\mathrm{KL}(Q_D\|\nu)+\mathrm{KL}(\nu\|Q_D)\\
&=\langle q_D,M_D-m_0\rangle.
\end{aligned}}
\tag{Energy}
\]

For the mean path, more precisely,
\[
\mathrm{KL}(Q_D\|\nu)=\int_0^1(1-s)\kappa(s)\,ds,
\]
\[
\mathrm{KL}(\nu\|Q_D)=\int_0^1s\kappa(s)\,ds.
\]

Thus the two orientations of KL are the two complementary time-weightings of the same Fisher energy density.

But:
\[
\text{length}=\int_0^1\sqrt{\kappa(s)}\,ds,
\qquad
\text{energy}=\int_0^1\kappa(s)\,ds.
\]
They are not the same. Neither the mean geodesic nor the exponential geodesic is generally a Levi-Civita/Fisher length minimizer.

The correct minimality is **infinitesimal**:
\[
\boxed{
g_M(u,u)
=
\min_{\substack{h\in L^2_0(Q_M)\\
E_{Q_M}[h(S-M)]=u}}
E_{Q_M}[h^2],
}
\tag{Min}
\]
uniquely attained by \(h=\ell_{M,u}\).

This is the rigorous “least-information motion realizing a prescribed response velocity.”

---

# 3. Eight concrete theorem packages, ranked

The line estimates below concern theorem packages using the stated infrastructure, not every supporting definition from scratch. In particular, Banach-valued differentiation and entropy Taylor estimates need careful scope control.

## 1. Nested Fisher projections and minimum-energy response lift

**Statement.** For \(Q=Q_M\), \(M\in\operatorname{relint}K\), and \(h\in L^2_0(Q)\),
\[
B_Mh
=
\left\langle
\Sigma_M^{-1}E_Q[(S-M)h],S-M
\right\rangle,
\]
\[
C_MB_M=B_M,\qquad B_MC_M=B_M,
\]
and (T) holds. For any feasible score in (Min),
\[
\|h\|_2^2=g_M(u,u)+\|h-\ell_{M,u}\|_2^2.
\]

**Proof.** Identify the finite-dimensional centered-statistic subspace as a closed subspace of the \(\sigma(S)\)-measurable \(L^2\) subspace. Use nested orthogonal projections. The covariance formula follows from the normal equations.

**Use.** `MeasureTheory.Lp`, `orthogonalProjection`, `condExpL2`, covariance invertibility on \(\mathbb V\).

**Pitfalls.**

- Use centered statistics, or include constants explicitly.
- Invert only on \(\mathbb V\), not all of \(\mathbb R^J\).
- Conditional expectation versions are \(L^2\) equivalence classes.

**Scope:** roughly 250–400 lines.  
**Why first:** it explains both the Jacobian and all three information channels.

---

## 2. Pathwise Pythagoras against an arbitrary reconstructed target

**Statement.** For finite \(\mathrm{KL}(D\|\nu)\), \(s\in[0,1]\), and interior \(N\),
\[
\mathrm{KL}(D_s\|Q_N)
=
L_s+R_s+\mathrm{KL}(Q_s\|Q_N).
\]

**Proof.** The logarithmic density ratio \(dQ_N/d\nu\) is affine in \(S\). Its expectation under \(D_s\) therefore equals its expectation under \(Q_s\). Combine the two relative-entropy identities and the existing three-way split.

**Use.** Existing Pythagorean theorem, statistic lift, bridge means, tilted log-density formula, `InformationTheory.klDiv`.

**Pitfalls.**

- Keep the theorem additive in `ℝ≥0∞`; do not casually subtract infinities.
- An interior target guarantees equivalence with \(\nu\).
- A boundary target can make the left side infinite even when the source mean is interior.

**Scope:** 150–250 lines.  
**Why second:** this is the nonlinear projection diagram in one theorem.

---

## 3. Exact observable defect and endpoint susceptibilities

**Statement.** For bounded measurable \(\varphi\), prove (G), and on the interior prove (G′), including its \(s=0\) specialization. If \(M_D\) is interior, include \(s=1\).

**Proof.**

1. Conditional expectation is preserved when integrating against a \(\sigma(S)\)-measurable density.
2. The fibre part is linear along the bridge.
3. Differentiate the remaining projected expectation using `obsMapDeriv`.

**Use.** `condExp`, tower law, lift-density identity, bridge linearity, `obsMapDeriv`.

**Pitfalls.**

- One does not need a measurable function on the statistic codomain: a \(\sigma(S)\)-measurable function on \(X\) suffices.
- Endpoints require one-sided derivatives unless the path is locally extended.
- Boundary \(s=1\) is excluded from the derivative assertion.

**Scope:** 180–300 lines.  
**Why third:** this directly answers the user’s question about actual expectation changes.

---

## 4. Quadratic information splitting along bounded tilts

**Statement.** Let \(h\) be bounded, measurable, and \(E_\nu h=0\), and set
\[
D_t=\frac{e^{th}}{E_\nu e^{th}}\nu.
\]
With \(B=B_0\), \(C=C_0\), as \(t\to0\),
\[
\mathrm{KL}(D_t\|\nu)
=\frac{t^2}{2}\|h\|_2^2+o(t^2),
\]
\[
\mathcal I(M_{D_t})
=\frac{t^2}{2}\|Bh\|_2^2+o(t^2),
\]
\[
L(D_t)
=\frac{t^2}{2}\|(I-C)h\|_2^2+o(t^2),
\]
\[
R(D_t)
=\frac{t^2}{2}\|(C-B)h\|_2^2+o(t^2).
\]

**Proof.**

- Expand the density uniformly:
  \(dD_t/d\nu=1+th+O(t^2)\).
- Its conditional density is \(1+tCh+O(t^2)\).
- Apply the entropy expansion at density \(1\).
- Use \(D^2\mathcal I(m_0)=\Sigma_0^{-1}\).
- Recover \(L\) and \(R\) from the exact additive identities.

**Use.** Bounded tilt differentiation, `condExp` linearity/contraction, entropy splitting, rate derivative, theorem 1.

**Pitfalls.**

- Work with finite real entropy functions locally; convert to `klDiv` afterwards.
- A generic entropy-Taylor lemma is the main work.
- Bounded \(h\) supplies uniform positivity and domination.

**Scope:** 300–400 lines if the entropy-Taylor helper is included efficiently; otherwise split into two packages.  
**Why fourth:** it makes the nonlinear and Hilbert-space stories demonstrably the same geometry.

---

## 5. Equal Fisher energies of the mean and exponential paths

**Statement.** Prove (Energy), together with the two weighted KL identities.

**Proof.** Along the mean path,
\[
\frac d{ds}\langle q(M_s),v\rangle=\kappa(s).
\]
Along the exponential path, using natural parameter \(sq_D\),
\[
\frac d{ds}\langle q_D,m(-sq_D)\rangle
=\operatorname{Var}_{E_s}\langle q_D,S\rangle.
\]
Apply the fundamental theorem of calculus. Identify the endpoint pairing with symmetrized KL using (B).

**Use.** Mean-map derivative, inverse-chart derivative, Legendre identity, existing integral remainder theorem.

**Pitfalls.**

- The parameterization is part of the statement.
- These are energies, not lengths.
- Do not claim global minimizing geodesics.

**Scope:** 150–250 lines.  
**Why fifth:** a strong, surprising identity at low incremental cost.

---

## 6. Mixed response Hessian via the frozen residual

**Statement.** For bounded measurable \(\varphi\) and \(u,z\in\mathbb V\), prove (H).

**Proof.** Differentiate the first-response formula. Differentiating the inverse covariance introduces the cubic covariance correction. It cancels exactly the fitted linear component of \(\varphi\).

Alternatively, if the directional second-derivative theorem is already genuinely established for every direction, obtain the mixed bilinear formula by polarization after securing \(C^2\) regularity.

**Use.** `obsMapDeriv`, differentiated bounded expectations, covariance derivative, inverse-operator derivative, existing frozen-residual result.

**Pitfalls.**

- Center the regression residual.
- Use \(\ell_{M,u}\), not \(\langle u,S\rangle\).
- Directional second derivatives alone do not automatically establish a Fréchet Hessian.

**Scope:** 200–350 lines.  
**Why sixth:** it completes the local second-order response atlas.

---

## 7. Finite-rate boundary completion of the curvature integral

**Statement.** If \(M_1\in K\) and \(\mathcal I(M_1)<\infty\), let
\(M_s=(1-s)m_0+sM_1\). Then
\[
\mathcal I(M_1)=\int_{[0,1)}(1-s)\kappa(s)\,ds,
\]
and for \(s<1\),
\[
\mathrm{KL}(Q_{M_1}\|Q_{M_s})
=\int_{[s,1)}(1-u)\kappa(u)\,du.
\]

**Proof.**

1. Radial points with \(s<1\) are interior.
2. Convexity and lower semicontinuity give
   \(\mathcal I(M_s)\to\mathcal I(M_1)\).
3. Pass to the endpoint in the interior remainder identity by monotone convergence.
4. Identify the endpoint Bregman expression using the bounded log density of \(Q_{M_s}\) relative to \(\nu\).

**Use.** `intrinsicInterior` segment facts, lower semicontinuity of the rate as a supremum, convexity, existing tail identity, monotone convergence.

**Pitfalls.**

- Use a nonnegative/improper integral formulation.
- No integrability of \(\kappa\) without its weight is required.
- Finite rate is essential for the finite endpoint conclusion.

**Scope:** 200–350 lines.  
**Why seventh:** it makes “all the way to the data distribution” mathematically honest.

---

## 8. An \(L^1(\nu)\)-valued first derivative of reconstruction

**Statement.** Write \(p_M=dQ_M/d\nu\). Locally on the relative interior,
\[
\boxed{
D_Mp_M[u]
=p_M\,\ell_{M,u}
\quad\text{in }L^1(\nu).
}
\]
Consequently, every bounded-observable response derivative follows by pairing with the same derivative density, uniformly over \(\|\varphi\|_\infty\le1\).

**Proof.** Differentiate normalized exponential densities in \(L^1\) with respect to the natural parameter, then compose with the inverse mean chart. Bounded statistics give a locally uniform exponential remainder bound.

**Use.** `Measure.tilted`, local bounds for exponentials, `MeasureTheory.Lp`, inverse-chart differentiability, composition rules.

**Pitfalls.**

- Prove an \(L^1\)-norm remainder estimate; pointwise differentiation is insufficient.
- Keep the chart on \(\mathbb V\).
- This is more substantial than merely repackaging scalar derivatives.

**Scope:** 250–400 lines with an explicit exponential remainder estimate.  
**Why eighth:** it is the best all-observables formulation, but should follow the scalar and Hilbert-space foundations.

---

# 4. What to do with the round-49 leftovers

## (2) Nested Fisher projections: **do now, first**

This is not an auxiliary embellishment. It gives:

- the tangent space of reconstructed laws;
- the differential of the projection;
- least-energy response realization;
- the three local information channels;
- the geometric meaning of the observable regression residual.

It is the missing conceptual spine.

## (3) Second-order fibre/marginal expansions: **do next**

Restrict initially to bounded exponential perturbations of \(\nu\), or of another interior reconstructed law. That avoids premature technical generality while proving the exact correspondence between nonlinear KL decomposition and orthogonal Fisher decomposition.

Do not begin with arbitrary \(L^2\) scores and positivity problems.

## (4) Conditional variational formula: **defer the generic version; retain the genuinely conditional refinement**

The displayed formula
\[
L=\sup_g\{E_Dg-\log E_{D^\uparrow}e^g\}
\]
is simply the usual KL variational formula applied to \((D,D^\uparrow)\). It is correct, but contributes relatively little new response geometry.

The more informative version is
\[
\boxed{
L
=
\sup_{g\ \mathrm{bounded}}
E_D\!\left[
g-\log E_\nu(e^g\mid\sigma(S))
\right].
}
\]
Equivalently,
\[
\boxed{
L
=
\sup_{\substack{g\ \mathrm{bounded}\\
E_\nu(e^g\mid\sigma(S))=1\;\nu\text{-a.e.}}}
E_Dg.
}
\]
These say that fibre information is detected by tests normalized **separately on each statistic fibre**.

Once a general bounded-test KL variational theorem exists, this refinement follows economically by conditional normalization and Jensen. Without that infrastructure, it should not displace the tangent and response work.

---

## Recommended next milestone

Build one coherent theorem chain:
\[
\boxed{
\text{nested Fisher projections}
\;\Longrightarrow\;
\text{response derivative and observable defect}
\;\Longrightarrow\;
\text{quadratic three-way KL split}.
}
\]

Then add the equal-energy identity and boundary curvature completion.

That produces a genuinely complete finite-statistic picture: **what changes in the responses, how the canonical posterior must move to realize that change, and exactly what information—and what observable behavior—the response atlas cannot see.**