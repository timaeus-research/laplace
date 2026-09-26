## Verdict

**Yes—with one essential qualification.** You now have a defensible response atlas from the reference law to the data **response**, together with an exact accounting of what the response does not determine about the data law.

The distinction should be explicit:
\[
D_s=(1-s)\nu+sD
\quad\longmapsto\quad
M_s=E_{D_s}S
\quad\longmapsto\quad
P_s=\Pi_\nu(M_s).
\]
In general, \(P_1\neq D\). Rather,
\[
KL(D\|\nu)=\mathcal I(M_D)+KL(D\|P_1).
\]
Thus the atlas reaches the canonical representative of the data’s response fiber; the residual measures the information discarded by passing to responses. This is a strength, not a deficiency.

Also, call \(\nu\) “featureless” or “maximum entropy” **relative to the chosen reference structure**. An arbitrary \(\nu\) need not maximize ordinary Shannon or differential entropy.

**No major existence theorem is now missing.** If I must select one remaining capstone, it is the **single integrated visible/invisible information theorem** in rank 1 below. Its ingredients have landed; what remains is to present them as the precise answer to “how much of the journey to the data law is captured by responses?”

---

## Conventions for the statements

I will use the sign convention suggested by your differential formulas:
\[
dP_\theta=Z(\theta)^{-1}e^{-\langle\theta,S\rangle}\,d\nu.
\]
Let
\[
\Omega=\{v\in\mathbb V:m_0+v\in\operatorname{relint}K\},
\qquad
C_\theta=-Dm(\theta)|_{\mathbb V}.
\]
Then \(C_\theta\) is the positive-definite covariance operator, and
\[
D\theta(v)=-C_{\theta(v)}^{-1},
\qquad
D^2\mathcal I(v)=C_{\theta(v)}^{-1}.
\]

The Lean-shaped statements below are theorem specifications, not claims about existing identifier names.

# Ranked next theorems

## 1. The complete information budget: visible curvature plus invisible remainder

### Statement

Assume \(D\) is a probability measure, \(D\ll\nu\), and
\[
KL(D\|\nu)<\infty.
\]
Under the existing bounded-statistic hypotheses, put
\[
f=\frac{dD}{d\nu},\quad
D_s=(1-s)\nu+sD,\quad
M_s=E_{D_s}S,\quad
P_s=\Pi_\nu(M_s).
\]

Define, for \(0<s<1\),
\[
\mathcal F_D(s)
=\int\frac{(f-1)^2}{1-s+sf}\,d\nu,
\qquad
\kappa(s)
=\operatorname{Var}_{P_s}\langle\theta_s',S\rangle.
\]

Prove together:
\[
\boxed{
\begin{aligned}
KL(D\|\nu)
  &=\int_0^1(1-s)\mathcal F_D(s)\,ds,\\
\mathcal I(M_D)
  &=\int_0^1(1-s)\kappa(s)\,ds,\\
KL(D\|\Pi_\nu(M_D))
  &=\int_0^1(1-s)\bigl[\mathcal F_D(s)-\kappa(s)\bigr]\,ds.
\end{aligned}}
\]

For the real-valued third identity, a useful formal interface is:
```lean
Integrable (fun s => (1 - s) * dataFisher s) (volume.restrict (Ioo 0 1))
Integrable (fun s => (1 - s) * kappa s) (volume.restrict (Ioo 0 1))
```
followed by the integral-of-difference theorem.

### Hidden hypotheses and corrections

- **Finite KL is the clean hypothesis for subtraction.** Do not write an unrestricted \(\mathbb R_{\ge0}^{\infty}\) subtraction identity.
- \(\mathcal F_D(0)\) can be infinite when \(f\notin L^2(\nu)\). Use `Ioo 0 1`, or assign harmless endpoint values before taking a real integral.
- Crucially, **do not claim**
  \[
  \mathcal F_D(s)-\kappa(s)\ge0
  \]
  pointwise. These Fisher quantities are evaluated at different laws, \(D_s\) and \(P_s\). There is no general pointwise contraction theorem here. “Integrated missing information” is safe; “nonnegative missing-Fisher density” is not.

### Local companion

For bounded \(h\), let
\[
dD_s=\frac{e^{sh}}{E_\nu e^{sh}}\,d\nu.
\]
Let \(g\) be the \(L^2(\nu)\)-orthogonal projection of \(h-E_\nu h\) onto the centered feature span:
\[
g=\langle a,S-m_0\rangle,\qquad
C_0a=E_\nu[(h-E_\nu h)(S-m_0)].
\]
Then
\[
\boxed{
KL(D_s\|\Pi_\nu(E_{D_s}S))
=\frac{s^2}{2}\operatorname{Var}_\nu(h-g)+o(s^2).
}
\]

A convenient Lean target is the punctured-limit form:
```lean
Tendsto
  (fun s => invisibleKL s / s ^ 2)
  (𝓝[≠] 0)
  (𝓝 ((1 / 2 : ℝ) * variance ν (h - g)))
```

### Proof route

- Promote the atlas’s truncated curvature budget to the full nonnegative integral using monotone convergence.
- Use finite data KL to obtain finiteness of both weighted budgets.
- Apply the landed information decomposition and `integral_sub`.
- For the local result, reuse the invisible-information second derivative and a second-order Taylor/Peano theorem.

**Why first:** this is the strongest single theorem answering the original request while respecting the difference between data and response.

---

## 2. Projection onto the response atlas, with reference-independent Pythagoras

### Main statement

For every finite-KL data law \(D\) and every finite family parameter \(\eta\),
\[
\boxed{
KL(D\|P_\eta)
=
KL(D\|\Pi_\nu(M_D))
+
KL(\Pi_\nu(M_D)\|P_\eta).
}
\]
This should include finite-rate boundary responses \(M_D\), not merely the relative interior.

A clean initial hypothesis set is:

- `IsProbabilityMeasure ν`, `IsProbabilityMeasure D`;
- bounded measurable sufficient statistic;
- \(D\ll\nu\);
- \(KL(D\|\nu)<\infty\);
- \(\eta\in\mathbb V\).

You can subsequently extend the theorem to infinite data KL when the projected response has finite rate, with explicit extended-real bookkeeping.

### Proof route

The bounded log-density ratio gives
\[
KL(R\|P_\eta)
=
KL(R\|\nu)+\langle\eta,E_RS\rangle+\log Z(\eta).
\]
Apply this to \(R=D\) and \(R=\Pi_\nu(M_D)\), use equal moments, and invoke the existing base-reference Pythagorean theorem.

This is inexpensive but conceptually important: **the projection is not merely the best approximation relative to \(\nu\); it is the information projection relative to every member of the family.**

### Geometric packaging

On parameter space and response space, respectively:
\[
g^e_\theta(a,b)=\langle a,C_\theta b\rangle,
\qquad
g^m_v(u,w)=\langle u,C_{\theta(v)}^{-1}w\rangle.
\]
Prove
\[
g^m_{m(\theta)-m_0}(Dm_\theta a,Dm_\theta b)
=g^e_\theta(a,b).
\]

For paths:
\[
E_{(1-t)D_0+tD_1}S=(1-t)M_0+tM_1,
\]
so projection of an ambient mixture produces the **intrinsic response \(m\)-geodesic**
\[
t\longmapsto\Pi_\nu((1-t)M_0+tM_1).
\]
And
\[
\Pi_\nu(E_{P_\theta}S)=P_\theta,
\]
so family \(e\)-geodesics are fixed pointwise by projection.

### Important terminology correction

These are geodesics of the **dual affine connections**, not generally geodesics of the Fisher metric’s Levi–Civita connection.

Also,
\[
\Pi_\nu((1-t)M_0+tM_1)
\neq
(1-t)\Pi_\nu(M_0)+t\Pi_\nu(M_1)
\]
in general. The projected curve is straight in response coordinates, not in ambient densities.

**Implementation recommendation:** package the two metrics, the pullback identity, and the two affine path classes first. A full connection/manifold abstraction is not necessary to state the mathematics beautifully.

---

## 3. Quantitative inverse stability on bounded parameter regions

This remains the highest-value analytic estimate.

### Statement

Assume, almost everywhere,
\[
\|S-m_0\|\le B,
\]
and choose \(\lambda_0>0\) such that
\[
\lambda_0\|u\|^2\le\langle u,C_0u\rangle
\qquad(u\in\mathbb V).
\]
For \(r\ge0\), set
\[
\kappa_r=e^{-2Br}\lambda_0.
\]

For \(\|\theta\|\le r\), prove:

1. Density comparison:
   \[
   e^{-2Br}\le\frac{dP_\theta}{d\nu}\le e^{2Br}
   \quad\text{a.e.}
   \]

2. Covariance coercivity:
   \[
   \langle u,C_\theta u\rangle\ge\kappa_r\|u\|^2.
   \]

3. Inverse differential bound:
   \[
   \|C_\theta^{-1}\|_{\mathrm{op}}\le\kappa_r^{-1}.
   \]

4. For \(\theta,\eta\in\overline B(0,r)\),
   \[
   -\langle m(\theta)-m(\eta),\theta-\eta\rangle
   \ge\kappa_r\|\theta-\eta\|^2,
   \]
   and consequently
   \[
   \boxed{
   \|\theta-\eta\|
   \le\kappa_r^{-1}\|m(\theta)-m(\eta)\|.
   }
   \]

The last statement is a `LipschitzOnWith` theorem for the inverse chart on the response image of the closed parameter ball.

### Proof route

- Obtain \(\lambda_0\) by compactness of the intrinsic unit sphere and positive definiteness. Handle \(\mathbb V=\{0\}\) separately, or formulate coercivity existentially.
- Normalize the exponential using the centered statistic.
- Use
  \[
  \operatorname{Var}_{P_\theta}(X)
  =E_{P_\theta}(X-E_{P_\theta}X)^2
  \ge e^{-2Br}E_\nu(X-E_{P_\theta}X)^2
  \ge e^{-2Br}\operatorname{Var}_\nu(X).
  \]
  This gives the desired exponent directly.
- Integrate the derivative along the parameter segment.

**Caution:** the image of a parameter ball need not be convex. Do not silently use response-segment convexity there.

---

## 4. Boundary compactification of the atlas: laws converge while parameters escape

### Robust theorem

Let
\[
M\in\operatorname{relbd}K,\qquad
M_s=(1-s)m_0+sM.
\]
Then
\[
\boxed{\|\theta(M_s)\|\longrightarrow\infty\quad(s\uparrow1).}
\]
For this parameter-escape statement, finite rate is not required.

If \(\mathcal I(M)<\infty\), combine it with your endpoint results to obtain
\[
P_{\theta(M_s)}\longrightarrow\Pi_\nu(M)
\]
in total variation, with the already established information-gap modulus.

A Lean-shaped escape statement is:
```lean
Tendsto
  (fun s => ‖theta (Mpath s)‖)
  (𝓝[<] 1)
  atTop
```

### Directional refinement

If
\[
s_n\uparrow1,\qquad
\frac{\theta(M_{s_n})}{\|\theta(M_{s_n})\|}\longrightarrow u,
\]
then
\[
\|u\|=1,\qquad
\langle u,x-M\rangle\ge0\quad(x\in K).
\]
Thus **\(-u\)** is an outward normal at \(M\), with your negative-exponential convention.

### What is not correct as originally phrased

“Divergence along the exposed-face normal” is too strong without additional assumptions.

- Normal cones can have multiple directions.
- Different normal scales can appear.
- A prescribed exposing normal need not be the asymptotic direction.
- Normalized parameters need not have a unique limit.

The unconditional statement is escape plus normal-cone containment of accumulation directions.

### Controlled exposed-face theorem

If
\[
F=\{x\in K:\langle a,x\rangle=b\}
\]
is an exposed maximizing face with \(\nu(S\in F)>0\), then, for fixed \(\eta\),
\[
P_{\eta-ta}
\longrightarrow
\frac{e^{-\langle\eta,S\rangle}\mathbf1_{\{S\in F\}}}
{\int_{\{S\in F\}}e^{-\langle\eta,S\rangle}\,d\nu}\,\nu
\quad(t\to\infty).
\]

This explicitly ties diverging tilts to conditioning. Identifying that limit with \(\Pi_\nu(M)\) requires its response to equal \(M\); face-interior chart hypotheses provide a natural sufficient condition.

### Proof route

- Parameter escape: a bounded subsequence would converge to a finite parameter whose response is on the boundary, contradicting chart surjectivity into the relative interior.
- Normal-cone refinement: use bounded-statistic exponential concentration along normalized parameter subsequences.
- Fixed-normal limit: dominated convergence after subtracting the exposing maximum.
- Reuse the conditioning and exposed-face certificates.

---

## 5. Boundary strict-convexity gap, as a Jensen–Shannon plus projection identity

### Statement

Assume
\[
\mathcal I(M_0)<\infty,\qquad\mathcal I(M_1)<\infty,
\qquad 0<t<1.
\]
Set
\[
P_i=\Pi_\nu(M_i),\quad
Q_t=(1-t)P_0+tP_1,\quad
M_t=(1-t)M_0+tM_1.
\]
Then
\[
\boxed{
\begin{aligned}
&(1-t)\mathcal I(M_0)+t\mathcal I(M_1)-\mathcal I(M_t)\\
&\quad=(1-t)KL(P_0\|Q_t)+tKL(P_1\|Q_t)
      +KL(Q_t\|\Pi_\nu(M_t)).
\end{aligned}}
\]
In particular, \(M_0\neq M_1\) implies a strictly positive gap.

### Proof route

First prove the general mixture-compensation identity:
\[
(1-t)KL(P_0\|\nu)+tKL(P_1\|\nu)
=
KL(Q_t\|\nu)
+(1-t)KL(P_0\|Q_t)+tKL(P_1\|Q_t).
\]
Then apply the existing projection decomposition to \(Q_t\).

Use finite-KL hypotheses initially. They avoid unnecessary \(\infty-\infty\) issues and cover the desired finite-rate boundary.

**Why worth doing:** it gives a global strict-convexity theorem across finite-rate boundary strata, beyond the scope of the interior Hessian theorem.

---

## 6. Smooth Hessian geometry and the derivative of Fisher

### Statement

Under bounded statistics and finite-dimensional intrinsic parameter space:
```lean
ContDiff ℝ ⊤ momentMap
ContDiffOn ℝ ⊤ theta Ω
ContDiffOn ℝ ⊤ rateInResponseCoordinates Ω
```
Together with smoothness of the covariance operator and the observable maps for bounded observables.

For \(a,b,w\in\mathbb V\), prove explicitly
\[
\boxed{
D_\theta C_\theta[w](a,b)
=
-E_{P_\theta}\!\left[
\langle a,S-m(\theta)\rangle
\langle b,S-m(\theta)\rangle
\langle w,S-m(\theta)\rangle
\right].
}
\]

### Sign warning

With \(e^{-\langle\theta,S\rangle}\), the derivative is **minus** the third central moment. Your proposed \(DC=T\) is correct only if `T` was defined with that sign, or in positive natural coordinates \(\alpha=-\theta\).

### Proof route

- Differentiate the partition function under the integral using boundedness.
- Establish smoothness of the covariance operator.
- Bootstrap the inverse chart using
  \[
  D\theta=-C_{\theta}^{-1},
  \]
  or invoke an appropriate smooth inverse-function theorem.
- Reuse the landed cubic tensor rather than reproving its component identities.

I would not delay ranks 1–5 for \(C^\infty\). The substantive atlas already exists at your current regularity.

---

## Entropy ordering: a corollary, not a separate project

Your atlas already gives
\[
\frac{d}{dr}\mathcal I(M_r)=\int_0^r\kappa(s)\,ds\ge0.
\]
Consequently,
\[
KL(P_r\|\nu)\ \text{is nondecreasing},
\qquad
H_\nu(P_r):=-KL(P_r\|\nu)\ \text{is nonincreasing}.
\]
For \(M\neq m_0\), positive definiteness gives strict increase away from the basepoint, and strict ordering along the nontrivial bridge.

But remove **“nested family of exponential tilts”** unless you define it narrowly. The parameters need not be collinear, and no fixed-statistic likelihood-ratio ordering or support nesting follows. Every interior representative has the same support up to null sets.

---

## How I would write “The response atlas”

Implementation priority and exposition order should differ slightly.

1. **The atlas and its fibers.**  
   Intrinsic chart, canonical representative, observable differential. Explain immediately why reaching the response is not the same as reproducing the data law.

2. **Dual geometry and projection.**  
   Fisher/co-Fisher metrics, affine \(e\)- and \(m\)-paths, generalized Pythagoras.

3. **The journey from reference to data.**  
   Straight response bridge and
   \[
   \mathcal I(M)=\int_0^1(1-s)\kappa(s)\,ds.
   \]

4. **The centrepiece: the complete information budget.**  
   Place the data Fisher budget beside the response curvature budget, then identify their difference with invisible information. Follow with the local regression-residual expansion.

5. **Stability and the boundary.**  
   Quantitative inverse stability in bounded parameter regions; parameter escape but law convergence at finite-rate boundary responses; conditioning on exposed faces.

6. **Global convexity and higher smoothness.**  
   Boundary gap identity, then cubic/Hessian geometry as refinements.

The section’s central claim should be:

> **The response atlas separates the information required to move the observed responses from the information remaining within their fibers, and gives an exact integrated curvature budget for both.**

That is stronger—and more accurate—than claiming that the exponential family itself reconstructs an arbitrary data law.