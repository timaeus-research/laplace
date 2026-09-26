The next step should be **global synthesis, not another isolated derivative identity**. You now have enough machinery to describe a response geometry, its observable differential, and the information accumulated along an entire journey.

I would rank the next six results as follows. Here \(i(M)\) denotes the **real value** of \(\mathcal I(M)\), used only where the rate is finite.

Throughout, assume the existing finite-dimensional, bounded-statistic hypotheses. Write
\[
\Omega=\{v\in\mathbb V:m_0+v\in\operatorname{relint}K\},
\qquad C_\theta=-D\,\mathrm{chartV}(\theta),
\]
where \(K\) is your moment body. Thus \(C_\theta\) is positive definite on \(\mathbb V\).

## 1. A global response atlas, including the information that the atlas does not see

This should be the flagship theorem.

### Statement

Let \(D\) be a probability law with
\[
\mathrm{KL}(D\|\nu)<\infty.
\]
Set
\[
M=E_D S,\quad \Delta=M-m_0,\quad
D_s=(1-s)\nu+sD,\quad M_s=m_0+s\Delta,\quad P_s=\Pi_\nu(M_s).
\]

Prove, in one structured package:

1. For \(0\le s<1\),
   \[
   M_s\in\operatorname{relint}K,
   \qquad
   \exists!\theta_s\in\mathbb V,\quad
   P_s=\nu_{-\langle\theta_s,S\rangle}.
   \]
   Moreover \(\theta_0=0\).

2. The parameter path is \(C^1\) on \([0,1)\), with
   \[
   \theta_s'=-C_{\theta_s}^{-1}\Delta.
   \]

3. The rate path is convex, nondecreasing, \(C^1\), and
   \[
   \frac{d}{ds}i(M_s)=-\langle\theta_s,\Delta\rangle.
   \]

4. At every \(s\in[0,1]\),
   \[
   \mathrm{KL}(D_s\|\nu)
   =
   \mathcal I(M_s)+\mathrm{KL}(D_s\|P_s).
   \]

5. At the endpoint,
   \[
   i(M_s)\longrightarrow i(M),
   \qquad
   \mathrm{KL}(P_1\|P_s)\longrightarrow0,
   \]
   with your quantitative certificate
   \[
   \mathrm{KL}(P_1\|P_s)\le i(M)-i(M_s).
   \]

A suitable Lean interface is a structure containing these conclusions, or an omnibus theorem plus smaller projection lemmas. For regularity, use the translated intrinsic coordinates:
```lean
ContDiffOn ℝ 1 thetaPath (Set.Ico (0 : ℝ) 1)
```
and derivative statements within that interval. Even cleaner: establish local extensions around each \(s<1\), including \(s=0\).

### Why this is first

This genuinely answers the standing direction, provided the theorem explicitly distinguishes:

- **the actual journey:** \(D_s\to D\);
- **the visible journey:** \(P_s\to\Pi_\nu(E_D S)\);
- **the invisible information:** \(\mathrm{KL}(D_s\|P_s)\).

The representative generally does **not** converge to \(D\). Omitting that distinction would make the atlas look more complete than it is.

### Proof route and names

Reuse your mixture bridge, intrinsic chart bijection, `responseProjection_eq_tilted`, envelope identity, and endpoint certificate.

Standard names I am confident exist:

- `ContDiffOn`, `HasDerivAt`, `HasDerivWithinAt`;
- `HasFDerivAt.comp`, `HasDerivAt.comp`;
- `ConvexOn`, `MonotoneOn`.

**One genuine remaining regularity step:** strict differentiability of the inverse at each point does not by itself supply the desired `ContDiffOn` statement. Prove continuity of \(\theta\mapsto C_\theta\), then continuity of its inverse, or invoke the appropriate \(C^1\) inverse-function API. Exact inverse-function theorem names: **unsure**.

---

## 2. The dual Fisher metric, with a quantitative inverse-stability theorem

Your candidate (b) is correct, inexpensive relative to what has landed, and foundational.

### Statement

For \(v\in\Omega\), put
\[
\theta(v)=\mathrm{chartVInv}(v),\qquad j(v)=i(m_0+v).
\]
Prove
\[
\nabla j(v)=-\theta(v),
\]
and
\[
D(\nabla j)(v)=C_{\theta(v)}^{-1}.
\]
Equivalently,
\[
D^2j(v)[u,w]
=
\langle u,C_{\theta(v)}^{-1}w\rangle.
\]

A particularly useful intermediate Lean theorem has the shape
```lean
HasFDerivAt
  (fun v : V => -chartVInv v)
  ((covEquiv (chartVInv v)).symm.toContinuousLinearMap)
  v
```
under `v ∈ Ω`, with `covEquiv` the continuous linear equivalence associated to \(C_\theta\).

Then prove the explicitly quantitative stability result you still lack.

Suppose
\[
\|S-m_0\|\le B\quad \nu\text{-a.e.},
\qquad
\langle u,C_0u\rangle\ge\lambda_0\|u\|^2,
\quad \lambda_0>0.
\]
For \(r\ge0\), define
\[
\boxed{\kappa_r=e^{-2Br}\lambda_0.}
\]
Then
\[
\|\theta\|\le r
\implies
\langle u,C_\theta u\rangle\ge\kappa_r\|u\|^2.
\]
Consequently, for \(\theta,\eta\) in that ball,
\[
\boxed{
\|\theta-\eta\|
\le
\kappa_r^{-1}\|m(\theta)-m(\eta)\|.
}
\]

No new nondegeneracy hypothesis is needed: in finite-dimensional \(\mathbb V\), positivity of \(C_0\) supplies some \(\lambda_0>0\). Handle \(\mathbb V=\{0\}\) separately or make the coercivity existence theorem include it.

### Proof route

The signs are:
\[
Dm=-C,\qquad D\theta=-C^{-1},\qquad D(-\theta)=C^{-1}.
\]
So **yes, your Hessian formula has the stated positive sign**.

For the explicit constant, the centered density satisfies
\[
\frac{dP_\theta}{d\nu}\ge e^{-2Br}
\quad(\|\theta\|\le r).
\]
Using variance minimization over constants,
\[
\operatorname{Var}_{P_\theta}X
\ge e^{-2Br}\operatorname{Var}_\nu X.
\]
Integrate the derivative along the parameter segment to obtain
\[
\langle\theta-\eta,m(\eta)-m(\theta)\rangle
\ge\kappa_r\|\theta-\eta\|^2,
\]
then apply Cauchy–Schwarz.

### Names

Confident: `HasFDerivAt`, `ContinuousLinearEquiv`, `ContinuousOn`, `ContDiffOn`.

Exact operator-inversion continuity and compact-sphere minimum lemma names: **unsure**. Your existing `chartDerivEquiv` avoids much of the matrix API.

A valuable corollary, when \(B>0\), is
\[
D^2j(v)[u,u]\ge B^{-2}\|u\|^2,
\]
because \(C_\theta\le B^2\,\mathrm{Id}\). This upgrades your basepoint quadratic bound to intrinsic strong convexity on \(\Omega\).

---

## 3. The full response differential—for arbitrary data paths and arbitrary observables

Candidate (d) should be strengthened and its hypotheses simplified.

### Core statement: depend only on the moment path

Let \(M:I\to m_0+\mathbb V\) be differentiable at \(s\), with \(M(s)\in\operatorname{relint}K\). Then
\[
\theta'(s)=-C_{\theta(s)}^{-1}M'(s),
\qquad
\frac{d}{ds}i(M(s))
=-\langle\theta(s),M'(s)\rangle.
\]

This requires **no topology on probability measures, no bounded log-density, and no special law path**. Those belong in corollaries establishing differentiability of \(M\).

Now add the theorem that most directly addresses “posterior expectation values”:

For bounded measurable \(F:X\to\mathbb R\), let
\[
R_F(M)=E_{\Pi_\nu(M)}F
\]
on the intrinsic interior. Then
\[
\boxed{
DR_F(M)[u]
=
\operatorname{Cov}_{P_{\theta(M)}}\!
\left(F,\left\langle C_{\theta(M)}^{-1}u,S\right\rangle\right).
}
\]

Thus every observable has a differential over the response manifold, not merely the selected statistics.

### Score-path corollary

Suppose a differentiable density path has score \(\ell_s\), with justified differentiation under the integral and
\[
E_{D_s}\ell_s=0.
\]
Then
\[
M'(s)=\operatorname{Cov}_{D_s}(S,\ell_s).
\]
Substitution gives the complete data-to-response susceptibility:
\[
\frac{d}{ds}R_F(M(s))
=
\operatorname{Cov}_{P_s}
\left(
F,
\left\langle
C_{\theta(s)}^{-1}\operatorname{Cov}_{D_s}(S,\ell_s),
S
\right\rangle
\right).
\]

Notice the two different laws: the driving covariance is under \(D_s\), while the response covariance is under \(P_s\).

### Proof route and names

Chain rule plus your inverse derivative. For the observable:
\[
D_\theta E_{P_\theta}F[w]
=-\operatorname{Cov}_{P_\theta}(F,\langle w,S\rangle);
\]
the two minus signs cancel.

Confident names: `HasFDerivAt.comp`, `HasDerivAt.comp`, `HasFDerivWithinAt`.

Exact differentiation-under-integral names: **unsure**. Reuse the machinery underlying `CubicResponse` rather than building a general “\(C^1\) manifold of laws” first.

**Stress test:** bounded log-densities alone do not justify differentiating expectations. You need derivative control or a direct hypothesis on the moment derivative.

---

## 4. An integrated Fisher-information budget for the entire journey

This is the most beautiful new synthesis available after item 2. It makes the “whole path” theorem more than a packaging exercise.

### Visible information as accumulated dual-metric energy

Along the straight mean path, prove
\[
\frac{d^2}{ds^2}i(M_s)
=
\langle\Delta,C_{\theta_s}^{-1}\Delta\rangle.
\]
Since \(i(M_0)=0\) and \(i'(M_s)|_{s=0}=0\), for \(r<1\),
\[
i(M_r)
=
\int_0^r(r-s)
\langle\Delta,C_{\theta_s}^{-1}\Delta\rangle\,ds.
\]

Passing to the endpoint gives
\[
\boxed{
i(M)=
\int_0^1(1-s)
\langle\Delta,C_{\theta_s}^{-1}\Delta\rangle\,ds.
}
\]
Interpret this initially as a nonnegative improper integral or `lintegral`; no boundedness of the inverse covariance near \(1\) is required.

This says:

> Finite endpoint information is exactly finite weighted dual-Fisher energy along the canonical response bridge.

### Total information along the mixture bridge

Let \(f=dD/d\nu\), \(f_s=1-s+sf\). For \(0<s<1\),
\[
\ell_s=\frac{f-1}{f_s},
\qquad
\mathcal F_{\rm data}(s)
=\int\frac{(f-1)^2}{f_s}\,d\nu.
\]
Prove
\[
\boxed{
\mathrm{KL}(D\|\nu)
=
\int_0^1(1-s)\mathcal F_{\rm data}(s)\,ds.
}
\]

Together with the visible identity:
\[
\mathrm{KL}(D\|\Pi_\nu(M))
=
\int_0^1(1-s)
\left[
\mathcal F_{\rm data}(s)
-\langle\Delta,C_{\theta_s}^{-1}\Delta\rangle
\right]ds.
\]

The last formula is an ordinary signed-integral identity once the two nonnegative integrals are known finite.

### Essential warning

Do **not** claim that the bracket is pointwise nonnegative. The two Fisher quantities use different laws, \(D_s\) and \(P_s\). Your basepoint regression inequality does not automatically extend to every \(s\).

Consequently, neither convexity nor monotonicity of the invisible-information path follows from the existing decomposition.

### Proof route and names

For the visible part: item 2, one-dimensional calculus, endpoint convergence, monotone convergence.

For total information, a robust route is the scalar identity
\[
x\log x-x+1
=
\int_0^1(1-s)\frac{(x-1)^2}{1-s+sx}\,ds,
\]
including \(x=0\), followed by Tonelli. This avoids assuming \(f-1\in L^2(\nu)\).

Confident names: `MeasureTheory.lintegral`, `intervalIntegral`.

Exact Tonelli, monotone-convergence, and twice-integrated derivative theorem names suitable here: **unsure**.

---

## 5. Pinsker, immediately converted into convergence of all bounded observable responses

This is worth doing, but I would not let a search for a perfect `fDiv` interface block it.

### Theorem

For probability laws \(\mu,\eta\), with
\[
\operatorname{TV}(\mu,\eta)=\sup_A|\mu(A)-\eta(A)|,
\]
prove
\[
\boxed{
\operatorname{ofReal}\!\left(2\operatorname{TV}(\mu,\eta)^2\right)
\le \mathrm{KL}(\mu\|\eta).
}
\]
This formulation handles infinite KL without dangerous `.toReal` conversions.

A convenient first Lean theorem is the measurable-event version:
```lean
ENNReal.ofReal
  (2 * ((μ A).toReal - (η A).toReal)^2)
    ≤ klDiv μ η
```
under probability-measure and `MeasurableSet A` hypotheses.

Then your endpoint theorem becomes
\[
\operatorname{TV}(P_1,P_s)
\le
\sqrt{\frac{i(M)-i(M_s)}2}.
\]
For \(|F|\le L\),
\[
\boxed{
|E_{P_s}F-E_{P_1}F|
\le
L\sqrt{2\bigl(i(M)-i(M_s)\bigr)}.
}
\]

This is a uniform convergence theorem for the entire class of bounded observables.

### Cheapest dependable proof route

1. Coarsen to the partition \(A,A^c\), obtaining binary KL as a lower bound.
2. For \(0<p,q<1\),
   \[
   b(p,q)=p\log(p/q)+(1-p)\log((1-p)/(1-q)),
   \]
   and
   \[
   \partial_p^2b(p,q)=\frac1p+\frac1{1-p}\ge4.
   \]
   Since \(b(q,q)=\partial_pb(q,q)=0\),
   \[
   b(p,q)\ge2(p-q)^2.
   \]
3. Handle binary boundary cases, then take the supremum over events.

Your conditioning chain rule may already give step 1 more cheaply than generic `fDiv` data processing.

### Names

Confident: `MeasureTheory.Measure.map`, `ENNReal.ofReal`, `Real.log`, `Real.sqrt`.

Exact available KL/`fDiv` data-processing names and TV API names: **unsure**. I would formalize the event inequality first and bridge to the preferred TV definition afterward.

Be explicit about convention: full variation norm is twice the TV used above.

---

## 6. Global strict convexity, including finite-rate boundary points, with an exact convexity-gap identity

Candidate (c) can be stronger than “strict convexity on the relint.”

### Statement

Let \(M_0,M_1\) have finite rate, \(0<t<1\), and write
\[
P_i=\Pi_\nu(M_i),\quad
Q_t=(1-t)P_0+tP_1,\quad
M_t=(1-t)M_0+tM_1.
\]
Prove the exact identity
\[
\boxed{
\begin{aligned}
&(1-t)i(M_0)+ti(M_1)-i(M_t)\\
&=(1-t)\mathrm{KL}(P_0\|Q_t)
+t\mathrm{KL}(P_1\|Q_t)
+\mathrm{KL}(Q_t\|\Pi_\nu(M_t)).
\end{aligned}}
\]

The first two terms are a weighted Jensen–Shannon divergence; the last measures failure of the mixture of representatives to remain canonical.

If \(M_0\ne M_1\), then \(P_0\ne P_1\), so the gap is strictly positive. Hence the rate is strictly convex on its **entire finite-rate domain**, including boundary points where the Fisher chart is unavailable.

### Optimization consequences

- On every convex constraint set, there is **at most one finite-rate minimizer**.
- Existence additionally follows for a compact constraint set meeting the finite-rate domain, using lower semicontinuity of the rate.
- Closed constraints inside the compact moment body are a natural specialization.

Do not state unconditional existence on arbitrary convex constraint sets.

### Proof route and names

Combine the mixture entropy identity
\[
(1-t)\mathrm{KL}(P_0\|\nu)+t\mathrm{KL}(P_1\|\nu)
=
\mathrm{KL}(Q_t\|\nu)
+(1-t)\mathrm{KL}(P_0\|Q_t)+t\mathrm{KL}(P_1\|Q_t)
\]
with your information decomposition for \(Q_t\).

Confident names: `StrictConvexOn`, `Convex`, `LowerSemicontinuous`, `IsCompact`.

Exact KL mixture-equality, KL-zero characterization, and compact-minimization lemma names: **unsure**. Your conditioning chain rule is again a plausible reusable route.

---

## Final stress test

Three qualifications should appear prominently in the eventual narrative:

1. **“Maximal entropy” is relative to \(\nu\).**  
   The reference law uniquely minimizes \(\mathrm{KL}(\,\cdot\,\|\nu)\). It is not generally a maximizer of an independently chosen Shannon or differential entropy.

2. **The Hessian is intrinsic.**  
   \[
   D^2\mathcal I=C^{-1}
   \]
   is correct on \(\mathbb V\), in the intrinsic interior. It is not an ambient inverse-covariance statement.

3. **Finite information does not give a finite endpoint parameter.**  
   The atlas ends continuously in information—and, after Pinsker, in TV—even when \(\theta_s\) diverges as \(s\uparrow1\).

My suggested implementation order is **1 → 2 → 3 → 5 → 4 → 6**. The conceptual centerpiece is the combination of **the atlas, the observable differential, and the integrated Fisher budget**: together they describe where responses go, how every bounded observable changes, and how much information the whole journey costs.