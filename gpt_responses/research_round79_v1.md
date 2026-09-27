The reverse implication does close **without a Schur-complement inverse**. Your scalar pairing is the right simplification. There is also one sign correction that should be made before formalizing anything.

## 1. Fix the data-side sign

Use your convention
\[
\frac d{dt}\mathbb E_{\rho_t}f=\operatorname{Cov}_{\rho_t}(f,h),
\qquad Dm(\theta)w=-\operatorname{Cov}_{P_\theta}(S,\langle w,S\rangle).
\]
Put
\[
d=H-h,\qquad \ell=\beta-\langle u,S\rangle,\qquad
a(t)=\mathbb E_{\rho_t}\ell.
\]
Then
\[
\boxed{a'=\operatorname{Cov}_{\rho_t}(\ell,h)
      =-\operatorname{Cov}_{\rho_t}(\ell,d)
      =a\,\mathbb E_{\rho_t}d-\mathbb E_{\rho_t}(\ell d)
      \le a\,\mathbb E_{\rho_t}d.}
\]
Thus the expression “\(a'=-\operatorname{Cov}(\ell,h)\)” in the question has the wrong sign. Your later identity is correct:
\[
\boxed{\langle u,\mathrm{dataCov}(t)\rangle=-a'(t).}
\]

Because the model and data means agree,
\[
a(t)=\beta-\langle u,m(\theta_t)\rangle
    =\mathbb E_{P_{\theta_t}}\ell.
\]
This equality is what lets the data dissipation estimate control model geometry.

---

## 2. Continuity of `dataThetaVel`: use local coercivity, not inverse API

### Recommended route

Given what you already have, I would use **(c), quantitatively**, with `exists_coercive_familyMeasure` on \(W\). It avoids both inverse-operator API and upgrading strict differentiability to `ContDiff`.

Here is the reusable lemma.

### Parametric linear solutions are continuous

Let \(E\) be a real Hilbert space, \(A_t:E\toL E\), and suppose
\[
A_tz_t=b_t.
\]
Assume \(A\) and \(b\) are continuous at \(t_0\), and
\[
\langle w,A_{t_0}w\rangle\ge\lambda\|w\|^2
\quad(\lambda>0).
\]
Eventually,
\[
\langle w,A_tw\rangle\ge\frac{\lambda}{2}\|w\|^2.
\]
Consequently,
\[
\boxed{
\|z_t-z_{t_0}\|
\le \frac2\lambda
\left(\|b_t-b_{t_0}\|
+\|A_t-A_{t_0}\|\,\|z_{t_0}\|\right).}
\]
Indeed,
\[
A_t(z_t-z_{t_0})
=b_t-b_{t_0}-(A_t-A_{t_0})z_{t_0},
\]
and pair with \(z_t-z_{t_0}\).

A Lean-shaped interface is:

```lean
lemma continuousAt_of_coercive_linear_equation
    (A : X → E →L[ℝ] E) (b z : X → E)
    (hA : ContinuousAt A x₀)
    (hb : ContinuousAt b x₀)
    (heq : ∀ x, A x (z x) = b x)
    (hλ : 0 < λ)
    (hcoercive : ∀ w, λ * ‖w‖ ^ 2 ≤ inner w (A x₀ w)) :
    ContinuousAt z x₀
```

The proof only needs an eventual operator-norm bound
\(\|A_t-A_{t_0}\|<\lambda/2\), Cauchy–Schwarz, and the displayed estimate.

Apply it on the subtype \(W\), with
\[
A_t=-Dm(\theta_t)|_W,\qquad
z_t=\mathrm{dataThetaVel}(t),\qquad
b_t=-\mathrm{dataCov}(t).
\]

Required inputs:

* `dataTheta` is continuous, already following from its derivative theorem;
* `continuous_meanMapDeriv`;
* continuity of `dataCov`, from bounded tilted moments;
* coercivity at the single point \(\theta_{t_0}\).

This proves global continuity if the data family is defined for all real \(t\), hence the required `ContinuousOn ... (Ici 0)`.

**Why this route:** the strict-derivative route is mathematically valid with the appropriate neighborhood differentiability hypotheses, but finding and satisfying the exact derivative-continuity theorem is unnecessary here. Likewise, continuity of operator inversion is standard, but I would not give you an unverified Mathlib theorem name. The estimate above is short, robust, and useful again.

---

## 3. Reverse implication: the complete scalar argument

Write
\[
q_t=P_{\theta_t},\quad
r=\mathrm{normalDepth}(\theta_t),\quad
v=\theta_t+ru=\mathrm{faceTheta}(\theta_t).
\]
Define
\[
r'=-\frac{\langle\theta'_t,u\rangle}{\langle u,u\rangle},
\qquad
v'=\theta'_t+r'u.
\]
Thus
\[
\theta'_t=v'-r'u,\qquad v'_t\in T'.
\]

On a sufficiently late tail, your landed results give:

* \(r(t)\to\infty\);
* \(v(t)\to v_M\), hence \(v\) is bounded;
* \(p(t):=q_t(A)\to1\);
* uniform tangential coercivity
  \[
  \operatorname{Var}_{q_t}\langle w,S\rangle\ge\lambda\|w\|^2
  \quad(w\in T').
  \]

Choose \(B>0\) with \(\|S\|\le B\) a.e. Set
\[
\begin{aligned}
V&=\operatorname{Var}_{q_t}\ell
  =\operatorname{Var}_{q_t}\langle u,S\rangle,\\
c&=\operatorname{Cov}_{q_t}
       (\langle u,S\rangle,\langle v',S\rangle),\\
D&=\|\mathrm{dataCov}(t)\|,\qquad
e=\mathbb E_{\rho_t}d,\qquad x=\|v'\|.
\end{aligned}
\]

All statements below are pointwise on that tail.

### Lemma 1: the two scalar block identities

From `dataCov = Dm θ θ'`,
\[
\boxed{r'V=-a'+c,}
\]
and, pairing with \(v'\),
\[
\boxed{
\operatorname{Var}_{q_t}\langle v',S\rangle
=-\langle v',\mathrm{dataCov}(t)\rangle+r'c.}
\]

These are the only block identities needed. There is no \(C^{-1}\).

Suggested interfaces:

```lean
lemma depthVel_mul_variance_eq :
    depthVel t * slackVariance t =
      -slackMeanVel t + tangentNormalCov t

lemma tangent_variance_eq :
    lawVar (q t) (fun ω ↦ inner (tangentVel t) (S ω)) =
      -inner (tangentVel t) (dataCov t)
        + depthVel t * tangentNormalCov t
```

### Lemma 2: covariance is small in the mean slack

Since \(\ell\ge0\) a.e. and
\(|\langle v',S\rangle|\le Bx\),
\[
\boxed{|c|\le 2Ba x.}
\]
Indeed \(c=-\operatorname{Cov}_{q_t}(\ell,\langle v',S\rangle)\), and bound the two terms defining covariance separately.

This is a useful standalone lemma:

```lean
lemma abs_cov_le_two_mul_mean_mul_bound
    (hℓ : 0 ≤ᵐ[q] ℓ)
    (hf : ∀ᵐ ω ∂q, |f ω| ≤ K) :
    |lawCov q ℓ f| ≤ 2 * (∫ ω, ℓ ω ∂q) * K
```

Include your usual probability and integrability hypotheses.

### Lemma 3: tangential velocity estimate

Coercivity and Lemmas 1–2 give
\[
\lambda x^2\le xD+2Ba|r'|x.
\]
Splitting off \(x=0\),
\[
\boxed{x\le\lambda^{-1}(D+2Ba|r'|).}
\]

```lean
lemma norm_tangentVel_le :
    ‖tangentVel t‖ ≤
      λ⁻¹ * (‖dataCov t‖
        + 2 * B * slackMean t * |depthVel t|)
```

### Lemma 4: atom mass controls mean slack versus variance

For any nonnegative slack vanishing on an event of mass \(p>0\),
\[
\boxed{p\,a^2\le(1-p)V.}
\]
This follows from
\[
a^2\le(1-p)\mathbb E_q\ell^2
=(1-p)(V+a^2).
\]

In particular,
\[
\frac{a^2}{V}\le\frac{1-p}{p}.
\]
Since \(p(t)\to1\), eventually
\[
\boxed{\frac{4B^2a^2}{\lambda}\le\frac V2.}
\]

This is the scalar absorption estimate replacing explicit Schur-complement inversion. It is simpler here than invoking the full `facet_schur_bound`.

### Lemma 5: weighted negative radial variation

Let \(z=(r')_-=\max(-r',0)\). If \(r'\ge0\), the desired estimate is trivial. Otherwise \(|r'|=z\), and
\[
Vz=a'-c\le ae+2Bax.
\]
Substituting Lemma 3,
\[
\left(V-\frac{4B^2a^2}{\lambda}\right)z
\le a\left(e+\frac{2B}{\lambda}D\right).
\]
After absorption,
\[
\boxed{
\sqrt V\,(r')_-
\le
2\frac a{\sqrt V}
\left(e+\frac{2B}{\lambda}D\right).}
\]

For a proper facet and a nondegenerate finite-parameter family, \(V>0\). On a tail with \(p\ge1/2\), Lemma 4 yields \(a/\sqrt V\le1\). Hence the particularly convenient conclusion is
\[
\boxed{
\sqrt V\,(r')_-
\le 2e+\frac{4B}{\lambda}D.}
\]

```lean
lemma sqrt_slackVariance_mul_neg_depthVel_le :
    Real.sqrt (slackVariance t) * max (-depthVel t) 0 ≤
      2 * dataDefectMean t
        + (4 * B / λ) * ‖dataCov t‖
```

Your `DataDissipation` now proves integrability of the left side on the tail.

### Lemma 6: compare with the fixed reference ray

Let
\[
g(s)=\sqrt{\mathrm{raySpeedSq}(0,u,s)}.
\]
Boundedness of \(v(t)\) gives fixed constants \(c_0,C_0>0\) such that
\[
\boxed{c_0g(r(t))\le\sqrt{V(t)}\le C_0g(r(t)).}
\]

Use the quantitative bounded-tilt variance comparison underlying `RayTiltInvariance`, rather than just its final finiteness equivalence. If that quantitative comparison is not exported, export it now.

It follows that
\[
\int g(r(t))(r'(t))_-\,dt<\infty.
\]

### Lemma 7: one-sided weighted variation

This should be a completely generic real-analysis lemma.

Suppose \(r\) is \(C^1\) on a tail, \(r(t)\ge R\), \(g\ge0\) is continuous on \([R,\infty)\), and
\[
\int_R^\infty g(s)\,ds<\infty,\qquad
\int g(r(t))(r'(t))_-\,dt<\infty.
\]
Then
\[
\boxed{\int g(r(t))|r'(t)|\,dt<\infty.}
\]

Take
\[
G(x)=\int_R^x g(s)\,ds.
\]
On each finite interval,
\[
g(r)|r'|=(G\circ r)'+2g(r)(r')_-.
\]
Therefore
\[
\int_{t_0}^Tg(r)|r'|
\le
\int_R^\infty g
+2\int_{t_0}^Tg(r)(r')_-.
\]
Pass to the half-line by monotone exhaustion.

**Lean advice:** prove the finite-interval inequality using ordinary interval integrals first, then a separate `lintegral` corollary. Do not manipulate a potentially undefined signed improper integral. Notice that this lemma itself does not need \(r\to\infty\); boundedness below suffices.

### Lemma 8: upper bound the full response speed

The standard-deviation triangle inequality gives
\[
\sqrt{\mathrm{responseSpeedSq}(t)}
\le Bx+\sqrt V\,|r'|.
\]
Using Lemma 3,
\[
\sqrt{\mathrm{responseSpeedSq}(t)}
\le \frac B\lambda D+
\left(1+\frac{2B^2}{\lambda}\frac a{\sqrt V}\right)
\sqrt V\,|r'|.
\]
On the same tail,
\[
\boxed{
\sqrt{\mathrm{responseSpeedSq}(t)}
\le \frac B\lambda D+
\left(1+\frac{2B^2}{\lambda}\right)C_0
g(r(t))|r'(t)|.}
\]
Both terms are integrable.

The initial compact interval has finite length by continuity of the response speed. This finishes the reverse implication.

### What is actually new here?

After your landed work, the remaining substantive ingredients are:

1. the elementary covariance bound \( |c|\le2Ba\|v'\|\);
2. the absorption argument for negative depth velocity;
3. the generic one-sided weighted-variation lemma.

Everything else is assembly.

---

## 4. The data-ray theorem to land

Under your standard hypotheses:

* bounded sufficient statistic with charged, full-dimensional relative polytope \(P\) in direction space \(W\);
* a proper facet \(F\), exposed by \(u\in W\), with your `FaceGauge` hypotheses;
* bounded measurable \(h\le H\) a.e.;
* \(p_*=\nu\{h=H\}>0\);
* \(\rho_t=\nu.\mathrm{tilted}(th)\);
* the response parameter and derivative objects already constructed;
* \(M=\mathbb E_\nu[S\mid h=H]\in\operatorname{ri}F\);

the statement is
\[
\boxed{
\int_0^\infty\sqrt{\mathrm{responseSpeedSq}(t)}\,dt<\infty
\quad\Longleftrightarrow\quad
\int_0^\infty\sqrt{\mathrm{raySpeedSq}(0,u,r)}\,dr<\infty.}
\]

Schematic Lean conclusion:

```lean
theorem data_fisher_length_lt_top_iff_ray
    -- standing family, facet, bounded-data, and top-mean hypotheses
    :
    (∫⁻ t in Set.Ici (0 : ℝ),
        ENNReal.ofReal (Real.sqrt (responseSpeedSq t))) < ⊤ ↔
    (∫⁻ r in Set.Ici (0 : ℝ),
        ENNReal.ofReal (Real.sqrt (raySpeedSq 0 u r))) < ⊤
```

Adapt the integrands to your existing nonnegative-real conventions.

* **Forward:** continuity of `dataThetaVel` plus `facet_fisher_access_iff`.
* **Reverse:** the eight lemmas above plus `DataDissipation`.

This says something stronger than existence of an accessible response: **every bounded charged-top data tilt whose limiting mean lies in that facet has the same length-finiteness answer.**

---

## 5. What is deepest now?

My ranking by **conceptual depth**, rather than immediate development priority, is:

1. **Intrinsic Fisher completion and its boundary fibers.**
2. **Codimension-two obstruction / charged-square counterexample.**
3. **Flags and genuinely higher-codimension accessibility.**
4. **Data-ray strengthening.**
5. **Layer classification of accessible facets.**

I would nevertheless **land the data-ray theorem next**: the proof has now become controlled scalar analysis, and it supplies a powerful bridge from data dynamics to intrinsic boundary geometry.

### 5.1 Intrinsic completion — the deepest next program

For \(\theta\in W\), define
\[
\mathcal Q_\theta(w)=\operatorname{Var}_{P_\theta}\langle w,S\rangle,
\qquad
L(\gamma)=\int\sqrt{\mathcal Q_{\gamma(t)}(\gamma'(t))}\,dt.
\]
Define \(d_F\) by infimizing lengths of piecewise \(C^1\) paths, and transport it through `meanMap` to `ri P`. On a data-response curve, this is exactly your `responseSpeedSq` length.

Here is a precise **first completion theorem**, before attempting a boundary classification. Let \(B>0\) bound \(\|S\|\), and put
\[
\Psi(\theta)=\sqrt{dP_\theta/d\nu}\in L^2(\nu).
\]
Then:

1. \(d_F\) is a finite-valued metric on \(W\), inducing its usual topology.
2. For all \(\theta,\eta\),
   \[
   \|m(\theta)-m(\eta)\|\le B\,d_F(\theta,\eta),
   \qquad
   \|\Psi(\theta)-\Psi(\eta)\|_2\le\tfrac12 d_F(\theta,\eta).
   \]
3. Both maps extend uniquely to the metric completion:
   \[
   \overline m:\widehat W_F\to P,\qquad
   \overline\Psi:\widehat W_F\to\overline{\Psi(W)}^{\,L^2}.
   \]
   Values of \(\overline\Psi\) are nonnegative unit vectors, hence square roots of probability densities.
4. After proving a finite-length \(C^1\) realization lemma for completion points, your facet theorem upgrades to
   \[
   \boxed{
   \exists x\in\widehat W_F,\ \overline m(x)=M
   \iff
   \int_0^\infty\sqrt{\mathrm{raySpeedSq}(0,u,r)}\,dr<\infty
   }
   \quad(M\in\operatorname{ri}F).
   \]

**Lean route:** define the metric on \(W\) first; use local upper and lower covariance bounds for topology and positivity, line segments for finiteness, and concatenation for the triangle inequality. Prove the two Lipschitz estimates before invoking `UniformSpace.Completion`. Transport to the mean atlas afterward. The deep question beyond this theorem is whether completion points with the same limiting mean—or the same Hellinger limit—must coincide. Neither injectivity nor surjectivity onto the full Hellinger closure should be assumed.

### 5.2 Charged square — the highest-value obstruction

This should isolate exactly what breaks beyond a facet: a single scalar depth no longer controls escape, and different normal directions or schedules can interact. The valuable theorem is the specific separation your proposed example targets—e.g. failure of a naive fixed-ray criterion—not merely existence of unusual asymptotics. **Lean route:** specify the countable atomic measure explicitly, prove its normalization and vertex charges, and reduce covariance/length statements to nonnegative series. Prove upper estimates for the candidate path and lower estimates for the rays separately. This is likely to tell you what the correct completion-fiber and flag statements can even be.

### 5.3 Flags — structurally deepest after the obstruction

Flags should be formulated as recursive face reductions with several depths, not as repeated application of the facet iff without additional uniformity. The issue is whether estimates in the first reduction remain controlled while the tangential component itself escapes toward a subface. **Lean route:** package conditioning on an exposed face as an exponential-family object with its own direction space, covariance, and gauge; prove compatibility under nested conditioning. Then formulate a two-stage theorem with explicit uniform estimates before generalizing to finite flags. The missing ingredient is likely quantitative multiscale control, not another face-coordinate identity.

### 5.4 Data-ray strengthening — a sharp dynamical theorem

Its depth is the fact that a prescribed data trajectory cannot accumulate infinite backtracking length when the facet ray is finite. **Lean route:** follow §§2–4. In particular, keep the negative-variation argument generic and the model-dependent work scalar. This is now a relatively short extension of the landed architecture, not a new geometric foundation.

### 5.5 Layer classification — there is a clean exact criterion

There is a stronger and cleaner statement than “finitely many atoms per shell.” Let \(\mu\) be the slack law along a fixed lift, with
\[
\mu\{0\}=p>0,\qquad \ell\ge0,
\]
and define dyadic layer masses
\[
m_n=\mu\{2^{-(n+1)}<\ell\le2^{-n}\}.
\]
For bounded slack, the exact criterion is
\[
\boxed{\text{finite ray length}\quad\Longleftrightarrow\quad
\sum_{n\ge0}\sqrt{m_n}<\infty.}
\]
Slack above \(1\) contributes only a finite amount.

Indeed, charged mass at zero makes tilted variance comparable to
\[
\int \ell^2e^{-r\ell}\,d\mu.
\]
For necessity, integrate over disjoint intervals \(r\in[2^n,2^{n+1}]\) and retain the \(n\)-th shell. For sufficiency, use the square-root subadditivity bound and integrate each shell separately. Both directions contribute a constant multiple of \(\sqrt{m_n}\).

Thus:

* \(m_n\asymp n^{-\alpha}\): accessible iff \(\alpha>2\);
* \(m_n\asymp n^{-2}(\log n)^{-\gamma}\): accessible iff \(\gamma>2\);
* polynomially approaching atoms \(\ell_k\asymp k^{-a}\), with weights \(\asymp k^{-b}\), \(b>1\): accessible, because their **dyadic aggregate** masses decay exponentially.

**Lean route:** first prove the charged-zero variance comparison; then a standalone dyadic Laplace-square-root theorem using `lintegral` and nonnegative sums. Apply `RayTiltInvariance` afterward. The number of atoms inside a shell is irrelevant: **total mass per multiplicative slack scale is the invariant.**

That last theorem is probably the best short project after the data-ray strengthening: it turns the facet theorem from an analytic criterion into an explicit geometric classification.