## Executive assessment

The next capstone should be **Legendre duality and the two journeys**, but with an essential correction:

> The full relative entropy is concave in the **full mean coordinates** \(\mu=\langle S\rangle\), with Hessian \(-G^{-1}\). It is not generally concave in the fixed-\(t\) response coordinates \(M=\langle R\rangle\).

On a fixed-\(t\) slice, it is the **relative entropy to \(P_{t,0}\), divided by \(t\)** whose Hessian is \(C^{-1}\). These distinctions also settle the normalization of the mixture second fundamental form.

My recommended order is:

1. **Duality and two-journey capstone**, with the necessary visible-quotient infrastructure.
2. **Exact global data quotient**.
3. **Quantitative stability on compact reachable regions**.
4. **Closed-set large-deviation upper bound**.
5. **Contraction/log-determinant identity**.
6. **Walls**, unless a specific wall mechanism is already sharply formulated.

---

# 1. Audit of the landed results

## 1.1 Canonical data assignment

The linear pullback construction and the differential
\[
D\,\mathrm{dataResponse}_d[h]
=-t\,\operatorname{Cov}_{t,a(d)}(R,R_{Lh})
\]
are correct.

Three qualifications matter.

### Positive temperature and common support

The exact kernel statement requires \(t\ne0\), normally \(t>0\). At \(t=0\), the entire data-response differential vanishes, regardless of visibility.

To identify invisibility independently of the current posterior, use equivalence of the finite exponential tilts with the reference measure:
\[
R_{Lh}\text{ constant }P_{t,a}\text{-a.s.}
\iff
R_{Lh}\text{ constant }\bar\pi\text{-a.s.}
\]
subject to the usual finite-loss, finite-normalizer assumptions.

### One displayed loss formula needs reconciliation

If
\[
D\,\mathrm{dataLoss}_d[h]=\langle R_{Lh}\rangle,
\]
then necessarily
\[
D^2\,\mathrm{dataLoss}_d[h,k]
=-t\,\operatorname{Cov}(R_{Lh},R_{Lk}).
\]

The third-cumulant formula
\[
t^2\kappa_3(L_0,R_{Lh},R_{Lk})
\]
is instead the Hessian of the **expected base loss**
\[
d\longmapsto \langle L_0\rangle_{t,a(d)}:
\qquad
D_h\langle L_0\rangle=-t\operatorname{Cov}(L_0,R_{Lh}).
\]

Thus the results can all be correct, but `dataLossGrad` cannot literally mean the gradient of the same scalar whose differential is \(\langle R_{Lh}\rangle\). The note should distinguish the free-energy landscape from the expected-base-loss landscape.

The entropy formula
\[
D_k\mathcal S(t,a(d))
=-t^2\operatorname{Cov}(L_0+a(d)\cdot R,R_{Lk})
\]
is correct.

### Weight space versus the manifold of data distributions

The assignment is canonical on the **mixture weight space**. To descend to the actual distribution \(\nu_d\), possibly represented by different weights, one needs
\[
\sum_jh_j\nu_j=0
\quad\Longrightarrow\quad
Lh\text{ invisible}.
\]
For the coefficient assignment itself to descend, the stronger conclusion \(Lh=0\) is needed.

Also, on the probability simplex the relevant tangent kernel is
\[
\{h:\textstyle\sum_jh_j=0,\ Lh\text{ invisible}\}.
\]

These are worthwhile explicit descent lemmas.

---

## 1.2 Natural journey

The entropy identities have the correct signs and weights:
\[
\frac{d}{ds}\mathcal S(s\theta_1)
=-s\,\operatorname{Var}_{s\theta_1}(\theta_1\cdot S),
\]
and
\[
\mathcal S(\theta_1)
=-\int_0^1s\,\operatorname{Var}_{s\theta_1}(\theta_1\cdot S)\,ds.
\]

The generic expectation-length estimate is
\[
\left|\langle\phi\rangle_{\theta_1}-\langle\phi\rangle_0\right|
\le
\int_0^1
\sqrt{\operatorname{Var}_{s\theta_1}(\phi)}
\sqrt{\operatorname{Var}_{s\theta_1}(\theta_1\cdot S)}
\,ds.
\]
An \(L^2\)-norm in place of the first standard deviation gives a weaker valid version.

The decomposition through \(P_{t,0}\) is also correct. It is particularly important because it explains why full entropy and fixed-slice relative entropy have different mean-coordinate Hessians.

“Featureless maximal entropy” should mean **maximal relative entropy \(-KL(\,\cdot\,\Vert\bar\pi)\)**, not maximal Shannon entropy unless the prior has the appropriate uniformity.

---

## 1.3 Mixture bending: correct residual, but normalize the tensor

Let
\[
g^{\mathrm F}_a(u,w)
=t^2\operatorname{Cov}(R_u,R_w).
\]
With your convention
\[
C=t\operatorname{Cov}(R,R),
\]
the actual Fisher metric in \(a\)-coordinates is
\[
g^{\mathrm F}=tC.
\]

Thus \(C\) is the response metric, or the Fisher metric rescaled by \(1/t\). This distinction should remain visible throughout the note.

### In coefficient coordinates

For fixed coefficient velocities \(u,w\),
\[
\left.\partial_s\partial_r
\frac{p_{a+su+rw}}{p_a}\right|_{s=r=0}
=
t^2\left(
\widetilde R_u\widetilde R_w
-\langle\widetilde R_u\widetilde R_w\rangle
\right).
\]

Under the score identification of ambient tangent vectors with mean-zero functions, the ambient mixture second fundamental form is therefore
\[
B^{(m)}_a(u,w)
=
t^2\operatorname{proj}_{(1\oplus\operatorname{span}\widetilde R)^\perp}
(\widetilde R_u\widetilde R_w).
\]

### In mean coordinates

Write \(M=m_t(a)\). Since
\[
D_am_t=-C,
\qquad
D_Ma=-C^{-1},
\]
the score associated with a mean-coordinate velocity \(v\) is
\[
\partial_v\log p_{a(M)}=tW_v.
\]

Consequently,
\[
\boxed{
B^{(m)}_M(v,w)=t^2\,\mathrm{mixBend}(v,w).
}
\]

In fact, in affine mean coordinates the entire second density derivative is normal:
\[
\left.
\partial_s\partial_r
\frac{p_{a(M+sv+rw)}}{p_{a(M)}}
\right|_{0,0}
=
t^2\,\mathrm{mixBend}(v,w).
\]
Its orthogonality to \(1\) follows from normalization; its orthogonality to every \(R_i\) follows from the affine dependence of the means on \(M\).

Hence:

- Your projection formula is correct.
- `mixBend` is the **normalized** mixture second fundamental form.
- For mean-coordinate velocities, the genuine tensor is \(t^2\mathrm{mixBend}\).
- Its Fisher squared norm carries the factor \(t^4\).

One can make `mixBend` itself the tensor by using velocities normalized to have scores \(W_v\), but that convention must be stated.

### Flatness does not imply zero bending

There are three distinct statements:

1. The ambient mixture connection is flat.
2. The induced mixture connection on a regular minimal exponential family is flat in mean coordinates.
3. The embedding need not be mixture-autoparallel: its normal second fundamental form can be nonzero.

Thus intrinsic m-geodesics are affine in means, but generally **are not literal convex mixtures of their endpoint probability measures**.

Finally, defining a bending *norm* requires the relevant fourth moments; the pointwise residual and its lower-order orthogonality need less.

---

## 1.4 Tilt lower bound and radius

The change of measure has the correct orientation:
\[
\frac{dP_b}{dP_a}
=\exp\{\lambda u\cdot R-\Lambda_a(\lambda u)\},
\qquad
b=a-\frac{\lambda}{t}u,
\]
so
\[
KL(P_b\Vert P_a)
=\lambda u\cdot m(b)-\Lambda_a(\lambda u).
\]

Put \(U=\sum_i|u_i|\). On the box of radius \(\rho\) around \(m(b)\),
\[
\left|\lambda u\cdot(\bar R_n-m(b))\right|
\le |\lambda|U\rho.
\]

Therefore the generally valid choice is
\[
\boxed{
\rho=\min\left\{\varepsilon,
\frac{\delta}{2(|\lambda|U+1)}
\right\}.
}
\]
Your expression is correct if \(\lambda\ge0\).

Once the tilted probability of that box is at least \(1/2\),
\[
P_a^{\otimes n}(\text{\(\varepsilon\)-box})
\ge
\frac12e^{-n(KL(P_b\Vert P_a)+\delta/2)}.
\]
Absorb the factor \(1/2\) by requiring
\[
n\ge \frac{2\log2}{\delta}.
\]

The bookkeeping is therefore correct, including strict boxes and \(\rho\le\varepsilon\). The hypotheses must include the finite second moments under \(P_b\) used by Chebyshev and the integrability needed for the KL identity.

---

# 2. The precise duality programme

## 2.1 Full natural coordinates

Use separate notation for the full mean:
\[
\mu(\theta)=\langle S\rangle_\theta,
\qquad S=(L_0,R).
\]
On a regular minimal region,
\[
\nabla A(\theta)=-\mu(\theta),
\qquad
D\mu(\theta)=-G(\theta),
\]
where
\[
G(\theta)=\operatorname{Cov}_\theta(S,S)
\]
is the full natural-coordinate Fisher form.

Define the negative-sign conjugate
\[
\boxed{
\Psi(\mu)=\sup_{\theta\in\Theta}
\{-\theta\cdot\mu-A(\theta)\}.
}
\]
Equivalently, \(\Psi(\mu)=A^*(-\mu)\) for the standard convex conjugate.

At every attained mean,
\[
\boxed{
\Psi(\mu(\theta))
=-\theta\cdot\mu(\theta)-A(\theta).
}
\]
Consequently,
\[
\boxed{
KL(P_\theta\Vert\bar\pi)
=\Psi(\mu(\theta))+A(0),
\qquad
\mathcal S(\mu)=-\Psi(\mu)-A(0).
}
\]

With an inverse full mean chart \(\theta=\theta(\mu)\),
\[
D_\mu\theta=-G(\theta(\mu))^{-1},
\]
and
\[
\boxed{
\nabla_\mu\Psi=-\theta,
\qquad
D^2_\mu\Psi=G^{-1},
}
\]
\[
\boxed{
\nabla_\mu\mathcal S=\theta,
\qquad
D^2_\mu\mathcal S=-G^{-1}.
}
\]

These are the full-family formulas. In particular, the entropy gradient is \(+\theta\), not \(-\theta\).

If the statistics have affine redundancies, replace inverses by inverses on the visible quotient. A total matrix inverse on a singular ambient space does not express this geometry correctly.

---

## 2.2 Fixed-\(t\) coordinates: where \(C^{-1}\) belongs

For \(t>0\), define
\[
F_t(a)=\frac1tA_t(a).
\]
Then
\[
\nabla_aF_t=-M,
\qquad
D_a^2F_t=C.
\]

Its negative-sign conjugate is
\[
\psi_t(M)
=\sup_a\{-a\cdot M-F_t(a)\}.
\]
On the slice mean chart,
\[
\psi_t(M)=-a(M)\cdot M-\frac1tA_t(a(M)),
\]
and
\[
\boxed{
\nabla_M\psi_t=-a(M),
\qquad
D_M^2\psi_t=C^{-1}.
}
\]

The relative-entropy identity is
\[
\boxed{
KL(P_{t,a(M)}\Vert P_{t,0})
=t\psi_t(M)+A_t(0).
}
\]

Thus the concave potential with Hessian \(-C^{-1}\) is
\[
-\frac1tKL(P_{t,a(M)}\Vert P_{t,0}),
\]
up to an irrelevant constant.

For the full entropy, let
\[
\ell_t(M)=\langle L_0\rangle_{t,a(M)}.
\]
Then
\[
\boxed{
\mathcal S(t,a(M))
=t\ell_t(M)-t\psi_t(M)-A(0),
}
\]
hence
\[
\boxed{
D_M^2\mathcal S
=tD_M^2\ell_t-tC^{-1}.
}
\]

There is no general sign for this Hessian. This is the principal correction to the proposed capstone.

Also, \((t,M)\) is a **mixed coordinate system**, not the full mean coordinate system \((\langle L_0\rangle,M)\).

---

## 2.3 What is immediate, and what is new?

| Result | Assessment |
|---|---|
| Legendre equality at an attained mean | Short corollary of the Gibbs variational inequality, or convexity of \(A\) plus \(DA=-\mu\) |
| \(\Psi(\mu(\theta))=-\mathcal S(\theta)-A(0)\) | Algebra once equality is established |
| Fixed-slice \(\nabla\psi_t=-a\) | Chain-rule cancellation using `sliceInv`/`responseChart` |
| Fixed-slice \(D^2\psi_t=C^{-1}\) | Short derivative theorem once the inverse-chart derivative is available |
| Full \(\nabla_\mu\mathcal S=\theta\) | Short corollary of \(d\mathcal S=-G(\theta,\cdot)\) and \(D_\mu\theta=-G^{-1}\) |
| Full mean inverse chart | Potentially genuinely new: the mixed chart does not supply it |
| Convexity of the reachable mean domain | Genuinely separate global issue; not supplied by local invertibility |
| Two-geodesic integral identities | New packaging and integration, but little new analytic machinery |
| KL as a Bregman divergence; Pythagoras | Mostly sign/orientation wrappers around `mixKL_three_point` |
| Arbitrary mean constraints, including unattained boundary means | Genuine convex-analysis/closure work |

For orientation, the Bregman identities are
\[
KL(P_\theta\Vert P_\eta)
=B_A(\eta,\theta)
=B_\Psi(\mu(\theta),\mu(\eta)).
\]
The three-point identity becomes
\[
KL(P\Vert R)
=
KL(P\Vert Q)+KL(Q\Vert R)
+(\theta_R-\theta_Q)\cdot(\mu_P-\mu_Q).
\]
Orthogonality of the last pairing gives the exact Pythagorean theorem. Projection inequalities require the additional convex constraint and first-order optimality argument.

---

# 3. The capstone: two journeys with two exact entropy budgets

Yes: this should be the capstone, stated in the **full visible natural/mean geometry**.

Let
\[
\mu_0=\mu(0),\qquad
\mu_1=\mu(\theta_1),\qquad
\Delta=\mu_1-\mu_0.
\]

## E-journey

Your landed path is
\[
\theta_e(s)=s\theta_1.
\]
Its entropy budget is
\[
\boxed{
-\mathcal S(\theta_1)
=
\int_0^1
s\,G_{s\theta_1}(\theta_1,\theta_1)\,ds.
}
\]

## M-journey

Assume the entire mean segment is reachable:
\[
\mu_m(s)=\mu_0+s\Delta,
\qquad
\theta_m(s)=\theta(\mu_m(s)).
\]
Put
\[
q(s)=
\Delta\cdot G_{\theta_m(s)}^{-1}\Delta.
\]

Then
\[
\boxed{
\frac d{ds}\mathcal S(\theta_m(s))
=\theta_m(s)\cdot\Delta,
}
\]
\[
\boxed{
\frac {d^2}{ds^2}\mathcal S(\theta_m(s))
=-q(s)\le0.
}
\]

Because \(\theta_m(0)=0\),
\[
\mathcal S'(0)=0,
\qquad
\mathcal S'(s)=-\int_0^sq(r)\,dr.
\]
Therefore the m-journey also has antitone entropy, and
\[
\boxed{
-\mathcal S(\theta_1)
=
\int_0^1(1-s)\,
\Delta\cdot G_{\theta_m(s)}^{-1}\Delta\,ds.
}
\]

This is the beautiful paired statement:
\[
\boxed{
\int_0^1s\,G_{\theta_e(s)}(\theta_1,\theta_1)\,ds
=
KL(P_{\theta_1}\Vert\bar\pi)
=
\int_0^1(1-s)\,
G_{\theta_m(s)}^{-1}(\Delta,\Delta)\,ds.
}
\]

The same information cost is expressed by:

- covariance along a straight natural-coordinate journey;
- inverse covariance along a straight mean-coordinate journey.

The opposite weights \(s\) and \(1-s\) are substantive, not cosmetic.

### A valuable additional identity

For an arbitrary reachable mean segment between \(P_0\) and \(P_1\),
\[
\boxed{
\int_0^1q(s)\,ds
=
KL(P_1\Vert P_0)+KL(P_0\Vert P_1).
}
\]
Consequently its Fisher length satisfies
\[
L_m^2\le
KL(P_1\Vert P_0)+KL(P_0\Vert P_1).
\]

This gives a clean bridge from duality to quantitative stability without first formalizing a global Riemannian distance.

---

# 4. Clean Lean formulation

## Start with chartwise differential identities, not `ConcaveOn`

The first target should be **second derivatives along reachable mean segments**.

Reasons:

1. Local mean-chart domains need not be convex.
2. A globally convex natural domain does not, without additional hypotheses, settle convexity of its gradient image.
3. `ConcaveOn` bundles a domain-level convexity assertion with the functional assertion.
4. Segment derivatives directly deliver the entropy-production and journey theorems.

Later derive `ConcaveOn` on every convex subset contained in the mean-chart domain. A global result on all of `chartDomain` should have a separate convexity theorem or hypothesis.

## Suggested theorem bundle

The following are schematic interfaces, not proposed exact Mathlib syntax.

### A. Chart potential

Define on the inverse-chart domain
\[
\mathrm{dualOnChart}(M)
=-\langle\mathrm{meanInv}(M),M\rangle
-A(\mathrm{meanInv}(M)).
\]

Prove:

```lean
dualOnChart_mean
hasFDerivAt_meanInv
hasFDerivAt_dualOnChart
hasFDerivAt_entropyMean
```

with derivatives
\[
D\,\mathrm{meanInv}=-G^{-1},\qquad
D\,\mathrm{dualOnChart}[h]=-\theta\cdot h,\qquad
D\,\mathrm{entropyMean}[h]=\theta\cdot h.
\]

Represent \(G\) as a continuous linear equivalence on the visible space when practical. This keeps the inverse honest.

### B. Avoid extended-real conjugates initially

Prove a universal inequality and an attainment statement:
\[
-\eta\cdot M-A(\eta)
\le \mathrm{dualOnChart}(M),
\]
with equality at \(\eta=\mathrm{meanInv}(M)\).

That is already the conjugacy theorem. It avoids making the first duality module depend on an extended-real supremum API.

### C. Segment differentiation

For \(M_s=M_0+s\Delta\), prove:

```lean
hasDerivAt_entropyMean_line
hasDerivAt_entropyMean_line_deriv
entropyMean_line_second_nonpos
```

The second derivative should be stated directly as
\[
-\langle \Delta,G^{-1}\Delta\rangle.
\]

### D. Integrated journey

Under continuity on the compact segment and featureless initial mean:

```lean
entropyMean_line_antitoneOn
entropyMean_eq_neg_integral_inverseMetric
naturalJourney_cost_eq_meanJourney_cost
meanJourney_energy_eq_jeffreys
meanJourney_length_sq_le_jeffreys
```

### E. Convexity corollaries

Only then add:

```lean
concaveOn_entropyMean_of_convex_subset
convexOn_dualOnChart_of_convex_subset
```

and strict versions on the visible space.

## Main pitfalls

- **Full versus slice means:** `responseChart` for \((t,M)\) is not the full mean chart.
- **Temperature factors:** \(C=t\operatorname{Cov}(R,R)\), while slice Fisher is \(tC\).
- **Featureless endpoint:** the fixed-\(t\) chart degenerates at \(t=0\); use the full natural chart there.
- **Regularity at zero:** a finite normalizer at \(\theta=0\) alone does not give an open exponential-moment neighborhood.
- **Reachability:** affine interpolation of endpoint means needs an explicit segment-domain hypothesis.
- **Redundancy:** invert only after removing affine-constant statistics.
- **Ambient versus intrinsic mixtures:** an m-geodesic is not generally \(sP_1+(1-s)P_0\).

---

# 5. Re-ranking and the next substantial directions

## 1. Duality and the two-journey theorem

This most directly completes the PI’s request. It converts an atlas of responses into a dual geometric map with an exact information budget.

The minimum first deliverable is:

1. Fixed-slice dual potential and \(C^{-1}\) Hessian.
2. Full mean-chart distinction and full entropy Hessian.
3. Mean-segment entropy production.
4. The paired e/m entropy-budget identity.

## 2. Exact visible/invisible quotient — open (e)

Upgrade the differential kernel to a **global fiber theorem**:
\[
\boxed{
m_t(a)=m_t(b)
\iff
P_{t,a}=P_{t,b}
\iff
a-b\text{ invisible}.
}
\]

The useful proof route is the symmetrized KL identity:
\[
KL(P_{t,a}\Vert P_{t,b})
+KL(P_{t,b}\Vert P_{t,a})
=
t(b-a)\cdot(m_t(a)-m_t(b)).
\]
Equal responses force both KL terms to vanish.

Pulling this back gives
\[
\mathrm{dataResponse}(d)=\mathrm{dataResponse}(e)
\iff
L(d-e)\text{ invisible}.
\]

This is stronger than local constant-rank geometry: it identifies the exact posterior equivalence classes globally. It also handles the data-mixture descent issue identified above.

## 3. Quantitative stability — open (d)

On a region where
\[
0<\alpha I\le C\le\beta I,
\]
the mean-coordinate dual Hessian obeys
\[
\beta^{-1}I\le D^2\psi_t\le\alpha^{-1}I.
\]

Along reachable mean segments this yields
\[
\boxed{
\frac{t}{2\beta}\|M-N\|^2
\le
KL(P_{t,a(M)}\Vert P_{t,a(N)})
\le
\frac{t}{2\alpha}\|M-N\|^2.
}
\]

Together with analogous coefficient-coordinate estimates, this gives stable inversion, quantitative identifiability, and controlled response landscapes. Compactness supplies uniform constants only after nondegeneracy on the visible space has been established.

## 4. Large-deviation upper bound — open (b)

This completes the variational-cost spine alongside the landed lower bound.

Separate the proof into:

1. local exponential-Chernoff upper bounds;
2. compact-set upper bounds by finite covers;
3. exponential tightness;
4. closed-set upper bounds.

Finite exponential moments in a neighborhood of zero under the sampling posterior are the standard sufficient condition for step 3 in finite dimension. Without an exponential-tightness mechanism, the compact upper bound does not automatically extend to every closed set.

This is a valuable theorem, but less conceptually new than duality now is.

## 5. Contraction/log-determinant — open (a)

Worth landing, especially if Jacobi is close. State the nonsingularity/positive-determinant hypotheses explicitly, and distinguish the derivative at fixed mean from the derivative at fixed coefficient.

Its best conceptual role is **volume response under temperature change**, complementing pointwise response and bending. It is not yet the central organizing theorem.

## 6. Walls — open (c)

Defer a general wall programme until “wall” has been split into mechanisms:

- loss of integrability at the natural-domain boundary;
- covariance degeneration;
- mean escape toward a convex-support face;
- failure of inverse-chart continuation.

They need not coincide. The quotient and duality modules will make their distinctions much cleaner.

---

# 6. One further direction of comparable depth

I would prioritize **constrained entropy maximization and exact information projection**, rather than Hamiltonian language.

For an attained full mean \(\mu\), let \(P_\mu\) be its exponential-family representative. For any admissible \(Q\) with the same mean,
\[
\boxed{
KL(Q\Vert\bar\pi)
=
KL(Q\Vert P_\mu)+KL(P_\mu\Vert\bar\pi).
}
\]

Hence
\[
\Psi(\mu)+A(0)
=
\min_{\mathbb E_QS=\mu}KL(Q\Vert\bar\pi),
\]
with unique minimizer \(P_\mu\).

This identifies the response manifold as the family of **least-informative distributions realizing each reachable mean**. It connects the PI’s “map from featureless to actual” directly to an optimization principle, and should be a short consequence of the landed Gibbs variational machinery.

By contrast:

- A response-geodesic distance becomes a genuine distance after quotienting under standard regularity, but **properness or completeness does not follow**.
- \(\partial_tm=-\operatorname{Cov}(L,R)\) is fluctuation–dissipation, not by itself a Hamiltonian flow: there is no supplied symplectic structure.
- There is a natural gradient interpretation already available:
  \[
  \operatorname{grad}_G\mathcal S=-\theta.
  \]
  Thus natural rays, after logarithmic reparameterization, are entropy-gradient trajectories with the appropriate orientation.

The strongest next narrative is therefore:

> **Invisible data directions are quotiented out; visible means uniquely specify the posterior; the posterior is the least-informative realization of those means; and natural and mean journeys spend exactly the same information cost through dual covariance budgets.**