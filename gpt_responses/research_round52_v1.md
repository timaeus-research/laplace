## 1. The missing structural theorem: a Fisher-orthogonal statistical retraction

My choice is **(i), stated locally on the regular mean domain**, and packaged with its tangent-space interpretation.

The existing results already explain how much information lies in each part of the map. What remains is to identify **the map itself as a geometric object**:

> Reconstruction is an idempotent statistical projection whose differential is the Fisher-orthogonal projection onto the exponential-family tangent space.

This connects the global KL decomposition, the atlas, and the quadratic shadow in one theorem. The dually-flat picture is beautiful, but it chiefly gives geometric names to identities already present. The retraction theorem identifies what reconstruction *does to perturbations*.

### Precise formulation

Write
\[
Q_m=q_m\nu,\qquad
\Sigma_m=\operatorname{Cov}_{Q_m}(S),\qquad
\ell_{m,u}=\langle \Sigma_m^{-1}u,S-m\rangle.
\]
Assume a regular interior mean \(m\), with \(\Sigma_m\) invertible. Define
\[
B_mh
=\left\langle
\Sigma_m^{-1}\mathbb E_{Q_m}[(S-m)h],S-m
\right\rangle .
\]
This is the orthogonal projection in \(L^2(Q_m)\) onto the span of the centered features.

For the **normalized** tilt
\[
D_t=\frac{e^{th}}{\mathbb E_{Q_m}e^{th}}Q_m,
\]
with bounded \(h\), the theorem is
\[
\left\|
\frac{d\Pi(M_{D_t})/dQ_m-1}{t}-B_mh
\right\|_{L^1(Q_m)}
\longrightarrow0.
\]
No centering assumption on \(h\) is necessary: \(B_m\) kills constants.

The structural package should include:

1. \(\Pi(M_{Q_m})=Q_m\);
2. the derivative above;
3. \(B_m^2=B_m\), self-adjointness, and the identification of its range and kernel;
4. compatibility with observation.

For the last item, put
\[
P_mh=\mathbb E_{Q_m}[h\mid\sigma(S)].
\]
Then
\[
P_mB_m=B_mP_m=B_m,
\]
and every centered score has the orthogonal decomposition
\[
h=B_mh+(P_m-B_m)h+(I-P_m)h.
\]
Thus the three information terms correspond to three orthogonal tangent components:
\[
\boxed{\text{reconstructible response}\;\oplus\;
\text{observable non-family response}\;\oplus\;
\text{unobservable response}.}
\]

You already have their squared norms in the quadratic limits. The retraction theorem supplies the operator-level explanation.

### Two important qualifications

**Do not call all finite-information laws a smooth manifold.** Nor should one assert differentiability at every boundary reconstruction. Covariance can degenerate, natural parameters can diverge, and boundary regularity requires separate hypotheses.

A clean formulation is:

- the information decomposition is global, including the boundary;
- reconstruction is a smooth Fisher-orthogonal retraction on the regular interior;
- any boundary smoothness or stratification is a separate theorem.

With bounded features, one can strengthen the local formulation without constructing a manifold of probability laws. Extend reconstruction to signed \(L^1(\nu)\) densities of mass one whose moments lie in the regular mean domain:
\[
f\longmapsto q_{\int Sf\,d\nu}.
\]
This is a map on an open subset of an affine Banach space. Its restriction to probability densities is the desired reconstruction map.

Also, “Fisher-orthogonal” describes the **differential**. It does not say reconstruction is the nearest-point projection for Fisher–Rao distance.

### Where the dually-flat theorem fits

Formalise the orthogonality statement too: it is extremely cheap and worth having.

Let \(A,B,C\) be mean coordinates, and let \(\theta\) denote natural coordinates. The arrival tangent of the m-geodesic \(A\to B\) is \(B-A\); the departure tangent of the e-geodesic \(B\to C\), expressed in mean coordinates, is
\[
\Sigma_B(\theta_C-\theta_B).
\]
Consequently,
\[
g_B\bigl(B-A,\Sigma_B(\theta_C-\theta_B)\bigr)
=\langle A-B,\theta_B-\theta_C\rangle.
\]
Your three-point identity therefore gives precisely
\[
\text{Pythagorean equality}
\quad\Longleftrightarrow\quad
\text{Fisher orthogonality at }B.
\]

That is a lovely geometric capstone. I would prove it immediately, but not substitute it for the retraction theorem.

---

## 2. The two outstanding analytic results

### A. The \(L^1\)-valued derivative

The minimal useful statement is
\[
\boxed{Dq(m)[u]=q_m\ell_{m,u}\quad\text{in }L^1(\nu).}
\]

Prefer a Fréchet derivative to a collection of directional derivatives. In finite-dimensional mean coordinates, the useful quantitative version is
\[
\|q_{m+z}-q_m-q_m\ell_{m,z}\|_1=o(\|z\|),
\]
or, under the existing second-order regularity,
\[
\|q_{m+z}-q_m-q_m\ell_{m,z}\|_1\le C_m\|z\|^2
\]
locally.

#### Cheapest route

Under bounded-feature assumptions:

1. Use
   \[
   D\theta(m)[z]=\Sigma_m^{-1}z.
   \]
2. Write \(q_{m+z}/q_m\) as a normalized exponential tilt of \(Q_m\).
3. Apply the existing uniform tilt expansion, now with a finite-dimensional parameter increment.
4. Integrate the uniform remainder against the probability \(Q_m\).

This avoids developing an abstract differentiation theory for measure-valued `Measure.tilted`. Differentiate its **density**, represented in `Lp ℝ 1 ν`; the measure identity is a corollary.

A uniform estimate in \(z\) matters: directional differentiability alone is not the Fréchet statement.

#### The mixed Hessian has an especially good form

Set
\[
c_m(u,z)=\mathbb E_{Q_m}[(S-m)\ell_{m,u}\ell_{m,z}].
\]
Then
\[
D^2q(m)[u,z]
=q_m\left(
\ell_{m,u}\ell_{m,z}
-g_m(u,z)
-\ell_{m,c_m(u,z)}
\right).
\]
Equivalently, writing \(C_mf=\mathbb E_{Q_m}f\),
\[
\boxed{
D^2q(m)[u,z]
=q_m(I-C_m-B_m)(\ell_{m,u}\ell_{m,z}).
}
\]

This is more illuminating than a coordinate Hessian: **the second derivative along mean-affine directions is normal to both mass and moment constraints**. Indeed,
\[
\int D^2q(m)[u,z]\,d\nu=0,\qquad
\int S\,D^2q(m)[u,z]\,d\nu=0.
\]

For Lean, derive the first displayed Hessian by differentiating the score and inverse covariance; obtain the projection form algebraically.

**Priority:** the first derivative should come before the retraction theorem because it is its cleanest prerequisite. The mixed Hessian need not.

---

### B. The conditional variational formula

Let \(\mathcal G=\sigma(S)\), \(d=dD/d\nu\), and
\[
a=\mathbb E_\nu[d\mid\mathcal G],\qquad \rho=a\nu.
\]
Assume \(\nu\) is a probability measure and \(KL(D\|\nu)<\infty\). Then the minimal statement is
\[
\boxed{
L=KL(D\|\rho)
=\sup_{g\in L^\infty(\nu)}
\left\{
\mathbb E_Dg-
\mathbb E_D\log\mathbb E_\nu[e^g\mid\mathcal G]
\right\}.
}
\]
Here the tests are measurable on the original space, not merely \(\mathcal G\)-measurable. The latter would give only zero.

No regular conditional probabilities or standard-Borel assumption are needed.

#### Upper bound: normalize a conditional tilt

For bounded \(g\), put
\[
c_g=\mathbb E_\nu[e^g\mid\mathcal G],\qquad
T_g=\frac{e^g}{c_g}\rho.
\]
Conditional expectation shows that \(T_g\) is a probability measure with the same \(\mathcal G\)-marginal as \(D\). Moreover,
\[
KL(D\|T_g)
=L-\mathbb E_Dg+\mathbb E_D\log c_g.
\]
Nonnegativity proves the upper bound.

This exact identity is worth exposing as a lemma: it explains the variational formula, rather than merely proving it.

#### Lower bound: clip the density ratio, not Lean’s logarithm at zero

Define
\[
w=
\begin{cases}
d/a,&a>0,\\
1,&a=0.
\end{cases}
\]
Then \(\mathbb E_\nu[w\mid\mathcal G]=1\) a.e., and \(w=dD/d\rho\), \(\rho\)-a.e.

Use
\[
w_n=\min(e^n,\max(e^{-n},w)),\qquad g_n=\log w_n.
\]
The decisive estimate is
\[
w_n\le w+e^{-n},
\]
hence
\[
\log\mathbb E_\nu[e^{g_n}\mid\mathcal G]
\le \log(1+e^{-n}).
\]
Since
\[
\mathbb E_Dg_n\longrightarrow \mathbb E_D\log w=L,
\]
the variational values approach \(L\) from below in the required limiting sense. There is no need to prove a separate dominated-convergence theorem for the conditional log-normalizers.

#### Pitfalls

- In Lean, `Real.log 0 = 0`. Clipping `log w` directly is therefore wrong on \(\{w=0\}\) for this argument.
- Set \(w=1\) on \(\{a=0\}\); otherwise conditional normalization is needlessly awkward.
- Transfer \(\nu\)-a.e. identities to \(D\)-a.e. using absolute continuity.
- Establish \(\log w\in L^1(D)\) from the existing finite-KL chain rule before invoking dominated convergence.
- With only bounded tests, the supremum need not be attained.
- If conditional division/pullout lemmas are weak, localize first to \(\{a\ge 1/n\}\).

**Priority:** conceptually worthwhile, but independent of the retraction theorem. I would do it after the first-order retraction package, not before.

---

## 3. Exact identities worth adding

For the bridge formulas below, take
\[
D_s=d_s\nu,\qquad d_s=1+s(d-1),\qquad
m_s=m_0+sv,\qquad Q_s=Q_{m_s}.
\]
For the cheapest initial formal statements, assume \(0<c\le d\le C\) and a regular atlas path. Endpoint extensions can then use your existing machinery.

### A. Simultaneous mixture compensation for all three terms

This is the most valuable inexpensive addition.

Let \(a=\mathbb E_\nu[d\mid\mathcal G]\), \(a_s=1+s(a-1)\), and define
\[
k_{\rm full}(s)=\int\frac{(d-1)^2}{d_s}\,d\nu,
\qquad
k_{\rm obs}(s)=\int\frac{(a-1)^2}{a_s}\,d\nu.
\]
Then
\[
\begin{aligned}
\mathcal I_s
&=\int_0^s(s-u)\kappa(u)\,du,\\
L_s
&=\int_0^s(s-u)\bigl(k_{\rm full}(u)-k_{\rm obs}(u)\bigr)\,du,\\
R_s
&=\int_0^s(s-u)\bigl(k_{\rm obs}(u)-\kappa(u)\bigr)\,du.
\end{aligned}
\]
Thus the whole decomposition is a decomposition of accumulated curvature.

**Proof:** apply the full-simplex formula to \(d_s\) and \(a_s\), then subtract using
\[
L_s=KL(D_s\|\nu)-KL(a_s\nu\|\nu),\qquad
R_s=KL(a_s\nu\|\nu)-\mathcal I_s.
\]
No differentiation of \(L_s\) or \(R_s\) is needed.

There is also an exact Fisher-loss identity. With the mixture score
\[
h_s=\frac{d-1}{d_s},
\]
one has
\[
\mathbb E_{D_s}[h_s\mid\mathcal G]=\frac{a-1}{a_s},
\]
and therefore
\[
k_{\rm full}(s)-k_{\rm obs}(s)
=\mathbb E_{D_s}\!\left[
\left(h_s-\mathbb E_{D_s}[h_s\mid\mathcal G]\right)^2
\right].
\]

**Important:** do not infer \(k_{\rm obs}\ge\kappa\). Those curvatures use different laws. \(L_s\) is convex along this mixture, but \(R_s\) need not be.

---

### B. The observable defect’s second-order term

Define
\[
F_\phi(m)=\mathbb E_{Q_m}\phi,\qquad
\Delta_\phi(s)=\mathbb E_{D_s}\phi-F_\phi(m_s).
\]
Put
\[
\phi^\perp=\phi-\mathbb E_\nu\phi-B_0\phi,
\qquad
\ell=\ell_{m_0,v}.
\]
Then
\[
\boxed{
\Delta_\phi(s)
=s\!\left[
\mathbb E_D(I-B_0)\phi-\mathbb E_\nu(I-B_0)\phi
\right]
-\frac{s^2}{2}\mathbb E_\nu[\phi^\perp\ell^2]
+o(s^2).
}
\]

The linear mixture contribution has zero second derivative, so this follows directly from the atlas Hessian:
\[
\Delta_\phi''(0)=-D^2F_\phi(m_0)[v,v].
\]

The exact integral version is
\[
\Delta_\phi(s)
=s\Delta_\phi'(0)
-\int_0^s(s-u)\,
\mathbb E_{Q_u}\!\left[
(\phi-\mathbb E_{Q_u}\phi-B_u\phi)\ell_{m_u,v}^2
\right]du.
\]

This shows how first-order invisibility can still produce a second-order observable defect.

---

### C. Reverse atlas divergence, asymmetry, and skewness

On the atlas,
\[
KL(\nu\|Q_s)=\int_0^s u\,\kappa(u)\,du.
\]
At \(s=1\),
\[
\begin{aligned}
KL(Q_1\|\nu)+KL(\nu\|Q_1)
&=\int_0^1\kappa(s)\,ds,\\
KL(Q_1\|\nu)-KL(\nu\|Q_1)
&=\int_0^1(1-2s)\kappa(s)\,ds.
\end{aligned}
\]
The sum also equals
\[
\langle v,\theta_1-\theta_0\rangle.
\]

A particularly elegant refinement is
\[
\kappa'(s)=-\mathbb E_{Q_s}\ell_{m_s,v}^{\,3}.
\]
Integration by parts yields
\[
\boxed{
KL(Q_1\|\nu)-KL(\nu\|Q_1)
=\int_0^1s(1-s)\,
\mathbb E_{Q_s}\ell_{m_s,v}^{\,3}\,ds.
}
\]
Thus divergence asymmetry is accumulated directional skewness.

The full-simplex analogue is
\[
KL(D\|\nu)-KL(\nu\|D)
=\int_0^1s(1-s)\,\mathbb E_{D_s}h_s^3\,ds.
\]

The weighted-curvature formulas are immediate; the skewness formulas require the corresponding curvature derivative.

---

### D. Reverse divergence: an exact correction, not another Pythagorean theorem

Let \(Q=\Pi(M_D)=q\nu\). In a regime where all terms are finite,
\[
\boxed{
KL(\nu\|D)
=KL(\nu\|Q)+KL(Q\|D)
+\int(q-1)\log(d/q)\,d\nu.
}
\]
The correction is generally nonzero. Forward moment matching does not remove it.

There is, however, a genuine nonnegative reverse **conditional** decomposition:
\[
KL(\nu\|D)
=KL(\nu\|a\nu)
+\int\left(
\log a-\mathbb E_\nu[\log d\mid\mathcal G]
\right)d\nu.
\]
The second integrand is nonnegative by conditional Jensen. Notice the weighting: this is a reverse fibre term averaged under the reference marginal, not under the data marginal.

I would record these chiefly to prevent an incorrect “reverse Pythagoras” interpretation.

---

### E. Length versus energy

For the atlas path,
\[
\operatorname{Len}(Q_\bullet)
=\int_0^1\sqrt{\kappa(s)}\,ds,
\]
and
\[
\operatorname{Len}(Q_\bullet)^2
\le
KL(Q_1\|\nu)+KL(\nu\|Q_1).
\]
Equality holds exactly when the speed is constant a.e.

This is a useful corollary, not the missing geometric heart. The m-geodesic need not be a Levi–Civita Fisher–Rao geodesic, so distinguish:

- its Fisher length;
- Fisher–Rao endpoint distance;
- the weighted energies giving directional KL.

There is no universal equality identifying any one of these with directional KL.

---

## 4. Ranking by depth × feasibility

These are **conditional budget targets**, based on the seabed you describe, not line-count guarantees from an inspected repository. Keep each item as a separate module or theorem block.

| Rank | Addition | Why it earns its place | Target lines |
|---:|---|---|---:|
| 1 | Simultaneous curvature formulas for \(\mathcal I,L,R\) | Exact nonlinear upgrade of the quadratic shadow; mostly subtraction | 60–160 |
| 2 | Local retraction theorem and \(B,P\) compatibility | Strongest structural completion; depends on next item | 80–200 |
| 3 | \(L^1\) Fréchet derivative of reconstruction density | Essential analytic bridge to geometry | 150–350 |
| 4 | Fisher orthogonality iff Pythagorean equality | Very high conceptual return for little work | 30–100 |
| 5 | Conditional variational formula | Gives the fibre term an operational/dual meaning | 220–400 |
| 6 | Observable defect expansion and integral remainder | Directly explains response errors beyond first order | 60–180 |
| 7 | Mixed density Hessian in normal-projection form | Beautiful extrinsic curvature statement | 180–350 |
| 8 | Atlas reverse divergence and weighted asymmetry | Immediate completion of the directional picture | 40–120 |
| 9 | Conditional Fisher-loss identity | Explains exactly why fibre curvature is nonnegative | 120–300 |
| 10 | Skewness formula for KL asymmetry | Elegant and genuinely informative | 120–300 |
| 11 | Reverse-divergence correction and reverse conditional chain | Clarifies the limits of Pythagoras | 70–220 |
| 12 | Length–energy inequality | Useful, but not a structural advance | 30–100 |

For **dual connections**, I would initially formalise coordinate certificates rather than a general connection framework. In mean coordinates,
\[
\nabla^{(m)}_u z=Dz[u],\qquad
\nabla^{(e)}_u z=Dz[u]-c_m(u,z).
\]
Prove metric duality and the two geodesic equations directly. Each coordinate block might fit the budget once moment derivatives exist; a full bundled differential-geometric development should not be advertised as a 400-line task.

### Recommended execution order

1. Add the cheap orthogonality and simultaneous-curvature identities.
2. Prove the \(L^1\) derivative.
3. State and prove the local Fisher-orthogonal retraction theorem.
4. Add the conditional variational formula.
5. Finish with the normal Hessian, defect expansion, and skewness identity.

The resulting narrative is unusually coherent:

> **Globally, reconstruction separates information. Locally, it orthogonally separates scores. Along the bridge, those separations accumulate as curvature.**

That is the structural sentence I would want the finished map to justify.