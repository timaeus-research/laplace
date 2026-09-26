The main change since round 53 is that **the local geometry is no longer missing a new idea; it is missing the right generality and packaging**. The global chart now lets you state everything intrinsically in response coordinates.

Two cautions matter:

1. Polarising second directional derivatives does **not by itself** establish a second Fréchet derivative.
2. The normal component of the density acceleration is **twice** the genuine Fisher–Rao second fundamental form.

There is also a surprisingly strong boundary theorem available from boundedness alone.

## 1. Re-ranking

My ranking by depth × feasibility is:

| Rank | Target | Assessment |
|---|---|---|
| **1** | **(a) Response-coordinate Hessian and observable defect** | The missing local heart. Most ingredients are present; it completes the passage from one atlas ray to the whole response manifold. |
| **2** | **(f) Universal boundary blow-up from a supporting normal** | Stronger and easier than it initially looks: along a straight segment to the relative boundary, \(\kappa(s)\to\infty\), with a universal \(1/(1-s)\) lower bound. |
| **3** | **(d) Fisher normal geometry / second fundamental form** | Very high conceptual value. The algebraic normal-acceleration theorem is inexpensive after (a); the genuine Riemannian statement needs the factor \(1/2\). |
| **4** | **(c) Conditional variational formula for general densities** | A clean extended-valued completion of the information theory. Clipping has a particularly useful one-sided normalization estimate. |
| **5** | **(e) Fisher–Rao distance and great circle** | Beautiful synthesis of the path results, but sphere geometry and absolutely continuous path machinery may dominate the proof. |
| **6** | **(b) Unbounded bridge curvature split** | Important, but distinguish pointwise curvature identities from differentiating potentially infinite entropy. The former should precede the latter. |

The packaging in (g) should happen **alongside ranks 1–3**, not as another distant target.

---

## 2. Top target: the response Hessian is the normal projection of a product of scores

Here is the clean statement, avoiding any dependence on the sign convention for \(\beta\).

Fix \(M\in\operatorname{ri}K\), and write
\[
Q=Q_M=\Pi(M),\qquad X=S-M,\qquad
A_M=(\Sigma_M|_{\mathbb V})^{-1}.
\]
For \(u\in\mathbb V\), define the response score
\[
\ell_{M,u}=\langle A_Mu,X\rangle .
\]
Thus
\[
Dq_M[u]=q_M\ell_{M,u}.
\]

Define, initially for bounded scalar observables,
\[
P_{0,M}f=E_Qf,
\qquad
B_Mf=\left\langle A_M E_Q[Xf],X\right\rangle,
\qquad
N_M=I-P_{0,M}-B_M.
\]
Here \(B_M\) is the orthogonal projection onto the response tangent scores, and \(N_M\) removes both the constant and tangent components.

### Precise Hessian statement

As a map from the relatively open response domain to \(L^1(\nu)\),
\[
M\longmapsto q_M=\frac{dQ_M}{d\nu}
\]
is twice Fréchet differentiable, with
\[
\boxed{
D^2q_M[u,z]
=
q_M\,N_M(\ell_{M,u}\ell_{M,z}).
}
\]

Expanded:
\[
\boxed{
\begin{aligned}
D^2q_M[u,z]=q_M\Big(
&\ell_{M,u}\ell_{M,z}
-\langle u,A_Mz\rangle\\
&-\left\langle
A_M E_Q[X\ell_{M,u}\ell_{M,z}],X
\right\rangle
\Big).
\end{aligned}}
\]

This simultaneously gives:

- symmetry and bilinearity;
- the existing atlas diagonal;
- zero mass acceleration;
- zero response acceleration;
- the normal-acceleration interpretation.

In particular,
\[
\int D^2q_M[u,z]\,d\nu=0,
\qquad
\int S_jD^2q_M[u,z]\,d\nu=0.
\]

The attractive point is that the formula is not merely “a second derivative with correction terms.” It says:

> **In affine response coordinates, all second-order density acceleration lies normal to the exponential family.**

Here “normal” refers to the score obtained by dividing the density acceleration by \(q_M\). The genuinely Fisher–Rao qualification comes below.

### Does polarisation avoid the inverse-chart second derivative?

**It avoids having to begin with it, but it does not eliminate the regularity obligation.**

If you establish the diagonal formula along every interior straight line, you can polarise its right-hand side:
\[
H_M[u,z]
=\tfrac12\bigl(H_M[u+z,u+z]-H_M[u,u]-H_M[z,z]\bigr).
\]
That produces the correct candidate. But existence of second directional derivatives, even with many good properties, is not by itself the desired Fréchet theorem.

The most economical rigorous route is probably:

1. establish a Fréchet derivative for \(M\mapsto\Sigma_M\);
2. differentiate \(M\mapsto A_M\);
3. differentiate the already-known first derivative \(Dq_M[u]=q_M\ell_{M,u}\).

This proves differentiability of the derivative map directly. There is no need first to build a separate, abstract second-order inverse-function theorem.

### Lemma-level proof plan

#### Lemma 1: derivative of bounded expectations in response coordinates

For fixed bounded \(F\),
\[
D_M(E_{Q_M}F)[u]
=
E_{Q_M}[F\ell_{M,u}].
\]

This is the existing first-order chart calculus composed with bounded exponential tilting.

#### Lemma 2: response derivative of covariance

For \(v,w\in\mathbb V\),
\[
\left\langle v,D\Sigma_M[u]w\right\rangle
=
E_Q[
\langle v,X\rangle
\langle w,X\rangle
\ell_{M,u}
].
\]

The derivatives of the centering terms disappear because \(E_QX=0\).

This is the Fréchet version of the landed atlas covariance derivative. The finite-dimensional basis assembly should transfer almost verbatim.

#### Lemma 3: derivative of inverse covariance

\[
DA_M[u]=-A_M(D\Sigma_M[u])A_M.
\]

This is exactly the existing inverse-operator machinery, now with a response-space input instead of a scalar path input.

#### Lemma 4: derivative of the score

For fixed \(z\),
\[
D_M\ell_{M,z}[u]
=
-\langle u,A_Mz\rangle
-\left\langle
A_ME_Q[X\ell_{M,u}\ell_{M,z}],X
\right\rangle.
\]

There are precisely two contributions:

- changing the inverse covariance;
- changing \(S-M\).

#### Lemma 5: differentiate the density derivative

Apply the product rule to \(q_M\ell_{M,z}\):
\[
D_M(q_M\ell_{M,z})[u]
=
q_M\ell_{M,u}\ell_{M,z}
+
q_MD_M\ell_{M,z}[u].
\]

For bounded features, all relevant densities and scores are locally uniformly bounded in parameter space. This supplies the \(L^1\) domination needed for the Banach-valued statement.

#### Lemma 6: projection packaging

Prove
\[
E_Q[\ell_{M,u}\ell_{M,z}]=\langle u,A_Mz\rangle
\]
and identify the remaining linear-score term with
\(B_M(\ell_{M,u}\ell_{M,z})\).

That turns the expanded formula into the structural formula \(q_MN_M(\ell_u\ell_z)\).

### Observable-defect corollary

To make the claimed formula precise, take the exponential perturbation
\[
D_t=\frac{e^{th}}{E_Qe^{th}}Q,
\qquad
M(t)=E_{D_t}S,
\]
and define
\[
\Delta_f(t)=E_{D_t}f-E_{\Pi(M(t))}f.
\]
For a clean first version, assume \(f,h\) bounded. Put
\[
\bar h=h-E_Qh,
\qquad
r_{f,M}=N_Mf.
\]
Then
\[
\boxed{\Delta_f'(0)=E_Q[r_{f,M}\bar h]}
\]
and
\[
\boxed{
\Delta_f''(0)
=
E_Q\!\left[
r_{f,M}\bigl(\bar h^2-(B_Mh)^2\bigr)
\right].
}
\]

The proof is short once the Hessian exists:

- \(M'(0)=E_Q[Xh]\), so its reconstruction score is \(B_Mh\);
- \(M''(0)=E_Q[X\bar h^2]\);
- use the second-order chain rule for \(q_{M(t)}\);
- cancel the constant and tangent components against \(r_{f,M}\).

The exponential perturbation matters: for an affine density perturbation, the second-order formula is different.

### Estimated size

Without inspecting the repository, my rough estimate is:

- generic response covariance and inverse derivative: **120–220 lines**;
- score derivative and \(L^1\) Hessian: **150–280 lines**;
- projection identities and observable defect: **100–180 lines**.

So approximately **370–680 lines**, assuming the existing derivative lemmas expose usable interfaces. Generalising the path statements first may reduce duplication, but I would not rebase the entire construction at \(Q_{M_0}\) unless the APIs make that especially cheap.

---

## 3. The boundary target is stronger than “perhaps \(\kappa\to\infty\)”

There is a universal theorem here.

Let
\[
M_s=M_0+s\Delta,\qquad \Delta=M_*-M_0,
\]
where \(M_0\in\operatorname{ri}K\) and
\(M_*\in\partial_{\mathrm{rel}}K\). Choose a nonzero relative supporting normal \(n\in\mathbb V\):
\[
\langle n,x\rangle\le b=\langle n,M_*\rangle
\quad(x\in K).
\]
Set
\[
Y=b-\langle n,S\rangle,\qquad
\delta=b-\langle n,M_0\rangle>0.
\]
Bounded features give \(0\le Y\le R\) almost everywhere, for some \(R>0\).

Under \(Q_s\),
\[
E_{Q_s}Y=(1-s)\delta,
\]
and therefore
\[
\operatorname{Var}_{Q_s}(Y)
\le R(1-s)\delta.
\]

Covariance Cauchy–Schwarz gives
\[
\langle n,\Delta\rangle^2
\le
\langle n,\Sigma_sn\rangle
\langle\Delta,\Sigma_s^{-1}\Delta\rangle.
\]
Since \(\langle n,\Delta\rangle=\delta\),
\[
\boxed{
\kappa(s)\ge \frac{\delta}{R(1-s)}.
}
\]

Consequently:
\[
\boxed{\kappa(s)\longrightarrow+\infty,}
\qquad
\boxed{\int_0^1\kappa(s)\,ds=+\infty.}
\]

Moreover, because
\[
\theta'(s)=-\Sigma_s^{-1}\Delta,
\]
we have
\[
-\langle\theta'(s),\Delta\rangle=\kappa(s),
\]
hence
\[
\boxed{
-\langle\theta(s)-\theta(0),\Delta\rangle
\ge
\frac{\delta}{R}\log\frac1{1-s}.
}
\]
This strengthens qualitative parameter escape to a quantitative logarithmic lower bound. The natural-coordinate velocity also satisfies
\[
\|\theta'(s)\|
\ge \frac{\delta}{R\|\Delta\|(1-s)}.
\]

This looks like a **150–300 line** target if supporting normals and interval integration are already convenient.

### What is not universal

There is no single sharp blow-up rate beyond such lower bounds.

- A two-point feature approaching a vertex has
  \(\kappa(s)\asymp(1-s)^{-1}\) and logarithmic natural-parameter growth.
- A uniform base law on \([0,1]\), tilted toward \(0\), has
  \(\kappa(s)\asymp(1-s)^{-2}\) and natural-parameter growth of order \((1-s)^{-1}\).

Thus the right next boundary theorem is a **universal lower bound**, followed later by tail-dependent asymptotics.

---

## 4. The genuine second fundamental form: include the factor \(1/2\)

Work in the centered score Hilbert space
\[
H_Q=\{h\in L^2(Q):E_Qh=0\}.
\]
The tangent and normal spaces are
\[
T_Q=\{\ell_{M,u}:u\in\mathbb V\},
\qquad
\mathcal N_Q=H_Q\cap T_Q^\perp.
\]

On all of \(L^2(Q)\), the projection onto this normal space is \(N_M\). It is important to remove constants: the orthogonal complement of \(T_Q\) in all of \(L^2(Q)\) contains constants, which are not simplex tangent scores.

There are two distinct statements.

### Density-acceleration theorem

For an affine response line,
\[
\boxed{\frac{q''}{q}=N_M(\ell^2).}
\]

This already follows from the landed diagonal formula after projection packaging. **It does not need the full polarised Hessian.**

### Fisher–Rao second fundamental form

For the Fisher metric \(E_Q[hk]\),
\[
\boxed{
\mathrm{II}^{\mathrm{FR}}_Q(\ell_{M,u},\ell_{M,z})
=
\frac12N_M(\ell_{M,u}\ell_{M,z}).
}
\]

The cleanest derivation uses the isometric square-root embedding
\[
q\longmapsto 2\sqrt q
\]
into the radius-\(2\) sphere of \(L^2(\nu)\). Differentiating twice introduces the correction
\(-\tfrac12\ell_u\ell_z\); the sphere connection removes the constant component. Normal projection leaves exactly \(\tfrac12N_M(\ell_u\ell_z)\).

I would land this in two stages:

1. the **normal density-acceleration identity**, using no Riemannian infrastructure;
2. a **square-root normal-acceleration identity**, which justifies calling the resulting bilinear form the Fisher–Rao second fundamental form.

That is cleaner than constructing an infinite-dimensional manifold of all positive densities merely to state this theorem.

---

## 5. General densities: two useful distinctions

### Conditional variational formula

Let \(\mathcal G=\sigma(S)\),
\[
a=E_\nu[d\mid\mathcal G],\qquad D^\uparrow=a\nu.
\]
The robust extended-valued statement is
\[
\boxed{
\mathrm{KL}(D\|D^\uparrow)
=
\sup_{\varphi\ \mathrm{bounded}}
\left\{
E_D\varphi-
E_D\log E_\nu[e^\varphi\mid\mathcal G]
\right\}.
}
\]

No subtraction of infinite entropies is needed.

For the lower bound, set \(r=d/a\) on the relevant support and
\[
\varphi_n=\operatorname{clip}_{[-n,n]}(\log r).
\]
The useful estimate is
\[
e^{\varphi_n}\le r+e^{-n}.
\]
Since \(E_\nu[r\mid\mathcal G]=1\) where \(a>0\),
\[
E_\nu[e^{\varphi_n}\mid\mathcal G]\le1+e^{-n}.
\]
Thus the normalization penalty has an upper bound tending to zero. The clipped log expectations converge to the extended KL, using the standard integrable bound on its negative part.

That estimate makes this target considerably more attractive than a generic “pass to the limit through conditional log-normalizers” proof.

### Unbounded bridge curvature

For the affine bridge,
\[
d_s=1-s+sd,
\qquad
k_d(s)=\int\frac{(d-1)^2}{d_s}\,d\nu,
\]
arbitrary probability densities already satisfy, for \(0<s<1\),
\[
k_d(s)\le
\frac{E_\nu|d-1|}{\min(s,1-s)}
\le \frac2{\min(s,1-s)}.
\]

So interior Fisher identities can remain finite when
\(\mathrm{KL}(D\|\nu)=+\infty\).

**Do not express this automatically as a classical second derivative of**
\(s\mapsto\mathrm{KL}(D_s\|\nu)\): that function may be identically infinite for \(s>0\).

A finite replacement is the weighted Jensen–Shannon quantity
\[
J(s)=(1-s)\mathrm{KL}(\nu\|D_s)
+s\mathrm{KL}(D\|D_s),
\]
for which
\[
J''(s)=-k_d(s).
\]

For endpoint identities, nonnegative kernels and extended integrals are the right language:
\[
\int_0^1(1-s)k_d(s)\,ds=\mathrm{KL}(D\|\nu),
\]
\[
\int_0^1s\,k_d(s)\,ds=\mathrm{KL}(\nu\|D).
\]

This suggests splitting (b) into an inexpensive **interior curvature extension** and a more delicate **extended-valued decomposition theorem**.

---

## 6. Fisher–Rao: compare endpoints before comparing paths

For probability densities \(p,q\),
\[
d_{\mathrm{FR}}(p,q)
=
2\arccos\int\sqrt{pq}\,d\nu.
\]
Every suitably absolutely continuous Fisher path between those endpoints has length at least this quantity, with equality for the square-root great circle.

This is the right completion of the length–energy results. But it is a common numerical lower bound only for paths with the **same endpoints**.

Your constructions naturally reach different objects:

- \(\Pi(M)\);
- \(D^\uparrow\);
- \(D\).

One should therefore present endpoint-labelled bounds rather than suggest all paths have the same Fisher–Rao lower bound.

Conditioning does give
\[
\int\sqrt a\,d\nu\ge\int\sqrt d\,d\nu,
\]
hence
\[
d_{\mathrm{FR}}(\nu,D^\uparrow)
\le d_{\mathrm{FR}}(\nu,D).
\]
But entropy minimisation does **not** automatically make \(\Pi\) a Fisher contraction or a nearest-point projection for Fisher–Rao distance. Avoid building such an ordering into the synthesis.

---

## 7. Repackage the programme as one structure theorem

I would give it one mathematical headline:

> **The response map is a global entropy-minimising chart, whose differential is Fisher duality and whose second differential is normal score multiplication.**

Then organise the formal results into five blocks.

### I. Global reconstruction

For every \(M\in\operatorname{ri}K\):

- unique gauge-fixed natural coordinate;
- \(E_{\Pi(M)}S=M\);
- unique entropy minimiser in the response fibre;
- continuous, differentiable global chart and inverse.

### II. Differential duality

\[
D\theta_M[u]=-A_Mu,
\qquad
Dq_M[u]=q_M\ell_{M,u},
\]
\[
g_M(u,z)=E_{Q_M}[\ell_{M,u}\ell_{M,z}]
=\langle u,A_Mz\rangle.
\]

This identifies the inverse covariance simultaneously as:

- inverse-chart derivative;
- response-space Fisher metric;
- Hessian of the minimum-information function.

### III. Normal geometry and observable response

\[
D^2q_M[u,z]=q_MN_M(\ell_{M,u}\ell_{M,z}),
\]
together with the first- and second-order observable-defect formulas.

This explains what reconstruction retains and what it discards.

### IV. Pathwise information accounting

Package the atlas, bridge, lift, and exponential interpolation results with:

- their endpoints;
- their velocities and Fisher energies;
- their KL identities;
- the specific contractions that are actually proved.

Keep the distinction between energy identities and length inequalities visible.

### V. Boundary obstruction

Along every straight interior-to-boundary response segment:

- covariance degenerates in a supporting direction;
- inverse-covariance curvature diverges;
- natural coordinates escape quantitatively.

In Lean, I would not make this one enormous conjunction. Use a small collection of structures or namespaces sharing \(Q_M,\Sigma_M,A_M,\ell_{M,u},B_M,N_M\), with a concise umbrella theorem.

**Recommended next sequence:** polarised response Hessian → observable defect → normal-geometry packaging, while landing the supporting-normal boundary bound as a short parallel development. Together, these turn the existing atlas calculations into a genuine geometry of the whole response manifold.