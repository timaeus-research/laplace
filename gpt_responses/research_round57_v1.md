## Executive recommendation

The TV Peano theorem is the right flagship: you now have a second-order response theorem **for the law, simultaneously for every bounded observable**.

My ranking for the next work is:

1. **Finite-rate boundary completion of the atlas.** This genuinely enlarges the territory you can map; higher interior regularity does not.
2. **The reconstruction as a smooth, compact-uniformly controlled retraction of distribution space.** Combine (v) with (ii). This directly answers “how does changing the data distribution change the reconstructed law?”
3. **All-orders relative-uniform analyticity**, preferably with the additional statement that every derivative of order at least two is normal.
4. **The TV atlas curve and its length bound.** Beautiful and inexpensive once item 2 is available, but primarily a corollary rather than a new frontier.

One qualification should stay visible throughout:

> The atlas reaches the reconstruction of the data, not arbitrary \(D\) itself. The discrepancy between \(D\) and its reconstruction is the unresolved, moment-invisible part of the data—not a missing segment of the exponential-family atlas.

Below, I distinguish mathematical conclusions from estimated formalization costs. The line estimates are planning estimates, not repository-checked estimates.

---

# 1. Sanity check: the landed theorem is exactly the right one

Write \(Q=\Pi(M)\), and use the **full variation norm**
\[
\|\mu\|_{\mathrm{var}}=|\mu|(X).
\]
For probabilities, the usual statistical distance is
\[
d_{\mathrm{TV}}(P,Q)=\tfrac12\|P-Q\|_{\mathrm{var}}.
\]

Your expansion says
\[
q_{M+z}
=
q_M+q_M\ell_{M,z}
+\frac12q_MN_M(\ell_{M,z}^{\,2})
+o(\|z\|^2)
\]
in \(L^1(\nu)\), indeed in a stronger relative-uniform sense.

Consequently, the derivative and polarized second derivative are
\[
D\Pi_M[u]=Q\,\ell_{M,u},
\]
\[
\boxed{
D^2\Pi_M[u,v]
=
Q\,N_M(\ell_{M,u}\ell_{M,v}).
}
\]

Here, the second formula is genuinely the second Fréchet derivative once you establish the usual smoothness of the density map and \(\theta\). A second-order Peano expansion **alone**, abstractly, does not establish differentiability of the first derivative. In this setting that distinction is easy to close, but worth keeping straight in theorem names.

### Why the regression subtraction is indispensable

In natural coordinates, the second derivative contains
\[
\ell^2-\operatorname{Var}_Q(\ell).
\]
In mean coordinates, the curvature of \(\theta(M)\) contributes precisely the additional regression subtraction.

There is also a decisive invariant check:
\[
\int S\,d\Pi(M)=M.
\]
Therefore
\[
\int S\,d(D^2\Pi_M[u,v])=0.
\]
The centered square generally fails this test. Its covariance with \(S\) need not vanish. The normal projection passes it.

Thus
\[
\int d(D^2\Pi_M[u,v])=0,
\qquad
\int S\,d(D^2\Pi_M[u,v])=0.
\]
The second-order response changes neither mass nor the prescribed first-order moment displacement.

### What to call the stronger estimate

At a fixed base point, define
\[
\|f\|_{\infty,q_M}
=
\operatorname*{ess\,sup}_x\frac{|f(x)|}{q_M(x)}.
\]
Then your theorem is a **second-order Peano expansion in a weighted \(L^\infty\) norm**, or, more descriptively, a **relative-uniform second-order expansion of the density**.

Equivalently, it is an \(L^\infty(Q)\) expansion of the likelihood ratio
\[
\frac{q_{M+z}}{q_M}.
\]

There is no single universally standard special name beyond these. I would use “relative-uniform Peano expansion.”

It is genuinely stronger than TV because
\[
\int |f|\,d\nu\le \|f\|_{\infty,q_M}.
\]
The converse fails in general.

If the formal setup has actual everywhere-bounded representatives, your pointwise supremum statement is stronger than the essential-supremum formulation as well. Do not silently change “every \(x\)” to “almost every \(x\)” when packaging it.

---

# 2. First priority: complete the atlas at finite-rate boundary points

This is the deepest next step because it turns an interior differential calculus into an endpoint reconstruction theorem.

Let
\[
M_s=m_0+s\Delta,\qquad \Delta=M_*-m_0,
\qquad Q_s=\Pi(M_s),\quad s<1,
\]
where \(M_*\in\operatorname{relbd}K\) and
\[
I_*:=\operatorname{genRate}(M_*)<\infty.
\]
Set
\[
i(s)=\operatorname{genRate}(M_s).
\]
On the interior,
\[
i'(s)=-\langle\theta(M_s),\Delta\rangle,
\qquad
i''(s)=\kappa_s
=\langle\Delta,\Sigma_{M_s}^{-1}\Delta\rangle.
\]

The precise target is:

## Boundary atlas completion theorem

Under the standing bounded-feature and minimality assumptions:

1. There is a unique probability \(Q_*\ll\nu\) with
   \[
   E_{Q_*}S=M_*,
   \qquad
   \mathrm{KL}(Q_*\Vert\nu)=I_*,
   \]
   minimizing relative entropy under that moment constraint.

2. Along the radial atlas,
   \[
   Q_s\longrightarrow Q_*
   \quad\text{in TV as }s\uparrow1.
   \]

3. The endpoint information defect is exactly
   \[
   \boxed{
   \mathrm{KL}(Q_*\Vert Q_s)
   =
   I_*-i(s)-(1-s)i'(s)
   =
   \int_s^1(1-t)\kappa_t\,dt.
   }
   \]
   The last integral is improper.

4. For every bounded observable \(\varphi\),
   \[
   \begin{aligned}
   E_{Q_*}\varphi-E_\nu\varphi
   =
   \lim_{t\uparrow1}\Big[
   tE_\nu(\varphi\ell_0)
   +\int_0^t(t-s)
       E_{Q_s}\!\left[\varphi N_{M_s}(\ell_s^2)\right]\,ds
   \Big].
   \end{aligned}
   \]

5. In particular,
   \[
   d_{\mathrm{TV}}(Q_*,Q_s)
   \le
   \sqrt{\frac12\int_s^1(1-t)\kappa_t\,dt}.
   \]

This is substantially stronger than `BoundaryEscape`: natural parameters can diverge while the laws converge in TV.

## The scalar endpoint lemma is within reach

Convexity and lower semicontinuity give
\[
i(s)\longrightarrow I_*.
\]
Indeed, the convex upper bound is
\[
i(s)\le (1-s)i(0)+sI_*=sI_*,
\]
and lower semicontinuity supplies the reverse liminf inequality.

If an optimizer \(Q_*\) is already available, your mixture argument supplies the same upper bound:
\[
\operatorname{genRate}(M_s)
\le
\mathrm{KL}((1-s)\nu+sQ_*\Vert\nu)
\le sI_*.
\]

Since \(i\) has its minimum at \(0\), \(i'(s)\ge0\). Convexity also gives
\[
0\le (1-s)i'(s)
\le
2\left(i\!\left(\frac{1+s}{2}\right)-i(s)\right).
\]
Hence
\[
\boxed{(1-s)i'(s)\longrightarrow0.}
\]

This is the key endpoint fact. No asymptotic control of \(\theta\) itself is needed.

## A cleaner existence route: construct the endpoint by TV Cauchy convergence

You may not need an independent entropy-minimizer existence theorem.

For \(0\le s<t<1\), the interior exponential-family identity gives
\[
\mathrm{KL}(Q_t\Vert Q_s)
=
i(t)-i(s)-(t-s)i'(s).
\]
Since \(i'(s)\ge0\) and \(i(t)\le I_*\),
\[
0\le \mathrm{KL}(Q_t\Vert Q_s)\le I_*-i(s).
\]
Pinsker therefore shows that \(Q_s\) is TV-Cauchy at \(1\).

This suggests the following formal route:

1. **Construct the limit in \(L^1(\nu)\).**  
   The densities \(q_s\) are Cauchy. Completeness gives \(q_*\in L^1(\nu)\).

2. **Preserve positivity and normalization.**  
   Thus \(q_*\) defines \(Q_*\ll\nu\).

3. **Pass the moments to the limit.**  
   Boundedness of \(S\) gives \(E_{Q_*}S=M_*\).

4. **Pass entropy lower semicontinuously.**
   \[
   \mathrm{KL}(Q_*\Vert\nu)
   \le \liminf_{s\uparrow1}i(s)=I_*.
   \]

5. **Use the Gibbs/Fenchel lower bound.**  
   Any law with moment \(M_*\) satisfies
   \[
   \mathrm{KL}(P\Vert\nu)\ge\operatorname{genRate}(M_*).
   \]
   Hence equality holds for \(Q_*\).

This avoids proving weak compactness of entropy sublevels or a general constrained-minimizer theorem first.

An important logical distinction: **lower semicontinuity of `genRate` is not by itself an existence theorem for \(Q_*\)**. The Cauchy construction bridges that gap.

## Deriving the tail identity

For a finite-entropy law \(P\) with moment \(M_*\),
\[
\mathrm{KL}(P\Vert Q_s)
=
\mathrm{KL}(P\Vert\nu)
+\langle\theta(M_s),M_*\rangle
+\log Z(\theta(M_s)).
\]
For \(P=Q_*\), this becomes
\[
h(s):=\mathrm{KL}(Q_*\Vert Q_s)
=
I_*-i(s)-(1-s)i'(s).
\]
Now
\[
h'(s)=-(1-s)\kappa_s,
\qquad
h(s)\longrightarrow0.
\]
Integrate first on \([s,b]\), then let \(b\uparrow1\).

This also gives uniqueness: any other feasible law of entropy \(I_*\) has KL to \(Q_s\) tending to zero, so has the same TV limit.

## Your triangular reparametrization is correct

For fixed \(0<t<1\), use the interior endpoint \(M_t\). Its atlas is
\[
r\longmapsto M_{rt},
\]
with
\[
\ell'_r=t\ell_{rt}.
\]
Since \(N\) is linear,
\[
N_{M_{rt}}\big((\ell'_r)^2\big)
=t^2N_{M_{rt}}(\ell_{rt}^2).
\]
Then
\[
t^2\int_0^1(1-r)F(rt)\,dr
=
\int_0^t(t-u)F(u)\,du.
\]

The only real pitfalls are:

- Treat \(t=0\) separately if the substitution lemma needs \(t>0\).
- Define the original boundary-directed atlas only for \(s<1\).
- Do **not** replace the displayed limit by an absolutely convergent endpoint integral without another theorem.

TV convergence ensures that the triangular expressions converge because they equal \(E_{Q_t}\varphi-E_\nu\varphi\). It does **not** automatically imply
\[
\int_0^1(1-s)
\left|E_{Q_s}[\varphi N(\ell_s^2)]\right|\,ds<\infty.
\]
The weighted curvature integral controls information; it need not control the absolute acceleration of every observable.

## Why not `FixedNormalLimit`?

`FixedNormalLimit` is ideal for identifying a particular exposed-face limit when the tilt has the required asymptotic shape. A radial mean atlas need not have that shape; multiple scales or further facial reduction can occur.

The convex-information route is more intrinsic and more general. Use `FixedNormalLimit` afterward to identify \(Q_*\) explicitly in favorable cases.

### Estimated Lean cost

If a boundary optimizer and the required KL algebra already exist:

- convex endpoint lemmas: **100–200 lines**;
- boundary KL defect and improper tail: **150–300**;
- Pinsker convergence and triangular endpoint: **150–300**.

If constructing \(Q_*\) by \(L^1\)-Cauchy convergence:

- add roughly **400–900 lines**, largely depending on existing entropy lower-semicontinuity infrastructure.

The highest-risk library work is entropy lower semicontinuity, not the scalar convex analysis.

---

# 3. Second priority: the reconstruction map on distribution space

This is the most direct answer to the original user direction.

Let
\[
U=\operatorname{ri}K,\qquad
\mathcal P_U=\{D:E_DS\in U\},
\qquad
\mathcal R(D)=\Pi(E_DS).
\]

The right one-line statement is:

> **The reconstruction is a smooth retraction of the moment-interior probability simplex onto the exponential family, with uniform TV response bounds over compact moment sets; its first derivative transmits exactly the moment perturbation, and all higher-order responses are moment-normal.**

“Compact-uniformly TV-Lipschitz” is justified. “Globally TV-Lipschitz” is not justified by the current assumptions.

## Precise derivative statement

For a finite signed perturbation \(H\) of mass zero, put
\[
m(H)=\int S\,dH.
\]
Then
\[
D\mathcal R_D[H]
=
Q\,\ell_{M,m(H)},
\qquad M=E_DS,\quad Q=\Pi(M),
\]
and
\[
D^2\mathcal R_D[H_1,H_2]
=
Q\,N_M\!\left(
\ell_{M,m(H_1)}\ell_{M,m(H_2)}
\right).
\]

One clean formal domain is the relatively open subset
\[
\{\mu:\mu(X)=1,\ E_\mu S\in U\}
\]
of the Banach affine space of finite signed measures. The formula defines \(\mathcal R\) there even when \(\mu\) is not positive. Restrict afterward to probabilities. This avoids differentiating on a simplex with an awkward boundary.

Alternatively, prove the calculus for \(\Pi:U\to L^1(\nu)\) and compose with the bounded linear moment map. That is probably the cheaper seabed route.

## Retraction and differential splitting

For \(Q\) in the family,
\[
\mathcal R(Q)=Q.
\]
At such \(Q\), define
\[
L_QH=Q\,\ell_{M,m(H)}.
\]
Since
\[
m(Q\ell_{M,u})=u,
\]
we obtain
\[
L_Q^2=L_Q,
\qquad
\ker L_Q=\{H:H(X)=0,\ m(H)=0\}.
\]

Thus the derivative is an actual projection onto the score tangent space, along moment-invisible perturbations.

This is an especially good “space of responses” theorem:

- moment fibers identify which data changes are invisible;
- the derivative gives the visible response;
- the normal Hessian describes the bending of the reconstructed law;
- the residual \(D-\mathcal R(D)\) belongs to the same moment-zero linear space.

Do not call \(L_Q\) an orthogonal projection in TV. Orthogonality belongs to the appropriate \(L^2(Q)\) density representation.

## Compact-uniform Lipschitz estimate

Take compact \(C\subset U\), and let \(H\subset U\) be a compact convex neighborhood of \(\operatorname{conv}C\). Work in the affine direction space \(\mathbb V\).

Put
\[
\Lambda_H=\sup_{M\in H}\|\Sigma_M^{-1}\|_{\mathrm{op}}.
\]
Then
\[
\begin{aligned}
\|D\Pi_M[u]\|_{\mathrm{var}}
&=E_Q|\ell_{M,u}|\\
&\le \sqrt{E_Q\ell_{M,u}^2}\\
&=\sqrt{\langle u,\Sigma_M^{-1}u\rangle}\\
&\le \sqrt{\Lambda_H}\,\|u\|.
\end{aligned}
\]
Integrating along the segment gives
\[
\boxed{
\|\Pi(M')-\Pi(M)\|_{\mathrm{var}}
\le \sqrt{\Lambda_H}\,\|M'-M\|.
}
\]

If \(L=\sup_x\|S(x)-c\|\) for any fixed \(c\), then for probabilities
\[
\|E_DS-E_{D'}S\|
\le L\|D-D'\|_{\mathrm{var}}.
\]
Therefore
\[
\boxed{
d_{\mathrm{TV}}(\mathcal R(D),\mathcal R(D'))
\le
L\sqrt{\Lambda_H}\,d_{\mathrm{TV}}(D,D')
}
\]
whenever their moments lie in \(C\).

The convex-neighborhood step matters: the segment between points of \(C\) need not remain in \(C\).

## Strengthen compact-uniformity to the relative-uniform norm

Given your explicit proof, I would target more than the proposed TV statement.

For every compact \(C\subset U\), prove that there are \(\rho_C>0\) and \(\omega_C(r)\to0\) such that, for \(M\in C\), \(0<\|z\|\le r\le\rho_C\),
\[
\boxed{
\sup_x
\frac{
\left|q_{M+z}(x)
-q_M(x)\left(1+\ell_{M,z}(x)
+\frac12N_M(\ell_{M,z}^2)(x)\right)\right|
}{
q_M(x)\|z\|^2
}
\le\omega_C(r).
}
\]

This immediately supplies your desired compact-uniform TV theorem.

### Lemma-level proof route

1. **Compact thickening.**  
   Choose a compact neighborhood \(H\subset U\) of \(C\), allowing all sufficiently short segments.

2. **Uniform coefficient bounds.**  
   Bound \(R_M\), \(D^2\theta(M)\), the covariance/regression operators, and the constants in the landed algebra uniformly on \(H\).

3. **Uniform Peano for \(\theta\).**  
   Prove
   \[
   \sup_{M\in C,\ 0<\|z\|\le r}
   \frac{\|\theta(M+z)-\theta(M)-D\theta_Mz
   -\frac12D^2\theta_M[z,z]\|}{\|z\|^2}
   \longrightarrow0.
   \]
   A modulus of continuity of \(D^2\theta\) on \(H\) gives a bound
   \[
   \|v_M(z)\|
   \le \tfrac12\omega_{D^2\theta,H}(\|z\|)\|z\|^2.
   \]

4. **Reuse the existing explicit density algebra.**  
   Choose the radius using uniform upper bounds rather than point-dependent norms. Your remainder then has the form
   \[
   \frac{\phi_M(z)}{\|z\|^2}
   \le
   A\,\omega_{D^2\theta,H}(\|z\|)
   +B\|z\|+C\|z\|^2.
   \]

5. **Integrate only at the end.**

This is a very favorable use of the explicit route: the difficult algebra has already been paid for.

### Which Taylor machinery?

I would not introduce `HasFTaylorSeriesUpToOn` merely to obtain this result.

The reusable theorem you want is:

> A \(C^2\) map between finite-dimensional/Banach spaces has a second-order Peano remainder uniformly over compact subsets of its open domain.

Use `Convex.taylor_approx_two_segment` if its actual hypotheses and codomain support fit this modulus-of-continuity proof. I would check that locally rather than commit to the name from memory. Otherwise extend the generic Peano lemma you already have.

### Estimated Lean cost

- generic compact-uniform Peano: **200–400 lines**;
- uniformizing `DensityPeano`: **200–450**;
- \(L^1\)-valued derivative packaging and Lipschitz estimate: **150–350**;
- moment-map composition, retraction, and splitting: **100–250**.

Rough total: **650–1450 lines**, with considerable savings if Banach-valued calculus is already packaged.

---

# 4. All orders: true, beautiful, but not the next obstruction

Yes: under your bounded-feature and nondegeneracy hypotheses,
\[
M\longmapsto q_M
\]
is locally real-analytic into \(L^\infty(\nu)\), hence into \(L^1(\nu)\) and TV.

At a fixed base \(M_0\), it is also analytic in
\[
\|f\|_{\infty,q_{M_0}}.
\]
Because bounded features make \(q_{M_0}\) bounded above and bounded away from zero, this is an equivalent \(L^\infty\) norm. The equivalence constants need not remain bounded near the boundary.

Do not describe a moving-base norm as a single Banach target without trivializing it at a fixed reference density.

## Clean all-orders statement

Locally around each \(M\), there are symmetric multilinear coefficient functions \(A_{M,n}\) such that
\[
\frac{q_{M+z}}{q_M}
=
\sum_{n=0}^{\infty}\frac1{n!}
A_{M,n}[z,\ldots,z],
\]
with convergence in relative-uniform norm, where
\[
A_{M,0}=1,\qquad
A_{M,1}[u]=\ell_{M,u},
\]
\[
A_{M,2}[u,v]=N_M(\ell_{M,u}\ell_{M,v}).
\]

The particularly beautiful addition is
\[
E_QA_{M,n}=0\quad(n\ge1),
\]
\[
E_Q[S\,A_{M,1}[u]]=u,
\qquad
E_Q[S\,A_{M,n}]=0\quad(n\ge2).
\]

Thus:

> **Every response of order at least two is normal to the mass-and-feature constraints.**

That is the all-orders extension of your normal Hessian, and more informative than analyticity alone.

## Best proof architecture

Use the Banach algebra \(L^\infty\):

1. \(\eta\mapsto-\langle\eta,S\rangle\) is bounded linear.
2. The exponential is analytic.
3. Integration is bounded linear.
4. Inversion is analytic near a nonzero scalar.
5. Hence the normalized density is analytic in natural coordinates.
6. Compose with the analytic inverse moment chart.

The explicit route can certainly be iterated. But it must control the normalized Taylor coefficients, not merely truncate the exponential numerator. For analyticity, arbitrary fixed-order constants \(C_n\) are insufficient: you need growth control ensuring a positive convergence radius.

If generic Banach-analytic infrastructure is awkward in Lean, a convergent majorant-series proof is preferable to separately formalizing order \(3\), order \(4\), and so on.

---

# 5. The TV curve: a valuable corollary, with sharp conventions

Along the atlas,
\[
Q'_s=Q_s\ell_s,\qquad
Q''_s=Q_sN_{M_s}(\ell_s^2).
\]
The pointwise formula you already have is the expanded version of the latter.

The natural path-length bound is
\[
\|Q_s-Q_t\|_{\mathrm{var}}
\le \int_t^sE_{Q_u}|\ell_u|\,du
\le \int_t^s\sqrt{\kappa_u}\,du,
\]
or
\[
\boxed{
d_{\mathrm{TV}}(Q_s,Q_t)
\le \frac12\int_t^s\sqrt{\kappa_u}\,du.
}
\]

This is obtained directly from the derivative and Cauchy–Schwarz, not from Pinsker. Pinsker gives a complementary information-based chord bound.

One useful caution: finite
\[
\int_0^1(1-s)\kappa_s\,ds
\]
does not by itself imply finite
\[
\int_0^1\sqrt{\kappa_s}\,ds.
\]
The information endpoint theorem can therefore establish TV convergence without establishing finite Fisher length.

This is another reason to prioritize the boundary information route over the path-length route.

---

# 6. How the whole programme becomes one theorem

I would package the eventual result as a **Response Atlas and Reconstruction Theorem** with four layers:

### A. Interior response geometry
\[
D\Pi_M[u]=Q\ell_u,\qquad
D^2\Pi_M[u,v]=QN(\ell_u\ell_v),
\]
with compact-uniform relative remainders—or convergent all-orders expansions.

### B. Dependence on the data law
\[
D\longmapsto E_DS\longmapsto\Pi(E_DS)
\]
is a compact-uniformly TV-Lipschitz smooth retraction, with moment fibers precisely describing invisible data changes.

### C. Radial transport of laws, observables, and information
The same atlas controls:

- the law in TV;
- every bounded observable;
- Fisher speed;
- integrated information gain;
- the normal acceleration/accounting term.

### D. Finite-rate boundary completion
The interior atlas extends radially in TV to the entropy-minimizing boundary law, with the exact information-tail certificate
\[
\mathrm{KL}(Q_*\Vert Q_s)
=
\int_s^1(1-t)\kappa_t\,dt.
\]

That endpoint extension is **radial**. Do not silently promote it to continuity under every approach to every boundary point.

The deepest remaining move is therefore not another isolated derivative. It is:

> **Turn the atlas into a completed reconstruction map, explain its fibers on data space, and let the information tail certify arrival at finite-rate endpoints.**

That joins the local normal geometry, the global information accounting, and the actual dependence on the data distribution into one mathematical object.