The programme is now close to having a coherent geometric statement, not just a collection of response formulas. I would organize it around:

> **The posterior response map equips the data manifold with an exact, possibly degenerate Hessian geometry. Its large-temperature geometry resolves into minimizer motion, posterior-shape change, and singular crossover profiles.**

Two corrections are important at the outset:

1. With your convention \(g_t=t^2\operatorname{Cov}_t\), the regular limit is **\(g_t/t\to G\)**, not \(t g_t\to G\). The quoted description of `responseForm_asymptotic` needs a normalization audit.
2. The thermodynamic-length coefficient is **\(\sqrt{\lambda}\)**. Thus the RLCT is the **square** of the logarithmic growth coefficient:
   \[
   \lambda=\left(\lim_{t\to\infty}\frac{\ell(t)}{\log t}\right)^2.
   \]

There is also a useful shortcut for A(iii): **uniform domination is not necessary on an affine mixture line**. Your exact covariance identity supplies the uniform integrability needed for length convergence.

## 1. Re-ranking: what I would prove next

I would split several candidates rather than rank them as indivisible packages.

| Priority | Target | Reason |
|---|---|---|
| 1 | **C, plus strict monotonicity from F** | Gives the global exact organizing object: a convex potential, its Hessian, and identifiable response coordinates. |
| 2 | **A(iii), using the no-domination route below; B’s invariant identity alongside it** | Turns pointwise response asymptotics into a genuine macroscopic distance law with surprisingly little new analysis. |
| 3 | **Corrected E: wall-window thermodynamic length equals profile length** | An unusually clean bridge between exact response geometry and singular blow-up geometry. Much of it is already available. |
| 4 | **A(i), then the regular common-minimizer shape metric** | Explains what remains after the leading minimizer-motion metric vanishes. This is essential for mapping more than just learned minimizers. |
| 5 | **D first on compact subsets of one stratum/chart** | The major infrastructure theorem. Avoid initially demanding uniformity through changing dominant faces or wall intersections. |
| 6 | **The concrete proper-prior instance of A(ii)** | Valuable validation and a complete worked example, but less structurally new. |
| 7 | **The moments theorem from F** | Cheap and worthwhile, but principally an identification theorem for a scalar statistic, not for the full response map. |

Full D remains the largest long-term analytical priority. But C, A(iii), and the wall-length theorem would make its eventual purpose much clearer.

### The missing organizing object: a filtered response geometry

The three scales in A are important, but not exhaustive. Even in regular models, the leading metric forgets all data variations that preserve the minimizer. Those variations can still change posterior shape.

Thus I would explicitly organize the tangent space by successive kernels:

- exact null directions: loss changes only by a constant;
- directions invisible to minimizer motion;
- among those, directions invisible to quadratic posterior shape;
- higher-order and singular responses.

This is more informative than assigning one metric to the entire manifold and declaring its degeneracies uninteresting.

---

## 2. A candidate for THE theorem of the programme

Let \(Q\) be a finite-dimensional affine family of data distributions, and write
\[
R_v(w)=D_qL_q(w)[v].
\]
For \(t>0\), define
\[
g_{t,q}(u,v)
=
t^2\operatorname{Cov}_{\rho_{t,q}}(R_u,R_v).
\]

The exact structural statement should be:

> **Posterior response geometry.**  
> On an affine data family with suitable exponential integrability, the posterior map
> \[
> \Phi_t:q\longmapsto\rho_{t,q}
> \]
> pulls back the Fisher–Rao metric to
> \[
> g_t=\operatorname{Hess}_q\log Z_t.
> \]
> Its nullspace consists precisely of data directions whose loss contrast is constant almost everywhere under the prior. On the identifiable quotient, the posterior family is a Hessian statistical manifold, with loss expectations as dual coordinates.

Indeed,
\[
D_v\log\rho_{t,q}
=
-t\bigl(R_v-\langle R_v\rangle_{t,q}\bigr),
\]
which simultaneously gives
\[
D_v\langle\phi\rangle_{t,q}
=-t\operatorname{Cov}_{t,q}(\phi,R_v),
\]
and
\[
|D_v\langle\phi\rangle_{t,q}|
\le
\sqrt{\operatorname{Var}_{t,q}(\phi)}
\sqrt{g_{t,q}(v,v)}.
\]

This is an exact statement about **all expectation responses**, not just a selected observable.

Its regular asymptotic continuation is:

> **Regular geometric limit.**  
> On a compact regular region \(K\subset Q\), under uniform Laplace hypotheses,
> \[
> \sup_{q\in K}\left\|\frac{g_{t,q}}t-G_q\right\|\longrightarrow0,
> \qquad
> G_q(u,v)=H_q\bigl(Dm_q[u],Dm_q[v]\bigr),
> \]
> where \(m(q)\) is the unique minimizer and \(H_q=d_w^2L_q|_{m(q)}\).
> Consequently, every fixed \(C^1\) path in \(K\) satisfies
> \[
> \frac{\operatorname{Length}_{g_t}(\gamma)}{\sqrt t}
> \longrightarrow
> \operatorname{Length}_{G}(\gamma).
> \]

Together, these are a strong central statement. I would not yet promote convergence of fixed-path lengths to convergence of intrinsic distances: taking an infimum over paths introduces additional compactness and coercivity issues, especially when \(G\) is degenerate.

There cannot be one universally useful scalar normalization across the entire singular-stratified manifold. The honest global programme is **one exact geometry, with a compatible atlas of differently scaled limits**.

---

## 3. A(iii): there is a cheap route that avoids uniform domination

For an affine path \(L_s=L_0+s\Delta\), put
\[
M_t(s)=\langle\Delta\rangle_{t,s},
\qquad
f_t(s)=t\operatorname{Var}_{t,s}(\Delta).
\]
Your exact derivative theorem gives
\[
M_t'(s)=-f_t(s).
\]
Hence
\[
\boxed{\int_0^1 f_t(s)\,ds=M_t(0)-M_t(1).}
\]

For bounded \(\Delta\), the right side is uniformly bounded:
\[
0\le M_t(0)-M_t(1)\le \operatorname{osc}(\Delta).
\]
An essential oscillation bound suffices.

Meanwhile,
\[
\frac{\ell_t}{\sqrt t}
=
\int_0^1\sqrt{f_t(s)}\,ds.
\]

Suppose merely that
\[
f_t(s)\longrightarrow\kappa(s)
\quad\text{for almost every }s.
\]
The family \(\sqrt{f_t}\) is uniformly bounded in \(L^2([0,1])\). Consequently it is uniformly integrable in \(L^1\), since
\[
\int_E\sqrt{f_t(s)}\,ds
\le
\sqrt{|E|}\sqrt{\int_0^1f_t(s)\,ds}
\le
\sqrt{C|E|}.
\]
Vitali convergence yields
\[
\boxed{
\frac{\ell_t}{\sqrt t}
\longrightarrow
\int_0^1\sqrt{\kappa(s)}\,ds.
}
\]

### Suggested theorem package

A useful abstract analysis lemma is:

> If \(f_t\ge0\), \(f_t\to f\) almost everywhere on a finite-measure space, and  
> \(\sup_t\int f_t<\infty\), then  
> \(\int\sqrt{f_t}\to\int\sqrt f\).

Then instantiate it using the exact integrated variance identity.

This is likely substantially cheaper than obtaining uniform-in-\(s\) Laplace error bounds. In Lean, the work is finite-measure uniform integrability/Vitali infrastructure, rather than a new parameter-dependent Laplace theorem.

It also gives a useful global bound:
\[
\boxed{
\ell_t^2
\le
t\bigl(\langle\Delta\rangle_{t,0}
       -\langle\Delta\rangle_{t,1}\bigr)
\le t\,\operatorname{osc}(\Delta).
}
\]

For unbounded \(\Delta\), you do not need boundedness itself: a uniform bound on the endpoint expectation difference is enough, provided the derivative/integral identity is justified.

### A second route: Scheffé convergence

In the regular moving-minimizer setting,
\[
\kappa(s)=d\Delta_{m_s}\bigl(H_s^{-1}d\Delta_{m_s}\bigr),
\]
and
\[
\frac{d}{ds}\Delta(m_s)=-\kappa(s).
\]
If endpoint expectations converge to \(\Delta(m_0)\) and \(\Delta(m_1)\), then
\[
\int_0^1 f_t\longrightarrow\int_0^1\kappa.
\]
Pointwise convergence plus convergence of masses gives \(L^1\) convergence of these nonnegative functions. Then
\[
\int_0^1|\sqrt{f_t}-\sqrt\kappa|
\le
\left(\int_0^1|f_t-\kappa|\right)^{1/2}.
\]

Either route removes the domination obstacle from A(iii).

---

## 4. B: the invariant limiting metric, and what uniformity requires

### The clean invariant formulation

At a regular point \(q\), define the covector
\[
B_q(v)=d_wR_v|_{m(q)}
\in T^*_{m(q)}W.
\]
The Hessian at a critical point,
\[
H_q=d_w^2L_q|_{m(q)},
\]
is intrinsically defined without choosing a connection. Positive definiteness identifies it with an isomorphism \(T W\to T^*W\).

Then
\[
\boxed{
G_q(u,v)=B_q(u)\bigl(H_q^{-1}B_q(v)\bigr).
}
\]

Differentiating the stationarity equation gives
\[
H_qDm_q[v]+B_q(v)=0,
\]
so equivalently
\[
\boxed{
G_q(u,v)=H_q(Dm_q[u],Dm_q[v]).
}
\]

This is the cleanest formulation:

> **The leading response metric measures motion of the learned minimizer using the loss Hessian.**

Two qualifications matter.

- It is not literally the pullback through
  \[
  q\mapsto d_wL_q(m(q)),
  \]
  because that map is identically zero. \(B_q(v)\) differentiates the loss in the data direction while holding \(w\) fixed, before evaluating at the minimizer.

- It need not be the pullback of one metric on \(W\): \(H_q\) may depend on \(q\) even when \(m(q)\) is unchanged. It is a Hessian field along the minimizer section. It becomes an ordinary pullback metric if \(H_q\) factors through \(m(q)\).

### Is it the model Fisher metric?

Only in the appropriate special case.

For negative log-likelihood loss at a well-specified distribution,
\[
q=p_{m(q)},
\]
the information identity gives
\[
H_q=I(m(q)),
\]
under the standard regularity assumptions. There, \(G=m^*I\).

For arbitrary data distributions, especially misspecified ones,
\[
H_q=-E_q[d_w^2\log p_w]\big|_{m(q)}
\]
need not equal the model Fisher information or the \(q\)-score covariance. Do not replace the loss Hessian by either without an additional theorem.

### Hypotheses for uniform Laplace asymptotics

A practical compact-parameter theorem should assume:

1. A unique minimizer \(m_s\), varying continuously or smoothly.
2. Uniform positive definiteness \(H_s\ge hI\), \(h>0\).
3. A common local coordinate neighborhood, or a finite controlled cover.
4. Uniform bounds on the loss derivatives required by the existing rate theorem.
5. A prior density uniformly positive near the minimizers, with controlled derivatives.
6. A uniform energy gap away from the local neighborhoods, together with uniform tail estimates for the relevant moments.
7. Uniform observable bounds/growth controls.

Joint smoothness, compactness, and uniform coercivity often produce these assumptions. Joint smoothness and uniqueness alone do not prevent problematic behavior at infinity.

**Fixed-potential rate theorems do not automatically yield uniform rates.** Compactness helps only once the proof supplies locally uniform estimates, or explicit constants whose controlling quantities are uniformly bounded. Pointwise eventual bounds cannot simply be patched by a finite cover.

A separate route, if available, is a uniform Poincaré/Brascamp–Lieb estimate. For example, global strong convexity of \(tL_s-\log\pi\), together with control of \(\nabla\Delta\), gives \(t\operatorname{Var}(\Delta)\le C\). But importing that machinery is probably unnecessary for A(iii), given the shortcut above.

### The next scale: common-minimizer shape geometry

Suppose the minimizer is fixed along a regular family. Write \(H_q\) for its changing Hessian. For tangent directions preserving the minimizer,
\[
g_{t,q}(u,v)\longrightarrow
\frac12\operatorname{tr}
\left(H_q^{-1}D_uH_q\,H_q^{-1}D_vH_q\right),
\]
under the corresponding Laplace moment assumptions.

This is the Fisher metric of the limiting centered Gaussian shape.

Thus the regular story already has two geometries:

- order \(t\): minimizer motion;
- order \(1\): covariance/shape change on fibers of the minimizer map.

That is a particularly beautiful strengthening of A(i). The boundedness result is the easy first step; the shape formula explains what the bounded distance measures.

---

## 5. C and F: convexity, duality, and identifiability

Let
\[
L_a=L_0+\sum_{i=1}^k a_i\Delta_i,
\qquad
A_t(a)=\log Z_t(L_a).
\]
For bounded measurable contrasts and a nonzero finite baseline tilted measure, \(A_t\) is finite and smooth on all \(\mathbb R^k\), and
\[
\partial_iA_t=-t\langle\Delta_i\rangle_a,
\qquad
\partial_i\partial_jA_t
=t^2\operatorname{Cov}_a(\Delta_i,\Delta_j).
\]

### Convexity by restriction to lines

Yes: this is the cheapest route.

Along the segment from \(a\) to \(b\), use baseline \(L_a\) and contrast
\[
\Delta_{b-a}=\sum_i(b_i-a_i)\Delta_i.
\]
Then invoke the mixture-line theorem.

The main pitfalls are:

- proving positivity and finiteness before treating `Real.log` as a log-partition function;
- ensuring the shifted baseline has the hypotheses required by the line API;
- distinguishing convexity on the simplex from convexity on the full affine parameter space;
- remembering that for unbounded contrasts the natural domain may be smaller than \(\mathbb R^k\).

### The sign convention in Legendre duality

With coefficients \(a\), the expectation map is
\[
a\mapsto\langle\Delta\rangle_a
=-\frac1t\nabla A_t(a).
\]
It is therefore an anti-monotone gradient map.

Using natural parameters \(\theta=-ta\),
\[
\widetilde A(\theta)
=\log\int e^{-tL_0+\theta\cdot\Delta}\,d\pi,
\qquad
\nabla_\theta\widetilde A=\langle\Delta\rangle_\theta.
\]
This is the standard convex Legendre convention.

Also,
\[
F_t(a)=-\frac1tA_t(a)
\]
is concave and satisfies \(\nabla F_t=\langle\Delta\rangle_a\).

### Nullspace and diffeomorphism

For finite \(t>0\), the posterior and baseline measure are equivalent under the usual finite-loss assumptions. Thus the exact nullspace is independent of \(a\):
\[
u\in\ker g_t
\iff
\sum_i u_i\Delta_i
\text{ is constant almost everywhere.}
\]

After quotienting by that fixed subspace, the Hessian is positive definite. On an open convex domain:

- positive Hessian gives strict convexity;
- strict convexity gives injectivity of the gradient;
- the inverse function theorem gives local smooth inverses;
- injectivity patches these into a diffeomorphism onto the open image.

Mathematically this is straightforward. In Lean, the principal extra work beyond a bilinear `responseForm` API is identifying the multivariate Fréchet derivative of the mean map. I would first land convexity, the Jacobian formula, and injectivity; package the diffeomorphism afterward.

For F, strict anti-monotonicity is an immediate high-value corollary. But qualify “moments determine the path”:

> Moments of \(\Delta\) determine its scalar distribution under the baseline measure, and hence its partition function and scalar tilt family.

They do **not** by themselves determine expectations of arbitrary \(\phi(w)\). That requires mixed moments \(E[\phi\Delta^n]\), or equivalent joint information.

---

## 6. E: the wall is transverse to a coefficient stratum, not the neutral ray

Your suspicion is correct.

For a loss-neutral starting point,
\[
L_s=C+s(L_{\mathrm{target}}-C),
\]
the posterior depends only on \(ts\). All nonconstant target coefficients scale together. This is a radial temperature path, not generally a transverse crossing of a coefficient wall.

By contrast,
\[
L_a(w)=w^p+a w^q,\qquad 0<q<p,
\]
changes one coefficient relative to another. The wall is \(a=0\), where the local leading order changes.

A concrete data path crosses or approaches this wall when its expected loss has a coefficient \(a(q)\) passing through or approaching zero while the \(w^p\) coefficient remains nonzero.

### The finite-\(t\) object to study

Blow up both parameter space and data space:
\[
y=t^{1/p}w,\qquad a=c\,t^{-\sigma_*},
\qquad \sigma_*=1-q/p.
\]
Then study the pushed-forward posterior
\[
(t^{1/p}\,\cdot)_*\rho_{t,a}
\]
as a family in \(c\), together with its expectations and Fisher metric.

For the pure monomial/Lebesgue model, you already have exact equality with the profile family. For a more general prior or higher-order loss terms, the appropriate target is locally uniform convergence in \(c\), including the score moments needed for metric convergence.

### A very attractive next theorem: wall length equals profile length

In your exact model,
\[
g^{(t)}_{aa}
=t^2\operatorname{Var}_{t,a}(w^q)
=t^{2\sigma_*}\operatorname{Var}_c(y^q).
\]
Since \(da/dc=t^{-\sigma_*}\),
\[
\boxed{
g^{(t)}_{cc}=\operatorname{Var}_c(y^q)=A''(c).
}
\]
Therefore
\[
\boxed{
\operatorname{Length}_{g_t}
\bigl([c_0t^{-\sigma_*},c_1t^{-\sigma_*}]\bigr)
=
\int_{c_0}^{c_1}\sqrt{\operatorname{Var}_c(y^q)}\,dc.
}
\]

This is exact for every \(t>0\), under the same reference-measure assumptions as `wall_posterior_eq_profile`.

It says:

> **A shrinking window in the data coordinate carries a fixed, nontrivial response geometry.**

That is arguably the cleanest next singular-geometric theorem available from the landed material.

If the current profile results cover only \(c>0\), call this a one-sided wall approach. A genuine two-sided crossing requires extending the profile family to negative \(c\). For \(0<q<p\), that extension is analytically possible, but needs a different domination argument.

---

## 7. RLCT, singular fluctuation, and the neutral endpoint

### In your fixed-loss setting, the constant is \(\lambda\)

Let \(K=L-\min L\ge0\). Under standard singular Laplace hypotheses,
\[
Z_K(t)\sim C\,t^{-\lambda}(\log t)^{m-1}.
\]
With justified differentiated or moment asymptotics,
\[
E_t[K]\sim\frac{\lambda}{t},
\qquad
\operatorname{Var}_t(K)\sim\frac{\lambda}{t^2}.
\]
Thus
\[
\boxed{t^2\operatorname{Var}_t(L)\longrightarrow\lambda.}
\]

A particularly illuminating formulation is that the rescaled excess energy \(tK\) has a limiting Gamma law with shape \(\lambda\), with convergence of the relevant moments. Its limiting mean and variance are both \(\lambda\).

Log multiplicity affects lower-order terms, not this limit. Formally,
\[
(\log Z_K)''(t)
=
\frac{\lambda}{t^2}
-\frac{(m-1)(\log t+1)}{t^2(\log t)^2}
+\text{smaller terms}.
\]
One must not differentiate an uncontrolled asymptotic remainder; the standard moment expansion supplies the justification.

### Why this is not the singular fluctuation \(\nu\)

The singular fluctuation concerns posterior fluctuations in the random empirical-learning setting, commonly through functional variance of pointwise log likelihoods. It is not generally the same as the posterior variance of a fixed deterministic total loss.

For your fixed \(q\), fixed \(L_q\), \(t\to\infty\) setting, the energy-variance coefficient is \(\lambda\).

If \(t=n\beta\), then for a fixed deterministic loss,
\[
\operatorname{Var}(nL)
\sim\frac{\lambda}{\beta^2}.
\]
This explains a common temperature factor, but should not be transplanted without qualification to random empirical losses.

### Improper priors change the neutral endpoint fundamentally

At a loss-neutral point, the posterior is the normalized prior. With a flat prior on \(\mathbb R^d\), that point does not define a probability distribution.

For a homogeneous flat-prior model, often
\[
\operatorname{Var}_u(L)=\frac{\lambda}{u^2}
\]
for every \(u>0\). Then
\[
\int_0^t\sqrt{\operatorname{Var}_u(L)}\,du=\infty.
\]
So the featureless-to-data length is already infinite at every finite \(t\).

Starting instead at a fixed \(u_0>0\),
\[
\int_{u_0}^t\sqrt{\operatorname{Var}_u(L)}\,du
\sim\sqrt\lambda\log t.
\]
The large-\(t\) logarithmic growth survives; the neutral endpoint does not.

Even a proper prior does not by itself guarantee finite variance at \(u=0\) for an unbounded loss. Your bounded-contrast version avoids this issue. For the anharmonic example, finite prior energy moments and the relevant continuity lemma should be explicit.

---

## 8. Audit of the landed statements

I cannot verify the Lean declarations from their names, but the stated mathematics is sound subject to these checks.

### `profile_expFamily`

Correct with
\[
A(c)=\log\int_0^\infty e^{-y^p-cy^q}\,dy.
\]
It is an exponential family relative to base measure \(e^{-y^p}dy\), with natural parameter \(-c\). The signs
\[
A'=-E_c[y^q],\qquad A''=\operatorname{Var}_c(y^q)
\]
are correct.

### `profileMean_strictAntiOn`

Correct for \(q>0\), positive nondegenerate profile support, and the domain on which differentiation is justified. The statistic \(y^q\) is not almost surely constant.

Strict monotonicity identifies \(c\) from that one response **within this profile family**; no stronger global identifiability claim is needed.

### `wall_posterior_eq_profile`

Exact equality requires the reference measure/prior assumed by the monomial calculation. A general nonconstant prior produces a rescaled factor \(\pi(t^{-1/p}y)\), so one usually obtains a limit rather than equality.

### `thermoLength_neutral_eq`

Correct:
\[
\ell(t)
=\int_0^1t\sqrt{\operatorname{Var}_{ts}(\Delta)}\,ds
=\int_0^t\sqrt{\operatorname{Var}_u(\Delta)}\,du.
\]
The constant neutral loss cancels. Integrability and endpoint moment assumptions remain part of the statement.

### `responseForm_asymptotic`

This is the one normalization that needs immediate checking. If
\[
\texttt{responseForm}=t^2\operatorname{Cov},
\]
then
\[
\frac{\texttt{responseForm}}t
=t\operatorname{Cov}\longrightarrow B^\top H^{-1}B.
\]
A theorem about \(t\cdot\texttt{responseForm}\) would instead fit a definition using raw covariance.

---

## Recommended next bundle

I would make the next round a tightly connected package:

1. **Multivariate log-partition convexity and its Hessian/Jacobian identification.**
2. **Strict response identifiability modulo constant-loss directions.**
3. **Integrated susceptibility**
   \[
   \int_0^1t\operatorname{Var}_{t,s}(\Delta)\,ds
   =\langle\Delta\rangle_{t,0}-\langle\Delta\rangle_{t,1}.
   \]
4. **Square-root integral convergence from an \(L^1\) mass bound**, giving A(iii) without uniform domination.
5. **Exact wall-window/profile thermodynamic-length equality.**

That bundle would establish a compelling picture: **global convex response coordinates, macroscopic regular transport, and nontrivial geometry inside shrinking singular windows**—all emerging from the same covariance response form.