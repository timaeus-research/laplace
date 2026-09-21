Your proposal is sound, but I would separate three levels:

1. **Fixed temperature:** a clean analytic map into a Banach space of measures.
2. **A fixed asymptotic type:** a smooth, coefficientwise map into formal asymptotic data.
3. **Changing singularity type:** a stratified problem, usually requiring transition asymptotics rather than a single topology on formal expansions.

The main corrections are: “polynomial in the jet” requires fixing the quadratic part; simultaneous resolution fixes **candidate poles**, not automatically actual poles; and the **real** RLCT has no general semicontinuity direction.

## Q1. Fixed temperature: yes, and total variation is a good target

Let \(K\) be compact, and let \(\nu\) be a finite, nonzero positive Radon measure incorporating the window/prior. Set
\[
Z_t(L)=\int_K e^{-tL}\,d\nu,\qquad
\mu_{L,t}=\frac{e^{-tL}}{Z_t(L)}\,\nu.
\]

For fixed \(t\geq0\),
\[
C(K)\longrightarrow \mathcal M(K),\qquad L\longmapsto\mu_{L,t}
\]
is **real analytic**, where \(C(K)\) has the sup norm and \(\mathcal M(K)\) has the total-variation norm.

Indeed, exponentiation is analytic in the Banach algebra \(C(K)\), integration is bounded linear, and \(Z_t(L)>0\). Its derivative is the signed measure
\[
D\mu_{L,t}[R]
=-t\bigl(R-\mu_{L,t}(R)\bigr)\mu_{L,t}.
\]
Consequently,
\[
D\langle\varphi\rangle_{L,t}[R]
=-t\,\operatorname{Cov}_{L,t}(\varphi,R).
\]

With the convention \(\|\eta\|_{\rm TV}=|\eta|(K)\), one even has
\[
\|D\mu_{L,t}[R]\|_{\rm TV}
=t\,\mathbb E_{\mu_{L,t}}|R-\mathbb ER|
\leq t\|R\|_\infty.
\]
Thus this is stronger than differentiability against each individual test.

### Alternative targets

If \(\mathcal F\subset C(K)\) is uniformly bounded, then
\[
L\longmapsto \bigl(\mu_{L,t}(\varphi)\bigr)_{\varphi\in\mathcal F}
\]
is analytic into \(\ell^\infty(\mathcal F)\). Taking \(\mathcal F\) to be the unit ball of \(C(K)\) recovers the total-variation norm.

For an unrestricted class of tests, \(\mathbb R^{\mathcal F}\) with product topology gives coordinatewise analyticity, but it is a weaker formulation. The measure-valued theorem is the cleanest foundational statement.

The same result holds on a Hölder or \(C^k\) space by composition with its continuous inclusion into \(C(K)\). Those stronger domains are useful for moving minimisers, not necessary at fixed \(t\).

### Composition with variations of \(q\)

Choose a Banach space \(B\) of signed distributions/densities such that
\[
A:B\to C(K),\qquad
Ar(w)=-\int r(x)\log p_w(x)\,dx
\]
is bounded linear. Then
\[
q\longmapsto \mu_{Aq,t}
\]
is analytic on the ambient Banach space, and restriction to admissible probability distributions gives the desired variation theory.

For mass-preserving variations \(r\),
\[
D_q\langle\varphi\rangle[r]
=-t\operatorname{Cov}_{L(q),t}(\varphi,Ar).
\]
Under the relevant Fubini assumptions this becomes
\[
D_q\langle\varphi\rangle[r]
=t\int r(x)\,
\operatorname{Cov}_{L(q),t}\!\bigl(\varphi,\log p_\bullet(x)\bigr)\,dx.
\]

Probability distributions themselves need not form an open Banach-space subset. The convenient formulation is an ambient analytic map, restricted to the positive, mass-one subset or its tangent directions.

For a finite mixture
\[
q_\theta=\sum_i\theta_iq_i,\qquad L_\theta=\sum_i\theta_iL_i,
\]
this is especially straightforward:
\[
\partial_{\theta_i}\langle\varphi\rangle_{\theta,t}
=-t\operatorname{Cov}_{\theta,t}(\varphi,L_i),
\]
with simplex-tangent directions understood when enforcing \(\sum_i\theta_i=1\).

### Rescaled tests

For fixed \(t\) and fixed centre \(w_*\), nothing changes: use
\[
\varphi_t(w)=\varphi(\sqrt t(w-w_*)).
\]
For bounded \(\varphi\), its sup norm stays bounded.

If the centre moves with \(L\), the test also varies. Along a differentiable family,
\[
\frac d{du}\mathbb E_u[\varphi(\sqrt t(w-w_*(u)))]
=
-t\operatorname{Cov}_u(\varphi_t,\dot L_u)
-\sqrt t\,\mathbb E_u[
\nabla\varphi(\sqrt t(w-w_*))\cdot\dot w_*].
\]
Differentiability of \(w_*\) requires stronger hypotheses than the \(C^0\) topology.

Finally, the \(t\)-dependent derivative bounds are not uniform as \(t\to\infty\). The fixed-temperature theorem alone does not justify interchanging differentiation and low-temperature asymptotics.

---

## Q2. Germ-level expectation data: use fixed-type formal data, with two corrections

### First distinguish germs from finite-temperature measures

A finite-temperature posterior on a fixed window is not determined by the germ of \(L\). Under an isolated-minimum/localisation hypothesis, its **algebraic asymptotic expansion** is local and hence determined by germ data.

In the smooth category, this expansion generally factors through the infinite Taylor jet: flat perturbations can be invisible to every algebraic order. This is different from identifying smooth germs.

### The Morse case has a particularly clean formulation

Fix the minimum at \(0\), subtract \(L(0)\), and write
\[
L(x)=\frac12x^\top Hx+\sum_{m\geq3}\ell_m(x),
\]
where \(\ell_m\) is homogeneous of degree \(m\). Let \(\varepsilon=t^{-1/2}\). Then
\[
tL(\varepsilon y)
=\frac12y^\top Hy+\sum_{m\geq3}\varepsilon^{m-2}\ell_m(y).
\]

For a fixed positive-definite \(H\), and a window/prior constant near the minimum,
\[
\mathbb E[\varphi(\sqrt t\,w)]
\sim\sum_{r\geq0}\varepsilon^r C_r(\varphi),
\]
with
\[
C_r(\varphi)
=
-\operatorname{Cov}_{\gamma_H}(\varphi,\ell_{r+2})
+
P_r(\ell_3,\ldots,\ell_{r+1};\varphi),
\qquad r\geq1.
\]

So the indexing point is:

> The coefficient of \(t^{-r/2}\) is affine in the degree-\((r+2)\) Taylor term.

A nonconstant prior adds its Taylor coefficients in the usual way.

The polynomial claim is correct **coefficientwise, with \(H\) fixed**. If \(H\) varies, the coefficients are generally smooth or analytic on the positive-definite cone, not polynomial. Already \(C_0(\varphi)=\mathbb E_{\gamma_H}\varphi\) depends nonpolynomially on \(H\). Varying the leading prior density also introduces division by its value at the minimum.

Each \(C_r\) depends on only finitely many jets. Thus a natural construction is
\[
\text{formal jets with positive-definite quadratic part}
\longrightarrow
\prod_{r\geq0}\mathcal D_r,
\]
with product topology. One can take \(\mathcal D_r=\mathcal S'(\mathbb R^d)\), since the coefficient distributions are Gaussian densities times polynomials. This map is smooth in the coefficientwise/product sense; with \(H\) fixed it is coefficientwise polynomial.

This is more canonical than first choosing a finite set of tests.

### Singular expansions: normalisation matters

For **unnormalised** Laplace integrals, the standard resolution grammar is
\[
I_\varphi(t)\sim
\sum_{\alpha}\sum_{j=0}^{m_\alpha-1}
c_{\alpha,j}(\varphi)t^{-\alpha}(\log t)^j.
\]

But posterior expectations are quotients \(I_\varphi/I_1\). Their expansions need not remain finite polynomials in \(\log t\) at each exponent. Dividing, for example, by
\[
t^{-\lambda}(a\log t+b)
\]
can generate an infinite expansion in inverse powers of \(\log t\).

Therefore I would initially store either:

* the **unnormalised asymptotic functional** \(\varphi\mapsto I_\varphi\), with the denominator distinguished; or
* a formal asymptotic algebra explicitly closed under the required divisions.

Also, ordinary rescaled tests \(\varphi(\sqrt t\,w)\) are tailored to Morse minima. Singular minima generally require anisotropic or chart-dependent scaling.

### Is a discrete topology on exponent sets appropriate?

It is workable as a **disjoint union of fixed-type coefficient spaces**, but not canonical. It declares continuity impossible whenever the type changes and discards crossover information.

A better distinction is:

* fixed singularity type: coefficientwise topology;
* changing type: topology on actual \(t\)-dependent expectation functions, supplemented by uniform or matched asymptotic estimates.

The latter records both finite-\(t\) continuity and nonuniformity at \(t=\infty\).

---

## Q3. Resolution in families is reasonable—but specify a relative normal-crossings hypothesis

### A useful precise hypothesis

Let \(S\) be a finite-dimensional smooth parameter space and \(f_s=L_s-\min L_s\). Assume \(f_s\) is analytic in the spatial variables, with suitable parameter regularity.

A strong, useful hypothesis is a proper map
\[
\pi:\widetilde X\to X\times S
\]
over \(S\) such that:

1. \(\widetilde X\to S\) is smooth;
2. the relevant exceptional and transformed divisors have **relative simple normal crossings**;
3. locally,
   \[
   f_s\circ\pi=a(y,s)\prod_i y_i^{N_i},
   \]
   with \(a\) nowhere zero and the \(N_i\) independent of \(s\);
4. the relative integration density has the form
   \[
   b(y,s)\prod_i|y_i|^{\nu_i-1}\,dy,
   \]
   with fixed \(\nu_i\);
5. the resolved support is controlled uniformly, and the relevant positive units are bounded away from zero on compact parameter subsets.

This gives genuine geometric control: fixed divisor incidence, vanishing orders, Jacobian orders, and smoothly varying units and amplitudes.

One important caveat: subtracting \(\min L_s\) does **not** automatically preserve analytic parameter dependence. Switching minimisers can already make the minimum-value function nonsmooth.

### What generic resolution actually gives

For finite-dimensional algebraic families in characteristic zero, one can resolve the generic fibre and spread the resolution out over a nonempty Zariski-open subset of the base. After shrinking, one obtains the required relative smoothness and normal-crossings properties.

Equivalently, a suitable total-space resolution can often be restricted after deleting bad parameters. But:

> Resolving the total space does not, without shrinking and checking relative conditions, imply that every fibre is resolved.

Analytic families have analogous local results, but “Zariski-open dense” is not the right universal language there. Arbitrary \(C^\infty\) families or infinite-dimensional spaces of \(q\)'s are outside this generic algebraic statement.

Relevant references/frameworks are:

* Hironaka’s characteristic-zero resolution theorem;
* Encinas–Nobile–Villamayor, **“On algorithmic equiresolution and stratification of Hilbert schemes”**;
* the equisingularity and simultaneous-resolution literature of Zariski, Teissier and Lipman.

Their notions should not be conflated: Whitney equisingularity, Zariski equisingularity and algorithmic equiresolution are not interchangeable hypotheses. For your theorem, specify the relative monomialisation properties actually used.

### What is constant?

From fixed \((N_i,\nu_i)\), one obtains a fixed **candidate pole set**, schematically
\[
-\frac{\nu_i+k}{N_i},\qquad k\in\mathbb N_0,
\]
with possible refinements from parity and the integration setting.

However, **actual poles can disappear** through vanishing residues, amplitude zeros or cancellations. Thus:

* fixed resolution data imply fixed candidate poles;
* they do not alone imply a fixed full actual pole set for every test.

For the leading pole, positivity is helpful. With a positive amplitude, stable relevant real divisor strata, and fixed incidence data,
\[
\lambda=\min_i\frac{\nu_i}{N_i}
\]
over the relevant real components, and the leading logarithmic multiplicity is determined by intersections of components attaining that minimum. Under those additional conditions, \((\lambda,m)\) is constant.

The coefficients depend smoothly on \(s\) under the uniform relative hypotheses. It is slightly too simple to call every coefficient an integral over an exceptional component: residues may involve transverse derivatives and finite-part constructions as well.

Moreover, coefficientwise smoothness is weaker than a **uniform differentiable asymptotic expansion**. To differentiate the expansion termwise, establish remainder estimates uniform in parameters and in the parameter derivatives you need.

### Semicontinuity: complex and real thresholds differ

For complex log canonical thresholds in the usual algebraic-family setting, the threshold is lower semicontinuous:
\[
\operatorname{lct}(s_0)\leq\liminf_{s\to s_0}\operatorname{lct}(s).
\]
Specialisation can make the singularity worse and lower the threshold.

**Do not transfer this without qualification to the real RLCT.** There is no general semicontinuity direction.

Two nonnegative analytic examples show both behaviours.

**Special fibre has smaller RLCT:**
\[
f_u(x)=x^4+u^2x^2.
\]
Then
\[
\lambda(0)=\frac14,\qquad \lambda(u)=\frac12\quad(u\ne0).
\]

**Special fibre has larger RLCT:** in \(\mathbb R^3\), with a marked zero at the origin,
\[
g_u(x,y,z)=\bigl(x^2+y^2+z^2+2ux\bigr)^2.
\]
For \(u\ne0\), the inner function defines a smooth hypersurface near \(0\), so
\[
\lambda(u)=\frac12.
\]
At \(u=0\), \(g_0=r^4\), hence
\[
\lambda(0)=\frac34.
\]

This distinction is particularly important for the statistical application.

### Boundary degeneration

At stratum boundaries, one may see:

* coefficients blowing up **or tending to zero**;
* a leading term disappearing;
* new divisor intersections or changed monomial orders;
* altered logarithmic multiplicities;
* loss of uniformity of the fixed-stratum expansion.

Exponent collisions can generate logarithms in broader asymptotic families, but in a fixed algebraic resolution stratum the rational candidate exponents are normally constant—not continuously moving quantities.

The right boundary object is often a crossover function involving a combined variable such as \(u\,t^\beta\).

---

## Q4. What to formalise next

My ranking by mathematical return is:

1. **A: Banach-space differentiability into measures.**
2. **C: smooth response of the effective tangential measure in normal-form families.**
3. **D: an explicit nonuniform low-temperature limit.**
4. **B as a standalone theorem**—because it should be an immediate, useful corollary of A.

For implementation cost, B may be the quickest result available immediately from your existing one-parameter identity.

### First theorem: measure-valued Fréchet derivative

I would target:

> **Theorem.** Let \(K\) be compact and \(\nu\) a finite, nonzero positive Radon measure. For \(t\geq0\), define
> \[
> \mathsf P_t(L)=\frac{e^{-tL}}{\int e^{-tL}\,d\nu}\nu,
> \qquad L\in C(K).
> \]
> Then \(\mathsf P_t:C(K)\to\mathcal M(K)\) is Fréchet differentiable, with
> \[
> D\mathsf P_t(L)[R]
> =-t(R-\mathsf P_t(L)(R))\,\mathsf P_t(L),
> \]
> and
> \[
> \|D\mathsf P_t(L)[R]\|_{\rm TV}\leq t\|R\|_\infty.
> \]
> Locally in \(R\),
> \[
> \|\mathsf P_t(L+R)-\mathsf P_t(L)-D\mathsf P_t(L)[R]\|_{\rm TV}
> \leq C\,t^2\|R\|_\infty^2.
> \]

The remainder estimate is the key upgrade from directional differentiation to genuine Fréchet differentiation. If the signed-measure API is cumbersome, first prove it for the normalised density as a \(C(K)\)- or \(L^1(\nu)\)-valued map.

### C gives the closest bridge to exceptional-divisor geometry

For a Morse–Bott family with fixed tangential space \(Y\), let
\[
\rho_u(y)=\chi_u(y)\det H_u(y)^{-1/2}.
\]
For its normalised tangential expectation,
\[
\frac d{du}\mathbb E_{\rho_u}[g_u]
=
\mathbb E_{\rho_u}[\dot g_u]
+
\operatorname{Cov}_{\rho_u}(g_u,S_u),
\]
where
\[
S_u
=
\frac{\dot\chi_u}{\chi_u}
-\frac12\operatorname{tr}(H_u^{-1}\dot H_u).
\]

For the one-normal-variable power model,
\[
\rho_u(y)=\chi_u(y)a_u(y)^{-1/(2k)},\qquad
S_u=\frac{\dot\chi_u}{\chi_u}-\frac1{2k}\frac{\dot a_u}{a_u}.
\]

These are exact in the product normal-form model with full normal integration and tangential amplitude. With a general compact cutoff they describe the leading tangential asymptotics.

This is a particularly good “resolution-free prototype” of differentiating integrals on a fixed resolved family.

### D: correct the proposed toy family

Your proposed
\[
\tfrac12x^2+ux^4
\]
does not exhibit an RLCT jump at the origin: its Hessian stays nondegenerate.

Use instead
\[
L_u(x)=x^4+u^2x^2.
\]
For a positive local prior,
\[
\lim_{t\to\infty}t\,\mathbb E_{u,t}[L_u]
=
\begin{cases}
\frac14,&u=0,\\[2mm]
\frac12,&u\ne0.
\end{cases}
\]
Every fixed-\(t\) quantity is smooth in \(u\), while this leading asymptotic invariant is discontinuous.

On the whole line with flat prior, \(x=t^{-1/4}y\) gives the exact crossover parameter
\[
s=u^2t^{1/2},
\]
and
\[
t\,\mathbb E[L_u]
=
\frac{\int (y^4+sy^2)e^{-y^4-sy^2}\,dy}
{\int e^{-y^4-sy^2}\,dy}.
\]
This interpolates between \(1/4\) and \(1/2\).

Notice that the unscaled posterior still converges weakly to \(\delta_0\) for every \(u\). The discontinuity belongs to the **asymptotic invariant/rescaled data**, not necessarily to the weak limiting measure.

**Bottom line:** formalise A as the analytic foundation, derive B, then use C as the geometrically informative family theorem. D is the essential warning example explaining why that smooth finite-temperature theory does not automatically extend uniformly across singularity strata.