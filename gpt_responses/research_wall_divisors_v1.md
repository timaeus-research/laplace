**There is a resolution-invariant phenomenon here, but the proposed correspondence with exceptional divisors of an arbitrary resolution is false.** The invariant object must retain the map to parameter space, the relative integration density, and the asymptotics of the resulting integral—not just the orders of \(F,x,s\) along divisors.

Your weighted-blow-up calculation is correct. Its interpretation should be:

> A Newton face defines a weighted degeneration. Its exceptional initial form, together with the parameter map and relative density, can furnish a crossover model.

This is weaker than saying that exceptional divisors classify crossovers. Below are explicit counterexamples, a corrected framework, and two test cases.

## 0. Two corrections to the stated analytic theorem

With your definition \(E_t=\langle F\rangle\), the displayed limit should be
\[
\boxed{\quad tE_t(\sigma t^{-\gamma})\longrightarrow
\frac{\int E(u,\sigma)e^{-E(u,\sigma)}\,du}
{\int e^{-E(u,\sigma)}\,du}.\quad}
\]
For example, \(F=x^2\) gives \(E_t=1/(2t)\), not \(1/2\). I will write
\[
H_t(s):=tE_t(s)
\]
throughout.

Also, pointwise higher-weight convergence and \(E,R\geq0\) alone are not enough for this theorem. One needs hypotheses controlling the rescaled integrals: integrability of the limiting density, domination/tightness, suitable behavior of \(\chi\), and corresponding control of the energy numerator.

For your second edge,
\[
E(u,\sigma)=\sigma^2u^4+\sigma^6u^2,
\]
the limiting integral is well-defined for \(\sigma\ne0\), **not at \(\sigma=0\)**. Its profile can have a limit as \(\sigma\to0\), but that is an iterated limit, not the theorem evaluated at \(\sigma=0\).

These distinctions become important in the degenerate examples below.

---

## 1. What the weighted blow-up actually proves

Let
\[
F(x,s)=\sum c_{ab}x^as^b,\qquad
N=\min_{c_{ab}\ne0}(pa+qb).
\]
In the chart
\[
x=uv^p,\qquad s=v^q,
\]
one has
\[
F\circ g=v^N\left(\sum_{pa+qb=N}c_{ab}u^a+O(v)\right).
\]
Thus
\[
\left.v^{-N}F\circ g\right|_{v=0}=F_\tau(u,1),
\]
where \(\tau\) is the minimizing Newton face.

That is an exact algebraic statement. It gives
\[
\alpha=p/N,\qquad \gamma=q/N.
\]

But there are three qualifications.

### The divisor is associated to a chosen face degeneration

For a plane Newton polygon, a compact edge with positive normal gives a distinguished ray in the normal fan. A toric modification adapted to the polygon contains the corresponding divisor. A smooth toric resolution generally contains **additional rays and additional divisors**.

Those additional divisors need not represent additional layers.

### The residual is not intrinsically a scalar function

If \(v\) is replaced by \(v'=a\,v\), then
\[
\Phi|_D\longmapsto a^{-N}\Phi|_D.
\]
Intrinsically, the leading coefficient is a section of a normal-bundle power, rather than a canonically trivialized scalar function on \(D\).

Locally where \(\Phi>0\), one can even set \(v'=v\Phi^{1/N}\), obtaining \(F=(v')^N\). The apparent residual becomes \(1\); the information has moved into the parameter map and density.

Thus “the residual is non-monomial” is not an invariant criterion without specifying a toroidal structure, coordinates, and trivialization.

### Use the fibre density, not the ambient Jacobian

In this chart,
\[
dx\,ds=qv^{p+q-1}\,du\,dv,
\]
but on a fixed \(s\)-fibre,
\[
dx=v^p\,du.
\]
The ambient discrepancy alone does not give the posterior integration density. The projection to \(s\) must be retained.

---

## 2. A decisive counterexample to “all exceptional divisors = all layers”

Take the Newton-nondegenerate polynomial
\[
F=x^4+s^2x^2.
\]
It has one compact lower edge, normal \((1,1)\), giving
\[
(\alpha,\gamma)=(1/4,1/4).
\]
Indeed,
\[
tF(t^{-1/4}u,\sigma t^{-1/4})=u^4+\sigma^2u^2.
\]
There is one standard crossover from \(1/4\) to \(1/2\).

Now insert any primitive positive ray \((p,q)\) into a toric refinement. Its divisor has
\[
\nu_D(F)=\min(4p,2p+2q),
\]
and hence
\[
\gamma_D=\frac{q}{\min(4p,2p+2q)}.
\]
These ratios are not restricted to \(1/4\). Across refinements they approach \(0\) when \(p/q\to\infty\), and are unbounded when \(q/p\to\infty\).

All these divisors lie over the origin. They plainly cannot all be layers.

Consequently:

* the set of ratios over the exceptional divisors of a resolution depends on the resolution;
* the set over **all** divisorial valuations is much too large;
* its infimum need not identify any physical crossover;
* only specially selected, asymptotically relevant degenerations can represent layers.

There is an equally instructive example using your merging-zero model. Blow up
\[
F=x^2(x-s)^2,\qquad x=su.
\]
Then
\[
F=s^4u^2(u-1)^2.
\]
Blow up the point \(s=0,u=1\), using \(u=1+sw\). Now
\[
F=s^6(1+sw)^2w^2.
\]
The new divisor gives \(\gamma=1/6\), although the original homogeneous model has only its \(s\,t^{1/4}\) crossover. Along \(s=\sigma t^{-1/6}\), the normalized energy simply tends to the separated-well value \(1/2\).

A necessary blow-up resolving a degenerate face need not introduce a new crossover exponent.

---

## 3. Answer to (a): Newton nondegeneracy and the relative problem

### The ordinary Newton statement

For a polynomial in \((x,s)\), standard face nondegeneracy requires, for each relevant face \(\tau\), that
\[
\nabla F_\tau=0
\]
have no solution in the algebraic torus. For a weighted-homogeneous face, Euler’s identity makes this equivalent to smoothness of \(F_\tau=0\) in the torus.

One must distinguish complex nondegeneracy from real nondegeneracy. For real Laplace integrals, complex degeneracies away from the real integration region need not matter.

Under suitable nondegeneracy, a modification adapted to the Newton polyhedron gives the familiar toric description of the hypersurface. But this does **not**, by itself, establish a uniform asymptotic theorem for integration in \(x\) with \(s\) held fixed.

### What the relative problem additionally needs

A crossover assertion involves:

1. the face form \(F_\tau\);
2. the projection to parameter space;
3. the relative density;
4. integrability of the limiting fibre model;
5. control of all other integration regions.

A face polynomial can be perfectly nondegenerate in the ordinary sense while its proposed rescaled fibre integral is nonintegrable. Conversely, a degenerate face can give an entirely valid crossover integral: your
\[
u^2(u-\sigma)^2
\]
is a good example.

Thus the useful analytic condition is not simply “relative Kouchnirenko nondegeneracy.” It is closer to:

> The face degeneration is compatible with the parameter projection, and its rescaled fibre integrals are uniformly integrable on the angular parameter region under consideration.

For a resolution-based formulation, one seeks normal-crossing/toroidal descriptions of **both the function and the parameter map**, with the density included. Resolving \(F\) alone is not enough.

### When edges really do classify the elementary layers

For one integrated variable, positive-coefficient even-monomial examples such as yours are especially favorable. Compact edges with positive normals give coercive one-dimensional face models for appropriate nonzero parameter directions; adjacent dominant monomials give the plateaus.

In that restricted setting, your edge-layer picture is sound.

In greater generality, the replacements are:

* successive Newton polygons in translated charts;
* a resolution tree, including face-root charts;
* a relative monomialization/toroidal description;
* asymptotic push-forward of the density along the parameter projection.

The first polygon may miss later behavior near roots of its face polynomial.

---

## 4. Answer to (b): ratios, thresholds, and the order of layers

### These are valuation ratios, but not ordinary lct formulas

An lct has the form
\[
\operatorname{lct}(F)=\inf_D\frac{A(D)}{\nu_D(F)},
\]
with \(A(D)\) a log discrepancy. Your ratio
\[
\frac{\nu_D(s)}{\nu_D(F)}
\]
contains no discrepancy.

Such ratios can occur as slopes in two-parameter log-canonicity regions, where inequalities look like
\[
A(D)-c\,\nu_D(F)+b\,\nu_D(s)\ge0.
\]
But that does not mean that their minimum is a crossover invariant. The preceding counterexample rules this out.

### “Earliest departure” uses the largest, not the smallest, listed \(\gamma\)

At fixed large \(t\), as \(|s|\) increases from zero,
\[
t^{-1/6}<t^{-1/10}.
\]
Thus your \(1/6\) layer is encountered before your \(1/10\) layer.

The terminology “outermost” can vary, but “earliest departure from the wall as \(s\) grows” corresponds to the **larger** exponent.

### A concrete first-departure formula

Suppose, in a positive-monomial setting,
\[
F(x,s)=x^A+\sum_{a,b}c_{ab}x^as^b,\qquad c_{ab}>0,\quad b>0.
\]
At the wall scale \(x=t^{-1/A}u\),
\[
t\,x^as^b=t^{1-a/A-b\gamma}u^a\sigma^b.
\]
All wall-perturbing terms disappear when
\[
\gamma>
\max_{a<A}\frac{A-a}{Ab}.
\]
Therefore the first departure occurs at
\[
\boxed{\gamma_{\rm first}
=\max_{a<A}\frac{A-a}{Ab}.}
\]
Geometrically, this selects the supporting edge adjacent to the wall vertex.

For your two-layer example,
\[
\max\left\{\frac{6-4}{6\cdot2},
\frac{6-2}{6\cdot6}\right\}
=\max\{1/6,1/9\}=1/6.
\]

This is a Newton-support characterization under the stated assumptions—not a minimum over all exceptional divisors.

### Plateaus are not simply invariants of divisor intersections

For a dominant monomial
\[
F\sim x^as^b,
\]
with smooth positive \(dx\)-density, the normalized energy is \(1/a\). With density \(|x|^h dx\), it is
\[
\frac{h+1}{a}.
\]
This explains your shared-vertex plateau.

But divisor intersections can be inserted or removed by refinements. What is meaningful is the monomial model, parameter projection, and density represented there.

There is also an important distinction between energy and the decay exponent along a path:
\[
Z(t,\sigma t^{-\gamma})
\asymp t^{-(1-b\gamma)/a},
\qquad
H_t\longrightarrow\frac1a.
\]
The exponent of \(Z\) along the path is not the energy plateau, because energy differentiates \(t\) **at fixed \(s\)**.

---

## 5. Answer to (c): several variables and weighted parameter directions

Suppose a chosen divisorial degeneration gives
\[
N=\nu_D(F),\qquad w_j=\nu_D(s_j).
\]
Its natural parameter variables are
\[
\boxed{\sigma_j=t^{w_j/N}s_j.}
\]
There is generally a vector of collapse exponents, not one scalar \(\gamma_D\).

If \(\rho\) is a weighted radial function satisfying
\[
\rho(r^{w_1}s_1,\ldots,r^{w_m}s_m)=r\rho(s),
\]
then the radial collapse variable is
\[
t^{1/N}\rho(s).
\]
For example, one can take
\[
\rho(s)=\left(\sum_j|s_j|^{L/w_j}\right)^{1/L}
\]
with suitable \(L\).

Weighted angular directions plus this radius are a useful description. Over the reals, a **weighted spherical/oriented blow-up** is often more faithful than projective space because signs and integration sectors matter.

However:

* not every divisor is relevant;
* angular loci can require further blow-ups;
* the leading parameter map can have a proper image or satisfy relations;
* valuations alone do not recover the angular dependence;
* \(\nu_D(x_i)/N\) need not describe fluctuation widths around a moving center.

The example in §8 makes the last point explicit.

### What is the Newton object?

Safe terminology includes:

* the Newton polyhedron in all \((x,s)\)-variables;
* its slices or supporting faces for prescribed parameter weights;
* parameter-dependent Newton polyhedra;
* parametric Newton-distance constructions.

There is no single universally standard “relative Newton polygon” that automatically contains all the proposed analytic information. That phrase also has other uses.

For sums of positive monomials, a particularly concrete formulation is a parametric linear program. If
\[
x_i\asymp t^{-a_i},\qquad s_j\asymp t^{-\gamma_j},
\]
then each monomial \(x^A s^B\) imposes
\[
A\cdot a+B\cdot\gamma\ge1.
\]
The leading volume exponent is obtained by minimizing the density-weighted sum of the \(a_i\), subject to these constraints. Changes of minimizing faces produce a polyhedral decomposition of parameter-rate space; positive-dimensional minimizing sets can produce logarithms.

This is closer to the multivariable replacement of your chain of edges.

---

## 6. Your relative-resolution record and the special fibre

The generic/equiresoluble locus is indeed insufficient for recovering the wall crossover. One must examine degeneration toward the excluded parameter locus.

But two cautions are essential.

First, if a modification is constructed **only over the generic open locus**, it has no specified special fibre over the wall. An extension must be constructed, and extensions are not unique.

Second, “wall = non-submersive locus of the modification” is too literal without an adapted definition. Extra blow-ups can introduce projection-critical exceptional strata without introducing a new statistical wall.

The robust formulation uses a stratification adapted to the function, projection, and density. On suitable parameter strata, the relevant resolution data are constant; at their boundaries one studies the relative asymptotic push-forward.

I cannot infer more about the particular Lean record from its name alone.

---

## 7. Answer to (d): the most relevant literature frames

I would separate three tasks.

### Fixed-parameter exponents and Newton calculations

* **Varchenko**, Newton polyhedra and asymptotics of oscillatory integrals.
* **Arnol’d–Gusein-Zade–Varchenko**, *Singularities of Differentiable Maps*, especially volume II.
* **Watanabe**, *Algebraic Geometry and Statistical Learning Theory*, for RLCTs, multiplicities, and statistical Laplace integrals.
* Work of **Greenblatt** on Newton-polyhedron methods and degenerate oscillatory/sublevel-set problems.

These support the Newton/resolution and exponent side.

### Uniformity in parameters and integration

* **Phong–Stein–Sturm**, particularly their work on growth and stability of real-analytic functions.
* **Lion–Rolin** and **Cluckers–Miller**, for parameterized integration and power/logarithm structures in subanalytic/constructible settings.
* **Melrose’s push-forward framework** for polyhomogeneous densities under suitable maps of manifolds with corners.

The last framework is conceptually very close to “resolve the joint geometry, retain the projection, and push forward the density.” Applying it to a particular Laplace problem requires the appropriate compactification and hypotheses.

### Equisingularity and zeta functions

* Resolution and equisingularity work of **Hironaka**, **Bierstone–Milman**, and others provides the geometric stratification machinery.
* **Igusa** and **Denef–Loeser** are natural for resolution formulas, candidate poles, and parameterized zeta phenomena.
* **Teissier’s polar invariants** are relevant when moving critical loci and projection geometry matter.

Lê–Ramanujam/Zariski equisingularity is useful background for constancy questions, but topological equisingularity alone is not the full framework for these density-dependent uniform profiles.

**For your specific objective, relative asymptotic integration/push-forward is the best organizing frame; Newton polygons provide computable models within it.**

---

## 8. Answer to (e): two concrete degenerate tests

First, a limitation on the requested formulation:

> In one integrated variable, a nonzero polynomial face form has only isolated zeros. A multiple face root is a degeneracy, but not a positive-dimensional zero set. If the face form is coercive, its Boltzmann integral remains perfectly valid.

Thus degeneracy does not force the outer profile to cease being a polynomial Boltzmann integral. What it can force is **additional analysis near a moving face root**, producing extra scales or competing chart contributions.

Here are two useful tests.

### Test A: the simplest extra profile, invisible in the first polygon

Take
\[
\boxed{F(x,s)=x^2\bigl((x-s)^2+s^4\bigr),\qquad s>0.}
\]
Assume \(\chi\) is smooth and positive near zero.

#### Outer layer

At \(s=\sigma t^{-1/4}\), \(x=t^{-1/4}u\),
\[
tF\longrightarrow u^2(u-\sigma)^2.
\]
This is your merging-zero profile:
\[
1/4\longrightarrow1/2.
\]

#### Further layer

For separated wells, the neighborhood of \(x=0\) contributes
\[
Z_0\sim \sqrt{\pi}\,t^{-1/2}s^{-1}.
\]
The neighborhood of \(x=s\) has the same Gaussian width, but energy offset \(s^6\):
\[
Z_s\sim \sqrt{\pi}\,t^{-1/2}s^{-1}e^{-ts^6}.
\]
Writing \(z=ts^6\),
\[
\boxed{
H_t(s)\longrightarrow
\frac12+\frac{z}{1+e^z}
}
\]
on the scale \(s=\sigma t^{-1/6}\), with \(z=\sigma^6>0\).

This is a genuine second profile—a hump, not a new plateau.

The further blow-up is explicit:
\[
x=su,\qquad
F=s^4u^2\bigl((u-1)^2+s^2\bigr).
\]
Near \(u=1\), put \(u=1+sw\):
\[
F=s^6(1+sw)^2(w^2+1).
\]
The second scale is read off there.

This shows why “layers = distinct plateau transitions” is too restrictive.

### Test B: unequal well types, producing a logarithmically shifted transition

A more stringent example is
\[
\boxed{F(x,s)=x^2\bigl((x-s)^4+s^6\bigr),\qquad s>0.}
\]

#### Outer layer: \(1/6\to1/4\)

At \(s=\sigma t^{-1/6}\), \(x=t^{-1/6}u\),
\[
tF\longrightarrow u^2(u-\sigma)^4.
\]
At \(\sigma=0\), this is \(u^6\), giving \(1/6\).

As \(\sigma\to\infty\), the quartic well near \(u=\sigma\) dominates the quadratic well near \(u=0\), giving \(1/4\). Hence
\[
1/6\longrightarrow1/4.
\]
The intermediate plateau occurs in
\[
t^{-1/6}\ll s\ll t^{-1/8}.
\]

#### Resolve the degenerate face root

Set \(x=s(1+v)\):
\[
F=s^6(1+v)^2(v^4+s^2).
\]
The further balance is \(v^4\sim s^2\). On the positive-\(s\) chart, use
\[
s=r^2,\qquad v=rw.
\]
Then
\[
F=r^{16}(1+rw)^2(w^4+1).
\]
Thus the new energy-offset scale is
\[
s\asymp t^{-1/8}.
\]

Notice:
\[
\nu_D(x)/\nu_D(F)=2/16=1/8,
\]
but the fluctuation coordinate satisfies
\[
x-s=r^3w,
\]
so its width exponent is \(3/16\), not \(1/8\). Orders of the original coordinate do not distinguish center motion from fluctuation width.

#### The two competing contributions

Put \(z=ts^8\). In the separated-well regime,
\[
Z_0\sim \sqrt{\pi}\,t^{-1/2}s^{-2},
\]
while
\[
Z_s\sim \frac{\Gamma(1/4)}2\,t^{-1/4}s^{-1/2}e^{-z}.
\]
Their ratio is
\[
Q=\frac{Z_s}{Z_0}
\sim C\,t^{1/4}s^{3/2}e^{-z}
=C\,t^{1/16}z^{3/16}e^{-z},
\qquad
C=\frac{\Gamma(1/4)}{2\sqrt{\pi}}.
\]
Consequently,
\[
\boxed{
H_t(s)\sim
\frac{\frac12+(z+\frac14)Q}{1+Q}.
}
\]
These approximations hold, in particular, through the transition region \(z=O(\log t)\).

For fixed positive \(z\), \(Q\to\infty\), so the \(s=\sigma t^{-1/8}\) profile is
\[
H_t\longrightarrow\frac14+\sigma^8.
\]
It does **not** approach the final chamber plateau as \(\sigma\to\infty\). A further nonuniform transition is still ahead.

The wells exchange dominance at \(Q\asymp1\), namely
\[
z_*(t)
=\frac1{16}\log t+\frac3{16}\log\log t+O(1).
\]
Therefore the eventual transition to \(1/2\) occurs near
\[
\boxed{
s\asymp\left(\frac{\log t}{16t}\right)^{1/8},
}
\]
not at a fixed value of \(s\,t^{1/8}\).

More precisely, define \(z_*\) by
\[
C\,t^{1/16}z_*^{3/16}e^{-z_*}=1.
\]
For \(z=z_*+w\), \(Q\to e^{-w}\), producing a logistic exchange of well masses.

The predicted structure is:

1. wall plateau \(1/6\);
2. outer crossover to \(1/4\);
3. intermediate plateau \(1/4\);
4. increasing energy from the lifted quartic well;
5. a logarithmically shifted mass-exchange region;
6. final chamber plateau \(1/2\).

The normalized energy can be of order \(\log t\) during the exchange. There is no requirement that a crossover remain between its endpoint plateaus.

This is a strong test of the conjecture: **pure-power divisorial scales alone do not describe the entire transition.**

Both local chart models are still polynomial. What fails is representation of the *whole transition* by the Boltzmann energy of one exceptional residual.

---

## 9. A revised conjecture worth formalizing

I would replace the divisor-layer bijection with something like:

> For an analytic family with specified density and parameter projection, the uniform asymptotics of its fibre Laplace integrals can be computed from compatible relative resolution data. Different compatible resolutions give equivalent pushed-forward asymptotic expansions. In Newton-adapted, uniformly integrable sectors, contributing faces yield weighted crossover models. Further face-root resolutions and competition between chart contributions may produce additional scales, logarithmic factors, and logarithmically shifted transitions.

This retains the genuinely invariant claim while avoiding resolution-dependent indexing.

For Lean, Test A is a clean next theorem: two separated Gaussian contributions with a controlled energy offset. Test B is the more discriminating target: it tests further blow-up geometry, unequal local types, and the logarithmic correction that the proposed divisor-only conjecture misses.