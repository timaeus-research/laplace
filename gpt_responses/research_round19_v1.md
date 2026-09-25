The deepest next step is to move from **response derivatives at a fixed data point** to a **stratified asymptotic response map**: a polyhedral description of rates, together with coefficient measures that vary within strata and crossover profiles that connect them.

Two corrections are important at the outset:

1. Your displayed LP value is **convex**, not concave, in \(\sigma\). The quartic example already witnesses this.
2. Fixed-\(\sigma\) asymptotics do **not** automatically become uniform asymptotics after substituting \(\sigma=\sigma(t)\), even if the LP value is evaluated at \(\sigma(t)\). The logarithmic factor is particularly sensitive to approaching walls.

## 1. The singular layer: the clean chart theorem

### A robust first theorem

Work on a positive chart \(x\in(0,1]^d\), with
\[
d\pi(x)=h(x)x^{b-1}\,dx,\qquad b_i>0,
\]
and
\[
L_t(x)=\sum_{j=1}^N k_j(t)t^{-\sigma_j}u_j(x)x^{\alpha_j}.
\]
Assume:

- \(\alpha_j\in\mathbb R_{\ge0}^d\setminus\{0\}\);
- \(h,u_j\) are bounded above and below by positive constants;
- \(0<k_-\le k_j(t)\le k_+<\infty\);
- \(\sigma\) is fixed.

Define
\[
P_\sigma=\{r\in\mathbb R_{\ge0}^d:
                   \alpha_j\cdot r+\sigma_j\ge1\ \forall j\},
\]
\[
\lambda(\sigma)=\min_{r\in P_\sigma}b\cdot r,\qquad
F_\sigma=\operatorname{argmin}_{P_\sigma}b\cdot r,
\qquad d_\sigma=\dim F_\sigma.
\]

Then the natural statement is
\[
\boxed{
Z_t=\Theta\!\left(t^{-\lambda(\sigma)}
                      (\log t)^{d_\sigma}\right).
}
\]
Thus, under the convention \(Z_t\sim Ct^{-\lambda}(\log t)^{m-1}\),
\[
m=d_\sigma+1.
\]

This is the cleanest first target because it needs neither convergence of \(k_j(t)\) nor an explicit profile integral. Comparability of coefficients cannot generally yield a limiting leading constant.

The exclusions matter:

- A constant monomial with coefficient \(t^{-\sigma}\), \(\sigma<1\), introduces stretched-exponential decay and can make this polynomial regime fail.
- Signed terms allow cancellation and invalidate the Newton/LP description without substantially stronger hypotheses.
- A density that vanishes on a controlling face can alter the answer; either incorporate that vanishing into \(b\), or require positivity where needed.

### The parametric-LP theorem

Writing \(A\) for the matrix with rows \(\alpha_j\), duality gives
\[
\lambda(\sigma)
=
\max_{\substack{y\ge0\\A^\top y\le b}}
       (1-\sigma)\cdot y.
\]

Consequently:

- \(\lambda\) is **convex**, continuous, coordinatewise nonincreasing, and piecewise affine;
- finitely many polyhedral cells suffice to fix the optimal dual face and the combinatorial type of the primal optimal face;
- \(d_\sigma\) is constant on a sufficiently refined cell decomposition, but may increase on walls.

With rational chart data, this is a rational polyhedral complex.

For your quartic chart,
\[
\lambda(\sigma)=\max\left\{\frac14,\frac{1-\sigma}{2}\right\},
\]
exactly as expected.

**Global caution:** with finitely many positive chart contributions,
\[
\lambda_{\mathrm{global}}(\sigma)=\min_\chi\lambda_\chi(\sigma).
\]
This is piecewise affine, but need not be convex. Among charts attaining the smallest exponent, take the largest logarithmic multiplicity. Merely tying two chart contributions does not create an additional logarithm.

### What follows from the existing machinery?

The separation I would enforce in Lean is:

1. **Pure polyhedral theorem:** dual representation, finite cells, affine restrictions, optimal-face dimension.
2. **Analytic comparison theorem:** chart integral is comparable to the LP scale.
3. **Refined limit theorem:** convergence to a coefficient/profile integral.

If your dominant-scale machinery already proves the monomial chart estimate with bounded positive perturbations, item 2 should be a wrapper around it. The key change of variables is
\[
x_i=e^{-(\log t)r_i},
\]
which exposes the constraints
\[
\alpha_j\cdot r+\sigma_j\ge1
\]
and a polyhedral Laplace problem whose minimizing face supplies the logarithm.

But a theorem for a moving wall parameter away from zero should not be treated as already proving a uniform theorem across the new LP walls.

### Why approaching walls is genuinely new

There is a simple logarithmic warning example:
\[
Z_t(\sigma)=\int_0^1\int_0^1
       e^{-t x(y+t^{-\sigma})}\,dx\,dy.
\]

For fixed \(0<\sigma<1\),
\[
\lambda(\sigma)=1,\qquad \dim F_\sigma=1,\qquad
Z_t(\sigma)\sim \sigma\,t^{-1}\log t.
\]
At \(\sigma=0\), the optimal face is a point and \(Z_t(0)\asymp t^{-1}\).

Now take
\[
\sigma(t)=(\log t)^{-1/2}.
\]
Then
\[
Z_t(\sigma(t))\asymp t^{-1}\sqrt{\log t},
\]
not uniformly \(t^{-1}\log t\), despite every \(\sigma(t)>0\) lying in the same open cell.

The wall variable is
\[
\tau=(\sigma-\sigma_*)\log t,
\]
or, for a general wall, its defining affine form multiplied by \(\log t\). In your quartic example this is equivalent to retaining
\[
s\,t^{1/2}=e^{-(\sigma-1/2)\log t}.
\]

So the new theorem is not just “allow moving \(\sigma\).” It is:

> Near a wall, retain the rescaled coefficient ratios of the newly competing monomials, and prove a profile limit uniform on compact sets of those ratios.

Different wall types require different normalizations: your quartic wall changes a profile constant, while the example above also interpolates logarithmic multiplicity.

---

## 2. Interior coefficient measures: a strong and attainable next layer

Here there is a particularly clean answer after **principalizing the ideal generated by the losses**, rather than merely making each loss separately monomial.

Suppose, in a fixed chart,
\[
f_i\circ\psi=x^N h_i(x),\qquad
U_a(x)=\sum_i a_i h_i(x),
\]
where \(h_i\ge0\) and \(\sum_i h_i\) is bounded below by a positive constant. Then
\[
L_a\circ\psi=x^N U_a(x).
\]
On compact subsets of the open simplex, \(U_a\) is uniformly positive.

If the original simultaneous monomial charts do not have a common monomial factor with a unit remaining, refine them by principalizing the sum ideal. This distinction makes the coefficient formula much cleaner.

### Explicit face formula

Suppose the chart density is \(H(x)x^{b-1}dx\), and set
\[
\lambda=\min_{N_i>0}\frac{b_i}{N_i},\qquad
I=\left\{i:\frac{b_i}{N_i}=\lambda\right\},\qquad m=|I|.
\]
For a test function \(\varphi\), the chart’s leading coefficient is
\[
\begin{aligned}
\mu_a^\chi(\varphi)
={}&
\frac{\Gamma(\lambda)}
     {(m-1)!\prod_{i\in I}N_i}\\
&\quad\cdot
\int
(\varphi\circ\psi)(0_I,y)\,
H(0_I,y)\,
U_a(0_I,y)^{-\lambda}
\prod_{k\notin I}y_k^{b_k-1-\lambda N_k}\,dy.
\end{aligned}
\]
This is for the positive-\(\lambda\) monomial regime; zero-loss sets of positive prior mass deserve a separate elementary case.

Summing the globally dominant charts gives
\[
t^\lambda(\log t)^{1-m}
   \int\varphi e^{-tL_a}\,d\pi
\longrightarrow \mu_a(\varphi).
\]
In particular,
\[
C(a)=\mu_a(1),\qquad
\rho_{t,a}\Rightarrow \frac{\mu_a}{C(a)}.
\]

So your proposed formula is essentially right. The integration domain is a **resolution face**, not generally the LP optimal face itself, and the monomial residue factors must be included.

### Continuity versus analyticity

Under this representation, the conclusion can be stronger than weak continuity:

> \(a\mapsto\mu_a\) is locally real analytic in total variation, provided the face integrals define finite measures and the face maps are fixed.

Indeed, all parameter dependence is in \(U_a^{-\lambda}\). Locally in the positive cone, its binomial series converges uniformly relative to a fixed integrable face measure.

For a tangent direction \(v\),
\[
D\mu_a[v](\varphi)
=
-\lambda\int
  \varphi\,U_a^{-\lambda-1}
  \Big(\sum_i v_i h_i\Big)\,d\nu,
\]
with chart factors absorbed into \(\nu\). Higher derivatives use the rising factorial \((\lambda)_n\).

This gives a genuine **singular response calculus for the limiting measure**, not just a regularity result for the leading constant.

### Lean target over `TermData`

I would first expose a representation theorem, schematically:
```lean
leadingMeasure a =
  ∑ χ in dominantTerms,
    Measure.map χ.faceMap
      (χ.faceMeasure.withDensity
        (fun y => ENNReal.ofReal ((χ.unit a y) ^ (-λ))))
```
The actual scalar coefficient can be absorbed into `faceMeasure`.

Then prove, in order:

1. positivity and local uniform lower bounds for `unit a`;
2. continuity of `a ↦ leadingMeasure a` against bounded continuous tests;
3. continuity of the normalized limiting posterior;
4. derivative formulas;
5. local analyticity in a normed space of finite signed measures.

Do not bundle uniform-in-\(a\) asymptotic convergence into the representation theorem without proving it. That is a separate, valuable consequence of uniform remainder or domination estimates on compact parameter sets.

---

## 3. Variational geometry and thermodynamic length

### Gibbs variational principle: yes, worth doing

For a probability prior, bounded measurable \(L_q\), and
\[
F_t(q)=-\log Z_t(q),
\]
the strongest useful statement is the **exact gap identity**
\[
\boxed{
tE_\rho L_q+\mathrm{KL}(\rho\|\pi)
=
F_t(q)+\mathrm{KL}(\rho\|\rho_{t,q}).
}
\]
With the appropriate extended-value conventions, this yields the variational principle and uniqueness of the Gibbs minimizer.

This buys more than convexity:

- a variational characterization of the response map;
- uniqueness of its output;
- certificates for approximate posteriors:
  an objective gap of \(\varepsilon\) is exactly a KL error of \(\varepsilon\);
- a bridge to variational inference and entropy duality.

For Lean, start with bounded losses and densities with finite KL. Establish the density/log-density identity first, then generalize to extended values. Mathlib’s `klDiv` should be a target interface, not a reason to begin with the most general measure-theoretic statement.

### It does not imply concavity along arbitrary paths

It proves concavity of \(F_t\) as a function on the convex space of data measures, because \(L_q\) depends affinely on \(q\).

But composing a concave function with a nonlinear path need not preserve concavity. Along a twice-differentiable loss path,
\[
\frac{d^2}{ds^2}F_t(L_s)
=
tE_s[\ddot L_s]
-
t^2\operatorname{Var}_s(\dot L_s).
\]
The acceleration term has no fixed sign.

That formula is a worthwhile small extension of `PathResponse.lean`.

### Thermodynamic length

Define the posterior Fisher speed by
\[
g_{t,s}=t^2\operatorname{Var}_s(\dot L_s),
\qquad
\mathcal L_t=\int_0^1\sqrt{g_{t,s}}\,ds.
\]
This is exactly the Fisher length of the induced posterior path.

Under **uniform** regular Laplace hypotheses along the path—unique global minimizer \(w_s\), uniformly positive Hessian \(H_s\), sufficient smoothness, and uniform localization—
\[
\frac{\mathcal L_t}{\sqrt t}
\longrightarrow
\int_0^1
\sqrt{\nabla\dot L_s^\top H_s^{-1}\nabla\dot L_s}\,ds.
\]
Differentiating the minimizer equation gives
\[
\dot w_s=-H_s^{-1}\nabla\dot L_s,
\]
so the limiting integrand is
\[
\sqrt{\dot w_s^\top H_s\dot w_s}.
\]

Two qualifications:

- The unnormalized length grows like \(\sqrt t\) only when this limiting length is positive.
- A loss-neutral reference is not a nondegenerate minimum. A path starting there generally needs a boundary-layer argument; the regular theorem cannot simply be integrated through that endpoint.

---

## 4. All orders: use one analytic potential

Yes. This is the right abstraction.

For bounded \(\varphi,\Delta,L_0\), define
\[
H(s,J)=
\log\int e^{-t(L_0+s\Delta)+J\varphi}\,d\pi.
\]
Then
\[
E_s[\varphi]=\partial_JH(s,0),
\]
and
\[
\partial_s^n\partial_JH(s,0)
=
(-t)^n\kappa_{n+1,s}
   (\varphi,\Delta,\ldots,\Delta).
\]

The clean foundational object is actually more general:
\[
K_\rho(z)=\log E_\rho
       \exp\left(\sum_{i=1}^k z_iX_i\right),
\]
for a finite family of bounded observables. Define joint cumulants as its derivatives at zero.

### Lean-level sequence

1. Prove the moment-generating function has a local power series, with coefficients given by integrated powers of the linear combination of observables.
2. Prove positivity on real parameters.
3. Compose with `log` to obtain real analyticity.
4. Define cumulants using higher Fréchet derivatives.
5. Derive tilt differentiation by affine composition and identification of the first derivative.

Schematic target:
```lean
iteratedDeriv n (fun s => posteriorMean t (L₀ + s • Δ) φ) s
  = (-t)^n *
      jointCumulant (posterior t (L₀ + s • Δ))
        (φ :: List.replicate n Δ)
```

Internally, finite tuples and multilinear maps will probably be cleaner than lists.

One important restraint: bounded observables make the MGF entire after complexification, but its logarithm can have complex singularities at zeros. Thus the cumulant Taylor expansion is **locally convergent**, not automatically globally convergent in \(s\).

The cheapest useful first result is analyticity of posterior expectations on finite-dimensional bounded-loss charts. The full cumulant ladder then becomes an interface theorem rather than a polynomial-induction project.

---

## 5. Ranked next five packages

This is a strategic ranking, with the cheapest entry theorem for each.

| Rank | Package | Main target | Cheapest first step |
|---|---|---|---|
| **1** | **`CoefficientResponse`** | Locally analytic leading coefficient measures and normalized limiting posteriors on open mixture simplices | Continuity of each `TermData` face integral under a uniformly positive affine unit |
| **2** | **`ValuationFan`** | LP dual formula, convex piecewise-affine chart exponents, optimal-face multiplicities, chartwise \(\Theta\)-asymptotics | Prove the finite maximum-of-affine-functions representation |
| **3** | **`WallResponseProfiles`** | Uniform crossover limits in rescaled coefficient ratios, including changing log multiplicity | Upgrade the quartic theorem to a profile uniform for \(s\sqrt t\) in compact sets |
| **4** | **`VariationalResponseGeometry`** | Gibbs gap identity, variational uniqueness, nonlinear-path Hessian, Fisher length | Density-level Gibbs gap identity; independently, the path Hessian formula |
| **5** | **`AnalyticResponse`** | Analytic chart response and all-orders cumulants from one CGF | Local power-series theorem for bounded-observable MGFs |

### Which single one best serves the stated objective?

**`CoefficientResponse`**, provided it is formulated for measures and test observables, not just \(C(a)\).

The LP fan tells you **where the asymptotic regime changes**. But inside the open simplex you already know that \((\lambda,m)\) are rigid. Those invariants therefore cannot describe most of the response variation there. The coefficient measure can:
\[
a\longmapsto
\left[
\varphi\longmapsto
\frac{\mu_a(\varphi)}{\mu_a(1)}
\right].
\]

That is the singular limiting analogue of your exact map \(q\mapsto\Phi_q\), with an explicit differential calculus.

The larger destination is then:
\[
\boxed{
\text{polyhedral rate strata}
\;+\;
\text{analytic coefficient-response maps}
\;+\;
\text{wall crossover profiles}.
}
\]
That combination—not the exponent fan alone—is a genuine map of responses from the featureless boundary into the data manifold.