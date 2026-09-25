## Executive recommendation

The organising object should be **the posterior-valued response map**
\[
\mathcal P_t:q\longmapsto \rho_{t,q},
\qquad
d\rho_{t,q}(w)=Z_t(q)^{-1}e^{-tL_q(w)}\,d\pi(w),
\]
with \(\Phi_{t,q}(\varphi)=\int\varphi\,d\rho_{t,q}\) its observable coordinates.

Its central structural feature is:

> **Mixture geometry on data is sent to exponential geometry on posteriors. The differential is a centred loss operator; its squared norm is posterior Fisher information. At zero temperature, this smooth geometry develops a stratified, multiscale boundary.**

That gives a programme with three layers:

1. **Exact:** affine loss transport, exponential tilts, covariance differentials, free-energy geometry.
2. **Asymptotic:** concentration, response scaling, degeneration of the induced metric.
3. **Singular:** relative resolution, strata, boundary layers, and transition functions between limiting responses.

Two important corrections are needed immediately:

- \(F=-\log Z\) is **concave**, not convex, on mixture lines. \(A=\log Z=-F\) is convex.
- “Maximal entropy” does **not** generally imply “constant expected loss”. The temperature-path interpretation is exact under the latter condition, not the former.

Throughout, take a fixed probability prior \(\pi\), and assume the integrability needed for each identity. A clean first formalisation uses bounded losses and observables; broader exponential-integrability hypotheses can follow.

---

# 1. The exact geometry: an affine map followed by a Gibbs map

The fundamental factorisation is
\[
q
\ \xrightarrow{\ \mathcal L\ }\ 
[L_q]\in \{\text{losses}\}/\{\text{constants}\}
\ \xrightarrow{\ \mathrm{Gibbs}_t\ }\ 
\rho_{t,q}.
\]

Constants must be quotiented out: replacing \(L_q\) by \(L_q+c\) changes \(Z\), but not any posterior expectation.

For \(t>0\), with finite losses and a common prior,
\[
\rho_{t,q}=\rho_{t,r}
\quad\Longleftrightarrow\quad
L_q-L_r\text{ is constant }\pi\text{-a.e.}
\]
Thus the response map has a natural **identifiable quotient of the data space**. Different data distributions can be indistinguishable to the model even when all posterior observables are available.

This quotient, rather than the full probability simplex, is the natural home of the geometry.

## 1.1 Mixture paths become posterior exponential geodesics

For
\[
q_s=(1-s)q_0+sq_1,\qquad
\Delta=L_{q_1}-L_{q_0},
\]
linearity of integration gives
\[
L_s=L_0+s\Delta,
\]
and hence
\[
\boxed{
\Phi_{t,q_s}(\varphi)
=
\frac{\mathbb E_{\rho_{t,q_0}}[\varphi e^{-ts\Delta}]}
{\mathbb E_{\rho_{t,q_0}}[e^{-ts\Delta}]}.
}
\]

So observation 1 is correct. For a fixed \(\varphi\), its entire response along the segment is determined by the joint law of \((\varphi,\Delta)\) under the base posterior.

This is more than an analogy with information geometry: a data **m-geodesic** maps exactly to a posterior **e-geodesic**, possibly with degeneracy.

The derivatives are
\[
\frac{d}{ds}\Phi_s(\varphi)
=-t\,\operatorname{Cov}_{\rho_s}(\varphi,\Delta),
\]
\[
\frac{d^2}{ds^2}\Phi_s(\varphi)
=t^2\,\kappa_{\rho_s}(\varphi,\Delta,\Delta).
\]
More generally,
\[
\frac{d^n}{ds^n}\Phi_s(\varphi)
=(-t)^n\kappa_{\rho_s}
(\varphi,\underbrace{\Delta,\ldots,\Delta}_{n}).
\]

These are derivative identities under appropriate domination. Calling them a *convergent cumulant expansion* additionally requires a local analyticity or exponential-moment hypothesis.

A particularly useful consequence is
\[
\frac{d}{ds}\mathbb E_{\rho_s}\Delta
=-t\,\operatorname{Var}_{\rho_s}(\Delta)\le 0.
\]
The posterior moves monotonically toward parameters favoured by the endpoint loss contrast—not toward increasing values of every observable.

---

# 2. Free energy, the influence operator, and the response metric

Write
\[
A_t(q)=\log Z_t(q),\qquad F_t(q)=-A_t(q).
\]
For a zero-mass signed perturbation \(h\), let
\[
R_h(w)=\int \ell(w,x)\,dh(x).
\]

In affine data coordinates,
\[
DA_t(q)[h]=-t\,\mathbb E_{\rho_{t,q}}R_h,
\]
\[
D^2A_t(q)[h,k]
=t^2\operatorname{Cov}_{\rho_{t,q}}(R_h,R_k).
\]
Consequently,
\[
D^2F_t(q)[h,h]
=-t^2\operatorname{Var}_{\rho_{t,q}}(R_h)\le0.
\]

Thus the same covariance object is simultaneously:

- the Hessian of the log partition function;
- minus the Hessian of the free energy;
- the Fisher information of the posterior family in data directions;
- the squared size of infinitesimal posterior response.

## 2.1 The differential is a centred loss operator

The posterior score in direction \(h\) is
\[
S_{q,h}(w)
=-t\bigl(R_h(w)-\mathbb E_{\rho_{t,q}}R_h\bigr).
\]
Therefore
\[
\boxed{
D\Phi_{t,q}[h](\varphi)
=\mathbb E_{\rho_{t,q}}[\varphi S_{q,h}]
=-t\,\operatorname{Cov}_{\rho_{t,q}}(\varphi,R_h).
}
\]

Define
\[
g_{t,q}(h,k)
=\mathbb E_{\rho_{t,q}}[S_{q,h}S_{q,k}]
=t^2\operatorname{Cov}_{\rho_{t,q}}(R_h,R_k).
\]

This is generally a **pseudometric**, not a metric:
\[
g_{t,q}(h,h)=0
\quad\Longleftrightarrow\quad
R_h\text{ is constant }\rho_{t,q}\text{-a.e.}
\]
For finite losses, this is the same a.e. condition under \(\pi\). It becomes a metric after quotienting invisible directions, subject to the usual manifold regularity issues.

Its operational meaning is especially clean:
\[
|D\Phi_{t,q}[h](\varphi)|
\le
\sqrt{\operatorname{Var}_{\rho_{t,q}}(\varphi)}
\sqrt{g_{t,q}(h,h)}.
\]
Indeed,
\[
\boxed{
g_{t,q}(h,h)
=
\sup_{\operatorname{Var}_{\rho_{t,q}}(\varphi)\le1}
|D\Phi_{t,q}[h](\varphi)|^2.
}
\]
This characterises the metric as **maximal standardised observable response**.

That is probably the best conceptual bridge between the existing susceptibility machinery and “mapping responses across data”.

## 2.2 A response kernel on data

Subject to Fubini and square-integrability,
\[
g_{t,q}(h,k)
=\iint K_{t,q}(x,y)\,dh(x)\,dk(y),
\]
where
\[
K_{t,q}(x,y)
=t^2\operatorname{Cov}_{\rho_{t,q}}
\bigl(\ell(\cdot,x),\ell(\cdot,y)\bigr).
\]

This gives a response-based similarity between data points. It also suggests a spectral programme: the principal eigenmodes of this kernel are data perturbations to which the posterior is most sensitive.

For contamination \(q_\varepsilon=(1-\varepsilon)q+\varepsilon\delta_x\),
\[
R_{\delta_x-q}(w)=\ell(w,x)-L_q(w).
\]
Hence the contamination influence function is
\[
-t\,\operatorname{Cov}_{\rho_{t,q}}
\bigl(\varphi,\ell(\cdot,x)-L_q\bigr).
\]
The subtraction matters when connecting a distributional tangent to existing BIF conventions.

## 2.3 Exact KL–Bregman correspondence

There is a load-bearing global identity:
\[
\boxed{
D_{\mathrm{KL}}(\rho_{t,q}\Vert\rho_{t,r})
=
A_t(r)-A_t(q)-DA_t(q)[r-q].
}
\]

Thus posterior KL divergence is the Bregman divergence of the convex potential \(A_t\), with the displayed orientation.

This packages convexity, the Fisher metric, and identifiability into one theorem. In finite-dimensional identifiable affine coordinates, the dual coordinates are
\[
\partial_i A_t=-t\,\mathbb E_{\rho_{t,q}}R_i.
\]
A full Legendre diffeomorphism needs strict convexity and suitable domain/boundary hypotheses; it is not automatic on the original data simplex.

## 2.4 What variational principle does this give?

For a probability prior,
\[
F_t(q)
=
\inf_{\rho\ll\pi}
\left\{
t\,\mathbb E_\rho L_q
+D_{\mathrm{KL}}(\rho\Vert\pi)
\right\}.
\]
This also proves concavity in \(q\): an infimum of affine functions is concave.

It does **not** intrinsically select the true data distribution. Optimising over \(q\) becomes a meaningful problem only after specifying an objective and constraints—experimental design, robustness, an adversary, entropy constraints, and so forth.

---

# 3. “Featureless” and the choice of path

## 3.1 The temperature-path identity is exact under posterior neutrality

If
\[
L_{q_0}(w)=c\qquad\pi\text{-a.e.},
\]
then
\[
L_{q_s}=(1-s)c+sL_{q_1},
\]
so
\[
\boxed{\rho_{t,q_s}=\rho_{ts,q_1}},
\qquad
Z_t(q_s)=e^{-t(1-s)c}Z_{ts}(q_1).
\]

I would call this condition **loss-neutrality** or **posterior neutrality**. It is model- and loss-dependent.

Under this condition, the note’s temperature family is exactly a mixture-path family. More precisely, the governing coordinate is \(\tau=ts\): large-\(t\) asymptotics describe every fixed \(s>0\), while the departure from the neutral endpoint occurs in an \(s\sim t^{-1}\) boundary layer when the relevant loss scale is order one.

But neutrality is not synonymous with maximal entropy.

### Examples and nonexamples

- **Uniform labels with deterministic \(0\)-\(1\) classification:** risk is \(1-1/K\), independent of the classifier. This is neutral.
- **Uniform labels with cross-entropy:** generally not neutral:
  \[
  -\frac1K\sum_{y=1}^K\log p_w(y)
  =\log K+D_{\mathrm{KL}}(U\Vert p_w).
  \]
  Uniform labels favour uniform predictions.
- **Independent, zero-mean noise with squared loss:** generally produces a term involving \(\|f_w\|^2\), so is not neutral unless that energy is constant.
- **Symmetry models:** an invariant data distribution can be neutral when a transitive parameter symmetry makes all parameters have equal expected loss.

Moreover, maximal entropy requires a specified reference measure and constraints; on many unbounded spaces there is no unconstrained maximiser.

So the useful statement is:

> **A neutral reference distribution makes mixture strength identical to inverse temperature. A maximum-entropy reference may or may not be neutral.**

When \(L_0\) is nonconstant, one still has an exact tilt from \(\rho_{t,q_0}\). This base posterior is a temperature-dependent effective prior; it is not generally the original prior.

## 3.2 Which coordinate should be used?

There is no universally correct scalar coordinate on data space.

- **Mixture weight:** best for the current formalisation and for adding/removing populations or patterns.
- **Exponential parameter:** best when log density ratios or sufficient statistics are the natural intervention.
- **Entropy or KL:** useful summaries, but they discard direction. Two equally entropic distributions can have entirely different loss images and responses.
- **Posterior thermodynamic length:**
  \[
  \mathcal L_t(q_\bullet)
  =\int\sqrt{g_{t,q_s}(\dot q_s,\dot q_s)}\,ds
  \]
  measures how far the posterior actually travels, independent of path parametrisation.

Recommendation: use mixture coordinates as the primary exact coordinates, and response length as an intrinsic diagnostic. Treat entropy and data KL as annotations, not as complete response coordinates.

---

# 4. Exponential data paths: a genuine but different calculus

Assume compatible supports and sufficient integrability. Write
\[
q_s(dx)=e^{sa(x)-\psi(s)}q_0(dx),
\qquad
a=\log\frac{dq_1}{dq_0}.
\]
Then
\[
\dot L_s(w)
=\operatorname{Cov}_{q_s}(\ell(w,X),a(X)),
\]
and
\[
\ddot L_s(w)
=\kappa_{q_s}(\ell(w,X),a(X),a(X)).
\]

On the posterior side,
\[
\frac d{ds}\Phi_s(\varphi)
=-t\,\operatorname{Cov}_{\rho_s}(\varphi,\dot L_s),
\]
\[
\boxed{
\frac {d^2}{ds^2}\Phi_s(\varphi)
=
t^2\kappa_{\rho_s}(\varphi,\dot L_s,\dot L_s)
-t\,\operatorname{Cov}_{\rho_s}(\varphi,\ddot L_s).
}
\]

The second term is the curvature of the loss path. Correspondingly,
\[
F''(s)
=t\,\mathbb E_{\rho_s}\ddot L_s
-t^2\operatorname{Var}_{\rho_s}(\dot L_s),
\]
which has no universal sign.

The compelling duality is therefore asymmetric:

> Data m-geodesics become posterior e-geodesics exactly. Data e-geodesics generally become curved posterior paths.

Do not expect preservation of both Amari connections, or equality between data Fisher information and the pulled-back posterior Fisher information, without strong additional structure.

---

# 5. The singular layer: what is actually stratified?

First remove the minimum:
\[
m(q)=\inf_w L_q(w),\qquad
\widetilde L_q=L_q-m(q).
\]
The zero locus relevant to resolution is that of \(\widetilde L_q\), not necessarily that of \(L_q\).

A typical expansion is
\[
Z_t(q)
=
e^{-tm(q)}
t^{-\lambda(q)}
(\log t)^{k(q)-1}
\bigl(C(q)+o(1)\bigr).
\]
For observables, one seeks a coefficient functional
\[
\int\varphi e^{-t\widetilde L_q}\,d\pi
=
t^{-\lambda(q)}(\log t)^{k(q)-1}
\bigl(\mu_q(\varphi)+o(1)\bigr),
\]
giving
\[
\Phi_{t,q}(\varphi)\longrightarrow
\frac{\mu_q(\varphi)}{\mu_q(1)}.
\]

The asymptotic response object is thus not just \(\lambda(q)\), but
\[
\boxed{
\bigl(m(q),\lambda(q),k(q),\mu_q,\text{transition scales}\bigr).
}
\]

At every finite \(t\), the posterior can remain smooth while its limit changes discontinuously. The phase diagram belongs to the **nonuniform low-temperature limit**, not necessarily to the finite-temperature map.

## 5.1 Three notions that must be separated

### A. Fixed parameter, fixed resolution data

If a relative resolution has fixed monomial exponents and positive units bounded away from zero, then the exponents do not “move continuously with \(q\)”. They are discrete data.

Within such a region, one expects fixed \((\lambda,k)\) and varying coefficients. Analytic dependence of those coefficients requires suitable relative-resolution and analytic hypotheses. For a moving limiting measure, analyticity should be formulated against an appropriate class of analytic test functions—not arbitrary continuous observables.

### B. Parameter degeneration

When a coefficient vanishes, a minimum changes type, or competing minimum branches exchange dominance, the resolution type can change.

A fixed zero locus is not enough for fixed exponents:
\[
L_s(w)=w^4+s w^2,\qquad s\ge0.
\]
Its zero locus is always \(\{0\}\), but
\[
\lambda(0)=\tfrac14,\qquad
\lambda(s)=\tfrac12\quad(s>0).
\]

### C. Temperature-dependent parameters

Let \(s=t^{-\sigma}\) in the same example. The dominant width is
\[
w\asymp t^{-r},\qquad
r=\max\left\{\tfrac14,\frac{1-\sigma}{2}\right\},
\]
so
\[
\lambda_{\mathrm{eff}}(\sigma)
=
\max\left\{\tfrac14,\frac{1-\sigma}{2}\right\}.
\]

This is where **piecewise-linear exponents** naturally appear. They are exponents of a coupled \(q(t),t\) limit, not ordinary fixed-\(q\) RLCTs.

The crossover variable here is \(s\,t^{1/2}\), not \(st\). PatternAttenuation’s \(st\) scale is an important special case, not a universal law.

## 5.2 What moves in the germbij LP?

For a positive monomial-sum chart of the schematic form
\[
\widetilde L_{q(t)}(x)
\asymp\sum_j t^{-\sigma_j}x^{\alpha_j},
\qquad
d\pi\asymp x^{b-1}\,dx,
\]
the scaling LP is
\[
\lambda_{\rm chart}(\sigma)
=
\min_{r\ge0}
\left\{
b\cdot r:
\alpha_j\cdot r+\sigma_j\ge1\ \forall j
\right\}.
\]

Here:

- \(\alpha_j,b\) are fixed resolution/Newton data;
- coefficient valuations \(\sigma_j\) move the constraint offsets;
- active faces change across polyhedral walls;
- the value is piecewise affine where the finite LP description applies;
- logarithmic multiplicities are controlled by the relevant optimal-face data.

For a fixed chart, the value is a maximum of affine functions through LP duality. Taking the minimum over contributing charts can destroy global convexity.

Crucially, **ties usually produce changes of slope or logarithmic multiplicity, not jumps in the LP value**. At ties, positive leading chart contributions add.

So the proposed phrase should be replaced by:

> Fixed-parameter singular types can be locally constant on suitable strata; coupled degeneration exponents are piecewise affine in valuation coordinates, with changes of active face and possible changes of logarithmic multiplicity.

Neither statement holds automatically over an unrestricted, infinite-dimensional space of distributions.

## 5.3 What common-minimiser rigidity really gives

Let \(f_i\ge0\) be losses after subtracting their individual minima, with a common zero. For weights \(a_i>0\),
\[
L_a=\sum_i a_i f_i.
\]
On any compact subset of the open weight simplex, \(L_a\) is uniformly comparable to
\[
G=\sum_i f_i.
\]
Hence all such mixtures have the same leading power and log multiplicity whenever these are defined.

This is a robust interior-stratum theorem. It does **not** imply that the coefficient measure or limiting posterior is constant.

## 5.4 Competing minima give another class of transition scales

If several minimum branches contribute,
\[
Z_t(q)\sim
\sum_i e^{-tm_i(q)}
t^{-\lambda_i(q)}
(\log t)^{k_i(q)-1}C_i(q).
\]
Their competition involves energy gaps, power laws, logarithms, and coefficients. A transition can occur when
\[
t(m_i-m_j)+(\lambda_i-\lambda_j)\log t
-(k_i-k_j)\log\log t-\log(C_i/C_j)
=O(1).
\]

This is the other major ingredient of a general phase diagram, beyond vanishing mixture weights.

---

# 6. What is preserved, and what is “created”, along the homotopy?

For finite losses, finite \(t\), and a fixed prior:

- all posteriors are equivalent to the prior;
- no new posterior support is created;
- mixture loss contrasts give a fixed identifiable quotient;
- the response family is smooth under domination;
- common-minimiser positive mixtures preserve \((\lambda,k)\) in their interior.

What can change:

- relative masses of parameter regions;
- modes and observable expectations;
- sensitivity eigenmodes and metric conditioning;
- low-temperature limiting support;
- leading coefficient measures;
- asymptotic singular type at boundary strata.

Thus “features appearing” should mean an operational change—an observable crossing a threshold, a response mode becoming appreciable, or a limiting component acquiring weight. It need not be a literal finite-temperature singularity.

The metric need not have a universal large-\(t\) scaling. At a regular minimum, perturbations that move the minimiser can produce \(g_t\) of order \(t\); other directions can be smaller. At singularities, the scaling becomes anisotropic and can itself be part of the phase diagram.

---

# 7. First five theorem packages to formalise

I would begin in a finite-dimensional affine family
\[
L_a=L_*+\sum_i a_iR_i,
\]
with a finite index type, a probability prior, and bounded measurable \(L_*,R_i,\varphi\). This avoids building a manifold of measures before proving the mathematics.

The statements below are Lean-level specifications, not claims about existing declaration names.

## 1. Mixture tilt representation, with neutral-baseline corollary

**Statement**
\[
\operatorname{postExp}(t,L_0+s\Delta,\varphi)
=
\frac{\operatorname{postExp}(t,L_0,\varphi e^{-ts\Delta})}
{\operatorname{postExp}(t,L_0,e^{-ts\Delta})}.
\]

**Hypotheses:** integrable numerator and denominators, positive finite normalisers. Bounded losses and observables under a probability prior suffice.

**Corollary**
\[
L_0=c
\Longrightarrow
\operatorname{postExp}(t,(1-s)L_0+sL_1,\varphi)
=
\operatorname{postExp}(ts,L_1,\varphi).
\]

**Cost:** very low; algebraic factorisation and normalisation.

**Cheapest first step:** prove this entirely at the loss-function level, without defining data distributions.

## 2. Mixture response derivative and second cumulant

**Statement**
```text
HasDerivAt
  (fun s => postExp t (L + s • R) φ)
  (-t * postCov t (L + s • R) φ R)
  s
```
with the second-derivative formula
\[
t^2\left(
E[\varphi R^2]
-2E[R]E[\varphi R]
-E[\varphi]E[R^2]
+2E[\varphi]E[R]^2
\right).
\]

**Hypotheses:** the compact-window domination used by `TiltInterpolation`.

**Cost:** first derivative is a wrapper around `hasDerivAt_tiltExp`; second derivative needs a small expectation-product calculus.

**Immediate corollary:** monotonicity of \(E_sR\).

## 3. Free-energy concavity and Hessian identity

**Statement**
\[
F'(s)=tE_sR,\qquad
F''(s)=-t^2\operatorname{Var}_sR,
\]
and `ConcaveOn` for \(F\) on the admissible interval.

**Hypotheses:** positive normalisers and the preceding derivative assumptions.

**Cost:** modest. The local derivative theorem is cheap; global concavity needs the relevant real-analysis bridge.

**Follow-on:** KL–Bregman identity. The mathematics is elementary, but its formal cost depends on how conveniently posterior KL is represented in the repository.

## 4. Influence operator and positive-semidefinite response form

For coefficient directions \(v\), define
\[
R_v=\sum_i v_iR_i,\qquad
S_a(v)=-t(R_v-E_aR_v).
\]

**Statements**

- \(v\mapsto S_a(v)\) is linear;
- observable directional derivatives equal \(E_a[\varphi S_a(v)]\);
- \(g_a(v,u)=E_a[S_a(v)S_a(u)]\) is bilinear and symmetric;
- \(g_a(v,v)\ge0\);
- its nullspace consists exactly of a.e.-constant loss directions;
- the covariance response bound holds.

**Cost:** moderate but mostly algebraic. Establish the directional theorem first; package a Fréchet derivative only afterward.

This theorem turns the response map into a genuine geometric object.

## 5. Uniform interior rigidity for finite mixtures

Let \(f_i\ge0\), \(G=\sum_i f_i\), and suppose
\[
0<c\le a_i\le C.
\]
Then
\[
cG\le L_a\le CG
\]
and, for \(t\ge0\),
\[
\boxed{
Z_G(Ct)\le Z_{L_a}(t)\le Z_G(ct).
}
\]

**Consequences:** if \(Z_G\) has a known power-log order, then every \(L_a\) has the same order, uniformly over the weight region.

**Hypotheses for the singular interpretation:** a common zero after subtracting individual minima, and the reference power-log theorem.

**Cost:** low, reusing positivity and the attenuation layer.

**Important boundary:** this proves uniform order bounds, not a uniform coefficient-measure expansion.

---

# 8. Cheap extensions versus the real research frontier

| Component | Mathematical status | Formalisation assessment |
|---|---|---|
| Mixture tilt and neutral-path identity | Immediate exact algebra | Very cheap |
| First/second response derivatives | Existing tilt calculus | Cheap |
| Free-energy concavity | Standard covariance calculus | Cheap–moderate |
| Influence pseudometric, finite-dimensional Fisher identity | Standard information geometry in explicit coordinates | Moderate |
| KL–Bregman identity | Standard exponential-family identity | Moderate, library-dependent |
| e-path first/second derivatives | Standard nested differentiation | Moderate; new domination bookkeeping |
| All-order convergent cumulant expansion | Standard with analytic hypotheses | Larger infrastructure |
| Uniform interior mixture order | Comparison argument | Cheap |
| Relative coefficient measures and parameter derivatives | Substantial parameter-uniform analysis | Major |
| Uniform transitions across singular strata | Main research target | Major |

The exact layer is already largely present in the seabed. Its novelty would be **organisation and synthesis**, not new covariance identities.

The substantial mathematical work lies in making singular asymptotics **relative, uniform, and compatible with differentiation and transitions**.

---

# 9. The single deepest target

I would aim at a:

## Uniform stratified response theorem

For a specified finite-dimensional analytic/tame family of data laws, prove that after a suitable parameter stratification and relative resolution, there is a chart-independent asymptotic description of
\[
q\longmapsto
\bigl(Z_t(q),\Phi_{t,q},D\Phi_{t,q},g_{t,q}\bigr)
\]
which:

1. is uniform on compact subsets of each stratum;
2. gives the coefficient measure and singular orders there;
3. resolves approach to boundary strata using explicit scaled coordinates;
4. supplies transition functions between adjacent asymptotic regimes;
5. permits the required derivatives through controlled remainders;
6. agrees on overlapping resolution charts.

Uniformity of function values alone is not enough for item 5; derivative control must be part of the theorem.

A useful generating object is
\[
\mathcal Z_t(q,J)
=
\int e^{-t(L_q-m(q))+J(w)}\,d\pi(w),
\]
initially with \(J\) in a finite-dimensional space of bounded analytic observables. Derivatives in \(J\) generate expectations and cumulants; derivatives in data directions generate influence and response geometry. A uniform relative asymptotic theorem for this one object would organise much of the programme.

The conceptual endpoint is:

> **Resolution should not merely explain one posterior’s asymptotics. It should provide an atlas for how the entire posterior response geometry degenerates as the data distribution changes.**

That is the natural extension of germbij: from the singular germ of a loss to the **relative singular geometry of a family of statistical responses**.