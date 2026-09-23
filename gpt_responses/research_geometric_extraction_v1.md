## Bottom line

For **one truth variable**, embedded resolution of
\[
F(x,s)(s-s_0)
\]
is the right next geometric construction. It can give a finite, closed-box-controlled atlas near the wall, an exact pointwise fibre formula for \(s\ne s_0\), and explicit monomial formulas for the fibre density.

But there is an important gap:

> That atlas does **not**, in general, produce a finite collection of fixed anisotropic rescalings satisfying your current `MultiDivisorData` hypotheses.

The obstructions include nonintegrable residual monomials, moving chart domains, and logarithmic factors arising from positive-dimensional optimal LP faces. These occur even for a one-parameter analytic family whose nonzero fibres have a unique nondegenerate minimum.

Thus I would split item F into:

1. **hironaka:** a wall-adapted monomial atlas with pointwise fibre integration;
2. **laplace:** analysis of the resulting constrained monomial integrals, including logarithmic sectors;
3. **a stronger optional interface:** certificates that particular sectors satisfy `MultiDivisorData`.

The existing generic relative modification does not itself supply the uniform wall control in step 1.

---

# 1. Which geometric object?

## (a) Embedded resolution: provable, and the right minimal input

Write \(s_0=0\). Resolve the divisor
\[
\{F\cdot s_1\cdots s_m=0\}.
\]
Subject to the embedded-resolution and Jacobian capabilities you list, this gives charts with
\[
F\circ g=A(z)z^K,\qquad
s_j\circ g=E_j(z)z^{Q_j},\qquad
|\det Dg|=B(z)|z|^H,
\]
where \(A,B,|E_j|\) are bounded above and away from zero on the chosen closed boxes.

Here:

- \(K=2k\) when the real nonnegativity hypotheses give even divisor orders;
- \(H\) is the exponent of the **total-space** Jacobian;
- \(Q\) records the orders of the truth coordinates.

Resolving the product monomialises its individual nonzero analytic factors: their divisors are supported on the same normal-crossing divisor.

This is a genuine wall-uniform object. It does **not** claim that the \(z\)'s are fibre coordinates.

### Special advantage when \(m=1\)

Near a point above \(s=0\), write
\[
s\circ g=E(z)z^q,\qquad q\ne0.
\]
Choose a vanishing coordinate \(z_\ell\) with \(q_\ell>0\). After shrinking, absorb the nonvanishing unit into that coordinate:
\[
z_\ell'=z_\ell |E(z)|^{1/q_\ell}.
\]
This is a local analytic coordinate change. Consequently one can arrange
\[
s\circ g=\eta z^q,\qquad \eta\in\{+1,-1\}.
\]

The phase and Jacobian remain monomial times units. On each appropriate sign orthant, \(s\ne0\) then permits an **explicit solve for \(z_\ell\)**.

This is the main reason the one-truth-variable interface is substantially easier.

## (b) Toroidalisation: potentially sufficient, but a stronger theorem

A suitably controlled toroidal morphism would be useful. However:

- toroidalisation of a morphism is not just embedded resolution of its coordinate product;
- precise theorems may involve additional hypotheses, base changes, or alterations;
- logarithmic smoothness and toroidality should not be conflated without specifying the log structures and the relevant saturation/smoothness conditions.

Also, the proposed description of fibres needs correction. For example,
\[
xy=s
\]
has hyperbolic fibres for \(s\ne0\), not unions of coordinate subspaces. Coordinate unions describe certain boundary fibres set-theoretically; multiplicities can remain, as in \(x^2y^3=s\).

For \(m>1\), product resolution can also leave independent base directions encoded in the units. For example,
\[
s_1=z_1,\qquad s_2=z_1(1+z_2)
\]
has exponent matrix of rank one, despite the map having generic rank two.

So I would **not** ask Chris to assert (b) as an automatic consequence of the currently stated toolkit.

## (c) Ray resolution: useful for examples, not the general existence statement

Weighted blow-ups and face-root iteration are excellent certificate-producing methods for Tests A/B. But:

- ordinary analytic weighted blow-ups use integral or rational weights, not arbitrary real ray weights;
- Newton nondegeneracy cannot be assumed for general analytic \(F\);
- termination of the proposed face-root algorithm is an additional theorem, unless reduced to an established resolution algorithm.

For rational power schedules, one can ramify the schedule parameter and resolve the pulled-back family. Arbitrary schedules are not analytic arcs.

**Recommendation:** construct (a), particularly its strengthened \(m=1\) form. Treat (c) as an implementation strategy for selected examples. Do not make (b) a prerequisite.

---

# 2. Pointwise fibre identities

## Over the existing generic locus

Yes: an honest fibrewise change-of-variables argument gives an identity **for every eligible \(s\in S'\)**.

It needs the usual ingredients, not merely the existence of a fibred chart:

- the restriction \(g_s\) is an isomorphism off the exceptional/zero locus;
- that omitted locus has fibre measure zero;
- chart overlaps are handled by a partition of unity or another multiplicity-correct decomposition;
- the derivative used is the actual fibre derivative.

For an analytic \(F_s\) not identically zero on a connected fibre component, its zero set has measure zero. If \(F_s\equiv0\) on a component, this argument needs a separate treatment.

A disintegration argument is unnecessary here.

## Continuity is an alternative, but not automatic

An almost-everywhere equality between two continuous functions of \(s\) extends to every \(s\) in an open set, because Lebesgue measure has full support there.

However, continuity of the original compactly supported fibre integral does **not** establish continuity of an individual resolved-chart integral. Moving domains, singular relative densities, and escape towards chart boundaries must be controlled separately.

If both sides have independently proved continuity on \(S'\), that is enough for every finite schedule point lying in \(S'\). It says nothing by itself about uniform chart control near the wall.

## You need control up to the wall, not an integral formula at the wall

This distinction is exactly right.

For \(s(t)\ne0\), the analytic argument needs:

- pointwise identities at those nonzero parameters;
- uniform resolved data on a compact neighbourhood above \(s=0\).

It does **not** need the central resolved fibre to be a smooth \(d\)-dimensional manifold, or a fibrewise change-of-variables formula at \(s=0\).

I would not formulate the requirement as “Chris’s particular generic modification extends.” An arbitrary previously chosen modification over \(S'\) need not come with such an extension.

Instead:

> Construct a new modification over a neighbourhood of the wall, resolve \(Fs\), and derive the nonzero-fibre formulas from it.

For \(m=1\), this is within the stated embedded-resolution toolkit, modulo the required formalised change-of-variables and partition-of-unity results.

---

# 3. The exact fibre integrand

Here is the calculation that should underlie the interface.

## General implicit-solve formula

Let \(n=d+m\), split the resolved coordinates as
\[
z=(u,v),\qquad u\in\mathbb R^d,\quad v\in\mathbb R^m,
\]
and suppose on a sign sector
\[
F\circ g=A(u,v)|u|^{K_J}|v|^{K_I},
\]
\[
s_j\circ g=E_j(u,v)|u|^{Q_{jJ}}|v|^{Q_{jI}},
\]
\[
|\det Dg|=B(u,v)|u|^{H_J}|v|^{H_I}.
\]

Suppose the base equations can be solved on this branch as
\[
v=V(u,s).
\]
Define the logarithmic derivative matrix
\[
M_{j\ell}(u,v)
=
\frac{v_\ell}{s_j(u,v)}
\frac{\partial s_j}{\partial v_\ell}
=
Q_{j\ell}
+
v_\ell\partial_{v_\ell}\log|E_j|.
\]
Assume \(\det M\ne0\).

The fibre density is
\[
\boxed{
D_s(u)=
\frac{B(u,V(u,s))}{|\det M(u,V(u,s))|}
\frac{|u|^{H_J}|V(u,s)|^{H_I+\mathbf1}}
{\prod_{j=1}^m|s_j|}.
}
\]

The mechanism is simply
\[
dx\,ds=|\det Dg|\,du\,dv,\qquad
du\,ds=
\left|\det\frac{\partial s}{\partial v}\right|du\,dv.
\]
Thus the relative determinant is the quotient of these two determinants.

A partition weight, the pulled-back observable/density, and the indicator of the solved chart domain multiply \(D_s\).

**Important:** \(H\) here is a total Jacobian exponent. One must not apply this quotient formula to an exponent already representing a relative Jacobian.

## Rescaling along a power ray

Let
\[
s_j(t)=\sigma_jt^{-\gamma_j},\qquad
u_i=t^{-\alpha_i}U_i,\qquad
v_\ell=t^{-\beta_\ell}V_{t,\ell}(U).
\]
For a scale with nonzero, finite leading units, the base exponent constraint is
\[
\boxed{Q_J\alpha+Q_I\beta=\gamma.}
\]

The rescaled phase is
\[
\boxed{
G_t(U)=
t^{1-K_J\cdot\alpha-K_I\cdot\beta}
A(t^{-\alpha}U,t^{-\beta}V_t(U))
|U|^{K_J}|V_t(U)|^{K_I}.
}
\]

The density normalisation is \(L(t)=t^{-\lambda}\), with
\[
\boxed{
\lambda=
(H_J+\mathbf1)\cdot\alpha+
(H_I+\mathbf1)\cdot\beta-
\sum_j\gamma_j.
}
\]
After factoring out \(L(t)\), the weight is
\[
w_t(U)=
\mathbf1_{D_t}(U)\,\Theta_t(U)
\frac{B(t^{-\alpha}U,t^{-\beta}V_t(U))}
{|\det M(t^{-\alpha}U,t^{-\beta}V_t(U))|}
\frac{|U|^{H_J}|V_t(U)|^{H_I+\mathbf1}}
{\prod_j|\sigma_j|},
\]
where \(\Theta_t\) includes the partition and original amplitude.

On an active Laplace scale,
\[
K_J\cdot\alpha+K_I\cdot\beta=1.
\]
If the remaining quantities converge appropriately, then
\[
\Phi_0(U)=A_0(U)|U|^{K_J}|V_0(U)|^{K_I}.
\]

The collapse exponents are \(\beta\); the fibre scaling exponents are \(\alpha\). They are **not uniquely determined by \((K,H,Q)\)**: the schedule and the selected LP face matter.

## Especially explicit formula for \(m=1\)

After removing the base unit, select \(v=z_\ell\), \(q_\ell>0\):
\[
|s|=|v|^{q_\ell}\prod_i|u_i|^{q_i}.
\]
On each permitted sign branch,
\[
|v|=
|s|^{1/q_\ell}\prod_i|u_i|^{-q_i/q_\ell}.
\]

Set
\[
p_s=\frac{H_\ell+1}{q_\ell}-1,\qquad
r_i=H_i-\frac{q_i(H_\ell+1)}{q_\ell},
\]
\[
\nu=\frac{K_\ell}{q_\ell},\qquad
\kappa_i=K_i-\frac{q_iK_\ell}{q_\ell}.
\]
Then
\[
\boxed{
D_s(u)=\frac{B(u,v(u,s))}{q_\ell}
|s|^{p_s}\prod_i|u_i|^{r_i},
}
\]
and
\[
\boxed{
F\circ g(u,v(u,s))
=
A(u,v(u,s))|s|^\nu\prod_i|u_i|^{\kappa_i}.
}
\]

These formulas are exact. The price is that:

- \(r_i,\kappa_i\) may be fractional or negative;
- the domain is constrained by \(v(u,s)\) remaining in the chart;
- the units now depend on the implicit solution.

If you use a collapse parameter \(|s|=\rho^{q_\ell}\), the explicit density power in \(\rho\) is
\[
p_\rho=H_\ell+1-q_\ell.
\]
This is a fibre density; there is no additional \(ds/d\rho\) factor.

## Where domination comes from—and where it does not

Positive upper and lower bounds on \(A\) give comparison with the **chart monomial**.

They give
\[
c\Phi_0\le G_t
\]
only after showing that the rescaled implicit solution contributes uniformly comparable monomial factors. In the one-parameter exact-monomial solve above, this is often straightforward on a balanced scale.

But positivity of \(A\) does **not** prove
\[
\int W e^{-c\Phi_0}<\infty,\qquad
\int W\Phi_0 e^{-c\Phi_0}<\infty.
\]
Nor does it bound \((\det M)^{-1}\), prove weight convergence, or control moving domains.

Those are separate analytic obligations. They are precisely where a raw resolution chart can fail to be `MultiDivisorData`.

---

# 4. LP organisation and the remainder

Your LP principle is correct at the level of **rates**, with two qualifications: logarithmic multiplicities, and the absence of a uniform gap between an optimal face and all other feasible points.

For a genuinely monomial base map of full row rank, the natural polyhedron is
\[
\mathcal P_\gamma
=
\{a\ge0:Qa=\gamma,\ K\cdot a\ge1\}.
\]
The candidate power exponent is
\[
\boxed{
\lambda(\gamma)=
\min_{a\in\mathcal P_\gamma}
\bigl((H+\mathbf1)\cdot a-\mathbf1\cdot\gamma\bigr).
}
\]
This describes polynomially contributing regions where \(tF\) does not grow polynomially.

It is a rate calculation, not yet an asymptotic theorem. Units, amplitudes, accessible chart regions, and possible absence of feasible scales must still be addressed.

## Why “all nonoptimal rates are negligible” is insufficient

Nonoptimal feasible vectors can approach the optimal face arbitrarily closely. There need not be a positive exponent gap.

Moreover, integration along an optimal face can create a logarithm. The optimum is not necessarily represented by finitely many isolated anisotropic scalings.

A basic example on a compact box is
\[
F(x,y,s)=x^2y^2+s^2(x^2+y^2).
\]
For every \(s\ne0\), the origin is the unique nondegenerate minimum. For
\[
s=t^{-\gamma},\qquad \gamma>\tfrac12,
\]
the \(s\)-dependent terms are uniformly negligible in the exponent, and
\[
\int_{[-1,1]^2}e^{-tF(x,y,s(t))}\,dx\,dy
\asymp t^{-1/2}\log t.
\]

The optimal scales contain the segment
\[
\alpha_x+\alpha_y=\tfrac12,\qquad \alpha_x,\alpha_y\ge0.
\]
A fixed balanced scaling leads to the residual phase \(U^2V^2\), whose exponential is not integrable on \(\mathbb R^2\).

Thus a finite sum of fixed pure-power `MultiDivisorData` limits does not capture this example. Your arbitrary-measure `RescaledData` and flexible `ChartAssembly` may accommodate a **logarithmic-sector construction**, but that construction is additional work.

## The useful packaging theorem

I would formulate the assembly theorem conditionally as follows.

> **Ray-sector asymptotic assembly.**  
> Suppose an exact pointwise fibre decomposition has been subdivided into finitely many sectors. Each retained sector has a certified normalisation
> \[
> L_\nu(t)=t^{-\lambda_\nu}(\log t)^{r_\nu}
> \]
> and a positive finite normalised limit, with the required energy and observable bounds. Suppose every discarded sector has an upper bound of the same form, or a superpolynomial bound.
>
> Let
> \[
> \lambda_*=\min_\nu\lambda_\nu,\qquad
> r_*=\max\{r_\nu:\lambda_\nu=\lambda_*\}.
> \]
> Retain sectors with \((\lambda_\nu,r_\nu)=(\lambda_*,r_*)\). Every discarded sector satisfying either
> \[
> \lambda_\nu>\lambda_*,\qquad\text{or}\qquad
> \lambda_\nu=\lambda_*,\ r_\nu<r_*
> \]
> contributes \(o(t^{-\lambda_*}(\log t)^{r_*})\).

The assembly implication is elementary and fits your existing architecture. Producing the sector certificates from constrained monomial integrals is the substantive new analytic theorem.

A lower bound \(F\ge t^{-1+\varepsilon}\) handles a different, easier class of remainder:
\[
e^{-tF}\le e^{-t^\varepsilon}.
\]
Use it when available, but do not identify it with every nonoptimal LP contribution.

---

# 5. Minimal specification for Chris

I would request the following **geometric** record first. It is deliberately weaker than “every chart supplies `MultiDivisorData`,” but it is the strongest clean specification here that follows from the stated resolution toolkit.

## Proposed record: `OneParameterWallMonomialAtlas`

Inputs:

- an open neighbourhood \(\Omega\subset\mathbb R^d\times\mathbb R\);
- analytic \(F\ge0\);
- wall parameter \(0\);
- a compact set \(K\) containing the support relevant to the fibre integrals;
- \(F_s\) not identically zero on the relevant connected fibre components for all sufficiently small \(s\ne0\).

Fields, schematically:

```text
space                  -- smooth real analytic (d+1)-manifold Y
map                    -- g : Y → Ω
map_proper
map_surjective
map_iso_off_divisor     -- off {F * s = 0}

finite_charts
chart_coordinate_maps
closed_boxes
chart_neighbourhoods   -- analytic data defined beyond each closed box

phase_exponents        -- Kν, preferably Kν = 2 kν
base_exponents         -- qν
jacobian_exponents     -- Hν
base_exponents_nonzero -- for charts meeting the central fibre

phase_unit
jacobian_unit
phase_unit_pos
unit_uniform_bounds

phase_normal_form      -- F ∘ g = Aν ∏ |z_i|^(Kν_i)
base_normal_form       -- s ∘ g = ην ∏ z_i^(qν_i)
total_jacobian_form    -- |det Dg| = Bν ∏ |z_i|^(Hν_i)

partition_weights
partition_nonnegative
partition_supported_in_charts
partition_sum_one      -- over the relevant compact pullback

small_parameter_cover -- same finite atlas covers the support for |s| < ε
```

Then either in this record or in a derived companion record:

```text
sign_branches
solve_index             -- qν_ℓ > 0
fibre_domain(s)
fibre_parameterisation(s)
fibre_phase_formula
fibre_density_formula
pointwise_fibre_integral_identity
```

The identity should quantify over **every** \(0<|s|<\varepsilon\), with suitable integrands. Schematically,
\[
\int \psi(x,s)\,dx
=
\sum_{\nu,\text{branches}}
\int_{D_\nu(s)}
(\rho_\nu\,\psi\circ g)(u,v_\nu(u,s))
D_{\nu,s}(u)\,du.
\]

Using nonnegative measurable \(\psi\), followed by an integrable signed version, makes this reusable for partition functions, energy, and observables.

## Proposed existence statement

> **One-parameter wall atlas existence.**  
> Under the preceding analytic and compact-support hypotheses, and assuming embedded resolution with monomial total Jacobian, there exist \(\varepsilon>0\) and a `OneParameterWallMonomialAtlas` giving the exact fibre identity for every \(0<|s|<\varepsilon\).

### Mechanism

1. Resolve \(Fs\) over a neighbourhood of the compact set.
2. Use properness to obtain compact control of its inverse image.
3. Cover the relevant central inverse image by finitely many normal-crossing charts.
4. Remove the base unit locally as above.
5. Shrink boxes and obtain uniform unit bounds.
6. Use compactness/properness to show these charts cover the relevant support for all sufficiently small \(|s|\).
7. Insert a subordinate partition of unity.
8. Solve one monomial base coordinate on sign branches.
9. Apply fibrewise change of variables off the analytic null set.

Steps 1–5 are the resolution-side content. Steps 6–9 require supporting topology, integration, and coordinate-change lemmas; they are not consequences of a bare normal-form equality alone.

This is a mathematical derivation from the stated toolkit, **not a claim that all these supporting lemmas already exist in the referenced Lean record**.

## What should not be included as an unconditional existence field

Embedded resolution alone does not justify fields asserting:

```text
finite_fixed_anisotropic_rescalings
each_residual_has_integrable_exponential
each_sector_is_MultiDivisorData
all_discarded_regions_have_a_positive_power_gap
no_logarithmic_normalisations
```

Nor does it justify a general multi-parameter toroidalisation theorem.

## The additional laplace-side record

A useful second record would be `RaySectorCertificate`, containing:

```text
schedule
sector_decomposition
normalisations             -- may include logarithms
pointwise_decomposition
rescaled_limit_data         -- RescaledData, or MultiDivisorData when applicable
discarded_sector_bounds
remainder_small
```

There are then two possible existence targets:

- **restricted version:** assume isolated, coercive residual sectors and the necessary domination bounds; prove certificates compatible with the present `MultiDivisorData`;
- **general one-parameter version:** develop constrained-monomial integration with logarithmic sectors, then derive certificates from `OneParameterWallMonomialAtlas`.

The second is what is needed for a genuinely general analytic wall theorem. The example above shows that restricting to one truth variable and an isolated wall does not remove the logarithmic issue.

---

## Suggested request to Chris

> Construct a finite wall-adapted embedded-resolution atlas for \(F(x,s)s\), with the base coordinate made exactly monomial, total Jacobian monomial, closed-box unit bounds, and compact uniform coverage near \(s=0\). Supply—or expose enough data to derive—an exact pointwise nonzero-fibre integration formula by solving one monomial base coordinate on sign branches.
>
> Do not require a smooth central fibre or an extension of the previously selected generic modification. Do not assert `MultiDivisorData` or negligible nonoptimal sectors as part of the resolution theorem.

That is the smallest robust geometric milestone. It handles the geometric difficulty at the wall; the remaining generality gap is then explicitly the analysis of constrained monomial integrals, rather than an unstated strengthening of relative resolution.