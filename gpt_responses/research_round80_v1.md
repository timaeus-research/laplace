## Recommendation

Use **globally C¹ paths with zero endpoint velocities**, define the real-valued length metric on the original vector space `W`, and only then put that metric on a wrapper type.

For Hellinger, use **scalar calculus against the endpoint chord**. This avoids both `Lp`-valued differentiation and Riemann-sum infrastructure.

For completion accessibility, your infinite concatenation argument is correct. Package it as a reusable finite-length-realisation theorem. For uniqueness over a facet, your argument is also correct **once arbitrary-sequence facet asymptotics have been established**; do not silently import a result proved only along the data path.

Two hypothesis audits first:

1. With
   \[
   P_\theta\propto e^{-\langle\theta,S\rangle}\nu,
   \]
   the derivative of the mean is **minus** covariance. Your displayed derivative theorem has the opposite sign. All norm estimates below are unaffected, but the scalar derivative identities must use a consistent convention.

2. The shell criterion needs its actual facet-charge hypotheses carried forward. For example, for uniform \(\nu\) on \([0,1]\), slack \(g(x)=x\) has summable square roots of dyadic shell masses, but the concentrating ray has speed asymptotic to \(1/r\), hence infinite length. Thus the shell statement, interpreted literally without a charged-face or equivalent additional hypothesis, is false. This is an audit of the abbreviated statement, not an objection to the landed theorem with its full hypotheses.

---

# Q1. The path class and metric

Write
\[
G(\theta,w)=\operatorname{Var}_{P_\theta}\langle w,S\rangle,
\qquad
F(\theta,w)=\sqrt{G(\theta,w)}.
\]

The first infrastructure should expose:

* joint continuity of `F` in \((\theta,w)\);
* `F θ (c • w) = |c| * F θ w`;
* `0 ≤ F θ w`;
* a global bound `F θ w ≤ K * ‖w‖`.

The missing joint continuity in the parameter is worth landing immediately; continuity in `w` alone does not suffice for the path API.

## Definition I would use

Schematic Lean, with paths and velocities valued in the existing normed space `W`:

```lean
structure FisherPath (x y : W) where
  toFun : ℝ → W
  vel : ℝ → W
  hasDerivAt : ∀ t, HasDerivAt toFun (vel t) t
  continuous_vel : Continuous vel
  source : toFun 0 = x
  target : toFun 1 = y
  vel_zero : vel 0 = 0
  vel_one : vel 1 = 0
```

Then

```lean
def FisherPath.length (p : FisherPath x y) : ℝ :=
  ∫ t in (0 : ℝ)..1, F (p.toFun t) (p.vel t)

def fisherDist (x y : W) : ℝ :=
  sInf {L | ∃ p : FisherPath x y, p.length = L}
```

The set is nonempty and bounded below by zero. A real `sInf` is reasonable here: all admissible paths have finite length, and segments establish nonemptiness. An `ENNReal` infimum is also possible, but introduces conversions with no immediate benefit.

**Why this class?**

* Zero endpoint velocities make finite and countable concatenation cheap.
* Global derivatives avoid endpoint `WithinAt` qualifications throughout the main path API.
* Segments become admissible after a single fixed reparametrisation.
* Any C¹ path on a compact interval can be converted to this class without changing length.

It is not the weakest mathematical class. It is the best fit for your existing C¹ facet theorem.

## The one reparametrisation lemma

Let
\[
\phi(t)=3t^2-2t^3.
\]
On \([0,1]\), it is increasing, maps endpoints to endpoints, and has zero endpoint derivative.

For a C¹ curve \(\gamma\),
\[
\widetilde\gamma(t)=\gamma(\phi(t)),\qquad
\widetilde\gamma'(t)=\phi'(t)\gamma'(\phi(t)).
\]
Hence
\[
F(\widetilde\gamma(t),\widetilde\gamma'(t))
=\phi'(t)F(\gamma(\phi(t)),\gamma'(\phi(t)))
\]
on \([0,1]\).

The change of variables you need is exactly
\[
\int_0^1 f(\phi(t))\phi'(t)\,dt=\int_0^1f(s)\,ds
\]
for continuous `f`.

I would prove this once using the primitive
\[
A(s)=\int_0^s f(q)\,dq,
\]
the chain rule, and the fundamental theorem of calculus. That avoids relying on the exact signature of a general substitution theorem. The relevant Mathlib families are `intervalIntegral.integral_hasDerivAt` and `intervalIntegral.integral_eq_sub_of_hasDerivAt`; check their current endpoint and integrability arguments locally.

Notice that \(\phi\) need not map all of \(\mathbb R\) into \([0,1]\). The supplied paths are globally defined.

## Concatenation

Define
\[
(p*q)(t)=
\begin{cases}
p(2t),&t\leq \frac12,\\
q(2t-1),&t>\frac12.
\end{cases}
\]

At the junction:

* values agree because `p.target = q.source`;
* left derivative is \(2p'(1)=0\);
* right derivative is \(2q'(0)=0\).

Yes: the robust proof is to establish the derivative within `Iic (1/2)` and `Ici (1/2)`, combine the two within-derivatives on their union, and discharge that the union is `univ`. Whether the exact convenience lemma is named `HasDerivWithinAt.union` in your checkout is an API detail; this is the right proof shape.

Do the same pasting argument for continuity of the proposed velocity. Land this as a **generic C¹ pasting lemma**, independent of probability.

Affine substitution on the two halves gives
\[
L(p*q)=L(p)+L(q).
\]
The metric triangle inequality then uses near-minimisers with error \(\varepsilon/2\).

Reversal gives symmetry. Flattened segments give finiteness.

I would not start with piecewise C¹, a.e. derivatives, or a dual definition of distance. Each moves work into machinery you will eventually have to reconcile with the existing facet theorem.

---

# Q2. Positivity and topology

Your plan is sound. In fact, it avoids local coercivity entirely.

Choose a common bound
\[
|S_j(x)|\leq B
\]
and write \(N=\#J\). In the usual Lean Pi norm,
\[
\|w\|=\max_j|w_j|,
\qquad
|\langle w,S(x)\rangle|\leq NB\|w\|.
\]
Your landed variance bound therefore gives
\[
F(\theta,w)\leq NB\|w\|.
\]

Thus one may take
\[
K=NB,\qquad d_F(\theta,\eta)\leq K\|\theta-\eta\|.
\]

For the mean, coordinatewise Cauchy–Schwarz gives
\[
\left|\frac d{dt}m_j(\gamma(t))\right|
\leq B\,F(\gamma(t),\gamma'(t)).
\]
Because the target has the sup norm,
\[
\|m(\theta)-m(\eta)\|\leq B\,L(\gamma),
\]
and consequently
\[
\boxed{\ \|m(\theta)-m(\eta)\|\leq B\,d_F(\theta,\eta).\ }
\]

There is **no extra cardinality factor** in this last bound. Cardinality entered only when bounding `dirLoss` using the Pi norm.

The clean Lean proof is coordinatewise scalar FTC followed by the Pi-norm bound. You do not need vector-valued integration.

Consequences:

* `d_F θ η = 0` implies equal means, hence equal parameters.
* Euclidean convergence implies Fisher convergence by the global segment bound.
* Fisher convergence implies mean convergence, then parameter convergence by the inverse chart.

For the last step, lift `m` into `intrinsicInterior P` and use the subspace topology plus the chart inverse. This is a local/topological assertion, **not** uniform equivalence of the two metrics.

Also land the subinterval estimate:
\[
\|m(\gamma(t))-m(\gamma(a))\|
\leq B\int_a^tF(\gamma(s),\gamma'(s))\,ds.
\]
It is exactly what controls wandering in Q5.

---

# Q3. Hellinger: use one scalar test function, not full duality

The cleanest route is a sharpened Route B:

> Test against the difference of the two endpoint square-root densities.

No supremum over test functions is needed.

Set
\[
Z(\theta)=\int e^{-\langle\theta,S\rangle}\,d\nu,\qquad
q_\theta=\sqrt{p_\theta}
=\frac{e^{-\langle\theta,S\rangle/2}}{\sqrt{Z(\theta)}}.
\]
Then \(\|q_\theta\|_2=1\).

For a path from \(a\) to \(b\), put
\[
h=q_b-q_a,\qquad H=\|h\|_2,
\qquad
A(t)=\int q_{\gamma(t)}h\,d\nu.
\]
The scalar derivative is
\[
A'(t)
=-\frac12\int hq_{\gamma(t)}
  \bigl(\ell_t-E_{P_{\gamma(t)}}\ell_t\bigr)\,d\nu.
\]
Cauchy–Schwarz gives
\[
|A'(t)|
\leq \frac12 H
\left(
\int q_{\gamma(t)}^2
  \bigl(\ell_t-E\ell_t\bigr)^2\,d\nu
\right)^{1/2}
=\frac12H\,F(\gamma(t),\gamma'(t)).
\]

But
\[
A(1)-A(0)=\int(q_b-q_a)^2\,d\nu=H^2.
\]
Scalar FTC now gives
\[
H^2\leq \frac12H\,L(\gamma).
\]
Split on `H = 0` and cancel otherwise:
\[
\boxed{\ H\leq \tfrac12L(\gamma).\ }
\]
Taking the infimum proves the desired contraction.

## Use the affinity identity to simplify the scalar differentiation

Your exact identity is valuable:
\[
\mathcal A(\theta,z)
=\int q_\theta q_z\,d\nu
=\frac{Z((\theta+z)/2)}{\sqrt{Z(\theta)Z(z)}}.
\]

Since
\[
A(t)=\mathcal A(\gamma(t),b)-\mathcal A(\gamma(t),a),
\]
you can obtain `HasDerivAt A` by differentiating this finite-dimensional expression in partition functions, then rewrite the derivative as the integral above.

This is a useful combination of **Route D’s algebra and Route B’s estimate**. It eliminates both:

* differentiation of an `Lp`-valued map;
* differentiation under an integral with a general `Lp` test function.

All fixed-parameter square-root densities are bounded because `S` is bounded. Thus the remaining integrability and algebraic integral rewrites are elementary probability-space facts.

## Suggested lemma statements

In mathematical form, to be translated into your existing notation:

1. `sqrtDensity_sq`:
   \[
   q_\theta^2=p_\theta.
   \]

2. `integral_sqrtDensity_sq`:
   \[
   \int q_\theta^2\,d\nu=1.
   \]

3. `sqrtDensity_memLp`:
   ```lean
   MemLp (sqrtDensity θ) 2 ν
   ```

4. `affinity_eq_partition`:
   \[
   \int q_\theta q_\eta\,d\nu
   =Z((\theta+\eta)/2)/\sqrt{Z(\theta)Z(\eta)}.
   \]

5. `hasDerivAt_affinity_curve`: the scalar derivative formula above with fixed endpoint `z`.

6. `abs_chordPairing_deriv_le`:
   \[
   |A'(t)|\leq \tfrac12H(a,b)F(\gamma(t),\gamma'(t)).
   \]

7. `hellinger_le_half_pathLength`.

8. `sqrtDensityEmbedding_lipschitz`:
   ```lean
   LipschitzWith (1 / 2) Ψ
   ```
   on the Fisher wrapper, where `Ψ θ` is the `Lp` class of `qθ`.

The conversion between the integral of a square and the `Lp` norm should be isolated in one helper.

## Why not partitions?

The partition route is mathematically valid with suitable uniform local estimates, but it is not cheaper here.

In particular,
\[
L(\gamma)=\lim\sum_i L(\text{parameter segment between }\gamma(t_i),\gamma(t_{i+1}))
\]
is **not directly just** the standard Riemann-sum theorem for the speed integrand. You must compare secant velocities with derivatives and control the Fisher norm uniformly over the intervening parameter segments.

That is manageable finite-dimensional analysis, but unnecessary infrastructure. The scalar chord argument proves the exact path inequality directly.

Route C adds a constant-speed reparametrisation problem, including zero-speed regions. I would avoid it.

---

# Q4. The completion architecture

Use a wrapper structure.

```lean
structure FisherPoint where
  parameter : W
```

Do **all calculus and normed-space work on `W`**. Define `fisherDist : W → W → ℝ` there without changing any instances.

Then install only the Fisher metric on `FisherPoint`.

Advantages:

* no competing inherited normed-space metric;
* no global instance changing the uniformity of `W`;
* calculus always sees the original normed vector space;
* completion always sees the Fisher uniformity.

Expose a plain equivalence
```lean
FisherPoint ≃ W
```
and, after Q2, a homeomorphism
```lean
FisherPoint ≃ₜ W
```
where the two topologies really are supplied by different types.

I would avoid a reducible synonym such as `def WF := W` for the public API. It invites accidental unfolding and instance confusion. Local `letI` instances are useful while constructing the metric, not as the enduring architecture.

Define
```lean
abbrev FisherCompletion :=
  UniformSpace.Completion FisherPoint
```

Then extend:

* the Lipschitz mean map into `J → ℝ`;
* the \(1/2\)-Lipschitz square-root map into `Lp ℝ 2 ν`.

Use the Lipschitz extension API if available, rather than proving uniform continuity and later reproving the same constants.

**Do not extend `m` with codomain `intrinsicInterior P`:** that target is precisely what fails to be complete. Extend into the ambient finite-dimensional space, then prove the image lies in the closed moment body.

---

# Q5. Completion accessibility

Yes: your proposed theorem is the correct upgrade.

For a facet-interior mean \(M\),
\[
\boxed{
(\exists x\in\widehat W_F,\ \bar m(x)=M)
\iff
\text{the corresponding normal ray has finite Fisher length}.
}
\]

The Cauchy-sequence intermediate formulation is useful, but it does not itself eliminate the realisation step.

## Package the hard direction generically

Prove:

> Every Fisher-Cauchy sequence has a subsequence joined by one globally defined, finite-length C¹ path with continuous velocity and zero velocities at integer junctions. If its means converge to \(M\), the whole path’s means converge to \(M\).

Choose a subsequence with
\[
d_F(\theta_n,\theta_{n+1})\leq 2^{-n}
\]
and paths of length at most, say, \(2^{1-n}\).

Use the flattened paths on `[n,n+1]`. Define the path to be constant for negative times. Then the derivative at zero is also genuinely a two-sided derivative, as required by the existing facet theorem.

At each positive integer, only two pieces occur locally. Therefore:

* the derivative exists by the same finite pasting lemma as Q1;
* its value is zero;
* the velocity is continuous there.

There is **no finite accumulation of junctions**, so no uniform bound on all piecewise derivatives is needed.

For total length, split the nonnegative lintegral into the unit intervals. Use half-open intervals or discard the countable endpoint set as null.

For mean convergence, exactly your estimate works:
\[
\sup_{t\in[n,n+1]}\|m(\gamma(t))-M\|
\leq
\|m(\theta_n)-M\|+B\,L(\gamma_n).
\]

## Converse

Finite ray length gives
\[
d_F(\theta(r),\theta(s))
\leq \int_r^s F(\theta(t),\theta'(t))\,dt.
\]
The tails tend to zero, so integer samples are Cauchy.

Use the ray with the tangential base appropriate to \(M\). A ray based at zero need not converge to that particular \(M\), even if finiteness of its length is equivalent by bounded tilting.

---

# Q6. Uniqueness over facets—and what is actually proved

Your distance argument is exactly right:

\[
\begin{aligned}
d_F(v_n-r_nu,v_M-r_nu)&\leq K\|v_n-v_M\|,\\
d_F(v_M-r_nu,v_M-r_n'u)
&\leq\text{ray-length tail beyond }\min(r_n,r_n').
\end{aligned}
\]

There is no need for a face-variance comparison in the first line. The global bounded-statistic estimate already does everything.

## The crucial prerequisite

You need the following theorem for **arbitrary sequences**, not just `dataTheta`:

> If \(m(\theta_n)\to M\in\operatorname{ri}F\), then in the fixed facet decomposition
> \[
> \theta_n=v_n-r_nu,\qquad v_n\perp u,
> \]
> one has \(v_n\to v_M\) and \(r_n\to+\infty\).

Under the appropriate charged-facet and face-minimality hypotheses, this is the right asymptotic theorem. Its proof must rule out tangential escape using the relative-interior assumption and the charged face. If the existing facet analysis already proves this sequential statement, reuse it. If it only treats the distinguished response path, this is a substantive new module.

With that theorem in hand:

\[
\boxed{\ \bar m^{-1}(M)\text{ contains exactly one point for every accessible }
M\in\operatorname{ri}F.\ }
\]

Moreover, the corresponding Hellinger limit is
\[
q^F_{v_M}(x)
=
\sqrt{
\frac{\mathbf1_F(x)e^{-\langle v_M,S(x)\rangle}}
{\int_F e^{-\langle v_M,S\rangle}\,d\nu}
},
\]
where \(F(x)\) abbreviates the exposed-face event.

This identification follows by dominated convergence along the fixed-base normal ray, once the face has positive mass.

## A useful stronger formulation

For a fixed accessible facet, you should obtain a homeomorphism
\[
\operatorname{ri}F
\;\cong\;
\bar m^{-1}(\operatorname{ri}F).
\]

Continuity of the inverse parametrisation follows from the same-depth estimate
\[
d_F(v-ru,w-ru)\leq K\|v-w\|,
\]
passed to completion limits, together with the face chart. The forward map is simply the continuous extended mean.

But do **not** yet state that the entire completion is the interior plus accessible facet interiors. Higher-codimension fibres remain unclassified.

## What changes in codimension at least two?

The normal direction becomes a cone, not a single half-line. The missing estimate is then:

> Two sufficiently deep normal parameters approaching the same face can be connected by a path of uniformly small Fisher length.

A finite tail along one ray does not establish that estimate for all approaches. Relative rates of different normal coordinates matter.

A charged square is a good test case, but not an automatic counterexample:

* for a finite distribution supported on the four vertices, the usual completion includes the edges and vertices uniquely;
* with additional accumulating layers, the two facet shell criteria alone do not settle simultaneous approach to a vertex.

Thus the genuine next question is **small intrinsic diameter of deep normal regions**, not merely existence of some finite-length normal ray.

## Another deep statement available before uniqueness

The Hellinger extension gives every completion point a probability density relative to the original base measure.

Indeed, limits of the \(q_\theta\) remain nonnegative and have `L²` norm one. Thus
\[
x\longmapsto \bar\Psi(x)^2\,\nu
\]
is a canonical probability-valued map, with
\[
\bar m_j(x)=\int S_j\,\bar\Psi(x)^2\,d\nu.
\]

This immediately shows that any represented boundary mean must lie on a face charged by \(\nu\). It does **not** prove that this probability-valued map is injective. That distinction is worth making explicit in the API.

---

# Q7. Concrete landing order

I would target the following small modules. The line bound should be enforced by splitting proofs, not by assuming the generic gluing theorem will fit automatically.

| Order | Module | Main statement |
|---:|---|---|
| 1 | `FisherSpeed` | Joint continuity, homogeneity, and `F θ w ≤ K * ‖w‖`. |
| 2 | `FlatC1Paths` | Generic zero-velocity endpoint pasting, reversal, and smoothstep flattening. |
| 3 | `FisherPathLength` | Length invariance under flattening; concatenation additivity; flattened segments. |
| 4 | `FisherMeanControl` | Mean displacement is at most `B * length`, including subintervals. |
| 5 | `FisherDistance` | Real path infimum is a metric; segment and mean Lipschitz bounds. |
| 6 | `FisherTopology` | Fisher wrapper is homeomorphic to `W`; construct `FisherCompletion` and extend the mean. |
| 7 | `SqrtDensityAffinity` | `MemLp`, unit norm, exact affinity formula, and scalar affinity derivative. |
| 8 | `HellingerFisherControl` | Scalar endpoint-chord proof of `H ≤ length / 2`; extend `Ψ`. |
| 9 | `FisherCompletionLaws` | Completion points give base-absolutely-continuous probabilities with the prescribed extended means. |
| 10 | `FisherCauchyRealisation` | Summable near-optimal paths concatenate to a finite-length C¹ path on `[0,∞)`. |
| 11 | `FacetCompletionAccess` | Completion fibre nonempty iff ray length finite iff the landed shell criterion. |
| 12 | `FacetMeanAsymptotics` | Arbitrary mean-convergent sequences have `v → vM`, `r → ∞`. |
| 13 | `FacetCompletionUnique` | Accessible facet fibres are singletons, form the face chart, and have face-conditioned Hellinger limits. |

Modules 10–11 do not depend on Hellinger, so they can move ahead of 7–9 if the immediate priority is the completion version of the landed facet theorem.

Finally, on rank 5: if the exact shell classification and its hypotheses are already exposed, there is no missing conceptual classification theorem merely because explicit power laws have not been added. Be careful only that an example \(m_n\asymp n^{-\alpha}\) must be interpreted through **dyadic slack-shell aggregation**. The threshold \(\alpha>2\) applies directly when the indexed quantities are the dyadic shell masses themselves.

**The central new theorem is now clear:** accessible facet interiors are not merely reachable limits of selected response paths; they are canonical, single-point fibres of the intrinsic Fisher completion.