## Recommendation

The next organising idea should be **an entropy-completed response atlas, equipped with a transport law**:

- **Transport:** how expectations change when the reference/data law changes.
- **Charts:** ordinary exponential charts in the interior, intrinsic charts on conditioned supports.
- **Completion:** every finite-rate response belongs to one of those charts.
- **Geometry:** covariance supplies the metric and the differential of the response map.

I would not make the `α`-connections the next major milestone. They enrich the differential geometry, but the completion theorem and the distribution-to-response transport law answer the user’s question more directly.

Two qualifications should frame the work:

1. The normalised prior \(\bar\pi\) is the maximiser of **relative entropy** \(-\mathrm{KL}(\,\cdot\,\Vert\bar\pi)\), not generally of Shannon entropy.
2. An arbitrary “actual data distribution” need not belong to the present finite-dimensional family. To reach it exactly, either its log-density ratio must lie in the span of the statistics, or the statistics/path must be enlarged.

---

# 1. Ranked targets

## 1. A master transport theorem, with thermodynamics as its canonical instance

Let \(\nu\) be a probability measure and let \(f,g\) be bounded measurable functions. Put
\[
\nu_s=\nu.\mathrm{tilted}(s f).
\]
The fundamental response identity is
\[
\frac{d}{ds}E_{\nu_s}g=\operatorname{Cov}_{\nu_s}(g,f).
\]

A Lean-flavoured target is:

```lean
hasDerivAt_integral_tilted_scale
    (hν : IsProbabilityMeasure ν)
    (hf : BoundedMeasurable f)
    (hg : BoundedMeasurable g) :
    HasDerivAt
      (fun s => ∫ x, g x ∂(ν.tilted (fun x => s * f x)))
      (covariance (ν.tilted (fun x => s * f x)) g f)
      s
```

Here and below, `BoundedMeasurable` is schematic packaging, not a proposed Mathlib identifier.

The accompanying entropy identity is
\[
\frac{d}{ds}\mathrm{KL}(\nu_s\Vert\nu)
=s\,\operatorname{Var}_{\nu_s}(f).
\]

### Thermal specialisation

Write
\[
H_a=L_0+a\cdot R,\qquad
P_{t,a}=\bar\pi.\mathrm{tilted}(-tH_a).
\]
Extend the thermal path to \(t=0\), where \(P_{0,a}=\bar\pi\). Then
\[
\boxed{
\frac{d}{dt}m_t(a)=-\operatorname{Cov}_{P_{t,a}}(R,H_a)
}
\]
and
\[
\boxed{
\frac{d}{dt}\mathrm{KL}(P_{t,a}\Vert\bar\pi)
=t\,\operatorname{Var}_{P_{t,a}}(H_a)
=-t\,\frac{d}{dt}E_{P_{t,a}}H_a.
}
\]

Integrating:
\[
\mathrm{KL}(P_{t,a}\Vert\bar\pi)
=\int_0^t s\,\operatorname{Var}_{P_{s,a}}(H_a)\,ds.
\]

This gives a precise interpretation of the journey: **expectations move by covariance, while information accumulated relative to the prior is the temperature-weighted fluctuation energy.**

### Reaching actual data

If a target law \(D\) satisfies
\[
D=\bar\pi.\mathrm{tilted}(f)
\]
with bounded measurable \(f\), then \(\nu_s=\bar\pi.\mathrm{tilted}(sf)\), \(0\le s\le1\), reaches \(D\) exactly and obeys the same response identity.

This is the clean bridge from the affine model to actual changes in the data distribution. Finite KL alone does **not** supply the domination needed for the same differentiability proof with an unbounded log-density ratio.

### Fixed-response temperature derivative

For fixed \(M\in\operatorname{interior}K\), let \(\theta_t(M)\) satisfy \(m_t(\theta_t(M))=M\). With your unnormalised \(A_t\),
\[
\operatorname{rateFun}_t(M)=I_t(M)+A_t(0).
\]
Consequently,
\[
\boxed{
\partial_t\operatorname{rateFun}_t(M)
=E_{P_{t,\theta_t(M)}}L_0-E_{Q_t}L_0.
}
\]
The same formula holds for the real-valued entropy-projection value there.

This is an important normalisation correction: the already-proved
\(\partial_t I_t(M)=\mathrm{obsMean}\) is not, by itself, the derivative of the rate function.

**Proof route.** Differentiate numerator and normaliser under the integral; apply the quotient rule; use `klDiv_tilted_eq`; integrate the derivative using the fundamental theorem of calculus.

**Expected API.** `Measure.tilted`, dominated differentiation of integrals, `HasDerivAt`, interval-integral FTC, covariance and variance identities.

**Pitfalls.**

- Differentiate `klDiv ... .toReal` only after proving finite KL.
- The path \(t\mapsto P_{t,a}\) keeps \(a\) fixed; fixed-response paths have a moving \(a=\theta_t(M)\).
- Neither the fixed-response rate nor its entropy-projection value is generally monotone in \(t\).

---

## 2. Intrinsic conditional response charts

This is the technical prerequisite for the completion theorem.

For a bounded feature law under a probability \(\nu\), define
\[
K_\nu=\overline{\operatorname{conv}}(\operatorname{supp}(R_\#\nu)),
\qquad
V_\nu=\operatorname{direction}(\operatorname{affineSpan}K_\nu).
\]

The correct general theorem is the relative-interior version of your moment-body theorem:
\[
\left\{E_{\nu.\mathrm{tilted}(q\cdot R)}R:q\in\mathbb R^\iota\right\}
=\operatorname{relint}K_\nu.
\]

After restricting parameters to \(V_\nu\), this becomes an identifiable intrinsic response chart.

```lean
range_intrinsicMeanMap :
    Set.range intrinsicMeanMap =
      intrinsicInterior ℝ (genMomentBody ν R)
```

For a positive supporting event \(F\), apply this theorem to \(\nu_F\). For \(M\in\operatorname{relint}K_{\nu_F}\),
\[
\operatorname{genRate}_\nu(M)
=-\log\nu(F)+\operatorname{genRate}_{\nu_F}(M),
\]
and the minimiser is an intrinsic tilt of \(\nu_F\).

### An important geometric distinction

Do **not** define the conditioned moment body as the geometric intersection
\[
K_\nu\cap\{u\cdot y=\beta\}.
\]
In general,
\[
K_{\nu_F}\subseteq K_\nu\cap\{u\cdot y=\beta\}
\]
can be strict.

For example, the original law may approach an entire boundary segment while assigning positive mass on that segment only at one point. Conditioning retains the actual boundary mass, not all boundary support-limit points.

Thus these should be called **conditional-support charts**, rather than automatically charts of the entire geometric face.

**Proof route.** Choose an origin in the affine hull; use an orthonormal basis of \(V_\nu\) to obtain minimal features; apply the existing full-dimensional theorem; transport back.

**Expected API.** `AffineSubspace.direction`, affine span, `Module.finrank`, orthonormal bases or orthogonal projection, finite-dimensional coordinate equivalences, intrinsic/relative interior.

**Pitfalls.**

- Ambient `hnd` fails on every proper supporting face.
- Zero-dimensional support must be handled explicitly: the intrinsic family is a singleton.
- The family is unchanged by adding a parameter annihilating \(V_\nu\); parameter uniqueness is intrinsic, not ambient.

---

## 3. Finite-rate completion by positive exposed conditioning

The central completion theorem should be:

> For a probability \(\nu\) with bounded measurable features, every \(M\) of finite `genRate` has a unique entropy minimiser. That minimiser is a bounded exponential tilt of a law obtained by finitely many positive-mass exposed conditionings.

Schematically:

```lean
exists_unique_entropyProjection_of_genRate_ne_top
    (hfin : genRate ν R M ≠ ⊤) :
    ∃! ρ, IsProbabilityMeasure ρ ∧
      featureMean ρ R = M ∧
      klDiv ρ ν = genRate ν R M
```

Strengthen the existence witness with a conditioning certificate:

```lean
∃ A q,
  0 < ν A ∧
  ExposedConditioningChain ν R A ∧
  ρ = (conditionalLaw ν A).tilted (fun x => dot q (R x))
```

with chain length at most \(\dim V_\nu\).

Then:
\[
\boxed{\operatorname{entropyProj}_\nu(M)=\operatorname{genRate}_\nu(M)}
\]
for **all** \(M\), not merely all of \(K_\nu\). At infinite-rate points, this follows immediately from the already-proved lower bound.

A useful stronger endpoint is completed Pythagoras:
\[
\mathrm{KL}(\rho\Vert\nu)
=\mathrm{KL}(\rho\Vert\rho_M)+\mathrm{KL}(\rho_M\Vert\nu)
\]
for every feasible probability \(\rho\), whenever \(\operatorname{genRate}_\nu(M)<\infty\).

**Proof route.**

- If \(M\in\operatorname{relint}K_\nu\), use target 2.
- Otherwise choose a proper intrinsic supporting hyperplane through \(M\).
- Its event has positive mass, since a null supporting event would force infinite rate.
- Apply the face decomposition. The residual rate is finite.
- The new conditional moment body has strictly smaller affine dimension.
- Recurse.
- Telescope the entry costs and lift the final minimiser.

**Expected API.** Strong induction on `Nat`, `Module.finrank`, strict dimension drop for proper affine subspaces, conditional/restricted measures, your face-rate lemmas and KL identities.

**Pitfalls.**

- Later faces need only be exposed in the **current conditional body**. They need not be exposed in the original body.
- Prove relative versions of the supporting and face-rate results; the ambient nondegeneracy hypotheses cannot survive recursion.
- Uniqueness is asserted only at finite rate. An equality with value `⊤` is not a useful uniqueness criterion.

This is the highest-value substantial theorem still missing.

---

## 4. The joint-body thermal compactification

Let \(T=(L_0,R)\), and let \(K^{\mathrm{joint}}\) be its moment body under \(\bar\pi\). The joint family
\[
\nu_b=\bar\pi.\mathrm{tilted}(-b\cdot T)
\]
has an intrinsic chart onto \(\operatorname{relint}K^{\mathrm{joint}}\).

The thermal model corresponds to
\[
b=(t,ta).
\]

### Finite-temperature geometry

For every \(t>0\), the response image is still
\[
\operatorname{range}m_t=\operatorname{interior}K.
\]
Therefore there is no nontrivial “derivative of the response moment body”: **the body does not move**.

What moves is its lift into the joint body:
\[
M\longmapsto
\left(E_{P_{t,\theta_t(M)}}L_0,\ M\right).
\]
This is the precise meaning of a temperature-dependent joint-body slice. It is generally a curved graph, not an affine hyperplane section.

Your `lossChart_temp_deriv_neg` is exactly a vertical monotonicity theorem for these graphs.

### Zero-temperature endpoint

For fixed \(a\), set
\[
\alpha=\operatorname{ess\,inf}_{\bar\pi}H_a,\qquad
G=\{H_a=\alpha\}.
\]
Prove:
\[
E_{P_{t,a}}H_a\longrightarrow\alpha,
\qquad
P_{t,a}(H_a\ge\alpha+\varepsilon)\longrightarrow0
\quad(\varepsilon>0).
\]

If \(\bar\pi(G)>0\), strengthen this to
\[
P_{t,a}\xrightarrow{\mathrm{TV}}\bar\pi_G,
\qquad
\mathrm{KL}(P_{t,a}\Vert\bar\pi)
\longrightarrow-\log\bar\pi(G).
\]

If \(\bar\pi(G)=0\), then
\[
\mathrm{KL}(P_{t,a}\Vert\bar\pi)\longrightarrow+\infty.
\]

This is the ground-state entry-cost theorem. “Degeneracy” here means **prior mass of the ground-state event**, not a count of minimisers.

**Proof route.** Reuse `FaceTotalVariation` on the one-dimensional statistic \(H_a\). For the positive-mass KL limit, write
\[
\mathrm{KL}(P_t\Vert\bar\pi)
=-tE_{P_t}(H_a-\alpha)
-\log E_{\bar\pi}e^{-t(H_a-\alpha)}.
\]
The first term tends to zero by dominated convergence using
\(z e^{-z}\le 1/e\); the second tends to \(-\log\bar\pi(G)\).
For a null ground event, use the scalar rate at the limiting exposed endpoint.

**Expected API.** Essential infimum, dominated convergence, exponential bounds, compactness of the joint moment body, existing face-TV and null-face rate results.

**Pitfalls.**

- A null ground event need not yield a unique limiting response or limiting probability law.
- Only concentration near the exposed ground face is automatic.
- A full-dimensional joint chart requires joint nondegeneracy, which feature nondegeneracy does not imply.

---

## 5. Stratified quantitative stability

Package stability as an atlas theorem: each intrinsic chart has uniform quantitative control on compact chart regions, but no uniform nondegenerate estimate is promised across strata.

For a fixed temperature and a convex parameter region on which
\[
\lambda I\le V(a)\le\Lambda I,
\]
prove, intrinsically,
\[
t\lambda\|a-b\|
\le\|m_t(a)-m_t(b)\|
\le t\Lambda\|a-b\|,
\]
and
\[
\frac{t^2\lambda}{2}\|a-b\|^2
\le\mathrm{KL}(P_{t,a}\Vert P_{t,b})
\le\frac{t^2\Lambda}{2}\|a-b\|^2.
\]

Add the direct response-to-law estimate from Pinsker:
\[
\|E_\rho R-E_\sigma R\|
\le 2B\,\mathrm{TV}_{\sup}(\rho,\sigma)
\le B\sqrt{2\,\mathrm{KL}(\rho\Vert\sigma)}
\]
when \(\|R\|\le B\) under the relevant laws.

**Proof route.** Integrate the covariance Jacobian and the Hessian/Bregman formula already available; use continuity and compactness for uniform eigenvalue bounds. Apply the same package to intrinsic conditional features.

**Expected API.** Positive-definite operators, compact extrema, operator norms, interval-integral estimates, Pinsker/total variation.

**Pitfalls.**

- The parameter segment must stay in the region of covariance control.
- Ambient covariance degenerates on a face; intrinsic covariance need not.
- State the TV convention explicitly.
- Pinsker constants here use natural logarithms.

This turns the atlas into a robust tool for “mapping” nearby data distributions and nearby responses.

---

## 6. Cubic tensor and dual affine connections

At fixed \(t\), let \(V\) be covariance and
\[
T_{ijk}=E[(R_i-m_i)(R_j-m_j)(R_k-m_k)].
\]
Then
\[
\partial_kV_{ij}=-tT_{ijk}.
\]

In the \(a\)-chart:
\[
\Gamma^{(e)}=0,\qquad
\Gamma^{(m)k}_{ij}
=-t(V^{-1})^{k\ell}T_{\ell ij}.
\]
Hence a mixture geodesic satisfies
\[
a''=tV^{-1}T(a',a').
\]

With the convention that \(\alpha=1\) is exponential:
\[
\Gamma^{(\alpha)}
=\frac{1-\alpha}{2}\Gamma^{(m)}.
\]

**Proof route.** Differentiate covariance; differentiate the inverse mean chart twice; identify straight mean-coordinate paths. Levi–Civita is the half-sum of the dual connections.

**Expected API.** Third Fréchet derivatives, continuous multilinear maps, differentiation of inverse maps, finite-dimensional tensor contractions.

**Pitfalls.**

- Use the intrinsic chart when covariance is singular ambiently.
- Sign conventions depend on the statistic \(-tR\).
- Only the exponential and mixture connections are automatically flat; do not infer flatness of the whole `α`-family.

I would initially formalise the geodesic equations directly, without waiting for a general manifold-connection framework.

---

# 2. The cleanest induction and the right conditioned family

## Induct on affine dimension—not feature count

Use strong induction on
\[
d(\nu,R)=\dim\operatorname{direction}(\operatorname{affineSpan}K_\nu).
\]

The induction hypothesis should quantify over **every probability law on the same sample space with the same bounded feature map**, having smaller affine support dimension.

This avoids changing the feature index at every recursive step. Orthogonal-coordinate reduction belongs inside the intrinsic-chart theorem, not inside the completion induction.

A good intermediate theorem is:

```lean
finite_rate_has_conditioned_tilt
    (hfin : genRate ν R M ≠ ⊤) :
    ∃ c : ConditioningCertificate ν R M,
      c.length ≤ affineSupportDim ν R ∧
      klDiv c.minimizer ν = genRate ν R M
```

A certificate can record nested measurable events
\[
X=A_0\supset A_1\supset\cdots\supset A_k,
\]
with:

- \(\nu(A_j)>0\);
- \(A_{j+1}\) is a supporting equality event under \(\nu(\cdot\mid A_j)\);
- the supporting inequality holds almost surely under that current law;
- \(M\) lies on the supporting hyperplane;
- \(M\in\operatorname{relint}K_{\nu(\cdot\mid A_k)}\);
- the endpoint is an intrinsic tilt with mean \(M\).

The telescoping identity is
\[
\sum_{j<k}-\log\nu(A_{j+1}\mid A_j)
=-\log\nu(A_k).
\]
Work in real numbers while all masses are positive, then apply `ofReal`.

### Why the recursion works

At each step, finite residual rate implies that \(M\) belongs to the **new conditional moment body**, not merely the old supporting hyperplane. This is where the generic off-body theorem is needed.

Dimension drops because the new body lies in a proper supporting hyperplane of the old affine hull. It may drop by more than one; strong induction handles that naturally.

## Restricting `μ` is correct—but not sufficient for intrinsic geometry

For measurable \(F\) of positive family mass,
\[
\boxed{
\operatorname{familyMeasure}(\mu.\mathrm{restrict}\,F)\,\pi\,L_0\,R\,t\,a
=
P_{t,a}(\,\cdot\mid F).
}
\]

The proof is simply restriction of `withDensity` and the normaliser identity
\[
Z_F(t,a)=Z(t,a)\,P_{t,a}(F).
\]

Moreover, since all finite tilts have strictly positive densities, positivity of \(Q(F)\) gives positivity of \(P_{t,a}(F)\) for every finite \(a\).

Thus:

- **Yes:** restricted `μ` is an excellent implementation for the conditioned affine family.
- **No:** the entire nondegenerate chart API does not apply verbatim. Ambient `hnd` fails on a proper face.

I would maintain two interfaces:

1. `familyMeasure (μ.restrict F) ...` for integration, differentiation and partition identities;
2. `conditionalLaw ν F` plus intrinsic coordinates for geometry and recursive completion.

Prove the bridge once.

---

# 3. The single identity at the centre of the temperature journey

My choice is
\[
\boxed{
\frac{d}{dt}\mathrm{KL}(P_{t,a}\Vert\bar\pi)
=-t\frac{d}{dt}E_{P_{t,a}}H_a
=t\,\operatorname{Var}_{P_{t,a}}(H_a).
}
\]

Its hypotheses are modest:

- \(\bar\pi\) is a probability;
- \(H_a\) is bounded measurable;
- \(a\) is fixed;
- \(t\ge0\), with the path extended to \(t=0\).

It simultaneously expresses:

- dissipation of expected loss;
- monotone departure from the featureless prior;
- the fluctuation mechanism driving that departure;
- the Fisher-speed contribution along the thermal path.

But place its vector companion immediately beside it:
\[
\frac{d}{dt}E_{P_{t,a}}R
=-\operatorname{Cov}_{P_{t,a}}(R,H_a).
\]
The scalar identity measures the journey; the vector identity maps its response trajectory.

For relative entropy,
\[
S_{\bar\pi}(P_{t,a})
:=-\mathrm{KL}(P_{t,a}\Vert\bar\pi)
=A_t(a)-\log\!\int\pi\,d\mu+tE_{P_{t,a}}H_a.
\]
Therefore
\[
S_{\bar\pi}'(t)=-t\,\operatorname{Var}(H_a)\le0.
\]

**Do not claim concavity in temperature.** In general,
\[
S_{\bar\pi}''(t)
=-\operatorname{Var}(H_a)
+t\,E[(H_a-EH_a)^3],
\]
which has no fixed sign.

Finally, the fixed-\(a\) path collapses to the prior at \(t=0\), although every positive-temperature chart covers the whole interior response body. Maintaining other responses as \(t\downarrow0\) generally requires parameters growing like \(1/t\). That distinction deserves an explicit explanatory theorem or remark.

---

# 4. Corrections and hypothesis checks

### ENNReal Pythagoras

Your interior identity
\[
\mathrm{KL}(\rho\Vert Q)
=\mathrm{KL}(\rho\Vert P_{t,a})
+\mathrm{KL}(P_{t,a}\Vert Q)
\]
is sound, including infinite values, provided:

- `ρ` is a probability;
- its feature means match those of \(P_{t,a}\);
- the relevant expectations are well-defined;
- the tilt statistic is bounded in the required sense.

The bounded tilt makes \(P_{t,a}\) and \(Q\) equivalent, with bounded log-density ratio. Thus the infinite case is compatible with adding a finite constant. No suspicious `∞ − ∞` operation is needed.

The uniqueness equivalence also needs the probability and mean constraints to remain explicit in its interface.

### Face-law entry cost

\[
\mathrm{KL}(Q_F\Vert Q)=-\log Q(F)
\]
is exactly correct for measurable \(F\) with \(0<Q(F)\le1\).

In Lean, distinguish the ENNReal mass from its real coercion:
```lean
klDiv (conditionalLaw Q F) Q =
  ENNReal.ofReal (-Real.log (Q F).toReal)
```

Probability of \(Q\) and positivity of \(Q(F)\) are essential. The statement should not accidentally extend through a totalised definition of conditioning on null events.

### Boundary-barrier null sets

Using \(\mu(F)=0\) rather than \(Q(F)=0\) is justified by the stipulated strict positivity of \(\pi\) and of the exponential factor. If the library later weakens the prior assumption to \(\pi\ge0\), formulate the criterion using \(Q(F)=0\) or \((\pi\mu)(F)=0\).

### The featureless member

For \(t>0\),
\[
Q_t=P_{t,0}\propto e^{-tL_0}\pi
\]
is featureless relative to \(R\), but is not generally the prior. Keep these two baselines distinct in theorem names and prose.

---

**Suggested next development sequence:** prove the general tilted transport identities; build the intrinsic relative-interior chart; complete finite-rate entropy projection by affine-dimension induction. Those three pieces would establish the main conceptual object: a response atlas from the prior through interior posteriors to every finite-information boundary response, with an exact differential law governing the journey.