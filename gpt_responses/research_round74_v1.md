## Recommendation

**Next, prove a stratified susceptibility-and-transport theorem: (B), strengthened by pulling it back to perturbations of the data law.** The atlas tells you *where responses live*. This theorem tells you *how every posterior expectation changes when the data move*, and integrates that change from the featureless response to any boundary response.

My ranking is:

1. **(B) Stratified susceptibility, with canonical transport from \(M_0\).**
2. **(A) An exact sequential convergence criterion in face-adapted natural coordinates.**
3. **(C) Fisher accessibility classified by boundary-layer shell masses.**
4. **(E) Relative-entropy/Bregman geometry of the response potential**, if not already available.
5. **(D) Uniform CLT through stratum changes**—important, but neither a consequence of the atlas nor the right next foundational theorem.

There are two important corrections:

- In **(A)**, “normal divergence in the polar cone” needs **divergence of every off-face vertex gap**, not merely divergent norm and a limiting normal direction.
- In **(C)**, neither proposed integral involving the cumulative layer mass is a general *iff* criterion. There is, however, a clean exact classification using **dyadic shell masses**.

Throughout, I assume \(\nu\) is a probability measure and use the positive exponential convention \(e^{\langle\eta,S\rangle}\). Reverse natural-coordinate signs where your API uses \(e^{-\langle\theta,S\rangle}\).

---

# 1. Ranked candidates

## 1. (B): susceptibility, followed by response transport

For each face \(F\), let \(L_F=\operatorname{span}(F-F)\). At \(M\in\operatorname{ri}F\), define the intrinsic covariance operator
\[
C_M:L_F\longrightarrow L_F
\]
and the covariance functional
\[
b_{f,M}(h)=\operatorname{Cov}_{q_M}\bigl(f,\langle h,S\rangle\bigr).
\]
Then the central theorem is
\[
\boxed{
D\bigl[M\mapsto \mathbb E_{q_M}f\bigr]_M[h]
=b_{f,M}(C_M^{-1}h),\qquad h\in L_F.
}
\]
The expectation is continuous on all of \(P\), but its derivative is defined facewise.

This is especially valuable after composing with the data moment map. For an admissible perturbation \(\dot\rho\) of the data law, remaining locally in the same moment stratum,
\[
\boxed{
\frac d{dt}\mathbb E_{q_{\mathbb E_{\rho_t}S}}f
=
b_{f,M}\!\left(C_M^{-1}\int S\,d\dot\rho\right).
}
\]
This is the requested response map over the data manifold, rather than only over natural-parameter space.

**Lean route.** Apply the existing intrinsic mean chart to the normalized `faceMeasure`. Differentiate numerator and normalizer of a bounded-observable expectation using parametric-integral differentiation; the derivative is covariance. Then upgrade the inverse mean chart from a homeomorphism to a differentiable local inverse using covariance positive-definiteness and the inverse-function theorem. Relevant Mathlib infrastructure lies in `Analysis.Calculus.ParametricIntegral`, `Analysis.Calculus.InverseFunctionTheorem`, continuous linear equivalences, and the chain rule. The only substantive new analytic work should be the bounded-observable differentiation lemma and the differentiable inverse-chart bridge.

### What happens near a subface?

There is **no universal blow-up exponent for arbitrary bounded \(f\)**. The observable can be constant, have cancellations, or couple differently to the collapsing directions. The correct initial results are:

1. the exact facewise derivative;
2. its Fisher bound;
3. exact ray derivatives;
4. examples or asymptotics under explicit layer and observable assumptions.

In particular, “Lipschitz in Hellinger” should mean **expectations as functions of probability laws**:
\[
|\mathbb E_p f-\mathbb E_q f|
\le 2\|f\|_\infty\,\|\sqrt p-\sqrt q\|_2.
\]
It does **not** mean that \(M\mapsto q_M\) is Hellinger-Lipschitz in the Euclidean mean parameter.

---

## 2. (A): the right first theorem is a vertex-gap criterion

This is much more immediately accessible than a full theory of face flags.

Fix a face \(F\), \(M\in\operatorname{ri}F\), and \(v_0\in V\cap F\). Remove the globally ineffective natural directions, and split
\[
\eta_n=\tau_n+\zeta_n,\qquad
\tau_n\in L_F,\quad
\zeta_n\in L\cap L_F^\perp,
\]
where \(L=\operatorname{span}(P-P)\).

Then the precise statement should be
\[
\boxed{
\operatorname{meanMap}(\eta_n)\to M
\iff
\begin{cases}
\tau_n\to \eta_F(M),\\[2mm]
\langle\zeta_n,v_0-v\rangle\to+\infty
&\text{for every }v\in V\setminus F.
\end{cases}
}
\]
Here \(\eta_F(M)\) is the intrinsic natural parameter relative to \(\nu\) conditioned on the face fibre.

This statement includes multiscale approaches: the different vertex gaps need not diverge at comparable rates.

**Lean route.** Forward: atlas continuity gives \(L^1\), hence TV convergence of the natural laws to \(q_M\). Their conditional laws on the face fibre are exactly the face exponential family at \(\tau_n\); conditional means converge to \(M\), so the face chart gives \(\tau_n\to\eta_F(M)\). Ratios of probabilities of the charged fibres \(S=v\) and \(S=v_0\) then force every off-face gap to diverge. Reverse: bounded tangential parameters and divergent vertex gaps give pointwise suppression off the face, a uniform domination obtained from the finite vertex inequalities, and dominated convergence. Mathlib pieces: orthogonal projection in finite-dimensional inner-product spaces, `Filter.Tendsto`, finite convex combinations, and dominated convergence.

### Is “normal part diverges in the polar cone” correct?

Only after sharpening it.

The vertex-gap condition says that \(\zeta_n\) eventually lies in the relative interior of the normal cone and escapes **every one of its boundary walls**. Equivalently, in its natural ambient normal space, its distance from the cone boundary tends to infinity.

Merely requiring
\[
\|\zeta_n\|\to\infty,\qquad
\zeta_n/\|\zeta_n\|\to u\in N_P(F)
\]
is insufficient: one vertex gap can stay bounded.

The reverse implication above does not follow merely from the existing single-ray theorem; it needs a short sequence-level dominated-convergence argument. The forward implication crucially uses the **charged vertex fibres and atlas continuity**.

After this, face flags become an organized description of successive scales—not a prerequisite for constructing the topology on \(\bigsqcup_F\Theta_F\). The atlas already supplies that topology by transport from \(P\).

---

## 3. (C): an exact Fisher classification exists, but use shells

Write the ray in gap coordinates:
\[
p_t(dx)=\frac{e^{-t g(x)}}{A+B(t)}\,\mu(dx),
\qquad g\ge0,
\]
where
\[
A=\mu(g=0)>0,\quad
B(t)=\int_{g>0}e^{-tg}\,d\mu,\quad
C_j(t)=\int_{g>0}g^j e^{-tg}\,d\mu.
\]
The finite measure \(\mu\) includes any fixed tangential tilt.

The decisive elementary estimate is
\[
\boxed{
\frac{A\,C_2(t)}{(A+B(t))^2}
\le \operatorname{Var}_{p_t}(g)
\le \frac{C_2(t)}{A+B(t)}.
}
\]
Indeed, \(C_1(t)^2\le B(t)C_2(t)\). Thus
\[
\boxed{
\text{finite Fisher ray length}
\iff
\int^\infty \sqrt{C_2(t)}\,dt<\infty.
}
\]

For bounded \(g\), choose \(R>0\) covering its positive range and set
\[
a_k=\mu\bigl(R2^{-(k+1)}<g\le R2^{-k}\bigr).
\]
Then an exact and geometrically meaningful classification is
\[
\boxed{
\text{finite Fisher ray length}
\iff
\sum_{k=0}^{\infty}\sqrt{a_k}<\infty.
}
\]

**Lean route.** First prove the variance sandwich by Cauchy–Schwarz. For the shell criterion, lower-bound \(C_2(t)\) using shell \(k\) on the disjoint time interval \(t\asymp 2^k/R\). For the upper bound, split \(C_2\) into shells and use \(\sqrt{\sum b_k}\le\sum\sqrt{b_k}\), followed by integration of a decaying exponential on each shell. This uses measure decomposition, nonnegative integrals/Tonelli, `ENNReal` summability, and elementary exponential integrals. It avoids a Tauberian theorem and avoids the false proposed lower bound.

### Why the proposed cumulative-layer criteria are not exact

In general,
\[
\operatorname{Var}_{p_t}(g)\gtrsim B(2t)/t^2
\]
is false: \(B(2t)\) may be dominated by mass at gaps **much smaller than \(1/t\)**, whose contribution to the second moment is tiny.

Likewise,
\[
\int_0\frac{\sqrt{H(r)}}r\,dr<\infty
\]
and
\[
\int^\infty\frac{\sqrt{B(t/2)}}t\,dt<\infty
\]
are useful sufficient conditions, not necessary ones.

For example, if near zero
\[
H(r)\sim c\bigl(\log(1/r)\bigr)^{-\beta},
\]
then shell masses satisfy \(a_k\asymp k^{-\beta-1}\), so:
\[
\text{finite Fisher length}\iff\beta>1,
\]
whereas the proposed cumulative-layer integral requires \(\beta>2\).

Your example has \(\beta=1\), hence infinite length. More explicitly,
\[
C_2(t)\sim \frac{c}{t^2(\log t)^2},
\qquad
\sqrt{\operatorname{Var}_{p_t}(g)}
\asymp \frac1{t\log t}.
\]

One further distinction matters: **an infinite-length particular ray does not prove infinite Fisher distance in higher dimensions**—another path might be shorter. In the one-dimensional intrinsic family, this obstruction does establish that the endpoint is absent from the intrinsic Fisher metric completion.

---

## 4. (E): the response potential and entropy geometry

If not already present, the next complementary structural theorem is
\[
I(M)=D(q_M\|\nu),\qquad
\nabla I(M)=\eta(M),\qquad
D^2I(M)=C_M^{-1}
\]
on the relative interior, with the corresponding facewise statements relative to the face reference law. Together with the information-projection Pythagorean identity, this identifies susceptibility as the derivative of a convex dual coordinate system.

**Lean route.** Use the exponential representation to rewrite relative entropy as \(\langle\eta,M\rangle-\log Z(\eta)\), then differentiate through the intrinsic inverse chart. The Hessian is the same inverse-covariance operator needed in (B), so this becomes inexpensive after rank 1. At boundary points, work facewise and keep the normalization constant from conditioning on the face. This would unify the atlas, Fisher geometry, and maximum-relative-entropy interpretation.

Also keep the scope explicit: the endpoint corresponding to a data law \(\rho\) is \(q_{\mathbb E_\rho S}\), not generally \(\rho\) itself.

---

## 5. (D): uniform CLT needs a degeneration regime

A standardized CLT cannot hold uniformly all the way to arbitrary stratum changes. The simplest obstruction is a rare Bernoulli direction: when its probability is \(\varepsilon\), Gaussian behavior needs an effective sample count \(n\varepsilon\to\infty\); \(n\varepsilon\asymp1\) produces Poisson rather than Gaussian behavior.

A defensible first theorem would be a facewise multivariate Berry–Esseen estimate controlled by
\[
\frac1{\sqrt n}\,
\mathbb E_{q_M}\left\|
C_M^{-1/2}(S-M)
\right\|^3.
\]
Uniformity holds on compact subsets of a fixed relative interior, and along boundary approaches satisfying an explicit uniform standardized-moment condition.

**Lean route.** This requires iid sums, Gaussian approximation, and a quantitative CLT library, not merely the response atlas. Compact-substratum moment control follows from the existing continuity and covariance results, but the probabilistic theorem is a separate large dependency. I would defer it.

---

# 2. Rank-1 package: precise statements and proof carriers

The following are **Lean-shaped interfaces**, not claims about existing declaration names.

## Hypotheses

Use:

- the existing `hS`, `hpoly`, `hcharged`;
- finite-dimensional real inner-product feature space;
- probability reference measure `ν`;
- measurable \(f:X\to\mathbb R\), with \(|f|\le K\) \(\nu\)-a.e.;
- `minimalFacePoly` and `faceMeasure` to select a fixed stratum;
- the intrinsic mean chart for that face measure.

The `vertexSection` is needed indirectly to establish the stratum and covariance nondegeneracy; it should not appear in the final susceptibility formula.

## Statement 1: global continuity

On the subtype \(P\),
```lean
theorem continuous_responseExpectation
    (hf : AEStronglyMeasurable f ν)
    (hbound : ∀ᵐ x ∂ν, ‖f x‖ ≤ K) :
    Continuous (fun M : P => ∫ x, f x ∂responseProjection M)
```

Carry it with the quantitative lemma
\[
|\mathbb E_{q_M}f-\mathbb E_{q_N}f|
\le K\int\left|\operatorname{projDens}(M)
                 -\operatorname{projDens}(N)\right|\,d\nu.
\]
No new compactness argument is needed.

## Statement 2: intrinsic derivative

Fix \(M_\ast\in\operatorname{ri}F\). Work in \(L_F\) on the open set
\[
\Omega_F=\{z\in L_F:M_\ast+z\in\operatorname{ri}F\}.
\]
Let `responseOnFace f z` denote \(\mathbb E_{q_{M_\ast+z}}f\). Then:
```lean
theorem hasFDerivAt_responseOnFace
    (hz : z ∈ faceMeanDomain F)
    (hf : AEStronglyMeasurable f ν)
    (hbound : ∀ᵐ x ∂ν, ‖f x‖ ≤ K) :
    HasFDerivAt
      (responseOnFace F f)
      ((covarianceFunctional F z f).comp
        (covarianceEquiv F z).symm.toContinuousLinearMap)
      z
```

Here:

- `covarianceFunctional F z f : L_F →L[ℝ] ℝ`;
- `covarianceEquiv F z : L_F ≃L[ℝ] L_F`.

This also handles zero-dimensional faces: the derivative is the unique map out of the zero space.

A particularly beautiful companion is
\[
\boxed{
|D R_f(M)[h]|
\le
\sqrt{\operatorname{Var}_{q_M}(f)}
\sqrt{\langle h,C_M^{-1}h\rangle}.
}
\]
That is the coordinate-free susceptibility bound by Fisher speed.

## Statement 3: canonical transport from the featureless law

Let
\[
M_s=(1-s)M_0+sM,\qquad M_0=\mathbb E_\nu S.
\]
Charged vertices imply \(M_0\in\operatorname{ri}P\), hence \(M_s\in\operatorname{ri}P\) for \(s<1\). For every \(r<1\),
\[
\mathbb E_{q_{M_r}}f-\mathbb E_\nu f
=
\int_0^r
b_{f,M_s}\bigl(C_{M_s}^{-1}(M-M_0)\bigr)\,ds.
\]
Global continuity then gives
\[
\boxed{
\mathbb E_{q_M}f-\mathbb E_\nu f
=
\lim_{r\uparrow1}
\int_0^r
b_{f,M_s}\bigl(C_{M_s}^{-1}(M-M_0)\bigr)\,ds.
}
\]

This is an **improper signed-integral identity**. Do not silently assert absolute integrability or finite Fisher length at the endpoint.

It is probably the best capstone statement for the standing directive: an exact accumulated-response formula from the featureless law to every completed response.

## The three proof-carrying lemmas

1. **Differentiation of tilted expectations**
   \[
   D_\eta\mathbb E_{p_\eta}f[h]
   =\operatorname{Cov}_{p_\eta}(f,\langle h,S\rangle).
   \]
   Bounded \(S\), bounded \(f\), and finite reference measure supply local domination.

2. **Differentiability of the intrinsic inverse mean map**
   \[
   D_M\eta_F=C_M^{-1}.
   \]
   Positive covariance plus the inverse-function theorem; the existing homeomorphism identifies the local inverse with the global chart.

3. **Observable continuity from density \(L^1\) convergence.**
   This supplies both global continuity and the boundary passage in transport.

Everything else is chain rule, Cauchy–Schwarz, and the fundamental theorem of calculus.

---

# 3. Ray susceptibility: a clean secondary package

Use the nonnegative gap
\[
g=\beta-\langle u,S\rangle
\]
for a maximally exposed face, and \(p_t\propto e^{-tg}\mu\). Then
\[
\frac d{dt}\mathbb E_{p_t}f=-\operatorname{Cov}_{p_t}(f,g),
\qquad
\frac d{dt}\mathbb E_{p_t}g=-\operatorname{Var}_{p_t}(g).
\]
Your existing variance estimate immediately yields
\[
\boxed{
\left|\frac d{dt}\mathbb E_{p_t}f\right|
\le \frac{4\|f\|_\infty}{t}\sqrt{\frac{B(t/2)}A}.
}
\]

For the maximized statistic \(\langle u,S\rangle=\beta-g\), its derivative is **positive** variance, not negative. The negative-sign formula applies to the gap, or to a ray explicitly written \(e^{-t\langle u,S\rangle}\).

Where the variance is nonzero,
\[
\frac{d\,\mathbb E_{p_t}f}{d\,\mathbb E_{p_t}g}
=
\frac{\operatorname{Cov}_{p_t}(f,g)}
     {\operatorname{Var}_{p_t}(g)}.
\]
This is a derivative **along this one-dimensional curve**, not the whole mean-space susceptibility.

For a sharp non-Lipschitz example, take \(f=1_{\{g>0\}}\) and assume the weighted layer satisfies
\[
H(r)\sim cr^\alpha,\qquad \alpha>0.
\]
Standard Laplace asymptotics give
\[
\mathbb E_{p_t}f\asymp t^{-\alpha},
\qquad
m(t):=\mathbb E_{p_t}g\asymp t^{-\alpha-1},
\]
hence
\[
\mathbb E_{p_t}f\asymp m(t)^{\alpha/(\alpha+1)},
\qquad
\frac{d\,\mathbb E_{p_t}f}{dm}\sim\frac{t}{\alpha+1}.
\]
In a one-dimensional feature model this directly proves failure of mean-Lipschitz continuity. For now, I would land the exact derivative and upper bound; make the asymptotic theorem a separate module.

---

# 4. Uniform density bound: correct, with a free sharpening

Yes: if
\[
\nu(S=v)\ge m>0\qquad\text{for every }v\in V,
\]
then
\[
\boxed{\frac{dq_M}{d\nu}\le \frac1m\quad \nu\text{-a.e.},\qquad M\in P.}
\]

For \(M\in\operatorname{ri}F\), write
\[
\frac{dq_M}{d\nu}
=
1_{\Phi_F}\frac{e^{\ell(S)}}{\int_{\Phi_F}e^{\ell(S)}\,d\nu}.
\]
Choose a vertex \(v_\ast\in V\cap F\) maximizing \(\ell\) on \(F\). Then the numerator is at most \(e^{\ell(v_\ast)}\), while the denominator is at least
\[
\nu(S=v_\ast)e^{\ell(v_\ast)}.
\]
Conditioning normalization cancels, so the bound is indeed against the **original** \(\nu\).

Two sharpenings are available:

- **Facewise**
  \[
  \frac{dq_M}{d\nu}
  \le
  \frac1{\min_{v\in V\cap F}\nu(S=v)}.
  \]
- **Parameter-dependent:** if \(W\subseteq V\cap F\) is the set of vertices maximizing \(\ell\), then
  \[
  \frac{dq_M}{d\nu}
  \le
  \frac1{\sum_{v\in W}\nu(S=v)}.
  \]

Finally, if \(V\) is the actual vertex set, the uniform constant
\[
\frac1{m_\ast},\qquad m_\ast=\min_{v\in V}\nu(S=v),
\]
is **optimal**. At a vertex \(v\),
\[
q_v=\nu(\,\cdot\mid S=v),\qquad
\frac{dq_v}{d\nu}=\frac{1_{\{S=v\}}}{\nu(S=v)}.
\]
If \(V\) contains redundant generators, minimizing over actual extreme vertices can improve the constant.

**Bottom line:** land susceptibility and canonical transport next; then the vertex-gap convergence theorem; then the shell-mass Fisher classification. That sequence turns the atlas into a differential response theory, gives its boundary-coordinate topology, and finally identifies exactly where its topological and metric completions diverge.