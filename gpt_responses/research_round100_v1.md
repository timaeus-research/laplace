## Recommendation

Programme J has supplied the interior geometry. The next programme should **reach the boundary and distinguish the geometry of responses from the statistics of estimating them**.

My first three priorities are:

1. **Reach arbitrary finite data laws in response, including boundary means.**
2. **Finish the i.i.d. curvature-bias theorem.**
3. **Make the quotient by feature means explicit.**

The most important conceptual distinction is now:

> The journey reaches the data’s **maximum-relative-entropy response**, not generally the data law itself. The discrepancy is precisely the information discarded by the feature map.

That distinction should become a theorem, not remain explanatory prose.

# Q1. Audit

## (a) The sphere theorem is correct—with two documentation traps

For a saturated finite family with charged reference law,
\[
\theta\longmapsto p=B(\theta)
\]
identifies the model with the entire positive simplex. Under
\[
p\longmapsto 2\sqrt p,
\]
the Fisher metric becomes the metric induced from the sphere of radius \(2\):
\[
\|d(2\sqrt p)\|^2=\sum_x\frac{dp_x^2}{p_x}.
\]
Therefore
\[
d_F(\theta_0,\theta_1)
=2\arccos\sum_x\sqrt{p_xq_x}
\]
is exactly right. **Uniformity of \(\nu\) is irrelevant.** Changing a charged reference law changes the natural-coordinate parametrisation, not the Fisher geometry of the full simplex.

The global-\(C^1\)-path convention does not change the answer. The positive great-circle arc stays strictly positive on its compact parameter interval; it therefore extends slightly beyond both endpoints and can then be extended to a global \(C^1\) path in \(W\). Its length on the designated interval remains the spherical distance.

Two corrections:

* **“Diameter below \(\pi\)” is false if it means the supremal diameter.** For \(|X|\ge2\), every pair has distance strictly below \(\pi\), but the diameter is **exactly \(\pi\)**. Approach two distinct vertices.
* **“Bounded, hence not complete” is not a valid implication.** Incompleteness follows from a Fisher-Cauchy sequence approaching a missing boundary point. Moreover, the one-atom model is a complete singleton.

There is also one definition-level audit I would perform immediately:

> Why does `fisherVar_sphereLift` quantify over **every real \(s\)**?

The ordinary sine-interpolated great circle, extrapolated outside its positive arc, encounters zero coordinates. A log-lift is not then an inverse simplex chart. If `spherePath` has a positivity-preserving global extension, fine. If it is the raw extrapolated great circle, the unrestricted statement needs scrutiny. The displayed statements alone do not settle this; check the definitions and the positivity lemma used in its proof.

## (b) Localised bias: correct and well chosen, but oracle-localised

Write \(L=A^{-1}\), \(Q(z)=C(Lz,Lz)\). On the certified ball,
\[
\theta_r(m_0+z)-\theta_0=Lz-\tfrac12Q(z)+R(z),
\qquad \|R(z)\|\le K\|z\|^3.
\]
For the reset estimator, subtract the full quadratic expectation and use centring. The three errors are precisely:

\[
\begin{aligned}
\text{lost linear tail}&\le \|L\|M_3/\delta^2,\\
\text{local Taylor remainder}&\le KM_3,\\
\text{lost quadratic tail}&\le \tfrac12\|Q\|M_3/\delta.
\end{aligned}
\]
Since
\[
\|Q(z)\|\le \|A^{-1}\|\,\|T\|\,\|A^{-1}\|^2\|z\|^2,
\]
your constant is sane and has exactly the expected structure.

Important qualifications:

* This is **reset localisation**, not conditioning on the good event. There is no division by the good-event probability.
* It is an **oracle localisation**: the reset point and the ball are centred at the unknown true response. It is an excellent local asymptotic theorem, but not yet a directly implementable estimator.
* It establishes no bias bound for the unlocalised estimator. Rare excursions towards the boundary can make natural coordinates enormous or undefined.
* “Curvature bias” means the second-order effect of the nonlinear inverse mean chart, encoded by the m-connection. It is **coordinate-dependent estimator bias**, not a scalar Riemannian-curvature invariant.
* For a merely finite measure, the theorem is an integral statement. Calling it an expectation presupposes a probability measure.

The genuinely missing statistical result is exactly the i.i.d. instance you identified.

## (c) Featureless journey: correct, with a precise meaning of “featureless”

Assuming \(\nu\) is a probability law, \(\theta=0\) gives \(\nu\). It maximises **relative entropy with respect to \(\nu\)**, equivalently minimises \(\mathrm{KL}(\,\cdot\,\Vert\nu)\) without moment constraints.

It does **not** generally maximise Shannon entropy. That description requires uniform \(\nu\) in the finite case.

If the underlying reference measure were not normalised, the starting law would be \(\nu/\nu(X)\); the displayed mixture formula with \(\nu\{x\}\) consequently relies on the probability hypothesis.

The endpoint \(t=1\) is harmless here because the target is \(B(\theta_1)\), hence strictly positive. But this does **not** establish arrival at arbitrary data:

* In a saturated family, a data law with zeros lies on the missing simplex boundary.
* In a non-saturated family, the endpoint law is the entropy projection of the data’s moments, not generally the data law.
* A data law with zeros can nevertheless have an **interior mean**, so singularity of the data law alone does not imply divergence of the response coordinate.

## (d) Good-event theorem: sound, but its statistical scope must be explicit

The exported event is a major improvement. It prevents a sign conclusion obtained from an inverse chart evaluated outside its legitimate domain.

A careful statistician would want five qualifications.

1. **Pointwise, not journey-uniform.** This controls one fixed sample size, truth law and certificate. It does not give simultaneous validity along an entire journey or under adaptive stopping.

2. **One-sided orientation is encoded in the certificate.** The conclusion is specifically
   \(\ell(\hat\theta)>\ell(\theta_0)\). The certificate selects the orientation; the theorem does not automatically handle both signs.

3. **The lower bound may be vacuous.** The coefficient
   \[
   \tau_{\theta_0}(D)
   =-\sum_{a,b}\operatorname{samplingOp}_{ab}\operatorname{Cov}_D(S_a,S_b)
   \]
   should have a prominently exported nonnegativity theorem. A useful probability guarantee requires \(nr^2\) sufficiently large.

4. **Pairwise independence supports this second-moment theorem, not the next bias theorem.** It should not silently migrate into fourth-moment or product-experiment claims.

5. **The converse and achievability results are not yet a universal matched statistical theorem.** The testing lower bound concerns product samples from \(P_{\theta_0}\) and \(P_{\theta_1}\). The good-event theorem permits an actual law \(D\) with potentially different feature covariance. Under misspecification, sampling resolution is governed by the sandwich covariance, not Fisher distance alone.

In particular, **same response does not mean same sampling behaviour**: two laws in the same moment fibre can have different feature covariance matrices.

# Q2. Ranked next modules

Here is my ranking by contribution to the standing direction—not by ease.

## 1. `ResponseBoundaryJourney`

**Target.** For finite charged \(X\), every data law \(D\), including one whose mean lies on the boundary of the moment polytope, has a canonical entropy-response endpoint. Along
\[
m_t=(1-t)m_\nu+t\,m_D,\qquad 0\le t<1,
\]
the existing chart defines \(P_t\), and
\[
P_t\longrightarrow R(D),
\]
where \(R(D)\) uniquely minimises \(\mathrm{KL}(P\Vert\nu)\) subject to \(E_PS=E_DS\).

**Proof route.** Work in the compact closed simplex. Relative entropy is continuous there because \(\nu\) charges every atom and \(x\log x\) extends continuously at zero; strict convexity gives uniqueness. Every \(m_t\), \(t<1\), is interior. If \(R=R(D)\), the competitor \((1-t)\nu+tR\) has mean \(m_t\). Minimality bounds the entropy of \(P_t\) by that competitor’s entropy. Every subsequential limit is feasible at \(m_D\) and has entropy no greater than \(R\), hence equals \(R\). This reuses the existing interior projection and avoids proving a global boundary chart first.

**Size:** one focused tide if finite-simplex compactness infrastructure is ready. Full continuity for arbitrary varying means is a further step.

## 2. `ResponseIIDSamplingBias`

**Target.**
\[
\left\|
E[\hat\theta_{\rm loc}-\theta_0]
+\frac1{2n}E_D[C(A^{-1}\xi,A^{-1}\xi)]
\right\|
\le \frac{C_{\theta_0,D}}{n^{3/2}},
\]
where \(\xi\) is the centred intrinsic feature displacement.

**Proof route.** First prove the generic continuous-bilinear identity
\[
E[Q(\bar\xi_n,\bar\xi_n)]
=\frac1nE[Q(\xi,\xi)].
\]
This part needs only centred pairwise independence and common second moments. Separately, under `iIndepFun`, expand scalar fourth moments:
\[
E\Big(\sum_{i=1}^nY_i\Big)^4
=nEY^4+3n(n-1)(EY^2)^2.
\]
Transfer to the finite-dimensional intrinsic norm using coordinates and norm equivalence; do not seek dimension-free constants initially. Combine \(M_2=O(n^{-1})\), \(M_4=O(n^{-2})\) by Cauchy–Schwarz and instantiate J4.

**Size:** the contraction is one tide; the independent fourth-moment infrastructure may deserve its own tide.

## 3. `ResponseFiniteFibres`

**Target.** Make the response atlas a literal quotient:
\[
\Delta(X)/{\sim}\ \cong\ \operatorname{conv}S(X),
\qquad
p\sim q\iff E_pS=E_qS.
\]
The response is a canonical entropy-minimising section.

**Proof route.** The barycentre map is a continuous affine surjection from a compact simplex to a Hausdorff polytope, hence a quotient map. Each fibre is an affine slice of the simplex. For an interior mean its affine dimension is
\[
|X|-1-\dim W,
\]
because the fibre contains the strictly positive model law. **Do not state that dimension uniformly on the boundary.** If \(F\) is the minimal face containing the mean and \(X_F=\{x:S(x)\in F\}\), the appropriate formula is
\[
|X_F|-1-\dim F.
\]
This gives a precise description of what the response forgets.

**Size:** quotient plus interior fibres is one tide; boundary-face dimensions and continuity of the entropy section are additional work.

## 4. `ResponseJourneyInformationCost`

**Target.** Extend the journey information identity to boundary endpoints:
\[
\mathrm{KL}(R(D)\Vert\nu)
=\int_0^1(1-t)\,G_{\theta_t}(\dot\theta_t,\dot\theta_t)\,dt.
\]

**Proof route.** First specialise existing interior identities. For
\(f(t)=\mathrm{KL}(P_t\Vert\nu)\),
\[
f(0)=f'(0)=0,\qquad f''(t)=G_{\theta_t}(\dot\theta_t,\dot\theta_t).
\]
At an interior cutoff \(T\),
\[
f(T)=\int_0^T(T-s)G_{\theta_s}(\dot\theta_s,\dot\theta_s)\,ds.
\]
Use the boundary convergence from module 1 and monotone convergence of the nonnegative kernels \((T-s)_+\). In saturation this becomes the explicit formula
\[
f''(t)=\sum_x\frac{(p_x-\nu_x)^2}{(1-t)\nu_x+tp_x}.
\]
For the full defect identity, add the boundary information-projection Pythagorean theorem, using the exponential family restricted to the endpoint’s supporting face.

**Size:** one tide after module 1 and the existing interior information-cost theorem.

**Warning:** finite weighted energy does not by itself prove finite Fisher length.

## 5. `ResponseObservableSamplingGeometry`

**Target.** Transfer sampling resolution from structural coordinates to the posterior quantities the user actually cares about.

For
\[
H_F(m)=E_{R(m)}F,
\]
define
\[
L_F(z)=DH_F(m_0)[z]
=-\operatorname{Cov}_{P_{\theta_0}}
 \bigl(F,\langle A^{-1}z,S\rangle\bigr).
\]
The sampling influence is \(L_F(\xi)\), and its variance is
\[
\sigma_F^2(D)=E_D[L_F(\xi)^2].
\]

**Proof route.** Reuse the observable derivative and certified inverse-chart remainder. Prove the exact \(1/n\) variance identity for the linearised observable, then a localised nonlinear remainder bound. For finitely many observables, export the whole covariance matrix. This makes explicit how posterior expectation changes separate into truth displacement, sampling noise and nonlinear bias. If this is already in the seabed, do not create a duplicate module; instead strengthen its interface to accept the new i.i.d. moment bounds.

**Size:** one tide without a CLT. A distributional limit or sharp local testing theory is a larger programme.

## 6. `ResponseSimplexCompletion`

**Target.** The Fisher completion of the saturated finite response space is the closed simplex with
\[
\bar d(p,q)=2\arccos\sum_x\sqrt{p_xq_x}.
\]

**Proof route.** Give the closed simplex the spherical metric, prove compactness and density of its positive part using \((1-\varepsilon)p+\varepsilon\nu\), then use the completion universal property. Reuse J3 as the isometric identification. This corrects the diameter/completeness documentation and gives missing boundary laws a canonical geometric home.

**Size:** one mathematical tide; possibly two Lean tides depending on the metric-completion interface.

This theorem is beautiful, but less urgent than the non-saturated boundary journey: saturation already makes response equal to law.

## 7. `ResponseExtrinsicGauss`

**Target.** Replace the vague “non-saturated sphere analogue” by the precise submanifold statement and its Gauss equation.

**Proof route.** Embed the finite model by \(2\sqrt{P_\theta}\). Let \(\Pi_\theta\) be the \(L^2(P_\theta)\) projection onto constants and centred features, and set
\[
r_{uv}=(I-\Pi_\theta)(h_uh_v),
\qquad h_u=-\langle u,S-E_\theta S\rangle.
\]
The second fundamental form inside the radius-\(2\) sphere is represented by \(\frac12\sqrt{P_\theta}\,r_{uv}\). Consequently,
\[
K(u,v)=\frac14+
\frac{E[r_{uu}r_{vv}]-E[r_{uv}^2]}
 {4\bigl(G(u,u)G(v,v)-G(u,v)^2\bigr)}.
\]
The fourth-order terms cancel appropriately against the projections, linking this to the existing cumulant geometry.

**Size:** probably two tides unless projection and sectional-curvature infrastructure is already substantial.

### What I would not prioritise

* **A generic non-saturated sphere equality.** It is false. The ambient spherical distance is a lower bound; the spherical shortest arc generally leaves the model. Also, the model is an embedded submanifold of the simplex, not automatically a metric quotient of it.
* **Universal numerical curvature bounds.** Do not expect a blanket \(0\le K\le1/4\). The Gauss correction has no such sign guarantee. Quantitative bounds should involve conditioning or cumulant/residual norms.
* **`ResponseGeometrySummary`.** Useful soon, but not the next mathematical tide. At present it risks packaging the interior story before its most important endpoint theorem exists.

# Q3. The missing headline theorem

## **Every finite data law is reachable in response, with an exact information budget**

Let \(X\) be finite, \(\nu_x>0\), and \(D\) any probability law. No saturation assumption and no full-support assumption on \(D\).

Let
\[
m_D=E_DS,\qquad
m_t=(1-t)m_\nu+t\,m_D,
\qquad
P_t=P_{\theta_r(m_t)}\quad(0\le t<1).
\]
Let \(R_D\) be the unique minimum-\(\mathrm{KL}(\,\cdot\,\Vert\nu)\) law with mean \(m_D\).

Then
\[
\boxed{
\begin{gathered}
P_t\longrightarrow R_D\quad(t\uparrow1),\\[2mm]
\mathrm{KL}(D\Vert\nu)
=
\underbrace{\mathrm{KL}(D\Vert R_D)}_{\text{information invisible to the features}}
+
\underbrace{\int_0^1(1-t)\,
G_{\theta_t}(\dot\theta_t,\dot\theta_t)\,dt}_{\text{information acquired by the response}}.
\end{gathered}}
\]

Moreover,
\[
E_{P_t}S=(1-t)E_\nu S+tE_DS,
\qquad
E_{P_t}F\longrightarrow E_{R_D}F
\]
for every finite observable \(F\).

This is the strongest natural completion of the user’s requested journey:

* It starts at the featureless reference law.
* It reaches every data **response**, even at a boundary mean.
* It says exactly what is and is not recovered.
* It measures the journey by the Fisher geometry already formalised.
* In saturation, \(R_D=D\), the defect vanishes, and the journey is the actual mixture segment—including its boundary endpoint.

### Statement shape in Lean terms, without code

I would expose three reusable component theorems and one flagship corollary:

1. **Endpoint response:** existence and uniqueness of a probability vector minimising finite relative entropy on the fibre of `dataMean D`.
2. **Journey convergence:** a `Tendsto` statement for the atom-mass vector of the existing chart lift, along `nhdsWithin 1 (Iio 1)`, with the path restricted or extended harmlessly below \(0\).
3. **Boundary information budget:** a finite nonnegative improper integral—or an equivalent `lintegral` formulation—equal to endpoint relative entropy, followed by the KL defect decomposition.
4. **Flagship corollary:** quantify over every finite probability law \(D\), with no interior-mean hypothesis, and combine convergence with the exact budget.

**Do not put a finite \(\theta_1\) in this statement.** At a boundary mean there is no such parameter. The law and all its bounded posterior expectations converge even while the natural coordinate escapes to infinity.

That is the next genuinely new headline: **the chart may end, but the response journey does not.**