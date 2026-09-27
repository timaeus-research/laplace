## Executive verdict

The six modules form a coherent response-map package. I see no substantive contradiction in the statements as reported. The main risks are **interpretive**:

1. A canonical face chart is not yet a chart for **every** face: existence of an admissible seed remains an accessibility issue.
2. Local or conditional equivalence of Fisher and Hellinger topologies must not become an unconditional boundary identification.
3. Covariance-orthogonal projection under the **data law** is not generally orthogonal projection for the **fitted-model Fisher metric**.
4. The exponential featureless→data segment is canonical for the exponential connection, not generally shortest for response length.

For Q2, the honest global theorem is indeed a decomposition over **accessible faces**, unless an additional theorem establishes accessibility of every face.

---

# Q1. Audit of the six modules

This is an audit of the mathematical statements supplied, rather than of their Lean implementations.

## 1.1 `SeedIndependentAtlas`

**Sound, with an important existence/uniqueness distinction.**

The seed-transport and one-point-agreement results are exactly the right atlas coherence statements. In particular:

- `faceEmbedExt_eq_iff` identifies the precise compatibility required of two seeds.
- `faceEmbedExt_transport` expresses change of origin, not a change of chart image.
- `faceEmbedExt_eq_of_charged_face` makes the chart canonical **once an admissible seed exists**.

Do not summarize the last result as “every charged face has a canonical chart” without adding accessibility.

Two other qualifications:

- `faceEmbedExt_injective` is conditional on law uniqueness in the **submodel completion**. It does not itself provide an isometric embedding or a topological embedding.
- Extended charts for different faces should not be expected to have disjoint images. Their finite strata can be disjoint; their completed images can meet on lower-dimensional strata.

For the note, distinguish notation explicitly:
\[
j_F:W_F\longrightarrow\widehat W,
\qquad
\widehat j_F:\widehat W_F\longrightarrow\widehat W.
\]
The stratification uses \(j_F(W_F)\), not \(\widehat j_F(\widehat W_F)\).

Also make clear that “all vertices charged” means positive mass on the statistic fibre \(S^{-1}\{v\}\), not that the underlying sample space has an atom literally named \(v\).

## 1.2 `ResponseProductAffinity`

**Correct constants under your convention \(H=\|\sqrt p-\sqrt q\|_2\).**

Take
\[
\operatorname{TV}(P,Q)=\sup_A|P(A)-Q(A)|
=\frac12\int|p-q|.
\]
For normalized real roots \(f,g\), put
\[
H=\|f-g\|_2,\qquad A=\langle f,g\rangle.
\]
Then
\[
H^2=2-2A,
\]
and Cauchy–Schwarz actually gives
\[
\operatorname{TV}(f^2\mu,g^2\mu)
\le \frac12\|f-g\|_2\|f+g\|_2
=H\sqrt{1-\frac{H^2}{4}}
=\sqrt{1-A^2}.
\]

Thus **“TV \(\le H\)” is correct**, but label it the convenient coarse bound. Readers using \(H_{\rm norm}=H/\sqrt2\) will instead recognize \(\operatorname{TV}\le\sqrt2 H_{\rm norm}\).

For nonnegative probability roots,
\[
A\in[0,1],\qquad
H_n^2=2-2A^n
=2\left[1-\left(1-\frac{H^2}{2}\right)^n\right]
\le nH^2.
\]
Your theorem already *is* the standard Hellinger tensorization inequality. The exact affinity identity is sharper; there is not a separate missing “standard \(H_n^2\le nH^2\)” theorem.

**Small proof-description correction:** for arbitrary signed roots, \(A\) can be negative. Standard Bernoulli on \(A=1+x\) directly covers \(A\ge0\), not all \(A\in[-1,1]\). The stated inequality still holds, for example from
\[
1-A^n=(1-A)\sum_{k=0}^{n-1}A^k\le n(1-A).
\]
So describe the general result as the elementary power inequality, or restrict the Bernoulli description to nonnegative roots.

The sharper product-testing statement is
\[
\operatorname{TV}(P^{\otimes n},Q^{\otimes n})
\le\sqrt{1-A^{2n}},
\qquad
\operatorname{err}(\varphi)\ge
\frac{1-\sqrt{1-A^{2n}}}{2}.
\]

Your existing tail theorem has the right factors:
\[
H(Q_{x_t},Q_{x_\infty})\le R(t)/2
\quad\Longrightarrow\quad
\operatorname{err}\ge \frac{1-\sqrt n\,R(t)/2}{2}.
\]
It is noninformative when the right side is negative, not false. Advertising the maximum with zero is optional.

## 1.3 `ResponseJourneyResolution`

**The separation result is sufficient, not necessary, and that is the right interpretation.**

A good title is:

> **Sufficient Fisher-ball separation for classification.**

For open balls, the condition
\[
\rho_0+\rho_1\le d_F(\theta_0,\theta_1)
\]
does imply disjointness. The class-1 error bound then follows because entering the class-0 ball entails leaving the class-1 ball.

This does **not** show:

- optimality of the classifier;
- a necessary sample size;
- impossibility when the balls overlap;
- that a short response path proves overlap.

In particular, \(d_F\le L\) is an **upper** bound. It cannot certify the lower-distance condition needed for disjoint balls. Your removal of that claim is correct.

For the confidence theorem, keep visible:

- \(n>0\), \(r>0\);
- positivity of the coercivity constant \(\lambda\);
- the relevant patch and segment hypotheses;
- the convention for samples whose empirical means do not have an interior response.

The last point is especially important if `θr` is a total Lean function whose inverse-mean interpretation only holds on interior means. The exit event should count inadmissible empirical means as failures, rather than silently assigning them a meaningful response.

## 1.4 `ResponseLawContinuity`

**The retraction is not a mathematical error, but it should disappear from the intrinsic statement in the note.**

For a probability law \(D\ll\nu\), bounded \(S\), and bounded measurable \(k\),
\[
\operatorname{Cov}_D(S,k)\in W.
\]
Consequently every genuine retraction \(p\) acts identically on that vector, and `densVel`, `densBilin`, and the resulting intrinsic quantities are independent of \(p\).

Until that bridge is proved, the formal results describe a **chosen projected extension** of the geometry. They should not yet be advertised as proving the intrinsic, retraction-free density formulation.

There are two clean proofs of membership:

1. Integrate the centered \(W\)-valued statistic in a closed finite-dimensional subspace.
2. Use the annihilator: if \(a\in W^\perp\), then \(\langle a,S\rangle\) is \(\nu\)-a.e. constant, hence \(D\)-a.e. constant, and
   \[
   \langle a,\operatorname{Cov}_D(S,k)\rangle=0.
   \]

I would try the second first if the seabed already characterizes `dirSpan` through constant contrasts.

Two further qualifications:

- Interior membership of the limiting mean must be **relative** to the correct affine hull. Ambient Euclidean interior can be empty.
- Continuity of an “effective dimension” is appropriate for a continuous spectral statistic, not for literal matrix rank. Keep its definition visible enough to prevent that reading.

## 1.5 `ResponseHellingerAtlas`

**Yes: the conditional formulation is appropriate.**

I would state the two levels separately.

**Interior/local theorem.** On the specified convex coercive patch, with \(B<\infty\), \(\lambda>0\), and the needed segment containment,
\[
\sqrt\lambda\,d_F\le 2B\,H\le B\,d_F.
\]
Hence the two notions of convergence agree there.

**Completion theorem.**
\[
H(Q_x,Q_y)=\|\Psi_x-\Psi_y\|_2\le \tfrac12\widehat d(x,y),
\]
so completion convergence implies Hellinger and TV convergence. If \(\widehat W\) is compact and completion laws separate points, then
\[
\Psi:\widehat W\to L^2(\nu)
\]
is a closed embedding, giving the converse convergence statement.

Do not drop compactness from the second argument merely because the root map is injective and Lipschitz. An injective continuous map need not have continuous inverse onto its image.

“Conditional completion Hellinger embedding” is more precise than suggesting an unconditional global equivalence of metrics.

## 1.6 `ResponseSubmersionCalculus`

**Strong algebraic differential structure; two naming cautions.**

First, the results establish a surjective differential, a canonical linear splitting, and a quotient equivalence. Without a specified Banach topology on `bddSpace` and a corresponding nonlinear submersion theorem, do not infer a Banach-manifold local product theorem. “Split response differential” is fully justified.

Second, distinguish the two geometries:
\[
\operatorname{Var}_{D}(k)
=\operatorname{Var}_{D}(k_{\rm hor})
+\operatorname{Var}_{D}(k_{\rm inv})
\]
is covariance orthogonality under the **data law**. In general,
\[
\operatorname{Var}_{D}(k_{\rm hor})
\ne |D\Phi_g[k]|_{F,\Phi(g)}^2.
\]
The horizontal regression uses the data covariance; response Fisher energy uses the fitted-model covariance. They agree at the featureless law, and more generally at a correctly specified family law.

Your explicit covariance-inverse formula is therefore important. It prevents an unjustified global “response is an orthogonal Fisher projection” slogan.

---

# Q2. The stratification theorem

## The correct target

Assume:

- bounded statistics and the standing probability hypotheses;
- a finite vertex set \(V\);
- `momentBody ν = convexHull ℝ V`;
- every vertex fibre is charged;
- the usual mean-range and inverse-mean results for the face models.

Let \(\mathcal F\) be the **nonempty** faces, including the whole polytope. Define mean-accessibility by
\[
\operatorname{Accessible}(F)
\iff
\exists x\in\widehat W,\quad
\operatorname{meanExt}(x)\in\operatorname{ri}F.
\]

The desired theorem is:

> **Accessible-face stratification.** For each accessible face \(F\), there is a canonical finite face chart \(j_F:W_F\to\widehat W\), and
> \[
> j_F(W_F)
> =\{x\in\widehat W:\operatorname{meanExt}(x)\in\operatorname{ri}F\}.
> \]
> These sets are pairwise disjoint and cover \(\widehat W\). Moreover,
> \[
> \operatorname{meanExt}(\widehat W)
> =\coprod_{\operatorname{Accessible}(F)}\operatorname{ri}F.
> \]

Equivalently,
\[
\boxed{\widehat W
=\coprod_{\operatorname{Accessible}(F)}j_F(W_F).}
\]

This is initially a **set-theoretic face decomposition**. Do not call it a Whitney stratification, or claim a frontier condition or a particular closure formula, without additional results.

## Dependency order

### Step 1: Identify the face moment body — unconditional

For
\[
E=\{x:\langle u,S(x)\rangle=\beta\},\qquad
F=\operatorname{conv}\{v\in V:\langle u,v\rangle=\beta\},
\]
prove
\[
\operatorname{momentBody}(\nu_E)=F.
\]

You have the upper inclusion. For the reverse inclusion:

- every tight vertex has positive mass;
- conditioning on \(E\) preserves positive mass at that vertex;
- hence every tight vertex belongs to the face moment body;
- convexity supplies their convex hull.

This also proves positivity of \(\nu(E)\) for every nonempty exposed face.

Then
\[
\operatorname{intrinsicInterior}(\operatorname{momentBody}(\nu_E))
=\operatorname{ri}F
\]
is a rewrite.

**Important:** positive face mass is not a Fisher accessibility proof.

### Step 2: Package minimal-face geometry — unconditional

For every \(M\) in the polytope:
\[
M\in\operatorname{ri}F_M,
\qquad F_M=\operatorname{minimalFacePoly}(V,M),
\]
and \(F_M\) is the unique face whose relative interior contains \(M\).

Also package the exposing-vector theorem with the face-body identification from Step 1. Later proofs should not repeatedly unpack tight vertices.

### Step 3: Establish the seed/accessibility bridge — check this explicitly

To construct `faceEmbed`, one needs an **admissible seed**, not merely a point with the correct mean.

The bridge should say that for \(M\in\operatorname{ri}F\), accessibility of \(M\) supplies \(x_0,v_0\) with
\[
\operatorname{meanMap}_{\nu_E}(v_0)=M,
\qquad
Q_{x_0}=\text{ambient realization of }P^F_{v_0}.
\]

If your current definition of accessibility already includes this law identity, this is done. If accessibility only means “\(M\) lies in the image of `meanExt`”, check that an existing theorem supplies the law identity.

**Singleton mean fibres alone do not manufacture an admissible seed.** They compare points after their existence has been established.

### Step 4: Construct the canonical chart — conditional on accessibility

Use one admissible seed, then `faceEmbedExt_eq_of_charged_face` to remove its choice.

Prove
\[
\operatorname{meanExt}(j_F(w))
=\operatorname{meanMap}_{\nu_E}(w).
\]
Finite face-model mean surjectivity gives
\[
\operatorname{meanExt}(j_F(W_F))=\operatorname{ri}F.
\]

This is the saturation statement: one accessible point of the face interior makes the entire face interior accessible.

### Step 5: Identify the entire ambient fibre stratum

Given \(x\) with mean \(M\in\operatorname{ri}F\), set
\[
w=\theta_r^F(M).
\]
Then \(x\) and \(j_F(w)\) have the same mean. Apply `meanExt_eq_face_unique`:
\[
x=j_F(w).
\]

This step needs mean intertwining and finite mean surjectivity; `completionLaw_faceEmbed` alone is not the most direct bridge.

### Step 6: Cover and disjointness — no extra accessibility hypothesis

First ensure
\[
\operatorname{meanExt}(x)\in\operatorname{momentBody}(\nu)
\]
for every completion point, by continuity and closedness of the polytope.

For any \(x\), choose the minimal face of its mean. That face is accessible **by this very point**, so Step 5 places \(x\) in its chart. Uniqueness of relative-interior face membership gives disjointness.

## Is every face automatically accessible?

**Not from the hypotheses listed.**

Charged vertices ensure the correct face moment body and positive limiting face mass. They do not exclude arbitrarily slow accumulation of mass near a supporting hyperplane. Such accumulation is precisely why a Fisher-length summability condition can matter.

Your condition \(\sum_k\sqrt{a_k}<\infty\) is genuinely stronger than finite total mass. Do not erase it through polytope terminology: a polytope moment body does not mean that the pushforward statistic law has finite support.

Useful unconditional special case:

> If the statistic pushforward has finite support, the positive gap between the exposed face and the remaining support gives exponential normal-ray decay, hence finite tail length and accessibility.

With a per-face accessibility theorem, the displayed decomposition upgrades to a decomposition over **all** nonempty faces.

A valuable corollary of the charged-polytope fibre uniqueness package is also worth extracting: two completion points with equal means lie over the same minimal-face interior, and hence coincide. Thus global mean—and consequently law—injectivity may follow **without** proving that every face is accessible.

---

# Q3. The canonical featureless→data journey

## Yes, with the correct meaning of “canonical”

Assume an admissible density \(q\) and constants \(0<c\le C<\infty\) such that
\[
c\le q\le C\quad \nu\text{-a.e.}
\]
Choose a bounded measurable representative \(h=\log q\), and put
\[
Z(t)=\int e^{th}\,d\nu,\qquad
\rho_t=\nu.\operatorname{tilted}(th),\qquad
\theta_t=\Phi(th).
\]
Then
\[
\frac{d\rho_t}{d\nu}=\frac{q^t}{Z(t)},\quad
\rho_0=\nu,\quad \rho_1=D.
\]

This is the exponential-connection geodesic. It is generally neither a Fisher–Rao geodesic in the data manifold nor a shortest response path.

Also qualify “maximal entropy”: \(\nu\) maximizes entropy **relative to \(\nu\)**, namely \(-D_{\rm KL}(\cdot\|\nu)\). Absolute maximal entropy needs a specified reference measure and an appropriate uniformity statement.

## First theorem package: endpoints, derivative, length

Prove the named specialized statements
\[
\theta_0=0,\qquad
\theta_1=\theta_r(E_D S),
\]
\[
\theta'_t
=(CDE\,\theta_t)^{-1}\operatorname{Cov}_{\rho_t}(S,\log q),
\]
and
\[
d_F(0,\theta_1)
\le L_e(q):=
\int_0^1
\sqrt{\operatorname{pullbackForm}_{t\log q}(\log q,\log q)}\,dt.
\]

This is largely a specialization layer, but an important one: it directly answers the user’s featureless→data directive.

### Initial regression

Let
\[
v_0=\operatorname{responseVel}(0,h),\qquad
h_{\rm reg}=\operatorname{horLin}_0(v_0).
\]
Then
\[
\operatorname{Cov}_\nu(S,h-h_{\rm reg})=0,
\]
\[
\operatorname{Var}_\nu h
=|v_0|_{F,0}^2+\operatorname{Var}_\nu(h-h_{\rm reg}).
\]

Say “the initial response is determined by regression of \(\log q\) on the statistics.” This avoids identifying the regression coefficient with \(\theta'_0\) without checking the family’s natural-parameter sign convention.

## Mixture comparison

For
\[
D_t^m=(1-t)\nu+tD,
\]
the response is exactly
\[
\theta_t^m=\theta_r\bigl((1-t)m_\nu+tm_D\bigr),
\]
and
\[
(\theta_t^m)'
=(CDE\,\theta_t^m)^{-1}(m_D-m_\nu).
\]

This is a particularly useful contrast:

- the mixture response path depends only on the endpoint means;
- the exponential response path can depend on features of \(D\) invisible to its endpoint mean.

If \(m_D=m_\nu\), the mixture response is constant. The exponential response need not be constant: intermediate means of \(q^t/Z(t)\) need not equal the endpoint mean.

Do **not** advertise a general length ordering. The existing theory gives
\[
d_F(0,\Phi(D))\le L_e(q),\qquad
d_F(0,\Phi(D))\le L_m(D),
\]
not a comparison between \(L_e\) and \(L_m\). Such a comparison would need a separate geometric theorem. In one response dimension, monotone paths between the same endpoints do have equal length; excursions can increase length.

## Entropy monotonicity: clean and worthwhile

Let \(\psi(t)=\log Z(t)\). Then
\[
\psi'(t)=E_{\rho_t}h,\qquad
\psi''(t)=\operatorname{Var}_{\rho_t}h,
\]
and
\[
D_{\rm KL}(\rho_t\|\nu)=t\psi'(t)-\psi(t).
\]
Therefore
\[
\boxed{\frac d{dt}D_{\rm KL}(\rho_t\|\nu)
=t\,\operatorname{Var}_{\rho_t}(\log q)\ge0}
\qquad (t\in[0,1]).
\]

This is a genuine journey-specific theorem, not merely a renamed coefficient-path result.

By contrast, do not claim monotonicity of a response defect. If the defect is
\[
\Delta(t)=D_{\rm KL}(\rho_t\|P_{\theta_t}),
\]
moment matching yields
\[
\Delta'(t)
=\operatorname{Cov}_{\rho_t}
\left(h,\log\frac{d\rho_t}{dP_{\theta_t}}\right),
\]
which has no immediate sign. A good later target is the initial second-order identity
\[
\Delta''(0)=\operatorname{Var}_\nu(h-h_{\rm reg}),
\]
subject to the required differentiation and KL identities.

**Ranking within Q3:** canonical endpoints/velocity/length; initial regression specialization; KL monotonicity; mixture response formula; local defect expansion. Global defect monotonicity is not a target without additional hypotheses.

---

# Q4. Next six modules

My ranking by depth × reachability is:

| Rank | Module | One-line deliverable |
|---|---|---|
| **1** | `AccessibleFaceStratification` | Identify face moment bodies, bridge accessibility to seeds, and prove \(\widehat W=\coprod_{F\ {\rm accessible}}j_F(W_F)\). |
| **2** | `CanonicalDataJourney` | For \(c\le q\le C\), package the \(q^t/Z(t)\) journey, endpoints, velocity, initial regression, length, and KL monotonicity. |
| **3** | `AbsolutelyContinuousForcing` | Prove \(\operatorname{Cov}_D(S,k)\in W\) for \(D\ll\nu\), then remove \(p\) from density response geometry. |
| **4** | `ResponseChamberClearance` | Turn actual containment of a Fisher ball in a chamber into an explicit coefficient-space clearance certificate. |
| **5** | `MixtureResponseJourney` | Prove the affine-mean response formula and its derivative and length, with interior-segment hypotheses explicit. |
| **6** | `SharpAffinityTesting` | Add \(\operatorname{TV}\le H\sqrt{1-H^2/4}\) and exact affinity-based \(n\)-sample testing bounds. |

### Dependencies and scope

**Rank 1** should be staged internally in the six steps above. Do not block the accessible-face theorem on proving universal accessibility.

**Rank 2** uses the coefficient calculus already present. The basic journey does not depend on rank 3. Its KL monotonicity part needs bounded-tilt differentiation of the log partition function, not general response curvature.

**Rank 3** should produce:
\[
p_1(\operatorname{densForcing}(q,k))
=p_2(\operatorname{densForcing}(q,k))
=\operatorname{densForcing}(q,k)
\]
after the appropriate subtype/coercion identification, and corresponding `densVel`/`densBilin` independence results. It should also connect density-based geometry to `responseVel` for normalized tilt densities.

**Rank 4** must first state genuine clearance, for example
\[
B_F(\theta,\delta)\subseteq\mathcal C.
\]
Then, under the segment upper-Fisher bound,
\[
\sqrt\Lambda\,r<\delta,\qquad
\langle y-\theta,y-\theta\rangle<r^2
\quad\Longrightarrow\quad y\in\mathcal C.
\]
This discharges frozen-margin hypotheses only when those hypotheses really follow from remaining in \(\mathcal C\). Metric closeness alone does not prove a sign margin.

**Rank 5** depends naturally on rank 3 for a unified intrinsic formulation. For endpoints with interior means, convexity gives an interior mean segment. For boundary endpoint means, formulate only on the interval where the response chart is defined, unless you deliberately invoke the completion theory.

**Rank 6** is a low-risk sharpening and should not delay the structural theorems.

Full second-order response calculus and curvature remain a **new project**. Differentiating this one bounded exponential segment, or proving its initial defect expansion, is a manageable precursor—not the same commitment as building a Hessian/connection/curvature API.

---

# The theorem I would put last in the note

I would finish with the existing tail theorem, explicitly presented as the operational meaning of a completed journey:

> **Finite samples cannot resolve the end of a finite-length response journey.**  
> Let \(\theta_t\) be a response path with integrable Fisher speed, completion endpoint \(x_\infty\), and remaining length
> \[
> R(t)=\int_t^\infty|\dot\theta_s|_F\,ds.
> \]
> For every \(n\) and every measurable randomized test \(0\le\varphi\le1\),
> \[
> \frac12\left[
> \int\varphi\,dQ_{\theta_t}^{\otimes n}
> +\int(1-\varphi)\,dQ_{x_\infty}^{\otimes n}
> \right]
> \ge
> \max\left\{0,\frac12-\frac{\sqrt n}{4}R(t)\right\}.
> \]

It joins the note’s geometry, journeys, completion, and sampling interpretation in one statement. The laws here are the **response-family laws**, not automatically the original data laws—a distinction worth preserving in the final sentence as well.