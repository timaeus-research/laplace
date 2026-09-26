## Recommendation

**Finish the support stratification first. Then turn the ray formula into a boundary-layer calculus, including Fisher-length criteria.** These provide genuinely new structure rather than repackaging the interior theory.

One important correction to the possible endgame: **charged-polytope hypotheses do not, by themselves, make the completed family the intrinsic Fisher-metric completion.** Even in dimension one, a boundary point can lie at infinite Fisher distance. The boundary-layer analysis explains exactly why.

The Lean declarations below are proposed shapes, not claims about existing Mathlib names.

## Re-ranking

| Rank | Project | Main payoff |
|---|---|---|
| **1** | **Minimal faces, exact supports, uniform domination** | Recover the face order from absolute continuity; upgrade the global atlas to every finite \(L^p\). |
| **2** | **Boundary-layer calculus** | Polynomial TV rates, a two-sided growth criterion, and finite Fisher-length access under quantitative hypotheses. |
| **3** | **Hellinger completion and a thin `ResponseAtlas`** | An unconditional canonical metric completion, without confusing ambient Hellinger geometry with intrinsic Fisher geometry. |
| **4** | **Facewise delta method and CLT** | Statistical fluctuations of the entire reconstructed law; mathematically clean once rank 1 is available. |
| **5** | **Natural-parameter compactification** | Worth stating after the strata are explicit; the boundary consists of face families, not merely face labels. |

---

# 1. Top project: the support-stratified response atlas

Write \(P=\operatorname{conv}V\), assume \(V\neq\varnothing\), and let
\[
m_*=\min_{v\in V}\nu\{S=v\}>0.
\]
For \(M\in P\), let \(F_M\) be its minimal face and \(q_M\) its response law.

The central theorem package should be:

\[
\boxed{\operatorname{momentBody}(\nu(\,\cdot\mid S\in F))=F}
\]
for every nonempty face \(F\) of \(P\), followed by
\[
\boxed{q_M\sim \nu|_{\{S\in F_M\}},\qquad
0\le \frac{dq_M}{d\nu}\le m_*^{-1}\quad \nu\text{-a.e.}}
\]

The striking consequence is an **order-theoretic reconstruction of the polytope from its response laws**:
\[
\boxed{q_M\ll q_N\iff F_M\subseteq F_N.}
\]
In particular,
\[
q_M\sim q_N\iff F_M=F_N.
\]

Thus the face lattice is not decoration added to the statistical family: it is encoded by absolute continuity.

## Lemma chain

### 1. Supporting cuts commute with finite convex hulls

Proposed shape:
```lean
theorem convexHull_inter_supporting_hyperplane
    (hV : ∀ v ∈ V, inner u v ≤ β) :
    convexHull ℝ (↑V : Set E) ∩ {y | inner u y = β}
      =
    convexHull ℝ
      (↑(V.filter fun v => inner u v = β) : Set E)
```

**Proof route:** write a point as a finite convex combination. The weighted slacks
\[
\lambda_v(\beta-\langle u,v\rangle)
\]
are nonnegative and sum to zero. Every positive coefficient therefore belongs to a tight generator. This is the same elementary rigidity mechanism as the supporting-face concentration theorem.

Allow \(u=0,\beta=0\), so the full polytope is included.

### 2. Obtain a finite description of the minimal face

Target an interface such as:
```lean
theorem exists_minimalFace_data
    (hM : M ∈ P) :
    ∃ F : Set E,
      IsFace P F ∧
      M ∈ relativeInterior ℝ F ∧
      F = convexHull ℝ (↑(V.filter fun v => v ∈ F) : Set E) ∧
      ∀ G, IsFace P G → M ∈ G → F ⊆ G
```

For the measure-theoretic route, also provide an exposing hyperplane for \(F\).

### 3. Restricted moment body equals the face

```lean
theorem momentBody_faceMeasure_eq
    (hF : IsFace P F) (hne : F.Nonempty) :
    momentBody (faceMeasure ν F) S = F
```

**Seabed route:**

* Use the existing exposed-face concentration machinery for the upper inclusion.
* Every generator \(v\in V\cap F\) remains charged after conditioning:
  \[
  \nu_F\{S=v\}=\frac{\nu\{S=v\}}{\nu\{S\in F\}}>0.
  \]
* Hence \(V\cap F\) lies in the restricted moment body.
* Convexity and step 1 give the reverse inclusion.

No new duality theorem is needed.

### 4. Identify the response on its minimal face

Because \(M\in\operatorname{ri}F_M\), apply the existing interior response theorem to `faceMeasure ν F_M`. Transport it back to \(\nu\), using:

* `compl_eq_zero_of_mean_face`;
* `genRate_face_eq`;
* uniqueness of the entropy minimizer.

The resulting representative has the form
\[
p_M(x)=
\frac{\mathbf 1_{\{S\in F_M\}}(x)e^{\ell_M(S(x))}}
     {\int_{\{S\in F_M\}}e^{\ell_M(S)}\,d\nu}.
\]
Strict positivity of the exponential gives the essential-support theorem immediately.

Suggested public interfaces:
```lean
theorem responseMeasure_mutuallyAbsolutelyContinuous_restrict_minimalFace ...
theorem responseDens_pos_ae_iff_stat_mem_minimalFace ...
```

### 5. Prove the uniform bound

Choose \(v_*\in V\cap F_M\) maximizing \(\ell_M\) over the face. Then
\[
e^{\ell_M(S(x))}\le e^{\ell_M(v_*)}
\quad(S(x)\in F_M),
\]
while
\[
\int_{\{S\in F_M\}}e^{\ell_M(S)}\,d\nu
\ge \nu\{S=v_*\}\,e^{\ell_M(v_*)}.
\]
Therefore \(p_M\le 1/m_*\).

```lean
theorem responseDens_le_inv_minGeneratorMass
    (hM : M ∈ P) :
    ∀ᵐ x ∂ν, responseDens ν S M x ≤ minGeneratorMass ν S V ⁻¹
```

First prove the stronger face-specific bound using the minimum over \(V\cap F_M\); derive the global version afterward.

### 6. Recover the face order

The forward direction of \(F_M\subseteq F_N\Rightarrow q_M\ll q_N\) follows from the support formula.

For the converse, if \(F_M\not\subseteq F_N\), the filtered-hull description supplies a generator
\[
v\in V\cap F_M,\qquad v\notin F_N.
\]
Its fibre has positive \(q_M\)-mass and zero \(q_N\)-mass.

### 7. Upgrade continuity to every finite \(L^p\)

For \(1\le p<\infty\), the common bound \(C=m_*^{-1}\) gives
\[
\|p_M-p_N\|_p
\le C^{1-1/p}\|p_M-p_N\|_1^{1/p}.
\]

Thus the completed response map is continuous into every finite \(L^p(\nu)\). **Do not assert \(L^\infty\)-continuity:** off-face support can accumulate arbitrarily close to a face.

## The single hardest lemma

**The geometric minimal-face theorem: every \(M\in P\) belongs to the relative interior of an exposed face generated by the tight members of \(V\).**

The supporting-cut identity itself is straightforward. The difficult formalization is coordinating minimality, relative interior, and exposure.

If a usable finite half-space representation is already available, take all inequalities active at \(M\), and sum their normals. Otherwise use finite descent through supporting cuts. When refining a previously exposed face, combine its exposing functional with a sufficiently small multiple of the new relative supporting functional; finiteness of \(V\) supplies the positive slack margin needed to preserve strictness outside the old face.

This geometric lemma should be isolated from all probability code.

---

# 2. Second project: boundary layers, rates, and Fisher accessibility

Keep your notation:
\[
B_t=\int_{\{g>0\}}e^{-tg}w\,d\nu,\qquad
H(r)=\int_{\{0<g\le r\}}w\,d\nu,\qquad A>0.
\]

## The clean quantitative theorem

For \(\alpha>0\),
\[
\boxed{H(r)=O(r^\alpha)\text{ as }r\downarrow0
\iff B_t=O(t^{-\alpha})\text{ as }t\to\infty.}
\]

This is an elementary **growth equivalence**, not a deep Tauberian theorem.

### Forward direction

Tonelli gives
\[
B_t=t\int_0^\infty e^{-tr}H(r)\,dr\qquad(t>0).
\]
If \(H(r)\le Kr^\alpha\) for \(0<r\le r_0\), and
\(W=\int_{\{g>0\}}w\,d\nu\), then
\[
B_t\le K\Gamma(\alpha+1)t^{-\alpha}+We^{-tr_0}.
\]

### Reverse direction

For any \(r,t>0\),
\[
H(r)\le e^{tr}B_t.
\]
Consequently, \(B_t\le Ct^{-\alpha}\) for \(t\ge t_0\) implies
\[
H(r)\le eC r^\alpha
\quad(0<r\le 1/t_0).
\]

Your exact formula then yields
\[
\|p_t-p_F\|_1=O(t^{-\alpha}).
\]

The sharper equivalence
\[
H(r)\sim cr^\alpha
\iff B_t\sim c\Gamma(\alpha+1)t^{-\alpha}
\]
is the genuinely Tauberian extension. Defer it: the big-\(O\) equivalence already supplies useful geometry with much less infrastructure.

## Minimal first module

Write `BoundaryLayerBounds`, with no face geometry in its core. Accept:

* a measurable nonnegative slack \(g\);
* a nonnegative integrable weight \(w\);
* definitions of \(H\) and \(B\).

Proposed declarations:
```lean
theorem boundaryMass_le_exp_mul_offFaceMass ...
theorem offFaceMass_eq_laplace_boundaryMass ...
theorem offFaceMass_le_of_boundaryMass_le_rpow ...
theorem offFaceMass_isBigO_iff_boundaryMass_isBigO ...
```

If the Gamma-integral route is awkward, establish the polynomial bound first by a dyadic decomposition. The exact Gamma constant is a refinement, not a prerequisite.

## The geometric dividend: finite Fisher-length rays

For the tilted law \(p_t\),
\[
\text{Fisher speed}(t)^2=\operatorname{Var}_{p_t}(g).
\]
Since the normalizing denominator is at least \(A\),
\[
\operatorname{Var}_{p_t}(g)
\le \frac1A\int_{\{g>0\}}g^2e^{-tg}w\,d\nu
\le \frac{16}{At^2}B_{t/2}.
\]
Thus a polynomial boundary layer of any positive exponent implies
\[
\boxed{\operatorname{Length}_{\mathrm{Fisher}}(p_{[T,\infty)})
=O(T^{-\alpha/2}).}
\]

This turns the boundary-ray module into a theorem about **metric accessibility**, not merely convergence.

## Why a general Fisher-completion theorem is false

Take \(S(x)=x\) on
\[
X=\{0,1\}\cup\{a_k:k\ge2\},\qquad a_k=e^{-k^2}.
\]
Give \(0\) and \(1\) positive reference mass, and give \(a_k\) mass proportional to \(k^{-2}\). All charged-polytope hypotheses hold for \(P=[0,1]\).

Consider \(p_t\propto e^{-tS}\nu\). It converges in TV to \(\delta_0\). But on each disjoint interval
\[
t\in[a_k^{-1},2a_k^{-1}],
\]
the atom at \(a_k\), together with the charged atom at zero, gives a Fisher-length contribution bounded below by a constant times \(1/k\). Hence the total length diverges.

The family is one-dimensional, so there is no alternative intrinsic route around this divergence: zero lies at infinite Fisher distance.

**Compactness in \(L^1\) does not imply Fisher accessibility.**

---

# 3. The unconditional metric capstone

Use **ambient Hellinger distance**
\[
d_H(p,q)=\|\sqrt p-\sqrt q\|_2.
\]
For probability densities,
\[
d_H(p,q)^2\le\|p-q\|_1\le2d_H(p,q).
\]

Therefore:

* the \(L^1\) and Hellinger topologies coincide;
* the completed family is Hellinger-compact and complete;
* it is the metric completion of the interior family equipped with the **restricted ambient Hellinger metric**.

This is a clean unconditional theorem. The map \(p\mapsto2\sqrt p\) also connects its infinitesimal geometry to Fisher information. But ambient distance and intrinsic Fisher distance must remain distinct.

A thin `ResponseAtlas` is now worthwhile. Suggested field order:

1. reference data and charged-polytope certificate;
2. response map and mean right-inverse;
3. continuity and identification with the completed family;
4. minimal-face support and uniform domination;
5. facewise analytic charts.

Keep rigidity, deformation retraction, metric-completion results, Fisher identities, and jet estimates as **theorems about the structure**, not redundant fields.

---

# 4. CLT: the next statistical theorem, not the next foundation

For IID observations from \(q_M\), put \(F=F_M\). Their empirical means remain in \(F\), and
\[
\sqrt n\,(q_{\widehat M_n}-q_M)
\Rightarrow Dq_M[G]
\quad\text{in }L^1(\nu),
\]
where \(G\) is Gaussian on \(\operatorname{dirSpan}F\), with covariance \(C_F\), and
\[
Dq_M[h](x)
=p_M(x)\,
\big\langle C_F^{-1}h,S(x)-M\big\rangle.
\]

**No Banach-space CLT is needed:** the limiting random density lies in the finite-dimensional image of \(Dq_M\). The route is finite-dimensional CLT plus a facewise delta method.

I cannot certify the current multivariate-CLT API without inspecting your Mathlib revision. Audit it before scheduling this project; scalar CLT plus Cramér–Wold still requires substantial weak-convergence infrastructure. Meanwhile, the deterministic facewise Fréchet derivative and remainder theorem are independently valuable.

Finally, the correct natural-parameter compactification is not
\(\Theta\cup\{\text{face labels}\}\): each face contributes its **own effective natural-parameter space**. Set-theoretically the strata correspond to
\[
\bigsqcup_{F\ne\varnothing}\Theta_F
\longleftrightarrow
\bigsqcup_{F\ne\varnothing}\operatorname{ri}F=P,
\]
with a non-disjoint-union topology supplied by the completed family. Rank 1 gives this compactification its precise mathematical content.