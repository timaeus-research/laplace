## Recommendation

**Make A the next programme: finite-range accessibility and the face-incidence theorem for the completion.** It turns the accessible-face atlas into an unconditional description of the entire completion, including how its boundary pieces meet. That is a substantial new theorem, not another closing package.

There are two important corrections to the proposed formulation:

1. **The variance generally decays as \(e^{-\mathrm{gap}\,t}\), not \(e^{-2\mathrm{gap}\,t}\).** Its square root decays as \(e^{-\mathrm{gap}\,t/2}\), which is enough for finite Fisher length.
2. The completed atlas is a **set-theoretic disjoint union of strata**, not a topological coproduct. Its interest is precisely that the strata accumulate on one another.

I would follow A with B. The resulting progression is: **finish the global boundary geometry, then develop the second-order differential geometry.**

I use the declarations supplied in the question as the verified seabed inventory. Below, new names are proposed names; the mathematical statements are precise, but I am not claiming checked Lean signatures or unreported existing declarations.

---

# Q1. Ranking by depth × reachability

### 1. A — Unconditional finite-range stratification

This has the best combination of mathematical substance and a short dependency distance. Finite essential range supplies a genuine positive support gap; that supplies finite-length normal rays; the existing general-face propagation and atlas theorems then do most of the global assembly. The important new result is not merely “every face is accessible,” but
\[
\overline{X_F}
 =\bigcup_{\varnothing\ne E\subseteq F}X_E
 =\operatorname{meanExt}^{-1}(F).
\]
This describes the completion’s incidence geometry exactly. It also cleanly separates phenomena caused by finite support from the accessibility obstructions possible for more general statistics.

### 2. B — Second-order response geometry

This is the deepest natural continuation of the response-map section itself. The first derivative is regression; the second derivative measures the mismatch between third cumulants of the data law and its response. There is a particularly clean connection theorem: the response is mixture-affine, while its exponential covariant Hessian is an explicit cumulant defect. The main caution is conceptual: this is a theorem about the covariant derivative of a map, **not generally a connection descending from the data manifold to the family**. Formalising higher derivatives and connections is a larger infrastructure commitment than A, but the central formulas are accessible now.

### 3. C(2) — Parametrised response atlases

Make this more than “apply the response map to several laws”: prove a coherent theorem for parameterised data families, their response maps, their differentiated regressions, and their boundary specialisations. This would give a strong global interpretation of the atlas as the image of the data manifold. Its weakness as the immediate next programme is that much of the pointwise content already exists; without a specific new parameter-dependent boundary theorem, it risks becoming API work. It becomes substantially better after A and B.

### 4. C(4) — Quantitative finite-range boundary asymptotics

My concrete proposal for “other” is a **normal-cone asymptotics programme**: leading support-gap asymptotics for mass, mean, Fisher speed and distance-to-endpoint, with uniform estimates on compact subsets of a normal cone’s interior. This would connect the face lattice to quantitative rates of response degeneration. It should follow A: the elementary exponential upper bound is easy, but sharp coefficients, uniformity near cone walls, and transitions between exposed faces require genuinely new work. Do not start by promising a full manifold-with-corners theorem.

### 5. C(1) — Global quotient theorem

Useful, but likely less new than it initially sounds. If the response is a continuous retraction onto the family and has the expected continuous section, identifying its fibres already gives a topological quotient theorem. The more interesting smooth statement is a submersion/fibre theorem. Crucially, the invisible tangent space
\[
\{h:\operatorname{Cov}_{D}(S,h)=0\}
\]
depends on \(D\); this is not ordinarily a quotient by one fixed linear space of invisible tilts. I would extract the short global quotient corollary when convenient, but not make it the next six-module research programme.

### 6. C(3) — Converse resolution theorem

Potentially important, but presently the least justified by the stated inventory. A large remaining path length or a large one-sided divergence does not by itself imply statistically detectable separation. The converse must use a lower bound on an actual separation quantity—Hellinger distance, affinity deficit, or testing distance—and then tensorise it. “Under coercivity” needs to be an explicit theorem hypothesis, not a placeholder. First establish the proposed geometric-to-statistical lower bound in an interesting class; only then promise a two-sided resolution programme.

---

# Q2. Six modules for A

## Conventions and hypotheses

Write \(P_\theta\) for the existing family law and \(\widehat W\) for its Fisher completion.

Use an **actual finite essential support**
\[
V\subseteq \text{statistic space},
\]
meaning:

- \(V\) is finite;
- \(\operatorname{statPoint}S\in V\), \(\nu\)-a.e.;
- every fibre over \(v\in V\) has positive \(\nu\)-measure.

Remove zero-mass points from a finite a.e. cover before using it as \(V\). Set
\[
P=\operatorname{conv}(V).
\]

For a proper nonempty exposed face, use the orientation
\[
F=\{x\in P:\langle u,x\rangle=\beta\},
\qquad
\beta=\max_{v\in V}\langle u,v\rangle,
\]
with \(u\in W\), and the seabed ray \(\theta-tu\) that concentrates on this face. Thus the ray reweighting favours larger \(\langle u,S\rangle\). If the actual family declaration uses the opposite exponential sign, reverse the exposing vector; the invariant requirement is that this is the orientation of `tendsto_measureReal_family_ray_faceFibre`.

Let
\[
T=\{v\in V:\langle u,v\rangle=\beta\},\quad
\delta=\min_{v\in V\setminus T}(\beta-\langle u,v\rangle)>0,
\]
and
\[
D=\max_{v\in V}(\beta-\langle u,v\rangle).
\]

The full face \(P\) is handled separately; it needs no positive gap.

---

## 1. `FiniteRangeFaceGeometry`

**Deliverable:** finite essential support gives a charged polytope, and every proper nonempty face has positive-gap exposing data.

### Statements

1. `momentBody_eq_conv_finite_essentialRange`:
   \[
   \operatorname{momentBody}(S,\nu)=\operatorname{conv}(V).
   \]

2. `finiteRange_charged`:
   the model is a charged polytope model under the existing ambient model hypotheses.

3. `exists_exposing_gap_of_nonempty_proper_face`:

   For every nonempty proper face \(F\) of \(P\), there exist \(u\in W\), \(\beta\in\mathbb R\), and \(\delta>0\) such that
   \[
   F=\operatorname{conv}(T),\qquad
   \forall v\in V\setminus T,\quad
   \langle u,v\rangle\le\beta-\delta.
   \]

4. `finiteRange_faceMeasure`:
   the face model has finite essential support \(T\).

### Dependencies

- Existing moment-body/support machinery.
- Finite-dimensional polytope fact: every face of a polytope is exposed.
- `momentBody_faceMeasure_eq`.
- `faceMeasure_charged` for compatibility with the existing face-model package.

### Care needed

The geometry is routine, but the formal support bookkeeping is not optional. An arbitrary finite a.e. cover can contain zero-mass “vertices” and give the wrong polytope.

---

## 2. `FiniteRangeRayDecay`

**Deliverable:** explicit exponential concentration and an integrable Fisher-speed bound.

Fix \(\theta\in W\), and put
\[
p=P_\theta(S\in F)>0,\qquad r=\frac{1-p}{p}.
\]

### Statements

1. `family_ray_conditional_face_eq`:
   \[
   P_{\theta-tu}(\,\cdot\mid S\in F)
     =P_\theta(\,\cdot\mid S\in F)
     =P^F_{\theta|F}.
   \]
   Here \(P^F_{\theta|F}\) means the ambient pushforward of the existing face-family law, with the seabed’s induced face parameter.

2. `family_ray_offFace_mass_le`:
   \[
   P_{\theta-tu}(S\notin F)\le r e^{-\delta t}
   \qquad(t\ge0).
   \]

3. `raySpeedSq_le_exp_gap`:
   \[
   \boxed{\;
   \operatorname{raySpeedSq}(S,\nu,\theta,u,t)
      \le D^2r e^{-\delta t}
   \;}
   \qquad(t\ge0).
   \]

4. `ray_fisherLength_tail_le`:
   \[
   \int_T^\infty
     \sqrt{\operatorname{raySpeedSq}(S,\nu,\theta,u,t)}\,dt
   \le
   \frac{2D\sqrt r}{\delta}e^{-\delta T/2}.
   \]

Export the final result in the existing `lintegral`/`ENNReal` convention as well.

### Proof

After cancelling \(e^{\beta t}\), the face contribution to the normalising denominator is \(p\), while the off-face contribution is at most \((1-p)e^{-\delta t}\). Then use
\[
\operatorname{Var}(Y)\le \mathbb E[(Y-\beta)^2]
\]
for \(Y=\langle u,S\rangle\).

### Dependencies

- `raySpeedSq` and `continuous_raySpeedSq`.
- Family reweighting identities.
- `measureReal_family_ray_faceFibre`.
- The path/tilt `lintegral` equivalences where needed for interoperability.

### Important correction

For a two-level statistic with levels \(\beta\) and \(\beta-\delta\),
\[
\operatorname{Var}_{P_{\theta-tu}}\langle u,S\rangle
   \sim c\,\delta^2e^{-\delta t}.
\]
Thus the proposed \(e^{-2\delta t}\) bound is generally false. It becomes valid only if “gap” is redefined as half the support gap.

---

## 3. `ExposedFaceRayEndpoint`

**Deliverable:** a finite-length normal ray reaches the correct face law, in any codimension.

I would make this module **more general than finite range**.

### Statement

Assume the existing charged-polytope/face-model hypotheses, a nonempty exposed face \(F\), its correctly oriented normal ray, and
\[
\int_0^\infty\sqrt{\operatorname{raySpeedSq}
   (S,\nu,\theta,u,t)}\,dt<\infty.
\]
Then there exists a unique \(\xi_{\theta,F}\in\widehat W\) such that
\[
\operatorname{Tendsto}
  \bigl(t\mapsto \iota(\theta-tu)\bigr)
  \;\operatorname{atTop}\;
  (\mathcal N\xi_{\theta,F}),
\]
and
\[
\begin{aligned}
\operatorname{completionLaw}(\xi_{\theta,F})
  &=P^F_{\theta|F},\\
\operatorname{meanExt}(\xi_{\theta,F})
  &=\mathbb E_{P^F_{\theta|F}}S
    \in\operatorname{ri}(F).
\end{aligned}
\]

Also export the metric tail estimate
\[
d_{\widehat W}(\iota(\theta-Tu),\xi_{\theta,F})
 \le\int_T^\infty\sqrt{\operatorname{raySpeedSq}(t)}\,dt.
\]

### Dependencies

- General length-to-distance and completion-Cauchy machinery.
- `tendsto_measureReal_family_ray_faceFibre`.
- The conditional-law identity from module 2, factored out if necessary.
- `momentBody_faceMeasure_eq`.
- `meanMap_faceMeasure_mem_intrinsicInterior`.
- Continuity of the extended mean/law; alternatively the path-endpoint package.

### Care needed

This is the principal conceptual bridge. It must be a **general exposed-face theorem**, not an application of the facet accessibility iff theorem.

No `hT` is required. Uniqueness is ordinary uniqueness of limits in the completion; identifying independently constructed endpoints can also use `completionLaw_injective`.

---

## 4. `FiniteRangeAllFacesAccessible`

**Deliverable:** accessibility is automatic for every nonempty face.

### Statements

1. `face_accessible_of_finiteRange`:
   \[
   \forall F\text{ a nonempty face of }P,\quad
   F\text{ is accessible}.
   \]

2. `exists_meanExt_eq_of_mem_face_intrinsicInterior_finiteRange`:
   \[
   m\in\operatorname{ri}(F)
   \Longrightarrow
   \exists \xi\in\widehat W,\quad \operatorname{meanExt}(\xi)=m.
   \]

3. `meanExt_surjective_of_finiteRange`:
   \[
   \forall m\in P,\quad
   \exists\xi\in\widehat W,\quad\operatorname{meanExt}(\xi)=m.
   \]

Together with `meanExt_injective`, the last theorem gives a bijection with \(P\).

### Dependencies

- Modules 1–3.
- `exists_meanExt_eq_of_mem_ri_face`.
- `exists_meanExt_eq_faceFamily`, where useful.
- The decomposition of a polytope into relative interiors of its nonempty faces.
- `meanExt_injective`.

### Routine versus substantive

Once module 3 exists, this is routine assembly. One ray endpoint in \(\operatorname{ri}(F)\) suffices; the existing propagation theorem supplies all of \(\operatorname{ri}(F)\).

---

## 5. `FiniteRangeFaceIncidence`

**Deliverable:** prove the exact closure relation, not merely one inclusion.

Write \(X_F\) for `faceStratum F`.

### Statements

For every nonempty face \(F\),
\[
\boxed{\;
\overline{X_F}
 =\operatorname{meanExt}^{-1}(F)
 =\bigcup_{\substack{E\text{ nonempty face}\\E\subseteq F}}X_E.
\;}
\]

Consequently, for nonempty faces \(E,F\),
\[
\boxed{\quad
X_E\subseteq\overline{X_F}
\iff E\subseteq F.
\quad}
\]

### Proof structure

**Upper inclusion:** continuity of `meanExt` and closedness of \(F\).

**Lower inclusion:** apply module 4 inside the face model \(F\). Every subface \(E\subseteq F\) is accessible in that model. Its endpoint is a limit of interior face-family points. Map that convergence into the ambient completion using `faceEmbedExt`; identify the image with the desired ambient point using compatibility of means/laws and ambient injectivity.

### Dependencies

- `finiteRange_faceMeasure`.
- `faceMeasure_charged`.
- Module 4 applied recursively to face models.
- `faceStratum_eq_range`.
- The continuous extension `faceEmbedExt` and its mean/law compatibility.
- `meanExt_injective` or `completionLaw_injective`.

**Inventory check:** continuity and endpoint compatibility of `faceEmbedExt` are the precise declarations to locate before beginning this module. If not already exported, prove them here. Injectivity alone is insufficient.

### Care needed

The lower inclusion is **not** a consequence of tilt transitivity alone. Tilts move within a stratum. One needs a convergent degeneration inside the face model and a continuous map of its completion into the ambient completion.

---

## 6. `FiniteRangeCompletionAtlas`

**Deliverable:** the unconditional, incident face atlas and its completed-law interpretation.

### Statements

1. `iUnion_all_nonempty_faceStratum`:
   \[
   \widehat W
     =\bigcup_{F\text{ nonempty face of }P}X_F.
   \]

2. `pairwise_disjoint_faceStratum`:
   distinct nonempty faces have disjoint strata.

3. `faceStratum_eq_range_finiteRange`:
   \[
   X_F=\operatorname{range}(j_F)
      =\{\xi:\operatorname{meanExt}(\xi)\in\operatorname{ri}(F)\}.
   \]

4. `completionLaw_range_eq_extendedFamily`:
   \[
   \operatorname{range}(\operatorname{completionLaw})
      =\bigcup_{F\text{ nonempty face}}
         \{\text{ambient face-family laws on }F\}.
   \]
   With `completionLaw_injective`, this is a bijective parametrisation.

5. Package the face-incidence order theorem from module 5.

### Dependencies

- `iUnion_faceStratum`.
- `faceStratum_eq_range`.
- Modules 4–5.
- `completionLaw_injective`.
- Existing face-embedding law compatibility.

### Scope restraint

Do **not** silently strengthen the continuous bijection
\[
\operatorname{meanExt}:\widehat W\longrightarrow P
\]
to a homeomorphism. The above results alone do not establish continuity of its inverse or compactness of \(\widehat W\). That stronger theorem may be true here, but needs a separate argument.

Likewise, a vertex stratum corresponds to the law on the **statistic fibre** over that vertex. It need not be a Dirac law on the original sample space.

### Dependency order

\[
\texttt{FiniteRangeFaceGeometry}
\to\texttt{FiniteRangeRayDecay}
\to\texttt{ExposedFaceRayEndpoint}
\to\texttt{FiniteRangeAllFacesAccessible}
\to\texttt{FiniteRangeFaceIncidence}
\to\texttt{FiniteRangeCompletionAtlas}.
\]

The endpoint module can later be moved earlier in the library because its abstract theorem does not require finite range.

---

# Q3. General exposed faces and the cleanest route

**Yes: (ii) is true for general exposed faces under the stated finite-range charged-polytope hypotheses. Codimension is not an obstruction.**

The decisive facts are:

1. The exposing statistic is constant on the face.
2. Therefore conditioning the ray law on the face removes the entire ray factor:
   \[
   P_{\theta-tu}(\cdot\mid S\in F)=P^F_{\theta|F}.
   \]
3. Off-face mass tends to zero.
4. Hence the ray law converges to that face-family law.
5. Its mean belongs to \(\operatorname{ri}(F)\).
6. The finite support gap makes the ray Fisher-Cauchy, so this law limit is realised by a completion point.

Indeed, under the usual probability normalisation, total-variation distance from the ray law to its face-conditional law is exactly the off-face mass. Thus the law identification is especially direct.

### Recommended route

**Use the ray directly for endpoint existence and identification. Use tilt propagation afterwards.**

This separates the arguments cleanly:

- finite length gives a metric endpoint;
- conditional-law concentration identifies it;
- `momentBody_faceMeasure_eq` and `meanMap_faceMeasure_mem_intrinsicInterior` locate its mean;
- `exists_meanExt_eq_of_mem_ri_face` fills the stratum.

The path-endpoint route is also valid **if** the existing path API accepts this normal ray after reparameterisation. Then `tendsto_pathEndpoint` and `completionLaw_pathEndpoint_eq` can discharge the completion-identification bookkeeping. But introducing a special admissible path merely to reuse those names could be more work than the direct ray argument. The path theorem does not replace the central calculation that the limiting law is the conditional face law.

### Role of `hT`

`hT` expresses that the face tangent space is the codimension-one hyperplane \(W\cap u^\perp\). For higher-codimension faces,
\[
T_F\subsetneq W\cap u^\perp
\]
can occur. Thus one cannot use the facet iff theorem unchanged.

This is a limitation of that theorem’s hypotheses, **not a failure of normal rays to reach higher-codimension faces**. A vector in the relative interior of a face’s normal cone exposes the entire face, and the finite-gap proof works in every codimension.

`NormalConeCauchyCoalescence` is valuable for comparing different normal-cone constructions, but is unnecessary for the existence proof above.

---

# B, queued next: the six-module shape

There is a clean connection theorem, with one essential qualification.

Use sign-neutral natural coordinates \(\eta\), defined by
\[
\log q_\eta=\langle\eta,S\rangle-\psi(\eta)+\text{base term}.
\]
Translate to the seabed’s \(\theta\) by its sign convention. Work on the effective statistic space, where
\[
C_q=\operatorname{Cov}_q(S,S)
\]
is invertible. For a bounded exponential data-chart direction \(h\), put
\[
a_h=C_q^{-1}\operatorname{Cov}_\rho(S,h).
\]

Then, for fixed chart directions \(h,k\),
\[
D^2\eta_\rho[h,k]
=C_q^{-1}\!\left(
 \kappa_\rho(S,h,k)
 -\kappa_q(S,\langle a_h,S\rangle,\langle a_k,S\rangle)
\right).
\]

The six modules should be:

| Module | Deliverable |
|---|---|
| `ResponseCumulantCalculus` | Differentiate covariance/Fisher operators and establish the required third- and fourth-cumulant identities. |
| `ResponseHessian` | Prove the displayed Hessian formula by twice differentiating moment matching. |
| `ResponseMixtureAffine` | In mean coordinates, the response preserves mixture interpolation and has zero mixture covariant Hessian. |
| `ResponseExponentialDefect` | Identify \(\nabla d\Phi\) for the source and target exponential connections with the cumulant defect above. |
| `ResponseFisherCurvature` | Establish the natural-coordinate Levi-Civita formulas and Fisher curvature from third cumulants; distinguish this from e/m flatness. |
| `ResponseHigherDefectVariation` | Use the preceding calculus and `ResponseDefectEvolution` to derive third and, under sufficient regularity, fourth initial defect derivatives and differentiated pull-back identities. |

The precise mixture statement is
\[
(\nabla^{m,\mathrm{target}}d\Phi)
-d\Phi\circ\nabla^{m,\mathrm{source}}=0,
\]
interpreted as the usual covariant Hessian of a map.

For the exponential connections, the analogous tensor is the explicit Hessian defect above. **It generally does not define a connection on the response space obtained by pushing forward the data connection:** different source lifts of the same response velocity can give different defects.

That distinction is worth formalising explicitly; it prevents an attractive but false “connection descends through response” theorem.

---

## Single ranked list of what to formalise next

1. **A — the six finite-range accessibility/incidence modules**, beginning with support-gap geometry.
2. **B — second-order response calculus and the e/m covariant-Hessian theorem.**
3. **C(2) — parameterised response families and coherent boundary specialisation.**
4. **C(4) — sharp normal-cone boundary asymptotics and uniform gap estimates.**
5. **C(1) — global topological quotient, then a genuinely smooth fibre theorem.**
6. **C(3) — two-sided statistical resolution, only after proving a concrete separation lower bound.**