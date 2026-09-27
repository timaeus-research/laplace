## Verdict

**The response-map section is complete at the stated scope.** Round 88 supplies the missing boundary organisation, canonical data journey, and sharp testing conclusion. I would not commission another six-module expansion.

There is, however, **one important final corollary to extract: global mean- and law-injectivity in the charged-polytope setting**, followed by removal of the now-redundant `huniq` assumptions in that setting. Two smaller presentation/coherence results are worth considering alongside it.

This is an audit of the reported theorem statements and their mathematical consequences, not an independent inspection of the Lean files.

## Q1. Audit of round 88

### 1.1 Accessible-face stratification

The claims are correctly scoped. In particular, they do **not** assert that every face is accessible.

Your current theorem is a good *structural* formulation:
\[
\forall x\in\widehat W,\quad
\exists\text{ an exposed-face presentation and a chart }j
\text{ with }\operatorname{range}(j)=\operatorname{stratum}(x).
\]
Together with `stratum_eq_or_disjoint` and `iUnion_stratum = univ`, it proves the advertised partition.

An explicit face-indexed union would be useful as a **public wrapper**, not as missing mathematics. For example, set
\[
X_F:=\{x:\operatorname{meanExt}(x)\in\operatorname{ri}(F)\},
\qquad
\operatorname{Accessible}(F):\Longleftrightarrow X_F\ne\varnothing,
\]
with \(F\) ranging over nonempty faces of the moment polytope. Then state
\[
\widehat W=\bigcup_{F:\,\operatorname{Accessible}(F)}X_F,
\qquad
X_F=\operatorname{range}(j_F).
\]
This formulation separates the choice-free partition from the construction of its charts.

Two qualifications belong in the note:

* This is a **set-theoretic accessible-face stratification**. Do not silently promote it to a frontier-compatible, Whitney, or otherwise smooth stratification.
* `faceChart_eq` removes **seed dependence for the fixed conditioned family**. Calling \(j_F\) canonical *as a chart indexed by the geometric face* also uses the identification of different exposing presentations: under the support hypothesis,
  \[
  \{\langle u,S\rangle=\beta\}=\{S\in F\}\quad \nu\text{-a.e.}
  \]
  Thus their conditioned laws agree, with the induced parameter spaces identified. Seed independence alone should not be cited as proving all presentation independence.

There is no need to burden the main text with the seed. A suitable sentence is: “Accessibility supplies a seed for the construction; the resulting finite chart is independent of that seed.”

### 1.2 Canonical data journey

Yes: **KL monotonicity on \([0,\infty)\) is correct**, and stronger than what the interpolation argument needs. Writing \(h=\log q\),
\[
\frac{d}{dt}D(\rho_t\Vert\nu)=t\,\operatorname{Var}_{\rho_t}(h).
\]
Bounded \(h\) makes the exponential family available for every real \(t\). The derivative is nonnegative for \(t\ge0\), and nonpositive for \(t\le0\); this is not monotonicity on all of \(\mathbb R\).

For the note, distinguish:

* the interpolation statement, \(0\le t\le1\);
* extrapolation beyond the data endpoint, \(t>1\).

The endpoint laws and responses require the stated probability normalisation and positive upper/lower density bounds. The matched-base variance decomposition is also correctly stated.

### 1.3 Absolutely continuous forcing

This is the right strengthening: absolute continuity, rather than a chosen exponential-density representation, ensures that covariance forcing lies in \(W\).

The phrase “every \(D\ll\nu\)” should retain the ambient **probability-law and measurability/integrability hypotheses**. Absolute continuity alone is not a substitute for these. With those conventions understood, there is no overclaim.

### 1.4 Chamber clearance

The implications and constants have the expected direction.

One notation correction is important: in the probability bound, the object tested against a Fisher ball centred at \(\theta(m_D)\) must be the **sample response**, not the raw empirical mean:
\[
\mathbb P\!\left(
 \operatorname{sampleResponse}\notin
 B_F\!\left(\theta(m_D),r/\sqrt\lambda\right)
\right)
\le \frac{\Lambda\,\operatorname{tr}(R C_D)}{nr^2}.
\]
If \(\widehat M\) denotes the empirical mean, the displayed formulation in the summary mixes mean-space and parameter-space objects. The theorem name suggests the formal statement already has the correct object.

These remain conditional, chamber-controlled bounds—not global coercivity or a global response Lipschitz theorem.

### 1.5 Mixture journey

Yes: an integrand defined globally but used only on \([0,1]\) is harmless. The note should write
\[
\theta_t=\theta_r\bigl((1-t)m_\nu+t m_D\bigr),\qquad 0\le t\le1,
\]
and make no assertion about the totalised extension elsewhere.

There is one endpoint subtlety worth checking against the actual definitions:

* If `mixResponse` is the chart evaluated on the **affine mean line**, the stated ordinary derivatives at \(0\) and \(1\) are appropriate. Both endpoint means are interior, so that affine line remains admissible locally.
* If it were instead defined outside \([0,1]\) using the literal `ofReal`-weighted `mixLaw`, the clipped weights would not give that same two-sided derivative at the endpoints.

Your description indicates the first construction. The clamp belongs in the length proof, not in an assertion that the clamped curve has those ordinary endpoint derivatives.

### 1.6 Sharp affinity testing

The constants are right, subject to the hypotheses that should remain visible:

* unit \(L^2\) normalisation of the roots;
* nonnegative roots for probability affinity, hence \(0\le A\le1\);
* \(0\le\varphi\le1\) for the test-function bound;
* independent product sampling;
* `err` meaning **equal-prior average error**, not the sum of the two errors.

In particular, the bound with constant \(\sqrt{1-A^2}\) is for \([0,1]\)-valued tests; arbitrary \([-1,1]\)-valued observables incur the corresponding factor of two.

“Sharp affinity bound” is appropriate. It does not mean that every particular pair of laws attains equality.

## Q2. Coverage of the six-part section

The round-87 theorem names are not reproduced here, so I distinguish that existing foundation from the explicitly named round-88 results.

| Part | Landed results carrying the exposition | Genuine gap? |
|---|---|---|
| **1. Response as projection** | The round-87 projection/moment-matching package; `responseOf_eq_dataTheta`, `journeyResponse_one`, `densResponse_tiltDens` connect it to the actual data response. | **No**, assuming the projection package is presented with its admissibility hypotheses. |
| **2. Infinitesimal geometry** | `CDE`, `responseVel`, `pullbackForm`; `covVec_mem_dirSpan`, `densVel_eq_symm`, `densVel_eq`; `hasDerivAt_journeyResponse`; the matched-base variance decomposition; the existing `deriv_deriv_responseDefect_zero_eq_residual`. | **No.** The canonical-journey defect statement is a useful specialisation, not missing mathematics. |
| **3. Sampling and resolution** | The existing `samplingOp/samplingEnergy` and `sampleResponse` results; `mem_of_fisherClearance`, `frozen_margin_of_euclidean_clearance`, and the clearance-based probability bound. | **No.** Keep the chamber hypotheses explicit and distinguish finite-sample bounds from asymptotic distribution claims. |
| **4. Boundary geometry** | The completion/root-law and face-embedding packages; `momentBody_faceMeasure_eq`; the face-interior singleton-fibre theorem; `range_faceChart`; `faceChart_eq`; `exists_faceChart_range_eq`; the partition theorems. | **One useful closure corollary:** global mean/law injectivity. No gap in the deliberately accessible-face formulation. |
| **5. Journeys through data** | Canonical logarithmic journey: endpoints, velocity, length and KL monotonicity. Mixture journey: relative-interior preservation, endpoints, inverse-covariance velocity and length. | **No.** Comparing their lengths is an extra example, not required structure. |
| **6. What finite samples can see** | Root-density/Hellinger control, `affinityExt_eq`, `affinityExt_ge`, product-affinity testing bounds, and the existing finite-tail theorem. | **No.** The sharp affinity result improves the closing statement rather than opening another obligation. |

### The proposed additions

**Global mean- and law-injectivity: do it.**  
For \(x,y\in\widehat W\) with equal extended means, choose the accessible-face witness supplied by `exists_faceChart_range_eq x`. Both means lie in that conditioned face’s relative interior, so `eq_of_meanExt_eq_of_mem_ri` gives \(x=y\). Thus
\[
\operatorname{meanExt}(x)=\operatorname{meanExt}(y)\Longrightarrow x=y.
\]
The mean–law identity then gives
\[
Q_x=Q_y\Longrightarrow x=y.
\]

No **extra accessibility hypothesis** is needed: the point \(x\) supplies the required witness. This does not show that every mean in the closed polytope is attained.

Use the result to discharge `huniq` **within the charged-polytope specialisations**. Retain explicit uniqueness assumptions in genuinely more general packages. For face-completion results, instantiate the same uniqueness theorem for the conditioned face family as needed.

**Chain compatibility: worth a short coherence theorem, but fix the types.**  
For a proper subface \(E\subseteq F\), the finite \(E\)-chart inside the \(F\)-family normally lands in \(\widehat W_F\), not \(W_F\). Consequently the natural statement is
\[
j_F^{\mathrm{ext}}\circ j_E^F=j_E,
\]
and, at completion level,
\[
j_F^{\mathrm{ext}}\circ (j_E^F)^{\mathrm{ext}}=j_E^{\mathrm{ext}}.
\]
The unextended expression \(j_F\circ j_E^F\) is generally ill-typed. If the stated embedding-composition and conditioning identities make this a short proof, it is a worthwhile capstone. It is not a frontier theorem.

**Canonical initial defect: include as a corollary or displayed equation.**  
Specialise the existing theorem to \(h=\log q\):
\[
\Delta''(0)=\operatorname{Var}_\nu\!\left(\log q-(\log q)_{\mathrm{reg}}\right).
\]
Preserve the existing definition and sign convention for \(\Delta\). This is valuable exposition because it identifies exactly what the initial response discards; it does not justify a new module.

**Per-face accessibility under finite statistic support: decline for this final batch.**  
It is a sound and attractive additional theorem. The correct sufficient hypothesis is that \(S\) has **finite essential range**, not necessarily that the underlying sample space or \(\nu\) has finite support. For a proper exposed face, a positive gap between face and off-face statistic values gives exponential decay of the normal-ray speed and hence finite tail length.

That would yield an all-nonempty-faces theorem in a stronger setting. It is not needed for the current note, and the charged-polytope hypothesis alone should not be described as supplying that uniform gap. Reopen it only if the note specifically promises an all-faces conclusion for finite-range models.

**One-dimensional exponential-versus-mixture length comparison: decline.**  
It is a useful example, but it needs the monotonicity condition explicitly. A one-dimensional response alone does not make an arbitrary exponential data journey monotone: its derivative is governed by a covariance that can change sign. Conditional equality of lengths for monotone paths is not a structural gap.

**Completion-valued journey versions: decline.**  
For these finite-parameter journeys, composing with the canonical isometric embedding \(W\to\widehat W\) transports the metric length statements. New completion-valued differential statements would also require saying what notion of derivative is intended. Neither is needed here.

**Anything else:** only presentation wrappers—especially the explicit accessible-face union and the distinction between empirical means and sample responses. There is no missing seventh mathematical component.

## Q3. The closing statement

Lead with the **exact affinity bound** and give the linearised tail-length bound as its readable consequence. Do not substitute a possibly negative \(1-R(t)^2/8\) into an even power without truncation or a small-tail hypothesis.

I would close the note with this paragraph:

> **Finite samples cannot uniformly resolve a finite-length tail.** Let \(\gamma(t)\) be a response-family curve with finite remaining Fisher length \(R(t)=\int_t^\infty|\dot\gamma(s)|_{F,\gamma(s)}\,ds\), and let \(x_\infty\in\widehat W\) be its completion limit. Put \(A_t=\int\Psi_{\gamma(t)}\Psi_{x_\infty}\,d\nu\). Then \(A_t\ge 1-R(t)^2/8\), and every test distinguishing \(n\) independent observations from \(P_{\gamma(t)}\) against \(Q_{x_\infty}\), with equal prior probabilities, has average error
> \[
> \operatorname{err}_n(t)\ \ge\
> \frac{1-\sqrt{1-A_t^{\,2n}}}{2}
> \ \ge\
> \max\!\left\{0,\frac{1-\sqrt n\,R(t)/2}{2}\right\}.
> \]
> Thus, for fixed \(n\), the optimal error tends to \(1/2\) along the tail; more generally, a fixed positive advantage over random guessing requires sample size at least of order \(R(t)^{-2}\). These are statements about the **response-family laws and their completion limits**, not about arbitrary data laws producing those responses: moment matching does not identify the data law with its fitted response law.

## What to do next — final ranked list

1. **Global injectivity and hypothesis discharge:** prove `meanExt_injective` and `completionLaw_injective` under the charged-polytope hypotheses; instantiate the Hellinger and face-completion packages without external `huniq`.
2. **Boundary presentation and coherence:** add the explicit accessible-face union wrapper and the correctly typed chain-compatibility corollaries, provided they remain short consequences of the existing results.
3. **Canonical defect specialisation, then stop:** expose the \(h=\log q\) second-derivative formula as a small corollary and finish the note with the sharp affinity tail theorem.