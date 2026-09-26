**Yes—the recovery argument is sound. But I would simplify its dependency graph: the exposed-chain theorem plus Pythagoras can replace the minimal-face/Csiszár part of step 2.** Build recovery at the density level, not with signed measures.

There are also two important corrections:

* The exposing-hyperplane description of a face preimage is generally an **a.e. equality**, not a pointwise equality.
* Under your charged-vertex hypotheses, the completed projection densities actually admit a **uniform global bound**. That bound is useful, but unnecessary for the first completion proof.

Throughout, retain the existing finite-dimensional, measurability, bounded-feature, and probability hypotheses.

## 1. Recommended decomposition

### A. Vertex witnesses

Your step 1 is right. Use the subtype of the finset consistently:

```lean
abbrev Vertex := {v // v ∈ V}
```

Define a nonnegative real density first:
\[
h_a(x)=\sum_{v:\mathrm{Vertex}}
       a_v\,\frac{\mathbf1_{\{S=v\}}(x)}{\nu.real\{S=v\}}.
\]

Then define the measure using `MeasureTheory.Measure.withDensity` and `ENNReal.ofReal`. Establish:

```lean
vertexDensity_nonneg
integral_vertexDensity
integral_statPoint_mul_vertexDensity
vertexDensity_le
vertexLaw_klDiv_ne_top
genRate_ne_top_of_mem_polytope
```

For simplex weights, a convenient bound is
\[
h_a\le C_V:=\sum_{v:\mathrm{Vertex}}\frac1{\nu.real\{S=v\}}.
\]
It is deliberately coarse and easy to formalize.

For finite KL, boundedness of the density and finiteness of `ν` suffice: use the continuous extension
\[
\psi(r)=r\log r,\qquad \psi(0)=0.
\]
Do not attempt to bound `log h_a` itself; it need not be bounded below. If using `klDiv_ne_top_iff`, its log-likelihood integrability should be proved **under the new measure**, via integrability of \(h_a\log h_a\) under `ν`.

Package the finite convex-hull characterization in a local lemma:

```lean
mem_polytope_iff_exists_vertexWeights :
  M ∈ P ↔ ∃ a, a ∈ stdSimplex ℝ Vertex ∧
    ∑ v, a v • (v : J → ℝ) = M
```

This isolates the finset/subtype coercion work.

### B. Continuous vertex section—and a separate domination lemma

The finite completion gives precisely the continuous simplex-valued section you need. **Do not make its Csiszár support theorem a dependency of recovery.**

Instead, prove this reusable lemma:

> If \(q=q_M\), and \(r\) is a feasible probability law with bounded density and finite KL relative to `ν`, then there exists \(\delta>0\) such that
> \[
> \delta r\le q.
> \]

Here is how your existing seabed proves it.

1. An exposed-chain representation gives a measurable set \(A\), with \(\nu(A)>0\), and
   \[
   q=f\,\nu,\qquad
   c\,\mathbf1_A\le f\le C\,\mathbf1_A
   \quad\text{a.e.}
   \]
   for some \(0<c\le C<\infty\). This is just boundedness of the exponential tilt on the conditioned law. The `dirSpan` condition is irrelevant to these bounds.

2. Pythagoras and finite \(\mathrm{KL}(r\|\nu)\) give
   \[
   \mathrm{KL}(r\|q)<\infty,
   \]
   hence \(r\ll q\). Therefore \(r(A^c)=0\).

3. If \(dr/d\nu\le H\), then
   \[
   r\le H\,\nu|_A,\qquad q\ge c\,\nu|_A.
   \]
   Choosing, for example, \(\delta=c/(H+1)\) gives the claim.

Apply this to \(r=\operatorname{vertexLaw}(a(M))\).

A density-level Lean statement is likely easier than a measure-order statement:

```lean
exists_pos_mul_vertexDensity_le_projectionDensity :
  ∃ δ : ℝ, 0 < δ ∧
    ∀ᵐ x ∂ν, δ * vertexDensity (a M) x ≤ projectionDensity M x
```

You will also want a bounded representative of `projectionDensity M`, obtained from the chain representation.

**This avoids proving that the chain terminal set is the entire minimal-face preimage.**

### C. Recovery densities

For a fixed limit point \(M\), choose a bounded representative \(f\) of \(dq_M/d\nu\), and define
\[
f_N=f+h_{a(N)}-h_{a(M)}.
\]

Use this as a real measurable function first. Prove eventual nonnegativity before making it a probability measure.

Suppose \(\delta h_{a(M)}\le f\), reducing \(\delta\) so that \(\delta\le1\). Continuity of the section and finiteness of `Vertex` give, eventually, for every vertex,
\[
a_v(N)-a_v(M)\ge-\delta a_v(M).
\]
Indeed:

* if \(a_v(M)=0\), this follows from \(a_v(N)\ge0\);
* if \(a_v(M)>0\), it follows from convergence.

Summing,
\[
f_N\ge f-\delta h_{a(M)}\ge0.
\]

The mass and moment calculations are then linear identities. No signed-measure API is needed.

Moreover,
\[
|f_N-f|
\le
\sum_v\frac{|a_v(N)-a_v(M)|}{\nu.real\{S=v\}}
\quad\text{a.e.},
\]
and the right-hand side tends to zero. This scalar estimate can replace formal `L∞` convergence entirely.

### D. Rate continuity, then `L¹` completion

Your proposed arguments are correct:

* recovery gives upper semicontinuity of the rate;
* existing lower semicontinuity gives continuity;
* Pythagoras between the recovery law and the projection at the moving mean, followed by Pinsker, gives `L¹` continuity.

Prefer one reusable recovery theorem packaging:

```lean
-- Schematic: convergence within P, or a sequence in P.
∃ b,
  (eventually probability/feasible at the moving mean) ∧
  Tendsto (fun i => density bᵢ) l (𝓝 (reconstructionL1 hS ν M)) ∧
  Tendsto (fun i => klDiv bᵢ ν) l (𝓝 (genRate ν S M))
```

For the final topology statements, work on the subtype `P`. Continuity there avoids repeated `ContinuousOn` membership bookkeeping.

## 2. Answers to the specific concerns

### (a) Lower bounds on the minimal face

Yes, your geometric route works, but it needs one additional identification:

\[
\operatorname{momentBody}(\operatorname{faceMeasure}\nu\{S\in F\})=F.
\]

The inclusion into \(F\) uses conditioning; the reverse inclusion uses the charged generators in \(F\). Then \(M\in\operatorname{relint}F_M\) lets you apply the interior tilt theorem directly.

For an exposing functional,
\[
F=P\cap\{y:u\cdot y=\beta\},
\]
so
\[
\{S\in F\}=\{u\cdot S=\beta\}
\quad \nu\text{-a.e.},
\]
using \(S\in P\) a.e. Not necessarily pointwise. Handle \(F=P\) separately if your exposed-face definition requires a proper face.

**An arbitrary exposed-chain representation alone does not immediately identify its terminal set with this particular preimage.** It does suffice for the domination argument above.

### (b) Is the support equivalence needed?

No.

With the geometric route, only
\[
a_v(M)>0\Longrightarrow v\in F_M
\]
is needed—not the converse. That implication already follows from the barycenter equation and the face property.

With the domination route, neither direction of Csiszár is needed. You need only simplex membership, the barycenter equation, and continuity.

### (c) Entropy convergence

Your uniform-density argument is the cleanest first implementation.

Eventually \(0\le f_N,f\le C\), and the displayed scalar bound gives uniform essential convergence. Uniform continuity of \(\psi(r)=r\log r\) on \([0,C]\) yields convergence of the integrals.

Alternatively, for sequences, use
`MeasureTheory.tendsto_integral_of_dominated_convergence`, with a constant bound on \(|\psi(f_N)|\). Treat the eventual tail rather than forcing every early \(f_N\) to be nonnegative.

A convexity proof is possible by writing
\[
b_N=(1-\varepsilon_N)q_M+\varepsilon_N r_N
\]
with uniformly bounded-entropy \(r_N\), but constructing \(r_N\) adds positivity bookkeeping. I would not choose it first.

### (d) Pinsker and absolute continuity

Your argument is exactly right. Pythagoras and finite entropy imply finite \(\mathrm{KL}(b_N\|q_N)\), hence absolute continuity.

Be careful with `ℝ≥0∞` subtraction: do not begin by rewriting KL as a difference. First establish all finiteness statements, then pass to real values and use the additive Pythagorean identity.

Observable convergence plus uniform integrability does **not** imply `L¹` convergence in general. Pinsker is the better route.

However, your parenthetical claim about density bounds is false under these hypotheses. Put
\[
p_*=\min_{v\in V}\nu.real\{S=v\}>0.
\]
On a face \(F\), a face tilt has density
\[
\frac{\mathbf1_{\{S\in F\}}e^{\theta\cdot S}}
     {\int_{\{S\in F\}}e^{\theta\cdot S}\,d\nu}.
\]
Its numerator is at most \(\max_{v\in V\cap F}e^{\theta\cdot v}\), while its denominator is at least \(p_*\) times that maximum. Thus
\[
\frac{dq_M}{d\nu}\le p_*^{-1}
\quad\text{a.e., uniformly in }M\in P.
\]
This is a beautiful later corollary; it does not eliminate the recovery argument.

## 3. Hardest lemma and module count

The hardest new lemma is the **local entropy recovery theorem**, especially its eventual positivity and representative bookkeeping—not compactness or homeomorphism.

I would use **five modules**, splitting the last if necessary:

1. `PolyhedralVertexWitness`
2. `PolyhedralVertexSection`
3. `ProjectionDensityBounds` — chain-based bounds and domination
4. `PolyhedralRecovery` — recovery plus rate continuity
5. `PolyhedralCompletion` — `L¹` continuity, homeomorphism, closure, retraction

A sixth `PolyhedralFaceGeometry` module can hold the minimal-face identification and the uniform global bound without blocking completion.

For APIs: use your supplied `klDiv_ne_top_iff`, Pythagorean and Pinsker results, and `EmpiricalTotalVariation`. For convexity, `convexHull_min`, `convexHull_mono`, and `Convex.sum_mem` are useful stable primitives. Wrap the finite barycentric characterization locally rather than spreading dependence on the precise finset convex-hull theorem spelling throughout the development. Your project’s KL/Pinsker names should remain the authoritative ones; I would not guess additional Mathlib identifiers here.

## 4. Facewise geometry: what to build first?

### Face membership versus mass one

For every feasible probability law \(\rho\), not just the projection,
\[
M\in F\iff \rho\{S\in F\}=1.
\]
For an exposed face, this follows by integrating the nonnegative gap
\(\beta-u\cdot S\). This is a small, useful standalone lemma.

Build it early **only if following the minimal-face route**. Recovery via domination does not need it.

### Facewise Fisher identity

Conceptually immediate after identifying the conditioned moment body with \(F\):

* apply the interior Fisher theorem to `faceMeasure ν {S ∈ F}`;
* restrict to its intrinsic direction space;
* the additive constant in `genRate_face_eq` disappears under differentiation.

The work is in identifying direction spaces and expressing the covariance inverse on the correct subtype. This is not a prerequisite for completion.

### Boundary-ray formula

This is nearly free algebra. For a fixed base weight \(e^h\), set
\[
A=\int_{\{S\in F\}}e^h\,d\nu,\qquad
B_t=\int_{\{S\notin F\}}e^h e^{-t(\beta-u\cdot S)}\,d\nu.
\]
The ray law is a mixture of the fixed face law and an outside law with disjoint supports, hence
\[
\|q_t-q_F\|_1=\frac{2B_t}{A+B_t}.
\]

Dominated convergence gives \(B_t\to0\). **Do not claim exponential decay without a positive gap away from the face**: polyhedrality of the moment body does not supply such a gap for general \(X\).

## 5. Best completion statement

Use the ambient space of **all probability densities in `L¹(ν)`**:
\[
\mathcal D_\nu=\{f\in L^1(\nu):f\ge0\text{ a.e.},\ \int f\,d\nu=1\}.
\]

Bounded features make the mean map continuous, and every such mean lies in \(P\). Define
\[
R(f)=\operatorname{reconstructionL1}(\operatorname{mean}f),\qquad
H(t,f)=(1-t)f+tR(f).
\]

This is a **mean-preserving strong deformation retraction** onto the compact completed family. No bounded-density or finite-entropy restriction on the ambient law is needed.

The completed family is homeomorphic to \(P\), with inverse the mean map. Density of the relative interior of \(P\), together with continuity, gives the closure-of-interior-family statement.

The push-forward viewpoint is elegant, but I would not refactor through it now. It requires transport of KL, reconstruction, and `L¹` pullback identities that your direct general-`X` seabed already lets you avoid.