**Given your existing transport certificate, I would use (A), but prove the pointwise identity first for continuous test functions, then upgrade it to an equality of fibre measures.** That gives the bounded-measurable version without asserting continuity for measurable integrands.

Route (B) is a good reusable alternative, especially if you expect other fibrewise change-of-variables results. Its essential new lemma is Euclidean, not manifold-theoretic.

Two preliminary points matter:

- The partition weights naturally live **upstairs**: write
  \[
  w_i(u)=\rho_i(\phi_i^{-1}u).
  \]
  They are not initially functions on the base.
- Arrange that these weights have compact support **inside the boxes on which transport is certified**. If `exists_resolutionChartData` produces a smaller box than the atlas core, shrinking the box does not preserve the cover automatically. Either obtain transport on the original boxes, or choose the certified boxes before taking the finite subcover and constructing the partition.

Below, \(k\) denotes a chart’s solve index; \(\ell\) remains the truth-coordinate index.

## 1. Route (A): what I would actually formalise

### A1. Assemble a weighted total-space identity

Choose nonnegative continuous—smooth if convenient—weights \(\rho_i\) upstairs such that:

- `tsupport ρ_i` lies in the corresponding certified core;
- their sum is one over the preimage of the physical region under consideration.

For a compact physical set \(K\), it is convenient to arrange this over a slightly larger horizontal neighbourhood and a small parameter interval, not just over \(K\times\{0\}\). Properness and the open cover of the compact wall preimage provide such a neighbourhood.

The resulting identity should have the form
\[
\int \Psi(y)\,dy
 =
 \sum_i\int w_i(u)\Psi(\operatorname{rep}_i u)
                |\det D\operatorname{rep}_i(u)|\,du,
\]
for tests supported in that physical neighbourhood.

Your `TransportsToOn` certificate supplies the chart-level measure transport. One still needs the assembly argument:

1. off the exceptional locus, the resolution has a unique inverse;
2. on that locus, total-space volume is zero;
3. the upstairs partition sums to one.

The weighted version of an unweighted transport certificate deserves its own helper lemma. For weights depending on \(u\), it uses the inverse on the injective regular part; it is not merely substitution of a target test function into the certificate.

**Mathlib infrastructure:** `Measure.map`, `Measure.withDensity`, lintegral transport, finite-sum lintegral/integral lemmas, and `PartitionOfUnity`. I would package the resulting identity as a measure identity before doing calculus.

### A2. Split coordinates, then substitute on two half-lines

Use a fixed coordinate permutation giving
\[
\mathbb R^n \simeq \mathbb R^{n-1}\times\mathbb R,
\qquad u=(w,v),
\]
with \(v=u_k\).

In Lean, this coordinate-splitting infrastructure is worth isolating. A type such as
```lean
{j : Fin n // j ≠ k}
```
is natural for the remaining coordinates; export to `Fin d → ℝ` through a chosen equivalence if laplace requires that type.

For fixed \(w\), put
\[
c(w)=S\prod_{j\ne k}w_j^{q_j}.
\]
On \(v>0\) and \(v<0\), substitute
\[
s=c(w)v^{q_k}.
\]
For \(c(w)\ne0\), each half-line map is a \(C^1\) diffeomorphism onto one half-line, and
\[
\left|\frac{ds}{dv}\right|=q_k\frac{|s|}{|v|}.
\]

The exceptional set \(c(w)=0\) is a finite union of coordinate hyperplanes for indices with \(q_j>0\), hence null. Prove this once and discard it using an a.e. congruence.

**Mathlib infrastructure:**

- `MeasureTheory.lintegral_prod` for the nonnegative proof;
- `MeasureTheory.integral_prod` for the integrable signed proof;
- `integral_image_eq_integral_abs_det_fderiv_smul` for substitution, including the one-dimensional case;
- `MeasureTheory.lintegral_congr_ae` / `MeasureTheory.integral_congr_ae`.

The exact one-dimensional interval-substitution lemma you might prefer depends on the formulation—there are several variants in the interval-integral API. Using the general change-of-variables theorem avoids depending on a particularly convenient half-line variant.

I would prove the substitution helper at the **measure/lintegral level**, rather than repeatedly establish Bochner integrability. If the available image-integral theorem is used to derive it, do that conversion once.

### A3. Obtain a.e. equality in the parameter

Test with
\[
\Psi(x,s)=f(x)\eta(s),
\]
including any fixed physical cutoff required by the coverage region.

After the substitution,
\[
\int \eta(s)L_f(s)\,ds=\int\eta(s)R_f(s)\,ds.
\]
Equality for all measurable parameter sets, or equivalently equality of the corresponding locally finite measures on the parameter interval, gives
\[
L_f(s)=R_f(s)\quad\text{a.e.}
\]

You do not need a bespoke distribution-theory argument. Equality of measures with densities is a clean route. There are also “equality of all set integrals implies a.e. equality” lemmas; I would check their exact names and hypotheses in the pinned Mathlib revision rather than build around a guessed name.

### A4. Upgrade for continuous tests, then identify measures

For each fixed continuous compactly supported \(f\):

1. prove \(R_f\) continuous on the punctured parameter interval;
2. \(L_f\) is continuous there;
3. continuous functions equal a.e. for Lebesgue measure are equal everywhere.

The last step can be proved directly: if the values differ at a point, continuity gives a nonempty open neighbourhood where they differ, contradicting a.e. equality. Mathlib’s open-positive-measure infrastructure supports this; I would not make the proof depend on a particular extensionality lemma name.

Now fix **any** nonzero small \(s\). Equality for all compactly supported continuous tests identifies the locally finite fibre measures. Restrict that measure equality to \(K\), then integrate arbitrary nonnegative measurable or bounded measurable functions.

This order is important:
\[
\boxed{\text{continuous tests}\;\to\;\text{pointwise in }s
       \;\to\;\text{measure equality}\;\to\;\text{measurable tests}.}
\]
It avoids needing a common a.e. exceptional set for uncountably many test functions.

## 2. The continuity issue is manageable—and local away from zero

Fix \(s_0\ne0\), and restrict \(s\) to a small neighbourhood where
\[
0<a\le |s|\le A.
\]

Suppose the upstairs weight is supported in a compact box with coordinate bounds \(R_j>0\). Wherever the solved integrand is nonzero,
\[
|s|=\prod_j|u_j|^{q_j}.
\]
Consequently, for every \(j\) with \(q_j>0\),
\[
|u_j|
\ge
\left(\frac{a}{\prod_{m\ne j}R_m^{q_m}}\right)^{1/q_j}.
\]

This is the key estimate.

### Why the apparently singular powers are harmless here

Write
\[
\alpha=\frac{h_k+1}{q_k},
\qquad
r_j=h_j-q_j\alpha.
\]

- If \(q_j>0\), the coordinate is uniformly bounded away from zero on the effective support.
- If \(q_j=0\), then \(r_j=h_j\ge0\), so there is no negative-power singularity at zero.
- \(|s|^{\alpha-1}\) is bounded and continuous near \(s_0\).
- The unit and partition weight are bounded on a fixed compact set.

Thus the integrands admit a majorant
\[
C\,1_B(w)
\]
for one fixed bounded box \(B\subset\mathbb R^d\).

### Moving domains

Do **not** try to prove continuity of the raw indicator \(1_{D(s)}\). Instead prove continuity of the **weighted zero extension**
\[
H(s,w)=
\begin{cases}
w_i(u(s,w))\,f(X_i(s,w))\,D_{i,s}(w),&w\in D(s),\\
0,&\text{otherwise}.
\end{cases}
\]

The proof has three parts:

- inside the solved domain, the graph map and density are continuous;
- at a box boundary, the partition weight vanishes on a neighbourhood, because its support is compactly contained in the box;
- near a coordinate zero with \(q_j>0\), the effective support is absent, by the lower bound above.

Then dominated convergence gives continuity of the integral. The relevant Mathlib lemma is `MeasureTheory.tendsto_integral_filter_of_dominated_convergence`; its precise filter hypotheses should be checked in your version. A dedicated continuity-under-the-integral wrapper may also be available.

**No uniform majorant as \(s\to0\) is required here.** That is a separate laplace problem.

### The indicator of physical \(K\)

For arbitrary measurable \(K\), the factor \(1_K(X_i(s,w))\) need not vary continuously. Likewise for bounded measurable \(\psi\).

So omit these during the continuity proof. Establish the fibre-measure identity using continuous tests on a neighbourhood, and then restrict the measures to \(K\).

### Disintegration does not remove this issue

Ordinary measurable disintegration determines conditional measures only **a.e. in \(s\)**. Measurable dependence alone cannot give the prescribed formula at every parameter.

Nor does restricting an equality of total-space Lebesgue measures to
\(\mathbb R^d\times\{s\}\) help: both restrictions are zero.

A theorem giving your particular fibre kernel at every \(s\) would need extra pointwise structure—continuity, a submersion/coarea theorem with pointwise hypotheses, or direct fibrewise change of variables. It would not be a cheaper consequence of disintegration.

## 3. Route (B): isolate one Euclidean determinant lemma

The useful reusable theorem is:

> Let \(R(w,v)=(X(w,v),T(w,v))\) be \(C^1\). Suppose \(v=V(w)\) is \(C^1\), \(T(w,V(w))=s\), and \(\partial_vT\ne0\). Then
> \[
> |\det D(w\mapsto X(w,V(w)))|
> =
> \frac{|\det DR(w,V(w))|}{|\partial_vT(w,V(w))|}.
> \]

### A determinant proof avoiding matrix inverses

Write
\[
DR=\begin{pmatrix}A&b\\c&d\end{pmatrix}.
\]
Differentiating the constant-truth identity gives
\[
c+d\,DV=0.
\]
Multiply by the shear:
\[
\begin{pmatrix}A&b\\c&d\end{pmatrix}
\begin{pmatrix}I&0\\DV&1\end{pmatrix}
=
\begin{pmatrix}A+bDV&b\\0&d\end{pmatrix}.
\]
The shear has determinant one, so
\[
\det DR=\det(A+bDV)\,d.
\]

This is generally easier than a Schur-complement theorem with inverse matrices.

**Mathlib pieces:** `HasFDerivAt.comp`, `Matrix.det_mul`, and block-triangular determinant lemmas for `Matrix.fromBlocks`. I am not certain of the exact block-triangular lemma names in your revision. Coordinate ordering contributes only a sign, removed by absolute values.

Since \(V\) is explicit, you do not need to invoke the implicit function theorem.

### Fibrewise null sets

For \(s\ne0\), all coordinates with \(q_j>0\) are nonzero. Therefore the Jacobian-zero set on a solved graph is contained in
\[
\bigcup_{\substack{j\ne k\\q_j=0,\ h_j>0}}\{w_j=0\}.
\]
It is null in \(\mathbb R^d\).

On its complement, chart-level injectivity follows from your `rep` injectivity on `{det ≠ 0}`.

To discard its **image**, use that the fibre map is \(C^1\), hence locally Lipschitz, and locally Lipschitz maps between equal-dimensional Euclidean spaces preserve null sets. Cover by countably many relatively compact pieces if needed. Mathlib has Lipschitz null-image infrastructure, but I would check the exact local-to-global lemma rather than assume a ready-made `ContDiffOn` version.

A total-space null-image statement is not enough: slicing an \(n\)-dimensional null set gives only an a.e. assertion about slices.

### Overlaps and the manifold

Across different charts, you need uniqueness of a **regular** preimage. This follows from generic injectivity:

- two distinct regular preimages give disjoint neighbourhoods mapped diffeomorphically to overlapping base neighbourhoods;
- their overlap meets the dense isomorphism locus;
- this contradicts uniqueness there.

This is worth exporting as a certificate. The cover then gives coverage of the fibre, except for the fibrewise critical images just shown null. Sum the upstairs partition weights at the unique regular preimage.

An alternative using “\(\{F(\cdot,s)=0\}\) is null” requires proving that \(F(\cdot,s)\) is not identically zero for every relevant \(s\). Do not silently infer that from total-space nontriviality.

**Verdict on friction:** (B) replaces dominated continuity and measure determination by a determinant lemma, local Lipschitz null-image arguments, and regular-preimage uniqueness. With your current toolkit, (A) probably wins; once those Euclidean helpers exist, (B) is quite direct.

## 4. Export a fixed-domain kernel to laplace

For each chart and branch, export:

- a total graph-lift function `lift i σ s w`;
- the horizontal output `X i σ s w`;
- a measurable solved domain `D i σ s`;
- the upstairs weight evaluated on the lift;
- the explicit density.

Define the weighted density piecewise:
\[
J_{i,\sigma}(s,w)=
\begin{cases}
\displaystyle
w_i(u)\frac{|b_i(u)|}{q_{i,k}}\,
|s|^{\alpha_i-1}
\prod_{j\ne k}|w_j|^{\,h_{i,j}-q_{i,j}\alpha_i},
& w\in D_{i,\sigma}(s),\\
0,&\text{otherwise},
\end{cases}
\]
where
\[
u=\operatorname{lift}_{i,\sigma}(s,w),
\qquad
\alpha_i=\frac{h_{i,k}+1}{q_{i,k}}.
\]

Here \(|b_i(u)|\) appears **once**.

The consumer-facing integral identity is
\[
\int_K\psi(x)\,dx
=
\sum_{i,\sigma}
\int_{\mathbb R^d}
J_{i,\sigma}(s,w)\,
(K.\mathrm{indicator}\,\psi)(X_{i,\sigma}(s,w))\,dw.
\]

Prefer an underlying **measure identity**, localized to the covered physical region:
\[
\operatorname{volume}\!\restriction_K
=
\sum_{i,\sigma}
(X_{i,\sigma}(s,\cdot))_*
\left(
\operatorname{ofReal}(J_{i,\sigma}(s,\cdot))\,
1_{X^{-1}(K)}\,dw
\right).
\]

This gives:

- nonnegative measurable tests without integrability obligations;
- signed tests under explicit integrability hypotheses;
- bounded measurable tests when \(K\) has finite volume.

### Useful auxiliary exports

Laplace should also receive:

1. the exact closed-form identity **on** `D`;
2. zero outside `D`;
3. measurability and nonnegativity;
4. active coordinates are nonzero on `D`;
5. the exact truth identity `T (lift …) = s`;
6. the phase formula and unit bounds.

Use a piecewise/indicator definition rather than relying on Lean’s totalized inverses and `Real.rpow` to behave meaningfully outside the solved domain.

Negative exponents should remain explicit. The identity theorem should not try to prove an \(s\)-uniform envelope: that belongs to sector decomposition and rescaling. Also, partition weights generally have no positive lower bound on their support; lower-bound statements must distinguish the units from the partition weights.

## 5. Branches: use only two solve-coordinate signs initially

The least painful initial design is:

> Keep \(w\in\mathbb R^d\) signed, and sum over only \(\sigma\in\{-1,+1\}\), the sign of the solved coordinate.

Set
\[
V_\sigma(w,s)
=
\sigma
\left(
\frac{|s|}{\prod_{j\ne k}|w_j|^{q_j}}
\right)^{1/q_k}.
\]

Besides box membership and active-coordinate nonvanishing, impose compatibility
\[
s\left(S\,\sigma^{q_k}\prod_{j\ne k}w_j^{q_j}\right)>0.
\]
This avoids substantial `Real.sign` bookkeeping.

- If \(q_k\) is odd, exactly one \(\sigma\) is compatible.
- If \(q_k\) is even, either both or neither are compatible.

Branching only on odd exponents does **not** resolve the sign of the solve coordinate when \(q_k\) is even.

Later, laplace can split the remaining coordinates into orthants if positive-coordinate sector analysis is useful. Do not replace orthants by numerical multiplicities unless symmetry has been proved: the units, partition weights, phase, and physical test function need not be invariant under sign changes.

## 6. Library boundary

I strongly prefer the Euclidean interface you suggest:

### Hironaka layer

Constructs and exports:

- finitely many Euclidean representatives;
- certified boxes;
- monomial identities and unit bounds;
- compactly supported nonnegative weights;
- weighted total-space transport, or the stronger geometric certificates needed for route (B).

### Euclidean fibre-transport layer

Proves:

- coordinate splitting and branch substitution;
- parameter-local domination and continuity;
- pointwise fibre-measure equality;
- explicit fixed-domain integral formulas.

### Laplace layer

Consumes only the explicit kernels, domains, phase identities, and bounds.

For route (A), exporting the **assembled weighted total-space transport identity** is particularly attractive: laplace and the Euclidean fibre theorem need know nothing about manifold partitions, exceptional-set descent, or resolution uniqueness.

**Recommended implementation order:** weighted transport interface → two-branch substitution → continuous compact-test pointwise theorem → fibre-measure equality → explicit indicator-kernel corollary. This reuses your strongest existing result and keeps the delicate manifold bookkeeping out of the asymptotic analysis.