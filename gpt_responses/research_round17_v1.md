I would do **both weakenings, but separately**. Removing the observable-support hypothesis is the more important interface change; localising phase nonnegativity is a useful, largely orthogonal change. Neither makes kernels attached to different regions pointwise equal merely because the regions agree near one wall point.

There is also a correction needed in the mixed-sign integrability example in outcome (2).

## 1. The right API weakening

### Phase: local nonnegativity, enforced at the integration domain

The natural hypothesis is
\[
0\le F(z)\qquad(z\in L'),
\]
or, at the chart layer,
\[
0\le F(\operatorname{rep}_i(u))\qquad(u\in\operatorname{dom}_i).
\]

These are interchangeable only once the relevant chart-image inclusion has been supplied. I would expose the region-level hypothesis publicly and derive the chart-level hypothesis internally.

The cheap implementation is **not necessarily** to thread this hypothesis through every existing unweighted lemma. Instead:

1. Give the elementary exponential bound a pointwise hypothesis `0 ≤ F (rep u)`.
2. Prove the bound actually needed for the **domain-indicated integrand**, splitting on `u ∈ dom`.
3. Retain the old global-nonnegativity theorems as wrappers.

This matters if `branchReal_le` is currently invoked at chart points outside `dom`: its old conclusion there need not survive, although the bound for the indicated integrand does.

Also distinguish nonnegativity from boundedness: `modelG_nonneg` may only need positivity of weights and exponentials, not \(F\ge0\). Audit actual uses rather than propagating `hF` uniformly.

**Qualification for the acceptance test:** this permits the linear phase on a one-sided region where \(z_1\ge0\). It does not make \(a z_1\) admissible on the full two-branch region containing negative \(z_1\). The quadratic test remains the right exported test.

### Observable: restrict the measure/integrand, not the observable

The clean formulation is
\[
\int_{L'} \theta(z)e^{-tF(z)}\,d\mu(z),
\]
with \(\theta\) continuous on a neighbourhood of \(\overline{L'}\), and no requirement that its zero extension be continuous.

For the immediate Lean implementation, keep ambient observables and drop `hφL` where possible. A subtype formulation can come later.

In particular, **continuous functions on \(L'\), extended by zero, are not the right replacement**:

- continuity on \(L'\) alone does not supply boundary traces;
- zero extension usually destroys continuity at the boundary;
- the limiting measure can charge that boundary.

If you eventually want a compact-region interface, `C(closure L', ℝ)` is a more suitable test space than `C(L', ℝ)`. But moving to subtypes now is unlikely to be the cheapest refactor.

### Where continuity is genuinely needed

Without the sources, I would audit `tendsto_weightFn` along this factorisation:
\[
w_t(u)
 = 1_{A_t}(u)\,J_t(u)\,\theta(\operatorname{rep}_t(u)).
\]

The ingredients are different:

- `θ (rep_t u) → θ (rep₀ u)` needs continuity **at the limiting chart image**, potentially in \(\partial L'\).
- Convergence of `1_{A_t}` needs a separate geometric argument.
- Domination needs bounds only where the indicated integrand is active.

The dangerous case is a positive-measure set of parameters whose limiting image lies on the physical boundary. Then one cannot infer the indicator limit just from convergence of chart points. Your zero-scale boundary regime is precisely a reason to keep the moving-domain argument explicit.

Thus my recommendation is:

> Keep the chart-domain indicator as geometry; keep the observable as a continuous trace-bearing function. Do not combine them into a continuously zero-extended weight.

## 2. What pointwise chart-independence can honestly say

### Agreement near one wall point is insufficient

There is no theorem of the proposed form for arbitrary bounded continuous \(\theta\).

For example, take \(T(x,y)=xy\), \(\theta=1\), and
\[
L_R=(-R,R)^2.
\]
The push-forward density of area is, for \(0<|s|<R^2\),
\[
K_R(s)=2\log\frac{R^2}{|s|}.
\]
Consequently,
\[
K_{R_2}(s)-K_{R_1}(s)=4\log(R_2/R_1).
\]

Both regions contain a neighbourhood of the same wall point. Their small nonzero fibres nevertheless include different pieces away from that point. The intersections with the square edges are transverse for the small nonzero values under discussion; transversality does not fix the mismatch.

This is **region dependence**, not chart dependence.

### The sharp useful statement

Fix the same weighted measure
\[
\nu_t=1_L\,\theta e^{-tF}\,\mu.
\]

Suppose two chart systems produce densities \(K_1,K_2\) of \(T_*\nu_t\) on an open interval \(I\), and both densities are continuous there. Then
\[
K_1(s)=K_2(s)\qquad(s\in I).
\]

For different regions \(L_1,L_2\), replace “the same weighted measure” by
\[
(T_*\nu_{1,t})|_I=(T_*\nu_{2,t})|_I.
\]
A convenient stronger hypothesis is equality of the weighted restricted measures on \(T^{-1}(I)\).

This formulation separates the two tasks:

1. **Identification:** the chart expressions represent the same push-forward measure.
2. **Version selection:** continuity upgrades a.e. equality to pointwise equality.

A conditional density is otherwise still only an a.e. object. Calling it intrinsic does not choose its value at an exceptional \(s\).

### Cheapest route using your existing tools

You can first prove a pointwise theorem **without weakening any analytic API**.

At a target \(s\), find a truth cutoff \(\chi\) such that:

- \(\chi(s)=1\);
- \(\widetilde\theta=\theta\cdot(\chi\circ T)\) satisfies the existing support hypotheses in both regions;
- both cutoff kernels are continuous at \(s\).

Then:

1. `totalKernel_ae_eq_of_support` gives a.e. equality for \(\widetilde\theta\).
2. Continuity at \(s\), together with full support of Lebesgue measure, gives equality at \(s\).
3. `totalKernel_mul_comp_truth` removes the cutoff because \(\chi(s)=1\).

No continuity theorem for the original unsupported \(\theta\) is needed in this argument.

The substantive geometric condition is that the truth-localised observable fits in the common region:
\[
\operatorname{supp}\theta
\cap T^{-1}(\operatorname{supp}\chi)
\subseteq L_1\cap L_2.
\]
Containment of a neighbourhood of one wall point does not imply this.

For an eventual support-free theory, prove continuity on regular-value intervals under an appropriate properness/domination hypothesis and suitable control of boundary crossings. **Boundary transversality is one sufficient geometric package, not the underlying uniqueness principle.** I would implement continuous-version uniqueness first and add geometric continuity theorems only as demanded by examples.

## 3. Correction: the mixed-sign zero-scale example

On \((0,\rho)^2\),
\[
u_1^{r_1}u_2^{r_2}e^{-cu_2/u_1}
\]
is integrable exactly when
\[
\boxed{r_2>-1\quad\text{and}\quad r_1+r_2>-2.}
\]

The sum condition alone is insufficient. For example, \(r_1=1,r_2=-2\) satisfies it, but the integral diverges as \(u_2\to0\) with \(u_1\) bounded away from zero.

Indeed, setting \(u_2=u_1v\) produces
\[
u_1^{r_1+r_2+1}v^{r_2}e^{-cv},
\qquad
0<u_1<\min(\rho,\rho/v).
\]
The small-\(v\) end gives \(r_2>-1\); the radial end gives the sum condition.

Unless that individual condition was already an ambient assumption, fix this example before using it to motivate the general theorem.

For a **single phase monomial**, the natural general criterion is particularly clean. Put \(b=r+\mathbf1\) and
\[
C=\{v\in\mathbb R_{\ge0}^k:\langle\kappa,v\rangle\ge0\}.
\]
Then the criterion is
\[
\boxed{\langle b,v\rangle>0\quad\text{for every }v\in C\setminus\{0\}.}
\]

Logarithmic coordinates turn the integrand, including volume, into a constant times
\[
\exp\!\left(-\langle b,x\rangle
-c'\exp(-\langle\kappa,x\rangle)\right),\qquad x\ge0.
\]
The cone \(C\) consists exactly of directions without superexponential suppression. This also recovers your landed coordinatewise sufficient condition.

## 4. Ranking

My implementation order would be:

### 1. **(a) Staged API weakening, with pointwise uniqueness as the first small deliverable**

Do not start with a wholesale replacement of `Phase`.

- First: continuous-version uniqueness and the cutoff-based pointwise theorem.
- Next: the support-free observable interface for the existing restricted kernel.
- Then: domain-local phase nonnegativity.

The observable change removes the boundary-trace obstruction. The phase change broadens admissible one-sided examples but is not needed for the quadratic exported acceptance test.

### 2. **(c) Tied-cut single-scaled certificate**

This is a real missing constructor, not just test infrastructure. It also covers the identity-chart regime you have already identified.

State the tail lemma with all relevant hypotheses:
\[
A>0,\quad c>0,\quad\kappa>0
\quad\Longrightarrow\quad
u^r e^{-cu^\kappa}\text{ integrable on }(A,\infty)
\]
for every real \(r\).

The “every \(r\)” claim needs \(\kappa>0\). If the cutoff \(A\) depends on remaining unscaled coordinates and tends to zero, fibrewise integrability alone does not prove the full profile certificate; retain the corresponding outer domination hypothesis.

### 3. **(b) The honest quadratic acceptance test**

Keep the exported two-branch record, \(F=a z_1^2\), and an observable with nonzero wall trace. This tests:

- the tied-cut constructor;
- branch bookkeeping;
- the actual exported kernel;
- agreement with an independently calculated constant.

Do not replace it with a formally easier zero-valued supported test.

### 4. **(d) LP optimal-vertex existence and classification**

Useful, but distinguish:

- existence of an optimum;
- existence of an optimal vertex;
- uniqueness of the optimum;
- classification of positive-dimensional optimal faces.

For a nonempty pointed polyhedron, a finite attained optimum admits an optimal vertex. Nonnegative-coordinate constraints usually provide pointedness in your setting. But an optimal-vertex theorem does **not** supply `UniqueLPMin`, and it does not resolve logarithmic contributions from optimal faces.

### 5. **(e) General zero-scale recession-cone integrability**

Mathematically valuable, but less urgent than the missing tied-cut constructor. First land the corrected two-dimensional mixed-sign example as a regression test; then generalise via the cone criterion.

### 6. **(f) Remaining closure work**

Without the note itself, I would check two items rather than invent another large workstream:

- **Nonvanishing discipline:** a certified zero coefficient is not a certified first nonzero asymptotic term.
- **Completeness of regime coverage:** LP classification must eventually cover tied constraints and optimal faces, not only unique vertices, before the atlas can be advertised as exhaustive.

You already have power-log dominance; avoid rebuilding that layer.

## 5. Concrete top-item statement and first step

A useful proposed helper signature is:

```lean
/-- Continuous versions of an a.e.-specified kernel agree on an open set. -/
theorem eqOn_of_ae_eq_restrict_of_continuousOn
    {U : Set ℝ} (hU : IsOpen U)
    {K₁ K₂ : ℝ → ℝ≥0∞}
    (h₁ : ContinuousOn K₁ U)
    (h₂ : ContinuousOn K₂ U)
    (hae : K₁ =ᵐ[volume.restrict U] K₂) :
    Set.EqOn K₁ K₂ U
```

This needs no finiteness assumption: `ℝ≥0∞` is Hausdorff. A real-valued version works identically. This is a proposed signature, not a claim about an existing Mathlib lemma name.

The proof is the standard positive-measure-neighbourhood argument: unequal values at a point yield, by continuity and Hausdorff separation, a nonempty open interval on which the values differ, contradicting a.e. equality.

**Cheapest first step:** derive your supported pointwise chart-independence theorem from this helper and the existing a.e./continuity theorems; then add the truth-cutoff corollary.

That delivers a genuine pointwise theorem immediately, while making its locality hypothesis explicit. The subsequent support-free refactor can broaden the continuity and push-forward identification inputs without changing the uniqueness layer.