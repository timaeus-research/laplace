## Executive conclusion

There is a useful distinction between what is ready to land and what deserves another research round.

* **Ready:** identify the facet boundary law, package `completionLaw`, prove concentration on supporting faces, and extend the facet response path to \(t=\infty\).
* **Promising, and stronger than a facet result:** under your **polytope + charged vertices** hypotheses, I would pursue **injectivity**, not search first for a square with a split fibre. There is a normal-translation argument that appears to rule out split fibres in this setting.
* **Still genuinely open work:** a usable necessary-and-sufficient **two-parameter accessibility criterion** at a vertex. Uniqueness and accessibility should now be separated sharply.

One correction first:
\[
\boxed{e^{-r\beta}Z(v-ru)\longrightarrow Z_F(v),}
\]
not \(e^{r\beta}Z(v-ru)\).

Here and below, a face event means \(A_F=\{x:S(x)\in F\}\); restrictions of \(\nu\) are to this event.

---

## Q1. Identify the face-conditioned law

### The right statement

Prove both statements, with the \(L^2\) statement first:
\[
\operatorname{rootDensExt}(x_M)
=
\left[
1_{A_F}\frac{e^{-\langle v_M,S\rangle/2}}{\sqrt{Z_F(v_M)}}
\right]_{L^2(\nu)}.
\]

Then derive
\[
\boxed{\operatorname{completionLaw}(x_M)
=(\nu|_{A_F}).\operatorname{tilted}(-\langle v_M,S\rangle).}
\]

The first identifies your already-constructed extension; the second is the useful public-facing theorem. In Lean, the measure construction is `ν.withDensity` with an `ℝ≥0∞`-valued density, not ordinary scalar multiplication of measures.

### Cheapest convergence proof: scalar DCT plus an exact affinity

You do not need an \(L^p\) dominated-convergence theorem.

Put
\[
g_r=e^{-\langle v_M,S\rangle}e^{r(\langle u,S\rangle-\beta)},
\qquad
A_r=\int g_r\,d\nu=e^{-r\beta}Z(v_M-ru).
\]
For \(r\ge0\),
\[
0\le g_r\le e^{-\langle v_M,S\rangle},
\qquad
g_r\longrightarrow 1_{A_F}e^{-\langle v_M,S\rangle}
\quad\text{a.e.}
\]
Thus \(A_r\to Z_F(v_M)>0\).

Now let \(q_F\) be the proposed face root density. Direct calculation gives
\[
\langle q_{v_M-ru},q_F\rangle_{L^2}
=\sqrt{\frac{Z_F(v_M)}{A_r}}.
\]
Both vectors have norm one, so
\[
\boxed{
\|q_{v_M-ru}-q_F\|_2^2
=2-2\sqrt{\frac{Z_F(v_M)}{A_r}}
\longrightarrow0.}
\]

This is cheaper than dominating \((q_r-q_F)^2\), and it reuses your affinity infrastructure.

### Mathlib tool

Use the established lemma

```lean
MeasureTheory.tendsto_integral_of_dominated_convergence
```

on the integer sequence \(r=n\). Its relevant hypotheses are:

* each integrand is a.e. strongly measurable;
* an integrable real-valued bound dominates its norm a.e.;
* pointwise a.e. convergence.

Here the bound is \(e^{-\langle v_M,S\rangle}\), integrable because \(S\) is bounded and \(\nu\) is finite. The supporting inequality and the pointwise limit need only hold a.e.

I would not choose an uncertain `tendsto_Lp_...` API for this proof. Scalar DCT plus the displayed norm identity avoids that dependency entirely.

**Important separation:** this Hellinger limit holds whether or not the ray has finite Fisher length. Accessibility is needed to identify it with a point of the Fisher completion.

---

## Q2. Injectivity: pursue a normal-translation theorem

First, the parenthetical equivalence needs qualification:

> Injectivity of a Lipschitz map does **not** by itself imply that the source topology equals the image topology.

Those are two theorems. In your setting, however, the same argument appears capable of proving both.

### Proposed theorem under your standing hypotheses

For a polytope moment body with every vertex charged:

1. `meanExt` is injective;
2. hence `rootDensExt` is injective;
3. `rootDensExt` is a topological embedding onto its image.

I would treat this as a research theorem with the following concrete proof programme—not as something already supplied by the facet modules.

### Step 1: every completion law is a face exponential-family law

Let \(x\) be a completion point and let \(M=\bar m(x)\). Let \(F\) be the unique face with \(M\in\operatorname{ri}F\).

The supporting-face argument in Q4 gives
\[
Q_x(A_F)=1.
\]
If \(\theta_n\to x\) in Fisher distance, Hellinger convergence gives
\[
P_{\theta_n}(A_F)\to1.
\]
Consequently the conditional laws \(P_{\theta_n}(\,\cdot\,|A_F)\) have means tending to \(M\).

Their canonical parameters are the projections of \(\theta_n\) onto
\[
T_F=\operatorname{dirSpan}(\nu|_{A_F},1,S).
\]
The inverse mean map of the restricted family then gives
\[
\operatorname{proj}_{T_F}\theta_n\to v_M.
\]
It follows that
\[
Q_x=(\nu|_{A_F}).\operatorname{tilted}(-\langle v_M,S\rangle).
\]

Thus **equal extended means already force equal extended laws**. What remains is to rule out multiple Fisher points representing that law.

### Step 2: uniform control of translations towards a face

Use the sign-adjusted normal cone
\[
C_F=\{a:\langle a,S\rangle=c_a\text{ on }A_F,\ 
                    \langle a,S\rangle\ge c_a\text{ a.e.}\}.
\]
Adding \(a\in C_F\) to the parameter suppresses mass off \(F\).

Writing \(f_a=e^{-(\langle a,S\rangle-c_a)}\), one has
\[
0<f_a\le1,\qquad f_a=1\text{ on }A_F,
\]
and
\[
P_{\theta+a}=\frac{f_a}{E_\theta f_a}P_\theta.
\]
Since \(E_\theta f_a\ge P_\theta(A_F)\), the variance-minimization formula yields
\[
\boxed{
\operatorname{fisherVar}(\theta+a,w)
\le \frac{\operatorname{fisherVar}(\theta,w)}
          {P_\theta(A_F)}.}
\]

Therefore translations by **arbitrarily large** elements of \(C_F\) are uniformly length-Lipschitz on paths satisfying \(P_\theta(A_F)\ge c>0\).

That uniformity is the key. A generic bounded-tilt estimate depending exponentially on \(\|a\|\) is not enough.

### Step 3: a translated-grid argument

After removing their vanishing tangential errors, two Cauchy sequences representing the same face law have the form
\[
v_M+a_n,\qquad v_M+b_n,\qquad a_n,b_n\in C_F
\]
eventually.

Why eventual cone membership? Each vertex outside \(F\) is charged. Its probability tends to zero while the probability of \(F\) tends to one; hence its normal energy gap tends to \(+\infty\). There are only finitely many vertices.

Connect through
\[
v_M+a_n+b_m.
\]
Translate short Cauchy-tail paths using the uniform estimate above. The remaining fixed normal shifts have Fisher distance tending to zero, because their score becomes constant under a law concentrating on \(F\).

This forces the two completion points to coincide.

**Technical caution:** short connecting paths must stay in a face-probability tube. This follows from your Hellinger control, since
\[
q\longmapsto \|1_{A_F}q\|_2
\]
is 1-Lipschitz. Do not silently assume that globally short paths stay inside the normal cone.

### Topological embedding

Fix an accessible face law \(q_F\) and one Fisher-Cauchy sequence approaching it. The same translated-tail estimate shows:

> Any parameter sequence whose root densities converge to \(q_F\) converges in Fisher distance to its accessible completion point.

Approximation then handles sequences of completion points. This gives inverse continuity on the image.

I would not claim this proof for arbitrary bounded-statistic models without the charged-polytope assumptions: eventual normal-cone membership is a real input.

### Facets only

If all completion points lie over interior means or accessible facet interiors, your existing facet uniqueness, together with interior uniqueness, already gives injectivity. Inverse continuity remains a separate theorem.

---

## Q3. The charged square: first prove an accessible singleton, not a split fibre

Under the Q2 programme, option (a) should be impossible under your standing hypotheses.

### Explicit first example

Take a probability measure on \([0,1]\)
\[
\mu=c\left(\delta_0+\delta_1+
                 \sum_{n\ge1}2^{-4n}\delta_{2^{-n}}\right),
\]
and put
\[
\nu=\mu\otimes\mu,\qquad S(x,y)=(x,y).
\]

Every square vertex is charged. The one-dimensional shell sums at \(0\) are finite:
\[
\sum_n\sqrt{2^{-4n}}=\sum_n2^{-2n}<\infty.
\]
At \(1\), the remaining support has a positive gap.

The family factorizes:
\[
P_{(a,b)}=P^{(1)}_a\otimes P^{(2)}_b,
\]
and the Fisher form splits:
\[
F_{(a,b)}(v,w)^2
=F^{(1)}_a(v)^2+F^{(2)}_b(w)^2.
\]

The precise first theorem I would formalize is:

> For this product family, if \(a_n,b_n\to+\infty\), then \((a_n,b_n)\) converges in the Fisher completion to a single point over \((0,0)\).

A convenient stronger bound is
\[
d_F((a,b),(a',b'))
\le d_1(a,a')+d_2(b,b').
\]
The one-dimensional finite tails prove the assertion immediately.

This gives a genuinely countable layered square example without requiring a general corner classification.

### What the two-parameter criterion must include

The masses
\[
m_{j,k}=\nu\{2^{-j-1}<\ell_1\le2^{-j},\
                 2^{-k-1}<\ell_2\le2^{-k}\}
\]
do **not include the axis layers** \(\ell_1=0\) or \(\ell_2=0\), nor the vertex mass. Include indices \(j=\infty\), \(k=\infty\), or add those pieces separately.

For a product measure, the criterion is clean:

> The corner is accessible iff both corresponding one-dimensional endpoints are accessible; when accessible, its fibre is a singleton.

For general correlated \(m_{j,k}\), I would **not** announce a scalar shell-sum criterion yet.

In particular, distinguish:

* accessibility along one fixed interior normal ray;
* accessibility along an anisotropic path;
* accessibility by successively approaching faces.

A test for one ray is not automatically a test for the vertex. Two-dimensional mass arrays can organize thin layers very differently in the two coordinates.

The strongest responsible general statement at present is:

* **nonemptiness:** still requires a genuinely multiscale accessibility theorem;
* **uniqueness:** should follow from the normal-translation theorem, independently of a shell classification.

That separation is more valuable than forcing both questions into one criterion.

---

## Q4. Boundary laws concentrate on charged faces

Yes. In fact, prove this for every exposed face containing the mean, and then for the minimal face.

Let \(q=\operatorname{rootDensExt}(x)\), and suppose
\[
\langle u,S\rangle\le\beta\quad\nu\text{-a.e.},
\qquad
\langle u,\bar m(x)\rangle=\beta.
\]
Set \(g=\beta-\langle u,S\rangle\ge0\). Your moment identity and \(\|q\|_2=1\) imply
\[
\int gq^2\,d\nu=0.
\]
Hence
\[
gq^2=0\quad\nu\text{-a.e.},
\]
and therefore
\[
q^2=0\quad\nu\text{-a.e. on }\{g>0\}.
\]

### Lean route

1. Define `completionLaw` using `withDensity`.
2. Prove its total mass is one from `norm = 1`.
3. Transfer the coordinate moment identities.
4. Prove integrability of \(gq^2\): \(g\) is bounded and \(q^2\) is integrable.
5. Apply the nonnegative-integral-zero characterization, e.g. the `integral_eq_zero_iff_of_nonneg_ae` API.
6. Use positivity of \(g\) off the supporting hyperplane to obtain \(q^2=0\) there.
7. Conclude `completionLaw x A_F = 1`.
8. Absolute continuity then gives \(\nu(A_F)>0\).

For a polytope, the minimal face is exposed, so one exposing functional suffices.

Under your present charged-vertex assumption, positivity of every nonempty face is already automatic. The substantive new result is **concentration of the completion law**, not merely face positivity.

The range decomposition can be stated exactly using accessibility:
\[
\operatorname{range}\bar m
=\bigcup_{F\le P}
\{M\in\operatorname{ri}F:M\text{ is Fisher-accessible}\}.
\]
Your facet modules identify the codimension-one terms. Higher-codimension terms remain an accessibility problem.

---

## Q5. Extending the data response to infinity

Under the hypotheses of your existing facet data-path equivalence, the desired equivalence is valid:
\[
\boxed{
\theta_t\text{ has a limit in }\widehat W_F
\iff
\text{its response length on }[0,\infty)\text{ is finite}.}
\]

But the reverse implication is **not** a general fact about curves in metric spaces.

### Why it works here

* Finite length gives the Cauchy criterion by the tail-length bound.
* Conversely, a completion limit has extended mean \(M\).
* The facet accessibility theorem forces the facet ray integral to be finite.
* Your data-ray equivalence then forces the response length to be finite.

Facet uniqueness identifies the limit as \(x_M\). Continuity on the finite interval, together with this limit, gives a continuous extension to the one-point endpoint compactification \([0,\infty]\).

After Q1:
\[
\operatorname{completionLaw}(x_M)
=(\nu|_{A_F}).\operatorname{tilted}(-\langle v_M,S\rangle).
\]

### The information-projection statement

Normalize the featureless reference as \(\mu_0=\nu/\nu(\Omega)\). Then the face law \(Q_M\) is the unique minimizer
\[
\boxed{
Q_M=\arg\min\left\{
D(Q\|\mu_0):
Q\text{ probability},\ Q\ll\mu_0,\ \int S\,dQ=M
\right\}.}
\]
The boundary moment constraint itself forces concentration on \(F\).

Call this **maximum relative entropy** unless the reference really is the uniform law for the relevant notion of entropy.

If \(h\le H\) a.e. and \(\nu\{h=H\}>0\), the data laws converge to
\[
Q_{\rm data}=\nu(\,\cdot\,|h=H).
\]
If its mean is \(M\), the completed response is the information projection with the **same mean**. It need not equal \(Q_{\rm data}\).

What is missing for the fully packaged theorem:

* the law identification from Q1;
* a continuous-extension wrapper;
* the conditional-data-limit theorem, if not already present;
* a measure-level KL minimization theorem allowing a boundary-supported reference tilt.

Your finite-parameter Bregman/Pythagoras results may supply much of the last item, but the boundary support and absolute-continuity bookkeeping must be explicit.

---

## Q6. Recommended landing order

I would split the deep claims into small modules rather than require each entire theorem to fit within 300 lines.

| Order | Module | One-line statement |
|---|---|---|
| 1 | **`FisherCompletionMeasure`** | Every completion point defines a probability law absolutely continuous with respect to \(\nu\), with mean `meanExt`. |
| 2 | **`FaceRootDensityLimit`** | A normal ray converges in Hellinger distance to its face-conditioned exponential-family law, without an accessibility assumption. |
| 3 | **`FacetCompletionLaw`** | An accessible facet point represents exactly that face law. |
| 4 | **`CompletionSupportingFace`** | A completion law is concentrated on every supporting face containing its mean. |
| 5 | **`DataResponseEndpoint`** | Under the facet hypotheses, continuous extension to infinity is equivalent to finite response length. |
| 6 | **`NormalTiltFisherComparison`** | Face-normal translation multiplies Fisher speed by at most \(P_\theta(F)^{-1/2}\). |
| 7 | **`CompletionFaceParameters`** | A Cauchy sequence over a face interior has convergent face parameters and eventually face-normal residuals. |
| 8 | **`CompletionFaceUnique`** | The translated-grid argument makes every nonempty mean fibre a singleton. |
| 9 | **`CompletionHellingerEmbedding`** | Hellinger convergence to an accessible law implies Fisher convergence. |
| 10 | **`ProductCornerCompletion`** | Product one-dimensional accessibility gives explicit accessible square corners and singleton fibres. |

**By mathematical depth:** 8–9 first, then the unresolved multiscale accessibility problem, then 2–5. **By implementation order:** use the table.

I would postpone a general flags package until the normal-translation infrastructure lands. The next conceptual target is:

> **One accessible face law has one intrinsic endpoint; the remaining geometry is which face laws are accessible.**

That is a substantially cleaner completion programme than allowing uniqueness and accessibility to remain entangled.