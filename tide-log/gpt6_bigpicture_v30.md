**Recommendation: freeze the coefficient-summability release, after a thin end-to-end wrapper and completion of v23. Treat C as a separately scoped extension, with a one-variable pilot before authorising the multivariate implementation.**

I cannot actually consult #30 from this conversation: its text and the repository declarations are not available here. The advice below uses your supplied status at `ba849b3`; in particular, I distinguish a precise wrapper contract from a verified Lean declaration.

## 1. Release now; give C a bounded experimental phase

The current result is substantial and publishable under the qualification:

> **The Taylor-tree expansion is formalised under weighted absolute summability of the input coefficient families, including identification of its coefficients with the explicit convergent series and their special-function derivative notation. The implication from the paper’s original analytic input hypotheses to these coefficient-family hypotheses remains separate.**

Do **not** call this the unqualified formalisation of the full paper theorem. Also, v23 is still running: the latest dictionary result does not yet have a completed independent-review sign-off.

### First specify C exactly

Before any implementation, write the bridge as a proposition with the following outputs for each input function:
\[
c:\mathbb N^d\to\mathbb R,\qquad
\sum_{\gamma\in\mathbb N^d}|c_\gamma|b^{|\gamma|}<\infty,\qquad
f(u)=\sum_\gamma c_\gamma u^\gamma\quad(u\in[0,b]^d).
\]

Include every further compatibility required downstream—for example, the constant coefficient and the relationship between the fluctuation family \(J\) and the input \(\xi\). A summability theorem alone is not the input bridge.

**Crucial hypothesis audit:** determine whether the paper assumes holomorphic extension to a suitable polydisc centred at \(0\), or something weaker. Real analyticity on a neighbourhood of the cube, by itself, does not guarantee convergence of the Taylor series at \(0\) throughout the cube. A complex-polydisc bridge is only an exact bridge if its assumptions follow from the paper’s assumptions.

### C₁: concrete one-variable route

Assume a holomorphic extension \(F\) to \(\{|z|<R\}\), with \(0<b<R\). Choose
\[
b<r<R.
\]

1. **Produce the series at \(0\).**  
   Use `DifferentiableOn.hasFPowerSeriesOnBall` / `cauchyPowerSeries`. Establish the adapter from a one-dimensional `FormalMultilinearSeries` to scalar coefficients:
   \[
   c_n=p_n(1,\ldots,1),\qquad p_n(z,\ldots,z)=c_nz^n.
   \]
   This is where coefficient normalisation and factorials must be checked.

2. **Obtain the majorant.**  
   Compactness gives a bound \(M\) on the circle of radius \(r\). Derive
   \[
   |c_n|\le Mr^{-n}.
   \]
   The proposed `norm_le_div_pow_of_pos_of_lt_radius` route is worth testing, but its exact hypotheses and radius conventions must be inspected—not assumed. An intermediate radius may be needed if a library bound uses a strict interior-radius condition.

3. **Weighted summability.**
   \[
   \sum_n|c_n|b^n\le \frac{M}{1-b/r}.
   \]

4. **Reality.**  
   If \(F\) agrees with a real-valued function on the relevant real segment, prove \(c_n\in\mathbb R\). Use uniqueness of the scalar power series, or a reflection/identity argument. “Real-valued on the segment” does not make the library’s complex coefficients definitionally real.

5. **Identification on the closed interval.**  
   Transfer the power-series identity to every \(u\in[0,b]\), then package it in the exact coefficient-family interface used by XXVIII.

**Planning estimate:** 5–8 implementation units, plus one independent review, assuming the cited series API supplies the needed quantitative bound. This is an estimate in the scale of your recent units, not a guarantee.

**Go/no-go gate after at most two scouting units:** require a compiled lemma producing scalar coefficients, their evaluation identity, and a usable geometric coefficient bound from a holomorphic-disc hypothesis. If that still requires substantial new analytic infrastructure, stop; do not allow “just an adapter” to become an unbudgeted project.

### C_d: iterate coordinates, but retain quantitative bounds

The realistic route is **iterated one-variable Cauchy coefficient extraction**, with mixed coefficients represented by iterated circle integrals. Slice-wise series existence alone is insufficient: one must prove compatibility of the slices and justify rearrangements.

For a holomorphic function on a polydisc containing the closed polydisc of radius \(r>b\), target:
\[
|c_\gamma|\le Mr^{-|\gamma|},
\qquad
\sum_\gamma|c_\gamma|b^{|\gamma|}
 \le M(1-b/r)^{-d}.
\]

The work packages are:

- coordinate insertion and holomorphic slices;
- iterated coefficient extraction and its quantitative bound;
- reconstruction on the smaller polydisc;
- interchange/regrouping of the absolutely convergent sums;
- reality and conversion to the existing multi-index family;
- the final bridge for both input functions.

Do not begin by building a general several-variable complex-analysis library unless the targeted route proves impossible.

**Planning estimate:** another 12–20 implementation units after C₁, plus review; budget roughly **20–30 units for the complete bridge**, allowing for integration and API friction. Multivariate infrastructure can push this higher.

**Multivariate gate:** first prove a quantitative two-coordinate extraction/reconstruction lemma with the product geometric majorant. If that needs a new general parameter-dependent integration framework, re-scope before proceeding to arbitrary \(d\).

**Is C₁ worth landing? Yes**, provided it closes the actual one-dimensional theorem and exports reusable scalar coefficient/bound adapters. Label it a one-dimensional corollary, not “C completed” or a nearly-complete multivariate bridge.

## 2. Yes: land one end-to-end wrapper

This is the highest-value remaining release task. At present, the reader must reconstruct the theorem by composing headlines. The wrapper should perform that composition without introducing another coefficient construction.

I recommend:

- `thm_TaylorTree_coeffFamily`: the readable end-to-end result;
- a companion dictionary theorem or a dictionary field in its result structure;
- later, `thm_TaylorTree_analytic`: obtained solely by applying C and the coefficient-family wrapper.

### Exact contract to implement

The actual signatures of XXVIII and its remainder predicate are needed to write a genuinely exact Lean statement. In particular, I would **not invent the power of \(n\), log indexing, cutoff admissibility, or quantifier order** from the summary alone.

Here is the exact *interface contract*; the capitalised predicates must be instantiated directly with the existing definitions, without changing their strength.

Let `D` package precisely the hypotheses and data of XXVIII. Let:

- \(I_D\) be its full coefficient index type, including the \(\Lambda(h,k)\) and log indices;
- \(\mathcal A_D\) be its admissible cutoffs;
- \(A_{D,\chi}(q)\) be the existing cutoff coefficient;
- \(T_{D,q,p}\), \(c_{\eta,D}\), \(J_D\), and \(\beta_D\) be the corresponding XXIX data;
- \(\operatorname{ExpansionRemainder}_{D,L}(C)\) be **exactly** XXVIII’s expansion-and-remainder conclusion.

Then the wrapper should state:
\[
\begin{aligned}
\exists C:I_D\to\mathbb R,\quad
&(\forall\chi\in\mathcal A_D,\ \forall q\in I_D,\
       A_{D,\chi}(q)=C(q))\\
{}\land{}&
\left(\forall q\in I_D,\
 \operatorname{Summable}\left[
 p\mapsto
 \left|\frac{\beta_D^p}{p!}
 T_{D,q,p}(c_{\eta,D}*J_D^{*p})\right|
 \right]\right)\\
{}\land{}&
\left(\forall q\in I_D,\
 C(q)=\sum_{p=0}^{\infty}\frac{\beta_D^p}{p!}
 T_{D,q,p}(c_{\eta,D}*J_D^{*p})\right)\\
{}\land{}&
\left(\forall L,\ \operatorname{AdmissibleOrder}_D(L)\to
 \operatorname{ExpansionRemainder}_{D,L}(C)\right)\\
{}\land{}&\operatorname{MomentDictionary}(D).
\end{aligned}
\]

Here `MomentDictionary` includes, under XXX’s exact hypotheses,
\[
\beta^p\operatorname{fluctMoment}(\beta,a,p,\mu,i)
=
(-1)^i
\left.\frac{d^i}{d\nu^i}
\left(\frac{d^p}{dx^p}S_\nu(x)\Big|_{x=a}\right)
\right|_{\nu=\mu},
\qquad \mu>0.
\]

Use XXX directly; do not silently enlarge the derivative domain because another identification holds for every real \(\mu\).

**Three important design points:**

1. Put \(\exists C\) **before** \(\forall L\) and \(\forall\chi\). One coefficient system serves every expansion order and cutoff.
2. Choose \(C\) to be the existing `familySpectralCoeff`, and expose that equality if useful. Do not construct a second “wrapper coefficient.”
3. Preserve XXVIII’s exact parameter dependence and uniformity. In particular, fixed-\(\beta\) estimates must not become uniform-in-\(\beta\) estimates through abbreviated wording.

A result structure with named fields will be much easier to consume than a long conjunction. The wrapper should be a small assembly proof, not another analytic development.

## 3. Authors’ hand-off: two pages, with links to details

Yes: **two pages maximum for the main report**. Put technical inventories and review logs behind links.

Suggested file: `staging/taylor_tree_author_handoff.md`.

### Page 1 — What is proved

**A. Release identification**

- Reviewed release commit and build command.
- Current baseline: `ba849b3`; record any subsequent wrapper/review commit.
- Zero `sorry`; no additional axioms, with the project’s established axiom-audit convention.

**B. Theorem map**

List the **actual Lean declaration names**, file paths, and paper counterparts:

| Result | Role |
|---|---|
| XXVII/XXVIII declarations | Expansion and remainder under coefficient summability |
| `familySpectralCoeff = familyCoeffSeries` declaration, XXIX | Explicit series and absolute convergence |
| u250 and XXX declarations | \(a\)-, \(\mu\)-, and mixed-derivative dictionary |
| `thm_TaylorTree_coeffFamily` | Single end-to-end statement |

Headline labels alone are not sufficient identifiers. Populate this table from the source, not from guessed names.

**C. Qualification paragraph**

Use the paragraph at the start of this answer, followed by the exact outstanding C proposition and a statement of whether its proposed complex-analytic assumptions match the paper.

### Page 2 — Author actions and caveats

**D. Paper correction**
\[
\partial_a^pS_\mu(a)=\boxed{\beta^p}\,S_{\mu+p/2}(a)
\]
under the stated normalisation of \(S\).

Mention the resulting mixed-derivative formula. Ask the authors to check downstream displays for the same missing factor; the formula without \(\beta^p\) is valid only under an appropriate changed normalisation or \(\beta=1\).

**E. Numerical sanity table**

State explicitly:

> Numerical comparisons are diagnostics, not kernel-checked proofs of the asymptotic expansion or of its remainder bounds. Their interpretation depends on the chosen normalisation, parameter regime, quadrature error, and truncation error.

Record whether the table uses the corrected \(\beta^p\) factors. Tests only at \(\beta=1\) cannot detect this erratum.

**F. Review and remaining work**

- v20–v22 outcomes, with any qualifications retained.
- v23 outcome once complete; until then mark it pending.
- C status and decision gate.
- Any remaining scope difference for `cor:standardintegralexp`; do not imply that the corollary is covered merely because TaylorTree’s coefficient clauses are covered.

## 4. Before freezing: short checklist

1. **Finish v23 and resolve its findings.**
2. **Land and review the wrapper**, including its quantifier order.
3. **Audit the paper-to-Lean hypothesis table:** analytic assumptions, \(b\), \(\beta\), admissible \(h,k\), cutoff class, parameter dependence, and remainder strength.
4. **Separate boundary claims.** The reported pointwise expansion is on \((0,b]^d\). If the standard-integral corollary uses the closed cube, make the measure-zero boundary transfer explicit where needed.
5. **Run a clean build and dependency/axiom audit on the final pin.**
6. **Preserve the existing release**, then tag the qualified release with its obligation ledger.
7. Only then open the bounded C₁ pilot.

**Priority order now:** preserve baseline → v23 → wrapper and interface review → two-page hand-off / release → optional C₁ pilot. The wrapper is release work; multivariate C is a new analytic workstream.
