## Recommendation

**Freeze the current result as a qualified milestone, but do not end the programme yet.** The analytic expansion and its remainder are now established; the remaining work concerns matching the paper’s input hypotheses and coefficient description, not repairing Stages 3–4.

I cannot consult #29 directly from this conversation. The recommendations below are based on the status and review findings you supplied.

My priority ranking for **faithfulness to the paper** is:

1. **C — the analytic-hypothesis bridge:** necessary to claim the paper’s own hypotheses.
2. **A — explicit absolutely convergent coefficient series:** necessary to close the coefficient-description qualification.
3. **B — derivative dictionary:** necessary if that dictionary appears in the theorem’s asserted coefficient formula.
4. **D — final hand-off and freeze.**

My recommended **execution order** is slightly different:

> **D₀: preserve the qualified release now → short C feasibility gate → A → C implementation → targeted B → independent fidelity review → D.**

A has the most predictable payoff and fits the infrastructure already built. C deserves early scouting because it is the remaining schedule risk. Do not reopen the proved expansion machinery.

---

## 1. Remaining work: scope, units, and gates

### A. Explicit coefficient-series identification

**Go. Estimate: 8–12 units**, assuming the polynomial coefficient kernel exposes the estimates used in u242. Otherwise allow **12–16**.

Use **finite lower intervals**, not multiset-indexed sums, as the primary API. For multi-indices, define
\[
(c*d)_\gamma=\sum_{\delta\in\operatorname{Iic}(\gamma)}
c_\delta d_{\gamma-\delta}.
\]
The subtraction is coordinatewise. The finite reindexing between these terms and pairs satisfying \(\delta+\epsilon=\gamma\) avoids needing a global `HasAntidiagonal` instance.

Keep the API deliberately small:

1. Convolution and its finite-pair reindexing lemma.
2. Absolute summability and
   \[
   \operatorname{mass}(c*d)\le \operatorname{mass}(c)\operatorname{mass}(d).
   \]
3. Unit, associativity, and powers—only as needed downstream.
4. Evaluation:
   \[
   \operatorname{evalF}(c*d)(u)
   =\operatorname{evalF}(c)(u)\operatorname{evalF}(d)(u)
   \quad(u\in[0,1]^d).
   \]
5. Compatibility with polynomial lists and convergence of powers under truncation.
6. Kernel functionals and the absolutely convergent outer series.
7. Identification of that series with the existing limit-defined coefficient.

**Important gate:** continuity of each \(T_{\mu,j,p}\) is not enough. Before building much API, exhibit a summable majorant
\[
\sum_{p=0}^{\infty}\frac{\beta^p}{p!}
\left|T_{\mu,j,p}(c_\eta*J^{*p})\right|<\infty,
\]
with control uniform over the truncations used for identification.

The natural majorant should come from the same exponential resummation behind u242, with phase parameter \(a+B\). Extract it explicitly. **If this cannot be obtained in two reconnaissance units, stop and inspect the kernel estimates rather than expanding the convolution library.**

Do this on the unit cube and transfer through u248–u249. A separate weighted convolution library for arbitrary \(b\) is unnecessary.

### B. Derivative dictionary

**Go after A; keep it theorem-specific. Estimate: 5–8 units**, potentially **8–12** if mixed/iterated derivative bookkeeping is poorly supported. The previous 4–7 estimate remains plausible only if the first dominated-differentiation lemma is straightforward.

For
\[
S_\nu(a)=\int_0^\infty t^{\nu-1}
e^{-\beta t+\beta a\sqrt t}\,dt,
\]
the essential identities are
\[
\partial_a^p S_\nu(a)
=\beta^p S_{\nu+p/2}(a),
\qquad
\partial_\nu^i S_\nu(a)
=\int_0^\infty t^{\nu-1}(\log t)^i
e^{-\beta t+\beta a\sqrt t}\,dt.
\]

Use local parameter ranges with \(\nu\ge\nu_0>0\) and bounded \(a\). Near zero, dominate by powers times absolute log powers; at infinity, absorb the \(\sqrt t\) term into exponential decay.

**Gate:** prove one local domination lemma that supports both parameter derivatives before attempting iterated derivatives.

Do not formalise a general parameter-dependent integral calculus library. Prove only the derivative orders and combinations appearing in the coefficient formula.

Also: **audit the sign convention against the actual definition of `fluctMoment`.** The notation \((-\partial_\mu)^i\) corresponds to \((-\log t)^i\), not \((\log t)^i\). Likewise, preserve the \(\beta^p\), factorials, and shifted exponent exactly.

### C. Cauchy-estimate bridge

**Necessary, but not a cheap corollary of the currently advertised Mathlib interfaces.**

The coordinatewise one-variable route is the more predictable route to the **sharp polydisc statement**
\[
|c_\gamma|\le M_r r^{-|\gamma|},
\qquad
\sum_\gamma |c_\gamma|b^{|\gamma|}
\le M_r(1-b/r)^{-d},
\quad b<r<R.
\]

It still needs substantial plumbing:

- restrictions to coordinate slices;
- iterated coefficient extraction or iterated Cauchy formulas;
- identification with Taylor derivatives, with the correct multi-index factorial;
- reconstruction on the closed cube;
- real coefficients when the holomorphic extension restricts to a real-valued function.

**Estimate: 2–3 scouting units, followed by 15–25 implementation units.** Budget **25–35 total** if contour-integral iteration or multivariate coefficient identification needs significant infrastructure.

`HasFPowerSeriesOnBall` is worth scouting, but not assuming as a shortcut. With the sup norm, the ball has the desired geometry, but a `FormalMultilinearSeries` is not yet the required multi-index family. A naïve coefficient extraction can introduce dimension-dependent losses and fail to preserve the crucial condition “every \(b<R\).”

#### Concrete C gate

Within the scouting allocation, require:

1. A precise Lean statement using the paper’s actual analytic hypothesis.
2. A credible coefficient-extraction construction.
3. A proof path yielding weighted absolute summability for **arbitrary \(b<R\)**, without an artificial radius loss.
4. A proof path for equality with the original function on the **closed** cube.

Ideally finish the one-dimensional bridge during scouting. If the multivariate plan remains only “iterate Cauchy somehow,” mark C **not yet budgetable** and report that fact. Do not silently replace the paper’s hypothesis by a stronger `HasFPowerSeriesOnBall` assumption.

If the paper actually supplies a Taylor expansion with convergence on a larger polydisc as part of its hypothesis, exploit that: the required bridge may be much smaller. Verify the source statement before building complex analysis.

---

## 2. What to tell the authors now

Present **Headline XXVIII as the principal Taylor-tree theorem**, **Headline XXVII as its unit-cube core**, and the proved standard-integral asymptotic consequence as the corollary. Give their actual Lean declaration names in the hand-off. Do not present u249 alone as an unqualified formalisation of every clause of `thm:TaylorTree`.

Here is the requested two-paragraph wording:

> We have formalised the Taylor-tree asymptotic expansion and its standard-integral corollary for general boxes, under the coefficient hypothesis \(\sum_\gamma |c_\gamma|b^{|\gamma|}<\infty\) for both the phase and amplitude. The main general-box theorem, Headline XXVIII, obtained from the unit-cube theorem Headline XXVII by exact scaling, uses the paper’s exponent set \(\Lambda(h,k)\), the paper’s logarithmic indexing, and a single coefficient system independent of the cutoff. For every positive cutoff \(L\), it proves the remainder \(O(N^{-L}(1+\log N)^{d-1})\) as \(N\to\infty\), under the formalised admissibility assumptions on the remaining parameters. The development contains no `sorry` and introduces no additional axioms.
>
> This is presently a qualified formalisation of `thm:TaylorTree`. Weighted absolute summability is a sufficient condition that is less restrictive than the larger-polydisc analytic hypothesis, but the implication from the paper’s analytic hypothesis—including identification with Taylor derivatives—has not yet been formalised. Coefficients are explicit for polynomial inputs and are defined for summable families by stable limits of polynomial truncations; their identification with the paper’s explicit absolutely convergent infinite coefficient series, and the special-function derivative notation for that formula, remain unformalised. Independent reviews of Stages 3 and 4 found no mathematical defects and recorded these scope qualifications.

---

## 3. Statements to re-state before showing the authors

**No mathematical repair is indicated by the reported reviews.** I would add or verify a thin author-facing layer covering these points:

- **Input functions versus representing families.** State explicitly that the integral uses the family evaluations, and provide the wrapper transporting the result along equality with given functions \(\xi,\eta\). Make clear whether representation independence is proved or not needed for the stated interface.

- **Quantifier order.** Display
  \[
  \exists(A_{\mu,j})\;\forall L>0,\quad\text{remainder bound},
  \]
  or its definition-based equivalent. The coefficient family must visibly be independent of both \(L\) and \(N\).

- **Fixed-parameter versus uniform bounds.** Say exactly which parameters the remainder constant may depend on. Do not let uniformity over mass-bounded families be read as uniformity in \(\beta\), \(b\), \(h\), or \(k\).

- **General-box threshold.** Unit-cube estimates requiring \(Nb^{2|k|}\ge1\) immediately give an eventual estimate in \(N\). An all-\(N\ge1\) box estimate requires separate treatment below that threshold. State whichever theorem was actually proved.

- **Coefficient normalization.** Put the \(b\)-prefactor, \(b^{-2|k|\mu}\), and the binomial mixing from
  \[
  \log(Nb^{2|k|})=\log N+2|k|\log b
  \]
  in one explicit coefficient-transport lemma. This is where authors can most easily compare formulas.

- **Admissibility in one place.** Include dimension/nondegeneracy assumptions and \(\beta>0\), \(b>0\); distinguish support containment from nonvanishing. The theorem says coefficients vanish off \(\Lambda\), not that every candidate exponent occurs.

Finally, call the numerical table a **sanity check**, not validation of the theorem or of a sharp remainder rate.

---

## 4. Concrete stopping criterion

There are two legitimate finish lines; keep their labels separate.

### Expansion under the paper’s own hypotheses

Minimal remaining work:

1. **C:** derive the existing family assumptions and evaluation identities from the paper’s actual analytic hypotheses.
2. Add the paper-facing theorem wrappers.
3. Obtain an independent review of that bridge and hypothesis matching.

At that point, you can say:

> “The Taylor-tree expansion and remainder are formalised under the paper’s own hypotheses; the paper’s explicit coefficient identification remains qualified.”

### Full `thm:TaylorTree`, including the stated coefficient formula

For the full claim targeted in your original stopping criterion, require:

1. **C:** exact input-hypothesis bridge.
2. **A:** identification of the existing coefficients with the explicit **absolutely convergent** family series.
3. **B:** the derivative dictionary to the extent it is part of the paper’s asserted formula.
4. One end-to-end theorem matching the paper, with the corollary obtained from it.
5. Independent review of hypotheses, coefficient normalization, and quantifiers.

**That is the final stop.** Do not add generic SCV infrastructure beyond what C needs; a universal convolution framework; special-function closed forms; sharper remainders; or additional numerical campaigns.

The standing instruction to continue autonomously supports proceeding through these bounded tasks. It does not justify an open-ended library project. Preserve the qualified release now, run the C gate, and make A the next substantial implementation target.
