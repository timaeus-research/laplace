## Recommendation

**Freeze `45b0943` as an immutable, qualified milestone now, and authorise one tightly bounded derivative-identification sprint. Then close the Taylor-tree programme.**

I would not leave this last identification undone without a short attempt: it removes the principal remaining translation between the formal coefficients and the paper’s notation. But I would **not** authorise a general several-variable Taylor API project to obtain it.

My suggested budget is **4–6 units, with a hard cap of 6 and a gate after unit 1**. That is a planning estimate, not a verified assessment of Mathlib at this pin. Your 3–5 estimate becomes plausible after one simplification to R-a described below.

The successful analytic bridge is already worth releasing. The finishing sprint must not put that release at risk.

---

## 1. Finish, but simplify R-a substantially

Your proposed target permits you to avoid the most expensive-looking part of your proposed proof:

> **You do not need a theorem commuting arbitrary iterated derivatives through `iterOp`.**

Let
\[
g(t)=\operatorname{polyCoeff}_d(r,F(t,\cdot),\gamma'),
\qquad
B=\prod_{i:\mathrm{Fin}\,d}\gamma'_i!.
\]

The induction hypothesis, applied separately for every \(t\) in the open parameter disc, gives
\[
g(t)=\frac{\operatorname{coordDeriv}_d(\gamma',F(t,\cdot),0)}{B}.
\]

If you establish that \(g\) is holomorphic on a disc containing the closed radius-\(r\) disc, then:

1. factor the coefficient recursively:
   \[
   \operatorname{polyCoeff}_{d+1}(r,F,(\gamma_0,\gamma'))
   =\operatorname{discCoeff}(g,r,\gamma_0);
   \]
2. apply `discCoeff_eq_iteratedDeriv_div`;
3. use the pointwise identity above as an eventual equality near zero;
4. move the constant \(B^{-1}\) through `iteratedDeriv`;
5. obtain exactly your recursive `coordDeriv` formula.

Thus the analytic obligation is **holomorphy of the coefficient as a function of the parameter**, not an arbitrary-order differentiation-under-the-integral dictionary.

### Revised work package

| Unit | Deliverable |
|---|---|
| 1 | Parameter-holomorphy gate for the circle/coefficient operator |
| 2 | Recursive factorisation of `polyCoeff`, and parameter holomorphy for tail coefficients |
| 3 | Inductive complex identity for arbitrary multi-index |
| 4 | Real-part identity and paper-facing wrapper with identified coefficient families |
| 5–6 | Integration, review fixes, documentation; contingency only |

Some of these may merge. Do not spend the contingency on commutation of partials or a general real/complex derivative library.

### The unit-1 gate

**Go** if there is a compiled parameter-holomorphy lemma that:

- uses hypotheses discharged from holomorphy on the larger open polydisc;
- works on a parameter neighbourhood containing the closed integration-radius disc;
- has a clear demonstrated route to iteration, including the needed continuity with passive parameters;
- does not ask callers for arbitrary-order derivative bounds.

A single-circle pilot is sufficient if its iteration is genuinely mechanical. A lemma only about one specially chosen integrand is not.

**Stop** after unit 1 if the proof still requires any of:

- a new hierarchy of arbitrary-order dominated-differentiation lemmas;
- extensive conversion between contour integrals and interval integrals;
- a substantial `FormalMultilinearSeries`/monomial bridge;
- derivative regularity on closed polydiscs that is not already dischargeable;
- a strengthening of the paper-facing assumptions.

The dominated-integral API you mention is relevant, but I cannot certify its exact fit at `45b0943`. The likely difficulty is not mathematical differentiation under the contour; it is packaging joint continuity, local domination, and iteration in the available API.

**R-b remains the wrong route for this programme.**

---

## 2. `coordDeriv` is an honest target—with two important qualifications

### Fixed order is sufficient

Yes: fixed-order iterated coordinate derivatives are an honest rendering of the paper’s \(\partial^\gamma F(0)\).

For holomorphic \(F\), any fixed coordinate order computes the usual mixed partial. You need not formalise order independence merely to use one convention for the notation.

Document it explicitly:

> “Mixed coordinate derivatives are taken recursively in the `Fin.cons` order. No separate permutation-invariance theorem is claimed.”

Your recursion differentiates the **tail coordinates first and the head coordinate last**. That is perfectly acceptable; spell out the order rather than leaving “along `Fin.cons`” ambiguous.

The base case should evaluate \(F\) at the unique empty vector. The theorem should use
\[
\gamma! = \prod_i(\gamma_i!),
\]
not the factorial of the total degree.

Useful sanity checks are:

- dimension zero;
- \(\gamma=0\), giving \(F(0)\);
- dimension one, recovering the existing theorem;
- a monomial, including a genuinely mixed multi-index.

### Ordinary `iteratedDeriv` is appropriate

There is no need to introduce `iteratedDerivWithin` at the origin. The functions are holomorphic on an **open neighbourhood** of zero, and derivatives are local. Your existing use of `Filter.EventuallyEq.iteratedDeriv_eq` is precisely the appropriate mechanism.

But preserve the radius margin. The one-variable theorem supplied assumes differentiability on the **closed** radius-\(r\) ball. Proving parameter holomorphy merely on the open radius-\(r\) ball does not directly discharge that hypothesis. Use the original \(R>r\), or an intermediate radius between them.

### Do not identify derivatives of the supplied real functions at zero without additional hypotheses

This is the most important semantic qualification.

Your current hypotheses constrain \(\xi,\eta\) only on \((0,b]^d\). They impose **nothing on their values at zero**, or elsewhere outside that box. Consequently:

- \(\operatorname{Re}F_\xi(0)\) need not equal the supplied \(\xi(0)\);
- even genuine equality \(F_\xi(u)=\xi(u)\) on the positive box does not fix this;
- derivatives of the supplied globally defined real function \(\xi\) at zero need not be those of the extension.

The safe target is
\[
\operatorname{polyRealCoeff}_\gamma
=
\operatorname{Re}\!\left(
\frac{\operatorname{coordDeriv}_\gamma F(0)}{\gamma!}
\right).
\]

These are the Taylor coefficients of the **canonical real-analytic restriction**
\[
x\longmapsto \operatorname{Re}F(x)
\]
near zero.

To identify them with derivatives of the supplied \(\xi\), require agreement on a real neighbourhood of zero, or explicitly replace \(\xi\) by that analytic representative. Do not add this extra real-derivative bridge to the compulsory sprint.

---

## 3. Headline honesty

Your proposed sentence is defensible when read together with its qualification, but I would make the distinction harder to miss.

### Recommended current hand-off wording

> **Under the paper’s polydisc holomorphy hypothesis, the Taylor-tree asymptotic expansion is formalised in every positive dimension for the original box integral, including exponent support, a cutoff-independent coefficient system, the explicit absolutely convergent collected coefficient series, the mixed moment-derivative dictionary, and remainder estimates. Input coefficients are explicit iterated Cauchy coefficients. Their several-variable identification with normalised Taylor derivatives remains unformalised.**

This is stronger and more precise than either “the bridge remains open” or an unqualified “the paper’s theorem is fully formalised.”

### After the sprint

Expose a theorem whose coefficients are **definitionally chosen or explicitly identified** as the real parts of normalised `coordDeriv`s.

The displayed primed theorem currently existentially quantifies `cξ` and `cη`; its statement does not expose their Cauchy origin. Knowing which witnesses the proof constructs is not a substitute for a paper-facing identification theorem.

Prefer a wrapper of the form:

- define the normalised derivative families;
- prove their weighted summability;
- obtain `∃ C, TaylorTreeConclusion ...` for those specific families;
- identify the family integral with the original integral.

### Accompanying non-claims

Keep these explicit:

1. **No derivative claim about arbitrary values of \(\xi,\eta\) outside the matching box.**
2. **No separately exposed fully expanded multi-index absolute-convergence theorem**, if only the collected outer series is exposed.
3. **Candidate support is not a nonvanishing or sharpness theorem.**
4. **Cutoff independence means independence from the spectral truncation threshold \(L\)**. It does not automatically mean that the displayed rescaled coefficients are independent of \(b\).
5. No resolution theorem, general-domain theorem, Mellin continuation, exact pole-order theorem, or posterior weak-convergence theorem follows merely from this completion.

Also audit the asymptotic-variable dictionary. The historical completion text says that `N` is the paper’s \(\sqrt n\), while the newer material uses sample-size-style exponents and `boxScale`. That may simply reflect different programmes’ conventions. **State the dictionary separately for each headline**, using the actual definition of `origPhaseIntegral`; do not let the historical convention silently migrate.

---

## 4. What next? My ranking

**The default answer after the identification sprint is: stop here, publish the hand-off, and close this programme.**

| Rank | Candidate | Rough budget | Go/no-go gate |
|---|---|---:|---|
| 1 | **(b) Bounded derivative identification** | 4–6 units | Parameter-holomorphy gate after unit 1 |
| 2 | **(a) Release and close** | 1–2 units | Current milestone builds; claims and stale status text reconciled |
| 3 | **(e) Posterior weak convergence, separately authorised** | 1 reconnaissance + 3–10 implementation | A concrete theorem route for probability measures and normalisation is identified before implementation |
| 4 | **(f) A second concrete Taylor-tree example** | 2–5 units | The intended coefficient and its nontriviality are calculated on paper before Lean work |
| 5 | **(d) Boundary/Δ tail and non-box domains** | 2 reconnaissance; perhaps 8–20+ scoped implementation | A precise domain decomposition and quantitative tail lemma are fixed |
| 6 | **(c) Resolution-based §4.3 application** | 2–3 reconnaissance; perhaps 15–30+ with external chart data | All external geometric input is stated, and the result adds materially to existing chart assembly |

These are planning ranges, especially speculative for (c) and (d).

### Why posterior weak convergence ranks above more analytic infrastructure

It closes a clear statistical interpretation gap in an already assembled example. It is a different, useful theorem—not another layer of notation over the same analytic conclusion.

Reconnaissance should compare:

- an existing MGF/Curtiss or characteristic-function route;
- direct bounded-continuous-test-function convergence of the explicit normal-crossing posterior.

Do not assume the fixed-\(\theta\) MGF results automatically supply a convenient Lean weak-convergence theorem.

### What a second example should accomplish

An example is worthwhile if it validates a genuinely nonconstant phase contribution or a next-order logarithmic coefficient. A numerical check is supporting evidence, not a formalisation milestone.

Distinguish two goals:

- demonstrating a nonzero \(p\ge1\) fluctuation contribution;
- demonstrating a genuinely infinite collected series at a fixed spectral exponent.

A simple one-dimensional polynomial example may accomplish the first without accomplishing the second. For the latter, mixed-ratio geometry with tangential fluctuation is a more natural test.

### What not to do

Do not let “finish §4” become an umbrella authorisation for:

- formal resolution of singularities;
- unrestricted general domains;
- complex Mellin continuation;
- a general multivariate analytic-combinatorics library.

Those are separate programmes with different risk profiles. An externally assumed resolution atlas can support an honest conditional theorem, but that is not a formalisation of the geometric existence result.

---

## 5. Stage 7 hand-off flags

### `SliceHolo`: keep it internal

This is a sensible proof interface, not a defect. The public theorem should continue to take ordinary holomorphy on the larger open polydisc.

Document the adapter chain:
\[
\text{holomorphic on }D_R
\;\Longrightarrow\;
\texttt{SliceHolo}\text{ at }r<R
\;\Longrightarrow\;
\text{Cauchy reconstruction and coefficient bounds}.
\]

Do not describe `SliceHolo` as merely “separate holomorphy”: it also packages continuity and boundary-slice conditions.

### Torus bounds versus closed-polydisc bounds

The contour coefficient estimate naturally uses a **torus bound**. A closed-polydisc bound is a convenient stronger hypothesis obtained by compactness inside \(D_R\).

Do not imply that a torus bound controls the whole closed polydisc unless that maximum-principle step has been formalised. There is no need to add it just to sharpen the wording.

### Real-part matching

Preserve this generality, but distinguish:

- extension of real data by complex-valued equality;
- agreement only after taking real parts;
- the canonical analytic continuation to the origin.

For real-part matching, complex Taylor coefficients themselves need not be real. Their real parts are the relevant coefficient family.

### Totalised contour integrals

Totalisation is not a mathematical gap if all substantive uses establish the needed regularity. Nevertheless, the hand-off should identify where continuity/integrability licenses:

- linearity and factor extraction;
- norm bounds;
- exchange with sums;
- any parameter differentiation.

The finishing sprint’s parameter lemma deserves particular scrutiny here. An algebraic expression involving a totalised integral is not, by itself, an analytic coefficient theorem.

### Documentation has fallen behind the mathematics

The excerpt still contains historical “not formalised” claims for the analytic bridge and other now-completed work. Preserve the historical normal-block completion statement, but label it explicitly as historical and add a current successor-completion statement.

A reader should not have to reconstruct units 240–265 to discover which qualifications remain.

---

## Bottom line

**Freeze now; attempt the derivative identification with a six-unit ceiling; stop immediately if the parameter-holomorphy gate fails.**

Use the fixed-order recursive derivative target. Exploit the induction hypothesis as a local identity, rather than proving arbitrary-order differentiation under the integral. Expose the resulting coefficient identification in the public theorem, and keep derivatives of the canonical analytic representative distinct from derivatives of arbitrary real functions matching only on the positive box.

After that, **close the Taylor-tree programme**. Posterior weak convergence is the strongest separately authorised successor; §4.3 and general-domain work are not natural “last finishing touches.”
