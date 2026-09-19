## 1. Verdict and precise statement shapes

**G, E, and Z are correct. R and N are correct in your original globally smooth setting, with two qualifications:**
- extending agreement from smooth to continuous observables needs an additional argument—not just the existing scalar-gauge lemma;
- positivity of a normalization window’s integral is not, by itself, enough to justify every claimed normalized/unnormalized equivalence.

### G: yes

A useful interface is:

> If \(K\) is continuous, nonnegative, has a second-order Taylor expansion near \(p\), and \(K(p)=0\), and \(\psi\) is continuous, compactly supported, nonnegative, and equals \(1\) near \(p\), then
> \[
> \exists \kappa>0,\ T>0,\quad
> \forall t\ge T,\qquad
> \kappa t^{-d/2}\le I_K(\psi,t).
> \]

“\(C^2\) near \(p\)” is an unambiguous sufficient regularity hypothesis. The actual local hypothesis needed by the integration lemma is simply
\[
K(w)\le A\|w-p\|^2
\]
on a ball.

I would expose **both** interfaces:
1. lower bound from a local quadratic upper bound;
2. lower bound from nonnegativity and local \(C^2\) regularity.

For the scalar-gauge API, also supply an integer-power corollary
\[
\kappa t^{-n}\le I_K(\psi,t),
\qquad n\in\mathbb N,\ n\ge d/2,\quad t\ge1.
\]
This avoids dragging real powers through the subsequent algebra.

### E: yes

For an integrable compactly supported \(\psi\), the operative hypothesis is
\[
L\ge\delta>0\quad\text{on }\operatorname{supp}\psi.
\]
Then, for \(t\ge0\),
\[
|I_L(\psi,t)|
\le \|\psi\|_{L^1}e^{-\delta t}.
\]

Thus the moment, and its product with any eventually polynomially bounded scalar function, is SuperPoly. No regularity of that scalar function is needed.

### Z: yes

A clean theorem statement is:

> \(L_1,L_2\) are globally continuous and nonnegative, satisfy a local quadratic upper bound at each of their respective zeros, both zero sets are nonempty, and projectively agree on smooth compactly supported observables. Then their zero sets coincide.

Global \(C^2\) is a convenient wrapper. **Global continuity plus \(C^2\) near the zeros is enough.** Continuity away from zeros supplies the positive gap used in E.

The genuinely essential regularity input is a **polynomially visible anchor at every zero**, not specifically \(C^2\). For instance, a local estimate
\[
L(w)\le A\|w-p\|^\alpha
\]
gives an anchor of order \(t^{-d/\alpha}\).

Both-zero-sets-nonempty is the right natural nondegeneracy assumption for this theorem. It is sharp as a general guarantee: \(L_2=L_1+c\) gives exact projective agreement with \(C=e^{-ct}\), but can remove all zeros of \(L_2\). Of course, it is not logically necessary in every individual example—both zero sets could be empty and hence equal.

There is **no issue with negative or nonmeasurable \(C\)**. All estimates involving \(C(t)\) are pointwise in \(t\); you never integrate \(C\). In particular,
\[
|C(t)|I_1(\psi,t)
\le |I_2(\psi,t)|+|R_\psi(t)|
\]
gives the upper polynomial bound without a sign assumption.

### R: yes for smooth tests immediately; continuous tests need one more lemma

From an agreement-region bump,
\[
I_1(\psi_0)=I_2(\psi_0)=A,\qquad
R_{\psi_0}=-(C-1)A.
\]
G discharges `hanchor_low`, so your existing algebra gives
\[
C-1\in\mathrm{SuperPoly}.
\]

Then, **for every observable covered by the projective hypothesis**,
\[
I_2(\phi)-I_1(\phi)\in\mathrm{SuperPoly}.
\]
Thus the immediate conclusion is for \(C_c^\infty\), not automatically \(C_c^0\).

However, with globally smooth losses, the continuous-test conclusion is indeed true. Here is a useful strengthening that proves it.

Write
\[
a_t=e^{-tL_1},\quad b_t=e^{-tL_2},\quad D=L_2-L_1.
\]
For \(t\ge0\),
\[
D(a_t-b_t)\ge0,\qquad
|a_t-b_t|\le t|D|,
\]
and consequently
\[
|a_t-b_t|^2\le tD(a_t-b_t).
\]

Given a compact \(K\), choose a smooth compactly supported \(\eta\) with \(\eta=1\) on \(K\). Exact smooth-test agreement applied to the **fixed smooth observable** \(\eta^2D\) gives
\[
E(t):=\int \eta^2D(a_t-b_t)\in\mathrm{SuperPoly},
\qquad E(t)\ge0.
\]
Therefore
\[
\int_K|a_t-b_t|
\le \operatorname{vol}(K)^{1/2}\sqrt{tE(t)}
\in\mathrm{SuperPoly}.
\]

This proves **local total-variation agreement beyond all orders**, hence agreement against every continuous compactly supported observable—and even every bounded measurable compactly supported observable.

I would formalize that as a separate theorem. If R is meant to inherit only the \(C^2\) hypotheses of Z, rather than the original \(C^\infty\) setting, do not silently use this argument: \(\eta^2D\) must belong to the tested observable class.

Finally, agreement does cover observables far from the common analytic zero. But the parenthetical “both moments are themselves SuperPoly” requires that the compact support avoid **both entire zero sets**, not merely the particular anchor zero.

### N: yes, subject to normalization bookkeeping

Under the stated smoothness and analyticity hypotheses:

1. Z identifies the zero loci.
2. The merged theorem gives germ equality at every common zero.
3. Taking the union of the resulting neighborhoods gives an open \(U\) containing the common zero locus with \(L_1=L_2\) on \(U\).
4. One zero supplies an anchor for R.
5. R gives scalar rigidity and exact agreement, with the continuous-test extension above if desired.

For the positivity question:

- **Once projective agreement with \(C=Z_2/Z_1\) is available**, positivity of \(Z_1\) is enough to define the ratio and apply R. You do not need a polynomial lower bound on that particular denominator.
- **Positivity alone does not imply polynomial control of \(1/Z_i\)**, nor does it justify an unrestricted equivalence between normalized and projective SuperPoly agreement.

Indeed,
\[
\frac{I_2}{Z_2}-\frac{I_1}{Z_1}
=\frac{I_2-(Z_2/Z_1)I_1}{Z_2}.
\]
For a fixed compactly supported window, nonnegative losses make \(Z_2\) bounded, so **normalized SuperPoly agreement implies projective agreement**. The converse requires control of \(1/Z_2\).

A positive window supported away from all zeros can have exponentially small \(Z_2\). To get the two-way equivalence, assume the window is nonnegative and positive near some zero; G then supplies the required polynomial lower bound.

## 2. Where analyticity enters

**Only in obtaining local equality from the merged theorem.**

- G: local quadratic control.
- E: a positive gap.
- Z: continuity and polynomial anchors.
- Scalar rigidity in R: local equality plus one polynomial anchor.
- Smooth-test gauge removal: bounded moments.
- Continuous-test extension: smoothness of \(L_2-L_1\), not analyticity.
- N: analyticity enters through germ identification.

It is therefore worth making R completely independent of analyticity:

> `projective_agreement + local_eq_at_zero + anchor ⇒ scalar_rigidity + exact_agreement`.

Then expose an analytic corollary that supplies `local_eq_at_zero`.

## 3. Paper headline and functions versus formal series

Yes: **“projective agreement forces exact agreement beyond all orders”** is a strong and appropriate headline.

I would qualify it as:

> **At a common analytic zero, projective agreement fixes its own scalar gauge.**

This cleanly communicates the role of anchoring. In that regime, normalized and unnormalized identifiability coincide **modulo SuperPoly errors**. They do not become literally identical notions outside that regime:

- additive constants remain a genuine normalized ambiguity without zero-level anchoring;
- exact agreement here means beyond-all-orders agreement, not equality of the integrals;
- it does not imply global equality of the losses;
- denominator control still matters when translating between normalized functions and formal quotients.

For formal series, state the bridge explicitly. Equality of full asymptotic expansions implies SuperPoly difference when the expansion scale and remainder theory reach arbitrarily negative powers. Equality of a merely selected or truncated formal expansion does not.

Likewise, formal division by \(Z\) needs an appropriate nonzero leading term or an analytic estimate controlling \(1/Z\). G is exactly the useful bridge for a window seeing a zero.

## 4. Nearby targets worth adding

### (a) Z with continuous observables

Yes, and the proof is unchanged: its chosen bumps are continuous compactly supported observables too.

For the primary theorem, however, the smooth-observable assumption is **weaker as an agreement assumption** and already sufficient. I would keep that primary and make the continuous-observable version a short wrapper.

### (b) Two-sided scalar tameness—and eventual positivity

This is especially useful. Before proving zero-locus equality, you can already prove
\[
\exists c,A>0,\ T,\quad
\forall t\ge T,\qquad
c\,t^{-d/2}\le C(t)\le A\,t^{d/2}.
\]

For the upper bound, use a bump at a zero of \(L_1\).

For the lower bound, use a nonnegative bump \(\psi_q\) at a zero of \(L_2\):
\[
C(t)I_1(\psi_q,t)
=I_2(\psi_q,t)-R_{\psi_q}(t)
\ge \frac{\kappa}{2}t^{-d/2}.
\]
Since \(I_1(\psi_q,t)>0\) and \(I_1(\psi_q,t)\le M\), this gives both eventual positivity and the lower bound.

**Suggested proof organization:** establish tameness first, then prove Z using E. A mismatch gives an exponentially small moment on one side and a polynomial lower bound on the other. This makes the two inclusions more uniform.

### (c) Different windows

Distinguish two conventions.

**Only denominators change:**
\[
I_1(\phi)/Z_1,\qquad I_2(\phi)/Z_2,
\quad Z_i=\int\chi_i e^{-tL_i}.
\]
If agreement holds for all the same unwindowed observables, the argument still works. A common window is not essential; boundedness and well-defined denominators suffice for the normalized-to-projective direction.

**Numerators are also windowed:**
\[
\frac{\int\phi\chi_i e^{-tL_i}}{\int\chi_i e^{-tL_i}}.
\]
Then neither the same scalar conclusion nor global visibility follows automatically. For example, \(\chi_2=a\chi_1\), \(L_2=L_1\), gives identical normalized expectations but \(Z_2/Z_1=a\). Windows can also hide zeros.

### (d) Local total variation

The energy argument above is arguably the best additional target:
\[
\forall K\text{ compact},\qquad
\int_K|e^{-tL_2}-e^{-tL_1}|
\in\mathrm{SuperPoly}.
\]
It closes the observable-class issue and gives a stronger, cleanly interpretable conclusion.

## 5. Packaging recommendation

I would separate the reusable analytic infrastructure from the headline assembly:

1. **G + E**, including integer-power anchor wrappers.
2. **Scalar tameness + Z**.
3. **R for smooth tests**, discharging the existing anchor hypothesis.
4. **N** as assembly from existing germ identification.
5. **Continuous-test/local-total-variation extension** as an explicit additional lemma or follow-up.

If approximately 450 lines is realistic with current APIs, one tide is reasonable. But do not hide the continuous-observable upgrade or the normalization equivalence inside an ostensibly algebraic corollary.

**Vote: ship G+E+tameness+Z+R+N together, with smooth-test conclusions first and the continuous-test upgrade explicitly proved rather than implicit.**