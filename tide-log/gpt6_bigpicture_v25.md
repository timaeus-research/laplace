## Recommendation: stop theorem development in this seabed

**Choose (A), with a small, bounded (G) close-out if needed.** Declare the **agreed §4 normal-block programme complete**, not §4 of the paper fully formalised.

Consult #24 set a sensible stopping condition: hand-off, one bounded end-to-end example, optionally E2, then freeze. You have now met that condition, including independent review and the necessary wording corrections. There is no newly exposed mathematical defect that justifies moving the finish line.

“Keep going on auto” should mean exercising autonomous judgement, including declaring a completed work package complete—not finding an indefinitely renewable supply of adjacent theorems.

The useful distinction is:

* **Complete:** the scoped normal-block programme, with its assembly machinery, statistical example, and Abelian coefficient bridge.
* **Not claimed:** full Taylor-tree expansion, general meromorphic continuation, the remaining boundary/fluctuation results, or the resolution-based SLT application.

The out-of-scope list should remain a scope boundary, not become a backlog that this programme is implicitly obliged to exhaust.

## Ranking

The estimates below are planning estimates, not conclusions from inspecting the repository or current Mathlib APIs.

| Rank | Candidate | Recommendation | Incremental units |
|---|---|---|---:|
| 1 | **A — stop** | **Go now.** Freeze the mathematical scope. | 0 |
| 2 | **G — bounded consolidation** | Go only for release hygiene; avoid broad refactoring. | 0–2 maintenance units |
| 3 | **B — posterior weak convergence** | Best optional successor, but not needed to complete this programme. | 1 reconnaissance unit; 3–6 additional if infrastructure fits, 6–10 for a small direct route |
| 4 | **E — bare-monomial complex pole statement** | Small, legitimate successor; lower payoff after XXI. | 2–4 for rational continuation/pole order; full Laurent packaging may exceed this |
| 5 | **D — concrete next-order term** | Only under a restricted amplitude, preferably \( \rho\equiv1 \). No-go as presently suggested for arbitrary continuous \(\rho\). | 4–7 restricted; general continuous case has no such blanket rate |
| 6 | **C — charted example** | Defer to a separately chartered coordinate-change/resolution programme. | 4–8 for an elementary coordinate change if plumbing exists; 10–20+ for genuine chart assembly |
| 7 | **F — general random amplitudes** | No-go without a concrete downstream consumer. | Requires fresh scoping; do not authorise an open-ended unit budget |

Here are the gates I would apply.

## A/G: finish without reopening the programme

The close-out should establish only that the deliverable is reproducible and its boundaries are unambiguous:

1. **Preserve `d65d48b` as the reviewed mathematical baseline.** Any later maintenance commit should be distinguishable from it.
2. Ensure the intended release location contains the final hand-off material—not merely a staging copy.
3. Run the clean build and existing reference/index checks.
4. Put a short completion statement at the top of the hand-off, with explicit nonclaims:
   * XX–XX'': fixed-\(\theta\) MGF convergence, not a formalised posterior weak-convergence theorem;
   * XXI: Abelian coefficient limit, not general meromorphic continuation or an exact-pole-order theorem;
   * signed-weight results versus genuine-prior results.
5. Mark the remaining paper material **“outside the completed work package.”**

**Gate:** if consolidation would rename public lemmas, reorganise major imports, merge files extensively, or require substantial re-review, stop. Those are not release hygiene.

Refreshing the growth visualisation is harmless if mechanical, but it is not a completion criterion. Likewise, cosmetic duplicates are not a reason to disturb a reviewed library.

**Budget:** one short close-out pass, no new mathematical headlines.

## B: the only extension I would seriously consider next

This is the strongest runner-up because it closes a real interpretive gap in the statistical example. It would replace an MGF-level approximation with an actual statement about posterior probability laws.

But there are two distinct projects hiding here:

1. **Apply an existing convergence theorem** to the MGF results.
2. **Develop probability infrastructure** sufficient to obtain that theorem.

Only the first, or a short model-specific direct proof, belongs in a small successor task.

### First specify the exact theorem

For a genuine prior, define the posterior pushforward \(\nu_{n,z_n}\) under
\[
x\longmapsto \sqrt n\,x_0x_1.
\]
Prove, for deterministic \(z_n\to z\),
\[
\nu_{n,z_n}\Rightarrow N(z,1).
\]

Do **not** silently bundle in random-measure convergence, uniformity in \(z\), total variation, rates, or a posterior centred at the observed statistic. These are additional statements.

In particular, the deterministic phase theorem does not by itself constitute a formalised convergence-in-distribution theorem for random posterior measures under the actual data sequence. That needs its own topology, measurability, and transfer argument.

### Go/no-go gate

Spend at most **one reconnaissance unit** establishing one of:

* a usable MGF convergence theorem with verified hypotheses; or
* a short direct bounded-continuous-test-function argument using the existing normal-block asymptotics.

`Measure.ext_of_charFun` alone is not enough: uniqueness of characteristic functions is not a convergence theorem. I would not assume a suitable Lévy/Curtiss route exists without checking its actual API.

For this particular model, **inspect the direct test-function route before building generic MGF infrastructure**. The likelihood already supplies Gaussian damping; the substantive question is whether the existing asymptotics accept the needed test amplitudes, possibly after truncation.

**No-go:** new generic tightness theory, substantial complexification of the kernel, or a library-level MGF continuity development.

**Cap:** approve a further 3–6 units only after the proof route is demonstrated. If the direct route instead needs 6–10, make that an explicit new project, not a small post-freeze amendment.

## E: worthwhile only as a sharply labelled bare case

For \(\eta=1\), the complex object is explicitly rational:
\[
\zeta(q)=\prod_i\frac{1}{2k_iq+h_i+1}
\]
on the integral’s convergence domain, with the appropriate coordinate conventions.

The useful small theorem is:

* equality with the integral in its convergence half-plane;
* the displayed rational function gives a meromorphic continuation;
* its pole at \(q=-\lambda\) has order \(m\), when \(m>0\);
* the leading coefficient matches XXI.

This does connect literally to “poles of \(\zeta\).” However, **it does not materially close the gap to continuation for general amplitudes**. Keep “bare monomial” prominent in the name and hand-off.

**Gate:** use rational-function/local-factorisation machinery. Do not require a general Laurent-series framework merely to express the result.

**Estimate:** 2–4 units for that narrow statement if the relevant APIs fit. A full Laurent expansion is additional packaging with little extra paper-facing value; I would omit it.

## D: the proposed rate needs a stronger hypothesis

This candidate needs an important correction.

For a general continuous weight with \(\rho(0)>0\), continuity supports the leading logarithmic behaviour, but **does not generally give a bounded subleading remainder**, hence does not justify a universal \(O(1/\log n)\) posterior correction. Slowly varying departures from \(\rho(0)\) can accumulate along the product fibres.

The “\(2\log(1/|t|)\) plus smooth part” description is safe for specially chosen weights, not for arbitrary continuous weights in the current headline.

A clean successor would take **\(\rho\equiv1\)**. Then the product-coordinate density is explicitly logarithmic, and one can target, for fixed \(z,\theta\),
\[
M_n(\theta)
=
e^{z\theta+\theta^2/2}
+\frac{C(z,\theta)}{\log n}
+o\!\left(\frac1{\log n}\right),
\]
with the precise coefficient derived from the Gaussian/logarithmic integrals.

**Gate:** first derive the coefficient and remainder on paper, including the \(\log N=\tfrac12\log n\) convention. Decide whether the theorem concerns evidence, the numerator, or the normalised MGF; these are not interchangeable budgets.

**No-go:** retaining arbitrary continuous \(\rho\), or adding random/uniform phase control to the same task.

This would be interesting new mathematics in the formalisation, but it starts a **next-order programme** immediately after a leading-order programme has been completed. That is why I would not do it now.

## C: first distinguish a coordinate change from a blow-up

The suggested examples do not automatically exercise genuine resolution:

* \(x_0^2x_1\) is already monomial.
* \(x_0^2(x_0-x_1)^2\) becomes a normal-crossing expression under the invertible linear change
  \[
  u=x_0,\qquad v=x_0-x_1.
  \]
  That is a useful coordinate-change example, but not a blow-up.

The latter may still test Jacobians and transformed domains. It should be advertised accordingly.

**Gate:** identify exactly which previously unexercised assembly hypotheses the example discharges. If it only changes exponents or contributes a constant Jacobian, its marginal value is limited.

A genuine blow-up example brings chart domains, exceptional sets, overlap accounting, and transformed amplitudes into play. That is a coherent next programme, but not a credible tiny epilogue. Retain the **10–20+** warning.

## F: no new abstraction without a consumer

The completed example already demonstrates that the deterministic analytic machinery can support a meaningful statistical result. General random amplitudes should wait until a named model or theorem cannot be handled cleanly without them.

**Gate:** require a concrete downstream statement and show why existing deterministic results plus probabilistic transfer are insufficient. Until then, no-go.

## Final direction

My instruction would be:

> **Freeze the scoped §4 normal-block programme. Perform only bounded release hygiene, publish the completion statement and scope boundary, and stop adding theorems here. Record B as the preferred separately authorised successor.**

The programme now has the right shape for a successful deliverable: general machinery, an assembled statistical example, a coefficient dictionary, independent reviews, and honest limitations. Another adjacent result is possible; it is not necessary.
