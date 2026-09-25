## Bottom line

I would **close the exact-constant item at the level of the theorem families you list**. I do not currently see a demonstrably missing constant formula. The remaining issue is **coverage**: does every regime asserted in the note admit one of those certificates, including boundary regimes?

I would **defer the general polyhedral integrability criterion**. The higher-value next step is to check the implication
\[
\text{analytic resolution with a phase record}
\quad\Longrightarrow\quad
\text{applicable asymptotic certificates}
\quad\Longrightarrow\quad
\text{the note’s final conclusion}.
\]
The first arrow is not supplied merely by exporting `TruthChartsData` and `Phase`.

One limitation matters here: I have your present inventory, not the text of the note or the exact earlier-round theorem statements. Thus below I distinguish **identified gaps** from **claims whose coverage should be audited**.

## Q1. Exact constants

### 1. No additional universal constant formula is presently justified

Your correction to round 14 is right. In this setting, asking for a separate abstract face-integral constant would mostly repackage:

- the simplex/Gamma constant;
- its partial-face transverse integral;
- the active-truth face volume/Jacobian constant;
- the degenerate-constraint variant.

I withdraw that as an independent research target.

However, a collection of constant formulas and an exhaustive classification theorem are different deliverables. In particular,
> “the worse coordinates are not spectators satisfying `specd > 0`”

is not itself a missing regime. It can mean that the proposed face or coordinate split is wrong. A zero reduced cost can enlarge the minimizing face; a negative one can invalidate the selected optimum. The question is whether another existing certificate applies—not whether the spectator theorem should be extended by simply weakening its strict inequality.

### 2. A useful endpoint test

There is one concrete boundary test I recommend checking against the active-truth inventory.

On \((0,1)^2\), take
\[
T(x,y)=xy,\qquad F(x,y)=ax,\qquad
\theta(x,y)=x^p y^q,
\]
with \(a>0\) and, for an integrable ambient weight, \(p,q>-1\). The truth push-forward density of \(e^{-tF}\theta\,dx\,dy\), for \(0<s<1\), is
\[
K_t(s)
 =s^q\int_s^1 x^{p-q-1}e^{-atx}\,dx.
\]
At the critical path \(s=\sigma/t\), \(\sigma>0\),
\[
\boxed{\quad
t^p K_t(\sigma/t)
\longrightarrow
\sigma^q\int_\sigma^\infty
u^{p-q-1}e^{-au}\,du.
\quad}
\]
Indeed, after \(u=tx\), the rescaled expression is exactly
\[
\sigma^q\int_\sigma^t u^{p-q-1}e^{-au}\,du.
\]

This is an **incomplete-Gamma boundary constant**, including when \(p=q\). It is finite for every real \(p-q\), because its lower endpoint is positive.

Why this is a good test:

- the phase scale and the truth scale meet a box boundary;
- blindly substituting into a full-Gamma constant is wrong;
- the boundary changes the transverse domain, not merely a prefactor.

I am **not asserting that your active-truth theorem misses this**. It may already produce precisely this transverse integral. If it does, a short regression closes the question. If it does not, the boxed statement is a precise, bounded missing theorem.

More generally, this is the kind of endpoint worth testing: **a surviving truncation in the transverse integral**.

### 3. The proposed endpoints need their actual definitions

I would not diagnose `β = 0` or `η = 0` from their names alone.

- If an endpoint makes two constraint rows dependent, your degenerate theorem is the relevant candidate.
- If it causes a box boundary to survive at leading order, use a boundary test like the one above.
- If it removes a growing logarithmic scale, it requires reselecting the asymptotic regime; substituting zero into a positive-scale formula is not automatically valid.
- If it means evaluating at the **zero truth fibre**, the continuity-at-\(s\ne0\) export route does not address it. Moreover, an a.e.-defined density has no intrinsically determined value at zero without additional structure.

Thus the right endpoint deliverable is a small hypothesis/coverage table, not a speculative new general formula.

### 4. Two vanishing fibre constraints

If this means a vector truth
\[
(T_1,T_2):\mathbb R^n\to\mathbb R^2,
\]
then yes: that is outside the scalar `TruthChartsData m T L'` interface described here.

It would require a two-dimensional push-forward kernel and an asymptotic along
\[
(s_1(t),s_2(t)),
\]
with potentially two truth equalities **in addition to** the phase condition. That is not the same as the existing “two constraints” consisting of phase and scalar truth.

But nothing in the section list establishes that the note claims vector truths. Unless it does, this is a new project, not a gap.

## Q2. General polyhedral integrability

**Defer it. It is mathematically useful, but currently an ornament relative to the stated consumer.**

With \(c>0\), \(\rho>0\), and ambient Lebesgue measure, the criterion you give is the natural one:
\[
C=\{d:d_j\le0\ (j\in I),\ \kappa\cdot d\le0\},
\]
and integrability is equivalent to
\[
b\cdot d<0\qquad(d\in C\setminus\{0\}).
\]

The necessity infrastructure is already substantially present. The substantial new sufficiency work would be a quantitative polyhedral/coercivity lemma, followed by integration of the resulting bound. Pointwise strict negativity must be converted into a uniform decay estimate, while separately handling the region where the exponential phase supplies decay.

That investment becomes worthwhile if you need one of:

1. automatic integrability discharge for a genuinely broader family of certificates;
2. several exponential monomials in the phase;
3. quotient profiles or additional affine constraints for which the single-scale reduction no longer settles applicability.

Under your present strict-truth result, the single-scale iff theorem already gives the relevant decision procedure. I would not build general convex-analysis machinery merely to reprove that case.

A bounded alternative, if useful, is a **consumer-facing applicability lemma** translating the existing iff into the exact hypotheses required by `TermData.vertex` or whichever profile constructor consumes it.

## Q3. What might still be uncovered?

The section list alone cannot establish another missing theorem. In particular, I would not re-list “wall crossing,” “mixed truths,” or “identifiability” as open after your report.

Here are the concrete checks that remain meaningful.

### A. Analytic hypotheses imply an applicable asymptotic decomposition

**Claim to check:** the singular-case theorem applies to every analytic input satisfying the note’s hypotheses, rather than only to inputs additionally equipped with certificates.

A schematic statement is:
```lean
analytic hypotheses →
∃ ε > 0, ∃ D : TruthChartsData m T (L ∩ {|T| ≤ ε}),
  ∃ P : D.Phase F,
    HasCertifiedAsymptoticDecomposition D P ...
```

The last predicate here is schematic, not a proposed existing name.

**Likely obstruction:** resolution yields monomial exponents and analytic units, but does not by itself supply:

- the relevant optimum and minimizing face;
- a valid independent/degenerate constraint split;
- strict spectator inequalities;
- the correct treatment of infeasible or transition regimes.

If an earlier round already constructs certificates from *arbitrary admissible chart exponent data*, this check is closed. If not, this is the most substantive potential remaining gap.

**Boundedness:** assembling existing constructors is bounded. Proving an unrestricted classification of all exponent configurations may not be.

### B. The final normalized theorem is exported from analytic hypotheses

**Claim to check:** the theorem in “The normalized formulation” is available without the user manually choosing charts and assembling certificates.

Shape:
```lean
analytic hypotheses + nontrivial nonnegative weight →
Tendsto (fun t ↦ numerator t / denominator t)
  atTop (𝓝 limitingRatio)
```
where numerator and denominator are the note’s original integrals or fibre observables.

**Likely obstruction:** not division itself—you report expectation and ratio theorems—but proving that the denominator’s dominant coefficient is positive for the analytically produced decomposition.

Possible bookkeeping includes selecting the dominant power/log pair and proving that at least one contributing chart has positive limiting mass. Nonnegative weights prevent cancellation, but do not automatically prove strict positivity.

**Boundedness:** usually a good bounded composition round, provided A is already covered.

### C. “Constructive recovery” means an actual reconstruction, not only uniqueness

**Claim to check:** does the note provide a recovery procedure beyond
\[
\text{equal observations}\implies\text{equal germs}?
\]

A suitable theorem shape is
\[
\operatorname{recoverJet}_N(\operatorname{observations}(f))
   =\operatorname{jet}_N(f),
\]
for every finite \(N\), or an explicit coefficient-by-coefficient recursion from pencil data.

**Likely obstruction:** a distinguishability or injectivity theorem need not provide the particular reconstruction claimed by the note. Conversely, if the earlier rounds already formalized the pencil inversion, nothing remains here.

If recovery differentiates a parameter-dependent asymptotic, check that it is justified by a uniform theorem or an exact identity—not by differentiating a merely pointwise limit.

**Boundedness:** finite-order algebraic reconstruction is a good bounded target. Effective computation or quantitative stability is a different, potentially much larger claim.

### D. “Why analyticity matters” has its advertised counterexample

If the section claims failure for smooth germs, the standard target is an explicit nonzero smooth germ flat at zero, together with equality of whatever observations the note says cannot distinguish it.

**Important distinction:** proving that two smooth functions have the same Taylor jet does **not** prove that they have the same exact observational data.

**Likely obstruction:** transporting flatness to the particular asymptotic or observational equivalence in the note.

**Boundedness:** an explicit flat-function example is bounded if the required remainder estimates are already available. An unrestricted smooth non-identifiability theorem may not be.

### E. The asymptotic-notation section claims more than a leading limit

Check whether it asserts only
\[
I(t)\sim Ct^{-\lambda}(\log t)^k,
\]
or also:

- an error rate;
- a full expansion;
- uniformity in a pencil parameter;
- differentiation of the expansion;
- invariance under the note’s permitted changes of scale.

Your inventory certifies leading constants, not automatically those stronger assertions.

**Boundedness:** scale-change corollaries are usually small. Full expansions and differentiated uniform asymptotics should not be smuggled into a “cleanup” round.

## Q4. Ranking the next bounded rounds

I would rank them as follows, skipping anything already explicitly closed.

1. **Note-to-Lean statement audit and final export.**  
   Match each displayed conclusion to a theorem with the same quantifiers; prioritize an end-to-end analytic-input theorem rather than another local model result.

2. **Certificate-coverage audit, then one missing constructor if necessary.**  
   Determine whether arbitrary chart data from resolution are classified; this tests the crucial resolution-to-asymptotics arrow.

3. **One critical-boundary exact-constant regression.**  
   Use the boxed \(T=xy,\ F=ax,\ s=\sigma/t\) limit to verify surviving transverse truncations without launching a general endpoint theory.

4. **Constructive recovery export, if earlier work proves only injectivity.**  
   Formalize the note’s finite-jet reconstruction and its correctness; otherwise replace this round with the precise smooth counterexample the note uses.

5. **Asymptotic-scale cleanup.**  
   Package only the scale changes, normalization conventions, and uniformity actually asserted in the final section.

I would place the general polyhedral integrability iff **below all five**. At this point, the best next contribution is likely not a stronger local integral theorem, but a precise demonstration that the existing local theorems cover—and export—exactly the note’s global claims.