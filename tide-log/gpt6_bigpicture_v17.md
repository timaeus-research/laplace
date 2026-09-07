## (a) Architectural position and the next bridge

**The deterministic normal block is now complete at leading order, including continuous amplitudes.** That is a substantial milestone, but it is one analytic component of the paper’s geometric assembly—not yet a formalisation of `thm:expectation_expansion`.

The distinction is:

- **Established:** for the monomial normal form, the leading power, logarithmic multiplicity, and the limiting functional on continuous amplitudes; cutoff scaling; and an asymptotic equivalence when the resulting coefficient is nonzero.
- **Not thereby established:** a resolution pullback, compatible localisation and partition of unity, tubular-coordinate integration, or a full per-stratum expansion with conormal Taylor remainders.

The strongest conceptual output is that the leading coefficient is a **face-supported functional**, not generally evaluation at the all-zero normal point. Equal ratios recover the corner-evaluation formula. Mixed ratios retain integration in the noncritical normal directions.

### My top pick: (1), immediately packaged as a carefully qualified version of (6)

Tangential integration is both:

1. **Most valuable now:** it connects the completed normal analysis to the actual coefficient integrals appearing in §3–4.
2. **Tractable:** it requires parameter integration and Fubini, not new asymptotic analysis.

The resulting theorem should initially be advertised as a **fixed-coordinate, tangentially integrated normal-block theorem**. Its equal-ratio specialisation gives the desired local expression involving an integral of the leading density over tangential coordinates. Identifying that coordinate expression with
\[
\int_{S_I}c_0\,|dv|
\]
still requires the chart/density/partition-of-unity bridge.

For mixed ratios, be particularly careful: the surviving face is \(u_J=0\), not necessarily the stratum defined by *all* normal coordinates vanishing. The residual normal integral cannot simply be renamed an integral over \(S_I\).

### Relative priority of the other candidates

- **(5) Exponential localisation:** excellent small independent bridge; do it soon. The analytic gap lemma is easy, although obtaining the gap geometrically is a separate task.
- **(2) Interior coordinates/parity:** a useful and bounded extension of the normal-block interface.
- **(3) Taylor-tree backend:** worthwhile after writing an explicit dictionary of kernels, large parameters, exponent sets, and noncancellation assumptions. Do not swap backends merely because their leading formulas look similar.
- **(4) Stochastic \(1/\log N\):** valuable, but it advances a different branch. I would not interrupt the deterministic geometric assembly for it.

## (b) Tangential theorem and proof architecture

### Recommended public statement

Write \(r=m+1\), and set
\[
\lambda=\min_i\frac{h_i+1}{2k_i},\qquad
J=\left\{i:\frac{h_i+1}{2k_i}=\lambda\right\},\qquad
A(N)=N^{-\lambda}(\log N)^{|J|-1}.
\]

Let \(K\subseteq\mathbb R^t\) be compact, \(q\) integrable on \(K\), and
\[
\eta:\mathbb R^t\times\mathbb R^r\to\mathbb R
\]
continuous. Under the existing positivity hypotheses on \(k,\beta\), prove
\[
\frac{
 \displaystyle\int_K q(v)
 \left[\int_{\mathrm{unitBox}}
       \eta(v,u)\,u^h e^{-\beta N u^{2k}}\,du\right]dv
}{A(N)}
\longrightarrow
\int_K q(v)\,
  \operatorname{amplitudeCoeff}(\eta(v,\cdot))\,dv.
\]

Equivalently, spell the limit out as
\[
\operatorname{faceLeadConst}
\int_K q(v)
 \left[\int_{\mathrm{unitBox}}
   \eta(v,\operatorname{faceProj}u)\,
   \operatorname{residualWeight}(u)\,du\right]dv.
\]

Allow **signed \(q\)** and signed amplitudes. Positivity belongs to the normal reference measures, not to the test function.

A Lean-facing shape, with the existing normal-data arguments suppressed, is:

```lean
theorem tangential_amplitude_tendsto
    {K : Set (Fin t → ℝ)}
    (hK : IsCompact K)
    {q : (Fin t → ℝ) → ℝ}
    (hq : IntegrableOn q K)
    {η : ((Fin t → ℝ) × (Fin r → ℝ)) → ℝ}
    (hη : Continuous η) :
    Tendsto
      (fun N =>
        (∫ v in K, q v *
          normalAmplitudeIntegral N (fun u => η (v, u))) /
            normalScale N)
      atTop
      (𝓝 (∫ v in K, q v *
        amplitudeCoeff (fun u => η (v, u))))
```

These are suggested interface names, not claims about existing declarations.

Start with iterated integrals. Add a product-measure or concatenated-coordinate presentation as a bridge, rather than making it a prerequisite.

### Cleanest proof here: (iii), average the amplitude first

For this deterministic compact-support problem, my first choice is
\[
\bar\eta(u)=\int_K q(v)\eta(v,u)\,dv.
\]

Then:

1. Prove \(\bar\eta\) is continuous.
2. Use Fubini to identify the numerator with the normal amplitude integral for \(\bar\eta\).
3. Apply `amplitude_tendsto` **once**.
4. Use Fubini again to identify
   \[
   \operatorname{amplitudeCoeff}(\bar\eta)
   =\int_K q(v)\operatorname{amplitudeCoeff}(\eta(v,\cdot))\,dv.
   \]

This reuses the strongest completed theorem and needs no new asymptotic envelope.

The continuity argument is local in \(u\): around each \(u_0\), joint continuity bounds \(\eta\) on \(K\) times a compact neighbourhood of \(u_0\); the integrable dominator is a constant times \(|q|\). You do **not** need global boundedness of \(\eta\).

Useful helper lemmas are:

- continuity of an integral over a compact parameter set against an integrable density;
- integrability/Fubini for a bounded continuous amplitude times \(q(v)\) and an integrable normal weight;
- integrability of `residualWeight`;
- commutation of `amplitudeCoeff` with the tangential integral.

If residual-weight integrability is currently only buried inside `face_moment_eq`, expose it now.

### DCT is the best fallback—and the more general parameter interface

Option (i) is completely sound. On \(K\times\mathrm{closedCube}\), obtain
\[
|\eta(v,u)|\le B.
\]
For sufficiently large \(N\),
\[
\frac{M(N)}{A(N)}\le C,
\]
hence
\[
\left|
q(v)\frac{\int\eta(v,u)w_N(u)\,du}{A(N)}
\right|
\le BC\,|q(v)|.
\]

That is the entire uniformity argument. The weight is independent of \(v\), so there is **no separate uniform-in-\(v\) normal asymptotic theorem to prove**. The bare mass limit already supplies the eventual bound; `envelope_of_tendsto_ratio` is enough if it matches the interface.

Use only an **eventual** bound, with \(N\) sufficiently large that the normalising scale behaves properly. Do not try to establish a convenient global bound through \(N=1\).

DCT becomes preferable if you want the more general theorem:

- measurable tangential parameter space;
- continuous normal sections;
- a measurable integrable sectionwise sup-norm bound;
- no joint continuity in the tangential parameter.

I would not formalise both proof routes immediately. For the stated compact continuous problem, choose averaging unless the existing dominated-limit API makes DCT materially shorter.

### Why not rerun moment transfer on the product cube?

It works, but buys little here. Tangential coordinates should **not** be encoded as normal coordinates with \(k=0\): they do not belong in `ratioExp` or the shifted-normal-moment analysis.

With a product reference measure, their moments are simply fixed tangential moments. Fubini factors mixed test monomials into:

- an ordinary tangential moment;
- a normal moment already handled by u184.

That is a valid tensor-product extension of the transfer theorem, but unnecessary infrastructure for this bridge.

### Leading-density corollary

If all normal ratios equal \(\lambda\), the limit reduces to
\[
\frac{\Gamma(\lambda)\beta^{-\lambda}}
     {(r-1)!\prod_i 2k_i}
\int_K q(v)\eta(v,0)\,dv.
\]

This is the right local deterministic precursor to the paper’s leading-coefficient formula. A smooth density depending on both \(v,u\) can simply be included in \(\eta\).

Keep the distinction between:

- a normalised limit, valid even when the coefficient vanishes;
- `IsEquivalent`, requiring the integrated coefficient to be nonzero.

Tangential cancellation can make that coefficient zero even when individual normal sections have nonzero coefficients.

## (c) Specific targets for review v4

I would give the reviewers the following checklist.

### 1. Critical-face combinatorics in u184

Check all branches when a shift touches \(J\):

- some original minimisers survive, so the exponent stays fixed but multiplicity decreases;
- no original minimiser survives, so the new minimum strictly increases;
- shifted and previously noncritical coordinates can tie at the new minimum.

The argument must not assume the new minimising set is a subset of the old one.

Also check that zero shift on \(J\) really preserves **exactly** the original minimising set.

### 2. Positivity and mass control in u185

The constant monomial is essential: it gives convergence, hence eventual boundedness, of total mass. Check that:

- eventual nonnegativity is sufficient everywhere it is used;
- uniform approximation controls integrals through absolute values correctly;
- all polynomial pullbacks are measurable and integrable;
- cube membership is assumed only where needed, with consistent pointwise/a.e. conventions;
- the zero-dimensional case, if supported, is harmless.

There should be no hidden demand that the continuous test amplitude itself be nonnegative.

### 3. Residual-weight integrability and the meaning of “face”

For \(i\notin J\), explicitly audit
\[
h_i-2k_i\lambda>-1.
\]
For \(i\in J\), the weight is defined to be \(1\), not the generally nonintegrable formal power obtained by substituting equality.

The coefficient is represented by an ambient box integral whose critical coordinates are dummy integrations of mass one. It is **not** Lebesgue measure restricted to a lower-dimensional face.

Check endpoint and `rpow` conventions, especially wherever negative residual exponents occur.

### 4. Constants and dimension conventions

Independently recalculate:

- \(\Gamma(\lambda)\beta^{-\lambda}\);
- factorial \((|J|-1)!\);
- critical factors \(\prod_{i\in J}(2k_i)^{-1}\);
- equal-ratio case with \(r=m+1\), hence factorial \(m!\);
- `amplitudeCoeff_const` against the pre-existing mixed constant.

This is a good place for a small mixed-ratio example checked from the displayed integrals.

### 5. Public claims and cancellation

Ensure the headline exposes the face functional, not merely a definition hiding it. Check that zero coefficient yields only the corresponding little-\(o\)/normalised-zero conclusion, not a claimed next leading order.

Finally, audit every conversion between the \(N\), \(N^2\), and \(\sqrt n\) conventions across the three programmes. Powers of \(2\) in logarithmic coefficients are particularly easy to lose.

## (d) Next five units

I would use this dependency-aware order.

| Unit | Proposed content | Deliverable |
|---|---|---|
| **u188** | Compact parameter integration helpers | Continuity of averaged amplitudes; integrability and Fubini against an integrable tangential density |
| **u189** | Tangential normal-amplitude asymptotic | The integrated normalised limit and explicit integrated face coefficient |
| **u190** | Headline local leading-density coefficient | Equal-ratio corner formula, mixed-ratio face formula, and nonzero-coefficient equivalence |
| **u191** | Exponential-gap localisation | A standalone integral estimate away from the zero set |
| **u192** | Symmetric normal boxes and reflections | Bare parity formula and continuous-amplitude signed-reflection reduction |

For u191, target the reusable analytic statement:
\[
\|a_N(x)\|\le g(x),\quad f(x)\ge\varepsilon>0
\quad\Longrightarrow\quad
\left\|\int_S a_N(x)e^{-\beta Nf(x)}\,dx\right\|
\le e^{-\beta N\varepsilon}\int_S g(x)\,dx
\]
for \(N\ge0\), with appropriate a.e. hypotheses and integrability. Then derive the big-\(O\) statement. Establishing the gap on a geometric complement remains separate.

For u192, the amplitude reduction should use
\[
\eta_{\rm sym}(u)
=\sum_{\sigma\in\{\pm1\}^r}
 \left(\prod_i\sigma_i^{h_i}\right)\eta(\sigma\cdot u).
\]
Odd \(h_i\) does **not** force the full amplitude integral to vanish for arbitrary \(\eta\). It forces the bare parity cancellation; in the equal-ratio amplitude limit it can force cancellation of the corner coefficient without annihilating lower-order terms.

### Scope sentence for the report

> We have formalised the leading asymptotics of deterministic monomial normal integrals with continuous amplitudes, including mixed exponents, logarithmic multiplicity, cutoff scaling, and the face-supported leading coefficient; the next stage integrates this local block over tangential variables, without yet claiming the resolution, stratified geometric assembly, or full expectation expansion.

### Milestone report: yes, now

This is exactly the right stopping point for an author-facing consolidated report. Keep it organised by mathematical claims, not unit chronology:

- **Scope and architecture:** what the normal block supplies to §3–4, and what remains outside it.
- **Main theorem sheet:** bare mixed/equal formulas, continuous-amplitude limit, cutoff scaling, and nonzero-coefficient equivalence.
- **The coefficient correction:** critical-face interpretation, equal-ratio reduction, and the mixed-ratio counterexample.
- **Proof and dependency map:** normal moments → shifted moments → continuous transfer → amplitude headline, with theorem/file references.
- **Verification and paper synchronisation:** completed reviews, v4 status, assumptions audit, build provenance, and the tracked TeX mirror.
- **Next geometric bridges:** tangential integration, local leading-density corollary, exponential localisation, and the explicit boundary before the full paper theorem.
