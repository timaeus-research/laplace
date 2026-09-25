There is one important statement-level problem: **the support hypothesis in (3) kills the boundary trace that the regression is meant to test.** The scaling calculation itself is correct. I would fix that before extending the certificate machinery.

A second issue to audit carefully is **pointwise, rather than almost-everywhere, invariance of the exported kernels**. The displayed pushforward identity alone cannot justify evaluation along \(s=\sigma t^{-\gamma}\).

## 1. Statement audit

### (1a) Proportional families

This looks like the right stronger form, subject to the ambient finite-dimensional assumptions implicit in the file.

In particular:

- No regularity, sign, or nonvanishing assumption on \(C\) should be added merely for convenience.
- There is no apparent need for \(L_1\geq0\).
- Analyticity only at points of \(W_0\) is appropriate for a conclusion on some open neighbourhood of \(W_0\).
- Neither closedness nor nonemptiness of \(W_0\) is needed; the empty case is simply vacuous.
- Global continuity ensures the compactly supported integrals are well behaved even when \(L_1\) takes negative values.

I would retain nonnegativity of both losses in the note only if it is part of the standing definition of “loss.” Otherwise state the stronger theorem, or add:

> In fact, nonnegativity of \(L_1\) is unnecessary.

Do not strengthen the conclusion to \(C=1\): negligible changes in \(C\) can be invisible to the hypothesis.

### (1b) Analytic-input pushforward theorem

The displayed statement is a useful and substantial end-to-end theorem. Its correct description remains:

> Analytic input produces the chart system and phase; a term-measure certificate then produces the fibre-expectation limit.

It is not yet an unconditional analytic fibre-asymptotics theorem.

The geometric assumptions look coherent. In particular, \(0\in W\subseteq U_0\) already supplies \(0\in U_0\), and the nonzero-germ condition on \(FT\), together with connectedness, is a natural way to exclude identically zero analytic factors on the relevant component.

I would check four things in the supporting definitions and export lemmas.

**1. Pointwise kernel semantics.**  
The pushforward identity determines `D.totalKernel θ` only almost everywhere. Altering it at a sequence
\[
s_n=\sigma n^{-\gamma}
\]
can preserve every displayed integral identity and destroy a fibre limit.

Thus any theorem transporting the limit between chart records must use something stronger:

- pointwise agreement on an eventual punctured interval;
- an appropriate continuity theorem plus a.e. agreement; or
- a canonical pointwise kernel construction with a proved comparison theorem.

This is especially important for the claim in (3) about *every* `TruthChartsData`. It may already be handled by the record’s additional fields; it does not follow from the displayed pushforward property alone.

**2. `ENNReal.toReal`.**  
The certificate should explicitly deliver eventual finiteness of the relevant kernels and eventual positivity of the denominator. Since `∞.toReal = 0`, a real-valued ratio theorem should not obtain its apparent meaning merely from conversion to `ℝ`.

**3. Integrability against the leading measure.**  
Check that the certificate supplies integrability of both amplitudes against `C.leadingMeasure`. Boundedness does this if the relevant measure is finite, but that finiteness needs to be part of the infrastructure.

**4. The range of \(\gamma\).**  
Quantifying over every real \(\gamma\) is not wrong when the certificate carries the restrictions. But the note’s shrinking-fibre interpretation requires \(\gamma>0\). For \(\gamma=0\) the fibre is fixed, and for \(\gamma<0\) it escapes. A note-facing corollary with `0 < γ` would make the intended scope clearer.

Some hypotheses are stronger than the compactly localized result needs—global continuity/nonnegativity of \(F\), and explicit global bounds on continuous compactly supported amplitudes—but these are API choices, not statement errors.

### (3) Critical-boundary regression

#### The formula and lower endpoint are correct

Putting \(u=tx\) in
\[
\int_{2\sigma/t}^{1/2}
 e^{-tax}\,(\sigma/(tx))^q x^p
 \psi(\sigma/(tx),x)\,\frac{dx}{x}
\]
gives exactly your normalization and lower endpoint \(2\sigma\).

For a weight equal to one on the square and \(p=q+1\), the intended constant is indeed
\[
\sigma^q\int_{2\sigma}^{\infty}e^{-au}\,du
=\frac{\sigma^q e^{-2a\sigma}}a.
\]

#### But the landed hypotheses force that trace to vanish

You assume global continuity of \(\psi\) and
```lean
∀ z, ψ z ≠ 0 → z ∈ mixLc
```
with `mixLc = [0,1/2]²`.

Consequently,
\[
\psi(v,0)=0 \qquad (0\leq v\leq 1/2).
\]
Approach \((v,0)\) from the half-plane with negative second coordinate: \(\psi\) vanishes there, hence vanishes at the boundary by continuity.

Therefore **the displayed theorem always has limit zero under its actual hypotheses**. It is a valid vanishing statement, but it does not yet test a nonzero boundary profile. In particular, “\(\psi\equiv1\) on the square” cannot satisfy those hypotheses.

The correct repair is to separate:

- the continuous observable \(\psi\), whose boundary trace may be nonzero;
- the restriction to the integration domain, supplied by `mixData` or by an indicator.

If `mixData.totalKernel` already restricts to the square as the stated formula suggests, remove `hψL`. Global continuity is more than enough; `ContinuousOn ψ mixLc` should suffice with suitable measurability bookkeeping.

#### The segment interpretation is exactly the right one

For nonzero boundary trace, the limit can also be written
\[
\sigma^p\int_0^{1/2}
v^{q-p-1}e^{-a\sigma/v}\psi(v,0)\,dv.
\]
This exhibits the boundary-supported measure directly. It is not generally a point-evaluation limit.

There is also an important classification distinction:

> A positive-dimensional support for the limiting measure does not imply a positive-dimensional face of LP minimizers.

Here the scaling is \(z_1\sim t^{-1}\), with \(z_0\) unscaled. At \(\gamma=1\), truth and phase are simultaneously active. This can be a unique LP optimum even though the surviving profile is distributed along a segment.

Thus the strict-truth vertex theorem does not cover this example. Whether `activeTruthDegenerate` does must be settled from its exact hypotheses, not its name. The likely relevant degeneracy is dependence of the active truth and phase constraints on the scaled coordinates, not a face of minimizers. The generic strict-truth, tied-cut, or tied-phase formulas should not be expected to reproduce the constant by formal substitution across an excluded boundary.

## 2. Ranked next work

### First: repair the boundary regression, then identify its certificate — (f) plus (d)

This is the highest priority because the current regression does not exercise its advertised nonzero case.

A cheap first theorem is schematically:

```lean
theorem mix_tendsto_totalKernel_boundary_one
    (hσ : 0 < σ) (ha : 0 < a) (q : ℕ) :
    Tendsto
      (fun t ↦ t ^ (q + 1) *
        (mixData.totalKernel
          (fun z ↦ ENNReal.ofReal
            (Real.exp (-(t * (a * z 1))) *
              (z 0 ^ q * z 1 ^ (q + 1))))
          (σ / t)).toReal)
      atTop
      (𝓝 (σ ^ q * Real.exp (-(2 * a * σ)) / a))
```

This assumes the square restriction is internal to `mixData`. Otherwise include its indicator explicitly.

Then prove the general continuous-observable version without ambient support in the square. After that:

1. construct the corresponding boundary `TermData`;
2. calculate its leading functional;
3. show that functional equals the segment integral;
4. derive the explicit constant through the model theorem.

That comparison is a much better coverage test than another constructor in isolation.

The unit-dependent version should have limit
\[
\sigma^q\int_{2\sigma}^{\infty}
u^{p-q-1}
e^{-u\,a(\sigma/u,0)}
\psi(\sigma/u,0)\,du.
\]
Continuity and strict positivity of \(a\) on the square give the uniform positive lower bound needed for domination. Notice that the result depends on the **whole boundary restriction of the unit**, not merely \(a(0)\).

### Second: a bounded constructive-recovery export — (a)

Do not initially promise “finite jets from exported chart data.” Specify exactly which data are observed.

The pushforward identity, leading fibre ratios, and chart exponents alone are not the same thing as sufficiently many coefficients of localized Laplace expansions. In particular, normalized expectations have an additive-constant ambiguity unless a normalization such as \(L(0)=0\) is fixed.

A useful eventual statement has the shape:

```lean
-- Schematic:
same_selected_laplace_coefficients
    (data₁ : RecoveryData L₁ k)
    (data₂ : RecoveryData L₂ k)
    (...) :
    iteratedFDeriv ℝ k L₁ p = iteratedFDeriv ℝ k L₂ p
```

But the definition of `RecoveryData` must enumerate:

- test amplitudes;
- expansion orders;
- normalization/gauge;
- admissible class of germs;
- dependence of the finite observation bound on that class.

The landed pieces supply chart generation, transport, and leading-profile evaluation. They do **not**, just from the statements presented, supply higher coefficient extraction or injectivity of the resulting finite coefficient map.

A bounded first recovery result could be one-dimensional. Fix \(k\geq1\), \(r\geq1\), and
\[
L(x)=x^{2k}+b x^{2k+r}+O(x^{2k+r+1})
\]
near zero. Choose a sufficiently small cutoff \(\chi=1\) near zero and choose \(j\in\{0,1\}\) with \(j\equiv r\pmod2\). Writing
\[
A_n=\int_{\mathbb R}u^n e^{-u^{2k}}\,du,
\]
prove
\[
t^{r/(2k)}
\left[
t^{(j+1)/(2k)}
\int \chi(x)x^j e^{-tL(x)}\,dx-A_j
\right]
\longrightarrow -bA_{j+2k+r}.
\]
The last moment is strictly positive, so this genuinely recovers \(b\). It tests coefficient extraction, signed amplitudes, and recovery without asserting an unproved general finite-determinacy bound.

### Third: an existence-and-coverage theorem for the LP — (c)

Prioritize mathematical existence and classification over an executable decision procedure.

A good staged interface is:

```lean
theorem exists_optimal_vertex
    (hfeasible : ...)
    (hcoercive : ...) :
    ∃ α, IsVertex P α ∧ IsLPMin objective P α
```

followed by a proved exhaustive classification and then:

```lean
theorem exists_termMeasureCertificate
    (hadmissible : AdmissibleExponentData ...)
    (...) :
    ∃ C : P.TermMeasureCertificate σ γ, True
```

The last theorem is the endpoint; the LP theorem alone does not produce it.

Two cautions:

- “vertex / two-scaled / face” mixes support patterns with the dimension of the optimal set. A minimizing face contains vertices; these are not automatically disjoint alternatives.
- Unique minimizers with dependent active constraints, as in this boundary example, need coverage too.

Even after this work, “hypothesis-free” should mean **free of a user-supplied certificate**, not free of admissibility, fibre-side, or nonzero-denominator assumptions.

### Fourth: minimal asymptotic-scale API — (e)

Keep this small and tied to consumers. Define
\[
S_{\lambda,m}(t)=t^{-\lambda}(\log t)^m
\]
and prove:

- eventual positivity and nonvanishing;
- multiplication;
- dominance: smaller \(\lambda\) dominates, and at equal \(\lambda\), larger \(m\) dominates;
- a scaled-limit ratio theorem.

The last item should express:
\[
f/S\to a,\qquad g/S\to b,\quad b>0
\quad\Longrightarrow\quad f/g\to a/b.
\]

Add formal division of expansions only after fixing the supported index sets and truncation convention. An arbitrary collection of real-power/log terms is not automatically a suitable formal-series algebra.

### Fifth: smooth singular counterexample, only if not already exported by `prop:flat` — (b)

This is mathematically cheap and useful for delimiting the analytic theorem:
\[
L_1(x)=x^{2k},\qquad
L_2(x)=x^{2k}+h(x),\qquad
h(0)=0,\quad h(x)=e^{-1/x^2}\ (x\ne0),
\]
with \(k\geq2\).

The target export is:

- both losses globally smooth and nonnegative;
- both have singular isolated minimum at zero;
- their germs differ;
- for every smooth compactly supported \(\phi\),
  \[
  \int\phi e^{-tL_2}-\int\phi e^{-tL_1}
  \quad\text{is superpolynomially small}.
  \]

If `prop:flat` already implies this, add the explicit instantiation rather than another general theorem. Normalized invisibility can then follow using a positive reference amplitude and a polynomial lower bound for its denominator.

I would move this above the LP project if the note currently makes an unsupported claim that analyticity is essential at singular minima.

## 3. Top-item obstruction and cheapest bounded step

The immediate obstruction is **the amplitude API, not the asymptotic analysis**: global continuity plus support in a closed box excludes precisely the boundary values you want to observe.

The cheapest bounded step is:

1. prove internally that the present `hψL` forces `ψ ![v, 0] = 0`;
2. add the nonzero constant-weight regression with domain restriction handled separately;
3. only then generalize to arbitrary continuous boundary traces and identify `activeTruthDegenerate`.

This gives a sharp acceptance test: the repaired theorem must produce
\[
\frac{\sigma^q e^{-2a\sigma}}a>0,
\]
and that value must be recovered through the certificate route.

Finally, in “What remains,” distinguish three separate outstanding claims: **certificate existence**, **pointwise chart-independence of fibre evaluations**, and **constructive recovery from specified observable coefficients**. The landed analytic-input theorem is an important bridge, but none of those three should be described as settled merely because every displayed note statement now has a `\leanref`.