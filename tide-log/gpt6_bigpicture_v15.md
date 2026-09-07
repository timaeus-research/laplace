## (a) Fidelity and mirror annotation

**Yes:** on the statement you supplied, `monomialBoxReal_isEquivalent'` is a faithful instance of the normal-moment asymptotic in the **equal-ratio, positive-orthant, unit-cutoff, constant-amplitude case**.

The identification is
\[
d=m_{\mathrm{Lean}}+1,\qquad
m_{\mathrm{paper}}=d,\qquad
\lambda_i=\frac{h_i+1}{2k_i}=\lambda,
\]
giving
\[
M(N)\sim
\frac{\Gamma(\lambda)\beta^{-\lambda}}
{(d-1)!\prod_i 2k_i}
N^{-\lambda}(\log N)^{d-1}.
\]

### Normalisation checklist

- **\(2k\), not \(k\): correct.** The exponential contains \(\prod x_i^{2k_i}\), and the substitution produces both the ratio \((h_i+1)/(2k_i)\) and the factor \(1/(2k_i)\).
- **\(\beta\): correct.** Replacing \(N\) by \(\beta N\) contributes \(\beta^{-\lambda}\); the fixed logarithmic shift does not change the leading coefficient.
- **Taylor index:** absorbing \(\gamma\) into \(h\) is correct for the normal Taylor monomial. It does **not** incorporate its Taylor coefficient, factorial convention, or tangential amplitude.
- **Half-open versus closed box:** immaterial for Lebesgue integration; the difference is a finite union of coordinate faces of measure zero. This deserves a sentence, not a new limitation.
- **Boundary versus interior coordinates:** the theorem concerns the positive orthant only. It does not assert the paper’s interior-coordinate projection or signed-chart assembly. When that is added, distinguish the paper’s projector
  \[
  \frac{1+(-1)^a}{2}
  \]
  from the raw full-interval identity
  \[
  \int_{-b}^{b}x^a F(x^{2k})\,dx
  =(1+(-1)^a)\int_0^b x^aF(x^{2k})\,dx.
  \]
  Whether the extra factor \(2\) is already accounted for is a chart-normalisation question.
- **Positive exponents and nonempty normal block:** the current theorem requires every \(k_i>0\) and \(d\ge1\). Coordinates with \(k_i=0\) are spectators, not covered normal coordinates.
- **Parameter:** a real-\(N\) limit at infinity implies the paper’s integer-\(n\) limit by restriction.

### Recommended placement

1. Put a **definition-level** `\leanref` on `eq:normal_moment_defn`, targeting `monomialBoxReal`, with the adjacent scope remark explaining the specialisation. Do not let that reference imply that the entire displayed family has been formalised.
2. After the paragraph containing `eq:a_minus_m_explicit`, insert a mirror-only **Formalised scope** remark containing a separate, labelled equation for the equal-ratio asymptotic.
3. Attach the asymptotic theorem’s `\leanref` to **that new bounded equation**, not to the commented-out source formula or the outdated headline theorem.
4. Leave the source warnings intact. Do not silently uncomment the paper’s formula.

Suggested compact text:

> **Formalised scope.** For a nonempty normal block of boundary-type coordinates, unit cutoff \(b=1\), positive integers \(k_i\), and nonnegative integers \(h_i\), the formalisation proves the following equal-ratio normal-moment asymptotic. If \((h_i+1)/(2k_i)=\lambda\) for every \(i\), then, for fixed \(\beta>0\),
> \[
> \int_{[0,1]^d}x^h e^{-\beta N x^{2k}}\,dx
> \sim
> \frac{\Gamma(\lambda)\beta^{-\lambda}}
> {(d-1)!\prod_i 2k_i}
> N^{-\lambda}(\log N)^{d-1}.
> \]
> Here the normal Taylor index may be absorbed into \(h\). Lean uses \((0,1]^d\), which gives the same Lebesgue integral. This statement does not include interior parity factors, tangential amplitudes, or the full expectation-expansion theorem.

This makes the milestone independently precise without presenting the authors’ unfinished statement as settled.

---

## (b) Mixed ratios: recommend A, simplified by a global envelope

**Recommendation: route A, using a boundedness-to-envelope lemma, then peel one nonminimal coordinate at a time.** Borrow proof structure from D where useful. Do not build general partial fractions.

The key simplification is:

> You do not need a uniform asymptotic in the extra parameter. A one-variable asymptotic, together with boundedness near zero, supplies the uniform domination automatically.

### 1. The generic envelope lemma

Write
\[
S_{\lambda,r}(M)=M^{-\lambda}(\log M)^r.
\]

Suppose \(\lambda>0\), \(r\in\mathbb N\), \(f\) is bounded on bounded positive intervals, and
\[
\frac{f(M)}{S_{\lambda,r}(M)}\longrightarrow C.
\]
Then there is \(K\ge0\) such that, for every \(M>0\),
\[
|f(M)|
\le K M^{-\lambda}\bigl(1+\max(0,\log M)\bigr)^r.
\tag{E}
\]

For the intended application, one can initially use the simpler assumption that \(f\) is globally bounded on \(M>0\). The weighted exponential box integrals satisfy
\[
0\le W(M)\le\prod_i\frac1{\lambda_i}
\qquad(M>0).
\]

Proof of (E):

- beyond a fixed threshold, use boundedness of the normalised ratio;
- below that threshold, use boundedness of \(f\) and \(\lambda>0\).

No two-sided asymptotic estimate is needed.

### 2. The dominated-coordinate transfer lemma

The central reusable theorem should say:

> If \(q>\lambda>0\), \(f\) is measurable and bounded on bounded positive intervals, and
> \[
> \frac{f(M)}{M^{-\lambda}(\log M)^r}\to C,
> \]
> then
> \[
> \frac{\displaystyle\int_{(0,1]}t^{q-1}f(Nt)\,dt}
> {N^{-\lambda}(\log N)^r}
> \longrightarrow \frac{C}{q-\lambda}.
> \tag{P}
> \]

A schematic Lean API is:

```lean
tendsto_integral_weighted_scale_div
    (hλ : 0 < λ) (hq : λ < q)
    (hf : Measurable f)
    (hbounded : ...)
    (hlim :
      Tendsto (fun M => f M / (M ^ (-λ) * log M ^ r))
        atTop (𝓝 C)) :
    Tendsto
      (fun N =>
        (∫ t in Ioc 0 1, t ^ (q - 1) * f (N * t)) /
          (N ^ (-λ) * log N ^ r))
      atTop (𝓝 (C / (q - λ)))
```

The proof is cleaner than the ratio expression in the question suggests.

For fixed \(t>0\),
\[
\frac{f(Nt)}{N^{-\lambda}(\log N)^r}\to Ct^{-\lambda},
\]
using \(Nt\to\infty\) and
\[
\frac{\log(Nt)}{\log N}\to1.
\]

For \(N\ge e\), \(0<t\le1\), envelope (E) gives
\[
\left|
t^{q-1}\frac{f(Nt)}
{N^{-\lambda}(\log N)^r}
\right|
\le K\,2^r\,t^{q-\lambda-1}.
\]
Indeed, \(\max(0,\log(Nt))\le\log N\).

The right side is integrable because \(q-\lambda>0\), and its integral is \(K2^r/(q-\lambda)\).

**Crucially, this never divides by \(\log(Nt)\) inside the dominating estimate.** It handles \(Nt<1\), \(Nt=1\), and \(r=0\) without splitting the domain.

### 3. Weighted mixed theorem

Define the real weighted integral
\[
W_{\boldsymbol\ell}(N)
=\int_{(0,1]^d}
\prod_i t_i^{\ell_i-1}
e^{-\beta N\prod_i t_i}\,dt.
\]

For nonempty \(d\), assume all \(\ell_i>0\), let
\[
\lambda=\min_i\ell_i,\qquad
J=\{i:\ell_i=\lambda\},\qquad m=|J|.
\]
Then the target is
\[
W_{\boldsymbol\ell}(N)\sim
\frac{\Gamma(\lambda)\beta^{-\lambda}}{(m-1)!}
\left(\prod_{i\notin J}\frac1{\ell_i-\lambda}\right)
N^{-\lambda}(\log N)^{m-1}.
\tag{W}
\]

Prove this by **removing a nonminimal coordinate**:

- if every coordinate is minimal, use u172–173;
- otherwise choose \(i\notin J\);
- put that coordinate first;
- apply the induction hypothesis to the remaining coordinates;
- apply (P) with \(q=\ell_i\).

Removing a nonminimal coordinate preserves both \(\lambda\) and \(m\).

For the internal theorem, I would avoid computing a minimum initially. Use explicit hypotheses
\[
\lambda>0,\quad \lambda\le\ell_i,\quad
\exists i,\ \ell_i=\lambda.
\]
Define the critical finite set by equality. Add the `min`/`argmin` wrapper afterward. This separates analysis from finite minimum bookkeeping.

### 4. Monomial assembly

Use u174’s existing arbitrary-weight substitution. The constant simplifies coordinatewise:
\[
\frac1{2k_i}\frac1{\lambda_i-\lambda}
=\frac1{h_i+1-2k_i\lambda}
\qquad(i\notin J).
\]

Thus:
\[
M(N)\sim
\frac{\Gamma(\lambda)\beta^{-\lambda}}{(m-1)!}
\left(\prod_{i\in J}\frac1{2k_i}\right)
\left(\prod_{i\notin J}
\frac1{h_i+1-2k_i\lambda}\right)
N^{-\lambda}(\log N)^{m-1}.
\]

Prove positivity of all denominators and of the final constant before constructing the `IsEquivalent` wrapper.

### Lean mechanics and likely friction

- **Integrability:** for weighted real integrals, continuity on the closed box is unavailable when \(\ell_i<1\). Dominate by \(\prod_i t_i^{\ell_i-1}\), using positive-power integrability and finite-product integration. Keep the existing ENNReal integral as the foundational object.
- **Coordinate permutation:** prove a small reusable reindexing lemma for `weightedBoxIntegral`. A swap taking a chosen coordinate to zero, followed by the existing `Fin.cons` recursion, should avoid a large subtype-product equivalence.
- **Induction:** induction on dimension, with the “all equal” branch handled directly, is likely simpler in Lean than constructing a separate recursion on \(|I\setminus J|\). Conceptually they are the same peel.
- **DCT:** work over `volume.restrict (Ioc 0 1)`. The domination is eventual in \(N\); restrict to a convenient tail if the chosen Mathlib theorem expects domination for every parameter.
- **Asymptotic interfaces:** prove the ratio-limit theorem first. Produce equivalence afterward with `Asymptotics.isEquivalent_of_tendsto_one`, respecting the current signature.

### Why not B?

B is mathematically valid, but a two-weight density alone does not stay two-weight after repeated peeling. It generates lower logarithmic powers and additional exponents, requiring a growing exact-density invariant.

There is a cleaner positive-density alternative: integrate an equal-ratio block against the remaining coordinates, obtaining a truncated-log density with a positive integral coefficient. That also admits DCT. But it introduces a new density theorem when the scale-transfer lemma already proves exactly what is needed.

**Estimate:** four substantive units if the weighted integrability and permutation infrastructure cooperate; five or six if those require separate helper units. Route C is disproportionate to this milestone.

---

## (c) Ranking the other candidates

My ordering is:

1. **Headline wrapper and mirror annotation — immediately.** Small effort, large improvement in public statement clarity.
2. **Focused statement-level review of u163–175.** Do this before extending the public claims. Audit the supplied statements and bridges, not merely the successful build.
3. **Mixed-ratio general \(d\).** Highest-value new mathematics: it reaches the actual minimum/multiplicity pattern and the explicit residue coefficient.
4. **Cutoff \(b\ne1\), then interior parity.** Cutoff is cheap after mixed ratios; parity deserves a separate normalisation check.
5. **Stochastic \(1/\log N\) regime.** Valuable, but orthogonal to closing the normal-moment statement.
6. **Taylor-tree integration.** Strategically important, but only after identifying the additional amplitude and remainder lemmas it needs.

For the review, prioritise:

- u173: constants, real-power conventions, tail normalisation, \(m=0\);
- u174–175: integrability and ENNReal-to-real bridges, product constants, \(d=1\);
- u163–164: precise extended-expectation meaning and the threshold equality case;
- u167–169: nonzero denominator constants and the scope of corner-vanishing assumptions.

### Cutoff calculation

With common cutoff \(b>0\), scaling \(x_i=bu_i\) gives
\[
M_b(N)=b^{\sum_i(h_i+1)}
M_1\!\left(Nb^{2\sum_i k_i}\right).
\]
Consequently the leading coefficient gains
\[
b^{\sum_i(h_i+1-2k_i\lambda)}
=\prod_{i\notin J}b^{h_i+1-2k_i\lambda}.
\]
This exactly matches the stated Laurent coefficient. In the equal-ratio case the leading coefficient is independent of \(b\).

### Stochastic caution

The ratio conclusion needs **joint convergence** of the appropriately normalised denominator and numerator:
\[
(A_N,B_N)\Rightarrow(A,B),\qquad \Pr(A=0)=0.
\]
Separate marginal convergence is insufficient. The continuous mapping step is then routine relative to establishing that joint expansion.

### Taylor-tree caution

The monomial theorem can replace a deterministic normal-moment backend. It does **not** replace the quadratic random-phase kernel or its \(S_{p-1}(a)\) coefficient.

Also, with mixed ratios, a general amplitude is not ordinarily evaluated at the all-coordinate origin: the nonminimal coordinates remain in the leading weighted integral. Connecting to Taylor trees therefore requires explicit amplitude/remainder control, plus cancellation and parity handling.

---

## (d) Ranked next five units

These are proposed implementation units, not a claim that every helper will fit without splitting.

| Unit | Deliverable |
|---|---|
| **u176 — `HeadlineMonomial.lean` + mirror/review checkpoint** | Public equal-ratio normal-moment wrapper; mirror-only scoped equation and references; focused statement audit of u163–175, with any corrections recorded before new extensions. |
| **u177 — `PowerLogEnvelope.lean`** | Convert a ratio limit plus boundedness near zero into envelope (E); prove fixed-positive-scale normalised convergence; include \(r=0\) explicitly. |
| **u178 — `DominatedCoordinate.lean`** | Generic peel theorem (P), integrability conclusion, ratio-limit and equivalence wrappers. Specialise once to an equal block plus one larger-ratio coordinate as a regression theorem. |
| **u179 — `WeightedMixedAsymptotic.lean`** | Weighted real/ENNReal bridge and mass bound; coordinate reindexing; induction removing nonminimal coordinates; theorem (W) under explicit minimum/attainment hypotheses. |
| **u180 — `MonomialMixedAsymptotic.lean`** | Apply arbitrary-weight substitution; simplify to the paper’s critical/noncritical denominator product; prove positivity, ratio limit, and `IsEquivalent`; add minimum/argmin and Headline wrappers, plus the corresponding bounded mirror statement. |

If u179 is too large, split out weighted integrability/reindexing rather than weakening the final statement or switching to exact partial fractions.

### Scope sentence for the next report

> Completed the deterministic positive-orthant, unit-cutoff normal-moment asymptotic in arbitrary positive dimension and for arbitrary positive monomial exponent ratios, with decay exponent equal to the minimum ratio, logarithmic degree one less than its multiplicity, and the explicit Gamma/residue coefficient; this excludes interior parity assembly, variable amplitudes, stochastic phase terms, and the full Taylor-tree expansion.

That is the natural next milestone: substantially closer to the paper’s stated normal-moment mechanism, while remaining sharply bounded and independently defensible.
