## Executive assessment

The main remaining gap is **not another isolated-minimiser theorem**. It is the connection between:

1. LP minimiser geometry;
2. logarithmic multiplicity;
3. the resulting ambient coefficient measure.

Your new results substantially complete the nondegenerate, unique-minimiser part. The most useful next steps are a record-level mixed-truth example, a product-chart face-classification theorem, and parameter stability.

Two important corrections to the proposed framing:

- `Q ≥ 0` is unnecessary in `uniqueLPMin_vertex_iff`.
- For a product chart, the LP optimal face is generally a **simplex in scaling space**, not a coordinate face of the orthant. The coefficient measure lives on a corresponding coordinate face in physical space. These are different geometries.

I can audit the mathematical interfaces below, but cannot independently certify the implementations or the exact record identities without the definitions/proofs.

# A. Audit

## A1. `tendsto_fibre_expectation_lex_measure`

The statement is mathematically sound as a **finite-sum asymptotic assembly theorem**.

The ordering is correct: smaller power exponent wins, and among equal power exponents, larger logarithmic exponent wins. In particular, `hmin` correctly expresses
\[
\lambda_p\geq\lambda_0,\qquad
\lambda_p=\lambda_0\Longrightarrow k_p\leq k_0.
\]

Several interface observations:

- **No separate attainment hypothesis is needed.** `hpos` forces the selected sum to be nonzero, hence the dominant index set cannot be empty.
- **No positivity assumption on `lam₀` is needed.** This theorem is about relative asymptotic scales, not integrability of an underlying local model.
- The finite-measure and bounded-continuous hypotheses make the observable integrals legitimate.
- The nonnegative-observable interface is appropriate for the `ENNReal` kernels. A signed-observable extension would be useful eventually, but is not a prerequisite for the thesis.
- Document that `lam p` is the **complete exponent of the term kernel**. For a partial-face certificate, this may be `γp + δ * λ`, rather than the local monomial exponent `λ`.

### Two-observable certificates versus universal certificates

Keep this theorem exactly at the two-observable level. It is the right minimal assembly interface.

But distinguish two claims:

> These two observables have the displayed limits.

and

> This measure is the asymptotic coefficient measure of this term.

Only the second requires a universal certificate. For example, schematically:
```lean
structure TermMeasureCertificate ... where
  μ : Measure Ambient
  finite : IsFiniteMeasure μ
  asymptotic :
    ∀ φ, AdmissibleObservable φ →
      Tendsto (scaledTermKernel φ) atTop (𝓝 (∫ z, φ z ∂μ))
```

Then provide a wrapper that extracts `hKψ` and `hKχ`.

**Recommendation:** keep the existing theorem as the low-level lemma; use universal certificates in the note’s principal theorem and in the wall-atlas API. Pairwise certificates alone do not identify a measure.

---

## A2. `tendsto_mixedLog`

The stated analytic lemma is correct. Continuity on the closed box supplies both boundedness and the interior convergence required after the logarithmic substitution.

The coefficient is indeed one:
\[
\int_{\sigma/(\rho t)}^\rho \frac{dx}{x}
 =\log t+\log(\rho^2/\sigma),
\]
so division by `log t` has limit one.

The open interval is harmless, and only eventual positivity of the lower endpoint and eventual nonemptiness matter.

### Does it capture the mixed-truth wall term?

Yes, for the positive-quadrant local model, **with the appropriate kernel identification**.

Let the truth map be
\[
H(x,y)=xy.
\]
For the delta/coarea convention,
\[
\int \Phi(x,y)\,\delta(xy-s)\,dx\,dy
 =
 \int_{s/\rho}^{\rho}\Phi(s/w,w)\,\frac{dw}{w},
 \qquad 0<s<\rho^2.
\]

Thus, if coordinate `0` is solved, then
\[
\operatorname{solvedCoord}(s,w)=s/w,\qquad
|\partial_x H|^{-1}=1/w
\]
on the positive branch. Your proposed `q = (1,1)`, `k = 0` identification is correct under that convention.

Your lemma is written with
\[
f(x,s/x).
\]
For the displayed branch kernel, apply it to
\[
f(u,v)=\Phi(v,u).
\]
The value at the origin is unchanged.

**Crucial distinction:** this is the coarea fibre measure
\[
\frac{d\mathcal H^1}{|\nabla H|},
\]
not unweighted arclength. There is no extra square-root factor.

### Including the loss and weights

For
\[
F(x,y)=xy\,a(x,y),\qquad s=\sigma/t,
\]
the exponential on the fibre is
\[
e^{-tF}=e^{-\sigma a(x,y)}.
\]
If \(W\) includes the chart density and atlas weight, use
\[
f_{\sigma,\phi}(x,y)
 =W(x,y)e^{-\sigma a(x,y)}\phi(\rho_i(x,y)).
\]
The coefficient measure for that branch is therefore
\[
W(0,0)e^{-\sigma a(0,0)}\,\delta_{\rho_i(0,0)},
\]
provided the pulled-back factors extend continuously to the corner.

This identification is specifically the `γ = 1` scaling. For other `γ`,
\[
e^{-tF}=e^{-\sigma t^{1-\gamma}a},
\]
and the fixed-integrand mixed-log lemma is not, by itself, the answer.

### Record bookkeeping that remains substantive

Check explicitly:

1. the branch domain becomes \(s/\rho<w<\rho\);
2. the Jacobian is \(1/|w|\), with no additional normalization;
3. odd-root/sign admissibility does not double-count;
4. chart density and atlas weights are inside \(W\);
5. the physical point is the chart image of the corner.

For signed quadrants, pull back by \((x,y)=(\varepsilon_1u,\varepsilon_2v)\), with \(u,v>0\). For \(s>0\), both `++` and `--` can contribute. They need not contribute equally, and need not have the same ambient corner image. Do not insert a universal factor of two.

Also: the constant-loss simplification \(e^{-\sigma a}\) applies when \(F=H a\) on the branch under consideration. A nonnegative extension such as \(F=|H|a\) requires the corresponding absolute-value version.

---

## A3. `integrable_vertexDom_iff`

This is the expected strict-gap criterion:
\[
\eta:=\frac{r_s+1}{\kappa_s}>0,
\qquad
r_j-\eta\kappa_j>-1 \quad(j\ne s).
\]

The hypotheses correctly describe a vertex scaling with an **inactive truth constraint**. That inactivity explains why `Q`, `γ`, `D`, and `q` disappear from the criterion.

The main wording caution is:

> This is integrability of the limiting model at the specified strict-slack vertex, not an unrestricted integrability criterion for the original chart.

In particular:

- `hstrict` is essential to this interpretation.
- Equality in a residual gap is not a harmless boundary case: it generally marks a logarithmic divergence of this limiting model and calls for a different normalization.
- `hδκ` ensures a genuinely scaled coordinate.
- The stronger global assumption `hκ : ∀ i, 0 < κ i` is natural for this analytic chart class. There is no need to weaken it just because the LP theorem admits weaker hypotheses.

Given the described `limitDomain`, I see no mathematical red flag.

---

## A4. `integrable_tiedDom_twoScaled_iff`

This also matches the expected criterion:
\[
\eta>0,\qquad \theta>0,\qquad
r_j-\eta\kappa_j+\theta Q_j>-1.
\]

The hypotheses doing real work are:

- two strictly positive scaled coordinates;
- two independent active linear forms (`hΔ`);
- a nonempty limiting domain;
- positive truth-domain scale `D`;
- the decomposition \(r_S+1=\eta\kappa_S-\theta Q_S\).

There is no general requirement here that `Q ≥ 0` or `κ > 0`. In logarithmic coordinates, the active two-coordinate change of variables is governed by the nonzero determinant. Integrability is then governed by the displayed multipliers and residual exponents.

Two presentation cautions:

1. **Nonemptiness is not cosmetic.** Otherwise the zero function on an empty domain is integrable regardless of the certificate.
2. This is a **nondegenerate two-scaled theorem**, not a theorem about every truth-tied face. `Δ = 0` falls outside precisely the coordinate change that makes the criterion work.

---

## A5. `uniqueLPMin_vertex_iff`

### `Q ≥ 0` is unnecessary

The strict truth slack lets you choose every perturbation sufficiently small, regardless of the signs of `Q`.

Write \(\alpha_s=\delta/\kappa_s>0\).

To force
\[
a_s/\kappa_s>0,
\]
consider \(\alpha+\varepsilon e_s\). It remains feasible for sufficiently small \(\varepsilon>0\):

- nonnegativity is preserved;
- the loss constraint improves since \(\kappa_s>0\);
- the truth constraint stays feasible because it was strictly slack.

If \(Q_s>0\), choose \(\varepsilon\) below the slack divided by \(Q_s\). If \(Q_s\leq0\), the truth constraint does not worsen.

For the residual inequality at \(j\ne s\), use
\[
\beta=\alpha+\varepsilon e_j
       -\varepsilon\frac{\kappa_j}{\kappa_s}e_s.
\]
For sufficiently small \(\varepsilon>0\), this preserves nonnegativity and truth feasibility, and keeps \(\kappa\cdot\beta=\delta\).

Uniqueness forces
\[
a_j-\frac{a_s}{\kappa_s}\kappa_j>0.
\]

The sufficiency identity never uses `Q ≥ 0`.

**Recommendation:** remove `hQ`.

In fact, the LP statement can be weakened further: with `δ > 0`, only `κ s > 0` is needed; the other `κ j` may have arbitrary signs. That generalization is mathematically clean but less important than removing `hQ`.

---

## A6. `uniqueLPMin_twoScaled_iff`

The absence of sign assumptions on `Q` and `κ` is correct.

Because the two scaled coordinates are positive and the determinant is nonzero, small perturbations can independently change the two active constraint values.

- Increase \(\kappa\cdot\beta\), keeping \(Q\cdot\beta=\gamma\): uniqueness forces \(\eta>0\).
- Decrease \(Q\cdot\beta\), keeping \(\kappa\cdot\beta=\delta\): uniqueness forces \(\theta>0\).
- Turn on a residual coordinate while compensating in the two scaled coordinates to preserve both equalities: uniqueness forces its reduced cost to be positive.

All these are local constructions; positivity of the two scaled coordinates supplies the room needed to maintain coordinate nonnegativity.

Conversely,
\[
a\cdot\beta-a\cdot\alpha
=
\eta(\kappa\cdot\beta-\delta)
+\theta(\gamma-Q\cdot\beta)
+\sum_{j\in N}c_j\beta_j.
\]
Strict positivity of all coefficients forces equality only when both constraints are equalities and all residual coordinates vanish. The determinant then forces \(\beta=\alpha\).

### A useful immediate wrapper

Package the analytic/LP equivalence explicitly:
\[
\operatorname{Integrable}(\texttt{tiedDom})
\iff
\operatorname{UniqueLPMin}(Q,\kappa,\gamma,\delta,r+1,\alpha),
\]
under the union of the existing hypotheses, including
\(\kappa\cdot\alpha=\delta\).

Do the same at the strict-slack vertex. These short corollaries make the note’s advertised connection visible without asking readers to compare two theorem statements manually.

# B. Recommended priorities

## 1. Record-level mixed-truth coefficient measure

**Exact target.** Construct a two-dimensional instance and prove, for each admissible continuous bounded observable,
\[
\frac{K_\phi(\sigma/t)}{\log t}
\longrightarrow
\int\phi\,d\mu_\sigma,
\]
where
\[
\mu_\sigma
=
\sum_{\text{admissible corner branches }b}
W_b(0)e^{-\sigma a_b(0)}\delta_{z_b}
\]
under the branchwise \(F=H a_b\), positive-fibre convention above.

Then derive the `totalKernel` expectation theorem through the existing measure-valued assembly API.

**Value.** This closes the most visible analytic-to-record gap and demonstrates that the architecture handles truth involving multiple coordinates—not just that a related scalar integral has been computed.

**Main risk.** Branch multiplicities, Jacobians, chart weights, and the exact coarea convention. The asymptotics themselves are already done.

**Scope advice.** First prove a one-positive-branch identity. Only then assemble signs and atlas terms.

---

## 2. Product-chart LP face classification and coefficient measure

This is now the most direct theorem for the thesis.

### Correct geometric statement

Assume
\[
\kappa_i>0,\qquad a_i=r_i+1>0,\qquad \delta>0,
\]
and `Q = 0`, with a feasible truth bound. Define
\[
\lambda=\min_i\frac{a_i}{\kappa_i},
\qquad
T=\{i:a_i/\kappa_i=\lambda\},
\qquad N=T^c.
\]
Then the LP optimal set is
\[
\operatorname{Opt}
=
\left\{\alpha\geq0:
\alpha_j=0\ (j\in N),\
\sum_{i\in T}\kappa_i\alpha_i=\delta
\right\}
=
\operatorname{conv}\left\{\frac{\delta}{\kappa_i}e_i:i\in T\right\}.
\]
Consequently,
\[
\dim\operatorname{Opt}=|T|-1.
\]

It is a simplex supported on selected coordinate axes, not literally a coordinate face of the orthant.

### Analytic match

For the corresponding product-like chart, prove that the logarithmic exponent is
\[
k=|T|-1,
\]
and the coefficient measure is the push-forward of a density on the physical face \(x_T=0\). Schematically, for an integral with exponential \(e^{-t^\delta U(x)x^\kappa}\),
\[
d\mu(z)
=
\frac{\delta^k\Gamma(\lambda)}{k!}
\left(\prod_{i\in T}\kappa_i^{-1}\right)
W(0_T,z)U(0_T,z)^{-\lambda}
\prod_{j\in N}z_j^{r_j-\lambda\kappa_j}\,dz,
\]
with your exact existing prefactors substituted.

The cases are:

- `T = all coordinates`: a point mass after push-forward;
- `|T| = 1`: a unique LP vertex, with a generally nontrivial physical face measure;
- intermediate `T`: a partially tied face density.

**Important:** a unique LP vertex does **not** generally mean a point-mass coefficient measure.

**Value.** This makes “the LP tells which faces carry the measure” precise, and connects LP face dimension to log multiplicity.

**Main risk.** Index-set conversions and transporting the existing partial-face theorem. Avoid unnecessary affine-dimension formalization initially: the explicit simplex characterization plus `k = T.card - 1` already gives most of the value.

Also say “carried by the face,” not “has support exactly equal to the face,” unless weights are positive and the chart map satisfies the necessary support hypotheses.

---

## 3. Local parameter uniformity, then `σ(t) → σ₀`

**Exact target.** For a compact parameter set \(C\) contained in a fixed admissible parameter region, prove
\[
\sup_{\sigma\in C}
\left|
\frac{t^{\lambda_p}}{(\log t)^{k_p}}
K_{p,\phi}(t,\sigma)
-\int\phi\,d\mu_p(\sigma)
\right|\longrightarrow0.
\]

Require:

- the powers and log orders are fixed on that region;
- coefficient integrals are continuous in \(\sigma\);
- the analytic bounds hold uniformly;
- \(C\) stays away from excluded parameter values, such as `σ = 0`.

For the ratio, require
\[
\inf_{\sigma\in C}\int\chi\,d\mu_*(\sigma)>0.
\]
Then obtain uniform convergence of expectations, and in particular
\[
\sigma(t)\to\sigma_0
\quad\Longrightarrow\quad
\langle\psi\rangle_{\chi,t,\sigma(t)}
\to
\frac{\int\psi\,d\mu_*(\sigma_0)}
     {\int\chi\,d\mu_*(\sigma_0)}.
\]

**Value.** This turns fixed-parameter asymptotics into stable landscape information and is a natural input to the ambient wall-atlas theorem.

**Main risk.** Pointwise domination must become parameter-independent domination, including moving domains. Do not claim uniformity across a chamber boundary where the dominant exponents change.

**Implementation advice.** Separate:

1. a generic uniform finite-sum/ratio assembly theorem;
2. uniform analytic certificates for each model.

The mixed-log example is a good first analytic instance on \(C\subset(0,\infty)\).

---

## 4. A scoped degeneracy theorem—not all degenerate asymptotics

The next degeneracy target should be **LP optimal-set structure**, with analytic consequences only in cases already covered by partial-face machinery.

### Exact general statement

Suppose a feasible \(\alpha\) and dual data satisfy
\[
a=\eta\kappa-\theta Q+c,\qquad
\eta,\theta,c_j\geq0,
\]
with complementary slackness at \(\alpha\). Then
\[
\beta\in\operatorname{Opt}
\iff
\beta\text{ is feasible and }
\eta(\kappa\cdot\beta-\delta)=
\theta(\gamma-Q\cdot\beta)=
c_j\beta_j=0
\]
for every \(j\).

This follows directly from your existing gap identity and describes the optimal set even when strict certificates fail.

**Value.** It explains what replaces uniqueness: a face cut out by vanishing nonnegative gap terms.

**Main risk.** Overinterpreting degeneracy analytically.

In particular:

- A zero reduced cost in the nondegenerate two-scaled setup gives a feasible equal-cost direction.
- `Δ = 0` does **not** automatically imply nonuniqueness or a new logarithm.
- A tied one-coordinate vertex can still be unique; the two active inequalities may be dependent on its support, and dual multipliers need not be unique.
- Divergence of the old limiting model does not alone identify the replacement normalization.

For `Q = 0`, your face theorem supplies the analytic continuation into ties. For general constrained degeneracies, a universal “LP face dimension equals log power” theorem needs additional work and hypotheses.

# C. Remaining candidates

## Hironaka-side ambient statement

The natural next ambient result is:

> The normalized coefficient measure is independent of the chosen certified wall atlas, on the observable region where both atlas constructions represent the same intrinsic kernels.

More precisely, with a common positive reference \(\chi\), conclude
\[
\frac{\mu_A|_{L'}}{\int\chi\,d\mu_A}
=
\frac{\mu_B|_{L'}}{\int\chi\,d\mu_B},
\]
under the hypotheses needed by your existing distinguishability theorem.

**Value:** it says the reconstructed object belongs to the landscape, not its chosen resolution.

**Risk:** matching intrinsic kernels and observable classes across atlases, and tracking normalization versus restriction. Preserve the theorem-level `IsOpen L'` hypothesis.

If both atlas descriptions already feed the same `wall_fibre_expectation`, this may be a short, high-value wrapper worth doing opportunistically.

## Numerical validation

The strongest first example is a **genuinely distributed partial-face measure**, not another point mass.

Take, on \((0,1)^3\),
\[
I_t(\phi)=
\int xyz^3\,e^{-txyz}\phi(x,y,z)\,dx\,dy\,dz.
\]
Here
\[
\kappa=(1,1,1),\qquad r=(1,1,3),
\]
so
\[
\lambda=2,\quad T=\{x,y\},\quad k=1.
\]
The predicted coefficient measure on the \(z\)-axis has density proportional to \(z\,dz\). Hence
\[
\frac{I_t(z)}{I_t(1)}\to\frac23,
\qquad
\frac{I_t(z^2)}{I_t(1)}\to\frac12.
\]

**Value:** this visibly distinguishes a nontrivial coefficient measure from “everything concentrates at one optimum.”

**Risk:** convergence can be slow at logarithmic order; direct quadrature poorly resolves the thin regions near the coordinate planes. Use logarithmic coordinates or analytically integrate one variable first.

I would use this before a two-scaled constant check: it illustrates the note’s central measure-valued claim more directly.

---

**Bottom line:** close the record-level mixed-truth example, then prove the product-chart LP/measure classification. Add parameter stability next. Treat general degeneracy through an optimal-set theorem first, rather than promising a uniform analytic classification prematurely.