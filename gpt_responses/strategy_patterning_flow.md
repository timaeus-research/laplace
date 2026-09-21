The plan is good **if the first pass is explicitly an algebraic formalisation of the note’s linear/quadratic models**, rather than a formalisation of the asymptotic and probabilistic reductions leading to those models.

There are three important corrections before starting:

1. **T1’s eigen-form is missing a factor of \(\eta\).**
2. **T3’s minimal-norm statement is false for Lean’s default norm on `ν → ℝ`**: that is the sup norm, not the Euclidean norm.
3. **T6’s weighted ray formula needs \(r\ge 0\)**, and its column norms must be Euclidean, not default Pi norms.

I cannot check the v4.33.0 API here. Below, existing project names are taken from the supplied files; Mathlib names I am not confident about are explicitly marked as search candidates. The line estimates mean retained definitions, statements, proofs, and short documentation—not exploration or scratch files.

## Scope and `\leanref` policy

Tag the exact equation or algebraic subclaim proved, rather than the entire proposition, unless the remaining hypotheses and conclusions really are covered. In particular:

- T1 does not prove the nonlinear \(O(\varepsilon^2)\) response.
- T2 does not prove a Laplace approximation or construct a stochastic chain.
- T4 proves identities for a covariance equation, not that an SDE has that stationary covariance.
- T5’s matrix result is a stationary second-moment balance.
- T7 does not prove preservation of an RLCT or its multiplicity.

That separation will make these references useful rather than inadvertently overstated.

---

## T1 — `Horizon.lean`

### Correctness

The recursion formula is correct without symmetry, positivity, or stability assumptions:

\[
\delta_T=-\varepsilon\eta
\left(\sum_{k<T}(I-\eta H)^k\right)b.
\]

The proposed eigen-form of the **unscaled sum** is incorrect. The correct forms are

\[
\left(\sum_{k<T}(I-\eta H)^k\right)v
=
\left(\sum_{k<T}(1-\eta\lambda)^k\right)v,
\]

and, when \(\eta\lambda\ne0\),

\[
\left(\sum_{k<T}(I-\eta H)^k\right)v
=
\frac{1-(1-\eta\lambda)^T}{\eta\lambda}\,v.
\]

Your desired formula belongs to the horizon filter

\[
F_T(H):=\eta\sum_{k<T}(I-\eta H)^k.
\]

For this filter:

- if \(\lambda\ne0\), its eigenvalue is
  \((1-(1-\eta\lambda)^T)/\lambda\), **including when \(\eta=0\)**;
- if \(\lambda=0\), its eigenvalue is \(\eta T\).

### Lightest route

Define the filter and state the recursion as \(\delta_T=-\varepsilon F_T(H)b\). Retain the raw scalar-sum lemma as an intermediate result.

Useful APIs:

- `Finset.sum_range_succ`
- `pow_succ` / `pow_succ'`
- `Matrix.mulVec_mulVec`
- matrix multiplication/addition distributivity
- `geom_sum_mul` / `geom_sum_eq` — confirm exact orientation and arguments.

The cleanest scalar proof avoids division initially:

\[
\lambda\left(\eta\sum_{k<T}(1-\eta\lambda)^k\right)
=1-(1-\eta\lambda)^T.
\]

Then divide only by \(\lambda\). This avoids an unnecessary \(\eta\ne0\) hypothesis.

For the matrix eigenvector-power lemma, a short induction is likely simpler than finding the most general endomorphism API.

### Estimate

**100–170 lines.**

### Recommendation

Keep. Name the file’s main result something like “linearized horizon response,” not the nonlinear proposition’s full name.

---

## T2 — `Profile.lean`

### Correctness and hypotheses

The per-mode variance formula is correct. For a genuine variance interpretation, require

\[
\varepsilon>0,\qquad q>0,\qquad \varepsilon q<4.
\]

The condition \(0<\varepsilon q<4\) alone allows both \(\varepsilon\) and \(q\) to be negative. The algebra still works, but the injected “variance” is then negative.

For the profile interpretation, use \(t:=n\beta>0\), \(\lambda_i\ge0\), and \(q_i=t\lambda_i+\gamma>0\). Algebraic first-step and limit identities can have weaker hypotheses.

**First step:** your identity is exact. Call it “first-step sharpness,” not a proof of the continuous-time initial derivative.

**Plateau:** correct under modal stability.

**Matrix trace:** correct under the ULA stability hypotheses already used by `ulaCov_conj_apply`.

**Zero-step-size count:** correct, but distinguish two tasks:

1. proving the rational expression tends to its value at \(h=0\);
2. identifying that value with the effective-dimension expression.

Neither requires a matrix-inverse continuity theorem.

### Lightest route

#### Scalar part

Use:

- `ar1_var_iterate`;
- scalar denominator algebra;
- a power-limit theorem.

The likely power-limit API is `tendsto_pow_atTop_nhds_zero_of_norm_lt_one`; confirm the exact name and whether a specialized real absolute-value version is more convenient. Handle exponent \(2k\) either by composing with \(k\mapsto2k\), or rewriting as \((\rho^2)^k\).

For finite sums, look for `tendsto_finset_sum` or the corresponding `Tendsto` finite-sum lemma on this pin.

Define the variance by recursion and derive the rational formula. Then the first-step result needs no denominator cancellation or stability assumptions.

#### Matrix trace part

Your \(P-\gamma I\) route is good, but **do not divide by \(t\)**. Use

\[
tH=P-\gamma I.
\]

This gives

\[
t\,\operatorname{tr}(HX)
=\operatorname{tr}(PX)-\gamma\operatorname{tr}(X)
\]

directly, with no unnecessary \(t\ne0\) hypothesis for this identity.

Package one reusable orthogonal trace lemma:

\[
\operatorname{tr}(BX)
=\sum_i b_i\,(U^\top XU)_{ii},
\qquad B=U\operatorname{diag}(b)U^\top.
\]

Its ingredients are:

- `Matrix.trace_mul_comm`;
- associativity and \(U^\top U=I\);
- `Matrix.trace`;
- `Matrix.diagonal_mul`.

This lemma also serves T5.

**Slicker alternative:** work from the outset in an eigenbasis of \(H\), where \(P\) has diagonal entries \(t\lambda_i+\gamma\), and use generic `lyapunovVia`. This is conceptually cleaner for a single common profile theorem, but slightly less direct if the public statement must use `ulaCov P h`.

Do not silently identify Mathlib’s separately selected eigenvalue enumerations of \(H\) and \(P\). Either use \(p_i\) throughout, or explicitly specify a common diagonalising basis.

#### Missing inexpensive result

You can also obtain the finite-time **matrix** identity cheaply from

- `covStep_iterate_zero_of_comm`;
- `ulaCov_fixed`;
- `ulaCov_commute`.

That is a valuable direct reference for the second part of Prop. 3.2.

### Estimate

- Scalar variance, first step, plateau: **100–170 lines**.
- Trace helper, matrix profile, zero-step limit: **120–220 lines**.
- Finite-time matrix wrapper: **25–50 lines**.

**Total: 245–440 lines.** Consider separating the scalar and matrix leaves.

### Recommendation

Keep. Prove the rational \(h\to0\) limit, not continuity of `ulaCov` through matrix inversion.

---

## T3 — `Direct.lean`

### Correctness and hypotheses

The identities are correct provided:

- the normalization scalar \(n\ne0\);
- \(R^\top=R\);
- \(S\) is invertible.

If \(n=\operatorname{card}\nu\), use `[Nonempty ν]` and derive positivity of its real cast. Do not leave a scalar named `n` whose relationship to the sample index type is implicit.

The mean-zero property requires an additional assumption:

\[
G\mathbf1=0.
\]

Include it as a separate inexpensive theorem.

### Minimal norm: essential restatement

For `ω : ν → ℝ`, the expression `‖ω‖` normally means the sup norm. The Euclidean minimum-norm solution need not minimize that norm.

Use either

\[
\sum_i\omega_i^2\le\sum_i(\omega'_i)^2
\]

or explicitly move vectors into `EuclideanSpace ℝ ν`.

For this matrix-heavy file, **sum-of-squares is the lightest and safest public statement**. A Euclidean-norm wrapper can follow.

### Lightest route

First prove a general rectangular-matrix lemma:

> If \(M\omega=y\) and \(\omega=M^\top z\), then every other solution satisfies
> \[
> \sum_i(\omega'_i)^2
> =
> \sum_i\omega_i^2+
> \sum_i(\omega'_i-\omega_i)^2.
> \]

This is more useful than directly proving the inequality.

The key identity is

\[
\langle M^\top z,v\rangle=\langle z,Mv\rangle.
\]

Likely relevant names include `dotProduct_mulVec`, `vecMul_dotProduct`, and transpose/mulVec identities; **confirm their namespaces and orientations**. If lookup takes more than a few minutes, unfolding the dot products and using `Finset.sum_comm` gives a short, predictable proof.

For your candidate,

\[
\omega=\chi^\top\bigl(n\,S^{-1}d\mu\bigr).
\]

Thus you need neither a pseudoinverse nor a general least-squares library.

For the matrix algebra:

- `Matrix.transpose_mul`, `Matrix.transpose_smul`;
- `Matrix.mul_nonsing_inv`, `Matrix.nonsing_inv_mul`;
- `Matrix.mulVec_mulVec`;
- distributivity, `smul_smul`, and scalar normalization.

As in the sampler files, `module` is helpful after distributing matrix products; `ring` does not prove noncommutative matrix identities.

### Corollary algebra

Correct. Use

\[
R(H+\rho I)=I
\quad\Longrightarrow\quad
RHR=R-\rho R^2.
\]

This is particularly clean: it does not require separately proving that \(R\) commutes with \(H\).

For the abstract identity, invertibility of \(H+\rho I\) suffices. To connect this back to the direct-force theorem’s symmetric \(R\), derive symmetry from symmetric \(H\).

The claimed asymptotic displacement \(H^{-1}\cdots\) is a further dynamical statement; the proposed algebra does not prove convergence of training.

### Estimate

- Definitions and direct identities: **100–170 lines**.
- General least-squares/Pythagorean lemma and application: **70–130 lines**.
- Mean-zero and \(C=H\) corollaries: **60–100 lines**.

**Total: 230–400 lines.**

### Recommendation

Keep, and make the generic sum-of-squares minimality lemma a reusable small component.

---

## T4 — `SGDLyapunov.lean`

### Correctness

All three targets are correct with the intended interpretations.

For (i), **no symmetry, positivity, or invertibility is required**. It is just cyclicity of trace.

For (ii), say the isotropic matrix **solves** the equation, not that it is the unique solution. Uniqueness would require additional hypotheses.

For (iii), modal stability suffices for uniqueness of the discrete fixed point. For an SGD covariance interpretation, state \(\eta>0\), \(B>0\), \(c\ge0\), and positive stable \(\lambda_i\). Some are unnecessary for the rational algebra but clarify the meaning.

### Lightest route

For (i)–(ii):

- apply `congrArg Matrix.trace`;
- simplify using `Matrix.trace_add`, `Matrix.trace_smul`;
- use `Matrix.trace_mul_comm`;
- finish with scalar algebra.

For (iii):

- `covStep_diagonal_fixed_iff`;
- `diagLyapunov`;
- entrywise diagonal simplification;
- scalar cancellation.

Extract the needed nonzero factors from stability at each index. There is no need to transport this theorem to a general eigenbasis unless a downstream result needs it.

### Estimate

**90–150 lines.**

### Recommendation

Excellent early target. Do not include the \(O(\eta^3)\) expansion on the first pass.

---

## T5 — `Virial.lean`

### (i) Matrix/ULA identity

Correct. With \(X=\operatorname{ulaCov}(P,h)\),

\[
\operatorname{tr}(PX)
=d+\frac h2\operatorname{tr}(P^2X).
\]

There is an even lighter route than eigenvalues:

\[
\left(P-\frac h2P^2\right)X=I.
\]

Take traces. This needs only invertibility of the ULA denominator—**not symmetry or stability**. Add a stable-SPD wrapper for the covariance interpretation.

Then derive the spectral sums separately if desired, using T2’s trace helper.

Do not write \(\sum_i p_i x_{ii}\) without specifying that \(x_{ii}\) are entries of \(U^\top XU\), not entries in the original coordinates.

**Estimate:** **30–60 lines** for the trace balance; **another 40–80** for spectral formulas.

### (ii) Genuine one-dimensional virial

Correct under appropriate hypotheses. A clean statement uses a named derivative \(U'\):

- `∀ x, HasDerivAt U (U' x) x`;
- `Integrable (fun x ↦ Real.exp (-U x))`;
- `Integrable (fun x ↦ x * U' x * Real.exp (-U x))`;
- \(x e^{-U(x)}\to0\) at both ends.

Set

\[
F(x)=xe^{-U(x)},\qquad
F'(x)=e^{-U(x)}-xU'(x)e^{-U(x)}.
\]

Then apply the whole-line fundamental theorem to \(F'\). This is often easier than invoking a product integration-by-parts theorem directly.

The API area to inspect is:

```text
Mathlib/MeasureTheory/Integral/IntegralEqImproper
```

and files found by searching for:

```text
integral_eq_sub_of_hasDerivAt
integral_deriv
integral_mul_deriv
atBot ... atTop
```

`integral_eq_sub_of_hasDerivAt_of_tendsto` and
`integral_mul_deriv_eq_deriv_mul` are **search candidates, not names I can certify on this pin**.

The proposed integrability assumptions imply integrability of \(F'\). For a normalized expectation theorem, also establish \(0<Z<\infty\); do not bury that in division conventions.

**Estimate:** **90–180 lines**, assuming a compatible whole-line FTC is readily available.

### Higher dimensions

A divergence theorem is not necessary. Coordinatewise one-dimensional FTC plus Fubini proves

\[
\int x_i\partial_iU\,e^{-U}=\int e^{-U},
\]

then sum over coordinates.

The difficulty is stating and transporting sectionwise decay and integrability—not the final summation. With explicit almost-everywhere slice hypotheses, this is realistic; reproducing the note’s weak regularity and cutoff formulation is a much larger project.

**Recommendation:** first pass: matrix identity plus 1D. Defer general \(d\)-dimensional integration by parts.

---

## T6 — `FourGon.lean`

### Correctness

**(a)** Correct, and trigonometry should be the last step.

Prove first

\[
\max(0,z)^2+\max(0,-z)^2=z^2
\]

by cases on \(0\le z\), then use the sine/cosine square identity.

**(b)** The weighted formula needs \(r\ge0\). Factoring

\[
\operatorname{ReLU}(rz)=r\operatorname{ReLU}(z)
\]

is invalid for negative \(r\).

Also, `‖W_i‖` for a column represented as `Fin 2 → ℝ` is the sup norm. Define squared column length by a dot product, or use EuclideanSpace explicitly.

**(c)** Correct for \(\varepsilon>0\), with standard Euclidean volume. The measure-valued theorem should have an `ENNReal.ofReal` on the right, or use `volume.real`.

### Lightest route

Avoid angles initially. Set the dead column to \((x,y)\). The strongest easy formula is

\[
\begin{aligned}
L_h(W(x,y))-L_h(W(0,0))
={}&\frac13\bigl[
h_0[x]_+^2+h_1[y]_+^2\\
&+h_2[-x]_+^2+h_3[-y]_+^2
-h_4(x^2+y^2)\bigr]\\
&+\frac{h_4}{3}(x^2+y^2)^2.
\end{aligned}
\]

This holds for all real \(x,y\), avoids angle conventions, and immediately gives the uniform-weight identity. The ray theorem is then a wrapper.

Use explicit `Fin 5` sum expansion and `fin_cases`, but name the five feature-loss identities separately rather than expecting one enormous `simp; ring` to succeed.

For volume, convert the set into a Euclidean ball of radius

\[
R=\sqrt{\sqrt{15\varepsilon}}.
\]

A general Euclidean ball-volume theorem exists in Mathlib; **the exact namespace and whether dimension two simplifies directly to \(\pi R^2\) need checking**. Search `volume_ball` in the inner-product-space/Euclidean volume files. Gamma simplification may be the main inconvenience.

### Estimate

- Coordinate algebra, ReLU identity, uniform and ray wrappers: **140–230 lines**.
- Volume theorem: **70–160 lines**, API-dependent.

### Recommendation

Keep the coordinate algebra. Make volume a separate optional leaf.

Skipping gradients is sensible initially, although squared ReLU is differentiable at zero, so this is not fundamentally a nonsmooth-analysis problem. The descending path is less attractive: sign-region bookkeeping and the \(O(r^6)\) claim add substantial work.

---

## T7 — `Positivity.lean`

### Correctness

Add **\(c_2>0\)**. The lower inclusion involving \(\varepsilon/c_2\) is not justified by the current assumptions.

For the two sublevel inclusions, nonnegativity of \(K\) is not needed. For the zero-set equality and samplewise derivation, it is.

Interestingly, neither measurability of \(U\) nor measurability of the functions is needed for the `measure_mono` inequalities: a measure is defined on arbitrary sets.

### Lightest route

- `Set.subset_def`;
- `lt_div_iff₀` / `div_lt_iff₀`, checking orientation;
- `measure_mono`.

Worth adding two small results:

1. finite positive weighted sums satisfy the pointwise sandwich;
2. under \(K\ge0\), the sandwich implies equality of zero sets.

These make the connection to the note substantially more complete at little cost.

### Estimate

**35–60 lines** for sublevel inclusions and measures; **70–110 total** with weighted sums and zero sets.

### Recommendation

Keep. Label it expressly as the sublevel-set core, not RLCT preservation.

---

## T8 — Jacobi / log determinant

### Correctness

For a log-volume theorem, require \(\det H>0\), typically via positive definiteness.

Mathematically the derivative formula also holds for \(\log|\det|\) at any invertible \(H\). Lean’s `Real.log` is extended to negative inputs through absolute value, so “invertible only” may formally work, but that is not the intended positive-volume interpretation unless explained.

### Route and uncertainty

I would **not drop this before a short API reconnaissance**. The determinant is polynomial and its derivative is the adjugate pairing:

\[
D\det(H)[M]=\operatorname{tr}(\operatorname{adj}(H)M).
\]

Then combine with inverse–adjugate identities and the derivative of `Real.log`.

Search for determinant calculus and adjugate results:

```text
hasFDerivAt_det
hasDerivAt_det
fderiv_det
adjugate
```

I cannot certify these declaration names or that a packaged Jacobi theorem exists on v4.33.0.

If only determinant polynomial smoothness exists, deriving the actual derivative via permutation expansion is feasible but no longer a cheap leaf.

### Estimate

- Packaged determinant derivative available: **40–90 lines**.
- Derivative infrastructure must be built: **180–350+ lines**.

### Recommendation

Conditional keep: time-box discovery, then defer if the derivative formula is not already accessible. This theorem alone does not formalise the moving-minimizer expansion in the note.

---

## T9 — Gaussian fourth moments / Isserlis

### Correctness

Your formula needs symmetric \(A,B\). For arbitrary real matrices the correct formula is

\[
\mathbb E[(Z^\top AZ)(Z^\top BZ)]
=
\operatorname{tr}A\,\operatorname{tr}B
+\operatorname{tr}(AB)+\operatorname{tr}(AB^\top).
\]

For symmetric matrices this becomes the stated expression.

### Lightest route

First search the **project**, not only Mathlib. The supplied context already mentions `StdGaussian`, `GaussianStein`, Wick contractions, and second-order covariance machinery. This result may be almost entirely present under another formulation.

The useful intermediate theorem is the coordinate fourth moment

\[
\mathbb E[Z_iZ_jZ_kZ_l]
=\delta_{ij}\delta_{kl}
+\delta_{ik}\delta_{jl}
+\delta_{il}\delta_{jk}.
\]

Once available, quadratic-form contraction is finite-sum algebra. Without it, coordinate independence/product integrals and one-dimensional moments are a more predictable route than searching indefinitely for a named Isserlis theorem.

I cannot certify a ready-made finite-dimensional Isserlis API in Mathlib.

### Estimate

- Existing coordinate fourth-moment theorem: **70–150 lines**.
- Gaussian moment infrastructure needed: **250–500+ lines**.

### Recommendation

Keep only if existing project machinery makes it short. Do not attach this exact Gaussian identity as a proof of the Taylor remainder \(O(\|\Sigma\|^3)\).

---

## Recommended attack order

1. **T7:** sublevel sandwich and zero-set core.
2. **T4(i)–(ii):** trace Lyapunov identities.
3. **T5(i):** algebraic ULA virial balance—no spectral machinery needed.
4. **T1:** corrected horizon filter and eigenvector formulas.
5. **T4(iii):** discrete diagonal SGD law.
6. **T2 scalar:** variance, first step, plateau.
7. **T2 matrix:** reusable trace lemma, finite-time ULA wrapper, effective count.
8. **T3:** direct force, general Euclidean minimality lemma, corollaries.
9. **T6 algebra:** Cartesian four-gon identities first.
10. **T5(ii):** one-dimensional analytic virial.
11. Optional leaves: **T8**, **T9**, **T6 volume**, after API reconnaissance.

Keep additions in new leaves, verify the root import closure, and compile each commit without `sorry`. Before the first new proof, check that the supplied sampler files themselves elaborate against the actual v4.33.0 pin.

## What I would drop or defer

- Nonlinear \(O(\varepsilon^2)\) horizon response.
- Continuous-time horizon/profile limits beyond the simple rational \(h\to0\) count.
- Full weak-regularity multivariate virial.
- Four-gon descending path and gradient claims on the first pass.
- RLCT and multiplicity preservation beyond the sublevel sandwich.
- T8 if determinant differentiation requires new infrastructure.
- T9 if the project lacks reusable Gaussian fourth moments.
- All probabilistic stationarity claims not explicitly connected to a random-variable covariance construction.

## False or under-hypothesised statements to fix

| Target | Required correction |
|---|---|
| T1 | Raw geometric sum has denominator \(\eta\lambda\); the stated formula is for the \(\eta\)-scaled filter. |
| T2 | Product stability alone does not ensure positive injected variance; use \(\varepsilon>0,q>0\). |
| T2 | Do not identify independently chosen eigenvalue enumerations without a common-basis argument. |
| T3 | Require nonzero normalization; default Pi norm is not Euclidean. |
| T3 | Mean-zero weights require \(G\mathbf1=0\). |
| T4 | An explicit solution is not a uniqueness theorem for the continuous Lyapunov equation. |
| T5 | Spectral diagonal entries must be in the eigenbasis. |
| T6 | Weighted ray formula requires \(r\ge0\); column norms and ball volume must be Euclidean. |
| T7 | Require \(c_2>0\). |
| T8 | Use positive determinant for log-volume, or explicitly formulate log absolute determinant. |
| T9 | Require symmetry, or retain both distinct trace contractions. |

With these changes, the core is a strong collection of small, auditable algebraic theorems, with the genuinely analytic obligations clearly separated.