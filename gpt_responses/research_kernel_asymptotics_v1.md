## Executive recommendation

There are **two different intermediate results** to build:

1. **A constrained monomial comparison theorem:** under a nonvanishing-weight hypothesis, identify the power and log order by a polyhedral problem.
2. **A certified rescaling theorem:** retain the moving unit and weight, and obtain the actual leading constant from their limits after rescaling.

The first does **not** imply the second. Moreover, with merely continuous nonnegative chart weights, even the first needs additional hypotheses: a weight can vanish on the dominant face, change the power, introduce other slowly varying factors, or produce stretched-exponential decay.

Three corrections are essential:

- The constraint imposed by the solved coordinate is generally **not harmless**.
- Bounds on \(|a|\) are not enough for a positive Boltzmann phase: you need positivity of the actual phase on each sign sector.
- The displayed `LPData` hypotheses cannot imply a finite positive limit of \(t^\Lambda Z(t)\) in general. They allow logarithmic sectors.

Below, \(\asymp\) means two-sided bounds by positive constants for all sufficiently large \(t\).

---

# 1. A useful one-chart formulation

## 1.1 First split into sign sectors

For real exponents, work with positive coordinate magnitudes. Split the unsolved variables into orthants, and retain only the admissible solved-coordinate branches. On each resulting sector write
\[
x_j=|w_j|>0,\qquad
v_t(x)=D\,t^{-\gamma/q}\prod_jx_j^{-Q_j/q},
\]
where
\[
q>0,\quad Q_j\geq0,\quad D=|\sigma|^{1/q}
\]
when \(|S|=1\), as in your atlas.

Signs are now a finite index \(\epsilon\). The branch admissibility condition is constant on a fixed orthant for fixed \(\operatorname{sgn}\sigma\). Real powers apply only to positive magnitudes; they should not encode branch signs.

After normalizing the box radius, consider
\[
K(t)=A_\sigma t^{-\gamma p}
 \sum_{\epsilon}
 \int_{(0,1)^d}
 \mathbf1_{\{v_t(x)<1\}}\,
 W_\epsilon(x,v_t(x))
 \prod_jx_j^{r_j}
 \exp\!\left[-B_\sigma t^\delta
     a_\epsilon(x,v_t(x))\prod_jx_j^{\kappa_j}\right]dx,
\tag{1}
\]
where
\[
\delta=1-\gamma\nu,\qquad
A_\sigma=\frac{|\sigma|^p}{q},\qquad
B_\sigma=|\sigma|^\nu.
\]
Box rescaling introduces additional fixed constants, which should be retained in \(A_\sigma,B_\sigma,D\).

Here \(W\) includes the partition weight, the observable-independent density unit \(|b|\), and any domain indicator not already accounted for.

**Positivity hypothesis:** on the support of \(W_\epsilon\),
\[
0<a_-\leq a_\epsilon\leq a_+<\infty.
\]
This is a hypothesis about the effective signed phase, not merely \(|a_\epsilon|\).

---

## 1.2 The constrained LP

Put \(b_j=r_j+1\). Under the logarithmic scaling \(x_j\sim t^{-\alpha_j}\),

- the box gives \(\alpha_j\geq0\);
- the solved-coordinate cutoff gives
  \[
  Q\cdot\alpha\leq\gamma;
  \]
- avoiding exponential suppression gives
  \[
  \kappa\cdot\alpha\geq\delta;
  \]
- the density contributes \(t^{-b\cdot\alpha}\).

Thus the relevant polyhedron is
\[
P_\gamma=
\left\{\alpha\in\mathbb R_{\geq0}^d:
Q\cdot\alpha\leq\gamma,\quad
\kappa\cdot\alpha\geq1-\gamma\nu
\right\}.
\tag{2}
\]

When the minimum exists, define
\[
\boxed{\lambda=\gamma p+\min_{\alpha\in P_\gamma}b\cdot\alpha},
\qquad
M=\operatorname*{argmin}_{\alpha\in P_\gamma}b\cdot\alpha,
\qquad m=\dim M.
\tag{3}
\]

Coordinates known to remain bounded away from zero should be removed from this LP and retained as unscaled face variables. More generally, one needs a finite stratification if the support excludes some candidate faces.

### A concrete comparison theorem worth targeting

Here is a sufficient, intentionally stronger-than-necessary statement.

> **Constrained monomial comparison theorem.**  
> In (1), assume:
>
> 1. \(\gamma>0,\ q>0,\ Q_j\geq0\), while \(\nu,p,\kappa_j,r_j\) are real.
> 2. \(b_j>0\) whenever \(Q_j=0\).
> 3. There are finitely many admissible sectors; their weights are measurable, nonnegative, and uniformly bounded.
> 4. The weights vanish outside the normalized box.
> 5. The positive unit bounds \(a_-\leq a_\epsilon\leq a_+\) hold wherever the corresponding weight is nonzero.
> 6. For at least one admissible sector, there exist \(\eta,w_->0\) such that
>    \[
>    W_\epsilon(x,v)\geq w_-
>    \quad\text{for }(x,v)\in[0,\eta]^{d+1}.
>    \]
> 7. \(P_\gamma\neq\varnothing\).
>
> Then the optimum is attained, its optimal face is compact, and
> \[
> \boxed{K(t)\asymp t^{-\lambda}(\log t)^m.}
> \tag{4}
> \]

The integrability condition in item 2 handles coordinates untouched by the truth monomial. Coordinates with \(Q_j>0\) are bounded away from zero at each fixed \(t\) by the cutoff, so their \(r_j\) need not exceed \(-1\).

This theorem is a **polyhedral Laplace estimate**, not a direct application of your existing nonnegative-exponent `LPData`.

The lower-weight condition is not automatic for partition-of-unity terms. It is a convenient theorem for models and for charts known to be positive on the relevant corner. The useful refined version replaces it by positivity on suitable neighborhoods of the dominant strata.

### What if \(P_\gamma\) is empty?

Do not assign an ordinary power–log asymptotic. Exponential or stretched-exponential suppression may occur. One must then analyze the positive minimum of the phase at the relevant scale.

---

## 1.3 Why arbitrary continuous weights are insufficient

Already without a fibre constraint,
\[
\int_0^1 e^{-tx^2}W(x)\,dx
\]
has no universal exponent determined by the phase and Lebesgue density.

Examples:

- \(W(x)=x^\beta\), \(\beta>0\), changes \(t^{-1/2}\) to \(t^{-(\beta+1)/2}\).
- \(W(x)=e^{-1/x^2}\), extended by \(0\) at \(0\), produces stretched-exponential suppression, governed by
  \[
  tx^2+x^{-2}\geq2\sqrt t.
  \]
- \(W(x)=1/\log(e/x)\), extended by \(0\), introduces an inverse logarithm.
- A weight behaving like
  \[
  x^\beta\bigl(2+\sin(\log\log(1/x))\bigr)
  \]
  near zero is continuous after extension by zero, but can prevent convergence of the normalized leading coefficient.

Thus:

> For arbitrary continuous chart weights, the safe output is a rescaled limit, possibly zero—not an automatically positive LP constant.

A zero constant cannot be fed into the displayed `ChartAssembly` as a positive chart normalization constant.

---

# 2. The exact-constant theorem: retain the moving unit

## 2.1 Recommended statement: a profile certificate

The reusable theorem should be formulated around explicit changes of variables, rather than pretending that every constrained LP has a single monomial rescaling.

Let
\[
L(t)=t^{-\lambda}(\log t)^m.
\]

A **profile certificate** for (1) consists of finitely many fixed measure spaces \((X_e,\mu_e)\), maps
\[
T_{e,t}:X_e\longrightarrow(0,1)^d,
\]
and nonnegative Jacobian densities \(J_{e,t}\), giving an exact integral decomposition. For example, for every nonnegative measurable \(f\),
\[
\int_{(0,1)^d}f(x)\,dx
=\sum_e\int_{X_e}f(T_{e,t}(u))J_{e,t}(u)\,d\mu_e(u).
\tag{5}
\]

Define
\[
G_{e,\epsilon,t}(u)
=B_\sigma t^\delta
 a_\epsilon(T_{e,t}(u),v_t(T_{e,t}(u)))
 \prod_jT_{e,t,j}(u)^{\kappa_j},
\]
and
\[
w_{e,\epsilon,t}(u)
=
\frac{t^{-\gamma p}}{L(t)}
J_{e,t}(u)
\mathbf1_{\{v_t(T_{e,t}(u))<1\}}
W_\epsilon(T_{e,t}(u),v_t(T_{e,t}(u)))
\prod_jT_{e,t,j}(u)^{r_j}.
\]

Then require, for each \(e,\epsilon\), precisely your `RescaledData` hypotheses:

- measurability;
- \(G_t\to G_0\) and \(w_t\to w_0\);
- \(G_0\geq0\);
- \(G_t\geq cG_0\) eventually wherever \(w_t\neq0\);
- \(|w_t|\leq\mathcal W\);
- the required integrability of
  \[
  \mathcal W e^{-cG_0},
  \qquad
  \mathcal W G_0e^{-cG_0}.
  \]

Your existing formulation uses everywhere pointwise convergence; an a.e. variant is often more convenient because sector boundaries are negligible.

> **Certified moving-kernel limit.**  
> Under (5) and these profile hypotheses,
> \[
> \boxed{
> \frac{K(t)}{L(t)}\longrightarrow
> C=A_\sigma\sum_{e,\epsilon}
> \int_{X_e}w_{e,\epsilon,0}(u)e^{-G_{e,\epsilon,0}(u)}\,d\mu_e(u).
> }
> \tag{6}
> \]
> Add \(C>0\) as a proved output condition when the theorem is intended for chart assembly.

For a bounded observable whose pullback converges under the same maps,
\[
H(T_{e,t}(u),v_t(T_{e,t}(u)))\to H_{e,0}(u),
\]
the corresponding numerator satisfies
\[
\frac{Q(t)}{L(t)}
\longrightarrow
J=A_\sigma\sum_{e,\epsilon}
\int H_{e,0}w_{e,\epsilon,0}e^{-G_{e,\epsilon,0}}\,d\mu_e.
\tag{7}
\]

For the energy numerator \(tF\,e^{-tF}\), use your energy-statistic conclusion directly.

This separates the hard geometry—constructing the certificate—from the already formalized dominated-convergence argument.

### Where the LP enters

A geometric certificate should also certify that its \(\lambda,m\) agree with (3). For \(m>0\), the changes of variables generally include **logarithmic face variables**, not just \(x=t^{-\alpha}u\) for a single optimizer.

The constant in (6) is not determined by \((\nu,\kappa,p,r,\gamma)\). It also depends on \(\sigma\), branch multiplicities, the unit, the surviving face weight, and the domain.

---

## 2.2 Naive unit freezing fails

The simplest example is
\[
I(t)=\int_0^1\int_0^1e^{-t(1+y)x^2}\,dx\,dy.
\]
Then
\[
t^{1/2}I(t)\longrightarrow
\frac{\sqrt\pi}{2}\int_0^1(1+y)^{-1/2}\,dy.
\]
Freezing the unit at \((0,0)\) gives \(\sqrt\pi/2\), which is wrong. Only \(x\) shrinks; \(y\) survives.

There is a particularly relevant moving-fibre version. Take
\[
s=xv,\qquad F=a(x,v)x^2,\qquad s=\sigma t^{-1/2},\quad \sigma>0.
\]
With density \(dx/x\) and a compactly supported weight \(W\), the substitution \(x=t^{-1/2}u\) gives
\[
K(t)=\int
e^{-a(t^{-1/2}u,\sigma/u)u^2}
W(t^{-1/2}u,\sigma/u)\,\frac{du}{u}.
\]
The limiting unit is
\[
a(0,\sigma/u),
\]
not \(a(0,0)\). For instance, \(a(x,v)=1+v\) genuinely changes the leading constant.

**Correct formulation:** if the rescaled points converge to a face-valued map \(U_0(u)\), then continuity gives
\[
a(U_t(u))\to a(U_0(u)).
\]
You may freeze at a single point only if \(U_0\) is that point almost everywhere relevant to the limiting measure.

Positive two-sided unit bounds allow comparison with constant-unit integrals. They give the same power–log **order when the comparison theorem applies**, not the same constant.

---

# 3. The moving cutoff is part of the leading geometry

The condition
\[
v_t(x)<1
\]
is equivalent to
\[
\prod_jx_j^{Q_j}>D^q t^{-\gamma}.
\tag{8}
\]
It gives the LP inequality \(Q\cdot\alpha\leq\gamma\). Dropping it changes the optimization problem.

For a direct sanity check,
\[
I_\gamma(t)=\int_{t^{-\gamma}}^1e^{-tx^2}\,dx.
\]
Without the cutoff, the order is \(t^{-1/2}\). But:

- if \(\gamma<1/2\),
  \[
  I_\gamma(t)\sim
  \frac12t^{\gamma-1}e^{-t^{1-2\gamma}};
  \]
- if \(\gamma=1/2\),
  \[
  t^{1/2}I_\gamma(t)\to\int_1^\infty e^{-u^2}\,du,
  \]
  not \(\sqrt\pi/2\);
- if \(\gamma>1/2\), the cutoff is harmless in this particular example.

The LP detects the transition:
\[
\alpha\leq\gamma,\qquad 2\alpha\geq1.
\]

### Lean representation

I recommend:

- preserve the original globally defined weight \(W(x,\pm v)\), extended by zero off its box;
- retain an explicit domain indicator when proving model comparisons or constructing rescalings;
- prove once that the indicator is redundant when multiplied by the actual supported weight.

Do **not** replace the moving support by a fixed compact support in \(x\). For each fixed nonzero \(s\), it may be bounded away from \(c(x)=0\), but not uniformly as \(s\to0\).

Also, if a unit is only defined or controlled on the box, an explicit indicator avoids accidentally asserting bounds outside its domain.

---

# 4. The case \(\gamma=0\) should be a separate entry point

The profile-certificate theorem applies unchanged to \(\gamma=0\). The corner-comparison theorem above deliberately does not.

At fixed \(s=\sigma\neq0\), the truth-active coordinates cannot all approach zero. The relevant domain is the actual fixed fibre, and the limiting unit is its restriction to the surviving face—not its value at the origin.

There may also be a positive minimum:
\[
F(z',s)=|z'|^2+s^2
\quad\Longrightarrow\quad
Z(t,\sigma)\sim C\,t^{-m/2}e^{-t\sigma^2}.
\]
A normalization consisting only of powers and logs cannot capture this.

For fixed fibres, use either:

1. a zero-minimum stratum analysis with the actual fixed-fibre weight; or
2. an exponential factor \(e^{-tF_{\min}(\sigma)}\), followed by local analysis around its minimizers.

The second analysis can depend on the unit’s nonmonomial behavior. It is not supplied by the wall exponents alone.

---

# 5. Chart assembly

Suppose the retained charts satisfy
\[
Z_i(t)=L_i(t)(C_i+o(1)),\qquad
Q_i(t)=L_i(t)(J_i+o(1)),
\]
with
\[
L_i(t)=t^{-\lambda_i}(\log t)^{m_i},\qquad C_i>0.
\]

The dominance order is:

1. smaller \(\lambda_i\) wins;
2. at equal \(\lambda_i\), larger \(m_i\) wins.

That is exactly the order in your `powLog` lemma.

Let \(D\) be the set of charts with the winning pair \((\lambda_*,m_*)\). Then
\[
Z(t)\sim t^{-\lambda_*}(\log t)^{m_*}\sum_{i\in D}C_i,
\]
and
\[
\frac{Q(t)}{Z(t)}
\longrightarrow
\frac{\sum_{i\in D}J_i}{\sum_{i\in D}C_i}.
\tag{9}
\]

If normalization constants \(d_i>0\) have been put inside \(L_i=d_i\,\mathrm{powLog}\), use the corresponding weighted sums.

### Exactly what your assembly needs

For each retained chart:

- eventual positivity of \(L_i\);
- a finite limit \(Z_i/L_i\to C_i\);
- **strict positivity** of \(C_i\);
- a finite limit \(Q_i/L_i\to J_i\).

For a finite nonempty family, the common \(c_0>0\) and finite \(M_J\) follow from these finite collections.

For every omitted contribution, prove its denominator and numerator are \(o(\sum L_i)\). For bounded observables, denominator bounds often suffice:
\[
|Q_i|\leq\|H\|_\infty Z_i.
\]
This does not automatically cover an unbounded observable such as \(tF\).

### Your particular `dominated_chart_limit`

It handles exactly `Fin 2`, with one normalization negligible relative to the other. It does not directly handle a general finite dominant cluster or tied charts.

Recommended addition: a finite maximal-pair assembly lemma using `tendsto_weighted_sub` and `powLog`. Alternatively, aggregate the dominant cluster first.

### Ties

Constants add. A finite sum of tied chart asymptotics does **not** create an additional logarithm. Logarithms arise inside a chart/model from a continuum of competing scales.

Signed numerators can cancel their leading constants; nonnegative denominator contributions cannot.

---

# 6. A complete single-monomial log theorem

This is the cleanest independent theorem to formalize first.

Let
\[
I(t)=\int_{(0,1)^d}
e^{-t\prod_i x_i^{A_i}}\prod_i x_i^{h_i}\,dx,
\]
with
\[
A_i\geq0,\qquad h_i>-1,
\]
and at least one \(A_i>0\). Put
\[
b_i=h_i+1,\qquad
\lambda=\min_{A_i>0}\frac{b_i}{A_i},
\]
\[
M=\left\{i:A_i>0,\ b_i/A_i=\lambda\right\},
\qquad k=|M|.
\]

Then
\[
\boxed{
I(t)\sim C\,t^{-\lambda}(\log t)^{k-1}
}
\tag{10}
\]
with
\[
\boxed{
C=
\frac{\Gamma(\lambda)}{(k-1)!}
\left(\prod_{i\in M}\frac1{A_i}\right)
\left(\prod_{i\notin M}\frac1{b_i-\lambda A_i}\right).
}
\tag{11}
\]
Coordinates with \(A_i=0\) contribute \(1/b_i\), as they should.

Replacing the phase by \(ct\prod x_i^{A_i}\), \(c>0\), multiplies \(C\) by \(c^{-\lambda}\).

The associated LP is
\[
\min b\cdot\alpha
\quad\text{subject to}\quad
\alpha\geq0,\quad A\cdot\alpha\geq1.
\]
Its optimal face is a simplex of dimension \(k-1\). Hence the log power is exactly the optimal-face dimension.

For \(A=(2,2)\), \(h=(0,0)\),
\[
\lambda=\tfrac12,\quad k=2,\quad
C=\frac{\sqrt\pi}{4}.
\]
Thus
\[
\int_0^1\int_0^1e^{-tx^2y^2}\,dx\,dy
\sim\frac{\sqrt\pi}{4}t^{-1/2}\log t.
\]

## Proof route I recommend

Use logarithmic coordinates followed by one Gamma integral.

For \(A_i>0\), set
\[
y_i=-A_i\log x_i.
\]
Then
\[
x_i^{h_i}\,dx_i
=\frac1{A_i}e^{-(b_i/A_i)y_i}\,dy_i,
\qquad
\prod_i x_i^{A_i}=e^{-\sum_i y_i}.
\]

For the \(k\) tied coordinates, their sum \(z\) has the simplex-volume factor
\[
\frac{z^{k-1}}{(k-1)!}.
\]
For the untied coordinates, write \(Y=\sum_{i\notin M}y_i\). In the remaining \(z\)-integral substitute
\[
u=t e^{-Y-z}.
\]

After normalization, the limiting \(u\)-integral is
\[
\int_0^\infty u^{\lambda-1}e^{-u}\,du=\Gamma(\lambda),
\]
while the untied coordinates give exponential integrals with rates
\[
b_i/A_i-\lambda>0.
\]

Dominated convergence is supported by a bound of the form
\[
u^{\lambda-1}e^{-u}
(1+|\log u|+Y)^{k-1}
\prod_{i\notin M}e^{-(b_i/A_i-\lambda)y_i}.
\]

For \(k=1\), keep the domain indicator explicitly; avoid treating its disappearance as an identity involving a zeroth power of a positive part.

This route gives the exact constant. Dyadic decomposition is attractive for \(\asymp\), but generally less direct for the Gamma constant.

---

# 7. What is false or missing in the supplied sketch?

## 7.1 The claimed LP finite-limit theorem is false under the displayed hypotheses

Take one monomial with
\[
A=(2,2),\quad h=(0,0),\quad \beta=0,\quad c=1,
\]
primal optimizer \(a=(1/2,0)\), and dual variable \(y=1/2\).

These satisfy the displayed primal/dual conditions, but
\[
t^{1/2}Z(t)\sim\frac{\sqrt\pi}{4}\log t\to\infty.
\]

Therefore the shown `LPData` cannot imply
\[
t^\Lambda Z(t)\to C\in(0,\infty)
\]
without additional hypotheses eliminating log degeneracy and ensuring an integrable rescaled profile.

The excerpt itself says the theorem was not found. I would audit the actual theorem statement before treating it as an available black box. An exponent statement such as
\[
-\frac{\log Z(t)}{\log t}\to\Lambda
\]
is compatible with logarithmic factors.

## 7.2 Your fibre exponents lie outside the shown `LPData`

The transformed \(\kappa_j\) and \(r_j\) may be negative. The cutoff is also a new upper constraint in logarithmic coordinates. Neither is covered by the displayed nonnegative-exponent LP model.

## 7.3 The atlas excerpt bounds absolute units

`a_bounds` bounds \(|a|\), not a positive phase coefficient. Analyticity and nonvanishing alone do not imply \(F\geq0\). The positive-loss/sign-sector reduction must be explicit.

## 7.4 The displayed `WallChartsData` forgets phase data

The displayed fibre identity returns transport data, but not the atlas’s `phase`, `kF`, `a`, and unit bounds. To formally connect the two layers, preserve a common chart index and a compatibility witness, or return an enriched chart package.

## 7.5 Substituting the desired \(\theta\) needs support bookkeeping

The displayed identity requires a globally continuous function supported inside the specified thin region. The raw function \(e^{-tF(z',s)}\phi(z')\) need not satisfy that condition as a function on all coordinates.

For a fixed sufficiently small schedule, insert a truth cutoff equal to one on the schedule, and ensure the spatial support hypotheses. If \(\phi\) does not vanish appropriately at the boundary of \(A'\), a simple zero extension may not be continuous.

---

# 8. A realistic Lean plan

I would use six public-facing lemmas. The full constrained polyhedral theorem is a separate infrastructure project; it is not realistically a single 150-line lemma with only the listed anchors.

| Order | Lemma / output | Main reuse |
|---|---|---|
| 1 | **Normalize signed branch kernels.** Orthant split, positive magnitudes, exact moving cutoff, phase and density identities. | `wallSolve_density`, phase analogue, `Real.rpow_*`, existing branch measurability |
| 2 | **Moving-unit comparison.** Positive unit bounds and weight bounds sandwich a chart between constant-unit constrained models; supported-weight/indicator equivalence. | Monotonicity of integrals and `Real.exp`; no LP machinery |
| 3 | **Certified moving-kernel limit.** From exact rescaled integral identities and `RescaledData`, output \(Z/L\to C\), \(Q/L\to J\), with a separate positivity criterion for \(C\). | `RescaledData`, dominated convergence, finite sums |
| 4 | **Single-monomial power–log asymptotic.** Statement (10)–(11), first for the tied block, then with untied factors. | `integral_prod` / `lintegral_prod`, Gamma integral, dominated convergence |
| 5 | **LP/profile compatibility.** Given a chosen rescaling or sector certificate, verify \(\lambda=\gamma p+b\cdot\alpha\), truth feasibility, phase feasibility, and the profile’s normalization. | Algebraic fibre formulas; a new constrained LP certificate, not the existing `LPData` unchanged |
| 6 | **Finite dominant-cluster assembly.** Select the winning power–log pair; sum tied constants; move all lower pairs into remainders. | `powLog`, `ChartAssembly.tendsto_weighted_sub`, finite-sum limits |

### Size expectations

Lemmas 2, 3, 5, and 6 are plausible at roughly your target size once interfaces are settled. Lemmas 1 and 4 will need auxiliary results.

For lemma 4, the likely prerequisites are:

- a one-dimensional logarithmic change-of-variables identity;
- a tied-coordinate simplex convolution identity;
- integrability of the Gamma kernel with fixed logarithmic moments.

`integral_rpow_mul_exp_neg_mul_rpow` is an excellent anchor for the one-coordinate/no-log case and useful integral estimates. It does not by itself supply the tied-coordinate convolution. `Real.Gamma` plus dominated convergence is the natural endpoint for the general tied case.

I would **not** begin by proving the full constrained power–log constant theorem. First prove the constant theorem from a profile certificate, then construct certificates for:

1. a unique dominant scale;
2. a truth-boundary/phase-boundary critical scale;
3. the explicit single-monomial tied block.

That immediately connects the formalized wall kernels to the formalized expectation limits, while keeping the genuinely new polyhedral analysis isolated.