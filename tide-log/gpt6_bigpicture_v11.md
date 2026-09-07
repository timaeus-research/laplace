The next major target should be **continuity of the composite coefficient maps, followed by distributional transfer and normalised remainders**. That directly addresses the paper’s missing justification, rather than merely extending the deterministic calculus.

Three important corrections first:

1. Your composite bound can probably **avoid the geometric factor** by using `ampCoeff_lipschitz`, not its coordinatewise corollary.
2. The complement of a small box is **not** generally a region where the monomial phase is bounded below.
3. The Gaussian example gives an infinite **expected asymptotic coefficient** above the threshold—not, in the compact-chart setup, an infinite expected integral at fixed \(n\).

## (a) Composite continuity: yes, and use the stronger estimate

Write
\[
D_x=\|x-x'\|_\rho,\qquad D_y=\|y-y'\|_\rho,
\]
and assume
\[
\|x\|_\rho,\|x'\|_\rho\le M_x,\qquad
\|y'\|_\rho\le M_y,\qquad \beta>0.
\]

For the moment parameters appearing in `coeffNorm`, set
\[
H_q(M_x)=
\int_0^\infty
s^{\alpha-1}(1+|\log s|)^\ell s^q
e^{-\beta s^2+2\beta M_xs}\,ds,
\qquad q=0,1.
\]
Under the appropriate near-zero moment condition—typically \(\alpha>0\)—both are finite. For the tail, one convenient estimate is
\[
-\beta s^2+2\beta M_xs
\le -\frac{\beta}{2}s^2+2\beta M_x^2.
\]

### Avoiding the radius-loss factor

If `wnorm` is indeed the weighted sum of absolute coefficients, then for \(0<r\le\rho\),
\[
\begin{aligned}
\operatorname{coeffNorm}_{\beta,\alpha,\ell,r}(c-c')
&=\int_0^\infty
s^{\alpha-1}(1+|\log s|)^\ell e^{-\beta s^2}
\|c_s-c'_s\|_r\,ds\\
&\le D_yH_0(M_x)+2\beta M_yD_xH_1(M_x).
\end{aligned}
\]
The first equality needs a justified nonnegative sum–integral interchange; establish finiteness rather than relying on unrestricted real-valued `tsum`.

Thus, schematically,
\[
|A_\alpha(x,y)-A_\alpha(x',y')|
\le C_A\bigl(H_0D_y+2\beta M_yH_1D_x\bigr),
\]
and similarly for \(B_\alpha\), using whichever moments their bounds require.

Your \((1-r/\rho)^{-2}\) estimate is valid as a coordinatewise route, but it throws away the weighted-\(\ell^1\) information you have already proved. **Prefer the norm-level route.** A strict \(r<\rho\) may still be needed elsewhere in the Taylor-tree hypotheses; this particular estimate does not require a geometric loss.

### What this proves relative to the paper

This is the honest missing argument for:

> The d=2 chart coefficient functionals are continuous, indeed Lipschitz on norm-bounded sets, in the weighted analytic coefficient topology.

For fixed \(\eta\), restrict to the \(x\)-variable. For random or varying amplitudes, retain joint continuity in \((x,y)\). Finite chart sums and finite coefficient vectors then inherit continuity.

It is **not yet a theorem about every interpretation of \(C^\omega(U)\)**. The topology on real-analytic functions needs care: a fixed holomorphic neighbourhood, a compact-open holomorphic topology, and an inductive-limit topology of analytic germs are different constructions.

Your proposed bridge is mathematically right in a fixed-polydisc setting:
\[
\|x-x'\|_\rho
\le (1-\rho/R)^{-2}\,
\|\widetilde\xi-\widetilde\xi'\|_{\infty,\overline D_R^2}.
\]
For a holomorphic function defined only on the open \(R\)-polydisc, use an intermediate radius below \(R\), unless extension to the closed polydisc is available.

**Recommendation:** define and formalise the weighted-array topology now. Stage the Cauchy bridge as an explicitly **unformalised compatibility statement**, not as a proved identification with the paper’s \(C^\omega\) space. Iterating one-variable Cauchy estimates is worthwhile eventually, but it should not block the probability layer.

## (b) Representation and distributional transfer

### Prefer a weighted wrapper around `lp`

I would use rescaling into Mathlib’s \(\ell^1\):
\[
a_{ij}=\rho^{i+j}x_{ij},
\qquad
x_{ij}=\rho^{-(i+j)}a_{ij},
\qquad \rho>0.
\]

Concretely, introduce a small abstraction—say `AnalyticCoeff ρ`—whose implementation is the relevant `lp … 1`, together with:

- `toArray`;
- membership/weighted-summability equivalence;
- `norm_eq_wnorm`;
- compatibility with addition and subtraction;
- evaluation and coefficient-map wrappers.

Keep the existing array algebra unchanged underneath.

A bespoke metric on `{x // WSummable ρ x}` is initially attractive, but later you will want completeness, separability, normed-group operations, and Borel measurability. The `lp` route gives the right ambient infrastructure without reconstructing it. Avoid making downstream proofs unfold the rescaling.

Also, **use the norm/Borel topology**, not merely the coordinatewise product topology on arrays. Coordinatewise convergence alone does not supply your continuity theorem.

### The CMT theorem is worth its own unit

Yes—even if its final proof is almost exactly `continuous_comp`. Its value is the exported theorem and the fully checked domain topology.

Prefer first proving a **finite-vector version**:
\[
(x_n,y_n)\Rightarrow(x,y)
\quad\Longrightarrow\quad
\bigl(A_{\alpha_1},B_{\alpha_1},\ldots,
A_{\alpha_k},B_{\alpha_k}\bigr)(x_n,y_n)
\Rightarrow
\bigl(A_{\alpha_1},B_{\alpha_1},\ldots\bigr)(x,y).
\]
Scalar statements follow immediately. Joint convergence is what later division and posterior-ratio arguments need.

Be precise that the hypothesis is joint convergence of \((x_n,y_n)\); separate marginal convergence is insufficient in general.

### Normalised remainders: distinguish the two slots

Let
\[
Z_n=\sum_{\gamma<2T}N_n^{-\gamma}
\bigl(A_\gamma(X_n)\log N_n+B_\gamma(X_n)\bigr)+R_n,
\]
where \(N_n\to\infty\), and \(X_n\) packages the arrays. Define
\[
L_{<\alpha,n}
=\sum_{\gamma<\alpha}N_n^{-\gamma}
\bigl(A_\gamma(X_n)\log N_n+B_\gamma(X_n)\bigr).
\]

For \(\alpha<2T\), the two statements should be:
\[
\frac{Z_n-L_{<\alpha,n}}
     {N_n^{-\alpha}\log N_n}
\Rightarrow A_\alpha(X),
\]
and
\[
\frac{Z_n-L_{<\alpha,n}
      -N_n^{-\alpha}A_\alpha(X_n)\log N_n}
     {N_n^{-\alpha}}
\Rightarrow B_\alpha(X).
\]

The subtraction in the second formula must use the **current random coefficient** \(A_\alpha(X_n)\), not the limiting one.

The proof has three ingredients:

1. Current coefficient convergence by CMT.
2. Higher retained terms vanish after normalisation.
3. The uniform remainder vanishes because \(2T-\alpha>0\).

For the first slot, \(B_\alpha(X_n)/\log N_n\) must also vanish. Uniform boundedness handles it, but tightness is enough.

### Bounded families first; localisation next

Your bounded-family statement is an excellent first theorem. Require bounds almost surely for each \(n\), rather than unnecessarily pointwise for every \(\omega\). Include measurability of the normalised integral/random error; your new parameter-measurability results should supply it.

But clearly label it as a **bounded analytic-family transfer theorem**. It does not yet handle nondegenerate Gaussian limits for the fluctuating array under a fixed deterministic norm bound.

The natural upgrade is:
\[
\Pr(|E_n|>\delta)
\le
\Pr(\|X_n\|>M)
+
\Pr(|E_n|>\delta,\ \|X_n\|\le M).
\]
On the ball, use the deterministic bound \(K(M)a_n\to0\); outside it, use norm boundedness in probability. Norm tightness follows from norm-valued distributional convergence in the standard setting.

This upgrade does **not** require moments of \(K(\|X_n\|)\), nor a probabilistic Arzelà–Ascoli theorem. It is the right route to Gaussian-valued limits.

## (c) The far-region tail: useful, but state the region correctly

Yes, this is a small, valuable paper-facing unit.

State it abstractly on a measurable set \(E\), assuming
\[
K(w)\ge\varepsilon>0,\qquad |\psi(w)|\le M
\]
almost everywhere there, and integrability of \(|\eta|\). Then
\[
\left|\int_E
\eta(w)e^{-\beta nK(w)+\beta\sqrt{nK(w)}\psi(w)}
\,d\mu(w)\right|
\le
\left(\int_E|\eta|\,d\mu\right)
e^{-\beta n\varepsilon/2+\beta M^2/2}.
\]

Use a supplied bound \(M\), rather than building a supremum API into the first theorem. The paper’s supremum is a corollary.

**Do not use “outside the small box” without an additional hypothesis.** For
\[
K(u_1,u_2)=u_1^{2k_1}u_2^{2k_2},
\]
points outside \([0,\delta]^2\) can still approach either coordinate axis, so \(K\) can approach zero. The correct region is \(\{K\ge\varepsilon\}\).

Probabilistically, if \(M_n^2=O_p(1)\), this yields
\[
Z_n^{(2)}=O_p(e^{-\beta\varepsilon n/2}),
\]
and therefore
\[
Z_n^{(2)}=o_p(e^{-cn})
\qquad\text{for every }c<\beta\varepsilon/2.
\]
Do not claim little-\(o_p\) at the exact displayed rate from this bound alone.

## (d) Gaussian example: valuable, with a corrected conclusion

For
\[
A(X)=C\int_0^\infty s^{p-1}e^{-\beta s^2+\beta Xs}\,ds,
\qquad C>0,\ p>0,
\]
and \(X\sim N(0,\sigma^2)\), Tonelli and the Gaussian exponential moment give
\[
\mathbb E[A(X)]
=
C\int_0^\infty s^{p-1}
e^{-(\beta-\beta^2\sigma^2/2)s^2}\,ds.
\]
Consequently,
\[
\mathbb E[A(X)]
=A(0)(1-\beta\sigma^2/2)^{-p/2}
\]
when \(\beta\sigma^2<2\), and the extended expectation is \(+\infty\) when \(\beta\sigma^2\ge2\).

Strict inequality over \(A(0)\) requires \(\sigma^2>0\). The degenerate Gaussian gives equality.

### The important correction

This does **not** show that the original compact-chart \(Z_n\) has infinite expectation at fixed \(n\).

Writing the bounded monomial coordinate as \(t=u^k\), Gaussian averaging gives
\[
\mathbb E\!\left[e^{-\beta nt^2+\beta\sqrt n\,tX}\right]
=
e^{-(\beta-\beta^2\sigma^2/2)nt^2}.
\]
For fixed \(n\), this is bounded on the compact chart, even above the threshold. With an integrable amplitude, \(\mathbb E[Z_n]\) is finite.

What the example actually demonstrates is more interesting and more accurate:

> Samplewise asymptotic expansions and distributional convergence do not justify averaging asymptotic coefficients. The expected leading coefficient can be infinite, and rare fluctuations can change the averaged asymptotic regime.

This is not a counterexample to `twoD_taylor_tree_expectation'`: its domination/integrability hypotheses must fail in the problematic regime.

### Scope relative to Hypothesis I

Do not claim this is an empirical-process example satisfying Hypothesis I without constructing such a statistical model. Relative finite variance may constrain the variance parameter, depending on its exact constant, but \(s=2\) alone does not establish the required temperature threshold.

Also, a CLT does not imply convergence of exponential moments. Even when the finite-\(n\) MGFs exist, the displayed Gaussian approximation is initially a fixed-\(s\) statement; it supplies no domination for the integral over all \(s\).

**Worth doing, but after distributional transfer.** Stage it as a “constant-Gaussian fluctuation model,” not as a theorem about the full empirical process.

In Lean, use `lintegral`/extended nonnegative expectation for the threshold theorem. A real Bochner integral is not the representation of “expectation \(=+\infty\).” Grep the pinned Gaussian MGF API first; I would not budget around an unverified lemma name.

## (e) General \(d\): still defer the full tree

The smallest attractive analytic theorem is the **equal-ratio monomial model**. For
\[
I_d(N)=
\int_{[0,1]^d}
\prod_i u_i^{h_i}
e^{-\beta N\prod_i u_i^{2k_i}}\,du,
\qquad
\frac{h_i+1}{2k_i}=\lambda>0,
\]
the substitutions \(t_i=u_i^{2k_i}\) give, for \(d\ge1\),
\[
I_d(N)=
\frac{\prod_i(2k_i)^{-1}}{(d-1)!}
\int_0^1
z^{\lambda-1}(-\log z)^{d-1}e^{-\beta Nz}\,dz.
\]
Hence
\[
I_d(N)\sim
\frac{\Gamma(\lambda)\beta^{-\lambda}}
{(d-1)!\prod_i2k_i}
N^{-\lambda}(\log N)^{d-1}.
\]

This makes pole multiplicity/log degree visible without introducing the full face machinery. It could later support a constant-fluctuation variant.

Rough planning estimates, not commitments:

| Target | Additional focused units |
|---|---:|
| Finite-coordinate \(2^d\)-face algebra only | 4–8 |
| Equal-ratio model and leading asymptotic | 8–15 |
| Full general-\(d\) analytic Taylor tree | 40–80+ |

The model theorem is roughly a sixth to a quarter of the 62-unit d=2 arc. The full theorem is another substantial programme; its difficulty is not simply enumerating \(2^d\) faces.

## (f) Next five units

| Rank | Unit | One-line specification |
|---|---|---|
| **1** | Composite coefficient stability | Bound `coeffNorm (ampCoeff … − ampCoeff …)` using the norm-level estimate and Gaussian-log moments; export bounded-set Lipschitz bounds for \(A,B\). |
| **2** | Weighted analytic coefficient space | Wrap rescaled `lp … 1`, bridge its norm to `wnorm`, and prove composite coefficient continuity. |
| **3** | Joint coefficient distributional transfer | Apply CMT to any finite vector of canonical coefficients under joint array-valued convergence in distribution. |
| **4** | Ordered normalised remainder transfer | Prove the \(A\)-slot and \(B\)-slot Slutsky statements first for uniformly bounded analytic families. |
| **5** | Far-phase exponential negligibility | Prove the abstract \(\{K\ge\varepsilon\}\) AM–GM integral bound and its bounded-in-probability consequence. |

Immediately afterward: **localise rank 4 to norm-bounded-in-probability families**, then the Gaussian averaging example. If “unit” must remain small, split rank 4’s deterministic normalisation lemma from its probabilistic wrapper rather than compressing both artificially.

## Statements to stage

In `learning-theory/projects/grammar/staging/leanref-fluctuation.md`, distinguish **proved**, **next**, and **mathematical compatibility only**.

### Already proved

- **d=2 Taylor-tree expansion:** deterministic remainder uniform under the stated envelope hypotheses.
- **Parameter measurability:** canonical coefficients and integrated standard integrals are measurable under the formalised joint-measurability assumptions.
- **Integrated/expectation expansions:** valid under the explicit domination and integrability hypotheses.
- **Taylor-data identification:** a represented analytic function has mixed derivatives \(i!j!x_{ij}\); representing arrays are unique.
- **Stability components:** amplitude coefficients are locally Lipschitz in weighted array norms; canonical coefficient maps satisfy linearity and difference bounds on the envelope class.
- **End-to-end represented-function chain:** represented analytic functions → unique arrays → amplitude coefficients → canonical coefficients.

### After the next units

- **Coefficient continuity:** d=2 coefficient functionals are locally Lipschitz in weighted analytic coefficient norms, supplying a rigorous chart-level justification for the continuity asserted in §4.3.
- **Distributional transfer:** joint convergence of analytic coefficient arrays implies joint convergence of finite coefficient vectors.
- **Ordered random asymptotics:** normalised \(A\)- and \(B\)-remainders converge in distribution under the stated bounded-family, later localisation, hypotheses.
- **Far-region control:** an abstract phase-gap estimate isolates the exponentially negligible contribution.

### Explicit limitations

- No formal identification yet with the paper’s full \(C^\omega\) topology.
- No formal empirical-process functional CLT or resolution/chart assembly.
- No general-\(d\) Taylor-tree theorem.
- No unrestricted interchange of expectation and asymptotic expansion.
- The future Gaussian example concerns an extended expected coefficient, not infinite fixed-\(n\) compact-chart integrals.

That staging tells a strong but accurate story: **the d=2 deterministic calculus is complete enough that the next work should close the analytic continuity and probabilistic transfer gap.**
