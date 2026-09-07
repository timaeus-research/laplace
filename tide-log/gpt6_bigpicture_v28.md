## Executive recommendation

**Freeze Stage 3 as a reviewed milestone, but do not stop there. Next do a short hypothesis/support audit, then Stage 4 by coefficient-space completion of the polynomial theorem.**

The key distinction is:

> Extending from polynomials to absolutely summable power series is a controlled completion problem. Identifying those series with the paper’s analytic hypotheses may be a separate, substantially harder problem.

Do not let those two tasks become one undifferentiated “analytic extension” project. In particular, I would **not** start by building a general `FormalMultilinearSeries` interface.

My assessment below is architectural, based on your statement inventory; v20 should decide whether the existing declarations actually support the proposed interfaces.

---

## 1. Ranking, gates, and estimates

| Priority | Candidate | Recommendation and gate | Estimated units |
|---|---|---|---:|
| 0 | **G: exact hypothesis audit + milestone freeze** | Record exactly what the paper means by analytic, its allowed box sizes, exponent set, and coefficient formula. Incorporate v20 before extending anything. | 1–2 |
| 1 | **B: true spectral support** | Go if Stage-1 support can be propagated through `coeffAt`. Prove the support theorem at the monomial level, not after summing phase orders. | 2–4 |
| 2 | **A: absolutely summable coefficient extension** | Main programme. Go once coefficient functionals have monomial-uniform bounds and the remainder estimate accepts uniform upper bounds on masses. | 8–12 optimistic; **10–15 budget** |
| 3 | **D: general box by scaling** | Low conceptual risk; can run independently. Include coefficient/logarithm transport, not merely an integral identity. | 2–4 |
| 4 | **C: derivative dictionary** | Needed for a literal paper-facing coefficient formula if that formula uses derivatives. Defer until the coefficient theorem is stable. | 4–7 |
| 5 | **E: leading term / sharpness** | **No-go as currently phrased.** First establish the correct leading coefficient under the actual geometric hypotheses. | 3–6 for a correctly restricted result; more for general face formulas |
| — | **F: stop at polynomial theorem** | Appropriate milestone and fallback, not the best endpoint if the goal remains full `thm:TaylorTree`. | 1–2 |

### Is Stage 4 five–ten units or twenty-plus?

- **Five–ten** is plausible for the *bare summable-family extension* if the polynomial theorem already exposes all the necessary quantitative bounds.
- **Ten–fifteen** is the safer planning number, including reviewed coefficient-space infrastructure and stability lemmas.
- **Twenty-plus** becomes realistic if Stage 4 also includes a general Mathlib analytic-function bridge, multivariate Cauchy estimates, or localization needed to cover a merely real-analytic function on the box.

Do not authorize the twenty-plus version implicitly. Make the analytic-hypothesis bridge its own gate.

### The crucial hypothesis audit

A function real analytic on a neighborhood of `[0,1]^d` need not have an origin-centered Taylor series converging on the whole cube. Already
\[
f(x)=\frac1{1+4x^2}
\]
is real analytic on the real line, but its Taylor series at zero has radius \(1/2\).

Thus:

- holomorphy on an origin-centered polydisc of radius \(R>1\) is sufficient;
- a globally absolutely convergent origin-centered power series is sufficient;
- generic real analyticity near the cube does **not** automatically imply either.

If the paper works with a sufficiently small box inside a Taylor neighborhood, scaling may resolve this. If it allows an arbitrary fixed analytic box, localization may be a genuine additional theorem. **Do not call the coefficient-family extension the full paper theorem until this is settled.**

---

## 2. Stage 4 design

### 2.1 Use a small coefficient-space API

For fixed positive dimension \(d\), use
```lean
abbrev MultiIndex := Fin d → ℕ
```
and real coefficient families
```lean
c : MultiIndex d → ℝ
```

For \(r\ge1\), define
\[
\operatorname{mass}_r(c)
  :=\sum_\gamma |c_\gamma|\,r^{|\gamma|},
\qquad |\gamma|=\sum_i\gamma_i,
\]
with the explicit hypothesis
\[
\operatorname{Summable}
  \bigl(\gamma\mapsto |c_\gamma|r^{|\gamma|}\bigr).
\]

A lightweight structure containing the family and its summability proof is enough initially. Provide a named `mass`; do not make construction of a fully bundled Banach algebra a prerequisite.

**Separate the roles of the two radii:**

- The integration/expansion theorem needs only \(r=1\).
- A weighted space with \(r>1\) is useful for obtaining this hypothesis from analyticity and for quantitative truncation rates.

In fact, the strongest convenient core theorem is for **unweighted absolutely summable coefficients**. Weighted analytic spaces then map into it.

### 2.2 Evaluation and the exact function hypothesis

Define
\[
\operatorname{eval}(c,u)=\sum_\gamma c_\gamma u^\gamma.
\]

On the closed cube,
\[
|u^\gamma|\le1,\qquad
|\operatorname{eval}(c,u)|\le\operatorname{mass}_1(c)
\le\operatorname{mass}_r(c).
\]

Use these bounds to obtain:

1. absolute pointwise convergence;
2. uniform convergence on the cube;
3. continuity there;
4. uniform convergence of finite truncations.

For external functions, the exact initial hypothesis should be:
\[
\xi(u)=\operatorname{eval}(c^\xi,u),\qquad
\eta(u)=\operatorname{eval}(c^\eta,u)
\quad(u\in[0,1]^d),
\]
with both coefficient families absolutely summable.

This avoids any ambiguity about what “analytic” currently means in the theorem.

Set
\[
a=c^\xi_0,\qquad
c^J_0=0,\qquad c^J_\gamma=c^\xi_\gamma\quad(\gamma\ne0).
\]
Then
\[
\xi(0)=a,\qquad J(u)=\xi(u)-a,\qquad
|J(u)|\le \operatorname{mass}_1(c^J).
\]

Truncations must retain the constant coefficient. Keeping \(a\) exactly fixed greatly simplifies coefficient convergence and the phase majorants.

### 2.3 Multiplication: submultiplicativity, not equality

Use the usual finite-antidiagonal convolution:
\[
(c*d)_\gamma=\sum_{\alpha+\delta=\gamma}c_\alpha d_\delta.
\]

The required API is:
\[
\operatorname{mass}_r(c*d)
 \le \operatorname{mass}_r(c)\operatorname{mass}_r(d),
\]
\[
\operatorname{eval}(c*d,u)
 =\operatorname{eval}(c,u)\operatorname{eval}(d,u).
\]

Also export
\[
\operatorname{mass}_r(c^{*p})\le\operatorname{mass}_r(c)^p
\]
and the power/product difference estimates needed for continuity.

For example, if both \(x,y\) have mass at most \(B\),
\[
\operatorname{mass}_1(x^{*p}-y^{*p})
 \le p B^{p-1}\operatorname{mass}_1(x-y)
\]
for \(p\ge1\).

Use existing convolution infrastructure if it fits cleanly, but do not reorganize the whole development merely to obtain an abstract algebra instance.

### 2.4 Reuse the polynomial theorem by density

**Recommendation: extend coefficient algebra and coefficient functionals; do not redo all Stage-3 integral proofs for infinite families.**

Choose finite downward-closed truncations, for example
\[
F_m=\{\gamma:\forall i,\ \gamma_i\le m\}.
\]
These are easy to construct, exhaust the index set, and preserve the constant term.

Let \(\xi_m,\eta_m\) be the corresponding polynomials. Their masses are bounded by the original masses, uniformly in \(m\).

Then establish three convergence statements.

#### I. Integral convergence

For every fixed \(N\),
\[
Z_{\xi_m,\eta_m}(N)\longrightarrow Z_{\xi,\eta}(N).
\]

Uniform convergence on the cube, uniform amplitude/phase bounds, and dominated convergence suffice. You do **not** need convergence uniform in unbounded \(N\).

#### II. Coefficient convergence

For each fixed \((\mu,j)\),
\[
A_{\mu,j}(\xi_m,\eta_m)
 \longrightarrow A_{\mu,j}(\xi,\eta).
\]

This is the important new work.

For each phase order \(p\), package the monomial coefficient kernel as a bounded linear functional on coefficient families:
\[
T_{\mu,j,p}(c)
 =K_k\sum_\gamma c_\gamma
   \sum_{q=j}^{n}
   \operatorname{coeffAt}(\rho_{h+\gamma},\mu,q)
   {q\choose j}
   \operatorname{fluctMoment}_p(\mu,q-j).
\]

Gate A gives a bound **uniform in \(\gamma\)**. Hence \(T_{\mu,j,p}\) extends directly from finite support to \(\ell^1\).

Now define
\[
A_{\mu,j}
 =\sum_{p\ge0}\frac{\beta^p}{p!}
   T_{\mu,j,p}\bigl(c^\eta*(c^J)^{*p}\bigr).
\]

This is cutoff-free and visibly the extension of the Stage-3 formula.

Use Gate B for summability in \(p\). For continuity, the power difference estimate introduces a factor \(p\). Absorb it using either:

- the corresponding majorant with an additional \(\sqrt t\); or
- a slightly enlarged mass envelope, such as \(B+1\).

There is still no smallness assumption.

#### III. Uniform remainder constants

Apply the polynomial theorem with the **same** upper bounds
\[
\operatorname{mass}_1(c^\eta),\qquad
\operatorname{mass}_1(c^J),\qquad a
\]
for every truncation.

If necessary, first refactor u238 to accept hypotheses
\[
\|\eta_m\|_1\le E,\qquad \|J_m\|_1\le B
\]
and return a constant depending on \(E,B\), not on the actual list.

Then, for each fixed \(N\ge1\), pass to the truncation limit in
\[
|Z_m(N)-S_{L,m}(N)|
 \le C(E,B,\ldots)N^{-L}(1+\log N)^n.
\]

Because the low-spectrum sum is finite, this passage is straightforward.

**The order is important:** fix \(N\), pass \(m\to\infty\), obtain the same inequality for every \(N\). No exchange of an asymptotic limit with a truncation limit is required.

### 2.5 Interchanging monomial sums with the box integral

Even with the density route, export one general lemma.

On the cube,
\[
\sum_\gamma |c_\gamma u^\gamma|
 \le \operatorname{mass}_1(c).
\]
Thus, for integrable \(F\),
\[
\sum_\gamma\int |c_\gamma u^\gamma F(u)|\,du
 \le \operatorname{mass}_1(c)\int|F(u)|\,du.
\]

This supplies the absolute-integrability hypothesis for the sum/integral exchange. It covers fixed phase orders without rebuilding the entire spectral proof.

Avoid making a giant simultaneous \((p,\gamma,\mu,j)\)-Tonelli theorem the central abstraction. The staged bounds already tell you the safe order of operations.

### 2.6 The single riskiest step

**Inside Stage 4, the riskiest step is coefficient continuity through the infinite phase sum—not convergence of \(Z\).**

Uniform convergence of functions alone does not provide convergence of the required asymptotic coefficients. The monomial-uniform Gate-A bound plus a phase-summable continuity majorant does.

Make that an early gate:

> Before generalizing the final theorem, prove a quantitative coefficient-stability theorem for two polynomial inputs with fixed constant phase term and uniformly bounded coefficient masses.

If this lands, the completion is largely mechanical. If it does not, stop and repair that interface before adding analytic-function machinery.

The separate scope risk remains the identification of the paper’s analytic hypotheses.

---

## 3. Statements to repair or qualify before author hand-off

### A. Label the result as polynomial

The headline should say explicitly:

> Polynomial phase and amplitude, unit cube, positive \(k_i\), positive \(\beta\); cutoff-free lattice-indexed coefficients; quantitative remainder and asymptotic consequences.

“Taylor tree proved” without those qualifiers would overstate the current result.

### B. Distinguish the ambient lattice from the true exponent set

Current coefficients are indexed by an ambient arithmetic lattice. That is mathematically legitimate, but not yet an exported identification with the paper’s \(\Lambda(h,k)\).

Prove B by:
1. support of each monomial density;
2. zero coefficient kernel off the true exponent set;
3. preservation under finite and absolutely convergent sums.

Do not deduce support merely from the remainder theorem.

Also use the paper’s exact definition of \(\Lambda(h,k)\); do not silently substitute a plausible union of arithmetic progressions.

### C. Explain the polynomial-list norm

The equality
\[
\|PQ\|_1=\|P\|_1\|Q\|_1
\]
is correct for an **uncollected list-product mass** with duplicated monomials retained. It is false in general for the canonical coefficient \(\ell^1\)-norm because coefficients can cancel.

Before publication, name this distinction. Stage 4 must use submultiplicativity. Ensure the list-to-coefficient bridge records mass decreasing under collection.

### D. Qualify the numerical checks

The numerical tests are good diagnostics, not evidence for absolute convergence or all-\(N\) uniformity. In particular, stable scaled error over a finite range is not a sharpness theorem.

### E. Do not present the derivative dictionary as formalized

Keep “interpretation only” conspicuous until C lands. The dictionary needs \(\mu>0\), \(\beta>0\), and locally uniform domination for the parameter derivatives, including logarithmic factors.

### F. The proposed leading-term formula is not generally correct

With arbitrary positive \(k_i\), the leading coefficient need not depend only on \(\eta(0)\) and \(\xi(0)\). Noncritical coordinates can survive along a dominant face.

For example, take
\[
d=2,\quad k=(1,1),\quad h=(0,2),\quad \xi=0.
\]
Then the \(N^{-1/2}\) coefficient is
\[
\frac{\sqrt\pi}{2\sqrt\beta}
 \int_0^1 v\,\eta(0,v)\,dv.
\]
Changing \(\eta\) from \(1\) to \(1+u_2\) preserves \(\eta(0)=1\) but changes this coefficient.

An origin-only formula may hold under additional criticality hypotheses—for example, in the fully tied case for the highest logarithmic term—but E must first be stated correctly. Do not use it as a casual consistency corollary.

### G. Disambiguate the indices

In the author-facing statement, use \(N\) for sample size and a separate symbol for the maximal logarithmic degree. Make the relationship between that degree and dimension explicit.

---

## 4. General box and stopping criterion

For D, the basic scaling is clean. Write \(|h|=\sum_i h_i\), \(|k|=\sum_i k_i\). Then
\[
Z_b(N;\xi,\eta)
 =b^{|h|+d}\,
   Z_1\!\left(Nb^{2|k|};\,\xi(b\,\cdot),\eta(b\,\cdot)\right).
\]

Transport the expansion using
\[
\log(Nb^{2|k|})=\log N+2|k|\log b.
\]
This produces a finite triangular transformation of logarithmic coefficients. For quantitative statements, also transport the threshold \(Nb^{2|k|}\ge1\); for `atTop` statements this is harmless.

### Concrete stopping criterion

Stop when one paper-facing theorem, with **no stronger unacknowledged hypotheses**, provides:

1. the paper’s admissible \(\xi,\eta,b,\beta,h,k\);
2. its true exponent set and logarithmic indexing;
3. cutoff-independent, absolutely convergent coefficients;
4. the required remainder for every cutoff;
5. the paper’s coefficient formula, either directly or through a proved derivative dictionary;
6. the stated corollary as an actual consequence;
7. an independent statement-level fidelity review confirming the match.

Leading positivity and sharpness are **not** additional stopping requirements unless the target theorem or corollary asserts them.

If the analytic-hypothesis audit reveals a genuine localization gap, use an explicit intermediate stop:

> Complete and freeze the absolutely summable power-series Taylor-tree theorem, with the general-box bridge and spectral support; publish the remaining analytic-localization gap as a precise separate obligation.

**Immediate next action:** preserve Stage 3, resolve the analytic-hypothesis question, then prove polynomial coefficient stability. That stability theorem is the highest-value technical gate for the next phase.
