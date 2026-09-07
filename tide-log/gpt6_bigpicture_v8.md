Querying gpt-6-astra (timeout: 560s)...
Response received in 219.5s
## Recommendation

The shortest honest route is:

1. **Normalize the existing 2D formula into canonical pole coefficients**, checking the logarithmic sign on one monomial.
2. **Prove cutoff independence of those coefficients**, then package the equal-starting-exponent theorem as `twoD_taylor_tree_equal`.
3. **Generalize the cutoff assembly—not the coefficient algebra—to unequal starting exponents.**
4. Prove the finite-part/series identification.
5. Add a **uniform-family remainder theorem** for parameter integration.

I would not start general-\(d\) analytic amplitudes yet.

Two important qualifications:

- A theorem “for every \(T\), there exist coefficients” is weaker than the paper. Define **one coefficient family independent of \(T\)**.
- With your definition
  \[
  M[\alpha;1;f]=\int_0^\infty s^{\alpha-1}\log s\,e^{-\beta s^2}f(s)\,ds,
  \]
  the collision transfer accompanying \(+\log N\) contains **\(-M[\alpha;1;f]\)**. This deserves the first regression test.

I cannot verify where hypotheses enter your existing files from the descriptions alone; below I distinguish mathematical consequences from the code audit needed.

---

# (a) Statement shape and exact coefficients

Write
\[
\alpha_i=\frac{h_1+i+1}{k_1},\qquad
\delta_j=\frac{h_2+j+1}{k_2},\qquad
\mu=\alpha/2.
\]

Use rational numbers for the exponent labels if convenient:
```lean
def poleU (i : ℕ) : ℚ := (h₁ + i + 1 : ℚ) / (2 * k₁)
def poleV (j : ℕ) : ℚ := (h₂ + j + 1 : ℚ) / (2 * k₂)
```
with \(k_1,k_2>0\). Cast into \(\mathbb R\) only for `Real.rpow` and comparisons with a real cutoff.

### Canonical coefficient functions

Let \(c=\mathrm{ampCoeff}\,\beta\,x\,y\), and put
\[
a_i(v,s)=\sum_j c_{ij}(s)v^j,\qquad
b_j(u,s)=\sum_i c_{ij}(s)u^i.
\]

For a positive exponent \(\alpha\), define the functions of \(s\)
\[
U_\alpha(s)=
\begin{cases}
k_1^{-1}\operatorname{FP}_{k_2\alpha-h_2-1}(a_i(\cdot,s)),
 &\alpha=\alpha_i,\\
0,&\text{otherwise},
\end{cases}
\]
and
\[
V_\alpha(s)=
\begin{cases}
k_2^{-1}\operatorname{FP}_{k_1\alpha-h_1-1}(b_j(\cdot,s)),
 &\alpha=\delta_j,\\
0,&\text{otherwise}.
\end{cases}
\]

Both indices are unique whenever they exist. Define
\[
C_\alpha(s)=
\begin{cases}
\dfrac{c_{ij}(s)}{k_1k_2},
 &\alpha=\alpha_i=\delta_j,\\
0,&\text{otherwise}.
\end{cases}
\]

Then the canonical coefficients in the **\(N\)-normalization** are
\[
\boxed{
 A_\mu=M_\beta[2\mu;0;C_{2\mu}],
}
\]
\[
\boxed{
 B_\mu=M_\beta[2\mu;0;U_{2\mu}+V_{2\mu}]
       -M_\beta[2\mu;1;C_{2\mu}].
}
\]

These formulas use the convention
\[
\operatorname{FP}_\gamma(v^j)=
\begin{cases}
b^{j-\gamma}/(j-\gamma),&j\ne\gamma,\\
\log b,&j=\gamma.
\end{cases}
\]
If your `axisPrim` has another resonant convention, translate the constant coefficient accordingly.

**Consequences:**

- \(A_\mu=0\) away from collisions.
- A collision contributes **one**, not two, copies of \(c_{ij}/(k_1k_2)\).
- The cutoff indices do not appear in the definitions.

### First necessary lemma: finite-part cutoff independence

If your finite part takes a truncation parameter, prove
\[
\operatorname{FP}^{M}_\gamma(a)
=\operatorname{FP}^{M'}_\gamma(a)
\quad\text{when }M>\gamma,\ M'>\gamma.
\]

Then define a canonical finite part using, for example,
\[
M(\gamma)=\left\lceil\max(\gamma,0)\right\rceil_{\mathbb N}+1.
\]

This is the cleanest way to prevent the Taylor-tree coefficients from secretly depending on \(T\).

### Finite exponent set

Define
\[
\Lambda_{<T}
=\{\mu<T:\mu=\alpha_i/2\text{ or }\mu=\delta_j/2\}.
\]

A straightforward finite implementation is to use
\[
K_\ell(T)=\left\lceil 2k_\ell\max(T,0)\right\rceil_{\mathbb N},
\]
take the images of `Finset.range K₁` and `Finset.range K₂`, union them, and filter by `< T`. These bounds overenumerate harmlessly.

The theorem should have the shape
```lean
theorem twoD_taylor_tree_equal ... :
  ∀ T : ℝ,
    (fun N =>
      Z N -
        ∑ μ ∈ polesBelow h₁ h₂ k₁ k₂ T,
          N ^ (-(2 * (μ : ℝ))) *
            (A μ * Real.log N + B μ))
      =O[atTop]
        (fun N => N ^ (-(2 * T)) * (1 + Real.log N))
```
where `A` and `B` are previously defined functions, not existentially chosen inside `∀ T`.

Taking all of \(\Lambda\) is sufficient. If desired, define \(\Lambda^*\) afterward by removing labels whose polynomial vanishes.

### Exact cutoff choice in the equal case

Let
\[
p=\frac{h_1+1}{k_1}=\frac{h_2+1}{k_2},\qquad
R=\max(1,2T-p),
\]
and choose
\[
\boxed{M_\ell=\lceil k_\ell R\rceil_{\mathbb N}.}
\]

Then \(M_\ell>0\), and
\[
\frac{M_\ell-1}{k_\ell}<R\le\frac{M_\ell}{k_\ell}.
\]
Thus both compatibility inequalities hold, and
\[
p+\min(M_1/k_1,M_2/k_2)\ge 2T.
\]

Every pole below \(2T\) is included. Terms retained by these cutoffs but with exponent \(\alpha\ge2T\) can be discarded into the requested remainder, since for \(N\ge1\),
\[
N^{-\alpha}(1+\log N)\le N^{-2T}(1+\log N).
\]

### Regrouping strategy

Use a tagged index type for the two axis families:
```lean
(Fin M₁) ⊕ (Fin M₂)
```
and its exponent map. Regroup this finite sum over the image by fibers.

- `Finset.sum_image` is appropriate for each individual axis map, since each is injective.
- It is **not** appropriate without fibers for the combined map: collisions are precisely its noninjectivity.
- Use the `Finset.sum_fiberwise` / `Finset.sum_fiberwise_of_maps_to` family where its local signature fits.
- A robust fallback is `Finset.sum_bij` on the finite type of pairs “exponent plus an element of its fiber.”

I would add a project-local regrouping lemma rather than repeat the library-dependent plumbing. Prove that every fiber has one or two elements, and handle those cases explicitly.

Before this step, establish the normal form
\[
\begin{aligned}
\mathrm{reducedSum}(N)
={}&\sum_{i<M_1}N^{-\alpha_i}M[\alpha_i;0;U_{\alpha_i}]\\
&+\sum_{j<M_2}N^{-\delta_j}M[\delta_j;0;V_{\delta_j}]\\
&+\sum_{\substack{i<M_1,\ j<M_2\\\alpha_i=\delta_j}}
N^{-\alpha_i}
\bigl(M[\alpha_i;0;C_{\alpha_i}]\log N
      -M[\alpha_i;1;C_{\alpha_i}]\bigr).
\end{aligned}
\]
Here the \(U,V\) summands mean their corresponding individual axis contributions. This is the decisive bookkeeping lemma.

### Paper normalization

For \(N=\sqrt n\),
\[
N^{-2\mu}(A_\mu\log N+B_\mu)
=n^{-\mu}\left(\frac{A_\mu}{2}\log n+B_\mu\right).
\]

Thus the paper’s polynomial is
\[
P_\mu(X)=\frac{A_\mu}{2}X+B_\mu.
\]

---

# (b) Unequal starting exponents

There is no useful general reduction by shifting to equal starting exponents. The right extension is a **general cutoff assembly theorem using the existing general face formulas**.

Let
\[
p_1=(h_1+1)/k_1,\qquad p_2=(h_2+1)/k_2.
\]

The corrected compatibility conditions are
\[
\boxed{
p_1+\frac{M_1-1}{k_1}
<
p_2+\frac{M_2}{k_2},
}
\]
\[
\boxed{
p_2+\frac{M_2-1}{k_2}
<
p_1+\frac{M_1}{k_1}.
}
\]

The expected remainder exponent is
\[
\boxed{
q_M=\min\left(p_1+\frac{M_1}{k_1},
              p_2+\frac{M_2}{k_2}\right),
}
\]
with the safe bound \(O(N^{-q_M}(1+\log N))\).

An exact universally safe choice is
\[
q=\max(2T,p_1,p_2)+1,\qquad
M_\ell=\left\lceil k_\ell(q-p_\ell)\right\rceil_{\mathbb N}.
\]
Then
\[
p_\ell+(M_\ell-1)/k_\ell<q
\le p_\ell+M_\ell/k_\ell.
\]

### Does the general face expansion already suffice?

Mathematically, yes, **if** its actual theorem hypotheses permit arbitrary base exponent.

For the face \(v^j b_j(u,s)\), the base exponent and transverse parameter are
\[
\delta_j=p_2+j/k_2,\qquad
\gamma'_j=k_1\delta_j-h_1-1.
\]
Its generated exponents are
\[
\delta_j+\frac{i-\gamma'_j}{k_1}
=\frac{h_1+i+1}{k_1}
=\alpha_i.
\]

The resonance condition is
\[
i=\gamma'_j
\iff \alpha_i=\delta_j.
\]

That identity is independent of \(p_1=p_2\). The analogous statement holds for the other face.

What requires an audit is whether your proved face theorem has additional restrictions on \(\gamma\), positivity, or the truncation order that were automatically satisfied in the equal case. In particular, the unequal extension must allow negative \(\gamma\).

### Which face carries the logarithm?

There is no canonical choice of one face. In a symmetric face-minus-corner decomposition:

- each face containing a resonant monomial generates a logarithmic contribution;
- the corner correction removes the duplicate;
- the final coefficient is symmetric and has one copy.

An implementation may assign each collision to one axis after cancellation, but that is bookkeeping, not geometry.

### Correct unequal corner formula

For a monomial \(c_{ij}(s)u^iv^j\), put
\[
a=\alpha_i,\quad d=\delta_j,\quad B=b^{k_1+k_2}.
\]
The state density, before multiplying by \(c_{ij}(s)\), is zero outside \(0<t<B\), and inside that interval is
\[
D_{ij}(t)=
\begin{cases}
\displaystyle
\frac{
b^{k_2(d-a)}t^{a-1}
-
b^{k_1(a-d)}t^{d-1}
}{k_1k_2(d-a)},
&a\ne d,\\[1.2em]
\displaystyle
\frac{t^{a-1}}{k_1k_2}
\bigl((k_1+k_2)\log b-\log t\bigr),
&a=d.
\end{cases}
\]

These, rather than formulas expressed only through \(i/k_1-j/k_2\), are the corner formulas needed in the unequal theorem. Collision testing must use
\[
k_2(h_1+i+1)=k_1(h_2+j+1).
\]

---

# (c) Finite parts and absolutely convergent coefficient series

**Yes: this is worth proving.** It is the clean bridge from a rigorous cutoff theorem to the paper’s coefficient description.

For a row \(z_j=c_{ij}(s)\), assume
\[
\sum_j |z_j|\rho^j<\infty,\qquad 0<b<\rho.
\]
Define
\[
q_\gamma(j)=
\begin{cases}
b^{j-\gamma}/(j-\gamma),&j\ne\gamma,\\
\log b,&j=\gamma.
\end{cases}
\]

Prove:
\[
\boxed{
\operatorname{FP}_\gamma\left(v\mapsto\sum_jz_jv^j\right)
=\sum_j z_jq_\gamma(j),
}
\]
and
\[
\boxed{\sum_j |z_jq_\gamma(j)|<\infty.}
\]

A useful strengthened form is the bounded-linear-functional estimate
\[
\left|\operatorname{FP}_\gamma(a)\right|
\le C_{\gamma,b,\rho}\sum_j|z_j|\rho^j.
\]

### Do not start with the \(\varepsilon\to0\) proof

Your subtracted-integral definition makes a shorter proof available.

Choose \(J>\gamma\). Then
\[
\operatorname{FP}_\gamma(a)
=
\int_0^b v^{-\gamma-1}
\left(a(v)-\sum_{j<J}z_jv^j\right)\,dv
+\sum_{j<J}z_jq_\gamma(j).
\]
Inside the integral the remainder is
\[
\sum_{j\ge J}z_jv^{j-\gamma-1},
\]
and
\[
\sum_{j\ge J}
|z_j|\int_0^b v^{j-\gamma-1}\,dv
=
\sum_{j\ge J}
|z_j|\frac{b^{j-\gamma}}{j-\gamma}
<\infty.
\]

Use the Bochner integral/`tsum` interchange theorem—normally through `MeasureTheory.integral_tsum`—after proving the required summability of integral norms. The exact arguments depend on the local Mathlib version and whether you express the integral using a restricted measure.

This avoids a separate uniform-convergence theorem on \([\varepsilon,b]\), subtraction of divergent terms, and a limit interchange.

### Explicit moment series

For example, the \(u\)-axis contribution at \(\alpha_i\) becomes
\[
\frac1{k_1}\sum_j q_{\gamma_i}(j)
M_\beta[\alpha_i;0;c_{ij}].
\]

Writing \(a=x-x_{00}\delta\), set
\[
d_{ij,n}=(y*a^{*n})_{ij}.
\]
Then
\[
c_{ij}(s)
=e^{\beta sx_{00}}
\sum_{n\ge0}\frac{(\beta s)^n}{n!}d_{ij,n},
\]
so
\[
M_\beta[\alpha;\ell;c_{ij}]
=
\sum_{n\ge0}\frac{\beta^n}{n!}d_{ij,n}
\int_0^\infty
s^{\alpha+n-1}(\log s)^\ell
e^{-\beta s^2+\beta sx_{00}}\,ds.
\]

For fixed \((i,j)\), the inner sum is actually finite because \(a_{00}=0\): \(d_{ij,n}=0\) for \(n>i+j\).

Prove absolute summability of the **joint** \((j,n)\)-family before rearranging it. Your exponential majorant supplies this: after absolute values, the \(s\)-integrand is bounded by a constant times
\[
s^{\alpha-1}(1+|\log s|)\,
e^{-\beta s^2+\beta s(x_{00}+X_\rho)}.
\]

Finally, \(t=s^2\) converts these into the paper’s Gaussian fluctuation moments, with the factor \(1/2\) and the corresponding powers of \(t\). At collisions, derivatives with respect to the Mellin exponent produce the logarithmic moments.

Also reuse your Taylor-data identification: weighted coefficient arrays mirror “series in derivatives” only after that identification is included.

---

# (d) Parameter adapter: uniform families first

Given the stated compact-support application, **the uniform-family theorem is less work and the better next target**.

Do not try to extract a measurable function of \(w\) by choosing a Big-O constant separately for every \(w\). That selection need not be measurable.

Aim for:

> For fixed structural parameters and a common envelope
> \[
> |c_{ij}(w,s)|\rho^{i+j}\le C_0e^{\beta Ls}
> \]
> for almost every \(w\), there exist \(C,N_0\), independent of \(w\), such that
> \[
> |Z_w(N)-S_w(N)|
> \le C N^{-q_M}(1+\log N)
> \]
> for almost every \(w\) and every \(N\ge N_0\).

Better still, formulate a core theorem where \(C,N_0\) are chosen **before the coefficient family**:
\[
\exists C,N_0\ \forall c,\quad
\operatorname{Envelope}(c;C_0,L,\ldots)
\Longrightarrow
\forall N\ge N_0,\ \operatorname{Bound}(c,N).
\]

This is uniformity in the analytic input, without yet needing measurability infrastructure.

### How to obtain the common envelope

It suffices that, almost everywhere,
\[
Y_\rho(w)\le\overline Y,\qquad
x_{00}(w)+X_\rho(w)\le\overline L.
\]
Then use \(C_0=\overline Y\), \(L=\overline L\).

Analyticity on a suitable common compact neighbourhood can give such bounds after choosing a common radius and, if necessary, shrinking the chart box. State the common weighted-norm bound explicitly rather than treating real analyticity alone as that bound.

### Converting the threshold to \(N\ge1\)

Your `param_integration` needs bounds beginning at \(1\). Add a small adapter extending the common estimate over \(1\le N\le N_0\), using:

- a common bound for \(Z_w(N)\);
- common coefficient bounds;
- positivity of \(N^{-q_M}(1+\log N)\) on that compact interval.

Then \(K(w)=C\) is measurable. It is integrable under a finite parameter measure. Alternatively, integrate against the measure with density \(\rho_I\).

Measurability of \(A(w),B(w),Z_w(N)\) is a separate lemma, using measurable coefficient evaluations and parameter-integral measurability.

### Does \(t_w\) occur?

- If all \(w\)-dependence is in \(\xi_w,\eta_w\), then \(t_w=1\).
- If the phase is
  \[
  -\beta N^2q(w)^2u^{2k},
  \]
  with matching fluctuation scaling, then \(t_w=q(w)\).
- For a retained monomial factor in noncritical coordinates, this often means \(t_w=w^{k_{\rm nc}}\).

Thus it depends on the chart normal form, not on parameter integration itself.

One further distinction: your current `param_integration` handles a **single leading exponent**. It applies after a leading-order corollary of the Taylor-tree theorem. Integrating a whole finite expansion deserves a simple finite-sum extension.

---

# (e) General \(d\)

A bare implication `Cutoff d → Cutoff (d+1)` is not yet the right induction statement.

The induction hypothesis would need:

1. amplitudes depending on auxiliary variables and on \(s\);
2. uniform envelopes and quantitative remainder bounds;
3. stability under face restriction, Taylor projection, and finite parts;
4. compatibility of the coefficient operators with these operations.

A codimension-one Taylor face is a \((d-1)\)-variable amplitude coupled to a remaining monomial variable; it is not directly an instance of an ordinary fixed-amplitude asymptotic theorem.

### Mathematical sequence

A viable general-\(d\) programme is:

1. **Monomial product-density transfer:** arbitrary shifted exponents, all pole multiplicities, including \(s\)-dependent coefficient functions.
2. **Operator-valued face expansion:** coefficients produced by the appropriate multivariable finite-part/residue operators, uniformly in remaining parameters.
3. **Taylor inclusion–exclusion identity:** your `TaylorProjections` supplies the algebra.
4. **Remainder estimates for every projection pattern:** each unexpanded coordinate gains its truncation order; the safe logarithmic degree is \(d-1\).
5. **Pole regrouping and coefficient coherence.**

Your constant-\(\xi\) all-\(d\) theorem is a substantial part of step 1, but not automatically its needed uniform \(s\)-dependent version.

### Definitions and scope

If beginning that programme, define the \(d\)-variable integral over `Fin d → ℝ` and prove the hard-coded \(d=1,2\) integrals equal the corresponding instances by Fubini. **Do not reprove the completed 2D theory merely to change its representation.**

For now, the strongest economical advertised scope is:

> **Constant \(\xi\), all \(d\); analytic \(\xi\), \(d\le2\), arbitrary positive \(k_i\) and admissible \(h_i\).**

That is preferable to an isolated \(d=3\) theorem unless \(d=3\) is required by an application.

---

# (f) SLT application

There is a distinction between a deterministic fluctuation functional and its stochastic limit.

### Deterministic leading coefficient

In the equal 2D case, with common starting exponent \(p\),
\[
c_{00}(s)=\eta(0,0)e^{\beta s\xi(0,0)}.
\]
Consequently,
\[
\boxed{
A_{p/2}
=
\frac{\eta(0,0)}{k_1k_2}
\int_0^\infty s^{p-1}
e^{-\beta s^2+\beta s\xi(0,0)}\,ds.
}
\]

This is the coefficient of \(N^{-p}\log N\). The coefficient of \(n^{-p/2}\log n\) is half of it.

**Do not extend the “depends only on \(\xi(0)\)” claim to the entire leading polynomial.** Its constant term generally depends on axis data. Nor does it hold for the leading coefficient in a general unequal-start case: that coefficient can depend on \(\xi\) along the surviving critical face.

### Continuity is the useful next analytic result

For each fixed \(\mu\), prove continuity of
\[
(x,y)\longmapsto(A_\mu,B_\mu)
\]
in the weighted-\(\ell^1_\rho\) topology. Local Lipschitz estimates are feasible:

- convolution and evaluation are bounded;
- the exponential is locally Lipschitz with an \(s e^{Cs}\) majorant;
- finite parts are bounded linear functionals;
- Gaussian damping integrates the resulting majorants.

Together with a locally uniform remainder theorem, this is the deterministic infrastructure needed for a continuous-mapping argument.

The genuinely stochastic SLT step is that an appropriate normalization of the partition function is asymptotically a fluctuation functional evaluated at \(\xi_n\), and that this functional converges in law when \(\xi_n\Rightarrow G\). Your machinery supplies the deterministic functional and its approximation—not the empirical-process convergence or tightness. Also, a CLT in a weaker function-space topology does not automatically imply convergence in your weighted-\(\ell^1\) topology.

Without the subsection’s exact statement, I would not identify a more specific stochastic claim as already covered.

---

# (g) Next six units and regression tests

| Rank | Unit | One-line specification |
|---|---|---|
| 1 | `TwoDCanonicalCoefficients` | Prove finite-part cutoff independence and reduce the existing face/corner expression to the canonical \(U,V,C\) formula. |
| 2 | `TwoDTaylorTreeEqual` | Define finite pole sets and global \(A_\mu,B_\mu\), choose exact cutoffs, regroup, and provide the \(n=N^2\) adapter. |
| 3 | `TwoDCutoffGeneral` | Replace equal-start compatibility by shifted compatibility, use the unequal monomial corner formula, and derive general 2D Taylor-tree. |
| 4 | `AxisFinitePartSeries` | Prove boundedness and `tsum` commutation of finite parts, then the absolutely convergent fluctuation-moment coefficient formula. |
| 5 | `TwoDUniformFamily` | Obtain common remainder constants from a common envelope and feed the leading expansion to parameter integration. |
| 6 | `TaylorTreeCoefficientContinuity` | Prove weighted-norm continuity/local Lipschitz bounds and identify the highest leading-log fluctuation functional. |

Rank 3 may naturally occupy more than one file. I would not conceal its corner/remainder audit inside a “wrapper” unit.

## Mandatory monomial tests

Set \(c_{ij}(s)=f(s)\) for one index pair and zero elsewhere.

### 1. Collision, \(b=1\)

For \(\alpha_i=\delta_j=\alpha\), the transferred expression must be
\[
\boxed{
\frac{N^{-\alpha}}{k_1k_2}
\left(M[\alpha;0;f]\log N-M[\alpha;1;f]\right).
}
\]

If your actual `transferTerm … 1 f` produces a plus sign on the second moment, then either its input convention differs or the displayed normal form is wrong. With the moment definition in the question, this sign is fixed by \(\log(s/N)=\log s-\log N\).

### 2. Collision, \(b\ne1\)

It must be
\[
\boxed{
\frac{N^{-\alpha}}{k_1k_2}
\left[
M[\alpha;0;f]\bigl(\log N+(k_1+k_2)\log b\bigr)
-M[\alpha;1;f]
\right].
}
\]

This detects missing or double-counted resonant `axisPrim` constants.

### 3. Noncollision

For \(a\ne d\), it must be
\[
\boxed{
\frac{1}{k_1k_2(d-a)}
\left[
b^{k_2(d-a)}N^{-a}M[a;0;f]
-
b^{k_1(a-d)}N^{-d}M[d;0;f]
\right].
}
\]

These formulas use moments over \((0,\infty)\); the exact box integral uses moments truncated at \(Nb^{k_1+k_2}\). Their difference is the Gaussian tail, not zero.

### 4. A higher collision with unequal starts

Use \(k_1=k_2=1,\ h_1=0,\ h_2=1\). Then the collision is \(i=j+1\), not \(i=j\). This detects any surviving equal-start collision predicate.

### 5. Normalization check

The collision coefficient is \(1/(k_1k_2)\) in the \(N,\log N\) convention and \(1/(2k_1k_2)\) in the \(n,\log n\) convention. Comparing directly with residues of denominators \(2k_i z+\cdots\) without changing variables can otherwise create a spurious factor-of-two discrepancy.

**Bottom line:** the next theorem should be a canonical, cutoff-independent 2D Taylor-tree wrapper. The hardest remaining issue is not grouping a `Finset`; it is ensuring the existing finite-part and collision conventions yield exactly the canonical monomial formulas above.
