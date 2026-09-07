**Recommendation: B2 → A2 → D2 if required by the chart domains → hand-off.** Keep C2 out of scope. Do E2 only as a narrowly stated dictionary.

Estimates below are additional units, assuming reuse of the existing limit and probability infrastructure.

### 1. B2: finite chart assembly — **2–4 units; GO**

This is the biggest remaining paper-facing gap.

The minimal honest theorem takes a finite family with
\[
I_{a,N}/\bigl(N^{-p_a}(\log N)^{m_a-1}\bigr)\to L_a.
\]
Define
\[
p_*=\min_a p_a,\qquad
m_*=\max\{m_a:p_a=p_*\}.
\]
Then
\[
\frac{\sum_a I_{a,N}}{N^{-p_*}(\log N)^{m_*-1}}
\longrightarrow
\sum_{a:(p_a,m_a)=(p_*,m_*)}L_a.
\]

Add:

- numerator/denominator assembly, assuming the selected denominator sum is positive;
- grouping charts into strata by a finite indexing map;
- optionally an explicitly negligible non-chart remainder.

**Important:** assemble numerator and denominator separately. The posterior limit is a **ratio of sums**, not a sum of chart posterior limits.

**Gate:** call this a *conditional chart-assembly theorem*. Resolution, change of variables, Jacobians and partition-of-unity identities remain hypotheses until supplied. Minimum exponent wins; at that exponent, **maximum** logarithmic multiplicity wins—not ordinary lexicographic minimum.

### 2. A2: general-d stochastic transfer — **4–8 units; GO**

**Use continuous phases, not finite Taylor coefficients.** Your deterministic theorem already supports the correct topology. No new uniform Stone–Weierstrass development should be needed.

Write \(F_N(\eta,\xi)\) for the normalized integral. On
\(\|\eta\|_\infty\le A,\ \|\xi\|_\infty\le M\), the mean-value estimate gives
\[
|e^{\beta s\xi}-e^{\beta s\xi'}|
 \le \beta s e^{\beta Ms}\|\xi-\xi'\|_\infty.
\]
For \(s\ge0\), absorb \(\beta s\) into \(C e^{\beta s}\). Thus the phase difference is controlled by the normalized integral with **constant phase \(M+1\)**. Amplitude differences are controlled by constant phase \(M\).

Headline XIII makes those scalar normalized integrals eventually bounded. Consequently, \(F_N\) is **eventually equi-Lipschitz on bounded input sets**. Pointwise convergence plus finite nets now gives uniform convergence on compact input sets.

This is cheaper than uniform polynomial approximation. An alternative is compact-uniform convergence of the bounded zero-phase linear operators applied to the compact image \(\{\eta\xi^j\}\).

Then reuse/generalize the existing tightness and continuous-mapping transfer:
\[
(\eta_n,\xi_n)\Rightarrow(\eta,\xi)
\quad\Longrightarrow\quad
F_n(\eta_n,\xi_n)\Rightarrow F(\eta,\xi).
\]

**Gates:**

- Put inputs in \(C([0,b]^d)\), including the boundary.
- For multiple observables/charts, require **joint convergence**, preserving dependence.
- Require the limiting denominator positive almost surely.
- Separate this transfer theorem from proving the paper’s empirical-process convergence. The latter is a distinct deliverable, potentially much larger.

### 3. D2: signed orthants with phase — **1–3 units; conditional GO**

Cheap if the signed change-of-variables infrastructure already exists, but **symmetrizing only \(\eta\) is generally wrong**.

For integer \(k_i\), set
\[
\varepsilon_\sigma=\prod_i\sigma_i^{k_i}.
\]
On the orthant \(x=\sigma u\),
\[
x^{2k}=u^{2k},\qquad
x^k\xi(x)=u^k\bigl[\varepsilon_\sigma\xi(\sigma u)\bigr].
\]
Apply XIII separately with
\[
\eta_\sigma(u)=\eta(\sigma u),\qquad
\xi_\sigma(u)=\varepsilon_\sigma\xi(\sigma u),
\]
and sum over orthants.

The density must also be reflected honestly: typically it is \(|x|^h\), not a signed \(x^h\). Odd monomials can produce \(J_p(a)+J_p(-a)\), **not** \(2J_p(a)\).

**Gate:** do this before hand-off if the paper actually integrates full signed normal fibres.

### 4. F2: report and hand-off — **1–2 units**

Prefer this after B2 and A2. Stopping now is defensible only with the explicit claim:

> General-dimensional deterministic normal-block leading asymptotics; existing stochastic results remain two-dimensional.

Do not describe XIV alone as the paper’s assembled stochastic expectation expansion.

### 5. E2: Mellin dictionary — **1–2 units for the model identity; defer full continuation**

For the Mellin convention
\[
M(z)=\int u^{kz}\eta(u)u^h\,du,
\]
the model leading pole is at \(z=-p\), of order \(m\), with leading Laurent coefficient
\[
\frac1{\prod_{j\in J}k_j}
\int \eta(\pi u)\prod_{i\notin J}u_i^{h_i-pk_i}\,du.
\]
The factorial appears in the density/logarithmic asymptotic, **not** that Laurent coefficient.

**Gate:** continuity alone does not generally provide meromorphic continuation through the pole. Also, for \(m>1\), say “leading Laurent coefficient,” not simply “residue.” A scalar state-density Mellin transform does not by itself encode a phase varying along the face.

### 6. C2: next pole — **NO-GO**

Still defer. Continuous amplitudes need not admit a power/log subleading expansion at all. Require stronger regularity, explicit pole separation and an actual paper dependency before reopening this.

## Constants and missing paper interfaces

Your constants look correct **provided**
\[
p=\min_i\frac{h_i+1}{k_i},\quad
J=\{i:(h_i+1)/k_i=p\},\quad m=|J|,
\]
with \(k_i>0,\ h_i>-1\). In particular,
\[
\frac{1}{(m-1)!\prod_{j\in J}k_j}
\]
and \(J_p=S_{p/2}/2\) are consistent. XIV’s mixed-ratio face density is correct; its common prefactor cancels.

Three checks matter:

- **Face measure:** integrate over the **inactive coordinates only**. On a unit cube, redundant integration over active coordinates is invisible; on a \(b\)-box it introduces a spurious \(b^m\).
- **Partition cutoffs:** chart amplitudes are normally nonnegative and may vanish, not strictly positive. Extend the positivity interface to positivity of the assembled leading coefficient.
- **Tangential variables:** if a stratum has a remaining base integral, supply either a compact-uniform parameter theorem plus domination, or an explicit integrated-remainder hypothesis.

Finally, translate scales explicitly: if the paper uses sample size \(n=N^2\), then \(\lambda=p/2\) and \(\log n=2\log N\). That changes the reported logarithmic normalization by \(2^{m-1}\).
