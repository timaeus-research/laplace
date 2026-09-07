Querying gpt-6-astra (timeout: 540s)...
Response received in 202.8s
## Recommendation

**Use (D) for the next theorem, then discharge its series hypothesis by a weighted-ℓ¹ version of (E). Do not make higher Schwarz a dependency of the paper-facing result.**

More specifically:

- Prove an **analytic-series-to-rectangular-data adapter**. It should produce exactly the compatible face data and envelopes consumed by your existing cutoff theorem.
- Next, construct the amplitude series for \(\eta e^{\beta s\xi}\) using **convolution and the exponential in a weighted coefficient algebra**, rather than starting with `MvPolynomial`.
- Retain the existing compatibility-based theorem as the general abstract result. There is nothing weak about that theorem if it is named and presented as a rectangular-data theorem rather than as an unconditional smooth theorem.
- Defer (B) as an independent Mathlib contribution. It is valuable, but it is not the shortest route to a theorem matching the paper’s assumptions.

One important qualification: an analytic coefficient envelope for \(e^{\beta s\xi}\) may have an exponential rate larger than the real supremum of \(\xi\). You must check that the resulting rate still fits your moment-integrability budget.

---

## (a) The precise theorem to formalise first

### Inputs

Fix
\[
0<b<\rho,\qquad M_1,M_2\in\mathbb N,
\]
and write
\[
\theta=b/\rho<1.
\]

Let
\[
c:\mathbb N\times\mathbb N\to\mathbb R\to\mathbb R
\]
be the coefficient family, with \(s\ge0\). Assume

\[
|c_{ij}(s)|\rho^{i+j}\le H(s),
\qquad H(s)\ge0,
\]
and, on \([0,b]^2\),
\[
\Phi(u,v,s)=\sum_{(i,j)\in\mathbb N^2}c_{ij}(s)u^iv^j.
\]

For the envelope specialization, assume
\[
H(s)\le C_0(1+s)^D e^{\beta sL},
\qquad C_0\ge0.
\]

For later parameter integration, also assume each \(s\mapsto c_{ij}(s)\) is measurable; with an additional parameter \(w\), use joint measurability in \((w,s)\).

**Do not require convergence on the boundary \(|u|=|v|=\rho\).** The coefficient bound alone gives absolute convergence on every strictly smaller polydisc, including your working square. Boundary convergence is unnecessary here.

### Define the face data

Set
\[
a_i(v,s)=\sum_{j=0}^\infty c_{ij}(s)v^j,
\qquad
b_j(u,s)=\sum_{i=0}^\infty c_{ij}(s)u^i.
\]

Define the rectangular remainder
\[
\begin{aligned}
R(u,v,s)={}&\Phi(u,v,s)
-\sum_{i<M_1}u^ia_i(v,s)
-\sum_{j<M_2}v^jb_j(u,s)\\
&+\sum_{i<M_1}\sum_{j<M_2}c_{ij}(s)u^iv^j.
\end{aligned}
\]

The theorem should return:

1. Absolute summability of all relevant series.
2. The face expansions with the **same** \(c_{ij}\).
3. The tail identity
   \[
   R(u,v,s)
   =\sum_{\substack{i\ge M_1\\j\ge M_2}}
      c_{ij}(s)u^iv^j.
   \]
4. The following normalized bounds.

Writing \(E(s)=(1+s)^D e^{\beta sL}\):

| Data | Bound |
|---|---|
| \(c_{ij}(s)\) | \(C_0\rho^{-i-j}E(s)\) |
| \(a_i(v,s)\) | \(C_0\rho^{-i}(1-\theta)^{-1}E(s)\) |
| \(b_j(u,s)\) | \(C_0\rho^{-j}(1-\theta)^{-1}E(s)\) |
| \(a_i-\sum_{j<M_2}c_{ij}v^j\) | \(H_i(s)v^{M_2}\) |
| \(b_j-\sum_{i<M_1}c_{ij}u^i\) | \(H'_j(s)u^{M_1}\) |
| \(R(u,v,s)\) | \(C_{\rm mix}E(s)u^{M_1}v^{M_2}\) |

Here
\[
H_i(s)=
\frac{C_0\rho^{-i-M_2}}{1-\theta}E(s),
\qquad
H'_j(s)=
\frac{C_0\rho^{-M_1-j}}{1-\theta}E(s),
\]
and
\[
\boxed{
C_{\rm mix}
=\frac{C_0\rho^{-M_1-M_2}}{(1-\theta)^2}.
}
\]

Thus the mixed envelope has **the same \(D,L\)** as the original coefficient envelope.

I would prove this first for an arbitrary nonnegative function \(H\), then add a short corollary specializing \(H\) to the exponential-polynomial envelope. That keeps all geometric-series reasoning independent of the Laplace machinery.

### Lean encoding

Use a product-indexed coefficient function as the primary representation:

```lean
c : ℕ × ℕ → ℝ → ℝ
```

and product-indexed summability:

```lean
Summable (fun ij : ℕ × ℕ =>
  ‖c ij s * u ^ ij.1 * v ^ ij.2‖)
```

Define faces by one-variable `tsum`. Convert between product sums and iterated sums only through proved summability.

For tails, **reindex by shifts**, rather than carrying subtypes or indicator functions throughout:

```lean
fun ij : ℕ × ℕ =>
  c (M₁ + ij.1, M₂ + ij.2) s *
    u ^ (M₁ + ij.1) * v ^ (M₂ + ij.2)
```

A particularly useful first helper is:

> If \(|d_{ij}|\le A r^i t^j\), with \(A\ge0\) and \(0\le r,t<1\), then the product family is absolutely summable and its absolute sum is at most \(A/((1-r)(1-t))\).

That helper, plus one-dimensional prefix/tail splitting, does almost all the work. You should need only a small interface to the product-`tsum` API, not repeated ad hoc Fubini arguments.

### Discharging the amplitude-series hypothesis

For \(\xi,\eta\), the clean next hypothesis is the stronger weighted-ℓ¹ condition at radius \(\rho\):

\[
Y_\rho=\sum_{i,j}|y_{ij}|\rho^{i+j}<\infty,
\]
\[
X_{\rho,+}=\sum_{(i,j)\ne(0,0)}
             |x_{ij}|\rho^{i+j}<\infty.
\]

Write
\[
\xi=x_{00}+\xi_+.
\]

For \(s\ge0,\ \beta\ge0\), the coefficient array of
\(\eta e^{\beta s\xi}\) satisfies
\[
\sum_{i,j}|c_{ij}(s)|\rho^{i+j}
\le
Y_\rho e^{\beta s(x_{00}+X_{\rho,+})}.
\]

Consequently, the adapter applies with
\[
C_0=Y_\rho,\qquad D=0,\qquad
L=x_{00}+X_{\rho,+}.
\]

This is sharper than replacing \(L\) by the full absolute coefficient norm of \(\xi\), because it preserves the sign of the constant term.

You need only coefficient convolution and its weighted norm inequality. Since \(\xi_+\) has zero constant coefficient, each exponential coefficient is a finite sum over exponential orders \(n\le i+j\), apart from the factor \(e^{\beta s x_{00}}\). This also gives a convenient measurability proof.

**Caution:** \(L=x_{00}+X_{\rho,+}\) is a coefficient-norm majorant, not generally \(\sup_{[0,b]^2}\xi\). If your moment theorem requires a strict upper bound on \(L\), establish that by shrinking the chart/radius or by a sharper majorant. Do not silently substitute the real-axis supremum.

---

## (b) The geometric bounds

Yes, both bounds in the question are correct.

For \(0\le u,v\le b\),
\[
\begin{aligned}
\sum_{\substack{i\ge M_1\\j\ge M_2}}
 |c_{ij}(s)|u^iv^j
&\le H(s)
 \sum_{i\ge M_1}(u/\rho)^i
 \sum_{j\ge M_2}(v/\rho)^j\\
&=
H(s)\frac{(u/\rho)^{M_1}(v/\rho)^{M_2}}
 {(1-u/\rho)(1-v/\rho)}\\
&\le
H(s)\frac{(u/\rho)^{M_1}(v/\rho)^{M_2}}
 {(1-b/\rho)^2}.
\end{aligned}
\]

Likewise,
\[
\left|a_i(v,s)-\sum_{j<M_2}c_{ij}(s)v^j\right|
\le
H(s)\rho^{-i}
\frac{(v/\rho)^{M_2}}{1-b/\rho}.
\]

These give exactly the envelopes required by `faceMoments_of_envelope`, with the constants above. The geometric argument preserves \(D,L\); the separate restrictions on \(L\) needed for integrability still have to hold.

---

## (c) Merge the log families: worthwhile, and simpler than `sum_eq_single`

Let
\[
\lambda_i=i/k_1,\qquad \mu_j=j/k_2,
\]
and define the collision finset
\[
\mathcal C=
\{(i,j)\in \operatorname{range}(M_1)\times
                 \operatorname{range}(M_2):\lambda_i=\mu_j\}.
\]

For arbitrary pointwise weights \(W_{ij}(s)\), prove the elementary identity
\[
\begin{aligned}
&\sum_{i<M_1}\sum_{j<M_2}
 [\lambda_i=\mu_j]W_{ij}(s)\\
&\quad+
\sum_{j<M_2}\sum_{i<M_1}
 [\mu_j=\lambda_i]W_{ij}(s)\\
&\quad-
\sum_{i<M_1}\sum_{j<M_2}
 [\lambda_i=\mu_j]W_{ij}(s)
=
\sum_{(i,j)\in\mathcal C}W_{ij}(s).
\end{aligned}
\]

Here brackets mean an `if ... then ... else 0`.

For the coefficients in your question, take
\[
W_{ij}(s)=\frac{c_{ij}(s)}{k_1k_2}.
\]

For the transferred expression, if \(\mathcal M_r\) denotes your existing Mellin functional at exponent \(r\), the merged contribution is
\[
\boxed{
\frac{\log N}{k_1k_2}
\sum_{(i,j)\in\mathcal C}
N^{-(p+i/k_1)}
\mathcal M_{p+i/k_1}[c_{ij}].
}
\]
This uses your normalization of the listed log coefficients.

### Proof strategy

First prove, once, the resonance equivalences:
\[
j=k_2i/k_1
\iff i/k_1=j/k_2
\iff k_1j/k_2-i=0,
\]
assuming \(k_1,k_2>0\).

Then:

1. Rewrite all three predicates to the same collision predicate.
2. On the collision branch, rewrite every exponent/functional parameter using \(\lambda_i=\mu_j\).
3. Use `Finset.sum_comm` for the v-face family.
4. The result is literally \(C+C-C=C\).
5. Convert the double indicator sum to the filtered product finset.

**No `sum_eq_single` is necessary.** It is useful only if you want to replace each inner sum by a unique resonant index. Keeping collision pairs avoids that arithmetic bookkeeping.

Do this before integration or Mellin transfer where convenient. The merger itself is a pointwise finite-sum identity.

---

## (d) General \(d\)

### First algebraic unit: abstract operators, ordered composition

Prove the algebraic theorem on an arbitrary real module \(E\), for supplied linear endomorphisms
\[
P_\ell:E\to_{\mathbb R}E.
\]

Neither derivatives nor idempotence are needed for inclusion–exclusion. Commutativity is needed only to make subset products independent of ordering.

I would **not** start with `Finset.prod` in `Module.End`: multiplication there is noncommutative. Use an ordered list of coordinate operators and composition recursion.

An especially short first theorem uses
\[
R_0=I,\qquad F_0=0,
\]
\[
R_{n+1}=(I-P_n)R_n,
\qquad
F_{n+1}=F_n+P_nR_n.
\]

Then induction gives
\[
\boxed{I=F_n+R_n}
\]
using only additivity and distributivity. No commutation is required.

A second lemma identifies
\[
F_d=
\sum_{\varnothing\ne S\subseteq\operatorname{Fin}d}
(-1)^{|S|+1}P_S,
\]
where \(P_S\) is composition in the fixed coordinate order. The powerset induction splits subsets according to whether they contain the newest coordinate. With pairwise commutation, \(P_S\) acquires the expected order-independent interpretation.

This separation gives you:

1. a very short reusable decomposition theorem;
2. the signed face-lattice interpretation as a separate combinatorial theorem.

### Explicit jets versus derivatives

For the first algebraic unit, **neither**: take the \(P_\ell\) abstractly.

For the analytic instantiation, coefficient truncation is ideal. On multi-index coefficient arrays, define
\[
(P_\ell c)_\alpha=
\begin{cases}
c_\alpha,&\alpha_\ell<M_\ell,\\
0,&\text{otherwise}.
\end{cases}
\]

These are linear, idempotent, and commute by pointwise `if` reasoning. Then transport the resulting identity through series evaluation.

Two cautions:

- Arbitrary jets assigned to one particular \(\Phi\) do not by themselves define linear operators on a function space.
- Derivative-based projections are not automatically linear maps on the space of **all** functions. Use an appropriate regularity space if you take that route.

The coefficient-array realization avoids both issues.

### First analytic unit: the product pushforward identity

Assume \(d\ge1\), \(b_\ell,k_\ell,p>0\), and
\[
h_\ell=k_\ell p-1,\qquad
R=\prod_\ell b_\ell^{k_\ell}.
\]

The clean theorem is the pushforward identity, initially for nonnegative measurable \(F\):
\[
\boxed{
\int_{\prod_\ell(0,b_\ell)}
 F\!\left(\prod_\ell u_\ell^{k_\ell}\right)
 \prod_\ell u_\ell^{h_\ell}\,du
=
\frac1{(d-1)!\prod_\ell k_\ell}
\int_0^R F(r)r^{p-1}
       \log(R/r)^{d-1}\,dr.
}
\]

Then extend to signed \(F\) under absolute integrability.

The conceptual derivation is logarithmic:
\[
x_\ell=u_\ell^{k_\ell},\qquad
t_\ell=\log(b_\ell^{k_\ell}/x_\ell).
\]
The sum \(T=\sum t_\ell\) has the simplex-volume factor
\[
T^{d-1}/(d-1)!,
\]
and \(r=Re^{-T}\).

But **formally, reuse `iterDivPrim` if it already contains the corresponding iterated product identity**. Generalize its test kernel to arbitrary nonnegative measurable \(F\), if needed, and obtain the displayed density theorem as a corollary. Do not introduce a new simplex-integration development merely for a slicker paper proof.

---

## (e) Instantiating `param_integration`

I recommend **(ii): a quantitative theorem directly from `face_transfer_bound` and `prodKernel_le_equal`**, then recover the existing `IsBigO` theorem as a corollary.

Reworking the entire second-order theorem is unnecessary if the desired deliverable is the first-order parameter-integrable block.

### Unscaled parameter theorem

Suppose, for \(N\ge N_0\),
\[
|Z_w(N)-N^{-p}(A(w)\log N+B(w))|
\le K(w)N^{-q}(1+\log N),
\]
where \(p<q\) and \(N_0\) is independent of \(w\).

The direct inputs are:

- measurability of \(Z_w(N)\), \(A(w)\), \(B(w)\), and \(K(w)\);
- integrability of \(A,B,K\) against the parameter measure, including any external weight;
- common \(p,q,N_0\).

Then integrate the inequality. Constants need not all be uniform: a measurable integrable \(K(w)\) is enough.

### The scaled noncritical-coordinate block

Usually the more relevant form is
\[
\int \omega(w) Z_w(N\tau(w))\,d\mu(w),
\]
with \(\tau(w)>0\) almost everywhere.

The candidate main coefficients are
\[
\bar A=\int \omega(w)\tau(w)^{-p}A(w)\,d\mu(w),
\]
\[
\bar B=\int \omega(w)\tau(w)^{-p}
              \bigl(B(w)+A(w)\log\tau(w)\bigr)\,d\mu(w).
\]

The main obstacle is that \(N\tau(w)\) need not be large uniformly in \(w\).

#### Patch the bound to all positive arguments

Use the bounded-kernel estimate to obtain
\[
|Z_w(t)|\le G(w),\qquad 0<t\le1.
\]

For \(q>p>0\), the large-\(t\) estimate then extends to
\[
|Z_w(t)-t^{-p}(A(w)\log t+B(w))|
\le \widetilde K(w)t^{-q}(1+|\log t|),
\qquad t>0,
\]
with, for example,
\[
\widetilde K=K+G+|A|+|B|.
\]

For \(N\ge1\),
\[
1+|\log(N\tau)|
\le 1+\log N+|\log\tau|.
\]

Therefore the integrated remainder is bounded by
\[
N^{-q}(1+\log N)
\int |\omega(w)|\widetilde K(w)\tau(w)^{-q}
                (1+|\log\tau(w)|)\,d\mu(w).
\]

This avoids a moving small-\(\tau\) region and a parameter-dependent asymptotic threshold.

### Noncritical gap condition

For
\[
\tau(w)=\prod_\ell w_\ell^{k_\ell},
\qquad
|\omega(w)|\sim\prod_\ell w_\ell^{h_\ell},
\]
and bounded envelope constants, the required integrability follows from
\[
h_\ell-k_\ell q>-1
\quad\text{for every noncritical coordinate}.
\]

Thus choose
\[
\boxed{
p<q<\min_\ell\frac{h_\ell+1}{k_\ell},
}
\]
also respecting the rate available from the two-dimensional theorem.

Equality at an endpoint is not harmless: it produces logarithmic divergence and indicates another critical coordinate.

### Constants to expose

Your quantitative theorem should expose enough data to build measurable \(K(w)\):

- amplitude and face-envelope constants;
- mixed-remainder constant;
- coefficient/finite-part moment bounds;
- the explicit product-kernel moment constants;
- radius-margin factors such as \((1-b/\rho)^{-1}\);
- denominators coming from exponent gaps;
- the exponential-rate margin needed for the \(s\)-integrals.

Keep geometric parameters and gap lower bounds uniform where practical. Allow amplitude-size constants to depend measurably on \(w\), provided the final weighted majorant is integrable.

For \(A(w),B(w)\), prove measurability from their explicit finite sums and parameter integrals—not from the existence of asymptotic coefficients.

---

## (f) Next five units

1. **Double-series geometric adapter.**  
   Product summability, compatible faces, rectangular tail identity, and explicit envelopes. This immediately connects analyticity-style data to your finished cutoff theorem.

2. **Weighted coefficient closure for \(\eta e^{\beta s\xi}\).**  
   Convolution norm bound, exponential coefficients, series evaluation, and the rate \(L=x_{00}+X_{\rho,+}\). Avoid a large polynomial abstraction layer.

3. **Quantitative equal-exponent first-order theorem.**  
   Build it directly from explicit face transfer and product-kernel bounds. Include the finite-sum log merger here as a small cleanup lemma.

4. **Noncritical-parameter integration adapter.**  
   First patch the estimate to all \(t>0\); then prove the scaled \(N\tau(w)\) integration theorem with the weighted logarithmic moment condition.

5. **General-\(d\) algebraic skeleton.**  
   Recursive \(I=F+R\), powerset expansion, and commuting coefficient truncations. Keep general-\(d\) analysis out of this unit.

After those, the natural sixth unit is the **general-\(d\) product-density theorem extracted from `iterDivPrim`**. Higher smooth Schwarz remains a worthwhile independent project, but it should no longer block the paper theorem.
