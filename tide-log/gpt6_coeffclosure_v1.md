Querying gpt-6-astra (timeout: 540s)...
Response received in 133.3s
## Recommendation

Use **(1), but isolate the finite-fiber bookkeeping in one lemma**. Then prove both weighted-norm closure and evaluation multiplicativity from the same grouping argument.

For the exponential, use **(b)(i)**: finite coefficient formulas, an absolutely summable three-index majorant, and evaluation by rearrangement. Given your completed `twoD_cutoff_analytic`, going back through jet remainders would duplicate substantially more analysis.

I would **not build a graded Banach algebra or use `MvPowerSeries` for this step**. You need a small weighted-series API, not a complete algebraic infrastructure.

---

## (a) Weighted convolution: the shortest robust route

Write
\[
I=\mathbb N^2,\qquad |k|=k_1+k_2,\qquad w_\rho(k)=\rho^{|k|},
\]
and assume throughout that \(\rho>0\). Define
\[
\operatorname{WSummable}_\rho(f)
  :\Longleftrightarrow
  \operatorname{Summable}\bigl(k\mapsto |f_k|w_\rho(k)\bigr).
\]

**Make this summability hypothesis explicit.** A bare inequality involving `tsum` is not a substitute: Lean's `tsum` has a default value for nonsummable families.

### 1. Keep your explicit double-antidiagonal convolution

For \(k=(i,j)\), set
\[
(f*g)_{i,j}
 =\sum_{(p,r)\in A_i}\sum_{(q,t)\in A_j}
       f_{p,q}g_{r,t},
\qquad
A_n=\{(a,b):a+b=n\}.
\]

There is no need for a `HasAntidiagonal (ℕ × ℕ)` instance.

The only indexing bridge you need is between:

- the fiber \(\{(a,b)\in I\times I:a+b=k\}\), and
- \(A_i\times A_j\).

It is the coordinate shuffle
\[
((p,r),(q,t))\longmapsto ((p,q),(r,t)).
\]

Prove once that the `tsum` over the fiber equals your explicit finite double sum. This is a finite equivalence, not a global summability problem. Using a local `Fintype` instance for the fiber is reasonable.

### 2. Group the **weighted** product family

The important family is
\[
H(a,b)=f_a g_b\,w_\rho(a+b)
      =(f_aw_\rho(a))(g_bw_\rho(b)).
\]

The weight identity is just
\[
w_\rho(a+b)=w_\rho(a)w_\rho(b).
\]

Absolute summability of \(H\) follows from weighted summability of \(f,g\). Apply fiberwise grouping to both \(H\) and \(|H|\), along
\[
\operatorname{add}:I\times I\to I.
\]

The signed grouped family is
\[
k\longmapsto w_\rho(k)(f*g)_k.
\]
The nonnegative grouped family is
\[
B_k=\sum_{a+b=k}|f_a|\,|g_b|\,w_\rho(k).
\]

Thus
\[
|(f*g)_k|w_\rho(k)\le B_k,
\qquad
\sum_k B_k=N_\rho(f)N_\rho(g).
\]

Domination gives both conclusions you actually need:
\[
\operatorname{WSummable}_\rho(f*g),
\qquad
N_\rho(f*g)\le N_\rho(f)N_\rho(g).
\]

**Crucial:** do not first try to prove summability of \(f_ag_b\) without weights. Weighted summability at \(\rho<1\) does not imply unweighted summability.

### Useful Mathlib ingredients

The facts you already found are sufficient:

- `HasSum.tsum_fiberwise`
- `tsum_mul_tsum_of_summable_norm`
- `summable_mul_of_summable_norm`
- `Equiv.tsum_eq`
- `norm_tsum_le_tsum_norm`
- summability by nonnegative domination
- `tsum_le_tsum`

For the finite bridge, the relevant tools are finite-type `tsum` conversion, finite-sum reindexing, and antidiagonal membership. I would keep all version-dependent antidiagonal names inside this bridge.

A useful local, reusable abstraction is:

> An absolutely summable family can be pushed forward along a map; the pushed-forward family is absolutely summable, and its \(\ell^1\) norm does not increase.

You can prove that from `HasSum.tsum_fiberwise` applied to the family and its absolute value. It is useful beyond convolution and avoids rebuilding the triangle-inequality argument.

### Why not total-degree regrading first?

Route (2) is mathematically sound, but it asks you to prove an additional blockwise convolution identity or inequality. That entails essentially the same coordinate shuffle, plus degree fibers and an extra layer of sums.

It becomes attractive if you subsequently need many statements about homogeneous blocks. For this closure theorem alone, it is extra machinery.

---

## (b) Precise theorem and exponential construction

Here is the statement I would target. It separates the reusable algebra from the paper-specific amplitude.

### Input

Let \(x,y:I\to\mathbb R\), and define
\[
a_{0,0}=0,\qquad a_k=x_k\quad(k\ne(0,0)).
\]

Assume
\[
\operatorname{WSummable}_\rho(a),\qquad
\operatorname{WSummable}_\rho(y).
\]
Put
\[
X=N_\rho(a),\qquad Y=N_\rho(y).
\]

Suppose, on the box in question,
\[
\xi(u,v)=\sum_{i,j}x_{i,j}u^iv^j,\qquad
\eta(u,v)=\sum_{i,j}y_{i,j}u^iv^j.
\]

The construction below works on the whole closed box
\[
|u|\le\rho,\qquad |v|\le\rho.
\]
In your application you can immediately restrict to \(b<\rho\).

### Construction

Define convolution powers recursively:
\[
a^{*0}=\delta_{(0,0)},\qquad
a^{*(n+1)}=a*a^{*n}.
\]

Prove the support statement
\[
n>|k|\Longrightarrow (a^{*n})_k=0.
\]

Now define
\[
E_k(t)=\sum_{n=0}^{|k|}
       \frac{t^n}{n!}(a^{*n})_k,
\]
and
\[
c_k(s)
 =e^{\beta s x_{0,0}}\,
   (y*E(\beta s))_k.
\]

In Lean, the exponential coefficient sum is naturally over
`Finset.range (k.1 + k.2 + 1)`.

### Output

For every real \(s\),
\[
\operatorname{WSummable}_\rho(c(s)),
\]
and
\[
\boxed{
N_\rho(c(s))
 \le Y\exp\!\bigl(\beta s x_{0,0}+|\beta s|X\bigr).
}
\]

Consequently, for \(\beta\ge0\) and \(s\ge0\),
\[
\boxed{
\sum_{i,j}|c_{i,j}(s)|\rho^{i+j}
 \le Y e^{\beta s(x_{0,0}+X)}.
}
\]

Every individual map \(s\mapsto c_k(s)\) is continuous on \(\mathbb R\).

Finally, whenever \(|u|,|v|\le\rho\),
\[
\boxed{
\sum_{i,j}c_{i,j}(s)u^iv^j
 =\eta(u,v)e^{\beta s\xi(u,v)},
}
\]
with absolute summability of the displayed coefficient evaluation.

The absolute value in the all-real-\(s\) estimate matters. The paper-facing bound generally holds only on the nonnegative parameter domain.

### Proof plan

#### Step 1: Weighted evaluation API

Define
\[
\operatorname{ev}_{u,v}(f)
 =\sum_{i,j}f_{i,j}u^iv^j.
\]

From weighted summability and \(|u|,|v|\le\rho\), prove
\[
\sum_{i,j}|f_{i,j}u^iv^j|\le N_\rho(f).
\]

Then prove
\[
\operatorname{ev}(f*g)=\operatorname{ev}(f)\operatorname{ev}(g).
\]

Use the same addition-fiber bridge as above, now for
\[
(f_a u^{a_1}v^{a_2})(g_b u^{b_1}v^{b_2}).
\]
Absolute summability follows from the evaluation bounds. The algebraic identity is `pow_add`.

This gives, by induction,
\[
\operatorname{ev}(a^{*n})=\operatorname{ev}(a)^n.
\]

You do not need a bundled algebra homomorphism unless it makes your downstream code clearer.

#### Step 2: Power estimates and support

Inductively obtain
\[
N_\rho(a^{*n})\le X^n.
\]

For support, use:

- \(a_{0,0}=0\);
- \(|p+q|=|p|+|q|\);
- if a summand in \(a*a^{*n}\) is nonzero, then \(|p|\ge1\) and \(|q|\ge n\).

Most of the index arithmetic should be handled by `omega` after unfolding degree and antidiagonal membership.

Support implies the scalar `HasSum` identity
\[
E_k(t)=\sum_{n=0}^{\infty}\frac{t^n}{n!}(a^{*n})_k,
\]
because the summands vanish beyond \(|k|\). Keep the **finite formula as the definition**: it makes continuity easy.

#### Step 3: One absolute-convergence lemma for the exponential

Prove joint summability of
\[
(n,k)\longmapsto
 \frac{|t|^n}{n!}|(a^{*n})_k|w_\rho(k).
\]

For each \(n\), its sum over \(k\) is bounded by
\[
\frac{|t|^n}{n!}X^n
 =\frac{(|t|X)^n}{n!}.
\]

The scalar majorant is summable by `Real.summable_pow_div_factorial`. Use the nonnegative/product summability API to assemble the joint family.

This is the main analytic lemma. It yields
\[
N_\rho(E(t))
 \le\sum_n\frac{(|t|X)^n}{n!}
 =e^{|t|X}.
\]

It also supplies every interchange needed for evaluation.

#### Step 4: Identify the exponential

By the preceding joint majorant,
\[
\begin{aligned}
\operatorname{ev}(E(t))
 &=\sum_n\frac{t^n}{n!}\operatorname{ev}(a^{*n})\\
 &=\sum_n\frac{(t\operatorname{ev}(a))^n}{n!}\\
 &=e^{t\operatorname{ev}(a)}.
\end{aligned}
\]

I would prove a tiny scalar helper once:
```lean
-- Schematic statement
lemma hasSum_real_exp_series (z : ℝ) :
    HasSum (fun n : ℕ => z ^ n / (n.factorial : ℝ)) (Real.exp z)
```

Derive it using `NormedSpace.exp_eq_tsum`, the real-exponential identification in your checkout, and `Real.summable_pow_div_factorial`. This keeps cast and exponential-notation cleanup out of the coefficient argument.

Since
\[
\operatorname{ev}(a)=\xi(u,v)-x_{0,0},
\]
convolution multiplicativity and `Real.exp_add` give the claimed amplitude identity.

#### Step 5: Multiply by \(\eta\) and restore the constant

Weighted convolution gives
\[
N_\rho(c(s))
 \le e^{\beta sx_{0,0}}\,Y\,N_\rho(E(\beta s))
 \le Y e^{\beta sx_{0,0}+|\beta s|X}.
\]

Continuity is completely finite-dimensional: \(E_k\) is a polynomial, each coefficient of \(y*E\) is a finite sum, and the remaining factor is an ordinary exponential.

### Feeding `twoD_cutoff_analytic`

Take
\[
L=x_{0,0}+X,\qquad H(s)=Y e^{\beta sL},\qquad D=0.
\]

For \(s\ge0\),
\[
|c_k(s)|\rho^{|k|}
 \le N_\rho(c(s))
 \le H(s).
\]

If your cutoff theorem requires a strictly positive growth constant, use \(C_0=\max(1,Y)\) rather than \(C_0=Y\).

There is no need for continuity of \(s\mapsto N_\rho(c(s))\): use the explicit continuous envelope \(H\).

---

## (c) Pitfalls worth preventing

### Product versus iterated `tsum`

Keep the coefficient index as `ℕ × ℕ` throughout the algebraic module. Convert to iterated sums only at the interface with your existing `dblSum`.

For signed families, establish joint absolute summability before rearranging. Summability of every row alone is not enough.

Likewise, assemble the nonnegative exponential majorant first; then derive summability of the signed evaluation family by domination.

### Antidiagonal namespaces

The natural-number antidiagonal and the generalized `HasAntidiagonal` interface are related but not interchangeable without checking elaboration.

- Choose one explicit natural-number antidiagonal API.
- Give index types explicitly in the finite-fiber bridge.
- Do not ask typeclass inference to construct an antidiagonal on `ℕ × ℕ`.
- Treat exact namespace spellings as checkout-dependent; verify them with `#check`.

This is a good reason to encapsulate the bridge rather than spread antidiagonal expressions through the exponential proof.

### Factorials and scalar expressions

Use one coefficient normalization consistently:
```lean
t ^ n / (n.factorial : ℝ)
```

Avoid switching between division and inverse multiplication except in small helper lemmas. Useful facts include `Nat.factorial_pos` and `Nat.factorial_ne_zero`; transfer positivity/nonzeroness to \(\mathbb R\) with casts.

Typical normalization points are
\[
\left|\frac{t^n}{n!}\right|=\frac{|t|^n}{n!},
\qquad
\frac{|t|^n}{n!}X^n=\frac{(|t|X)^n}{n!}.
\]
Handle these once, using positivity of the factorial cast and `mul_pow`.

### Radius and parameter signs

Require \(\rho>0\), not merely an arbitrary real radius. This makes the weight nonnegative, controls evaluation, and avoids degenerate weight issues.

Require \(s\ge0\) and \(\beta\ge0\) when simplifying \(|\beta s|\) to \(\beta s\). Keep the stronger absolute-value estimate internally.

### The sign and size of \(L\)

Yes: **any finite real \(L\) is harmless for genuinely Gaussian decay**. For example,
\[
e^{-\alpha s^2+\beta Ls},\qquad \alpha>0,
\]
has all polynomial moments on \(s\ge0\), regardless of the sign of \(L\).

Indeed, completing the square—or absorbing the linear term into half the Gaussian—proves this. No inequality \(L\le\sup\xi\) is needed.

In fact \(x_{0,0}+X\) is normally a conservative upper bound for \(\xi\) on the weighted box, so exceeding its actual supremum is expected. The qualification is that your moment theorem must retain a strictly positive quadratic decay coefficient.

---

## (d) Size and module boundaries

A realistic first-pass estimate, including helper lemmas:

| Component | Approximate Lean lines |
|---|---:|
| Finite-fiber/antidiagonal bridge | 100–200 |
| Weighted convolution and evaluation API | 150–300 |
| Convolution powers and degree support | 100–200 |
| Exponential majorant and evaluation | 200–400 |
| Continuity and cutoff-theorem adapter | 60–130 |
| **Total** | **610–1230** |

These are engineering estimates, not a promise; the product-summability API and finite-fiber conversion are the main uncertainty. Roughly **5–8 focused proof units** seems plausible with your current infrastructure.

Suggested module split:

1. `DoubleSeriesConvolution`
2. `DoubleSeriesWeighted`
3. `DoubleSeriesExp`
4. paper-specific amplitude adapter

**Do not start with a reusable graded-\(\ell^1\) algebra module.** Start with weighted summability, convolution closure, and evaluation multiplicativity on `ℕ × ℕ`. Add total-degree regrading later if several downstream arguments need homogeneous blocks. The degree-support lemma for the exponential does not itself justify the larger abstraction.
