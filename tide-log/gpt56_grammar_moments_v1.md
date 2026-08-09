## A. Correctness of the three candidates

### 1. Rate-halving tail bound

Yes. Let
\[
M_j(t):=\int_{\mathbb R}x^{2j}\exp\!\left(-\frac{t x^4}{24}\right)\,dx,
\qquad
\alpha_j:=\frac{2j+1}{4}.
\]
For \(t>0\), \(a>0\), and \(w>a\),
\[
e^{-t w^4/24}
=
e^{-t w^4/48}e^{-t w^4/48}
\le
e^{-t a^4/48}e^{-t w^4/48}.
\]
Since \(w^{2j}\ge 0\), integration gives
\[
\int_{(a,\infty)}w^{2j}e^{-t w^4/24}\,dw
\le
e^{-t a^4/48}
\int_{(a,\infty)}w^{2j}e^{-t w^4/48}\,dw
\le
e^{-t a^4/48}M_j(t/2).
\]

The bookkeeping is exactly right:
\[
e^{-t w^4/48}
=
e^{-(t/2)w^4/24}.
\]

Using the merged moment formula,
\[
M_j(t)=\frac12\left(\frac{24}{t}\right)^{\alpha_j}\Gamma(\alpha_j),
\]
one obtains
\[
M_j(t/2)
=
\frac12\left(\frac{48}{t}\right)^{\alpha_j}\Gamma(\alpha_j)
=
2^{\alpha_j}M_j(t).
\]

Thus the prefactor behaves as \(t^{-\alpha_j}\). It **decays** as \(t\to\infty\), although it blows up as \(t\downarrow0\). So the proposed description is correct once “grows like” is replaced by “scales like” or “decays like”.

This estimate is weaker than the existing specialized \(j=0\) tail estimate in its exponential rate, but it is much more uniform and avoids polynomial-times-Gaussian tail machinery.

---

### 2. Bounded-prior moment approximation

Yes. For
\[
f_{j,t}(x)=x^{2j}e^{-t x^4/24},
\]
the integrand is even, nonnegative, and integrable. Hence
\[
M_j(t)
=
\int_{[-a,a]}f_{j,t}(x)\,dx
+
2\int_{(a,\infty)}f_{j,t}(x)\,dx.
\]
In fact, because the tail is nonnegative,
\[
\left|
\int_{[-a,a]}f_{j,t}(x)\,dx-M_j(t)
\right|
=
2\int_{(a,\infty)}f_{j,t}(x)\,dx.
\]
Candidate 1 therefore gives
\[
\left|
\int_{[-a,a]}x^{2j}e^{-t x^4/24}\,dx-M_j(t)
\right|
\le
2M_j(t/2)e^{-t a^4/48}.
\]

Substituting the closed form,
\[
2M_j(t/2)
=
\left(\frac{48}{t}\right)^{\alpha_j}\Gamma(\alpha_j).
\]

So candidate 2 is correct as stated.

---

### 3. Normalized bounded/full-line agreement

The `SuperPoly` claim is correct, but a fixed-\(a\) exponential estimate is the more informative primary theorem.

Write
\[
A_j(t)=M_j(t),\qquad
B_j(t)=\int_{[-a,a]}x^{2j}e^{-t x^4/24}\,dx,
\]
and
\[
Q_j(t)=\frac{B_j(t)}{B_0(t)},\qquad
N_j(t)=\frac{A_j(t)}{A_0(t)}.
\]
Let \(r_j=A_j-B_j\). Candidate 2 yields
\[
0\le r_j(t)
\le 2M_j(t/2)e^{-ct}
=
k_j A_j(t)e^{-ct},
\qquad
c=\frac{a^4}{48},
\]
where
\[
k_j=2^{\alpha_j+1}.
\]

In particular,
\[
B_0(t)\ge A_0(t)(1-k_0e^{-ct}),
\]
so eventually \(B_0(t)\ge A_0(t)/2\). Then
\[
Q_j-N_j
=
\frac{A_jr_0-A_0r_j}{B_0A_0},
\]
and consequently, eventually,
\[
|Q_j(t)-N_j(t)|
\le
2(k_0+k_j)\frac{A_j(t)}{A_0(t)}e^{-ct}.
\]
But
\[
\frac{A_j(t)}{A_0(t)}
=
\left(\frac{24}{t}\right)^{j/2}
\frac{\Gamma((2j+1)/4)}{\Gamma(1/4)}.
\]
Therefore
\[
|Q_j(t)-N_j(t)|
\le C_{j,a}\,t^{-j/2}e^{-t a^4/48}
\]
eventually. Since \(t^{-j/2}\le 1\) for \(t\ge1\), this even gives
\[
Q_j-N_j=O\!\left(e^{-t a^4/48}\right).
\]

So I would expose either:

1. an eventual quantitative inequality of the above form; or
2. an `IsBigO atTop` theorem against `fun t ↦ exp (-(a^4 / 48) * t)`,

and derive `SuperPoly` as a corollary.

A useful caveat: if the Lean proof uses only coarse polynomial denominator bounds and produces
\[
|Q_j-N_j|\le t^K e^{-ct},
\]
then this is not \(O(e^{-ct})\) with the same \(c\). It is, however, \(O(e^{-c't})\) for every \(0<c'<c\). Here the sharper relative-error argument avoids that loss and preserves \(c=a^4/48\).

For \(j=0\), of course, both normalized moments are identically \(1\), so the difference is exactly zero.

---

## B. Cheapest Lean staging

### A generic even-split lemma is worthwhile

Since this is already the second use and normalized moments will use it repeatedly, extracting the split is worthwhile. The cheapest useful version should stay specialized to real-valued functions:

```lean
theorem integral_eq_integral_Icc_add_two_mul_Ioi_of_even
    {f : ℝ → ℝ} (hf : Integrable f) (heven : Function.Even f)
    {a : ℝ} (ha : 0 ≤ a) :
    (∫ x, f x) =
      (∫ x in Set.Icc (-a) a, f x) +
        2 * ∫ x in Set.Ioi a, f x := ...
```

No continuity hypothesis is needed. `Integrable f` and `Function.Even f` are the right inexpensive assumptions:

- global integrability supplies integrability on all restricted sets;
- exact evenness is much easier to use than an a.e.-even formulation;
- `0 ≤ a` is needed for the interval decomposition;
- retaining `ℝ → ℝ` avoids unnecessary Bochner/scalar-generalization friction.

The proof should be extracted from the existing `quartic_partition_split` proof rather than generalized aggressively. A vector-valued version is possible later if genuinely needed.

### Suggested theorem order

1. Extract the generic real-valued even split.
2. Prove the rate-halving tail estimate.
3. Prove the bounded-prior approximation by one application of the split.
4. Only then add normalized ratios.

For the normalized theorem, the cheapest route is probably the relative-error calculation above, rather than a very general quotient asymptotics framework. Define
\[
r_j=M_j-B_j
\]
and prove
\[
0\le r_j\le k_jM_j e^{-ct}.
\]
The denominator lower bound and quotient estimate then become elementary algebra.

The new anchoring lemmas are useful for obtaining the final `SuperPoly` corollary, but I would not force the main analytic estimate through the anchoring abstraction if a direct exponential inequality is simpler.

One Lean-specific point: it is not necessary to prove the bounded denominator nonzero for every real \(t\) merely to establish an `atTop` statement. The eventual estimate
\[
B_0(t)\ge M_0(t)/2>0
\]
is enough for the asymptotic quotient argument. A global positivity lemma is mathematically true for \(a>0\), but may be avoidable staging work.

---

## C. Minimal good target and possible grammar-facing variants

### Minimal incremental target: candidate 2

If only one theorem is to be added now, I would choose the bounded-prior moment approximation:
\[
\left|
\int_{[-a,a]}x^{2j}e^{-t x^4/24}\,dx-M_j(t)
\right|
\le
2M_j(t/2)e^{-t a^4/48}.
\]

Reasons:

- candidate 1 is primarily an internal tail lemma;
- candidate 2 is the first theorem directly expressing “bounded prior agrees with the full-line quartic model”;
- it generalizes the existing \(j=0\) bounded-prior result to the whole moment family;
- it is immediately reusable for normalized moments, polynomial observables, and finite grammar coefficients;
- it does not yet require denominator positivity or quotient asymptotics.

Candidate 3 is the better semantic endpoint if normalized expectations are already the next downstream object, but it is not the minimal addition.

### A cleaner eventual endpoint: rescaled normalized moments

A particularly grammar-friendly formulation is to rescale away the known polynomial behavior. Since
\[
N_j(t)
=
\left(\frac{24}{t}\right)^{j/2}
\frac{\Gamma((2j+1)/4)}{\Gamma(1/4)},
\]
the normalized theorem implies
\[
t^{j/2}Q_j(t)
=
24^{j/2}
\frac{\Gamma((2j+1)/4)}{\Gamma(1/4)}
+
O\!\left(e^{-t a^4/48}\right).
\]

Equivalently, the rescaled bounded-prior moment is exponentially anchored to an explicit Gamma constant. This is often more directly useful than merely saying \(Q_j-N_j\) is `SuperPoly`, because the limiting coefficient is visible in the statement.

### Polynomial or \(Z_n[\phi]\)-style wrappers

A finite-polynomial observable theorem is also nearby:
\[
\int_{[-a,a]}P(x)e^{-t x^4/24}\,dx
-
\int_{\mathbb R}P(x)e^{-t x^4/24}\,dx
\]
is exponentially small with an explicit finite sum of moment prefactors. On symmetric domains, odd terms vanish exactly, so only the even coefficients matter.

That may eventually be closer to a `Z_n[\phi]` coefficient than individual moments. Nevertheless, I would not introduce a `Z_n`-specific analytic theorem until the grammar-side object and normalization are stable. The moment approximation is the reusable analytic kernel; finite polynomial or grammar coefficients can then be assembled algebraically without redoing any integration.

**Recommendation:** land candidate 2 now, with candidate 1 as its helper and the generic even-split lemma extracted. Next, if the grammar layer consumes normalized coefficients, prove the stronger exponential normalized/rescaled theorem and derive `SuperPoly` as a short corollary.