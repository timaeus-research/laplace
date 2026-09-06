Assume throughout that \(\beta>0\), \(b>0\), and \(n>0\). Write
\[
p_i:=\frac{h_i+1}{k_i}=2\mu_i,\qquad
B_i:=b^{k_i},\qquad L:=\sqrt n\,B_1B_2,
\]
and define
\[
f(s):=e^{-\beta s^2+\beta as},\qquad
F_\gamma(x):=\int_0^x s^\gamma f(s)\,ds,\qquad
A_\gamma:=\int_0^\infty s^\gamma f(s)\,ds.
\]
For \(\gamma>-1\),
\[
\boxed{A_\gamma=\frac12 S_{(\gamma+1)/2}(a).}
\]

The two leading constants are
\[
\boxed{C_{\log}=\frac{S_\mu(a)}{4k_1k_2}}
\]
and, when \(\mu_1<\mu_2\),
\[
\boxed{
C=
\frac{S_{\mu_1}(a)}{2k_1}\,
\frac{b^{\,h_2+1-k_2(h_1+1)/k_1}}
     {h_2+1-k_2(h_1+1)/k_1}.
}
\]
In particular, the logarithmic coefficient is independent of \(b\).

## 1. Exact reduction by the inner \(v\)-substitution

For \(u>0\), substitute
\[
s=\sqrt n\,u^{k_1}v^{k_2}.
\]
Then
\[
\int_0^b v^{h_2}f(\sqrt n\,u^{k_1}v^{k_2})\,dv
=
\frac1{k_2}
(\sqrt n\,u^{k_1})^{-p_2}
F_{p_2-1}(\sqrt n\,u^{k_1}B_2).
\]

Now substitute \(x=\sqrt n\,B_2u^{k_1}\) in the outer integral. This gives the common exact reduction
\[
\boxed{
Z(n)=
\frac{n^{-p_1/2}B_2^{p_2-p_1}}{k_1k_2}
\int_0^L x^{p_1-p_2-1}F_{p_2-1}(x)\,dx.
}
\tag{1}
\]

All endpoint singularities here are integrable: near zero,
\[
F_{p_2-1}(x)=O(x^{p_2}),
\]
so the final integrand is \(O(x^{p_1-1})\), with \(p_1>0\).

### A. Equal exponents

If \(p_1=p_2=p=2\mu\), set \(\gamma=p-1\). Equation (1) becomes
\[
Z(n)=\frac{n^{-\mu}}{k_1k_2}H_\gamma(L),
\qquad
H_\gamma(L):=\int_0^L \frac{F_\gamma(x)}x\,dx.
\]

Let
\[
M_\gamma:=\int_0^\infty s^{\gamma+1}f(s)\,ds
=\frac12 S_{\mu+1/2}(a),
\qquad E:=e^{\beta a^2/2}.
\]
Completing the square gives \(f(s)\le E\), hence
\[
0\le F_\gamma(x)\le \frac{E}{\gamma+1}x^{\gamma+1}.
\]
Also, for \(x>0\),
\[
0\le A_\gamma-F_\gamma(x)\le \frac{M_\gamma}{x}.
\]

Exactly as in your completed case, splitting at \(1\) gives, for \(L\ge1\),
\[
\boxed{
A_\gamma\log L-M_\gamma
\le H_\gamma(L)
\le A_\gamma\log L+\frac{E}{(\gamma+1)^2}.
}
\tag{2}
\]
Thus \(H_\gamma(L)=A_\gamma\log L+O(1)\). Since
\[
\log L=\frac12\log n+(k_1+k_2)\log b,
\]
we obtain
\[
Z(n)
=
\frac{A_\gamma}{2k_1k_2}n^{-\mu}\log n
+O(n^{-\mu}).
\]
Using \(A_\gamma=S_\mu(a)/2\),
\[
\boxed{
Z(n)\sim\frac{S_\mu(a)}{4k_1k_2}n^{-\mu}\log n.
}
\]

The logarithm comes precisely from the outer exponent becoming \(-1\).

### B. Unequal exponents, \(\mu_1<\mu_2\)

Put
\[
d:=p_2-p_1=2(\mu_2-\mu_1)>0.
\]
Equation (1) becomes
\[
Z(n)=
\frac{n^{-\mu_1}b^{k_2d}}{k_1k_2}
K_d(L),
\qquad
K_d(L):=\int_0^L x^{-d-1}F_{p_2-1}(x)\,dx.
\]

The particularly useful finite-\(L\) identity is
\[
\boxed{
K_d(L)=
\frac{F_{p_1-1}(L)-L^{-d}F_{p_2-1}(L)}d.
}
\tag{3}
\]
Indeed, exchanging integration over \(0<s<x<L\),
\[
\begin{aligned}
K_d(L)
&=\int_0^L s^{p_2-1}f(s)
       \left(\int_s^L x^{-d-1}\,dx\right)ds\\
&=\frac1d\int_0^L
       \bigl(s^{p_1-1}-L^{-d}s^{p_2-1}\bigr)f(s)\,ds.
\end{aligned}
\]

Consequently,
\[
K_d(L)\longrightarrow\frac{A_{p_1-1}}d
=\frac{S_{\mu_1}(a)}{2d}.
\]
There is no logarithm: \(x^{-d-1}F_{p_2-1}(x)\) is integrable at infinity.

An exact chart formula, useful for both proof and numerical checking, is
\[
\boxed{
Z(n)=\frac1{k_1k_2d}
\left[
b^{k_2d}n^{-\mu_1}F_{p_1-1}(L)
-
b^{-k_1d}n^{-\mu_2}F_{p_2-1}(L)
\right].
}
\tag{4}
\]
Therefore
\[
Z(n)\sim
\frac{b^{k_2d}S_{\mu_1}(a)}{2k_1k_2d}n^{-\mu_1}.
\]

Since
\[
D:=k_2d=h_2+1-\frac{k_2(h_1+1)}{k_1}>0,
\]
this is exactly
\[
C=\frac{S_{\mu_1}(a)}{2k_1}\frac{b^D}{D}.
\]

### About the “unsaturated region”

With **inner \(v\)** integration, the dominant outer scale is
\[
u\asymp n^{-1/(2k_1)},
\]
and the limiting integral \(K_d(\infty)\) samples all finite values of the scaled cutoff \(x\). Replacing \(F_{p_2-1}(x)\) solely by its small-\(x\) approximation would not give the exact constant.

With **inner \(u\)** integration instead, the explanation is simpler: for each fixed \(v>0\), the scaled \(u\)-integral saturates to its half-line mass. Its remaining weight is
\[
v^{h_2-k_2p_1},
\]
which is integrable at zero exactly when \(p_1<p_2\). Thus “unsaturated” is not the right description of that orientation.

## 2. Lean-sized decomposition

I would separate the analytic kernel lemmas from all natural-number chart algebra. The names below are proposed names in `Laplace.Grammar`, not claims that these lemmas already exist in Mathlib.

### Layer I: weighted kernel

Use real exponents for the kernel:
```lean
-- Schematic definitions
weightedKernel (γ s : ℝ) :=
  Real.rpow s γ * Real.exp (-β * s^2 + β * a * s)

weightedPrimitive (γ x : ℝ) :=
  ∫ s in (0 : ℝ)..x, weightedKernel β a γ s

weightedMass (γ : ℝ) :=
  ∫ s in Set.Ioi (0 : ℝ), weightedKernel β a γ s
```

Keep original chart powers as `npow`; convert only in substitution lemmas.

Suggested small lemmas:

| Lemma | Content |
|---|---|
| `weightedKernel_nonneg` | Nonnegativity on \(s\ge0\). |
| `weightedKernel_le_const_mul_rpow` | \(s^\gamma f(s)\le E s^\gamma\), for \(s>0\). |
| `weightedKernel_integrableOn` | Integrable on `Ioi 0`, assuming \(-1<\gamma\). |
| `weightedMass_eq_fluctuation` | \(A_\gamma=S_{(\gamma+1)/2}/2\). |
| `weightedMoment_eq_fluctuation` | \(M_\gamma=S_{(\gamma+2)/2}/2\); preferably just reuse the preceding lemma at \(\gamma+1\). |
| `weightedPrimitive_nonneg` | \(0\le F_\gamma(x)\), \(x\ge0\). |
| `weightedPrimitive_le_mass` | \(F_\gamma(x)\le A_\gamma\). |
| `weightedPrimitive_le_rpow` | \(F_\gamma(x)\le E x^{\gamma+1}/(\gamma+1)\). |
| `weightedMass_sub_primitive_eq_tail` | Split the half-line at \(x\). |
| `weightedMass_sub_primitive_le` | Tail bounded by \(M_\gamma/x\). |
| `weightedPrimitive_tendsto_mass` | Squeeze using the preceding estimate. |

Expose integrability explicitly. Lean’s totalized integral means an equality involving an integral is not generally an adequate substitute for an integrability hypothesis.

For the mass identity, \(t=s^2\) gives
\[
s^\gamma\,ds=\frac12t^{(\gamma-1)/2}\,dt.
\]
This is the same substitution infrastructure as the 1D theorem, but the weight exponent is now real. Extracting its real-exponent analytic core is likely worthwhile.

### Layer II-A: logarithmic primitive

Define \(H_\gamma\) using an interval integral. Prove separately:

1. `weightedLogPrimitive_intervalIntegrable`  
   Dominate near zero by
   \[
   \frac{E}{\gamma+1}x^\gamma.
   \]

2. `weightedLogPrimitive_one_le`  
   \[
   H_\gamma(1)\le E/(\gamma+1)^2.
   \]

3. `weightedLogPrimitive_split`  
   For \(L\ge1\),
   \[
   H_\gamma(L)=H_\gamma(1)+A_\gamma\log L
      -\int_1^L \frac{A_\gamma-F_\gamma(x)}x\,dx.
   \]

4. `weightedLogPrimitive_bounds`  
   Equation (2), using \(M_\gamma/x^2\).

5. `weightedLogPrimitive_div_log_tendsto`  
   \(H_\gamma(L)/\log L\to A_\gamma\).

These should closely match your existing unweighted proof. Generalizing that proof is preferable to maintaining a second copy.

### Layer II-B: noncritical primitive

For \(p,q>0\), define
\[
J_{p,q}(L):=\int_0^L x^{p-q-1}F_{q-1}(x)\,dx.
\]

Prove:

1. `weightedPowerPrimitive_intervalIntegrable`  
   Near zero the integrand is bounded by a constant times \(x^{p-1}\).

2. `weightedPowerPrimitive_eq`  
   For \(p\ne q\), \(L>0\),
   \[
   \boxed{
   J_{p,q}(L)
   =\frac{L^{p-q}F_{q-1}(L)-F_{p-1}(L)}{p-q}.
   }
   \tag{5}
   \]

3. `weightedPowerPrimitive_tendsto_of_lt`  
   If \(p<q\),
   \[
   J_{p,q}(L)\to A_{p-1}/(q-p).
   \]

For (5), two proof routes are reasonable:

- **Fubini on the triangle:** conceptually direct, especially if your existing Fubini infrastructure is reusable.
- **Integration by parts on \([\varepsilon,L]\):** avoids triangle bookkeeping. The endpoint term vanishes because
  \[
  \varepsilon^{p-q}F_{q-1}(\varepsilon)=O(\varepsilon^p).
  \]

I would not integrate by parts directly at zero: individual factors may be singular there even though their product vanishes.

### Layer III: bounded substitutions and chart algebra

Make the following standalone substitution lemma:
\[
\boxed{
\int_0^b v^h f(c v^k)\,dv
=
\frac1k c^{-(h+1)/k}
F_{(h+1)/k-1}(c b^k)
}
\]
under \(c>0\), \(b>0\), \(k>0\).

Then split the chart reduction into:

1. `standardIntegral2D_inner_eq`
2. `standardIntegral2D_eq_weightedPowerPrimitive`
3. `standardIntegral2D_eq_weightedLogPrimitive` under \(p_1=p_2\)
4. `standardIntegral2D_eq_of_candidate_lt` giving (4)
5. the two final asymptotic lemmas.

With power-algebra helpers extracted, each item is a plausible roughly-80-line target; putting substitutions, integrability, and exponent normalization in one lemma is not.

## 3. Mathlib substitution route and pitfalls

The relevant general API is
```lean
intervalIntegral.integral_comp_mul_deriv
```
and your existing scaling API
```lean
intervalIntegral.integral_comp_mul_left
```
remains useful. I cannot verify the exact binder lists against your particular 2026 Mathlib checkout; use `#check` locally rather than treating the following as compiling applications.

### Recommended route

Split
\[
v\mapsto c v^k
\]
into:

1. \(w=v^k\);
2. \(s=cw\).

For the first substitution, apply the derivative-based theorem on a **positive cutoff interval** \([\varepsilon,b]\), with map \(v\mapsto v^k\). The target weight is
\[
\frac1k w^{(h+1)/k-1}f(cw).
\]
Multiplying by \(kv^{k-1}\) recovers \(v^h f(cv^k)\).

Then send \(\varepsilon\downarrow0\), using the power-integrability bounds already proved.

This avoids depending on a specialized `integral_comp_rpow` theorem’s exact endpoint hypotheses.

### Important pitfalls

- The transformed exponent can lie in \((-1,0)\). The transformed kernel is then integrable but not continuous at zero.
- Consequently, a whole-interval substitution theorem with a continuity hypothesis may not apply directly.
- Prove identities involving negative real powers only on \(v>0\), not merely \(v\ge0\).
- Use `Real.rpow_natCast` to bridge natural and real powers, and `Real.rpow_add`, `Real.rpow_mul`, and `Real.mul_rpow` with their required sign hypotheses.
- Establish exponent identities separately with `field_simp`/`ring`; establish denominator nonzeroness first.
- The scaled parameter \(c=\sqrt n\,u^{k_1}\) is positive only for \(u>0\). Handle \(u=0\) by almost-everywhere congruence in the outer integral, rather than forcing a pointwise formula there.
- Keep all real ratios explicitly cast:
  \[
  p_i=((h_i:\mathbb R)+1)/(k_i:\mathbb R).
  \]
  Do not accidentally introduce natural-number division.

For cutoff limits, it is often simpler to bound the omitted integral by \(C\varepsilon^r\), \(r>0\), than to invoke a large general convergence theorem.

## 4. Which regime first? What is the common framework?

**For your current development, I would formalize (A) first.** You already have the logarithmic primitive proof; its weighted generalization supplies almost everything except the power substitutions.

**Without that existing work, (B) with the order swapped is analytically easier.** Integrate in the singular coordinate \(u\), then use dominated convergence with the integrable weight \(v^{D-1}\).

The common framework is indeed \(J_{p,q}\), but there is an important orientation issue:

| Relation | Outer exponent \(e=p-q-1\) | Behavior |
|---|---:|---|
| \(p=q\) | \(-1\) | \(A_{q-1}\log L+O(1)\) |
| \(p>q\) | \(>-1\) | \(J_{p,q}(L)\sim A_{q-1}L^{p-q}/(p-q)\) |
| \(p<q\) | \(<-1\) | \(J_{p,q}(L)\to A_{p-1}/(q-p)\) |

Thus, with the requested **inner \(v\)** order and \(\mu_1<\mu_2\), you need the **\(e<-1\)** branch, not the \(e>-1\) branch.

Equation (5) handles both noncritical branches with almost no additional analysis. The critical branch is precisely where its denominator vanishes and a logarithm replaces the power difference.

## 5. Numerical sanity checks

For \(\beta=1.3\), \(a=0.4\),
\[
A_0=\int_0^\infty e^{-1.3s^2+0.52s}\,ds
=
\frac{\sqrt\pi}{2\sqrt{1.3}}e^{0.052}
\bigl(1+\operatorname{erf}(0.2\sqrt{1.3})\bigr)
\approx1.02583964.
\]
Hence
\[
S_{1/2}(0.4)\approx2.05167928.
\]

### A. \(k=(1,2)\), \(h=(0,1)\), \(b=1\)

Here \(p_1=p_2=1\), so \(\mu=1/2\), and
\[
Z(n)=\frac1{2\sqrt n}H_0(\sqrt n).
\]
Prediction:
\[
\boxed{
Z(n)\sim0.25645991\,n^{-1/2}\log n,
\qquad
\frac{\sqrt n\,Z(n)}{\log n}\longrightarrow0.25645991.
}
\]
Convergence of this normalized quantity is generally only \(O(1/\log n)\).

### B. \(k=(1,1)\), \(h=(0,1)\), \(b=1\)

Here \(p_1=1\), \(p_2=2\), \(d=1\). Exactly,
\[
Z(n)=n^{-1/2}F_0(\sqrt n)-n^{-1}F_1(\sqrt n).
\]
Prediction:
\[
\boxed{\sqrt n\,Z(n)\longrightarrow1.02583964.}
\]

There is also a useful second term:
\[
A_1=\frac1{2\beta}+\frac a2A_0
\approx0.58978331,
\]
so, up to exponentially small tails,
\[
\boxed{
Z(n)=1.02583964\,n^{-1/2}-0.58978331\,n^{-1}.
}
\]
For example,
\[
Z(100)\approx0.09668613,\qquad
Z(10^4)\approx0.01019942.
\]

**Recommended implementation centerpiece:** prove the exact chart reduction (1), the weighted logarithmic bounds (2), and the noncritical identity (5). Those three lemmas isolate the multiplicity criterion cleanly from the chart-specific natural-power algebra.
