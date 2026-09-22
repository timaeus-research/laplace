**A and C are correct. B is correct with a continuous-extension caveat and a correction to the proposed strict-sign condition.** I would strengthen B to a unique zero with signs on either side. For Q3, even the normalized envelope need not decrease, but a simple monotone upper bound is available.

Throughout, assume \(p>0\), \(N\ge1\), and \(b\in\mathbb N\); likewise \(C\ge1\) when discussing the variance envelope.

## 1. Correctness of A–C

### A: correct, including at \(hp=1\)

Write \(u=hp\), \(v=h'p\), and \(m=b+1+k\ge1\). For \(0\le u\le v\le1\),
\[
(1-v)^{2m-1}\le(1-u)^{2m-1},
\]
and
\[
(1-v)(1-u/2)\le(1-u)(1-v/2),
\]
because the right side minus the left side is \((v-u)/2\).

All factors are nonnegative, so multiplying gives exactly
\[
(1-v)^{2m}(1-u/2)
\le
(1-u)^{2m}(1-v/2).
\]
The denominators \(1-u/2\) and \(1-v/2\) are positive, proving the desired antitonicity of each summand.

Thus averaging and multiplying by \(1/p\) proves A. There is no endpoint problem at \(v=1\): every summand on that side is zero because \(m\ge1\). Nonnegativity then lets you square and sum to obtain the bias-sum result.

The restriction to \(h\le1/p_{\max}\) matters. Beyond it, some \(\rho_i\) become negative and their even powers begin increasing again.

### B: correct after two small repairs

Use the continuous expression
\[
s_2(h)=\frac1{p(1-hp/2)}
\]
when including \(h=0\). The original expression
\[
\frac{2h}{1-(1-hp)^2}
\]
is \(0/0\) there; with Lean’s totalized division, it does **not** take the continuously extended value \(1/p\). The analogous issue affects the closed-form geometric sum for \(a\). For the endpoint argument, use the finite-sum definition of \(a\).

With these choices,
\[
a(0)=1,\quad a(1/p)=0,\qquad
f(0)=-1/p,\quad f(1/p)=1/p.
\]
Continuity and IVT give an interior zero.

The useful simplification is
\[
f(h)=\frac{hp-2a(h)}{p(2-hp)}.
\]
Consequently, on \([0,1/p]\),
\[
f(h)<0\iff a(h)>hp/2,\qquad
f(h)=0\iff a(h)=hp/2.
\]
The candidate’s displayed sufficient condition simplifies to \(a(h)\ge hp/2\), which gives **\(f(h)\le0\)**, not strict negativity.

### C: correct

All three inflation values and the isotropic LLC formula are correct:
\[
\operatorname{LLC}_{\mathrm{ULA}}
=\frac{d/2}{1-hp/2}.
\]
For \(d=10\), this gives \(10,20,100\) at relative steps \(1,3/2,19/10\). Use explicit rational constants in the Lean instances.

## 2. Strengthen B to uniqueness and signs—but limit the interpretation

Yes: your monotonicity argument works. The discretization term is strictly increasing, since for \(h<h'\),
\[
\frac{h'}{2-ph'}-\frac{h}{2-ph}
=
\frac{2(h'-h)}{(2-ph')(2-ph)}>0.
\]
By A, \(s_2(h)a(h)\) is antitone. Therefore \(f\) is strictly increasing on the extended interval \([0,1/p]\).

I would state:
\[
\exists!\,h_*\in(0,1/p),\qquad f(h_*)=0,
\]
together with
\[
0<h<h_*\implies f(h)<0,\qquad
h_*<h\le1/p\implies f(h)>0.
\]

An alternative route is particularly simple: \(a(h)\) is antitone, so
\[
hp-2a(h)
\]
is strictly increasing. This directly establishes uniqueness and signs using the simplified numerator.

**Interpretation:** this is an honest theorem about *per-direction cancellation of discretization inflation and zero-start deflation*. At \(h_*\), that diagonal estimator’s MSE against \(1/p\) equals its variance.

It does **not** establish the full empirical Frobenius tradeoff:

- different directions generally have different cancellation steps;
- the centered variance also depends on \(h\);
- minimizing squared bias is not the same as minimizing total MSE;
- it does not locate an optimum near \(hp_{\max}\approx0.5\)–\(1\).

I would describe B as a rigorous mechanism underlying the observed tradeoff, not a formalization of the entire empirical claim.

## 3. The centered envelope: exact monotonicity fails, but a cheap bound works

Let
\[
R(h)=
\frac{\sum_{i,j}(1+\delta_{ij})s_i s_j
       \frac{1+\rho_i\rho_j}{1-\rho_i\rho_j}}
     {\sum_i s_i^2}.
\]
The normalized envelope in the question is \(R(h)/(CN)\).

### Neither absolute nor normalized monotonicity holds generally

For the **absolute** envelope, even one dimension suffices. At \(hp=1\), the autocorrelation factor
\[
\frac{1+\rho^2}{1-\rho^2}
\]
has derivative zero, whereas \(s_2(h)^2\) has positive derivative. Thus the envelope increases near that endpoint, even from the left.

For the **normalized** envelope, changing weights can also defeat monotonicity, even on \(0<h\le1/p_{\max}\). Here is a counterexample family:

- \(M\) directions with precision \(1\);
- one direction with precision \(q\in(0,1)\);
- inspect \(h=1\).

Set \(t=1/[q(2-q)]\). Direct differentiation gives
\[
\lim_{M\to\infty}R_M'(1)
=
\frac{4t(1-q)}{2-q}(t+q-3).
\]
For \(q=1/10\), \(t=100/19\), so this is positive. Hence sufficiently many stiff directions give a normalized envelope increasing near \(h=1\).

Over the larger stability interval \(0<hp<2\), even the isotropic normalized envelope fails monotonicity: its autocorrelation factor decreases until \(hp=1\), then increases.

### A useful monotone upper bound

There is nevertheless a very cheap statement on \(0<h\le1/p_{\max}\). Let \(p_{\min}>0\) and
\[
r(h)=1-hp_{\min}.
\]
Then \(0\le\rho_i\le r(h)<1\), giving
\[
\frac{1+\rho_i\rho_j}{1-\rho_i\rho_j}
\le
\frac{1+r(h)^2}{1-r(h)^2}.
\]
Also,
\[
\sum_{i,j}(1+\delta_{ij})s_i s_j
=
\left(\sum_i s_i\right)^2+\sum_i s_i^2
\le(d+1)\sum_i s_i^2.
\]
Therefore
\[
\boxed{
\frac{\text{centered envelope}}{\sum_i s_i^2}
\le
\frac{d+1}{CN}
\frac{1+(1-hp_{\min})^2}{1-(1-hp_{\min})^2}
}
\]
and this **upper bound is antitone** in \(h\) on the stated interval. It is exact in the isotropic case. This distinguishes a decreasing correlation-controlled bound from the generally nonmonotone normalized envelope itself.

## Vote

**Formalise A + B + C.**

- **A:** as proposed, including the endpoint and squared-bias-sum corollary.
- **B:** strengthen to a unique cancellation step and signs on either side; use the continuous rational extension and correct the strict-sign condition.
- **C:** include as inexpensive, direct E1 checks.

Treat the monotone centered-envelope **upper bound** as an optional add-on—not an exact monotonicity theorem.