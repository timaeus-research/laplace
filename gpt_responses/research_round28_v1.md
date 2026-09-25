## 1. Re-ranking: finish the geometry, then sharpen the wall

The main conceptual advance since round 27 is that you now have an **identifiability theorem, a differential response calculus, and several exact global divergences**. The next step should make these visibly parts of one geometry.

My ranking of substantive work is:

| Rank | Target | Reason |
|---|---|---|
| **1** | Quotient mean-map theorem | Closes the global identifiable-data picture; mathematically nearly a corollary, though Lean quotient infrastructure can make it longer. |
| **2** | Interior-minimum geometry (6) | Explains the negative chamber geometrically, rather than only asymptotically. Reusable well beyond the monomial model. |
| **3** | Two-term wall law (5b) | Turns the phase diagram into a matched expansion with an actual renormalized constant. The required negative-side coefficient is especially simple. |
| **4** | Square-root immersion (2′) | Supplies the canonical ambient geometry behind `DataQuotient`, `AngularBound`, and `TwoValuedGeodesic`. |
| **5** | Global response chart and entropy duality of the ray | A clean featureless-to-data coordinate system; inexpensive once derivative and endpoint APIs are assembled. |
| **6** | Boundary rate-function interpretation | Attractive synthesis, but should follow the chart/duality theorem rather than lead it. |

**Do immediately, outside that ranking:** package the phase diagram, multiplicative-scale self-similarity, and product equality case. These are short synthesis targets, not competing research projects.

### 1.1 The quotient mean map: yes, with the right target

Fix \(t>0\), a finite-dimensional Euclidean parameter space \(E\), bounded sufficient statistics \(R:X\to E\), and
\[
dP_a=Z(a)^{-1}e^{-t(L_0+\langle a,R\rangle)}\,d\pi.
\]
Assume the normalizations are finite and positive, and all these laws are equivalent to the reference measure on which the invisible subspace is defined. Set
\[
K=\{v:\langle v,R\rangle\text{ is a.e. constant}\},\qquad
M(a)=\mathbb E_aR.
\]

Then:

1. \(M(a+k)=M(a)\) for \(k\in K\).
2. \(M(a)-M(0)\in K^\perp\).
3. The map
   \[
   \widetilde M:K^\perp\longrightarrow K^\perp,\qquad
   a\longmapsto M(a)-M(0)
   \]
   is an open embedding, indeed a \(C^1\) diffeomorphism onto its image.

The derivative is
\[
D\widetilde M_a=-t\,\operatorname{Cov}_a(R)|_{K^\perp},
\]
hence invertible. Global injectivity follows from
\[
\langle M(b)-M(a),b-a\rangle
=-t\int_0^1\operatorname{Var}_{a+s(b-a)}
       (\langle b-a,R\rangle)\,ds<0
\]
when \(a,b\in K^\perp\), \(a\ne b\).

**Lean recommendation:** first formalize this on \(K^\perp\), not on `E ⧸ K`. Then transport it through the finite-dimensional identification \(E/K\simeq K^\perp\). This separates the mathematical theorem from quotient-topology plumbing.

One important detail: **\(F=\log Z\) itself does not descend**:
\[
F(a+k)=F(a)-t\,c_k.
\]
The corrected potential
\[
\bar F(a)=F(a)+t\langle a,M(0)\rangle
\]
does descend, with gradient \(-t(M(a)-M(0))\). This gives the quotient a strictly convex potential, not merely an embedding.

Identifying the image with the relative interior of the convex support is a worthwhile subsequent theorem, but is not needed for this closure.

### 1.2 The affine-family angular bound: a direction warning

With \(B(a,b)=-\log\rho(P_a,P_b)\), the correct global statement is
\[
d_G(a,b)\ge 2\arccos\rho(P_a,P_b)
=2\arccos(e^{-B(a,b)}),
\]
where \(d_G\) is intrinsic length distance, with invisible directions quotiented out or retained as a pseudometric.

But
\[
B(a,b)\le \tfrac12\mathrm{KL}(P_a\Vert P_b)
\]
does **not** produce a KL-based lower bound for length: substitution goes in the wrong direction. In particular, it does not imply
\[
d_G(a,b)\ge 2\arccos(e^{-\mathrm{KL}/2}).
\]

Thus package the **affinity lower bound** now; do not advertise a KL lower bound without additional hypotheses comparing KL from above by affinity loss.

### 1.3 Three cheap synthesis theorems

**Multiplicative-scale self-similarity.** Under the regular-variation hypotheses already supporting your limits, with \(\lambda>0\) and \(c,d>0\),
\[
\begin{aligned}
D_{\rm ray}(cu,du)&\longrightarrow
 \sqrt\lambda\,|\log(d/c)|,\\
\mathrm{KL}(P_{cu}\Vert P_{du})&\longrightarrow
 \lambda\left(d/c-1-\log(d/c)\right),\\
-\log\rho(P_{cu},P_{du})&\longrightarrow
 \lambda\log\frac{c+d}{2\sqrt{cd}}.
\end{aligned}
\]
Here \(D_{\rm ray}\) is length **along the ray**, not ambient Fisher distance. The length limit follows directly from \(u^2\operatorname{Var}_u\to\lambda\), uniformly on each multiplicative interval by the definition of a limit at infinity.

This says that log-temperature translations asymptotically preserve three different response geometries.

**Product lower-bound equality.** On the common integration interval, put \(v_i(u)=\sqrt{\operatorname{Var}_u(L_i)}\), \(D_i=\int v_i\). If both \(D_i>0\), then
\[
D(L_1+L_2)=\sqrt{D_1^2+D_2^2}
\iff
\frac{v_1(u)}{D_1}=\frac{v_2(u)}{D_2}\quad\text{a.e.}
\]
The zero-length cases should be separate easy branches. This is equality in the integral triangle inequality for the nonnegative vector \((v_1,v_2)\).

**Ray response chart.** Let \(\pi\) be a probability measure, \(\ell\) measurable and finite a.e., bounded below, integrable under \(\pi\), and not a.e. constant. Then
\[
u\longmapsto m(u)=\mathbb E_u\ell
\]
is a decreasing homeomorphism
\[
(0,\infty)\simeq
(\operatorname*{ess\,inf}\ell,\mathbb E_0\ell),
\]
with
\[
m'(u)=-\operatorname{Var}_u(\ell)<0.
\]
No boundedness of \(\ell\) above is needed: exponential damping supplies the moments for \(u>0\).

For normalized prior and \(F(u)=\log\mathbb E_\pi e^{-u\ell}\),
\[
F^*(-m(u))=-u\,m(u)-F(u)
=\mathrm{KL}(P_u\Vert\pi),
\]
where the conjugate uses the chosen domain of \(F\). This is **relative entropy**, not necessarily differential entropy.

---

## 2. Interior-minimum geometry: separate convergence from domination

I would build this in two layers:

1. a uniform centered-moment Laplace theorem;
2. a weaker domination lemma which, combined with existing pointwise Laplace results, already proves the integrated length limit.

The second is probably the fastest route to landing (6).

### 2.1 A Lean-ready uniform theorem

Let \(A=[a_-,a_+]\), let \(D\subseteq\mathbb R\) be a fixed measurable interval, and define
\[
Z_{t,a}=\int_D e^{-tV(a,x)}w(a,x)\,dx,\qquad
dP_{t,a}=Z_{t,a}^{-1}e^{-tV(a,x)}w(a,x)\,dx.
\]

Allowing \(w\) to depend on \(a\) costs little mathematically; fixing \(w(x)\) may make the first implementation simpler.

Assume:

**Measurability and positivity**
- All integrands involved are measurable.
- \(w\ge0\).
- The following local and tail assumptions hold.

**A uniformly interior minimizer**
- \(x_*:A\to\mathbb R\) is continuous.
- Some \(r>0\) satisfies
  \[
  [x_*(a)-r,x_*(a)+r]\subset D
  \quad(a\in A).
  \]

Write
\[
\Delta V(a,x)=V(a,x)-V(a,x_*(a)).
\]

**Uniform quadratic expansion**
- \(H:A\to(0,\infty)\) is continuous, \(H\ge h_0>0\).
- For \(|h|\le r\),
  \[
  \left|\Delta V(a,x_*(a)+h)-\tfrac12H(a)h^2\right|
  \le \omega_V(|h|)h^2,
  \]
  uniformly in \(a\), where \(\omega_V(s)\to0\).

**Uniform observable expansion**
- \(d:A\to\mathbb R\) is continuous.
- For \(|h|\le r\),
  \[
  |f(x_*(a)+h)-f(x_*(a))-d(a)h|
  \le \omega_f(|h|)|h|,
  \]
  with \(\omega_f(s)\to0\).

**Uniform prior regularity**
- \(w_*(a)=w(a,x_*(a))\) is continuous and \(w_*\ge w_0>0\).
- For \(|h|\le r\),
  \[
  |w(a,x_*(a)+h)-w_*(a)|\le\omega_w(|h|),
  \]
  with \(\omega_w(s)\to0\).

**Uniform tail separation and one weighted envelope**
- For some \(\eta>0\),
  \[
  |x-x_*(a)|\ge r,\ x\in D
  \implies \Delta V(a,x)\ge\eta.
  \]
- For some \(t_0>0,C<\infty\),
  \[
  \sup_{a\in A}\int_D
  \left(1+|f(x)-f(x_*(a))|^2\right)
  e^{-t_0\Delta V(a,x)}w(a,x)\,dx\le C.
  \]

After shrinking \(r\), the local expansion gives a uniform positive quadratic lower bound.

**Conclusion**
\[
\sup_{a\in A}
\left|t\,\operatorname{Var}_{t,a}(f)
-\frac{d(a)^2}{H(a)}\right|\longrightarrow0.
\]

For Lean, the conclusion can first be expressed without a supremum:
```text
∀ ε > 0, ∃ T > 0, ∀ t ≥ T, ∀ a ∈ A,
  |t * variance (P t a) f - d a ^ 2 / H a| < ε
```
This avoids irrelevant supremum bookkeeping.

### 2.2 Prove centered moments, not raw moments

Define, for \(k=0,1,2\),
\[
J_k(t,a)=\sqrt t\int_D
 \bigl(\sqrt t[f(x)-f(x_*(a))]\bigr)^k
 e^{-t\Delta V(a,x)}w(a,x)\,dx.
\]
Prove uniformly:
\[
\begin{aligned}
J_0&\to w_*(a)\sqrt{2\pi/H(a)},\\
J_1&\to0,\\
J_2&\to w_*(a)\sqrt{2\pi/H(a)}\,d(a)^2/H(a).
\end{aligned}
\]
Then use the exact identity
\[
t\operatorname{Var}_{t,a}(f)
=\frac{J_2}{J_0}-\left(\frac{J_1}{J_0}\right)^2.
\]

This avoids subtracting two raw moments whose leading terms coincide. It also exposes the uniformly positive denominator needed by the ratio API.

### 2.3 What is actually needed for integrated length?

Uniform convergence is stronger than necessary.

It suffices that:

1. \(t\operatorname{Var}_{t,a}(f)\to d(a)^2/H(a)\) for a.e. \(a\);
2. for all sufficiently large \(t\),
   \[
   \sqrt{t\operatorname{Var}_{t,a}(f)}\le g(a),
   \qquad g\in L^1(A).
   \]

Then dominated convergence gives
\[
\int_A\sqrt{t\operatorname{Var}_{t,a}(f)}\,da
\longrightarrow
\int_A\frac{|d(a)|}{\sqrt{H(a)}}\,da.
\]

On compact parameter intervals, a constant bound is convenient. To obtain it, you do **not** need a uniform Taylor remainder. It is enough to have, uniformly locally,
\[
c h^2\le\Delta V(a,x_*(a)+h)\le C h^2,
\]
\[
0<w_-\le w(a,x_*(a)+h)\le w_+,
\qquad
|f(x_*(a)+h)-f(x_*(a))|\le L|h|,
\]
together with the tail gap and weighted envelope above.

These imply
\[
\int e^{-t\Delta V}w\ge c_1t^{-1/2},
\]
and
\[
\int (f-f(x_*))^2e^{-t\Delta V}w\le c_2t^{-3/2}
\]
for large \(t\). Finally,
\[
\operatorname{Var}(f)\le\mathbb E[(f-f(x_*))^2].
\]

**Recommended base:** existing pointwise local Laplace machinery plus this uniform domination wrapper. Use `MovingMinimizer` to verify the geometric hypotheses. Use `HigherLaplaceDomain` only when a rate is genuinely required. The half-line lemma is useful for tails and model instances, but is not by itself the most natural API for arbitrary moving interior minima.

### 2.4 Geometric identification

For
\[
V(a,x)=V_0(x)+a f(x),
\]
the critical-point identity gives
\[
H(a)x_*'(a)+f'(x_*(a))=0.
\]
Consequently,
\[
\frac{\ell_t(a_-,a_+)}{\sqrt t}
\longrightarrow
\int_{a_-}^{a_+}\sqrt{H(a)}\,|x_*'(a)|\,da.
\]

For \(V(a,x)=x^p+a x^q\), \(p>q>0\), \(a<0\),
\[
x_*(a)=(-qa/p)^{1/(p-q)},\qquad
H(a)=p(p-q)x_*(a)^{p-2}.
\]
With
\[
\beta=\frac{p}{2(p-q)},\qquad
k_-=\frac{q}{\sqrt{p(p-q)}}\left(\frac qp\right)^{\beta-1},
\]
the limiting speed is
\[
\sqrt{H(a)}|x_*'(a)|=k_-|a|^{\beta-1}.
\]
Thus
\[
\int_{-A}^{0}\sqrt H\,|x_*'|\,da
=\frac{k_-}{\beta}A^\beta=K_-(A).
\]

The compact-uniform theorem applies on \([-A,-\varepsilon]\), **not automatically up to the wall**. The identification at \(0\) is an improper-integral calculation, with your existing chamber/wall estimates supplying the limiting passage.

---

## 3. The negative-profile correction: explicit coefficient

I will state the normalization explicitly. Let
\[
d\mu_B(z)\propto
\exp\!\left[-B\left(z^p-\frac pq z^q\right)\right]\,dz,
\qquad z>0,\quad p>q>0.
\]
The minimizer is \(z=1\), and
\[
H=V''(1)=p(p-q).
\]

Then
\[
\boxed{
\operatorname{Var}_{\mu_B}\!\left(\sqrt B(z^q-1)\right)
=
\frac{q^2}{p(p-q)}
+\frac{q^2(p-2)}{2p^2(p-q)}\,\frac1B
+O(B^{-2}).
}
\]

For the wall law, the weaker conclusion with \(O(B^{-1})\) after the leading constant is sufficient.

**This coefficient assumes Lebesgue density \(dz\).** If the amplitude is \(z^{\nu-1}dz\), it becomes
\[
\frac{q^2(p-2\nu)}{2p^2(p-q)}.
\]
And a different normalization of \(B\) must be transported explicitly.

### 3.1 Checks before formalization

- \(p=2,q=1\): the potential is \((z-1)^2-1\). The coefficient vanishes, as it should for a Gaussian with exponentially remote truncation.
- \(p=4,q=2\):
  \[
  \operatorname{Var}(\sqrt B(z^2-1))
  =\frac12+\frac{1}{8B}+O(B^{-2}).
  \]
  Under \(s=z^2\), the law is proportional to
  \(s^{-1/2}e^{-B(s-1)^2}ds\), an independent check.

### 3.2 A reusable local coefficient lemma

For a smooth potential \(V\) with an isolated nondegenerate interior minimum \(x_0\), flat amplitude near \(x_0\), and observable \(g\), write
\[
H=V''(x_0),\quad J=V'''(x_0),\quad K=V''''(x_0),
\qquad g_i=g^{(i)}(x_0).
\]
Under sufficient local smoothness and exponentially controlled tails,
\[
B\operatorname{Var}_B(g)
=\frac{g_1^2}{H}+\frac{\mathcal C}{B}+o(B^{-1}),
\]
where
\[
\boxed{
\mathcal C=
\frac{g_1^2J^2}{H^4}
-\frac{g_1^2K}{2H^3}
-\frac{2g_1g_2J}{H^3}
+\frac{g_2^2}{2H^2}
+\frac{g_1g_3}{H^2}.
}
\]

For the monomial model,
\[
J=H(p+q-3),\qquad
K=H\bigl(p^2+pq+q^2-6p-6q+11\bigr),
\]
and \(g_1=q,\ g_2=q(q-1),\ g_3=q(q-1)(q-2)\).
The coefficient simplifies to the boxed expression above. This final simplification is an excellent `field_simp`/`ring` target.

### 3.3 Can `tendsto_sqrt_mul_integral` be reused?

**Yes, as the Gaussian-limit engine; no, not merely by feeding it a difference observable.**

The missing ingredient is a controlled expansion of the **density**, including the cubic term and the square of that cubic term. Put \(y=\sqrt B(z-1)\). Locally,
\[
e^{-B(V(1+y/\sqrt B)-V(1))}
=e^{-Hy^2/2}
\left[
1-\frac{Jy^3}{6\sqrt B}
+\frac1B\left(\frac{J^2y^6}{72}-\frac{Ky^4}{24}\right)
+\text{remainder}
\right].
\]

Expand also
\[
\sqrt B(g(1+y/\sqrt B)-g(1))
=g_1y+\frac{g_2y^2}{2\sqrt B}
+\frac{g_3y^3}{6B}+\cdots.
\]

The \(B^{-1/2}\) contributions to the relevant even integrals vanish by parity. But the scaled observable has mean of order \(B^{-1/2}\), whose square contributes at order \(B^{-1}\). **Do not omit that centering correction.**

The Lean-friendly decomposition is:

1. restrict to a fixed symmetric neighborhood of \(1\);
2. prove a Taylor remainder bound dominated after scaling by Gaussian times polynomial;
3. use the existing Gaussian-limit machinery on the rescaled remainder;
4. discharge polynomial Gaussian moments;
5. bound the complement exponentially using separation from the minimum.

Thus I would add a small reusable **second-order centered-moment Laplace lemma**, preferably atop `HigherLaplaceDomain`. A fixed-observable leading-limit theorem alone cannot justify the extra powers of \(B\).

---

## 4. The two-term wall law and its constant

For the flat-prior two-monomial model, set
\[
\sigma=\frac{p-q}{p},\qquad
h(c)=\sqrt{\operatorname{Var}_c(y^q)}.
\]
Scaling gives the exact identity
\[
\ell_t(a,b)=\int_{a t^\sigma}^{b t^\sigma}h(c)\,dc.
\]

The negative-profile expansion above yields
\[
h(-s)=k_-s^{\beta-1}+O(s^{-\beta-1}).
\]
The positive rescaling \(y=s^{-1/q}z\) gives
\[
h(s)=\frac1{\sqrt q\,s}+O(s^{-1-p/q}).
\]
Both subtracted tails are integrable. This is the essential structural point.

Define
\[
\begin{aligned}
C_{\rm prof}={}&
\int_{-\infty}^{-1}
  [h(c)-k_-(-c)^{\beta-1}]\,dc\\
&+\int_{-1}^{1}h(c)\,dc\\
&+\int_1^\infty
  [h(c)-1/(\sqrt q\,c)]\,dc
-\frac{k_-}{\beta}.
\end{aligned}
\]
Then, for \(A>0\), \(a_1>0\),
\[
\boxed{
\ell_t(-A,a_1)
=K_-(A)\sqrt t
+\frac{\sigma}{\sqrt q}\log t
+C_{\rm prof}+\frac{\log a_1}{\sqrt q}
+o(1).
}
\]

A useful prediction: **after subtracting \(K_-(A)\sqrt t\), the constant is independent of \(A>0\)**. The positive endpoint contributes only \((\log a_1)/\sqrt q\).

Before proving any model-specific rate, formalize an abstract theorem:

> If a locally integrable \(h\) has integrable residuals after subtracting \(k s^{\beta-1}\) at \(-\infty\) and \(c/s\) at \(+\infty\), then its expanding-window integral has the corresponding power, logarithm, and renormalized-constant expansion.

That isolates all hard analysis in two tail lemmas. It also makes the phase diagram a clean corollary:
\[
\begin{array}{ll}
a<0<b:& \ell_t(a,b)/\sqrt t\to K_-(-a),\\[2mm]
a=0<b:& \ell_t(0,b)/\log t\to \sigma/\sqrt q,\\[2mm]
0<a<b:& \ell_t(a,b)\to \dfrac1{\sqrt q}\log(b/a).
\end{array}
\]

The resulting story is unusually coherent: the negative chamber measures motion of a concentrated minimizer, the wall supplies a global transition profile, and the positive chamber becomes logarithmic scale geometry. The quotient mean map and square-root immersion then explain where this entire response geometry lives.