**Yes—the exact logarithmic constant is the right next target. And there is a substantially shorter localisation proof: radius-independence itself makes the complement negligible, without dimension reduction.**

I am assessing the mathematical statements here, not auditing the Lean declarations.

## (a) Exact constant: correct, with global control as well as local continuity

Assume the usual fully tied logarithmic hypotheses:
\[
n=k+1,\qquad \kappa_i>0,\qquad \lambda>0,\qquad
r_i+1=\lambda\kappa_i,\qquad \delta>0.
\]
Then your cancellation of the \(R\)-dependence is exactly right.

Joint continuity of \(W,a\) at \((0,0)\), together with \(a(0,0)>0\) and \(v(t)\to0\), provides everything needed **on a sufficiently small box**. For the entire original box, you also need tail control. A convenient sufficient package is, for all sufficiently large \(t\),
\[
a(x,v(t))\ge a_{\min}>0,\qquad
|W(x,v(t))|\le M
\]
throughout that box.

Thus:

- **Local continuity determines the constant.**
- **A global positive lower bound on the unit and a global bound on the weight exclude competing contributions elsewhere.**

Continuity only at the face point is not, by itself, sufficient. For example, a unit could approach zero elsewhere as \(v\to0\), creating another contribution that the local argument cannot control. Continuous, nonvanishing units on a compact closed chart box give the required uniform lower bound automatically.

Signed weights pose no mathematical difficulty, but a positive-weight sandwich should not be applied blindly when \(W(0,0)-\varepsilon<0\). Instead use
\[
|W-w_0|\le\varepsilon
\]
to bound the weight error by a positive kernel, and separately squeeze the kernel with unit \(a\).

### Continuity in chart coordinates

I agree in the \(Q=0\) setting **provided the bridge map extends continuously to the relevant closed face**, and the weight means the residual continuous weight after extracting the monomial powers.

That proviso matters in general: for truth \(xy=s\), the bridge \((x,v)\mapsto(x,v/x)\) does not extend jointly continuously at \((0,0)\). Continuity of the original chart unit does not repair that. In the genuinely product-like \(Q=0\) situation, where the bridge is continuous at the face, your composition argument is sound.

## (b) A shorter proof: subtract two constant-unit boxes

Write
\[
J_R(t;c)
=
\int_{(0,R)^n}
x^r\exp\!\left(-Bc\,t^\delta x^\kappa\right)\,dx,
\qquad
N(t)=\frac{t^{\delta\lambda}}{(\log t)^k}.
\]
Your constant-model theorem gives
\[
N(t)J_R(t;c)\longrightarrow
C(c):=
(Bc)^{-\lambda}
\frac{\delta^k\Gamma(\lambda)}{k!}
\prod_i\frac1{\kappa_i},
\]
and \(C(c)\) is independent of \(R\).

Consequently, for every fixed \(0<R'<R\),
\[
\begin{aligned}
&N(t)\int_{(0,R)^n\setminus(0,R')^n}
x^r e^{-Bc\,t^\delta x^\kappa}\,dx\\
&\qquad =
N(t)J_R(t;c)-N(t)J_{R'}(t;c)
\longrightarrow 0.
\end{aligned}
\]

Now apply the global bounds:
\[
\begin{aligned}
&N(t)\left|
\int_{(0,R)^n\setminus(0,R')^n}
W(x,v(t))x^r
e^{-Bt^\delta a(x,v(t))x^\kappa}\,dx
\right|\\
&\qquad\le
M N(t)\bigl(J_R(t;a_{\min})-J_{R'}(t;a_{\min})\bigr)
\longrightarrow0.
\end{aligned}
\]

That is the entire complement argument. It works also for \(k=0\); no separate exponential-decay proof is needed.

Inside the small box, choose \(R'\) and then \(t\) large enough that
\[
|W-w_0|\le\varepsilon,\qquad |a-a_0|\le\varepsilon,
\qquad \varepsilon<a_0.
\]
For the unweighted moving-unit integral \(I_{R'}(t)\),
\[
J_{R'}(t;a_0+\varepsilon)
\le I_{R'}(t)
\le J_{R'}(t;a_0-\varepsilon).
\]
Also,
\[
N(t)\left|
\int_{(0,R')^n}(W-w_0)x^r
e^{-Bt^\delta a x^\kappa}\,dx
\right|
\le \varepsilon N(t)J_{R'}(t;a_0-\varepsilon).
\]
Take limits, then let \(\varepsilon\to0\), using continuity of \(C(c)\) for \(c>0\). Restoring the factor \(A t^{-\gamma p}\) gives exactly your proposed constant.

**For Lean, I would make this the main route.** It needs nested-box integral subtraction, the existing constant-model limits, and a norm bound—not `piFinSuccAbove` or an induction on dimension.

Your coordinate-wise argument is nevertheless correct under the same global bounds. It proves the stronger fixed-complement estimate
\[
O((\log t)^{-1})
\]
at the target normalisation when \(k\ge1\), and exponential negligibility when \(k=0\). Keep it if that quantitative estimate will be useful; it is unnecessary for the exact limit.

### Useful abstraction

The underlying statement is an approximate-identity theorem:
\[
N(t)\,1_{(0,R)^n}x^r
e^{-Bc\,t^\delta x^\kappa}\,dx
\;\Rightarrow\; C(c)\,\delta_0
\]
as finite measures on the closed box.

That makes the geometry particularly clear: despite the continuum of logarithmic allocations among coordinates, the physical box variables concentrate at the origin. A reusable “radius-independent box asymptotics imply localisation” lemma could serve beyond this particular kernel.

## (c) Next targets: my ranking

### 1. A genuine atlas-level expectation example — candidate (ii)

After the exact logarithmic theorem, this is my first choice.

You now have strong local ingredients. The most valuable remaining integration test is:
\[
\text{atlas transport}
\to\text{chart asymptotics}
\to\text{power-log selection}
\to\text{expectation ratio}.
\]

A two-chart example exercises issues that another local certificate does not:

- coverage modulo null sets;
- overlap or partition-of-unity bookkeeping;
- signs and chart multiplicities;
- subdominant chart contributions;
- assembly of the observable and denominator with the same geometric weights.

Ideally, the final theorem should allow chart terms
\[
K_\ell(t;f)\sim t^{-\lambda_\ell}(\log t)^{k_\ell}C_\ell(f),
\]
and explicitly conclude
\[
\frac{\sum_\ell K_\ell(t;\psi)}
     {\sum_\ell K_\ell(t;\chi)}
\longrightarrow
\frac{\sum_{\ell\in D}C_\ell(\psi)}
     {\sum_{\ell\in D}C_\ell(\chi)},
\]
where \(D\) is the lexicographically dominant collection and the denominator constant is positive.

If `PowerLogAssembly` already provides this full signed-observable ratio wrapper, the atlas instance alone is the gap. Otherwise, I would bundle that wrapper with the instance.

A simple example with one subdominant chart is already worthwhile. An example with two genuinely leading chart contributions would test more of the assembly.

### 2. State precisely what limiting expectations retain — candidate (iii)

For the note’s conceptual aim, I would then make the **limiting weighted measure on the dominant strata** explicit.

The important distinction is:

- partition-function asymptotics retain absolute scale information, such as \((\lambda,k)\) and total coefficients;
- leading expectation ratios retain the corresponding **normalised** limiting measure.

In particular, concentration at one point makes all continuous-observable limits point evaluations. Those limits alone cannot distinguish many different local losses, learning exponents, or overall amplitudes.

A theorem phrased through a limiting measure would turn this from an interpretive remark into a clean mathematical answer to “what expectation values know.” It would also naturally handle faces whose surviving unscaled coordinates do not collapse to one point.

### 3. General degenerate-LP classification — candidate (i)

Important, but I would put the full classification after the end-to-end example.

The key distinction is not “one scaled coordinate versus several”; it is:

> **isolated optimum versus positive-dimensional optimal face**, with all active constraints included.

With strict truth and several freely scaled coordinates, your recession obstruction is decisive. If there are at least two scaled coordinates, there is a nonzero supported direction with \(d\cdot\kappa=0\); choosing its sign makes \(d\cdot(r+1)\ge0\). Thus an ordinary integrable profile is impossible in that setting.

With tied truth, additional active constraints change the recession cone. Two scaled coordinates can occur at an isolated vertex determined by two active constraints. That need not produce a logarithm.

#### Is “integrable iff isolated” plausible?

**Yes, in an appropriately specified polyhedral monomial model. Not as an unrestricted statement about arbitrary units.**

A natural intermediate target is the following. Let
\[
P=\log L,\qquad h=r+1,
\]
with \(P\) a full-dimensional polyhedron, and suppose the phase is uniformly comparable to \(e^{\kappa\cdot z}\). Then the expected exact criterion is
\[
\int_P e^{h\cdot z}e^{-a(z)e^{\kappa\cdot z}}\,dz<\infty
\quad\Longleftrightarrow\quad
h\cdot d<0
\quad
\forall\,0\ne d\in\operatorname{Rec}(P)
\text{ with }\kappa\cdot d\le0.
\]
Here uniform comparability means \(0<a_{\min}\le a(z)\le a_{\max}<\infty\).

Your recession theorem supplies the necessity. A polyhedral cone argument should supply sufficiency. If this cone identifies with the negative feasible tangent cone of the LP at the selected optimum, strict negativity is precisely the isolation condition.

Positive-dimensional optimal faces then belong to the log-face machinery. Under the usual nonvanishing and nondegeneracy assumptions, face dimension is the natural logarithmic degree—but vanishing amplitudes and active truth boundaries still need explicit treatment.

## (d) Soundness checks on items 1–3

I see no intrinsic mathematical problem, but these are the points I would make explicit in the public statements.

### 1. Vertex certificate

The Gamma reduction is sound, including negative \(\kappa_j\). The common formula is
\[
\int_0^\infty
u_j^{r_j}e^{-cP u_j^{\kappa_j}}\,du_j
=
\frac{\Gamma(\eta)}{|\kappa_j|}
(cP)^{-\eta},
\qquad
\eta=\frac{r_j+1}{\kappa_j}>0.
\]
The absolute value in the Jacobian factor is essential.

For a variable unit, this is a comparison calculation using its lower bound, not an exact integration of that unit. A lower bound alone really does suffice for both integrabilities, provided the weighted factor is the same nonnegative phase appearing in the exponential:
\[
\Phi e^{-\Phi}\le 2e^{-\Phi/2}.
\]

The remaining exponents and strict-optimality inequalities match exactly. Strict truth is important because it identifies the limiting domain used in that reduction; it should not disappear from the wrapper’s interpretation.

### 2. General recession direction

The argument is convincing. The necessary bookkeeping is:

- \(d\ne0\);
- measurable \(L\) and phase;
- a positive-volume box compactly contained in the positive orthant;
- forward invariance under the relevant transports;
- a phase upper bound valid on those transported boxes.

Full two-sided flow invariance is stronger than necessary; forward invariance is enough.

The phase upper bound is essential for the obstruction. An arbitrarily growing unit can suppress mass along a nominally bad monomial recession direction. Thus the result is not an obstruction based solely on \((\kappa,r)\) without phase control.

### 3. Blow-up example

The listed exponents are consistent with the direct calculation:
\[
\gamma+(-2)(\gamma-\tfrac12)=1,
\qquad
\gamma+(-1)(\gamma-\tfrac12)=\tfrac12,
\]
respectively giving tied phase and the \(t^{-1/2}\) scale.

The main audit point is the sign multiplicity. For ordinary fibre Lebesgue measure, the **full** sector contributes
\[
\int_{|s|\le |z_1|\le1}e^{-t(s^2+z_1^2)}\phi(s,z_1)\,dz_1
\sim \phi(0)\sqrt{\pi}\,t^{-1/2}
\]
when \(s=D t^{-\gamma}\), \(\gamma>1/2\). The constant \(\phi(0)\sqrt\pi/2\) is the contribution of one sign branch. Your wording “term constant” is consistent with that; just ensure the final sector theorem sums both branches.

Also retain the usual positivity/nonvanishing assumption on the denominator observable for the ratio conclusion.

**Bottom line:** prove localisation by subtracting nested constant-unit boxes; then use the exact-log result in a genuine atlas-level ratio example. The recession/LP equivalence is a strong subsequent theorem, but the atlas assembly will currently add more end-to-end value.