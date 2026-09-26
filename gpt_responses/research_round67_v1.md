## 1. Analytic tilt: use an existing Banach algebra, not a new one

**Recommendation: a variant of (b), using continuous functions on a compact feature ball.** In your finite-dimensional setting, Mathlib already has the required Banach algebra:
\[
A=C(K,\mathbb R),\qquad K=\overline B(0,R).
\]
Thus the missing ring structure on `Lp ∞` need not enter the proof.

Assume explicitly that \(S\) is measurable, \(\|S\|\le R\) a.e., and \(g\in L^1(\nu)\). **Bounded \(g\) alone requires finite \(\nu\)** or another integrable envelope.

### The two continuous linear maps

Modify \(S\) on its exceptional null set to obtain a measurable \(S_0:X\to K\). Taking \(R>0\) makes the default value \(0\in K\) immediate. Define
\[
A_\theta:E\to_L C(K,\mathbb R),\qquad
(A_\theta h)(z)=-\langle h,z\rangle ,
\]
and
\[
T_g:C(K,\mathbb R)\to_L L^1(\nu),\qquad
T_g(u)=[g\,(u\circ S_0)].
\]
Their bounds are
\[
\|A_\theta h\|_\infty\le R\|h\|,\qquad
\|T_g(u)\|_1\le \|g\|_1\|u\|_\infty.
\]

Then, exactly,
\[
\operatorname{weightL1}(\theta)=T_g\bigl(\exp_A(A_\theta\theta)\bigr).
\]

The following is a **structural Lean skeleton**, not a claim about every constructor’s exact argument order:

```lean
abbrev K := Metric.closedBall (0 : E) R
abbrev A := C(K, ℝ)

-- CompactSpace K from finite dimensionality / properness.
-- S₀ : X → K, measurable, with (fun x => (S₀ x : E)) =ᵐ[ν] S.

def featureCLM : E →L[ℝ] A := ...
-- h ↦ (z ↦ -⟪h, (z : E)⟫)
-- bound: ‖featureCLM h‖ ≤ R * ‖h‖

def weightedPullbackCLM : A →L[ℝ] Lp ℝ 1 ν := ...
-- u ↦ Integrable.toL1 (g * (u ∘ S₀))
-- bound: ‖weightedPullbackCLM u‖ ≤ ‖gL1‖ * ‖u‖

def analyticWeight (θ : E) : Lp ℝ 1 ν :=
  weightedPullbackCLM (NormedSpace.exp (featureCLM θ))
```

The actual obligations are modest:

* continuity of \(z\mapsto-\langle h,z\rangle\);
* linearity and the displayed uniform bound for `featureCLM`;
* integrability of \(g(u\circ S_0)\), dominated by \(\|u\|_\infty|g|\);
* linearity of `weightedPullbackCLM`, proved by L¹ extensionality;
* its norm estimate, from the integral norm bound;
* evaluation of the algebra exponential is scalar exponential.

For the last item, evaluate through the continuous algebra homomorphism \(u\mapsto u(z)\): it commutes with `exp`. If finding that specialization is awkward, apply evaluation to the defining exponential series.

Now use precisely the analytic tools in your inventory:

1. `ContinuousLinearMap.analyticAt`;
2. `NormedSpace.exp_analytic` in the commutative Banach algebra \(C(K,\mathbb R)\);
3. `AnalyticAt.comp`;
4. eventual/a.e. equality with your existing `weightL1`.

**Yes: prove the L¹ theorem once, then obtain the scalar integral by `L1.integralCLM`.** Bounded observable numerators follow by replacing \(g\) by \(Fg\), or by applying the corresponding continuous linear functional on L¹.

### Entire series, without manual multilinearity

This route also supplies your desired series. At a center \(a\), put \(g_a=g e^{-\langle a,S\rangle}\). Then
\[
P_{a,n}(h_1,\ldots,h_n)
=\frac1{n!}\left[g_a\prod_{i=1}^n(-\langle h_i,S\rangle)\right],
\]
with
\[
\|P_{a,n}\|\le \|g_a\|_1\frac{R^n}{n!}.
\]

Build it by composing:

* `ContinuousMultilinearMap.mkPiAlgebraFin` in \(C(K,\mathbb R)\);
* `compContinuousLinearMap`, using `featureCLM` in every slot;
* the continuous linear map \(T_{g_a}\);
* scalar multiplication by \(1/n!\).

The exponential series in the algebra, followed by \(T_{g_a}\), proves `hasSum`. No integration-of-analytic-families lemma is needed. The factorial bound proves `radius = ⊤`: for every finite \(\rho\), the terms \(\|P_{a,n}\|\rho^n\) are summable, or bounded by the scalar exponential majorant as required by the radius API.

This is **entire in the strong sense that the Taylor series has infinite radius**, not merely analytic at every real point.

### If the compact-algebra plumbing becomes expensive

Your option (a) remains an excellent fallback. Its only delicate point is proving convergence **in L¹**, not merely convergence of integrals:

\[
\left|g_a\sum_{n<N}\frac{(-\langle h,S\rangle)^n}{n!}\right|
\le |g_a|e^{R\|h\|}.
\]

Apply dominated convergence to the absolute difference from \(g_a e^{-\langle h,S\rangle}\), using twice that envelope, and identify its integral with the L¹ norm. Multilinearity is pointwise algebra followed by L¹ extensionality; continuity comes from the displayed product bound.

I would not pursue (c) or (d): neither removes more work than the compact Banach algebra does.

---

## 2. Grade-\(\omega\) inversion: use the local IFT directly

Your proposed route is correct. **Do not extend the old successor-grade bootstrap:** \(C^\infty\) does not imply grade \(\omega\).

Let \(f=\mathrm{chartV}\), \(z\in\operatorname{range}f\), and \(a=\mathrm{chartVInv}(z)\). At \(a\), supply:

* `ContDiffAt ℝ ω f a`, obtained from analyticity;
* `HasFDerivAt f (CDE a : V →L[ℝ] V) a`, where `CDE a` is a continuous linear equivalence;
* \(\omega\ne0\).

Then `ContDiffAt.to_localInverse` gives an analytic-grade local inverse near \(z=f(a)\).

### Identifying the inverse

For your globally injective `chartV`, this is particularly routine. On a neighborhood where the local inverse \(j\) satisfies
\[
f(j(y))=y,
\]
one automatically has \(y\in\operatorname{range}f\), hence
\[
f(\mathrm{chartVInv}(y))=y=f(j(y)).
\]
Injectivity gives eventual equality
\[
\mathrm{chartVInv}=j.
\]
Transfer `ContDiffAt` across that eventual equality.

Thus you do not even need to separately intersect with the image merely to establish membership: the local right-inverse equation supplies it. If injectivity is only known on a parameter domain, additionally ensure that both inverse values remain in that domain.

**Worth extracting:** a small project lemma saying that a specified inverse of an analytic map with invertible derivative is analytic on its open image. Prove it once by this argument rather than hunting for a more specialized inverse theorem.

### Finish the atlas

Once the inverse is analytic, composition and division give:

\[
M\longmapsto[q_M]\in L^1(\nu)
\]
analytic on the relative interior mean domain, and
\[
s\longmapsto p(s)
\]
analytic on the open set where the affine mean path lies in that domain.

For every **bounded measurable observable** \(F\), the response
\[
s\longmapsto E_{Q_{M_s}}F
\]
is analytic by a continuous linear functional on L¹. Unbounded observables need separate weighted-integrability control; they do not follow from L¹ analyticity alone.

### Traps to avoid

* State the primary conclusion as `AnalyticOnNhd` on an **open subset of the displacement space \(V\)**.
* A relative interior generally is not open in the original redundant ambient feature space. Your \(m_0+V\) coordinates solve this.
* On an open set, pass pointwise between `ContDiffWithinAt` and `ContDiffAt`, then use `.analyticAt`. This avoids unnecessary `UniqueDiffOn` bookkeeping.
* On arbitrary non-open sets, `AnalyticOn` is not interchangeable with `AnalyticOnNhd`.
* The numerator is entire; the **normalized density and inverse chart are only locally analytic**. Complex zeros of the partition function prevent inheriting infinite Taylor radius through division.

---

## 3. Quantitative analyticity: take the cheap natural-parameter theorem first

The scale
\[
r_M=c\lambda^2/L^3
\]
is still valuable: it quantifies how far the **mean-coordinate** atlas is guaranteed to continue analytically.

But I would not expect to extract this from `to_localInverse`. Even if its underlying IFT construction uses quantitative estimates, the interface you listed does not expose the complex/power-series neighborhood needed for that conclusion. Budget it as a separate quantitative analytic inverse argument.

### Best one-module quantitative target

At a base distribution \(Q_a\), suppose
\[
T=S-M_a,\qquad \|T\|\le L\quad Q_a\text{-a.e.}
\]
Then
\[
q_{a+h}
=q_a\,\frac{e^{-\langle h,T\rangle}}
              {E_{Q_a}e^{-\langle h,T\rangle}}.
\]

The numerator coefficients have bounds \(L^n/n!\), and the denominator perturbation has majorant
\[
e^{Lt}-1.
\]
Consequently, geometric inversion gives an L¹-valued Taylor series whose coefficient norms are majorized by
\[
\frac{e^{Lt}}{2-e^{Lt}},
\qquad Lt<\log 2.
\]

In particular, for \(L>0\), set
\[
\rho_\theta=\frac{\log(3/2)}L.
\]
One can construct coefficients \(A_n\) satisfying
\[
\sum_{n\ge0}\|A_n\|\rho_\theta^n\le3,
\qquad
\|D^n q_a\|_{\mathrm{op}}
\le 3n!\rho_\theta^{-n}.
\]
The \(L=0\) case is constant.

A convenient remainder consequence, for \(t=\|h\|<\rho_\theta\), is
\[
\left\|q_{a+h}-\sum_{n=0}^N A_n(h,\ldots,h)\right\|_1
\le 3\left(\frac{t}{\rho_\theta}\right)^{N+1}.
\]

This uses only exponential coefficients, integration, and a geometric-series inverse. **No complexification is necessary.** It also immediately controls every bounded-observable Taylor remainder.

This is substantially cheaper than a quantitative mean-coordinate inverse, while being more informative than “the unnormalized tilt is entire.”

Keep the distinction explicit: a natural-parameter radius is not a mean-space radius. Along \(M_s=m+s\delta\), a mean-space radius \(r_M\) would translate to a guaranteed parameter radius \(r_M/\|\delta\|\), when \(\delta\ne0\).

---

## 4. Re-ranking toward “the whole response space”

### 1. Qualitative analytic response atlas

**Precise target**
\[
\operatorname{AnalyticOnNhd}_{\mathbb R}
\bigl(M\mapsto[q_M]\bigr)
\quad\text{on the open interior displacement domain}.
\]

Include as corollaries:

* analytic normalized tilt and inverse mean chart;
* analytic mean-coordinate response for every bounded observable;
* analytic affine-path reconstruction on its maximal interior parameter domain.

**Seabed route:** the two-CLM compact-algebra construction; your normalization formulas; grade-\(\omega\) local inversion plus injectivity; composition.

This is the highest return: it upgrades the entire existing jet calculus with one genuinely new ingredient.

### 2. Finite-\(X\) face completion — and preferably a strong deformation retraction

This best answers “all the way to the data distribution,” including boundary means.

Let \(X\) be finite, let the reference weights \(w_x>0\), and let
\[
C=\operatorname{conv}\{S(x):x\in X\}.
\]
For \(m\in C\), define
\[
q^*(m)=
\underset{\substack{q\in\Delta_X\\E_qS=m}}{\arg\min}
D(q\|w).
\]

**Precise package**

1. \(q^*(m)\) exists uniquely and depends continuously on \(m\).
2. In \(\operatorname{relint}C\), it agrees with your existing exponential-family reconstruction.
3. If \(F\) is the minimal face containing \(m\), then
   \[
   \operatorname{supp}q^*(m)=\{x:S(x)\in F\},
   \]
   and \(q^*(m)\) is the restricted exponential-family solution on that face.
4. The completed family is exactly the closure of the interior family, and the moment map identifies it homeomorphically with \(C\).
5. The map
   \[
   R(p)=q^*(E_pS)
   \]
   is a continuous, moment-preserving retraction of the simplex onto the completed family.

There is a beautiful inexpensive extra:
\[
H_t(p)=(1-t)p+tR(p).
\]
Because \(E_{H_t(p)}S=E_pS\),
\[
R(H_t(p))=R(p).
\]
Thus \(H\) is a **strong deformation retraction**, once continuity of \(R\) is established.

**Seabed route:** compactness of finite-dimensional feasible polytopes; continuity and strict convexity of finite KL with \(0\log0=0\); identify the interior optimizer using your existing normal form. Prove boundary continuity through a polytope-specific feasible-lifting lemma plus compactness—not merely “limits of minimizers,” which needs the recovery-sequence direction. Exposed-face limits identify the closure: add a diverging normal parameter selecting a face, while retaining its finite tangential parameter.

For full-support \(w\), the segment from \(E_wS\) to any \(m\in C\) remains in \(\operatorname{relint}C\) until its endpoint. You therefore obtain an **analytic interior path with a continuous completed endpoint**.

One essential limitation: \(R(p_{\mathrm{data}})\) need not equal \(p_{\mathrm{data}}\). Exact recovery requires the data distribution to belong to the completed family, or sufficiently rich features.

### 3. Explicit analytic estimates

First the natural-parameter coefficient/remainder module above; then the mean-space radius \(c\lambda^2/L^3\). The latter is especially useful for certified continuation, but should not delay completion of the qualitative geometry.

### 4. Moving projection / all-orders normal jets

Prefer a structural theorem over a large Bell-polynomial expansion. If
\[
B_k=q^{-1}p^{(k)},\qquad k\ge2,
\]
then along an affine mean path,
\[
B_{k+1}=N_s\bigl(\partial_sB_k+\ell_sB_k\bigr).
\]
This follows from differentiation and the invisible tower.

The key warning is that \(N_s\) moves: replacing derivatives of projected expressions by projections of derivatives loses precisely the bending terms already visible in your third jet. A clean differentiation identity for the moving normal projection would organize every higher order.

### 5. Reconstruction CLT

An elegant eventual corollary:
\[
\sqrt n\bigl(q_{\widehat M_n}-q_M\bigr)
\Rightarrow Dq_M[Z]\quad\text{in }L^1,
\]
with \(Z\) the finite-dimensional Gaussian mean fluctuation. Define reconstruction outside the interior arbitrarily, or work on the event of interior membership, whose probability tends to one.

It gives statistical meaning to the tangent response map, but face completion more directly advances the user’s geometric direction.

**Bottom line:** build analyticity through \(C(K,\mathbb R)\), invert at grade \(\omega\), then complete the finite family across faces. That yields an analytic interior atlas sitting inside a continuous, moment-preserving reconstruction of the whole simplex.