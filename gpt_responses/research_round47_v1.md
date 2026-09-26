## Verdict

The next deepest theorem is **an exhaustive description of the finite-information boundary**, not another interior regularity theorem:

> **Every finite-information response is obtained by finitely many exposed conditionings, followed by an ordinary finite tilt on the final conditioned law.**

You have an interior chart, endpoint convergence, and necessary normal-cone conditions. What is still missing is a **converse, constructive description of every endpoint**. A referee interested in the *whole* response atlas would ask: “Do your face constructions exhaust the finite-rate boundary, or are they only examples?”

Two qualifications should remain explicit throughout:

- The atlas reaches **\(\Pi(M_D)\), not generally \(D\)**. Matching finitely many expectations cannot recover every bounded-observable response of \(D\).
- For general \(\nu\), the starting law is the **zero-relative-information reference law**, not necessarily a maximum-Shannon-entropy law.

My ranking is below. Rank measures conceptual value; the cheap duality theorem in item 6 could be implemented immediately.

---

# 1. Exhaustive face-conditioned completion of the atlas

**This is my proposed second centrepiece after the budget.** Candidate **(c)** is its essential analytic building block, but the exhaustive theorem is substantially stronger.

### 1A. First prove the fixed-normal limit, in total variation

Let
\[
P_\theta(dx)=Z(\theta)^{-1}e^{-\langle\theta,S(x)\rangle}\nu(dx).
\]
Assume \(S\) is measurable and essentially bounded, \(\nu\) is a probability measure, and
\[
\langle a,S\rangle\le h\quad \nu\text{-a.e.},\qquad
F=\{x:\langle a,S(x)\rangle=h\},\qquad \nu(F)>0.
\]
For fixed \(\eta\), put
\[
Q_{\eta,F}(dx)
=\frac{e^{-\langle\eta,S(x)\rangle}1_F(x)}
       {\int_F e^{-\langle\eta,S\rangle}\,d\nu}\nu(dx).
\]

Then
\[
P_{\eta-ta}\longrightarrow Q_{\eta,F}
\quad\text{in total variation as }t\to\infty.
\]

A useful stronger package is
\[
\begin{aligned}
p_t&:=P_{\eta-ta}(F),\\
P_{\eta-ta}(\,\cdot\mid F)&=Q_{\eta,F},\\
d_{\rm TV}(P_{\eta-ta},Q_{\eta,F})&=1-p_t,\\
\operatorname{KL}(Q_{\eta,F}\Vert P_{\eta-ta})&=-\log p_t\longrightarrow0.
\end{aligned}
\]
Here \(d_{\rm TV}=\sup_A|P(A)-Q(A)|\).

**Do not claim convergence of the reverse KL.** If \(\nu(F^c)>0\), then
\[
\operatorname{KL}(P_{\eta-ta}\Vert Q_{\eta,F})=\infty
\]
for every finite \(t\).

Schematic Lean statements:
```lean
theorem tendsto_tilt_fixedNormal_totalVariation
    (ha : ∀ᵐ x ∂ν, inner a (S x) ≤ h)
    (hF : 0 < ν {x | inner a (S x) = h}) :
    Tendsto
      (fun t : ℝ => tvDist (tilt ν S (η - t • a)) (faceTilt ν S η a h))
      atTop (𝓝 0)

theorem kl_faceTilt_tilt_fixedNormal :
    klDiv (faceTilt ν S η a h) (tilt ν S (η - t • a))
      = ENNReal.ofReal (-Real.log (tilt ν S (η - t • a) F).toReal)
```
The second statement needs the usual finite-\(t\), probability and positivity hypotheses.

**Proof:** remove the common factor \(e^{th}\) and apply dominated convergence to
\[
e^{-\langle\eta,S\rangle}e^{-t(h-\langle a,S\rangle)}.
\]
The exact conditional identity gives the TV and KL formulas almost for free.

If additionally \(h-\langle a,S\rangle\ge\delta>0\) off \(F\), obtain exponential rates. Without this gap, assert convergence but no universal exponential rate.

### 1B. Then prove exhaustion by finite exposed chains

Let \(K_\rho\) denote the essential moment body for a reference law \(\rho\). For every \(M\) with \(\mathcal I_\nu(M)<\infty\), there exist
\[
\nu_0=\nu,\ \nu_1,\ldots,\nu_k,\qquad k\le\dim\mathbb V,
\]
such that:

1. \(\nu_{i+1}\) is \(\nu_i\) conditioned on a positive-mass proper exposed face of \(K_{\nu_i}\);
2. \(M\) lies on that face;
3. \(M\in\operatorname{relint}K_{\nu_k}\);
4. for some finite \(\eta\),
   \[
   \Pi_\nu(M)=\operatorname{tilt}_{\nu_k}(\eta).
   \]

If \(\nu_k=\nu(\cdot\mid A)\), then also
\[
\boxed{\quad
\mathcal I_\nu(M)=-\log\nu(A)+\mathcal I_{\nu(\cdot\mid A)}(M).
\quad}
\]

Schematic target:
```lean
theorem exists_exposedChain_chart_of_rate_lt_top
    (hM : rate ν S M < ⊤) :
    ∃ c : PositiveExposedChain ν S,
      c.length ≤ finrank ℝ (visibleSubspace ν S) ∧
      M ∈ relativeInterior (momentBody c.finalLaw S) ∧
      ∃ η, projection ν S M = tilt c.finalLaw S η
```

**Proof route using your landed layer:**

- Take the finite-entropy projection at \(M\).
- If \(M\) is not in the relative interior, use a supporting hyperplane.
- Equality of the supporting expectation forces every feasible law to be supported on its preimage.
- Absolute continuity of the projection forces that preimage to have positive reference mass.
- Condition, apply the conditioning entropy identity, and repeat.
- Each proper step strictly decreases affine dimension.
- Finish with the existing relative-interior chart.

**Important precision:** recurse on the **essential moment body of the conditioned law**, not automatically on the entire geometric face of the original body. These can differ.

This gives an exhaustive face-conditioned completion. It does **not**, without additional work, give a canonical disjoint or Whitney stratification. Chains need not be unique, and a single fixed normal ray need not reach every stratum. Iterated limits—or a diagonal sequence of tilts—are the correct general formulation.

---

# 2. Arbitrary-observable transport, with an exact second-order residual formula

Candidate **(a)** is the best next **interior response theorem**. Its strongest formulation is not merely “differentiate twice”; it is:

> **First-order motion is regression. Second-order motion is the interaction between the regression residual and squared score.**

Work on a compact subinterval of the interior path. Write
\[
\Delta=M_D-m_0,\qquad P_s=\Pi(m_0+s\Delta).
\]
All covariance operators below are restricted to \(\mathbb V\). Define
\[
\begin{aligned}
C_s&=\operatorname{Cov}_{P_s}(S,S),\\
v_s&=C_s^{-1}\Delta=-\theta_s',\\
c_{\varphi,s}&=\operatorname{Cov}_{P_s}(S,\varphi),\\
\beta_{\varphi,s}&=C_s^{-1}c_{\varphi,s},\\
r_{\varphi,s}(x)
 &=\varphi(x)-E_{P_s}\varphi
   -\langle\beta_{\varphi,s},S(x)-M_s\rangle.
\end{aligned}
\]

For bounded measurable \(\varphi\),
\[
\boxed{
\frac d{ds}E_{P_s}\varphi
=\langle\beta_{\varphi,s},\Delta\rangle
}
\]
and
\[
\boxed{
\frac {d^2}{ds^2}E_{P_s}\varphi
=
E_{P_s}\!\left[
r_{\varphi,s}
\langle v_s,S-M_s\rangle^2
\right].
}
\]

Equivalently,
\[
\frac {d^2}{ds^2}E_{P_s}\varphi
=
T_{\varphi,s}(v_s,v_s)
-\left\langle
c_{\varphi,s},C_s^{-1}T_s(v_s,v_s,\cdot)
\right\rangle.
\]

Lean-shaped target:
```lean
theorem hasDerivAt_observableResponse_deriv
    (hφ : AEStronglyMeasurable φ ν)
    (hφ_bdd : ∀ᵐ x ∂ν, ‖φ x‖ ≤ L)
    (hs : s ∈ Ioo 0 1) :
    HasDerivAt
      (fun t => inner (observableRegression t φ) Δ)
      (∫ x, observableResidual s φ x *
        (inner (inverseCovariance s Δ) (S x - M s)) ^ 2 ∂P s)
      s
```

### The correct nonlinear remainder statement

Using the **basepoint** coefficient \(\beta_{\varphi,0}\),
\[
E_{P_s}\varphi-E_\nu\varphi
=s\langle\beta_{\varphi,0},\Delta\rangle
+\int_0^s(s-u)\,
 E_{P_u}[r_{\varphi,u}\langle v_u,S-M_u\rangle^2]\,du.
\]

Thus “the visible part is what moves” is true **instantaneously**, but false if interpreted as saying that a fixed basepoint regression residual never moves. That residual generally starts moving at second order.

For an explicit bound, suppose
\[
\|S\|\le B,\quad |\varphi|\le L,\quad
\|\theta_u\|\le r\quad(0\le u\le s),
\]
and set \(\kappa_r=e^{-2Br}\lambda_0\). One convenient, nonoptimal bound is
\[
\left|
E_{P_s}\varphi-E_\nu\varphi
-s\langle\beta_{\varphi,0},\Delta\rangle
\right|
\le
\frac{LB^2}{\kappa_r^2}
\left(1+\frac{B^2}{\kappa_r}\right)
s^2\|\Delta\|^2.
\]

**Proof route:** prove only the regularity needed:
\[
D_\theta C_\theta[w]=-T_\theta(\cdot,\cdot,w),
\]
differentiate \(C_sv_s=\Delta\), and use covariance differentiation. Full \(C^\infty\) remains unnecessary.

Do not extend this uniform bound to a boundary endpoint: the bounded-natural-coordinate hypothesis is doing real work.

---

# 3. The correct residual-information theorem—and its endpoint limit

Candidate **(b)** contains an important false claim. Correcting it would materially improve the paper.

## 3A. Residual information is not just conditional information given \(S\)

Let \(D_S=S_*D\), \(\nu_S=S_*\nu\), and \(P=\Pi(M_D)\). When \(P\) is a tilt, including a face-conditioned tilt, its density relative to \(\nu\) is a measurable function of \(S\). Consequently, \(P\) and \(\nu\) have the same conditional law given \(S\), wherever relevant.

But the chain rule is
\[
\boxed{
\operatorname{KL}(D\Vert P)
=
\operatorname{KL}(D_S\Vert P_S)
+
\int \operatorname{KL}\bigl(D(\cdot\mid S=z)
                    \Vert\nu(\cdot\mid S=z)\bigr)\,D_S(dz).
}
\]

The first term does **not** vanish merely because \(D\) and \(P\) have the same mean of \(S\). Equal means are much weaker than equal pushforward distributions.

A decisive example: if \(S\) is injective, the conditional term vanishes, but \(\operatorname{KL}(D\Vert P)\) can still be positive.

Thus the invisible information has two pieces:

1. **unmatched distributional structure of \(S\)** beyond its prescribed expectations;
2. **unmatched conditional structure inside the fibres of \(S\)**.

### A version preserving general measurable \(X\)

Avoid regular conditional probabilities initially. Define the reference-conditional lift
\[
D^\uparrow(dx)
=\frac{dD_S}{d\nu_S}(S(x))\,\nu(dx).
\]
Then prove
\[
\boxed{
\operatorname{KL}(D\Vert P)
=
\operatorname{KL}(D\Vert D^\uparrow)
+\operatorname{KL}(D_S\Vert P_S).
}
\]

Schematic:
```lean
def conditionalLift :=
  ν.withDensity (fun x => (Measure.map S D).rnDeriv (Measure.map S ν) (S x))

theorem kl_projection_eq_kl_conditionalLift_add_kl_map
    (hD : klDiv D ν < ⊤) :
    klDiv D (projection ν S (mean D S))
      = klDiv D (conditionalLift ν D S)
        + klDiv (Measure.map S D)
            (Measure.map S (projection ν S (mean D S)))
```

Prove the disintegration interpretation separately under standard-Borel hypotheses on \(X\). Do not silently add those hypotheses to the whole existing development.

## 3B. Endpoint convergence is cheap; a universal rate is not

Put
\[
H=\operatorname{KL}(D\Vert\nu),\quad
H_s=\operatorname{KL}(D_s\Vert\nu),\quad
R_s=H_s-\mathcal I(M_s).
\]
Your landed endpoint results imply
\[
R_s\longrightarrow H-\mathcal I(M_D)
=\operatorname{KL}(D\Vert\Pi(M_D)).
\]

Mixture compensation gives the useful explicit estimate
\[
sH-h_2(s)\le H_s\le sH,
\]
where \(h_2\) is binary entropy. If
\[
\delta I_s=\mathcal I(M_D)-\mathcal I(M_s),
\]
then
\[
(1-s)H-\delta I_s
\le R_1-R_s
\le (1-s)H+h_2(s)-\delta I_s.
\]

This is a clean endpoint modulus **in terms of the atlas information gap**. An explicit rate then follows from any available bound on that gap.

Do not assert that \(R_s\) is monotone, or that its second derivative is nonnegative. In particular, the name “invisible information density” does not by itself make
\(\mathcal F_{\rm data}(s)-\kappa(s)\) pointwise nonnegative.

---

# 4. Sharp interior endpoint rates: distinguish the information gap from KL

Candidate **(f)** is valuable, but its quadratic claim needs correction.

Assume \(M\in\operatorname{relint}K\), let \(g(s)=\mathcal I(M_s)\), and suppose \(\|\theta_s\|\le r\). Then
\[
g'(s)=-\langle\theta_s,\Delta\rangle,\qquad
g''(s)=\langle\Delta,C_s^{-1}\Delta\rangle.
\]

There are two exact tail formulas:
\[
\boxed{
\operatorname{KL}(\Pi(M)\Vert\Pi(M_s))
=\int_s^1(1-u)g''(u)\,du,
}
\]
and
\[
\boxed{
\operatorname{KL}(\Pi(M_s)\Vert\Pi(M))
=\int_s^1(u-s)g''(u)\,du.
}
\]

Therefore both KL divergences satisfy
\[
\operatorname{KL}(\cdots)
\le \frac{\|\Delta\|^2}{2\kappa_r}(1-s)^2.
\]

But
\[
\mathcal I(M)-\mathcal I(M_s)
=(1-s)g'(1)+O((1-s)^2),
\]
so the **information gap is generally first order**, not second order. More explicitly,
\[
0\le \mathcal I(M)-\mathcal I(M_s)
\le(1-s)(-\langle\theta(M),\Delta\rangle).
\]

Lean-shaped:
```lean
theorem kl_projection_endpoint_le_sq
    (hM : M ∈ relativeInterior (momentBody ν S))
    (hθ : ∀ u ∈ Icc s 1, ‖atlasCoord M u‖ ≤ r) :
    klReal (projection ν S M) (projection ν S (Mpath M s))
      ≤ ‖M - mean ν S‖ ^ 2 / (2 * coercivityRadius r) * (1 - s) ^ 2
```

Pinsker then yields linear endpoint convergence for bounded-observable responses. For \(|\varphi|\le L\),
\[
|E_{\Pi(M)}\varphi-E_{\Pi(M_s)}\varphi|
\le \frac{L\|\Delta\|}{\sqrt{\kappa_r}}(1-s).
\]

**Proof route:** Bregman KL plus the one-dimensional integral Taylor formula, followed by inverse coercivity. This is high-value reuse, not a new major theory.

---

# 5. Fisher-orthogonal tangent/fibre decomposition

This is the substantive version of candidate **(e)**. I would formalise this before introducing geodesic terminology.

At an interior family member \(P\), work in
\[
L^2_0(P)=\{h\in L^2(P):E_Ph=0\}.
\]
Define
\[
A_Ph=E_P[h(S-M)]\in\mathbb V.
\]
Then the Fisher-orthogonal projection onto the exponential-family score space is
\[
\mathsf P_Ph
=\left\langle C_P^{-1}A_Ph,S-M\right\rangle.
\]

Prove:
\[
\begin{aligned}
A_P(h-\mathsf P_Ph)&=0,\\
\langle \mathsf P_Ph,h-\mathsf P_Ph\rangle_{L^2(P)}&=0,\\
\|h\|_{L^2(P)}^2
&=\langle A_Ph,C_P^{-1}A_Ph\rangle
 +\|h-\mathsf P_Ph\|_{L^2(P)}^2.
\end{aligned}
\]

Schematic:
```lean
theorem fisher_norm_sq_eq_visible_add_residual
    (h : Lp ℝ 2 P) (hh : ∫ x, h x ∂P = 0) :
    ‖h‖ ^ 2
      = inner (momentTangent h) (inverseCovariance P (momentTangent h))
        + ‖h - visibleScoreProjection P h‖ ^ 2
```

This identifies:

- exponential-family tangent directions;
- moment-preserving fibre directions;
- their orthogonality at the projection;
- the dual Fisher metric as the minimum Fisher cost of producing a prescribed moment velocity.

That last formulation is particularly good:
\[
\boxed{
\inf_{E_Ph=0,\ E_Ph(S-M)=\dot M}E_Ph^2
=\langle\dot M,C_P^{-1}\dot M\rangle.
}
\]

**Geodesic stress test:**

- Mixture curves of laws are mixture-affine.
- Their projected moment coordinates are straight, hence m-geodesics in the family’s expectation coordinates.
- The projected laws themselves are **not generally literal mixtures** of the endpoint family laws.
- Tilt-coordinate straight lines are e-geodesics.
- These are not generally Levi–Civita geodesics of the Fisher metric.

Unless affine connections are actually defined, describe these as e-/m-affine paths rather than claiming a full formal geodesic theory.

---

# 6. Close the Legendre diagram—cheaply, with the signs fixed

Candidate **(d)** is worth doing, but is mostly completion and API consolidation.

Your candidate combines two different conventions. If
\[
\Lambda_+(q)=\log\int e^{\langle q,S\rangle}\,d\nu,
\]
then
\[
\mathcal I(M)=\sup_q[\langle q,M\rangle-\Lambda_+(q)],
\qquad
\nabla\Lambda_+(q)=m(-q),
\]
not \(-m(q)\).

For
\[
A(\theta)=\log\int e^{-\langle\theta,S\rangle}\,d\nu,
\]
the derivative is \(-m(\theta)\), but the conjugate pairing is \(-\langle\theta,M\rangle\).

On \(\mathbb V\), the cleanest implementation uses centred statistics:
\[
\Psi(q)=\log\int e^{\langle q,S-m_0\rangle}\,d\nu,\qquad
J(y)=\mathcal I(m_0+y).
\]
Then
\[
\boxed{
\Psi(q)=\sup_{y:\,J(y)<\infty}[\langle q,y\rangle-J(y)],
}
\]
with unique attainment at
\[
y=m(-q)-m_0,
\]
and
\[
\nabla\Psi(q)=m(-q)-m_0.
\]

The uniqueness is for moment points; visible coordinates remove the parameter gauge.

**Proof route:** the defining Fenchel inequality gives one direction; the tilted law and the landed KL identity give equality. No abstract Fenchel–Moreau machinery is necessary.

---

## What is genuinely adding depth?

| Item | Contribution |
|---|---|
| Exhaustive conditioned boundary atlas | **Major structural addition**: turns endpoint examples into a complete classification |
| Arbitrary-observable residual curvature | **Major response-level addition**: explains nonlinear motion of every bounded observable |
| Correct conditional/marginal residual split | **Major conceptual clarification**: precisely identifies what the atlas omits |
| Interior endpoint rates | Strong quantitative corollaries of the landed machinery |
| Fisher tangent/fibre splitting | Substantive geometric packaging; especially valuable as a variational theorem |
| Whole-domain duality | Mostly bookkeeping, but important bookkeeping |

None needs to be advertised as a new theorem of classical mathematics. The novelty may instead lie in their unified, general-law, boundary-aware, fully formal synthesis.

## What else would readers expect?

Two expectations lie beyond the six items:

1. **Differential geometry:** the relation between the cubic tensor, dual affine connections, and Levi–Civita curvature. This is more geometrically meaningful than \(C^\infty\) alone, but I would still defer it until the boundary completion and observable curvature theorem are done.

2. **Large deviations:** an operational theorem explaining why \(\mathcal I\) is called a rate—Cramér asymptotics for empirical responses, followed eventually by a Gibbs-conditioning statement for empirical laws. Bounded statistics make the moment-space LDP a natural target; law-level conditioning needs extra topology and careful hypotheses.

My recommendation is therefore:

> **Finish the atlas before polishing its smoothness:** exhaust every finite-information endpoint by recursive conditioning, then show how every observable moves through the atlas and exactly which information remains outside it.