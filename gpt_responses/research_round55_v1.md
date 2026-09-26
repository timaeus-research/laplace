## 1. The missing heart: finite response, with an explicit account of what reconstruction does not capture

The second-order geometry is now substantial enough that I would **stop treating another curvature theorem as the main objective**.

The missing heart is a theorem that turns this geometry into a usable answer to the original question:

> Given a change in the data law, what changes in every posterior expectation are determined by the response, how do those changes accumulate along the atlas, and what remains invisible to the response coordinates?

There are two indispensable pieces:

1. **Finite-amplitude response calculus:** Taylor expansion, remainder control, and integration along the atlas.
2. **The vertical residual:** the difference between the actual data law and its reconstructed posterior.

The second piece prevents a beautiful geometry of `Π(M)` from being mistaken for a geometry describing every aspect of `D`.

For bounded `φ`, write
\[
F_\phi(M)=E_{\Pi(M)}\phi,\qquad \Delta=M-m_0.
\]
For an interior endpoint, the theorem I would aim to display prominently is
\[
\boxed{
\begin{aligned}
E_D\phi-E_\nu\phi
={}&\operatorname{Cov}_\nu(\phi,\ell_{m_0,\Delta})\\
&+\int_0^1(1-s)\,
 E_{Q_s}\!\left[
 \phi\,N_{M_s}(\ell_{M_s,\Delta}^{\,2})
 \right]\,ds\\
&+E_D[N_M\phi],
\end{aligned}}
\tag{*}
\]
where \(M_D=M\), \(Q_s=\Pi(M_s)\), and \(M_s=m_0+s\Delta\).

The three terms are:

- the baseline linear susceptibility;
- the accumulated nonlinear response geometry;
- the feature-invisible discrepancy between data and reconstruction.

This is a particularly direct answer to “from the featureless distribution to our actual data distribution.” The atlas reaches the reconstructed endpoint; the last term says exactly what is still missing.

For boundary endpoints, establish this first on \([0,t]\), \(t<1\). Passing to \(t\uparrow1\) requires separate convergence/integrability results. Boundary blow-up does not supply those automatically.

### My ranking: depth × Lean feasibility

| Rank | Deliverable | Assessment |
|---|---|---|
| **1** | **(a) + the necessary part of (d): finite response calculus**, culminating in (*) | Highest payoff. Converts the existing differential results into predictions for finite changes. |
| **2** | **§7 packaging around horizontal response / vertical residual**, including the corrected theorem in (c) | Cheap relative to its conceptual value. This should explain the programme, not merely catalogue results. |
| **3** | **Fisher–Rao second fundamental form** | Worth landing next as planned: close to existing work, geometrically beautiful, and clarifies the normal Hessian. |
| **4** | **Dual-flat structure in algebraic form**, rather than a full connection/bundle API | Deep and feasible using potential, metric, and cubic-tensor identities. |
| **5** | A genuine ambient response-fibre connection | Important, but requires choosing and constructing an ambient space of laws. The present section-level splitting is not yet that construction. |
| **6** | Fisher–Rao great circles | Beautiful comparison geometry, but less directly about data-response reconstruction. |
| **7** | General conditional variational / unbounded extension | Valuable enlargement of scope; not the missing conceptual step in the bounded programme. |

One qualification: **the corrected version of (c) is sufficiently cheap that I would land it immediately**, independently of this ranking.

---

## 2. Top-ranked deliverable: a finite response theorem

### 2.1 Local scalar statement

Fix \(M\in\operatorname{ri}K\), let \(Q=\Pi(M)\), and let \(\phi\) be bounded and measurable. Define
\[
A_{M,\phi}(u)=\operatorname{Cov}_Q(\phi,\ell_{M,u}),
\]
and
\[
H_{M,\phi}(u,w)
=E_Q\!\left[\phi\,N_M(\ell_{M,u}\ell_{M,w})\right].
\]

Then \(A_{M,\phi}\) is a continuous linear functional and \(H_{M,\phi}\) a continuous symmetric bilinear form on \(\mathbb V\). The desired statement is
\[
\boxed{
F_\phi(M+z)
=
F_\phi(M)+A_{M,\phi}(z)
+\tfrac12 H_{M,\phi}(z,z)
+o(\|z\|^2).
}
\tag{T}
\]

This is a full Fréchet–Peano expansion, not merely a second derivative along each fixed line.

In Lean-shaped terms, the remainder
```text
z ↦ responseExpectation (M + z) φ
      - responseExpectation M φ
      - responseDerivative M φ z
      - (1 / 2) * responseHessian M φ z z
```
should be `IsLittleO` of `z ↦ ‖z‖ ^ 2` at `𝓝 0`.

The local neighbourhood must, of course, remain inside the response domain.

### 2.2 What is still needed beyond the landed Hessian?

There is one real assembly step:

> Differentiability of the derivative field applied to each fixed \(w\) must be promoted to differentiability of the operator-valued derivative field.

Let
\[
A(z):w\longmapsto
E_{\Pi(M+z)}[\phi\,\ell_{M+z,w}].
\]
You want
\[
DA(0)[u](w)=H_{M,\phi}(u,w)
\]
as a derivative into \(\mathbb V\toL\mathbb R\).

Your `hasFDerivAt_integral_responseScore` gives the fixed-\(w\) ingredients. In finite-dimensional \(\mathbb V\), assemble them on a finite basis. This is analogous to the basis assembly already used for `thirdOp`.

That step matters: pointwise directional second derivatives alone should not be advertised as a Fréchet Taylor theorem.

### 2.3 Clean Mathlib route

I would not make the project depend on a guessed name for a second-order Taylor lemma. I cannot verify the exact September 2026 checkout here.

The robust route is a small reusable **Peano-from-differentiable-derivative-field lemma**:

- \(F\) is differentiable near \(0\), with derivative field \(A\);
- \(A\) is differentiable at \(0\), with derivative \(B\);
- conclude
  \[
  F(z)-F(0)-A(0)z-\tfrac12B(z)z=o(\|z\|^2).
  \]

This needs only the little-\(o\) characterization of `HasFDerivAt` and a mean-value norm estimate.

#### Proof of the generic lemma

Differentiability of \(A\) at zero gives, for sufficiently small \(h\),
\[
\|A(h)-A(0)-B(h)\|\leq\varepsilon\|h\|.
\]

For a small fixed \(z\), put
\[
G_z(t)=F(tz)-F(0)-tA(0)z-\tfrac12t^2B(z)z.
\]
Then
\[
G_z'(t)=\bigl(A(tz)-A(0)-tB(z)\bigr)z,
\]
so, for \(0\leq t\leq1\),
\[
\|G_z'(t)\|\leq\varepsilon t\|z\|^2
\leq\varepsilon\|z\|^2.
\]
The mean-value inequality gives
\[
\|G_z(1)\|\leq\varepsilon\|z\|^2.
\]

This route avoids proving \(C^2\) regularity merely to obtain the pointwise Peano expansion. It also works for Banach-valued \(F\).

Strict differentiability of `responseTheta` is useful upstream, but **the decisive input here is differentiability of the assembled derivative field**.

### 2.4 Compact-uniform control

For uniform statements, prove continuity of
\[
M\longmapsto H_{M,\phi}
\]
in bilinear-operator norm.

Bounded features, bounded \(\phi\), continuity of \(\theta(M)\), and continuity of \(\Sigma_M^{-1}\) make this quite accessible: on a compact interior neighbourhood, the densities, scores, and projection coefficients admit common bounds.

Distinguish three statements:

- bounded Hessian gives an \(O(\|z\|^2)\) remainder after the **linear** approximation;
- continuous Hessian gives \(o(\|z\|^2)\) after the **quadratic** approximation;
- Lipschitz Hessian gives an \(O(\|z\|^3)\) quadratic remainder.

For a compact set \(C\) contained in the response domain, choose a compact interior neighbourhood containing the relevant short segments. A modulus of continuity \(\omega_C\) for the Hessian gives
\[
\left|
F_\phi(M+z)-F_\phi(M)-A_{M,\phi}(z)
-\tfrac12H_{M,\phi}(z,z)
\right|
\leq
\tfrac12\omega_C(\|z\|)\|z\|^2.
\]

You do not need to formalize another cumulant order to get this.

### 2.5 The \(L^1\)-density theorem

The corresponding statement is
\[
\boxed{
\left\|
q_{M+z}-q_M-q_M\ell_{M,z}
-\tfrac12q_MN_M(\ell_{M,z}^2)
\right\|_{L^1(\nu)}
=o(\|z\|^2).
}
\tag{D}
\]

This is stronger than proving (T) separately for every bounded observable. In particular, it gives a remainder uniform over \(\|\phi\|_\infty\leq1\).

But the pointwise density Hessian does **not** by itself prove (D). You need a Banach-valued differentiability step:

1. construct the density map into \(L^1(\nu)\);
2. construct its derivative field
   \[
   z\longmapsto\bigl[w\mapsto q_{M+z}\ell_{M+z,w}\bigr];
   \]
3. prove its derivative at zero is
   \[
   (u,w)\longmapsto q_MN_M(\ell_{M,u}\ell_{M,w});
   \]
4. apply the same generic Peano lemma.

Local domination is favourable here because \(S\) is bounded and \(\theta\) stays locally bounded. The main cost is likely the `Lp`/a.e.-equivalence interface, not new analysis.

### 2.6 From local calculus to the endpoint theorem

On the interior atlas,
\[
\frac{d}{ds}F_\phi(M_s)
=\operatorname{Cov}_{Q_s}(\phi,\ell_{M_s,\Delta}),
\]
and
\[
\frac{d^2}{ds^2}F_\phi(M_s)
=E_{Q_s}\!\left[\phi N_{M_s}(\ell_{M_s,\Delta}^2)\right].
\]

Twice integrating gives the reconstruction part of (*).

For the last term, the fibre identity is immediate:
\[
E_D[B_M\phi]=0
\qquad\text{when }E_DS=M.
\]
Consequently,
\[
E_D[N_M\phi]=E_D\phi-E_Q\phi.
\]

This final identity needs no finite-KL hypothesis: bounded observables and appropriate absolute continuity suffice for the usual a.e.-defined formulation.

### Estimated Lean cost

Assuming the stated derivative results and the existing integration API are readily usable:

| Component | Approximate lines |
|---|---:|
| Bilinear Hessian packaging and operator-valued derivative assembly | 80–160 |
| Generic second-order Peano lemma | 80–170 |
| Scalar response Taylor theorem | 40–90 |
| Hessian continuity / compact bounds | 100–200 |
| Integrated atlas theorem and vertical residual | 100–200 |
| **Scalar package total** | **400–820** |
| Additional \(L^1\)-valued package | **350–750** |

These are planning estimates; the `Lp` bridge is the main uncertainty.

---

## 3. Sanity check: “only the normal part of \(\phi\) responds at second order”

**Correct, with two qualifications.**

Because \(N_M\) is an orthogonal projection in \(L^2(Q)\),
\[
\begin{aligned}
H_{M,\phi}(u,w)
&=E_Q[\phi\,N_M(\ell_u\ell_w)]\\
&=E_Q[(N_M\phi)\,\ell_u\ell_w]\\
&=E_Q[(N_M\phi)\,N_M(\ell_u\ell_w)].
\end{aligned}
\]

Thus the clean hierarchy at a fixed base point is:

- the constant part contributes to the value;
- the tangent/regression part controls the first derivative;
- only the normal part can contribute to the response-coordinate Hessian.

In particular, affine feature observables have zero response Hessian, as they must.

### Qualification 1: this is a response-coordinate Hessian

For a nonlinear response path \(M_s\),
\[
\frac{d^2}{ds^2}F_\phi(M_s)
=
H_{M_s,\phi}(\dot M_s,\dot M_s)
+
A_{M_s,\phi}(\ddot M_s).
\]
The second term can see the tangent part of \(\phi\).

So the slogan applies to affine response perturbations—or to the Hessian itself—not to every second derivative along every parametrized curve.

### Qualification 2: normal does not mean necessarily detectable at second order

The normal space can be larger than
\[
\operatorname{span}\{N_M(\ell_u\ell_w):u,w\in\mathbb V\}.
\]
A nonzero normal observable can still have zero Hessian.

The exact statement is:

> Second-order response detects the component of the observable lying in the span of the normal quadratic score products.

That is sharper than saying it detects the entire normal component.

---

## 4. Candidate (c): the proposed extra normal term is false

For a fixed law \(D\) in the fibre over \(M\), the true Hessian is simply
\[
\boxed{
D_z^2\,\mathrm{KL}(D\|\Pi(M+z))\big|_{z=0}[u,w]
=
\langle\Sigma_M^{-1}u,w\rangle.
}
\tag{K}
\]

Assume finite KL so that this is an ordinary real-valued differentiability statement.

There are two revealing proofs.

### Proof 1: Pythagoras removes all fibre dependence

The exponential-family identity gives
\[
\mathrm{KL}(D\|\Pi(M+z))
=
\mathrm{KL}(D\|Q)
+
\mathrm{KL}(Q\|\Pi(M+z)).
\]
The entire dependence on \(D\) is an additive constant.

Therefore **every derivative in \(z\)**, not just the Hessian, is independent of the choice of \(D\) in that fibre.

Using the Bregman identity and \(D^2\mathcal I(M)=\Sigma_M^{-1}\) yields
\[
\mathrm{KL}(D\|\Pi(M+z))
=
\mathrm{KL}(D\|Q)
+\tfrac12\langle\Sigma_M^{-1}z,z\rangle
+o(\|z\|^2).
\]

### Proof 2: the apparent normal term cancels

Your density Hessian gives
\[
D^2\log q_M[u,w]
=
N_M(\ell_u\ell_w)-\ell_u\ell_w.
\]
Since
\[
N_M(\ell_u\ell_w)
=
\ell_u\ell_w
-E_Q[\ell_u\ell_w]
-B_M(\ell_u\ell_w),
\]
we obtain
\[
-D^2\log q_M[u,w]
=
E_Q[\ell_u\ell_w]+B_M(\ell_u\ell_w).
\]
Taking \(E_D\), the regression term vanishes because \(D\) has response \(M\). Differential duality supplies (K).

So the candidate
\[
G_M(u,u)+E_D[N_M(\ell_u^2)]
\]
does **not** describe this KL Hessian. The logarithm introduces a squared-score subtraction that cancels the proposed extra fibre dependence.

This is itself an important structure theorem:

> The transverse KL profile toward reconstructed responses is identical on an entire response fibre, up to an additive constant.

If you want a quantity that genuinely sees fibre-specific normal geometry, use observable discrepancies such as \(E_D[N_M\phi]\), or study a divergence with the arguments reversed under suitable positivity and integrability assumptions. The forward KL in (c) deliberately forgets everything except the sufficient statistic.

---

## 5. What to say about connections and the third cumulant

### The current splitting is not yet an ambient connection

At \(Q=\Pi(M)\), you have the Fisher-orthogonal splitting of centered scores
\[
g=B_Mg+N_Mg,
\]
and the horizontal lift of \(u\) is \(\ell_{M,u}\).

That constructs horizontal spaces **along the reconstructed section**.

At a general law \(D\), the Fisher-horizontal lift would instead use its own covariance:
\[
h_{D,u}
=
\langle\Sigma_D^{-1}u,S-M_D\rangle.
\]
Using the reconstructed covariance \(\Sigma_M\) at \(D\) generally fails the lift identity:
\[
\operatorname{Cov}_D(S,\ell_{M,u})
=
\Sigma_D\Sigma_M^{-1}u,
\]
which need not equal \(u\).

Thus an ambient fibre-bundle claim requires additional definitions and hypotheses.

In a smooth positive-law setting where these objects exist, the Fisher-horizontal distribution is locally integrable: its leaves are exponential-tilt orbits of the starting law. With response coordinates on each leaf, horizontal lifts of constant response directions commute. The corresponding Ehresmann curvature is zero.

That is not the same statement as vanishing Fisher–Rao Levi-Civita curvature.

### The most economical formal dual-flat statement

I would formalize the following before introducing abstract connections:
\[
\nabla\mathcal I(M)=-\theta(M),
\qquad
D^2\mathcal I(M)[u,w]=G_M(u,w),
\]
and, defining
\[
C_M(u,w,z)=E_Q[\ell_u\ell_w\ell_z],
\]
\[
D G_M[z](u,w)=-C_M(u,w,z).
\]

Together with the canonical-divergence identity
\[
\mathrm{KL}(\Pi(M)\|\Pi(M'))
=
\mathcal I(M)-\mathcal I(M')
+\langle\theta(M'),M-M'\rangle,
\]
these express the essential dual-flat structure without a manifold-connection development.

The sign deserves explicit documentation:

- in the natural \(\theta\)-coordinates, contracting `thirdOp` gives the cubic score tensor;
- in response coordinates, \(D_MG=-C_M\).

The cubic tensor is **not curvature**. It measures the difference between the dual affine connections.

If you want explicit connection coefficients in response coordinates, let
\[
A_M(u,w)=\operatorname{Cov}_Q(S,\ell_u\ell_w).
\]
Then, with the usual e/m conventions,
\[
\Gamma^{(m)}=0,\qquad
\Gamma^{(e)}(u,w)=-A_M(u,w),\qquad
\Gamma^{LC}(u,w)=-\tfrac12A_M(u,w).
\]
Symmetry gives torsion-freeness; the coordinate descriptions give e/m flatness. This is a good later theorem, but the Hessian-potential package is the more economical immediate target.

---

## Recommendation

Land `FisherRaoCurvature` as planned, but make the next main milestone:

**`FiniteResponse`**
1. operator-valued response Hessian;
2. scalar Peano expansion;
3. compact-uniform remainder;
4. integrated atlas response;
5. exact vertical residual;
6. corrected fibre-independent KL Hessian.

The organising equation should be (*).

That is where the programme becomes more than a beautiful geometry of reconstruction: it becomes an exact account of **what data changes do to posterior expectations, what the chosen responses determine, and what they cannot determine**.