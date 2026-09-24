## 1. Audit

**Mathematically, the displayed theorem is correct for the stated `modelKernel`.** This is an audit of the formula and assumptions, rather than of the unseen Lean proofs. In particular, the powers of `ρ`, the determinant factor, and the factor `1 / η` agree with the two transverse integrations.

### (a) Nondegeneracy versus a positive point

Your condition is **strictly weaker** than existence of a point of the face with every coordinate positive.

Write the affine parametrisation of the equality plane as
\[
\alpha_{\rm free}=u,\qquad
\alpha_{{\rm solved},j}=a_j-c_j\cdot u.
\]
Then `c_j ≠ 0 ∨ a_j ≠ 0` says precisely that the \(j\)-th solved coordinate is **not identically zero on the entire equality plane**. It does not say that the plane meets the positive orthant.

Even a nonempty face is insufficient. In your example, change to \((\delta,\gamma)=(2,1)\). Then
\[
c_0=1,\quad c_1=0,\qquad a_0=0,\quad a_1=1.
\]
Both hypotheses hold, but the face is the singleton \((0,0,1)\), and its projected one-dimensional volume is zero.

A useful additional theorem is:
\[
\boxed{\quad
\text{under your two nondegeneracy hypotheses,}\quad
\operatorname{vol}(F')>0
\iff \exists\alpha\in F,\ \forall i,\ \alpha_i>0 .
\quad}
\]
The forward implication removes finitely many null coordinate-boundary hyperplanes; the reverse follows from an open neighbourhood in free coordinates. This includes \(k=0\), with the usual zero-dimensional volume convention.

Your excluded case genuinely needs the transverse restriction. The canonical indicator is \(1_{\{b_j(v)>0\}}\); replacing it by `≥ 0` changes nothing in the transverse integral because an inverse-matrix row is nonzero.

### (b) `δ ≥ 0`

**Not analytically necessary.** For \(L\ge1\),
\[
\frac{s+\delta L}{L}\le |s|+|\delta|.
\]
Replace `δ` by `|δ|` in the envelope.

With positive \(\kappa\), negative \(\delta\) makes the limiting face empty, so the extended theorem has limit zero. Thus retaining `hδ` is a reasonable application-facing restriction, but not an essential analytic hypothesis.

### (c) Signed constants and LP optimality

No assumption `w₀ ≥ 0` is needed. Likewise `A` can be signed: extract these scalars before invoking nonnegative integration. Positivity becomes necessary only when packaging the result as a **positive leading measure**.

For the LP
\[
\min_{\alpha\ge0,\ \kappa\cdot\alpha\ge\delta,\ Q\cdot\alpha\le\gamma}
(r+1)\cdot\alpha,
\]
the certificate gives
\[
(r+1)\cdot\alpha-(\beta\delta-\eta\gamma)
=\beta(\kappa\cdot\alpha-\delta)
+\eta(\gamma-Q\cdot\alpha)\ge0.
\]
Because both multipliers are positive, equality holds exactly on the simultaneous equality face.

Consequently:

* **If the face is nonempty**, it is exactly the LP-optimal set. No nondegeneracy assumption is needed for this conclusion.
* Your nondegeneracy hypotheses **do not ensure nonemptiness**.
* If the face is empty, the certificate is still a dual-feasible lower bound, but need not be optimal.

So the analytic/LP decoupling is right. Just avoid interpreting “certificate + nondegeneracy” as proving LP optimality or a nonzero leading coefficient. A zero limit also need not identify the true logarithmic order.

---

## 2. Ranking for the next rounds

I would rank the requested tasks as follows.

### 1. **(d) Close the example identification**

Small, useful regression test. Prove an equality of the nonnegative integrals first, then pass to `toReal`:
```lean
theorem modelKernel_degExample_eq_degI (t : ℝ) :
    modelKernel ... t = (degI t).toReal
```
Use whatever restrictions on `t` the definition of `degI` actually needs. The work should be coordinate permutation, product-measure identification, and the indicator/Ioo presentation—not a second asymptotic argument.

### 2. **(a) Constant units with spectators**

This is the highest-value substantive extension. Target:
\[
\frac{t^\lambda}{(\log t)^k}K(t)
\longrightarrow
C_J\prod_{i\in I}\frac1{d_i},
\qquad
d_i=r_i+1-\beta\kappa_i+\eta Q_i>0,
\]
where \(C_J\) is the current face constant for the active coordinates.

**Normalisation warning:** if the original spectator coordinates range over \((0,\rho)\), rather than already-normalised \((0,1)\), their factor is
\[
\prod_{i\in I}\frac{\rho^{d_i}}{d_i}.
\]
The powers of `ρ` must either appear here or be explicitly absorbed into the prefactor.

### 3. **(b) Face traces**

Separate two results:

1. **Exact trace model:** the units already depend only on spectators and the surviving truth coordinate.
2. **Trace replacement:** the original units converge to those traces away from the relative boundary, and the boundary contribution is negligible.

For clarity, call the physical truth coordinate \(u\), reserving \(v=(s,h)\) for transverse logarithmic coordinates. For normalised spectators, and with scale factors absorbed consistently, the target constant has shape
\[
\frac{A\,\operatorname{vol}(F')}{|\det M|}
\,\Gamma(\beta)B^{-\beta}qD^{-q\eta}
\int_{(0,1)^I}\int_0^\rho
W_0(y,u)a_0(y,u)^{-\beta}
u^{q\eta-1}\prod_i y_i^{d_i-1}\,du\,dy.
\]
This formula assumes the traces are independent of the phase-normal coordinate \(s\). If they genuinely depend on both transverse variables, retain the transverse integral instead of performing the Gamma integration.

### 4. **(f) Chart-level test-function/leading-measure theorem**

This should come before asserting a Dirac-valued `TermData`.

There is an important active-truth distinction:
\[
u_t=D\rho^{-\sum Q/q}e^{-h/q}
\]
stays of order one. **It does not generally tend to zero.**

Even with \(I=\varnothing\), the natural chart-coordinate limit is therefore supported on
\[
\{x=0,\ 0<u<\rho\},
\]
with constant-unit truth density proportional to \(u^{q\eta-1}\,du\), not automatically at \((0,0)\).

The statement to formalise is
```lean
Tendsto (fun t ↦ normalisation t * kernelWithTest φ t)
  atTop (𝓝 (∫ z, φ z ∂leadingMeasure))
```
with the leading measure obtained by pushing forward the spectator/truth density through the trace of the chart map.

Only if that trace map is constant does this reduce to
`const • dirac (rep 0)`.

### 5. **(c) `TermData.activeTruth`**

The **scalar exponent/coefficient wrapper can be done immediately** if it is cheap:
```lean
lam := γ * p + β * δ - η * γ
kk  := k
```
and substitute the phase values of `A`, `B`, `D`.

But the proposed
```lean
μ := const • dirac (rep 0)
```
needs both:

* positivity of the coefficient when `μ` is a positive measure;
* a chart-collapse hypothesis covering the surviving truth coordinate and, later, spectators.

After (f), the wrapper should be straightforward and correctly state the support.

### 6. **(e) General-truth Hironaka export**

Still last. The resolution/export layer should consume the analytic trace theorem and its actual leading measure, rather than force a Dirac interface prematurely.

**One additional short extension worth considering:** handle `c_j = a_j = 0` by retaining the corresponding transverse half-plane indicator. Much of the landed proof should survive, and it removes a genuine geometric exception.

---

## 3. Intrinsic constant

**Yes—coordinate independence is worth formalising; Hausdorff normalisation can wait.**

Let \(M_P\) and \(M_{\widetilde P}\) be the matrices for two invertible solved pairs. The transition between their free-coordinate descriptions is an affine equivalence
\[
u_{\widetilde P}=Tu_P+b
\]
satisfying
\[
|\det T|=\frac{|\det M_{\widetilde P}|}{|\det M_P|}.
\]
It maps one projected face exactly onto the other. Lebesgue change of variables then gives
\[
\frac{\operatorname{vol}(F'_P)}{|\det M_P|}
=
\frac{\operatorname{vol}(F'_{\widetilde P})}
     {|\det M_{\widetilde P}|}.
\]

That is the cleanest first formalisation: affine equivalences, determinants, and the volume API you already use. It avoids Hausdorff measure entirely.

For the intrinsic formula, let \(G\) be the linear part of the affine graph parametrisation. Linear algebra gives
\[
\sqrt{\det(G^{\mathsf T}G)}
=\frac{\sqrt{\det(RR^{\mathsf T})}}{|\det M|}.
\]
The affine area formula then yields
\[
\frac{\operatorname{vol}(F')}{|\det M|}
=
\frac{\mathcal H^k(F)}{\sqrt{\det(RR^{\mathsf T})}}.
\]

Two formalisation cautions:

* use **Euclidean** ambient geometry, e.g. `EuclideanSpace ℝ ι`, not the default sup metric on `ι → ℝ`;
* check the normalisation of the Hausdorff measure API: the displayed formula uses the normalisation agreeing with Lebesgue measure on Euclidean \(k\)-planes.

---

## 4. Spectators: freezing versus enlarged DCT

### Can constant-unit spectators be derived from the landed theorem?

**Yes, but you need a uniform bound that the limit theorem itself does not supply.**

Freeze physical spectator coordinates \(\xi_i\in(0,\rho)\). The inner kernel has
\[
B_\xi=B\prod_{i\in I}\xi_i^{\kappa_i},
\qquad
D_\xi=D\prod_{i\in I}\xi_i^{-Q_i/q},
\]
and exterior density \(\prod_i\xi_i^{r_i}\).

Apply the landed theorem pointwise in \(\xi\). Its limiting factors combine exactly as
\[
\xi_i^{r_i}
\,\xi_i^{-\beta\kappa_i}
\,\xi_i^{\eta Q_i}
=\xi_i^{d_i-1}.
\]
Thus outer DCT gives the spectator result once domination is proved.

This also works for units depending **only on the frozen spectators**. It does **not** allow the substitution
`w₀ := W₀(y, ·)` into the existing theorem: `w₀` is a scalar. Dependence on the surviving truth variable requires a trace theorem or enlarged transverse DCT.

### The needed uniform estimate

The normalisation in your last parenthesis is reversed. With
\[
\lambda=\gamma p+\beta\delta-\eta\gamma,
\]
you need, schematically,
\[
\left|
\frac{t^\lambda}{(\log t)^k}
\,\bigl[\text{spectator density}\bigr]K_y(t)
\right|
\le C\prod_i y_i^{d_i-1},
\qquad t\ge t_0.
\]
Here \(K_y\) must be defined consistently as either including or excluding the exterior density.

Under
\[
|W|\le W_*,\qquad a\ge a_*>0,
\]
and nonnegative spectator \(\kappa_i\), your **global** \(s,h\) coordinates give precisely the useful uniformity:
\[
\kappa' \cdot z'
\le s+\delta L-\sum_{i\in I}\kappa_i z_i
\le s+\delta L.
\]
The spectator shifts therefore do not worsen the fibre envelope. After extracting \(\prod y_i^{d_i-1}\), the same integrable transverse majorant works uniformly in \(y\).

If your chosen coordinates introduce logarithmic spectator losses, the weaker bound
\[
C\prod_i y_i^{d_i-1}
\left(1+\sum_i|\log y_i|\right)^k
\]
is still sufficient, since every \(d_i>0\). Likewise, polynomial \(|\log u|\) losses are integrable against \(u^{q\eta-1}du\) because \(q\eta>0\).

**Recommendation:** use outer DCT to derive the constant-unit spectator theorem, but first extract the existing proof’s domination estimate into a reusable lemma. For genuine face traces, use a single enlarged DCT in spectators and transverse variables; freezing alone does not remove the new analytic work.