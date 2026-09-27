## 0. Fix the signs and the reusable notation first

Write
\[
\rho=\nu.\mathrm{tilted}\,g,\qquad
\theta=\mathrm{responseOf}\,g,\qquad q=\mathrm{Pfam}\,\theta,
\]
and abbreviate
\[
L_w=\mathrm{dirLoss}\,S\,w,\qquad
A_\theta=\mathrm{CDE}\,\theta,\qquad
V_g(k)=A_\theta^{-1}(\mathrm{forcing}\,g\,k).
\]

Thus `V_g(k)` is the existing `responseVel`, with boundedness proofs suppressed.

The crucial convention is
\[
\mathrm{CD}_\theta w=-\operatorname{Cov}_{q}(S,L_w).
\]
Consequently, if \(C_q\) denotes the positive covariance operator on \(W\), then
\[
A_\theta=-C_q,\qquad V_g(k)=-C_q^{-1}\operatorname{Cov}_{\rho}(S,k).
\]

Introduce two **\(W\)-valued** cumulants:
\[
\begin{aligned}
B_g(k,\ell)_j
  &=\mathrm{thirdCentral}\,\rho\,(S\,j)\,k\,\ell,\\
T_\theta(v,w)
  &=(\mathrm{thirdOp}\,\theta\,v)\,w.
\end{aligned}
\]
The coordinate identity required for the second is
\[
T_\theta(v,w)_j
 =\mathrm{thirdCentral}\,q\,(S\,j)\,L_v\,L_w.
\]

This is consistent with `hasFDerivAt_chartDeriv`: differentiating `CD = − covariance` introduces a second minus sign, so **`thirdOp` has the positive third-cumulant sign**.

A particularly convenient construction of \(B\), avoiding a new coordinatewise membership proof, is
\[
B_g(k,\ell)
 =\mathrm{forcing}\,g\,
   \bigl((k-E_\rho k)(\ell-E_\rho\ell)\bigr).
\]
Its coordinate identity is just expansion of `lawCov`. Boundedness follows from boundedness of \(k,\ell\).

Below, declarations are Lean-flavoured specifications, not claims about the exact argument order of existing declarations. In particular, check the argument order of `thirdVec`; use `thirdOp` as the canonical operator-facing interface.

---

# Q1. Audit and adaptation of the original six modules

## B1. `ResponseCumulantCalculus`

### What should actually be added

This should be a **small bridge layer**, not a second implementation of `CovarianceFrechet`.

Define, schematically:

```lean
def dataThird (hg : Bdd g) (hk : Bdd k) (hl : Bdd ℓ) : W :=
  forcing g ((k - integral ρg k) * (ℓ - integral ρg ℓ))
```

Prove:

```lean
dataThird_apply :
  (dataThird hg hk hl : J → ℝ) j =
    thirdCentral (ν.tilted g) (S j) k ℓ

dataThird_symm :
  dataThird hg hk hl = dataThird hg hl hk
```

The substantive differentiation bridge is

```lean
hasDerivAt_forcing_add :
  HasDerivAt
    (fun t : ℝ => forcing (g + t • k) ℓ)
    (dataThird hg hk hl)
    0
```

and its version at arbitrary \(t\).

Also expose the existing family calculation in the form

```lean
thirdOp_apply_apply :
  ((thirdOp θ v) w : J → ℝ) j =
    thirdCentral (Pfam θ) (S j)
      (dirLoss S v) (dirLoss S w)
```

together with symmetry in `v w`.

### Proof route

1. Rebase the tilt:
   \[
   \nu.\mathrm{tilted}(g+t k)
     =(\nu.\mathrm{tilted}g).\mathrm{tilted}(t k).
   \]
2. Apply `hasDerivAt_lawCov_tilted` coordinatewise.
3. Assemble the finite-dimensional derivative into \(W\).
4. Obtain the model-side identities from `thirdVec_eq_respCov` and `hasFDerivAt_chartDeriv`.

### Existing dependencies

- `hasDerivAt_lawCov_tilted`
- `thirdVec_eq_respCov`
- `thirdOp`
- `hasFDerivAt_chartDeriv`
- bounded-tilt composition identities
- `forcing` and its existing \(W\)-membership infrastructure.

**Assessment:** mostly bridge work. Do not count it as a full new research module.

---

## B2. `ResponseHessian`

This is the central new theorem.

Define
\[
\boxed{
H_g(k,\ell)
 =
 A_\theta^{-1}
 \left(
 B_g(k,\ell)-T_\theta(V_g(k),V_g(\ell))
 \right).
}
\]

In covariance-operator notation, the same formula is
\[
H_g(k,\ell)
 =
 C_q^{-1}
 \left(
 T_\theta(V_g(k),V_g(\ell))-B_g(k,\ell)
 \right).
\]
That reversed order is essential: the round-90 formula used the natural-parameter sign, whereas here \(\theta\) is **minus** the natural parameter.

### Natural Lean statement

Yes: the cleanest first target is the derivative of the velocity field.

```lean
def responseHess (hg : Bdd g) (hk : Bdd k) (hl : Bdd ℓ) : W :=
  (CDE (responseOf g)).symm
    (dataThird hg hk hl -
      (thirdOp (responseOf g) (responseVel hg hk))
        (responseVel hg hl))

hasDerivAt_responseVel_add :
  HasDerivAt
    (fun t : ℝ =>
      responseVel (bdd_add_smul hg hk t) hl)
    (responseHess hg hk hl)
    0
```

Boundedness-proof arguments should preferably be hidden behind an unbundled or bundled velocity-field wrapper.

For the diagonal, pair this with

```lean
hasDerivAt_responseOf_add :
  HasDerivAt
    (fun t : ℝ => responseOf (g + t • k))
    (responseVel hg hk)
    0
```

to obtain the second derivative of the response curve.

For two parameters, it gives
\[
\partial_s\partial_t\,
\mathrm{responseOf}(g+s k+t\ell)\big|_{(0,0)}
=H_g(k,\ell).
\]

### Derivation from moment matching

Let
\[
\theta(t)=\mathrm{responseOf}(g+t k),\qquad
m(t)=E_{\nu.\mathrm{tilted}(g+t k)}S.
\]
Moment matching says
\[
\mathrm{mean}(\theta(t))=m(t).
\]

The first derivative gives
\[
A_{\theta(t)}\theta'(t)=\mathrm{forcing}(g+t k)\,k.
\]

At zero, \(\theta'(0)=V_g(k)\). Differentiating again gives
\[
T_\theta(V_g(k),V_g(k))
 +A_\theta\theta''(0)
 =B_g(k,k).
\]
Hence
\[
\theta''(0)=A_\theta^{-1}
  \bigl(B_g(k,k)-T_\theta(V_g(k),V_g(k))\bigr).
\]

For the mixed version, differentiate
\[
A_{\theta(s)}V_{g+s k}(\ell)=\mathrm{forcing}(g+s k)\,\ell.
\]
This gives precisely the displayed formula for \(H_g(k,\ell)\).

### Lean proof route

Your proposed route is the right one:

- use `hasFDerivAt_inverse_response` along the mean path
  \(m(t)-m(0)\);
- use `hasDerivAt_forcing_add`;
- use the product/application rule;
- simplify with `inverse_response_deriv_apply`;
- identify the resulting third-cumulant term with `thirdOp`.

This reuses the already-proved inverse differentiation rather than reproving an inverse-operator theorem.

### Important corollaries

```lean
responseHess_symm :
  responseHess hg hk hl = responseHess hg hl hk
```

This follows directly from symmetry of `dataThird` and `thirdOp`. It does **not** require a general Schwarz theorem.

Also prove bilinearity in \(k,\ell\). On finite-dimensional data slices this is the actual second Fréchet derivative. On `bddSpace`, calling it a continuous bilinear Fréchet Hessian requires the relevant normed-space infrastructure.

---

## B3. `ResponseMixtureAffine`

### The nontrivial coordinate statement

Let \(d=m_D-m_\nu\), and, wherever the mixture mean belongs to the open moment body, put
\[
\theta_t=\mathrm{mixResponse}\,t,\qquad
v_t=A_{\theta_t}^{-1}d.
\]
Then
\[
\boxed{
\theta_t''=-A_{\theta_t}^{-1}T_{\theta_t}(v_t,v_t).
}
\]

Equivalently,
\[
A_{\theta_t}\theta_t''
   +T_{\theta_t}(v_t,v_t)=0.
\]

This accompanies
\[
\frac{d^2}{dt^2}\mathrm{mean}(\theta_t)=0.
\]

A Lean-facing statement is

```lean
hasDerivAt_mixVelocity :
  HasDerivAt
    (fun s => (CDE (mixResponse s)).symm d)
    (-(CDE (mixResponse t)).symm
      ((thirdOp (mixResponse t) v) v))
    t
```

under the appropriate local interior hypotheses.

### Is this new?

Essentially **no**. It is the existing atlas-velocity theorem, after identifying:

- the straight mean path;
- `mixResponse` with the atlas response;
- `v` with `atlasVel`;
- the displayed cumulant correction with `atlasBend`.

The statement that the mixture-coordinate acceleration vanishes is also already built into the affine mean path.

**Recommendation:** add a short compatibility/corollary file if useful, but drop this as an independent programme-B module. Do not introduce “zero covariant Hessian” terminology into theorem names without a connection API.

---

## B4. `ResponseExponentialDefect`

Here “defect” should mean **acceleration defect**, not the scalar KL response defect.

For
\[
\rho_t=\nu.\mathrm{tilted}(t h),\quad
\theta_t=\mathrm{responseOf}(t h),\quad
v_t=V_{t h}(h),
\]
the exact statement is
\[
\boxed{
\theta_t''
 =
 A_{\theta_t}^{-1}
 \left(
 B_{t h}(h,h)-T_{\theta_t}(v_t,v_t)
 \right).
}
\]

Lean-facing:

```lean
hasDerivAt_expResponseVelocity :
  HasDerivAt
    (fun s => responseVel (bdd_smul hh s) hh)
    ((CDE θt).symm
      (dataThird (bdd_smul hh t) hh hh -
        (thirdOp θt vt) vt))
    t
```

### Connection-free interpretation

The source journey is affine in its exponential coordinate \(t h\). The target exponential coordinate is \(-\theta_t\), so its acceleration vanishes exactly when \(\theta_t''=0\).

Thus the response preserves exponential straightness to second order precisely when
\[
B_{t h}(h,h)=T_{\theta_t}(v_t,v_t).
\]

This compares:

- the data third cumulant driving the changing moment velocity;
- the model third cumulant generated by the already-matched first-order response.

No connection formalism is needed.

### Status and dependencies

This is a direct corollary of `ResponseHessian`, not an independent calculus module.

The canonical journey is the specialization \(h=\log q\), subject to the boundedness hypotheses already used by `CanonicalDataJourney`.

There is generally **no scalar sign for a \(W\)-valued acceleration**. Skewness controls specified scalar contractions, not an ordering of the acceleration vector. Do not advertise an unconditional “sign of the bend.”

---

## B5. Rename `ResponseFisherCurvature` to `ResponsePullbackVariation`

That is the right scope. These are third-cumulant variation identities, not yet Riemann-curvature theorems.

Write
\[
G_g(h,\ell)=\mathrm{pullbackBilin}_g(h,\ell)
 =\operatorname{Cov}_{q}(L_{V_g(h)},L_{V_g(\ell)}).
\]

The clean general statement is
\[
\boxed{
\begin{aligned}
D_kG_g(h,\ell)
={}&\mathrm{thirdCentral}\,q\,
       L_{V_g(k)}\,L_{V_g(h)}\,L_{V_g(\ell)}\\
 &-\mathrm{thirdCentral}\,\rho\,L_{V_g(\ell)}\,h\,k\\
 &-\mathrm{thirdCentral}\,\rho\,L_{V_g(h)}\,\ell\,k.
\end{aligned}
}
\]

In Lean, start with a `HasDerivAt` for
`fun t => pullbackBilin (g + t • k) h ℓ`.

For the diagonal journey \(g+t h\),
\[
\frac{d}{dt}G_{g+t h}(h,h)\bigg|_{t=0}
 =
 \kappa_q(L_v,L_v,L_v)-2\kappa_\rho(L_v,h,h),
 \qquad v=V_g(h).
\]

If the fitted score/regressor is \(r=-L_v\), this becomes
\[
\frac{d}{dt}G_{g+t h}(h,h)\bigg|_{0}
 =
 2\kappa_\rho(r,h,h)-\kappa_q(r,r,r).
\]

### Proof route

Differentiate
\[
G_g(h,\ell)=\operatorname{Cov}_{q}(L_{V_g(h)},L_{V_g(\ell)}).
\]

There are three terms:

1. change of the model law: a **negative** model third cumulant;
2. change of \(V_g(h)\);
3. change of \(V_g(\ell)\).

Substitute `responseHess`. The two velocity terms each contribute a positive model third cumulant, leaving the single positive model term displayed above.

Dependencies:

- `hasFDerivAt_lawCov_family`
- `ResponseHessian`
- the covariance/`CD` pairing identities
- `pullbackBilin` and `fisherVar`.

This is genuinely new in its general data-direction form.

---

## B6. `ResponseHigherDefectVariation`

The third derivative has an important factor of two. It is **not** merely the third cumulant of the residual.

For the existing initial journey
\[
\rho_t=\nu.\mathrm{tilted}(t h),
\]
the initial model is \(\mathrm{Pfam}(0)=\nu\), and the initial response is \(0\). Put
\[
v=V_0(h),\qquad r=-L_v,\qquad e=h-r=h+L_v.
\]
Constants in \(r\) or \(e\) do not matter below.

Then
\[
\boxed{
\Delta'''(0)
 =2\,\mathrm{thirdCentral}\,\nu\,e\,e\,e
  +3\,\mathrm{thirdCentral}\,\nu\,e\,e\,r.
}
\]
Equivalently,
\[
\Delta'''(0)
 =2\kappa_\nu(h,h,h)
  -3\kappa_\nu(r,h,h)
  +\kappa_\nu(r,r,r).
\]
In terms of response velocity:
\[
\Delta'''(0)
 =2\kappa_\nu(e,e,e)-3\kappa_\nu(e,e,L_v).
\]

### Recommended Lean statement

First prove the more robust derivative statement:

```lean
hasDerivAt_secondDeriv_responseDefect_zero :
  HasDerivAt
    (fun t => deriv (deriv (responseDefect h)) t)
    (2 * thirdCentral ν e e e +
     3 * thirdCentral ν e e r)
    0
```

Then derive the nested-`deriv` equality. Exact names should follow the existing defect API.

### Derivation from the every-\(t\) formula

Use
\[
\Delta''(t)
 =
 \operatorname{Var}_{\rho_t}h-G_{t h}(h,h)
 +\operatorname{Cov}_{\rho_t}
    \bigl((h-E_{\rho_t}h)^2,\;t h+L_{\theta_t}\bigr).
\]

At zero:

1. The variance derivative is \(\kappa_\nu(h,h,h)\).
2. `ResponsePullbackVariation` gives
   \[
   G'(0)=2\kappa_\nu(r,h,h)-\kappa_\nu(r,r,r).
   \]
3. The last covariance has second argument zero at \(t=0\). Therefore changes in its law and first argument contribute zero there. Only the derivative of its second argument remains:
   \[
   \operatorname{Cov}_\nu((h-E_\nu h)^2,h+L_v)
   =\kappa_\nu(h,h,e).
   \]

Adding gives the formula above.

### Required inputs

- the **every-\(t\)** `deriv_deriv_responseDefect`, not just its value at zero;
- `hasDerivAt_lawCov_tilted`, including the variance specialization;
- differentiability of the response;
- the pullback-variation theorem;
- a product-rule lemma for covariance with varying integrands;
- `responseOf 0 = 0` and `Pfam 0 = ν`;
- third-cumulant multilinearity and symmetry.

No fourth cumulant is needed, because the potentially more complicated terms vanish at the matched initial point.

The same result holds at any matched base \(\rho_g=\mathrm{Pfam}(\theta_0)\), with \(\nu\) replaced by that base law and with the corresponding relative defect. That extension should be stated separately from the existing `responseDefect`.

---

# Q2. What is actually new, and what should replace the duplicates?

## Novelty audit

| Proposed item | Status |
|---|---|
| Model-side cumulant differentiation | Already in `CovarianceFrechet` |
| Data-side cumulant differentiation | Small rebasing/assembly bridge |
| Full data-direction response Hessian | **New central theorem** |
| Mixture acceleration | Existing atlas theorem, re-expressed |
| Exponential acceleration | Specialization of the new Hessian |
| Pullback-form variation | **New general identity** |
| Initial third defect derivative | **New scalar consequence with real content** |
| Hessian symmetry | Valuable, inexpensive Hessian corollary |
| Canonical e-journey Hessian at zero | Specialization, not a standalone module |
| Second-order Taylor expansion | Valuable calculus corollary, not an independent deep module |

I would not manufacture six independent modules by giving these corollaries separate filenames. To retain six substantial modules, broaden B in the following controlled ways.

## Replacement 1: `ResponseDataSmooth`

### Unconditional finite-dimensional target

For any finite collection of bounded directions \(k_i\), prove
\[
z\longmapsto
\mathrm{responseOf}\left(g+\sum_i z_i k_i\right)
\]
is \(C^\infty\).

Schematically:

```lean
contDiff_responseOf_finiteSlice :
  ContDiff ℝ ∞
    (fun z : ι → ℝ =>
      responseOf (g + fun x => ∑ i, z i * k i x))
```

This gives a clean setting for:

- an actual symmetric second Fréchet derivative;
- mixed derivatives;
- Taylor expansions;
- two-parameter variations later.

### Proof route

- rebase at `ν.tilted g`;
- prove smoothness of the bounded-tilt moment numerator and denominator;
- use `SmoothFamily` with the added data features, or reuse its integral proof;
- compose with the smooth local inverse of `meanMap`;
- use that bounded tilts have means in the response domain.

**Important infrastructure caveat:** `velLin : bddSpace X →ₗ W` does not by itself establish that `bddSpace X` carries the appropriate normed-space topology, nor that `velLin` is continuous. A global theorem

```lean
ContDiff ℝ ∞ (responseOf : bddSpace X → W)
```

should be promised only after auditing that structure. If a sup-norm bounded-function space is available, the Banach-space version is natural; otherwise finite-dimensional slices are the correct first deliverable.

### Taylor theorem bundled here or with the Hessian

For fixed \(g,k\),
\[
\mathrm{responseOf}(g+t k)
 =
 \mathrm{responseOf}(g)+tV_g(k)
 +\frac{t^2}{2}H_g(k,k)+o(t^2).
\]

State this using an `IsLittleO` remainder, or a punctured-limit quotient. A `HasStrictFDerivAt` statement alone is not a second-order Taylor statement.

---

## Replacement 2: `ResponseSecondOrderLifts`

This is a genuinely useful second-order extension of round 85.

Let \(g(t)\) be a bounded finite-dimensional data slice with
\[
g(0)=g,\qquad g'(0)=k,\qquad g''(0)=b.
\]
Then
\[
\boxed{
(\mathrm{responseOf}\circ g)''(0)
 =V_g(b)+H_g(k,k).
}
\]

For a concrete first theorem, use the polynomial journey
\[
g(t)=g+t k+\tfrac12t^2b.
\]

Now use an existing horizontal right inverse, written abstractly as
\[
\mathcal H_g:W\to\mathrm{bddSpace}\,X,
\qquad V_g(\mathcal H_g a)=a.
\]
Verify that the existing `horLin` has precisely this orientation before choosing the wrapper.

For any desired response acceleration \(a\), choose
\[
b=\mathcal H_g\bigl(a-H_g(k,k)\bigr).
\]
Then the response has initial velocity \(V_g(k)\) and acceleration \(a\).

In particular,
\[
b=-\mathcal H_g(H_g(k,k))
\]
cancels the response acceleration.

If \(V_g(k)=0\), this constructs a data journey stationary under the response **through second order**. It does not, by itself, construct an exact curve in a response fibre; do not conflate a two-jet statement with an exact level-set theorem.

Dependencies:

- `ResponseHessian`
- finite-slice smoothness
- `velLin`, `horLin`, and their right-inverse identities.

---

## Replacement 3: `ResponseLengthSecondVariation`

This is a reasonable sixth substantial module **if six genuinely substantial modules are wanted**. It is a larger extension: it needs fourth cumulants. It should come last, not block the Hessian headline.

Let \(g(t,\varepsilon)=g(t)+\varepsilon r(t)\) on a compact interval. Define
\[
P(t,\varepsilon)
 =
 G_{g(t,\varepsilon)}
   \bigl(\partial_tg(t,\varepsilon),\partial_tg(t,\varepsilon)\bigr),
\]
and
\[
\mathcal L(\varepsilon)=\int\sqrt{P(t,\varepsilon)}\,dt.
\]

Under smoothness and a uniform positive-speed bound,
\[
\boxed{
\mathcal L''(0)
 =
 \int
 \left[
 \frac{\partial_\varepsilon^2P(t,0)}{2\sqrt{P(t,0)}}
 -
 \frac{(\partial_\varepsilon P(t,0))^2}
      {4P(t,0)^{3/2}}
 \right]dt.
}
\]

The positive-speed assumption matters: the norm is not twice differentiable at zero speed.

Put \(w=g'(t)\), \(z=r'(t)\), and let
\[
J_g(k;h,\ell)=D_kG_g(h,\ell),\qquad
K_g(m,k;h,\ell)=D_mD_kG_g(h,\ell).
\]
Then
\[
\begin{aligned}
P_\varepsilon
 &=J_g(r;w,w)+2G_g(w,z),\\
P_{\varepsilon\varepsilon}
 &=K_g(r,r;w,w)+4J_g(r;w,z)+2G_g(z,z).
\end{aligned}
\]

The required \(K\) is explicit: differentiate the third-cumulant formula for \(J\). With \(v_a=V_g(a)\), \(H_{ma}=H_g(m,a)\), and \(L\)-arguments understood,
\[
\begin{aligned}
K_g(m,k;h,\ell)
={}&-\kappa_{4,q}(L_{v_m},L_{v_k},L_{v_h},L_{v_\ell})\\
&+\kappa_{3,q}(L_{H_{mk}},L_{v_h},L_{v_\ell})\\
&+\kappa_{3,q}(L_{v_k},L_{H_{mh}},L_{v_\ell})\\
&+\kappa_{3,q}(L_{v_k},L_{v_h},L_{H_{m\ell}})\\
&-\kappa_{4,\rho}(L_{v_\ell},h,k,m)
 -\kappa_{3,\rho}(L_{H_{m\ell}},h,k)\\
&-\kappa_{4,\rho}(L_{v_h},\ell,k,m)
 -\kappa_{3,\rho}(L_{H_{mh}},\ell,k).
\end{aligned}
\]

Here \(\kappa_4\) is the fourth cumulant, not merely the fourth central moment.

This is connection-free and genuinely deeper than repackaging atlas acceleration. If that broadening is unwanted, stop at five substantive modules and treat the sixth as a packaging/Taylor file rather than claiming equal novelty.

---

# Q3. Headline theorem for the note

The single formula should be the symmetric response Hessian:

\[
\boxed{\displaystyle
D^2\Phi_g[k,\ell]
=
\bigl(\mathrm{chartDerivEquiv}(\Phi(g))\bigr)^{-1}
\!\left[
\kappa_{\nu.\mathrm{tilted}g}(S,k,\ell)
-
\kappa_{\mathrm{Pfam}(\Phi(g))}
 \bigl(S,\mathrm{dirLoss}\,S\,D\Phi_g[k],
          \mathrm{dirLoss}\,S\,D\Phi_g[\ell]\bigr)
\right].
}
\]

Here vector cumulants are interpreted as the \(W\)-valued objects above, and
\(\Phi=\mathrm{responseOf}\). In these conventions the inverse chart derivative is **minus** the inverse covariance operator.

The first-order response theorem says that moment forcing is transported through the inverse covariance operator, and that the resulting response form is exactly the Fisher form on the lifted velocity. The second-order theorem identifies what changes when that first-order transport is differentiated: the data contributes its third cumulant, while the changing model chart contributes the model third cumulant evaluated on the horizontal response velocities. Their difference is the response acceleration after applying the same inverse chart derivative. Thus the theorem extends the submersion picture from tangent vectors to two-jets: it measures the failure of exponential straightness, explains mixture-coordinate bending, controls variation of the pulled-back Fisher form, and supplies the correction needed to prescribe a second-order horizontal lift.

**Sign audit:** the signs in the Hessian, pullback variation, and third-defect formulas above are fixed by `Pfam θ = ν.tilted (−dirLoss S θ)`; none is left uncertain. Only existing declaration argument order and available bundled-space structure need repository verification.

## Ranked list of six modules to formalise next

1. **`ResponseDataSmooth`** — finite-dimensional bounded-data slices are \(C^\infty\); include the small data-cumulant bridge.
2. **`ResponseHessian`** — velocity-field derivative, explicit symmetric Hessian, Taylor expansion, and mixture/exponential/canonical corollaries.
3. **`ResponsePullbackVariation`** — general third-cumulant formula for variation of `pullbackBilin`.
4. **`ResponseHigherDefectVariation`** — the matched-base formula \(\Delta'''(0)=2\kappa(e,e,e)+3\kappa(e,e,r)\).
5. **`ResponseSecondOrderLifts`** — general journey acceleration and prescribed response two-jets using `horLin`.
6. **`ResponseLengthSecondVariation`** — fourth-cumulant pullback variation and positive-speed length second variation; explicitly the stretch module.