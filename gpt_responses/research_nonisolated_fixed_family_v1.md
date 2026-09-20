## Bottom line

**Yes, for a cutoff supported in a common analytic neighborhood of the relevant zero sets, the fixed cutoff–monomial family is sufficient, including for non-isolated zeros.** A general proof uses the all-orders, distribution-valued Laplace expansion supplied by resolution of singularities.

There are two important qualifications and one useful simplification:

1. **Analyticity merely at \(p\) is not the same hypothesis as analyticity near all zeros meeting \(\operatorname{supp}\chi\).** The expansion proof needs the latter. One can arrange this by choosing \(\chi\) sufficiently small initially; one cannot silently shrink an already fixed cutoff while retaining its monomial hypotheses.
2. **No uniformity in monomial degree is needed once coefficient distributions exist.** Moments determine each coefficient distribution separately.
3. **For two genuinely cylindrical losses, the result for all smooth tests has an elementary proof using transverse concentration alone.** Integrate out the tangential variables first. There is no tangential approximation problem in this case.

I assume throughout that \(\chi\geq0\), is compactly supported, and equals \(1\) on the target ball.

---

## 1. Checking your analysis

### The failure of the point-centered Taylor argument is real

For \(L(x,y)=x^2\), powers of the full distance to \(p\) do not acquire arbitrarily strong decay. Tangential mass remains spread out. Thus Q1's particular Taylor-majorant argument does not extend unchanged.

Likewise, polynomial density alone does not upgrade per-polynomial superpolynomial decay to per-smooth-test superpolynomial decay.

An abstract illustration is instructive. On \([-1,1]\), let \(P_n\) be the Legendre polynomials and set
\[
d\mu_1=dy,\qquad
d\mu_2(t)=\bigl(1+\tfrac12P_{n(t)}(y)\bigr)\,dy,
\qquad n(t)=\lfloor\log t\rfloor.
\]
Every fixed polynomial eventually has exactly the same integral against these two positive measures. But the smooth function
\[
f(y)=\sum_{n\geq1}e^{-\sqrt n}P_n(y)
\]
has discrepancy of size
\[
\frac{e^{-\sqrt{n(t)}}}{2n(t)+1},
\]
which is not superpolynomial in \(t\). The series is \(C^\infty\), since the derivatives of \(P_n\) have polynomial growth in \(n\).

**This is not a counterexample involving two fixed losses.** It shows why compact support, positivity, and moment data by themselves do not close your argument.

### Your coefficient-distribution route is correct

The essential additional structure is not merely concentration near \(W_0\), but an asymptotic expansion in a locally finite scale with **compactly supported distribution coefficients**.

One terminological adjustment: such coefficients need not be tangential measures. Higher coefficients typically include **normal derivatives of delta distributions supported on \(W_0\)**. Compact support, rather than their being measures, is what makes moment determination work.

---

## 2. A clean abstract sufficiency theorem

The arbitrary scalar \(C(t)\) can be eliminated without constructing an asymptotic expansion for it.

Put
\[
\mu_j(t)(f)=\int \chi f\,e^{-tL_j},\qquad
Z_j(t)=\mu_j(t)(1),
\]
and define
\[
D(t)=Z_1(t)\mu_2(t)-Z_2(t)\mu_1(t).
\]

Suppose:

1. the \(\mu_j(t)\) have common compact support;
2. \(Z_1(t)\geq c\,t^{-d}\) eventually;
3. each \(\mu_j\) has an all-orders distribution-valued expansion
   \[
   \mu_j(t)\sim
   \sum_{(\alpha,k)\in E_j}
   t^{-\alpha}(\log t)^kT_{j,\alpha,k},
   \]
   with locally finite exponent sets, finitely many log powers at each exponent, and compactly supported distribution coefficients;
4. for every polynomial \(P\),
   \[
   \mu_2(t)(P)-C(t)\mu_1(t)(P)
   \quad\text{is superpolynomially small}.
   \]

Then the same conclusion holds for every smooth \(f\), hence for every target \(\phi\) supported where \(\chi=1\).

### Proof

Write
\[
E_P(t)=\mu_2(t)(P)-C(t)\mu_1(t)(P).
\]
Then
\[
D(t)(P)=Z_1(t)E_P(t)-E_1(t)\mu_1(t)(P).
\]
Both multiplying factors are bounded, so \(D(t)(P)\) is superpolynomially small.

Products of the two expansions give an expansion for \(D\). Uniqueness of scalar power–log expansions implies that every coefficient distribution \(S\) of \(D\) satisfies
\[
S(P)=0
\qquad\text{for every polynomial }P.
\]
A compactly supported distribution with all moments zero is zero. For example, its Fourier–Laplace transform is entire, and all derivatives at the origin vanish.

Thus every coefficient of \(D\) vanishes. The all-orders remainder theorem yields
\[
D(t)(f)=O(t^{-N})
\quad\text{for every }f,N.
\]
Finally,
\[
\mu_2(t)(f)-C(t)\mu_1(t)(f)
=
\frac{D(t)(f)+E_1(t)\mu_1(t)(f)}{Z_1(t)}.
\]
The polynomial lower bound on \(Z_1\) preserves superpolynomial decay.

**At no point is a degree-uniform estimate on the original monomial errors used.**

### The required remainder statement

It is enough to have, for each requested order \(A\), a finite truncation with
\[
\left|
\mu_j(t)(f)-\sum_{\text{retained terms}}
t^{-\alpha}(\log t)^kT_{j,\alpha,k}(f)
\right|
\leq C_A t^{-A}\|f\|_{C^{q_A}(K)}.
\]

One does not need a single fixed truncation whose remainder is beyond all orders. One needs arbitrarily accurate finite truncations.

The lower bound on \(Z_1\) is elementary here: smooth nonnegativity and \(L_1(p)=0\) give \(L_1(x)\leq A\|x-p\|^2\) locally, hence
\[
Z_1(t)\gtrsim t^{-n/2}.
\]

---

## 3. Where the forward expansion is available

### General analytic losses: yes, by resolution

For nonnegative real-analytic \(L_j\) near all zeros meeting the compact cutoff support, resolution gives the required expansion:
\[
\int\chi f\,e^{-tL_j}
\sim
\sum_{\alpha\in\mathbb Q_{\geq0}}\sum_k
t^{-\alpha}(\log t)^kT_{j,\alpha,k}(f).
\]

The relevant exponent set is locally finite. The coefficients are distributions supported on
\[
\operatorname{supp}\chi\cap L_j^{-1}(0).
\]
Smooth amplitudes and smooth cutoffs are allowed. Regions separated from the zero set contribute exponentially small terms.

Consequently:

> **Analytic cutoff–monomial sufficiency.**  
> If both losses are nonnegative and analytic near the zeros meeting \(\operatorname{supp}\chi\), per-monomial superpolynomial projective agreement implies superpolynomial agreement for all tests supported where \(\chi=1\).

Your existing localized singular theorem then gives germ equality at \(p\).

This is a standard consequence of the resolution-based forward theory, not a new identifiability conjecture. But **the greybook’s unconditional \(\Theta\)-estimate alone is insufficient**: it supplies neither the higher coefficient distributions nor their all-orders remainders.

### Only analytic at \(p\), with a larger arbitrary cutoff

The preceding proof does **not** establish that more literal statement. If the cutoff reaches other zeros where the losses are only smooth, those regions are not covered by the analytic expansion theorem.

I would therefore state the formal theorem with an explicit support-level analytic hypothesis, or choose the fixed cutoff inside a common analytic neighborhood from the outset. I am not asserting a counterexample to the weaker hypothesis.

### Morse–Bott: yes, without resolution

Suppose both losses are smooth Morse–Bott near all zeros meeting the cutoff support, with normal ranks \(r_j\). Parameter-dependent Morse coordinates and Gaussian integration give
\[
\mu_j(t)(f)
=
t^{-r_j/2}
\sum_{k=0}^{M-1}t^{-k}T_{j,k}(f)
+
R_{j,M}(t,f),
\]
with a retained-line estimate of the form
\[
|R_{j,M}(t,f)|
\leq
A_M t^{-r_j/2-M}\|f\|_{C^{q_M}(K)}
+
A_Me^{-ct}\|f\|_\infty.
\]
The leading coefficient is
\[
T_{j,0}(f)
=
(2\pi)^{r_j/2}
\int_{W_j}
\frac{\chi f}{\sqrt{\det H_{j,\mathrm{normal}}}}
\,d\mathrm{vol}_{W_j}.
\]
Higher coefficients involve finitely many normal derivatives of the amplitude.

The abstract theorem applies. Multiple components of different normal ranks can be handled by a finite sum of such expansions.

**The needed uniformity is uniformity of the Gaussian remainder over compact tangential parameter sets—not uniformity in polynomial degree.** Moment determination comes afterward, coefficient by coefficient.

---

## 4. Cylindrical losses: a stronger elementary result

This case is substantially easier than your analysis suggests, provided **both** losses share the cylindrical structure.

Write \(w=(x,y)\), with \(x\in\mathbb R^k\), and suppose throughout the relevant support
\[
L_j(x,y)=K_j(x).
\]
Assume
\[
c\|x\|^\nu\leq K_1(x)
\]
on the transverse projection of \(\operatorname{supp}\chi\), and \(K_1(0)=K_2(0)=0\).

Then the cutoff–monomial hypotheses imply superpolynomial agreement for **all** target smooth tests. No forward singular expansion is needed.

### Product cutoff: immediate reduction

If
\[
\chi(x,y)=\chi_x(x)\chi_y(y),
\qquad \int\chi_y>0,
\]
the hypotheses with tangential degree zero give
\[
\int\chi_x x^\alpha e^{-tK_2}
-
C(t)\int\chi_x x^\alpha e^{-tK_1}
\in\mathrm{SuperPoly}.
\]
Apply Q1 in the \(x\)-variables.

For an arbitrary target test \(\phi\), set
\[
F_\phi(x)=\int\phi(x,y)\,dy.
\]
Then
\[
\int\phi(x,y)e^{-tK_j(x)}\,dx\,dy
=
\int F_\phi(x)e^{-tK_j(x)}\,dx.
\]
The transverse theorem handles \(F_\phi\). **No approximation in \(y\) occurs.**

### Nonproduct cutoff: use a positive marginal weight

Set
\[
a(x)=\int\chi(x,y)\,dy.
\]
The tangential-degree-zero hypotheses become the weighted transverse moment hypotheses
\[
\int a(x)x^\alpha e^{-tK_2(x)}\,dx
-
C(t)\int a(x)x^\alpha e^{-tK_1(x)}\,dx
\in\mathrm{SuperPoly}.
\]

Your Q1 proof generalizes from a plateau cutoff to a smooth compactly supported weight \(a\geq0\) with \(a(0)>0\). It proves agreement on every amplitude \(af\) with \(f\) smooth.

For a target \(\phi\) supported where \(\chi=1\), its marginal \(F_\phi\) has compact support inside \(\{a>0\}\). Thus
\[
F_\phi=af
\]
for a suitable smooth compactly supported \(f\), obtained by dividing by \(a\) near \(\operatorname{supp}F_\phi\).

This yields the full conclusion.

**Analyticity is unnecessary for this family-to-all-tests transfer.** It is needed only if you then invoke analytic rigidity to conclude germ equality.

### Crucial limitation

If only \(L_1\) is cylindrical and \(L_2\) has arbitrary tangential dependence, this marginal reduction does not work: the two integrals do not share the same \(F_\phi\)-reduction.

There is still an elementary restricted-test theorem, described next.

---

## 5. What transverse concentration alone proves

Suppose only
\[
c\|x\|^\nu\leq L_1(x,y)
\quad\text{on }\operatorname{supp}\chi.
\]
The full cutoff–monomial family then controls tests
\[
\chi(x,y)\sum_{\ell=1}^m f_\ell(x)P_\ell(y),
\]
where the \(f_\ell\) are smooth and the \(P_\ell\) polynomial. No cylindrical assumption on \(L_2\) is needed.

Taylor expansion in \(x\), uniformly for \(y\) in the compact support, gives a polynomial approximant with remainder bounded by
\[
B_N\|x\|^{2N}.
\]
Use the polynomial majorant
\[
M_N(x)=\sum_{i=1}^k x_i^{2N}.
\]
The key retained estimates are
\[
\int\chi M_N e^{-tL_1}
\leq A_Nt^{-2N/\nu},
\]
and, from the monomial data,
\[
\int\chi M_N e^{-tL_2}
\leq |C(t)|A_Nt^{-2N/\nu}+\mathrm{SuperPoly}.
\]
Together with \(|C(t)|\leq At^D\), this gives
\[
|\operatorname{projDiff}(\chi f)(t)|
\leq
\mathrm{SuperPoly}+B'_Nt^{D-2N/\nu}.
\]
Choosing \(N\) proves every desired order.

The cutoff matters: the natural restricted class is **\(\chi\) times transverse-smooth/tangential-polynomial functions**. An uncut nonzero polynomial in tangential variables is not compactly supported.

There is also an elementary full-test theorem for the enlarged fixed family
\[
\{\chi(x,y)x^\alpha\psi(y):\alpha,\ \psi\in C^\infty\}.
\]
Transverse Taylor coefficients of a general test belong to this family. Again, only finitely many hypotheses are used at each requested order.

---

## 6. One-point anchoring: useful, but not a substitute

As you state it, `prop:one-point` requires:

1. equality of the relevant full normalized asymptotic data \(\Phi_{L_1}=\Phi_{L_2}\); and
2. ratio-based recovery at one point.

It does not, by itself, turn monomial agreement into equality of \(\Phi\).

Likewise, transverse coercivity is not point-isolated coercivity in the ambient space. Flat tangential directions do not automatically satisfy an isolated-point recovery hypothesis.

A valid application is:

- establish a transverse recovery theorem using a **common cylindrical structure**;
- verify the precise full-\(\Phi\) hypothesis required by anchoring;
- use anchoring to propagate the resulting local conclusion.

Without those steps, this would be circular. If common cylindricity holds only locally, one also needs a justified localization of the available data.

---

## 7. Ranked formalisation plan

Here is the order I would recommend.

| Rank | Lemma / theorem | Main estimate or input | Status |
|---|---|---|---|
| **1** | **Positive-weight version of Q1** | Replace plateau cutoff by \(a\geq0,\ a(0)>0\); retain \(t^{D-2N/\nu}\) remainder | Direct extension of existing proof |
| **2** | **Common-cylinder sufficiency, product cutoff** | Fubini and existing transverse Q1 | Easiest genuinely new full-test result |
| **3** | **Common-cylinder sufficiency, arbitrary cutoff** | Smooth marginal \(a(x)=\int\chi(x,y)\,dy\), division on \(\{a>0\}\) | Formalisation, not research |
| **4** | **Transverse concentration for restricted tests** | Taylor in \(x\), polynomial coefficients in \(y\) | Direct reuse of majorant engine |
| **5** | **Projective cross-multiplication reduction** | \(D(P)=Z_1E_P-E_1\mu_1(P)\), then divide by \(Z_1\gtrsim t^{-d}\) | Small, broadly reusable |
| **6** | **Compactly supported distributions are moment-determinate** | Fourier–Laplace analyticity, or polynomial approximation in finite \(C^q\) norms | Standard mathematics; infrastructure-dependent |
| **7** | **Abstract expansion ⇒ monomial sufficiency** | Scalar expansion uniqueness plus rank 6 | No new analysis once expansion interface exists |
| **8** | **Parameter-uniform Gaussian/Morse–Bott expansion** | \(C^q\)-seminorm remainder \(O(t^{-r/2-M})\) | Substantial formalisation, not research |
| **9** | **General analytic distribution-valued expansion** | Resolution/monomialisation with smooth-amplitude remainder control | Major new infrastructure |

### Suggested Lean-flavoured interfaces

Schematically:

```lean
-- Weighted Q1
cutoff_moments_force_weighted_tests
  (ha_nonneg : ∀ x, 0 ≤ a x)
  (ha_zero : 0 < a 0)
  (hcoercive : ... on tsupport a ...)
  (hmom : ∀ α, SuperPoly (... a * monomial α ...)) :
  ∀ f, ContDiff ℝ ∞ f → SuperPoly (... a * f ...)
```

```lean
-- Both losses have the same tangentially flat splitting
cutoff_monomials_force_all_tests_of_common_cylinder
  (hcyl₁ : L₁ (x, y) = K₁ x)
  (hcyl₂ : L₂ (x, y) = K₂ x)
  (hcoercive : ...)
  (hmom : ...) :
  ∀ φ, IsLocalTest φ → SuperPoly (projDiff L₁ L₂ C φ)
```

```lean
-- Expansion infrastructure kept separate from Laplace geometry
fixed_moments_force_all_tests_of_distributional_expansions
  (hexp₁ : HasDistributionalExpansion μ₁ E₁)
  (hexp₂ : HasDistributionalExpansion μ₂ E₂)
  (hlower : Eventually (fun t => c * t ^ (-d) ≤ Z₁ t))
  (hmom : ∀ α, SuperPoly (...)) :
  ∀ f, IsSmoothTest f → SuperPoly (...)
```

For ranks 6–7, a full general distribution library is not logically essential. One can initially represent a coefficient as a linear functional with an explicit compact-support/finite-seminorm bound:
\[
|T(f)|\leq A\max_{|\beta|\leq q}\|\partial^\beta f\|_{L^\infty(K)}.
\]
Moment determination then follows from polynomial approximation in \(C^q\) on a box containing \(K\). Unlike your original density argument, this is legitimate: it is applied to **one fixed coefficient functional**, not to a \(t\)-dependent error requiring a rate.

## Recommendation

**Formalise the common-cylinder theorem first**, starting with a product cutoff and then abstracting Q1 to a positive marginal weight. It proves full smooth-test sufficiency with the tools you already have and removes the apparent tangential-uniformity obstruction entirely.

Next, separate the abstract coefficient-distribution argument from the forward asymptotic machinery. For Morse–Bott, the outstanding work is parameter-uniform Gaussian bookkeeping. For general analytic non-isolated zeros, the outstanding work is the resolution-based forward theorem—not a remaining ambiguity about whether moments determine its coefficients.