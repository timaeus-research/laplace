## 1. Audit

Subject to the ambient hypotheses and definitions not reproduced here, the displayed analytic statements look consistent. The main qualification is **what supported observables determine**.

### Moving-parameter theorems

The tied normalisation
\[
\frac{t^{\gamma p+\delta\lambda}}{(\log t)^k}
\]
is correct for \(k+1\) tied coordinates. For constant units, the coefficient should simplify to
\[
A_0w_0(B_0a_0)^{-\lambda}
\frac{\delta^k\Gamma(\lambda)}{k!\prod_i\kappa_i}.
\]
In particular, for a fixed positive box radius, the leading coefficient is independent of that radius. This is a useful algebraic check on `tiedConst`.

The partial-face coefficient displayed has the correct spectator weight
\[
\prod_j z_j^{r_j-\lambda\kappa_j},
\]
and the strict gaps give exactly the integrability conditions
\[
r_j-\lambda\kappa_j>-1.
\]

Other points:

- No sign assumption on \(A\) is needed for the constant-unit results if the proof uses linearity. Its absence is not suspicious.
- Eventual nonnegativity of \(A,D\) is natural in the variable-unit sandwich.
- \(B_0>0\) supplies eventual positivity of \(B(t)\).
- The cutoff hypothesis is the appropriate moving-\(D\) condition.
- The extra `hγq` in the constant-unit partial statement is a harmless restriction, even if a sharper constant-unit theorem could potentially dispense with it.

### The antitone squeeze

Yes: the hypotheses shown for `tendsto_of_antitone_param` suffice for the intended conclusion
```lean
Tendsto (fun t ↦ N t * f (B t) t) atTop (𝓝 (L B₀))
```
Only eventual antitonicity is needed. Only positive comparison parameters are needed. Continuity at \(B_0\), not continuity everywhere, is enough.

Indeed, choose fixed
\[
0<b_-<B_0<b_+.
\]
Eventually,
\[
N(t)f(b_+,t)\le N(t)f(B(t),t)\le N(t)f(b_-,t).
\]
Then move \(b_\pm\) towards \(B_0\). No continuity or measurability of \(f\) in its parameter is required.

The displayed `hanti` is particularly convenient because its eventual quantifier is **outside** the quantifiers over \(b,b'\).

### Observable class and the certificate

Your correction to the observable class was necessary. A small terminology point: the hypothesis
```lean
∀ z, φ z ≠ 0 → z ∈ L'
```
means “vanishes off `L'`.” It does **not** assert that the topological support is contained in `L'`, nor that the support is compact.

This class is sufficient for the ratio theorem as stated.

However, it introduces an important qualification for measure uniqueness:

> These tests determine the measure restricted to the open set \(L'\), not an arbitrary measure on the whole ambient space.

For example, adding a Dirac mass outside \(L'\) changes no certified integral. Thus the certificate structure shown cannot, on its own, imply equality of the whole normalised leading measures.

For `normalise_eq_of_forall_tendsto`, check that its full signature includes either:

1. hypotheses that both leading measures are carried by \(L'\); or
2. a conclusion about their restrictions to \(L'\).

Also distinguish:
\[
\frac{\mu}{\int\chi\,d\mu}
\qquad\text{from}\qquad
\frac{\mu}{\mu(\mathrm{univ})}.
\]
The ratio limits directly determine the first. Under the appropriate support and nonzero-mass hypotheses, they determine the probability normalisation as well.

### The tied Dirac measure

The tied point mass
\[
c\,\delta_{\operatorname{rep}(0)}
\]
is the right conclusion: all tied coordinates localise at zero, and the eliminated coordinate tends to zero under the cutoff hypothesis.

Two checks matter:

- The chart hypotheses must establish \(c\ge0\), so `ENNReal.ofReal c` does not silently truncate a signed coefficient.
- If `rep 0 ∉ L'`, every permitted continuous observable vanishes there. The certificate then sees none of that mass. This is another reason to formulate uniqueness with support hypotheses or restrictions.

### “Classify every term ⇒ certificate ⇒ ratio limit”

This is correct with your explicit denominator condition. It does **not** additionally prove:

- that the computed leading coefficient measure is nonzero;
- that the selected formal leading order is the first *nonvanishing* order;
- or that the certificate represents all globally bounded continuous observables.

For instance, zero terms can carry artificially early powers. The constructor can still produce a valid certificate, but its leading measure may be zero. Your `hpos` excludes precisely the resulting obstruction to the ratio conclusion.

So the honest headline is:

> Classifying every term constructs a certificate; any supported denominator with nonzero leading integral gives the corresponding ratio limit.

### Weighted mixed truth

The weighted theorem is correct. Eventually the moving domain lies in \((0,b)\), and both arguments of \(f\) lie in \([0,b]\). Consequently,
\[
|x^{h-1}f(x,\sigma/(tx))|\le Cx^{h-1},
\]
with an integrable dominator exactly when \(h>0\).

No positivity assumption on \(f\) is needed. The exclusion of \(h=0\) is substantive, not technical.

---

## 2. One exact genuinely positive-dimensional example

I recommend the following example. It has **positive truth and loss exponents in every coordinate**, two independent active constraints, and a one-dimensional optimal face.

### Exact theorem

For \(t>0\), define
\[
I(t)=
\int_{(0,1)^3}
\mathbf 1_{\{xyz>t^{-2}\}}\,
z^2\,e^{-t^3xyz^2}\,dx\,dy\,dz.
\]

Then
\[
\boxed{\displaystyle
\lim_{t\to\infty}\frac{t^4}{\log t}\,I(t)=1.}
\]

This is already a complete, concrete target for formalisation.

In your model-kernel conventions, take
\[
\begin{aligned}
&\rho=A=B=D=q=1,\qquad \gamma=2,\qquad p=0,\qquad \delta=3,\\
&Q=(1,1,1),\qquad \kappa=(1,1,2),\qquad r=(0,0,2),\\
&W\equiv1,\qquad a\equiv1.
\end{aligned}
\]
The truth-domain condition is
\[
t^{-2}(xyz)^{-1}<1,
\]
exactly as required.

### Optimal face

Write
\[
x=t^{-\alpha},\quad y=t^{-\beta},\quad z=t^{-\zeta}.
\]
The asymptotic linear programme is
\[
\text{minimise }\alpha+\beta+3\zeta
\]
subject to
\[
\alpha,\beta,\zeta\ge0,\qquad
\alpha+\beta+\zeta\le2,\qquad
\alpha+\beta+2\zeta\ge3.
\]

The truth and loss normals are independent. Moreover,
\[
\alpha+\beta+3\zeta
=
2(\alpha+\beta+2\zeta)-(\alpha+\beta+\zeta)
\ge 6-2=4.
\]
Equality holds precisely on
\[
\boxed{\zeta=1,\qquad \alpha+\beta=1,\qquad \alpha,\beta\ge0.}
\]

Thus:

- both truth and loss constraints are active;
- the optimal value is \(\lambda=4\);
- the optimal face is a segment, of dimension \(1\);
- the logarithmic exponent is \(k=1\).

The strict truth-domain inequality causes no issue: the LP uses its closure, and the boundary has zero volume.

### Exact reduction and constant

First collapse the product \(s=xy\):
\[
\int_0^1\int_0^1 F(xy)\,dx\,dy
=
\int_0^1(-\log s)F(s)\,ds.
\]
Hence
\[
I(t)=
\int_0^1\int_0^1
(-\log s)\,z^2\,
\mathbf 1_{\{sz>t^{-2}\}}
e^{-t^3sz^2}\,dz\,ds.
\]

Now put
\[
u=ts,\qquad v=tz.
\]
For \(t>1\),
\[
\frac{t^4}{\log t}I(t)
=
\int_{(0,t)^2}
\mathbf 1_{\{uv>1\}}
\left(1-\frac{\log u}{\log t}\right)
v^2e^{-uv^2}\,du\,dv.
\]

The limiting integral is
\[
\begin{aligned}
\int_0^\infty\int_{1/v}^{\infty}
v^2e^{-uv^2}\,du\,dv
&=\int_0^\infty e^{-v}\,dv\\
&=1.
\end{aligned}
\]

For dominated convergence, it suffices to establish
\[
\int_{\substack{u,v>0\\uv>1}}
(1+|\log u|)\,v^2e^{-uv^2}\,du\,dv<\infty.
\]
This is elementary. Substituting \(w=uv^2\) changes the domain to \(w>v\), and the logarithm becomes
\[
|\log w-2\log v|.
\]
The resulting logarithmic moments are integrable against \(e^{-w}\) on \(0<v<w\).

### Which existing theorem does it use?

The correct existing analytic component is the **two-scaled integrability result**, after collapsing \(xy\).

The reduced two-coordinate data are
\[
Q'=(1,1),\qquad \kappa'=(1,2),\qquad r'=(0,2),
\]
with nonzero determinant. The required inner density is exactly
\[
\mathbf 1_{\{uv>1\}}v^2e^{-uv^2}.
\]

I would therefore reuse `integrable_tiedDom_twoScaled`, if its general signature covers these data, and add the logarithmic-moment lemma. I cannot confirm a literal Lean instantiation without that theorem’s signature.

This is **not** a direct application of the existing \(Q=0\) tied or partial kernel theorem: the truth truncation remains active. The new ingredient is the exact product-fibre factor \(-\log s\), not a new two-scaled asymptotic analysis.

### Is this already in `TwoScaledInner` / `TiedTruthCertificate`?

There are two separate assertions:

- In **two logarithmic coordinates**, two independent active equalities with \(\Delta\ne0\) isolate a point. That face has dimension zero and contributes no face-dimensional logarithm.
- In **three logarithmic coordinates**, the same rank-two active system can leave a segment. This example does exactly that.

Thus the two-scaled certificate supplies the inner analytic mechanism, but does not by itself supply the extra logarithm unless it already includes a product-fibre/log-weight construction.

Strictly speaking, the optimal face’s affine hull here is one-dimensional. What needs at least three dimensions is the **ambient logarithmic coordinate space** supporting two independent active constraints and a positive-dimensional intersection.

---

## 3. Uniformity

For the note, the moving-parameter form is already a strong and honest statement. I would state that theorem prominently and describe compact-uniform convergence as a consequence only where its hypotheses have actually been discharged.

The relevant consequence is:

> If the moving-parameter limit holds for every path approaching every point of a parameter region, and the limiting coefficient is continuous, then convergence is uniform on compact subsets of that region.

Qualifications:

- The normalisation must be fixed on the region, or otherwise specified consistently.
- Compact sets must avoid \(\sigma=0\) and other changes of asymptotic regime.
- For ratios, the limiting denominator must be nonzero throughout the compact set; continuity then gives a uniform positive lower bound.
- The abstract assembly theorem does not itself discharge the moving asymptotics of every term. Your missing variable-unit partial case remains relevant.

The clean formal target is often
```lean
∀ ε > 0, ∀ᶠ t in atTop, ∀ σ ∈ C, |error t σ| < ε
```
rather than a real-valued supremum, which adds boundedness and empty-set bookkeeping.

A cheaper proof is possible if you first prove **neighbourhood-uniform estimates** and use a finite compact subcover. But deriving those estimates from the existing pathwise theorem naturally uses the same diagonal/sequential argument. I would not expect global monotonicity in \(\sigma\): prefactors, scale parameters, domain cutoffs, and variable units can move in competing directions.

---

## 4. Variable-unit partial faces with moving parameters

I would try a short stability lemma before duplicating 436 lines.

The key distinction is:

> The kernel is antitone in \(B\) with \(D,W,a\) fixed. It need not be antitone when changing the parameter also changes the unit evaluations.

For \(Q=0\), the eliminated variable
\[
v_t=D(t)t^{-\gamma/q}
\]
is independent of the integration coordinates. If the units are continuous on a suitable closed box and the loss unit is bounded below, compactness gives uniform estimates such as
\[
|W(x,v_t)-W(x,0)|\le\varepsilon,
\]
and
\[
(1-\varepsilon)a(x,0)
\le a(x,v_t)
\le(1+\varepsilon)a(x,0).
\]

You can then compare with **frozen-\(v\), still variable-\(x\)** kernels having:

- weights \((W(x,0)-\varepsilon)_+\) and \(W(x,0)+\varepsilon\);
- slightly smaller and larger fixed scales;
- the original frozen loss unit \(a(x,0)\).

Apply the existing fixed partial-face theorem to those kernels, then let \(\varepsilon\downarrow0\). Treat \(A(t)\) by linearity.

Two cautions:

1. Freezing the spectator dependence to a single constant generally loses the correct partial-face measure. The comparison should retain \(W(0,z,0)\) and \(a(0,z,0)\).
2. If the existing hypotheses give only pointwise face continuity rather than uniform control on a compact box, this short proof needs an additional localisation/dominated-convergence step.

So my recommendation is:

- **First try a frozen-unit perturbation squeeze.**
- Use the substitution-generated proof if the actual hypotheses make that abstraction harder than the original argument.

The \(B\)-monotonicity is useful, but does not alone solve the moving-\(D\) issue.

---

## 5. Ranking

### Immediate correctness check

**Audit the support assumptions of measure uniqueness.** This is the only potentially substantive overclaim visible in the material supplied.

### Recommended development order

1. **Package “what expectation values know.”**  
   State that leading ratios determine the \(\chi\)-normalised leading measure on the observable region, and globally when it is carried there. This is now a central conclusion, not merely assembly infrastructure.

2. **Formalise the explicit three-coordinate example above.**  
   It demonstrates genuinely positive-dimensional optimal-face behaviour with independent active truth and loss constraints. The remaining proof is concrete and small compared with a general face theorem.

3. **General-truth hironaka export.**  
   High value if the note advertises arbitrary analytic truths. Promote this to second place if that generality is part of the headline theorem.

4. **Variable-unit partial moving stability.**  
   Try the perturbation squeeze first. This closes a real gap in the scope of the parameter-stability story.

5. **Compact-uniform packaging.**  
   Useful polish, but lower mathematical priority. Prefer a uniform-on-set formulation over explicit suprema.

The overall position is now strong: **the certificate closes the fixed-parameter assembly; the remaining conceptual example is an active-truth, active-loss optimal segment; and expectation values identify a projective leading measure on precisely the region tested by the observables.**