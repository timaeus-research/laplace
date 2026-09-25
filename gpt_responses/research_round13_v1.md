## Bottom line

The export is the right **transport interface** for a general truth function. It is not, by itself, a full **asymptotic chart certificate**: the two points to keep separate are the structure of the density and the distinction between an a.e.-defined push-forward density and a specified fibre kernel.

Your proposed general-unit boundary limit is correct. The trace retains **both** the surviving coordinate and the truth variable, and the phase unit stays **inside the transverse exponential**.

I would prioritize the general-unit boundary theorem and a laplace-side bridge consuming the actual export. A certificate-only mixed example is useful documentation, but not a new mathematical stress test.

---

## Q1. Audit of `exists_truthChartsData_phase`

### (a) Wall point and non-degeneracy

The assumptions have the right shape.

* `T 0 = 0` says that the distinguished point lies on the truth wall. There is no reason to require `dT 0 ≠ 0`; singular truth walls are precisely what the resolution interface should accommodate.
* Nonvanishing of the germ of `F * T` excludes both identically-zero phase and identically-zero truth germs.
* Together with analyticity and connectedness of `W`, this prevents `F * T` from vanishing identically on an open part of `W`. Thus it also supplies the appropriate nontriviality for charts over a compact set elsewhere in that same connected region.

No requirement `F 0 = 0` is needed for the export. Such a requirement may be relevant to a particular asymptotic application, but should not be baked into the transport theorem.

Likewise, phase positivity is an **application-side** condition. A nonzero real analytic unit can be negative; the export should not promise the positivity needed for a decaying Laplace kernel unless that is separately assumed or obtained by branch selection.

### (b) The thin compact region

`L ∩ {|T| ≤ ε}` is the natural formulation. Compactness is what upgrades coverage of `L ∩ {T = 0}` to coverage of a sufficiently thin truth region.

Two qualifications:

1. This is a **localized theorem**. A theorem integrating outside `L`, or outside the thin region, still needs support assumptions or a remainder estimate.
2. If `L ∩ {T = 0}` is empty, the thin region can be empty. That is correct, not a defect.

The exact `≤ ε` boundary should be harmless for applications at sufficiently small nonzero truth values.

### (c) What is supplied, and what is not?

I would distinguish three interfaces.

#### 1. Exact transport: sufficient

For an exact localized push-forward theorem, the finite transport identity, truth monomialization, phase factorization, and measurability/continuity data are sufficient.

In particular, you do **not** need a separate Jacobian field merely to state or prove an identity of the form
\[
\int_{L'}\theta(z)\eta(T(z))\,dz
=
\int_{\mathbb R}\eta(s)K_\theta(s)\,ds.
\]
The transported density already contains the Jacobian and partition weights.

For nonnegative measurable integrands, the `lintegral` interface is especially appropriate. Signed versions require the usual integrability assumptions.

#### 2. Asymptotic chart matching: density structure matters

To match a transported term to the analytic kernels with prescribed exponents `r`, one generally needs a factorization, on each relevant branch, of the form
\[
\operatorname{dens}(u)
=
\prod_j |u_j|^{r_j}\,J(u),
\]
where the remaining factor has the boundedness and trace properties needed by the analytic theorem. Often it is cleaner to keep the nonvanishing Jacobian unit separate from the possibly vanishing partition weight.

A continuous nonnegative `dens` alone does not certify:

* its monomial vanishing order;
* the exponent vector used to calculate the candidate asymptotic order;
* positivity of a leading trace;
* eligibility for a particular `TermData` constructor.

This does **not** mean that the existing `dens` is wrong. It means that information already available in the resolution proof may be hidden by the exported record.

My recommendation is:

> Keep `TruthChartsData` lean. Add an optional refinement/certificate recording phase and density factorizations for asymptotic consumers.

The existing `_phase` theorem can remain as a lightweight export. A stronger theorem can produce the refinement when needed.

There is also a geometric adapter to check: the export uses balls and restricted chart domains, while the analytic model uses positive boxes. Orthant decomposition, box localization, and the treatment of domain indicators need to be explicit somewhere. Exact transport can absorb arbitrary measurable domain indicators; trace-based asymptotics cannot automatically ignore their boundary behavior.

#### 3. Fibrewise asymptotics: watch the a.e. issue

This is the most important semantic qualification.

The push-forward identity determines \(K_\theta\) only **almost everywhere in \(s\)**. By itself it does not determine values on a prescribed sequence \(s_n\to0\), hence cannot establish a pointwise small-\(s\) limit for an independently defined fibre kernel.

There are three clean formulations:

* use the **explicit chart-slice formula** as the chosen representative \(K_\theta\), and prove its pointwise asymptotics;
* state the result in an essential/a.e. sense;
* identify the explicit representative with another fibre kernel through an additional pointwise identity or regularity argument.

Thus `lintegral_mul_comp_truth` replaces `fibre_eq` for **integrated transport**, but not automatically for every pointwise conclusion previously using `fibre_eq`.

#### Signs and branches

The integer exponents, nonzero `S`, and phase unit determine the sign on each orthant. That is enough information in principle; an explicit positive-orthant branch API would be a convenience, not necessarily a new record field.

It should nevertheless expose:

* which truth signs a branch contributes to;
* the sign or positivity of the phase on that branch;
* the solve-coordinate factor and its Jacobian.

So: **yes for the exact general-truth push-forward theorem; conditionally yes for asymptotics, after the density/domain adapter and representative issue are addressed.**

---

## Q2. General-unit boundary regime

### The surviving coordinate and trace hypothesis

Put
\[
I=\mathrm{Fin}\,k\oplus\mathrm{Fin}\,2,\qquad
b=\operatorname{inr}(1),\qquad
J=\{i:I\mid i\ne b\}.
\]

For \(z\in(0,\rho)\) and \(y:J\to\mathbb R\), let
\[
\operatorname{insert}_b(z,y)_b=z,\qquad
\operatorname{insert}_b(z,y)_i=y_i\quad(i\ne b).
\]

The appropriate trace assumptions are, for every \(z,u\in(0,\rho)\),
\[
W(\operatorname{insert}_b(z,y),u)\longrightarrow W_{\rm tr}(z,u),
\]
\[
a(\operatorname{insert}_b(z,y),u)\longrightarrow a_{\rm tr}(z,u),
\]
as
\[
y\longrightarrow0
\quad\text{within}\quad
\prod_{i:J}(0,\rho).
\]

Require joint measurability of the two trace functions and the bounds
\[
0\le W_{\rm tr}(z,u)\le W_\star,\qquad
a_{\rm tr}(z,u)\ge a_{\min}
\]
on that product of intervals. Retain the ambient measurability and bounds from the general theorem.

This is preferable to using a filter at an ambient boundary point without explicitly fixing the surviving coordinate: the latter can accidentally impose a stronger trace hypothesis.

### Precise limit

Write
\[
M=\operatorname{transMat}(\kappa,Q),\qquad
R=\sum_i(r_i+1),\qquad K=\sum_i\kappa_i,
\]
\[
c_\rho=B\rho^K,\qquad
h_0=-\left(q\log(\rho/D)+\Bigl(\sum_iQ_i\Bigr)\log\rho\right).
\]

For \(v=(s,h)\), define
\[
b_1(v)=\operatorname{fibreB}(\kappa,Q,v,1),
\qquad
z(v)=\rho e^{-b_1(v)},
\qquad
u(v)=\operatorname{truthOf}(h).
\]

With the conventions in the question, the truth coordinate is
\[
u(v)=D\rho^{-\sum_iQ_i/q}e^{-h/q}
     =\rho e^{-(h-h_0)/q}.
\]
In particular, \(h>h_0\) is exactly the condition \(0<u(v)<\rho\).

Let
\[
H=\{v:h>h_0,\ b_1(v)>0\},
\]
so that both trace arguments belong to \((0,\rho)\). Define the ENNReal integral
\[
\mathcal I=
\int_H^{\!-}
 \operatorname{vWeight}
   \bigl(\beta,\eta,0,\,
     c_\rho a_{\rm tr}(z(v),u(v)),\,h_0\bigr)(v)
 \;\operatorname{ofReal}(W_{\rm tr}(z(v),u(v)))\,dv.
\]

Then the proposed conclusion is
\[
\boxed{
\begin{aligned}
&\frac{t^{\gamma p+\beta\delta-\eta\gamma}}{(\log t)^k}
 \operatorname{modelKernel}
   (\rho,A,B,D,\gamma,p,q,\delta,Q,\kappa,r,W,a;t)\\
&\qquad\longrightarrow
 A\,\rho^R\,|\det M|^{-1}\,
 \mathcal I.\operatorname{toReal}\,
 \bigl(\operatorname{volume}(F')\bigr).\operatorname{toReal}.
\end{aligned}}
\]

Here \(F'=\operatorname{facePolytope}(\kappa,Q,\delta,\gamma)\), as in the constant-unit degenerate theorem.

Equivalently, the real transverse integrand on \(H\) is
\[
e^{-\beta s}\,
e^{-c_\rho a_{\rm tr}(z(v),u(v))e^{-s}}\,
e^{-\eta h}\,
W_{\rm tr}(z(v),u(v)).
\]

Using the restricted set \(H\) avoids requiring meaningful trace bounds outside the trace domain. One can instead extend the traces by \(0\) and \(a_{\min}\), respectively, and use your full-space indicator formulation.

### Answers to the specific checks

**The phase unit enters exactly as you proposed.** It multiplies \(c_\rho\) inside
\[
\exp\!\left(-c_\rho a_{\rm tr}(z(v),u(v))e^{-s}\right).
\]
In general it cannot be pulled out as \(a_{\rm tr}^{-\beta}\): the surviving coordinate \(z(v)\) depends on the transverse variables, and so does the boundary restriction.

**There is exactly one factor of \(\rho\) in the surviving coordinate:**
\[
x_b=\rho e^{-(M^{-1}v)_1}.
\]
The quantity \(e^{-(M^{-1}v)_1}\) is the normalized box coordinate. If the trace is defined in physical coordinates, its argument includes \(\rho\), as above.

**The same domination is enough.** On the relevant domain,
\[
0\le
W\,e^{-c_\rho a e^{-s}}
\le
W_\star e^{-c_\rho a_{\min}e^{-s}}.
\]
Thus the constant-unit degenerate integrand at \(a_{\min}\) supplies the dominator. No upper bound on `a` is needed.

**Pointwise fixed-\((z,u)\) traces are enough here.** The degeneracy gives an exact identity
\[
x_b=z(v),
\]
independent of the large parameter and of the free face variables. Likewise \(u=u(v)\) is fixed in the transformed integral. The other coordinates collapse for a.e. relevant face point. If these two retained arguments merely converged rather than being exactly fixed, the stated trace assumptions would not automatically suffice.

**Coordinate ordering:** yes, the collapsing indices are precisely
\[
\operatorname{inl}(\mathrm{Fin}\,k)\ \sqcup\ \{\operatorname{inr}(0)\},
\]
and the survivor is `inr 1`. An `insert`/restriction API indexed by `i ≠ inr 1` will make this explicit and reduce bookkeeping errors.

As a sanity check, constant traces recover the displayed constant-unit theorem directly.

---

## Q3. What should the mixed example be?

### Option (ii): useful, but not a new test

The certificate-level lemma is worth having as a short public API/example:

> Given three certified terms and the required order comparisons, the leading measure is the sum of exactly the leading contributions.

But that tests assembly already covered by `ofTermData` and `lexMeasure`. It does not test whether the three term shapes can actually arise together with the claimed orders from one admissible chart problem.

### Option (i): only valuable if it tests the analytic adapter

A hand-built `WallChartsData 2` instance earns its construction cost if it establishes all of the following:

1. one genuine transported problem produces the three shapes;
2. the exponent and positivity conditions are satisfied;
3. the intended order equalities/inequalities actually hold;
4. the leading contributions are nonzero;
5. the chart-to-term adapter and final assembly run without extra informal identifications.

If most of the 500 lines are record plumbing and the analytic certificates are simply assumed, it buys little beyond option (ii).

### Recommendation

Do **(ii)** as inexpensive documentation, but label it an assembly example rather than an end-to-end analytic example.

Defer **(i)** unless the note explicitly claims a concrete simultaneous vertex/tied/active example. The more valuable integration test now is a small example consuming the **general-truth export itself**, especially one with nonlinear `T`, branch handling, and a nontrivial density factorization.

Option (iii) is defensible for scope closure, but a cheap certificate example is useful enough that I would retain it.

---

## Q4. Closure and ranking

I would not identify another missing weighted asymptotic regime from the list you give. The outstanding issues are chiefly the retained-coordinate unit theorem and the export-to-asymptotics interface.

### Recommended order

1. **General-unit boundary theorem.**  
   This is the substantive remaining analytic theorem. The statement above should be the target.

2. **Laplace-side general-truth bridge consuming the actual export.**  
   First state and prove the exact push-forward theorem with an explicit chosen kernel. Then identify precisely what additional phase/density/domain certificates the asymptotic theorem consumes. This will reveal whether the hironaka export needs a stronger optional refinement.

3. **Boundary mirror and chart wrapper.**  
   Derive the `j = 0` mirror by exchanging the two solved coordinates if practical; avoid duplicating the dominated-convergence proof. The wrapper is needed before the boundary theorem closes the application-facing gap.

4. **Nontriviality/positivity and localization corollaries, where not already present.**  
   A limit theorem allowing a zero coefficient is not automatically a theorem about the true leading order. Check that the note’s claims have the necessary positive-mass hypotheses, and that any passage beyond the thin compact region has its required remainder/support argument.

5. **Certificate-level mixed example.**  
   Cheap, helpful, and not a blocker.

6. **Full hand-built mixed atlas.**  
   Optional unless advertised as a concrete result.

The key closure distinction is:

> An exact general-truth transport theorem is essentially supported by the current export. A pointwise general-truth asymptotic theorem additionally needs a specified fibre-kernel representative and certified eligibility of the transported densities/domains for the analytic term theorems.

Once those interfaces and the general-unit boundary wrapper are in place, I would regard the described Euclidean program as closed without requiring a large synthetic mixed-atlas construction.