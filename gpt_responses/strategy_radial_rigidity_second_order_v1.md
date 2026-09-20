## Recommendation

Use **(b), but only in a sparse, second-order form**—not a general formal-power-series engine. Generalize (a) by subtracting *all the linear Taylor terms through the required order*. There is still only one quadratic contribution: \(Q_k^2/2\).

This handles the intermediate orders without constructing another loss package and without expanding arbitrary products of Taylor coefficients.

Write
\[
\rho=k-2,\qquad
S_h(x)=\sum_{m=\rho}^{2\rho-1}h^m B_m(x),
\quad B_m=Q_{m+2},\quad Q=B_\rho,\quad R=Q_{2k-2}.
\]
The two pointwise inputs are simply
\[
\frac{V_h}{h^\rho}\longrightarrow Q,
\qquad
\frac{V_h-S_h}{h^{2\rho}}\longrightarrow R.
\]
Then
\[
\frac{e^{-V_h}-1+S_h}{h^{2\rho}}
\longrightarrow \frac12Q^2-R.
\]

That is the new analytic engine I would build.

### Ranking

1. **Sparse version of (b), implemented as a generalized (a): recommended full theorem.**
2. **(d) using literal (a): good milestone**, especially if you want the elimination theorem working before the full Taylor bookkeeping.
3. **Literal (a) for the unrestricted theorem:** insufficient as stated; upgrading it to allow \(S_h\) is inexpensive and gives route 1.
4. **(c): not the cheap formal route.** Exact Stein identities introduce derivative/cutoff bookkeeping, and their perturbed expectations still contain the same nonlinear information. I do not see a justified shortcut from them to positivity that avoids equivalent asymptotic work.

An important simplification: **you do not need a separate engine for every intermediate order.** Prove one residual expansion through order \(2\rho\), then use a finite-polynomial coefficient uniqueness lemma against SuperPoly data.

---

## 1. The pointwise engine

### Primitive exponential lemma

First prove the ordinary real-variable limit
\[
\frac{e^{-w}-1+w}{w^2}\longrightarrow \frac12
\quad(w\to0),
\]
with the quotient continuously filled in at \(w=0\), or an equivalent Taylor-remainder formulation avoiding division by \(w\).

Then prove:

```lean
-- Schematic signatures: names/local notation need adapting to the project.
theorem tendsto_exp_neg_sub_one_add_linear_div_pow
    (hρ : 0 < ρ)
    (hV :
      Tendsto (fun h => V h / h ^ ρ) atZeroPos (𝓝 Q))
    (hR :
      Tendsto
        (fun h => (V h - S h) / h ^ (2 * ρ))
        atZeroPos (𝓝 R)) :
    Tendsto
      (fun h =>
        (Real.exp (-V h) - 1 + S h) / h ^ (2 * ρ))
      atZeroPos (𝓝 ((1 / 2 : ℝ) * Q ^ 2 - R))
```

Here `atZeroPos := nhdsWithin 0 (Set.Ioi 0)`.

The proof uses
\[
e^{-V}-1+S=(e^{-V}-1+V)-(V-S).
\]
Consequently, this lemma need not know that \(S\) is a finite sum.

Your requested special case follows by taking \(S_h=h^\rho Q\):
\[
\frac{e^{-W_h}-1+h^\rho Q}{h^{2\rho}}
\longrightarrow \frac12Q^2-R
\]
when \(W_h/h^\rho\to Q\) and
\((W_h-h^\rho Q)/h^{2\rho}\to R\).

**No third-order uniform exponential remainder estimate is needed.** Second-order pointwise convergence plus domination of the second-order residual is enough.

---

## 2. Abstract integral and normalization engines

I would separate these into two layers:

1. DCT for a linear-subtracted residual;
2. normalization algebra for finite expansions.

For localization, it is particularly useful for the second layer to accept **weights**, rather than require every family to have the form \(e^{-(P+V)}\) globally.

### 2.1 Residual integral theorem

Set
\[
w_0=e^{-P},\qquad
F_h=\frac{w_h-w_0+w_0S_h}{h^{2\rho}}.
\]
For an unlocalized exponential family, \(w_h=e^{-(P+V_h)}\). For your application, \(w_h\) is the indicator-weighted rescaled density.

The pointwise conclusion should be
\[
F_h\longrightarrow w_0T,\qquad T=\frac12Q^2-R.
\]

The DCT hypothesis shapes should mirror the existing engine:

```lean
(hlim :
  ∀ᵐ x ∂μ,
    Tendsto (fun h => F h x) atZeroPos (𝓝 (w₀ x * T x)))

(hmeas₀ :
  ∀ᶠ h in atZeroPos, AEStronglyMeasurable (F h) μ)

(hmeasA :
  ∀ᶠ h in atZeroPos,
    AEStronglyMeasurable (fun x => A x * F h x) μ)

(hdom₀ :
  ∃ G₀, Integrable G₀ μ ∧
    ∀ᶠ h in atZeroPos, ∀ᵐ x ∂μ, ‖F h x‖ ≤ G₀ x)

(hdomA :
  ∃ GA, Integrable GA μ ∧
    ∀ᶠ h in atZeroPos, ∀ᵐ x ∂μ,
      ‖A x * F h x‖ ≤ GA x)
```

Together with eventual integrability of \(w_h,A w_h\), and integrability of the finitely many \(w_0B_m,A w_0B_m\), this gives
\[
\frac{
 \int A w_h-\int A w_0+\sum_{m=\rho}^{2\rho-1}h^m\int A B_mw_0
}{h^{2\rho}}
\longrightarrow \int A T w_0,
\]
and the same statement with \(A=1\).

This can be a thin wrapper around your existing DCT tools.

### 2.2 Normalization theorem

Define
\[
Z_0=\int w_0>0,\qquad
\mathbb E_0f=\frac{\int fw_0}{Z_0},\qquad
M_h(A)=\frac{\int A w_h}{\int w_h}.
\]
Put
\[
c_m=\operatorname{Cov}_0(A,B_m).
\]
Then the normalized conclusion is
\[
\boxed{
\frac{
 M_h(A)-\mathbb E_0A+
 \sum_{m=\rho}^{2\rho-1}h^m c_m
}{h^{2\rho}}
\longrightarrow
\operatorname{Cov}_0(A,T)
-\mathbb E_0Q\,\operatorname{Cov}_0(A,Q).
}
\]

With \(T=Q^2/2-R\), this is exactly the expansion you need.

A schematic top-level statement is:

```lean
theorem tendsto_normalized_linear_subtracted_div_pow
    (hρ : 0 < ρ)
    (hZ : 0 < ∫ x, w₀ x ∂μ)
    -- fixed and eventual integrability hypotheses
    -- the two residual integral limits, for A and 1
    :
    Tendsto
      (fun h =>
        (normalizedMoment μ (w h) A
          - normalizedMoment μ w₀ A
          + ∑ m ∈ Finset.Ico ρ (2 * ρ),
              h ^ m * covariance μ w₀ A (B m))
        / h ^ (2 * ρ))
      atZeroPos
      (𝓝
        (covariance μ w₀ A T
          - normalizedMoment μ w₀ (B ρ)
              * covariance μ w₀ A (B ρ)))
```

I would make the theorem take the **two scalar residual limits** rather than bundle all DCT hypotheses into it. Then provide a corollary combining the integration and normalization layers.

### Why only this normalization correction appears

The numerator and denominator both start changing at order \(h^\rho\). Thus the only product of two nonconstant contributions at order at most \(2\rho\) is the product of their leading \(h^\rho\) terms.

No intermediate \(B_m\), \(m>\rho\), participates in a quadratic term at this order.

For the proof, the denominator residual expansion already implies
\[
Z_h\to Z_0,\qquad
\frac{Z_h-Z_0}{h^\rho}\to-\int Qw_0.
\]
So you can derive these rather than ask for an additional first-order theorem.

An especially useful exact identity is
\[
\begin{aligned}
&\frac{M_h(A)-\mathbb E_0A+\sum_m h^m c_m}{h^{2\rho}}\\
&\quad=
\frac{\int(A-\mathbb E_0A)F_h}{Z_h}
+
\frac{Z_h-Z_0}{h^\rho Z_h}
  \sum_m h^{m-\rho}c_m.
\end{aligned}
\]
Its limit immediately gives the formula above. The identity is used only eventually, where \(h>0\) and \(Z_h\ne0\).

---

## 3. Domination: avoid \(e^{|V|}\)

Your concern about negative, large \(V\) is correct. A bound involving \(e^{|V|}\) is poorly matched to this localization.

Use the endpoint bound
\[
\boxed{
|e^{-v}-1+v|
\le \frac{v^2}{2}\max(1,e^{-v})
\le \frac{v^2}{2}(1+e^{-v}).
}
\]
It follows from the second-order integral remainder, since the maximum of \(e^{-sv}\) on \(s\in[0,1]\) occurs at an endpoint.

Multiplying by \(e^{-P}\) gives
\[
e^{-P}|e^{-V}-1+V|
\le
\frac{V^2}{2}\bigl(e^{-P}+e^{-(P+V)}\bigr).
\]

**Both weights on the right are already controlled by your quadratic lower bounds.** No positivity of the Taylor polynomial or of \(Q_k\) is required.

### Inner region

Choose \(r>0\) such that \(B_r(0)\subset U\) and the required Taylor estimates hold there.

On \(\|hx\|<r\), arrange
\[
\left|\frac{V_h(x)}{h^\rho}\right|
 \le C_1\|x\|^{\rho+2},
\]
and
\[
\left|\frac{V_h(x)-S_h(x)}{h^{2\rho}}\right|
 \le C_2\|x\|^{2\rho+2}.
\]
The latter is the Taylor bound with remainder beginning at degree
\[
2\rho+2=2k-2.
\]

Then
\[
|F_h(x)|
\le
C\left(\|x\|^{2\rho+4}+\|x\|^{2\rho+2}\right)
e^{-c_*\|x\|^2},
\]
for some \(c_*>0\). Multiplication by a polynomially growing observable preserves integrability.

You also need the **pointwise identification** of the highest remainder with \(R=Q_{2k-2}\). A big-\(O\) Taylor bound alone does not identify that limit. Analyticity supplies it; depending on package APIs, use either a degree-\((2k-2)\) little-\(o\) remainder or a degree-\((2k-1)\) big-\(O\) remainder.

### Outer region

On \(\|hx\|\ge r\), do **not** estimate the exponential remainder through \(V_h\). Estimate the residual directly:
\[
F_h=\frac{w_h-w_0+w_0S_h}{h^{2\rho}}.
\]
Here
\[
h^{-a}\le r^{-a}\|x\|^a
\qquad(a\in\mathbb N).
\]
Thus the negative powers of \(h\) become polynomial factors, while:

- \(w_h\) is bounded by a Gaussian on its support;
- \(w_0\) is Gaussian;
- every \(B_m\) has polynomial growth.

This gives an integrable polynomial-times-Gaussian majorant for the outer region as well.

For each fixed \(x\), the outer region eventually disappears, since \(hx\to0\). Consequently it contributes zero to the pointwise limit.

This strategy handles:

- the boundary indicator;
- parts of \(U\) outside the Taylor ball;
- negative indefinite perturbations;
- different localizations of the reference and perturbed losses.

If your reference moment uses a localized Gaussian instead of the full Gaussian, discharge its difference from the full Gaussian by the existing tail-slice lemmas at order \(2\rho\).

---

## 4. Intermediate orders: one coefficient lemma, not many analytic engines

The expansion yields, for each probe,
\[
D_A(h)
=
-\sum_{m=\rho}^{2\rho-1}
 h^m\operatorname{Cov}_\gamma(A,B_m)
+h^{2\rho}a_A+o(h^{2\rho}).
\]

Prove a reusable scalar lemma:

> If a function is \(o(h^n)\) at every required power, and has a finite expansion through degree \(M\), every coefficient of that expansion is zero.

A convenient implementation is induction on the least exponent: divide by its power, take the limit, remove the vanishing coefficient. This is finite algebra and limits, not repeated Laplace analysis.

In fact, for this application, **flatness at the single sufficiently high order \(o(h^{2\rho})\)** already forces all coefficients in the displayed expansion to vanish. SuperPoly supplies that hypothesis.

Apply the lemma to \(A=q\):
\[
\operatorname{Cov}_\gamma(q,Q_j)
=j\,\mathbb E_\gamma Q_j.
\]
Therefore
\[
\mathbb E_\gamma Q_j=0
\qquad(k\le j\le2k-3).
\]
In particular \(\mathbb E_\gamma Q_k=0\). The corresponding intermediate coefficients for \(q^2\) then vanish automatically by your second covariance identity.

So the recommended proof is:

1. obtain the full sparse expansion for \(q\);
2. coefficient uniqueness gives all intermediate means zero and the top coefficient zero;
3. use those means in the expansion for \(q^2\);
4. its top coefficient is zero;
5. eliminate.

Remember the scaling when importing the original hypotheses:
\[
\langle q\rangle_{L,t}=h^2M_h(q),\qquad
\langle q^2\rangle_{L,t}=h^4M_h(q^2).
\]
SuperPoly absorbs these fixed powers, but that bridge should be explicit.

---

## 5. Formula and elimination: confirmed

Before imposing first-order vanishing, the coefficient is
\[
a_A
=
\frac12\operatorname{Cov}_\gamma(A,Q_k^2)
-\operatorname{Cov}_\gamma(A,Q_{2k-2})
-\mathbb E_\gamma Q_k\,
   \operatorname{Cov}_\gamma(A,Q_k).
\]

The sign of the last term is **negative**.

Once \(\mathbb E_\gamma Q_k=0\), the formula becomes exactly
\[
\boxed{
a_A
=
\frac12\operatorname{Cov}_\gamma(A,Q_k^2)
-\operatorname{Cov}_\gamma(A,Q_{2k-2}).
}
\]
For an arbitrary observable, intermediate linear terms may still precede this coefficient. For the two radial probes, the intermediate means established above remove them.

Set
\[
s=\mathbb E_\gamma[Q_k^2],
\qquad r=\mathbb E_\gamma[Q_{2k-2}].
\]
Your identities give
\[
a_q=ks-(2k-2)r,
\]
and
\[
a_{q^2}
=k(2k+2d+2)s-(2k-2)(2k+2d)r.
\]
Hence
\[
\begin{aligned}
a_{q^2}-(2d+2k)a_q
&=k\bigl((2k+2d+2)-(2d+2k)\bigr)s\\
&=2ks.
\end{aligned}
\]
Thus the arithmetic is correct:
\[
\boxed{a_{q^2}-(2d+2k)a_q=2k\,\mathbb E_\gamma[Q_k^2].}
\]

With both coefficients zero and \(k>0\), \(s=0\). Together with \(\mathbb E Q_k=0\), this gives zero Gaussian self-covariance, matching your existing rigidity lemma.

---

## 6. What the gap theorem loses

The gap theorem is a worthwhile milestone, but not an adequate replacement for the unrestricted analytic theorem.

- For **\(k=3\)** there are no intermediate degrees: the gap condition is vacuous. Thus literal (a) already handles the complete leading-cubic case.
- For larger \(k\), the gap condition restricts finitely many Taylor jets and is generally nongeneric.
- Odd homogeneous terms have zero Gaussian mean, but their pointwise presence still breaks literal (a)'s assumed shape. The sparse residual engine handles them with no special cases.
- Symmetry can make the gap automatic in particular classes, but not in general.

The extra cost of allowing the finite sum \(S_h\) is modest compared with the localization/domination work, which both approaches need.

---

## 7. Estimated implementation size

Without inspecting the actual files, I would budget **roughly 800–1,600 additional lines** for the sparse engine and its Laplace instantiation, assuming the existing Gaussian integrability and tail APIs are readily reusable.

| Component | Rough lines |
|---|---:|
| Endpoint exponential bound and scalar second-order limit | 100–200 |
| Pointwise linear-subtracted exponential limit | 50–100 |
| Two DCT residual-integral wrappers | 70–140 |
| Finite-sum limit helpers and normalization algebra | 150–280 |
| Inner/outer domination and localized instantiation | 250–500 |
| Coefficient uniqueness and radial elimination | 100–200 |
| Analytic first-nonzero-jet contradiction / package glue | 80–200 |

These ranges are planning estimates, not a repository-derived count. If selecting the first nonzero analytic jet and concluding local equality are not already supported, that final item can be substantially larger.

### Suggested lemma order

1. `abs_exp_neg_sub_one_add_le_endpoint`
2. `tendsto_exp_neg_sub_one_add_self_div_sq`
3. `tendsto_exp_neg_sub_one_add_linear_div_pow`
4. `tendsto_integral_linear_subtracted_weight`
5. `tendsto_normalized_linear_subtracted_div_pow`
6. `HigherLaplaceDomain.secondOrderResidual_inner_bound`
7. `HigherLaplaceDomain.secondOrderResidual_outer_bound`
8. `tendsto_rescaledMoment_linear_subtracted_div_pow`
9. `coefficients_eq_zero_of_flat_finite_expansion`
10. `radial_second_order_elimination`
11. the analytic rigidity theorem.

**Bottom line:** subtract the finite linear jet, dominate the exponential residual by its two endpoint weights, and normalize once. This preserves your existing first-order architecture while avoiding both a general expansion library and a new family of polynomial loss packages.