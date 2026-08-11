## 1. Base-coefficient recovery

Yes. The clean route is:

1. prove the leading scaled second-moment limit for each jet separately;
2. use eventual equality of the second moments to identify the two limits;
3. use injectivity in \(a\);
4. substitute \(a_1=a_2\) and invoke `polynomialJet_recovery` unchanged.

There is no benefit in extending the pairwise-difference machinery to unequal reference measures. If \(a_1\neq a_2\), the rescaled \(J\)-difference already has a nonzero \(q^0\) term, so the existing \(q^{-r}\) argument is deliberately at the wrong scale.

For general \(k\), let
\[
A_s(a)=\int_{\mathbb R}x^s e^{-a x^{2k}}\,dx
\]
for even \(s\). Scaling gives
\[
A_s(a)=a^{-(s+1)/(2k)}A_s(1),
\]
and hence
\[
M_2(a)=\frac{A_2(a)}{A_0(a)}
      =\frac{A_2(1)}{A_0(1)}a^{-1/k}.
\]
Thus \(M_2\) is strictly decreasing, and therefore injective, for every \(k\geq 1\), not only \(k=1\).

For \(k=1\),
\[
M_2(a)=\frac1{2a}.
\]
With \(a=\lambda/2\), this is \(M_2=1/\lambda\), as required by the nondegenerate theorem.

The desired analytic statement is simply
\[
q^{-2}\langle x^2\rangle_{i,q}\longrightarrow M_2(a_i).
\]
If the unscaled second moments are eventually equal, division by \(q^2\) and passage to the limit give
\[
M_2(a_1)=M_2(a_2),
\]
hence \(a_1=a_2\).

### Minimality

- The second moment alone is enough when the minimum is already fixed at \(0\).
- Equality of first moments is not needed for the polynomial recovery theorem.
- If the public theorem is phrased using variance, first and second moments can be included to form the variance, but this is a presentation corollary rather than part of base-coefficient recovery. One additionally proves that the squared mean is lower order at the \(q^2\) scale.
- Recovering \(a\) from \(Z\) is less attractive: it uses unnormalised data and may interact with additive constants in the loss. The normalized second moment is canonical and already belongs to the intended data.

I would prove the limit generically in \(k\) if the existing \(A_s(a)\)-scaling infrastructure makes that inexpensive, but package the first user-facing theorem at \(k=1\).

---

## 2. Scope of the smooth-loss reduction

It should be on the same strategic roadmap, but scoped as a separate programme or milestone from B′.

B′ should have a crisp endpoint:

> Finite polynomial jets with possibly different positive quadratic coefficients are identified by the appropriate normalized moment data.

The smooth theorem introduces a substantially different collection of obligations:

- local quadratic bounds;
- fixed-region and moving-region localization;
- Taylor remainder bounds after rescaling;
- superpolynomial or sufficiently high-order tail estimates;
- comparison of partition functions and normalized quotients;
- cutoff removal;
- finite-order-to-full-jet quantifier management.

More importantly, the smooth reduction cannot generally invoke the current exact-equality theorem verbatim. If two smooth models have equal moment data and each is replaced by a Taylor polynomial, the two polynomial models are only **asymptotically indistinguishable** to a controlled order; their moments are not eventually exactly equal.

Therefore the smooth programme needs a stability version of the algebraic theorem, with hypotheses of the form
\[
q^{-r}\bigl(\mu^{(1)}_{s}(q)-\mu^{(2)}_{s}(q)\bigr)\to 0
\]
at the coefficient-sensitive scale, rather than literal eventual equality. The existing proof should adapt—its contradiction only needs the observed difference to vanish at the relevant scale—but this deserves its own theorem interface.

So:

- **B′:** unequal-base polynomial recovery;
- **C:** asymptotically stable recovery plus smooth localization and Taylor transfer.

That separation keeps B′ closed and useful without understating what remains for Theorem 3.1.

---

## 3. Tide-sized stages

### Programme B′: unequal-base polynomial jets

#### B1. Leading second-moment asymptotic

Closed target, generically in \(k\):
```lean
scaled_secondMoment_tendsto :
  q⁻² * moment 2 jet q ⟶ A 2 a / A 0 a
```
together with
```lean
base_secondMoment_formula :
  A 2 a / A 0 a =
    (A 2 1 / A 0 1) * a ^ (-1 / k)
```
in whatever real-power formulation best matches the library.

For \(k=1\), provide the simple corollary
```lean
gaussian_secondMoment :
  A 2 a / A 0 a = 1 / (2 * a)
```

This stage should use one-profile scaling/DCT only; no pairwise subtraction.

#### B2. Base-coefficient injectivity

Closed target:
```lean
baseCoeff_eq_of_eventuallyEq_secondMoment :
  Eventually (fun q => moment 2 jet₁ q = moment 2 jet₂ q) atZero⁺ →
  a₁ = a₂
```

Optionally also expose a more reusable limit-based version:
```lean
baseCoeff_eq_of_scaledSecondMoment_diff_tendsto_zero :
  q⁻² * (moment 2 jet₁ q - moment 2 jet₂ q) ⟶ 0 →
  a₁ = a₂
```

The second form is the better bridge to the later smooth programme.

#### B3. Variable-base polynomial recovery

Closed target, preferably for general \(k\):
```lean
polynomialJet_recovery_variableBase :
  eventual equality of second moments →
  (∀ r ≤ R, eventual equality of moments at degree 2*k+r) →
  a₁ = a₂ ∧ coefficients₁ = coefficients₂
```

Proof structure:

1. apply B2;
2. substitute the resulting equality of base coefficients;
3. invoke `polynomialJet_recovery` verbatim.

No modification of the pairwise secant/DCT/variance induction should be needed.

#### B4. Nondegenerate \(k=1\) package

Closed target:
```lean
nondegeneratePolynomialJet_recovery :
  potentials
    (λ₁ / 2) * x^2 + ∑ r ≤ R, c₁ r * x^(2+r)
    (λ₂ / 2) * x^2 + ∑ r ≤ R, c₂ r * x^(2+r) →
  matching normalized moments →
  λ₁ = λ₂ ∧ c₁ = c₂
```

The minimal matching data are:

- degree \(2\), to recover \(\lambda\);
- degree \(2+r\) for each coefficient \(c_r\), \(1\leq r\leq R\).

A degree-one hypothesis may be included in a theorem shaped like the note’s observable package, but it is mathematically redundant once the minimum is fixed at zero.

#### B5. \(t\)- and variance-facing corollaries

Closed targets:

- transfer \(q=t^{-1/2}\);
- prove
  \[
  t\,\mathbb E_t[x^2]\to \frac1\lambda;
  \]
- if desired, prove
  \[
  t\,\operatorname{Var}_t(x)\to \frac1\lambda
  \]
  by showing \(t(\mathbb E_t x)^2\to0\);
- restate B4 in the notation used by `germbij`.

This should be a packaging tide, not new recovery machinery.

“Parity completion” does not need its own tide: for \(k=1\), the existing observables \(x^{2+r}\) already alternate through both parities.

---

### Separate Programme C: smooth-germ transfer

#### C1. Asymptotically stable polynomial recovery

Replace exact eventual equality by vanishing at the coefficient-sensitive scale. This is the essential bridge between Taylor approximation and the existing algebraic core.

Closed target: a finite-order theorem saying that sufficiently high-order agreement of the normalized moment asymptotics forces equality of the coefficients through order \(R\).

#### C2. Local quadratic control and domain splitting

From the nondegenerate minimum assumptions, produce:

- a neighborhood with two-sided quadratic control;
- a positive loss gap on the cutoff annulus;
- denominator lower bounds;
- a precise inner/moderate-tail/outer-region decomposition.

The outer estimate requires the theorem’s actual global or cutoff assumptions; a merely local nondegenerate minimum is not by itself enough to suppress competing minima.

#### C3. Rescaled Taylor-remainder bounds

For each finite \(J\), compare the smooth loss with its degree-\((J+2)\) Taylor polynomial on the moving inner region and prove the required \(o(q^J)\) integral bounds, uniformly for the finite family of observables being used.

#### C4. Normalized quotient and cutoff transfer

Transfer numerator and partition-function estimates to normalized moments, including explicit denominator control, and show that compactly supported observables agreeing with monomials near the minimum have the same finite asymptotic coefficients.

#### C5. Finite-order smooth recovery

Combine C1–C4 to show:

> Agreement of the relevant smooth-model moment asymptotics through order \(R\) determines the Taylor coefficients through order \(R+2\).

#### C6. Full Taylor-jet packaging

Quantify over arbitrary finite \(R\) and package the compatible family of finite-order conclusions as equality of the full Taylor jets. Add the \(\lambda\)-from-variance statement and the note’s final observable formulation.

---

## Main scope trap

The main trap is treating “replace the smooth loss by its Taylor polynomial” as though it produced an exact polynomial comparison to which `polynomialJet_recovery` applies directly.

It does not. It produces order-controlled errors, so the necessary bridge is an **asymptotically stable recovery theorem**, followed by careful localization and normalized-ratio estimates. Closely related traps are:

- assuming a local quadratic bound alone gives global \(o(t^{-\infty})\) tails;
- moving from recovery at every finite order to a full-jet theorem without handling the quantifiers explicitly;
- advertising B′ as Theorem 3.1 when it is only its finite polynomial algebraic core.

With those boundaries, B′ is small, low-risk, and now clearly justified by the completed weighted-jet machinery; Programme C is the genuine analytic formalisation of the note’s “Justification” paragraph.