## 1. Envelope decision

Do **not** use E1 alone as the stage-2 envelope, and do not invest in the proposed two-region estimate.

The relevant factorization is

\[
L_q(u)
= u^{2k}\left(a+\sum_{r=1}^R c_r(qu)^r\right)
= u^{2k}P(qu),
\qquad
P(y):=a+\sum_{r=1}^R c_r y^r.
\]

Consequently, small \(q\) does not make the perturbation globally small: \(qu\) still ranges over all of \(\mathbb R\).

For example, with \(P(y)=1-3y+y^2\), the leading coefficient is positive and the degree is even, but \(P(1)=-1\). At \(u=q^{-1}\),

\[
L_q(q^{-1})=-q^{-2k},
\]

so the Gibbs weight has a remote peak of size \(\exp(q^{-2k})\). Every fixed-\(q\) integral exists, but the measure does not converge to the reference measure as \(q\to0\). Thus E1 gives pointwise integrability but not the asymptotic regime needed in stages 6–7.

The correct envelope is the following strengthened version of E2.

### Recommended envelope: uniformly positive profile

Require a certified \(\rho>0\) such that

\[
\forall y\in\mathbb R,\qquad
\rho \le P(y)=a+\sum_{r=1}^R c_r y^r.
\tag{PE}
\]

Then, for every real \(q,u\),

\[
L_q(u)=u^{2k}P(qu)\ge \rho u^{2k}.
\tag{1}
\]

This is the clean global inequality. It gives:

* integrability for every \(q\);
* a \(q\)-independent dominating function;
* domination of all \(q\)-derivatives by polynomial multiples of
  \(\exp(-\rho u^{2k})\);
* direct access to differentiation/Taylor expansion at \(q=0\);
* no cutoff or Taylor-remainder machinery.

There is no useful “small \(q\)” substitute for (PE): because of the \(qu\) factor, a global lower bound on \(L_q/u^{2k}\) is exactly a global lower bound on \(P\), independent of \(q\).

### Arbitrary target jets

If the target coefficients \(c_1,\dots,c_R\) do not satisfy (PE), append an auxiliary stabilizer beyond the order being extracted:

\[
P_{\mathrm{stab}}(y)
=
a+\sum_{r=1}^R c_r y^r+d y^M,
\]

where \(M>R\) is even and \(d>0\) is chosen sufficiently large. Since \(a>0\), the original profile is positive near \(0\), and a sufficiently large even top term can lift its negative part away from \(0\). The added term first occurs at order \(q^M\), so it does not alter extraction through order \(R\).

That is preferable to E3 for the stage 6–7 algebraic programme. E3 is appropriate only if the final theorem must concern an arbitrary prescribed smooth global potential rather than a stabilized polynomial model.

---

## 2. Recommended stage-2 Lean statement

The cleanest API separates:

1. the unscaled polynomial potential;
2. the rescaled jet;
3. the profile-positivity certificate;
4. the integral scaling identities;
5. the normalized expectation identity.

Below, `Fin R` indexes \(r=1,\dots,R\).

```lean
open scoped BigOperators
open MeasureTheory

noncomputable section

def jetProfile
    (R : ℕ) (a : ℝ) (c : Fin R → ℝ) (y : ℝ) : ℝ :=
  a + ∑ i : Fin R, c i * y ^ (i.1 + 1)

def jetPotential
    (k R : ℕ) (a q : ℝ) (c : Fin R → ℝ) (u : ℝ) : ℝ :=
  a * u ^ (2 * k) +
    ∑ i : Fin R,
      c i * q ^ (i.1 + 1) * u ^ (2 * k + (i.1 + 1))

/-- The original, unscaled polynomial potential. -/
def polynomialJet
    (k R : ℕ) (a : ℝ) (c : Fin R → ℝ) (x : ℝ) : ℝ :=
  jetPotential k R a 1 c x
```

### Algebraic factorization

This should be an explicit early lemma, since it explains the envelope.

```lean
theorem jetPotential_eq_pow_mul_profile
    (k R : ℕ) (a q : ℝ) (c : Fin R → ℝ) (u : ℝ) :
    jetPotential k R a q c u
      = u ^ (2 * k) * jetProfile R a c (q * u) := by
  ...
```

### Profile envelope

```lean
def HasPositiveJetProfile
    (R : ℕ) (a ρ : ℝ) (c : Fin R → ℝ) : Prop :=
  0 < ρ ∧ ∀ y : ℝ, ρ ≤ jetProfile R a c y
```

The principal lower-bound lemma is then:

```lean
theorem jetPotential_lower_bound
    {k R : ℕ} {a ρ q : ℝ} {c : Fin R → ℝ}
    (hk : 0 < k)
    (hprof : HasPositiveJetProfile R a ρ c)
    (u : ℝ) :
    ρ * u ^ (2 * k) ≤ jetPotential k R a q c u := by
  ...
```

Notice that this holds for every real \(q\), not merely small positive \(q\).

### Integrability lemmas

The main workhorse should cover every polynomial moment.

```lean
theorem integrable_pow_mul_exp_neg_jetPotential
    {k R n : ℕ} {a ρ q : ℝ} {c : Fin R → ℝ}
    (hk : 0 < k)
    (hprof : HasPositiveJetProfile R a ρ c) :
    Integrable
      (fun u : ℝ =>
        u ^ n * Real.exp (-jetPotential k R a q c u)) := by
  ...
```

The partition-function specialization:

```lean
theorem integrable_exp_neg_jetPotential
    {k R : ℕ} {a ρ q : ℝ} {c : Fin R → ℝ}
    (hk : 0 < k)
    (hprof : HasPositiveJetProfile R a ρ c) :
    Integrable
      (fun u : ℝ => Real.exp (-jetPotential k R a q c u)) := by
  simpa using
    integrable_pow_mul_exp_neg_jetPotential
      (k := k) (R := R) (n := 0)
      (a := a) (ρ := ρ) (q := q) (c := c) hk hprof
```

Positivity of the denominator:

```lean
theorem integral_exp_neg_jetPotential_pos
    {k R : ℕ} {a ρ q : ℝ} {c : Fin R → ℝ}
    (hk : 0 < k)
    (hprof : HasPositiveJetProfile R a ρ c) :
    0 <
      ∫ u : ℝ, Real.exp (-jetPotential k R a q c u) := by
  ...
```

For later differentiation, it is useful to expose the actual dominating estimate:

```lean
theorem norm_pow_mul_exp_neg_jetPotential_le
    {k R n : ℕ} {a ρ q : ℝ} {c : Fin R → ℝ}
    (hk : 0 < k)
    (hprof : HasPositiveJetProfile R a ρ c)
    (u : ℝ) :
    ‖u ^ n * Real.exp (-jetPotential k R a q c u)‖
      ≤ |u| ^ n * Real.exp (-ρ * u ^ (2 * k)) := by
  ...
```

The right-hand side is integrable using the existing `kth_integrable_pow` family. This is the lemma that stages 3 onward should use for dominated differentiation.

### Reference normalized moment

```lean
def normalizedJetMoment
    (k R s : ℕ) (a q : ℝ) (c : Fin R → ℝ) : ℝ :=
  (∫ u : ℝ,
      u ^ s * Real.exp (-jetPotential k R a q c u)) /
    (∫ u : ℝ,
      Real.exp (-jetPotential k R a q c u))
```

### Unnormalized scaling identities

For \(t>0\), define

\[
q=t^{-1/(2k)}.
\]

In Lean, use real powers explicitly:

```lean
let q : ℝ := Real.rpow t (-(1 : ℝ) / (2 * k : ℝ))
```

The key integral statement should be:

```lean
theorem integral_polynomialJet_scale
    {k R s : ℕ} {a ρ t : ℝ} {c : Fin R → ℝ}
    (hk : 0 < k)
    (ht : 0 < t)
    (hprof : HasPositiveJetProfile R a ρ c) :
    let q : ℝ := Real.rpow t (-(1 : ℝ) / (2 * k : ℝ))
    (∫ x : ℝ,
        x ^ s *
          Real.exp (-t * polynomialJet k R a c x))
      =
    q ^ (s + 1) *
      ∫ u : ℝ,
        u ^ s *
          Real.exp (-jetPotential k R a q c u) := by
  ...
```

The partition-function case should also be available directly:

```lean
theorem integral_exp_polynomialJet_scale
    {k R : ℕ} {a ρ t : ℝ} {c : Fin R → ℝ}
    (hk : 0 < k)
    (ht : 0 < t)
    (hprof : HasPositiveJetProfile R a ρ c) :
    let q : ℝ := Real.rpow t (-(1 : ℝ) / (2 * k : ℝ))
    (∫ x : ℝ,
        Real.exp (-t * polynomialJet k R a c x))
      =
    q *
      ∫ u : ℝ,
        Real.exp (-jetPotential k R a q c u) := by
  ...
```

These are proved by the substitution \(x=qu\), together with

\[
tq^{2k}=1.
\]

### Exact normalized scaling theorem

A definition-independent ratio form is:

```lean
theorem normalized_polynomialJet_scale
    {k R s : ℕ} {a ρ t : ℝ} {c : Fin R → ℝ}
    (hk : 0 < k)
    (ht : 0 < t)
    (hprof : HasPositiveJetProfile R a ρ c) :
    let q : ℝ := Real.rpow t (-(1 : ℝ) / (2 * k : ℝ))
    Real.rpow t ((s : ℝ) / (2 * k : ℝ)) *
      ((∫ x : ℝ,
          x ^ s *
            Real.exp (-t * polynomialJet k R a c x)) /
       (∫ x : ℝ,
          Real.exp (-t * polynomialJet k R a c x)))
      =
    normalizedJetMoment k R s a q c := by
  ...
```

Using the repository’s argument order for `gibbsExpectation`, the intended public corollary is:

```lean
theorem gibbsExpectation_polynomialJet_scale
    {k R s : ℕ} {a ρ t : ℝ} {c : Fin R → ℝ}
    (hk : 0 < k)
    (ht : 0 < t)
    (hprof : HasPositiveJetProfile R a ρ c) :
    let q : ℝ := Real.rpow t (-(1 : ℝ) / (2 * k : ℝ))
    Real.rpow t ((s : ℝ) / (2 * k : ℝ)) *
        gibbsExpectation
          (polynomialJet k R a c) t (fun x : ℝ => x ^ s)
      =
    normalizedJetMoment k R s a q c := by
  ...
```

The ratio-form theorem should be the foundational result; the `gibbsExpectation` theorem can then be a short unfolding corollary.

### Minimal \(R=2\) profile certificate

For

\[
P(y)=a+c_1y+c_2y^2,
\]

the natural condition is

\[
c_2>0,\qquad c_1^2<4ac_2.
\]

Then one may take

\[
\rho=a-\frac{c_1^2}{4c_2}>0.
\]

A useful convenience lemma is therefore:

```lean
theorem hasPositiveJetProfile_two
    {a c₁ c₂ : ℝ}
    (hc₂ : 0 < c₂)
    (hdisc : c₁ ^ 2 < 4 * a * c₂) :
    HasPositiveJetProfile 2
      a
      (a - c₁ ^ 2 / (4 * c₂))
      ![c₁, c₂] := by
  ...
```

This is exactly the quadratic-profile analogue of the discriminant argument already used for the cubic/quartic anharmonic potential.

---

## 3. Generic \(R\) or \(R=2\)?

Implement the **generic-\(R\) theorem immediately**, but also add \(R=2\) as the first concrete certificate/test case.

Reasons:

1. Once profile positivity is assumed, the analytic proof is independent of \(R\). It is just:
   * finite-sum factorization;
   * the bound \(L_q\ge\rho u^{2k}\);
   * existing monomial-exponential integrability;
   * linear change of variables.

2. Stages 6–7 need generic coefficient indexing to express the triangular covariance structure. Starting with a bespoke pair `(c₁, c₂)` would force an API rewrite precisely where coefficient extraction begins.

3. \(R=2\) remains valuable as:
   * the minimal parity example;
   * a test of unrestricted odd coefficients;
   * a concrete discriminant certificate;
   * a regression test for the generic theorem.

So the recommended division is:

* **core stage 2:** generic finite profile with `HasPositiveJetProfile`;
* **stage-2 example/corollary:** \(R=2\) under the quadratic discriminant condition;
* **later envelope utility:** existence of a positive even stabilizer of degree \(M>R\) for arbitrary prescribed coefficients through order \(R\).

This gives the later covariance machinery a stable generic API without forcing the finite target jet itself to be globally coercive.