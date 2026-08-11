## Recommendation in brief

- **Public theorem/API:** use **existence of coefficients plus a comparison/uniqueness theorem**, not an explicit closed formula.
- **Internal proof object:** nevertheless define finite exponent coefficients recursively as universal polynomials in the homogeneous Taylor terms \(V_s\). This makes the proof and jet-dependence manageable without exposing a multinomial formula.
- **Domain packaging:** add a thin `ForwardExpansionDomain N` mixin over `HigherLaplaceDomain (N + 2)`. The genuinely missing hypothesis is a **Peano/little-\(o\) Taylor remainder at order \(N+2\)**. No additional global coercivity or measurability fields should be needed.
- **Localization:** cut first at a mesoscopic radius such as \(\|z\|\le q^{-1/2}\). Only then use the exponential remainder estimate. Expanding globally with an \(e^{|R_q|}\) bound is not integrable for higher-degree potentials.
- **First infrastructure tide:** Gaussian-polynomial superpolynomial tails, their transfer to the existing rescaled integrand via coercivity, and elementary facts about the mesoscopic cutoff.

---

# A. Expansion object and coefficient packaging

## 1. Public expansion predicate

Package the asymptotic statement separately from how coefficients are constructed.

Schematic Lean:

```lean
def IsMomentExpansion
    (D : LocalLaplaceDomain E)
    (α : MultiIndex d)
    (N : ℕ)
    (c : Fin (N + 1) → ℝ) : Prop :=
  (fun q =>
      rescaledPosteriorMoment D α q
        - ∑ j : Fin (N + 1), c j * q ^ (j : ℕ))
    =o[nhdsWithin 0 (Set.Ioi 0)]
      (fun q : ℝ => q ^ N)
```

Here `rescaledPosteriorMoment` should be whichever existing expression is definitionally or theorem-equivalent to

\[
q^{-|\alpha|}
 \left\langle w^\alpha\right\rangle_{t=q^{-2}}.
\]

If finite sums over `Fin` are inconvenient, use:

```lean
∑ j in Finset.range (N + 1), c j * q ^ j
```

with `c : ℕ → ℝ`. The `Fin (N+1)` version better records that only finitely many coefficients are present.

The main public theorem should be existential:

```lean
theorem exists_momentExpansion
    (D : ForwardExpansionDomain N)
    (α : MultiIndex d) :
    ∃ c : Fin (N + 1) → ℝ,
      IsMomentExpansion D.toLocalLaplaceDomain α N c
```

This is enough for the forward existence claim.

## 2. Prove coefficient uniqueness once

Existential coefficients are safe only if accompanied by a generic uniqueness lemma:

```lean
theorem asymptoticPolynomial_coeff_unique
    {N : ℕ}
    {f : ℝ → ℝ}
    {c d : Fin (N + 1) → ℝ}
    (hc :
      (fun q => f q - ∑ j, c j * q ^ (j : ℕ))
        =o[nhdsWithin 0 (Set.Ioi 0)] fun q => q ^ N)
    (hd :
      (fun q => f q - ∑ j, d j * q ^ (j : ℕ))
        =o[nhdsWithin 0 (Set.Ioi 0)] fun q => q ^ N) :
    c = d
```

It may be easier to prove the pointwise form by taking the least index at which coefficients differ:

```lean
theorem asymptoticPolynomial_coeff_eq
    ...
    (j : Fin (N + 1)) :
    c j = d j
```

This lemma is independent of Laplace analysis and will also make any later `Classical.choose` definition canonical.

## 3. Jet-dependence in comparison form

Define a reusable jet equality predicate. Equality of continuous multilinear maps is preferable to equality only on diagonals.

```lean
def JetEqUpTo
    (k : ℕ) (L₁ L₂ : E → ℝ) : Prop :=
  ∀ m ≤ k,
    iteratedFDeriv ℝ m L₁ 0 = iteratedFDeriv ℝ m L₂ 0
```

Then state coefficient dependence directly:

```lean
theorem momentExpansion_coeff_eq_of_jetEq
    {j : ℕ}
    (D₁ : ForwardExpansionDomain j)
    (D₂ : ForwardExpansionDomain j)
    (α : MultiIndex d)
    (hjet : JetEqUpTo (j + 2) D₁.L D₂.L)
    {c₁ c₂ : Fin (j + 1) → ℝ}
    (hc₁ : IsMomentExpansion D₁.toLocalLaplaceDomain α j c₁)
    (hc₂ : IsMomentExpansion D₂.toLocalLaplaceDomain α j c₂) :
    c₁ ⟨j, Nat.lt_succ_self j⟩ =
      c₂ ⟨j, Nat.lt_succ_self j⟩
```

A slightly stronger triangular statement is likely just as easy:

```lean
theorem momentExpansion_coeff_eq_of_jetEq
    {N : ℕ}
    (hjet : JetEqUpTo (N + 2) D₁.L D₂.L)
    ...
    (j : Fin (N + 1)) :
    c₁ j = c₂ j
```

This uses more jet equality than necessary for coefficients below \(N\), but is convenient. Afterwards prove the sharp corollary saying coefficient \(j\) only uses the \((j+2)\)-jet.

### Recommendation

Use **existence plus comparison** as the exported mathematical statement. Do not expose a multinomial Gaussian-integral formula as the primary API.

Internally, however, the proof should construct numerator and denominator coefficients. Purely nonconstructive existence from the outset would make the integration and finite-division steps harder, not easier.

If the final family theorem wants an actual function `ℕ → ℝ`, define it later using choice:

```lean
noncomputable def momentCoeff (D ...) (α ...) (j : ℕ) : ℝ := ...
```

and use uniqueness to show that it is independent of the chosen expansion order.

---

# B. Exponent split and `ForwardExpansionDomain`

## 1. What `HigherLaplaceDomain (N+2)` is missing

An estimate of the form

\[
|\operatorname{rem}_{N+2}(y)|\le C\|y\|^{N+2}
\]

does **not** by itself identify the coefficient of \(q^N\). After substituting \(y=qz\) and dividing by \(q^2\), it only gives an \(O(q^N)\) error, whereas the order-\(N\) expansion needs that error to be \(o(q^N)\) for fixed \(z\).

The missing input is the Peano remainder

\[
\operatorname{rem}_{N+2}(y)=o(\|y\|^{N+2})
\quad\text{as }y\to0.
\]

Mathematically this follows from appropriate \(C^{N+2}\) regularity, but if extracting it from Mathlib is expensive, it should be a direct field of the forward-domain mixin.

## 2. Suggested structure

```lean
structure ForwardExpansionDomain (N : ℕ)
    extends HigherLaplaceDomain (N + 2) where
  taylorRemainder_isLittleO :
    (fun y =>
      L y -
        ∑ m in Finset.range (N + 3),
          taylorHomogeneousTerm m L y)
      =o[𝓝 0]
        (fun y => ‖y‖ ^ (N + 2))
```

Adjust the Taylor sum to the exact convention already used by `HigherLaplaceDomain`.

No new fields should be needed for:

- coercivity,
- measurability,
- local-domain membership,
- Gaussian domination,
- the \(O(\|y\|^{N+2})\) remainder bound.

Those already come from `LocalLaplaceDomain` and `HigherLaplaceDomain`.

If the little-\(o\) theorem can be proved once from the existing `ContDiff` field, then make `ForwardExpansionDomain` a theorem-level abbreviation rather than a structure. But a one-field mixin is the Lean-cheapest reliable route.

## 3. Homogeneous exponent terms

Define

```lean
def exponentHomogeneousTerm (s : ℕ) (L : E → ℝ) (z : E) : ℝ :=
  taylorHomogeneousTerm (s + 2) L z
```

Thus

\[
V_s(z)=\frac{1}{(s+2)!}D^{s+2}L(0)[z,\ldots,z].
\]

The quadratic term should be bridged separately:

```lean
theorem taylorHomogeneousTerm_two_eq
    (D : ...) (z : E) :
    taylorHomogeneousTerm 2 D.L z = (1 / 2 : ℝ) * D.H z z
```

or in whatever quadratic-form notation the repository uses.

## 4. Scaled remainder

Define the normalized Taylor remainder:

```lean
def scaledTaylorRemainder
    (D : ForwardExpansionDomain N)
    (q : ℝ) (z : E) : ℝ :=
  q ^ (-(N + 2 : ℤ)) *
    (D.L (q • z) -
      ∑ m in Finset.range (N + 3),
        taylorHomogeneousTerm m D.L (q • z))
```

Using division rather than integer powers may simplify positivity obligations:

```lean
... / q ^ (N + 2)
```

Then prove, for `q ≠ 0`, the exact split:

```lean
theorem exponent_split
    (D : ForwardExpansionDomain N)
    (hq : q ≠ 0) :
    (D.L (q • z) - D.L 0) / q ^ 2
      =
      (1 / 2 : ℝ) * D.H z z
        + ∑ s in Finset.Icc 1 N,
            q ^ s * exponentHomogeneousTerm s D.L z
        + q ^ N * scaledTaylorRemainder D q z
```

It is often cleaner to index the middle sum as:

```lean
∑ s in Finset.range N, q ^ (s + 1) * V (s + 1) z
```

Key remainder lemmas:

```lean
theorem scaledTaylorRemainder_tendsto
    (D : ForwardExpansionDomain N)
    (z : E) :
    Tendsto
      (fun q => scaledTaylorRemainder D q z)
      (nhdsWithin 0 (Set.Ioi 0))
      (𝓝 0)
```

and a local polynomial bound:

```lean
theorem scaledTaylorRemainder_bound
    (D : ForwardExpansionDomain N) :
    ∃ C r > 0, ∀ q z,
      0 < q →
      ‖q • z‖ < r →
      |scaledTaylorRemainder D q z|
        ≤ C * ‖z‖ ^ (N + 2)
```

The latter follows directly from the existing `HigherLaplaceDomain` remainder bound.

## 5. No further “uniformity” field is needed

The combination

- pointwise convergence of `scaledTaylorRemainder D q z` to zero,
- its polynomial bound in \(z\),
- and mesoscopic localization,

is enough for dominated convergence. A separate uniform-in-\(z\) remainder field would be stronger than necessary.

---

# C. Exponential remainder and coefficient construction

## 1. Do not apply the \(e^{|R_q|}\) estimate globally

The scalar estimate

\[
\left|e^{-x}-\sum_{m=0}^{N}\frac{(-x)^m}{m!}\right|
 \le \frac{|x|^{N+1}}{(N+1)!}e^{|x|}
\]

is appropriate only after mesoscopic localization.

Globally, a bound such as

\[
e^{-c\|z\|^2}e^{qC\|z\|^{N+2}}
\]

need not be integrable. The existing coercivity controls the exact Boltzmann factor, but that cancellation is destroyed by replacing it with \(e^{|R_q|}\).

The correct order is:

1. localize to \(\|z\|\le q^{-1/2}\);
2. show the correction is small relative to \(\|z\|^2\);
3. apply the scalar exponential remainder;
4. dominate by a Gaussian with slightly weakened constant;
5. discard the complement by superpolynomial Gaussian tails.

## 2. Internal coefficient recursion

Avoid explicit multinomial collection. Define the coefficients of

\[
\exp\left(-\sum_{s\ge1}q^sV_s\right)
\]

recursively.

Let \(P_0=1\), and for \(j\ge1\),

\[
P_j(z)
=
-\frac1j\sum_{s=1}^{j}s\,V_s(z)P_{j-s}(z).
\]

Schematic Lean:

```lean
def expCorrectionCoeff
    (V : ℕ → E → ℝ) : ℕ → E → ℝ
  | 0 => fun _ => 1
  | j + 1 =>
      fun z =>
        -((j + 1 : ℝ)⁻¹) *
          ∑ s in Finset.Icc 1 (j + 1),
            (s : ℝ) * V s z *
              expCorrectionCoeff V (j + 1 - s) z
```

This recursion has several advantages:

- `P_j` visibly uses only `V₁, …, V_j`;
- hence it uses only derivatives through order `j+2`;
- polynomial-growth and measurability proofs are inductive;
- no multinomial indexing infrastructure is needed;
- it is compatible with the usual formal identity \(P'=-A'P\).

The public theorem need not mention this definition.

## 3. Scalar finite-expansion lemma

Prove a reusable scalar lemma before integration. In conceptual form:

```lean
theorem exp_graded_expansion
    {N : ℕ}
    (a : ℕ → ℝ)
    (ρ : ℝ → ℝ)
    (hρ : Tendsto ρ (nhdsWithin 0 (Set.Ioi 0)) (𝓝 0)) :
    (fun q =>
      Real.exp
        (-(∑ s in Finset.Icc 1 N, q ^ s * a s
            + q ^ N * ρ q))
        -
        ∑ j in Finset.range (N + 1),
          q ^ j * expCorrectionCoeffScalar a j)
      =o[nhdsWithin 0 (Set.Ioi 0)]
        (fun q => q ^ N)
```

The proof may use the ordinary Taylor remainder for `Real.exp`. The recursive coefficients are only the collection mechanism.

For integration, little-\(o\) alone is insufficient; also prove a quantitative companion. Its exact constants need not be elegant:

```lean
theorem exp_graded_remainder_bound
    {N : ℕ} :
    ∃ C K : ℕ, ∀ q a ρ,
      0 < q →
      q ≤ 1 →
      |∑ s in Finset.Icc 1 N, q ^ s * a s
          + q ^ N * ρ| ≤ η →
      |
        Real.exp (-(...))
          - ∑ j in Finset.range (N + 1),
              q ^ j * expCorrectionCoeffScalar a j
      |
      ≤ C * q ^ N *
          polynomialMajorant K a ρ * Real.exp η
```

In practice it may be easier to state the quantitative lemma already in the function-valued, mesoscopic form rather than inventing a general `polynomialMajorant`.

## 4. Mesoscopic correction bound

For the cutoff

\[
B_q=\{z:\|z\|\le q^{-1/2}\},
\]

prove:

```lean
theorem exponentCorrection_le_quadratic_on_meso
    (D : ForwardExpansionDomain N) :
    ∀ᶠ q in nhdsWithin 0 (Set.Ioi 0),
      ∀ z ∈ mesoscopicSet q,
        |exponentCorrection D N q z|
          ≤ (D.coercivityConstant / 2) * ‖z‖ ^ 2
```

The precise fraction can be `c/2`, `c/4`, etc.

The reason the fixed exponent \(1/2\) works for every finite order is:

\[
q^s\|z\|^{s+2}
=
\|z\|^2(q\|z\|)^s
\le
\|z\|^2q^{s/2}.
\]

For the Taylor remainder, the local little-\(o\) bound is uniform once
\(\|qz\|\le\sqrt q\to0\).

## 5. Integrated numerator expansion lemma

The main stage-3 interface should hide the scalar algebra:

```lean
theorem numerator_hasExpansion
    (D : ForwardExpansionDomain N)
    (α : MultiIndex d) :
    ∃ a : Fin (N + 1) → ℝ,
      (fun q =>
        rescaledNumerator D α q
          - ∑ j, a j * q ^ (j : ℕ))
        =o[nhdsWithin 0 (Set.Ioi 0)]
          (fun q => q ^ N)
```

Internally, take

\[
a_{\alpha,j}
=
\int z^\alpha
 e^{-H[z,z]/2}
 P_j(z)\,dz.
\]

It is useful to prove the internal formula, even if it is not the public API:

```lean
def numeratorCoeff
    (D : ForwardExpansionDomain N)
    (α : MultiIndex d)
    (j : Fin (N + 1)) : ℝ :=
  ∫ z,
    monomial α z *
      Real.exp (-(1 / 2) * D.H z z) *
      expCorrectionCoeff (fun s => V D s) j z
```

This gives jet-dependence essentially by simplification.

The denominator is the `α = 0` case. Stage 4 can then use a generic finite-division lemma for asymptotic polynomials whose constant denominator coefficient is nonzero.

## 6. Recommended route

Use:

- the recursive `P_j` packaging for coefficient collection;
- the ordinary scalar exponential Taylor remainder for estimates;
- a single proof for arbitrary `N`.

Do **not** recurse on the whole Laplace theorem “one order at a time.” That would repeatedly reopen localization, domination, integration, and denominator division. The recursion should be confined to the algebraic coefficient object.

---

# D. Minimal stage-1 infrastructure tide

The first tide should be entirely independent of Taylor expansion. It should establish the cutoff and outer-tail mechanism needed by all later stages.

Define, for positive \(q\),

```lean
def mesoscopicSet (q : ℝ) : Set E :=
  {z | ‖z‖ ≤ (Real.sqrt q)⁻¹}
```

Equivalent formulations such as `Real.sqrt q * ‖z‖ ≤ 1` may avoid inverse side conditions.

## 1. Gaussian-polynomial integrability

This may already exist, but expose the exact reusable statement:

```lean
theorem integrable_norm_pow_mul_gaussian
    (p : ℕ) {c : ℝ} (hc : 0 < c) :
    Integrable
      (fun z : E => ‖z‖ ^ p * Real.exp (-c * ‖z‖ ^ 2))
```

If the project only works over `EuclideanSpace`, specialize there rather than generalizing prematurely.

## 2. Gaussian tail is superpolynomial at the mesoscopic radius

Core statement:

```lean
theorem gaussianPolynomial_tail_isLittleO
    (p M : ℕ) {c : ℝ} (hc : 0 < c) :
    (fun q =>
      ∫ z in (mesoscopicSet q)ᶜ,
        ‖z‖ ^ p * Real.exp (-c * ‖z‖ ^ 2))
      =o[nhdsWithin 0 (Set.Ioi 0)]
        (fun q : ℝ => q ^ M)
```

If proving this directly is awkward, split it into:

```lean
theorem gaussianPolynomial_tail_bound :
  ∃ C K, ∀ R ≥ 1,
    ∫ z in {z | R ≤ ‖z‖},
      ‖z‖ ^ p * exp (-c * ‖z‖^2)
      ≤ C * R ^ K * exp (-(c / 2) * R ^ 2)
```

and then invoke the existing `Anchoring.SuperPoly` result with
\(R=q^{-1/2}\), giving an \(e^{-c'/q}\) bound.

## 3. Transfer to the existing rescaled integrand

Using coercivity and the indicator already built into `LocalLaplaceDomain.integrand`:

```lean
theorem integrand_outer_isLittleO
    (D : LocalLaplaceDomain E)
    (p M : ℕ) :
    (fun q =>
      ∫ z in (mesoscopicSet q)ᶜ,
        ‖z‖ ^ p * D.integrand q z)
      =o[nhdsWithin 0 (Set.Ioi 0)]
        (fun q : ℝ => q ^ M)
```

If `integrand` can be signed, state the norm/absolute-value version:

```lean
∫ z in ..., ‖z‖ ^ p * ‖D.integrand q z‖
```

This is the main stage-1 theorem later used for every monomial numerator and for the denominator.

There is no need to first formulate this for the unrescaled integral. The existing dilation identity can transport it back. The rescaled statement is exactly what stages 2–3 need.

## 4. Cutoff eventually lies in every fixed Taylor ball

```lean
theorem smul_mem_ball_on_mesoscopic
    {r : ℝ} (hr : 0 < r) :
    ∀ᶠ q in nhdsWithin 0 (Set.Ioi 0),
      ∀ z ∈ mesoscopicSet q,
        ‖q • z‖ < r
```

This follows from

\[
\|qz\|\le q/\sqrt q=\sqrt q.
\]

This lemma is what allows the local Taylor remainder bound to be used uniformly on the cutoff.

## 5. Cutoff tends pointwise to one

```lean
theorem eventually_mem_mesoscopicSet (z : E) :
    ∀ᶠ q in nhdsWithin 0 (Set.Ioi 0),
      z ∈ mesoscopicSet q
```

Consequently:

```lean
theorem indicator_mesoscopic_tendsto (z : E) :
    Tendsto
      (fun q => (mesoscopicSet q).indicator f z)
      (nhdsWithin 0 (Set.Ioi 0))
      (𝓝 (f z))
```

The latter may be unnecessary if the eventual-membership lemma simplifies DCT goals directly.

## What should not be in tide 1

Do not yet add:

- Taylor-term definitions;
- exponential Taylor estimates;
- universal coefficient recursion;
- numerator expansions;
- finite division.

Those belong to stages 2–4. Tide 1 should end once arbitrary polynomial observables can be cut to the mesoscopic region with a superpolynomial error.

---

## Proposed implementation order

1. `AsymptoticPolynomial`: expansion predicate and coefficient uniqueness.
2. `GaussianMeso`: mesoscopic cutoff, Gaussian-polynomial tails, coercivity transfer.
3. `ForwardExpansionDomain`: Peano remainder and exact exponent split.
4. `ExpGraded`: recursive `P_j`, scalar expansion, polynomial-growth lemmas.
5. `NumeratorExpansion`: localized DCT plus outer-tail removal.
6. `AsymptoticDivision`: denominator and quotient.
7. `ForwardCoefficients`: existential public theorem and jet-comparison theorem.

This preserves the desired public design—existence and finite-jet determination—while retaining enough explicit internal structure to make the Lean proof tractable.