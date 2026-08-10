## Short answer

For one tide, I recommend **a package-derivation wrapper that assumes the fixed-ball Taylor remainder bounds** and derives everything else from the existing `quadratic_peano` and `exists_local_lower_bound`.

Do **not** include the general `C^k ⇒` fixed-ball multivariate Taylor bound in the same tide. That is mathematically routine but likely the only API-fragile part: Mathlib’s useful Taylor machinery is primarily one-dimensional, and the radial iterated-derivative bridge will probably need a custom induction.

There is also an important scoping constraint:

> `HigherLaplaceDomain k` stores global `ContDiff ℝ k L`, and `LocalLaplaceDomain` stores global `Measurable L`.

Thus `ContDiffAt ℝ k L 0` alone cannot construct the current structures. The input needs global smoothness, e.g.
```lean
∀ k : ℕ, ContDiff ℝ k L
```
or `ContDiff ℝ ∞ L`, unless the structures are weakened to local regularity.

---

# A. Minimal lemma stack

## 1. Constructing `LocalQuadraticApprox`

The cheapest route is to reuse the already-proved:

```lean
quadratic_peano
  (hL : ContDiff ℝ 2 L)
  (hgrad : fderiv ℝ L 0 = 0)
```

It returns the remainder for `hessianMatrix L`. Therefore formulate the order-two matching hypothesis in one of these convenient forms:

```lean
hdiag : ∀ y, qform (hessianMatrix L) y = qform H y
```

or

```lean
hdiag : ∀ y, hess L y y = qform H y
```

The second form transfers using `hess_apply_self`.

Then:

1. obtain Peano for `hessianMatrix L`;
2. rewrite the quadratic term using `hdiag`;
3. obtain `lambda`, positivity, and the form lower bound from
   ```lean
   qform_coercive hH
   ```
4. assemble `LocalQuadraticApprox L H`.

No new second-order Taylor theorem is needed.

### About `ContDiffAt 2`

I would not plan around an off-the-shelf Mathlib theorem of exactly the form

```lean
L y - L 0 - fderiv ... - iteratedFDeriv ... / 2
  = o[𝓝 0] ‖y‖²
```

with the project’s `iteratedFDeriv`/`taylorHomogeneousTerm` normalization. There is Taylor infrastructure, but the exact multivariate Peano statement and coefficient bridge are not reliably a one-line API.

Moreover, even if proved from `ContDiffAt`, that would not fill the global `ContDiff` and `Measurable` fields downstream. For the current structures, reuse the existing global-`ContDiff` `quadratic_peano`.

---

## 2. Local lower bound and the quantifier shape

Yes: the desired `rescaled_lower` follows directly from an unrescaled bound on the chosen ball.

Suppose:

```lean
∀ y ∈ U, c * ‖y‖ ^ 2 ≤ L y - L 0
```

Let `y = q • x`, with `q > 0` and `q • x ∈ U`. Then

```text
c ‖q • x‖² ≤ L(q • x) - L(0)
c q² ‖x‖² ≤ L(q • x) - L(0)
c ‖x‖² ≤ (L(q • x) - L(0)) / q².
```

Since `q² > 0`, the division step is immediate.

Even cheaper, use the existing theorem:

```lean
A.exists_local_lower_bound
```

which produces `δ,c > 0` and

```lean
0 < q → ‖q • x‖ ≤ δ →
  c * ‖x‖ ^ 2 ≤ (L (q • x) - L 0) / q ^ 2
```

Then choose

```lean
U := Metric.ball 0 ρ
```

with `ρ ≤ δ`. Membership gives `‖q • x‖ < ρ ≤ δ`, hence the theorem applies.

The existing proof gives the expected constant:

```text
qform H y / 2 ≥ λ ‖y‖² / 2
|remainder y| ≤ λ ‖y‖² / 4
⇒ L y - L 0 ≥ λ ‖y‖² / 4.
```

So `c := λ / 4`.

---

## 3. Assembling `LocalLaplaceDomain`

Given a Taylor radius `rₖ` and lower-bound radius `δ`, choose for example

```lean
ρ := min δ rₖ
U := Metric.ball 0 ρ
```

Both inputs are positive, so `ρ > 0`.

Fields are then:

```lean
U := Metric.ball 0 ρ
measurableSet_U := measurableSet_ball
delta := ρ
delta_pos := ...
ball_subset_U := Set.Subset.rfl
c := c_lower
c_pos := ...
rescaled_lower := lower bound restricted using ρ ≤ δ
measurable_L := (hcont k).continuous.measurable
```

Using the same `ρ` for `U`, `delta`, and `taylorRadius` makes both inclusion fields reflexive:

```lean
ball_subset_U := Set.Subset.rfl
taylorBall_subset := Set.Subset.rfl
```

The Taylor estimate originally available on the larger radius `rₖ` is restricted via `ρ ≤ rₖ`.

---

## 4. Fixed-ball Taylor remainder from `C^k`

The standard mathematical route is exactly the radial one.

For fixed `y`, define

```lean
g t := L (t • y).
```

One needs the identity

```lean
iteratedDeriv k g t
  = iteratedFDeriv ℝ k L (t • y) (fun _ ↦ y)
```

up to the precise application syntax for `ContinuousMultilinearMap`.

Then one-dimensional Taylor–Lagrange on `[0,1]` gives

```text
|L y - Σ_{j<k} taylorHomogeneousTerm j L y|
  ≤ (sup_{z ∈ closedBall 0 r} ‖iteratedFDeriv ℝ k L z‖ / k!) ‖y‖^k.
```

The derivative bound comes from:

1. continuity of `z ↦ iteratedFDeriv ℝ k L z`;
2. compactness of `closedBall 0 r` in finite-dimensional `EuclidD d`;
3. the multilinear operator-norm estimate
   ```text
   ‖D^kL(z)(y,…,y)‖ ≤ ‖D^kL(z)‖ ‖y‖^k.
   ```

### Likely missing/API-fragile pieces

I would expect at least one custom lemma here:

1. **Radial iterated derivative identity.**  
   A first-derivative chain rule is standard. The exact arbitrary-order theorem, in the required `iteratedFDeriv` representation, is unlikely to be available under a ready-to-use theorem name. An induction is probably needed.

2. **Coefficient identification.**  
   You must show the scalar Taylor coefficient
   ```lean
   iteratedDeriv j g 0 / j!
   ```
   is exactly
   ```lean
   taylorHomogeneousTerm j L y.
   ```
   This should follow from the radial identity and the definition, but often requires normalization rewrites.

3. **Uniform norm bound on the closed ball.**  
   Compactness and continuity are present, but finding the exact theorem chain for
   `iteratedFDeriv` continuity and extracting a real constant may require some API work.

4. **Taylor theorem indexing.**  
   `range k` means terms `0,…,k-1`, so the remainder uses derivative order `k`. The relevant one-dimensional theorem may be parameterized by `k - 1`; this tends to introduce arithmetic bookkeeping.

There may be a direct norm-Taylor theorem in the calculus library, but even then it is likely to reduce internally to a segment/ray and may not line up directly with this project’s `taylorHomogeneousTerm`. I would not make the tide depend on finding such a theorem.

---

# B. Estimated Lean effort

These estimates assume the current project lemmas and structures remain unchanged.

| Component | Estimate | Risk |
|---|---:|---|
| Transfer `quadratic_peano` from `hessianMatrix L` to `H` using diagonal equality | 5–15 lines | Low |
| Assemble `LocalQuadraticApprox L H` | 10–20 lines | Low |
| Invoke `exists_local_lower_bound` and choose a smaller radius | 5–15 lines | Low |
| Assemble `LocalLaplaceDomain` with `U = ball 0 ρ` | 20–40 lines | Low |
| Restrict an assumed Taylor bound to the smaller ball | 5–15 lines | Low |
| Assemble one `HigherLaplaceDomain k` | 15–30 lines | Low |
| Package as `∀ k, 2 < k → HigherLaplaceDomain k L H` | 10–25 lines | Low |
| **Total wrapper assuming Taylor bounds** | **60–120 lines** | **Low** |
| Radial first-derivative lemma | 10–20 lines | Medium |
| Arbitrary-order radial iterated-derivative identity | 30–80 lines | Medium/high |
| Scalar Taylor coefficient identification | 15–40 lines | Medium |
| Compact-ball bound for `iteratedFDeriv k` | 25–60 lines | Medium |
| Full `C^k` fixed-ball Taylor bound | 70–160 additional lines | High/API-sensitive |
| Local analytic power-series route | 100–250 lines | High unless bridge lemmas already exist |

The radial proof can become substantially longer if coercions between continuous linear maps, continuous multilinear maps, and iterated derivative application do not simplify cleanly.

---

# C. Options, ranked

## 1. Assume the Taylor bounds; derive the packages

### Suggested hypothesis

```lean
hcont : ∀ k : ℕ, ContDiff ℝ k L

htaylor : ∀ k : ℕ, 2 < k →
  ∃ r C : ℝ,
    0 < r ∧ 0 ≤ C ∧
    ∀ y ∈ Metric.ball (0 : EuclidD d) r,
      |L y - ∑ j ∈ Finset.range k,
          taylorHomogeneousTerm j L y| ≤
        C * ‖y‖ ^ k
```

together with:

```lean
hgrad : fderiv ℝ L 0 = 0
hdiag : ∀ y, qform (hessianMatrix L) y = qform H y
hH : H.PosDef
```

Then produce:

```lean
∀ k, 2 < k → HigherLaplaceDomain k L H
```

This is the best one-tide scope. It exercises the package wiring, radius shrinking, coercivity, and measurable/smooth fields without opening the fragile Taylor-calculus subproject.

**Rank: 1 — recommended.**

---

## 2. Prove a reusable radial `C^k` Taylor-bound theorem

A subsequent tide can establish something like:

```lean
theorem exists_taylorRemainder_bound
    (hL : ContDiff ℝ k L) :
    ∃ r C, 0 < r ∧ 0 ≤ C ∧
      ∀ y ∈ Metric.ball 0 r,
        |L y - ∑ j ∈ Finset.range k,
            taylorHomogeneousTerm j L y| ≤ C * ‖y‖ ^ k
```

In fact, global `ContDiff ℝ k L` should permit this for any fixed positive radius, with a radius-dependent `C`.

The clean implementation plan is:

1. radial iterated-derivative identity;
2. one-dimensional Taylor–Lagrange;
3. compact closed-ball derivative bound;
4. operator-norm estimate.

This gives the strongest general constructor but is a distinct engineering task.

**Rank: 2 — best mathematical follow-up, not best current scope.**

---

## 3. Use `AnalyticAt`

Mathematically, `AnalyticAt ℝ L 0` gives a convergent local power series, and a geometric majorant yields every finite-order remainder bound on a sufficiently small ball.

However, for the current structures it has two disadvantages:

1. `AnalyticAt` is local, while `HigherLaplaceDomain` requires global
   ```lean
   ContDiff ℝ k L
   ```
   and `Measurable L`.

2. The power-series coefficients must be identified with
   ```lean
   iteratedFDeriv ℝ j L 0 / j!
   ```
   and hence with `taylorHomogeneousTerm`. Even if Mathlib has much of this bridge, the exact API can be costly.

If the capstone already provides both global smoothness and an analytic expansion with coefficients in the project’s preferred form, this route becomes more attractive. Otherwise it is not cheaper than the radial proof.

**Rank: 3 — use only if the analytic coefficient bridge is already available.**

---

# Recommended tide boundary

Implement one noncomputable wrapper along these lines:

```lean
noncomputable def higherLaplaceDomainFamilyOfTaylorBounds
    (hcont : ∀ k : ℕ, ContDiff ℝ k L)
    (hgrad : fderiv ℝ L 0 = 0)
    (hdiag : ∀ y, qform (hessianMatrix L) y = qform H y)
    (hH : H.PosDef)
    (htaylor : ∀ k, 2 < k →
      ∃ r C, 0 < r ∧ 0 ≤ C ∧
        ∀ y ∈ Metric.ball 0 r,
          |L y - ∑ j ∈ Finset.range k,
              taylorHomogeneousTerm j L y| ≤ C * ‖y‖ ^ k) :
    ∀ k, 2 < k → HigherLaplaceDomain k L H
```

Internally:

1. build `LocalQuadraticApprox L H` once;
2. obtain its local lower-bound radius and constant once;
3. for each `k`, choose Taylor data;
4. set `ρ := min lowerRadius taylorRadius`;
5. use `U := Metric.ball 0 ρ`;
6. restrict both estimates to that ball;
7. assemble `HigherLaplaceDomain`.

That scope is small, robust, and directly composes with `tendsto_local_rate_integral`. The general `C^k`/analytic derivation of `htaylor` should be a separate tide.