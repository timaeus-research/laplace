1. **Pointwise quadratic rescaling**

### Recommended route

For the pointwise statement at a fixed `x`, reuse the one-dimensional ray reduction already used in `SmoothRecovery`:

```lean
def ray (L : EuclidD d → ℝ) (x : EuclidD d) : ℝ → ℝ :=
  fun q => L (q • x)
```

Then apply the one-variable Taylor API to `ray L x`. The relevant Mathlib identifier is:

```lean
taylor_isLittleO
```

from `Mathlib.Analysis.Calculus.Taylor`.

The associated one-variable derivative objects are:

```lean
iteratedDeriv
ContDiffAt.iteratedDeriv
```

and composition regularity is normally obtained through:

```lean
ContDiffAt.comp
ContDiff.contDiffAt
ContinuousLinearMap.contDiff
```

For hand-computed derivatives, the basic chain-rule identifiers are:

```lean
HasFDerivAt.comp
HasFDerivAt.hasDerivAt
```

The exact invocation of `taylor_isLittleO` has somewhat elaborate arguments, so I would copy the invocation pattern from `SmoothRecovery` rather than introduce `FormalMultilinearSeries` solely for this theorem.

The desired ray expansion is:

```lean
(fun q =>
    L (q • x) - L 0
      - q * DL x
      - q ^ 2 / 2 * D2 (fun _ : Fin 2 => x))
  =o[𝓝 0] fun q => q ^ 2
```

where

```lean
DL : EuclidD d →L[ℝ] ℝ
D2 : EuclidD d [×2]→L[ℝ] ℝ
```

are the first and second Fréchet derivatives at zero. Under `DL = 0`, this gives

```lean
Tendsto
  (fun q => (L (q • x) - L 0) / q ^ 2)
  (𝓝[>] 0)
  (𝓝 ((1 / 2 : ℝ) * D2 (fun _ : Fin 2 => x)))
```

and then the Hessian bridge turns the target into `qform H x / 2`.

### Why not start with `FormalMultilinearSeries`?

The formal Taylor-series API is useful when constructing a reusable multivariate Peano theorem, but it is considerably more expensive to set up. The relevant namespace revolves around:

```lean
FormalMultilinearSeries
HasFTaylorSeriesUpTo
```

For the fixed-ray limit, it buys little over the existing one-dimensional proof.

There is an important qualification: the ray argument proves the limit for each fixed `x`, but by itself does **not** give a uniform quadratic remainder in all directions. Consequently, it is sufficient for H3(a), but not the best basis for H3(b).

### Hessian representation

I recommend taking the continuous bilinear form as the primary analytic Hessian and deriving the matrix:

```lean
abbrev HessianForm (d : ℕ) :=
  EuclidD d [×2]→L[ℝ] ℝ

noncomputable def hessianMatrix
    (B : HessianForm d) : Matrix (Fin d) (Fin d) ℝ :=
  fun i j => B ![e i, e j]
```

Here `e i` can simply be defined explicitly to avoid basis API friction:

```lean
def e (i : Fin d) : EuclidD d :=
  fun j => if j = i then 1 else 0
```

The bridge you want is:

```lean
theorem diagonal_hessian_eq_qform
    (B : HessianForm d)
    (H : Matrix (Fin d) (Fin d) ℝ)
    (hH : ∀ i j, H i j = B ![e i, e j])
    (x : EuclidD d) :
    B (fun _ : Fin 2 => x) = qform H x := by
  -- expand x in coordinates, then use bilinearity
```

Equivalently, avoid exposing the coordinate proof downstream and store directly:

```lean
hessian_diag :
  ∀ x, D2 (fun _ : Fin 2 => x) = qform H x
```

This is often the least brittle interface.

The matrix convention

```lean
H i j = D2 ![e i, e j]
```

is correct. Since the second Fréchet derivative of a scalar `C²` map is symmetric, the resulting matrix is symmetric. Do check the orientation of `qform` once—whether it expands as `x ⬝ᵥ H.mulVec x` or the transposed convention—but symmetry makes the final diagonal expression insensitive to that choice.

A useful exported formulation of H3(a) is:

```lean
theorem rescaled_loss_tendsto
    (x : EuclidD d) :
    Tendsto
      (fun q => (L (q • x) - L 0) / q ^ 2)
      (𝓝[>] (0 : ℝ))
      (𝓝 ((1 / 2 : ℝ) * qform H x))
```

Using `𝓝[>] 0`, i.e.

```lean
nhdsWithin 0 (Set.Ioi 0)
```

also makes `q ≠ 0` eventually automatic.

---

2. **Nondegenerate lower bound**

### Best mathematical organization

The clean intermediate result is a genuinely multivariate Peano expansion:

```lean
(fun y =>
    L y - L 0 - (1 / 2 : ℝ) * qform H y)
  =o[𝓝 0]
(fun y : EuclidD d => ‖y‖ ^ 2)
```

assuming `DL(0) = 0`.

From this and coercivity

```lean
0 < λ
∀ y, λ * ‖y‖ ^ 2 ≤ qform H y
```

choose the little-`o` error smaller than `λ / 4`. Eventually,

```lean
|L y - L 0 - (1 / 2) * qform H y|
  ≤ (λ / 4) * ‖y‖ ^ 2
```

and hence

```lean
(λ / 4) * ‖y‖ ^ 2 ≤ L y - L 0.
```

Substituting `y = q • x` and dividing by `q²` gives:

```lean
(λ / 4) * ‖x‖ ^ 2
  ≤ (L (q • x) - L 0) / q ^ 2
```

for positive `q` whenever `‖q • x‖` is sufficiently small.

This avoids eigenvalue calculations inside the local Taylor proof.

### Coercivity versus “smallest eigenvalue”

Although `H.PosDef` implies the existence of such a `λ` in finite dimension, proving the quantitative bound via the smallest eigenvalue can itself become a substantial Lean detour. I recommend exporting or separately proving:

```lean
∃ λ : ℝ, 0 < λ ∧
  ∀ x : EuclidD d, λ * ‖x‖ ^ 2 ≤ qform H x
```

and letting the local Taylor lemma consume it.

This can later be connected to `Matrix.PosDef` once, in a dedicated matrix/coercivity lemma. It is a better interface than making every local asymptotics proof unfold spectral theory.

### Quantitative Taylor APIs

The named Taylor remainder results are:

```lean
taylor_mean_remainder_bound
taylor_mean_remainder_bound_iteratedDeriv
```

These are principally one-variable Taylor results. There is not an equally convenient turnkey theorem saying:

> on a normed-space ball, continuity of the second Fréchet derivative gives a quadratic multivariate remainder estimate.

One can prove that by restricting to each segment and using the one-dimensional theorem. For fixed `y`, set:

```lean
g t := L (t • y)
```

Then continuity of `D²L` on a ball gives, uniformly for `t ∈ [0,1]`,

```lean
|g'' t - qform H y| ≤ ε * ‖y‖ ^ 2.
```

Applying the one-dimensional remainder estimate at `t = 1` gives the required bound.

The general mean-value inequality often useful for such proofs is:

```lean
Convex.norm_image_sub_le_of_norm_fderiv_le
```

but proving the second-order estimate by applying a first-order mean-value inequality twice involves substantial derivative-map plumbing.

### Recommendation

Split the result into two layers:

```lean
/-- Analytic theorem: C² plus the Hessian identification gives a
multivariate quadratic Peano remainder. -/
theorem quadratic_peano_of_contDiffAt_two ...

/-- Easy order-theoretic consequence of Peano remainder plus coercivity. -/
theorem local_quadratic_lower_bound_of_peano ...
```

If the multivariate Peano theorem begins consuming too much time, it is entirely reasonable for H4 initially to **take the lower bound as a hypothesis**. H4 does not need to know how it was derived.

In particular, deriving the lower bound from `C²` is likely the hardest API-sensitive part of H3. H4 should not be blocked on it.

### Domain caveat

A lower bound valid only when

```lean
‖q • x‖ ≤ δ
```

does not dominate an integral with indicator `1_U (q • x)` unless membership in `U` implies this norm bound. Thus H4 needs one of:

```lean
U ⊆ Metric.closedBall 0 δ
```

or, more directly,

```lean
q • x ∈ U →
  c * ‖x‖ ^ 2 ≤ (L (q • x) - L 0) / q ^ 2.
```

If `U` extends outside the local ball, local nondegeneracy alone is insufficient for the advertised global Gaussian dominator. One then needs additional assumptions such as compactness/boundedness of `U`, uniqueness of the minimum, and a positive gap away from the local ball.

---

3. **Hypothesis packaging**

I suggest separating the intrinsic local quadratic information from the domain/integration information.

### H3: intrinsic quadratic approximation

```lean
structure LocalQuadraticApprox
    {d : ℕ}
    (L : EuclidD d → ℝ)
    (H : Matrix (Fin d) (Fin d) ℝ) where
  hH_posDef : H.PosDef

  /-- A quantitative coercivity form, avoiding spectral API downstream. -/
  lambda : ℝ
  lambda_pos : 0 < lambda
  qform_lower :
    ∀ x : EuclidD d,
      lambda * ‖x‖ ^ 2 ≤ qform H x

  /-- Stronger than the fixed-ray result and sufficient for the lower bound. -/
  quadratic_peano :
    (fun y =>
        L y - L 0 - (1 / 2 : ℝ) * qform H y)
      =o[𝓝 0]
    (fun y : EuclidD d => ‖y‖ ^ 2)
```

Then derive, rather than store:

```lean
LocalQuadraticApprox.rescaled_tendsto
LocalQuadraticApprox.exists_local_lower_bound
```

with statements resembling:

```lean
theorem rescaled_tendsto
    (A : LocalQuadraticApprox L H)
    (x : EuclidD d) :
    Tendsto
      (fun q => (L (q • x) - L 0) / q ^ 2)
      (𝓝[>] (0 : ℝ))
      (𝓝 ((1 / 2 : ℝ) * qform H x))
```

and

```lean
theorem exists_local_lower_bound
    (A : LocalQuadraticApprox L H) :
    ∃ δ c : ℝ,
      0 < δ ∧ 0 < c ∧
      ∀ {q : ℝ} {x : EuclidD d},
        0 < q →
        ‖q • x‖ ≤ δ →
        c * ‖x‖ ^ 2
          ≤ (L (q • x) - L 0) / q ^ 2
```

If proving `quadratic_peano` immediately is undesirable, an initial weaker structure can store `rescaled_tendsto` and `local_lower` directly.

### H4: integration domain and domination

```lean
structure LocalLaplaceDomain
    {d : ℕ}
    (L : EuclidD d → ℝ)
    (H : Matrix (Fin d) (Fin d) ℝ)
    extends LocalQuadraticApprox L H where
  U : Set (EuclidD d)
  measurableSet_U : MeasurableSet U

  delta : ℝ
  delta_pos : 0 < delta

  ball_subset_U :
    Metric.ball (0 : EuclidD d) delta ⊆ U

  /-- Needed if the local lower bound is to dominate the whole
  indicator-supported integrand. -/
  U_subset_closedBall :
    U ⊆ Metric.closedBall 0 delta

  measurable_L : Measurable L
```

An even cleaner H4-facing field is the exact bound it consumes:

```lean
  c : ℝ
  c_pos : 0 < c

  rescaled_lower :
    ∀ {q : ℝ} {x : EuclidD d},
      0 < q →
      q • x ∈ U →
      c * ‖x‖ ^ 2
        ≤ (L (q • x) - L 0) / q ^ 2
```

Then `U_subset_closedBall` need not be exposed at all.

### Generic H4 theorem

Do not prove three independent dominated-convergence arguments. Use a generic test function with quadratic growth:

```lean
theorem tendsto_indicator_rescaled_integral
    (A : LocalLaplaceDomain L H)
    (h : EuclidD d → ℝ)
    (h_cont : Continuous h)
    (C : ℝ)
    (hC : 0 ≤ C)
    (h_growth :
      ∀ x, |h x| ≤ C * (1 + ‖x‖ ^ 2)) :
    Tendsto
      (fun q =>
        ∫ x,
          A.U.indicator
            (fun x =>
              h x *
                Real.exp
                  (-((L (q • x) - L 0) / q ^ 2)))
            x)
      (𝓝[>] (0 : ℝ))
      (𝓝
        (∫ x,
          h x * Real.exp (-((1 / 2 : ℝ) * qform H x))))
```

Then specialize to:

```lean
fun _ => 1
fun x => x i
fun x => x i * x j
```

The elementary coordinate bounds are:

```lean
|x i| ≤ ‖x‖
|x i * x j| ≤ ‖x‖ ^ 2
```

so all three fit the same growth hypothesis.

For the DCT step, the filter-indexed theorem is:

```lean
MeasureTheory.tendsto_integral_filter_of_dominated_convergence
```

The pointwise indicator convergence follows from:

```lean
Metric.ball 0 δ ⊆ U
```

because for fixed `x`,

```lean
q • x → 0
```

as `q → 0+`, so eventually `q • x ∈ U`.

The domination is:

```lean
|indicator U (...) x|
  ≤ C * (1 + ‖x‖ ^ 2) * Real.exp (-c * ‖x‖ ^ 2).
```

Its integrability should be packaged once using the H2 Gaussian integrability results, dilation, and the polynomial-moment estimates.

---

4. **Tide staging**

Use separate tides.

### Tide H3a: fixed-ray asymptotics and Hessian bridge

Deliver:

- ray restriction `q ↦ L (q • x)`;
- use of `taylor_isLittleO`;
- computation of first and second ray derivatives;
- bridge from `D²L(0)[x,x]` to `qform H x`;
- `rescaled_tendsto`.

This is relatively contained, especially because `SmoothRecovery` already supplies a local pattern.

### Tide H3b: uniform Peano estimate and local lower bound

Deliver:

- multivariate quadratic Peano remainder, or a segmentwise uniform remainder theorem;
- coercivity of `qform H`;
- extraction of `δ` and `c`;
- the rescaled lower bound.

This is the hardest step. The likely API mismatch is that Mathlib’s most accessible Taylor remainder lemmas are one-dimensional, while the needed conclusion is uniform over directions in a normed space. The second likely friction point is obtaining a quantitative coercivity constant from `Matrix.PosDef`.

### Tide H4: generic dominated convergence

Deliver:

- measurable rescaled indicator integrands;
- eventual pointwise convergence;
- one polynomial-times-Gaussian dominator;
- the generic quadratic-growth test-function theorem;
- corollaries for `1`, `x i`, and `x i * x j`;
- rewriting the target integrals using the H2 values.

H4 is conceptually routine once the exact support-wide lower bound is available. Its probable API friction is measurability of `Set.indicator` compositions and matching the filter-indexed DCT theorem, but this is much less mathematically difficult than H3b.

So I would not combine H3 and H4 into one tide. The best sequence is:

1. H3a: pointwise rescaling;
2. H3b: uniform lower bound;
3. H4: generic dominated convergence and moment corollaries.