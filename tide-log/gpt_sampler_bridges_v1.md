## 1. Correctness and hypotheses

**M1–M3 are correct**, with one important correction to the suggested square-root proof of M1, and one qualification about the convergence conclusion.

Let `ι` be finite with decidable equality, and let `E := EuclideanSpace ℝ ι`.

### M1

For every `c : ℝ`,
```lean
(stdGaussian E).map (fun ξ => c • ξ)
  = multivariateGaussian 0 ((c ^ 2) • (1 : Matrix ι ι ℝ))
```
is correct. No sign condition on `c` is needed.

However,
```lean
CFC.sqrt (c ^ 2 • 1) = c • 1
```
is **false for negative `c`** in nonzero dimension. The square root is `|c| • 1`. Thus a proof through the definition either assumes `0 ≤ c` or additionally uses the symmetry of the standard Gaussian.

### M2

```lean
(μ.prod (multivariateGaussian 0 R)).map
    (fun p => euclid A p.1 + p.2)
  = gaussStep A R μ
```
is correct. Probability is a convenient sufficient assumption on `μ`; the identity itself is measure-theoretic and can be proved at greater generality, subject to the hypotheses of the product-map API.

No positive-semidefiniteness assumption on `R` is needed for this identity: it only manipulates the measure already named `multivariateGaussian 0 R`. Positive-semidefiniteness matters when asserting that its covariance is actually `R`.

### M3

The intended statement needs
```lean
hh : 0 ≤ h
```
and follows from M1 and M2 using
```lean
Real.sq_sqrt (show 0 ≤ 2 * h by positivity)
```
to identify the covariance.

The sampling-law identity holds at `h = 0`. **The convergence conclusion generally does not.** To invoke the existing ULA convergence theorem, retain all its stability assumptions on `A`, or equivalently the appropriate restrictions on `h` and the precision matrix.

Also, applying M3 successively to implemented random variables requires that each fresh noise be independent of the current state. Independence from the whole past is a standard sufficient condition.

### B

B is correct. I would state it with:

- `[IsProbabilityMeasure P]`;
- `hη : ∀ c k, MemLp (η c k) 2 P`;
- the stated second-moment table;
- `0 < C` and `0 < N`;
- the hypotheses required by the existing closed-form theorem, presumably `|ρ| < 1`;
- exactly the existing definitions of `σ²`, `R₁`, `R₂`, and `T_N`, with `σ² = v / (1 - ρ²)`.

Separate **bridge hypotheses** from **closed-form hypotheses**: the L² construction and expectation identity do not themselves need `|ρ| < 1`. That restriction belongs to the downstream AR(1) formula. Likewise, `P` being a probability measure is not needed for the basic L² bridge, though it makes “expected variance” and the independence corollary natural.

The moment table does **not** need a separate centring assumption. It already supplies all inner products used in the proof. Centring is needed for the proposed independence-based sufficient condition, not for B itself.

Two details deserve attention:

1. This is the pooled variance with denominator `C * N`, not the Bessel-corrected statistic.
2. Your `AR1Chain` orthogonality field apparently includes innovation index `0`. Although the recurrence never uses `η 0`, setting it to zero would violate the diagonal condition when `v ≠ 0`. Keep a genuine innovation at index zero, or deliberately revise the structure’s indexing.

## 2. M1: prefer characteristic functions

I would use characteristic functions, particularly since the existing Gaussian and convergence development already uses them.

The proof has three steps:

1. The mapped measure has characteristic function obtained from
   ```lean
   charFun_map_smul
   charFun_stdGaussian
   ```
2. The existing characteristic-function formula for `multivariateGaussian` gives the same result: its mean is zero and the covariance quadratic form is
   \[
   \langle t,(c^2I)t\rangle=c^2\|t\|^2.
   \]
3. Apply
   ```lean
   Measure.ext_of_charFun
   ```

This route handles negative `c` and `c = 0` uniformly and avoids matrix square-root normalization.

**API caveat:** I cannot check the supplied Mathlib pin here. Treat the proof layouts below as layouts rather than compiled scripts; in particular, check namespace, argument order, and measurable versus a.e.-measurable arguments locally.

If the multivariate-Gaussian characteristic-function theorem requires positive-semidefiniteness, supply it for `(c ^ 2) • 1`. That is a small algebraic side lemma, not a substantive obstruction.

### Why not `IsGaussian.ext`?

It is also a good proof, especially if you already have packaged lemmas for the mean and covariance of linear images. But it requires coordinating:

- Gaussianity of the scalar image;
- its mean;
- `covarianceBilin_map`;
- `covarianceBilin_stdGaussian`;
- the corresponding mean and covariance facts for `multivariateGaussian`.

That is more moving parts than equality of characteristic functions in this particular development.

### When the definition-based route is attractive

If you only wanted the nonnegative scaling used by M3, you could prove
```lean
0 ≤ c →
  (stdGaussian E).map (fun ξ => c • ξ)
    = multivariateGaussian 0 ((c ^ 2) • 1)
```
by simplifying the positive square root, then the associated Euclidean linear map.

But I would not spend the excursion finding the exact `CFC.sqrt` scalar-identity theorem unless that normalization is independently useful. The unrestricted M1 is a cleaner public lemma.

## 3. M2/M3: use a generic independent-input map lemma

The useful reusable result is not Gaussian-specific:

```lean
-- Schematic statement
map_add_prod (μ ν : Measure E) (L : E →L[ℝ] E) :
  (μ.prod ν).map (fun p => L p.1 + p.2)
    = (μ.map L) ∗ ν
```

Use probability or suitable `SFinite` assumptions to match the product-map lemmas.

Set
```lean
F : E × E → E × E := fun p => (L p.1, p.2)
add : E × E → E := fun p => p.1 + p.2
```
and establish the calculation
```text
(μ.prod ν).map (add ∘ F)
    = ((μ.prod ν).map F).map add
    = ((μ.map L).prod ν).map add
    = (μ.map L) ∗ ν.
```

The load-bearing lemmas are:

- `Measure.map_map`;
- `Measure.map_prod_map`;
- the pushforward-of-product characterization of convolution.

For the measurable functions involved, use the measurability of `L`, projections, pairing, and addition. For example, `L.continuous.measurable` supplies the linear-map part. If `map_prod_map` asks for `AEMeasurable`, pass `.aemeasurable`.

### Convolution unfolding

I would put the identity
```lean
μ ∗ ν = (μ.prod ν).map (fun p => p.1 + p.2)
```
behind one local helper if it is not already exposed in a convenient form.

Inspect `Measure.conv` and `Measure.mconv` at the pin. The additive operation may be generated from the multiplicative definition, so do not assume that `rw [Measure.conv]` is the right interface. If the identity is definitional, use `rfl` or `change` once in the helper rather than scattering implementation-specific unfoldings through M2/M3.

### M3

Similarly, with
```lean
s : E → E := fun ξ => Real.sqrt (2 * h) • ξ
```
use
```text
(μ.prod stdGaussian).map (fun p => L p.1 + s p.2)
    = (μ.prod (stdGaussian.map s)).map
        (fun p => L p.1 + p.2)
    = (μ.prod (multivariateGaussian 0 ((2*h) • 1))).map
        (fun p => L p.1 + p.2)
    = gaussStep A ((2*h) • 1) μ.
```

The first equality is again `map_map` plus `map_prod_map`, now for `(id, s)`; the second is M1 and `Real.sq_sqrt`; the third is M2.

This organization keeps Gaussian algebra out of the product-map proof.

## 4. B: define pointwise, package into L², and prove one generic expectation bridge

For this target, I prefer **pointwise chains first**. The public theorem is about explicitly defined real-valued random variables, so make those the primary objects.

```lean
x c 0       := fun _ => 0
x c (k + 1) := fun ω => ρ * x c k ω + η c (k + 1) ω
```

Prove `MemLp (x c k) 2 P` by induction using the zero, scalar-multiplication, and addition closure properties of `MemLp`.

Then define
```lean
ηL c k := (hη c k).toLp (η c k)
xL c k := (hx c k).toLp (x c k)
```

### First isolate two small L² identification lemmas

For `hf : MemLp f 2 P` and `hg : MemLp g 2 P`, prove:
```lean
inner ℝ (hf.toLp f) (hg.toLp g)
  = ∫ ω, f ω * g ω ∂P
```
and
```lean
‖hf.toLp f‖ ^ 2 = ∫ ω, (f ω) ^ 2 ∂P.
```

The essential API is:

- `MeasureTheory.L2.inner_def`;
- `MemLp.coeFn_toLp`;
- `integral_congr_ae`;
- real inner-product simplification and the norm-square/inner-self identity.

Prove the second from the first. **Do not go through `Lp.norm_def`**: that introduces the machinery of `eLpNorm`, extended nonnegative reals, and roots for no benefit.

### Prove the recurrence in L² by a.e. extensionality

You need:
```lean
xL c (k + 1) = ρ • xL c k + ηL c (k + 1).
```

If convenient `MemLp.toLp_*` lemmas exist, use them. But do not make this bridge depend on guessing their exact names. A stable fallback is:

1. use extensionality for `Lp`;
2. combine the relevant a.e. identities with `filter_upwards`;
3. use `MemLp.coeFn_toLp`, `Lp.coeFn_add`, and `Lp.coeFn_smul`;
4. simplify the pointwise recurrence, including `smul_eq_mul`.

The initial-zero field is analogous.

Now the innovation Gram fields follow immediately from the first identification lemma and the assumed moment table. For different chains, simplify that table using `c ≠ c'`.

### Prove a generic finite-family statistic lemma

Before applying `pooled_sample_variance`, prove a lemma for any finite family `fₐ ∈ L²`. Write `Fₐ` for its `toLp` image and let `q : ℝ`. Then:
\[
\int \left(q\sum_a f_a(\omega)^2-
          \left(q\sum_a f_a(\omega)\right)^2\right)dP
=
q\sum_a\|F_a\|^2-
\left\|q\mathbin{\bullet}\sum_a F_a\right\|^2.
\]

This is exactly the interface the existing Gram theorem needs.

The proof obligations are:

- integrability of each square;
- `MemLp` for the finite weighted sum, hence integrability of its square;
- `integral_sub`, finite-sum integration, and integration of a constant multiple;
- the norm-square identification lemma;
- identification of the `toLp` of the weighted pointwise sum with the weighted sum of the `toLp`s.

For the last item, a finite induction using `Lp.coeFn_add` and `Lp.coeFn_smul` is sufficient. A dedicated finite-sum coercion lemma is convenient but **not load-bearing**. I would not block the proof on whether this pin calls it `Lp.coeFn_sum` or something else.

Finally instantiate with
```text
a = (c,i),  c : Fin C,  i ∈ range N
fₐ = x c (b + 1 + i)
q = 1 / ((C : ℝ) * (N : ℝ)).
```
Use explicit real casts early to avoid natural-division or coercion normalization problems.

This gives a clean three-layer proof:

1. pointwise chains → `AR1Chain` in L²;
2. expected pointwise statistic → Hilbert-space statistic;
3. `pooled_sample_variance`.

### Independence corollary

Index innovations by `Fin C × ℕ`, and assume:

- `MemLp` for each innovation;
- zero integral for each innovation;
- second moment `v`;
- `IndepFun` for every two distinct combined indices.

Use `IndepFun.integral_mul_eq_mul_integral` off the diagonal; use the second-moment hypothesis on the diagonal. Pairwise independence suffices. Independence only between chains, or only within each chain, is not by itself enough to cover all distinct combined indices.

## 5. Scope and recommendation

M and B are thematically coherent: together they connect a law-level sampler and a Hilbert-space calculation to actual random variables. But they are **separate implementation clusters**, with little proof-code overlap.

My recommendation is to make **B the main excursion**, including:

- the pointwise-to-L² chain construction;
- the generic expected-quadratic-statistic lemma;
- the expected pooled-variance theorem;
- the centred pairwise-independent-noise corollary.

It supplies the more substantial missing semantic bridge: the abstract Gram theorem becomes the claimed expected statistic of realised chains.

M1–M3 are a useful, bounded follow-up. If M is selected instead, a particularly valuable endpoint is the random-variable corollary: given `X` with law `μ`, `ξ` with law `stdGaussian E`, and `IndepFun X ξ`, the update has law `gaussStep …`. This makes the independence assumption explicit rather than leaving the theorem solely on a canonical product space.

Defer kernels and path-space construction. A kernel introduces measurable dependence on the starting state, and path space adds another infrastructure layer. Neither is needed for these bridges.

A later eigendirection theorem is well motivated: for an eigenvalue `λ`, set `ρ = 1 - h * λ` and innovation variance `v = 2 * h`. With centred independent Gaussian innovations, B then becomes the finite-run ULA diagnostic along that direction. Preserve the zero-start assumption: stationary or arbitrary initialization needs a corresponding extension of `AR1Chain`.

**Vote: target B alone—pointwise real AR(1) chains → L² Gram theorem → expected pooled sample variance, including the centred pairwise-independent-noise corollary.**