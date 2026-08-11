## A. Correctness of the candidates

### 1. Translation bridge

The intended mathematics is correct, but the proposed statement should be sharpened.

Most importantly, `posteriorIntegral` is already the **unrescaled** localized Gibbs integral:

```lean
∫ w, Set.indicator A.U
  (fun w ↦ f w * Real.exp (-(L w / q ^ 2))) w
```

`posteriorIntegral_eq` is the subsequent dilation identity expressing it as

```lean
q ^ d * exp (-(L 0 / q ^ 2)) * (rescaled integral).
```

Therefore, translation of the actual localized moment does **not** need to interact with the `q`-dilation at all. The clean proof path is:

1. expose `posteriorMoment` as a quotient of the two unrescaled localized integrals;
2. translate numerator and denominator using `integral_add_left_eq_self`;
3. only separately relate `q` to physical temperature `t`.

A useful foundational API would be something like:

```lean
noncomputable def regionIntegralQ
    (Λ : EuclidD d → ℝ) (V : Set (EuclidD d))
    (φ : EuclidD d → ℝ) (q : ℝ) : ℝ :=
  ∫ w, Set.indicator V
    (fun w ↦ φ w * Real.exp (-(Λ w / q ^ 2))) w

noncomputable def regionMomentQ
    (Λ : EuclidD d → ℝ) (V : Set (EuclidD d))
    (φ : EuclidD d → ℝ) (q : ℝ) : ℝ :=
  regionIntegralQ Λ V φ q / regionIntegralQ Λ V (fun _ ↦ 1) q
```

Then define the translated region explicitly, preferably in a form whose membership simplifies well:

```lean
def translatedRegion (p : EuclidD d) (U : Set (EuclidD d)) :=
  {w | w - p ∈ U}
```

This avoids possible pointwise `+ᵥ` notation friction. The central theorem should be:

```lean
regionMomentQ
    (fun w ↦ L (w - p))
    (translatedRegion p A.U) φ q
  =
A.posteriorMoment (fun y ↦ φ (p + y)) q
```

This should hold for every `q`, including junk cases, because numerator and denominator are individually equal under translation. No denominator nonvanishing argument is needed.

A named lemma exposing the package quotient would also be worthwhile, even if its proof is just `rfl`/`unfold`:

```lean
A.posteriorMoment f q =
  regionMomentQ L A.U f q
```

That lemma is conceptually distinct from the existing rescaled identity
`posteriorMoment_eq_integrand_div`.

#### Raw loss versus minimum-shifted loss

Use the raw exponent as the primary definition:

```lean
exp (-(t * Λ w))
```

or, in the `q` version,

```lean
exp (-(Λ w / q^2)).
```

That exactly matches `posteriorIntegral`. Then prove a separate normalization lemma saying that replacing `Λ w` by `Λ w - a`, in particular by `Λ w - Λ p`, does not change the normalized moment. The multiplying exponential is always nonzero, so the cancellation is junk-safe.

There is no need for an “infimum shift” in the definition.

#### Temperature parametrization

For a note-literal physical-temperature definition, use:

```lean
noncomputable def regionMomentTDirect
    (Λ : EuclidD d → ℝ) (V : Set (EuclidD d))
    (φ : EuclidD d → ℝ) (t : ℝ) : ℝ :=
  (∫ w, V.indicator (fun w ↦ φ w * exp (-(t * Λ w))) w) /
  (∫ w, V.indicator (fun w ↦ exp (-(t * Λ w))) w)
```

Then prove, for `0 < t`,

```lean
regionMomentTDirect
    (fun w ↦ L (w - p)) (translatedRegion p A.U) φ t
  =
A.locatedMomentT p φ t
```

The positivity assumption is relevant because `posteriorMomentT` is implemented using
`q = (sqrt t)⁻¹`. For negative `t`, that implementation has junk semantics and is not the direct Gibbs factor `exp (-tL)`. Since `SuperPoly` is at `atTop`, an eventually-positive equality is fully sufficient for later recovery theorems.

An alternative is to define `regionMomentT` by composition with `(sqrt t)⁻¹`; that gives equality for all `t`, but it is less literally the physical Gibbs integral. Having both definitions and a positive-temperature bridge is the cleanest API.

---

### 2. Located `ccData` headline

The proposed conclusion is mathematically reasonable, but it is **not yet merely a direct application** of `superPoly_moment_of_ccData`.

There are two hidden issues.

#### The observables differ after centering

Actual coordinate data uses the same observable

```lean
fun w ↦ w i
```

for both losses. After translating to centered coordinates, this becomes

```lean
fun y ↦ (p₁ + y) i
```

on the first side and

```lean
fun y ↦ (p₂ + y) i
```

on the second side.

These are smooth and have polynomial growth, so analytically they are fine. But
`superPoly_moment_of_ccData A B` expects the **same centered observable** `P` on both sides. Consequently, it cannot directly be instantiated with these two translated coordinate observables.

What is needed first is an actual-coordinate cutoff-removal theorem, for example:

```lean
superPoly_locatedMoment_of_ccData
```

which concludes

```lean
SuperPoly (fun t ↦
  A.locatedMomentT p₁ P t - B.locatedMomentT p₂ P t)
```

for a single actual observable `P`.

Its proof is the translated analogue of `superPoly_moment_of_ccData`, using a cutoff in actual coordinates.

#### Support in the intersection is not sufficient by itself

Writing

```lean
tsupport φ ⊆ translatedRegion p₁ A.U
tsupport φ ⊆ translatedRegion p₂ B.U
```

is syntactically equivalent to support in the intersection. But it is not logically enough for location recovery unless that intersection contains neighborhoods of **both** minima.

For example, if the translated localization regions are disjoint, the only admissible test may be zero; such data clearly cannot determine `p₁ = p₂`.

The cutoff used to recover actual coordinate moments must:

- equal `1` near `p₁`, so its tail is negligible for the first loss;
- equal `1` near `p₂`, so its tail is negligible for the second loss;
- have support in the admissible common test region.

Thus the theorem needs one of the following stronger formulations:

1. data for all globally compactly supported smooth tests; or
2. a common actual open region `V` containing neighborhoods of both `p₁` and `p₂`, with admissible compact supports in `V`; or
3. explicit assumptions that both minima lie in the interior of the intersection of the two actual localization regions.

The second option is closest to a note-literal premise `φ ∈ C_c^∞(U)` for one common actual localization region `U`.

#### After location equality

Once `p₁ = p₂ = p` is established, the remaining composition is much cleaner.

Given a centered test `ψ`, define the actual test

```lean
φ w := ψ (w - p).
```

The translation bridge turns actual moment agreement for `φ` into centered moment agreement for the same `ψ` on both sides. That directly feeds:

```lean
smooth_positive_jet_recovery_of_ccData
```

and then the analytic germ theorem.

For a fully literal conclusion at the actual point,

```lean
iteratedFDeriv ℝ j Λ₁ p = iteratedFDeriv ℝ j Λ₂ p,
```

one additional derivative-under-translation bridge is needed. Equality of the centered derivatives at `0` is not definitionally the same statement. Likewise, the centered eventual germ equality must be transported from `𝓝 0` to `𝓝 p`, although that filter translation is comparatively easy.

So candidate 2 contains more than just headline gluing:

- actual-coordinate cutoff removal;
- a common-region hypothesis strong enough for both minima;
- centered-data transport after location recovery;
- derivative/germ transport back to the actual point.

---

### 3. `IsSymm` from analyticity

Yes. Analyticity gives `ContDiffAt ℝ ⊤`, and the omega-regularity permutation theorem gives symmetry of every iterated derivative.

The relevant Mathlib API is expected to be:

```lean
ContDiffAt.iteratedFDeriv_comp_perm
```

with a conclusion expressed using `ContinuousMultilinearMap.domDomCongr`. Since `ContinuousMultilinearMap.IsSymm` is the assertion that the map is invariant under all permutations, the proof should be essentially:

```lean
theorem AnalyticAt.iteratedFDeriv_isSymm
    {L : EuclidD d → ℝ} {x : EuclidD d}
    (hL : AnalyticAt ℝ L x) (k : ℕ) :
    (iteratedFDeriv ℝ k L x).IsSymm := by
  intro σ
  exact hL.contDiffAt.iteratedFDeriv_comp_perm σ
```

The exact argument order or orientation of the equality may require `simpa` or `.symm`, depending on the current Mathlib declaration. The key ingredients are:

- `AnalyticAt.contDiffAt`;
- `ContDiffAt.iteratedFDeriv_comp_perm`;
- `ContinuousMultilinearMap.IsSymm`;
- `ContinuousMultilinearMap.domDomCongr`.

The condition `1 < k` is unnecessary for this standalone symmetry theorem; it holds at every order. The recovery theorem can then restrict it to `1 < k`.

The warning in the tide log is correct: use omega regularity. Trying to obtain this directly from only `ContDiffAt ℝ k` is likely to run into the existing API restriction.

---

## B. Minimal good scope for one tide

Candidate 1 alone is the right minimal scope, provided it is implemented as a reusable bridge layer rather than as one monolithic theorem.

Candidate 2 is not “mostly gluing” yet. Its actual-coordinate cutoff theorem and common-region issue are substantive. Combining all of that with the measure-translation work would make the tide substantially larger and harder to review.

A good first tide would contain:

1. generic unrescaled region integral and normalized moment;
2. a named package-to-unrescaled-quotient lemma;
3. translated-region membership lemmas;
4. translation invariance of numerator and denominator;
5. the actual located-moment identity at scale `q`;
6. direct-temperature equality for eventually positive `t`;
7. optionally, raw-loss versus minimum-shifted-loss invariance.

Candidate 3 is tiny and independent enough that it could be included as a bonus, but it should not be allowed to obscure the primary translation bridge.

---

## C. Recommended decomposition

A clean sequence would be:

### Tide 1: `TranslationBridge`

- `regionIntegralQ`
- `regionMomentQ`
- `regionMomentTDirect`
- `posteriorMoment_eq_regionMomentQ`
- translated-region definitions and simp lemmas
- translation theorem at `q`
- positive-temperature bridge
- invariance under subtracting `Λ p`

This layer will also be useful beyond the current inverse theorem.

### Tide 2: actual-coordinate cutoff removal

Prove something like:

```lean
superPoly_locatedMoment_of_ccData
```

with a common actual test region containing neighborhoods of both candidate minima. Include translation-preservation lemmas for:

- `ContDiff`;
- `HasCompactSupport` and `tsupport`;
- polynomial growth under affine translation.

Then apply it to `P w = w i` and obtain the data needed by
`location_eq_of_superPoly_first_moments`.

### Tide 3: located grand headline

- recover `p₁ = p₂`;
- translate the actual `ccData` premise to centered `ccData`;
- invoke `smooth_positive_jet_recovery_of_ccData`;
- transport centered derivatives back to the common actual point;
- state the smooth located theorem.

### Tide 4 or small bonus: analytic wrapper

- derive all `IsSymm` assumptions from analyticity;
- invoke the smooth located theorem;
- transport the centered germ equality to `𝓝 p`;
- state the fully located analytic germ theorem without explicit symmetry hypotheses.

The largest correction to the original plan is therefore: **candidate 1 is sound after sharpening, but candidate 2 needs a genuinely new located cutoff-removal layer and a stronger common-region assumption.**