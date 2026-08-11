## A. Cheapest honest statement shape

The best first theorem is **option (ii), with the hypothesis stated as a pushforward identity**, rather than as an equality of integrals:

```lean
Measure.map (δ s) volume
  = ENNReal.ofReal (s ^ (-Q)) • volume
```

for `0 < s`, where

```lean
δ s w i = s ^ q i * w i
Q = ∑ i, q i
```

with `^` here representing `Real.rpow` as appropriate.

This is preferable to taking an arbitrary integral identity as a hypothesis:

- it says exactly what geometric fact the proof uses;
- it gives the integral substitution for every measurable integrand;
- it is reusable for `lintegral`, Bochner integrals, distributions, and later variants;
- it avoids making the first nonseparable theorem depend on determinant and `Measure.pi` engineering.

I would organize the development in three layers:

1. **Abstract measure-scaling lemma**: pushforward scaling + quasi-homogeneity implies unnormalized and normalized moment scaling.
2. **Pi-type diagonal pushforward lemma**: prove that the concrete `δ s` satisfies the pushforward hypothesis.
3. **Recovery theorem**: exact power-law rigidity recovers `q`.

Option (iii), a full abstraction over measurable equivalences and measure characters, is mathematically clean but probably more infrastructure than this programme currently needs.

### Concrete pi-type pushforward

For a general diagonal map

```lean
D c w i = c i * w i
```

with all `c i ≠ 0`, the desired formula is

```lean
Measure.map (D c) volume
  = ENNReal.ofReal |∏ i, c i|⁻¹ • volume.
```

Equivalently, for positive `c`,

```lean
∫ w, f w
  = (∏ i, c i) • ∫ w, f (D c w).
```

The most direct current-Mathlib route is the finite-dimensional linear-map theorem

```lean
MeasureTheory.Measure.map_linearMap_volume_pi
```

together with the determinant of the diagonal linear map. The remaining relevant lemmas are:

```lean
MeasureTheory.integral_map
MeasureTheory.integral_smul_measure
Matrix.det_diagonal
```

and the standard `LinearMap.det`/matrix representation API.

The proof has the following shape:

```lean
let D : (ι → ℝ) →ₗ[ℝ] (ι → ℝ) :=
{ toFun := fun w i => c i * w i
  map_add' := by intros; ext i; simp [mul_add]
  map_smul' := by intros; ext i; simp [mul_assoc, mul_left_comm] }

have hbij : Function.Bijective D := by
  -- inverse is coordinatewise multiplication by (c i)⁻¹
  ...

have hdet : LinearMap.det D = ∏ i, c i := by
  -- represent D by the diagonal matrix and use Matrix.det_diagonal
  ...

have hmap :
    Measure.map D volume
      = ENNReal.ofReal |∏ i, c i|⁻¹ • volume := by
  simpa [hdet] using
    MeasureTheory.Measure.map_linearMap_volume_pi D hbij
```

Then `MeasureTheory.integral_map` and `MeasureTheory.integral_smul_measure` give the integral formula.

The exact elaboration of the determinant step depends somewhat on how `D` is defined and which basis/matrix simp lemmas are imported. Consequently, this is not reliably a ten-line theorem from scratch. The measure-theoretic part is short; constructing the diagonal linear map and normalizing its determinant is the annoying part.

I would **not** use:

- `MeasurePreserving.pi`: coordinate multiplication is not measure-preserving;
- `integral_fintype_prod_volume_eq_prod`: that only handles product integrands;
- coordinatewise Fubini: it adds integrability/Tonelli bookkeeping and obscures the actual geometric statement.

There does not appear to be a more convenient specialized “map pi volume under coordinatewise scaling” lemma that makes the determinant route unnecessary. If you want the smallest PR now, use the pushforward hypothesis and isolate the concrete diagonal-volume theorem as a subsequent infrastructure result.

### Even cheaper one-parameter hypothesis

For the moment theorem, you do not actually need the general `c : ι → ℝ` lemma. It suffices to assume directly:

```lean
∀ s > 0,
  Measure.map (δ q s) volume
    = ENNReal.ofReal (s ^ (-(∑ i, q i))) • volume
```

This is the true minimal nonseparable geometric hypothesis.

---

## B. Integrability hypotheses

Yes: the substitution/scaling identity can be stated **without an `Integrable` hypothesis**, provided the integrand has the required measurability.

`MeasureTheory.integral_map` is compatible with Mathlib’s convention that a nonintegrable Bochner integral is `0`. Under a measurable equivalence such as an invertible diagonal map, integrability is preserved in both directions. Thus if one side is nonintegrable, so is the corresponding transformed side, and both Bochner integrals evaluate to `0`.

The theorem should nevertheless assume something such as:

```lean
Measurable P
```

or directly that the relevant moment integrand is measurable/AEMeasurable. Quasi-homogeneity alone does not imply measurability.

So the right distinction is:

- no `Integrable` hypothesis is formally necessary;
- a `Measurable`/`AEMeasurable` hypothesis is necessary for clean use of `integral_map`;
- for mathematically meaningful moments, later consumers will normally need finiteness or positivity anyway.

For example, if

```lean
Fα t w = (∏ i, w i ^ α i) * Real.exp (-t * P w),
```

then, with the pushforward identity and `0 < t`,

```lean
Iα t
  = t ^ (-(∑ i, q i + ∑ i, (α i : ℝ) * q i)) * Iα 1.
```

Again, powers should be implemented consistently using `Real.rpow`.

For normalized moments,

```lean
Mα t = Iα t / I0 t,
```

one obtains

```lean
Mα t
  = t ^ (-(∑ i, (α i : ℝ) * q i)) * Mα 1.
```

No explicit hypothesis `I0 1 ≠ 0` is formally needed if `/` is field division:

- if `I0 1 ≠ 0`, cancellation is ordinary;
- if `I0 1 = 0`, the scaling law gives `I0 t = 0`, and both normalized expressions reduce to `0`.

A proof will likely use `by_cases h : I0 1 = 0`.

That said, for semantic clarity it may still be preferable for the user-facing normalized theorem to assume

```lean
I0 1 ≠ 0
```

or, more naturally in the Laplace setting,

```lean
0 < I0 1.
```

This prevents the theorem from discussing “normalized moments” whose normalizing integral is Mathlib’s artificial zero for a nonintegrable function.

An alternative is to prove the raw scaling first with `lintegral`, where no integrability issue exists and divergence is represented by `∞`. However, normalization in `ℝ≥0∞` is less convenient, and signed/odd moments would still require Bochner integration. For your current even-coordinate recovery consumer, the real-integral route is reasonable.

---

## C. Weight-recovery consumer

The intended recovery theorem is correct. For each potential `Pᵣ` with weights `qᵣ`, the coordinate moment has the exact form

```lean
Mᵣ,i t = Mᵣ,i 1 * t ^ (-2 * qᵣ i)
```

for `0 < t`, since `α = 2 eᵢ`.

A suitable consumer statement is:

```lean
theorem weights_eq_of_eventually_coordinate_moments_eq
    (hq₁ : ∀ i, 0 < q₁ i)
    (hq₂ : ∀ i, 0 < q₂ i)
    (hscale₁ : ...)
    (hscale₂ : ...)
    (hpos₁ : ∀ i, 0 < M₁ i 1)
    (hpos₂ : ∀ i, 0 < M₂ i 1)
    (hmatch :
      ∀ i, ∀ᶠ t in atTop,
        M₁ i t = M₂ i t) :
    q₁ = q₂ := by
  funext i
  -- rewrite both sides using their exact power laws
  -- apply eventual_power_eq to
  --   M₁ i 1 * t ^ (-2*q₁ i)
  --   M₂ i 1 * t ^ (-2*q₂ i)
  -- conclude -2*q₁ i = -2*q₂ i
  -- linarith
```

If the available rigidity theorem is formulated on an explicit positive ray rather than `atTop`, use:

```lean
∃ T > 0, ∀ t ≥ T, M₁ i t = M₂ i t
```

or whichever ray filter the merged theorem expects.

Positivity is the right convenient hypothesis. Nonzero coefficients are mathematically sufficient for exponent rigidity, but positivity aligns with the existing `eventual_power_eq` route and with even moments.

There is no problem with taking positivity as an assumption. Quasi-homogeneity alone certainly does not imply it. Even adding `P ≥ 0` is not enough without measurability, finiteness, and support information.

Under stronger analytic assumptions one can eventually prove positivity automatically:

- `P` measurable and finite a.e.;
- `exp (-P) > 0` a.e.;
- the normalizing integral is finite and positive;
- `w i ≠ 0` on a set of positive volume;
- the coordinate-square numerator is integrable.

Continuous nonnegative proper quasi-homogeneous potentials with positive weights should normally satisfy the desired facts, but proving the required coercivity and integrability is a separate analytic theorem. Also, topological properness by itself does not generally guarantee that `exp (-P)` is integrable without using the quasi-homogeneous structure. Taking `M_{2e_i}(1) > 0` as a hypothesis is therefore the right scope for this tide.

As noted, this consumer recovers only

```lean
q₁ = q₂
```

not coefficients or the full potentials. Mixed quasi-homogeneous potentials can share the same weight vector and coordinate-moment exponents.

---

## D. Cheapest minimal nonseparable step

The cheapest genuinely nonseparable result is:

1. define a one-parameter family `δ s`;
2. assume its pushforward scales volume by `s⁻Q`;
3. assume `P (δ s w) = s * P w`;
4. derive exact scaling of arbitrary monomial-weighted Laplace integrals;
5. derive normalized scaling and coordinate-weight recovery.

In particular, do **not** initially prove the fully general theorem for arbitrary diagonal coefficients `c i`. The one-parameter pushforward law

```lean
Measure.map (δ s) volume = s⁻Q • volume
```

is all the Laplace argument needs.

A useful abstract interface would be something like:

```lean
def ScalesMeasure
    (δ : ℝ → X → X) (Q : ℝ) (μ : Measure X) : Prop :=
  ∀ s, 0 < s →
    Measure.map (δ s) μ
      = ENNReal.ofReal (s ^ (-Q)) • μ
```

Then the main theorem is independent of pi types, determinants, and Lebesgue measure. The concrete pi-type diagonal action becomes one instance.

That abstraction is smaller than a general measurable-equiv framework while still isolating the genuinely geometric input. It also makes clear that separability is nowhere used: the only facts about `P` are measurability and quasi-homogeneity.

So the recommended implementation order is:

1. abstract `ScalesMeasure` moment theorem;
2. normalized moment theorem;
3. coordinate recovery theorem via `eventual_power_eq`;
4. separately prove the pi-volume diagonal pushforward using  
   `MeasureTheory.Measure.map_linearMap_volume_pi` and `Matrix.det_diagonal`.

This gives the nonseparable mathematical result now without making it wait on the most brittle piece of Mathlib determinant plumbing.