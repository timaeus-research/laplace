**A1–A4 and B are the right next step.** The main qualifications are to carry the existing measurability/normalization hypotheses into the kernel construction, and to require positive definiteness for the **Gaussian probability-law and moment statements for both MALA and pMALA**. I would make C optional rather than part of the commitment.

## 1. Kernel construction and Markov property

### A1: the measure-level definition is correct

Writing
\[
a(x)=Z^{-1}\int q(x,y)\alpha(x,y)\,d\mu(y),
\]
with the integrand interpreted in `ℝ≥0∞`, the desired measure is
\[
K(x)=
\mu.\mathrm{withDensity}\!\left(y\mapsto
\frac{\operatorname{ofReal}(q(x,y)\alpha(x,y))}{Z}\right)
+(1-a(x))\cdot\delta_x.
\]

Here `1 - a x` should be **ENNReal truncated subtraction**, and its scalar action should be on measures. Under the existing bound `a x ≤ 1`, it is exactly the rejection probability.

For measurable `E`, evaluate the two summands using:

- `withDensity_apply`;
- moving the constant `Z⁻¹` outside the `lintegral`;
- evaluation of the Dirac measure.

This gives your existing `mhKernelSet` formula.

**Yes: measurable evaluation on every measurable set suffices.** The measurable structure on `Measure X` is designed for this. Schematically:

```lean
toFun := fun x =>
  mu.withDensity (fun y => ENNReal.ofReal (q x y * alpha x y) / Z)
    + (1 - acceptMass x) • Measure.dirac x

measurable' := Measure.measurable_of_measurable_coe ...
```

Inside the measurability proof, first identify the displayed measure’s value on `E` with `mhKernelSet ... x E`, then use `measurable_mhKernelSet`.

One organizational wrinkle: **a `Kernel` definition cannot omit the hypotheses needed to prove its measurability field**. Either give `mhKernel` those hypothesis arguments, or package the standing assumptions in a structure. Avoid a fallback construction for nonmeasurable inputs; it would only complicate the application lemmas.

I would first prove an application lemma for the raw measure expression, then use it in the kernel constructor. This avoids trying to use `mhKernel_apply` before `mhKernel` exists.

### `Kernel.withDensity` versus `Measure.withDensity`

For this seabed, I prefer the direct `Measure.withDensity` construction.

A kernel-level `withDensity` route starts with a constant kernel and then needs the parameterized density to be measurable on `X × X`; depending on the pinned API, its construction/theorems can also bring s-finiteness conditions or instances. Those hypotheses are probably available here, but **you already have exactly the evaluation-measurability theorem needed for the direct route**. There is little benefit in redoing that infrastructure.

I would check the local declaration before making an exact claim about which assumptions `Kernel.withDensity` itself has in your snapshot.

### A2: Markovness needs the proposal normalization hypotheses

Once `mhKernel_apply` is established,
\[
K(x,\mathrm{univ})=a(x)+(1-a(x))=1
\]
follows from `mhAcceptMass_le_one`.

The important wording qualification is that **`q > 0` and `0 < Z < ∞` alone do not establish Markovness**. You also need the existing hypothesis that the proposal rows normalize with `Z`, or whatever standing assumptions were used to prove `mhAcceptMass_le_one`. Include the full standing hypotheses, not just those two examples.

The construction is a measure even without `a ≤ 1`; the bound is what makes it a probability measure.

### A4: separate proposal assumptions from target-law assumptions

The intended Gaussian specializations are correct:

- MALA’s Gaussian proposal is well-defined and normalized for `h > 0`;
- pMALA additionally needs the positive-definite preconditioner supplied here by `P⁻¹`;
- the stationary **Gaussian probability law**, and its `P⁻¹` moments, require `P` positive definite in both cases.

It is useful to distinguish the proposal normalizer from the target normalizer in names and theorem arguments. Confusing these two `Z`-like quantities is an easy source of unpleasant elaboration and rewrite errors.

## 2. Fixed point: use `Measure.bind`

Your proposed A3 is the cleanest statement:
```lean
(mhTargetLaw pi mu T).bind (mhKernel ...) = mhTargetLaw pi mu T
```

Its proof should be exactly the extensionality argument you describe. Schematically, with the function coercion made explicit if necessary:

```lean
  apply Measure.ext
  intro E hE
  rw [Measure.bind_apply hE K.measurable.aemeasurable]
  -- Rewrite K x E using mhKernel_apply, then use mh_invariant_law.
```

You may need a `simp_rw` or a small `lintegral_congr` step to rewrite the integrand. I would not insist on making the entire proof one `rw` chain.

For the standard `Measure.bind_apply` theorem, **no `SFinite` or `IsFiniteMeasure` assumption is needed**: the operative assumptions are measurability of `E` and a.e. measurability of the measure-valued function. A kernel gives actual measurability, hence a.e. measurability with respect to `ν`.

If elaboration needs help:

```lean
have hK :
    AEMeasurable (fun x => (K x : Measure X)) ν :=
  K.measurable.aemeasurable
```

The exact accessor/coercion syntax may vary slightly with the local API.

Two advantages of this route:

1. It matches “the target law is a fixed point” literally.
2. The measure equality itself does not need probability instances. Those establish that the fixed point is a stationary **probability** law, but are not needed for the extensionality proof.

`Kernel.const` or measure–kernel composition notation can be useful later for composition algebra. They would add a wrapper here without simplifying the proof.

## 3. Moments: use the ENNReal-density integral theorem

The direct bridge is indeed
`integral_withDensity_eq_integral_toReal_smul`.

Let
```lean
f x := ENNReal.ofReal (pi x) / T
```
and establish:

- measurability of `f`;
- `∀ᵐ x ∂mu, f x < ∞`.

With real-valued `pi` and `T ≠ 0`, density finiteness is straightforward. Retain `T < ∞` as well, because you want a genuine positive finite normalizer and later use `0 < T.toReal`.

The integral theorem reduces the goal to
\[
\int f(x).\mathrm{toReal}\, g(x)\,d\mu(x).
\]
Pointwise, for nonnegative `pi x`,
\[
f(x).\mathrm{toReal}
=\frac{\pi(x)}{T.\mathrm{toReal}},
\]
using `ENNReal.toReal_div` and `ENNReal.toReal_ofReal`. Then pull out the constant:
\[
\int g\,d\nu
=\frac{\int \pi(x)g(x)\,d\mu(x)}{T.\mathrm{toReal}}.
\]

Check the exact measurability argument order in the pinned declaration, but this is the right lemma family. Going through an NNReal density is possible; it adds a conversion layer without a clear benefit.

### Normalizer bridge

For integrable, nonnegative `pi`,
\[
\int \pi\,d\mu
=
\left(\int^- \operatorname{ofReal}(\pi)\,d\mu\right).\mathrm{toReal}.
\]

Yes, `integral_eq_lintegral_of_nonneg_ae` is the appropriate bridge. The strong-measurability/a.e.-strong-measurability premise needed by its local signature comes from integrability. The `ofReal` is already part of the real-integral-to-lintegral expression; `toReal_ofReal` is principally useful in the density simplification above.

I would prove these Gaussian identification lemmas explicitly:

```lean
targetWeight P = tiltedWeight P 0
(targetZ P).toReal = tiltedZ P 0
```

Then package the central reusable bridge:
```lean
∫ x, g x ∂gaussianLaw P = tiltedExpectation P 0 g
```

Give it whatever measurability/integrability hypotheses your chosen proof route needs. This reduces the final moments to the existing tilted-moment theorems and `tiltMean P 0 = 0`.

### Integrability: reuse the seabed

**Yes, discharge polynomial-weight integrability using the existing Gaussian lemmas.** In particular, use `integrable_coord_mul_gaussianWeight_matCLM`, rewrite the target weight, and normalize by the constant. Do the analogous thing for coordinates.

A subtle but important distinction:

- The Bochner-integral change-of-density equality may be available without a separate integrability hypothesis, because Lean’s integral is total.
- Calling the resulting values “mean” and “covariance” should still come with genuine integrability facts.

I would export, or at least prove locally:

```lean
Integrable (fun x => x i) (gaussianLaw P)
Integrable (fun x => x i * x j) (gaussianLaw P)
```

Then prove:
```lean
∫ x, x i ∂gaussianLaw P = 0
∫ x, x i * x j ∂gaussianLaw P = P⁻¹ i j
```

Strictly speaking, the second theorem is a **raw second-moment** statement. Together with zero mean it gives covariance. A centered-integral corollary is cheap and makes “covariance `P⁻¹`” explicit, without needing to engage Mathlib’s covariance API immediately.

## 4. Scope and nearby additions

**A+B is a coherent tide.** Around 300 lines is plausible if the existing normalizer and integrability lemmas rewrite smoothly, but it is not a reliable budget: coercions, hypothesis plumbing, and the density-to-real bridge could push it higher.

Suggested order:

1. Raw measure application lemma and measurable kernel.
2. Markov instance.
3. Generic `bind` fixed point.
4. MALA/pMALA wrappers.
5. Gaussian integral bridge, integrability, and moments.

Two inexpensive additions:

- Ensure the Markov/probability instances are exposed so `IsProbabilityMeasure (ν.bind K)` can be obtained through the existing instance machinery. A dedicated theorem is probably unnecessary unless instance search needs a bridge.
- Add stationarity after finitely many repeated transitions if the kernel iteration API is already convenient. A recursive sequence of measures also proves this by immediate induction. Do not assume `K^n` is the correct local notation.

**C is mathematically correct but not necessarily cheap.** Detailed balance gives reversibility, but exchanging restricted integrals and tidying the rejection/diagonal term may require another substantial proof unless the seabed already exposes a symmetric accepted-flux theorem. I would defer it rather than compromise the moment statements.

**Vote: A+B**, with the full standing normalization/measurability hypotheses carried into A, positive definiteness for both Gaussian stationary-law specializations, and integrability plus an explicit centered-moment corollary in B.