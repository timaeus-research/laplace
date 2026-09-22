# Consult: bridging the relative Watanabe modification (hironaka) to the consumer theorems (laplace)

You are advising on the architecture of a Lean 4 / Mathlib formalisation. Please answer the numbered questions at the end. Be concrete: name the intermediate statements, say which are cheap and which are campaigns, and give counterexamples where a statement is false as posed.

## What now exists

### Producer (timaeus-research/hironaka, main a8897879f, Lean 4.33.1)

Vocabulary (`Monomialize/Relative/Vocabulary.lean`), product typing `(Fin d → ℝ) × (Fin p → ℝ)`, `f : (Fin d → ℝ) → (Fin p → ℝ) → ℝ` curried:

```lean
def IsRelativeWatanabeChart (f) {Θ} {U : AnalyticManifold.{0} ℝ ((Fin d → ℝ) × (Fin p → ℝ))}
    (g : AnalyticMap U (model.restrict Θ)) (P : U) (φ : OpenPartialHomeomorph U ((Fin d → ℝ) × (Fin p → ℝ)))
    (ρ σ : ℝ) (k h : Fin d → ℕ) (a b : (Fin d → ℝ) × (Fin p → ℝ) → ℝ) : Prop :=
  IsFibredChart g φ ∧ P ∈ φ.source ∧ (φ P).1 = 0 ∧ 0 < ρ ∧ 0 < σ ∧
    centeredBox d ρ ×ˢ Metric.closedBall (inclusion Θ (g P)).2 σ ⊆ φ.target ∧
    AnalyticOnNhd ℝ a φ.target ∧ AnalyticOnNhd ℝ b φ.target ∧
    (∀ z ∈ φ.target, 0 < a z) ∧ (∀ z ∈ φ.target, b z ≠ 0) ∧
    (∀ z ∈ φ.target, f (chartRep g φ z).1 (chartRep g φ z).2 = a z * ∏ j, z.1 j ^ (2 * k j)) ∧
    ∀ z ∈ φ.target, relJacobian g φ z = b z * ∏ j, z.1 j ^ h j
-- IsFibredChart g φ : φ ∈ maximalAtlas ∧ ∀ z ∈ φ.target, (chartRep g φ z).2 = z.2
-- relJacobian g φ z = det of the d×d u-block of fderiv (g ∘ φ⁻¹) at z

structure RelativeWatanabeModificationOn (f) (V : Opens (Fin d → ℝ)) (S' : Opens (Fin p → ℝ)) : Type 1 where
  U : AnalyticManifold.{0} ℝ ((Fin d → ℝ) × (Fin p → ℝ))
  g : AnalyticMap U (model.restrict (prodOpens V S'))
  proper : IsProperMap g
  surjective : Function.Surjective g
  isoOff : AnalyticMap.IsAnalyticIsoOver g {z | f (incl z).1 (incl z).2 ≠ 0}
  chartAt : ∀ P : U, f (incl (g P)).1 (incl (g P)).2 = 0 → RelativeWatanabeChartAt f g P   -- ∃ φ ρ σ k h a b, IsRelativeWatanabeChart …
```

Statements of record (proof twins in `Proofs/Record/*` are sorry-free; axiom audit pending a build):

```lean
theorem Statements.exists_relativeWatanabeModificationOn_generic {d p} {U₀} {S₀} (hU₀ : IsOpen U₀) (hS₀ : IsOpen S₀)
    {f} (hf : AnalyticOnNhd ℝ (Function.uncurry f) (U₀ ×ˢ S₀))
    (W : Opens (Fin d → ℝ)) (hW : IsConnected (W : Set _)) (hWU : (W : Set _) ⊆ U₀)
    (S : Opens (Fin p → ℝ)) (hS : IsConnected (S : Set _)) (hSS : (S : Set _) ⊆ S₀)
    (hH1 : ∀ O, IsOpen O → O.Nonempty → O ⊆ (W : Set _) ×ˢ (S : Set _) → ∃ z ∈ O, f z.1 z.2 ≠ 0)
    (hH2 : ∀ x ∈ W, ∀ s ∈ S, 0 ≤ f x s)
    (V : Opens (Fin d → ℝ)) (hVc : IsCompact (closure (V : Set _))) (hVW : closure (V : Set _) ⊆ W) :
    ∃ S' : Opens (Fin p → ℝ), (S' : Set _) ⊆ S ∧ (S : Set _) ⊆ closure (S' : Set _) ∧
      Nonempty (RelativeWatanabeModificationOn f V S')
```
plus a zero-at-origin corollary and a local theorem at an equiresoluble parameter (equiresolubility is relative to a fixed total-space resolution).

Fibre specialisation exists (`Monomialize/Relative/Fibre/*`): for `s ∈ S'` the fibre `fibreAnalyticManifold` is an analytic `d`-manifold, `fibreBlowDown : fibre → V` is proper, surjective, an analytic iso off the zero set (`isAnalyticIsoOver_fibreBlowDown`), with `WatanabeChartAt` at zero points (`watanabeChartAt_fibreBlowDown`, `fibre_prop`, `fibre_prop_product`); the zero set of the fibre has measure zero (`volume_fibre_zeroSet_eq_zero`); slice charts have `slice_phase` and `slice_jacobian` with the SAME `(k, h)` as the relative chart.

How hironaka's single-function theorem is consumed today (greybook, `GreyBook/Extras/Germbij/AnalyticLaplace.lean`): NOT by a change of variables in the Laplace integral. The chain is
```
modification / LogResolutionData (finite chart family)  ⟶  Monomialize.Manifold.exists_hasLLCExponentsOn_of_logResolutionData
   : ∃ (lam : ℚ) (theta : ℕ) r₀, 0 < lam ∧ 1 ≤ theta ∧ theta ≤ d ∧ ∀ r ≤ r₀, HasLLCExponentsOn volume (closedBall w r) (fun x ↦ |K x|) lam theta
   -- HasLLCExponentsOn μ K f lam theta := sublevelVol μ K f =Θ[𝓝[>] 0] llcScale lam theta   (sublevel-volume Θ-form)
⟶ greybook Abelian transfer (Θ-form): Z(t) = ∫ e^{-tK} = Θ(t^{-lam} log^{theta-1} t)   (HasLaplaceTheta)
```
`lam` is `combLam` of the chart family (a rational computed from the chart data), `theta` is `combTheta`. Uniqueness of `(lam, theta)` on small balls is `HasLLCExponentsOn.unique`.

### Consumer (timaeus-research/laplace, Lean 4.33.0, hironaka-free)

`Laplace/Multi/RelativeChartLeading.lean`, `RelativeChartFamily.lean` (one active variable, `n` tangential variables `y : EuclidD n`, a real parameter `s`):
```lean
def chartIntegral (k h : ℕ) (a b χ : ℝ × EuclidD n → ℝ) (g : EuclidD n → ℝ) (t : ℝ) : ℝ :=
  ∫ z : ℝ × EuclidD n, g z.2 * χ z * b z * |z.1| ^ h * Real.exp (-(t * (a z * z.1 ^ (2 * k))))
theorem ChartData.tendsto_rpow_mul_chartIntegral : Tendsto (fun t ↦ t ^ ((h+1)/(2k)) * chartIntegral …) atTop (𝓝 (agmom k h * ∫ y, g y * χ (0,y) * b (0,y) * a (0,y) ^ (-(h+1)/(2k))))
def RelativeChartDecomposition (Z : ℝ → ℝ → ℝ) (k h : Fin N → ℕ) (a b : Fin N → ℝ → ℝ × EuclidD n → ℝ) (χ φ : Fin N → ℝ × EuclidD n → ℝ) (R : ℝ → ℝ → ℝ) : Prop :=
  ∀ s t, 0 < t → Z s t = (∑ i, chartIntegral (k i) (h i) (a i s) (fun z ↦ b i s z * φ i z) (χ i) (fun _ ↦ 1) t) + R s t
theorem RelativeChartDecomposition.tendsto_rpow_mul … (hR : Tendsto (fun t ↦ t ^ lam * R s t) atTop (𝓝 0)) :
  Tendsto (fun t ↦ t ^ lam * Z s t) atTop (𝓝 (∑ i ∈ univ.filter (chartExp (k i) (h i) = lam), ∫ y, chartDensity …))   -- lam = min e_i, constant in s
structure RelativeChartFamily (S' : Set ℝ) (k h) (a a' b b') (χ) (a₀ Ba Bb) : Prop  -- s-derivatives of a, b continuous & bounded on S'
theorem RelativeChartFamily.hasDerivAt_chartCoeff / hasDerivAt_leadingExp   -- score ḃ/b − e ȧ/a, quotient rule
```
Also available in laplace: Θ-form rigidity `mixture_isTheta` (pointwise comparability of losses preserves `Z =Θ t^{-λ} log^p t`), the separable attenuation identity, and the crossover theorems.

greybook `Extras/Germbij` depends on hironaka (pin e301b89, on upstream main history; toolchain 4.33.1) and is the natural home for a bridge; laplace cannot import hironaka without a toolchain bump.

## The goal

Consumer-level theorems about a family of losses `f(·, s)` on the generic set `S'`:
(G1) the leading exponent `λ(s)` and multiplicity `θ(s)` of `Z_s(t) = ∫_V φ(x) e^{-t f(x,s)} dx` (compactly supported prior φ ≥ 0 in V) are LOCALLY CONSTANT in `s ∈ S'`;
(G2) the leading coefficient `C(s)` in `Z_s(t) ~ C(s) t^{-λ} log^{θ-1} t` is differentiable in `s` with derivative an integral of a score over the divisor;
(G3) expectations `⟨φ⟩_{s,t}` and their `s`-derivatives, as in `RelativeChartFamily.hasDerivAt_leadingExp`.

## Questions

1. **Route.** (R1) Θ-form: from the record + fibre specialisation + hironaka's sublevel-volume readout, prove (G1) with `(λ(s), θ(s))` locally constant on `S'`. What exactly is missing? In particular: does the readout expose `combLam`/`combTheta` as a function of a finite chart family's `(k, h)` data, so that slicing the SAME relative charts at nearby `s` gives the same pair? Or does the readout's existential hide the chart family, making constancy unprovable without reopening it? (R2) Laplace-level: a change of variables along the fibre map `fibreBlowDown : fibre → V` in the Laplace integral, producing a `RelativeChartDecomposition` (finite sum of chart integrals + exponentially small remainder). This needs the change-of-variables formula for an analytic map between a `d`-manifold and `ℝ^d` that is a diffeomorphism off a null set, pulled through chart boxes with a partition of unity. Mathlib has `MeasureTheory.integral_image_eq_integral_abs_det_fderiv_smul` for injective differentiable maps on open sets of `ℝ^d`. Is R2 realistic, and what is the shortest lemma list? Which route gives (G2)/(G3)? Please rank.

2. **Reduce to `d = 1` first?** With `d = 1` every relative chart has exactly one active variable, matching laplace's `chartIntegral` with `n = 0`. Is a `d = 1, p = 1` bridge a sensible first milestone, and does anything in the general-`d` structure make it misleading (e.g. charts with `k = 0`, "off-zero kind", several charts meeting)? What is the shape of the `RelativeChartDecomposition` one actually gets from the record in `d = 1` (indexing of charts, the role of the closed box `[−ρ,ρ] × closedBall(s_P, σ)`, the partition of unity in `s`)?

3. **Amplitude positivity and the identification of λ.** `tendsto_rpow_mul` gives `t^λ Z → Σ_{e_i = λ} C_i(s)` with `λ = min e_i`; the limit may be `0` if the amplitude vanishes on the divisor of every minimising chart. With a positive prior `φ > 0` on `V` and `b ≠ 0`, is the leading sum automatically positive, and is that the right way to identify `λ` with the RLCT of `f(·, s)` on `V` (so that (G1) follows from the decomposition alone, without the Θ-route)? What about `θ` (log multiplicity): the one-active-variable charts give `θ = 1` only; where do the `log t` factors come from in `d ≥ 2`, and is `θ(s)` locally constant for the same reason?

4. **Statement to aim for.** Write the precise Lean-flavoured statement you would recommend as the FIRST bridge theorem (the one to hand to a formaliser), with its hypotheses, in whichever route you rank first, and estimate its size in lines and the sub-lemmas.

5. **Where.** greybook `Extras/Germbij` (imports hironaka; would restate the small laplace chart definitions or take laplace as a dependency after a toolchain bump to 4.33.1) versus bumping laplace and adding hironaka as a dependency. Recommendation and why.
