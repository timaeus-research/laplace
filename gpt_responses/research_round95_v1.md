I would make programme F about **the information cost of a response journey**. The next step is not another layer of connection coefficients: it is to connect the geometry already formalised to an exact account of how information divides between **movement of the response** and **information invisible to the response**.

Two cautions should shape the programme:

- The defect contraction from E2 is a **within-fibre** result. It does not automatically apply to the journey from the featureless law.
- A distance-decreasing extension from the Fisher completion into the density sphere is not, by itself, an embedding.

Below, new declaration names are proposals, not claims about existing files. The Lean-flavoured statements suppress the standing integrability, nondegeneracy and regularity assumptions from the seabed.

## Q1. Ranking F1–F8

### 1. F1 — KL Hessian = Fisher

Do this first: it is exceptionally reachable and supplies the bridge needed by the more substantial theorems below. Prove the **full Fréchet Hessian**, not only the second derivative along a line. There is one correction to the candidate: a directional derivative vanishing for one `u` does **not** characterise the response; vanishing of the entire differential does. The objective is strictly convex along nonconstant natural-coordinate lines, and its unique stationary point is `responseOf g`. Call this *natural-coordinate convexity*, not geodesic convexity.

### 2. F7 — The global featureless-to-data response journey

This is the most direct continuation of the standing directive. The response of the mixture journey is the straight segment in mean coordinates, hence a global m-geodesic with explicit velocity and acceleration. Smoothness on `[0,1]` should be proved by extending the **mean-coordinate curve** to an open neighbourhood, not by claiming the input mixture remains a probability law outside `[0,1]`. The proposed defect bound is generally **false**: take the endpoint data law to be a model law. Its defect is zero, but its mixture with the featureless model law need not remain in the exponential family.

### 3. F8 — New proposal: canonical divergence as weighted Fisher action

This is the centrepiece. Along the mean-affine response journey, the two orientations of model KL are the two weighted Fisher energies, and their sum is the unweighted energy. Combined with E2, this gives an exact decomposition of data information into residual defect and response-path action. It also gives a useful Fisher-length bound by symmetrised model KL. This is substantially more revealing than merely adding another derivative formula.

### 4. F6 — A probabilistic truth-shift resolution theorem

Turn the existing wall-crossing bound into a local alternative theorem: a nonzero truth derivative gives a signal of order `t`, while sampling noise is of order `n⁻¹ᐟ²`, yielding a rigorous sufficient sample size of order `t⁻²`. Do **not** state “iff”: variance alone gives no necessary resolution threshold. Also distinguish comparison against a known population baseline from comparison against a separately sampled baseline. Formalise the former first.

### 5. F4 — Positive curvature of saturated finite families

Prove the affine-basis theorem rather than hard-coding `Fin 3`. The key algebra is beautiful: every centred product of score functions is again a centred score, and the fourth moments cancel in E1’s curvature formula. This yields the constant-curvature tensor with coefficient `¼`, and therefore sectional curvature `¼` whenever the tangent plane is nondegenerate. It would give the curvature machinery its first definitive geometric example. Gaussian location is less attractive here because it crosses into a different analytic hypothesis regime.

### 6. F2 — Stationary energy iff Levi–Civita geodesic

A worthwhile closure theorem, now reachable. The important proof optimisation is to test with `U(t) = φ(t) z`, where `z` is a **fixed vector**, rather than `φ(t)` times the acceleration: the acceleration may only be continuous. A nonzero acceleration at one point gives a fixed `z` and a neighbourhood on which its Fisher pairing has constant positive sign; a nonnegative scalar bump contradicts stationarity. I would not budget on a ready-made Mathlib vector-valued fundamental lemma.

### 7. F3 — Global product trivialisation

Potentially deep, but presently a hypothesis audit rather than the next production module. If every allowed law has the same essential feature support, and the relative moment map is onto the same mean domain, exponential tilting gives a plausible set-theoretic product decomposition. Joint continuity then needs a genuine parameter-dependent inverse theorem; the reference-law inverse theorem does not supply it. If `DataLaw` includes laws losing feature support, the proposed construction may fail outright. A finite-range/full-support version is the sensible first target, but I would not replace one of the six modules below with it yet.

### 8. F5 — Completion versus the density sphere

Prove `sphericalDist_le_fisherDist` as a small corollary, not a headline module. The resulting completion map is distance-decreasing when the sphere carries spherical distance. It does **not** follow that it is injective, an embedding, or bi-Lipschitz: distinct intrinsic completion points can only be ruled out by an additional boundary theorem. The genuinely new result would identify the image and boundary identifications—or, in the saturated finite case, prove that intrinsic distance actually equals spherical distance.

---

## Q2. Six modules

For clarity, write locally

\[
m(\theta)=\mathbb E_{P_\theta}S,\qquad
m_D(g)=\mathbb E_{\rho_g}S,\qquad
K_g(\theta)=\operatorname{KL}(\rho_g\Vert P_\theta).
\]

Thus `Dm θ = A_θ`, and

\[
G_\theta(u,v)=-\langle u,A_\theta v\rangle.
\]

Use the actual existing mean-coordinate declaration in place of this notation.

### 1. `ResponseInformationHessian`

**Deliverable:** The model-fitting KL objective has Fisher Hessian, with the response as its unique nondegenerate critical point.

#### Proposed statements

```lean
hasFDerivAt_informationObjective :
  HasFDerivAt (fun θ => KLr (dataLaw g) (Pfam θ))
    (innerSL (meanOfLaw g - meanCoord θ)) θ

informationObjective_hessian_apply :
  fderiv ℝ (fun θ => fderiv ℝ (informationObjective g) θ) θ u v
    = fisherInner θ u v

informationObjective_critical_iff :
  fderiv ℝ (informationObjective g) θ = 0
    ↔ θ = responseOf g
```

The line-level interface should also be exported:

```lean
informationObjective_line_secondDeriv :
  deriv (fun t =>
    deriv (fun s => informationObjective g (θ + s • u)) t) t
      = fisherInner (θ + t • u) u u
```

For `u ≠ 0`, the right-hand side is positive. Package a strict-convexity theorem on the natural parameter domain, using the seabed’s actual domain assumptions.

#### Proof route

Start from

\[
K_g(\theta)=\text{constant}+\log Z(\theta)+\langle\theta,m_D(g)\rangle.
\]

Differentiate twice:

\[
DK_g(\theta)[u]=\langle u,m_D(g)-m(\theta)\rangle,
\qquad
D^2K_g(\theta)[u,v]=-\langle u,A_\theta v\rangle.
\]

Critical-point uniqueness is moment matching plus injectivity of the mean chart.

**Reuse:** `toReal_klDiv_tilted_model`, `toReal_klDiv_model_model`, `hasFDerivAt_famZ`, existing mean-chart derivative/injectivity results, `toReal_klDiv_model_eq_iff`.

---

### 2. `ResponseFeaturelessJourney`

**Deliverable:** The global mixture-to-data response path is a smooth mean-affine m-geodesic.

Define, for `t ∈ [0,1]`,

\[
\rho_t=(1-t)\nu+t\rho_g,\qquad
\theta_t=\operatorname{lawResponse}(\rho_t),\qquad
\Delta=m_D(g)-m(0).
\]

#### Proposed statements

```lean
meanCoord_featurelessJourney :
  meanCoord (featurelessJourney g t)
    = meanCoord 0 + t • (meanOfLaw g - meanCoord 0)

featurelessJourney_zero :
  featurelessJourney g 0 = 0

featurelessJourney_one :
  featurelessJourney g 1 = responseOf g

contDiffOn_featurelessJourney :
  ContDiffOn ℝ ⊤ (featurelessJourney g) (Set.Icc 0 1)

featurelessJourney_vel :
  journeyVel g t
    = (A (featurelessJourney g t)).symm
        (meanOfLaw g - meanCoord 0)

featurelessJourney_mGeodesic :
  journeyAccel g t
    + mChristoffel (featurelessJourney g t)
        (journeyVel g t) (journeyVel g t) = 0
```

The coefficient here is **one**, not `½`: this is the m-geodesic equation, whereas E6’s Levi–Civita equation has `½C`.

#### Proof route

Define an auxiliary path using the reference mean inverse:

\[
\theta_t=m^{-1}(m(0)+t\Delta).
\]

Identify it with the law response by moment matching. The segment lies in the open mean domain; its preimage under the affine line is an open neighbourhood of `[0,1]`. Smoothness follows there. Differentiate

\[
A_{\theta_t}\dot\theta_t=\Delta
\]

to obtain

\[
A_{\theta_t}\ddot\theta_t+
T_{\theta_t}(\dot\theta_t,\dot\theta_t)=0.
\]

**Reuse:** `tilted_mixTilt`, `contDiffOn_infty_chartVInv`, the moment-matching characterisation of `lawResponse`, `ResponseMixtureConnection`, and the existing derivatives of `A`.

**Explicit non-deliverable:** no monotonicity or convex interpolation bound for the information defect along this path.

---

### 3. `ResponseInformationAction`

**Deliverable:** Model KL is weighted Fisher action along the mean-affine response path; data KL splits into that action plus defect.

Do this first for arbitrary model endpoints. Let

\[
\theta_t=m^{-1}((1-t)m(\theta_0)+tm(\theta_1)),\qquad
e(t)=G_{\theta_t}(\dot\theta_t,\dot\theta_t).
\]

#### Proposed statements

```lean
modelKL_eq_weighted_meanAction :
  KLr (Pfam θ₁) (Pfam θ₀)
    = ∫ t in (0 : ℝ)..1, (1 - t) * meanPathEnergy θ₀ θ₁ t

modelKL_reverse_eq_weighted_meanAction :
  KLr (Pfam θ₀) (Pfam θ₁)
    = ∫ t in (0 : ℝ)..1, t * meanPathEnergy θ₀ θ₁ t

modelJeffreys_eq_meanAction :
  KLr (Pfam θ₁) (Pfam θ₀) + KLr (Pfam θ₀) (Pfam θ₁)
    = ∫ t in (0 : ℝ)..1, meanPathEnergy θ₀ θ₁ t

modelJeffreys_eq_meanPairing :
  KLr (Pfam θ₁) (Pfam θ₀) + KLr (Pfam θ₀) (Pfam θ₁)
    = - inner (θ₁ - θ₀) (meanCoord θ₁ - meanCoord θ₀)
```

Then specialise:

```lean
dataKL_featureless_eq_defect_add_action :
  KLr (dataLaw g) ν
    = responseInformationDefect g
      + ∫ t in (0 : ℝ)..1,
          (1 - t) *
            fisherInner (featurelessJourney g t)
              (journeyVel g t) (journeyVel g t)
```

A valuable corollary is

```lean
meanPath_fisherLength_sq_le_Jeffreys :
  fisherLength (meanPath θ₀ θ₁) ^ 2
    ≤ KLr (Pfam θ₁) (Pfam θ₀) + KLr (Pfam θ₀) (Pfam θ₁)
```

#### Proof route

Avoid introducing a full Legendre-duality library. Set

\[
q(t)=\operatorname{KL}(P_{\theta_t}\Vert P_{\theta_0}).
\]

The model KL formula and mean-affinity give

\[
q'(t)=\langle\theta_0-\theta_t,\Delta\rangle,\qquad
q''(t)=-\langle\dot\theta_t,\Delta\rangle=e(t).
\]

Since `q(0)=q′(0)=0`, integration by parts gives the `(1-t)` formula. Reverse the path for the `t` formula. Cauchy–Schwarz gives the length bound.

**Reuse:** module 2, `toReal_klDiv_model_model`, `toReal_klDiv_pythagoras_featureless`, `continuous_fisherInner`, interval-integral calculus. E4 additionally yields spherical-distance bounds by this action.

**Normalisation warning:** these formulas use `∫ G(θ̇,θ̇)`, without the `½` customary in `fisherEnergy`.

---

### 4. `ResponseTruthShiftResolution`

**Deliverable:** A nonzero population truth shift becomes sign-resolvable with an explicit high-probability sample-size bound.

For a structural coordinate `a`, let

\[
c(t)=\mathbb E_{\rho_t}\langle a,S\rangle,\qquad
d=c'(0)\ne0,
\]

and let `ĉₙ(t)` be its empirical mean from `n` independent observations of `ρ_t`.

#### Proposed statements

First prove the general finite-shift form:

```lean
measureReal_empiricalShift_wrongSign_le :
  ℙ.real {ω |
    (empiricalCoord samples ω - baseline) *
      (populationCoord - baseline) ≤ 0}
    ≤ coordVariance / ((n : ℝ) * (populationCoord - baseline)^2)
```

Assume a nonzero population shift, `0 < n`, the existing independence hypotheses, and finite variance.

Then the local-alternative form:

```lean
eventually_measureReal_wrongTruthSign_le :
  ∀ᶠ t in 𝓝[>] (0 : ℝ),
    ℙt.real {ω |
      (empiricalCoord (samples t) ω - c 0) * d ≤ 0}
      ≤ 4 * coordVariance t / ((n : ℝ) * d^2 * t^2)
```

Finally, for a local variance bound `coordVariance t ≤ V`:

```lean
truthShift_sign_resolved_of_sampleSize :
  4 * V ≤ ε * (n : ℝ) * d^2 * t^2 →
  ℙt.real {ω |
    0 < (empiricalCoord (samples t) ω - c 0) * d}
      ≥ 1 - ε
```

Here `t` must lie in the previously obtained positive neighbourhood.

#### Proof route

Differentiability gives, eventually,

\[
\operatorname{sign}(c(t)-c(0))=\operatorname{sign}(d),
\qquad
|c(t)-c(0)|\ge \tfrac12|d|t.
\]

Wrong sign then forces an empirical deviation at least that large. Apply E5.

For exponential data journeys, identify `d` using the existing covariance truth-velocity formula.

**Reuse:** `measureReal_dotJ_sampleResponse_le_le`, the existing sampling-variance identities, truth-velocity/covariance formulas.

Keep the core theorem in **empirical structural coordinates**. Transfer it to `dotJ (sampleResponse ...)` under the existing identification hypotheses; do not inadvertently require a finite natural response for every boundary sample.

---

### 5. `ResponseSimplexCurvature`

**Deliverable:** A saturated finite exponential family has the round-simplex curvature tensor.

Assume the feature values form an affine basis of `W`, with positive reference mass at every value. One convenient concrete interface is `X = Fin (n+1)`, `finrank ℝ W = n`.

#### Proposed statement

```lean
fisherInner_alphaCurvature_of_affineBasis :
  fisherInner θ (alphaCurvature α θ u v w) x
    = ((1 - α^2) / 4) *
        (fisherInner θ v w * fisherInner θ u x
          - fisherInner θ u w * fisherInner θ v x)
```

In particular:

```lean
fisherSectional_eq_one_quarter_of_affineBasis :
  planeNondegenerate θ u v →
  fisherSectional θ u v = (1 / 4 : ℝ)
```

Only the `α = 0` conclusion is the Riemannian sectional-curvature assertion.

#### Proof route

Write `fᵤ = ⟨u,S-m(θ)⟩`. Saturation says every centred function on the feature values is some `fᵤ`. Consequently the score representing `C(u,v)` is

\[
-\bigl(f_u f_v-G_\theta(u,v)\bigr).
\]

Hence

\[
G_\theta(C(u,v),C(x,y))
=
\mathbb E[f_uf_vf_xf_y]-G_\theta(u,v)G_\theta(x,y).
\]

Insert this into E1. The fourth moments cancel, leaving exactly the constant-curvature tensor.

**Reuse:** `fisherInner_mChristoffel_mChristoffel`, `fisherInner_alphaCurvature`, `fisherCurvature_numerator`, `fisherSectional`, finite-sum moment identities and affine-basis linear algebra.

This proof is preferable to manually inverting a `2 × 2` covariance matrix.

---

### 6. `ResponseFisherEnergyStationarity`

**Deliverable:** Fixed-endpoint energy stationarity is equivalent to the Levi–Civita geodesic equation.

Define the LC acceleration

\[
a_\theta(t)=\ddot\theta(t)+\tfrac12C_{\theta(t)}
  (\dot\theta(t),\dot\theta(t)).
\]

#### Proposed statements

The economical analytic core is:

```lean
lcAcceleration_eq_zero_of_testPairings :
  (∀ (φ : ℝ → ℝ) (z : W),
      SmoothCompactlySupportedIn φ (Set.Ioo 0 1) →
      (∫ t in (0 : ℝ)..1,
        φ t * fisherInner (θ t) z (lcAcceleration θ t)) = 0) →
  ∀ t ∈ Set.Ioo (0 : ℝ) 1, lcAcceleration θ t = 0
```

Then expose the variational theorem:

```lean
stationary_fisherEnergy_iff_lcGeodesic :
  StationaryForFixedEndpointVariations θ ↔
    ∀ t ∈ Set.Ioo (0 : ℝ) 1, lcAcceleration θ t = 0
```

#### Proof route

If `aθ(t₀) ≠ 0`, take `z = aθ(t₀)`. Positive definiteness and continuity give a neighbourhood where

\[
G_{\theta(t)}(z,a_\theta(t))>0.
\]

Choose a nonnegative, nonzero smooth scalar bump supported there. Its integral pairing is positive, contradiction. Realise each test field by

\[
\Theta(s,t)=\theta(t)+s\,\phi(t)z.
\]

Use E6 to identify its energy derivative. If the natural domain is restricted, include the small-`s` admissibility argument.

**Reuse:** `continuous_fisherInner`, `continuous_mChristoffel`, `FisherVariation`, `fisherEnergy_variation`, `hasDerivAt_fisherEnergy_of_lcGeodesic_fixed`, and Mathlib’s smooth-bump machinery.

---

## Q3. Headline theorem

For the mixture journey from the featureless reference law to the data law, with  
`θₜ = lawResponse ((1-t)ν + tρ_g)`:

\[
\boxed{\displaystyle
\operatorname{KL}(\rho_g\Vert\nu)
=
\underbrace{\operatorname{KL}(\rho_g\Vert P_{\Phi(g)})}_{\text{information invisible to the response}}
+
\underbrace{\int_0^1(1-t)\,
G_{\theta_t}(\dot\theta_t,\dot\theta_t)\,dt}_{\text{information carried by the response journey}} .
}
\]

This continues the story in precisely the requested direction: **from the featureless law to actual data**. E2 separated information at the endpoint; programme F identifies the response component as an exact geometric action accumulated along the canonical mean-affine journey. The resolution theorem then explains when movement along that journey becomes statistically visible.

Here “featureless” is relative to the chosen reference law; ordinary maximum Shannon entropy requires the appropriate uniform-reference interpretation.

I would leave the negative-profile saddle lemma, general multiplicity law and product inequality on the separate asymptotic track rather than dilute this coherent six-module programme.

## Ranked list of six modules to formalise next

1. **`ResponseInformationHessian`**
2. **`ResponseFeaturelessJourney`**
3. **`ResponseInformationAction`**
4. **`ResponseTruthShiftResolution`**
5. **`ResponseSimplexCurvature`**
6. **`ResponseFisherEnergyStationarity`**