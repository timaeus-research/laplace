# Spec: relative (parametrised) resolution for singular learning theory

**For:** the hironaka campaign (timaeus-research/hironaka).
**From:** the germbij / laplace formalisation ("What expectation values know about the loss landscape").
**Date:** 2026-09-21.
**Status of the consumer side:** everything below the interface is formalised in laplace
(`Laplace/Multi/ResolvedChartResponse.lean`, `MorseBottResponse.lean`, `SingularPowerNormalForm.lean`,
`ToyCrossover.lean`) and in greybook `Extras/Germbij`; this document specifies the missing input.

---

## 1. What we want to prove downstream, and why it needs a family version

Let `q_s` be a smooth family of true distributions (parameter `s` in an open `S ⊆ ℝ^p`), and
`L_s(w) = -∫ q_s log p_w` the population loss. The posterior expectation values at temperature `t`
have asymptotic expansions in `t` whose exponents are the poles of the zeta function of the fibre
`L_s` and whose coefficients are integrals over the exceptional divisor. The downstream theorem is:

> **Level 3 (smooth response on a stratum).** If the family `L_s` admits a resolution *in the
> family* — a single modification over `W × S` whose chart exponent data do not depend on `s` —
> then along the family (i) the leading pole `(λ, m)` is constant, (ii) every expansion
> coefficient is a smooth function of `s`, and (iii) its derivative is a covariance of the test with
> an explicit score built from the `s`-derivatives of the units and amplitudes on the charts.

What is already formalised is (iii) chart by chart, for a chart with one active exponent
(`SPFamilyData.hasDerivAt_spExp_tangential`: score `χ'/χ − (1/2k)·a'/a`) and for the Morse–Bott
chart (`MBFamilyData.hasDerivAt_tanExp`, `MBFamilyData'.hasDerivAt_mbExp_tangential`: score
`χ'/χ − ½ tr(H⁻¹ H')`), plus the counterexample `x⁴ + u²x²` showing that (i)–(iii) fail when the
exponent data change with `s` (`ToyCrossover`). What is missing is the global object that makes
"chart exponent data independent of `s`" a theorem rather than a hypothesis, i.e. the relative
version of hironaka's `WatanabeModificationOn`.

## 2. What hironaka currently exports (the single-function interface)

`Monomialize/Transport/AnalyticResolutionExports.lean`:

```lean
structure WatanabeModificationOn (f : (Fin d → ℝ) → ℝ) (W : Opens (Fin d → ℝ)) where
  U : AnalyticManifold.{0} ℝ (Fin d → ℝ)
  g : AnalyticMap U ((AnalyticManifold.model ℝ (Fin d → ℝ)).restrict W)
  proper : IsProperMap g
  surjective : Function.Surjective g
  isoOff : AnalyticMap.IsAnalyticIsoOver g {x | f (inclusion W x) ≠ 0}
  chartAt : ∀ P : U, f (inclusion W (g P)) = 0 → WatanabeChartAt f g P

theorem exists_watanabeModificationOn (hU₀ : IsOpen U₀) (hf : AnalyticOnNhd ℝ f U₀) (h0 : f 0 = 0)
    (hne : ¬ ∀ᶠ x in 𝓝 0, f x = 0) (W : Opens _) (hW : IsConnected W) (h0W : 0 ∈ W)
    (hWU : W ⊆ U₀) : Nonempty (WatanabeModificationOn f W)
```

`Monomialize/Transport/ZeroChartExtraction.lean`:

```lean
structure EvenChartBox (R : WatanabeModificationOn K W) where
  φ : OpenPartialHomeomorph R.U (Fin d → ℝ)
  mem : φ ∈ maximalAtlas 𝓘(ℝ, Fin d → ℝ) ω R.U
  k : Fin d → ℕ                 -- half exponents of the phase
  h : Fin d → ℕ                 -- exponents of the Jacobian
  b : (Fin d → ℝ) → ℝ           -- analytic nonvanishing Jacobian unit
  b_analytic : AnalyticOnNhd ℝ b φ.target
  b_ne_zero : ∀ u ∈ φ.target, b u ≠ 0
  phase_eq : ∀ u ∈ φ.target, K (watanabeRep R.g φ u) = ∏ j, u j ^ (2 * k j)
  jac_eq : ∀ u ∈ φ.target, (fderiv ℝ (watanabeRep R.g φ) u).det = b u * ∏ j, u j ^ h j
  r ρ : ℝ; r_pos; r_lt_ρ; box_subset : centeredBox d ρ ⊆ φ.target
  zero_mem : 0 ∈ φ.target ∧ K (watanabeRep R.g φ 0) = 0
```

greybook consumes exactly this (`GreyBook.Ch2.RLCTExistence`, `Extras/Germbij/AnalyticLaplace`:
`exists_hasRLCTTheta_of_analyticOnNhd_nonneg`) to get the Θ-form expansion of a single loss. Note
that in these charts the phase is an *exact* monomial (no unit `a`): the unit has been absorbed into
the chart. For the family version we do **not** want that normalisation, see §3.3.

## 3. The requested object: `RelativeWatanabeModificationOn`

### 3.1 Data

For a parameter space `S : Opens (Fin p → ℝ)` (or a general analytic manifold; `p = 1` suffices for
a first version) and a function `f : (Fin d → ℝ) → (Fin p → ℝ) → ℝ`, analytic in `(x, s)` jointly on
`U₀ × S`, with `f x s ≥ 0` (SLT losses are nonnegative; positivity of the amplitude is used
downstream but is not needed for the resolution itself):

```lean
structure RelativeWatanabeModificationOn
    (f : (Fin d → ℝ) → (Fin p → ℝ) → ℝ) (W : Opens (Fin d → ℝ)) (S : Opens (Fin p → ℝ)) where
  /-- The resolved total space, a manifold of dimension `d + p`. -/
  U : AnalyticManifold.{0} ℝ (Fin (d + p) → ℝ)
  /-- The blow-down over the parameter space: `g : U → W × S`, commuting with the projection to `S`. -/
  g : AnalyticMap U (model.restrict (W ×ˢ S))
  proper : IsProperMap g
  surjective : Function.Surjective g
  /-- `U → S` is a submersion (the family is smooth over `S`). -/
  smoothOverS : IsSubmersion (projS ∘ g)
  /-- `g` is an analytic isomorphism over `{(x, s) | f x s ≠ 0}`. -/
  isoOff : AnalyticMap.IsAnalyticIsoOver g {z | f (inclusion z).1 (inclusion z).2 ≠ 0}
  /-- The relative chart clause at every point over the zero set (see 3.2). -/
  chartAt : ∀ P : U, f (g P).1 (g P).2 = 0 → RelativeWatanabeChartAt f g P
```

### 3.2 The relative chart clause (the heart of the request)

`RelativeWatanabeChartAt f g P` should provide a chart `φ` of `U` around `P`, **fibred over `S`**:
coordinates `(u, s) ∈ (Fin d → ℝ) × (Fin p → ℝ)` with `projS ∘ g ∘ φ⁻¹ = (u, s) ↦ s`, and on
`φ.target`:

```lean
  k : Fin d → ℕ                          -- half exponents of the phase, INDEPENDENT of s
  h : Fin d → ℕ                          -- Jacobian exponents, INDEPENDENT of s
  a : (Fin d → ℝ) → (Fin p → ℝ) → ℝ      -- analytic positive unit
  b : (Fin d → ℝ) → (Fin p → ℝ) → ℝ      -- analytic nonvanishing Jacobian unit
  a_analytic : AnalyticOnNhd ℝ (uncurry a) φ.target
  b_analytic : AnalyticOnNhd ℝ (uncurry b) φ.target
  a_pos : ∀ z ∈ φ.target, 0 < a z.1 z.2
  b_ne_zero : ∀ z ∈ φ.target, b z.1 z.2 ≠ 0
  phase_eq : ∀ z ∈ φ.target, f (g (φ.symm z)).1 (g (φ.symm z)).2 = a z.1 z.2 * ∏ j, z.1 j ^ (2 * k j)
  jac_eq : ∀ z ∈ φ.target, (relative Jacobian of g ∘ φ.symm in the u-directions at z) = b z.1 z.2 * ∏ j, z.1 j ^ h j
  box_subset : centeredBox d ρ ×ˢ ball s₀ σ ⊆ φ.target      -- a product box, uniform in s
```

The two clauses that matter downstream are: **`k` and `h` do not depend on `s`**, and the chart
target contains a **product box** `(u-box) × (s-ball)` so that the units and amplitudes are
controlled uniformly on compact parameter sets. Everything the laplace theorems need
(`SPFamilyData`: common lower bound on the unit, common compact support, bounded continuous
`s`-derivatives) follows from analyticity of `a`, `b` on such a product box.

### 3.3 Do not absorb the unit

In the single-function `EvenChartBox` the phase is an exact monomial, the unit having been absorbed
by a further coordinate change (`a^{1/2k}` rescaling). In the family version please **keep the unit
`a(u, s)` explicit** (or provide both forms). The response formula downstream is precisely the
covariance with `∂_s log a` weighted by the RLCT, and it is invisible if the unit is normalised
away; also the normalising coordinate change would itself depend on `s`, which is what we want to
track.

### 3.4 Existence theorem (what to prove)

```lean
theorem exists_relativeWatanabeModificationOn
    (hf : AnalyticOnNhd ℝ (uncurry f) (U₀ ×ˢ S₀)) (hnonneg : ∀ x s, 0 ≤ f x s)
    (hne : ∀ s ∈ S₀, ¬ ∀ᶠ x in 𝓝 0, f x s = 0)
    (W : Opens _) (hW : IsConnected W) (h0W : 0 ∈ W) (hWU : W ⊆ U₀) (s₀ : Fin p → ℝ) (hs₀ : s₀ ∈ S₀) :
    ∃ S : Opens (Fin p → ℝ), s₀ ∈ S ∧ S ⊆ S₀ ∧ Nonempty (RelativeWatanabeModificationOn f W S)
```

**Important: this is false as stated for arbitrary `s₀`** (the toy `x⁴ + u²x²` has no relative
resolution on any neighbourhood of `u = 0` with constant exponents). The correct statement is
*generic*: there is an open dense (in the algebraic setting Zariski-open dense) subset `S' ⊆ S₀` of
parameters over which a relative modification exists, i.e.

```lean
theorem exists_relativeWatanabeModificationOn_generic … :
    ∃ S' : Set (Fin p → ℝ), IsOpen S' ∧ Dense S' ∧ S' ⊆ S₀ ∧
      ∀ s₀ ∈ S', ∃ S : Opens _, s₀ ∈ S ∧ Nonempty (RelativeWatanabeModificationOn f W S)
```

together with the local statement at a given `s₀` under an **equisingularity hypothesis** to be
chosen by the campaign (see §5). The generic statement is the one the note needs first: it says
"resolution works in the family on strata", and the complement of `S'` is where the phase
transitions live.

### 3.5 Minimal first version

If the full relative theorem is too far, the following would already unlock the downstream chain:

- `p = 1` (one real parameter);
- `d = 1` transverse variable plus tangential variables handled as parameters (the singular power
  normal form `a_s(y) x^{2k}` is then literally the chart clause with `k` constant) — this is the
  case already treated in laplace *assuming* the chart form, so a hironaka theorem producing it
  from an analytic family would close the loop;
- or: the **relative chart-existence statement alone** (3.2 without 3.1's global properness):
  for `(x₀, s₀)` in the zero set and `s₀` generic, a fibred chart with `s`-independent exponents on a
  product box. Downstream we can glue with a partition of unity ourselves.

## 4. What the consumer will do with it (acceptance test)

Given `R : RelativeWatanabeModificationOn f W S` and a finite cover of the zero set over a compact
`S₁ ⊆ S` by relative chart boxes, laplace will:

1. write each chart contribution to `∫ φ e^{-t f_s} dx` as an integral of the form treated by
   `SPFamilyData` (one active exponent) or its several-active-exponent analogue (to be added to
   laplace: the generalised Gaussian moments `∫ ∏ u_j^{m_j} e^{-∏ u_j^{2k_j}}` and the
   Newton-polytope leading pole, which is greybook Ch4 material);
2. read off that `(λ, m)` is constant on `S` (from constant `(k, h)` and positivity of `a`);
3. prove `HasDerivAt (fun s ↦ coefficient s) (Σ_charts Cov(test, score_chart)) s₀` by
   `hasDerivAt_normalized_of_dominated` on each chart and `HasDerivAt.sum`;
4. state the theorem of §1 and record in `germbij_slop.tex` S7 that Level 3 is unconditional on
   `S'`.

An acceptance test for the hironaka side, independent of laplace: for `f x s = a(s) · x₁^{2k}` with
`a` analytic positive, the relative modification is the identity with the obvious chart, `k` constant;
for `f x u = x⁴ + u²x²`, the generic set `S'` must exclude `u = 0`.

## 5. Mathematical background and pointers (from the Astra consult of 2026-09-21,
`laplace/gpt_responses/research_truth_variation_v1.md`)

- Generic simultaneous resolution (characteristic zero, algebraic families): resolve the generic
  fibre and spread out over a nonempty Zariski-open subset of the base; after shrinking one obtains
  relative smoothness and relative simple normal crossings. Resolving the total space does **not**
  by itself resolve every fibre. Analytic families have local analogues; "Zariski-open dense" must
  be replaced by the appropriate analytic notion.
- Equisingularity notions are **not interchangeable**: Whitney equisingularity, Zariski
  equisingularity and algorithmic equiresolution (Encinas–Nobile–Villamayor, *On algorithmic
  equiresolution and stratification of Hilbert schemes*) are different hypotheses; the campaign
  should fix the one whose relative monomialisation properties are actually used, and state it.
  The functorial (Włodarczyk/Kollár) proof strand already in hironaka is the natural route: the
  functoriality with respect to smooth morphisms (hironaka's `resolution_functorial`,
  `localResolutionIndependentOn`) is the ingredient that makes the algorithm commute with the
  projection to `S` on the good locus.
- Fixed exponent data `(k, h)` fix the **candidate** pole set `{-(h_j + 1 + ℓ)/(2 k_j)}`; actual
  poles can disappear by cancellation, but the leading pole is stable given positivity of the
  amplitude, which SLT losses have. The consumer only needs the leading pole and the coefficients.
- The real RLCT has **no** semicontinuity direction: `x⁴ + u²x²` (special fibre more singular,
  λ: 1/2 → 1/4) and `(x²+y²+z²+2ux)²` in `ℝ³` (special fibre less singular, λ: 1/2 → 3/4) are both
  nonnegative analytic families. This is why the theorem is generic, not everywhere.
- Subtracting `min L_s` need not preserve analytic parameter dependence (switching minimisers);
  the spec above therefore takes `f` itself nonnegative with `0` in the zero set for every `s`, and
  leaves the minimiser bookkeeping to the consumer.

## 6. Non-goals

- No claim about the full actual pole set or about log multiplicities beyond the leading pair.
- No complex-analytic or algebraic variant is required; real-analytic, as in the existing exports.
- No statement across strata: the boundary behaviour (crossover, `u t^β` variables) is the
  consumer's business (`ToyCrossover.lean` is the model example).

---

## Revisions after the hironaka planning round (2026-09-21/22)

Chris's planning note ("Relative resolution for SLT: what the hironaka side will deliver, and what
the consumer side must settle", 21 September 2026) was checked against this spec and against the
repositories. The consumer side accepts the following; the record described there supersedes §3 of
this document where they differ.

### Accepted producer decisions

- **D0** (built on `timaeus-research/hironaka` main, `a3b0fd098`, not on the fork). Confirmed: the
  interface quoted in §2 above (`WatanabeModificationOn`, `EvenChartBox`,
  `exists_watanabeModificationOn`) exists only on `dmurfet/hironaka` branch `sector-atlas`
  (`cb11bc8d9`); the certified input `watanabe_thm_2_3_of_isConnected`, `IsAnalyticIsoOver`,
  `exists_chart_absorbing_unit` are on upstream main. Nothing on the consumer side depends on the
  fork's names.
- **D1** (record over `V × S'` with `cl(V)` compact in `W`; `S'` open and dense in `S`).
- **D2** (all `d, p ≥ 1`), **D4** (no fibrewise canonicity), **D5** (product typing).
- **D3** (equiresolubility with respect to a fixed total-space resolution, provisional): acceptable
  as the hypothesis of the local statement. The consumer needs only the chart-form output; whether
  a printed equisingularity notion also characterises the good set is of interest for interpreting
  the stratification of truth space, not for the bridge.

### Accepted edits to this spec

1. **Density.** Read `Dense S'` as `S' ⊆ S ∧ IsOpen S' ∧ S ⊆ closure S'`. The ambient reading was an
   error in this document.
2. **`W` relatively compact.** Add `IsCompact (closure W) ∧ closure W ⊆ U₀` to the existence theorem.
3. **Base point.** Replace `h0W`/`hne` by "`F` does not vanish identically on any nonempty open subset
   of `W × S`"; the base-point form is a corollary.
4. **Nonnegativity** only on `W × S`.
5. **`smoothOverS`** dropped as a field (derived).
6. **The unit.** Accepted that `a` may be the constant `1` on some charts after the unit is absorbed
   into a `u`-coordinate (the note's "`±1`" should read `1`, since `a > 0` is a clause). No
   normalisation of `a` is needed on the consumer side: the response theorems take the score
   `∂_s b / b − e · ∂_s a / a` as it comes, and with `a ≡ 1` the whole `s`-dependence sits in `b`.
7. **Jacobian sign.** Accepted; the bridge applies `|det| = |b| ∏ |u_j|^{h_j}`.
8. **Several active variables, `p > 1`.** Consumer-side additions, not yet done.
9. **Typing.** Accepted.

### Consumer-side obligations (status)

| Obligation (note §6) | Status |
|---|---|
| 4. Remainder term | **Done** (laplace, this commit): `RelativeChartDecomposition` now carries a remainder `R s t`, and `tendsto_rpow_mul` takes `t^λ R s t → 0`; `tendsto_rpow_mul_of_exp_remainder` shows an `O(e^{-εt})` remainder qualifies. |
| 5. Localisation in `s` | **Done**: `RelativeChartFamily S' …` quantifies over `s ∈ S'` and the response theorems take `S' ∈ 𝓝 s₀`. |
| 3. Uniform bounds on nested compact boxes | Consumer takes the bounds as hypotheses of `RelativeChartFamily`; the bridge must supply them from the closed box `[−ρ, ρ]^d × closedBall(s_P, σ)` in the record. Not yet done. |
| 1. Finite cover, 2. injectivity, 6. moving amplitudes | Bridge-side; not yet done. |
| 7. Positivity on a minimising chart | Noted. `tendsto_rpow_mul` is true regardless (the limit is then `0` and `λ = min e_i` is only a lower bound on the exponent); the identification of `λ` with the RLCT needs the leading amplitude nonzero at the divisor, which holds for a positive prior and cutoff. This is the "second failure mode" of the crossover section (germbij_slop.tex S8). |
| Bridge location | Recommended: greybook `Extras/Germbij` (already depends on hironaka, toolchain `v4.33.1`); laplace stays hironaka-free and exports the chart theorems. |

### Acceptance test T2

The note's exclusion argument for `x⁴ + u²x²` (no relative Watanabe modification over `V × S'` with
`0 ∈ S'`, for any resolution, by comparing vanishing orders `2k = 2(h+1)` at `s ≠ 0` against
`2k = 4(h+1)` at `s = 0`) was checked and is correct. It makes the crossover section's "first failure
mode" a theorem rather than an observation about one chart choice. The consumer does not have the
bridge from a chart decomposition to `t·E[L] → λ`; the limits `1/4` and `1/2` in
`Laplace/Multi/ToyCrossover.lean` are proved directly.

---

## The record landed (2026-09-22): verification and bridge plan

**Producer.** `timaeus-research/hironaka` main `a8897879f` (Extension A). Statements of record in
`Statements/Record/RelativeChartForm.lean` (`Statements.exists_relativeWatanabeModificationOn_generic`,
`…_generic_of_zero_at_origin`) and `Statements/Record/RelativeChartFormLocal.lean`
(`Statements.exists_relativeWatanabeModificationOn_of_equiresoluble`); vocabulary in
`Monomialize/Relative/Vocabulary.lean` (`IsRelativeWatanabeChart`, `RelativeWatanabeChartAt`,
`RelativeWatanabeModificationOn`, product typing, closed box `centeredBox d ρ ×ˢ closedBall s_P σ`,
`a > 0`, `b ≠ 0`, `relJacobian` = det of the `u`-block). Fibre specialisation in
`Monomialize/Relative/Fibre/*` (`fibreAnalyticManifold`, `fibreBlowDown` proper/surjective/iso off
the zero set, `watanabeChartAt_fibreBlowDown`, `slice_phase`/`slice_jacobian` with the same `(k, h)`,
`volume_fibre_zeroSet_eq_zero`).

**Audit (this session, worktree `lean/hironaka-upstream` at `a8897879f`).** `lake build` of
`Proofs.Record.RelativeChartForm` and `Proofs.Record.RelativeChartFormLocal`: 9769 jobs, clean.
`#print axioms`: `Proofs.Record.RelativeChartForm.exists_relativeWatanabeModificationOn_generic`,
`…_generic_of_zero_at_origin`, and `Monomialize.Relative.exists_relativeWatanabeModificationOn_of_equiresoluble`
(the local twin is a `hironaka_type_eq` check against it) each depend only on
`propext, Classical.choice, Quot.sound`. The single textual "sorry" under `Monomialize/Relative/` is a
word in a docstring (`TotalSpace/ApplyCertified.lean:22`).

**How hironaka is consumed today.** Not by a change of variables in the Laplace integral. greybook
(`Extras/Germbij/AnalyticLaplace.lean`) goes modification → `LogResolutionData` (finite chart family,
`Monomialize/VolumeScaling/Interface.lean`) → `Monomialize.Analytic.hasLLCExponentsOn_closedBall
(D) : HasLLCExponentsOn volume (closedBall w r) f D.combLam D.combTheta` (sublevel-volume Θ-form;
`combLam = inf_α (chart α).lam`, `combTheta = sup over minimisers of (chart α).theta`) → Θ-form
Abelian transfer to `Z(t) = Θ(t^{-λ} log^{θ-1} t)`. The readout IS data-preserving, so the exponent
pair of a sliced relative family is a function of the frozen `(k, h)`.

**Correction to the consumer goals (Astra, `gpt_responses/research_relative_bridge_v1.md`).** Local
constancy of `(λ, θ)` on `S'` is FALSE for an arbitrary compactly supported prior: `f(x, s) = (x − s)²`
with prior `x² η(x)` has `Z_0 ~ t^{-3/2}`, `Z_s ~ s² t^{-1/2}` although the identity is a relative
modification with `(k, h) = (1, 0)` on all of `S`. The prior must be positive at every zero in its
support at the reference parameter (the amplitude-vanishing failure mode of germbij_slop S8), and the
statement is local in `s`. Coefficient differentiability additionally needs a smooth prior
(`1 + |x|` gives `C(s) = √π (1 + |s|)`).

**Bridge plan (route R1 first, then R2 in `d = p = 1`), home: greybook `Extras/Germbij`, hironaka pin → `a8897879f`.**

First bridge theorem (weighted local Θ, `d = p = 1`): for `M : RelativeWatanabeModificationOn f V S'`,
`f ≥ 0` on `V × S'`, a continuous compactly supported prior `φ ≥ 0` with `tsupport φ ⊆ V`, a reference
`s₀ ∈ S'` with at least one zero of `f(·, s₀)` in `tsupport φ` and `φ > 0` at every such zero: there
are `λ : ℚ`, `0 < λ`, and an open `T ∋ s₀`, `T ⊆ S'`, with
`HasLLCExponentsOn (volume.withDensity (ofReal ∘ φ)) V (fun x ↦ |f x s|) λ 1` for all `s ∈ T`; Abelian
corollary: a common `HasLaplaceTheta (λ, 1)` on `T`. Sub-lemmas:
1. `exists_uniform_relativeChartCover_near` — from properness: a parameter neighbourhood `T` of `s₀`
   and finitely many relative charts at points of the fibre over `s₀`, with shrunken boxes, covering
   the lifted zeros over `tsupport φ × T`; fixed `(k i, h i)`.
2. `relativeChartCover.slice_logResolutionData` — for each `s ∈ T`, a `LogResolutionData` for
   `f(·, s)` from the slices (`slice_phase`, `slice_jacobian`, `volume_fibre_zeroSet_eq_zero`).
3. `combLam_slice_eq`, `combTheta_slice_eq` — the pair depends only on `(k, h)`, hence is constant on `T`.
4. `hasLLCExponentsOn_closedBall` (exists) → weighted compact version: finite-cover gluing, comparison
   with a prior bounded above and below near the zeros, removal of the region `f ≥ δ`.
5. Assembly and the Laplace Θ corollary.
Estimated 1,000–2,500 lines. R2 (chartwise change of variables in `d = 1`, giving a
`RelativeChartDecomposition` and hence coefficients and expectations via laplace's
`RelativeChartFamily`) is a subsequent several-thousand-line campaign; it needs a parameter-dependent
cutoff in the decomposition interface (partition weights `ψ_i(u, s)`) and a derivative bound on the
remainder, not just the remainder bound. General `d` needs a multi-active monomial leading theorem
(log factors from tied exponents), a separate campaign.
