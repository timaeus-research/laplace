# Handoff: the transverse active-truth face theorem (analytic half)

**STATUS 2026-09-25: the constant-unit theorem is landed for `I = ∅` (`ActiveTruthTheorem.lean`, `tendsto_modelKernel_activeTruth'`) AND with spectators (`ActiveTruthSpectator.lean`, `tendsto_modelKernel_activeTruth_spectator`, extra factor `∏ ρ^{dᵢ}/dᵢ`; route: `ActiveTruthUniform` = lintegral form + uniform bound, `SpectatorEnvelope` = one-variable integrability, outer DCT in `ξ`). The exact trace model `W = w(u)`, `a = a(u)` is landed too (`ActiveTruthTraceTheorem.lean`, `tendsto_modelKernel_trace`, constant `A Γ(β) B^{-β} q D^{-qη} vol(F')/|det M| ∫_0^ρ u^{qη−1} w a^{-β}`). Remaining (Astra round 9 order): the weighted fibre lemma, the general trace replacement `W(x,u)` (needs a.e. positivity of the reconstructed coordinates on `F'`), the chart wrapper `TermData.activeTruth`, spectators with traces, the example identification with `degI`.**

**TL;DR.** Astra (round 7, `gpt_responses/research_round7_v1.md`) gave the general statement behind
the degenerate example (`DegenerateFace.lean`, `t⁴ I(t)/log t → 1`): with a dual certificate
`(β, η)`, coordinates `J ⊔ I` (`c_j = βκ_j − ηQ_j` on `J`, reduced costs `d_i > 0` on `I`),
`κ_J, Q_J` independent, the face `F_J = {α_J ≥ 0 | κ_J·α = δ, Q_J·α = γ}` with a positive point,
`k = |J| − 2`, `λ = γp + βδ − ηγ`: `t^λ/(log t)^k · K(t) → A q D^{-qη} Γ(β)/(𝒥 B^β) · H^k(F_J) ·
∫_{(0,1)^I} ∏ y^{d_i−1} ∫_0^ρ v^{qη−1} W₀/a₀^β`. The LP half is done (`ActiveTruthLP.lean`) and the
polytope-fibre core is done (`PolytopeFibre.lean`). This note is the plan for the analytic half,
constant units first (`W ≡ w₀`, `a ≡ a₀`, `I = ∅`).

## Proven (dependency order)

- `ActiveTruthLP.lean`: `dual_identity`, `lpOptimal_activeTruth_iff` (optimal set = the face),
  `lpOptimal_deg_iff` (the example's LP).
- `PolytopeFibre.lean`: `volume_hyperplane`, `poly2`, `fibre2_eq_smul`, `volume_fibre2`
  (`= ofReal (L^k) * volume (poly2 … (a + b/L))`), `tendsto_volume_poly2`.
- `TwoScaledInner.lean` (older): `integral_posOrthant_comp_exp`, `integrableOn_posOrthant_comp_exp_iff`
  (the exponential substitution on the positive orthant), `integral_exp_mul_exp_neg_exp`
  (`∫ e^{ηv} e^{-c e^v} dv = Γ(η) c^{-η}`), `integral_twoScaledInner` (the `(s, h)` integral for
  `k = 0`: `Γ η c^{-η} (e^{-θh}/θ)/|Δ|`).
- `LinearChange` / `GaussianMomentsPosDef`: `integral_comp_mulVec`, `integrable_comp_mulVec_iff`.
- `LogCoordinates.lean` (step 1a): `integral_box_eq_orthant`, `integrableOn_box_iff_orthant`.
- `ActiveTruthModel.lean` (step 1b): `logCut`, `cutVar_negExp_lt_iff`, `modelIntegrand_const_negExp`,
  `modelKernel_const_eq_log` (the kernel as an orthant integral in `z`).

- `LintegralChange.lean`: `lintegral_sum_split`, `lintegral_comp_mulVec_add`.
- `ActiveTruthAssembly.lean` (step 2): `transMat`, `transShift`, `transMat_mulVec_add_shift`,
  `image_mulVec_add_orthant`, `innerKv`, `logIntegrand`, `lintegral_inner_subst`.
- `ActiveTruthAssembly.lean` (step 3): `fibreSet`, `vWeight`, `innerKv_eq`, `lintegral_innerKv_swap`.
- `ActiveTruthFibre.lean` (step 4): `fibreCoef`/`fibreA`/`fibreB`, `mem_fibreSet_iff`,
  `fibre2_subset_box`, `volume_fibreSet_eq`, `volume_fibreSet_le`, `isBounded_poly2_fibre`,
  `tendsto_volume_fibreSet_div`.
- `ActiveTruthLimit.lean` (step 5): `sWeight`/`hWeight`, `lintegral_vWeight_zero`,
  `pow_abs_add_le_exp`, `integrable_sWeight_mul_pow`, `volume_fibreSet_div_le`,
  `tendsto_lintegral_vWeight_fibre`.
- `ActiveTruthTheorem.lean` (assembly): `modelKernel_const_eq_lintegral`, `lintegral_logIntegrand_eq`,
  `facePolytope`, `tendsto_modelKernel_activeTruth`, `activeTruth_const_eq`,
  `tendsto_modelKernel_activeTruth'` — **the constant-unit theorem is DONE** (68b3d17).

## Decision: do steps 2–5 in `lintegral` form

As in `DegenerateFace.lean`: convert the model kernel once with `ofReal_integral_eq_lintegral_ofReal`
(the integrand is bounded by `w₀ ∏ x^r` on the box, integrable for `r > −1`), then all substitutions
are `lintegral_map` against `Real.map_linearMap_volume_pi_eq_smul_volume_pi` / translations, Tonelli
swaps are free, and the only analysis is the final `tendsto_lintegral_filter_of_dominated_convergence`.
Bound the fibre volume by `((s + δL)/κ_min)^k` directly (from `κ·z = s + δL`, `z ≥ 0`, `κ > 0`)
rather than through `poly2` inclusions.

## The target (constant units, `I = ∅`, all coordinates tied to the face)

`K(t) = A t^{-γp} ∫_{(0,1)^n, D t^{-γ/q} ∏ x^{-Q/q} < ρ} w₀ ∏ x^r e^{-B t^δ a₀ ∏ x^κ} dx`,
`c = r + 1 = βκ − ηQ`, `n = k + 2`, `R = (κ_a κ_b; Q_a Q_b)` invertible for two indices `a, b`.
Claim: `t^{γp + βδ − ηγ}/(log t)^k · K(t) → A w₀ Γ(β) (B a₀)^{-β} (ρ/D)^{qη}/η · vol(F')/|det R|`
where `F' = {α' ∈ ℝ^k_{≥0} | α_a(α') ≥ 0, α_b(α') ≥ 0}` is the projected face (`α_a, α_b` solve
`κ·α = δ, Q·α = γ` in terms of `α'`). (`vol F'/|det R| = H^k(F_J)/𝒥`.)

## Proof plan (each step a lemma)

1. **Log substitution.** `x = e^{-z}`, `z ∈ ℝ^n_{≥0}`: `∏x^r dx = e^{-c·z} dz` (`c = r + 1`),
   `t^δ ∏ x^κ = e^{δL − κ·z}` (`L = log t`), cut `D t^{-γ/q} ∏ x^{-Q/q} < ρ ⟺ Q·z − γL < q log(ρ/D)`.
   Use `integral_posOrthant_comp_exp` on the orthant (or redo: `integral_image_eq_integral_abs_det_fderiv_smul`
   with the diagonal `expDeriv`).
2. **Linear change to `(s, h, z')`.** `s = κ·z − δL`, `h = γL − Q·z`, `z' = z_{J∖{a,b}}`; the map
   `z ↦ (s, h, z')` is affine with linear part `M` (`|det M| = |det R|`), and `c·z = βs + ηh + mL`
   with `m = βδ − ηγ` (from `c = βκ − ηQ`). Use `integral_comp_mulVec` (the inverse map) plus a
   translation. The integrand becomes `w₀ e^{-mL} e^{-βs − ηh} e^{-B a₀ e^{-s}} 1_{h > q log(D/ρ)}` times
   the indicator of the fibre `{z' | z ≥ 0}` = `fibre2 c₁ c₂ a₁ a₂ b₁ b₂ L` with `b_i = b_i(s, h)` affine.
3. **Fubini.** Separate `(s, h)` from `z'`: `∫_{(s,h)} w₀ e^{-mL} e^{-βs−ηh} e^{-Ba₀e^{-s}} 1_{h > q log(D/ρ)}
   · volume(fibre2 … L) d(s,h) / |det R|`. Then `t^{γp+m} K = A w₀ / |det R| · ∫ e^{-βs−ηh} e^{-Ba₀e^{-s}} 1 ·
   volume(fibre2 … L)`.
4. **DCT in `(s, h)`.** `volume(fibre2 … L)/L^k = volume(poly2 (a + b(s,h)/L)) → vol F'` pointwise
   (`tendsto_volume_poly2`); domination: `volume(poly2 (a + u)) ≤ C (1 + |u₁| + |u₂|)^k` (needs a
   lemma: when the two constraints bound the orthant, `poly2 c₁ c₂ (a₁+u₁) (a₂+u₂) ⊆ closedBall 0
   (C (1 + |u₁| + |u₂|))`; then `volume ≤ ofReal ((2C(1+…))^k)` by `Real.volume_pi_closedBall`), and
   `e^{-βs−ηh} e^{-Ba₀e^{-s}} (1 + |s| + |h|)^k` integrable on `s ∈ ℝ`, `h > q log(D/ρ)` (β, η > 0;
   `∫ e^{-βs} e^{-Ba₀e^{-s}} |s|^j` finite: Gamma integrals with logs — bound `|s|^j ≤ C_j (e^{εs} + e^{-εs})`
   and use `integral_exp_mul_exp_neg_exp` at `β ± ε`).
5. **Limit.** `∫ e^{-βs} e^{-Ba₀e^{-s}} ds = Γ(β)(Ba₀)^{-β}` (`integral_exp_mul_exp_neg_exp`, `v = −s`),
   `∫_{h > q log(D/ρ)} e^{-ηh} dh = (ρ/D)^{qη}/η`.

## Then

- Spectator coordinates `I` (density `∏ y^{d_i−1}`) — the same with `y` frozen in the Fubini.
- Face traces `W₀(y, v), a₀(y, v)` — localisation away from the relative boundary of `F_J`
  (Astra: dominating factor `(1 + |log w| + |log v| + ∑|log y_i|)^k ∏ y^{d−1} v^{qη−1} w^{β−1} e^{-Ba_-w}`).
- The chart-level wrapper (`WallChartsData.Phase`: `A = |σ|^p/q`, `B = |σ|^ν`, `D = |σ|^{1/q}`) and a
  `TermData.activeTruth` constructor for the certificate.

## Friction to expect

- Big-operator bodies swallow trailing `* exp …`: parenthesise `(∏ j, x j ^ r j) * exp …`.
- `∞` is a token: no `degΦ∞`-style identifiers.
- `lintegral_lintegral_swap` needs `(μ := volume) (ν := volume)` and `aemeasurable (μ := volume.prod volume)`.
- Interval scalings: `Real.map_volume_mul_left` + `lintegral_map` (`lintegral_Ioo_comp_mul_left'`).
- `Set.indicator_of_mem` with an `∈ {p | …}` membership needs a `show … from` ascription.
