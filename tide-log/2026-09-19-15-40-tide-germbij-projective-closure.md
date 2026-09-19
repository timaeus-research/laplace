# Tide: germbij projective identifiability closure

**Direction (user):** "Ok let's continue with the formalisation and exploration of this … statements involving actual expectation values (i.e. with the 1/Z incorporated) …" — continued on auto; this tide takes the two stretch corollaries recorded by the normalized-singular tide (equal zero loci in projective form; the scalar `C(t) = 1 + o(t^{-∞})`).
**Seabed:** laplace, commit a52c51b (main; NormalizedSingular + SufficientFamilies merged)
**Started:** 2026-09-19T15:40Z
**Ledger direction:** germbij: projective (normalized) identifiability closure — equal zero loci forced and the scalar C(t) = 1 + o(t^-infty), via a Gaussian-type lower bound of the localized Laplace integral near a zero.

## Seabed snapshot

- `normalized_families_force_germ_eq_at/_eq_near` (NormalizedSingular): projective SuperPoly agreement over
  `C_c^∞` ⇒ `L₁ = L₂` near common zeros; `normalized_expectations_force_eq_near` (1/Z form with window χ).
- `sector_lower_bound_multi` (Sector): `vol(S)·c²·e^{-4C₀}·t^{-m-d/2} ≤ ∫_{t^{-1/2}S} a² e^{-tK}` given
  `K ≤ C₀‖w‖²` on a ball and `|a(t^{-1/2}x)| ≥ c t^{-m/2}` on `S`. With `a ≡ 1`, `m = 0` this is the
  Gaussian-type lower bound `∫ e^{-tK} ≳ t^{-d/2}` — assembled once already inside
  `analytic_square_weight_eq_zero_near`, not yet as a standalone lemma.
- `quadratic_upper_bound_of_nonneg` (SingularPrep): `C²`, `K(0)=0`, `K ≥ 0` near 0 ⇒ `K ≤ C₀‖w‖²` on a ball.
- `exists_bump_one_on_ball` (SingularPrep); `laplace_moment_bounded`, `anchor_moment_eq` (OnePointAnchoring):
  `|∫φ e^{-tL}| ≤ ∫|φ|` for `t ≥ 0`, exact equality of anchor moments on a region where `L₁ = L₂`.
- `superPoly_of_mul_anchor`, `superPoly_sub_of_scalar_gauge`, `anchored_proportionality_remove_scalar`
  (Anchoring): the scalar-gauge algebra, all conditional on a polynomial lower bound `hanchor_low`
  which the seabed never discharges. `lower_bound_not_superpolynomial` (Decay).
- Missing: (i) a standalone Gaussian-type lower bound near a zero; (ii) exponential smallness of
  `∫ψ e^{-tL}` when `L ≥ δ > 0` on `supp ψ`; (iii) the polynomial bound `|C(t)| = O(t^{d/2})`; (iv) the
  equal-zero-loci theorem; (v) `SuperPoly (C − 1)` and the transfer projective ⇒ exact.

## Candidates v1 (Claude)

Notation: `I_i(φ, t) = ∫ φ e^{-tL_i}`, `R_φ = I₂(φ) − C·I₁(φ)`; hypothesis "projective" = `SuperPoly R_φ` for all `φ ∈ C_c^∞`
(or for all continuous compactly supported `φ` — the closure results below need only bumps, so the weaker
hypothesis class suffices and I will state them for the `C_c^∞` class to compose with NormalizedSingular).

### G. Gaussian-type lower bound near a zero (standalone lemma; a ≡ 1 case of the sector bound)
```
theorem exists_lower_bound_integral_exp_near_zero {K ψ} {p}
    (hKc : Continuous K) (hK0 : ∀ w, 0 ≤ K w) (hKp : K p = 0) (hK2 : ContDiffAt ℝ 2 K p)
    (hψc : Continuous ψ) (hψs : HasCompactSupport ψ) (hψ0 : ∀ w, 0 ≤ ψ w)
    {R : ℝ} (hR : 0 < R) (hψ1 : ∀ w, ‖w − p‖ ≤ R → ψ w = 1) :
    ∃ κ T₀ : ℝ, 0 < κ ∧ ∀ t, T₀ ≤ t → κ * t ^ (-(Fintype.card ι : ℝ)/2) ≤ ∫ w, ψ w * exp(-(t * K w))
```
Copy of the assembly inside `analytic_square_weight_eq_zero_near` with `a ≡ 1`, `m = 0`, `S = ball 0 1`.
Discharges the seabed's standing `hanchor_low` hypothesis (used by `superPoly_of_mul_anchor`,
`anchored_proportionality_remove_scalar`, `one_point_anchoring_contradiction`). ~120 lines.

### E. Exponential smallness away from the zero set
`L` continuous, `L ≥ δ > 0` on `tsupport ψ`, `ψ` continuous c.s. ⇒ `|∫ ψ e^{-tL}| ≤ (∫|ψ|) e^{-tδ}` for `t ≥ 0`,
hence `SuperPoly (fun t ↦ ∫ ψ e^{-tL})` and even `O(t^{d/2} e^{-tδ})`-type products stay SuperPoly. ~50 lines.

### Z. Equal zero loci, projective form (no analyticity)
```
theorem zero_locus_eq_of_projective {L₁ L₂} (h1 : ContDiff ℝ 2 L₁) (h2 : ContDiff ℝ 2 L₂)
    (hL1 : ∀ w, 0 ≤ L₁ w) (hL2 : ∀ w, 0 ≤ L₂ w) {C : ℝ → ℝ} (hfam : projective over C_c^∞)
    (hne1 : ∃ p, L₁ p = 0) (hne2 : ∃ q, L₂ q = 0) :
    {w | L₁ w = 0} = {w | L₂ w = 0}
```
Proof. (⊆) `p ∈ Z(L₁) \ Z(L₂)`: `L₂ ≥ δ` near `p`; bump `ψ` there: `I₂(ψ)` SuperPoly (E), so `C·I₁(ψ)` SuperPoly;
`I₁(ψ) ≥ κ t^{-d/2}` (G) ⇒ `SuperPoly C` (variant of `superPoly_of_mul_anchor` with `C` in place of `C−1`).
Then every `I₂(φ) = R_φ + C·I₁(φ)` is SuperPoly (`I₁(φ)` bounded, `laplace_moment_bounded`), contradicting
G at `q ∈ Z(L₂)`. (⊇) `q ∈ Z(L₂) \ Z(L₁)`: from a bump at `p ∈ Z(L₁)`: `|C(t)| ≤ (∫ψ_p + 1)·t^{d/2}/κ`
eventually (bounded `I₂`, G for `I₁`); bump `ψ_q`: `I₁(ψ_q) ≤ M e^{-tδ}` so `C·I₁(ψ_q)` is SuperPoly
(polynomial × exponential), hence `I₂(ψ_q)` SuperPoly, contradicting G at `q`. ~150 lines.
Both zero sets nonempty is necessary (`L₂ = L₁ + c` is projective with `C = e^{-ct}`).

### R. Scalar rigidity and the transfer projective ⇒ exact
```
theorem superPoly_scalar_sub_one_of_eqOn {L₁ L₂} … {p} (hp : L₁ p = 0) (hEq : ∀ᶠ w in 𝓝 p, L₁ w = L₂ w)
    (hfam : projective) : SuperPoly fun t ↦ C t − 1
theorem superPoly_difference_of_projective … : ∀ φ ∈ C_c^∞ (or continuous c.s.), SuperPoly fun t ↦ I₂(φ) − I₁(φ)
```
Proof: bump `ψ₀` inside the agreement neighbourhood: `I₁(ψ₀) = I₂(ψ₀)` exactly (`anchor_moment_eq`), so
`(C−1)·I₁(ψ₀) = −R_{ψ₀}` SuperPoly; G gives the anchor lower bound; `superPoly_of_mul_anchor`; then
`superPoly_sub_of_scalar_gauge` with `laplace_moment_bounded`. ~60 lines. Composed with
`normalized_families_force_germ_eq_at` (which supplies `hEq`): **projective agreement + one common
analytic zero ⇒ exact (unnormalized) agreement beyond all orders for every observable.** So the whole
unnormalized theory (pencil theorem etc.) applies to normalized data.

### N. The 1/Z package (headline for the paper)
```
theorem normalized_expectations_closure {L₁ L₂ χ} (h1 h2 : ContDiff ℝ ∞) (hL1 hL2 : nonneg)
    (hA1 hA2 : analytic at every zero) (hne1 hne2 : zero sets nonempty)
    (hχ … window, hZ1 hZ2 positivity) (hfam : Φ_{L₁} = Φ_{L₂} over C_c^∞) :
    {L₁ = 0} = {L₂ = 0} ∧ (∃ U open ⊇ {L₁ = 0}, EqOn L₁ L₂ U) ∧ SuperPoly (fun t ↦ Z₂ t / Z₁ t − 1)
      ∧ ∀ φ ∈ C_c^∞, SuperPoly (fun t ↦ I₂(φ) − I₁(φ))
```
Z + `normalized_families_force_eq_near` at `W₀ = Z(L₁) = Z(L₂)` + R with `C = Z₂/Z₁`. ~80 lines.

**Proposed tide:** G + E + Z + R + N in one file `Laplace/Multi/ProjectiveClosure.lean` (~450 lines).
Vote: all five; G is the load-bearing new lemma, Z and R the new theorems, N the paper statement.

## GPT-6 Astra v1 (summary; verbatim in `gpt_germbij_projective_v1.md`)

- G, E, Z correct. Z needs only global continuity + C² near the zeros (a polynomially visible anchor at
  every zero); "both zero sets nonempty" is the right sharp nondegeneracy. No issue with C negative or
  non-measurable: all estimates are pointwise in t, `|C| I₁ ≤ |I₂| + |R|`.
- R correct for the tested class (C_c^∞): projective ⇒ exact for every observable IN THE HYPOTHESIS CLASS.
  Upgrading to continuous/bounded measurable tests needs a separate argument: local total variation
  `∫_K |e^{-tL₂} − e^{-tL₁}| ∈ SuperPoly` via `|a−b|² ≤ t·D·(a−b)`, `D = L₂−L₁`, tested at the smooth
  observable `η²D`. Recorded as follow-up; do not smuggle it in.
- N correct; normalized ⇒ projective is fine (Z₂ bounded for t ≥ 0). The CONVERSE needs 1/Z₂ control
  (window positive near a zero + G); positivity alone is not enough. Do not claim an unrestricted
  equivalence.
- Analyticity enters ONLY via the merged germ theorem (supplying `hEq`); make R analyticity-free.
- Extra target (b): scalar tameness BEFORE Z: `c t^{-d/2} ≤ C(t) ≤ A t^{d/2}` eventually (upper from a
  bump at a zero of L₁, lower + eventual positivity from a bump at a zero of L₂). Organise: G+E →
  tameness → Z → R → N.
- Headline for the paper: "at a common analytic zero, projective agreement fixes its own scalar gauge";
  normalized and unnormalized identifiability coincide modulo SuperPoly errors in that regime (not
  literally; additive constants remain ambiguous without a zero-level anchor).
- Different windows: denominators-only changes are harmless; windowed numerators are NOT (χ₂ = aχ₁ gives
  identical normalized expectations with Z₂/Z₁ = a).

## Vote
- Claude: G + E + tameness + Z + R + N, one file `Laplace/Multi/ProjectiveClosure.lean`; TV upgrade as follow-up
- GPT-6 Astra: ship G+E+tameness+Z+R+N together, smooth-test conclusions first, continuous-test upgrade explicit or deferred

## Numerical check
Not feasible: structural statements (existence of bounds, equality of zero sets, SuperPoly). The one closed
form, the anchor exponent `t^{-d/2}`, is the Gaussian volume scaling already checked in the sector arc.

## Step 3 plan
`Laplace/Multi/ProjectiveClosure.lean` (imports NormalizedSingular, OnePointAnchoring): (G) `exists_lower_bound_integral_exp_of_quadratic`
(a ≡ 1 sector bound), `exists_lower_bound_integral_exp_near_zero` (C² interface), `anchor_lower_bound_eventually`
(integer power `t^{-d}`, the seabed's `hanchor_low` shape); (E) `abs_integral_mul_exp_le_of_gap`,
`superPoly_integral_mul_exp_of_gap`, `superPoly_polyBounded_mul_integral_of_gap`; tameness
`exists_scalar_upper_bound`, `eventually_scalar_lower_bound`; (Z) `superPoly_scalar_of_zero_gap`,
`zero_iff_zero_of_projective`; (R) `superPoly_scalar_sub_one_of_eventuallyEq`, `superPoly_difference_of_projective`;
(N) `normalized_expectations_closure`. Smooth bumps via `ContDiffBump p`.

## Result

Commit `001f1f0` on `tide/germbij-projective-closure`: `Laplace/Multi/ProjectiveClosure.lean` (657 lines), imported
from `Laplace.lean`; `lake build` clean (8890 jobs), `scripts/sorries` 0/0/0/0. Two LSP rounds (ten errors total:
one implicit `p`, one `one_pow` simp-shape in the sector bound, one beta-redex before `rw`, and `ContDiff.of_le (by simp)`
for `2 ≤ ∞` which does not fire — replaced by `AnalyticAt.contDiffAt`).

Theorems: (G) `exists_lower_bound_integral_exp_of_quadratic`, `exists_lower_bound_integral_exp_near_zero`,
`anchor_lower_bound_eventually`, `not_superPoly_integral_exp_near_zero`; (E) `abs_integral_mul_exp_le_of_gap`,
`superPoly_polyBounded_mul_integral_of_gap`, `superPoly_integral_mul_exp_of_gap`; `ProjectiveAgreement` (def),
`gapBump`, `exists_gapBump_of_pos`; tameness `exists_scalar_upper_bound`, `eventually_scalar_lower_bound`;
(Z) `superPoly_scalar_of_zero_gap`, `zero_iff_zero_of_projective`; (R) `superPoly_scalar_sub_one_of_eventuallyEq`,
`superPoly_difference_of_projective`, `projective_forces_exact_at`; (N) `projectiveAgreement_of_normalized`,
`normalized_expectations_closure`.

Surprises: (1) the seabed's `hanchor_low` hypothesis (three consumers, never discharged since the anchoring tide)
falls to the `a ≡ 1` case of the sector bound in 90 lines; (2) `ContDiff.of_le` to grade 2 from `∞` has no
one-liner on this pin — analyticity at the zeros (already assumed for the germ theorem) is the cheap route;
(3) `eventually_scalar_lower_bound` gives eventual POSITIVITY of the scalar with no sign assumption anywhere.
