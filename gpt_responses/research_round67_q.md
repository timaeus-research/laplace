# Research round 67: the analytic response atlas — route through Mathlib's ω-grade calculus

## Landed since round 66 (laplace `Laplace/Multi/*`, sorry-free, pushed)
- **L1PointwiseDeriv + ThirdJet** (round-66 rank 3, "projection after differentiation"): the principle
  `coeFn_hasDerivAt_L1_ae` (L¹-derivative = pointwise derivative a.e. from L¹ convergence of difference quotients ⇒ a.e.
  subsequence); `s ↦ β_s` is `C^∞` on the interior atlas domain, `β' = atlasVelD`, `β'' = atlasVelDD`;
  `ℓ' = ⟨β',M_s⟩ + ⟨β,δ⟩ − ⟨β',S⟩ = −c_s − r_s` with the bending score `r_s = ⟨β'_s, S − M_s⟩` (a tangent score);
  `ℓ'' = ⟨β'',M_s⟩ + 2⟨β',δ⟩ − ⟨β'',S⟩`; pointwise `q''' = q(ℓ³ + 3ℓℓ' + ℓ'')`; `p'''(s) = [q_s(ℓ³+3ℓℓ'+ℓ'')]` in L¹ on (0,1);
  invisible tower ⇒ `q H₃ = q N H₃`; `N` kills the affine part ⇒ **`p'''(s) = [q_s N_{M_s}(ℓ_s³ − 3ℓ_s r_s)]`**
  (`iteratedDeriv_three_reconstructionL1_atlas_cubic`); `d³/ds³ E_{Q_{M_s}}F = E_{Q_s}[N_s F · (ℓ³ − 3ℓr)]`.
- **QuantitativeJets + CubicRemainder** (round-66 rank 1 pre-theorem): with `λ|v|² ≤ Var_{Q_s}⟨v,S⟩` on `𝕍`, `|S − M_s| ≤ L`,
  `|M − m₀| ≤ D` (Euclidean): `c_s ≤ D²/λ`, `|ℓ_s| ≤ DL/λ`, `E r_s² ≤ L²c_s²/λ`, `‖p'‖₁ ≤ D/√λ`, `‖p''‖₁ ≤ LD²/λ^{3/2}`,
  `‖p'''‖₁ ≤ 4L²D³/λ^{5/2}` (exactly your numbers), and the cubic remainder `‖p(s) − p(0) − sp'(0) − ½s²p''(0)‖₁ ≤
  (4L²D³/λ^{5/2}) s³/6` with the Lagrange `1/3!` (pairing with `|F| ≤ 1`, real Lagrange remainder on `t ↦ E_{Q_{M_t}}F`,
  norm duality via the sign observable).

## Mathlib inventory relevant to analyticity (this pin, Lean v4.33.0; checked by grep)
- `ContDiffAt.to_localInverse (hf : ContDiffAt 𝕂 n f a) (hf' : HasFDerivAt f (f' : E ≃L[𝕂] F) a) (hn : n ≠ 0) :
  ContDiffAt 𝕂 n (hf.localInverse hf' hn) (f a)` — **any grade `n`, including `ω`** (𝕂 = ℝ or ℂ). So the analytic
  inverse-function theorem is available as the `ω` case of the `C^n` one (`ContDiffAt.analyticAt : ContDiffAt 𝕜 ω f x →
  AnalyticAt 𝕜 f x`, `contDiff_omega_iff_analyticOnNhd`, `contDiffOn_omega_iff_analyticOn (hs : UniqueDiffOn)`).
- `contDiffAt_map_inverse (e : E ≃L[𝕜] F) : ContDiffAt 𝕜 n inverse (e : E →L F)` for any `n` (so `θ ↦ (Dm(θ)|_𝕍)⁻¹` is
  analytic once `θ ↦ Dm(θ)|_𝕍` is); `AnalyticAt.fderiv`, `AnalyticAt.comp`, `AnalyticAt.div`, `Finset.analyticAt_sum`,
  `ContinuousLinearMap.analyticAt`, `NormedSpace.exp_analytic`, `analyticOnNhd_rexp`.
- **Absent**: any "integral of an analytic family is analytic" lemma; any multivariable analytic IFT other than through
  `to_localInverse`; a `NormedRing` instance on `Lp E ∞ μ` (only `AEEqFun` has `coeFn_mul/pow`); the 1-D
  `analyticAt_localInverse` is `𝕜 → 𝕜` only.
- Power series API: `HasFPowerSeriesOnBall` (fields `r_le : r ≤ p.radius`, `r_pos`, `hasSum`), `FormalMultilinearSeries`,
  `MultilinearMap.mkContinuous` (build a continuous multilinear map from a bound `‖f m‖ ≤ C ∏‖m i‖`),
  `ContinuousMultilinearMap.mkPiAlgebraFin`, `compContinuousLinearMap`, `hasSum_integral_of_dominated_convergence`,
  `tendsto_integral_of_dominated_convergence`, `FormalMultilinearSeries.radius` lemmas (`le_radius_of_bound`, …).
- Seabed: `famNum g θ = ∫ g e^{−⟨θ,S⟩} dν` is `C^∞` (by induction, `SmoothFamily`); `weightL1 θ = [g e^{−⟨θ,S⟩}] ∈ L¹` is
  `C^∞` (`InvisibleTower`); `chartV`, `chartDeriv`, `(CDE θ)⁻¹`, `chartVInv` (on the open `range chartV`), `θ(m₀+z)`, `atlasTheta`,
  `densL1 θ = [q_θ]`, `M ↦ [q_M]` on Ω, the normal form — all `C^∞` (`SmoothFamily/SmoothChart/InvisibleTower/ResponseHessian/
  SmoothNormalForm`); the `chartVInv` smoothness was a bootstrap `C^n ⇒ C^{n+1}` via `contDiffOn_succ_iff_fderiv_of_isOpen`
  and `fderiv chartVInv = (CDE)⁻¹ ∘ chartVInv`.

## The user's direction (unchanged)
"map the space of responses across the data manifold, ideally all the way from the featureless distribution to the data
distribution; maximum beauty and depth."

## Questions
1. **The analytic tilt map.** The only genuinely new analytic input is: for bounded `S` and `g ∈ L¹(ν)` (or bounded `g`),
   `θ ↦ [g e^{−⟨θ,S⟩}] ∈ L¹(ν)` (and the scalar `θ ↦ ∫ g e^{−⟨θ,S⟩}dν`) is analytic (entire). Given the inventory above, what is
   the cheapest Lean route? Options we see: (a) build the `FormalMultilinearSeries` by hand, `p n := (n!)⁻¹ ·
   mkContinuous (m ↦ [g ∏_i (−⟨m i, S⟩)])` with the bound `‖p n‖ ≤ ‖g‖₁ (card J · B)^n/n!` (so `radius = ⊤`) and the `hasSum`
   field by dominated convergence of the exponential partial sums; (b) an infinite-dimensional Banach-algebra argument
   (`NormedSpace.exp` on bounded functions) — but `Lp ∞` has no ring instance here, so we would need our own Banach algebra of
   bounded measurable functions; (c) something via `ContDiffAt ω` characterisations that avoids constructing series (e.g. a
   Cauchy-estimate criterion `‖iteratedFDeriv n f‖ ≤ C A^n n!` ⇒ analytic — does Mathlib have it? we could not find one);
   (d) a complexification / 1-D-per-line argument. Which do you recommend, with the concrete Lean skeleton (definitions,
   the multilinearity/continuity/hasSum obligations, and the lemmas to discharge them)? Is it better to do the L¹-valued map
   once and derive the scalar one by `L1.integralCLM ∘ _`?
2. **The analytic bootstrap at grade ω.** With the tilt map analytic, `famZ`, `famMean`, `chartV`, `chartDeriv`, `(CDE θ)⁻¹` become
   `ContDiff ℝ ω` by composition; for `chartVInv` (the inverse of the mean map on the open `range chartV`) we can apply
   `ContDiffAt.to_localInverse` at grade ω at each point and identify the local inverse with `chartVInv` on a neighbourhood (both
   are inverses of the injective `chartV` on an open set). Is that identification routine (`HasStrictFDerivAt.eventually_right_inverse`,
   `localInverse_apply_image`, injectivity of `chartV`), or is there a cleaner way to get `ContDiffOn ℝ ω chartVInv (range chartV)`
   from the seabed's `C^∞` bootstrap (e.g. a lemma "inverse of an analytic map with invertible derivative is analytic on the image")?
   Then `M ↦ [q_M]` is `AnalyticOnNhd` on the interior displacements, `s ↦ p(s)` is real-analytic on the interior atlas domain, and
   every observable response `s ↦ E_{Q_{M_s}}F` is real-analytic — the qualitative analytic response atlas. Correct? Any traps
   (e.g. `ContDiffOn ω` on non-open sets, `UniqueDiffOn` side conditions, `analyticOn` vs `analyticOnNhd`)?
3. **Quantitative radius.** After the qualitative theorem, is the explicit radius `r = cλ²/L³` (your round-66 contraction) still worth
   formalising, or is a cheaper explicit statement available from the series construction (e.g. the tilt map's power series has
   radius ⊤ with explicit coefficient bounds, and the inverse chart's radius can be bounded through `to_localInverse`'s
   quantitative content — does Mathlib expose any radius from the IFT? we think not)? What is the most valuable explicit
   analytic statement reachable in one module?
4. **Re-ranking.** Given all of the above is landed or routed, rank the remaining candidates for the direction — (i) the analytic
   atlas (qualitative), (ii) the explicit radius, (iii) finite-`X` face completion (retraction of the simplex onto the completed
   family), (iv) the reconstruction CLT (finite-dim CLT + delta method into L¹), (v) anything deeper we are missing (the all-orders
   Bell tower `H_{k+1} = N(H_k' + ℓH_k)` in closed form? the moving normal projection identity? an intrinsic/coordinate-free
   statement of the third jet?) — with precise statements and seabed routes for the top two. Answer in ≤ 3000 words.
