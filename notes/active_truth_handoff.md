# Handoff: the transverse active-truth face theorem (analytic half)

**STATUS 2026-09-25: the constant-unit theorem is landed for `I = ∅` (`ActiveTruthTheorem.lean`, `tendsto_modelKernel_activeTruth'`) AND with spectators (`ActiveTruthSpectator.lean`, `tendsto_modelKernel_activeTruth_spectator`, extra factor `∏ ρ^{dᵢ}/dᵢ`; route: `ActiveTruthUniform` = lintegral form + uniform bound, `SpectatorEnvelope` = one-variable integrability, outer DCT in `ξ`). The exact trace model `W = w(u)`, `a = a(u)` is landed too (`ActiveTruthTraceTheorem.lean`, `tendsto_modelKernel_trace`, constant `A Γ(β) B^{-β} q D^{-qη} vol(F')/|det M| ∫_0^ρ u^{qη−1} w a^{-β}`). The weighted fibre lemma (`ActiveTruthFibreWeighted.lean`) and the general trace replacement (`ActiveTruthGeneral.lean`, `tendsto_modelKernel_general`, units `W(x,u), a(x,u)` with traces) are landed too. The chart wrapper is landed (`ActiveTruthChart.lean`, `TermData.activeTruth`; the leading measure lives on the truth segment `u ↦ rep(bridgePt 0 u)`). Spectators with general units are landed (`ActiveTruthSpectatorGeneral.lean`, `tendsto_modelKernel_general_spectator`: extra factor `∫_{(0,ρ)^m} ∏ ξ^{d−1} (…)` with the traces depending on `ξ`, a.e. in `ξ`; the general integrand is dominated pointwise by `W_*` times the constant-unit integrand at `a_-`, so the constant-unit spectator majorant is reused). `vol(F') > 0 ⇔ positive face point` is `volume_poly2_pos_iff` (`ActiveTruthFacePositive.lean`). The chart wrapper with spectator coordinates is landed too (`ActiveTruthChartSpectator.lean`, `TermData.activeTruthSpectator`; leading measure on `specBox × truth segment` pushed forward along `(ξ,u) ↦ rep(bridgePt (specPt e ξ) u)`). The LP→chart interface is landed (`ActiveTruthLPChart.lean`: the chart LP's optimal set is the active face under the certificate, the active-truth power is the LP value of the face, and the coefficient measures are nonzero for a positive face polytope with `wt|b| > 0` at a truth point). The example identification is landed (`ActiveTruthExampleBridge.lean`, `tendsto_degI_of_face`). Astra round 11 (e47fce9) ranks next: the general-truth hironaka export, moving parameters by squeezing between corner kernels, one mixed vertex/tied/active example; the `c_j = a_j = 0` case is deferred as a scoped exclusion (different boundary regime). Solved-pair independence is landed (`ActiveTruthFaceInvariance.lean`, `faceConst_eq`); the moving-constants version (constant units, squeeze) is landed (`ActiveTruthParam.lean`, `tendsto_modelKernel_activeTruth(_spectator)_param`). The general-unit moving version is landed too (`ActiveTruthGeneralParam.lean`, `tendsto_modelKernel_general_param`, via the time change `τ = t (D₀/D)^{q/γ}` that absorbs the moving cut constant). The chart-level moving-σ wrapper is landed (`ActiveTruthChartParam.lean`, `tendsto_termKernel_activeTruth_param`). Compact-σ uniformity is landed (`ActiveTruthChartUniform.lean`). Astra round 12 (f96245f): closure verdict positive for the nondegenerate regime with a six-point hypothesis-discharge checklist; the `xy = s` bookkeeping was already closed (`MixedTruthRecord`); the `c_j = a_j = 0` constant-unit boundary theorem is landed (`ActiveTruthDegenerate.lean`: half-plane-restricted transverse integral × one-constraint face polytope). The `h < 0` weighted mixed truth is landed (`MixedTruthWeightedNeg.lean`; trichotomy complete). The general-truth hironaka export is landed (hironaka `wall-atlas` 70ac670cb: `Truth*.lean`, `exists_truthChartsData(_phase)` — `TruthChartsData m T (L ∩ {|T| ≤ ε})` from the resolution of `F·T`, with the monomial form of `F` on the boxes). Support-separated distinguishability is landed (`ActiveTruthDistinguish.lean`, `exists_observable_of_activeTruth_separated`: a leading active-truth term with a positive-weight truth-segment point in an open `O ⊆ L'` null for the other phase's leading measure gives an observable with non-vanishing fibre-ratio difference). The general-unit boundary version is landed (`ActiveTruthDegenerateGeneral.lean`, `tendsto_modelKernel_general_degenerate`: partial traces `Wtr(z,u)`, `atr(z,u)` at the surviving coordinate `z = ρ e^{-(M⁻¹v)_1}`, limit `A ρ^Σ/|det M| (∫⁻ vWeightTD).toReal vol(F')` with the unit inside the transverse exponential). The exact push-forward theorem for an analytic truth is landed in hironaka (`TruthPushforward.lean`, `exists_truth_pushforward`: the exported `TruthChartsData` and its `totalKernel` as the explicit representative). The chart wrapper of the boundary regime is landed (`ActiveTruthChartDegenerate.lean`, `activeTruthDegMeasure` on the surface `(z,u) ↦ rep(bridgePt (survPt z) u)`, `tendsto_modelKernelOf_activeTruth_degenerate`, `TermData.activeTruthDegenerate`; the `j = 0` labelling is absorbed by `e`). Round 13 is closed: positivity of the degenerate measure (`ActiveTruthDegeneratePositive.lean`), the density-factorisation certificate of the export (hironaka `exists_truthChartsData_certified`), the certificate-level dominant term (`ActiveTruthLeadingTerm.lean`, `ofTermData_leadingMeasure_eq_of_lt`). Astra round 14 (db67154) confirmed closure and ranked the consumer interface first: DONE — the term layer is now stated for `TruthChartsData m T L'` (`WallChartsData` is an abbrev for the coordinate truth; laplace 9c4c1ff), and hironaka has `WallAtlasT.toPhase` + `exists_truthChartsData_withPhase` (a phase record for the resolution of `F·T`). Round-14 items 2–3 are landed: `MixedTruthExport.lean` (`totalKernel_ae_eq_of_support`, `totalKernel_mul_comp_truth`, `eq_of_ae_eq_of_continuousAt`, `mixDataC`, `exported_mix_tendsto_totalKernel`) and hironaka `exists_mixed_export_regression` (the resolution-produced charts for `z₀z₁ a` carry the logarithmic coefficient `e^{-σ a(0)} ψ(0)`). Round-14 item 4 is landed in the strict single-scale model (`ProfileIntegrability.lean`, `integrable_singleScaleProfile_iff`: integrable ⇔ `r_j > −1` and every effective exponent `r_i − κ_i(r_j+1)/κ_j > −1`, i.e. the strict-optimum condition of the phase-constrained LP; necessity by the recession directions `−e_j` and `κ_i e_j − κ_j e_i`, sufficiency by Fubini + Gamma). Remaining: (5) the exact log-face constant (Astra's formula `vol_d(F) ∫_N …`), the general polyhedral criterion (all coordinates, non-strict constraint) if the note needs it; then a round-15 consult. Astra round 15 (bfeaf99): exact constants closed; polyhedral criterion deferred; ranking (1) note-to-Lean statement audit + an end-to-end analytic-input theorem, (2) certificate-coverage audit, (3) the boundary regression `T = xy`, `F = ax`, `θ = x^p y^q` (incomplete-Gamma constant `σ^q ∫_σ^∞ u^{p−q−1} e^{-au} du`), (4) constructive-recovery export or the smooth counterexample, (5) scale cleanup. The audit is DONE: the identifiability section is fully formalised; the untagged `q:proportional` proof lives in `NormalizedSingular` (tag suggestion `normalized_expectations_force_eq_near`) and is now also proved under the pencil theorem's weaker hypotheses (`ProportionalFamilies.lean`, dc95fcb/0910141, `proportional_families_force_eq_near`; not mirrored — pencil chain). The general-truth end-to-end theorem is landed (hironaka `TruthTheoremPhase.lean` d7e5a9124: `truth_fibre_expectation(_dominant/_measure/_point/_certificate)`, `truth_fibre_expectation_pushforward` — push-forward identity + certified expectation limit for the SAME resolution-produced `D`; certificates remain inputs). The boundary regression is landed (`MixedTruthBoundary.lean` 1507293 / hironaka c58c724af: `mix_tendsto_totalKernel_boundary`, `exported_mix_tendsto_totalKernel_boundary`: `t^p K_t(σ/t) → σ^q ∫_{2σ}^∞ u^{p−q−1} e^{-au} ψ(σ/u,0) du`). The coverage audit is DONE (`CertificateFromLP.lean` 7b22892 / hironaka 11ad4063d: `ProfileIntegrableOf.of_uniqueLPMin_vertex/_twoScaled`, `TermData.vertexOfUniqueLPMin/twoScaledOfUniqueLPMin` — certificates from LP uniqueness at both nondegenerate shapes; no decision procedure for the shape yet). Astra round 16 (b4a9590) found a statement error in the boundary regression (support hypothesis killed the trace) — REPAIRED (0394638: no support hypothesis, unit `a(z)`, acceptance value `σ^q e^{-2aσ}/a`; exported version withdrawn). The boundary `TermData` is landed (`ZeroScaleCertificate.lean` 964befc / hironaka e511103e5: `ProfileIntegrableOf.of_zeroScale`, `TermData.zeroScale` — scale `α = 0`, `phaseExp = 0`, effective `κ_j < 0` or (`κ_j = 0 ∧ r_j > −1`); the model theorem needed no change). The certificate acceptance test is ANALYSED but deferred (spec: the linear phase is not admissible as a `Phase` (sign), `F ≥ 0` is global in the term theorems, observables supported in `L'` cannot see the wall segment, so the test must use the exported record over the full thin region with `F = a z₁²`, `p = 0`, and a tied-cut single-scaled certificate; ~400 lines). Item 5 is landed (`FlatInvisibleSingular.lean` d0450d6: `singular_flat_witness_superpolynomial`). Item 2 (1D recovery) and item 4 (scale API `powLog`) were already covered. Astra round 17 (d2c6626): ranking (1) version-selection + cutoff pointwise chart-independence [DONE: `KernelPointwise.lean` 4a69762], then support-free observables, then local `F ≥ 0`; (2) tied-cut single-scaled certificate [DONE: `TiedCutCertificate.lean` 39456ee / hironaka 40b9b23e6, `ProfileIntegrableOf.of_tiedCut₁`, `TermData.tiedCut₁`]; (3) the quadratic exported two-branch acceptance test; (4) LP optimal vertex; (5) recession-cone criterion at α = 0. The support-free observable interface is landed (face in `interior L'` OR observable vanishing near the face — the disjunction is needed because the chart radius exceeds the region radius; `InteriorObservable.lean` 55079dc / hironaka 06504af86: `tendsto_fibre_expectation_of_interior` with the limiting faces in `interior L'` instead of a support condition). REMAINING (round-17 order): (3) the quadratic exported two-branch acceptance test (now feasible: `F = a z₁²`, observable `z₀^q ψ`, `TermData.tiedCut₁`, interior faces, `tendsto_nhds_unique`); local `F ≥ 0`; (4) LP optimal vertex; (5) recession-cone criterion at α = 0 (+ the corrected 2D mixed-sign example); then a round-18 consult; (2) 1D constructive-recovery export (`t^{r/2k}[t^{(j+1)/2k}∫χ x^j e^{-tL} − A_j] → −b A_{j+2k+r}`); (3) LP optimal-vertex existence + classification ⇒ `exists_termMeasureCertificate`; (4) minimal scale API; (5) smooth singular counterexample if `prop:flat` does not export it. NEW DIRECTION (user, 2026-09-25): the RESPONSE MAP over the data manifold `q ↦ Φ_q` (how expectation values change with the data distribution, from a featureless reference to the data). Astra round 18 (4ede3cf, `research_round18_v1.md`): three layers (exact / asymptotic / singular-stratified); corrections: `−log Z` is CONCAVE on mixture lines, `log Z` convex; "featureless" must mean LOSS-NEUTRAL (`L_{q₀}` constant), not maximal entropy; e-geodesic data paths give curved posterior paths (extra `−t Cov(φ, L̈_s)`); coupled `q(t), t` exponents piecewise affine with crossover scale example-dependent (`s t^{1/2}` for `w⁴ + s w²`). Ranked: (1) tilt representation + neutral corollary [DONE `ResponseMap.lean` 70e5ba5], (2) first/second response derivatives + monotone `⟨Δ⟩_s` [DONE], (3) log Z convexity + Hessian + KL–Bregman [DONE], (4) influence operator / response form PSD + response bound [DONE; nullspace = a.e.-constant directions NOT done], (5) uniform interior rigidity for finite mixtures [DONE `MixtureRigidity.lean`]. Landed after round 18: `PathResponse.lean` (80098f5: `PathData` master identity `d/ds⟨φ⟩_{L_s} = −t Cov(φ, L̇_s)`, e-geodesic `L̇_s = Cov_{q_s}(ℓ,a)`), `ResponseMetric.lean` (11a22af: `g_a(v,u)/t → ⟨∇R_v, P⁻¹∇R_u⟩`), `CoupledPhaseDiagram.lean` (2e5f928: `t^{max(1/4,(1−σ)/2)} Z(t,t^{-σ}) → C(σ)` for `w⁴ + s w²`), `ResponseNullspace.lean` (96699c0: `g_a(v,v) = 0 ⇔ R_v` a.e. constant on supp π). Astra round 19 (22505e1, `research_round19_v1.md`): corrections — the LP value `λ(σ)` is CONVEX (not concave) in σ; fixed-σ asymptotics are NOT uniform near LP walls (`∫∫ e^{-tx(y + t^{-σ})}`: `σ(t) = (log t)^{-1/2}` gives `t^{-1}√log t`, not `t^{-1} log t`; wall variable `τ = (σ − σ*) log t`). Ranking: (1) `CoefficientResponse` — leading coefficient measure `μ_a(φ) = ∫_F φ U_a^{-λ} dν` (principalised mixture, affine unit `U_a = ∑ aᵢhᵢ`) locally analytic in `a`, derivative `−λ∫ φ U_a^{-λ-1} R_v dν` [IN PROGRESS: `CoefficientResponse.lean`], (2) `ValuationFan` — LP dual `λ(σ) = max{(1−σ)·y : y ≥ 0, Aᵀy ≤ b}`, convex piecewise affine, log multiplicity = dim of optimal face, chartwise Θ-asymptotics `t^{-λ(σ)} (log t)^{d_σ}`, (3) `WallResponseProfiles` — uniform crossover in `s√t` on compacts, (4) `VariationalResponseGeometry` — Gibbs gap identity `tE_ρL + KL(ρ‖π) = F + KL(ρ‖ρ_t)` [IN PROGRESS: `GibbsVariational.lean`], path Hessian `F'' = tE[L̈] − t²Var(L̇)`, Fisher length `L_t/√t → ∫√(ẇᵀHẇ)`, (5) `AnalyticResponse` — joint CGF `H(s,J) = log∫e^{-t(L₀+sΔ)+Jφ}π`, cumulants as mixed partials. Single best: (1), formulated for measures/test observables (the singular analogue of `q ↦ Φ_q`). PROGRESS: (1) first step DONE (`CoefficientResponse.lean` 80c6b4f: `hasDerivAt_faceCoef`, `hasDerivAt_facePosterior` = singular fluctuation–response `−λ Cov_{ν_a}(φ, R_v/U_a)`; NOT yet: representation theorem over `TermData`, local analyticity); (2) first step DONE (`ValuationLP.lean` c178053: `offsetLP` convex + antitone, `offsetLP_quartic = coupledExponent`; NOT yet: piecewise affinity via dual vertices, log multiplicity = dim optimal face, chartwise Θ-asymptotics `t^{-λ(σ)}(log t)^{d_σ}`); (3) exact wall profile `t^{1/4} Z(t, c/√t) = quartProfile c` + Gaussian matching `√c quartProfile c → √π` [`CoupledPhaseDiagram` addition]; (4a) DONE (`GibbsVariational.lean` 6e09786), (4b) DONE (`PathHessian.lean` efbfcad); (4c) exact part DONE (`ThermoLength.lean` 45fcdb7: Fisher speed bounds displacement; the `√t` degeneration needs uniform Laplace along the path — NOT done); (1) bridge to the atlas DONE for the trace regime (`TraceMixtureResponse.lean`: `tendsto_modelKernel_trace_mixture`, `hasDerivAt_tracePosterior`); (5) NOT started. NEXT candidates: the general-`TermData` representation (unit inside `dsProfile`), spectator/degenerate regimes of the mixture bridge, local analyticity of `a ↦ μ_a` (binomial series), piecewise affinity of `offsetLP`, joint CGF. The wall example is DONE (`WallLogMultiplicity.lean` 19aaa3c: exact identity + three regimes). Astra round 20 (a433a1e, `research_round20_v1.md`): AUDIT OK (singular fluctuation–response sign/ratio/normalisation correct; affine unit exact under a fixed common-factor representation; `τ = σ log t` NOT universal — both walls have `1/log t` width in VALUATION space, the log example has a SECOND crossover at `ts ≍ 1`: `tZ(t,c/t) − log t → −log c − E₁(c)`; thermo-length theorem is the uniform-speed Lipschitz corollary, integrated version still to do; Gibbs: equality-iff not done). Ranking: (1) `TermScoreResponse` — for an exponential-form term `dμ_a = H e^{-B U_a(u∞) P} dm`, `D_v ∫φ dμ_a = −∫ φ S_v dμ_a` with score `S_v = B R_v P`, then normalised `−Cov_{μ̄_a}(φ, S_v)`; differentiate FIRST, marginalise SECOND; (2) `GammaFaceMarginal` — `∫_0^∞ z^{β−1} e^{−BUz} = Γ(β)(BU)^{−β}` and `E[S_v | u] = β R_v/U_a` (bridge to `faceCoef`); (3) `HigherResponse` — all-order unnormalised derivatives of bounded tilts, recursive normalised API, cumulant identification (power series later); (4) `WallProfileUniform` — fixed-wall rescaling theorem `σ(t,τ) = σ* + τ v/log t`, `t^{b·r*} Z → Φ(τ)` locally uniformly, LP certifies `b·r* = offsetLP`; (5) `ResponseAnalytic`. SINGLE MOST VALUABLE: normalised response theorem for the ASSEMBLED leading measure `μ_a = ∑_k μ_{k,a}` (relative masses of chart terms change too). PROGRESS after round 20: (1) DONE `TermScoreResponse.lean` 5f10474 (`ScoreData.hasDerivAt_termCoef/termPosterior`), (2) DONE `GammaFaceMarginal.lean` 6c4214d (`gamma_score`, `termCoef_prod_eq_faceCoef`, `termScoreCoef_prod_eq`), deepest target DONE in scalar form `AssembledResponse.lean` (`hasDerivAt_assembledPosterior`; terms on a common base space, common unit family). (3) unnormalised layer DONE (`HigherResponse.lean`: `iteratedDeriv_tiltNum/mixNum/priorZ_pathLoss`; normalised cumulant identification NOT done), second wall DONE (`WallSecondCrossover.lean`: `tendsto_wallZ_second`). OPEN: (4) WallProfileUniform (fixed-wall rescaling theorem `σ* + τv/log t`), (5) ResponseAnalytic; side DONE: integrated thermodynamic-length inequality (`ThermoLengthIntegral.lean`), the second wall (`WallSecondCrossover.lean`), Gibbs equality-iff (`GibbsUniqueness.lean`); still open: instantiation of `ScoreData` on an actual `termDensity` (needs a `Phase` family affine in the weight), the `√t` degeneration of the thermodynamic length. Astra round 21 (9d12840, `research_round21_v1.md`): AUDIT OK (envelope natural; everywhere-positivity of `U_a` stronger than needed — add an a.e.-on-active-support wrapper; Gamma model correct WHEN the term has the radial form — classify the `Q`-cut and truth constraint after scaling; assembled formula recovers the disjoint-union covariance incl. relative-mass term `Cov_p(m_k, q_k)`; MixtureSeries fine — normalised posterior is real-analytic, not entire). KEY: physical score `t D_v L_a(Ψ_t x) → B P(x) R_v(u∞)` (the vanishing monomial factor is essential — name physical vs unit score directions differently). RANKING: (1) score-weighted asymptotic bridge — the FOUR-INTEGRAL theorem: if `A_t∫1`, `A_t∫φ_t`, `A_t∫Q_t`, `A_t∫φ_tQ_t` (with `Q_t = t D_v L_a`) converge to the `μ_a`-integrals then `t Cov_t(φ_t, D_vL_a) → Cov_{μ̄_a}(φ, S_v)` (quotient-limit algebra); first instance: the regular model `L_a = a w^p` (exact under `y = t^{1/p} w`), then two labelled copies (relative-mass test); the `w⁴ + s w²` wall response needs the renormalised derivative `∂_c = t^{-1/2}∂_s`, `∂_c E[ψ(y)] = −Cov(ψ, y²)`; (2) affine phase families + `Phase.mixture` (same phase monomial factor `f_i∘χ = M h_i`; aggregate unit bounds `c ≤ U_a ≤ C`, not per-weight; `B` frozen); (3) uniform 1D wall profiles and response (`F(c) = ∫₀^∞ e^{-y^p − c y^q}`, `F^{(n)}(c) = (−1)^n ∫ y^{nq} e^{…}`, cut domain `(0,1)` gives NO second crossover — the log example's second crossover is a cube-chart logarithmic-channel effect); (4) normalised cumulant response; (5) thermodynamic-length asymptotics (two regimes: `g_t = O(1)` vs `g_t ~ t g_∞`). SINGLE MOST VALUABLE: locally uniform convergence of assembled score-weighted asymptotics ⇒ locally uniform convergence of posterior directional derivatives to the disjoint-union covariance. PROGRESS after round 21: (1) interface DONE (`ScoreBridge.lean`: `tendsto_scaled_cov_of_four`, `tendsto_response_of_four`, regular model `regular_scaled_cov_eq` exact); (3) 1D two-monomial wall DONE (`TwoMonomialWall.lean`: exact profile, both regimes; uniform profile DERIVATIVES `F^{(n)}(c)` not done); (5) partially (integrated inequality). OPEN: two labelled copies (relative-mass bridge test), rescaled-score domination lemma on the atlas term theorems, affine phase families + `Phase.mixture`, normalised cumulant response, wall response `∂_c E[ψ(y)] = −Cov(ψ, y²)` for the quartic wall, thermo-length asymptotics. Then a round-22 consult.**

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

**2026-09-25 (later):** `ProfileResponse.lean` landed (b5b5186): the profile law `∝ e^{-(y^p+cy^q)}`, `∂_c⟨ψ⟩_c = −Cov_c(ψ,y^q)` with the unbounded score dominated by the profile decay, `wall_posterior_eq_profile` (finite-`t` posterior of the scaled observable at `s = c t^{-σ*}` equals the profile law for every `t`), `hasDerivAt_wall_posterior`. GOTCHA: a module named `WallResponse.lean` already existed (2026-09-22 low-resolution wall arc, imported by `WallCutoff`); creating a same-named file OVERWROTE it and broke the umbrella build — restored from git and renamed mine. Always `ls Laplace/Multi/<Name>.lean` before creating a module. Next: the profile family as an exponential family in the wall variable (all-order derivatives, log-convexity, monotone mean map), then the round-21 list.

**2026-09-25 (round 22):** landed `ProfileFamily` (wall profile = exponential family, mean map strictly decreasing), `ThermoLengthAsymptotic` (ℓ(t)/log t → √λ on the neutral line), `IntegratedSusceptibility` (∫₀¹ tVar = ⟨Δ⟩₀−⟨Δ⟩₁, ℓ ≤ √(2Mt), strict identifiability), `AffineConvexity` (log Z convex on ℝ^k, Hessian = responseForm). Astra round 22 (`gpt_responses/research_round22_v1.md`): the organising theorem is 'Φ_t pulls Fisher–Rao back to Hess_q log Z_t'; corrections: λ = (lim ℓ/log t)², wall is transverse to a coefficient stratum not the neutral ray, flat prior ⇒ infinite featureless length. REMAINING from the round-22 bundle: (4) sqrt-integral convergence from an L¹ mass bound (truncation argument, no Vitali) ⇒ ℓ/√t → ∫√κ; (5) wall-window length = profile length (exact, via `wall_posterior_eq_profile` and `integral_comp_mul_right`); then shape metric at a fixed minimiser, D on compact chart subsets, the proper-prior instance of the √λ log t law.

**2026-09-25 (round 22 bundle COMPLETE):** IntegratedSusceptibility, AffineConvexity, WallWindowLength, SqrtIntegralConvergence, GaussianShapeMetric all landed and pushed (last 3112f84). Slop paragraphs for each. Next candidates: (i) regular geometric limit `responseForm/t → H(Dm[u],Dm[v])` by combining `responseForm_asymptotic` with the moving-minimiser derivative (MovingMinimizer.lean); (ii) multivariate Legendre duality (mean map Jacobian = −t·responseForm, injectivity modulo nullspace); (iii) proper-prior instance of the √λ log t law (Gaussian prior + anharmonic; needs continuity of u ↦ Var_u down to u = 0 and `localisedVar_energy_leading`); (iv) D on compact chart subsets; (v) `priorZ_pathLoss_eq_of_moments_eq` (HasSum.unique) — cheap.

**2026-09-25 (round 23):** Astra round 23 (`gpt_responses/research_round23_v1.md`) confirmed the receding-wall conjecture; landed `ProfileTailLength` (scaled Cesàro), `ProfileGammaTail` (c²Var_c(y^q) → 1/q), `WallRecedes` (ℓ_t/log t → σ*√(1/q)), plus `RegularGeometricLimit`, `ShapeMetricLimit`, `GaussianShapeMetric`, `MeanMapInjective`, `MomentDetermination`, `BoundedDistance`. Astra's remaining ranking: E entropy duality on the mean-map image (`J_t(m(a)) = E_a L₀ + D(P_a‖μ)/t`; KL = Bregman of log Z multivariate), D mean-map diffeomorphism, C uniform Laplace on compact families, B proper-prior √λ log t instance; strong-form receding wall (integrable tail `Var_c = 1/(qc²) + O(c^{-2-p/q})`) and the spectator example `x²+y⁴+ay²` (coefficient 1/(2√2)). NB: the Cesàro lemmas now take `∀ a b, 0 ≤ a → 0 ≤ b → IntervalIntegrable`.

**2026-09-25 (late):** also landed `EntropyDuality` (Legendre dual at realised means = ⟨L₀⟩ + KL/t; tangent inequality; KL = Bregman of log Z) and `SpectatorWall` (x²+y⁴+ay²: coefficient 1/(2√2)). Remaining Astra items: B proper-prior instance of ℓ/log t → √(d/2) (Gaussian localiser prior + rotated anharmonic via `localisedVar_energy_leading`; needs `priorCov volume π L L L u = gibbsCov (localisedRotatedAnharmonic … u) u L L` and continuity of u ↦ Var_u down to u = 0 by dominated convergence with the Gaussian prior), D mean-map diffeomorphism (Fréchet derivative via `hasFDerivAt_integral_of_dominated_loc_of_deriv_le`, then IFT), C uniform Laplace on compact families, strong-form receding wall (integrable tail `I_k(c) = Γ + O(c^{-p/q})` from `1 − e^{-εx^r} ≤ εx^r`).

**2026-09-25 (round 24):** Astra round 24 (`gpt_responses/research_round24_v1.md`) landing order: finite-initial-length lemma + B from base u₀; exact bound t²Var ≤ 1/(qa²) + integrable defect; renormalised receding wall; two-sided window (already covered); singular response chart (LANDED as `WallChart`: two couplings, exact profile Fisher matrix pull-back); D; negative chamber (√t); C last. Also landed `WallRecedes` exponent form. In progress: `ThermoLengthFromBase` (Cesàro from u₀ > 0, dominated continuity of u ↦ Var_u(L) on [u₀,∞) for L ≥ 0 with ∫L²e^{-u₀L}π < ∞), then the Gaussian-prior anharmonic instance.

**2026-09-25 (round 24, continued):** landed `ThermoLengthFromBase` (Cesàro from any base point; dominated continuity of u ↦ Var_u(L) on [u₀,∞)), `AnharmonicFeaturelessLaw` (Gaussian-prior separable anharmonic: (∫_{s₀}^t √Var_u)/log t → √(d/2)), `WallChart` (two-coupling singular response chart, exact), `WallRecedes` exponent form. Remaining from Astra's round-24 order: strong-form receding wall (quantitative tail |I_k − Γ| ≤ c^{-p/q}Γ(s+r+1), integrable defect, renormalised limit — IN PROGRESS as `WallRecedesStrong`); D (mean-map diffeomorphism via `hasFDerivAt_integral_of_dominated_loc_of_deriv_le`); negative chamber (√t, K₋(A)); multiplicity correction; C last.

**2026-09-25 (round 24, strong form):** `WallRecedesStrong` landed (1f9382e): quantitative Gamma tail, `|c²Var_c(y^q) − 1/q| ≤ C_V c^{-p/q}`, integrable speed defect, `∃K, ℓ_t − σ*√(1/q) log t → K`. Round-24 items 1, B, 2, 3, 5 all done. Remaining: D (mean-map diffeomorphism: `hasFDerivAt_integral_of_dominated_loc_of_deriv_le` for the numerators with `dirCLM R x = ∑ R j x • proj j`, quotient rule, `hasFDerivAt_pi`, strictness via `hasStrictFDerivAt_of_hasFDerivAt_of_continuousAt`, inverse function theorem), negative chamber (√t), multiplicity correction, C. Consider a round-25 consult after D.

**2026-09-25 (item D, stages 1–2):** `MeanMapFDeriv` (Fréchet differentiation of the affine numerators under the integral, `dirCLM`) and `MeanMapJacobian` (`hasFDerivAt_meanMap`, `meanMapDeriv_apply : Dm(a)[v]ᵢ = −t Cov_a(Rᵢ,R_v)`, `meanMapDeriv_injective`) landed (b760065). Remaining for D: continuity of `a ↦ meanMapDeriv a` (dominated continuity of CLM-valued integrals) ⇒ `hasStrictFDerivAt_of_hasFDerivAt_of_continuousAt` ⇒ finite-dim injective ⇒ `ContinuousLinearEquiv` ⇒ `HasStrictFDerivAt.toPartialHomeomorph` (planned module `MeanMapChart`). Then negative chamber, multiplicity, C; round-25 consult.

**2026-09-25 (item D closed):** `MeanMapChart` (089e33b): `continuousAt_affNumDeriv` (dominated continuity, same majorant as `hasFDerivAt_affNum`), `hasStrictFDerivAt_meanMap` (per component via `hasStrictFDerivAt_pi''` + `proj_pi` + `hasStrictFDerivAt_of_hasFDerivAt_of_continuousAt`), `meanMapDerivEquiv` (`LinearEquiv.ofInjectiveEndo` → `toContinuousLinearEquiv`), `meanMapInverse := HasStrictFDerivAt.localInverse` with left/right inverse, continuity, `hasStrictFDerivAt_meanMapInverse` (derivative `(meanMapDerivEquiv …).symm`), `map_nhds_meanMap`, `meanMapInverse_deriv_comp`. Round-24 remaining: negative chamber (√t scale, K₋(A)), multiplicity correction (−(m−1)/(2√λ) log log t), uniform Laplace C; then a round-25 Astra consult on the user's direction (map the space of responses from the featureless distribution to the data distribution).

**2026-09-25 (round 25):** Astra round 25 (`gpt_responses/research_round25_v1.md`) on the user's "map across the data manifold" direction. Landed: `MeanMapEmbedding` (d76d9c3/1bbcea1: open embedding, global inverse strictly differentiable), `StateDensity` (d932320: lossLaw, lawExp/lawVar/lawLength/radialLength, featureless line depends only on the state density), `RenormalisedLength` + `LogGammaTails` (20290ad), `MultiplicityModel` (9566791: `logModel_length_renormalised`, the (λ,m)=(1,2) state density (−log ℓ)dℓ on (0,1) has ∫_{u₀}^t √Var_u = log t − ½ log log t + K + o(1)). Remaining round-25 order: (4) negative-profile matching `h(−b) ~ K_{p,q} b^{β−1}`, `β = p/(2(p−q))` (rescale y = b^{1/(p−q)} z, fixed potential z^p − z^q with large parameter, localise at the interior minimiser — the seabed's regular Laplace machinery is for smooth potentials on ℝ^d; a half-line real-exponent instance needs new localisation, ≥400 lines) ⇒ `ℓ_t(−A,0)/√t → K₋(A)`; general integer k (binomial expansion of (T − log s)^k, needs Λ-moments with (log s)^r, r ≤ k); Tauberian `u²Var → λ` from regular variation of Z (ratio Z((1+s)u)/Z(u), uniform integrability); square-root Fisher immersion `Ψ(a) = 2√(dP_a/dP_0)` with ⟨DΨ[v],DΨ[w]⟩ = G_a(v,w) and the two-valued-contrast geodesic characterisation; radial functional laws (`D_t(aL+b) = D_{at}(L)`, product prior inequality `√(D₁²+D₂²) ≤ D(L₁+L₂) ≤ D₁+D₂`); two-sided window corollary (trivial from `wall_window_length`). Do not start uniform Laplace C.

**2026-09-25 (Tauberian):** `TauberianVariance` landed (3887088): `tendsto_ratio_of_regVar` (abstract squeeze), `tendsto_sq_mul_lawVar_of_regVar`, `regVar_of_asymptotic`, `tendsto_sq_mul_priorCov_of_partition_asymptotic`. Remaining round-25 items: negative-profile matching (heavy), general integer k multiplicity (binomial expansion of (T − log s)^k; needs `∫ s^j e^{-s} (log s)^r` tails and an IBP recursion in r), square-root Fisher immersion, radial functional laws (scaling, product prior), two-sided window corollary.

**2026-09-25 (capstones):** `FeaturelessLawFromPartition` and `FisherInformation` landed (5bab595). Remaining round-25: negative-profile matching (heavy, needs half-line real-exponent Laplace localisation), general integer k multiplicity, radial functional laws (scaling `priorExp μ π (aL+b) φ u = priorExp μ π L φ (au)`, product-prior inequality), two-sided window corollary; then a round-26 consult.

**2026-09-25 (radial laws):** `RadialLaws` landed. Remaining round-25: negative-profile matching, general integer k multiplicity, product-prior inequality for D_t; then round-26 consult.

**2026-09-25 (round 26):** Astra round 26 (`gpt_responses/research_round26_v1.md`): crown = length–distance cluster (affinity formula, Jensen-gap integral identity `B(t) = ½∫₀ᵗ min(u,t−u) Var_u`, sqrt-speed identity, angular lower bound `D(t) ≥ 2 arccos ρ(0,t)`, `d_FR → π` under regular variation), exact KL Pythagoras (Bregman + affine information projection), negative chamber via the centred generalised-gamma saddle lemma (`x^{a−1}e^{−x^r+bx}`, rescale `x = x_b z`, `φ(z) = z^r − rz + r − 1`, three centred integrals), general k, product-prior inequality. Landed: `Affinity` (affinity formula, Jensen gap of log Z, Z → 0, ρ²/Z → 2^{2λ}/Z(0), d_FR → π). Next: `RadialCurvature` (derivatives of lawMoment under the integral: F' = −⟨ℓ⟩, F'' = Var; Jensen-gap integral identity; sqrt-speed identity), angular lower bound (Cauchy–Schwarz on the L² sphere: `−ρ' ≤ ½√(1−ρ²)√Var`), `InformationProjection` (KL Pythagoras), then the saddle lemma.

**2026-09-25 (curvature):** `RadialCurvature` landed. Remaining round-26 crown: the angular lower bound `D(s₀,t) ≥ 2 arccos ρ(s₀,t)` (Cauchy–Schwarz on the L² sphere: `−ρ'(u) = (ρ/2)(⟨ℓ⟩_m − ⟨ℓ⟩_u) ≤ ½√(1−ρ²)√Var_u`, then integrate `θ = arccos ∘ ρ`; needs `ρ < 1` off the diagonal), KL Pythagoras (`InformationProjection`), the centred saddle lemma for the negative chamber, general k, product-prior inequality.

**2026-09-25 (KL Pythagoras):** `InformationProjection` landed. Next: the centred generalised-gamma saddle lemma (`SaddleLemma`: density `x^{a−1} e^{−x^r + b x}`, `x_b = (b/r)^{1/(r−1)}`, `σ_b² = 1/(r(r−1)x_b^{r−2})`, `Var_{Q_b}(X) ~ σ_b²` via three centred integrals after `x = x_b z`, `φ(z) = z^r − rz + r − 1`), then `wall profile matching` `h(−b) ~ K b^{β−1}` and the chamber law; the angular bound; general k; product inequality.

**2026-09-25 (angular bound):** `AngularBound` landed (0479d27): round-26 Theorems A and B complete. Remaining: the centred generalised-gamma saddle lemma for the negative chamber (see the round-26 response §3 for the recipe), general integer k multiplicity, product-prior inequality. Then a round-27 consult.

**2026-09-25 (negative chamber, profile matching):** `HalfLineLaplace` (634e5ea/41c8586: abstract centred half-line Laplace lemma `tendsto_sqrt_mul_integral` + Gaussian moments), `TwoMonoPotential` (4b60250: `ψ = z^p − (p/q)z^q`, `φ = ψ − ψ(1)`, quadratic bound, coercivity, L'Hôpital limit `φ(1+h)/h² → p(p−q)/2`, envelope `|z^q−1| ≤ max q 1 |z−1|(1+z)^n`), `NegativeChamber` (f61c81f): rescaling identity `N_g(−b) = y_b e^{-Bψ(1)} ∫ g(y_b z)e^{-Bφ}`, `B = y_b^p`, and **`tendsto_negVar_mul_rpow'`: `Var_{-b}(y^q)·(qb/p)^{(p−2q)/(p−q)} → q²/(p(p−q))`** — Astra's `h(−b) ~ K_{p,q} b^{β−1}`, `β = p/(2(p−q))`. Next: the chamber law `ℓ_t(−A,0)/√t → K₋(A) = (∫₀^A √(K_{p,q}) a^{(β−1)/2}... )` i.e. `∫₀^A √(Var_{−a t^{σ}}) ...` assembled through `wall_window_length` with `c₀ = −A t^σ`, `c₁ = 0` and `intervalIntegral.integral_comp_neg`; needs continuity of `b ↦ negVar b` on `(0,∞)` (dominated, negative `c`) and a power-asymptotic integral lemma (`f(b) b^{γ} → K` ⇒ `(∫₀^{A t^σ} √f)/t^{σ(1−γ/2)} → …`, Cesàro-type as in `ProfileTailLength`). Then general integer k multiplicity, product-prior inequality, round-27 consult.

**2026-09-25 (chamber law):** `NegativeChamberLaw` (3499549): power-law Cesàro, continuity of the profile variance on all of ℝ (uniform majorant for `c ≥ −b₁`), and **`negative_chamber_law`: `ℓ_t(−A,0)/√t → K₋(A) = L_{p,q} A^β/β`**, `β = p/(2(p−q))`, `L_{p,q} = (q/√(p(p−q)))(q/p)^{β−1}`. With `wall_recedes` this is the two-sided law of the two-monomial wall (log t on the `1/q` side, √t on the interior-minimiser side). Numerics (p=3,q=1): speed constant matches to 3 digits at b=50. Remaining: general integer k multiplicity (binomial expansion of `(T − log s)^k`, Λ-moments with `(log s)^r`), product-prior inequality `√(D₁²+D₂²) ≤ D(L₁+L₂) ≤ D₁+D₂`; then a round-27 Astra consult on what remains of the "map across the data manifold" programme.

**2026-09-25 (product prior):** `ProductPrior` (ec96134): `Var_u(L₁+L₂) = Var_u(L₁)+Var_u(L₂)` on `π₁⊗π₂` and `√(D₁²+D₂²) ≤ D(L₁+L₂) ≤ D₁+D₂`. Round-25/26 lists now closed except general integer k multiplicity and the square-root Fisher immersion (round-25 item 5). Round-27 consult: `gpt_responses/research_round27_{q,v1}.md`.

**2026-09-25 (round 27):** Astra round 27 (`gpt_responses/research_round27_v1.md`) ranking: (1) data-to-posterior quotient & response stability (finite data space, kernel of the pulled-back Fisher metric = loss contrasts constant π-a.e., `|D⟨O⟩[h]| ≤ √Var(O)√g(h,h)`; 500–1000 lines via a linear complement + `MeanMapChart`), (2) square-root immersion `Ψ = 2√p_a` into L²(π) with `⟨DΨ v, DΨ w⟩ = G` and the two-valued-contrast great-circle theorem (800–1600 + 400–900), (3) exact affinity–KL decomposition + dilation limits — LANDED as `AffinityKL` (df6fae8), (4) all integer k multiplicities via finite binomial sums: `u^{j+1}N_{j,k}(u) = Σ_r (−1)^r C(k,r) (log u)^{k−r} Λ_{j,r}(u)`, `A_j = j! − k M_{j,1}/x + O(x⁻²)`, `M_{1,1} = c+1`, `M_{2,1} = 2c+3` with `c = M_{0,1}` NEVER identified with −γ; quotient lemma for `(a₀ + a₁/x + O(x⁻²))/(b₀ + b₁/x + O(x⁻²))`; conclusion `u²V_k = 1 − k/log u + O(1/log² u)` (400–850 lines), (5) global wall chart `m : ℝ → (0,∞)` decreasing homeomorphism (`m' = −Var < 0`, endpoints from both chamber limits; 150–400 lines) and the genuinely two-term wall law (needs `Var_B(√B(z^q−1)) = q²/(p(p−q)) + O(1/B)`; 1200–2500 lines — NOT implied by the current o(1) matching), (6) interior-minimum geometry `t Var_{t,a}(f) → f'(x_a)²/H_a`, length `∫√H_a |x_a'| da` (900–1800). §3: hierarchy `d_FR ≤ d_M ≤ Length_G(γ)`; natural straight lines are NOT intrinsic geodesics in general (`g(∇_v v, w) = −(t³/2)κ(R_v,R_v,R_w)`); two-valued contrasts ⇔ great circles. Next: (5) global chart, then (4), then (1).

**2026-09-25 (global chart):** `GlobalWallChart` (78723af): the wall response holds for every real coupling, `Var_c(y^q) > 0` on ℝ, `m = ⟨y^q⟩` strictly decreasing continuous with `m(+∞) = 0`, `m(−∞) = +∞`, `profileMeanHomeomorph : ℝ ≃ₜ Ioi 0`. Round-27 item 5 (chart) DONE. Next: (4) general integer k multiplicity via Astra's binomial route (`u^{j+1}N_{j,k} = Σ_r (−1)^r C(k,r)(log u)^{k−r}Λ_{j,r}(u)`, `A_j = j! − k M_{j,1}/x + O(x⁻²)`, quotient lemma), then (1) data-to-posterior quotient.

**2026-09-25 (data quotient):** `DataQuotient` (ec2ae4f): kernel of `G_a` = a.e.-constant contrasts (independent of `a`), `P_a = P_b ↔ L_a − L_b` constant, `D_a⟨φ⟩[v] = −t Cov_a(φ, R_v)`, `|D⟨φ⟩[v]| ≤ √Var(φ)√G(v,v)`, and the path inequality along `C¹` data paths. Round-27 item 1 DONE (finite-alphabet affine form; the quotient manifold API was deliberately not built). Remaining round-27: (2) sqrt immersion + two-valued great circles, (4) general k, (6) interior-minimum geometry, (5b) two-term wall law.

**2026-09-25 (general k):** `LogPowGammaTails` + `MultiplicityModelK` (454cd8e): for the state density `(−log ℓ)^k dℓ` (`(λ,m) = (1,k+1)`), `u²Var_u = 1 − k/log u + O(1/log² u)` and **`∫_{u₀}^t √Var_u = log t − (k/2) log log t + K + o(1)` for EVERY k** (Watanabe's `−((m−1)/2) log log t`). Route: Astra's binomial expansion + `ratio_expansion`/`sq_expansion` (reusable). Round-27 items 1, 3, 4, 5(chart) DONE. Remaining: (2) square-root immersion + two-valued great circles, (6) interior-minimum geometry, (5b) two-term wall law; then a round-28 consult.

**2026-09-25 (two-valued geodesics):** `TwoValuedGeodesic` (20630ef): the computable core of round-27 item 2 — quadratic characterisation of two-valued contrasts, and for the two-atom state density `∫_s^t √Var_u = 2 arccos ρ(s,t)` exactly (Bernoulli line = great circle; the angular bound of `AngularBound` is attained). The `Lp`-valued immersion `Ψ = 2√p_a` itself was NOT built (Astra's 800–1600 lines of `Lp` differentiation); the inner-product identity `⟨DΨ v, DΨ w⟩ = G(v,w)` remains open in that form. Round-27 items 1, 2 (core), 3, 4, 5-chart DONE. Remaining: (6) interior-minimum geometry, (5b) two-term wall law, the `Lp` immersion; round-28 consult `gpt_responses/research_round28_{q,v1}.md`.

**2026-09-25 (round 28):** Astra round 28 (`gpt_responses/research_round28_v1.md`) ranking: (1) quotient mean map on `K^⊥` (`K` = a.e.-constant contrasts; `M(a+k) = M(a)`, `M(a) − M(0) ∈ K^⊥`, `M̃ : K^⊥ → K^⊥` a `C¹` diffeomorphism onto its image, global injectivity from `⟨M(b) − M(a), b − a⟩ = −t∫₀¹ Var_{a+s(b−a)}(R_{b−a}) ds < 0`; the descended potential `F̄(a) = F(a) + t⟨a, M(0)⟩`), (2) interior-minimum geometry via a domination wrapper (`t Var ≤ C` from `c h² ≤ ΔV ≤ C h²`, `w₋ ≤ w ≤ w₊`, `|f − f(x*)| ≤ L|h|`, tail gap, weighted envelope; centred moments `J_k`; identification `√H|x*'| = k₋|a|^{β−1}` on `[−A, −ε]`), (3) two-term wall law with the explicit coefficient `Var_B(√B(z^q−1)) = q²/(p(p−q)) + q²(p−2)/(2p²(p−q)) B⁻¹ + O(B⁻²)` (check: `p=4,q=2` gives `½ + 1/(8B)`), abstract expanding-window theorem first, constant `C_prof` independent of `A`, (4) `Lp` immersion, (5) ray chart `u ↦ ⟨ℓ⟩_u` decreasing homeomorphism `(0,∞) ≃ (ess inf ℓ, ⟨ℓ⟩_0)` + Legendre `F*(−m(u)) = KL(P_u‖π)`, (6) rate-function reading. WARNING: `B ≤ ½KL` does NOT give a KL lower bound for length. Landed from the "do immediately" list: `WallPhaseDiagram` (c6b175f: phase diagram + ray self-similarity). Still cheap: product equality case (`v₁/D₁ = v₂/D₂` a.e.). Next: (1) quotient mean map.

**2026-09-25 (quotient mean map):** `QuotientMeanMap` (d8a86f5): invisible subspace is a `Submodule`; `M(a+k) = M(a)`; annihilator identity; `M(a) = M(b) ↔ b − a ∈ K`; strict monotonicity `⟨M(b)−M(a), b−a⟩ = −t∫₀¹ Var < 0` off `K`. Round-28 item 1 core DONE (the `K^⊥` open-embedding packaging deferred). Next: (2) interior-minimum geometry via the domination wrapper, (3) two-term wall law (abstract expanding-window theorem + coefficient `q²(p−2)/(2p²(p−q))`), product equality case, ray chart + Legendre.

**2026-09-25 (interior minimum):** `InteriorMinimumTwoMono` (07990a7): for the two-monomial wall in the negative chamber (`a < 0`) the profile minimiser `x_a = (q|a|/p)^{1/(p−q)}` with Hessian `H_a = p(p−q)x_a^{p−2}` satisfies `√H_a |x_a'| = k₋|a|^{β−1}`, the pointwise law `t·Var_{t,a}(w^q) → f'(x_a)²/H_a`, and the window law `ℓ_t(a₀,a₁)/√t → ∫_{a₀}^{a₁} √H_a|x_a'| da = K₋(−a₀) − K₋(−a₁)`: the negative chamber law IS the classical interior-minimum geometry (Astra round-28 item 2, realised as a corollary of the chamber law rather than through the abstract domination wrapper; the abstract 1D uniform theorem remains open). Astra's second-order coefficient `q²(p−2)/(2p²(p−q))` numerically CONFIRMED. Next: (3) two-term wall law (abstract expanding-window theorem: `h` with integrable residuals after subtracting `k s^{β−1}` at −∞ and `c/s` at +∞ ⇒ `K₋(A)√t + (σ/√q) log t + C_prof + (log a₁)/√q + o(1)`; positive tail from `WallRecedesStrong`, negative tail needs the `O(1/B)` Laplace refinement), product equality case (`v₁/D₁ = v₂/D₂` a.e.), ray chart `u ↦ ⟨ℓ⟩_u` + Legendre `KL(P_u‖π) = −u m(u) − F(u)` (corollary of `lawKL`), abstract 1D interior-minimum theorem, `Lp` immersion, `K^⊥` packaging; then round-29 consult.

**2026-09-25 (ray chart):** `RayChart` (5f89c43): `Var_u = Z⁻¹∫(ℓ−m)²e^{−uℓ} > 0` off the degenerate case, `m = ⟨ℓ⟩_u` strictly decreasing and a homeomorphism `(0,∞) ≃ₜ m''(0,∞)` (the ray chart), `F = log Z` convex with `F' = −m`, tangent inequality, and the Legendre identity `KL(P_u‖P_0) = −u m(u) − F(u) + F(0) = F(0) + sup_v(−m(u)v − F(v))` (attained at `v = u`): the KL from the featureless end of the ray is Cramér's rate function of the loss under the prior at the level `m(u)`. Round-28 items 5 (without the endpoint identification `m(∞) = ess inf ℓ`, which needs a Laplace-type input) and 6 (algebraic core) DONE. Next: two-term wall law (3), product equality case, abstract 1D interior-minimum theorem, `Lp` immersion, `K^⊥` packaging; round-29 consult.

**2026-09-25 (round 29, natural coordinates):** Astra round 29 (`gpt_responses/research_round29_v1.md`) re-ranked: (1) the joint exponential family `S = (L₀,R)`, `θ = (t, ta)`; (2) `N^⊥` open embedding + featureless anchor `KL(P_θ‖P_0) = ∫₀¹ s Var_{sθ}(S_θ) ds`; (3) ray Cramér curvature (`I(x) = −xu(x) − F(u(x))`, `I' = −u`, `I'' = 1/Var`, `ds² = I''(m) dm²`); (4) general ess-inf endpoint (no regular variation) + finite-alphabet endpoint distribution `P_{rh} → π(·|S_h = min)`; (5) moment-polytope image theorem (full natural family; the `t>0` image is NOT convex in general); (6) two-term wall law (full `c₁` derivation, sub-step order given); (7) abstract moving-minimum theorem. `NaturalCoordinates` (7734fc5) LANDED item 1 and the anchor of item 2: pull-backs of expectations/mean map/free energy/response form along `Θ`, joint kernel vs slice kernel, KL = Bregman of `ψ` (agreeing with the slice KL), the featureless anchor, and the ray chart coordinate as the joint mean map on the ray (`⟨L_a⟩ = η₀ + a·M`). Next: (3) Cramér curvature on `RayChart` (inverse chart `u(x)` from `exists_rayChart`, derivative via `HasDerivAt.of_local_left_inverse`), (4) ess-inf endpoint, then (2) the `N^⊥`-restricted embedding (plumbing over `MeanMapEmbedding` applied to `S` at `t = 1`), (6) two-term wall law.

**2026-09-25 (Cramér):** `RayCramer` (1f616eb): the ray chart is inverted on its open image (`u(x)`, `u' = −1/Var`), the rate function `I(x) = −x u(x) − F(u(x)) = sup_{v>0}(−xv − F(v)) = KL(P_{u(x)}‖P_0) − F(0)`, `I' = −u`, `I'' = 1/Var_{u(x)}` (Fisher speed = curvature of the rate function in the response coordinate), `I` convex, and the length substitution `∫_{u₀}^{u₁}√Var = ∫_{m(u₁)}^{m(u₀)} √(I'')`. Round-29 item 3 DONE. Next: (4) the ess-inf endpoint without regular variation (`m(u) → α` from `ν{ℓ < α+ε} > 0` + `sup_{y≥ε} y e^{−ry} = ε e^{−rε}`; finite-alphabet endpoint law `P_{rh} → π(·|S_h = min)`), then (2) the `N^⊥` packaging, (6) two-term wall law.

**2026-09-25 (endpoint):** `RayEndpoint` (ba4dda8): `⟨ℓ⟩_u → ess inf ℓ` as `u → ∞` with no regular variation (only `ℓ ≥ α` a.e. and positive mass near `α`), via Astra's tilt estimate. With `RayChart` + `RayCramer` the featureless ray is now charted from `⟨ℓ⟩_{0⁺}` down to the ground state `ess inf ℓ` and read as a convex rate function. Round-29 items 1, 3, 4 DONE, item 2's anchor DONE. Remaining: the finite-alphabet endpoint distribution `P_{rh} → π(·|S_h = min S_h)` (faces of the moment polytope), the `N^⊥` open-embedding packaging, the moment-polytope image theorem (5), the two-term wall law (6), the abstract moving-minimum theorem (7); then round 30.

**2026-09-25 (faces):** `FiniteEndpoint` (59b7c51): on a finite alphabet every natural ray `rh` of the joint family ends at the prior conditioned on the face `{S_h = min S_h}` (`P_{rh} → π(·|S_h = min)`, `M(rh) → E_π[S | S_h = min]`): the global boundary map of the response chart, featureless anchor → ground states in every direction. Round-29 items 1, 3, 4 (+ finite-alphabet endpoint law) DONE, anchor of 2 DONE. Remaining: `N^⊥` open-embedding packaging (2), moment-polytope image theorem (5: `η(E) = int conv S(Ω)`, coercivity of `θ ↦ ψ(θ) + ⟨θ,x⟩`), two-term wall law (6), abstract moving minimum (7); then a round-30 consult.

**2026-09-25 (moment polytope):** `MomentPolytope` (daa0d87): on a finite alphabet with positive prior and nondegenerate statistic, `range η = interior conv S(X)` — the strongest global statement of the response chart (Astra round-29 item 5): every interior point of the moment polytope is realised by exactly one posterior (open embedding + variational surjectivity), the boundary faces are the ray endpoints (`FiniteEndpoint`), the origin of natural coordinates is the prior (`NaturalCoordinates`). Round 29 items 1–5 DONE (item 2 minus the degenerate `N^⊥` plumbing). Remaining: two-term wall law (6), abstract moving minimum (7), `N^⊥` packaging; round-30 consult next (what remains for the "map across the data manifold" beyond the finite alphabet: the moment-polytope theorem for bounded statistics on a general alphabet — closure of the range = closed convex hull of the essential range? — and the wall-crossing constants).

**2026-09-25 (round 30, segment divergences):** Astra round 30 (`gpt_responses/research_round30_v1.md`): corrections (wall family non-steep, mean band `v^r < u ≤ C_Γ v^r` inside the convex support, temperature rays log-infinite in all chambers, `L² ≤ 2KL` false) and ranking: (1) bounded-statistic moment-body theorem on a general probability space (`range η = interior (closed conv (essRange S))`, key lemma: uniform positive-mass cap `μ{−⟨e, S − x⟩ ≥ c} ≥ m` for all unit `e`), (2) full mean-coordinate potential (multivariate `RayCramer`), (3) segment identities — LANDED as `SegmentDivergence` (965c96f: `KL(P_b‖P_a) = t²∫ sV`, `KL(P_a‖P_b) = t²∫(1−s)V`, Jeffreys `Length² ≤ KL + KL`, three-point identity, Pythagoras, projection orthogonality), (4) fixed-temperature graph / partial minimisation, (5) `N^⊥`, (6) wall mean band, (7) two-term wall law, (8) moving minimum. Next: (1) the bounded-statistic moment body (cap lemma first, then the finite proof runs unchanged), then (2).

**2026-09-25 (moment body, general alphabet):** `EssentialRange` + `MomentBody` (7193793): for a bounded statistic under a positive prior on ANY measurable space, with no a.e.-constant nonzero contrast, `range η = interior (closed conv (essRange S))`. Round-30 item 1 DONE (the finite-alphabet `MomentPolytope` is now a special case in spirit; both stay). Next: (2) the full mean-coordinate potential (`DualPotential`: inverse chart `θ(m)` on the open range via `meanMapHomeomorph`, derivative `(meanMapDerivEquiv).symm` by `HasFDerivAt.of_local_left_inverse`, `I(m) = −⟨θ(m),m⟩ − ψ(θ(m))`, `∇I = −θ`, `D²I = G⁻¹`, `KL = Bregman of I` in mean coordinates, path-length transport `Length_G = ∫√⟨ṁ, D²I ṁ⟩`), then (4) fixed-temperature graph, (5) `N^⊥`, (6) wall mean band, (7) two-term wall law.

**2026-09-25 (dual potential):** `DualPotential` (42c4b76): the response geometry in mean coordinates for the general affine family — `DA = −t⟨·, m⟩`, `I(y) = −t⟨θ(y),y⟩ − A(θ(y))`, `KL = Bregman(I)` in mean coordinates, `∇I(m(a)) = −t a`, `D²I = −t(Dm)⁻¹` inverting the covariance, `⟨Dm v, D²I Dm v⟩ = G(v,v)` (path-length transport pointwise). Round-30 items 1, 2, 3 DONE. Remaining: (4) fixed-temperature graph / partial minimisation, (5) `N^⊥`, (6) the wall mean band, (7) two-term wall law, (8) abstract moving minimum; round-31 consult next.

**2026-09-25 (temperature slices):** `TemperatureSlice` (ad5fa33): the fixed-temperature slice is the contrast family under the tilted prior `e^{−tL₀}π` (natural parameter `t a`), whose null sets are those of `π`; hence `range (a ↦ m(t,a)) = interior (momentBody R)` at every temperature, a bijection, and the joint-family slice is a graph `η₀ = h_t(M)` over the same open convex body for all `t`. Round-30 item 4 (coverage half; the variational characterisation `∂_{η₀}I = −t` and the reduced potential `J_t` not built). Remaining: (5) `N^⊥`, (6) wall mean band, (7) two-term wall law, (8) abstract moving minimum; round-31 consult next.

**2026-09-25 (observable regression):** `ObservableRegression` (see git log): the response of an arbitrary bounded observable in mean coordinates, `DΦ = Cov(φ,R)·Cov(R,R)⁻¹` (regression on the sufficient statistic) and the sensitivity bound `|DΦ ṁ| ≤ √Var(φ)√⟨ṁ,D²I ṁ⟩`. This is the PI's "change of posterior expectation values with the change of the data distribution" in the response chart. Next: round-31 consult (remaining: `N^⊥`, wall mean band, two-term wall law, abstract moving minimum, the variational characterisation of the temperature slice).

**2026-09-25 (round 31, Legendre/entropy):** Astra round 31 (`gpt_responses/research_round31_v1.md`) re-ranked after the bounded case closed: (1) Legendre identity + constrained entropy minimisation — LANDED as `LegendreMaximum` (4714c57: `IsMaxOn` of the dual objective at `a₀`, unique under nondegeneracy; `KL(q‖P_0) = KL(q‖P_a) + I(m(a)) + A(0)` for every probability density with the contrast means of `P_a`, hence `P_a` is the least-informative distribution realising its response); (2) the wall mean band via the Schur-complement fixed-mean derivative `∂_α U = −(Var F − Cov(F,z)²/Var z)` and entropy competitors at the endpoints (no Laplace asymptotics needed); (3) temperature-slice variational principle incl. `∂_t h_t(M) = −` residual variance of `L₀` after regression on `R`; (4) non-steep boundary extension; (5) `N^⊥`; (6) two-term wall law; (7) observable segment transport; (8) Cramér. Next: (2) the wall mean band (abstract fixed-mean monotonicity lemma first), then (3).

**2026-09-25 (slice variational):** `SliceVariational` (10b16c1): tangent inequality and convexity of the dual potential on the response space; in the joint family `∂_e I = −t` at the slice point and the slice point minimises `I(e,M) + te` over the fibre — the temperature slice as the graph of the minimiser of the reduced potential `J_t(M) = inf_e (I(e,M) + te)`. Round-31 items 1 and 3 (variational core; the residual-variance identity `∂_t h_t(M) = −(Var L₀ − Cov(L₀,R)C_RR⁻¹Cov(R,L₀))` and `D²J_t = C_RR⁻¹` NOT built — they need block inversion of the joint covariance). Remaining: (2) wall mean band, (4) non-steep boundary extension, (5) `N^⊥`, (6) two-term wall law, (7) observable segment transport, (8) Cramér.

**2026-09-25 (mean segment):** `MeanSegment` (b9b314d): the inverse Jacobian of the mean map is continuous; along the mean segment (`m`-geodesic) the observable transport `⟨φ⟩_{a₁} − ⟨φ⟩_{a₀} = ∫₀¹ D⟨φ⟩(γ_s)[(Dm)⁻¹d] ds`, the dual segment identities `KL(P_{a₁}‖P_{a₀}) = ∫(1−s)Q`, `KL(P_{a₀}‖P_{a₁}) = ∫ sQ` with `Q = ⟨d, D²I d⟩` (mirror of `SegmentDivergence`), `∫Q = Jeffreys`, and `|Δ⟨φ⟩|² ≤ (∫Var φ)(KL + KL)`. Round-31 items 1, 3 (core), 7 DONE. Remaining: (2) wall mean band, (4) non-steep boundary extension, (5) `N^⊥`, (6) two-term wall law, (8) Cramér; round-32 consult next.

**2026-09-25 (constrained response):** `ConstrainedResponse` (0c45475): the fixed-mean derivative. Moving the data in direction `v` while adjusting `w` so that `⟨R_w⟩` is constant, `d/ds⟨R_v⟩ = −t (Var R_v − Cov(R_v,R_w)²/Var R_w)`; the Schur complement is the variance of the regression residual `R_{v−λw}` and is positive iff `R_v` is not a.e. affine in `R_w`. This is the abstract core of round-31 item 2 (the wall mean band `∂_α U = −(Var F − Cov(F,z)²/Var z)`); the wall instance itself (unbounded statistic `F = log x`, `z`) is NOT built — it needs the unbounded-statistic tilt data. Remaining: (2) wall instance, (4) non-steep boundary extension, (5) `N^⊥`, (6) two-term wall law, (8) Cramér; round-32 consult next.

**2026-09-25 (featureless point):** `FeaturelessPoint` (e2bec0f): `0 < KL(P_b‖P_a)` for `a ≠ b` (so the family is injectively embedded in divergence), `I(m 0) = −A(0)`, `I(y) − I(m 0) = KL(P_{θ(y)}‖P_0)` on the response space, hence the prior's response is the unique minimiser of the dual potential and `I + A(0)` is the information-relative-to-featureless function on the response space. This is the origin of the PI's "map from featureless to data": the dual potential, normalised at the prior, is the KL distance from the featureless distribution as a function of the response. Round-32 consult next.

**2026-09-25 (Astra round 32 + multi-constrained response):** Round-32 ranking (`gpt_responses/research_round32_v1.md`): (1) multi-constraint Schur + loss surface `h(t,M) = ⟨L₀⟩` on the slice with `∂_M h = cᵀC⁻¹` (regression of the loss on the features) and `∂_t h = −σ²` (unexplained variance), general observable `∂_t⟨φ⟩|_M = −Cov(φ,L₀) + Cov(φ,R)C⁻¹c`, and the full reduced Hessian `D²J = [[−σ², cᵀC⁻¹],[C⁻¹c, C⁻¹]]`, `∂_tJ = h`, `∇_MJ = −β`; work in the natural feature coordinate `β = ta` with `F(t,β) = (t, m(t,β))` for the IFT (only `C_RR` needs inverting); (2) annealing bridge (fixed `E`: `d/dt⟨φ⟩ = −Cov(φ,E)`, `KL(P_T‖ρ̄) = ∫₀ᵀ s Var_s E`, pathwise chain rule for loss paths, data-manifold bridge `L_ν = ∫ℓ(·,z)dν`); (3) `N^⊥`; (4) second-order response `D²m[u,v] = t² Cum₃`; (5) Cramér; (6) boundary; (7) wall band instance; (8) two-term wall law. Corrections: the featureless point is `P_{t,0} = e^{−tL₀}π`, not `π`; information level sets are not a dual foliation. `MultiConstrainedResponse` (72ae2fd) lands the algebraic engine of (1): covariance matrix of constrained statistics, regression residual identity and its vanishing criterion, invertibility under nondegeneracy, and the multi-constrained response derivative for any bounded observable. NEXT: the loss surface (IFT on `F(t,β) = (t, m(t,β))` in the joint natural coordinates, then `∂_t h = −σ²`, `∂_M h = cᵀC⁻¹`), then the reduced potential's Hessian, then the annealing bridge.

**2026-09-25 (slice chart + loss surface):** `SliceChart` (675ddb5) and `LossSurface` (abbe53f). The slice map `θ ↦ (θ_none, ⟨R⟩_θ)` of the joint family is strictly differentiable with injective derivative under FEATURE nondegeneracy only, injective on positive temperatures, with a strictly differentiable partial inverse; the temperature path `tempPath M t` (slice point at temperature `t` with feature response `M`) is differentiable in `t`. Consequences: for every bounded `φ`, `∂_t⟨φ⟩|_M = −(Cov(φ,L₀) − ∑ bₖ Cov(φ,Rₖ))` with `C b = Cov(R,L₀)`; the loss surface `h(t,M) = ⟨L₀⟩` has `∂_t h = −Var(L₀ − ∑ bₖRₖ)` (unexplained variance) and is nonincreasing in `t`; in the feature directions `D_M⟨φ⟩[d] = ∑ bₖ dₖ` (regression coefficients). Round-32 item 1 DONE except the reduced potential's block Hessian (`∂_tJ = h`, `∇_MJ = −β`, `D²J`); NEXT: that Hessian (`J(t,M) = I_t(M)` with `∂_t I_t(M) = h_t(M) − ?` — check Astra's normalisation warning `∂_t𝒦 = h − E_{P_{t,0}}L₀`), then the annealing bridge (round-32 item 2), then `N^⊥`.

**2026-09-25 (reduced potential):** `ReducedPotential`: `∂_t A_t(a) = −⟨L_a⟩`, envelope identity `∂_t J(t,M) = h(t,M)`, `∂_t(J + A_t(0)) = h − ⟨L₀⟩_{t,0}`, `D_M²J = C⁻¹`, mixed partial `∂_tβ = −b`. Round-32 item 1 COMPLETE (block Hessian assembled). NEXT: round-32 item 2, the annealing bridge (fixed energy `E`: `d/dt⟨φ⟩_t = −Cov_t(φ,E)`, `KL(P_T‖ρ̄) = ∫₀ᵀ s Var_s E ds`, thermodynamic length; pathwise chain rule `d/ds⟨φ⟩_{P_s} = −t Cov(φ, L̇_s)` for loss paths; data-manifold bridge `L_ν = ∫ℓ(·,z)dν(z)`), then `N^⊥` (item 3), second-order response `D²m = t² Cum₃` (item 4).

**2026-09-25 (annealing ray):** `AnnealingRay`: `d/dt⟨φ⟩_{t,a} = −Cov(φ, L_a)`, `E' = −Var(L₀)`, `E` antitone on `ℝ`, `∫₀ᵀ Var = E(0) − E(T)`, `KL(P_T‖π̄) = ∫₀ᵀ u Var_u ≤ T(E(0) − E(T))`, `(Δ⟨φ⟩)² ≤ (∫₀ᵀ Var φ)(E(0) − E(T))`. Round-32 item 2 fixed-energy part DONE. NEXT: the data-manifold bridge (mixture paths of data distributions `ν_s = (1−s)ν₀ + sν₁` give affine loss paths `L_{ν_s} = L₀ + sΔ`, so the pathwise response is `−t Cov(φ, L₁ − L₀)`; a small `DataMixture` module), then `N^⊥` (item 3), then `D²m = t² Cum₃` (item 4); a round-33 consult after those.

**2026-09-25 (data mixture):** `DataMixture`: the population loss `L_ν = ∫ℓ(·,z)dν` (`dataLoss`) is affine along mixtures of data distributions, so the segment `ν_s` in the data manifold is the affine loss path `L_{ν₀} + s(L_{ν₁} − L_{ν₀})`; response `d/ds⟨φ⟩ = −t Cov(φ, L_{ν₁} − L_{ν₀})` and both KL segment identities between the posteriors of two data distributions. Round-32 item 2 DONE (fixed-energy ray + data-manifold bridge). NEXT: `N^⊥` (item 3), second-order response `D²m = t² Cum₃` (item 4); then a round-33 consult.

**2026-09-25 (third cumulant):** `ThirdCumulant`: `κ₃`, covariance derivatives along data lines (`−t κ₃(φ,ψ,R_v)`) and in temperature (`−κ₃(φ,ψ,L_a)`), `D²m[u,v] = t² κ₃(R,R_u,R_v)`, `∂_w G(u,v) = −t³ κ₃(R_u,R_v,R_w)` (Amari–Chentsov tensor). Round-32 item 4 DONE. Remaining ranked: (3) `N^⊥` quotient packaging, (5) Cramér, (6) boundary theory, (7) wall band instance, (8) two-term wall law. NEXT: round-33 consult (what remains for "maximum beauty and depth" now that items 1, 2, 4 are complete), then `N^⊥`.

**2026-09-25 (Astra round 33):** see memory summary and `gpt_responses/research_round33_v1.md`. Ranking: (1) boundary rays (scalar tilt ladder A–D, then `V = R_v`, `q = P_{t,0}`), (2) `N^⊥` by restriction, (3) two-axis response + integrability (cheap), (4) three-point KL identity (check `mixKL_three_point` — may already be it), (5) Cramér (extended rate), (6) second-order loss surface, (7) lengths, (8) wall asymptotics. Plan: ship (3), (4), (6) as short consolidations while building (1).

**2026-09-25 (two-axis response):** `TwoAxisResponse`: exactness of the response one-form `d⟨φ⟩ = −Cov(φ,L_s)dt − tCov(φ,D)ds` and of `dA = −⟨L_s⟩dt − t⟨D⟩ds` along data lines (both mixed partials computed and equal). Round-33 items 3 and 4 DONE (4 was already `mixKL_three_point`). NEXT: (1) boundary rays — scalar tilt ladder (`Z_λ → q(V = α)`, positive-mass face limits, KL limits), (2) `N^⊥` by restriction, (6) second-order loss surface.

**2026-09-25 (face limit):** `FaceLimit`: the scalar tilt ladder, positive-mass half — `e^{λα}Z_λ → ∫_F π`, boundary posterior `⟨φ⟩_λ → E[φ | F]`, `λ⟨V−α⟩ → 0`, `KL → −log π̄(F)`, and the feature-ray instantiation. NOT DONE: the zero-mass face `KL → ∞` (needs the two-event Jensen/data-processing bound: Jensen for `x log x` on the restricted normalised measures, `ConvexOn.map_average_le` with `convexOn_mul_log`). NEXT: zero-mass face, then `N^⊥`, then second-order loss surface.

**2026-09-25 (face infinite):** `FaceInfinite`: `KL(q_λ‖π̄) → +∞` for a zero-mass supporting face (two-event tangent bound + concentration + vanishing neighbourhood mass). Round-33 item 1 COMPLETE (positive-mass face: boundary posterior at finite cost `−log π̄(F)`; zero-mass face: infinite cost). NEXT: (2) `N^⊥` by restriction, (6) second-order loss surface, (5) Cramér with the extended rate; round-34 consult after those.

**2026-09-25 (effective features):** `EffectiveFeatures`: `N^⊥` by restriction — `ker C = N`, `P_{a+n} = P_a`, bijective chart `m|_W : W ≃ range m` and positive-definite response form on any complement `W` of `N`, `dim W + dim N = |ι|`. Round-33 item 2 DONE. NEXT: (6) second-order loss surface (`D²_M h[d,e] = κ₃(R_{q_d},R_{q_e},H)`, `∂_t D_M h[d] = −κ₃(R_{q_d},H,H)`, `∂_t² h = κ₃(H,H,H)`), then (5) Cramér with the extended rate; round-34 consult.

**2026-09-25 (Astra round 34):** see memory + `gpt_responses/research_round34_v1.md`. NEXT (1): second-order loss surface — layers A/B/C (normal-equation derivative via continuity of `C⁻¹`; envelope lemma for `s = v − c·b`; cumulant specialisation along `tempPath`), giving `∂_t²h = κ₃(H,H,H)` with `H = L₀ − b·R`; then (2) actual-data reachability polytopes, (3) lengths, (4) journey theorem.

**2026-09-25 (loss curvature):** `ResidualFormDeriv` (envelope derivative of `v − ⟨c,b⟩` with `b` only continuous) + `LossCurvature`: `∂_t² h(t,M) = κ₃(H,H,H)`, `H = L₀ − b·R`; every covariance moves by `−κ₃(·,·,H)` along the temperature path; `b = C⁻¹c` continuous. Round-34 item 1 DONE (the `E_tt` block; the mixed/`MM` blocks of the residual-cumulant Hessian not built). NEXT: (2) actual-data reachability: finite family of data losses `ℓ(·,z_j) = L₀ + a_j·R + k_j`, mixture polytope `conv{a_j}`, reachable responses `m_t(conv{a_j})` compact and not all of `int K`, reachability criterion; (3) lengths; (4) journey theorem `KL(P_{η₁}‖P_{η₀}) = ∫₀¹ G_{η_s}(η_s − η₀, η̇_s) ds`; (5) halfspace Chernoff.

**2026-09-25 (data reachability):** `DataReachability`: finite mixtures of feature-affine data distributions, reachable responses `= m_t '' conv{aⱼ}`, compact, inside `int K`, reachability criterion. Round-34 item 2 DONE (the "not all of int K" claim is not formalised — needs a witness). NEXT: (3) lengths — `(∫₀ᵀ√Var_u)² ≤ T(E(0)−E(T))`, `|Δ⟨φ⟩| ≤ ∫√Var φ · v_F`, `Length_F ≥ 2|Δ⟨φ⟩|/(b−a)`; (4) journey theorem `KL(P_{η₁}‖P_{η₀}) = ∫₀¹ G_{η_s}(η_s − η₀, η̇_s) ds` for any path; (5) halfspace Chernoff; then a round-35 consult.

**2026-09-25 (journey):** `JourneyPotential`: `KL(P_{η(1)}‖P_{η(0)}) = ∫₀¹ G_{η(s)}(η(s) − η(0), η'(s)) ds` for any `C¹` path in the natural coordinates (differential of the endpoint divergence); segment corollary. Round-34 item 4 DONE. NEXT: (3) lengths (`(∫₀ᵀ√Var)² ≤ T(E(0)−E(T))`, Fisher-length lower bound on observable change), (5) halfspace Chernoff; then a round-35 consult.

**2026-09-25 (ray lengths):** `RayLength`: Fisher length `Length(T) = ∫₀ᵀ √Var_u(L₀)` of the annealing ray; `Length(T)² ≤ T(E(0) − E(T))`; `|Δ⟨φ⟩| ≤ ∫√(Var φ · Var L₀)`; Popoviciu `Var φ ≤ ((hi−lo)/2)²`; `|Δ⟨φ⟩| ≤ ((hi−lo)/2) Length(T)`, i.e. `Length(T) ≥ 2|Δ⟨φ⟩|/(hi−lo)`. Round-34 item 3 DONE. NEXT: (5) halfspace Chernoff `P(u·R̄_n ≥ r) ≤ exp[−n sup_λ{λr − Λ(λu)}]`; then a round-35 consult.

**2026-09-25 (halfspace Chernoff):** `HalfspaceChernoff`: `P(u·R̄_n ≥ r) ≤ exp[−n(λr − Λ_ν(λu))]` for i.i.d. samples of bounded features (Mathlib Chernoff + `iIndepFun_pi`), `iInf` form; `familyMeasure` (P_{t,a} as a measure, probability, expectations = `priorExp`); `Λ_{P_{t,a}}(θ) = A_t(a − θ/t) − A_t(a)`, so the Chernoff rate under a family member is the Legendre transform of the free energy. Round-34 item 5 DONE (halfspace form only; closed-set finite-n bound is false). NEXT: round-35 Astra consult (candidates: mixed/MM blocks of the residual-cumulant Hessian, finite-union/compact-cover Cramér upper bound, reachable-set ≠ int K witness, Legendre identification `sup_λ{λr − Λ(λu)}` with the dual potential along the ray a − (λ/t)u).

**2026-09-25 (information projection):** round-35 consult (`gpt_responses/research_round35_*`): ranking (1) Chernoff ⇄ information projection, (2) unified residual-cumulant Hessian `D²h[X,Y] = κ₃(H, S_X, S_Y)` with `S_{(τ,v)} = −τH + V_v`, `V_v = (C⁻¹v)·R` (MM block is `C⁻¹K_HC⁻¹`, NOT `−C⁻¹`), (3) entropy geometry `𝒮(P_{t,a}) = −KL(P_{t,a}‖π̄) = t h + t a·M + A_t(a)`, `d𝒮 = t dh + t a·dM`, `P_{t,0}` = max relative entropy at its loss expectation, (4) joint-chart Fisher metric `g((τ,v),(τ,v)) = τ² Var(H) + vᵀC⁻¹v` (temperature ⊥ response), arcsine length bound `Length ≥ 2|arcsin√z(1) − arcsin√z(0)|`, (5) compact-cover Cramér, (6) reachable-chart synthesis. Landed (1): `HalfspaceProjection` (attained value, halfspace Pythagorean identity, primal/dual optimality, IsLeast/IsGreatest, Chernoff exponent = `KL(P_{a*}‖P_a)`); and the properness witness `reachableResponse_ne_range`. NEXT: (2) unified Hessian (start with `∂_v b = C⁻¹κ₃(R,H,V_v)` via the identity `Cb = c`), (4) joint-chart metric, (3) entropy geometry, then interior-threshold existence for the projection (`u·m(a) < r < ess sup u·R` ⇒ finite tilt).

**2026-09-25 (joint-chart metric):** `JointChartMetric`: `natForm` (Fisher form in natural coords), chart velocity `D sliceInv(τ,v) = (τ, −τb − C⁻¹v)`, block-diagonal metric `G((τ,v),(τ',v')) = ττ'Var(H) + v'·C⁻¹v` (temperature ⊥ response), general-path observable bound `|Δ⟨φ⟩| ≤ ((hi−lo)/2)·natLength`, `natLength ≥ 2|Δ⟨φ⟩|/(hi−lo)`. Round-35 item 4 DONE. NEXT: (2) unified residual-cumulant Hessian `D²h[X,Y] = κ₃(H,S_X,S_Y)` — the score `S_X = τH − R_{C⁻¹v}` is now available as `dirLoss_jointStat_sliceInv_deriv`, so the MM/tM blocks are derivatives of `h(t,M) = ⟨L₀⟩_{sliceInv(t,M)}` along chart directions: differentiate `Cov` along a chart path with velocity `S_X` (`hasDerivAt_cov_of_hasDerivAt_exp` with `c = 1`, `D = S_X`); (3) entropy geometry `𝒮 = −KL(P_{t,a}‖π̄) = t h + t a·M + A_t(a) − log∫π`, `d𝒮 = t dh + t a·dM`; interior-threshold existence for the projection; arcsine length bound.

**2026-09-25 (entropy geometry):** `RelativeEntropyGeometry`: `𝒮(θ) = −KL(P_θ‖π̄) = ⟨θ,m(θ)⟩ + A(θ) − A(0)`, `(t,a)`-chart form, `𝒮 ≤ 0 = 𝒮(π̄)`, `d𝒮 = −G_θ(θ,·)`, `d/dt 𝒮|_M = −t Var(H)`, general difference identity, featureless point = max relative entropy at its loss expectation (Gibbs variational principle within the family). Round-35 item 3 DONE. NEXT: (2) unified residual-cumulant Hessian `D²h[X,Y] = κ₃(H, S_X, S_Y)` (score `S_X` from `dirLoss_jointStat_sliceInv_deriv`; differentiate `⟨L₀⟩ ∘ sliceInv` along chart lines `M + s v` with `hasDerivAt_cov_of_hasDerivAt_exp`); interior-threshold existence for the halfspace projection; arcsine length bound; compact-cover Cramér.

**2026-09-25 (unified Hessian):** `ChartPathDerivatives` + `LossHessian`: along any differentiable path in natural coordinates, `d Cov = −κ₃(·,·,S)`, `d b = −C⁻¹κ₃(R,H,S)`, `d Var(H) = −κ₃(H,H,S)`; on the joint chart the chart score of `(τ,v)` is `τH − (C⁻¹v)·R`, the gradient is `−τ Var(H) + v·b`, and **`D²h[X,Y] = κ₃(H, S_X, S_Y)`** (`hasDerivAt_lossGrad_line`): the entire loss curvature is one residual-cumulant tensor (tt = κ₃(H,H,H), tM = −κ₃(H,H,V_v), MM = κ₃(H,V_v,V_w) = C⁻¹K_HC⁻¹ ≠ −C⁻¹). Round-35 item 2 DONE. Round-35 items 1–4 all DONE. NEXT: round-36 consult; candidates: interior-threshold existence for the halfspace projection (`u·m(a) < r < ess sup u·R` ⇒ finite tilt), arcsine length bound, compact-cover Cramér, reachable-chart synthesis, symmetry `D²h[X,Y] = D²h[Y,X]` as a corollary (κ₃ symmetric), positivity/sign questions for the MM block.

**2026-09-25 (interior thresholds):** round-36 consult saved (`research_round36_*`): audit clean; corrections: the full-family m-Hessian of `h` is 0 (h is a mixture coordinate) — the response block is the INTRINSIC mixture Hessian of the fixed-temperature family, `Hess^{(e)}h = κ₃(L₀,S_X,S_Y)`, `B^{(m)}(v,w) = −D²_M h[v,w]/σ² ∂_t|_M`; energy-score sign convention for α-connections; contraction `tr(CK) = Cov(H,Q) = −∂_t log det C|_M`. Ranking: (1) global chart synthesis (largely present: `range_meanMap_slice`, `sliceMap_injOn/surj`, `hasStrictFDerivAt_sliceInv`; package as BijOn + continuity), (2) interior-threshold existence — DONE now (`InteriorThreshold`: tilted mean → ess sup with only accessibility; `d/dλ u·m(a_λ) = Var(R_u)`; every `u·m(a) < r < ess sup` has a finite tilt; `sup_μ{μr − Λ(μu)} = inf{KL(b‖a) : u·m(b) ≥ r}`), (3) fixed-temperature mixture-geometry capstone, (4) arcsine bound, (5) compact-cover Cramér. NEXT: symmetry corollary of the Hessian + block instances; global chart packaging; contraction identity; arcsine bound.

**2026-09-25 (global chart):** `LossHessianBlocks` (symmetry + tt/tM/MM blocks) and `ChartSynthesis` (`responseChart : PartialHomeomorph` from `{θ_none > 0}` onto `chartDomain = {t>0} × int K`, `BijOn`, continuity of `h` and `𝒮` on the chart domain). Round-36 items 1 (packaging), 2 DONE. NEXT: arcsine length bound `Length ≥ 2|arcsin√z(1) − arcsin√z(0)|`; contraction identity `tr(CK) = Cov(H,Q)`; compact-cover Cramér; then a round-37 consult.

**2026-09-25 (arcsine):** `ArcsineLength`: Bhatia–Davis + `2|arcsin√z(1) − arcsin√z(0)| ≤ Length` along any C¹ natural path with interior observable expectations. NEXT: compact-cover Cramér (`CompactCoverCramer`: finite-union Chernoff + finite subcover from pointwise dual witnesses ⇒ `P(R̄_n ∈ F) ≤ N e^{−nα}`), contraction identity, round-37 consult.

**2026-09-25 (compact-cover Cramér):** `CompactCoverCramer`: finite-union Chernoff and `P(R̄_n ∈ F) ≤ N e^{−nα}` for compact `F` with pointwise dual witnesses `θ·x − Λ(θ) > α`. Round-36 items 1, 2, 4, 5 DONE (3 = interpretation, in the slop note). NEXT: round-37 consult (`research_round37_*`); candidates: contraction identity `tr(CK) = Cov(H,Q)`, asymptotic form `limsup (1/n) log P ≤ −α`, canonical parameter map on the reachable locus, second fundamental form of the fixed-temperature leaf, consolidation of the slop note.

**2026-09-25 (data locus):** round-37 consult saved (`research_round37_*`): audit clean (essential-inf characterisation exact; arcsine interiority on all ℝ harmless; compact-cover witnesses ⇔ `α < inf_F I` by compactness + lsc); the SEVEN-THEOREM SPINE for the note: I global response atlas, II data calibration factors through moments/coefficients, III covariance is the response metric, IV third cumulants govern constrained bending, V integrated journeys (with the `(t,0) ≠ π̄` reference distinction), VI boundary approach and concentration, VII variational cost and fluctuation rarity. Ranking: (1) canonical data assignment — DONE now as `DataLocus` (in our setting data → coefficients is LINEAR, so the pulled-back loss Hessian is the e-Hessian `t²κ₃(L₀,·,·)`, not the residual one), (2) one reference-to-data journey theorem, (3) mixture second fundamental form `𝓑(v,w)`, (4) contraction + log-det, (5) tilt-based finite-n lower bound (Chebyshev), (6) asymptotic compact upper bound, (7) walls. NEXT: (2) journey theorem package; (5) lower bound; then consolidate the note along the seven-theorem spine.

**2026-09-25 (natural journey):** `NaturalJourney`: along the natural ray `s θ` from the prior: `𝒮 = −∫ s G`, `d𝒮/ds = −s G ≤ 0` (antitone), length/arcsine bounds; two-leg decomposition `𝒮(t,a) = 𝒮(t,0) − KL(P_{t,a}‖P_{t,0}) + t(⟨L₀⟩_{t,a} − ⟨L₀⟩_{t,0})`. Round-37 item 2 DONE; the seven-theorem overview was added to the slop note. NEXT: tilt-based finite-n lower bound (Chebyshev; needs product-density change of measure), mixture second fundamental form 𝓑, contraction identity; round-38 consult.

**2026-09-25 (mixture bending):** `MixtureBending`: the Fisher-normal mixture acceleration 𝓑(v,w) of the fixed-temperature family — symmetric, centred, orthogonal to every feature, and `⟨H𝓑(v,w)⟩ = κ₃(H,V_v,V_w)` (= the response block of the loss Hessian). Round-37 items 1–3 DONE (4 contraction, 5 tilt lower bound, 6 asymptotic, 7 walls open). NEXT: round-38 consult; or the tilt lower bound (needs `Measure.pi` of `withDensity` = `withDensity` of the product density — NOT in Mathlib; prove via `Measure.pi_eq` on boxes + `lintegral_fintype_prod_eq_prod`).

**2026-09-25 (tilt lower bound):** `ProductDensity` + `TiltLowerBound`: `P_a^{⊗n}(R̄_n within ε of m_t(b)) ≥ e^{−n(KL(P_b‖P_a)+δ)}` for large n — the information distance is the EXACT exponential cost of a response fluctuation (upper bound: halfspace Chernoff/projection; lower bound: change of measure to the tilt + Chebyshev). Round-37 items 1,2,3,5 DONE; open: 4 contraction/log-det, 6 asymptotic form, 7 walls. NEXT: round-38 consult.

**2026-09-25 (mean journey / duality capstone 1):** round-38 consult (`research_round38_{q,v1}`): top pick = Legendre duality + two-journey capstone (with the correction: FULL entropy is concave in FULL mean coordinates; on the fixed-t slice the concave potential is −KL(P_{θ(M)}‖P_{t,0})). Landed `MeanJourney`: mean segment coefficient `meanLine`, inverse-covariance form `meanSpeed = Δ·Cov⁻¹Δ ≥ 0`, `KL(P_{a₁}‖P_{a₀}) = ∫₀¹(1−s) Δ·Cov_{θ(M(s))}⁻¹Δ ds` = `t²∫₀¹ s Var(R_v)` (paired e/m identity), Jeffreys `KL+KL = ∫₀¹ q`, length ≤ √Jeffreys, `meanEntropy` concave, entropy antitone along the mean journey from m(0). Round-38 ranking remaining: 2 global visible quotient (`m(a)=m(b) ⇔ a−b invisible` via symmetrised KL), 3 quantitative stability (`t/(2β)‖M−N‖² ≤ KL ≤ t/(2α)‖M−N‖²`), 4 LD upper bound, 5 contraction/log-det, 6 walls. Audit notes: `dataLoss'` = expected BASE loss (not free energy) — note wording must say so; `mixBend` tensor carries `t²` for mean-coordinate velocities.

**2026-09-25 (response stability):** `ResponseStability`: under uniform ellipticity `α‖w‖² ≤ Var(R_w) ≤ β‖w‖²`, `2αKL ≤ ‖Δm‖² ≤ 2βKL` (mean journey) and `t²α‖Δa‖² ≤ 2KL ≤ t²β‖Δa‖²` (natural journey), hence the mean map is bi-Lipschitz `αt‖Δa‖ ≤ ‖Δm‖ ≤ βt‖Δa‖`; the upper bound is unconditional with `β = ∑Mᵢ²` from bounded features. Round-38: items 1 (duality/two journeys) and 3 (stability) DONE; item 2 (global fibre `m(a)=m(b) ⇔ a−b invisible`) was ALREADY landed as `meanMap_eq_iff_invisible` (QuotientMeanMap). Open: 4 LD upper bound, 5 contraction/log-det, 6 walls; Astra's §6 (constrained entropy minimisation) already landed as `dual_add_le_relEnt` (LegendreMaximum). NEXT: slop paragraphs (MeanJourney, ResponseStability, MixtureBending normalisation remark), then round-39 consult.

**2026-09-25 (full mean geometry + asymptotic form):** `FullMeanGeometry`: the round-38 capstone in the FULL geometry by instantiating MeanJourney on the joint family (L₀:=0, S, t:=1) under joint nondegeneracy: 𝒮 concave in full mean coordinates, gradient θ, Hessian −G⁻¹, `∫₀¹ s G_{sθ}(θ,θ) = KL(P_θ‖π̄) = ∫₀¹(1−s) Δ·G⁻¹Δ`, entropy antitone along the full mean journey. `AsymptoticUpperBound`: `P(R̄_n∈F) ≤ e^{−n(α−ε)}` eventually, log form under positivity. Round-38 items 1,2,3,4(compact) DONE. Open: 5 contraction/log-det (Jacobi EXISTS: `Laplace.Patterning.hasDerivAt_det_trace`), closed-set LD via exponential tightness, 6 walls. NEXT: slop paragraphs, round-39 consult.

**2026-09-25 (contraction identity):** `ContractionIdentity`: `tr(CK) = tr(TC⁻¹) = Cov(H, ZᵀC⁻¹Z) = −∂ₜ log det C|_M` (Jacobi from `Laplace.Patterning.hasDerivAt_log_det`). Round-38 items 1–5 DONE (2 pre-existing). Open: closed-set LD via exponential tightness, walls (split into mechanisms per Astra), full-geometry stability (instantiate ResponseStability on the joint family). NEXT: slop paragraph, round-39 consult.

**2026-09-25 (round 39: profile geometry):** consult `research_round39_{q,v1}`: audit OK (with the localisation warning: global ellipticity impossible for bounded features → ResponseStability made segmentwise); top pick "profile geometry" landed as `ProfileGeometry`: profile gap = KL, Pythagoras slice/temperature, rate contraction, entropy balance `d𝒮/ds = ⟨θ, μ'⟩` in full mean coordinates (D and E of the bundle were already landed: `natForm_sliceInv_deriv`, `hasDerivAt_relEntropy_temp`). Remaining from round 39: Schur complement C (`(u̇,Ṁ)ᵀG⁻¹(u̇,Ṁ) = ṀᵀV⁻¹Ṁ + (u̇ − cᵀV⁻¹Ṁ)²/δ`), fluctuation–response `Cov(R̄_n) = V/n`, full bounded-feature LDP (closed sets via the box; open lower bound via tilt + interior approximation), first wall theorem (ray concentration on the exposed face, `Var_{t,rv}(R_v) → 0`), overview theorem V rewrite in the note. NEXT: slop paragraphs (profile geometry + stability localisation + theorem V rewrite), then fluctuation–response and the wall theorem.

**2026-09-25 (fluctuation–response + first wall theorem):** `FluctuationResponse`: `Var(v·R̄_n) = v⬝Cov_a v/n = −v⬝Dm_t(a)v/(nt)`. `WallRay`: along `a − (λ/t)u`, `u·m → β = sup R_u` and `Var(R_u) → 0`, `G(u,u) → 0` (Bhatia–Davis squeeze). Round-39 remaining: Schur complement C, bounded-feature closed/open LDP, exposed-face lemma (`u·M ≤ β` on K), overview theorem V rewrite + paragraphs in the note. NEXT: note update, then LDP closed sets via the box, then round-40 consult.

**2026-09-25 (LDP bounds):** `LargeDeviationBounds`: closed-set upper bound through the feature box (no exponential tightness needed), open-set lower bound at every tilted mean. Round-39 remaining: Schur complement C, exposed-face lemma, interior approximation for boundary points of open sets. NEXT: slop paragraph, Schur complement, round-40 consult.

**2026-09-25 (Schur complement):** `SchurComplement`: `d⬝G⁻¹d = d_R⬝C⁻¹d_R + (d₀ − b·d_R)²/Var(H)`; the slice inverse-covariance metric is the minimal lift of the full one, attained at the slice tangent. Round-39 bundle A–F COMPLETE (A,B,F ProfileGeometry; C SchurComplement; D,E pre-existing). Also landed: FluctuationResponse, WallRay, LargeDeviationBounds. NEXT: slop paragraphs (LargeDeviationBounds, SchurComplement), round-40 consult.

**2026-09-25 (round 40 + journey energy + temperature compatibility):** consult `research_round40_{q,v1}`: ranking 1 whole-body rate/Cramér (extended rate `⨆ q ofReal(q·M − Λ(q))` in ℝ≥0∞; `= KL(P_a‖P_0)` at interior means via the landed Legendre identity; `= ⊤` off K by separation; convex/lsc; radial approximation; eventual-exponential Cramér; exposed-face entropy cost `𝓘(M) = −log p_F + 𝓘_F(M)`; blow-up criterion; conditional convergence of the wall ray), 2 temperature compatibility (DONE: `TemperatureCompatibility`, `∂_t² I_t(M) = −Var(H) < 0`), 3 dual connections (`a'' = (1/t)V⁻¹C(w,w)` on the m-journey), 4 equal energy (DONE: `JourneyEnergy`), 5 full-geometry stability. Structural consolidation pass requested (7-section catalogue + dependency table). NEXT: the rate-function module (RateFunction: definition, interior identification, ⊤ off K, convexity/lsc), then the note catalogue.

**2026-09-25 (rate function):** `RateFunction`: extended rate `𝓘 = ⨆ q ofReal(q·M − Λ(q))`; `𝓘(m_t a) = KL(P_a‖P_0)`; `𝓘 = ⊤` off the moment body; lsc. Round-40 bundle A/B DONE (attainment B.4 = `range_meanMap_slice`, landed earlier). Remaining of the bundle: C radial interior approximation, D full Cramér in eventual-exponential form, E exposed-face entropy cost, F blow-up criterion, G conditional convergence of the wall ray. NEXT: note catalogue (structural pass), then C/D.

**2026-09-25 (Cramér):** `CramerTheorem`: eventual-exponential Cramér for `Q = P_{t,0}` — closed-set upper bound (`c < 𝓘` on `F`), open-set lower bound (`𝓘(M) < c`, `M ∈ G`) with radial interior approximation. Round-40 bundle A–D DONE. Remaining: E exposed-face entropy cost (`𝓘(M) = −log p_F + 𝓘_F(M)`), F blow-up criterion, G conditional convergence of the wall ray; dual connections (item 3). NEXT: slop paragraph + note catalogue, then round-41 consult.

**2026-09-25 (exposed faces):** `ExposedFace`: on a positive-mass exposed face `{u·M = β}`, `𝓘(M) = −log p_F + 𝓘_F(M)` with `𝓘_F` the rate of the conditional law `Q(·|F)` — the boundary inherits a lower-dimensional rate geometry with an entry cost. Round-40 bundle A–E DONE. Remaining: F blow-up criterion (`𝓘 → ∞` towards the boundary iff every proper exposed face is null), G conditional convergence (largely `FaceLimit`), dual connections. NEXT: slop paragraph, round-41 consult.

**2026-09-25 (round 41 + null faces):** consult `research_round41_{q,v1}`: audit OK (face identity holds on the whole hyperplane, `K_F ⊊ K ∩ H` possible; eventual-exponential Cramér equivalent to liminf/limsup with `log 0 = −∞`; radial constants right). Ranking: 1 boundary-barrier criterion F (F1 null face ⇒ ⊤ on hyperplane DONE; F2 positive face ⇒ `𝓘(M_F) = −log p` DONE; F3 supporting hyperplane at each boundary point via `geometric_hahn_banach_open_point`; F4 uniform blow-up from lsc + compact sublevel sets — NO sphere compactness needed), 2 conditional response charts + entropy-projection `𝓘(M) = inf_{E_ρR=M} KL(ρ‖Q)` and the finite-conditioning completion principle, 3 dual connections (geodesic-equation route: `a'' = tV⁻¹C(a',a')`, no inverse derivative if `a` is C²), 4 G exact TV: `d_TV(ν_λ, ν_F) = 1 − p/Z_λ → 0` (do first, cheap), 5 full-geometry stability, 6 entropy identities (`𝒮(Q_F) = 𝒮(Q) + log p_F` is FALSE in general; `D(Q_F‖Q) = −log p_F`). Landed: `NullFace` (F1, F2). NEXT: `FaceTotalVariation` (G), then F3/F4, then conditional charts.

**2026-09-25 (face total variation):** `FaceTotalVariation`: the wall ray converges in total variation to the face law `Q(·|F)`, with the exact bound `|P_s(A) − Q_F(A)| ≤ 1 − P_s(F)` and `P_s(F) → 1`. Round-41 items G, F1, F2 DONE. Remaining: F3/F4 (supporting hyperplanes at boundary points; uniform blow-up from lsc + compact sublevels), conditional response charts + entropy projection, dual connections. Slop paragraph for NullFace + FaceTotalVariation pushed (edbed51). NEXT: F3/F4.

**2026-09-25 (boundary barrier):** `BoundaryBarrier`: the moment body is compact; every boundary point has a supporting direction; the rate is `+∞` on the whole boundary iff every supporting face is null (`rateFun_frontier_eq_top_iff`); finite sublevel sets are compact subsets of the interior, so the rate exceeds any threshold within a positive distance of the boundary and tends to `⊤` along any family approaching it. Round-41 item F COMPLETE (F1–F4), G DONE. Remaining round-41: conditional response charts + entropy projection, dual connections, full-geometry stability. NEXT: slop paragraph for BoundaryBarrier, then conditional charts / entropy projection.

**2026-09-25 (entropy projection):** `EntropyProjection`: `𝓔(M) = inf {KL(ρ‖Q) : E_ρ R = M}` (Mathlib `klDiv`); Donsker–Varadhan gives `𝓘 ≤ 𝓔` everywhere; `P_{t,a} = Q.tilted(−t a·R)` and `KL(P_a‖Q) = famKL a 0`; on the response space `𝓔 = 𝓘` with the family member as unique minimiser (Pythagoras `KL(ρ‖Q) = KL(ρ‖P_a) + KL(P_a‖Q)`); `KL(Q_F‖Q) = −log Q(F)` and the identity holds at conditional means of positive faces. Round-41: F, G, entropy projection (interior + positive faces) DONE. Remaining: conditional response charts (intrinsic chart on a positive face + `𝓘_Q = −log Q(F) + 𝓘_{Q_F}` already as `rateFun_face_eq`; telescoping entry costs), dual connections, full-geometry stability, completion principle (finite sequence of conditionings reaches every finite-rate mean). NEXT: slop paragraph for EntropyProjection, then round-42 consult.

**2026-09-25 (thermal transport):** `ThermalTransport`: master transport law `d/ds E_{ν_s} g = Cov_{ν_s}(g,f)` and `d/ds KL(ν_s‖ν) = s Var_s(f)` for Mathlib tilts; the family is the tilt of the prior `P_{0,0}` by `−t H_a`; `KL(P_{t,a}‖π̄) = −𝒮(t,a) = ∫₀ᵗ s Var_{s,a}(H_a) ds` with derivative `t Var_{t,a}(H_a)`; `∂_t 𝓘_t(M) = E_{t,θ_t(M)} L₀ − E_{Q_t} L₀` (also for entropyProj). Round-42 item 1 DONE. Remaining round-42: 2 intrinsic conditional charts (relint moment-body theorem for a general law), 3 finite-rate completion by induction on affine dimension, 4 joint-body thermal compactification (t → ∞ ground-state entry cost), 5 stratified stability, 6 dual connections. NEXT: slop paragraph, then item 4 (ground-state limit, reuses FaceTotalVariation on the scalar statistic H_a) or item 2.

**2026-09-25 (ground state):** `GroundState`: zero-temperature endpoint at fixed `a` — energy relaxes to the essential infimum, positive-mass ground state gives TV convergence `P_{t,a} → π̄(·|G)` with the exact bound, and `KL(P_{t,a}‖π̄) → −log π̄(G) = KL(π̄_G‖π̄)`. Round-42 item 4 COMPLETE: null ground state ⇒ `KL → +∞` (`tendsto_klDiv_prior_temp_null`, via the tangent bound `affLogZ_tangent_temp` and monotonicity). Remaining: item 2 intrinsic charts (relint moment-body theorem for a general law), item 3 completion, 5 stability, 6 dual connections. NEXT: item 2 / item 3 (they need the relative-interior chart), or round-43 consult.

**2026-09-25 (relative interior):** `RelativeInterior` (ball and supporting-functional characterisations of `intrinsicInterior`) and `RelativeMomentBody` (`range meanMap = intrinsicInterior K` with NO nondegeneracy hypothesis — the intrinsic response chart). Round-42 item 2 core DONE. Remaining for the completion (item 3): conditional family on a positive face as `familyMeasure (μ.restrict F)` (bridge `= P(·|F)`), relative supporting hyperplanes at frontier-of-relint points, dimension drop, induction on `finrank (dirSpan)`. NEXT: slop paragraph; then item 3.

**2026-09-25 (completion principle):** `ConditioningChainRule` + `EntropyCompletion`: every response of finite rate has a UNIQUE entropy minimiser (strong induction on the affine dimension of the moment body; interior = family member, boundary = positive-mass exposed conditioning + induction), and `entropyProj ν S M = genRate ν S M` for every `M`. Round-42 items 1–4 DONE. Remaining: 5 stratified stability, 6 dual connections; conditioning certificate (explicit chain of events, length ≤ dim) as a strengthening; Pythagoras at boundary points. NEXT: slop paragraph, then round-43 consult.

**2026-09-25 (data-to-response map):** round-43 consult saved (`gpt_responses/research_round43_v1.md`; ranking: 1 data-to-response map + information decomposition, 2 global intrinsic chart Equiv + quantitative stability, 3 explicit conditioning certificate (indexed inductive `ExposedChain ν S A n`), 4 mixture bridge to arbitrary finite-entropy data, 5 conditional-chart compatibility, 6 cubic tensor). `DataResponseMap`: `responseProjection`, `KL(D‖ν) = 𝓘(E_D S) + KL(D‖Π)`, relint means for equivalent laws / tilts, the tilt path's derivative and integrated information, and Π_ν = Π_{ν_F} on positive faces. Item 1 core + item 5 DONE. NEXT: slop paragraph; then item 3 (certificate) or item 2 (global chart + stability).

**2026-09-25 (certificate):** `IntrinsicChart` (𝕍 ≃ relint K) and `ConditioningCertificate` (indexed inductive `ExposedChain`, depth bound `n + dim 𝕍_{ν_A} ≤ dim 𝕍_ν`, telescoped entry cost `−log ν(A)`, `exists_exposedChain`, `Π_ν(M) = tilt of ν_A`). Round-43 items 1, 2 (chart part), 3, 5 DONE. Remaining: quantitative stability on 𝕍 (item 2b), mixture bridge (item 4), cubic tensor (item 6); the chart's differentiability/inverse-function structure on 𝕍. NEXT: slop paragraph; then round-44 consult or item 4.

**2026-09-25 (mixture bridge):** `MixtureBridge`: convexity of Mathlib's `klDiv` in the first argument (new, from `convexOn_klFun`), rate convex/monotone along the straight mean path from the featureless response, the path in the intrinsic chart for `s < 1`, and `𝓘(M_s) → 𝓘(M_D)` at the endpoint. Round-43 items 1, 2a, 3, 4 (minus TV/Pinsker), 5 DONE. Remaining: 2b quantitative stability on 𝕍, 6 cubic tensor, Pinsker for the TV convergence. NEXT: slop paragraph; round-44 consult.

**2026-09-25 (endpoint convergence, round 44):** consult `gpt_responses/research_round44_v1.md` (ranking: 1 endpoint KL certificate + zero-rate, 2 C¹ intrinsic Legendre chart on 𝕍 (Fréchet derivative = covariance, inverse via `HasStrictFDerivAt.toPartialHomeomorph`), 3 differential of the data→response map (`θ'(s) = C⁻¹ Cov_{D_s}(S,h)`, basepoint second derivative `⟨b, C₀⁻¹ b⟩ ≤ Var h`, residual variance), 4 quantitative susceptibility (`𝓘(M) ≥ ‖M − m₀‖²/(2L)` under a uniform tilted-covariance bound; local inverse stability), 5 Bregman packaging `KL(P_θ‖P_η) = A(η) − A(θ) − ⟨∇A(θ), η−θ⟩` (`famKL`), 6 cubic tensor). `EndpointConvergence` DONE: `klDiv_tilted_right_eq`, `genRate_eq_zero_iff`, `responseProjection_eq_tilted`, `klDiv_responseProjection_segment_le`, `tendsto_klDiv_responseProjection_segment`. NEXT: slop paragraph; then item 5 (Bregman, quick from `klDiv_tilted_right_eq`), item 3 basepoint theorem, item 2 chart derivative on 𝕍.

**2026-09-26 (response susceptibility):** `ResponseSusceptibility`: envelope identity, intrinsic gradient of the rate = natural coordinate (`hasFDerivAt_genRate_chart`), data path `D_s = ν.tilted (s h)` in chart coordinates with `θ'(s) = (Dm|_𝕍)⁻¹ Cov_{D_s}(S,h)` and `d/ds 𝓘(M(s)) = −⟨θ(M(s)), Cov_{D_s}(S,h)⟩`. Round-44 item 3 first half DONE. NEXT: slop paragraph; basepoint theorem (second derivative at `s = 0`: `⟨b, C₀⁻¹ b⟩ ≤ Var_ν h`, residual variance identity); then item 4 (quadratic information bound), item 6 (cubic tensor).

**2026-09-26 (basepoint curvature):** `BasepointCurvature`: at the featureless law the visible information along `D_s = ν.tilted (s h)` has zero velocity and second derivative `Var_ν(regressor)`, `regressor = ⟨−θ'(0), S⟩` the regression of `h` on the visible statistics (regression identity `Cov(⟨e,S⟩, g) = Cov(⟨e,S⟩, h)`), with `Var g ≤ Var h` and gap `Var(h − g)` (the invisible information). Round-44 item 3 DONE. NEXT: slop paragraph; item 4 (quadratic information bound `𝓘(M) ≥ ‖M − m₀‖²/(2L)` under a uniform tilted-covariance bound + local inverse stability), item 6 (cubic tensor); then round-45 consult.

**2026-09-26 (quadratic information bound):** `QuadraticInformationBound`: `𝓘_ν(M) ≥ ‖M − m₀‖²/(2B²)` for all `M` when `‖S − m₀‖ ≤ B` a.s. (second-order CGF bound along rays, Cauchy–Schwarz variance bound under every tilt). Round-44 items 1–5 DONE (4 without the local inverse stability constant). NEXT: slop paragraph; item 6 (cubic tensor: `d/ds Var_{sf} f = κ₃` along rays, `D³A` as the third central moment), then round-45 consult.

**2026-09-26 (cubic response):** `CubicResponse`: `d/ds Cov_{ν_{sf}}(g,k) = E_{ν_{sf}}[(g−Eg)(k−Ek)(f−Ef)]` (the cubic tensor `D³A[u,v,w]` as the third central mixed moment; variance moves by `κ₃`; along the data path the susceptibility entries move by `thirdCentral D_s (S i) (S j) h`). Round-44 items 1–6 DONE. NEXT: slop paragraph; round-45 consult (what remains: Pinsker/TV, local inverse stability constant, connections/curvature packaging, and the user's "map the space of responses across the data manifold" — candidate: the full path from maximal-entropy to data in one theorem statement: information decomposition + endpoint + quadratic bound assembled).

**2026-09-26 (invisible information):** `InvisibleInformation`: the invisible remainder `KL(D_s‖Π(M(s)))` along the data path has derivative `s Var_{D_s} h + ⟨θ(s), Cov_{D_s}(S,h)⟩`, zero velocity at the featureless law and curvature `Var_ν(h − regressor)` there. Round-44 fully closed. NEXT: round-45 consult.

**2026-09-26 (round 45, item 3):** consult `research_round45_v1.md` (order 1→2→3→5→4→6). `ResponsePathDifferential` DONE: the differential of the response map along ANY differentiable response path (`θ' = (Dm|𝕍)⁻¹ M'`, `d/ds 𝓘 = −⟨θ, M'⟩`) and of every bounded observable (`d/ds E_{Π(M s)} φ = −Cov(φ, ⟨θ', S⟩)`). NEXT: slop paragraph; item 1 (atlas package on the straight path `m₀ + sΔ`, instance of item 3), item 4 (Fisher budget: second derivative along the straight path `⟨Δ, C⁻¹Δ⟩` from `hasDerivAt_responseTheta_path`, Taylor with integral remainder, endpoint by monotone convergence), item 2 (Hessian/stability), item 5 (Pinsker), item 6.

**2026-09-26 (atlas + Fisher budget):** `ChartContinuity` (chart derivative and susceptibility continuous in θ) and `StraightPathAtlas` (round-45 items 1 and the visible half of 4): straight path `M_s` in the relint for s<1, `θ_s` C¹ with velocity `(Dm|𝕍)⁻¹Δ`, `d/ds 𝓘(M_s) = −⟨θ_s,Δ⟩`, curvature = variance of the dual velocity contrast ≥ 0 and continuous, integrated Fisher budget `𝓘(M_r) = ∫₀ʳ (r−s) κ(s) ds` and `→ 𝓘(M)` as r↑1, information decomposition along the mixture bridge. NEXT: slop paragraph; round-45 item 2 (Hessian `D²𝓘 = C⁻¹` packaging + inverse stability `κ_r = e^{−2Br}λ₀`), item 5 (Pinsker via `klDiv_map_le` + binary KL), item 6 (strict-convexity gap identity), data-side Fisher budget `KL(D‖ν) = ∫₀¹ (1−s)𝓕_data(s) ds`.

**2026-09-26 (Pinsker for events):** `PinskerEvent`: Hoeffding-form CGF bound, `2(μA − ηA)² ≤ KL(μ‖η)`, and along the straight bridge `2(Π(M)A − Π(M_s)A)² ≤ 𝓘(M) − 𝓘(M_s)` with `Π(M_s)(A) → Π(M)(A)` as s↑1 for every event. Round-45 items 1, 3, 4 (visible half), 5 (event form) DONE. NEXT: slop paragraph; item 2 (Hessian packaging `D²𝓘 = C⁻¹` + inverse stability constant), item 6 (strict-convexity gap identity), data-side Fisher budget; the bounded-observable form of Pinsker needs a TV-as-sup API.

**2026-09-26 (dual Fisher metric):** `DualFisherMetric`: gradient of the rate = −θ(v) eventually, Hessian `D_v[∇𝓘(w)][u] = Cov_{θ}(⟨u',S⟩,⟨w',S⟩)` (`u' = (Dm|𝕍)⁻¹u`), symmetric, positive definite on 𝕍. Round-45: 1 ✓, 2 (Hessian ✓, stability constant open), 3 ✓, 4 (visible ✓, data-side open), 5 (event ✓, observable form open), 6 open. NEXT: slop paragraph; data-side Fisher budget `KL(D‖ν) = ∫₀¹ (1−s) ∫ (f−1)²/(1−s+sf) dν ds` (scalar identity `x log x − x + 1 = ∫₀¹ (1−s)(x−1)²/(1−s+sx) ds` + Tonelli); inverse stability constant; item 6 gap identity.

**2026-09-26 (data-side Fisher budget):** `DataFisherBudget`: `KL(D‖ν) = ∫₀¹ (1−s) 𝓕_data(s) ds` in ℝ≥0∞ (scalar KL-integrand identity + Tonelli). Round-45: 1 ✓, 2 (Hessian ✓ / stability constant open), 3 ✓, 4 ✓ (both halves), 5 (event ✓ / observable form open), 6 open. NEXT: slop paragraph; inverse-stability constant `κ_r = e^{−2Br}λ₀` (density bound of `P_θ`, variance comparison, coercivity on the unit sphere, segment integration); item 6 strict-convexity gap identity; then round-46 consult.

**2026-09-26 (observable Pinsker):** `PinskerObservable`: `(E_μF − E_ηF)² ≤ 2L² KL(μ‖η)` for `|F−c| ≤ L`; along the bridge every bounded posterior expectation converges at the endpoint with the information gap as modulus. Round-45: 1 ✓ 2 (Hessian ✓, stability constant open) 3 ✓ 4 ✓ 5 ✓ 6 open. NEXT: slop paragraph; round-46 consult (remaining: inverse-stability constant, convexity-gap identity, connections packaging).

**2026-09-26 (round 46):** consult `research_round46_v1.md` (verdict: the atlas is defensible; capstone = complete information budget). `ProjectionPythagoras` DONE (Pythagoras relative to every family member). NEXT: slop paragraph; `InformationBudget`: (i) `affLogZ ν 1 0 S 1 θ = featCgf ν S (−θ)`, (ii) `(1−r)·(−⟨θ_r,Δ⟩) ≤ 𝓘(M) − 𝓘(M_r)` via `le_iSup` at `q = −θ_r`, (iii) `genRate M = ∫⁻ s in Ioo 0 1, ofReal((1−s)κ s)` by `lintegral_iSup` on indicators of `Ioo 0 r_n` with `ofReal_integral_eq_lintegral_ofReal`, `intervalIntegral.integral_of_le`, `Ioo_ae_eq_Ioc`, `le_of_tendsto`, (iv) real forms and `KL(D‖Π(M_D)).toReal = ∫ (1−s)(𝓕_D(s).toReal − κ(s))` for finite `KL(D‖ν)`; then inverse stability, parameter escape, gap identity.

**2026-09-26 (visible budget over the whole bridge):** `VisibleBudget`: `𝓘(M) = ∫₀¹ (1−s) κ(s) ds` (ℝ≥0∞ and Bochner over `Ioo 0 1`), via the convexity gap `(1−r)(−⟨θ_r,Δ⟩) ≤ 𝓘(M) − 𝓘(M_r)` and monotone convergence. NEXT: slop paragraph; `InformationBudget` (invisible = difference of the two budgets for finite `KL(D‖ν)`: Ioc→Ioo via `setLIntegral_congr Ioo_ae_eq_Ioc`, `ae_lt_top'` for a.e. finiteness of `dataFisher`, `Measurable.lintegral_prod_right'`, `integral_sub`); then inverse stability, parameter escape, gap identity.

**2026-09-26 (capstone):** `InformationBudget`: `KL(D‖Π(M_D)) = ∫₀¹ (1−s)[𝓕_D(s) − κ(s)] ds` for finite `KL(D‖ν)` — the complete information budget (total = data Fisher budget, visible = dual-Fisher budget, invisible = difference). Round-46 items 1 ✓ 2 ✓ (Pythagoras; metric packaging as prose). NEXT: slop paragraph; then round-46 items 3 (inverse stability constant `κ_r = e^{−2Br}λ₀`: names `isCompact_sphere`, `IsCompact.exists_isMinOn`, `integral_tilted`), 4 (parameter escape `‖θ(M_s)‖ → ∞` at boundary responses), 5 (gap identity), 6 (C^∞).

**2026-09-26 (tilt density bounds):** `TiltDensityBounds`: `E_{P_θ} φ ≥ e^{−2Br} E_ν φ`, `Var_{P_θ} g ≥ e^{−2Br} Var_ν g` on `⟨θ,θ⟩ ≤ r²`. NEXT: `InverseStability` (λ₀ via `isCompact_sphere`/`IsCompact.exists_isMinOn` on the quadratic form `u ↦ −⟨u, chartDeriv 0 u⟩`, homogeneity; convexity of the `dotJ`-ball; segment integration of `t ↦ ⟨θ−η, m(η+t(θ−η))⟩` with `dotJ_meanMapDeriv`; conclude `κ_r² ⟨θ−η,θ−η⟩ ≤ ⟨mη−mθ, mη−mθ⟩`); then slop paragraph for item 3; then round-46 items 4–6.

**2026-09-26 (inverse stability):** `InverseStability`: coercivity `λ₀` of the reference covariance on `𝕍`, `Var_{P_θ}⟨u,S⟩ ≥ e^{−2Br}λ₀⟨u,u⟩` on the ball, strong monotonicity of the mean map and the Lipschitz bound `κ_r²⟨θ−η,θ−η⟩ ≤ ⟨mθ−mη,mθ−mη⟩`, `κ_r = e^{−2Br}λ₀`. Round-46 items 1–3 DONE. NEXT: item 4 (parameter escape at boundary responses), item 5 (gap identity), item 6 (smoothness); round-47 consult afterwards.

**2026-09-26 (mixture compensation):** `MixtureCompensation`: `a KL(P₀‖ν) + b KL(P₁‖ν) = KL(Q‖ν) + a KL(P₀‖Q) + b KL(P₁‖Q)` unconditionally in `ℝ≥0∞`; gap identity for the rate and STRICT CONVEXITY of `𝓘` on its whole finite domain (boundary strata included). Round-46 items 1–3, 5 DONE. NEXT: item 4 (parameter escape at boundary responses, normal-cone accumulation), item 6 (smoothness), round-47 consult.

**2026-09-26 (boundary escape):** `BoundaryEscape`: `‖θ(M_s)‖ → ∞` as `s ↑ 1` for finite-rate boundary responses (compactness + chart image = relative interior). Round-46 items 1–5 DONE (item 4 robust part; directional/normal-cone refinement and fixed-normal conditioning limit open). NEXT: item 4 refinement (normal cone), item 6 (smoothness), round-47 consult.

**2026-09-26 (normal cone):** `NormalCone`: escape directions are inward normals — `‖θ_n‖ → ∞`, `m(θ_n) → M`, `θ_n/‖θ_n‖ → u` ⟹ `⟨u, x − M⟩ ≥ 0` on the moment body (Laplace-principle bound from `KL(P_θ‖ν) ≥ 0`); atlas instance for `θ(M_s)/‖θ(M_s)‖`. Round-46 items 1–5 DONE incl. the directional refinement of 4 (fixed-normal conditioning limit still open). NEXT: item 6 (smoothness) or round-47 consult.

**2026-09-26 (fixed-normal limit, round 47):** consult `gpt_responses/research_round47_{q,v1}.md` (verdict: exhaustion by exposed chains — already landed as `exists_exposedChain`/`ExposedChain.genRate_eq`; missing piece was the fixed-normal conditioning limit). `FixedNormalLimit`: conditioning commutes with tilting; `P_{η−ta}(·|F) = Q`; `p_t → 1`; events, bounded observables converge; `KL(Q‖P_{η−ta}) = −log p_t → 0`. NEXT (Astra round-47 ranking): interior endpoint rates `KL(Π(M)‖Π(M_s)) = ∫_s^1 (1−u) g'' ≤ ‖Δ‖²(1−s)²/(2κ_r)` (item 4), variational Fisher metric `inf E h² = ⟨Ṁ, C⁻¹Ṁ⟩` (item 5), second-order observable transport (item 2), residual-information split `KL(D‖P) = KL(D‖D↑) + KL(S_*D‖S_*P)` (item 3A), Legendre closure (item 6).

**2026-09-26 (endpoint tail):** `EndpointTail`: exact `KL(Π(M)‖Π(M_s)) = 𝓘(M) − 𝓘(M_s) − (1−s)𝓘'(s) = ∫_s^1 (1−u)κ(u) du` for every finite-rate M; `κ ≤ ‖Δ‖²/κ_r` on balls; `KL ≤ ‖Δ‖²(1−s)²/(2κ_r)`. Round-47 items 1A, 4 DONE. NEXT: variational Fisher (5), second-order observable transport (2), residual-information split (3A), Legendre closure (6).

**2026-09-26 (variational Fisher):** `FisherVariational`: the dual Fisher metric `⟨Ṁ, C⁻¹Ṁ⟩ = Var⟨C⁻¹Ṁ,S⟩` is the minimal Fisher cost `inf E h²` over score perturbations producing `Ṁ`, attained by the centred score; the atlas curvature `κ(s)` is the minimal cost of the velocity `Δ`. Round-47 items 1A, 4, 5 DONE. NEXT: second-order observable transport (2), residual-information split (3A), Legendre closure (6).

**2026-09-26 (Legendre closure):** `LegendreClosure`: `Λ(q) = max_{𝓘(M)<∞} [⟨q,M⟩ − 𝓘(M)]`, attained exactly at `m(−q)` (uniqueness from strict convexity). Round-47 items 1A, 4, 5, 6 DONE. NEXT: second-order observable transport (2; needs the derivative of the inverse covariance along the path, i.e. `D_θ C_θ = −T`), residual-information split (3A), or round-48 consult.

**2026-09-26 (observable curvature, round 48):** consult `gpt_responses/research_round48_{q,v1}.md`. `ObservableCurvature`: first- and second-order transport of any bounded observable along the atlas, `F''(s₀) = T_{P_{s₀}}(r₀,⟨v,S⟩,⟨v,S⟩)` by freezing the regression residual (no inverse differentiation); canonical regression coefficient from the chart. Round-47 items 1A, 2, 4, 5, 6 DONE. NEXT (Astra round-48): residual-information split via the statistic lift `D↑ = ν.withDensity (d(S_*D)/d(S_*ν) ∘ S)` — measure identities (`S_*D↑ = S_*D`, `D ≪ D↑`), base split `KL(D‖ν) = KL(D‖D↑) + KL(S_*D‖S_*ν)`, bounded-tilt split by subtraction, lift = unique least-informative realisation, tower law for nested statistics; then Pinsker/entropy corollaries.

**2026-09-26 (statistic lift):** `StatisticLift`: `D↑ = ν.withDensity (d(S_*D)/d(S_*ν) ∘ S)`, `S_*D↑ = S_*D`, `D ≪ D↑`, base split `KL(D‖ν) = KL(D‖D↑) + KL(S_*D‖S_*ν)`, `KL(D↑‖ν) = KL(S_*D‖S_*ν)`, lift = unique least-informative realisation of the statistic law, residual split `KL(D‖ν.tilted(f∘S)) = KL(D‖D↑) + KL(S_*D‖S_*P)` for bounded `f`. Round-48 items 1, 2, 5A DONE. NEXT: apply the residual split to `Π_ν(M_D)` (a bounded tilt by a function of `S`: `responseProjection_eq_tilted` gives the tilt with `f = −⟨θ,·⟩`, so `KL(D‖Π(M_D)) = KL(D‖D↑) + KL(S_*D‖S_*Π(M_D))`), the tower law for nested statistics (5B), the general-density extension, then round-49 consult.

**2026-09-26 (residual information):** `ResidualInformation`: invisible information of the atlas = fibre part `KL(D‖D↑)` + marginal part `KL(S_*D‖S_*Π(M_D))` (relint case); information tower for nested statistics. Round-48 items 1, 2, 5A, 5B DONE. NEXT: general-density extension (boundary responses: Π(M_D) is a tilt of a conditioned law, density still a function of S), Pinsker/entropy corollaries, round-49 consult.

**2026-09-26 (general residual split):** `GeneralResidualSplit`: residual split for any density that is a function of `S` (unbounded allowed); every finite-rate projection is `ν.withDensity (g ∘ statPoint S)` via the exposed chain; invisible information = fibre + marginal for EVERY finite-information data law. Round-48 ranking fully landed (items 1, 2, general extension, 5A, 5B). NEXT: round-49 consult (re-rank: Pinsker/entropy corollaries, Fisher tangent/fibre L² packaging, differential-geometric packaging, or new directions).

**2026-09-26 (bridge residual, round 49):** consult `gpt_responses/research_round49_{q,v1}.md` (ranking: 1 bridge residual/affine lift, 2 nested Fisher projections in L², 3 second-order expansions of fibre/marginal/total residual along tilt paths, 4 conditional variational formula for fibre information (`dD↑/dν = E_ν[dD/dν | σ(S)]`), 5 empirical projection consistency, 6 dual affine coordinates). `BridgeResidual`: log bound for dominated laws, entropy moduli `bH − h₂ ≤ KL(D_s‖ν) ≤ bH`, affine lift `(aν+bD)↑ = aν + bD↑`, fibre moduli `bL₁ − h₂ ≤ L_s ≤ bL₁ + h₂`, total-residual modulus. NEXT: joint convexity of KL (perspective inequality for `klFun`) to remove the `h₂` slack and get convexity of `L_s`; then items 2–4.

**2026-09-26 (joint convexity):** `KLJointConvexity`: joint convexity of KL (perspective inequality for `klFun`, no integrability), `L_s ≤ b L₁` without slack. NEXT (round-49 ranking): convexity of `s ↦ L_s` as a function (needs `D_s = (1−s/t)ν + (s/t)D_t` re-mixing — cheap corollary), then nested Fisher projections in L² (item 2), second-order expansions of fibre/marginal/total residual along tilt paths (item 3), conditional variational formula for the fibre information (item 4), empirical projection consistency (item 5).

## 2026-09-26 (cont.): LiftConditional + EmpiricalProjection landed

- `LiftConditional.lean`: `rnDeriv_statisticLift_eq_condLExp` (the lifted density is `ν⁻[dD/dν | σ(S)]`),
  `bridge_remix`, `fibreInformation_bridge_le_remix` (convexity of `s ↦ L_s` in re-mixed form).
- `EmpiricalProjection.lean`: interior divergence identity `KL(Π(M)‖Π(M')) = 𝓘(M) − 𝓘(M') + ⟨θ(M'), M − M'⟩`,
  `sampleResponse`, SLLN for the empirical response, a.s. membership in the moment body, eventual relint
  membership, and the consistency theorem `ae_tendsto_klDiv_responseProjection_sampleResponse`.
- Gotchas: `Pairwise ((· ⟂ᵢ[P] ·) on X)` needs `open Function` for `on` — write `Pairwise fun i k ↦ IndepFun …`
  instead; `empMean` already exists in `HalfspaceChernoff` (named ours `sampleResponse`); `continuous_dotJ_right`
  exists in `EssentialRange`; `ENNReal.toReal_ofReal_eq_max` does not exist — get the sign from
  `featCgf_eq_dotJ_sub_genRate_meanMap` instead; `ae_statPoint_mem_essRange` carries `[Fintype J]` in its type
  (use `set_option linter.unusedFintypeInType false in` on consumers whose type doesn't need it).
- NEXT (round-49 ranking): nested Fisher projections in L² (item 2), second-order expansions of fibre/marginal/total
  residual along tilt paths (item 3), conditional variational formula for the fibre information (item 4: sup over
  bounded σ(S)-measurable tests), then a round-50 consult on the "featureless → data" mapping programme.

## 2026-09-26 (cont.): round-50 consult (`gpt_responses/research_round50_{q,v1}.md`), TargetPythagoras + PathEnergy landed

- Astra's round-50 ranking (deepest formulation = "retraction onto the exponential family with exact information defect
  and infinitesimal orthogonal decomposition"): 1 nested Fisher projections in L² (three-way Pythagoras
  `‖h‖² = ‖Bh‖² + ‖(C−B)h‖² + ‖(I−C)h‖²`, minimum-energy response lift); 2 Pythagoras against an arbitrary
  reconstructed target (DONE: `TargetPythagoras`); 3 exact observable defect
  `Δ_φ(s) = s E_D(φ−ψ) + (E_{D_s}ψ − E_{Q_s}ψ)`, `ψ = E_ν[φ|σ(S)]`, and `Δ'_φ`; 4 quadratic splitting of
  `KL`, `𝓘`, `L`, `R` along bounded tilts; 5 equal Fisher energies (exponential path DONE: `PathEnergy`; mean path
  needs continuity of `atlasTheta` at `s = 1`); 6 mixed response Hessian via the frozen residual; 7 finite-rate
  boundary completion of the curvature integral; 8 `L¹`-valued derivative of the reconstruction density.
- Astra's consistency note: `κ(s) = Var_{Q_s}⟨Σ⁻¹v, S⟩` (natural-parameter velocity), which is what `atlasCurv`
  already is (`atlasCurv_eq_priorCov` with `atlasVel`); only the consult's prose summary was sloppy.
- NEXT: item 3 (observable defect: needs `∫ φ g dν = ∫ E_ν[φ|σ(S)] g dν` for bounded σ(S)-measurable `g` —
  `condExp` + `integral_condExp`/`condExp_mul_of_stronglyMeasurable_left`), then item 1 (L² spine), item 4.
- `ObservableDefect` landed (round-50 item 3). Gotchas: `Measurable[m] f` works with `comap_measurable`,
  `.const_mul/.exp/.div_const/.stronglyMeasurable`; `ae_bdd_condExp_of_ae_bdd` is deprecated for
  `ae_bdd_abs_condExp_of_ae_bdd_abs` (real bound, no `ℝ≥0`); `Integrable.of_bound` needs `[IsFiniteMeasure D]`;
  a `def` of type `MeasurableSpace X` trips `warn.classDefReducibility` (disable per-def). NEXT: item 1 (L² spine:
  nested Fisher projections), item 4 (quadratic splitting), item 5 mean-path half (continuity of `atlasTheta` at 1).
- `NestedProjections` landed (round-50 item 1, abstract half). Gotchas: `Submodule.complete_of_finiteDimensional`
  returns `IsComplete ↑s` (use `.completeSpace_coe`); `Submodule.starProjection_apply U v` explicit to rewrite one
  occurrence; `condExpL2 E 𝕜 hm` is definitionally `(lpMeas …).orthogonalProjectionOnto` (instances via
  `Fact (m ≤ m0)`). NEXT: identify `B h` for `h = toLp φ` with the regression `E φ + ⟨a, S − M⟩` (normal equations,
  `eq_starProjection_of_mem_of_inner_eq_zero`), `‖Bh − Eh‖² = Var⟨a,S⟩ = g_M(u,u)`, and the minimum-energy
  characterisation of `ℓ_{M,u}`; then item 4 (quadratic splitting along bounded tilts).
- `RegressionProjection` landed (item 1 complete: B = regression, `‖Bφ − Eφ‖² = ⟨a, Cov(S,φ)⟩`). Gotcha: expand
  `⟪u, A + B − C⟫` with `inner_sub_right` BEFORE `inner_add_right` (top symbol is the subtraction). NEXT: item 4
  (quadratic splitting of KL/𝓘/L/R along bounded tilts, `KL(D_t‖ν) = t²/2 ‖h‖² + o(t²)` etc.), then item 5 mean-path
  half, item 6 mixed Hessian, item 7 boundary completion.
- `AtlasEnergy` landed (item 5 complete: equal Fisher energies; `KL(ν‖Π(M)) = ∫ s κ`). Gotchas: `Ioo_mem_nhdsLT h`
  is a filter membership — ascribe it as `∀ᶠ s in 𝓝[<] 1, s ∈ Ioo 0 1` before `.and`/`.exists`; `hasDerivAt_id'
  (x := 1)` elaborates `1 : ℕ` — write `(x := (1 : ℝ))`; `((s • ⟨_, h⟩ : 𝕍) : J → ℝ)` elaborates as `s • ↑⟨_,h⟩`
  (smul outside), reconcile with `Submodule.coe_smul`; `rw [← hf] at this` fails on beta-reduced statements — `rw [hf]`
  in the goal and `exact`. NEXT: item 4 (quadratic splitting along bounded tilts), item 6 (mixed Hessian), round-49
  item 4 (conditional variational formula), round-51 consult.
- `TiltQuadratic` + `TiltRateQuadratic` landed (item 4: `KL(ν_t‖ν)/t² → Var f/2`, `𝓘(M_t)/t² → ⟨a,u⟩/2`; hence
  `(L+R)(ν_t)/t² → ½‖(I − B₀)(f − Ef)‖²` is a short corollary via Pythagoras — TODO state it, plus the individual
  `L`/`R` expansions which need the condExp of the tilt density). Gotchas: `hasDerivAt_pi` lives in
  `Analysis/Calculus/Deriv/Prod.lean`; `HasStrictFDerivAt.exists_lipschitzOnWith` gives `∃ K, ∃ s ∈ 𝓝 x, …`;
  `conv_lhs => rw [← h0]` to rewrite the argument `0` but not the RHS `0`; Lipschitz→`IsBigO.of_bound K` then
  `.trans (hM.isBigO_sub)`; `IsLittleO.congr_right (fun t ↦ by ring)` to turn `t * t` into `t ^ 2`; omits cascade —
  drop `[Nonempty J]` from a section's `variable` line instead of omitting it on every theorem.

## Round 51 (`gpt_responses/research_round51_{q,v1}.md`)

- Astra's ranking: 1–2 compact Chernoff upper bound + tilted lower bound (ALREADY in the seabed: `CramerTheorem.lean`
  `cramer_upper`/`cramer_lower`, `LargeDeviationBounds.open_lower_bound`, `AsymptoticUpperBound`), 3 separate `L`/`R`
  quadratic limits (`p_t = 1 + th + O_{L^∞}(t²)`, condExp preserves the bound, entropy-Taylor lemma), 4 `L¹`-valued
  reconstruction derivative `Dq(m)[u] = q_m ℓ_{m,u}`, 5 conditional variational formula
  `L = sup_g E_D[g − log E_ν(e^g|σ(S))]` (clip `log(d/c)`), 6 coarse-graining towers (atlas refinement needs affine
  feature inclusion: `𝓘_f − 𝓘_c = KL(P_f‖P_c)`; observational refinement `L_G = L_H + KL(D^H‖D^G)`; `R` not monotone),
  7 full-simplex mixture-path identities (DONE: `MixturePathEnergy`).
- Gotchas: Tonelli for real integrals over `(volume.restrict (Ioc 0 1)).prod ν`: `Integrable.of_bound` with the a.e.
  bound obtained from `Measure.prod_restrict` + `ae_restrict_iff'`; `isCompact_Icc (a := c) (b := C)` (named args on
  `isCompact_Icc`, not on `exists_bound_of_continuousOn`); `field_simp` may not clear `1 + s*(r-1)` — use
  `linear_combination k * mul_inv_cancel₀ h` instead; `integral_congr_ae` goals are beta-redexes (`beta_reduce`).
- NEXT: item 3 (needs `‖p_t − 1 − th‖_∞ = O(t²)` and the entropy-Taylor lemma), item 6 (cheap: instances of
  `TargetPythagoras` and `klDiv_statisticLift_tower`), item 5, item 4.
- Round-51 item 3 COMPLETE (`EntropyTaylor`, `LiftDensity`, `LiftQuadratic`): all four quadratic limits
  (`‖h‖²`, `‖B₀h‖²`, fibre `∫(h−g)²`, marginal `∫g² − ⟨a,u⟩`, `g = E_ν[h|σ(S)]`). Gotchas: `Bdd` is an `And`, so
  `Bdd.sub h₁ h₂`, not `h₁.sub h₂`; `Π` is reserved even inside hypothesis names (`hΠne`); `0 ≤ᵐ f` goals show
  `0 x` (add `Pi.zero_apply`); `ae_eq_condLExp hm ν X hY hXY` takes `hm` explicitly; state `hsplit` with the
  `tiltResponse` spelling by type ascription (defeq) before `rw`. NEXT: round-51 items 6 (towers), 5 (conditional
  variational), 4 (`L¹` derivative); L² identification of `∫ g²` with `‖condExpL2 h‖²` (`MemLp.condExpL2_ae_eq_condExp`).
- `AtlasRefinement` landed (round-51 item 6). Remaining from round 51: item 5 (conditional variational formula
  `L = sup_g E_D[g − log E_ν(e^g|σ(S))]`), item 4 (`L¹` derivative of the reconstruction density), then a round-52
  consult. Gotcha: `⟨_, by rw [...]⟩` for an existential witness leaves the metavariable unassigned after `rw` — give
  the witness explicitly.
- Round-52 consult (`gpt_responses/research_round52_{q,v1}.md`; ranking: 1 simultaneous curvature formulas for
  𝓘, L, R; 2 local Fisher-orthogonal retraction theorem; 3 L¹ Fréchet derivative `Dq(m)[u] = q_m ℓ_{m,u}`;
  4 Fisher orthogonality iff Pythagoras; 5 conditional variational formula; 6 observable-defect second order;
  7 mixed Hessian `D²q = q_m(I − C_m − B_m)(ℓ_u ℓ_z)`; 8 reverse divergence/asymmetry; 9 conditional Fisher-loss
  identity; 10 skewness `KL(Q₁‖ν) − KL(ν‖Q₁) = ∫ s(1−s) E ℓ³`; 11 reverse-divergence correction; 12 length–energy).
  `BregmanGeometry` landed (items 4, 8). `CurvatureSplit` landed (item 1): `KL(D_s‖ν) = ∫₀ˢ (s−w) k_d`,
  `L_s = ∫₀ˢ (s−w)(k_d − k_a)`, `R_s = ∫₀ˢ (s−w)(k_a − κ)` with `a = E_ν[d|σ(S)]`, the lift of the bridge being the
  bridge of `a` (`statisticLift_densLaw_bridge`). Gotchas: `omit hc0 in` changes call arity (drop the argument at
  every call site); `Integrable.const_add` does not exist on the `And`; `norm_integral_le_of_norm_le` needs its
  constant bound given (`integrable_const c`); after `rw [meanMap_zero_eq_mean]` `beta_reduce` before `ring`.
  NEXT (round 52): item 3 (L¹ derivative of the reconstruction density along the atlas), item 2 (local retraction),
  item 5 (conditional variational formula), item 6, item 7, item 10 (skewness), item 12.
- `ConditionalFisherLoss` landed (round-52 item 9): `k_d − k_a = ∫ (d−a)²/(d_w a_w²) dν` (conditional variance of the
  mixture score), `k_a ≤ k_d`, `L_s = ∫₀ˢ (s−w) · condVar`, existence of a clamped `σ(S)`-measurable conditional
  density. Gotchas: `field_simp` did not clear `1 + w*(y−1)` even with the `≠ 0` fact in context — use
  `div_sub_div`/`div_eq_div_iff` + `ring`; `positivity` cannot see `0 < (w*z+1)^2` (use `pow_pos`);
  `Measurable.max`/`.min` under `statSigma S` need the constant FIRST when the term is `max c (min C f)`;
  `(measurable_klKernel_uncurry hr).comp (prodMk …)` does not infer `f` — build the measurability by hand.
  NEXT: item 3 (L¹ derivative of the family density: θ-chart `O(‖η‖²)` bound, then `responseTheta` chain rule),
  item 2 (local retraction), item 5 (conditional variational formula), items 6, 7, 10, 12.
- `DensityDerivative` + `ReconstructionDerivative` landed (round-52 item 3): `L¹` derivative of the family density
  `p_θ` in the natural chart (`O(‖η‖²)` remainder, explicit constant `10K²`) and of the reconstruction density
  `q_M = p_{θ(M)}` in response coordinates (`o(‖z‖)`, derivative `q_M(⟨Dθ z, M⟩ − ⟨Dθ z, S⟩)`). Gotchas: clear two
  denominators with `simp only [div_eq_mul_inv]; linear_combination (…) * hZ'inv − (…) * hZinv` rather than
  `field_simp`; `h1.comp 0 h2` needs the base point of `h1` written as `f 0` (`rw [show toV M = toV M + 0 …] at h1`);
  `∀ z, … (M + z)` infers `z : J → ℝ` unless annotated `z : dirSpan …`; `unfold` outer definitions before inner
  ones (`famZ` before `famWeight`); `IsBigO.congr_left h (fun z ↦ …)` then `.trans (hlip.pow 2)`.
  NEXT (round 52): item 2 (local Fisher-orthogonal retraction: `Π(M_{Q_m}) = Q_m` is `responseProjection_mean_familyMeasure`;
  the derivative along tilts `D_t = e^{th}Q_m/Z` gives `(dΠ(M_{D_t})/dQ_m − 1)/t → B_m h` in `L¹(Q_m)` — combine
  `isLittleO_reconstruction_density_remainder` with `hasDerivAt_tiltResponse` and the regression identification),
  item 5 (conditional variational formula), items 6, 7, 10, 12.
- `RetractionDerivative` landed (round-52 item 2): the differential of reconstruction at `Π(M)` along tilts
  `e^{th}Π(M)/Z` is `q_M ⟨a, S − M⟩` with `a` the regression coefficient (`Σ_M a = Cov_{Π(M)}(S,h)`), i.e. the
  `L²(Π(M))` projection of `h` onto the centred features: `∫ |q_{M_t} − q_M − t q_M(⟨a,S⟩ − ⟨a,M⟩)| = o(t)`.
  Gotchas: a `by rw …; exact …` in an argument slot whose implicit is undetermined fails (`?m ∈ momentBody`) —
  hoist to a typed `have`; `tiltResponse_zero ν f` (hS omitted); pull `t` inside sums with `mul_sub, Finset.mul_sum,
  mul_assoc` before `ring` when both sides carry sums. Round 52 landed: items 1, 2, 3, 4, 8, 9.
  NEXT: item 5 (conditional variational formula `L = sup_g E_D[g − log E_ν(e^g|σ(S))]`, clip `w = d/a`),
  item 6 (observable-defect second-order term), item 7 (mixed Hessian), item 10 (skewness
  `KL(Q₁‖ν) − KL(ν‖Q₁) = ∫ s(1−s) E ℓ³`), item 12 (length–energy); then round-53 consult.
- `AtlasLength` landed (round-52 item 12): `Len² ≤ ∫κ = KL(Π‖ν) + KL(ν‖Π)`. Gotcha: `integral_const` gives
  `(volume.restrict s).real univ • c`; rewrite `measureReal_def` BEFORE `Measure.restrict_apply_univ`;
  `Integrable.congr` pointwise goals are beta-redexes (`beta_reduce` before `rw [Real.sq_sqrt]`).
  Remaining round 52: item 5 (conditional variational formula), 6 (observable-defect second order),
  7 (mixed Hessian), 10 (skewness).
- `ConditionalVariational` landed (round-52 item 5): exact identity `KL(D‖T_g) = L − E_D g + E_D log E_ν[e^g|σ(S)]`
  for the conditional tilt, hence the conditional Donsker–Varadhan inequality and attainment at `g = log(d/a)`
  (bounded densities make the clipping unnecessary); `IsGreatest` packaging with the true conditional expectation
  (a.e. versions transported to `D` by `hDν.ae_eq`). Gotchas: `=ᵐ[ν] fun _ ↦ 1 ∧ …` parses the `∧` INTO the lambda
  (parenthesise); `klDiv_self` needs `SigmaFinite` (provide the probability instance first);
  `condExp_mul_of_stronglyMeasurable_left` uses Pi-multiplication `f * g` (state the function equality with
  `Pi.mul_apply`); `Real.exp_le_one_iff`, `Real.one_le_exp`, `inv_anti₀` for the clamp bounds.
  Round 52 landed: 1, 2, 3, 4, 5, 8, 9, 12. Remaining: 6 (observable-defect second order), 7 (mixed Hessian),
  10 (skewness). NEXT: round-53 consult (re-rank; ask for the next depth targets beyond 6/7/10).
- Round-53 consult (`gpt_responses/research_round53_{q,v1}.md`): ranking 1 skewness (`κ' = T(f,f,f)`, asymmetry =
  accumulated skewness), 2 mixed Hessian `D²q_M[u,z] = q_M(I − P₀ − B_M)(ℓ_u ℓ_z)` (P₀ = constant projection, NOT
  conditional expectation) with the observable-defect second order as a corollary, 3 global response-chart theorem
  (diffeomorphism modulo gauge; section + unique fibrewise minimiser; boundary), 4 unbounded densities for the bridge
  curvature split, 5 conditional variational formula for general densities (sup, not max), 6 four-path comparison
  package (e-path `e^{s log d}ν/Z` in the full simplex), 7 further curvature tensors.
- `AtlasSkewness` landed (rank 1): `κ'(s) = T_{Q_s}(f_s,f_s,f_s)` via the exact increment
  `κ(t) − κ(s) = Cov_{Q_s}(f_t,f_s) − Cov_{Q_t}(f_t,f_s)` (no inverse-covariance differentiation), and
  `KL(Π‖ν) − KL(ν‖Π) = ∫₀¹ s(1−s) E ℓ³`. Gotchas: `isLittleO_one_iff` takes the codomain `F` explicitly
  (`(isLittleO_one_iff ℝ).2`); `IsLittleO.sum` gives the Pi-sum (`congr_left` with `Finset.sum_apply`); a `have hP :=
  isProbabilityMeasure_familyMeasure …` without an expected type leaves `L₀` a metavariable (`by simp` fails with
  `?m = 0`) — ascribe the type; IBP on `[0,1]` needs `IntervalIntegrable (deriv κ)`: get it from `measurable_deriv` +
  a pointwise bound rather than continuity of the third moment.
  NEXT (round 53): rank 2 mixed Hessian (natural chart first: `D²p_θ[η,ζ] = p_θ(ℓ_η ℓ_ζ − Cov(ℓ_η,ℓ_ζ) − ⟨…⟩)`, then
  response coordinates), rank 3 global chart, rank 4 unbounded bridge split, rank 6 four-path package.
- `ExponentialPath` landed (round-53 rank 6): exponential path `E_s = ν.tilted(s log d)`; equal energies of the
  mixture and exponential paths `ν → D` and `ν → D↑`; `KL(D↑‖ν)+KL(ν‖D↑) ≤ KL(D‖ν)+KL(ν‖D)`; generic
  length ≤ √energy on `Ioo 0 1`. Gotcha: `sq_integral_sqrt_le_integral` already existed in `SegmentDivergence`
  (continuous version) — name clashes surface only at the umbrella build or the daemon; grep first.
  NEXT (round 53): rank 2 mixed Hessian (needs C² of the chart: derivative of `chartDeriv θ_s` along the path via
  `hasDerivAt_lawCov_familyMeasure_path` on the entries and `Ring.inverse` differentiation of the CLM —
  `hasFDerivAt_ring_inverse`), rank 3 global chart packaging (`meanMapHomeomorph`,
  `range_meanMap_eq_intrinsicInterior_momentBody`, strict derivatives, uniqueness of the fibrewise minimiser),
  rank 4 unbounded bridge split (interior-time identities via nonnegative kernels), rank 5 general conditional
  variational (sup, clipping).
- `GlobalChart` landed (round-53 rank 3, packaging of existing pieces): `relintChart : 𝕍 ≃ₜ ri K`, strict
  derivatives, inverse = `responseTheta`, section + unique fibrewise minimiser (`global_response_chart`).
  Gotchas: `continuous_meanMap` wants `hπ : ∀ x, 0 ≤ π x` (`zero_le_one`), unlike the chart lemmas (`one_pos`);
  in an `∃ e, … ∧ ∀ M, … e.symm M …` statement annotate `M`'s type; `responseChart` already existed in
  `ChartSynthesis` — the umbrella build is the only place a `def` clash surfaces (`_proof_2` collision).
  NEXT (round 53): rank 2 mixed Hessian (C² of the chart via `Ring.inverse` differentiation), rank 4 unbounded
  bridge split, rank 5 general conditional variational formula; or round-54 consult.
- `AtlasVelocityDerivative` landed (round-53 rank 2, stage 1 of the mixed Hessian): the covariance operator
  `Σ_s = −chartDeriv θ_s` is differentiable along the atlas with derivative the third-cumulant operator
  `D_s`, and `β_s' = −Σ_s⁻¹ D_s β_s`. Gotchas: `rw [← integral_const_mul]` picks the FIRST `c * ∫` (use
  `conv_rhs`); `ext v` on CLMs into a submodule descends into coordinates — use `ContinuousLinearMap.ext fun v ↦`;
  `sum_apply` (root) replaces the deprecated `ContinuousLinearMap.sum_apply`; the derivative identity for
  `−mulLeftRight x x G` applied to a vector is `rfl` (state it as an explicit `have … := rfl`, then `rw`);
  `Ring.inverse_unit`, `ContinuousLinearEquiv.unitsEquiv` for the unit; `Module.finBasis`, `Module.Basis.coord`,
  `LinearMap.toContinuousLinearMap` for the basis decomposition of an operator.
  NEXT: stage 2 — the density along the atlas: `d/ds q_s = q_s ℓ_s` (needs the derivative of `famZ θ_s`, via
  `integral_dirLoss_mul_famWeight` and dominated differentiation or `hasFDerivAt_obsMap`), then
  `d²/ds² q_s = q_s(ℓ_s² − κ(s) − ⟨Σ_s⁻¹ c_s, S − M_s⟩)` with `c_s = D_s β_s` (as vector `= E_s[(S−M_s) ℓ_s²]`),
  and the orthogonality `∫ q'' = 0`, `∫ S q'' = 0` by direct algebra.
- `AtlasHessian` landed (round-53 rank 2 complete on the atlas diagonal): `d²/ds² q_s = q_s(ℓ_s² − κ + ⟨w_s, S − M_s⟩)`
  with `w_s = Σ_s⁻¹ D_s β_s`, zero mass and zero feature moments. Gotchas: `have h : Integrable f _ := …`
  leaves the measure a metavariable (`IsProbabilityMeasure ?m` stuck) — always write the measure;
  `Bdd.const _` inside `.sub` needs the constant given; `(hasDerivAt …).neg.exp` produces a Pi-negated
  function — restate the negated `HasDerivAt` with a lambda type before `.exp`; `chartDeriv θ (e.symm y) = y`
  via `rw [← coe_chartDerivEquiv]; exact ContinuousLinearEquiv.apply_symm_apply _ _`.
  Round 53 landed: ranks 1, 2 (atlas diagonal), 3, 6. Remaining: rank 4 (unbounded bridge split), rank 5
  (general conditional variational), the polarised mixed Hessian `D²q_M[u,z]` in response coordinates
  (needs the second Fréchet derivative of the inverse chart — the path version is the diagonal `u = z = Δ`),
  observable-defect second order as a corollary. NEXT: round-54 consult or rank 4.
- Round-54 consult (`gpt_responses/research_round54_{q,v1}.md`): ranking 1 polarised response Hessian +
  observable-defect second order (Fréchet route: differentiate `M ↦ Σ_M`, then `A_M = Σ_M⁻¹`, then
  `Dq_M[u] = q_M ℓ_{M,u}`; est. 370–680 lines), 2 universal boundary blow-up (DONE), 3 Fisher normal geometry /
  second fundamental form (factor 1/2), 4 conditional variational for general densities (sup, clipping), 5
  Fisher–Rao great circle, 6 unbounded bridge split; §7 repackage as one structure theorem (global
  reconstruction / differential duality / normal geometry / pathwise accounting / boundary obstruction).
- `BoundaryBlowup` landed (rank 2): `κ(s) ≥ δ/(R(1−s))` from a supporting normal, `κ → ∞`, `∫₀¹ κ = ∞`,
  `−⟨θ_s,Δ⟩ ≥ (δ/R) log(1/(1−s))`. Gotchas: `not_imp` is `Classical.not_imp` (root deprecated);
  `intervalIntegral.integral_comp_sub_left f d` leaves `d − 0` in the bounds (`sub_zero` before
  `integral_inv_of_pos`); `continuous_sub_left (1:ℝ)` gives the lambda `fun s ↦ 1 − s`; a `Nonempty X`
  witness plus `+ 1` makes the bound `R` strictly positive without extra argument.
  NEXT: rank 1 (polarised Hessian) — the path machinery (`AtlasVelocityDerivative`, `AtlasHessian`) is the diagonal;
  or rank 3 packaging, or §7 structure theorem; or rank 4.
- `NormalGeometry` landed (round-54 rank 3, stage 1): response scores `ℓ_{M,u} = ⟨R u, M − S⟩`, differential
  duality `E_Q[ℓ_u ℓ_z] = ⟨Σ_M⁻¹ u, z⟩` (positive definite), regression/normal projections `B_M`, `N_M`
  (zero mass, zero feature moments, kill tangent scores), and the density-acceleration theorem
  `q_s''/q_s = N_{M_s}(ℓ_s²)` (via `atlasBend = R Cov(S, ℓ²)`). Gotchas: a `local notation` for the
  reconstruction measure / inverse chart derivative must avoid `.symm` projection syntax (write
  `ContinuousLinearEquiv.symm (…)`); `covVec` was taken by `MultiConstrainedResponse` (→ `respCov`); defs whose
  `M` is not determined by their arguments must take `M` explicitly (`regProj hS ν M hf`); `unfold atlasTheta`
  lines up `atlasTheta`-stated seabed lemmas with `responseTheta … (atlasPath …)`-stated new ones before `ring`.
  NEXT: rank 1 (polarised Hessian `D²q_M[u,z] = q_M N_M(ℓ_u ℓ_z)`, Fréchet route) — the atlas diagonal now reads
  `N_M(ℓ²)`; rank 3 stage 2 (Fisher–Rao second fundamental form `II = ½ N_M(ℓ_u ℓ_z)` via `q ↦ 2√q`); §7 structure
  theorem; rank 4.
- `CovarianceFrechet` landed (round-54 rank 1, stage 1): Fréchet differentiability in natural coordinates of
  `E_{P_θ}φ`, `Cov_{P_θ}`, `p_θ(x)`; the third-cumulant operator `T_θ` as Fréchet derivative of `Σ_θ|_𝕍`
  (basis assembly + `thirdOp_coe_apply` by uniqueness of derivatives); response coordinates via
  `hasStrictFDerivAt_responseTheta_add`; `D R_M[u] = −R T(Ru) R`; the polarised Hessian
  `D²q_M[u,w] = q_M N_M(ℓ_u ℓ_w)` (`hasFDerivAt_famDens_responseScore`). Gotchas: `.congr_deriv` is for
  `HasDerivAt`; for `HasFDerivAt` use `.congr_fderiv`; dot-notation `.sub/.mul` on a `have h := …` whose type
  is displayed as `HasFDerivAtFilter` yields Pi-form functions — ascribe the `HasFDerivAt` type with lambdas;
  defs placed under `include hS` get `hS` only if their body uses it (put `S ν` explicit on defs that don't);
  `local notation` cannot contain `.symm` projection syntax (use `ContinuousLinearEquiv.symm (…)`); align
  base points `θ(M + 0)` vs `θ(M)` by instantiating the outer derivative at `θ(M + 0)` and rewriting AFTER `comp`
  (rewriting before `comp` with `← h0` also hits the derivative's own occurrences and causes whnf timeouts);
  `(-mulLeftRight R R) G w = -(R (G (R w)))` as an explicit `rfl` lemma for `simp`; `dotCLM (M + z)` with
  `z : 𝕍` needs `(z : J → ℝ)` (dotCLM's index type is implicit).
  NEXT: observable-defect second order (`z ↦ E_{Q_z}[φ ℓ_{z,w}]` differentiable with derivative
  `∫ φ N_M(ℓ_u ℓ_w) dQ`; needs one integral-expansion helper `∫ ψ(a − ⟨v,S⟩) = a∫ψ − Σ v_j ∫ψ S_j`); then rank 3
  stage 2 (Fisher–Rao second fundamental form), §7 structure theorem, rank 4.
- `ObservableHessian` landed (round-54 rank 1 COMPLETE): `D_M E_{Π(M)}φ[u] = Cov_Q(φ, ℓ_u)` and the second
  derivative `E_Q[φ N_M(ℓ_u ℓ_w)]` (via the finite-combination identity `E_Q[φ ℓ_{M,w}] = ⟨R_M w, M⟩E_Qφ −
  Σⱼ (R_M w)ⱼ E_Q[φ Sⱼ]` and the integral-expansion helper). Gotchas: `HasFDerivAt.fun_sum` gives the lambda
  form (`.sum` the Pi form); when summands must match under `Σ` for `ring`, state helper identities with the
  factor order the derivative produces (`(∫ φ Sⱼ) * (Rc)ⱼ`) and fix with `Finset.sum_congr … mul_comm`;
  `(ContinuousLinearMap.proj j).hasFDerivAt` needs `(R := ℝ) (φ := fun _ : J ↦ ℝ)`.
  NEXT: rank 3 stage 2 (Fisher–Rao second fundamental form along the atlas: `r = 2√q`, `r'' = (r/4)N(ℓ²) −
  (κ/4) r − (r/4) B(ℓ²)` with the three pieces L²(ν)-orthogonal), §7 structure theorem, rank 4 (general
  conditional variational), rank 6 (unbounded bridge); round-55 consult.
- `FisherRaoCurvature` landed (round-54 rank 3 COMPLETE): square-root embedding `r_s = 2√q_s` on the sphere of
  radius 2, speed² = κ, acceleration = normal `(r/4)N(ℓ²)` + radial `−(κ/4)r` + tangential `−(r/4)B(ℓ²)`,
  pairwise orthogonal. Gotchas: `rw [← h]` with `h : ∫ … = 0` rewrites the `0` inside `familyMeasure ν 1
  (fun _ ↦ 0)` — use `(integral_congr_ae …).trans h`; `unfold atlasTheta` fails ("no atlasTheta") when the only
  occurrences sit inside `sqrtDens`/`atlasVel` applications — unfold only what is syntactically present and
  `unfold atlasTheta at hκ` for the hypothesis instead; `field_simp` closed the `√q` derivative identity once
  `√q` was `obtain`ed as an opaque `r` with `r² = q` and `q` rewritten to `r²` (`rw [← hr, ← hsq]`).
  Round-55 consult landed (`research_round55_v1`): NEXT = `FiniteResponse`: (1) path derivatives
  `d/ds E_{Q_s}φ = E_{Q_s}[φ ℓ_s]`, `d²/ds² = E_{Q_s}[φ N(ℓ_s²)]` (finite-combination trick as in
  ObservableHessian), (2) bound on `s ↦ R_s` over `[0,1]` (continuity of `Ring.inverse ∘ chartDeriv ∘ θ_s`,
  `NormedRing.inverse_continuousAt`) ⇒ `IntervalIntegrable` of the second derivative, (3) IBP
  `F(1) − F(0) = F'(0) + ∫₀¹(1−s)F''`, (4) fibre identity `E_D[N_M φ] = E_D φ − E_Q φ` for `E_D S = M`,
  (5) the accounting identity (*); then the Peano expansion (operator-valued assembly + generic lemma), the
  fibre-independent KL Hessian, dual-flat package.
- `FiniteResponse` landed (round-55 rank 1, stage 1 — the ACCOUNTING IDENTITY `E_D φ − E_ν φ = E_ν[φ ℓ_0] +
  ∫₀¹(1−s)E_{Q_s}[φ N(ℓ_s²)] + E_D[N_M φ]`). Gotchas: `HasDerivAt.clm_apply` on
  `(dotCLMlin.hasFDerivAt.comp_hasDerivAt s hM)` hits a whnf timeout — use the coordinate-sum route
  (`HasDerivAt.fun_sum` of `(hasDerivAt_pi.1 hβ i).mul (hasDerivAt_pi.1 hM i)` + `simp only [dotJ,
  Finset.sum_add_distrib]`) as AtlasHessian does; `ring` normalises INSIDE integrals under binders and can
  desynchronise two integrals that differ only by `atlasScore` vs its unfolding — restate the curvature identity
  in the exact syntactic form first (`hκ'` via `unfold atlasTheta at hκ; exact hκ`) and `rw [← hκ']`;
  `ContinuousAt.comp h hG` mis-parses `chartDeriv (atlasTheta t)` as `f x` with `f = chartDeriv` — pass
  `(f := fun t ↦ …)`; `NormedRing.inverse_continuousAt u` + `isCompact_Icc.exists_bound_of_continuousOn`
  bounds `s ↦ Σ_s⁻¹` on `[0,1]`; `‖⟨c, h⟩‖` in a submodule: `rw [← Submodule.norm_coe, Submodule.coe_mk]`;
  interval integrability of a derivative field: `Integrable.of_bound (measurable_deriv _).aestronglyMeasurable`
  + `.congr` with the pointwise `deriv = field` identity on `Ioc`; in `integral_eq_sub_of_hasDerivAt` the
  integrability is of the DERIVATIVE (`HasDerivAt.continuousOn h2` for the derivative field, not `h3`).
  NEXT (round 55): Peano expansion `F_φ(M+z) = F + A z + ½H(z,z) + o(‖z‖²)` (operator-valued assembly of
  `hasFDerivAt_integral_responseScore` on a basis + generic second-order Peano lemma from a differentiable
  derivative field), the fibre-independent KL Hessian `D²_z KL(D‖Π(M+z)) = ⟨Σ_M⁻¹u,w⟩`, dual-flat package
  (`∇𝓘 = −θ`, `D²𝓘 = G`, `DG[z](u,w) = −C(u,w,z)`), §7 structure theorem.
- `FibreHessian` landed: relative interior open in `𝕍` (`eventually_add_mem_intrinsicInterior`, via
  `map_nhds_eq_of_equiv` on `chartV` + `range_meanMap_eq_intrinsicInterior_momentBody`), interior-point derivatives of
  `θ(M+·)` and `𝓘(M+·)`, Pythagoras–Bregman `klDiv_fibre_eq`, KL derivative field `−⟨R_{M+z}w, z⟩`, Fisher Hessian.
  Gotchas: `HasFDerivAt.comp` with inner map `fun z ↦ z − z₀` needs `(f := fun z ↦ z - z₀)` (unifier picks
  `HSub.hSub z₀`); align the outer point by `rw [show (0 : 𝕍) = z₀ - z₀ by simp] at h`; a bare `0` derivative in a
  `HasFDerivAt` statement is a stuck `Module ?m ℝ` — ascribe `(0 : 𝕍 →L[ℝ] ℝ)`; `hasFDerivAt_const c x` takes the
  constant FIRST; `HasFDerivAt.const_sub` avoids zero maps; `rw` with root `sub_apply` needs `_root_.sub_apply`
  when `InformationTheory` is open; `-(A ∘SL B)` applied needs `neg_apply, neg_apply, comp_apply` in that order;
  `dotJ_comm` for `dotJ w θ` vs `dotJ θ w`. NEXT: Peano expansion (operator-valued assembly of
  `hasFDerivAt_integral_responseScore` on a basis + generic second-order Peano lemma), dual-flat package, §7.
- `ResponseTaylor` landed (round-55 rank 1 COMPLETE with FiniteResponse): generic Peano lemma from a
  differentiable derivative field (mean value on `[0,1]`: `norm_image_sub_le_of_norm_deriv_le_segment'` with the
  segment function `g t = F(tz) − t A0 z − (t²/2) Bzz`), `responseDerivField`, differentiability of the response at
  interior points, Fréchet derivative of the field = Hessian (basis assembly with `smulRightL (c i)` into `ℝ`,
  value by `hB.clm_apply (hasFDerivAt_const w 0)` + `.unique`), `response_peano`. Gotchas:
  `Metric.eventually_nhds_iff` gives `∀ ⦃y⦄, dist y x < ε → …` (strict-implicit `y`: pass only the distance
  proof); `hasFDerivAt_iff_isLittleO_nhds_zero` leaves `A (0 + h)` — `rw [zero_add]`; `abs_of_nonneg (sq_nonneg _)`
  inside `rw` grabs the first `|·|` — give the argument.
  NEXT: dual-flat package (`∇𝓘 = −θ` (have: `hasFDerivAt_genRate_response_at`), `D²𝓘 = G` = Fisher metric,
  `DG[z](u,w) = −C(u,w,z)` cubic tensor), §7 structure-theorem packaging, `L¹` density Peano, compact-uniform
  remainders, round-56 consult.
- `DualFlat` landed: `∇𝓘 = −θ`, `D²𝓘 = G` (Fisher form), `DG = −C` (cubic score tensor, totally symmetric),
  `B_M` = L²(Q)-orthogonal projection onto tangent scores, Bregman canonical divergence — packaged as
  `dual_flat_structure`. Gotchas: `cubicForm` exists in `Patterning/GaussianFourth` (→ `cubicScore`); the
  identification `dotJ (R⟨c⟩) w = −C` goes through `fisherForm_eq_neg_dotJ` at `⟨respCov(ℓ_vℓ_u), _⟩` and
  `integral_regProj_mul_responseScore` (regProj unfolds to `responseScore ⟨respCov f, _⟩` with the SAME
  membership proof term), closed by `linarith`; `.neg` on `HasFDerivAt` gives a Pi-negated function
  (`Pi.neg_apply` in the congr simp set); `fun M' hM' ↦ lemma … hM'` trips the unused-variable linter on `M'`.
  NEXT: §7 structure-theorem packaging (global chart ∧ differential duality ∧ normal geometry ∧ accounting ∧
  boundary blow-up), `L¹` density Peano, compact-uniform remainders, round-56 consult.
- `ResponseStructure` landed: `response_structure_theorem` packages global chart ∧ differential duality/dual-flat ∧
  normal geometry (polarised Hessian + Peano) ∧ accounting identity ∧ boundary obstruction. Gotcha: a binder
  `∀ M (hrel : M ∈ K) …` whose `hrel` is used only in the proof trips the unused-variable linter — write
  `∀ M ∈ K, ∀ hfin : …,` instead. Round-56 consult running/landed (`research_round56_{q,v1}`). NEXT per consult.
- `InformationAlongAtlas` landed (round-56 companion): `KL(D‖Q_s) = KL(D‖Π(M)) + ∫_s^1(1−t)κ`, budget
  `KL(D‖ν) = KL(D‖Π(M)) + ∫₀¹(1−t)κ`, antitone, `d/ds = −(1−s)κ`. Gotchas: EndpointTail ALREADY had
  `toReal_klDiv_responseProjection_atlas(_eq_integral)` (`KL(Π(M)‖Q_s) = ∫_s^1(1−t)κ`) — grep before writing;
  `rw [← familyMeasure_zero_eq hS ν] at h` rewrites every `ν` (motive error) — prove
  `responseProjection (atlasPath 0) = ν` as a separate `have` and rewrite with it;
  `ContinuousOn.stronglyMeasurableAtFilter (μ := volume) isOpen_Ioo hcontOn s hs` for the FTC-left lemma.
  NEXT (round 56): the TV density Peano (`∫|q_{M+z} − q_M − q_Mℓ_z − ½q_MN(ℓ_z²)| = o(‖z‖²)`): (1) pointwise
  Hessian field `H_z[u,w] = q_z N_{M+z}(ℓ_uℓ_w)` at interior `z` (repackage `hasFDerivAt_famDens_responseScore`
  at base `M+z`), (2) domination `q_z ≤ C q_0`, `|H_z[u,w]| ≤ C q_0 ‖u‖‖w‖` on a small ball (bounded features,
  `R` locally bounded), (3) integrated continuity `∫|H_z[e_i,e_j] − H_0[e_i,e_j]| → 0` by dominated convergence,
  (4) pointwise scalar Taylor with integral remainder along `t ↦ tz` + Fubini ⇒ `o(‖z‖²)`; then compact-uniform;
  then the triangular boundary endpoint.
- `ThetaPeano` + `DensitySecondOrder` landed (steps 1–2 of the TV density Peano, EXPLICIT route instead of the
  Fubini/dominated-convergence route): vector-valued Peano lemma; `θ(M+z) = θ + Rz − ½R T(Rz)(Rz) + o(‖z‖²)`;
  pointwise-uniform second order `|p_{θ+η} − p_θ T_θ(η)| ≤ 13(K‖η‖)³ p_θ` via the abstract ratio lemma
  `abs_ratio_sub_second_order_le` (core cubic identity from sympy, monomials bounded one by one; `nlinarith`
  avoided). Gotchas: an appended `section` after `end Laplace.Multi` silently loses the namespace (all names
  unknown) — insert before the final `end`; `Real.exp_bound (x := −w) … (n := 3)` gives the constant
  `4/(6·3) = 2/9`; after `rw [hε]` there is no `ε` left for a later `rw [← hε]` inside a calc step — keep `ε`
  abstract until the end.
  NEXT (step 3): `DensityPeano.lean` — compose: with `η(z) = θ(M+z) − θ(M) = Rz − ½R c_z + v(z)` (`c_z =
  Cov_Q(S,ℓ_z²)`, `v = o(‖z‖²)`), expand `T_{θ(M)}(η)` = `1 + ℓ_z + ½N_M(ℓ_z²) + ⟨v, m − S⟩ + O(‖z‖³)` pointwise-
  uniformly (algebraic identity for `densTrunc` at `Rz + ζ` + bounds on `ℓ_c`, covariances of `⟨ζ,S⟩`), then
  `∀ ε > 0, ∀ᶠ z, ∀ x, |q_{M+z} − q_M − q_Mℓ_z − ½q_MN(ℓ_z²)| ≤ ε‖z‖² q_M` and the TV corollary
  `∫|…| = o(‖z‖²)`.
- `DensityPeanoAlgebra` + `DensityPeano` landed (round-56 FLAGSHIP): `famDens_response_peano` (pointwise-uniform
  relative `o(‖z‖²)` remainder of `q_{M+z}` against `q_M(1 + ℓ_z + ½N(ℓ_z²))`) and
  `isLittleO_integral_famDens_response_peano` (TV Peano `∫|…| = o(‖z‖²)`). Gotchas: `maxHeartbeats` is a
  per-DECLARATION budget — a 300-line proof dies with a `whnf` timeout at the header and at whatever line the
  budget ran out (looks like a local unification problem; it is not) → `set_option maxHeartbeats 2400000 in`
  with the mandatory comment BEFORE the docstring; `∀ z, … θr (M + z) …` infers `z : J → ℝ` from `M + z` —
  annotate `∀ z : 𝕍` / `fun z : 𝕍 ↦` everywhere; `mul_le_mul` against a goal `… ≤ c ^ 2` whnf's the square to
  `c * npowRec 1 c` (rewrite `sq` first); `abs_lawCov_le` needs the `IsProbabilityMeasure` instance of
  `P_{θ(M)}` in scope (`have := isProbabilityMeasure_family_responseTheta hS ν (M := M)`); `rw` closing
  `(fun z ↦ …) z` redexes needs an explicit `rfl`; `Metric.eventually_nhds_iff` gives `dist z 0 < δ` (strict) —
  `.le`. ‖ζ z‖ ≤ ‖z‖ needs the threshold `1/(BK₂²‖R‖³+1)`, NOT `‖z‖ ≤ 1/2`.
  NEXT (round 56): compact-uniform remainders (M in a compact of ri K: uniform `R`, uniform `v = o` via the
  strict derivative), the triangular boundary endpoint, round-57 consult.
- `BoundaryTaylor` landed (round-56 boundary item A, reparametrisation route): accounting identity on `[0,t]` for every
  `t < 1` at finite-rate (boundary) responses + triangular endpoint limit. Gotchas: `atlasTheta`/`responseTheta` need
  `[Nonempty J]` (cannot `omit`); `module` fails after `ext` has gone down to coordinates (`(t • M) j` atoms) — stop at
  `Subtype.ext` and let `module` work in `J → ℝ`; `intervalIntegral.integral_comp_mul_right` needs `f` explicit when the
  integrand is a beta-redex `(fun u ↦ …) (s * t)`. Round-57 consult landed (`research_round57_v1`): rank 1 = finite-rate
  boundary COMPLETION (endpoint law by TV-Cauchy, `(1−s)i'(s) → 0`, `KL(Q_*‖Q_s) = ∫_s^1(1−t)κ`), rank 2 = reconstruction
  as compact-uniformly Lipschitz retraction of distribution space, rank 3 = all-orders relative-uniform analyticity,
  rank 4 = TV atlas curve. NEXT: rank 1 per §2 of the consult.
- `BoundaryCompletion` landed (round-57 rank 1; assembly): `Q_s → Q_* = Π(M)` for bounded observables at every
  finite-rate response, `KL(Q_*‖Q_s) → 0`, Pinsker tail bound, triangular accounting at the endpoint,
  `boundary_completion` package. Gotcha: `zero_le` takes its argument implicitly (`fun _ ↦ zero_le`).
  NEXT (round 57 rank 2): the reconstruction as a compact-uniformly TV-Lipschitz retraction of distribution space:
  `‖Π(M') − Π(M)‖_var ≤ √Λ_H ‖M' − M‖` on compact convex `H ⊂ ri K` (via `E_Q|ℓ_u| ≤ √⟨u,Σ⁻¹u⟩` and segment
  integration of the density derivative), `‖E_DS − E_{D'}S‖ ≤ L‖D − D'‖_var`, `D ↦ Π(E_DS)` TV-Lipschitz on
  compacts; derivative `DR_D[H] = Q ℓ_{M,m(H)}` is a projection (`L_Q² = L_Q`, kernel = moment-invisible
  perturbations); then rank 3 (all-orders) / rank 4 (TV atlas curve).
- `ReconstructionLipschitz` landed (round-57 rank 2): TV-Lipschitz retraction of distribution space. Gotchas: local
  notations that mention section variables cannot be used inside a later `variable (h : …)` binder ("Unknown constant
  ν✝") — write the terms out there; `hasFDerivAt_integral_response_at hS ν hF hz` takes no `hrel`;
  `Subtype.image_preimage_coe` (not `Set.`); `norm_integral_le_integral_norm` + `simpa only [Real.norm_eq_abs]` for
  `|∫f| ≤ ∫|f|` (the `abs_` name is interval-only); after `rw [hF]` with `hF : F = fun x ↦ if …` the goal is a
  beta-redex — `beta_reduce` before `split_ifs`; `responseProjection_mean_familyMeasure` ALREADY EXISTS in
  `AtlasRefinement` (for any `θ : K → ℝ`) — the duplicate-name grep printed it and I overlooked the line: read the grep
  output, not just "dupdone". NEXT: compact-uniform relative-uniform Peano (consult §3 lemma route), all-orders
  analyticity (rank 3), TV atlas curve `d_TV(Q_s,Q_t) ≤ ½∫√κ` (rank 4); round-58 consult.
- `AtlasTotalVariation` landed (round-57 rank 4): TV speed of the atlas ≤ Fisher speed. Gotchas: `atlasCurv_eq_integral_score_sq`
  (AtlasHessian) needs `hrel` — the `hfin`-only version for `u < 1` goes through `atlasCurv_eq_priorCov`,
  `priorCov_eq_lawCov_familyMeasure`, `lawCov_self_eq_integral_sq`, `dotJ_integral_eq` + `mean_familyMeasure_one_zero` +
  `meanMap_atlasTheta`; the atlas derivative at finite-rate (boundary) `M` for `u < 1` comes from
  `hasFDerivAt_integral_response_at` at base `m₀` along `t ↦ t • ⟨M − m₀, _⟩` (no reparametrisation needed).
  NEXT: compact-uniform relative-uniform Peano (consult §3 lemma route: uniform `‖R‖`, `‖T‖`, uniform θ-Peano via
  continuity of `D²θ`), all-orders analyticity (rank 3), round-58 consult.
- `UniformPeano` + `ThetaUniformPeano` + `DensityPeanoUniform` landed (round-57 rank 2b): the compact-uniform
  relative-uniform second-order expansion of the reconstruction density. Route: generic uniform Peano (mean value ×2 +
  uniform continuity of `D²F`), `continuous_thirdOp`, quantitative version of `famDens_response_peano` with the
  θ-remainder as a hypothesis (`abs_famDens_response_remainder_le`), then assembly with explicit thresholds
  (`densPeanoBound_le`). Gotchas: `(1/2) • v` without a type ascription elaborates the numeral in ℕ (`= 0 • v`) — write
  `(1 / 2 : ℝ) • v` in every `have`; `continuous_induced_rng.2` presents the goal as `Subtype.val ∘ f` — `change` to the
  lambda before `rw`; `thirdCentral_eq` takes the measure explicitly first; `hasFDerivAt_responseTheta_add_at hS ν hz`
  and `hasFDerivAt_inverse_response hS ν hz` translate to arbitrary interior base points with the
  `HasFDerivAt.comp (f := fun w ↦ w − z)` + `congr 4; abel` idiom. NEXT: all-orders analyticity (rank 3) or round-58
  consult; also the compact-uniform observable Taylor corollary is immediate from the TV statement.
- `ResponseAtlasTheorem` landed: the one-theorem packaging (§6 of round 57) of the whole "featureless → data" programme.
  Round-57 items 1, 2, 2b, 4 and the packaging are DONE; remaining: rank 3 (all-orders relative-uniform analyticity, with
  `E_Q A_n = 0`, `E_Q[S A_n] = 0` for `n ≥ 2`). NEXT: round-58 consult, then per ranking.
- `EmpiricalTotalVariation` landed: TV consistency of the empirical reconstruction (SLLN + compact-uniform Lipschitz on a
  compact convex neighbourhood). Gotcha: `filter_upwards [h.eventually (Metric.closedBall_mem_nhds …)]` hands the
  membership already unfolded to `dist … ≤ r`. Round-58 consult running (`research_round58_{q,v1}`).
- `EntropyGapStability` landed (round-58 rank 1): lsc of the rate, entropy-gap inequality, non-radial stability under
  `(M, 𝓘(M))`-convergence. Gotchas: `genRate_mixture_gap` is stated with `a b : ℝ≥0` weights, `(a : ℝ) • M₀` and
  `(a : ℝ≥0∞) * 𝓘`; `ENNReal.Tendsto.const_mul` needs the constant pinned via a typed `have`; `add_le_add_left/right`
  orientation is unreliable — use `add_le_add h le_rfl`; `Real.continuous_sqrt.tendsto 0 |>.comp` then
  `rw [Real.sqrt_zero]`. Round-58 consult (`research_round58_v1`) remaining: named observable Taylor corollary,
  moment-normality at all orders (needs C^n), analyticity route (a), segment continuity of the rate (4.2), observable
  delta method (5.3, needs CLT), dual-curve comparison (6).
- `SegmentStability` + `ObservableTaylorUniform` landed (round-58 §4.2 and the named observable corollary). Gotchas:
  `ENNReal.ofReal_eq_coe_nnreal` rewrites leave `↑⟨x,p⟩ = ↑⟨x,q⟩` unsolved — go through `ENNReal.coe_nnreal_eq` + the
  real coercion identity instead; `(⟨x, h⟩ : ℝ≥0) : ℝ) = x` is `rfl` after `rw`; `Tendsto.mono_left nhdsWithin_le_nhds`
  needs `(s := Iio 1)`; a section variable `ν` not mentioned in a statement is NOT an argument of that theorem.
  Round-58 remaining: moment-normality at all orders / analyticity (rank 3), observable delta method (needs CLT), dual
  curve comparison. NEXT: round-59 consult or all-orders audit.
- `DualCurveComparison` landed (round-58 §3(iv)/(6)). Gotchas: after `rw` closes a goal by rfl a following `congr 1`/`exact`
  errors "No goals"; `IsLittleO.comp_tendsto` + `IsBigO.of_bound` with `simp only [Function.comp_def, Real.norm_eq_abs,
  norm_smul]` then `abs_of_nonneg (sq_nonneg (|t| * ‖u‖))`, `abs_of_nonneg (sq_nonneg t)`, `mul_pow, sq_abs`.
  Round-58 remaining: all-orders/moment-normality (large; smooth IFT `ContDiffAt.to_localInverse` exists, no Banach
  analytic IFT, no CLT in Mathlib → delta method out of reach). NEXT: round-59 consult.
- `EntropyGapTotalVariation` landed: TV form of the entropy gap and TV continuity on the finite-rate domain. Gotchas:
  `responseProjection_absolutelyContinuous hS ν hfin` already exists (StraightPathAtlas); rnDeriv lemmas need the
  `IsProbabilityMeasure (responseProjection …)` instance in scope (`have hP := (responseProjection_spec …).1`);
  `integral_rnDeriv_smul` is in namespace `MeasureTheory` (not `Measure`). Round-59 consult landed
  (`research_round59_v1`) — NEXT per its ranking.
- `DifferentialRetraction` landed (round-59 rank 2, prototype-level: `C¹` continuity of the derivative NOT stated). Gotchas:
  convert an `L¹`-valued `HasFDerivAt` goal to the seabed's real little-o via
  `rw [hasFDerivAt_iff_isLittleO_nhds_zero, ← isLittleO_norm_left, ← isLittleO_norm_right]`; `Integrable.toL1_sub` etc. are
  `rfl` lemmas in Pi form (use `← toL1_sub` then `L1.norm_of_fun_eq_integral_norm`); `LinearMap.toContinuousLinearMap`
  for a linear map out of the finite-dimensional `𝕍`. NEXT: refinement tower package (already have both identities in
  `AtlasRefinement`), `C¹`/`C²` of `reconstructionL1`, all-orders prototype; round-60 consult.
- `RefinementTower` landed (package of `AtlasRefinement` + `responseProjection_spec`). Round-59 ranks 1–3 DONE; remaining:
  `C¹`/`C²` of `reconstructionL1`, all-orders prototype. NEXT: round-60 consult.
- `ReconstructionC1` landed. Gotchas: `continuousOn_iff_continuous_domRestrict` + `Set.domRestrict_apply` (the `restrict`
  names are deprecated); `eventually_mem_nhdsWithin.and h2` (not `self_mem_nhdsWithin.and`); coercion of a 𝕍-difference
  in a statement is elaborated leafwise (`↑a − ↑b`), so fold with `← Submodule.coe_sub` before `Submodule.norm_coe`.
  Round-60 consult landed (`research_round60_v1`): converse of entropy-graph stability is FALSE; reconstruction-bias theorem
  reachable without CLT; all-orders prototype = option (a) unnormalised. NEXT per consult.
- `RegressionOrthogonality` landed (cheap Hilbert-space meaning of the tangent retraction). Gotcha: `rw [← h]` with
  `h : ∫ … = 0` rewrites the zeros inside `familyMeasure ν 1 (fun _ ↦ 0)` — use `(integral_congr_ae …).trans h`.
  Round-60 remaining: length control for `C¹` curves, reconstruction-bias theorem (fourth-moment bound of iid bounded sums
  + compact-uniform observable Peano), `C²` via differentiating the score, all-orders prototype (unnormalised Laplace
  transform `ContDiff ⊤`). NEXT: reconstruction-bias theorem.
- `CurveLength` landed. Gotchas: `ContinuousWithinAt.comp` needs `(g := …) (f := …)` explicit when the goal is a lambda
  (else it unifies `g := HAdd.hAdd M`); `congr 1; abel` for the argument of `reconstructionL1` after the chain rule.
  Round-60 remaining: reconstruction-bias theorem (Hoeffding via `measure_sum_range_ge_le_of_iIndepFun` +
  `hasSubgaussianMGF_of_mem_Icc_of_integral_eq_zero`; needs `iIndepFun`), `C²` via differentiating the score,
  all-orders prototype. NEXT: reconstruction-bias theorem (probability lemmas first).
- `EmpiricalMoments` landed (unbiasedness, `Γ/n` second moments, Hoeffding tails of `M̂_n`). Gotchas: the Hoeffding lemma is
  `HasSubgaussianMGF.measure_sum_range_ge_le_of_iIndepFun` (namespaced); its constant `((‖b − a‖₊/2)^2 : ℝ≥0)` casts to
  `4B²` by `push_cast; rw [Real.norm_eq_abs, abs_of_nonneg]`; the `B = 0` case of the tail is NOT dominated by
  `exp(−c n δ²)` (it gives `exp 0 = 1`) — use the bound `B + 1` in the existential corollary; `iIndepFun.comp` gives the
  centred family, `HasSubgaussianMGF.neg` the lower tail. NEXT: reconstruction-bias theorem assembly
  (`integral_response_peano_uniform` + `Γ/n` + tail with fallback outside the compact convex neighbourhood).
- `BiasForm` + `ReconstructionBias` landed: THE RECONSTRUCTION-BIAS THEOREM (round-60 §4). Gotchas: `Submodule.linearProjOfIsCompl`
  is deprecated for `Submodule.projectionOnto p q h` (`projectionOnto_apply_left h x`); `continuousOn_responseTheta_add` is
  based at the featureless response `m₀ = meanMap …` (obtain `M = m₀` and `subst`); after `obtain ⟨M, hM⟩ : ∃ M, M = …`
  the abbreviation is OPAQUE, so `change` between `M j` and its definition fails — rewrite with `hM` instead; state
  abbreviations of families pointwise (`∀ a b, Γ a b = …`) so `simp only [← hΓ]` folds applied occurrences;
  `simp_rw [linearMap_eq_sum_coordUnit L]` loops (RHS contains `L (coordUnit a)`) — use a `funext` rewrite of the
  integrand; `plugIn` takes `[DecidablePred (· ∈ C)]` so `ContinuousOn.measurable_piecewise` unifies. NEXT: bias
  coefficient as `½ E_D b_F(S(x) − M, S(x) − M)` (π-free form), `C²` via differentiating the score, all-orders prototype,
  round-61 consult.
- `sum_dataCov_mul_biasForm_eq` landed (π-free bias coefficient). Round-60 remaining: `C²` via differentiating the score,
  all-orders prototype (unnormalised Laplace transform `ContDiff ⊤`); then round-61 consult. NEXT: round-61 consult
  (reconstruction-bias theorem done; ask for the next core feature of `D ↦ Π(D)` across the data manifold).
- `dataMoment_mixture_eq_atlasPath` landed (mixture path ↔ straight atlas). Round-61 consult landed (`research_round61_v1`):
  NEXT in order: (1) data-path transport: for a TV-`C¹` curve `t ↦ D_t` with interior responses, `Ṁ_t = ∫ S dḊ_t`,
  `d/dt G_F(M_t) = lin_{F,M_t}(Ṁ_t) = ∫ ψ_{F,M_t} dḊ_t` with `ψ_{F,M} = ⟨C_M⁻¹ c_F(M), S − M⟩`, and
  `G_F(M_1) − G_F(M_0) = ∫_0^1 lin_{F,M_t}(Ṁ_t) dt`; along the mixture path `𝓘(M_t)' = ⟨θ_t, δ⟩`, `𝓘(M_t)'' = H_{M_t}(δ,δ)`,
  `𝓘(M_t) = ∫_0^t (t−r) H_{M_r}(δ,δ) dr` (convex, nondecreasing, `𝓘(M_t) ≤ t 𝓘(M)`); (2) information splitting along the
  atlas with the NON-monotonicity of the invisible part (counterexample to record in the slop note) and the identity
  `tR'(t) = R(t) + KL(ν‖D_t) − KL(ν‖Q_{M_t})`; (3) `C²`; (4) `𝓘`-bias; (5) joint plug-in covariance. Mathlib-facing
  extractions suggested: empirical bilinear contraction `E B(Z̄_n, Z̄_n) = (1/n) E B(Z,Z)`; localised second-order delta lemma.
- `ResponseTransport` landed (round-61 rank 1: chain rule + FTC for `G_F` along response paths, influence function,
  influence form along the affine data path). Gotchas: state algebraic identities with the DIRECT `(CDE …).symm u` rather
  than the CLM coercion `(… : 𝕍 →L 𝕍) u` (otherwise `linarith` sees two atoms); bridge in continuity proofs with
  `ContinuousLinearEquiv.coe_coe`; `deriv_mem_dirSpan_of_path hV hM'` takes only two explicit args; `hasDerivAt_atlasPath ν
  (M := M) s`; `lawCov_dirLoss_left hS Q v ψ hψ`; subtype-valued paths are continuous via
  `Topology.IsInducing.subtypeVal.continuousOn_iff` + `ContinuousOn.congr`. NEXT: rank 2 (information splitting along
  the atlas with the non-monotone invisible part: record the three-point counterexample in Lean, `R(t) ≤ t KL(D‖ν)`,
  `tR'(t)` identity), then `C²`, `𝓘`-bias, joint plug-in covariance.
- `InvisibleHump` landed (rank 2: envelopes + the three-point non-monotonicity counterexample). Gotchas: `Measure.count` on
  `Fin 3` with `(3:ℝ≥0∞)⁻¹ • count`; `tilted_apply_eq_ofReal_integral'` + `integral_singleton` (`μ.real {a} • f a`) give
  point masses; `ℝ≥0`-smul on `ℝ≥0∞` unfolds with `ENNReal.smul_def` THEN `smul_eq_mul`; never `rw [hump3D]` in a goal that
  later needs `klDiv_self` (the `IsProbabilityMeasure` instance is on the def, the unfolded `familyMeasure` has no
  `SigmaFinite` instance) — restate the projection identity for the def by `:= h` (defeq); `θ' : 𝕍` needs `(θ' : J → ℝ) 0`.
  Round-61 remaining: `L²` local expansion `R(t) = ½t²‖N_{m₀}h‖² + o(t²)`, diagnostic `tR'(t)` identity, `C²` (rank 3),
  `𝓘`-bias (rank 4), joint plug-in covariance (rank 5). NEXT: rank 5 (cheap, 250–500 LOC: joint covariance of plug-ins with
  the sandwich form), then rank 4, then `C²`.
- `PlugInCovariance` landed (rank 5): `n Cov(Ĝ_F, Ĝ_G) → E_D[lin_F(S−M) lin_G(S−M)]`. Gotchas: an anonymous constructor
  `⟨…, fun _ ↦ tendsto_proof⟩` for `∀ [inst], Tendsto …` unfolds `Tendsto` into its filter definition — use
  `refine ⟨…, ?_⟩; intro _; exact …`; `Set.piecewise` lemmas need the instance in the statement (`[DecidablePred (· ∈ C)]`);
  `all_goals first | exact … | exact …` discharges the four `integral_sub` side goals. Round-61 remaining: rank 4 (`𝓘`-bias:
  needs a compact-uniform second-order Peano for `𝓘` in response coordinates), rank 3 (`C²`), the `L²` local expansion of
  the invisible information, the `tR'(t)` identity. NEXT: rank 4 — first check which Taylor data for `genRate` exist
  (`hasFDerivAt_genRate_chart`, `genRate_atlasPath_eq_integral`); the uniform second-order Peano for `𝓘` may follow from
  `uniform_responseTheta_peano` + the dual-gradient identity `D𝓘 = θ`.
- `InformationTaylor` + `PlugInBias` + `InformationBias` landed (rank 4). Gotchas: a `def` in a section with `include hS`
  does NOT take `hS` unless its statement mentions it (`pairLin ν`, not `pairLin hS ν`); `rw [h]` with `h : m₀ + ↑z = M`
  rewrites ALL occurrences — do not list it twice; the generic `uniform_peano_of_hasFDerivAt` works verbatim for the rate
  with `A z := pairLin (θr (m₀+z))`, `B z := pairLin.comp (Rat z)`; a theorem whose statement does not mention `ν` has
  no `ν` argument even inside the `(ν)` section (`sum_dataCov_mul_bilinear_eq_integral hS D b`). Round-61 remaining:
  rank 3 (`C²` of the reconstruction in `L¹`), the `L²` local expansion of the invisible information, the `tR'(t)`
  identity; the round-61 programme is otherwise CLOSED (ranks 1, 2, 4, 5 done). NEXT: round-62 consult with the
  full picture; candidates: `C²` in `L¹`, the diagnostic identity, the invisible `L²` expansion, and the referee-level
  restatement of the bias/covariance theorems with an intrinsic (`π`-free) `L`.
- Round-62 consult landed (`research_round62_v1`): flagship = `C²` of the `L¹`-valued reconstruction with Hessian an
  invisible signed measure (`½ Σ Γ_ab ∂²q` uniform-in-`F` bias); cheap structural items: (2) tangent Pythagoras
  `E_Q[a²] = g_M(u,u) + ‖N_M a‖²`, `u = E_Q[T a]`, `ψ_{F,M} = P_M(F − EF)` (= our `regProj F`!), `E_Q[ψ_F ℓ_u] = lin_F(u)`,
  `Var_Q ψ_F = g_M(c_F,c_F)` (metric on the covariance VECTOR, not inverse); (3) the atlas is the exact natural-gradient
  flow of `L(M) = KL(Q_{M*}‖Q_M)` with `grad_g L = M − M*`, `M(τ) = m₀ + (1−e^{−τ})(M* − m₀)`, dissipation
  `dL/dτ = −g(M−M*, M−M*)`; `κ(s) = g_{M_s}(δ,δ)` = squared Fisher speed, `𝓘(M_s) = ∫₀ˢ(s−r)κ` a weighted kinetic energy;
  (4) second-order transport; (5) invisible information = squared normal data displacement (`L²` expansion);
  (6) tilt-path diagnostics. Order: tangent geometry → second transport → natural-gradient atlas, with `C²` in parallel.
  Sanity: information-bias coefficient `½ tr_V(C_M⁻¹ Γ_D)` confirmed, `= ½ dim 𝕍` when `Γ = C_M`. Referee: state on `𝕍`
  with `Z = S − M`, `Γ_D = E_D[Z⊗Z]`, `dG_F ∈ 𝕍*`, `b_F ∈ Sym²(𝕍*)` (affine mean-coordinate Hessian, not Levi-Civita).
- `TangentPythagoras` landed (round-62 rank 2; the influence function IS `regProj`, so the whole regression API applies).
  NEXT: rank 4 second-order transport along the affine data path (`d²/dt² G_F(M_t) = b_{F,M_t}(δ,δ)` and the exact
  second-order formula `G_F(M_t) = G_F(m₀) + t lin_{F,m₀}(δ) + ∫₀ᵗ (t−r) b_{F,M_r}(δ,δ) dr`; seabed has
  `hasDerivAt_deriv_integral_familyMeasure_atlas` with a `thirdCentral` second derivative and `atlasHess_eq_normalProj`),
  then rank 3 (natural-gradient atlas), then the `C²` flagship.
- `SecondOrderTransport` landed (rank 4). Gotchas: a `local notation` whose body is an anonymous constructor fails
  ("no quot_precheck") — use a `def` (`atlasInc`); `atlasTheta s` and `θr (atlasPath s)` are defeq but not syntactic —
  state intermediate integrals in whichever form the goal has after `unfold`, and pass instances by a typed `have`
  (`IsProbabilityMeasure (Pfam (atlasTheta s)) := isProbabilityMeasure_family_responseTheta …`); interval integrability
  of a second derivative without proving its continuity: `measurable_deriv` + `Measure.integrableOn_of_bounded` on
  `Ioc` + `HasDerivAt.deriv` on the interval; `ae_restrict_iff' measurableSet_Ioc`. NEXT: round-62 rank 3 (the atlas is
  the natural-gradient flow of `KL(Q_{M*}‖Q_M)`: `grad_g L = M − M*`, explicit flow with `s = 1 − e^{−τ}`, dissipation),
  then the `L²` invisible expansion, then the `C²` flagship.
- `NaturalGradientAtlas` landed (round-62 rank 3). Gotchas: `klDiv` needs `open InformationTheory`; the family-KL
  chain `klDiv_familyMeasure` → `ENNReal.toReal_ofReal (famKL_nonneg …)` → `famKL_eq` gives the real Bregman form
  (pass `(M₀ := 0) (fun _ ↦ by simp)` for `L₀ = 0`; DualPotential's `hπ` is `0 ≤ π`, FamilyBregman's is `0 < π`);
  `hasFDerivAt_affLogZ` needs `(π := …) (L₀ := …) (R := S) (t := 1)` pinned; compose at the point `θr (M + ↑0)` and
  `simp only [h0]` afterwards; `HasFDerivAt.congr_fderiv` (not `congr_deriv`); `HasDerivAt.scomp` for a vector path
  composed with a real reparametrisation; a `def` whose statement does not mention `S` needs `variable (S) in`.
  Round-62 status: ranks 2, 3, 4 DONE; remaining: rank 1 flagship (`C²` `L¹`-Hessian as invisible signed measure),
  rank 5 (invisible `L²` expansion), rank 6 (tilt diagnostics). NEXT: rank 5 (`R(t) = ½t²‖N_{m₀}h‖² + o(t²)`) since it is
  short and independent, then the `C²` flagship.
- `InvisibleQuadratic` landed (round-62 rank 5). Gotchas: `h ▸ proof` inside a subtype literal in a THEOREM STATEMENT causes a
  kernel deterministic timeout — name the membership proof as its own theorem (`sub_one_dir_mem`); `LinearMap.map_smul₂`
  already applies to the doubly-applied bilinear form (`f (c•x) y = c • f x y`), so no `LinearMap.smul_apply` afterwards;
  `Integrable.bdd_mul (hg) (hf_meas) (bound)` needs the BOUNDED factor first; `mean_densLaw_bridge ν hd hc0 hc hC hS`;
  `integrable_of_bounds ν hd hc hC`; `Ioo_mem_nhdsGT one_pos : Ioo 0 1 ∈ 𝓝[>] 0`; `Metric.tendsto_nhdsWithin_nhds` binds
  `⦃x⦄ (hx : x ∈ s) (hd : dist x a < δ)`. Round-62 status: ranks 2, 3, 4, 5 DONE; remaining rank 1 flagship (`C²`
  `L¹`-Hessian as invisible signed measure; the atlas-level facts `integral_atlasHess = 0`, `integral_mul_atlasHess = 0`
  already exist in `AtlasHessian`) and rank 6 (tilt-path diagnostics). NEXT: round-63 consult with the full picture, or
  begin the `C²` flagship via the atlas: `hasDerivAt_famDens_deriv_atlas` + dominated convergence for the `L¹` second
  derivative along the atlas (a "C² along lines" version), before the full Fréchet `C²`.
- Round-63 consult landed (`research_round63_v1`): the missing bridge is the UNIFORM `L¹` SECOND JET at a fixed base,
  `sup_{‖h‖≤ρ} ‖q_{M+h} − q_M − J_M h − ½H_M[h,h]‖₁/‖h‖² → 0` with `H_M[u,v] = q_M N_M(ℓ_uℓ_v)` — which the seabed's
  `integral_abs_famDens_response_peano_uniform` (DensityPeanoUniform) ALREADY provides (compact-uniform TV Peano); linewise
  second derivatives + polarisation do NOT suffice; the signed-measure bias in `L¹` is the sup over `‖F‖∞ ≤ 1` of the
  scalar bias with F-UNIFORM remainder/tail constants (`‖f‖₁ = sup_F |∫Ff|`). Rank 2: reconstruction as a smooth retraction
  `R(d) = q_{m(d)}`, `DR_d[h] = q_M ℓ_{M,∫Sh}`, `R∘R = R`, `m∘R = m`, `P_M² = P_M`, `ker P_M = {∫h = 0, ∫Sh = 0}`; Fisher
  contraction only at `Q_M` (from general `D` needs `Cov_D(S) ⪯ C_M`). Rank 3: whole-law transport + invisible acceleration.
  Rank 4: all-orders invisible tower. Closing main theorem proposed ("Response geometry: projection, invisible bending,
  averaged curvature"; five parts, most landed). NEXT: `UniformBias` — the F-uniform scalar bias (dual form of the `L¹`
  signed-measure bias): restate the observable Peano with `∀ F` inside the `∃ δ`, bound `|lin_F(e_a)| ≤ BF ∫|ℓ|`,
  `|b_F(e_a,e_b)| ≤ BF ∫|N(ℓℓ)|`, and rerun the schema with `K = BF · K₀`.
- `UniformBias` landed (round-63 rank 1, dual form): the bias limit is uniform over the unit ball of bounded observables,
  from the observable-uniform Peano (copy of `integral_response_peano_uniform`'s proof with `F` quantified inside `∃ δ`) and
  the trivial bounds `|lin_F| ≤ ‖F‖∞ ∫|ℓ|`, `|b_F| ≤ ‖F‖∞ ∫|N(ℓℓ)|` (via `N` self-adjoint); the schema's constant becomes
  `‖F‖∞ · K₀`. Gotcha: `∀ {F} (hF : Bdd F) {BF} (hBF : …)` in a statement trips the unused-binder linter when `hBF` is not
  referenced in the conclusion — write `(∀ x, |F x| ≤ BF) →` anonymously. NEXT: (i) the closing package theorem in the
  consult's five-part form (parts 1–5 assembled from landed pieces: `hasDerivAt_reconstructionL1_curve`/`ResponseTransport`
  for whole-law transport, `SecondOrderTransport` for bending, `UniformBias` for averaged bending, `NaturalGradientAtlas`);
  (ii) rank 2 retraction differential `R(d) = q_{m(d)}`, `DR_d[h] = q_M ℓ_{M,∫Sh}`; (iii) the `L¹` Bochner form of the bias.
- `ResponseGeometry` landed (round-63 closing theorem): the exact invisibility identity (mass via `integral_famDens` +
  `integral_responseScore`; feature moments via `integral_famDens_mul` + `integral_stat_responseTheta` +
  `moment_famDens_mul_responseScore`) and the five-part `response_geometry` package (pure assembly of
  `responseProjection_eq_familyMeasure_responseTheta`, `integral_stat_responseTheta`, `responseProjection_mean_familyMeasure`
  (called as `hS ν θ` with `S' := S`), `hasFDerivAt_reconstructionL1`, `famDens_mul_responseScore_moment_eq`,
  `integral_response_sub_featureless_eq_integral_atlas`, `obsResponse_atlas_eq_second_order`,
  `reconstruction_bias_uniform_of_nhd`, `natFlow_zero ν _`, `hasDerivAt_natFlow ν _`, `tendsto_natFlow ν _`,
  `hasDerivAt_natLoss_natFlow`). Gotchas: `integral_sub` needs the `Integrable (fun x ↦ f x - g x)` witness typed as a
  lambda (`Integrable.sub` gives the Pi form); a theorem in an `include hrel` section whose proof uses `hrel` takes it as an
  argument even when the STATEMENT does not mention it (`integral_deviation_eq_zero hS ν hrel h`); the NaturalGradientAtlas
  flow lemmas omit `hS`, so they are `natFlow_zero ν Mt` etc. NEXT: (i) rank 3 whole-law `L¹` transport / invisible
  acceleration in Bochner form (`hasDerivAt_reconstructionL1_curve` + FTC in `L¹`, `atlasHess` domination); (ii) the tilt
  diagnostic `tR'(t) = R(t) + KL(ν‖D_t) − KL(ν‖Q_{M_t})`; (iii) Bochner `L¹` form of the bias; (iv) round-64 consult.
- `DataRetraction` landed (round-63 rank 2): the response map as a map on `L¹(ν)`, `R(d) = [q_{m(d)}]`, is a differentiable
  retraction of the fixed-mass affine subspace with `DR_d[h] = Dp_{m(d)}(π ∫ S h dν)`, `R∘R = R`, `m∘R = m`, `DR∘DR = DR`,
  `ker DR = {∫ S h = 0}`, visible/invisible splitting, chain rule along data paths. Gotchas: a `def` in an `include hS` section
  whose statement and body do not mention `hS` drops it (`dirProjL S ν` needs `variable (S) in`; theorems about it need
  `omit hS in`); `Integrable.bdd_mul (c := …) (f := …)` must have both named or `abs_sub` leaves `(fun x ↦ ?m) x`; a `set f := fun x ↦
  (…) • (…)` on `J → ℝ` in a long proof caused whnf/isDefEq timeouts — use `obtain ⟨f, hf⟩ : ∃ f, f = … := ⟨_, rfl⟩` and
  `rw [hf]` where needed; `integrable_pi_iff` for vector-valued integrands; `ContinuousLinearMap.integral_comp_comm` twice
  (`ι ∘ P`) shows an a.e.-`𝕍`-valued integrand integrates into `𝕍`; `HasFDerivWithinAt.comp_hasDerivWithinAt` needs
  `(s := univ) (l := …) (f := …) (x := …)` named, then `hasDerivWithinAt_univ`; `L1.norm_eq_integral_norm`,
  `Lp.coeFn_add/smul/zero`, `Integrable.coeFn_toL1`, `LinearMap.mkContinuousOfExistsBound`. NEXT: Bochner `L¹` whole-law
  transport (`reconstructionL1 M − reconstructionL1 m₀ = ∫₀¹ Dp_{M_s} δ ds`, the `hftc` inside `integral_abs_famDens_curve_le`,
  factor it out), tilt diagnostic `tR'`, round-64 consult.
- `TransportL1` + `TiltDiagnostic` landed. TransportL1: the Bochner FTC factored out of `integral_abs_famDens_curve_le`;
  the atlas as a `𝕍`-valued curve is `s ↦ dirProjL S ν (atlasPath s − m₀)` (derivative via `(dirProjL S ν).hasFDerivAt.comp_hasDerivAt`,
  `Subtype.ext` + `dirProjL_of_mem`); `simp only [hcoe, atlasPath_one] at h` rewrites inside-out and kills the outer pattern —
  do `rw [hcoe 1, hcoe 0, atlasPath_one, atlasPath_zero] at h` then `simp only [hcoe] at h` for the binder occurrence.
  TiltDiagnostic: `hasDerivAt_integral_of_dominated_loc_of_deriv_le` with ball radius `min s₀ (1 − s₀)` so the bridge bounds
  apply; `hasDerivAt_klFun (hx : x ≠ 0)` composed with `((hasDerivAt_id s).mul_const h).const_add 1`; `toReal_klDiv_densLaw`
  and `toReal_klDiv_densLaw_symm` (MixturePathEnergy) give `A = ∫ klFun r`, `KL(ν‖D) = ∫ (r − 1 − log r)`; the Euler identity
  is a pointwise `ring` after `← integral_const_mul, ← integral_sub`; `toReal_klDiv_familyMeasure_symm` + `atlasPath_sub` +
  `dotJ_smul_right` give the rate Euler identity; `Pfam (atlasTheta … : J → ℝ)` needs the explicit coercion or instance
  search sticks; `meanMap_responseTheta … hrel` is accepted by `exact` for `meanMap … (atlasTheta …)` (defeq). Round-62/63
  lists now fully landed except the all-orders tower. NEXT: round-64 consult (what remains for depth: all-orders invisible
  tower via smooth inverse function theorem, Fisher contraction `Cov_D(S) ⪯ C_M`?, CLT of the reconstruction law, geodesic
  vs atlas), or the tower directly.
- Round-64 consult landed (`research_round64_{q,v1}`). Ranking: 1 = GLOBAL NORMAL FORM of the retraction
  `U ≃ Ω × K`, `Φ(d) = (m(d), d − p(m(d)))`, `Φ⁻¹(M,k) = p(M) + k`, `R(M,k) = (M,0)` (C¹ from DataRetraction + `m∘p = id`),
  plus curved-path second-order transport `d²/dt² p(m(d_t)) = H[Ṁ,Ṁ] + J M̈` (needs `p ∈ C²`); 2 = exact KL splitting against
  EVERY family member `KL(d‖q_N) = KL(d‖q_M) + KL(q_M‖q_N)` (route: `log(q_M/q_N)` affine in `S`, so `E_d = E_{q_M}`), uniqueness
  of both minimisers, and Fisher orthogonality at `q_M`: `⟨J_M u, k⟩_{q_M} = ∫ ℓ_u k dν = 0` for `∫k = 0 = ∫Sk`, `⟨J u, J v⟩ = g(u,v)`,
  so `DR_{q_M}` is the Fisher-orthogonal projection onto the family tangent (NOT a submersion at general `d`); 3 = smooth tower via
  the BOOTSTRAP `θ' = A(θ)⁻¹δ` (`C^r ⇒ C^{r+1}`), recursions `v_k = −A⁻¹ Σ_{|π|≥2} K_{|π|}[v_{|B_i|}]`, `a_j = ⟨v_j, T − μ_s⟩ − (j−1)⟨δ, v_{j−1}⟩`,
  `P_{k+1} = ∂P_k + ℓ P_k` (Bell polynomials); 4 = Chernoff `P(⟨θ(M), M̂_n⟩ ≥ ⟨θ(M), M⟩) ≤ e^{−n𝓘(M)}`. Sanity: signed base
  points fine; state identities on the fixed-mass interior-response set; `‖DR h‖₁ ≤ √g(m̄(h), m̄(h))` notation. NEXT: rank 2
  (FibreOrthogonality), then rank 1 normal form, then Chernoff, then the bootstrap tower.
- `FibreOrthogonality` landed (round-64 rank 2). Gotchas: `responseScore`/`responseTheta` need `[Nonempty X]` and `[Nonempty J]`
  (an `omit` of either fails with "cannot omit referenced section variable"); `Integrable.toL1 f` takes the function
  EXPLICITLY (`hf.toL1 (fun x ↦ …)`, an `_` leaves `NormedAddCommGroup ?m` stuck); `sub_mul` before `Finset.sum_mul` when
  distributing `(a − ∑ f) * k`; `klDiv_self` + `ENNReal.toReal_zero` turn `toReal_klDiv_tilted_right ν Q_M … (−dirLoss θ_M)` into
  the closed form of `KL(Q_M‖ν)`; `ENNReal.toReal_eq_toReal_iff' h1 h2` + `ENNReal.toReal_add` lift a real identity to `ℝ≥0∞`;
  `ENNReal.add_right_inj (h : a ≠ ⊤)` for cancellation; `klDiv_eq_zero_iff` for uniqueness. NEXT: round-64 rank 1 (global
  normal form `Φ(d) = (m(d), d − p(m(d)))`, `Φ⁻¹(M,k) = p(M) + k`, `U ≃ Ω × K`, both directions differentiable within the
  fixed-mass set; needs `∫ reconstructionL1 M = 1`), then Chernoff (rank 4), then the bootstrap tower (rank 3).
- `NormalForm` landed (round-64 rank 1). Gotchas: `invisibleSet` already exists (QuotientMeanMap) — the `L¹` set is
  `invisibleDirs hS ν`; `HasFDerivWithinAt.comp` needs `(g := …) (f := …) (t := …) (s := …)` named when composing with
  `Prod.fst` (`hasFDerivWithinAt_fst`), else the unifier cannot see through `fun Mk ↦ p Mk.1`; `HasFDerivWithinAt.prodMk`
  for the pair; `(CLM).hasFDerivWithinAt` for the linear parts; `HasFDerivWithinAt.mono` to shrink the fixed-mass set to
  `dataSet`; `abel`/`abel_nf` close the `p + (d − p) = d` and `p + k − p = k` identities in `L¹`. NEXT: round-64 rank 4
  Chernoff (`P(⟨θ(M), M̂_n⟩ ≥ ⟨θ(M), M⟩) ≤ e^{−n𝓘(M)}` via `measure_ge_le_exp_mul_mgf` and `mgf` of iid sums), then rank 3
  bootstrap smoothness of `θ(M)`, then round-65.
- `ResponseChernoff` landed (round-64 rank 4; note the seabed ALREADY had `HalfspaceChernoff`, `HalfspaceProjection`,
  `CompactCoverCramer` — grep before planning LD work). Gotcha: `Set.mem_setOf_eq` is deprecated (`Set.mem_ofPred_eq`).
  Round 64: ranks 1, 2, 4 DONE. NEXT: rank 3, the smooth bootstrap — plan: (i) `θ ↦ ∫ g e^{−⟨θ,S⟩} dν` is `ContDiff ℝ n` for
  every bounded `g` by induction on `n` with `contDiff_succ_iff_fderiv` (fderiv = −Σ_j (∫ g S_j e^{…}) • proj_j, same class);
  (ii) `famZ`, `meanMap`, the covariance operator `A(θ)` smooth; `A(θ)⁻¹` smooth via `contDiffAt_ring_inverse`; (iii)
  bootstrap on `Ω₀ = {z ∈ 𝕍 | m₀ + z ∈ Ω}` (open in `𝕍`): `Θ(z) = θr (m₀ + z)`, `fderivWithin Θ = A(Θ)⁻¹`, so `C^n ⇒ C^{n+1}`
  by `contDiffOn_succ_iff_fderiv_of_isOpen`; (iv) then `s ↦ [q_{M_s}]` smooth in `L¹` and all-orders invisibility.
- `SmoothFamily` landed (rank 3 stage A). Gotchas: the induction `contDiff_famNum (n) : ∀ {g}, Bdd g → ContDiff ℝ n (famNum g)`
  generalises over `g` (the derivative involves `g S_j`); `contDiff_succ_iff_fderiv` after `rw [Nat.cast_succ]`, its `n = ω`
  clause is `fun h ↦ absurd h (WithTop.natCast_ne_top n)`; `fderiv` is identified pointwise by `(hasFDerivAt …).fderiv` and
  `dotCLMlin_apply` so the derivative reads `θ ↦ −dotCLMlin (V θ)` (a CLM composed with a `contDiff_pi` vector); `ContDiff.div`
  needs `∀ θ, famZ θ ≠ 0`; `contDiff_infty_iff_fderiv` gives smoothness of `fderiv` = `meanMapDeriv` (`hasFDerivAt_meanMap` needs
  `hZ : priorZ … ≠ 0` from `famZ_eq_priorZ ν`); `contDiff_clm_apply_iff` (finite-dim domain) reduces `θ ↦ chartDeriv θ` to
  vectors; `contDiffAt_map_inverse (n := ∞) (CDE θ₀)` + `coe_chartDerivEquiv` + `ContinuousLinearMap.inverse_equiv` give the
  smooth inverse; deprecations `ContinuousLinearMap.smul_apply/neg_apply` → root `smul_apply/neg_apply`. NEXT (stage B,
  `SmoothChart`): `U = range chartV` open via `HasStrictFDerivAt.map_nhds_eq_of_equiv`; `fderiv chartVInv = (CDE ∘ chartVInv).symm`
  on `U`; bootstrap `ContDiffOn n chartVInv U` by `contDiffOn_succ_iff_fderiv_of_isOpen`; then `z ↦ θr (m₀ + z)` and the atlas
  coordinate `s ↦ atlasTheta s` are `C^∞`, and observable responses `G_F ∘ atlas` are `C^∞` on `(0,1)`.
- `SmoothChart` landed (rank 3 stage B). Gotchas: openness of `range chartV` from `HasStrictFDerivAt.map_nhds_eq_of_equiv`
  (rewrite `chartDeriv θ₀ = ↑(CDE θ₀)` with `← coe_chartDerivEquiv` first) + `Set.image_univ` + `Filter.image_mem_map univ_mem`;
  the bootstrap step is `(contDiffOn_succ_iff_fderiv_of_isOpen hU).2 ⟨diffOn, fun h ↦ absurd h (WithTop.natCast_ne_top n),
  ((G.of_le (by exact_mod_cast natCast_le_infty n)).comp_contDiffOn ih).congr (fderiv formula)⟩`; `responseTheta M =
  chartVInv (toV M)` and `toV (m₀ + z) = z` by `Subtype.ext` + `toV_apply` + `add_sub_cancel_left`; the atlas is
  `(fun z ↦ θr (m₀ + z)) ∘ (s ↦ s • atlasInc)` (`ContDiffOn.comp` with the `MapsTo` from `atlas_mem_intrinsicInterior`).
  Round 64: ranks 1–4 ALL DONE (rank 3 as smoothness; the explicit Bell/Faà-di-Bruno tower and the all-orders invisibility in
  density form remain unformalised). NEXT: round-65 consult with the full picture; candidates: all-orders invisibility in
  density form (`iteratedDeriv k (fun s ↦ ∫ (1,S) q_{M_s})=0`, k ≥ 2, needs differentiation under the integral to all
  orders — the `famNum` induction gives it for free since `s ↦ q_s(x)` and `s ↦ ∫ g q_s` are both smooth); curved-path
  second-order transport; analyticity.
- `InvisibleTower` landed (the round-63/64 "all-orders invisible tower", in Bochner `L¹` form). Gotchas: `Lp.ext` + a.e.
  `Lp.coeFn_neg/coeFn_finsetSum/coeFn_smul` (with `eventually_all` over the finite index) + `Integrable.coeFn_toL1` identify a
  finite `L¹` combination pointwise; `Integrable.toL1_sub` twice then `Integrable.toL1_eq_toL1_iff` for the remainder identity;
  `hasFDerivAt_iff_isLittleO_nhds_zero` + `IsBigO.of_bound` + `isLittleO_norm_pow_id (E' := …) one_lt_two` turn a quadratic
  remainder bound (on a ball where `B‖η‖ ≤ 1`) into the derivative; `Real.abs_exp_sub_one_sub_id_le` needs `|x| ≤ 1`;
  `ContinuousLinearMap.smulRightL ℝ E F (proj j)` is the CLM `W ↦ (proj j).smulRight W` (its application is `rfl`);
  `famWeight_pos θ x` has `S` implicit; set-builder sets cannot be `local notation` (define `atlasDomain S ν M`);
  `ContinuousLinearMap.iteratedFDerivWithin_comp_left L (hf.contDiffWithinAt hs) hU.uniqueDiffOn hs (i := k) (cast ≤ ∞)` +
  `iteratedDerivWithin_eq_iteratedFDerivWithin` + `Function.comp_def` give `L (iteratedDerivWithin k f U s) =
  iteratedDerivWithin k (L ∘ f) U s`; higher `iteratedDerivWithin` of an affine curve vanish via `iteratedDerivWithin_succ`,
  `derivWithin_congr`, `derivWithin_fun_const _ _`; `L1.integralCLM f = ∫ f` by `← L1.integral_eq, L1.integral_eq_integral`.
  NEXT: round-65 consult (what remains: curved-path second-order transport `q̈ = H[Ṁ,Ṁ] + JM̈` now cheap from `contDiff_densL1`
  and the smooth chart; analyticity; the explicit Bell/cumulant recursion for the tower; the `L¹` bias in Bochner form).
- Round-65 consult landed (`research_round65_{q,v1}`). Ranking: 1 = explicit global Hessian `D²p_M[u,v] = [q_M N_M(ℓ_uℓ_v)] ∈ K`,
  `D²R_d[h,k] = H_{m(d)}[m(h), m(k)]`, curved-path `d²/dt² p(M_t) = H[Ṁ,Ṁ] + J M̈`, and the `C^∞` upgrade of the normal form
  (route: polarisation from `atlasHess` lifted to `L¹`, second-order chain rule); 2 = constructive featureless jets with `L¹`
  Taylor remainder: `p'(0) = [ℓ]`, `p''(0) = [N(ℓ²)]`, `p'''(0) = [N(ℓ³ − 3ℓr)]` (`r = ⟨b, X⟩`, `b = C⁻¹E[Xℓ²]` = the bend),
  `f^{(k)}(0) = E_ν[F P_k]`, and `‖p(s) − Σ_{j≤n} s^j/j! p^{(j)}(0)‖₁ ≤ s^{n+1}/(n+1)! sup‖p^{(n+1)}‖₁` (controls all bounded
  observables at once); 3 = quantitative local analyticity + finite-step continuation (contraction + majorant for the inverse);
  4 = boundary completion (finite sample space: the section extends continuously to the polytope; FALSE in `L¹` for general
  bounded features); 5 = reconstruction CLT (delta method). Sanity: the normal form is for SIGNED unit-mass densities
  (probability densities are the constrained subset `p(M) + k ≥ 0`); normal-form derivatives are tangent maps on the affine
  tangent space; `invisible_tower` correct for affine paths, for curved paths `m(p^{(k)}) = M^{(k)}`; "maximal entropy" = maximal
  RELATIVE entropy w.r.t. the reference. NEXT: `FeaturelessTaylor` — pairing CLM `obsL1`, duality lemma (`L¹` element killed by
  all bounded observables is 0), `p''(s) = [atlasHess s]` in `L¹` via duality + `hasDerivAt_deriv_obsResponse_atlas`, and the
  `L¹` Taylor remainder on `[0,1]` via `taylor_mean_remainder_bound`; then the Hessian in all directions by polarisation.
- `AtlasJetL1` landed (round-65 rank 2, minus the explicit `p'''(0)`). Gotchas: the sign observable `F = if 0 ≤ f x then 1 else −1`
  (measurable via `Measurable.ite (measurableSet_le measurable_const hm)`) gives `∫ F f = ∫ |f| = ‖f‖₁` and hence duality;
  after `rw [hF]` on a `set`/`obtain`-defined function the goal is a beta-redex — `beta_reduce` before `split_ifs`/`rw [sq]`;
  `hasDerivAt_reconstructionL1_curve` needs `(γ := …) (γ' := …) (t := s)` named (higher-order unification); `iteratedDeriv 2 g =
  deriv (deriv g)` by `iteratedDeriv_succ, iteratedDeriv_one`; `iteratedDerivWithin_of_isOpen hU hs` converts the InvisibleTower
  `Within` statements to `iteratedDeriv`; `taylor_mean_remainder_bound (C := …)` needs its bound named;
  `iteratedDerivWithin_eq_iteratedDeriv uniqueDiffOn_Icc_zero_one (contDiffAt) (left_mem_Icc.2 zero_le_one)` turns the Taylor
  coefficients into ordinary `iteratedDeriv k p 0`; an `(hF : Bdd F)` binder unused in the conclusion must be anonymous `Bdd F →`.
  NEXT: the featureless values `p(0) = [1]`, `p'(0) = [ℓ_{m₀,δ}]`, `p''(0) = [N_{m₀}(ℓ²)]` (the last via the second-order Peano
  expansion `integral_response_peano_biasForm` + `taylor_isLittleO` + uniqueness of Peano coefficients, since
  `hasDerivAt_deriv_obsResponse_atlas` is only on `(0,1)`), then the explicit second-order featureless expansion for observables;
  then round-65 rank 1 (Hessian in all directions by polarisation) or rank 3/4.
- `FeaturelessJet` landed (round-65 rank 2 complete except `p'''(0)`). Gotchas: `p''(0)` cannot come from
  `hasDerivAt_deriv_obsResponse_atlas` (only on `(0,1)`); use the TV Peano `isLittleO_integral_famDens_response_peano hS ν hrel₀`
  composed with `s ↦ s • δ` (`IsLittleO.comp_tendsto`, `‖s•δ‖² = O(s²)`), pair with `F` (`abs_integral_le_integral_abs` +
  `integral_mono` — `norm_integral_le_of_norm_le` gets stuck on `NormedSpace ℝ ?m` unless `(f := …)` is given), and compare with
  `taylor_isLittleO (convex_Icc 0 1) (left_mem_Icc.2 zero_le_one) hf` paired via `(obsL1 ν hF).isBigO_comp _ _ |>.trans_isLittleO`;
  the difference is `0·s + b s²` (`simp only [Finset.sum_range_succ, Finset.sum_range_zero, hc0, hc1, Nat.factorial]; push_cast;
  ring` inside `IsLittleO.congr_left`), and `eq_zero_of_isLittleO_sq` (via `IsLittleO.tendsto_div_nhds_zero` + `tendsto_nhds_unique`
  on the `NeBot` filter `𝓝[Ioo 0 1] 0`, from `mem_closure_iff_nhdsWithin_neBot` + `closure_Ioo`) finishes; `field_simp` closes
  `(a s + b s²)/s = a + b s` outright but needs `ring` for `(0 s + b s²)/s² = b`; lemmas in an `include hrel` section whose
  statement mentions only `M` via the local notation need `(M := M)` at call sites. Round 65: rank 2 DONE (modulo `p'''(0)`),
  rank 4 (`ResponseChernoff`) done earlier as part of round 64. NEXT: rank 1 — the Hessian of `p` in all directions
  `D²p_M[u,v] = [q_M N_M(ℓ_uℓ_v)]` by polarisation from the affine lines through `M` (re-centred atlases) plus the second-order
  chain rule for curved paths; or rank 3 (analyticity: contraction + majorant for the inverse mean map).
- `ResponseHessian` landed (round-65 rank 1, the explicit invisible Hessian). Gotchas: set-builder sets and projections
  (`(…).smulRight`) cannot be `local notation` — use defs (`addDomain S ν M`, `lineCLM ν w`); a `variable {w : 𝕍}` line in a
  nested section must spell `dirSpan ν (fun _ ↦ 1) S` (the local notation yields "Unknown constant ν✝"); the diagonal Hessian
  along a line uses `ContinuousLinearMap.iteratedFDerivWithin_comp_right (lineCLM ν w) hP hU.uniqueDiffOn hpre.uniqueDiffOn hx
  (i := 2) (cast)`, `ContinuousMultilinearMap.compContinuousLinearMap_apply`, `iteratedFDerivWithin_eq_iteratedFDeriv`,
  `iteratedFDeriv_two_apply`; symmetry from `ContDiffAt.isSymmSndFDerivAt` with `minSmoothness_of_isRCLikeNormedField`; the
  general direction by rescaling `c = r/(2(‖u‖+1))` into the ball of `Metric.isOpen_iff`, bilinearity `map_smul, map_smul,
  smul_apply, smul_smul` (root `smul_apply`), `LinearMap.map_smul₂`; polarisation `simp only [map_add, add_apply]` then
  `hsymm v u`, `two_smul`, `abel`; coercions of `u + v`/`c • u` must be written `((u + v : 𝕍) : J → ℝ)` to match
  `Submodule.coe_add/coe_smul`. Round 65: ranks 1 (Hessian; curved-path chain rule still open), 2, 4 DONE. NEXT: the curved-path
  second-order transport `(P∘γ)'' = D²P[γ',γ'] + DP[γ'']` (assembly from `contDiffAt_reconstructionL1_add` + `HasDerivAt.clm_apply`),
  the `C^∞` upgrade of NormalForm, then round-66 consult (analyticity / boundary completion / CLT).
- `CurvedTransport` landed (round-65 rank 1 complete: Hessian everywhere + curved-path chain rule). Gotchas: no
  `fderiv_comp_sub_const` in Mathlib — proved `fderiv_comp_sub_const'` by cases on differentiability (`DifferentiableAt.comp (x - a)
  (g := …) (f := fun y ↦ y + a)` for the converse); a rebased map `fun z ↦ f (z − z₀)` must be STATED with `((z − z₀ : 𝕍) : J → ℝ)`
  and the lemma instantiated with an explicit `(fun w ↦ …)` then `beta_reduce at h` before `rw`; `HasFDerivAt.comp_hasDerivAt`
  takes the point FIRST (`comp_hasDerivAt t (l := P) (f := γ) hl hf`); the second derivative of `t ↦ DP(γ t)(γ' t)` is
  `(HasFDerivAt.comp_hasDerivAt t₀ hP2 (hγ t₀)).clm_apply hγ'` with `hP2` from `ContDiffAt.fderiv_right_succ` after `.of_le
  (cast 2)`; `variable {γ : ℝ → 𝕍}` lines must spell `dirSpan ν (fun _ ↦ 1) S`. Round 65: ranks 1, 2, 4 DONE. NEXT: `C^∞`
  upgrade of `NormalForm` (assembly), then round-66 consult (analyticity via contraction + majorant; boundary completion for finite
  `X`; reconstruction CLT; explicit `p'''(0)`).
- `SmoothNormalForm` landed (assembly; no new gotchas — `ContDiffOn.comp` with a `MapsTo` from the set membership, `prodMk`,
  `contDiffOn_fst/snd`, and `rfl` unfoldings of `normalForm`/`normalFormInv`). Round 65: ranks 1, 2, 4 fully DONE. NEXT: round-66
  consult — remaining candidates: analyticity of the response chart (contraction + majorant), boundary completion for finite `X`,
  reconstruction CLT (delta method; Mathlib CLT status?), explicit `p'''(0)` / cumulant recursion, and anything deeper.
- Round-66 consult landed (`research_round66_{q,v1}`). Ranking: 1 = QUANTITATIVE ANALYTIC RESPONSE ATLAS (real-analyticity of
  `P : Ω → L¹` via complexified local tilt around `Q_M`, contraction `η = G⁻¹z − G⁻¹(h(η) − Gη)` with radius `r = cλ²/L³`;
  uniform charts along the compact atlas; cheap pre-theorem: explicit bounds `‖p'‖₁ ≤ D/√λ`, `‖p''‖₁ ≤ LD²/λ^{3/2}`,
  `‖p'''‖₁ ≤ 4L²D³/λ^{5/2}`); 2 = finite-`X` FACE COMPLETION (continuous retraction of the whole simplex onto the completed
  family, smooth on strata, KL splitting, feasible recovery sequences); 3 = MOVING NORMAL PROJECTION + THIRD JET (short):
  `d/ds (N_s f_s) = N_s f_s' − L_s(ℓ_s N_s f_s)`, `d/ds [q_s N_s f_s] = [q_s N_s(f_s' + ℓ_s N_s f_s)]`, `ℓ' = −c − r`,
  `p'''(s) = [q_s N_s(ℓ³ − 3ℓr)]`; or "projection after differentiation": `q'''/q = ℓ³ + 3ℓℓ' + ℓ''` is already normal (k ≥ 2
  invisible), so apply `N_s` and kill the affine `ℓ''` and the `cℓ` term; tower `H_{k+1} = N_s(H_k' + ℓ H_k)`; 4 = reconstruction
  CLT (`√n(P(M̂_n) − P(M)) ⇒ [q ℓ_Z]`, second order `n(…) ⇒ ½[q N(ℓ_Z²)]`; finite-dim CLT + delta method). Sanity: global
  `fderiv` at locally smooth points is fine; curved paths need only local interior membership; the normal form is for SIGNED
  unit-mass data (positivity constrains the kernel slices). NEXT (per Astra): land 3 (third jet) via "projection after
  differentiation": the L¹-derivative = pointwise-derivative principle (L¹ convergence ⇒ a.e. subsequence), the pointwise
  `q''' = q(ℓ³ + 3ℓℓ' + ℓ'')` with `ℓ'' ` affine in `S` (smoothness of `s ↦ atlasVel s`), then `N` of the affine part vanishes;
  then the quantitative bounds; then analyticity (flagship) and face completion (capstone).
- `L1PointwiseDeriv` + `ThirdJet` landed (round-66 rank 3 DONE). Principle: `coeFn_hasDerivAt_L1_ae` (eventual representatives
  near `s₀`; sequence `s₀ + ε/2·(1/(n+1))` inside the `Metric.eventually_nhds_iff` ball; `hasDerivAt_iff_tendsto_slope` ∘ sequence,
  `tendstoInMeasure_of_tendsto_Lp (p := 1)`, `.exists_seq_tendsto_ae`, `slope_def_module` + `Lp.coeFn_smul/sub`, `ae_all_iff`,
  `tendsto_nhds_unique`). Third jet: `s ↦ atlasVel s` is `C^∞` on `atlasDomain` (`contDiff_chartDerivEquiv_symm.comp_contDiffOn
  contDiffOn_atlasTheta |>.clm_apply contDiffOn_const`), `β' := deriv atlasVel`, `β'' := deriv (deriv atlasVel)` via
  `contDiffOn_infty_iff_deriv_of_isOpen`; `atlasVelD = atlasAccel` on `[0,1]` by `(hasDerivAt_atlasVel …).deriv`; pointwise
  `q''' = q(ℓ³ + 3ℓℓ' + ℓ'')`; `p''' = deriv (iteratedDeriv 2 p)` from `iteratedDeriv_succ` twice + `iteratedDeriv_one` (state the
  equalities `e2`, `e3` as `have`s, never bare `rw [iteratedDeriv_succ]` on a goal with two matches); apply the principle to
  `f := iteratedDeriv 2 p`, `φ := atlasHess'` (`= atlasHess` on `(0,1)` by `iteratedDeriv_two_reconstructionL1_atlas`);
  `invisible_tower` k = 3 gives zero mass/moments, so `q H₃ = q N H₃` pointwise (`famDens_mul_normalProj_of_invisible`);
  `H₃ = (ℓ³ − 3ℓr) + responseScore(u) + const` with `u = (−3c)•δ + CDE β''`, killed by `normalProj_add/const/responseScore`.
  Gotchas: `HasDerivAt.mul` on lambdas yields Pi products — `simp only [Pi.mul_apply, Pi.add_apply]` before `unfold; ring`;
  `rw [normalProj_add hS ν _ _ x]` leaves `Bdd` side goals — name the bounded proofs (`hA1`, `hA2`) and pass them; a `rw` with
  `← atlasScore_eq_responseScore` needs `hS ν hfin`; `Integrable.toL1_eq_toL1_iff f g hf hg`. Round 66: rank 3 DONE. NEXT: rank 1
  cheap pre-theorem (explicit `‖p^{(k)}‖₁` bounds in terms of `λ`, `L`, `D`) then the analytic atlas (contraction + majorant;
  check Mathlib for `HasFPowerSeriesAt` inverse-function API), then rank 2 face completion (finite `X`), rank 4 CLT.
- `QuantitativeJets` + `CubicRemainder` landed (round-66 rank 1 pre-theorem DONE): explicit `‖p'‖₁ ≤ D/√λ`, `‖p''‖₁ ≤ LD²/λ^{3/2}`,
  `‖p'''‖₁ ≤ 4L²D³/λ^{5/2}` and the cubic remainder `(4L²D³/λ^{5/2}) s³/6` with Lagrange's `1/3!` (via pairing with `|F| ≤ 1`,
  `taylor_mean_remainder_lagrange` on the REAL response, then norm duality `norm_L1_le_of_forall_integral_mul_le`). Hypotheses:
  `hcov : ∀ v : 𝕍, λ⟨v,v⟩ ≤ lawCov Q_s (dirLoss v)(dirLoss v)`, `hSb : ∀ x, ⟨M_s − S x, M_s − S x⟩ ≤ L²`, `⟨M−m₀,M−m₀⟩ ≤ D²`
  (Euclidean `dotJ`; uniform in `t ∈ [0,1]` for the remainder). Gotchas: local notations (`𝕍`, `Pfam`, `m₀`) inside a `variable`
  line give "Failed to infer binder type"/panics — spell them out; `rw [lemma_with_Prop_arg]` where the Prop arg is a `{g}`-dependent
  `hg : Bdd g` leaves an unassigned `case hg` goal (proof irrelevance blocks assignment) — pass `hg` explicitly; `rw [e] at h` with
  `e : a = √a * √a` rewrites the `a` inside `√a` too — rewrite the goal side with `Real.mul_self_sqrt` instead; `abs_of_nonneg
  (sq_nonneg _)` in a `rw` list picks the first `|·|` — give the argument; `rw [taylor_within_apply, sub_zero]` already kills
  `(s − 0)`; `Real.sqrt_div (hx : 0 ≤ x) y`, `Real.sqrt_mul (hx) y`, `pow_le_pow_left₀`. Round 66: ranks 3, 1-pre DONE. NEXT:
  rank 1 flagship (analyticity of `P : Ω → L¹`; grep Mathlib `HasFPowerSeriesAt`/`AnalyticAt` inverse-function API first), rank 2
  face completion (finite `X`), rank 4 CLT.
- Round-67 consult landed (`research_round67_{q,v1}`). Route for the ANALYTIC ATLAS: (1) analytic tilt via the Banach algebra
  `A = C(K, ℝ)`, `K = closedBall (0 : J → ℝ) R` (compact): `featureCLM : (J → ℝ) →L A`, `h ↦ (z ↦ −⟨h,z⟩)`; `T_g : A →L L¹`,
  `u ↦ [g (u ∘ S₀)]` with `S₀ : X → K`; `weightL1 θ = T_g (NormedSpace.exp (featureCLM θ))` (evaluate `exp` through the
  evaluation ring hom, `NormedSpace.map_exp`, `Real.exp_eq_exp_ℝ`); analyticity by `ContinuousLinearMap.analyticAt`,
  `NormedSpace.exp_analytic`, `AnalyticAt.comp`; scalar `famNum` by `L1.integralCLM`; (2) grade-ω inversion by
  `ContDiffAt.to_localInverse` at each point + identification with `chartVInv` through injectivity of `chartV` (eventual
  equality), NOT the successor bootstrap; state results as `AnalyticOnNhd` on OPEN subsets of `𝕍` (`m₀ + 𝕍` coordinates);
  (3) `M ↦ [q_M]` analytic on interior displacements, `s ↦ p(s)` analytic on `atlasDomain`, bounded-observable responses
  analytic. Quantitative: natural-parameter theorem at `Q_a` with `|S − M_a| ≤ L`: `q_{a+h} = q_a e^{−⟨h,T⟩}/E e^{−⟨h,T⟩}`,
  coefficients majorised by `e^{Lt}/(2 − e^{Lt})`, radius `ρ = log(3/2)/L`, `Σ‖A_n‖ρ^n ≤ 3`, remainder `3 (t/ρ)^{N+1}`. Re-ranking:
  1 qualitative analytic atlas; 2 finite-`X` face completion (KL-projection `q*(m)` on `conv S(X)`, continuous moment-preserving
  retraction `R(p) = q*(E_p S)` of the simplex, strong deformation retraction `H_t = (1−t)p + tR(p)`); 3 explicit estimates;
  4 moving-projection tower `B_{k+1} = N_s(∂_s B_k + ℓ_s B_k)`; 5 reconstruction CLT. NEXT: `AnalyticTilt` module.
- `AnalyticTilt` landed (analytic atlas step 1). Gotchas: a `def` in an `include hS` section drops `hS` when unused
  (`featPt hB x`, not `featPt hS hB x`), so downstream `theorem`s that DO use `hS` have it back (`measurable_featPt hS hB`);
  `include hS` at the top does not prevent `unusedSectionVars` warnings for `[Nonempty X]` — `omit [Nonempty X] in` BEFORE the
  docstring on every theorem that does not integrate over a probability space; `isCompact_closedBall` is the exported root name;
  `continuous_eval_const z` is the root `ContinuousEval` lemma; `NormedSpace.map_exp e (continuous_eval_const z) u` with a hand-made
  `RingHom` `v ↦ v z`; `NormedSpace.exp_analytic (𝕂 := ℝ) _`; `ContinuousMap.norm_le _ (nonneg)`, `ContinuousMap.norm_coe_le_norm`;
  `integral_mul_const` (no `integral_mul_right`); `Integrable.toL1_add/smul` reversed inside `map_add'/map_smul'` then
  `Integrable.toL1_eq_toL1_iff`. NEXT: `AnalyticFamily` (mirror `SmoothFamily` at grade ω: famMean, meanMap, meanMapDeriv, chartV,
  chartDeriv, `(CDE θ)⁻¹`), then `AnalyticChart` (grade-ω `to_localInverse` + injectivity ⇒ `chartVInv` analytic on `range chartV`;
  `θ(m₀+z)`, `atlasTheta`, `densL1`, `M ↦ [q_M]` AnalyticOnNhd on addDomain, `s ↦ p s` analytic on atlasDomain, observables).
- `AnalyticChart` landed (round-67 rank 1 DONE: the qualitative analytic response atlas). Gotchas: at grade ω use
  `ContDiff.fderiv_right le_top` (`ω + 1 ≤ ω` is `le_top`), `contDiffAt_map_inverse (n := ω)`, `(ω : WithTop ℕ∞) ≠ 0 := by simp`;
  `hf.to_localInverse hf' hn` with `hf' : HasFDerivAt chV (CDE θ₀ : 𝕍 →L 𝕍) θ₀` (the equiv is inferred), `hf.localInverse hf' hn`
  is DEFINITIONALLY `(hf.hasStrictFDerivAt' hf' hn).localInverse chV (CDE θ₀) θ₀`, so `hstrict.eventually_right_inverse` transfers
  by a typed `have hy' : chV (hf.localInverse hf' hn y) = y := hy` (never `change` with the coerced CLM in the equiv slot: whnf
  timeout); `ContDiffAt.congr_of_eventuallyEq h (hg : f₁ =ᶠ f)` then `.contDiffWithinAt`; `AnalyticOnNhd` from `ContDiffOn ω` on
  an OPEN set via `.contDiffAt (hU.mem_nhds hz) |>.analyticAt`. `[Nonempty J]` is genuinely used (featPt's `0 ≤ B`), so do not
  omit it; `[Nonempty X]` omits only where the linter asks (famMean, meanMap, densL1) — over-omitting errors with "cannot omit
  referenced section variable". NEXT: round-67 rank 2 finite-`X` face completion (KL projection `q*(m)` on `conv S(X)`, continuity,
  moment-preserving retraction `R(p) = q*(E_p S)`, strong deformation retraction), or rank 3 explicit natural-parameter radius
  `ρ = log(3/2)/L` with `Σ‖A_n‖ρ^n ≤ 3`.
- `PointwiseJets` landed (round-67 rank 4 in structural form): `p^{(k)}(s) = [∂_s^k q_s]` for all `k` (induction with the principle,
  `hasDerivAt_iteratedDeriv_of_contDiffOn` from `iteratedDeriv_succ'` + `contDiffOn_infty_iff_deriv_of_isOpen`), Bell tower
  `B_{k+1} = ∂B_k + ℓB_k`, pointwise invisible tower. Gotchas: `coeFn_hasDerivAt_L1_ae` needs `(φ := fun t x ↦ …)` named (the
  representative is not inferable from `?_`); a `def` in a section with `(hfin)` that does not use it must be declared
  `omit hfin in variable (M) in` so that `M` is an explicit argument (`atlasJet hS ν M k s x`); after `rw [hx]` with
  `coeFn_toL1`, close `atlasJet … = iteratedDeriv …` by `rfl`. NEXT: round-67 rank 2 face completion (finite `X`; the seabed
  already has `EntropyCompletion` — unique minimiser `q*(M)` for every finite-rate `M` — and `BoundaryCompletion` — the atlas
  completes at `s = 1`; missing: continuity of `M ↦ q*(M)` on the closed polytope, support = minimal face, the retraction
  `R(p) = q*(E_p S)` of the simplex and the strong deformation retraction), or rank 3 explicit natural-parameter radius.
- Round-68 consult landed (`research_round68_{q,v1}`): FACE COMPLETION (finite `X`, full-support `ν`) without any polyhedral
  continuity theory. Route: (1) all fibres over `C = conv S(X)` are nonempty (image of the simplex under the linear moment map)
  and every `m ∈ C` has finite rate (any probability vector has finite KL against full-support `ν`); (2) MAXIMAL SUPPORT from
  Pythagoras: for `r` feasible at `m`, `KL(r‖ν) = KL(r‖q*(m)) + 𝓘(m) < ∞` ⇒ `r ≪ q*(m)` ⇒ `r_x > 0 → q*(m)_x > 0`;
  (3) additive recovery on the finite simplex: `a_n → r`, `supp r ⊆ supp p` ⇒ `b_n = p + a_n − r ∈ Δ` eventually, `b_n → p`,
  `A b_n = A p + A a_n − A r`; (4) limits of minimisers are minimisers: `m_n → m`, `q*(m_n) → r` (subsequence) ⇒ `A r = m`,
  `supp r ⊆ supp q*(m)`, `b_n` feasible at `m_n`, `D(q*(m_n)) ≤ D(b_n) → D(q*(m))` ⇒ `D(r) ≤ D(q*(m))` ⇒ `r = q*(m)` by
  uniqueness; compactness ⇒ `qStar` continuous, value continuous by composition. (5) support = minimal face via the accessible
  set `J_m = {x | ∃ r feasible at m, r_x > 0}` and an elementary face construction `D = conv S(supp q*(m))`. (6) probability
  VECTORS `stdSimplex ℝ X` as the primary type (compactness, convex combinations), bridge to `responseProjection`; completed
  family = range `qStar` = closure of the interior family, homeomorphic to `C`; retraction `R(p) = q*(E_p S)`, strong deformation
  retraction `H_t = (1−t)p + tR(p)` with `R ∘ H_t = R`. Modules: `FiniteEntropySupport` (bridge, finite rate, maximal support),
  `FiniteCompletionContinuity`, `FiniteMinimalFace`, `FiniteCompletionRetraction`. Explicit radius deferred after face completion.
  NEXT: `FiniteEntropySupport`.
- `FiniteEntropySupport` landed (face completion module 1). Gotchas: the `unusedFintypeInType` linter wants `[Finite X]` (+
  `cases nonempty_fintype X`) on theorems whose TYPE has no `Fintype` sum (measure statements), and `omit [Fintype X] in`;
  `vecMeasure` via `count.withDensity` (singleton value by `withDensity_apply`, `Measure.restrict_singleton`,
  `lintegral_smul_measure`, `lintegral_dirac`, `Measure.count_singleton`), integrals by
  `integral_withDensity_eq_integral_toReal_smul₀` + `integral_count`; `Measure.AbsolutelyContinuous.mk`; `zero_le` has an
  implicit argument; hull ↔ simplex via the seabed's `reachableCoeff_eq_convexHull` + `mem_reachableCoeff_of_mem_stdSimplex`
  (`[Finite J]` + `cases nonempty_fintype J`); `ENNReal.add_ne_top`, `klDiv_ne_top_iff` for `r ≪ q*`. NEXT: module 2
  `FiniteCompletionContinuity`: real entropy `entVec ν p = Σ p x log(p x/ν.real{x})` with the bridge
  `(klDiv (vecMeasure p) ν).toReal = entVec` (rnDeriv of `withDensity`, `llr`, full support ⇒ a.e. = everywhere), continuity
  (`Real.continuous_mul_log`), additive recovery `b_n = p + a_n − r`, limits of minimisers, `tendsto_of_subseq_tendsto` +
  `IsCompact.tendsto_subseq` ⇒ `Continuous (qStarVec)` on the polytope.
- `FiniteCompletionContinuity` landed (face completion module 2, the crux). Gotchas: `isClosed_stdSimplex ℝ X` takes explicit
  arguments; `continuousOn_iff_continuous_restrict` is deprecated → `continuousOn_iff_continuous_domRestrict` (then
  `continuous_iff_seqContinuous` and `tendsto_qStarVec` on `fun n ↦ (u n : J → ℝ)`); `tendsto_of_subseq_tendsto fun ns hns ↦
  ⟨φ, …⟩` with `IsCompact.tendsto_subseq (x := …)`; `ENNReal.mul_div_cancel (ha₀) (ha) : a * (b / a) = b`; the density identity
  `vecMeasure p = ν.withDensity (ofReal p / ν{·})` via `count_withDensity` + `Measure.sum_smul_dirac` and `withDensity_mul` in a
  `calc` (a `conv_rhs` rewrite of `ν` also rewrites inside the density); `Measure.rnDeriv_withDensity ν (f := …)
  (measurable_of_countable _)` then `forall_of_ae_full_support` to make the a.e. identity pointwise; `toReal_klDiv` has the
  `+ ν.real univ − μ.real univ` tail (kill with `probReal_univ`); `IsFiniteMeasure` instances for `vecMeasure (qStarVec …)` and
  `responseProjection` must be `have`d before `measure_ne_top`/`klDiv_ne_top_of_full_support`; `Fintype`-free statements need
  `omit [Fintype X] in … [Finite X] … cases nonempty_fintype X`. NEXT: module 3 `FiniteMinimalFace` (accessible set
  `J_m = {x | ∃ r feasible, r_x > 0}`, `supp q*(m) = J_m`, `x ∈ J_m ↔ S(x) ∈ minimal face`) and module 4
  `FiniteCompletionRetraction` (range qStarVec = closure of the interior family, homeomorphic to the polytope; `R(p) = q*(E_p S)`
  continuous moment-preserving retraction; strong deformation retraction `H_t`).
- `FiniteCompletionRetraction` landed (face completion module 4). Gotchas: `Set.Finite.isCompact_convexHull (𝕜 := ℝ)`; a
  `Homeomorph` between subtypes by `where` fields (`toFun`, `invFun`, `left_inv`, `right_inv`, `continuous_toFun` via
  `ContinuousOn.comp_continuous continuous_subtype_val (fun M ↦ M.2) |>.subtype_mk _`); `convex_stdSimplex ℝ X hp hq ha hb hab`
  unfolds `Convex`/`StarConvex` directly. Round-68 modules 1, 2, 4 DONE. OPEN: module 3 `FiniteMinimalFace` (support of `q*(m)` =
  the minimal face; accessible set `J_m`); "completed family = closure of the interior family" needs `momentBody = conv S(X)`
  for finite full-support `X` (essRange = range statPoint) and density of the relative interior (ray argument via
  `atlas_mem_intrinsicInterior`). NEXT: minimal face, or the explicit natural-parameter radius (round-67 rank 3), or a
  round-69 consult for the next deepening.
- `FiniteMinimalFace` landed (face completion module 3; round-68 package COMPLETE except the closure statement). Gotchas:
  `facePolytope` already exists in `ActiveTruthTheorem` (found only by the umbrella build) → `carriedResponses`;
  `IsExtreme` is a structure `⟨subset, left_mem_of_mem_openSegment⟩` with `openSegment` as `∃ a b, 0 < a ∧ 0 < b ∧ a + b = 1 ∧
  a • x + b • y = z`; `isExtreme_sInter`/`sInter_subset_of_mem`/`subset_sInter` for the minimal face; the absorption parameter
  `ε = ½ min_{supp} q*` via `Finset.exists_min_image` on `univ.filter (0 < q ·)`, nonempty because `Σ q = 1`; after
  `field_simp` the unit-mass goal is `(2 − q x₀)/(2 − q x₀) = 1` (`div_self`). NEXT: the closure statement
  (`completedFamily = closure (interior family)`: needs `momentBody = conv S(X)` for finite full-support `X` and density of the
  relative interior along rays), then round-67 rank 3 (explicit natural-parameter radius) or a round-69 consult.
- `FiniteCompletionClosure` landed: round-68 face completion COMPLETE (five modules). Gotchas: `mem_essRange_iff measurable_const
  (fun _ ↦ one_pos) hS` (section variables `hπm hπ hS`); a finite range is closed (`(finite_range _).isClosed`) and its complement
  open gives the ball missing the range (`Metric.isOpen_iff`); `Set.image_mono` (not `image_subset`); `1/(n+2) → 0` by
  `tendsto_const_nhds.div_atTop (tendsto_natCast_atTop_atTop.atTop_add tendsto_const_nhds)`; density along the atlas ray via
  `atlas_mem_intrinsicInterior hS ν hfin hs0 (hs1 : s < 1)` + `tendsto_qStarVec` + `mem_closure_of_tendsto`. NEXT: round-69
  consult (re-rank: explicit natural-parameter radius; general-`X` face completion; reconstruction CLT; a capstone package
  theorem "the response atlas of the data manifold"), or land the explicit radius directly.
- Round-69 consult landed (`research_round69_{q,v1}`). Ranking: 1 = GENERAL-`X` POLYHEDRAL COMPLETION WITH CHARGED VERTICES
  (moment body a polytope, every vertex fibre `{S = v}` of positive `ν`-mass ⇒ `q_M ∼ ν|_{S ∈ F_M}` with an explicit face tilt,
  `M ↦ q_M` TV-continuous on the whole polytope, homeomorphism/closure/deformation retraction as in the finite case; route:
  vertex witnesses `L(a) = Σ a_i ν(·|S = v_i)`, conditional tilt on the minimal face (HARDEST: transporting conditional measure,
  affine hull, moment body, relative interior through one face-restriction construction), reuse the finite completion as a
  continuous vertex section `a(M)`, bounded-density additive recovery `b_n = q_M + L(a(M_n) − a(M))`, lower semicontinuity of
  the rate, Pythagoras + Pinsker instead of compactness; COUNTEREXAMPLE: `X = ℕ`, `S(n) = (cos(1/n), sin(1/n))`, all points
  charged, every face charged, yet `q_{S(n)} = δ_n` does not converge in TV — "all faces positive" is NOT enough, polyhedrality
  + charged vertices is the right hypothesis); 2 = SERIES-FREE EXPLICIT FACTORIAL BOUNDS IN NATURAL COORDINATES: along
  `p(t) = [q_{a+tv}]`, `Y = ⟨v,T⟩`, `|Y| ≤ L`, `ρ = log(3/2)/L`: `Σ_{k≤N} ρ^k ‖p^{(k)}(s)‖₁/k! ≤ 3`, hence `‖p^{(k)}‖₁ ≤ 3 k! ρ^{−k}`
  and remainder `3(|t|/ρ)^{N+1}`; route: `Z(t)p(s+t) = p(s)e^{−tY}`, `|Z^{(j)}(0)| ≤ L^j`, Leibniz ⇒ `b_k ≤ L^k + Σ_{j≥1} C(k,j) L^j
  b_{k−j}`, weighted sums `B_N ≤ 3/2 + ½ B_{N−1}` ⇒ `B_N ≤ 3` (no power series; NOT a response-coordinate radius); 3 = stratified
  Fisher geometry on faces (`D²I_F = Cov|_{V_F}⁻¹`, face lattice `M ∈ F ↔ q_M{S ∈ F} = 1`), exact boundary-ray formula
  `‖q_t − q_F‖₁ = 2B_t/(A + B_t)`; 4 = CLT (deterministic delta lemma first; no multivariate CLT assumed); 5 = capstone
  `ResponseAtlas` structure (documentation-level). Also: `H_t` (vertical fibre contraction) vs natural-gradient flow (horizontal
  transport) are complementary. NEXT: module `NaturalParameterMajorant` (rank 2, one module), then rank 1.
- `NaturalParameterMajorant` landed (round-69 rank 2 COMPLETE): `Σ_{k≤N} ρ^k ‖p^{(k)}(t)‖₁/k! ≤ 3` and `‖p^{(k)}(t)‖₁ ≤ 3 k! ρ^{−k}`
  with `ρ = log(3/2)/L` along every natural-parameter line, series-free, all `t`. Gotchas: `open scoped Nat` makes `φ` the
  totient notation (named `(φ := …)` arguments fail) — write `k.factorial`; defs not using `hfin`/`hS` need
  `omit hfin in variable (M) in` / `omit hS in variable (S) in` so the parameters stay explicit (`natZ S ν θ v`,
  `natWJet S ν θ v`); the type ascription `(iteratedDeriv k (natW …) t : X → ℝ)` mis-elaborates — write
  `((… : X →₁[ν] ℝ) : X → ℝ) a`; Leibniz for `Z • p` is `iteratedDerivWithin_smul (mem_univ t) uniqueDiffOn_univ
  hZ'.contDiffWithinAt hC'.contDiffWithinAt (n := k)` + `iteratedDerivWithin_univ`, with `ContDiff.of_le (m := k) (by
  exact_mod_cast natCast_le_infty k)`; `Z^{(j)}` from `ContinuousLinearMap.iteratedFDeriv_comp_left` + `iteratedDeriv_eq_iteratedFDeriv`
  + `change … (L1.integralCLM ∘ natW …)`; the top Leibniz term is isolated by `sum_range_succ'` + `add_sub_cancel_left`, the nsmul
  by `← Nat.cast_smul_eq_nsmul ℝ, norm_smul`; `omit [Nonempty J] in` before docstrings on every lemma not using `Classical.arbitrary J`
  (an over-omit of `[Nonempty X]` on `iteratedDeriv_natW_eq_sum` fails because `contDiff_natZ` needs it). NEXT: round-69 rank 1
  (general-`X` polyhedral completion with charged vertices; hardest lemma is the face-restriction transport) or rank 3 (stratified
  Fisher geometry on faces + boundary-ray TV formula `‖q_t − q_F‖₁ = 2B_t/(A+B_t)`); optionally the Taylor-remainder corollary
  `‖p(s+t) − Σ_{k≤N} p^{(k)}(s)t^k/k!‖₁ ≤ 3(|t|/ρ)^{N+1}` via `norm_L1_le_of_forall_integral_mul_le` (second module per Astra).
- `NaturalParameterTaylor` landed (round-69 rank 2 second module; also closes round-67 rank 3 "explicit natural-parameter
  radius"): `‖p(s+t) − Σ_{k≤N} p^{(k)}(s)t^k/k!‖₁ ≤ 3(|t|/ρ)^{N+1}` for all `s, t`, hence the `L¹` Taylor series converges on
  `|t| < ρ = log(3/2)/L`. Gotchas: the template is `reconstructionL1_cubic_remainder` (norm duality via
  `norm_L1_le_of_forall_integral_mul_le`, scalar `taylor_mean_remainder_lagrange (n := N) hlt.ne hg2 hg'` with `uIcc_of_le`/
  `uIoo_of_le`, `taylor_within_apply`, `add_sub_cancel_left` for `(s + t − s)`); on the whole line `hg'` is
  `(hg.differentiable_iteratedDeriv N (by exact_mod_cast natCast_lt_infty N)).differentiableOn.congr` +
  `iteratedDerivWithin_eq_iteratedDeriv (uniqueDiffOn_Icc hlt) (hg.of_le …).contDiffAt`; a general
  `clm_iteratedDeriv_of_contDiff L hf k t` replaces the atlas-specific pairing lemma; negative `t` by reflection
  (`iteratedDeriv_comp_neg`, `dirLoss_neg`, and `(−1)^k (−1)^k = 1` via `← mul_pow; norm_num` + `linear_combination`); the
  closing identity `3(N+1)!/ρ^{N+1} · t^{N+1}/(N+1)! = 3(t/ρ)^{N+1}` needs `div_pow; field_simp; rw [div_pow, mul_pow]; field_simp`
  with `log(3/2) ≠ 0` in context. NEXT: round-69 rank 1 (general-`X` polyhedral completion with charged vertices) or rank 3
  (facewise Fisher geometry `D²I_F = Cov|_{V_F}⁻¹`, face lattice `M ∈ F ↔ q_M{S ∈ F} = 1`, boundary-ray formula
  `‖q_t − q_F‖₁ = 2B_t/(A + B_t)`); a round-70 consult should fix the Lean shape of the face-restriction transport first.
