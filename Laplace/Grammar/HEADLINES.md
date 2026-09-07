# Grammar §4 formalisation — headline index (general-dimensional normal block)

## Taylor-tree programme (opened 2026-09-07, after the freeze; Astra #26)
**Stage 1 — exact multivariate state density — COMPLETE (units 223–226).**
| Headline | Statement | File:line |
|---|---|---|
| XXII | exact state density: `∫_{(0,1]^{n+1}} ∏aᵢ^{wᵢ} g(∏aᵢ) = ∫₀¹ v g`, `v = eval (stateDensityRep n w)` a finite sum of `z^{μ-1}(-log z)^j`, `μ ∈ {wᵢ+1}`, `j < multiplicity` | StateDensity.lean (`weightedBoxIntegral_eq_stateDensity`, `stateDensityRep_exponent_mem`, `stateDensityRep_degree_lt`) |
| XXII′ | Mellin transform `∫₀¹ z^s v = ∏ 1/(wᵢ+s+1)`; basis `∫₀¹ τ^{c-1}(-log τ)^j = j!/c^{j+1}`; real identity for `f ≥ 0`; integrability | StateDensityAPI.lean (`mellin_stateDensity`, `integral_Ioc_rpow_mul_neg_log_pow`, `integral_unitBox_eq_stateDensity`) |
| XXII″ | top coefficient `c_{l,m-1} = (1/(m-1)!) ∏_{wᵢ+1≠l} 1/(wᵢ+1-l)`; monomial form `= a_{-m}/(m-1)!` (Headline XXI's `mellinCoeff h k l 1`) | StateDensityLeadCoeff.lean (`stateDensityRep_leadCoeff`, `monomial_leadCoeff`) |
Convolution calculus in `PowLogCalculus.lean` (`PowLogRep.eval_conv`, `conv_exponent_mem`, `conv_degree_lt`).
**Stage 2 — exact monomial moments with a constant phase — COMPLETE (units 227–229).**
| Headline | Statement | File:line |
|---|---|---|
| XXIII | exact identity: `∫_{(0,1]^{n+1}} u^h (√N u^k)^p e^{-βNu^{2k}+β√N u^k a} = ∏1/(2kᵢ) ∑_{(μ,j,c)∈v} c N^{-μ} ∑_{i≤j} C(j,i)(log N)^{j-i} ∫₀^N t^{μ-1}(-log t)^i g(t)`, `g(t) = (√t)^p e^{-βt+β√t a}`, every `N > 0` | MonomialPhaseExpansion.lean (`monomialPhase_eq`) |
| XXIII′ | asymptotic form: `T(N) − monomialMainSum(N) = O(e^{-βN/8})` with the full moments `fluctMoment β a p μ i = ∫₀^∞ t^{μ-1}(-log t)^i g` | MonomialPhaseTail.lean (`monomialPhase_isBigO`, `tail_le`) |
Tools: `phaseKernel`, `truncMoment`, `basis_scaling`, `integral_unitBox_monomial_eq_stateDensity` (MonomialPhaseIdentity.lean).
**Stage 3 — polynomial Taylor tree with spectral truncation — COMPLETE (units 230–239; Astra #27, Gates A–D passed).**
Scope: polynomial phase `ξ` and amplitude `η` (finite monomial lists `MonoRep`), box `(0,1]^{n+1}` (`d = n+1`), `β > 0`, `kᵢ > 0`, `N` = paper's `n`; `Z(N) = polyPhaseIntegral = ∫ η u^h e^{-βN u^{2k} + β√N u^k ξ(u)}`; `Λ_L = latticeBelow (2∏kᵢ) L` (the lattice `Q⁻¹ℕ` below the cutoff; coefficients vanish at exponents not carried by any density).
| Headline | Statement | File:line |
|---|---|---|
| XXIV | exact polynomial Taylor tree, every `N > 0`: `Z(N) = ∑_p β^p/p! ∑_{(γ,c)∈ηJ^p} c · monomialTruncSum(h+γ)` with `J = ξ − ξ(0)` (absolutely convergent; `HasSum` form at L159 / L286) | PhaseTaylorIdentity.lean:270 (`polyPhaseIntegral_eq_tsum_truncSum`) |
| XXV | quantitative cutoff: `|Z(N) − ∑_{μ∈Λ_L} N^{-μ} ∑_{j≤n} A_{μ,j}(log N)^j| ≤ C · N^{-L}(1+log N)^n` for all `N ≥ 1`, `L > 0`, `C` explicit and `N`-free; exact form `= R_high − tail` at L444 | LowSpectrumTail.lean:457 (`taylorTree_cutoff_bound`) |
| XXVI | asymptotic expansion: `Z − spectralSum_L = O(N^{-L}(1+log N)^n)` (L41), `= O(N^{-L}(log N)^n)` (L64), `= o(N^{-L'})` for `L' < L` (L81) | TaylorTreeAsymptotic.lean:41 (`taylorTree_isBigO`) |
| — | spectral coefficient `A_{μ,j} = ∑_p β^p/p! K_k ∑_{(γ,c)} c ∑_{q=j}^{n} coeffAt(ρ_{h+γ},μ,q) C(q,j) fluctMoment_p(μ,q−j)`: cutoff-free, absolutely convergent (Gate D) | SpectralCoefficients.lean:371 (`spectralCoeff`), :343 (`summable_coeffTerm_series`), :384 (`mainSeries_eq_sum`) |
| — | Gate C: `|R_high(N)| ≤ K_k‖η‖₁(n+1)!Q^n M_{L,n}(ξ(0)+‖J‖₁) · N^{-L}(1+log N)^n` (τ-side estimate, constants independent of the monomial) | HighSpectrumBound.lean:376 (`abs_highRemainder_le`), :118 (`basis_integral_le`) |
| — | Gate B: log majorant `M_{ν,r,p}(b) = ∫₀^∞ t^{ν-1}(1+|log t|)^r(√t)^p e^{-βt+βb√t}` finite for all real `b`; Tonelli `∑_p (βB)^p/p! M_{ν,r,p}(b) = M_{ν,r,0}(b+B)` (no smallness on `B`) | PhaseMajorant.lean:146 (`integrableOn_logMajorant`), :246 (`tsum_phaseLogMoment_series`) |
| — | Gate A: uniform weighted budget `∑|c| j! Q^j ≤ (n+1)! Q^n` for every lattice-supported state density | DensityBudget.lean:204 (`budget_stateDensityRep_le`) |
| — | lattice `Q = 2∏kᵢ`, `(e+1)/(2kᵢ) ∈ Q⁻¹ℕ_{>0}`, spacing `1/Q`, finite `latticeBelow` | SpectralLattice.lean:37 (`ratio_mem_lattice`) |
| — | polynomial ℓ¹ algebra: `|P(u)| ≤ ‖P‖₁` on the cube, `‖PQ‖₁ = ‖P‖₁‖Q‖₁`, `‖P^p‖₁ ≤ ‖P‖₁^p`, `fluct` | MonomialRep.lean:85 (`abs_eval_le_l1`), :149 (`l1_pow_le`) |
| — | **spectral support (u240)**: `A_{μ,j} = 0` unless `μ ∈ Λ(h,k) = ⋃_i ((hᵢ+1)/(2kᵢ) + ℕ/(2kᵢ))` (paper's candidate set, `candidateExp`); expansion restated over `Λ(h,k) ∩ [0,L)`; explicit coefficient formula (`C_{μ,m} = A_{μ,m-1}`); summed exponential tail `|tailSeries| ≤ C(1+log N)^n e^{-βN/4}` | CandidateSupport.lean:87 (`spectralCoeff_eq_zero_of_not_candidate`), :131 (`taylorTree_isBigO_candidate`), :105 (`spectralCoeff_eq`), :142 (`abs_tailSeries_le_exp`) |
Low-spectrum tail replacement: `LowSpectrumTail.lean` (`tsum_logTailMoment_series` L48, `exp_le_rpow_const` L137, `abs_tailSeries_le` L396). Numerical checks: XXIV in d=1 to 2e-15; XXV in d=1 (L = 5/2): error × N^{5/2} ≈ 0.15 stable over N = 10…640.
**Stage 4 — analytic data by coefficient families — COMPLETE (units 241–247; Astra #28).**
Hypothesis: `ξ(u) = ∑_γ cξ_γ u^γ`, `η(u) = ∑_γ cη_γ u^γ` with `∑|c_γ| < ∞` (`CoeffFamily.AbsSummable`) — a *sufficient, strictly weaker* form of the paper's hypothesis: holomorphy on `D_R`, `R > 1`, implies it via Cauchy estimates `|c_γ| ≤ M_r r^{-|γ|}` (bridge NOT formalised; it would also identify `c_γ = ∂^γ f(0)/γ!`). Paper correspondence: `P_μ(X) = ∑_{j≤n} A_{μ,j} X^j`, `C_{μ,m} = A_{μ,m-1}`. The coefficients are cutoff-independent LIMITS of the polynomial coefficients; their identification with an explicit absolutely convergent series over `(p, γ)` (a convolution of families) is NOT formalised. Route: box truncations `truncList c m` (finite `MonoRep`), coefficient stability, pass to the limit at fixed `N`.
| Headline | Statement | File:line |
|---|---|---|
| XXVII | `|Z(N) − ∑_{μ∈Λ_L} N^{-μ} ∑_{j≤n} A_{μ,j}(cξ,cη)(log N)^j| ≤ cutoffBound(ξ(0), mass η, mass ξ) · N^{-L}(1+log N)^n` for all `N ≥ 1`, `L > 0`; `O(N^{-L}(1+log N)^n)` (L54), `O(N^{-L}(log N)^n)` (L66), `o(N^{-L'})` for `L' < L` (L96), over `Λ(h,k)` (L122) | FamilyTaylorTree.lean:39 (`familyTaylorTree_cutoff_bound`) |
| — | **stability gate**: `|A_{μ,j}(ξ',η') − A_{μ,j}(ξ,η)| ≤ K_k D (E β M_{μ+1/2,n}(a+B) ‖Δ‖₁ + M_{μ,n}(a+B) ‖Δη‖₁)` for `η' ~ η ++ Δη`, `J' ~ J ++ Δ`, same constant phase | CoeffStability.lean:147 (`abs_spectralCoeff_sub_le`) |
| — | family coefficients `A_{μ,j}(cξ,cη) = lim_m A_{μ,j}(truncations)` (Cauchy via the gate), vanishing off `Λ(h,k)` | FamilySpectralCoeff.lean:130 (`familySpectralCoeff`), :135 (`tendsto_truncCoeff`), :142 |
| — | `Z_m(N) → Z(N)` at fixed `N` (dominated convergence) | FamilyPhaseIntegral.lean:45 (`tendsto_polyPhaseIntegral_truncList`) |
| — | uniform constant: `taylorCutoffConst ≤ cutoffBound a E B` from `ξ(0) = a`, `‖η‖₁ ≤ E`, `‖J‖₁ ≤ B` (`M` monotone in `b`, `tailConst` in `|b|`) | UniformCutoffConst.lean:61 (`taylorCutoffConst_le`) |
| — | coefficient families: mass, eval (`|eval| ≤ mass` on the cube), truncations with `truncList c m' ~ truncList c m ++ rest`, `‖rest‖₁ ≤ tailMass c m → 0`, uniform convergence | CoeffFamily.lean:189 (`truncList_perm`), :149 (`tailMass_tendsto_zero`), :221 (`abs_evalF_sub_truncList_le`) |
| — | list algebra: `pow (J ++ Δ) p ~ pow J p ++ R`, `‖R‖₁ ≤ p‖Δ‖₁(‖J‖₁+‖Δ‖₁)^{p-1}` | MonoRepPerm.lean:65 (`pow_append_perm`) |
| — | general box `(0,b]^d` (u248): `Z_b(N) = b^{|h|+d} Z_1(N b^{2|k|}; ξ(b·), η(b·))`, rescaled family `c_γ b^{|γ|}` summable iff the weighted mass at radius `b` is finite | BoxScaling.lean:80 (`familyPhaseIntegralBox_eq`) |
| XXVIII | Taylor tree on `(0,b]^d` (u249): for `∑|c_γ| b^{|γ|} < ∞`, `|Z_b(N) − boxSpectralSum(N)| ≤ b^{|h|+d} cutoffBound · (N b^{2|k|})^{-L}(1+log(N b^{2|k|}))^n`; `O(N^{-L}(1+log N)^n)` in the sample size (L82); paper's form `∑_μ N^{-μ} ∑_{j≤n} C^b_{μ,j}(log N)^j` by binomial re-expansion (L131, `boxCoeff`) | BoxTaylorTree.lean:45 (`boxTaylorTree_cutoff_bound`) |
| ★ | **end-to-end wrapper (u256)** `thm_TaylorTree_coeffFamily`: `∃ C, TaylorTreeConclusion …` — one coefficient system (= `familySpectralCoeff` of the rescaled data), vanishing off `Λ(h,k)`, equal to the paper's absolutely convergent series, remainder bound for every cutoff `L` (`N b^{2|k|} ≥ 1`), `IsBigO` in `N`, and the mixed derivative dictionary; quantifier order `∃ C ∀ L` | TaylorTreeWrapper.lean:68 |

**Stage 6 — the analytic bridge, one variable (units 257–258; Astra #30 C₁ pilot) — COMPLETE.**
| — | Cauchy coefficients of `f : ℂ → ℂ` holomorphic on `|z| ≤ r` (u257): `discCoeff f r n = (cauchyPowerSeries f 0 r).coeff n`; `∑ discCoeff z^n = f z` on `|z| < r` (L48); Cauchy estimate `‖discCoeff‖ ≤ M_r r^{-n}` (L40); weighted summability at every `b < r`; `discCoeff = f^{(n)}(0)/n!` (L75) | CauchyCoeff1D.lean |
| XXXI | **analytic Taylor tree in `d = 1` under the paper's own hypothesis (u258)**: for `fξ, fη` holomorphic on the closed disc of radius `r > b`, the real Cauchy-coefficient families represent `Re fξ, Re fη` on `(0,b]` (L50: `∑ Re(discCoeff) x^n = Re f(x)`) and `TaylorTreeConclusion` holds for them — no reality hypothesis needed | AnalyticBridge1D.lean:102 (`thm_TaylorTree_analytic_1d`) |
| XXXI′ | **paper-facing `d = 1` corollary (u259)**: real `ξ, η` on `(0,b]` with holomorphic extensions to `|z| < R`, `R > b`; for any `r ∈ (b,R)` the real Cauchy-coefficient families satisfy `TaylorTreeConclusion` and their family integral IS the original `Z(N) = ∫_{(0,b]} η u^h e^{-βN u^{2k} + β√N u^k ξ} du` (`familyPhaseIntegralBox_eq_orig_1d`) | AnalyticTaylorTree1D.lean:63 (`thm_TaylorTree_analytic_1d'`) |
Review v24 (u256–258): qualified pass, no defect; should-fixes done in u259 (paper-facing corollary, integral transport, `Re f` docstring, closed-disc/totalised-integral wording). Release scope: coefficient-family theorem in every dimension; analytic bridge complete in `d = 1` only.
**Stage 7 — the several-variable analytic bridge (units 260–264; Astra #31 route R2) — COMPLETE.**
| — | normalised circle operator `A_r g = (2πi)⁻¹ ∮ w⁻¹ g` (u260): `‖A_r g‖ ≤ sup‖g‖`, Cauchy formula `A_r((1−z/w)⁻¹ g) = g z`, coefficient `HasSum`, parametric continuity | CircleOperator.lean |
| — | iterated operator `A_r^{[d]}` along `Fin.cons`, torus bound, `SliceHolo`, **iterated Cauchy formula** `A_r^{[d]}(w ↦ F w ∏(1−zᵢ/wᵢ)⁻¹) = F z` (L160), supplied by joint differentiability on the open polydisc (L213) | PolydiscCauchy.lean |
| — | parametric continuity on sets, series interchange `A_r(Σ G_n) = Σ A_r(G_n)` (L91), product geometric series | CircleOpParam.lean |
| — | **Cauchy coefficients `c_γ = A_r^{[d]}(F ∏ wᵢ^{-γᵢ})`** (u263, the gate): `‖c_γ‖ ≤ M r^{-|γ|}` (L33), reconstruction `∑_γ c_γ z^γ = F z` as `HasSum` on the open polydisc (L87), `∑ ‖c_γ‖ b^{|γ|} < ∞` for `b < r` | PolydiscCoeff.lean |
| XXXII | **`thm:TaylorTree` under the paper's own hypothesis, every dimension (u264)**: real `ξ, η` on `(0,b]^d` with holomorphic extensions to the polydisc `{|zᵢ| < R}`, `R > b`; for `r ∈ (b,R)` the real Cauchy-coefficient families `polyRealCoeff` satisfy `TaylorTreeConclusion` and their family integral IS the original `Z(N)` (`familyPhaseIntegralBox_eq_orig`) | AnalyticTaylorTree.lean:112 (`thm_TaylorTree_analytic`) |
Not formalised: the multi-index derivative identification `c_γ = ∂^γ F(0)/γ!` (γ! = ∏ γᵢ!; Astra #31 units 9–10, coordinate-wise uniqueness) — the coefficients are the explicit iterated Cauchy integrals.
| XXXII′ | **paper-facing form (u265)**: the same from `0 < b < R` alone, `∃ cξ cη C` (radius `(b+R)/2` chosen inside) | AnalyticTaylorTree.lean:133 (`thm_TaylorTree_analytic'`) |
Review v25 (u260–264): qualified pass at statement level, no mathematical defect — "the analytic bridge is successfully closed"; should-fixes done in u265: headline reads "applies under the paper's hypothesis" (the formal matching assumption is real-part agreement `Re Fξ = ξ` on the box, weaker than a genuine extension), residual task stated with the complex/real distinction (`polyCoeff = ∂^γ F(0)/γ!`, `polyRealCoeff = Re(…)`, linkage to `ξ` needs the genuine extension), `∃ r` corollary XXXII′, torus-bound estimate vs closed-polydisc-bound reconstruction distinguished in the docstrings; the "duplicate declaration" remarks are statement-extractor artefacts (each source has one). Numerics: `polyCoeff` at `d = 2` vs Taylor coefficients `2e-16`, reconstruction `4e-15`.

**Analytic bridge — COMPLETE in every dimension (2026-09-07; pin see git; Headlines XXXI–XXXII′, units 257–265; reviews v24–v25).** `thm:TaylorTree`/`cor:standardintegralexp` now hold under the paper's own hypothesis (holomorphic `Fξ, Fη` on a polydisc of radius `R > b` with `Re Fξ = ξ`, `Re Fη = η` on `(0,b]^d`) with the original integral `Z(N)`. Only the derivative identification of the coefficients remains outside the formalisation.
Remaining for general `d` (superseded — done above): iterated one-variable Cauchy coefficient extraction with the product majorant `|c_γ| ≤ M r^{-|γ|}` (Astra #30: gate = quantitative two-coordinate lemma; 12–20 units).

**Taylor-tree programme — COMPLETE under the coefficient-summability hypothesis (2026-09-07; pin `ba849b3`; Headlines XXII–XXX, units 223–255; reviews v18–v23 all pass/qualified pass with no mathematical defect).** Formalised: `thm:TaylorTree`/`cor:standardintegralexp` on `(0,b]^d` for phase and amplitude given by coefficient families with `∑|c_γ| b^{|γ|} < ∞` — the paper's exponent set `Λ(h,k)`, log indexing, cutoff-independent coefficients equal to the paper's explicit absolutely convergent Cauchy-product series (XXIX), the mixed derivative dictionary `β^p fluctMoment = (−∂_μ)^i ∂_a^p S_μ(a)` (XXX), remainder `O(N^{-L}(1+log N)^{d-1})` for every `L`. **Not formalised (the single remaining gap to the paper's own hypotheses):** the Cauchy-estimate bridge from holomorphy on the polydisc `D_R`, `R > b`, to `∑|c_γ| b^{|γ|} < ∞` with `c_γ = ∂^γ f(0)/γ!` (Mathlib has no several-variable Cauchy estimates; Astra #29: 15–25 units, not budgeted). Review v23 (u255): qualified pass ("duplicate declaration" is a statement-extractor artefact; the source has one). Paper erratum: `∂_a^p S_μ = β^p S_{μ+p/2}`, the displayed formula omits `β^p`.

**Qualified release (Astra #29, 2026-09-07; pin `bb504c0`).** Principal theorem: Headline XXVIII (general box), core Headline XXVII (unit cube), corollary `boxSpectralSum_eq`. Hand-off wording (Astra #29): *We have formalised the Taylor-tree asymptotic expansion and its standard-integral corollary for general boxes, under the coefficient hypothesis `∑_γ |c_γ| b^{|γ|} < ∞` for phase and amplitude: the paper's exponent set `Λ(h,k)`, the paper's logarithmic indexing, a single coefficient system independent of the cutoff, and for every `L > 0` the remainder `O(N^{-L}(1+log N)^{d-1})`; no `sorry`, no additional axioms. This is a qualified formalisation of `thm:TaylorTree`: the coefficient hypothesis is sufficient and less restrictive than the polydisc hypothesis, but the implication from the paper's analytic hypothesis (incl. `c_γ = ∂^γ f(0)/γ!`) is not formalised; coefficients are explicit for polynomial inputs and defined for summable families as stable limits of truncations — their identification with the paper's explicit absolutely convergent series, and the special-function derivative notation, remain unformalised (the `∂_a` half of the dictionary is now a theorem, u250). Independent reviews v20/v21 found no mathematical defects.* Constants depend on `d, h, k, β, b, L` and the data through `ξ(0)` and the masses; the general-box quantitative bound needs `N b^{2|k|} ≥ 1`; "vanish off `Λ(h,k)`" is support containment, not nonvanishing.
Astra #29 plan: A (explicit coefficient series via `Finset.Iic` convolution, 8–12 units, gate = summable majorant of `∑_p β^p/p! |T_{μ,j,p}(c_η * J^{*p})|`), C scouting (Cauchy bridge, 2–3 scouting units then 15–25; gate = arbitrary `b < R`, closed cube), B derivative dictionary (5–8), then final review.

Review v21 (Stage 4): qualified pass, no mathematical defect (moment shift, appended-perturbation estimate, constant phase of truncations, fixed-N limit, `|a|+B` monotonicity all confirmed); should-fixes are documentation (done above: analytic bridge labelled, coefficient-series identification labelled, u242 described as appended-perturbation stability). The reviewer's "duplicate `pow_append_perm`" is a paste artefact of the statement extractor (source has one declaration).
**Stage 5 — explicit coefficient series (units 251–254; Astra #29 candidate A) — COMPLETE.**
| — | Cauchy product of families `(c*e)_γ = ∑_{α≤γ} c_α e_{γ-α}` (Finset.Iic, no antidiagonal instance): `evalF (c*e) = evalF c · evalF e` on the cube, `mass (c*e) ≤ mass c · mass e` | CoeffConv.lean:81 (`evalF_conv`), :116 (`mass_conv_le`) |
| — | collected coefficients of lists: `coeffFn (mul P Q) = conv`, `coeffFn (pow P p) = convPow`, `coeffFn (fluct P)`, `coeffFn (truncList c m) = truncFamily c m` | CoeffFnBridge.lean:154 (`coeffFn_mul`), :176 (`coeffFn_pow`) |
| — | kernel functional `T_p(f) = K_k ∑_γ f_γ S_p(μ,j;γ)`: `coeffTerm P = T_p (coeffFn P)`, `|T_p f| ≤ K_k D M_{μ,n,p}(a) mass f` | CoeffKernel.lean:81 (`coeffTerm_eq_kernelFunctional`), :100 (`abs_kernelFunctional_le`) |
| XXIX | **the paper's coefficient series**: `A_{μ,j}(cξ,cη) = ∑_p β^p/p! T_p(cη * J^{*p})`, `J = fluctFamily cξ`, absolutely convergent (`|term_p| ≤ K_k D M_{μ,n,p}(a) mass(cη) mass(J)^p`, Tonelli) and EQUAL to the limit-defined family coefficient (`familySpectralCoeff_eq_series`, μ > 0); `(cη * J^{*p})_γ` is the paper's `η_m/m! · ξ_{n,p}` (eq:flucttreeterms); power-difference estimate `mass(c^{*p} − c'^{*p}) ≤ p B^{p-1} mass(c − c')` (L95) | FamilyCoeffSeries.lean:306 (`familySpectralCoeff_eq_series`), :152 (`familyCoeffSeries`), :195 (`summable_familyCoeffSeries_terms`) |
Review v21's qualification (ii) is thereby closed in the coefficient-family setting: for `μ > 0` the family coefficients are the *collected* Cauchy-product series matching the paper's formula when the input families are normalised Taylor coefficients `c_γ = ∂^γ f(0)/γ!` (that normalisation is part of the unformalised analytic bridge). `summable_familyCoeffSeries_terms` is absolute convergence of the outer collected series in `p`; the fully expanded multi-index series is not exposed as a separate theorem. Review v22 (u250–254): qualified pass, no mathematical defect; hand-off wording: *the phase-parameter derivative dictionary is formalised including the factor `β^p` (the paper's displayed `∂^p S_μ = S_{μ+p/2}` omits it); spectral-parameter derivatives producing logarithmic moments remain to be formalised.*
| XXX | **the derivative dictionary (u255)**: `∂_μ fluctMoment = −fluctMoment` at the next log order; `fluctMoment β a p μ i = (−1)^i ∂_ν^i S_{ν+p/2}(a)|_{ν=μ}` (L169); `β^p fluctMoment β a p μ i = (−∂_μ)^i ∂_a^p S_μ(a)` (the paper's coefficient notation, sign `(−∂_μ)^i ↔ (−log t)^i` exact); shift identity `fluctMoment β a p ν 0 = S_{ν+p/2}(a)`; identification of the family coefficients with the paper's series for EVERY real `μ` (L210) | FluctuationDerivativeMu.lean:180 (`fluctMoment_eq_mixed_deriv`) |
| — | derivative dictionary, phase half (u250): `∂_a fluctMoment = β · fluctMoment` at the next phase order; `∂_a^p S_μ(a) = β^p fluctMoment β a p μ 0` | FluctuationDerivative.lean (`hasDerivAt_fluctMoment`, `iteratedDeriv_fluctuationFn`) |
Not formalised: the Cauchy-estimate bridge from holomorphy on a polydisc to `∑|c_γ| < ∞` (the only remaining gap to `thm:TaylorTree` under the paper's own hypotheses; Astra #29: 15–25 units, unbudgeted).

Review v20 (Stage 3): qualified pass, no mathematical defect; should-fix items 1 (candidate support), 2 (coefficient formula), 6 (exponential tail) done in u240; 3–5 are documentation (done). **Stage 3 frozen as reviewed milestone at u240.**
Not formalised (Stage 4, Astra #28 plan: coefficient families `(Fin d → ℕ) → ℝ` with `Summable |c|`, polynomial truncations, coefficient-stability gate first, then density): analytic (non-polynomial) `ξ, η`; `b ≠ 1` (scaling `Z_b(N) = b^{|h|+d} Z_1(N b^{2|k|}; ξ(b·), η(b·))`); the derivative dictionary `fluctMoment β a p μ i = (−∂_μ)^i S_{μ+p/2}(a) = β^{-p}(−∂_μ)^i ∂_a^p S_μ(a)` (interpretation only). Hypothesis audit: the paper assumes holomorphy on the origin-centred polydisc `D_R`, `R > b`, which gives `∑|c_γ| b^{|γ|} < ∞` by Cauchy estimates — so "absolutely summable coefficient family on the box" is implied by the paper's hypothesis (no localisation gap for the stated theorem; the Cauchy-estimate bridge itself is a separate Mathlib obligation).


## Completion statement (2026-09-07)
The scoped **§4 normal-block programme is complete** at the reviewed baseline `d65d48b` (Astra #24–#25; reviews
v1–v17): general machinery (Headlines VI–XIX), the assembled statistical example (XX–XX'' with the genuine-prior
lemmas), and the Abelian coefficient dictionary (XXI). Explicit non-claims: XX–XX'' are fixed-`θ` moment-generating-
function limits, not a formalised weak-convergence theorem for posterior laws; XXI is a real-axis Abelian coefficient
limit, not meromorphic continuation or an exact-pole-order theorem; the signed-weight statements are analytic, the
posterior interpretation needs `ρ ≥ 0`. The remaining paper material (full Taylor-tree expansion, complex Mellin
continuation, the boundary tail, `eq:flucttreeterms`, the resolution-based §4.3 application) is **outside the
completed work package**. Preferred separately authorised successor (Astra #25): posterior weak convergence of the
law of `√n x₀x₁` to `N(z,1)` for deterministic phases (reconnaissance first: Lévy/Curtiss route vs direct
test-function route); a cheap robustness variant is available via Mathlib's CLT (i.i.d. mean-0 variance-1 data).

Pinned commit for the mirror `grammar_lean.tex`: see `\laplaceLeanCommit` there. All statements
zero `sorry`/`axiom`; independent statement-level reviews v1–v15 in `tide-log/gpt6_fidelity_review_v*.md`.
Conventions: boxes `(0,1]^d` (`unitBox`), `(-1,1]^d` (`symBox`); `ratioExp h k i = (hᵢ+1)/(2kᵢ)`,
`λ = min`, `J` the minimisers, `m = multCount`; chart variable `N` (paper's `√n`), `p = 2λ`;
`phaseMoment β p a = ∫₀^∞ s^{p-1} e^{-βs²+βas} ds` is the paper's `J_p(a) = S_{p/2}(a)/2`.

| Headline | Statement | File:line |
|---|---|---|
| VI  | bare equal-ratio normal moment asymptotic | HeadlineMonomial.lean:73 |
| VII | bare mixed-ratio (face) asymptotic, `minRatio` wrapper | HeadlineMonomialMixed.lean:58 |
| VIII | continuous amplitude: face-supported functional | HeadlineAmplitude.lean:85 |
| IX  | tangential integration against a compact set | HeadlineTangential.lean:38 |
| X   | stochastic `1/log N` regime (d = 2) | HeadlineStochasticLog.lean:37 |
| XI  | signed reflections, zero phase (parity) | SymmetricAmplitudeAsymptotic.lean:89 |
| XII | zero-phase unequal-exponent dictionary, `noLogConst` closed form | QuadraticMixedBridge.lean:115 |
| XIII | phase-dressed leading term, general d (face integral of `η(πu) J_p(ξ(πu))`) | HeadlinePhase.lean:117 |
| XIII' | equal ratios: corner value `η(0) J_p(ξ(0)) / ((d-1)! ∏ kᵢ)` (= paper's `A_p` at d = 2) | HeadlinePhase.lean:138 |
| XIII'' | uniform cutoff `(0,b]^d` | PhaseCutoff.lean:117 |
| XIV | per-stratum posterior quotient (deterministic) | PhasePosterior.lean:148 |
| XV  | conditional finite chart assembly (deterministic) | HeadlineAssembly.lean:51 |
| XVI | random phases and amplitudes: `F_{N_n}(X_n) ⇒ F(Z)` | PhaseRandomTransfer.lean:222 |
| XVII | random per-stratum posterior quotient | PhaseRandomPosterior.lean:99 |
| XVIII | assembled stochastic posterior quotient over charts | HeadlineStochasticAssembly.lean:102 |
| XIX | symmetric box with phase (signed `x^h` / absolute `|x|^h`) | HeadlineSymmetricPhase.lean:102 / 127 |
| XX  | end-to-end example: model `N(x₀x₁,1)` on `(-1,1]²`, posterior MGF of `√n x₀x₁` → `e^{zθ+θ²/2}` (exact likelihood identity at L152) | NormalCrossingModel.lean:278 |
| XX' | Gaussian data `Yᵢ` iid `N(0,1)`: `E_post[e^{θ√n x₀x₁}] − e^{Zₙθ+θ²/2} → 0` in probability (uniform-in-phase MGF at L255, Chebyshev at L350) | NormalCrossingData.lean:361 |
| XX'' | Gaussian data: `E_post[e^{θ√n x₀x₁}] ⇒ e^{Zθ+θ²/2}`, `Z ~ N(0,1)` (exact law `Zₙ ~ N(0,1)` at L123) | NormalCrossingLaw.lean:178 |
| XXI | real-axis Abelian limit for the leading Mellin (zeta) coefficient: `s^m ∫ η u^{2k(-λ+s)+h} → ∏_J 1/(2kᵢ) ∫ η(πu) ∏_{∉J} u^{h-2kλ}` as `s → 0⁺` (`η` continuous on the closed cube; no continuation/pole-order claim); `η = 1` gives the paper's `a_{-m}` (L303); Γ-dictionary with Headline VIII (L338) | MellinCoefficient.lean:285 |
| — | genuine prior (`ρ ≥ 0`, `ρ(0) > 0`): evidence positive at every sample size; posterior mean of `1` is `1` | NormalCrossingPrior.lean:87 / 102 |
| — | formal face-vs-corner counterexample (`5√π/12 ≠ √π/4`) | MixedRatioCounterexample.lean:126 |
| — | abstract assembly (min exponent, max log multiplicity) | ChartAssembly.lean:142 |

Earlier headlines (I–V, d = 2 Taylor tree, coefficient CLT, chart posterior limit, `1/log N` regime)
are in `Headline.lean`, `HeadlinePosterior.lean` and their neighbours.

## What the theorems assume (hand-off)
See `projects/grammar/staging/normal-block-report-v3.pdf` §Assumptions: the chart decomposition is an
external input ("conditional" = assuming); densities are deterministic and strictly positive; no
remainders; joint convergence of the empirical phases is a hypothesis; the stochastic results are weak
limits, not expansions with rates; selection is at the normalised scale and signed numerators may cancel.
Headlines XX/XX'/XX'' concern one concrete statistical model with no chart-decomposition or likelihood-remainder
hypothesis (XX assumes `Zₙ → z`; XX'/XX'' assume i.i.d. `N(0,1)` data). They are fixed-`θ` moment-generating-function
limits, not weak convergence of the posterior law, with no rate; the weight `ρ` may be signed (`ρ(0) > 0` only), and for a
genuine prior (`ρ ≥ 0` on the box) the evidence is positive at every sample size (`NormalCrossingPrior.lean`). Reviews v16–v17.
