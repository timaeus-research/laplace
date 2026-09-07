# Astra consult #32 — the Taylor-tree programme after the analytic bridge: freeze, finish the derivative identification, or what next?

You are advising a Lean 4 / Mathlib formalisation (project `laplace`, namespace `Laplace.Grammar`, pin `45b0943`) of Section 4 of the paper "Grammar of the fluctuations" (Murfet et al.; `thm:TaylorTree`, `cor:standardintegralexp`: asymptotic expansion of the standard integral Z(β,n;ξ,η) = ∫_(0,b]^d η(u) u^h exp(-βn u^(2k) + β√n u^k ξ(u)) du in powers n^(-μ) (log n)^(m-1), μ ∈ Λ(h,k), with coefficients given by explicit series in the fluctuation moments S_μ(a) and its derivatives).

Your previous consults: #26 roadmap (density-first, spectral truncation); #27 Stage 3 design; #28 Stage 4 by coefficient families; #29 freeze qualified release + bridge scouting; #30 wrapper theorem + one-variable pilot C₁; #31 route R2 for the several-variable bridge (recursive normalised circle operators on slices, 10-unit cap, gate after unit 3). Reviews v18–v25 (independent statement-level fidelity reviews by a separate model) all pass/qualified pass with no mathematical defect.

## Status (2026-09-07)

Route R2 succeeded in 6 units (cap was 10); the gate (quantitative reconstruction) passed at unit 263. Headline XXXII (`thm_TaylorTree_analytic`, and the primed form taking only `0 < b < R`): for real ξ, η on (0,b]^d with holomorphic Fξ, Fη on the open polydisc {|z_i| < R}, R > b, whose real parts agree with ξ, η on the box, the real parts of the several-variable Cauchy coefficients at any radius r ∈ (b,R) form weighted-summable coefficient families representing ξ, η on the box, the family integral IS the original Z(N), and the full Taylor-tree conclusion (structure `TaylorTreeConclusion`: exponent support Λ(h,k), cutoff-independent coefficients equal to the explicit absolutely convergent Cauchy-product series, mixed derivative dictionary β^p fluctMoment = (−∂_μ)^i ∂_a^p S_μ(a), remainder O(N^{-L}(1+log N)^{d-1}) for every L) holds. Zero sorry, zero additional axioms, 9140 jobs.

Review v25 verdict: "qualified pass at statement level … the analytic bridge is successfully closed. The remaining qualification is derivative/paper-data identification and headline precision." Should-fixes applied in unit 265 (wording "applies under the paper's hypothesis"; real-part agreement vs genuine extension; residual task stated as `polyCoeff γ F = ∂^γ F(0)/γ!` (complex) hence `polyRealCoeff = Re(...)`; ∃ r corollary; torus vs closed-polydisc bound).

**The single remaining gap to the paper's formulation:** the coefficients are the explicit iterated Cauchy integrals c_γ = A_r^{[d]}(F ∏ w_i^{-γ_i}), NOT identified with ∂^γ F(0)/γ! (γ! = ∏ γ_i!). In d = 1 the identification is done (`discCoeff_eq_iteratedDeriv_div`). Consequently the paper's coefficient formula (eq:flucttreeterms, in terms of Taylor coefficients ξ_{n,p}, η_m/m! of ξ, η at 0) is formalised with the Cauchy coefficients in place of the normalised derivatives; c^ξ_0 = ξ(0) is available only through the reconstruction at z = 0 (Re Fξ(0)).

## HEADLINES excerpt (Stages 5–7)

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



## Key Lean statements (verbatim from source; note: excerpts are extracted mechanically and may be truncated)

```lean
/-- The normalised circle operator `A_r(g) = (2πi)⁻¹ ∮_{|w|=r} w⁻¹ g(w) dw`. -/
noncomputable def circleOp (r : ℝ) (g : ℂ → ℂ) : ℂ

/-- `A_r^{[d]}`: iterated normalised circle operator along `Fin.cons`. -/
noncomputable def iterOp : (d : ℕ) → ℝ → ((Fin d → ℂ) → ℂ) → ℂ
  | 0, _, G => G Fin.elim0
  | d + 1, r, G => circleOp r fun w => iterOp d r fun w' => G (Fin.cons w w')

theorem circleOp_congr {r : ℝ} (hr : 0 ≤ r) {g₁ g₂ : ℂ → ℂ} (h : EqOn g₁ g₂ (Metric.sphere 0 r)) :
    circleOp r g₁ = circleOp r g₂

/-- Recursive slice hypothesis: `F` continuous on the closed polydisc, holomorphic in the first
coordinate on the disc for every tail in the closed polydisc, and recursively so for every
first-coordinate value on the closed disc. -/
def SliceHolo : (d : ℕ) → ℝ → ((Fin d → ℂ) → ℂ) → Prop
  | 0, _, _ => True
  | d + 1, r, F => ContinuousOn F (closedPolydisc (d + 1) r) ∧
      (∀ w' ∈ closedPolydisc d r, DiffContOnCl ℂ (fun t => F (Fin.cons t w')) (Metric.ball 0 r)) ∧
      (∀ w : ℂ, ‖w‖ ≤ r → SliceHolo d r fun w' => F (Fin.cons w w'))

/-- **The iterated Cauchy formula**: `A_r^{[d]} (w ↦ F w ∏ (1 − zᵢ/wᵢ)⁻¹) = F z` on the open
polydisc. -/
theorem iterOp_cauchy : ∀ (d : ℕ) {r : ℝ}, 0 < r → ∀ {F : (Fin d → ℂ) → ℂ}, SliceHolo d r F →
    ∀ {z : Fin d → ℂ}, z ∈ openPolydisc d r →
      iterOp d r (fun w => F w * ∏ i, (1 - z i / w i)⁻¹) = F z
  | 0, _, _, F, _, z, _ => by
    simp only [iterOp, Finset.univ_eq_empty, Finset.prod_empty, mul_one]
    congr 1
    exact Subsingleton.elim _ _
  | d + 1, r, hr, F, hF, z, hz => by
    obtain ⟨_, hslice, htail⟩

/-- **The iterated Cauchy formula**: `A_r^{[d]} (w ↦ F w ∏ (1 − zᵢ/wᵢ)⁻¹) = F z` on the open
polydisc. -/
theorem iterOp_cauchy : ∀ (d : ℕ) {r : ℝ}, 0 < r → ∀ {F : (Fin d → ℂ) → ℂ}, SliceHolo d r F →
    ∀ {z : Fin d → ℂ}, z ∈ openPolydisc d r →
      iterOp d r (fun w => F w * ∏ i, (1 - z i / w i)⁻¹) = F z
  | 0, _, _, F, _, z, _ => by
    simp only [iterOp, Finset.univ_eq_empty, Finset.prod_empty, mul_one]
    congr 1
    exact Subsingleton.elim _ _
  | d + 1, r, hr, F, hF, z, hz => by
    obtain ⟨_, hslice, htail⟩

/-- The several-variable Cauchy coefficients `c_γ = A_r^{[d]}(w ↦ F w ∏ᵢ wᵢ^{-γᵢ})`. -/
noncomputable def polyCoeff (d : ℕ) (r : ℝ) (F : (Fin d → ℂ) → ℂ) (γ : Fin d → ℕ) : ℂ

/-- **Reconstruction**: `∑_γ c_γ z^γ = F z` on the open polydisc, as a `HasSum`. -/
theorem hasSum_polyCoeff : ∀ (d : ℕ) {r M : ℝ}, 0 < r → ∀ {F : (Fin d → ℂ) → ℂ}, SliceHolo d r F →
    (∀ w ∈ closedPolydisc d r, ‖F w‖ ≤ M) → ∀ {z : Fin d → ℂ}, z ∈ openPolydisc d r →
      HasSum (fun γ : Fin d → ℕ => polyCoeff d r F γ * ∏ i, z i ^ γ i) (F z)
  | 0, r, M, _, F, _, _, z, _ => by
    have hval : ∀ γ : Fin 0 → ℕ, polyCoeff 0 r F γ * ∏ i, z i ^ γ i = F z

/-- The Cauchy coefficients are the normalised Taylor coefficients `f^{(n)}(0)/n!`. -/
theorem discCoeff_eq_iteratedDeriv_div {f : ℂ → ℂ} {r : NNReal}
    (hf : DifferentiableOn ℂ f (Metric.closedBall 0 r)) (hr : 0 < r) (n : ℕ) :
    discCoeff f r n = iteratedDeriv n f 0 / (n.factorial : ℂ)

/-- **Headline XXXII, paper-facing form**: the same conclusion from `0 < b < R` alone (the
intermediate radius `r = (b + R)/2` is chosen inside the proof). -/
theorem thm_TaylorTree_analytic' (n : ℕ) (h k : Fin (n + 1) → ℕ) (hk : ∀ i, 0 < k i) (β : ℝ)
    (hβ : 0 < β) {b R : ℝ} (hb : 0 < b) (hbR : b < R)
    {Fξ Fη : (Fin (n + 1) → ℂ) → ℂ} {ξ η : (Fin (n + 1) → ℝ) → ℝ}
    (hFξ : DifferentiableOn ℂ Fξ (openPolydisc (n + 1) R))
    (hFη : DifferentiableOn ℂ Fη (openPolydisc (n + 1) R))
    (hξ : ∀ u ∈ piBox (n + 1) (Ioc 0 b), (Fξ fun i => (u i : ℂ)).re = ξ u)
    (hη : ∀ u ∈ piBox (n + 1) (Ioc 0 b), (Fη fun i => (u i : ℂ)).re = η u) :
    ∃ (cξ cη : CoeffFamily (n + 1)) (C : ℝ → ℕ → ℝ),
      TaylorTreeConclusion n h k β b cξ cη C ∧
      ∀ N, familyPhaseIntegralBox n h k β N b cξ cη = origPhaseIntegral n h k β N b ξ η

/-- The conclusion of the Taylor-tree theorem for a coefficient system `C` on the box `(0,b]^d`. -/
structure TaylorTreeConclusion (n : ℕ) (h k : Fin (n + 1) → ℕ) (β b : ℝ)
    (cξ cη : CoeffFamily (n + 1)) (C : ℝ → ℕ → ℝ) : Prop where
  /-- `C` is the family spectral coefficient of the rescaled data. -/
  coeff_eq : ∀ μ j, C μ j = familySpectralCoeff n h k β (scale cξ b) (scale cη b) μ j
  /-- Support: `C` vanishes off the paper's candidate exponent set `Λ(h,k)`. -/
  vanish : ∀ μ j, ¬ candidateExp h k μ → C μ j = 0
  /-- The explicit series is absolutely convergent (`μ > 0`). -/
  summable : ∀ μ, 0 < μ → ∀ j,
    Summable fun p => |familyCoeffTerm n h k β (scale cξ b) (scale cη b) μ j p|
  /-- `C` equals the paper's Cauchy-product series `∑_p β^p/p! T_p(cη * J^{*p})`, every real `μ`. -/
  series : ∀ μ j, C μ j = familyCoeffSeries n h k β (scale cξ b) (scale cη b) μ j
  /-- Quantitative remainder for every cutoff, with `N b^{2|k|} ≥ 1`. -/
  remainder : ∀ L, 0 < L → ∀ N, 0 ≤ N → 1 ≤ boxScale k b N →
    |familyPhaseIntegralBox n h k β N b cξ cη - b ^ (∑ i, h i + (n + 1)) *
        ∑ μ ∈ latticeBelow (latticeQ k) L, boxScale k b N ^ (-μ) *
          ∑ j ∈ Finset.range (n + 1), C μ j * (Real.log (boxScale k b N)) ^ j| ≤
      b ^ (∑ i, h i + (n + 1)) *
        cutoffBound n k β L (scale cξ b 0) (mass (scale cη b)) (mass (scale cξ b)) *
        (boxScale k b N ^ (-L) * (1 + Real.log (boxScale k b N)) ^ n)
  /-- Asymptotic form in the sample size. -/
  isBigO : ∀ L, 0 < L →
    (fun N : ℝ => familyPhaseIntegralBox n h k β N b cξ cη - boxSpectralSum n h k β L b cξ cη N)
      =O[atTop] fun N : ℝ => N ^ (-L) * (1 + Real.log N) ^ n
  /-- The paper's derivative dictionary for the kernel moments (`μ > 0`). -/
  dictionary : ∀ (a : ℝ) (p : ℕ) (μ : ℝ), 0 < μ → ∀ i : ℕ,
    β ^ p * fluctMoment β a p μ i =
      (-1) ^ i * iteratedDeriv i (fun ν => iteratedDeriv p (fluctuationFn β ν) a) μ

/-- **The Taylor tree for coefficient-family data** (`thm:TaylorTree` / `cor:standardintegralexp`
under `∑ |c_γ| b^{|γ|} < ∞`): one cutoff-independent coefficient system, equal to the paper's
explicit series, with the remainder bound for every cutoff and the derivative dictionary. -/
theorem thm_TaylorTree_coeffFamily (n : ℕ) (h k : Fin (n + 1) → ℕ) (hk : ∀ i, 0 < k i) (β : ℝ)
    (hβ : 0 < β) {b : ℝ} (hb : 0 < b) {cξ cη : CoeffFamily (n + 1)} (hξ : AbsSummableAt cξ b)
    (hη : AbsSummableAt cη b) :
    ∃ C : ℝ → ℕ → ℝ, TaylorTreeConclusion n h k β b cξ cη C
```

## Candidate routes for the derivative identification (my analysis — please correct)

(R-a) **Recursive differentiation under the contour integral.** By definition `iterOp (d+1) r G = circleOp r (fun w₀ => iterOp d r (fun w' => G (Fin.cons w₀ w')))`, so `polyCoeff (d+1) r F (Fin.cons γ₀ γ') = circleOp r (fun w₀ => w₀^{-γ₀} · polyCoeff d r (F ∘ Fin.cons w₀) γ')`. If g(w₀) := polyCoeff d r (F ∘ Fin.cons w₀) γ' is holomorphic in w₀ on a disc of radius > r (differentiation under the circle integral: Mathlib has `hasDerivAt_integral_of_dominated_loc_of_deriv_le`, already used in this project for ∂_a and ∂_μ), then the one-variable result gives `circleOp(w₀^{-γ₀} g) = g^{(γ₀)}(0)/γ₀!`, and by induction g^{(γ₀)}(0) = polyCoeff d r ((∂_0^{γ₀} F)(0, ·)) γ' = ∂^{γ'}(∂_0^{γ₀}F)(0)/γ'!. The formal target would be a **coordinate-recursive iterated derivative** `coordDeriv (d+1) (Fin.cons γ₀ γ') F 0 := iteratedDeriv γ₀ (fun w₀ => coordDeriv d γ' (F ∘ Fin.cons w₀) 0) 0` (partials applied in a fixed coordinate order; no commutation of partials needed), with the theorem `polyCoeff d r F γ = coordDeriv d γ F 0 / ∏ γ_i!` for F differentiable on the open polydisc of radius R > r. Estimated 3–5 units: (1) holomorphy in a parameter of circleOp / iterOp images (parametric differentiation under the integral, iterated); (2) `iteratedDeriv` of a parametric iterOp = iterOp of the iterated partial; (3) assembly + the d = 1 base + real parts; (4) paper-facing corollary that the coefficient formula is in terms of coordDeriv of Fξ, Fη at 0, and for ξ genuinely extended (Fξ = ξ on the real box), that these are the real iterated partials of ξ.

(R-b) **Uniqueness of monomial expansions** on the polydisc (if Σ c_γ z^γ = Σ c'_γ z^γ for |z_i| < r then c = c'), coordinate-wise via `HasFPowerSeriesAt.eq_formalMultilinearSeries`, plus a several-variable Taylor theorem F(z) = Σ ∂^γF(0)/γ! z^γ — the latter is NOT in Mathlib in monomial form (Mathlib's several-variable power series are FormalMultilinearSeries on the normed space Fin d → ℂ; extracting monomial coefficients from symmetric multilinear maps is heavy). Likely 8–15 units. Not recommended.

(R-c) **Leave as a labelled gap** and freeze: the coefficients are explicit, computable, cutoff-free, and equal to the paper's series with Cauchy coefficients in place of Taylor coefficients; a reader who accepts that Cauchy coefficients are Taylor coefficients (standard) has the paper's statement.

## Questions

1. **Freeze or finish?** Given (R-a) at an estimated 3–5 units against a programme that has consumed ~43 units (223–265), is the derivative identification worth doing now, or should the Taylor-tree programme be frozen at pin 45b0943 with (R-c)? Please give a clear recommendation with a gate (what would make you say stop after unit 1 of R-a).

2. **If (R-a): is the coordinate-recursive `coordDeriv` the right formal target?** The paper writes ∂^γ f(0) with no order; holomorphy makes partials commute, but proving commutation in Lean is extra work. Is "fixed-order iterated partials along Fin.cons" an honest rendering of ∂^γ f(0)/γ!? Any pitfalls in stating it (e.g. `iteratedDeriv` of a function ℂ → ℂ that is only differentiable on a ball, vs `iteratedDerivWithin`)? In this project `iteratedDeriv` on an open set was handled via `Filter.EventuallyEq.iteratedDeriv_eq`.

3. **Honesty of the headline.** With the gap as stated, is the sentence "thm:TaylorTree and cor:standardintegralexp are formalised under the paper's own hypothesis in every dimension; the coefficient formula is in terms of the explicit Cauchy coefficients rather than Taylor derivatives" a fair hand-off claim? What exact non-claims should accompany it?

4. **Big picture — after the Taylor tree.** The grammar seabed now has: the normal-block programme (Headlines I–XXI; frozen per your #25), and the Taylor-tree programme (XXII–XXXII). What, if anything, should come next in this seabed, and what should not? Candidates I can see: (a) STOP — publish hand-off and close; (b) the derivative identification (R-a); (c) the paper's §4.3 SLT application (Watanabe-style: free energy asymptotics assembled from charts of a resolution — heavy, needs the chart decomposition as external input, cf. Headline XV); (d) the boundary/Δ tail and general (non-box) domains; (e) posterior weak convergence for the normal-crossing model (your #25 option B, 3–10 units); (f) a second concrete statistical example using the Taylor tree (e.g. a non-constant phase ξ where the coefficient series is genuinely needed, checking a next-order term numerically). Please rank with unit estimates and go/no-go gates, and say plainly if the answer is "stop here".

5. **Anything in the Stage 7 architecture you would flag for the hand-off** (e.g. the `SliceHolo` recursive hypothesis, the torus-bound vs closed-polydisc distinction, the real-part matching hypothesis, or the fact that Lean's contour integrals are totalised)?

Please be concrete and decisive; planning estimates are fine, but say when you are guessing about Mathlib's current API.
