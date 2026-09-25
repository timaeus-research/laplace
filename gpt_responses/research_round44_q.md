# Round 44: mapping responses across the data manifold — what remains for depth and beauty

You are advising a Lean 4 / Mathlib formalisation (laplace repo, `Laplace/Multi/*`). The user's standing direction:
"make sure we are tackling core features of the change in posterior expectation values with the change in the data
distribution that allow us to map the space of responses across the data manifold (ideally, all the way from the
featureless distribution of maximal entropy to our actual data distribution). What would it take to do this with
maximum beauty and depth?"

## Setting (formalised)
Finite measure `ν` on `X`, statistics `S : J → X → ℝ` (J finite), a.e.-bounded. Affine family
`P_{t,a} ∝ exp(−t(L₀ + a·R)) π` (`familyMeasure`), `meanMap`, `affLogZ`, `famKL`, `rateFun` (Cramér transform of the
CGF), `momentBody μ π S := closedConvexHull(essRange)` (compact convex), `dirSpan := direction of its affine span`
(the "visible subspace" 𝕍), `intrinsicInterior`. General-law objects (π := 1): `genRate ν S M`, `faceMeasure ν F`
(conditioning), `entropyProj ν S M := ⨅_{ρ prob, E_ρ S = M} klDiv ρ ν`. Mathlib `InformationTheory.klDiv` throughout.

## Landed (all sorry-free)
- FaceTotalVariation: `P_{t,ta} → faceLaw` as t→∞ along rays (TV on sets).
- BoundaryBarrier: `rateFun = ⊤` on the frontier of the moment body (under a null-hyperplane hypothesis), compact
  sublevel sets, `rateFun → ⊤` near the frontier.
- EntropyProjection: Donsker–Varadhan `∫f dρ − log∫e^f dν ≤ KL(ρ‖ν)`; `klDiv (ν.tilted f) ν` formula;
  `genRate_le_entropyProj`, `entropyProj_le_klDiv`; Pythagoras `klDiv ρ Q = klDiv ρ P_a + klDiv P_a Q` when E_ρ S = M(a);
  `klDiv_eq_rateFun_iff`.
- ThermalTransport: derivative in the scalar tilt `s` of `∫ g dν_s`, of `klDiv (ν_s) ν` (= s·Var), of relEntropy,
  rateFun and entropyProj in temperature.
- GroundState: t→∞ concentration on the face of minimal loss; KL to prior limits; null-face divergence.
- RelativeInterior / RelativeMomentBody / IntrinsicChart: `range meanMap = intrinsicInterior(momentBody)`;
  `intrinsicChart : dirSpan ≃ intrinsicInterior K` (bijection natural coordinates θ ∈ 𝕍 ↔ responses M).
- ConditioningChainRule: `klDiv ρ ν = klDiv ρ (ν_F) + (−log ν F)` for ρ ≪ ν supported in F; conditioning on an exposed
  face drops finrank of dirSpan.
- EntropyCompletion: Pythagorean minimiser `ρ_M` exists for every M with finite genRate; unique; `entropyProj = genRate`.
- DataResponseMap: `responseProjection ν M` (canonical representative); **information decomposition**
  `klDiv D ν = genRate ν S (E_D S) + klDiv D (Π (E_D S))` for every finite-information data law D; the exponential data
  path `ν.tilted (s·f)` has mean in the relative interior with explicit derivative; `Π(ν_F) = ν_F`.
- ConditioningCertificate: `ExposedChain` (iterated exposed-face conditioning), rate preserved along the chain,
  `Π_ν M = familyMeasure (ν_A) 1 0 S 1 θ` with θ ∈ dirSpan(ν_A): every representative is an exponential tilt of a
  conditioned ν.
- MixtureBridge (just landed): `klDiv` convex in its first argument (`klDiv (a•ν'+b•ρ) ν ≤ a klDiv ν' ν + b klDiv ρ ν`),
  `genRate ν S ((1−s)m₀ + sM) ≤ s · genRate ν S M`, monotone in s, path in relint for s<1,
  `genRate(M_s) → genRate(M_D)` as s↑1 (lower semicontinuity + convexity).

## Open items from your round-43 ranking
- 2b: quantitative stability of the intrinsic chart on 𝕍 (Lipschitz/Hölder of θ ↦ M restricted to 𝕍, or of M ↦ θ).
- 6: the cubic tensor ∂³A and dual (e/m) connections; the "response manifold" as a dually flat space.
- TV convergence of representatives Π(M_s) → Π(M_D) at the endpoint (needs Pinsker; Mathlib has no Pinsker — is there a
  route via `klDiv` = `fDiv` and Mathlib's `InformationTheory` files? Or via the Pythagorean identity and
  `klDiv_eq_zero_iff` + a compactness/`lowerSemicontinuous` argument on densities?).
- Differentiability of the chart on 𝕍 (Fréchet derivative = covariance restricted to 𝕍, invertible on 𝕍).

## Questions
1. Given the user's direction (map the responses from the featureless law to the data law, with maximum beauty and depth),
   what are the 4–6 most valuable NEXT theorems, ranked, with precise statements (Mathlib-flavoured) and hypothesis lists?
   Prefer theorems that are (a) genuinely about the data→response map, (b) provable from the landed layer plus Mathlib
   (Lean v4.33.0, recent Mathlib), (c) beautiful as statements.
   Candidates I'm weighing: (i) Pinsker via `klDiv` and `fDiv`/`totalVariation` if any such lemma exists; (ii) the
   "featureless-to-data" geodesic: the m-geodesic (mixture path) vs the e-geodesic (tilt path) between ν and D, and the
   statement that the response map sends the e-geodesic to a straight segment in θ and the m-geodesic to a straight segment
   in M (both already essentially formal: `mean_mixture`, `familyMeasure_eq_tilted`), assembled as a "dually flat"
   theorem; (iii) the generalised Pythagorean theorem for a general pair (e-flat, m-flat) — we have it at the projection;
   (iv) covariance = Hessian of the CGF restricted to 𝕍, positive definite on 𝕍 → local inverse function theorem →
   the chart is a C¹ diffeomorphism on 𝕍 (Mathlib has `HasStrictFDerivAt.toPartialHomeomorph`); (v) the maximum-entropy
   characterisation of the responses of the featureless law m₀ = E_ν S: genRate = 0 iff M = m₀ (probably a 5-line
   corollary of `klDiv_eq_zero_iff`); (vi) the "information gained per unit response": the derivative of genRate along
   the mixture path at s=0 is 0 and along the tilt path is Var (already have Thermal); a global comparison
   genRate(M_D) ≥ (1/2)|M_D − m₀|²/(sup Var) type bound (a reverse Pinsker on responses — from Cramér/Chernoff?
   Mathlib has `ProbabilityTheory.measure_ge_le_exp_mul_mgf`).
2. For each, the key Mathlib lemma names you are confident exist (say "unsure" if not).
3. Any statement above that is FALSE as I've phrased it? Please stress-test (v) and (vi).
Answer with a ranked list; be concrete.
