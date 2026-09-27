# Round 85: the response atlas over the data manifold — what is the unifying statement, and what is deepest next?

## Landed since round 84 (all sorry-free; `Laplace/Multi/*`, timaeus-research/laplace, main)

Your round-84 ranking, with what each became:

1. `AccessibleFaceStrata` (rank 3): `Π(m_A(v)) = P^A_v` (boundary KL Pythagoras + uniqueness of the information
   projection); one extended mean in `ri(face body)` ⇒ all of it is accessible, any codimension, from an arbitrary
   accessible point (no normal ray). Accessible extended means = union of relative face interiors.
2. `ResponsePullbackForm` (ranks 1+2 merged). For ANY bounded tilt `ρ_g ∝ e^g ν` and bounded `k`:
   `dirSpan (ν.tilted g) = dirSpan ν` (tilt invariance of `W`); `forcing g k := Cov_{ρ_g}(S,k) ∈ W`;
   `responseOf g := θ(E_{ρ_g}S)`; `responseVel g k := (Dm(Φ(g))|_W)⁻¹ forcing`; `pullbackForm g k := |responseVel|²_F`;
   `pullbackForm = −⟨responseVel, forcing⟩ = Cov_{ρ_g}(⟨−responseVel,S⟩, k)`; `pullbackForm ≥ 0`;
   `pullbackForm = 0 ↔ forcing = 0` (kernel = covariance-invisible directions);
   relative-covariance amplification: `(∀w, Var_{ρ_g}⟨w,S⟩ ≤ κ Var_{P_Φ}⟨w,S⟩) ⇒ pullbackForm ≤ κ Var_{ρ_g} k`;
   at a MATCHED law `ρ_g = P_{Φ(g)}`: `k_vis := ⟨−responseVel,S⟩` is the regression of `k` on `S`
   (`Cov(⟨e,S⟩,k_vis) = Cov(⟨e,S⟩,k)` ∀e), `Var k = pullbackForm + Var(k − k_vis)`, `Cov(k − k_vis, ⟨e,S⟩) = 0`,
   `pullbackForm ≤ Var k`.
   (Only the quadratic form `G(k,k)`; the bilinear `G(k,ℓ)` is not stated.)
3. `FisherNormalisedSampling` (rank 4), basis-free as you suggested: a linear retraction `p : (J→ℝ) →ₗ W` exists;
   `samplingOp θ p := ι ∘ (Dm(θ)|_W)⁻¹ ∘ p`; `samplingEnergy θ p z := −⟨samplingOp z, z⟩`;
   on `W`: `samplingEnergy = fisherVar θ ((Dm|_W)⁻¹ z)` (retraction-independent);
   `matchedOp θ := ι ∘ (Dm|_W)⁻¹ ∘ Dm` is a projection onto `W` (`LinearMap.IsProj`), `trace = finrank W`;
   `E samplingEnergy(M̂_n − m) = −Σ_{ab} (R_θ)_{ab} Cov_D(S_a,S_b)/n = −tr(R_θ C_D)/n` (any data law `D`, `n` iid samples);
   at `D = P_θ`: `E samplingEnergy(M̂_n − m) = finrank W / n`.
   (Sign convention: `Dm = −C`, so `samplingOp = −R_θ` in your notation and the energy is `+zᵀC⁻¹z` on `W`.)
4. `ResponseLocalTesting` (rank 5), your elementary local converse: `|⟨w, m(θ)−m(η)⟩| ≤ 2‖⟨w,S⟩−c‖_∞ H(θ,η)`
   (Cauchy–Schwarz on `(q_θ−q_η)(q_θ+q_η)(⟨w,S⟩−c)`, `∫(q_θ+q_η)² ≤ 4`); `‖m(θ)−m(η)‖₂ ≤ 2B H` for `‖S−a‖₂ ≤ B`;
   on a coercive convex patch `U ⊆ ri` (`λ⟨w,w⟩ ≤ Var_{P_θ(M)}⟨w,S⟩`, `M ∈ U`):
   `√λ d_F(θ(M₀),θ(M₁)) ≤ 2B H(P_{θ(M₀)},P_{θ(M₁)}) ≤ B d_F(θ(M₀),θ(M₁))`; affinity `∫q_θq_η = 1 − H²/2`,
   `A^n ≤ exp(−nH²/2) ≤ exp(−nλ d_F²/(8B²))`. (No TV/testing-error statements: the seabed has no testing framework.)
5. `ResponseClassResolution` (rank 9), abstract class partition: for a class `C ∋ m = E_D S` with Fisher margin `r`
   (`∀ z ∈ W, samplingEnergy θ p z < r² → m + z ∈ C`): `M̂_n − m ∈ W` a.s., Markov ⇒
   `P(M̂_n ∉ C) ≤ −tr(R_θC_D)/(n r²)`, and `≤ finrank W/(n r²)` at `D = P_θ`.

Not done from round 84: `TiltedFisherCompactConvergence` (6), `AccessibleFaceNonexpansion` (7),
`FaceChainAccessibility` (8), `ResponsePathLengthBudget` (10), the bilinear form `G(k,ℓ)`, the Hellinger form of the
compactification.

Earlier layer (for reference): completion `Ŵ` of `(W, d_F)`; `Q_x = Π(meanExt x)` for every completion point;
`M ↦ Π(M)` closed embedding of the closed polytope into `L¹(ν)`; along `ρ_t ∝ e^{th}ν`, `Q_{[θ_t]} = Π(E_{ρ_t}S) → Π(E[S|h=H])`;
uniqueness of the completion fibre over every charged face interior; bounded-tilt action `tiltExt` on `Ŵ`;
`H ≤ ½ d_F`; the data/response resolution floors.

The standing direction is unchanged: "map the space of responses across the data manifold, ideally all the way
from the featureless distribution of maximal entropy to the actual data distribution, with maximum beauty and
depth", and the user's resolution story (two shifts of the structural coordinate — from varying the truth and from
sampling — and chambers that cannot be resolved when the sampling variance exceeds their size).

## Questions

### Q1. The unifying statement
With the differential (`ResponsePullbackForm`), the noise floor (`FisherNormalisedSampling`), the local testing
metric (`ResponseLocalTesting`) and the chamber bound (`ResponseClassResolution`) all landed, is there now ONE
theorem about the response map `Φ : {bounded tilts of ν} → Ŵ` that the seabed can state and prove and that deserves
to be the centrepiece of the note's response-map section? Candidates I see:
(a) `Φ` as a "Riemannian submersion up to a factor": for the data Fisher metric `G^{data}_g(k) = Var_{ρ_g} k` and the
    response Fisher metric, `G^{resp}_g(k) ≤ κ_g G^{data}_g(k)` with equality on the horizontal space at matched laws
    (the score decomposition), kernel = vertical = covariance-invisible. Is there a clean statement of "horizontal
    lift" (every response tangent vector `v ∈ W` is `DΦ_g[k]` for the horizontal `k = ⟨−v,S⟩`-type contrast) that
    closes the picture (`DΦ_g` surjective onto `W`, with a canonical right inverse)?
(b) A length/distance comparison along arbitrary bounded-tilt paths `g_t`: `d_F(Φ(g_0),Φ(g_1)) ≤ ∫ √(G^{resp}_{g_t}(ġ_t)) dt`
    (this is `ResponsePathLengthBudget`), and the consequence: a finite-energy path in the data manifold has a
    response endpoint in `Ŵ` whose law is `Π` of the limiting mean.
(c) The "resolution theorem" proper: for two data laws `ρ, ρ'` on the data manifold with `d_F(Φ(ρ),Φ(ρ')) = δ`, the
    structural coordinates from `n` samples of each are separated with probability `≥ 1 − 2 finrank W/(n δ²)`-type
    bounds when `δ ≫ √(finrank W/n)` (using the class bound with `C` = a Fisher ball), and indistinguishable
    (affinity) when `δ ≪ 1/√n`. Which precise formulation is both true and provable from the landed pieces?
Please state the theorem you would put at the centre, with hypotheses matching what is landed.

### Q2. Compact-uniform convergence of the covariance forms (`TiltedFisherCompactConvergence`)
Give the Lean-level route: from `L¹(ν)` convergence of laws `Q_n → Q` (bounded densities?) to uniform convergence of
`w ↦ Var_{Q_n}⟨w,S⟩` on compacts of `W`, and of the pull-back forms along bounded tilts. Which hypotheses are
needed (uniformly bounded tilts `|g_n| ≤ K`?), and what is the payoff theorem (continuity of `g ↦ G^{resp}_g` in the
data law; hence continuity of the Fisher-normalised noise floor and of the class margins along the data manifold)?

### Q3. The length budget in multi-parameter form (`ResponsePathLengthBudget`)
State precisely: for a `C¹` path of bounded tilts `g : [0,∞) → {bounded functions}` with `sup_t ‖g_t‖_∞ < ∞`? or
only with the pull-back speed integrable, `∫_0^∞ √(G^{resp}_{g_t}(ġ_t)) dt < ∞ ⇒` the response path is Fisher-Cauchy,
converges in `Ŵ`, and the limit's law is `Π(lim E_{ρ_{g_t}} S)`. What is the minimal hypothesis package given the seabed
(`fisherDist_le_integral` needs `FisherPath`-type `C¹` data in `W`; the response path `t ↦ Φ(g_t)` is `C¹` by the
chart's inverse function theorem on the interior)?

### Q4. Nonexpansion and face chains (`AccessibleFaceNonexpansion`, `FaceChainAccessibility`)
Given `AccessibleFaceStrata` (accessibility of a whole open face from one point, no ray), what remains of value in
7 and 8? Is the nonexpansion `d̂(j_F v, j_F w) ≤ d_F^{(F)}(v,w)` still needed for anything downstream, or is the
picture of "accessible extended means = union of relative face interiors, each reached uniquely" already the final
one, with only the *criterion* for which faces are accessible (finite normal ray for facets; general faces?) open?

### Q5. Ranked list
Rank the next 8–10 modules (Lean-sized, with statements) by depth × reachability for the standing direction, and
say what the note's response-map section should now claim as its main theorems (with the Lean names above).

### Q6. Corrections
Any of the landed statements above that are weaker than they should be, mis-signed, or that you would restate?
In particular: is `pullbackForm ≤ Var k` at matched laws the right "contraction" (the data Fisher metric dominates
the response Fisher metric on matched laws), and should the class margin be defined through the Fisher ball in `W`
(as done) or through a Hellinger ball of laws?
