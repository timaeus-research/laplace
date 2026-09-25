# Research round 43 — after the completion principle

You are Astra, advising a Lean 4 / Mathlib formalisation (repo `laplace`, modules `Laplace/Multi/*`) of the response
geometry of an affine exponential family. Everything below is proved (no sorry) unless marked OPEN.

## Setting (unchanged from round 42)
Sample space `X`, measure `μ`, prior density `π > 0`, bounded base loss `L₀`, bounded features `R : ι → X → ℝ`
(`ι` finite), temperature `t > 0`; `P_{t,a} ∝ exp(−t(L₀ + a·R)) π`, `Q_t = P_{t,0}`, prior `π̄ = P_{0,0}`.
`meanMap t a = m_t(a)`, `momentBody K = closure(convexHull(essRange))`. General-law versions: for a probability
law `ν` and bounded `S : J → X → ℝ`, `genRate ν S M = sup_q (q·M − log E_ν e^{q·S})` (ENNReal), `faceMeasure ν F = ν(·|F)`,
`entropyProj ν S M = inf { klDiv ρ ν : ρ probability, E_ρ S = M }` (Mathlib `InformationTheory.klDiv`).

## Landed since round 42 (all sorry-free), following your ranking
1. `ThermalTransport` (your #1): for probability `ν`, bounded `f g`, tilts `ν_s = ν.tilted (s f)` (Mathlib `Measure.tilted`):
   `d/ds E_{ν_s} g = Cov_{ν_s}(g, f)` and `d/ds KL(ν_s‖ν) = s Var_{ν_s} f` (`hasDerivAt_integral_tilted`,
   `hasDerivAt_klDiv_tilted_toReal`). Thermal: `P_{t,a} = π̄.tilted(−t H_a)`, `KL(P_{t,a}‖π̄) = −𝒮(t,a) = ∫₀ᵗ s Var_{s,a}(H_a) ds`,
   `d/dt KL(P_{t,a}‖π̄) = t Var_{t,a}(H_a)`, and at fixed interior `M`: `∂_t 𝓘_t(M) = E_{P_{t,θ_t(M)}} L₀ − E_{Q_t} L₀`
   (also for `entropyProj`).
2. `GroundState` (your #4): fixed `a`, `α = ess inf H_a`, `G = {H_a = α}`: `⟨H_a⟩_{t,a} → α` (under `π(H_a < α+ε) > 0 ∀ε`);
   positive `π̄(G)`: `P_{t,a}(G) → 1`, `|P_{t,a}(A) − π̄(A|G)| ≤ 1 − P_{t,a}(G)`, `KL(P_{t,a}‖π̄) → −log π̄(G) = KL(π̄_G‖π̄)`;
   null `G`: `KL(P_{t,a}‖π̄) → +∞` (monotone in `t` by the transport law; a bound would, via the Bregman tangent bound
   `A_t − (s−t)⟨H⟩_t ≤ A_s` and `⟨H⟩_t → α`, keep `log E e^{−s(H−α)}` bounded below).
3. `RelativeInterior` + `RelativeMomentBody` (your #2): for convex `K ⊆ ℝ^J`, `x ∈ intrinsicInterior ℝ K ↔ x ∈ K ∧ ∃ δ>0,
   ∀ v ∈ direction(affineSpan K), ‖v‖ < δ → x + v ∈ K`, and `↔ x ∈ K ∧ ∀ e, (∀ y ∈ K, e·y ≤ e·x) → ∀ y ∈ K, e·y = e·x`
   (Hahn–Banach on the direction subspace). **`range (θ ↦ E_θ S) = intrinsicInterior ℝ K` with no nondegeneracy hypothesis**
   (`range_meanMap_eq_intrinsicInterior_momentBody`): `⊆` by the supporting characterisation and "a.s. bounded by its own
   expectation ⇒ a.s. constant"; `⊇` by coercivity along the direction subspace `𝕍`, a minimiser on `𝕍`, the first-order
   condition along `𝕍` and `x − m(θ₀) ∈ 𝕍`. No coordinates chosen.
4. `ConditioningChainRule` + `EntropyCompletion` (your #3): `KL(ρ‖ν) = KL(ρ‖ν_F) + (−log ν(F))` for `ρ ≪ ν_F`
   (`klDiv_eq_klDiv_faceMeasure_add`), a law whose mean is on a supporting hyperplane is carried by the face, the affine
   dimension of the moment body strictly drops under conditioning on a proper supporting face
   (`finrank_dirSpan_faceMeasure_lt`), and **the completion principle**: for every `M` with `genRate ν S M ≠ ⊤` there is
   `ρ_M` (probability, mean `M`, `KL(ρ_M‖ν) = 𝓘(M)`) with `KL(ρ‖ν) = KL(ρ‖ρ_M) + 𝓘(M)` for EVERY probability `ρ` with
   mean `M` (`exists_pythagorean_minimiser`; strong induction on `finrank (dirSpan ν 1 S)` over all probability laws with
   the same features), hence uniqueness (`exists_unique_entropy_minimiser`) and `entropyProj ν S M = genRate ν S M` for
   ALL `M` (`entropyProj_eq_genRate`).
   Not yet extracted: an explicit conditioning certificate (chain of nested events `X = A₀ ⊃ … ⊃ A_k`, `k ≤ dim`, the
   minimiser as a tilt of `ν(·|A_k)`); the proof constructs it but the statement only records the minimiser.

Earlier rounds: BoundaryBarrier (rate = ⊤ on ∂K ⇔ all supporting faces null; uniform blow-up), EntropyProjection
(Donsker–Varadhan; `P_{t,a} = Q.tilted(−t a·R)`; `KL(P_a‖Q) = famKL`; interior Pythagoras), FaceTotalVariation, WallRay,
Cramér upper/lower bounds, exposed faces, contraction identity, Schur complement, fluctuation–response, dual potential,
mean journey, bi-Lipschitz stability of the mean map under covariance bounds.

## The user's direction (verbatim, unchanged)
"Continue, but make sure we are tackling core features of the change in posterior expectation values with the change
in the data distribution that allow us to 'map' the space of responses across the data manifold (ideally, all the way
from the 'featureless' distribution of maximal entropy to our actual data distribution). What would it take to do this
with maximum beauty and depth?"

## Questions
1. Re-rank what remains. Candidates: (a) the conditioning certificate as an explicit structure with telescoping entry
   costs and length ≤ dim; (b) your #5 stratified stability (intrinsic bi-Lipschitz and KL bounds under covariance
   bounds on the direction subspace; Pinsker for responses); (c) your #6 dual connections and the cubic tensor
   (`∂_k V_ij = −t T_ijk`, mixture geodesics `a'' = t V⁻¹ T(a',a')`); (d) "reaching the actual data": for a data law
   `D = π̄.tilted f` with bounded `f`, the path `s ↦ π̄.tilted (s f)`, its response trajectory `M(s)`, `KL(D‖π̄) = ∫₀¹ s Var ds`,
   and the identification of `entropyProj` along it — what exact statement expresses "the map of responses from
   maximal entropy to the data" most completely? Is the joint moment body of `(L₀, R)` (the "data manifold") with the
   thermal path as a curve in it the right object, and what is its intrinsic-chart statement now that the relint
   theorem exists (the joint family needs no `hjnd` anymore)? (e) the conditional response charts on positive faces
   as instances of the relint theorem for `ν_F` (already implied — what is worth stating?); (f) anything deeper.
   Give at most six targets, each with a precise Lean-flavoured statement, proof sketch at the level of the lemmas
   above, expected Mathlib API, pitfalls.
2. The completion induction quantifies over all probability laws on `X` with the same features; the certificate would
   need the events to be exposed "in the current conditional body". What is the cleanest Lean data structure for the
   certificate (a `List` of events with a `Forall₂`-style predicate? an inductive predicate `ExposedChain ν S A`?), and
   which telescoping lemma should be stated first?
3. Corrections: flag anything suspicious in the statements above (in particular the ENNReal Pythagoras at boundary
   points for laws not `≪ ν`, where both sides are `⊤`).
