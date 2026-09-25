# germbij — research consult, round 21: audit of the singular response layer and the next deep step

Landed since round 20 (all sorry-free, laplace `Laplace/Multi/`):

- `TermScoreResponse.lean`: exponential-form term `dμ_a = H e^{-B U_a(u∞) P} dm`; `ScoreData` (nonneg measurable `H, P`, measurable face map, bounded `hᵢ`, `B > 0`, `U_a ≥ c > 0`); envelope `|φ| H (1+P) e^{-B(c/2)P}` integrable ⇒ `D_v ∫φ dμ_a = −∫ φ S_v dμ_a` with `S_v = B R_v(u∞) P` (`hasDerivAt_termCoef`) and `D_v ⟨φ⟩_{μ̄_a} = −Cov_{μ̄_a}(φ, S_v)` (`hasDerivAt_termPosterior`).
- `GammaFaceMarginal.lean`: `∫₀^∞ z^{β−1} e^{-bz} = b^{-β}Γ(β)`; `gamma_score`: `∫ z^{β−1}(BRz)e^{-BUz} / ∫ z^{β−1}e^{-BUz} = βR/U`; product-domain term `(u,z)` with weight `w(u) z^{β−1}`, profile `z`: `termCoef = Γ(β)B^{-β} faceCoef (φw)` and the score-weighted integral `= Γ(β)B^{-β} β ∫ φ w U^{-β-1} R_v` (Fubini on `ν.prod (volume.restrict (Ioi 0))`).
- `AssembledResponse.lean`: for finitely many terms on a common base `(X,m)` with common unit family: `D_v (∑_k∫φdμ_k)/(∑_k μ_k(X)) = −(∑_k∫φS_k dμ_k − ⟨φ⟩ ∑_k∫S_k dμ_k)/∑_k μ_k(X)` (your "single most valuable" in scalar form).
- `HigherResponse.lean`: `(d/ds)^n ∫φ e^{-tL_s}π = (−t)^n ∫φΔ^n e^{-tL_s}π`; `priorExp_const` (neutral base ⇒ posterior = prior).
- `MixtureSeries.lean`: `∫φ e^{-tL_s}π = ∑_n (−ts)^n/n! ∫φΔ^n e^{-tL₀}π` (HasSum, all `s`), so `Z_t(L_s)` is entire in `s`.
- `WallSecondCrossover.lean`: `tZ(t,c/t) − log t → −log c − E₁(c)` (your second crossover).
- `ThermoLengthIntegral.lean`: `|⟨φ⟩_{s₁}−⟨φ⟩_{s₀}| ≤ ∫_{s₀}^{s₁} √Var_s(φ)√g_s ds` along a C² path.
- `GibbsUniqueness.lean`: `KL(ρ‖ρ_t) = 0 ⇒ ρ = ρ_t` a.e.; the variational bound is attained only at the posterior.

Still open: the instantiation of `ScoreData` on an actual `termDensity` of the atlas (the unit is a field of the `Phase` record; needs a family of phases affine in the weight); the uniform asymptotic bridge (interchange of `t → ∞` with `D_v`); WallProfileUniform (general fixed-wall rescaling); cumulant identification of the normalised all-orders derivatives; the `√t` degeneration of the thermodynamic length.

## Questions

1. **Audit** of the new statements: `TermScoreResponse` (is the envelope hypothesis `|φ|H(1+P)e^{-B(c/2)P} ∈ L¹` the natural one, and does `ScoreData` capture the atlas term correctly — in particular the requirement `U_a ≥ c` EVERYWHERE on the face space rather than on the support of `H`?), `GammaFaceMarginal` (is `w(u) z^{β−1}` with profile `z` the right product-domain model, i.e. does the scaled coordinate of a real atlas term enter exactly as `z^{β−1} e^{-B U z}` after the change of variables, and where do the `Q`-monomial cut and the truth constraint go?), `AssembledResponse` (the common-base-space simplification: is the disjoint-union covariance really recovered, including the relative-mass term?), `MixtureSeries` (fine?).

2. **The uniform asymptotic bridge.** We now have at finite `t`: `D_v⟨φ⟩_{t,a} = −t Cov_{t,a}(φ, R_v)`, and in the limit: `D_v⟨φ⟩_{∞,a} = −Cov_{μ̄_a}(φ, S_v)`. What is the cleanest theorem that connects them — i.e. under what hypotheses does `t Cov_{t,a}(φ, R_v) → Cov_{μ̄_a}(φ, S_v)`? Is it a statement about the rescaled observable `t R_v(w) = t R_v(u∞) + …` restricted to the scaled coordinates (so that `t R_v` converges to `B R_v(u∞) P` in the coupled scaling), and can it be obtained from the existing term theorems (`tendsto_fibre_expectation`, `tendsto_modelKernel`) by applying them to the observable `t R_v · φ`? What is the minimal instance (e.g. the trace regime, or the 1D `w⁴ + s w²` example where everything is explicit) to prove first?

3. **The `Phase` family.** To instantiate `ScoreData` on the atlas, we need the unit `a(z)` of the phase to be `U_a(z) = ∑ aᵢ hᵢ(z)` for a mixture. Is the right move (a) a constructor `Phase.mixture` producing a Phase for `∑ aᵢ fᵢ` from Phases of the `fᵢ` sharing the same chart data (same `kF, hJ, wt, b`, units `a_i` adding to `∑ aᵢ a_i`), with the `bounds` field needing `a_i ≥ 0` and weights bounded below, or (b) a general "affine family of phases" abstraction? What breaks: `Phase.bounds` (upper/lower bounds on units), `dens_eq`, positivity of `B`?

4. **The general two-monomial wall.** For `Z(t,s) = ∫₀^∞ e^{-t(w^p + s w^q)} dw` (`p > q > 0` real), `s = t^{-σ}`, the exponent is `λ(σ) = max(1/p, (1−σ)/q)` with wall `σ* = 1 − q/p`, the profile in `c = s t^{1−q/p}` is exact (`t^{1/p} Z = ∫ e^{-(y^p + c y^q)}`), and both regimes follow by DCT. Is this the right "first abstract" instance of WallProfileUniform, or should the first abstraction be the 2-monomial, d-dimensional positive orthant chart with density `x^{b−1}` (`Z = ∫_{(0,1)^d} x^{b−1} e^{-t(x^α + t^{-σ} x^{α'})}`) — and what exactly is the statement with the chart cut `(0,1)^d` (does the cut produce the second crossover, as in the log example)?

5. Rank the next five packages and name the single most valuable theorem now.
