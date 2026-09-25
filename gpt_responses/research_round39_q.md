# Research consult, round 39 (germbij / laplace `Laplace/Multi/*`)

Same programme (PI: "core features of the change in posterior expectation values with the change in the data
distribution; map the space of responses across the data manifold, from the featureless distribution of maximal
entropy to the actual data distribution; maximum beauty and depth"). All formal, sorry-free, on `main`.
Conventions as in round 38: `P_{t,a} ∝ exp(−t(L₀ + a·R)) π`, `A_t(a) = log Z`, `m_t(a) = ⟨R⟩`, Lean's
`featCov = Cov_{t,a}(R,R)` (so your `C = t Cov` is `t·featCov`), natural coordinates `θ = (t, ta)`, `S = (L₀, R)`,
`G_θ = Cov_θ(S,S)`, `𝒮(θ) = −KL(P_θ ‖ π̄)`, dual potential `I(y) = −t⟨θ(y),y⟩ − A(θ(y))` on the slice response space.

## Landed since round 38 (your ranking: 1 duality + two journeys, 2 global quotient, 3 stability, 4 LD upper,
## 5 contraction/log-det, 6 walls) — ALL FIVE DONE

1. `MeanJourney` (slice): `meanLine y₀ d s = θ(y₀ + s d)` with `d/ds a(s) = −(1/t) Cov⁻¹ Δ`; the inverse-covariance
   form `q(s) = Δ·Cov_{a(s)}⁻¹Δ = Var(R_{Cov⁻¹Δ}) ≥ 0` is the second derivative of `I` along the mean segment;
   `KL(P_{a₁}‖P_{a₀}) = ∫₀¹ (1−s) q(s) ds` (m-journey), paired with the e-journey `t²∫₀¹ s Var_{a₀+sv}(R_v) ds`;
   Jeffreys `KL+KL = ∫₀¹ q`; `(∫√q)² ≤ Jeffreys`; `meanEntropy M := −KL(P_{θ(M)}‖P_{t,0}) = I(m(0)) − I(M)` is
   concave on the response space, `d/ds = t⟨Δ, a(s)⟩`, `d²/ds² = −q`, antitone along the mean journey from `m(0)`.
2. Global quotient: was already in the seabed (`meanMap_eq_iff_invisible : m_t(a) = m_t(b) ↔ b − a ∈ invisible`).
3. `ResponseStability`: with the covariance form `w·Cov_a w = Var_a(R_w)` and its Cauchy–Schwarz inequality; under
   `α‖w‖² ≤ Var_a(R_w) ≤ β‖w‖²` (for all a): `2α KL ≤ ‖Δm‖² ≤ 2β KL` (mean side), `t²α‖Δa‖² ≤ 2KL ≤ t²β‖Δa‖²`
   (natural side), hence bi-Lipschitz `αt‖Δa‖ ≤ ‖Δm‖ ≤ βt‖Δa‖`; unconditional Lipschitz with `β = ∑ Mᵢ²` for
   `|Rᵢ| ≤ Mᵢ`.
4. `FullMeanGeometry`: the joint family IS the affine family `(L₀ := 0, R := S, t := 1)`, so everything instantiates
   under joint nondegeneracy `hjnd` (no nontrivial combination of `L₀, Rᵢ` a.s. constant): `fullMean θ = ⟨S⟩_θ`,
   `𝒮(θ) = meanEntropy_joint(fullMean θ)`, **𝒮 concave in full mean coordinates**, gradient `θ`, Hessian `−G⁻¹`
   along full mean segments, `∫₀¹ s G_{sθ}(θ,θ) ds = KL(P_θ‖π̄) = ∫₀¹ (1−s) Δ·G⁻¹_{θ(μ(0)+sΔ)}Δ ds` with
   `Δ = μ(θ) − μ(0)`, entropy antitone along the full mean journey. Zero new analysis.
5. `AsymptoticUpperBound`: compact `F`: `∀ε>0 ∃N₀ ∀n≥N₀, P(R̄_n∈F) ≤ e^{−n(α−ε)}`; log form under positivity.
6. `ContractionIdentity`: κ₃ multilinear over feature combinations; `κ₃(φ,ψ,χ) = Cov(φ,(ψ−⟨ψ⟩)(χ−⟨χ⟩))`;
   `K = Cov⁻¹ T Cov⁻¹` with `T_pq = κ₃(H,R_p,R_q)`, `K_ij = κ₃(H, R_{Cov⁻¹eᵢ}, R_{Cov⁻¹eⱼ})` (the response block);
   `tr(Cov·K) = tr(T Cov⁻¹) = Cov(H, ZᵀCov⁻¹Z)`; Jacobi: `d/dt log det Cov(t,M)|_M = −tr(Cov·K)` (with Lean's
   Cov, not tCov — the `t` factors differ from your normalisation by the constant `log tⁿ`, whose derivative is `n/t`,
   so in your `C = tCov` normalisation `−∂_t log det C = tr(Cov K) − n/t`; please confirm).
Audit corrections applied to the note: `dataLoss'` is the expected BASE loss (its gradient `−t Cov(L₀,R_{Lh})`,
Hessian `t²κ₃`), the mixture bending tensor for mean-coordinate velocities is `t² mixBend`, the concave potential with
Hessian `−G⁻¹` lives in full mean coordinates (item 4), on the slice `−KL(P_{θ(M)}‖P_{t,0})` is concave with Hessian
`−Cov⁻¹` (Lean normalisation).

## Questions
1. **Audit** items 1, 3, 4, 6. (a) Is `hjnd` (joint nondegeneracy) exactly the right hypothesis for the full mean chart,
   and is the range of `fullMean` (= interior of the joint moment body, by the landed `range_meanMap_slice` applied to
   the joint family) the correct full mean domain? (b) In item 3 the ellipticity is assumed for ALL `a`; is the
   convex-region version (segment in the region) worth the extra bookkeeping, and is the natural-side bound
   `t²α‖Δa‖² ≤ 2KL` the sharp form of "quantitative identifiability"? (c) Item 6 normalisation as stated.
2. **What is now the most beautiful/deep missing piece?** Candidates I see: (i) the relation between the slice geometry
   and the full geometry — the slice m-journey is the full m-journey constrained to `⟨L₀⟩` free? (the temperature slice
   as a constrained minimum was landed earlier: `slice_variational`); a Pythagorean decomposition of the full journey
   into the slice journey and the temperature leg; (ii) entropy production along ARBITRARY paths in mean coordinates
   `d𝒮/ds = ⟨θ(s), μ'(s)⟩` (the m-side of the landed `d𝒮 = −G(θ,·)` in natural coordinates) and the "work–heat"
   decomposition; (iii) the closed-set LD upper bound via exponential tightness (bounded features ⇒ `R̄_n` in a
   compact box, so the closed case is the compact case intersected with the box — is that all?) and the matching
   open-set lower bound from `tilt_lower_bound` + the global chart (every interior point is a tilted mean); (iv) walls,
   split into mechanisms (integrability loss at the natural boundary; covariance degeneration; mean escape to a face;
   inverse-chart failure) — which mechanism is the sharpest first formal target, and what is its statement?; (v) the
   response curvature `D²m = t²κ₃` as the mixture second fundamental form in natural coordinates and the α-family of
   connections; (vi) a "fluctuation–response" theorem for the empirical response: the covariance of the empirical mean
   of the posterior sample equals (1/n) times the response form — connecting the finite-n sampling side with the
   geometry. Please rank (i)–(vi) plus anything I missed, and for the top pick give the theorem bundle in Lean-friendly
   form with pitfalls, as before.
3. **Consolidation**: the note now has 40+ Lean paragraphs after the seven-theorem overview. Should the overview be
   updated to reflect the duality capstone (mean journey / full mean geometry) as theorem V's precise form, and what
   would you change in the seven-theorem statement?
