# Research consult, round 38 (germbij / laplace `Laplace/Multi/*`)

Same programme (PI: "core features of the change in posterior expectation values with the change in the data
distribution; map the space of responses across the data manifold, from the featureless distribution of maximal
entropy to the actual data distribution; maximum beauty and depth"). All formal, sorry-free, on `main`.
Conventions: family `P_{t,a} ∝ exp(−t(L₀ + a·R)) π`, `A_t(a) = log Z`, `m_t(a) = ⟨R⟩`, `C = t Cov(R,R)` response form
(Fisher metric in `a`), natural coordinates `θ = (t, ta)`, joint statistic `S = (L₀, R)`, featureless point `θ = 0`
(the prior `π̄`), `𝒮(θ) = −KL(P_θ ‖ π̄) = θ·m(θ) + A(θ) − A(0) ≤ 0`, `d𝒮 = −G(θ,·)`.

## Landed since round 37 (your ranking: 1 canonical data assignment, 2 journey theorem, 3 mixture second
## fundamental form, 4 contraction/log-det, 5 tilt lower bound, 6 asymptotic form, 7 walls)

1. Canonical data assignment — DONE (`DataLocus`): for the finite mixture family `ν_w = ∑ w_j ν_j` the data map
   `d ↦ a(d) = ∑_j d_j a_j` is a CLM `dataCoeff : (J → ℝ) →L (ι → ℝ)`; `dataResponse d = m_t(a(d))`,
   `dataMetric d h k = G_{a(d)}(Lh, Lk)`, `dataLoss' d = h(t, a(d))`, `dataEntropy d = 𝒮(t, a(d))`;
   `HasFDerivAt dataResponse` with derivative `h ↦ −t Cov(R, R_{Lh})`; **kernel of the differential = invisible
   directions exactly** (`dataResponse_deriv_eq_zero_iff`: `D dataResponse[h] = 0 ↔ Lh ∈ N^⊥`, i.e. `R_{Lh}` a.s.
   constant), `dataResponse_add_of_invisible`; `dataMetric_self_eq_zero_iff`; pullback landscapes:
   `hasFDerivAt_dataLoss` (`D dataLoss'[h] = ⟨R_{Lh}⟩`), `hasDerivAt_dataLossGrad_line` (`t²κ₃(L₀,R_{Lh},R_{Lk})`),
   `hasDerivAt_dataEntropy_line` (`−t²Cov(L_w, R_{Lk})` where `L_w` is the current tilt observable).
2. Journey theorem — DONE (`NaturalJourney`): along the natural ray `θ(s) = s θ₁` from the featureless point:
   `d/ds 𝒮 = −s·natForm(θ₁,θ₁)` (so `𝒮` is antitone), `𝒮(θ₁) = −∫₀¹ s Var_{sθ₁}(θ₁·S) ds`,
   `|⟨φ⟩_{θ₁} − ⟨φ⟩_0| ≤ ∫₀¹ √natForm ‖…‖` (length bound), arcsine version, and the decomposition
   `𝒮(t,a) = 𝒮(t,0) − KL(P_{t,a}‖P_{t,0}) + t(⟨L₀⟩_{t,a} − ⟨L₀⟩_{t,0})`.
3. Mixture bending — DONE (`MixtureBending`): with centred features `R̃ᵢ = Rᵢ − mᵢ` and whitened directions
   `W_v = R̃_{C⁻¹v}` (so `⟨W_v W_w⟩ = v·C⁻¹w/t`), `prodObs v w = W_v W_w`, `mixBend v w = W_v W_w − ⟨W_v W_w⟩ −
   (∑ᵢ ⟨R̃ᵢ W_v W_w⟩ · R̃_{C⁻¹eᵢ}·t)` = the residual of `W_v W_w` after projecting on constants and the tangent
   space `span R̃`; `⟨mixBend⟩ = 0`, `⟨R̃ᵢ · mixBend⟩ = 0` (orthogonal to tangent), and
   `⟨(residual of any φ) · mixBend v w⟩ = ⟨φ · mixBend v w⟩` (the second fundamental form only sees the normal
   part). So `B^{(m)}(v,w) := mixBend v w` is the explicit m-second fundamental form; its "norm"
   `⟨mixBend v w · mixBend v' w'⟩` is the bending form.
4. Tilt lower bound — DONE (`ProductDensity`, `TiltLowerBound`): `P_a = P_b.withDensity(e^{−(λu·R − Λ_a(λu))})`
   for `b = a − (λ/t)u`; `KL(P_b‖P_a) = λu·m(b) − Λ_a(λu)`; `Measure.pi` of `withDensity` = `withDensity` of the
   product density (proved by Bochner Tonelli on boxes); Chebyshev via Mathlib's `variance_sum_pi`; **theorem**:
   `∀ ε δ > 0, ∃ N, ∀ n ≥ N, e^{−n(KL(P_b‖P_a)+δ)} ≤ P_a^{⊗n}(∀ i, |R̄_{n,i} − m_i(b)| < ε)`.

The seven-theorem spine you proposed (I atlas, II data calibration, III covariance metric, IV third-cumulant
bending, V journeys, VI boundary, VII variational cost) is now the opening of the note; per-module paragraphs
follow.

## Open
(a) contraction identity `tr(CK) = Cov(H,Q) = −∂_t log det C|_M` (needs Jacobi; we have `hasDerivAt_finset_prod`
and `det_apply'`); (b) `limsup (1/n) log P(R̄_n ∈ F) ≤ −inf_F I` (extended-real log); (c) walls; (d) quantitative
stability on compact reachable regions; (e) exact visible/invisible quotient of the data manifold (partly done:
kernel of the differential is `N^⊥`).

## Questions
1. **Audit** items 1–4 as stated. In particular: (i) is `mixBend` really the m-second fundamental form of the
   fixed-`t` family in the mixture geometry of all probability measures (the m-connection is flat on the mixture
   family, tangent space `span{R̃ᵢ}` in `L²(P)`, normal projection = orthogonal complement in `L²(P) ⊖ 1`)? Our
   `mixBend` projects `W_v W_w` onto `1 ⊕ span R̃` orthogonally in `L²(P_a)`; is the m-second fundamental form the
   normal part of `∂_v ∂_w` of the density ratio `p_{a+v}/p_a`, and does that equal the normal part of `W_v W_w`
   (up to the factor `t²`)? (ii) In the tilt lower bound the box `{∀ i, |R̄ᵢ − mᵢ| < ε}` is the sup-norm ball; the
   radius bookkeeping is `ρ = min ε (δ/(2(λ∑|uᵢ|+1)))` — correct constants?

2. **Depth question: dually flat structure.** The note has `A(θ)` (e-potential), `𝒮 = −KL(P_θ‖π̄)`, the chart
   `θ ↔ (t, M)` and `d𝒮 = −G(θ,·)`. The missing "beautiful" piece seems to be the *Legendre dual*: the m-potential
   `A*(M) = sup_θ(−θ·M − A(θ))` (or with the note's sign conventions) with `A*(m(θ)) = −𝒮(θ) − A(0)`... so that
   `−𝒮` in mean coordinates IS the convex conjugate of the log-partition, `∇_M A* = −θ(M)`, `D²_M A* = C⁻¹`
   (inverse response), `𝒮` concave in mean coordinates, the m-geodesic `M(s) = (1−s)M₀ + sM₁` and the e-geodesic
   `θ(s) = (1−s)θ₀ + sθ₁`, and the generalised Pythagorean theorem (we have `mixKL_three_point`). Please state
   precisely, with the note's sign conventions (loss = `θ·S`, density `e^{−θ·S}π`), the dual potential, the
   Legendre identity, the mean-coordinate gradient and Hessian of `𝒮`, and which of these are one-line corollaries
   of landed theorems (`sliceInv`, `responseChart`, `hasFDerivAt_affLogZ`, `d𝒮 = −G`, Gibbs variational principle)
   versus genuinely new. Would you make "`𝒮` is concave in mean coordinates with Hessian `−C⁻¹`, and the two
   geodesics from the featureless point to the data" the *capstone journey theorem* (the "map from maximal entropy
   to the data" the PI asks for)? What is the cleanest Lean formulation (a `Convex`/`ConcaveOn` statement on
   `chartDomain`, or the second-derivative along m-segments via the chart)?

3. **Re-rank** (a)–(e) plus the dually-flat programme of Q2, and propose any new direction of comparable depth
   (e.g. the entropy-production identity along the m-geodesic, the "response geodesic distance" as a proper metric
   on the reachable locus, the relation between the fixed-`t` mixture bending and the `t`-derivative of `C`, or the
   fluctuation-dissipation form `∂_t m = −Cov(L, R)` as a Hamiltonian flow). For the top pick give the theorem
   bundle in Lean-friendly form and the main pitfalls, as in round 37.
