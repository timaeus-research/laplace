# Research consult, round 32 (germbij / laplace `Laplace/Multi/*`)

Same programme (PI: "make sure we are tackling core features of the change in posterior expectation values with the
change in the data distribution that allow us to map the space of responses across the data manifold, ideally all the
way from the featureless distribution of maximal entropy to our actual data distribution; what would it take to do this
with maximum beauty and depth?"). All formal, sorry-free, on `main`. Bounded statistics `R : ι → X → ℝ`, `L₀` bounded,
positive prior `π·μ` on any measurable space, `t > 0`, nondegeneracy `hnd` (no nonzero contrast a.e. constant).
Notation: `P_a ∝ e^{−t(L₀ + ⟨a,R⟩)}π`, `A(a) = log Z`, `m(a) = ⟨R⟩_a`, `I(y) = −t⟨θ(y),y⟩ − A(θ(y))` on `range m`.

## Landed since round 31 (your ranking 1–8)

1. `LegendreMaximum` (your #1): Legendre identity `sup_θ(−t⟨θ,m(a₀)⟩ − A(θ))` attained uniquely at `a₀`; constrained
   entropy `KL(q‖P_0) = KL(q‖P_a) + I(m(a)) + A(0)` for any admissible `q` with `⟨R⟩_q = m(a)`, hence `P_a` is the
   least-informative distribution realising its response and `I + A(0)` is the minimal entropy cost.
2. `SliceVariational` (your #3, core): tangent inequality and convexity of `I` on `range m`; in the joint family
   (statistic `(L₀, R)`, natural coordinate `θ = (t, ta)`) `∂_{η₀}I = −t` at the slice point and the slice point
   minimises `e ↦ I(e,M) + te` over the fibre (the slice is the graph of the minimiser of `J_t(M) = inf_e(I(e,M)+te)`).
   NOT built: the residual-variance identity `∂_t h_t(M)` and `D²J_t = C_RR⁻¹` (block inversion).
3. `MeanSegment` (your #7): continuous inverse Jacobian; along the mean segment `y_s = m(a₀) + s d`,
   `⟨φ⟩_{a₁} − ⟨φ⟩_{a₀} = ∫₀¹ DΦ(y_s)[d] ds`, dual segment identities `KL(P_{a₁}‖P_{a₀}) = ∫(1−s)Q`,
   `KL(P_{a₀}‖P_{a₁}) = ∫ sQ`, `Q = ⟨d, D²I(y_s) d⟩`, `∫Q = Jeffreys`, `|Δ⟨φ⟩|² ≤ (∫Var φ)(KL + KL)`.
4. `ConstrainedResponse` (abstract core of your #2): along `a(s) = a₀ + s v + β(s) w` with `⟨R_w⟩` constant,
   `d/ds⟨R_v⟩ = −t(Var R_v − Cov(R_v,R_w)²/Var R_w)`; the Schur complement is `Var(R_{v−λw})`, `λ` the regression
   coefficient, positive iff `R_v` is not a.e. affine in `R_w`. (Single constraint direction only.)
5. `FeaturelessPoint`: `0 < KL(P_b‖P_a)` for `a ≠ b`; `I(m 0) = −A(0)`; `I(y) − I(m 0) = KL(P_{θ(y)}‖P_0)` for all
   attainable `y`; the prior's response is the unique minimiser of `I` on `range m`, so `I + A(0)` is the
   information-relative-to-featureless as a function on the response space.

Not done from round 31: the wall mean band INSTANCE (unbounded `F = log x`), (4) non-steep boundary extension, (5) `N^⊥`,
(6) two-term wall law, (8) Cramér for the response vector.

## My proposal for the next core piece: the loss surface over the feature space

Define `h(t, M) := ⟨L₀⟩` at the unique point of the temperature-`t` slice with contrast response `M` (well defined for
`M ∈ interior(momentBody R)`, every `t > 0`, by `TemperatureSlice`). Claims:
(a) `h` is `C¹` in `(t, M)` (inverse function theorem on `Φ(t,a) = (t, m(t,a))`, block-triangular derivative, as in the
    seabed's `MovingMinimizer`);
(b) `∂_M h = Cov(L₀,R) C_RR⁻¹` — the regression coefficients of the loss on the features (a reading of `ObservableRegression`);
(c) `∂_t h = −(Var L₀ − Cov(L₀,R) C_RR⁻¹ Cov(R,L₀))` — minus the variance of `L₀` unexplained by `R` (your round-31 residual
    identity), via a MULTI-constraint version of `ConstrainedResponse` (constraints `⟨R_i⟩` for all `i`, `β' = −C⁻¹c`);
(d) consequences: `h` is decreasing in `t` at fixed `M`, strictly unless `L₀` is a.e. affine in `R`; and `J_t(M) = I(h,M)+th`
    with `∂_t J_t(M) = h_t(M)` (envelope), `∂_M J_t = ∂_M I` restricted.
Interpretation: over the space of feature responses, the posterior energy is a smooth surface whose slope in the feature
directions is the regression of the loss on the features and whose descent in temperature is the unexplained variance.

## Questions

1. Is the proposal (a)–(d) correct as stated, and is it the right next core piece for the PI's goal? Anything false or
   missing (e.g. is `C_RR` invertible exactly under `hnd`? yes by `responseForm` positivity; is (d)'s envelope claim right)?
2. Re-rank what remains for "maximum beauty and depth", including: (i) the multi-constraint Schur lemma + loss surface
   above; (ii) `N^⊥`; (iii) non-steep boundary extension of the moment-body chart; (iv) the wall mean band instance
   (needs unbounded-statistic tilt data: `log x` under `e^{−t(x^p + a x^q)}` on `(0,∞)`); (v) two-term wall law;
   (vi) Cramér/large deviations for the empirical response; (vii) anything else you regard as core to "the change in
   posterior expectation values with the change in the data distribution" — e.g. second-order response
   (`D²m = −t (third cumulant tensor)`), the response of a general observable along the temperature ray, an
   annealing/thermodynamic-length identity for the ray `t ↦ P_t` from the prior to the loss minimiser, or a global
   statement that the two foliations (information spheres `I + A(0) = const` around the featureless point and the
   mean segments through it) are the dually-flat structure.
3. For (i): give the cleanest formulation of the multi-constraint Schur derivative in Lean-friendly terms (finite index
   `κ`, covariance `Matrix κ κ ℝ`, `Matrix.mulVec`), and any pitfall in the implicit-function/inverse-function step.
4. Any correction to the landed statements above (as in rounds 30–31)?
