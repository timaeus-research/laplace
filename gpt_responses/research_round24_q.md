# Research round 24: after the receding wall — what next, at what cost

## Landed since round 23 (sorry-free, pushed)

1. `ProfileTailLength`: `tendsto_integral_div_log_scaled` (`c h(c) → L ⇒ (∫_{c₀}^{a₁t^σ} h)/log t → σL`).
2. `ProfileGammaTail`: `profileMoment_eq_tail` (`N_k(c) = (1/q) c^{-(k+1/q)} I_k(c)`),
   `tendsto_tailIntegral` (`I_k(c) → Γ(k+1/q)`), `tendsto_sq_mul_profileVar` (`c² Var_c(y^q) → 1/q`).
3. `WallRecedes`: `wall_recedes` (`ℓ_t(c₀t^{-σ*}, a₁)/log t → σ*√(1/q)`), and the exponent form
   `σ*√(1/q) = √(σ*(λ₊ − λ_wall))`, `λ₊ = 1/q`, `λ_wall = 1/p`.
4. `SpectatorWall`: `x² + y⁴ + a y²` reduces (Fubini + evenness) to the half-line `w⁴ + a w²`;
   `spectator_wall_recedes`: coefficient `(1/2)√(1/2) = 1/(2√2)`.
5. `EntropyDuality`: `meanMap_legendre` (`F(a) − a·m(a) = ⟨L₀⟩_a + KL(P_a‖π)/t`),
   `affFreeEnergy_le_tangent`, `affFreeEnergy_sub_dot_le` (Legendre sup at `a`), `mixKL_aff_eq`
   (`KL(P_a‖P_b) = A(b) − A(a) + t(b−a)·m(a)`).
6. Earlier today: `RegularGeometricLimit`, `ShapeMetricLimit`, `GaussianShapeMetric`,
   `MeanMapInjective`, `MomentDetermination`, `BoundedDistance`, `IntegratedSusceptibility`,
   `AffineConvexity`, `SqrtIntegralConvergence`, `WallWindowLength`, `ThermoLengthAsymptotic`,
   `ProfileFamily`, `ProfileResponse`.

## Remaining items and my cost estimates (Lean lines, not time)

- **B. Proper-prior instance of `ℓ/log t → √(d/2)`** (Gaussian localiser prior + rotated anharmonic,
  `localisedVar_energy_leading` gives `t² Var → d/2` with rate): the identification
  `priorCov volume π L L L u = gibbsCov(localised u) u L L` is 20 lines, but integrability/continuity
  of `u ↦ Var_u(L)` down to `u = 0` (polynomial × Gaussian, `L ≥ 0`) is ~150 lines of plumbing;
  starting from a base temperature `u₀ > 0` instead (Cesàro lemma with base `u₀`) avoids the
  `u = 0` endpoint but still needs continuity on `(0,∞)` (~80 lines). ~250 total.
- **D. Mean map diffeomorphism**: Fréchet derivative of `a ↦ ∫ R_i e^{-t(L₀+a·R)}π` via
  `hasFDerivAt_integral_of_dominated_loc_of_deriv_le` (normed-space parameter), quotient rule,
  `hasFDerivAt_pi`; then C¹ (dominated continuity of the derivative), `HasStrictFDerivAt` and the
  local inverse; global: injective + local homeomorphism. ~350 lines.
- **C. Uniform Laplace on compact families**: the seabed's rate theorems are fixed-potential with
  opaque constants; a uniform version would need re-proving the localisation with explicit
  dependence on the jet data. ≥ 600 lines.
- **Strong-form receding wall**: `|I_k(c) − Γ| ≤ c^{-r} Γ(s+r+1)` from `1 − e^{-x} ≤ x`, then
  `c² Var = 1/q + O(c^{-r})`, `h(c) − √(1/q)/c = O(c^{-1-r})` integrable, renormalised limit via
  `intervalIntegral_tendsto_integral_Ioi`. ~250 lines.

## Questions

1. Given these costs, re-rank B, C, D, strong-form; and propose any cheaper targets of comparable
   depth that I am missing. In particular:
   (a) Is there a clean *exact* statement about the response geometry of the `w^p + a w^q` family
   for `a` in a fixed compact interval away from the wall (e.g. `t² Var_{t,a}(w^q) ≤ C/a²` uniformly,
   or a monotonicity in `a` of the profile speed) that would give the `O(1)` remainder of the
   receding-wall law without the full tail expansion?
   (b) The wall-side of the two-monomial family: for `a < 0` (the other chamber, `L_a = w^p − |a| w^q`
   has a second minimum away from 0), what does the response geometry look like and is there a
   two-sided crossing theorem worth stating with the current profile machinery (which is one-sided)?
   (c) For the multi-wall picture: with two couplings `L = w^p + a w^q + b w^r`, `q < r < p`, the
   crossover chambers of the valuation LP — is there a "product" structure of the profile lengths, and
   is a statement like "the response distance between chambers is Σ σᵢ√κᵢ log t" reachable?
2. The "map" question of the user: with the three scales, entropy duality, mean-map injectivity and
   the receding wall landed, what is the single most valuable theorem still missing for "a map of the
   space of responses from the featureless distribution to the data"? Candidates I see: (i) a global
   statement that the response distance from the featureless point to ANY data distribution with
   RLCT λ grows like √λ log t (we have it along the neutral line; is that already the general
   statement, since any data distribution defines its own neutral line?); (ii) the singular version of
   the shape metric (the profile Fisher metric as the "shape" of a singular posterior); (iii) the
   relation between the response metric and the "learning coefficient of the data variation" (the
   RLCT of the pair (L_q, L_{q'}))?
3. Audit: `spectator_priorExp` reduces the 2D family to the half-line one for even φ — fine. In
   `wall_recedes` the domain hypothesis is `0 ≤ c₀`; with `c₀ = 0` the window starts AT the wall.
   Any subtlety at `c₀ = 0` (the profile at `c = 0` is the pure `w^p` law; `Var_0(y^q)` finite)?
