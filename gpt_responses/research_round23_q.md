# Research round 23: the map of responses — audit and next targets

## Landed since round 22 (all sorry-free, pushed; Laplace/Multi/*)

Your round-22 bundle is complete, plus the two regular scales:

1. `IntegratedSusceptibility`: `∫₀¹ t Var_{t,s}(Δ) ds = ⟨Δ⟩_{t,0} − ⟨Δ⟩_{t,1}`; `ℓ(t)² ≤ t(⟨Δ⟩₀ − ⟨Δ⟩₁)`,
   `ℓ ≤ √(2Mt)`; `mixCov_self_pos` (non-degenerate contrast ⇒ Var > 0 everywhere, from the nullspace
   theorem); `mixExp_strictAnti` / `mixExp_injective`.
2. `AffineConvexity`: `affLogZ a = log Z_t(L₀ + ∑ aᵢRᵢ)` is `ConvexOn ℝ univ` (by restriction to
   mixture lines); `D_v A = −t⟨R_v⟩_a`; `D_v² A = responseForm a v v`; free energy concave.
3. `WallWindowLength`: for `L_a = w^p + a w^q` on `(0,∞)`, `g_t(c t^{-σ*}) = t^{2σ*} Var_c(y^q)` and
   `∫_{c₀t^{-σ*}}^{c₁t^{-σ*}} √g_t da = ∫_{c₀}^{c₁} √Var_c(y^q) dc` exactly for every t.
4. `SqrtIntegralConvergence`: `∫√F_n → ∫√f` from a.e. convergence + uniform L¹ mass bound (truncation);
   hence `ℓ(t)/√t → ∫₀¹ √κ` on a mixture line from pointwise `t Var_{t,s}(Δ) → κ(s)` (κ integrable,
   `∫κ ≤ 2M`).
5. `GaussianShapeMetric`: for `L_a = ½wᵀ(H₀ + ∑aᵢBᵢ)w`, flat prior: `responseForm a v v =
   ½ tr((B_v H_a⁻¹)²)` EXACTLY for every t (Wick variance of a quadratic form under the tilted
   Gaussian).
6. `RegularGeometricLimit`: `responseForm/t → ⟨−H⁻¹∇R_v, H(−H⁻¹∇R_u)⟩ = H(Dm[v], Dm[u])`, with the
   velocities supplied by the stationarity equation (`movingMinimizer_deriv`).
7. `MomentDetermination`: same base moments ⇒ same Z along the line; same mixed moments ⇒ same
   response of φ.
8. `MeanMapInjective`: `meanMap a = (⟨Rᵢ⟩_a)ᵢ`; `D_v log Z = −t∑vᵢmᵢ`; the mean map is injective when
   no nonzero direction has an a.s.-constant contrast on the prior support (proof: strict
   anti-monotonicity along the segment from a to b with contrast R_{b−a}).
9. `ShapeMetricLimit`: with both direction gradients zero, `cov2Coefficient` collapses to
   `½ trASig(A_v Σ A_u Σ)`, so `responseForm a v u → ½ tr(A_v Σ A_u Σ)` at rate O(1/t)
   (`gibbsCov_first_order_rate_explicit`, quintic-jet hypotheses); `trASig_matCLM_eq_trace`.
10. `BoundedDistance`: `fisherSpeed ≤ C` on [0,1] ⇒ `ℓ ≤ √C`.

Earlier this session: `ProfileResponse`, `ProfileFamily` (wall = exponential family; mean map
strictly decreasing), `ThermoLengthAsymptotic` (`ℓ(t)/log t → √λ` on the neutral line).

## A conjecture I would like you to check: the wall recedes logarithmically

Two-monomial family `L_a = w^p + a w^q`, `0 < q < p`, Lebesgue on `(0,∞)`. For FIXED `a > 0` and
`t → ∞` the posterior is dominated by `a w^q` near 0, so `y = w^q` is asymptotically
`Gamma(shape 1/q, rate ta)`: `Var_{t,a}(w^q) ≈ (1/q)/(ta)²`, i.e. `g_t(a) = t² Var → 1/(q a²)`, so
`√g_t(a) → 1/(a√q)` and the limiting length between `a₀ < a₁` (both fixed) is `(1/√q) log(a₁/a₀)`.
Gluing with the window (`a₀ = c₀ t^{-σ*}`, where the length is the t-independent profile length),
the distance from the wall window to a fixed data point `a₁` grows like

   `(σ*/√q) log t + O(1) = σ* √λ_q log t + O(1)`,   `λ_q = 1/q` the RLCT of `w^q` on `(0,∞)`.

Questions: (i) is this right (constants, the Gamma-law step, the matching of the two regimes)?
(ii) Is there a clean general statement — "in the singular layer, the distance to a wall grows like
(exponent gap) × √(RLCT of the dominant side) × log t" — and what is the right invariant form of the
"exponent gap" σ*? (iii) How does it compare with the featureless law `√λ log t`: is the wall a
"partially featureless" point (one monomial switched off) and is the factor σ* the codimension-type
quantity of the wall in the valuation LP (`ValuationLP`: `offsetLP` convex, `coupledExponent`)?

## Questions for ranking (beauty × depth × reachability)

A. The "wall recedes" theorem above, in the two-monomial model, from `two_q_regime`-type profile
   asymptotics (TwoMonomialWall) + numerator asymptotics for `w^q` and `w^{2q}` in the q-regime.
B. The proper-prior regular instance of `ℓ/log t → √(d/2)` (Gaussian prior + anharmonic; needs
   continuity of `u ↦ Var_u(L)` down to u = 0 and `localisedVar_energy_leading`).
C. Uniform-in-s Laplace asymptotics on a compact regular family (your D on compact chart subsets).
D. The mean map is a diffeomorphism onto its image when the response form is positive definite
   (multivariate Fréchet derivative of `meanMap`; inverse function theorem).
E. A "generating function of the whole map": the free energy `F_t(q)` on the affine span as a concave
   potential whose Legendre transform is the entropy of the response — is there a clean identity
   `F*_t(m) = −(1/t)·(Gibbs entropy relative to the prior at the posterior with means m)` worth
   formalising (Gibbs variational principle is landed: `gibbs_variational`, uniqueness)?
F. Anything you consider essential and missing for "a map of the space of responses from the
   featureless distribution to the data" as the user asked.

## Audit requests

- `responseForm_shape_asymptotic`: hypotheses `hv : ObservableQuinticApprox (dirLoss R v) 0`,
  `hu : ObservableTensorApprox (dirLoss R u) 0`, potential `PotentialQuinticApprox (affLoss L₀ R a) H`,
  `LaplaceCov6MomentHypotheses H Hinv`; conclusion `|responseForm − ½ trASig(A_v∘Σ∘A_u∘Σ) 1| ≤ K/t`.
  Is the value ½ tr(A_v Σ A_u Σ) the correct shape metric (with `A_v = ∇²R_v(m)`, Σ = H⁻¹)? Does it
  agree with your `½ tr(H⁻¹ D_uH H⁻¹ D_vH)` (note `D_vH = ∇²R_v` along an affine family)?
- `GaussianShapeMetric`: `t² Var_t(½wᵀBw) = ½ tr((BH⁻¹)²)` under `e^{-t·½wᵀHw}` on ℝ^d — sign and
  factor check against the Fisher–Rao metric on covariances.
- `meanMap_injective` hypothesis: "∀ v ≠ 0, ¬∃ c, ∀ᵐ x, π x ≠ 0 → R_v x = c". Is this the right
  non-degeneracy (it is the nullspace condition of the response form, independent of a)?
