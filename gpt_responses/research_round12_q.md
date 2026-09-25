# Consult: germbij analytic layer, twelfth research round (after research_round11)

Same setting (Lean 4 + Mathlib, laplace `Laplace.Multi`, mirrored on hironaka `wall-atlas`). Since round 11, all sorry-free:

* **(d) example identification** (`ActiveTruthExampleBridge.lean`): `modelKernel 1 1 1 1 2 0 1 3 degQ degκ degr 1 1 t = (degI t).toReal` and `tendsto_degI_of_face : t⁴ I(t)/log t → 1` from the general theorem (regression test passed).
* **(c) solved-pair independence** (`ActiveTruthFaceInvariance.lean`), by your augmented-map route: `augMat κ Q = fromBlocks 1 0 A M'`, `faceLift w = augMat⁻¹ (w, δ, γ)`, `w ∈ F' ↔ faceLift w ≥ 0`, the transition `augMat_σ · P_σ · augMat⁻¹ = fromBlocks L C 0 1`, `|det L| = |det M_σ|/|det M|`, affine change of variables:
```lean
theorem volume_facePolytope_div_det_perm {κ Q : Fin k ⊕ Fin 2 → ℝ} (hκ : ∀ s, 0 < κ s)
    (hΔ : (transMat κ Q).det ≠ 0) (σ : Equiv.Perm (Fin k ⊕ Fin 2))
    (hΔσ : (transMat (κ ∘ σ) (Q ∘ σ)).det ≠ 0) (δ γ : ℝ) :
    (volume (facePolytope (κ ∘ σ) (Q ∘ σ) δ γ)).toReal / |(transMat (κ ∘ σ) (Q ∘ σ)).det| =
      (volume (facePolytope κ Q δ γ)).toReal / |(transMat κ Q).det|
-- and faceConst_eq : P.faceConst i γ e₂ = P.faceConst i γ e₁ for two splittings e₁ e₂ : Fin k ⊕ Fin 2 ≃ Fin m.
```
* **(f) moving constants, constant units** (`ActiveTruthParam.lean`), by your squeeze (two parameters `B, D`, antitone through the exponential and through the cut; `tendsto_of_antitone_param2`): `tendsto_modelKernel_activeTruth_param` and the spectator version.
* **(f′) moving constants, GENERAL units** (`ActiveTruthGeneralParam.lean`) — beyond the squeeze, whose monotonicity in `D` fails when the units depend on `u = D t^{-γ/q} ∏x^{-Q/q}`. The trick is a change of time: for `γ > 0`,
```lean
noncomputable def cutTime (D₀ γ q D t : ℝ) : ℝ := t * (D₀ / D) ^ (q / γ)
theorem modelKernel_cutTime {ι : Type*} [Fintype ι] {ρ A B D D₀ γ p q δ t : ℝ} {Q κ r : ι → ℝ}
    {W a : (ι → ℝ) → ℝ → ℝ} (hD : 0 < D) (hD₀ : 0 < D₀) (hγ : 0 < γ) (hq : 0 < q) (ht : 0 < t) :
    modelKernel ρ A B D γ p q δ Q κ r W a t =
      modelKernel ρ (A * (D₀ / D) ^ (q * p)) (B * (D₀ / D) ^ (-(q * δ / γ))) D₀ γ p q δ Q κ r W a
        (cutTime D₀ γ q D t)
```
(exact, any index type, any units, since the units are evaluated at the cutoff variable and `cutVar D₀ … τ = cutVar D … t`). So moving `D` is moving `(A, B)` at the reparametrised time; `B` enters only through `e^{-B t^δ a ∏x^κ}`, antitone for any nonnegative unit; one-parameter squeeze along `τ` at fixed `D₀` (fixed-`b` limits from the trace theorem composed with `τ → ∞`, finiteness from the uniform bound), times the normaliser ratio `N(t)/N(t c(t)) = c^{-λ}(1 + log c/log t)^k → 1`:
```lean
theorem tendsto_modelKernel_general_param {ρ γ p q δ β η : ℝ} {Q κ r : Fin k ⊕ Fin 2 → ℝ}
    {A B D : ℝ → ℝ} {A₀ B₀ D₀ : ℝ} (hρ : 0 < ρ) (hq : 0 < q) (hγ : 0 < γ) (hβ : 0 < β)
    (hη : 0 < η) (hδ : 0 ≤ δ) (hκ : ∀ i, 0 < κ i) (hΔ : (transMat κ Q).det ≠ 0)
    (hc₀ : fibreCoef κ Q 0 ≠ 0 ∨ fibreA κ Q δ γ 0 ≠ 0)
    (hc₁ : fibreCoef κ Q 1 ≠ 0 ∨ fibreA κ Q δ γ 1 ≠ 0)
    (hr : ∀ i, r i + 1 = β * κ i - η * Q i) {W a : (Fin k ⊕ Fin 2 → ℝ) → ℝ → ℝ}
    {Wstar amin : ℝ} (hamin : 0 < amin) (hWm : Measurable (Function.uncurry W))
    (ham : Measurable (Function.uncurry a)) (hWb : ∀ x u, 0 ≤ W x u ∧ W x u ≤ Wstar)
    (hab : ∀ x u, amin ≤ a x u) {Wtr atr : ℝ → ℝ} (hWtrm : Measurable Wtr)
    (hatrm : Measurable atr) (hWtrb : ∀ u ∈ Ioo (0 : ℝ) ρ, 0 ≤ Wtr u ∧ Wtr u ≤ Wstar)
    (hatrb : ∀ u ∈ Ioo (0 : ℝ) ρ, amin ≤ atr u)
    (hWtr : ∀ u ∈ Ioo (0 : ℝ) ρ, Tendsto (fun x ↦ W x u)
      (𝓝[Set.pi univ fun _ : Fin k ⊕ Fin 2 ↦ Ioo (0 : ℝ) ρ] 0) (𝓝 (Wtr u)))
    (hatr : ∀ u ∈ Ioo (0 : ℝ) ρ, Tendsto (fun x ↦ a x u)
      (𝓝[Set.pi univ fun _ : Fin k ⊕ Fin 2 ↦ Ioo (0 : ℝ) ρ] 0) (𝓝 (atr u)))
    (hA : Tendsto A atTop (𝓝 A₀)) (hB : Tendsto B atTop (𝓝 B₀)) (hB₀ : 0 < B₀)
    (hD : Tendsto D atTop (𝓝 D₀)) (hD₀ : 0 < D₀) :
    Tendsto (fun t ↦ t ^ (γ * p + (β * δ - η * γ)) / log t ^ k *
        modelKernel ρ (A t) (B t) (D t) γ p q δ Q κ r W a t) atTop
      (𝓝 (A₀ * Gamma β * B₀ ^ (-β) * q * D₀ ^ (-(q * η)) *
        (volume (facePolytope κ Q δ γ)).toReal / |(transMat κ Q).det| *
        ∫ u in Ioo (0 : ℝ) ρ, u ^ (q * η - 1) * (Wtr u * atr u ^ (-β))))
```
* **Chart level** (`ActiveTruthChartParam.lean`): `tendsto_termKernel_activeTruth_param` — along `σ(t) → σ₀ ≠ 0` (γ > 0) the active-truth term kernel converges to `∫ φ d(activeTruthMeasure … σ₀ …)`; parameter stability now for tied, partial and active-truth terms.

Not done: (h) a mixed vertex/tied/active example (would need a new `WallChartsData m` instance with `m ≥ 2`; every existing toy record is `WallChartsData 1 0` and each took a full session), (g) the general-truth hironaka export (refactor of the non-Euclid wall layer, `ℓ ↦ T`), (e) the `c_j = a_j = 0` boundary regime (deferred per your advice), certificate completeness/strong duality (scoped out per your advice).

## Questions

1. **Audit the time change.** Is `modelKernel_cutTime` as stated correct (the constant exponents `qp` and `−qδ/γ`; note `t^{-γp}` and `t^δ` both scale)? Is there any subtlety in the normaliser ratio with `log` (we need `t c(t) > 1` eventually, fine) or in composing the fixed-`b` limit with `τ → ∞` (the squeeze's `hanti` is asked at times `τ(t) ≥ e`)? Anything the statement of `tendsto_modelKernel_general_param` should also carry (e.g. does `γ > 0` exclude a case the note needs; `γ` is the cut exponent `s = σ t^{-γ}`)?

2. **What is left for the note's active-truth claim at the Euclidean layer?** With the face theorem (constant, trace, general units, spectators), the chart wrapper (with and without spectators), LP interface, nonvanishing, solved-pair independence, the example instance, and parameter stability all landed, is the analytic side of the note's active-truth claim closed modulo (e), (g), (h)? If you see a gap (a hypothesis of `TermData.activeTruth(Spectator)` that a chart coming from a resolution would not satisfy, an assumption about the units, the ρ-box, the traces, the sign branches ε, b), name it.

3. **Ranking for the next rounds.** Candidates: (h) the mixed example; (g) export; (e) the boundary regime `c_j = a_j = 0` as a separate theorem (you sketched: the solved coordinate does not collapse — what is the precise limit statement? is the constant-unit version tractable?); a `sup_σ`-uniform version on a compact parameter set (compactness + the moving version); the round-3 leftover "totalKernel bookkeeping for `xy = s`" (mixed truth at the log endpoint, `MixedTruthRecord.lean` has the identity chart `mixData`); the `h < 0` case of the weighted mixed truth (`t^h K → σ^h ∫ u^{-h-1} …`); a distinguishability statement for active-truth faces under support-separation hypotheses; anything else the note needs. Please rank and, for the top item, give the statement to formalise.

Please be specific and concise.
