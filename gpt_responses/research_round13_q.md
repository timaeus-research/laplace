# Consult: germbij analytic layer, thirteenth research round (after research_round12)

Same setting (Lean 4 + Mathlib, laplace `Laplace.Multi`, mirrored on the local hironaka branch `wall-atlas`). Since round 12, all sorry-free, standard axioms:

* **(1) compact-σ uniformity** (`ActiveTruthChartUniform.lean`, `tendsto_termKernel_activeTruth_uniform`): for a compact `C ∌ 0` of admissible σ and a fixed admissible test function, the normalised term kernel converges uniformly in `σ ∈ C` (from the moving-σ theorem by a subsequence/escaping-times argument, `eventually_uniform_of_moving`).
* **(5) constant-unit boundary regime** (`ActiveTruthDegenerate.lean`):
```lean
theorem tendsto_modelKernel_activeTruth_degenerate {ρ A B D γ p q δ β η w₀ a₀ : ℝ}
    {Q κ r : Fin k ⊕ Fin 2 → ℝ} (hρ : 0 < ρ) (hD : 0 < D) (hq : 0 < q) (hB : 0 < B)
    (ha₀ : 0 < a₀) (hβ : 0 < β) (hη : 0 < η) (hδ : 0 ≤ δ) (hκ : ∀ i, 0 < κ i)
    (hΔ : (transMat κ Q).det ≠ 0) (hc₀ : fibreCoef κ Q 0 ≠ 0 ∨ fibreA κ Q δ γ 0 ≠ 0)
    (hdeg : fibreCoef κ Q 1 = 0 ∧ fibreA κ Q δ γ 1 = 0)
    (hr : ∀ i, r i + 1 = β * κ i - η * Q i) :
    Tendsto (fun t ↦ t ^ (γ * p + (β * δ - η * γ)) / log t ^ k *
        modelKernel ρ A B D γ p q δ Q κ r (fun _ _ ↦ w₀) (fun _ _ ↦ a₀) t) atTop
      (𝓝 (A * w₀ * ρ ^ (∑ i, (r i + 1)) * |(transMat κ Q).det|⁻¹ *
        (∫⁻ v : Fin 2 → ℝ, vWeight β η 0 (B * a₀ * ρ ^ (∑ i, κ i))
          (-(q * log (ρ / D) + (∑ i, Q i) * log ρ)) v *
          (Ioi (0 : ℝ)).indicator (fun _ ↦ (1 : ℝ≥0∞)) (fibreB κ Q v 1)).toReal *
        (volume (facePolytope κ Q δ γ)).toReal))
```
(`vWeight β η 0 c₀ h₀ (s,h) = e^{-βs} e^{-c₀ e^{-s}} 1_{h>h₀} e^{-ηh}` in the transverse variables; `fibreB κ Q v 1 = (M⁻¹v)_1`; the solved coordinate `x_b = ρ e^{-(M⁻¹v)_1}` stays of order one; `F'` is the one-constraint polytope.)
* **(6) weighted mixed truth `h < 0`** (`MixedTruthWeightedNeg.lean`, `tendsto_weightedMixed_neg`): `t^h ∫_{σ/(bt)}^b x^{h-1} f(x,σ/(tx)) dx → σ^h ∫_0^b u^{-h-1} f(0,u) du`; the weighted trichotomy is complete.
* **(g) the general-truth hironaka export** (hironaka `wall-atlas`, `Monomialize/Relative/Wall/Truth*.lean`, 1446 lines): the wall layer with the coordinate `z ℓ` replaced by a function `T` throughout (resolution of `F·T`, factor separation, unit absorption, finite atlas over the compact wall part `L ∩ {T = 0}`, small-parameter cover of `L ∩ {|T| ≤ ε}`, partition of unity, weighted transport off `{F·T = 0}`). End statement:
```lean
theorem exists_truthChartsData_phase {U₀ : Set (Fin (m + 1) → ℝ)} (hU₀ : IsOpen U₀)
    {F : (Fin (m + 1) → ℝ) → ℝ} (hF : AnalyticOnNhd ℝ F U₀) (T : (Fin (m + 1) → ℝ) → ℝ)
    (hT : AnalyticOnNhd ℝ T U₀) (hT0 : T 0 = 0)
    (hne : ¬ ∀ᶠ z in 𝓝 (0 : Fin (m + 1) → ℝ), F z * T z = 0) (W : Opens (Fin (m + 1) → ℝ))
    (hW : IsConnected (W : Set (Fin (m + 1) → ℝ))) (h0W : (0 : Fin (m + 1) → ℝ) ∈ W)
    (hWU : (W : Set (Fin (m + 1) → ℝ)) ⊆ U₀) {L : Set (Fin (m + 1) → ℝ)} (hL : IsCompact L)
    (hLW : L ⊆ W) :
    ∃ ε > 0, ∃ D : TruthChartsData m T (L ∩ {z | |T z| ≤ ε}),
      ∃ (kF : D.ι → Fin (m + 1) → ℕ) (a : D.ι → (Fin (m + 1) → ℝ) → ℝ),
        (∀ i, Continuous (a i)) ∧ (∀ i u, a i u ≠ 0) ∧
        ∀ i, ∀ u ∈ Metric.closedBall (0 : Fin (m + 1) → ℝ) (D.ρ i),
          F (D.rep i u) = a i u * ∏ j, u j ^ kF i j
```
where `TruthChartsData m T L'` has: finite `ι`, continuous `rep i`, radii `ρ i > 0`, `dom i = closedBall 0 (ρ i) ∩ rep i ⁻¹' L'`, continuous nonnegative `dens i` supported in the open ball, `S i ≠ 0`, exponents `q i` with a solve index `k i`, `q i (k i) > 0`, `truth : ∀ u ∈ dom i, T (rep i u) = S i * ∏ u^(q i)`, and `transport : ∀ Ψ ≥ 0 measurable, ∫⁻_{L'} Ψ = ∑ i ∫⁻_{dom i} Ψ(rep i u) · ofReal(dens i u)`. The fibre identity (`fibre_eq`, a slice of the box for a coordinate truth) does not transfer; the record's push-forward identity `∫ θ(z) η(T z) dz = ∫ η(s) K_θ(s) ds` (`lintegral_mul_comp_truth`) is the replacement.
* **(7) support-separated distinguishability** (`ActiveTruthDistinguish.lean`): `exists_observable_of_separated` (leading measures separated by a measurable `O ⊆ L'`: `0 < μ₁(O)`, `μ₂(O) = 0` ⇒ some continuous nonnegative bounded ψ supported in `L'` has `fibreRatio₁ ψ χ − fibreRatio₂ ψ χ ↛ 0`), `activeTruthMeasure_pos_of_open` (the active-truth measure charges every open set meeting its truth segment at a point of positive weight `wt|b|`), `activeTruthMeasure_eq_zero_of_disjoint`, `le_leadingMeasure_of_leading`, and `exists_observable_of_activeTruth_separated` combining them.

Open from your round-12 ranking: (4) the mixed vertex/tied/active example (h); the general-unit version of (5).

## Questions

**Q1 (audit of the export).** Is `exists_truthChartsData_phase` the right shape for a general truth function? Specifically: (a) `T 0 = 0` as the wall-point condition and `F·T ≢ 0` near `0` as the only non-degeneracy; (b) the thin region `L ∩ {|T| ≤ ε}` for a compact `L` in a connected `W`; (c) anything the mixed-truth layer (which consumes `TruthChartsData` + `lintegral_mul_comp_truth`) needs that this does not provide — e.g. the monomial form of the Jacobian with its own unit, the sign/branch structure, or a Phase-like record for `F` (the `_phase` conjunct gives the unit and exponents of `F` but no Jacobian data beyond `dens`). Would you add fields, or is this sufficient to state the general-truth push-forward theorem on the laplace side?

**Q2 (general-unit boundary regime: statement).** Please propose the precise limit statement for the general-unit version of the degenerate theorem. Reference: the nondegenerate general-unit theorem is
```lean
theorem tendsto_modelKernel_general {ρ A B D γ p q δ β η : ℝ} {Q κ r : Fin k ⊕ Fin 2 → ℝ}
    (hρ : 0 < ρ) (hD : 0 < D) (hq : 0 < q) (hB : 0 < B) (hβ : 0 < β) (hη : 0 < η) (hδ : 0 ≤ δ)
    (hκ : ∀ i, 0 < κ i) (hΔ : (transMat κ Q).det ≠ 0)
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
      (𝓝[Set.pi univ fun _ : Fin k ⊕ Fin 2 ↦ Ioo (0 : ℝ) ρ] 0) (𝓝 (atr u))) :
    Tendsto (fun t ↦ t ^ (γ * p + (β * δ - η * γ)) / log t ^ k *
        modelKernel ρ A B D γ p q δ Q κ r W a t) atTop
      (𝓝 (A * Gamma β * B ^ (-β) * q * D ^ (-(q * η)) *
        (volume (facePolytope κ Q δ γ)).toReal / |(transMat κ Q).det| *
        ∫ u in Ioo (0 : ℝ) ρ, u ^ (q * η - 1) * (Wtr u * atr u ^ (-β))))
```
(the units `W(x,u)`, `a(x,u)` are evaluated at the active coordinates `x` and the cutoff variable `u = D t^{-γ/q} ∏ x^{-Q/q}`; the proof works in the transverse variables `v = (s,h)` where `u = truthOf h`, the exponential weight `e^{-c₀ e^{-s} a}` becomes `vWeight` with `c₀ ↦ c₀ · atr(truthOf h)`, and the domination is by `Wstar` times the constant-unit integrand at `amin`). In the degenerate regime the solved coordinate `x_b = ρ e^{-(M⁻¹v)_1}` does not collapse. My guess: the trace hypothesis becomes convergence of `W(x,u)` as the OTHER `k+1` coordinates tend to `0` with `(x_b, u)` fixed, pointwise on `Ioo 0 ρ × Ioo 0 ρ`, to `Wtr(x_b, u)`, likewise `a`; the limit is
`A ρ^{Σ(r+1)} |det M|⁻¹ vol(F') ∫ vWeight β η 0 (c₀ atr(z_b(v), u(v))) h₀ (v) · Wtr(z_b(v), u(v)) · 1_{(M⁻¹v)_1>0} dv` with `z_b(v) = ρ e^{-(M⁻¹v)_1}`, `u(v) = truthOf h`. Is that right (in particular the way `a` enters through the exponent, and whether `x_b` should be read as `ρ e^{-(M⁻¹v)_1}` or with the box scaling `ρ`), and is the same domination (`W ≤ Wstar`, `a ≥ amin`) enough? Any subtlety about the ordering of coordinates in `Fin k ⊕ Fin 2` (the collapsing set is `inl` ⊔ `inr 0`, the surviving one `inr 1`)?

**Q3 (the mixed example).** With the export in place, should (h) be (i) a hand-built `WallChartsData 2` instance with one vertex, one tied and one active-truth term and its lex assembly (~500 lines of record construction), (ii) an abstract certificate-level lemma (given `TermData` of the three shapes with lex-comparable orders, the leading measure is the sum over the leading shapes — essentially `ofTermData` + `lexMeasure`, cheap), or (iii) dropped, with the six-point checklist of round 12 as the deliverable? Which one actually tests something the current theorems do not?

**Q4 (closure).** Is anything still missing at the Euclidean layer for the note's active-truth and mixed-truth claims, given the above? Please rank the remaining work (general-unit boundary, its `j = 0` mirror and chart wrapper, the mixed example, a laplace-side general-truth push-forward theorem consuming the export, anything you add).
