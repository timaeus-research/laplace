# Consult: germbij analytic layer, eleventh research round (after research_round10)

Same setting (Lean 4 + Mathlib, laplace `Laplace.Multi`, mirrored on hironaka `wall-atlas`). Your round-10 items (a) and (b) are landed, sorry-free, plus `volume_poly2_pos_iff` (`0 < vol(poly2 c₁ c₂ a₁ a₂) ↔ ∃ w > 0, c_j·w < a_j`, under `(c_j,a_j) ≠ (0,0)`).

## (a) Spectators with general units (`ActiveTruthSpectatorGeneral.lean`) and the chart wrapper (`ActiveTruthChartSpectator.lean`)

```lean
theorem tendsto_modelKernel_general_spectator {ρ A B D γ p q δ β η : ℝ}
    {Q κ r : Fin m ⊕ (Fin k ⊕ Fin 2) → ℝ} (hρ : 0 < ρ) (hD : 0 < D) (hq : 0 < q) (hB : 0 < B)
    (hβ : 0 < β) (hη : 0 < η) (hδ : 0 ≤ δ) (hκ : ∀ i, 0 < κ i)
    (hΔ : (transMat (fun j ↦ κ (Sum.inr j)) (fun j ↦ Q (Sum.inr j))).det ≠ 0)
    (hc₀ : fibreCoef (fun j ↦ κ (Sum.inr j)) (fun j ↦ Q (Sum.inr j)) 0 ≠ 0 ∨
      fibreA (fun j ↦ κ (Sum.inr j)) (fun j ↦ Q (Sum.inr j)) δ γ 0 ≠ 0)
    (hc₁ : fibreCoef (fun j ↦ κ (Sum.inr j)) (fun j ↦ Q (Sum.inr j)) 1 ≠ 0 ∨
      fibreA (fun j ↦ κ (Sum.inr j)) (fun j ↦ Q (Sum.inr j)) δ γ 1 ≠ 0)
    (hrJ : ∀ j, r (Sum.inr j) + 1 = β * κ (Sum.inr j) - η * Q (Sum.inr j))
    (hd : ∀ i, 0 < specd β η Q κ r i)
    {W a : (Fin m ⊕ (Fin k ⊕ Fin 2) → ℝ) → ℝ → ℝ} {Wstar amin : ℝ} (hamin : 0 < amin)
    (hWm : Measurable (Function.uncurry W)) (ham : Measurable (Function.uncurry a))
    (hWb : ∀ x u, 0 ≤ W x u ∧ W x u ≤ Wstar) (hab : ∀ x u, amin ≤ a x u)
    {Wtr atr : (Fin m → ℝ) → ℝ → ℝ} (hWtrm : Measurable (Function.uncurry Wtr))
    (hatrm : Measurable (Function.uncurry atr))
    (hWtrb : ∀ ξ, ∀ u ∈ Ioo (0 : ℝ) ρ, 0 ≤ Wtr ξ u ∧ Wtr ξ u ≤ Wstar)
    (hatrb : ∀ ξ, ∀ u ∈ Ioo (0 : ℝ) ρ, amin ≤ atr ξ u)
    (hWtr : ∀ᵐ ξ : Fin m → ℝ, ξ ∈ specBox m ρ → ∀ u ∈ Ioo (0 : ℝ) ρ,
      Tendsto (fun x' ↦ W (Sum.elim ξ x') u)
        (𝓝[Set.pi univ fun _ : Fin k ⊕ Fin 2 ↦ Ioo (0 : ℝ) ρ] 0) (𝓝 (Wtr ξ u)))
    (hatr : ∀ᵐ ξ : Fin m → ℝ, ξ ∈ specBox m ρ → ∀ u ∈ Ioo (0 : ℝ) ρ,
      Tendsto (fun x' ↦ a (Sum.elim ξ x') u)
        (𝓝[Set.pi univ fun _ : Fin k ⊕ Fin 2 ↦ Ioo (0 : ℝ) ρ] 0) (𝓝 (atr ξ u))) :
    Tendsto (fun t ↦ t ^ (γ * p + (β * δ - η * γ)) / log t ^ k *
        modelKernel ρ A B D γ p q δ Q κ r W a t) atTop
      (𝓝 (A * Gamma β * B ^ (-β) * q * D ^ (-(q * η)) *
        (volume (facePolytope (fun j ↦ κ (Sum.inr j)) (fun j ↦ Q (Sum.inr j)) δ γ)).toReal /
        |(transMat (fun j ↦ κ (Sum.inr j)) (fun j ↦ Q (Sum.inr j))).det| *
        ∫ ξ in specBox m ρ, (∏ i, ξ i ^ (specd β η Q κ r i - 1)) *
          ∫ u in Ioo (0 : ℝ) ρ, u ^ (q * η - 1) * (Wtr ξ u * atr ξ u ^ (-β))))
```
(`specd β η Q κ r i = r (inl i) + 1 − β κ (inl i) + η Q (inl i)`, `specBox m ρ = (0,ρ)^m`.) Proof structure: freeze `ξ` (`modelIntegrand_sum_elim_general`: `1_{box}(ξ)∏ξ^{r_I}` × active integrand at `B_ξ = B∏ξ^{κ_I}`, `D_ξ = D∏ξ^{−Q_I/q}`, units `W(ξ,·,·)`), pointwise limit by the general-unit theorem at `(B_ξ, D_ξ)`, and domination by the POINTWISE bound `modelIntegrand(W,a) ≤ W_* · modelIntegrand(1, a_-)` (the exponential is decreasing in `a`), so the constant-unit spectator majorant `K∏ξ^{d−1}(1+|κ_i||log ξ_i|)^k` is reused verbatim times `W_*`; evaluation via `trace_const_eq` at `(B_ξ,D_ξ)` and `∏ξ^{r_I} B_ξ^{-β} D_ξ^{-qη} = B^{-β}D^{-qη}∏ξ^{d_i−1}`.

Chart wrapper, `e : Fin n ⊕ (Fin k ⊕ Fin 2) ≃ Fin m`, `specPt e ξ = fun j ↦ Sum.elim ξ 0 (e.symm j)` (spectators `ξ`, active coordinates `0`):
```lean
noncomputable def activeTruthSpecDensityFn (i : D.ι) (ε : Fin m → Bool) (b : Bool) (σ γ β η : ℝ)
    (e : Fin n ⊕ (Fin k ⊕ Fin 2) ≃ Fin m) (ξ : Fin n → ℝ) (u : ℝ) : ℝ :=
  P.constA i σ * Gamma β * P.constB i σ ^ (-β) * (D.q i (D.k i) : ℝ) *
    D.constD i σ ^ (-((D.q i (D.k i) : ℝ) * η)) * P.faceConstSpec i γ e *
    ((∏ l, ξ l ^ (specd β η (D.Qexp i ∘ e) (P.kappa i ∘ e) (P.rExp i ∘ e) l - 1)) *
      (u ^ ((D.q i (D.k i) : ℝ) * η - 1) *
        ((P.wt i (D.bridgePt i ε b (specPt e ξ) u) * |P.b i (D.bridgePt i ε b (specPt e ξ) u)|) *
          |P.a i (D.bridgePt i ε b (specPt e ξ) u)| ^ (-β))))))
-- activeTruthSpecDensity = (specBox n ρ ×ˢ Ioo 0 ρ).indicator (uncurry activeTruthSpecDensityFn)
noncomputable def activeTruthSpecMeasure (i : D.ι) (ε : Fin m → Bool) (b : Bool) (σ γ β η : ℝ)
    (e : Fin n ⊕ (Fin k ⊕ Fin 2) ≃ Fin m) : Measure (Fin (m + 1) → ℝ) :=
  ((volume : Measure ((Fin n → ℝ) × ℝ)).withDensity fun p ↦
      ENNReal.ofReal (P.activeTruthSpecDensity i ε b σ γ β η e p)).map
    (fun p ↦ D.rep i (D.bridgePt i ε b (specPt e p.1) p.2)p.2)
-- tendsto_modelKernelOf_activeTruthSpectator: t^{γp+βδ−ηγ}/(log t)^k · modelKernelOf i φ ε b t γ σ → ∫ φ d(activeTruthSpecMeasure)
-- TermData.activeTruthSpectator : (γp + βδ − ηγ, k, activeTruthSpecMeasure), under hr (active certificate), hd (d_l > 0), hΔ, (c_j,a_j) ≠ (0,0).
```
The traces are the values of the chart weight `1_{dom} φ(rep ·) wt |b|` and unit `|a|` at `bridgePt (specPt e ξ) u`, read off joint continuity (these points lie in the chart ball exactly for `ξ` in the box, which is why the abstract theorem asks for traces only at a.e. `ξ ∈ specBox`).

## (b) LP-to-chart interface and nonvanishing (`ActiveTruthLPChart.lean`)

```lean
theorem exists_face_point_of_volume_pos {κ Q : Fin k ⊕ Fin 2 → ℝ} {δ γ : ℝ}
    (hΔ : (transMat κ Q).det ≠ 0)
    (hc₀ : fibreCoef κ Q 0 ≠ 0 ∨ fibreA κ Q δ γ 0 ≠ 0)
    (hc₁ : fibreCoef κ Q 1 ≠ 0 ∨ fibreA κ Q δ γ 1 ≠ 0)
    (hvol : 0 < volume (facePolytope κ Q δ γ)) :
    ∃ α : Fin k ⊕ Fin 2 → ℝ, (∀ j, 0 ≤ α j) ∧ (∀ i, 0 < α (Sum.inl i)) ∧
      ∑ j, κ j * α j = δ ∧ ∑ j, Q j * α j = γ
-- (face point Sum.elim w y with y = M⁻¹(δ − κ'·w, Q'·w − γ), i.e. y_j = fibreA j − fibreCoef j ⬝ w)
theorem lpOptimal_activeTruth_spectator_iff (hβ : 0 < β) (hη : 0 < η)
    (hr : ∀ j, r (e (Sum.inr j)) + 1 = β * κ (e (Sum.inr j)) - η * Q (e (Sum.inr j)))
    (hd : ∀ l, 0 < specd β η (Q ∘ e) (κ ∘ e) (r ∘ e) l)
    (hne : ∃ α₀ : Fin k ⊕ Fin 2 → ℝ, (∀ j, 0 ≤ α₀ j) ∧
      ∑ j, κ (e (Sum.inr j)) * α₀ j = δ ∧ ∑ j, Q (e (Sum.inr j)) * α₀ j = γ)
    (α : ι → ℝ) :
    LPOptimal Q κ γ δ (fun j ↦ r j + 1) α ↔
      (∀ j, 0 ≤ α j) ∧ ∑ j, κ j * α j = δ ∧ ∑ j, Q j * α j = γ ∧
        ∀ l, α (e (Sum.inl l)) = 0
-- (e : Fin n ⊕ (Fin k ⊕ Fin 2) ≃ ι, any finite ι; LPOptimal Q κ γ δ c α := feasible ∧ ∀ feasible β, c·α ≤ c·β; chart form lpOptimal_iff_activeFace with hvol in place of hne)
theorem activeTruth_lam_eq_lpExponent (p : ℝ)
    (hr : ∀ j, r (e (Sum.inr j)) + 1 = β * κ (e (Sum.inr j)) - η * Q (e (Sum.inr j)))
    (hd : ∀ l, 0 < specd β η (Q ∘ e) (κ ∘ e) (r ∘ e) l) {α : ι → ℝ}
    (hκ : ∑ j, κ j * α j = δ) (hQ : ∑ j, Q j * α j = γ) (hI : ∀ l, α (e (Sum.inl l)) = 0) :
    γ * p + (β * δ - η * γ) = lpExponent γ p (fun j ↦ r j + 1) α
-- lpExponent γ p b α = γ p + ∑ b_j α_j is the seabed's power of a vertex/tied term at α.
theorem activeTruthMeasure_ne_zero (i : D.ι) (ε : Fin m → Bool) (b : Bool) (hσ : σ ≠ 0)
    (hβ : 0 < β) (hη : 0 < η) (e : Fin k ⊕ Fin 2 ≃ Fin m) (hκ : ∀ j, 0 < P.kappa i j)
    (hΔ : (transMat (P.kappa i ∘ e) (D.Qexp i ∘ e)).det ≠ 0)
    (hvol : 0 < volume (facePolytope (P.kappa i ∘ e) (D.Qexp i ∘ e) (P.phaseExp i γ) γ))
    {u₀ : ℝ} (hu₀ : u₀ ∈ Ioo (0 : ℝ) (D.ρ i))
    (hpos : 0 < P.wt i (D.bridgePt i ε b 0 u₀) * |P.b i (D.bridgePt i ε b 0 u₀)|) :
    P.activeTruthMeasure i ε b σ γ β η e ≠ 0
-- and activeTruthSpecMeasure_ne_zero (with (ξ₀,u₀), ξ₀ ∈ specBox).
```

## Questions

1. **Audit.** Are the spectator theorem's constant and hypotheses right (in particular the a.e.-in-the-box trace hypothesis, the global bounds on the traces, the factor `∏ξ^{d−1}` with `d_l = r_l+1−βκ_l+ηQ_l`, the double integral order), and the chart density/measure (the push-forward along `(ξ,u) ↦ rep(bridgePt (specPt e ξ) u)`, no Jacobian since the chart map is the record's `rep` and the density is stated in chart coordinates)? Is `lpOptimal_activeTruth_spectator_iff` the right "LP-to-chart interface", or did you mean something stronger (e.g. deriving `(β,η)` from LP optimality of the face — a strong-duality statement — rather than assuming it)? If the latter: is it worth formalising (finite LP strong duality is not in Mathlib; we could prove existence of a certificate for a face given as the optimal set by a Farkas-type argument only with real effort)?

2. **The `c_j = a_j = 0` case** (your item (e)). With `fibreCoef j = 0` and `fibreA j = 0` the `j`-th fibre constraint reads `0 ≤ (Nv)_j` independently of `L` and `w`: the fibre-volume limit becomes `1_{(Nv)_j ≥ 0} · vol(poly2 without constraint j)`, so the transverse `(s,h)`-integral acquires the indicator `1_{(Nv)_j ≥ 0}` — i.e. a half-plane restriction in `(s,h)` and a different constant. Is that the correct statement? When does this case occur geometrically (in the three-coordinate example it does not: `fibreCoef 1 = 0` but `fibreA 1 = 1 ≠ 0`)? Is it worth formalising, or should it be recorded as a scoped exclusion in the note?

3. **Solved-pair independence** (your item (c)): `vol(F')/|det M|` where `F'` is the projection of the face `{α ≥ 0 | κ·α = δ, Q·α = γ}` to the `k` free coordinates and `M` the 2×2 matrix of the solved pair. Independence of the choice of solved pair is a linear change of variables between two parametrisations of the same `k`-dimensional face; the cleanest Lean route seems: both equal `H^k(F)/𝒥` where … — but we avoided Hausdorff measure. Suggest the most economical formal statement (e.g. for two splittings `e₁, e₂` with both `det ≠ 0`: `vol(F'_{e₁})/|det M_{e₁}| = vol(F'_{e₂})/|det M_{e₂}|`) and proof (an affine bijection `F'_{e₁} → F'_{e₂}` with constant Jacobian `|det M_{e₁}|/|det M_{e₂}|`?).

4. **Ranking for the next rounds** among: (c) solved-pair independence; (d) identification of the three-coordinate example's model kernel with `degI` (Fubini bookkeeping on `Fin 1 ⊕ Fin 2`, mechanical); (e) the `c_j = a_j = 0` case; (f) the moving-parameter version of the active-truth theorem (`A(t), B(t), D(t) → A₀, B₀, D₀`; the tied theorem's moving version was obtained by substitution because constants entered only pointwise in `t`; here the constants enter the uniform bound and the DCT majorant, so a parameter-uniform majorant is needed — how?); (g) the general-truth export to hironaka; (h) anything the note needs that we have not listed (e.g. an assembly theorem with active-truth terms alongside vertex/tied terms — `TermMeasureCertificate.ofTermData` already accepts them; or a distinguishability statement for active-truth faces).

Please be specific and concise.
