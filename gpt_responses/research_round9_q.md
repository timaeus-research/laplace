# Consult: germbij analytic layer, ninth research round (after research_round8)

Same setting (Lean 4 + Mathlib, laplace `Laplace.Multi`, mirrored on hironaka `wall-atlas`). Landed since round 8, following your ranking:

1. **Constant units with spectators** (your item 2), `ActiveTruthSpectator.lean`, on the index `Fin m ⊕ (Fin k ⊕ Fin 2)` (spectators first). Route: your "outer DCT": the constant-unit theorem restated in `lintegral` form with a uniform bound for `t ≥ e` (`ActiveTruthUniform.lean`: `∫ e^{-βs} e^{-ce^{-s}} (|s|+δ)^k ds ≤ c^{-β}(1 + δ + |log c|)^k C_k` by the shift `s ↦ s + log c`), the frozen-spectator factorisation (`modelIntegrand(elim ξ x') = 1_{(0,ρ)^m}(ξ) ∏ξ^{r_I} · modelIntegrand(B_ξ, D_ξ)(x')`, `B_ξ = B∏ξ^{κ_I}`, `D_ξ = D∏ξ^{−Q_I/q}`), the factor identity `∏ξ^{r} c₀(ξ)^{-β} e^{-ηh₀(ξ)} = c_J^{-β} e^{-ηh₀J} ∏ ξ^{d_i−1}`, the logarithmic loss distributed by `C + ∑ aᵢ ≤ C ∏(1 + aᵢ)`, and the one-variable integrability of `x^{d−1}(C + a|log x|)^k` on `(0,ρ)`:

```lean
theorem tendsto_modelKernel_activeTruth_spectator {ρ A B D γ p q δ β η w₀ a₀ : ℝ}
    {Q κ r : Fin m ⊕ (Fin k ⊕ Fin 2) → ℝ} (hρ : 0 < ρ) (hD : 0 < D) (hq : 0 < q) (hB : 0 < B)
    (ha₀ : 0 < a₀) (hβ : 0 < β) (hη : 0 < η) (hδ : 0 ≤ δ) (hκ : ∀ i, 0 < κ i)
    (hΔ : (transMat (fun j ↦ κ (Sum.inr j)) (fun j ↦ Q (Sum.inr j))).det ≠ 0)
    (hc₀ : fibreCoef κJ QJ 0 ≠ 0 ∨ fibreA κJ QJ δ γ 0 ≠ 0) (hc₁ : … 1 …)
    (hrJ : ∀ j, r (Sum.inr j) + 1 = β * κ (Sum.inr j) - η * Q (Sum.inr j))
    (hd : ∀ i, 0 < specd β η Q κ r i) :   -- specd i = r (inl i) + 1 − β κ (inl i) + η Q (inl i)
    Tendsto (fun t ↦ t ^ (γ * p + (β * δ - η * γ)) / log t ^ k *
        modelKernel ρ A B D γ p q δ Q κ r (fun _ _ ↦ w₀) (fun _ _ ↦ a₀) t) atTop
      (𝓝 (A * w₀ * Gamma β * (B * a₀) ^ (-β) * (ρ / D) ^ (q * η) / η *
        (volume (facePolytope κJ QJ δ γ)).toReal / |(transMat κJ QJ).det| *
        ∏ i, ρ ^ specd β η Q κ r i / specd β η Q κ r i))
```
(`κJ = fun j ↦ κ (Sum.inr j)` etc.)

2. The seabed's model kernel is `modelKernel ρ A B D γ p q δ Q κ r W a t = A t^{-γp} ∫ 1_{(0,ρ)^n ∩ {u_t < ρ}} W(x, u_t(x)) ∏x^r e^{-B t^δ a(x, u_t(x)) ∏x^κ}` with `u_t(x) = D t^{-γ/q} ∏ x^{-Q/q}` (`cutVar`); in log coordinates `x = ρe^{-z}`, `u_t = D ρ^{-∑Q/q} t^{-γ/q} e^{Q·z/q}`, and in the transverse coordinates `s = κ·z − δL`, `h = γL − Q·z` (`L = log t`) it is `u(h) = D ρ^{-∑Q/q} e^{-h/q}` — `t`-free, of order one, as you said in round 8.

## The next theorem: the exact trace model (your item 3.1), then the chart-level statement (item 4)

I intend to generalise the pipeline from constant units to **truth-dependent units** `W(x, u) = w(u)`, `a(x, u) = a(u)` (still `I = ∅` first), by carrying `w(u(h))` and `a(u(h))` through the same five steps: the inner substitution is unchanged (the new factors depend only on `Q·z = γL − h`), Tonelli is unchanged (the fibre set does not see `w, a`), the `v`-weight becomes `1_{h>h₀} e^{-βs−ηh} w(u(h)) e^{-B ρ^{∑κ} a(u(h)) e^{-s}}`, the DCT bound is `W_* · (the constant-unit bound at a_-)` with `|w| ≤ W_*`, `a ≥ a_- > 0`, and the limit is
```
t^{γp+βδ−ηγ}/(log t)^k · K(t) → A vol(F')/|det M| · Γ(β) ρ^{∑(r+1)} (Bρ^{∑κ})^{-β} ∫_{h>h₀} e^{-ηh} w(u(h)) a(u(h))^{-β} dh
                                = A vol(F')/|det M| · Γ(β) B^{-β} q D^{-qη} ∫_0^ρ u^{qη−1} w(u) a(u)^{-β} du
```
(`ρ^{∑(r+1)} ρ^{-β∑κ} ρ^{η∑Q} = 1` by the certificate; the second line by `u = D ρ^{-∑Q/q} e^{-h/q}`, `dh = −q du/u`).

**Questions.**

1. **Hypotheses on `w, a`.** For the `lintegral` route I need `w ≥ 0` (signed `w` then by linearity, `w = (w + W_*) − W_*`). Is "`w` measurable, `0 ≤ w ≤ W_*`; `a` measurable, `a_- ≤ a`" the right generality, or should I insist on continuity now because the chart-level statement will need `w(u) = φ(chart point)·(unit)` continuous? Any subtlety with the truth cut `u < ρ` (open) versus `u ≤ ρ` for measurable `w`?

2. **The chart-level statement (item 4).** In the seabed the certified observables are functions `φ` of the chart coordinate `x` (all `n` coordinates), not of `u`. For an active-truth chart with `I = ∅`, on the face's relative interior every active coordinate `x_j = ρ e^{-Lα_j} → 0`, so `φ(x) → φ(0)` and the leading measure *for such observables* is `c · δ₀` with `c = A Γ(β) B^{-β} q D^{-qη} vol(F')/|det M| ∫_0^ρ u^{qη−1} W₀(0,u) a₀(0,u)^{-β} du` — Dirac after all, with the `u`-integral inside the constant. Do you agree, and is your round-8 warning ("not Dirac") only about observables that see `u` (i.e. depend on `t` through `u_t(x)`)? If so the seabed's `TermData`/`TermMeasureCertificate` interface (`μ = c • dirac (rep 0)`) is the right target for active-truth charts, with spectators giving `δ_{x_J = 0} ⊗ ∏ y^{d−1} dy` instead.

3. **Trace replacement (item 3.2).** With `W(x,u)` depending on the active coordinates, Tonelli no longer separates: the inner integral becomes `∫_{fibreSet v} W(ρe^{-z(z')}, u(h)) dz'` and I need `L^{-k} ∫_{fibreSet v} W(ρe^{-z}, u) dz' → W(0, u) vol(F')` — by the scaling `z' = Lw` and DCT on the polytope: for `w` in the relative interior of `F'`, all coordinates of `z = (Lw, y(Lw))` tend to `+∞`, so `x → 0`; domination by `sup|W|`. Is this the right shape of the "localisation away from the relative boundary" — i.e. is the hypothesis just "`W` bounded, and `W(·, u) → W(0, u)` as `x_J → 0` for each `u`" (continuity of `W` at `x_J = 0` uniformly? or pointwise plus DCT suffices since the fibre points converge to `0` for a.e. `w`)? What exactly must be assumed about `W` near the boundary `∂F'` (where some `α_j = 0` and `x_j` does not go to `0`) — nothing, because `∂F'` is null?

4. **Order of work.** (i) exact trace model `w(u), a(u)`; (ii) trace replacement in `x_J`; (iii) redo spectators on top (units `W(y, u)`); (iv) the chart wrapper `TermData.activeTruth`. Or is there a shortcut: prove (ii) directly with `W(x, u)` general (bounded measurable, continuous at the face) and skip (i) as a separate statement? What is the cleanest single statement you would formalise that covers (i)+(ii) and feeds (iv)?

5. **The seabed's positivity requirements.** `TermData` needs `0 ≤ c` for `μ = ofReal c • dirac`; the note's units satisfy `W₀ > 0`, `a₀ > 0` on the face. With signed `A` (`A = |σ|^p/q > 0` in the phase data) everything is nonneg — fine. Anything else the certificate needs that the analytic theorem should output (e.g. the `lam₀/k₀` minimality across terms is bookkeeping in `ofTerms`; nothing analytic)?

Please be specific and concise: the statements you would write, the hypotheses, and the order.
