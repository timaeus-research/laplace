# Consult: germbij analytic layer, eighth research round (after research_round7)

Same setting (Lean 4 + Mathlib, laplace `Laplace.Multi`, mirrored on hironaka `wall-atlas`). Landed since round 7: **your item 1, the transverse active-truth face theorem, constant units, `I = ∅`**, plus the polytope-fibre core, in five files (`PolytopeFibre`, `LogCoordinates`, `ActiveTruthModel`, `LintegralChange`, `ActiveTruthAssembly`, `ActiveTruthFibre`, `ActiveTruthLimit`, `ActiveTruthTheorem`, `ActiveTruthExample`), all sorry-free, standard axioms.

Index: `Fin k ⊕ Fin 2`, the two solved coordinates last (`Sum.inr 0 = a`, `Sum.inr 1 = b`), `z = −log(x/ρ)`, `L = log t`, `s = κ·z − δL`, `h = γL − Q·z`. Route entirely in `lintegral` form: kernel → orthant integral (`x = ρe^{-z}`) → `integral_eq_lintegral_of_nonneg_ae` (no integrability side condition) → Fubini `z = (z', y)` → inner affine change `v = (s,h) = M y + shift(z')` with the orthant condition on `y` carried as an image set → Tonelli (`v` outside, fibre volume inside) → the fibre is the open polytope `{z' > 0 | c_j·z' < a_j L + b_j(v)}` → DCT in `v`.

## Statements (Lean, verbatim)

```lean
def transMat (κ Q : Fin k ⊕ Fin 2 → ℝ) : Matrix (Fin 2) (Fin 2) ℝ :=
  Matrix.of ![fun j ↦ κ (Sum.inr j), fun j ↦ -Q (Sum.inr j)]

/-- The coefficient vector of the `j`-th fibre constraint: `N_{j0} κ' − N_{j1} Q'`. -/
noncomputable def fibreCoef (κ Q : Fin k ⊕ Fin 2 → ℝ) (j : Fin 2) : Fin k → ℝ :=
  fun i ↦ (transMat κ Q)⁻¹ j 0 * κ (Sum.inl i) - (transMat κ Q)⁻¹ j 1 * Q (Sum.inl i)
noncomputable def fibreA (κ Q : Fin k ⊕ Fin 2 → ℝ) (δ γ : ℝ) (j : Fin 2) : ℝ :=
  (transMat κ Q)⁻¹ j 0 * δ - (transMat κ Q)⁻¹ j 1 * γ
noncomputable def fibreB (κ Q : Fin k ⊕ Fin 2 → ℝ) (v : Fin 2 → ℝ) (j : Fin 2) : ℝ :=
  (transMat κ Q)⁻¹ j 0 * v 0 + (transMat κ Q)⁻¹ j 1 * v 1

def poly2 (c₁ c₂ : Fin k → ℝ) (a₁ a₂ : ℝ) : Set (Fin k → ℝ) :=
  {x | (∀ i, 0 ≤ x i) ∧ c₁ ⬝ᵥ x ≤ a₁ ∧ c₂ ⬝ᵥ x ≤ a₂}
/-- The limiting polytope: the face projected to the free coordinates. -/
noncomputable def facePolytope (κ Q : Fin k ⊕ Fin 2 → ℝ) (δ γ : ℝ) : Set (Fin k → ℝ) :=
  poly2 (fibreCoef κ Q 0) (fibreCoef κ Q 1) (fibreA κ Q δ γ 0) (fibreA κ Q δ γ 1)

theorem mem_fibreSet_iff (hΔ : (transMat κ Q).det ≠ 0) (δ γ L : ℝ) (v : Fin 2 → ℝ) (z' : Fin k → ℝ) :
    z' ∈ fibreSet κ Q δ γ L v ↔
      (∀ i, 0 < z' i) ∧ ∀ j, fibreCoef κ Q j ⬝ᵥ z' < fibreA κ Q δ γ j * L + fibreB κ Q v j

/-- **The transverse active-truth face theorem** (constant units, closed-form constant). -/
theorem tendsto_modelKernel_activeTruth' {ρ A B D γ p q δ β η w₀ a₀ : ℝ}
    {Q κ r : Fin k ⊕ Fin 2 → ℝ} (hρ : 0 < ρ) (hD : 0 < D) (hq : 0 < q) (hB : 0 < B)
    (ha₀ : 0 < a₀) (hβ : 0 < β) (hη : 0 < η) (hδ : 0 ≤ δ) (hκ : ∀ i, 0 < κ i)
    (hΔ : (transMat κ Q).det ≠ 0) (hc₀ : fibreCoef κ Q 0 ≠ 0 ∨ fibreA κ Q δ γ 0 ≠ 0)
    (hc₁ : fibreCoef κ Q 1 ≠ 0 ∨ fibreA κ Q δ γ 1 ≠ 0)
    (hr : ∀ i, r i + 1 = β * κ i - η * Q i) :
    Tendsto (fun t ↦ t ^ (γ * p + (β * δ - η * γ)) / log t ^ k *
        modelKernel ρ A B D γ p q δ Q κ r (fun _ _ ↦ w₀) (fun _ _ ↦ a₀) t) atTop
      (𝓝 (A * w₀ * Gamma β * (B * a₀) ^ (-β) * (ρ / D) ^ (q * η) / η *
        (volume (facePolytope κ Q δ γ)).toReal / |(transMat κ Q).det|))
```
(`modelKernel ρ A B D γ p q δ Q κ r W a t = A t^{-γp} ∫ 1_{(0,ρ)^n ∩ {D t^{-γ/q} ∏x^{-Q/q} < ρ}} W(x,v_t) ∏x^r e^{-B t^δ a(x,v_t) ∏x^κ}`, the seabed's constrained model kernel.)

The example of round 6/7, as an instance (`ActiveTruthExample.lean`): `κ = (1,1,2)`, `Q = (1,1,1)`, `r = (0,0,2)`, `(β,η) = (2,1)`, `ρ = A = B = D = q = w₀ = a₀ = 1`, `γ = 2`, `p = 0`, `δ = 3`; `transMat = [[1,2],[−1,−1]]`, `det = 1`, `fibreCoef = (1, 0)`, `fibreA = (1, 1)`, `facePolytope = [0,1]`:
```lean
theorem tendsto_modelKernel_degExample :
    Tendsto (fun t ↦ t ^ 4 / log t *
      modelKernel 1 1 1 1 2 0 1 3 degQ degκ degr (fun _ _ ↦ 1) (fun _ _ ↦ 1) t) atTop (𝓝 1)
```
which agrees with the hand computation `tendsto_degI : t⁴/log t · I(t) → 1` of `DegenerateFace.lean` (the two integrals are not yet formally identified: `modelKernel` on `Fin 1 ⊕ Fin 2` versus the iterated `Ioo` lintegral `degI`).

**Note the nondegeneracy hypothesis.** My first version required `fibreCoef j ≠ 0` for both constraints; the example has `fibreCoef 1 = 0` (the constraint `α_z = 1 ≥ 0` is vacuous), so the hypothesis was weakened to `fibreCoef j ≠ 0 ∨ fibreA j ≠ 0` (used only to make the boundary hyperplanes `{c_j·z' = a_j L + b_j}` null: empty when `c_j = 0`, `a_j L + b_j ≠ 0` eventually). The excluded case `c_j = a_j = 0` is the one where the `j`-th solved coordinate is `y_j ≡ b_j(v)` (the face lies in `{α_j = 0}`), and there the limit genuinely changes (an extra half-plane indicator `1_{b_j(v) ≥ 0}` in the transverse integral).

## Questions

1. **Audit.** Is `tendsto_modelKernel_activeTruth'` correct as stated, and are the hypotheses the right ones? In particular: (a) is `fibreCoef j ≠ 0 ∨ fibreA j ≠ 0` (for both j) equivalent to your "face `F_J` has a positive point" given `κ_J, Q_J` independent, or strictly weaker/stronger? (b) Is `δ ≥ 0` needed (it is used only for `(s + δL)/L ≤ |s| + δ`)? (c) I do not assume `w₀ ≥ 0` or the LP optimality of the face — the theorem is purely about the integral given a certificate `(β, η)` with `r + 1 = βκ − ηQ` and `β, η > 0`. Is that the right decoupling from `lpOptimal_activeTruth_iff`, i.e. does the existence of such a certificate with a nondegenerate face already force the face to be the LP-optimal set (so no separate optimality hypothesis is ever needed at the analytic layer)?

2. **Intrinsic constant.** `vol(F')/|det M|` should equal `H^k(F_J)/𝒥` with `𝒥 = √det(RRᵀ)`, `R = (κ_J; Q_J)` the `2 × n` constraint matrix, independent of the solved pair. Is this worth formalising (a coordinate-independence statement: the constant is the same for any choice of invertible solved pair), and what is the cleanest route in Mathlib (Hausdorff measure of an affine graph vs a direct "change of solved pair" argument comparing two coordinate forms by a linear change of variables on the free coordinates)?

3. **Ranking for the next rounds** (please rank, with the statement shape you would formalise):
   (a) spectator coordinates `I ≠ ∅` with reduced costs `d_i > 0` (extra factor `∫_{(0,1)^I} ∏ y^{d_i − 1}` = `∏ 1/d_i` for constant units; the Fubini freezes `y`);
   (b) face traces `W₀(y, v), a₀(y, v)` with localisation away from the relative boundary of `F_J` (your dominating factor `(1 + |log w| + |log v| + ∑|log y_i|)^k …`);
   (c) the chart-level wrapper: `TermData.activeTruth` for the certificate (`lam = γp + βδ − ηγ`, `kk = k`, `μ = const · dirac(rep 0)`), threading `A = |σ|^{p}/q, B = |σ|^ν, D = |σ|^{1/q}` of `WallChartsData.Phase`;
   (d) the formal identification `modelKernel(example) = (degI t).toReal` (closing the instance check);
   (e) the general-truth Hironaka export (resolving `F·T`), your round-7 item 2;
   (f) anything closer to the note's actual expectation-value claims that the constant-unit theorem now unlocks (e.g. an "active-truth" version of the headline iff `normalise_restrict_eq_iff_forall_tendsto`, or the leading measure `(LM)` at the level of test functions supported in the chart).

4. **One technical question for (a)/(b).** With spectators, the fibre volume bound `κ'_i z'_i ≤ s + δL` and the polynomial envelope `(|s|+δ)^k ≤ (k/a+δ)^k e^{a|s|}` are unchanged; the new factor is `∏_{i∈I} y_i^{d_i−1}` on `(0,1)^I` times, for face traces, `W₀(y, v) e^{-B a₀(y,v) e^{-s}}`. Is there a reason to prefer freezing `y` outside (Fubini in `y` first, then the `I = ∅` theorem pointwise in `y` with `w₀ := W₀(y,·)`) over enlarging the DCT — i.e. can the `I ≠ ∅` theorem be *derived* from the landed `I = ∅` theorem plus a dominated convergence in `y` alone, and what uniform-in-`y` bound would that need on `modelKernel` (`(log t)^k t^{-λ} K_y(t) ≤ C ∏ y^{d−1}` uniformly in `t ≥ t₀`)?

Please be specific and concise; audit first, then ranking, then the technical answer.
