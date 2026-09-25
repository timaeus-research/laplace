/-
Copyright (c) 2026 Timaeus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Timaeus
-/
import Laplace.Multi.ActiveTruthUniform
import Laplace.Multi.ActiveTruthSpectator
import Laplace.Multi.PartialTiedParam

/-!
# The active-truth face theorem with moving constants

Astra round 11, item (f): the constant-unit face theorems with constants `A(t), B(t), D(t)`
converging to `A₀, B₀ > 0, D₀ > 0`, by squeezing rather than by a parameter-uniform dominated
convergence. The constant-unit kernel with `A = 1` is antitone in `B` (the exponential
`e^{-B t^δ a₀ ∏x^κ}` decreases in `B`) and antitone in `D` (the cut `D t^{-γ/q} ∏x^{-Q/q} < ρ`
shrinks the domain as `D` grows) — `modelIntegrand_const_anti_of_le`, pointwise, for any index
type — so for `t` large the moving kernel is trapped between the fixed-parameter kernels at the
corners `(B₀ ∓ d, D₀ ∓ d)`, whose normalised limits converge to the limit at `(B₀, D₀)` as
`d → 0` (`tendsto_of_antitone_param2`, the two-parameter version of the partial-face squeeze).
The comparison of the Bochner kernels goes through `lintegral` and `ENNReal.toReal_mono`, with
finiteness from the uniform bounds (`lintegral_modelIntegrand_const_ne_top`,
`lintegral_modelIntegrand_spectator_ne_top`). Results: `tendsto_modelKernel_activeTruth_param`
(no spectators) and `tendsto_modelKernel_activeTruth_spectator_param`.
-/

open Real MeasureTheory Set Filter Topology
open scoped ENNReal Matrix

namespace Laplace.Multi

/-- **Two-parameter squeeze**: a kernel antitone in two positive parameters, with fixed-parameter
limits continuous at the limiting parameters, converges along moving parameters. -/
theorem tendsto_of_antitone_param2 {f : ℝ → ℝ → ℝ → ℝ} {N B D : ℝ → ℝ} {L : ℝ → ℝ → ℝ}
    {B₀ D₀ : ℝ} (hB₀ : 0 < B₀) (hD₀ : 0 < D₀) (hB : Tendsto B atTop (𝓝 B₀))
    (hD : Tendsto D atTop (𝓝 D₀)) (hN : ∀ᶠ t in atTop, 0 ≤ N t)
    (hanti : ∀ᶠ t in atTop, ∀ b b' d d', 0 < b → b ≤ b' → 0 < d → d ≤ d' → f b' d' t ≤ f b d t)
    (hlim : ∀ b d, 0 < b → 0 < d → Tendsto (fun t ↦ N t * f b d t) atTop (𝓝 (L b d)))
    (hL : ContinuousAt (Function.uncurry L) (B₀, D₀)) :
    Tendsto (fun t ↦ N t * f (B t) (D t) t) atTop (𝓝 (L B₀ D₀)) := by
  have hlo : ContinuousAt (fun d : ℝ ↦ L (B₀ - d) (D₀ - d)) 0 := by
    have hp : ContinuousAt (fun d : ℝ ↦ (B₀ - d, D₀ - d)) 0 :=
      ((continuous_const.sub continuous_id).prodMk
        (continuous_const.sub continuous_id)).continuousAt
    exact hL.comp_of_eq hp (by simp)
  have hhi : ContinuousAt (fun d : ℝ ↦ L (B₀ + d) (D₀ + d)) 0 := by
    have hp : ContinuousAt (fun d : ℝ ↦ (B₀ + d, D₀ + d)) 0 :=
      ((continuous_const.add continuous_id).prodMk
        (continuous_const.add continuous_id)).continuousAt
    exact hL.comp_of_eq hp (by simp)
  rw [Metric.tendsto_nhds]
  intro ε hε
  obtain ⟨η₁, hη₁, hL₁⟩ := Metric.continuousAt_iff.mp hlo (ε / 2) (by positivity)
  obtain ⟨η₂, hη₂, hL₂⟩ := Metric.continuousAt_iff.mp hhi (ε / 2) (by positivity)
  obtain ⟨d, hd⟩ : ∃ d : ℝ, d = min (min (η₁ / 2) (η₂ / 2)) (min (B₀ / 2) (D₀ / 2)) := ⟨_, rfl⟩
  have hd0 : 0 < d := by
    rw [hd]
    exact lt_min (lt_min (by positivity) (by positivity)) (lt_min (by positivity) (by positivity))
  have hdη₁ : d < η₁ := by
    rw [hd]
    exact ((min_le_left _ _).trans (min_le_left _ _)).trans_lt (by linarith)
  have hdη₂ : d < η₂ := by
    rw [hd]
    exact ((min_le_left _ _).trans (min_le_right _ _)).trans_lt (by linarith)
  have hdB : d < B₀ := by
    rw [hd]
    exact ((min_le_right _ _).trans (min_le_left _ _)).trans_lt (by linarith)
  have hdD : d < D₀ := by
    rw [hd]
    exact ((min_le_right _ _).trans (min_le_right _ _)).trans_lt (by linarith)
  have hdd : dist d 0 < η₁ ∧ dist d 0 < η₂ := by
    rw [Real.dist_eq, sub_zero, abs_of_pos hd0]
    exact ⟨hdη₁, hdη₂⟩
  have hLlo : dist (L (B₀ - d) (D₀ - d)) (L B₀ D₀) < ε / 2 := by
    have := hL₁ hdd.1
    simpa using this
  have hLhi : dist (L (B₀ + d) (D₀ + d)) (L B₀ D₀) < ε / 2 := by
    have := hL₂ hdd.2
    simpa using this
  have h1 := (hlim _ _ (by linarith) (by linarith)).eventually
    (Metric.ball_mem_nhds (L (B₀ - d) (D₀ - d)) (half_pos hε))
  have h2 := (hlim _ _ (by linarith) (by linarith)).eventually
    (Metric.ball_mem_nhds (L (B₀ + d) (D₀ + d)) (half_pos hε))
  have hBlo : ∀ᶠ t in atTop, B₀ - d < B t := hB.eventually_const_lt (by linarith)
  have hBhi : ∀ᶠ t in atTop, B t < B₀ + d := hB.eventually_lt_const (by linarith)
  have hDlo : ∀ᶠ t in atTop, D₀ - d < D t := hD.eventually_const_lt (by linarith)
  have hDhi : ∀ᶠ t in atTop, D t < D₀ + d := hD.eventually_lt_const (by linarith)
  filter_upwards [h1, h2, hBlo, hBhi, hDlo, hDhi, hN, hanti] with t h1 h2 hBlo' hBhi' hDlo' hDhi'
    hNt hanti
  rw [Real.dist_eq] at h1 h2
  rw [Real.dist_eq] at hLlo hLhi
  have hup : N t * f (B t) (D t) t ≤ N t * f (B₀ - d) (D₀ - d) t :=
    mul_le_mul_of_nonneg_left (hanti _ _ _ _ (by linarith) hBlo'.le (by linarith) hDlo'.le) hNt
  have hdown : N t * f (B₀ + d) (D₀ + d) t ≤ N t * f (B t) (D t) t :=
    mul_le_mul_of_nonneg_left (hanti _ _ _ _ (by linarith) hBhi'.le (by linarith) hDhi'.le) hNt
  rw [Real.dist_eq, abs_lt]
  constructor
  · linarith [(abs_lt.mp h2).1, (abs_lt.mp hLhi).1]
  · linarith [(abs_lt.mp h1).2, (abs_lt.mp hLlo).2]

/-- The constant-unit integrand is antitone in `B` and in `D`, pointwise. -/
theorem modelIntegrand_const_anti_of_le {ι : Type*} [Fintype ι] {ρ B B' D D' γ q δ t : ℝ}
    {Q κ r : ι → ℝ} {w₀ a₀ : ℝ} (hBB' : B ≤ B') (hDD' : D ≤ D') (ht : 0 ≤ t)
    (hw₀ : 0 ≤ w₀) (ha₀ : 0 ≤ a₀) (x : ι → ℝ) :
    modelIntegrand ρ B' D' γ q δ Q κ r (fun _ _ ↦ w₀) (fun _ _ ↦ a₀) t x ≤
      modelIntegrand ρ B D γ q δ Q κ r (fun _ _ ↦ w₀) (fun _ _ ↦ a₀) t x := by
  unfold modelIntegrand
  by_cases hx : x ∈ modelDomain ρ D' γ q Q t
  · have hx0 : ∀ i, 0 < x i := fun i ↦ ((Set.mem_univ_pi.mp hx.1) i).1
    have hcut : cutVar D γ q Q t x ≤ cutVar D' γ q Q t x := by
      unfold cutVar
      exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hDD' (Real.rpow_nonneg ht _))
        (Finset.prod_nonneg fun j _ ↦ Real.rpow_nonneg (hx0 j).le _)
    have hx' : x ∈ modelDomain ρ D γ q Q t := ⟨hx.1, lt_of_le_of_lt hcut hx.2⟩
    rw [Set.indicator_of_mem hx, Set.indicator_of_mem hx']
    beta_reduce
    have hr0 : 0 ≤ ∏ j, x j ^ r j := Finset.prod_nonneg fun j _ ↦ Real.rpow_nonneg (hx0 j).le _
    have hκ0 : 0 ≤ ∏ j, x j ^ κ j := Finset.prod_nonneg fun j _ ↦ Real.rpow_nonneg (hx0 j).le _
    refine mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr (neg_le_neg ?_)) (mul_nonneg hw₀ hr0)
    exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right hBB' (Real.rpow_nonneg ht _)) ha₀) hκ0
  · rw [Set.indicator_of_notMem hx]
    refine Set.indicator_nonneg (fun y hy ↦ ?_) x
    have hy0 : ∀ i, 0 < y i := fun i ↦ ((Set.mem_univ_pi.mp hy.1) i).1
    exact mul_nonneg (mul_nonneg hw₀ (Finset.prod_nonneg fun j _ ↦
      Real.rpow_nonneg (hy0 j).le _)) (exp_pos _).le

theorem one_lt_of_exp_one_le {t : ℝ} (ht : exp 1 ≤ t) : 1 < t := by
  have := Real.add_one_le_exp (1 : ℝ)
  linarith

section NoSpectator

variable {k : ℕ}

/-- Finiteness of the constant-unit active-truth integral, from the uniform bound. -/
theorem lintegral_modelIntegrand_const_ne_top {ρ B D γ q δ β η a₀ t : ℝ}
    {Q κ r : Fin k ⊕ Fin 2 → ℝ} (hρ : 0 < ρ) (hD : 0 < D) (hq : 0 < q) (hB : 0 < B)
    (ha₀ : 0 < a₀) (hβ : 0 < β) (hη : 0 < η) (hδ : 0 ≤ δ) (hκ : ∀ i, 0 < κ i)
    (hΔ : (transMat κ Q).det ≠ 0) (hr : ∀ i, r i + 1 = β * κ i - η * Q i) (ht : exp 1 ≤ t) :
    ∫⁻ x, ENNReal.ofReal (modelIntegrand ρ B D γ q δ Q κ r (fun _ _ ↦ 1) (fun _ _ ↦ a₀) t x) ≠
      ⊤ := by
  intro htop
  have h := normalised_lintegral_le (γ := γ) hρ hD hq hB ha₀ hβ hη hδ hκ hΔ hr ht
  have ht1 : 1 < t := one_lt_of_exp_one_le ht
  have hc : 0 < t ^ (β * δ - η * γ) / log t ^ k :=
    div_pos (Real.rpow_pos_of_pos (by linarith) _) (pow_pos (Real.log_pos ht1) _)
  rw [htop, ENNReal.mul_top (ENNReal.ofReal_pos.mpr hc).ne'] at h
  exact ENNReal.ofReal_ne_top (top_le_iff.mp h)

/-- The constant-unit active-truth kernel (`A = 1`) is antitone in `(B, D)` for `t ≥ e`. -/
theorem modelKernel_const_anti_active {ρ B B' D D' γ p q δ β η t : ℝ}
    {Q κ r : Fin k ⊕ Fin 2 → ℝ} {w₀ a₀ : ℝ} (hρ : 0 < ρ) (hq : 0 < q) (ha₀ : 0 < a₀)
    (hw₀ : 0 ≤ w₀) (hβ : 0 < β) (hη : 0 < η) (hδ : 0 ≤ δ) (hκ : ∀ i, 0 < κ i)
    (hΔ : (transMat κ Q).det ≠ 0) (hr : ∀ i, r i + 1 = β * κ i - η * Q i) (hB : 0 < B)
    (hBB' : B ≤ B') (hD : 0 < D) (hDD' : D ≤ D') (ht : exp 1 ≤ t) :
    modelKernel ρ 1 B' D' γ p q δ Q κ r (fun _ _ ↦ w₀) (fun _ _ ↦ a₀) t ≤
      modelKernel ρ 1 B D γ p q δ Q κ r (fun _ _ ↦ w₀) (fun _ _ ↦ a₀) t := by
  have ht0 : 0 < t := zero_lt_one.trans (one_lt_of_exp_one_le ht)
  rw [modelKernel_const_eq_toReal, modelKernel_const_eq_toReal]
  refine mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left ?_ hw₀) (by positivity)
  refine ENNReal.toReal_mono
    (lintegral_modelIntegrand_const_ne_top hρ hD hq hB ha₀ hβ hη hδ hκ hΔ hr ht)
    (lintegral_mono fun x ↦ ENNReal.ofReal_le_ofReal ?_)
  exact modelIntegrand_const_anti_of_le hBB' hDD' ht0.le zero_le_one ha₀.le x

/-- **The face theorem with moving constants** (constant units, no spectators):
`A(t) → A₀`, `B(t) → B₀ > 0`, `D(t) → D₀ > 0`. -/
theorem tendsto_modelKernel_activeTruth_param {ρ γ p q δ β η w₀ a₀ : ℝ}
    {Q κ r : Fin k ⊕ Fin 2 → ℝ} {A B D : ℝ → ℝ} {A₀ B₀ D₀ : ℝ} (hρ : 0 < ρ) (hq : 0 < q)
    (ha₀ : 0 < a₀) (hw₀ : 0 ≤ w₀) (hβ : 0 < β) (hη : 0 < η) (hδ : 0 ≤ δ) (hκ : ∀ i, 0 < κ i)
    (hΔ : (transMat κ Q).det ≠ 0) (hc₀ : fibreCoef κ Q 0 ≠ 0 ∨ fibreA κ Q δ γ 0 ≠ 0)
    (hc₁ : fibreCoef κ Q 1 ≠ 0 ∨ fibreA κ Q δ γ 1 ≠ 0)
    (hr : ∀ i, r i + 1 = β * κ i - η * Q i) (hA : Tendsto A atTop (𝓝 A₀))
    (hB : Tendsto B atTop (𝓝 B₀)) (hB₀ : 0 < B₀) (hD : Tendsto D atTop (𝓝 D₀))
    (hD₀ : 0 < D₀) :
    Tendsto (fun t ↦ t ^ (γ * p + (β * δ - η * γ)) / log t ^ k *
        modelKernel ρ (A t) (B t) (D t) γ p q δ Q κ r (fun _ _ ↦ w₀) (fun _ _ ↦ a₀) t) atTop
      (𝓝 (A₀ * w₀ * Gamma β * (B₀ * a₀) ^ (-β) * (ρ / D₀) ^ (q * η) / η *
        (volume (facePolytope κ Q δ γ)).toReal / |(transMat κ Q).det|)) := by
  obtain ⟨L, hLdef⟩ : ∃ L : ℝ → ℝ → ℝ, L = fun b d ↦ 1 * w₀ * Gamma β * (b * a₀) ^ (-β) *
      (ρ / d) ^ (q * η) / η * (volume (facePolytope κ Q δ γ)).toReal / |(transMat κ Q).det| :=
    ⟨_, rfl⟩
  have hlim : ∀ b d, 0 < b → 0 < d → Tendsto (fun t ↦ t ^ (γ * p + (β * δ - η * γ)) / log t ^ k *
      modelKernel ρ 1 b d γ p q δ Q κ r (fun _ _ ↦ w₀) (fun _ _ ↦ a₀) t) atTop (𝓝 (L b d)) :=
    fun b d hb hd ↦ by
      rw [hLdef]
      exact tendsto_modelKernel_activeTruth' (A := 1) hρ hd hq hb ha₀ hβ hη hδ hκ hΔ hc₀ hc₁ hr
  have hL : ContinuousAt (Function.uncurry L) (B₀, D₀) := by
    rw [hLdef]
    have h1 : ContinuousAt (fun p : ℝ × ℝ ↦ (p.1 * a₀) ^ (-β)) (B₀, D₀) :=
      (continuousAt_fst.mul continuousAt_const).rpow_const (Or.inl (mul_pos hB₀ ha₀).ne')
    have h2 : ContinuousAt (fun p : ℝ × ℝ ↦ (ρ / p.2) ^ (q * η)) (B₀, D₀) :=
      (continuousAt_const.div continuousAt_snd hD₀.ne').rpow_const
        (Or.inl (div_pos hρ hD₀).ne')
    exact ((((continuousAt_const.mul h1).mul h2).div_const _).mul continuousAt_const).div_const _
  have hN : ∀ᶠ t : ℝ in atTop, 0 ≤ t ^ (γ * p + (β * δ - η * γ)) / log t ^ k := by
    filter_upwards [eventually_gt_atTop 1] with t ht
    exact div_nonneg (Real.rpow_pos_of_pos (one_pos.trans ht) _).le
      (pow_pos (Real.log_pos ht) _).le
  have hanti : ∀ᶠ t : ℝ in atTop, ∀ b b' d d', 0 < b → b ≤ b' → 0 < d → d ≤ d' →
      modelKernel ρ 1 b' d' γ p q δ Q κ r (fun _ _ ↦ w₀) (fun _ _ ↦ a₀) t ≤
        modelKernel ρ 1 b d γ p q δ Q κ r (fun _ _ ↦ w₀) (fun _ _ ↦ a₀) t := by
    filter_upwards [eventually_ge_atTop (exp 1)] with t ht
    intro b b' d d' hb hbb' hd hdd'
    exact modelKernel_const_anti_active hρ hq ha₀ hw₀ hβ hη hδ hκ hΔ hr hb hbb' hd hdd' ht
  have key := tendsto_of_antitone_param2 hB₀ hD₀ hB hD hN hanti hlim hL
  have hfin := hA.mul key
  have e : A₀ * L B₀ D₀ = A₀ * w₀ * Gamma β * (B₀ * a₀) ^ (-β) * (ρ / D₀) ^ (q * η) / η *
      (volume (facePolytope κ Q δ γ)).toReal / |(transMat κ Q).det| := by
    rw [hLdef]
    ring
  rw [e] at hfin
  refine hfin.congr' (Eventually.of_forall fun t ↦ ?_)
  beta_reduce
  rw [modelKernel_eq_A_mul (A := A t)]
  ring

end NoSpectator

section Spectator

variable {m k : ℕ}

/-- Finiteness of the constant-unit spectator integral, from the spectator majorant. -/
theorem lintegral_modelIntegrand_spectator_ne_top {ρ B D γ q δ β η a₀ t : ℝ}
    {Q κ r : Fin m ⊕ (Fin k ⊕ Fin 2) → ℝ} (hρ : 0 < ρ) (hD : 0 < D) (hq : 0 < q) (hB : 0 < B)
    (ha₀ : 0 < a₀) (hβ : 0 < β) (hη : 0 < η) (hδ : 0 ≤ δ) (hκ : ∀ i, 0 < κ i)
    (hΔ : (transMat (fun j ↦ κ (Sum.inr j)) (fun j ↦ Q (Sum.inr j))).det ≠ 0)
    (hrJ : ∀ j, r (Sum.inr j) + 1 = β * κ (Sum.inr j) - η * Q (Sum.inr j))
    (hd : ∀ i, 0 < specd β η Q κ r i) (ht : exp 1 ≤ t) :
    ∫⁻ x, ENNReal.ofReal (modelIntegrand ρ B D γ q δ Q κ r (fun _ _ ↦ 1) (fun _ _ ↦ a₀) t x) ≠
      ⊤ := by
  intro htop
  have h1 : ∫⁻ ξ, specF ρ B D γ q δ β η a₀ Q κ r t ξ ≤
      ∫⁻ ξ, ENNReal.ofReal (specG ρ B D q δ β η a₀ Q κ r ξ) :=
    lintegral_mono fun ξ ↦ specF_le hρ hD hq hB ha₀ hβ hη hδ hκ hΔ hrJ ht ξ
  have h2 : ∫⁻ ξ, specF ρ B D γ q δ β η a₀ Q κ r t ξ =
      ENNReal.ofReal (t ^ (β * δ - η * γ) / log t ^ k) * ∫⁻ x, ENNReal.ofReal
        (modelIntegrand ρ B D γ q δ Q κ r (fun _ _ ↦ 1) (fun _ _ ↦ a₀) t x) := by
    rw [lintegral_modelIntegrand_spectator, ← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
    refine lintegral_congr fun ξ ↦ ?_
    unfold specF specInner
    ring
  have ht1 : 1 < t := one_lt_of_exp_one_le ht
  have hc : 0 < t ^ (β * δ - η * γ) / log t ^ k :=
    div_pos (Real.rpow_pos_of_pos (by linarith) _) (pow_pos (Real.log_pos ht1) _)
  rw [h2, htop, ENNReal.mul_top (ENNReal.ofReal_pos.mpr hc).ne'] at h1
  exact lintegral_specG_ne_top hρ hB ha₀ hη hδ hκ hd (top_le_iff.mp h1)

theorem modelKernel_const_anti_spectator {ρ B B' D D' γ p q δ β η t : ℝ}
    {Q κ r : Fin m ⊕ (Fin k ⊕ Fin 2) → ℝ} {w₀ a₀ : ℝ} (hρ : 0 < ρ) (hq : 0 < q) (ha₀ : 0 < a₀)
    (hw₀ : 0 ≤ w₀) (hβ : 0 < β) (hη : 0 < η) (hδ : 0 ≤ δ) (hκ : ∀ i, 0 < κ i)
    (hΔ : (transMat (fun j ↦ κ (Sum.inr j)) (fun j ↦ Q (Sum.inr j))).det ≠ 0)
    (hrJ : ∀ j, r (Sum.inr j) + 1 = β * κ (Sum.inr j) - η * Q (Sum.inr j))
    (hd : ∀ i, 0 < specd β η Q κ r i) (hB : 0 < B) (hBB' : B ≤ B') (hD : 0 < D) (hDD' : D ≤ D')
    (ht : exp 1 ≤ t) :
    modelKernel ρ 1 B' D' γ p q δ Q κ r (fun _ _ ↦ w₀) (fun _ _ ↦ a₀) t ≤
      modelKernel ρ 1 B D γ p q δ Q κ r (fun _ _ ↦ w₀) (fun _ _ ↦ a₀) t := by
  have ht0 : 0 < t := zero_lt_one.trans (one_lt_of_exp_one_le ht)
  rw [modelKernel_const_eq_toReal, modelKernel_const_eq_toReal]
  refine mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left ?_ hw₀) (by positivity)
  refine ENNReal.toReal_mono
    (lintegral_modelIntegrand_spectator_ne_top hρ hD hq hB ha₀ hβ hη hδ hκ hΔ hrJ hd ht)
    (lintegral_mono fun x ↦ ENNReal.ofReal_le_ofReal ?_)
  exact modelIntegrand_const_anti_of_le hBB' hDD' ht0.le zero_le_one ha₀.le x

/-- **The spectator face theorem with moving constants** (constant units). -/
theorem tendsto_modelKernel_activeTruth_spectator_param {ρ γ p q δ β η w₀ a₀ : ℝ}
    {Q κ r : Fin m ⊕ (Fin k ⊕ Fin 2) → ℝ} {A B D : ℝ → ℝ} {A₀ B₀ D₀ : ℝ} (hρ : 0 < ρ)
    (hq : 0 < q) (ha₀ : 0 < a₀) (hw₀ : 0 ≤ w₀) (hβ : 0 < β) (hη : 0 < η) (hδ : 0 ≤ δ)
    (hκ : ∀ i, 0 < κ i)
    (hΔ : (transMat (fun j ↦ κ (Sum.inr j)) (fun j ↦ Q (Sum.inr j))).det ≠ 0)
    (hc₀ : fibreCoef (fun j ↦ κ (Sum.inr j)) (fun j ↦ Q (Sum.inr j)) 0 ≠ 0 ∨
      fibreA (fun j ↦ κ (Sum.inr j)) (fun j ↦ Q (Sum.inr j)) δ γ 0 ≠ 0)
    (hc₁ : fibreCoef (fun j ↦ κ (Sum.inr j)) (fun j ↦ Q (Sum.inr j)) 1 ≠ 0 ∨
      fibreA (fun j ↦ κ (Sum.inr j)) (fun j ↦ Q (Sum.inr j)) δ γ 1 ≠ 0)
    (hrJ : ∀ j, r (Sum.inr j) + 1 = β * κ (Sum.inr j) - η * Q (Sum.inr j))
    (hd : ∀ i, 0 < specd β η Q κ r i) (hA : Tendsto A atTop (𝓝 A₀))
    (hB : Tendsto B atTop (𝓝 B₀)) (hB₀ : 0 < B₀) (hD : Tendsto D atTop (𝓝 D₀))
    (hD₀ : 0 < D₀) :
    Tendsto (fun t ↦ t ^ (γ * p + (β * δ - η * γ)) / log t ^ k *
        modelKernel ρ (A t) (B t) (D t) γ p q δ Q κ r (fun _ _ ↦ w₀) (fun _ _ ↦ a₀) t) atTop
      (𝓝 (A₀ * w₀ * Gamma β * (B₀ * a₀) ^ (-β) * (ρ / D₀) ^ (q * η) / η *
        (volume (facePolytope (fun j ↦ κ (Sum.inr j)) (fun j ↦ Q (Sum.inr j)) δ γ)).toReal /
        |(transMat (fun j ↦ κ (Sum.inr j)) (fun j ↦ Q (Sum.inr j))).det| *
        ∏ i, ρ ^ specd β η Q κ r i / specd β η Q κ r i)) := by
  obtain ⟨L, hLdef⟩ : ∃ L : ℝ → ℝ → ℝ, L = fun b d ↦ 1 * w₀ * Gamma β * (b * a₀) ^ (-β) *
      (ρ / d) ^ (q * η) / η *
      (volume (facePolytope (fun j ↦ κ (Sum.inr j)) (fun j ↦ Q (Sum.inr j)) δ γ)).toReal /
      |(transMat (fun j ↦ κ (Sum.inr j)) (fun j ↦ Q (Sum.inr j))).det| *
      ∏ i, ρ ^ specd β η Q κ r i / specd β η Q κ r i := ⟨_, rfl⟩
  have hlim : ∀ b d, 0 < b → 0 < d → Tendsto (fun t ↦ t ^ (γ * p + (β * δ - η * γ)) / log t ^ k *
      modelKernel ρ 1 b d γ p q δ Q κ r (fun _ _ ↦ w₀) (fun _ _ ↦ a₀) t) atTop (𝓝 (L b d)) :=
    fun b d hb hd' ↦ by
      rw [hLdef]
      exact tendsto_modelKernel_activeTruth_spectator (A := 1) hρ hd' hq hb ha₀ hβ hη hδ hκ hΔ
        hc₀ hc₁ hrJ hd
  have hL : ContinuousAt (Function.uncurry L) (B₀, D₀) := by
    rw [hLdef]
    have h1 : ContinuousAt (fun p : ℝ × ℝ ↦ (p.1 * a₀) ^ (-β)) (B₀, D₀) :=
      (continuousAt_fst.mul continuousAt_const).rpow_const (Or.inl (mul_pos hB₀ ha₀).ne')
    have h2 : ContinuousAt (fun p : ℝ × ℝ ↦ (ρ / p.2) ^ (q * η)) (B₀, D₀) :=
      (continuousAt_const.div continuousAt_snd hD₀.ne').rpow_const
        (Or.inl (div_pos hρ hD₀).ne')
    exact (((((continuousAt_const.mul h1).mul h2).div_const _).mul continuousAt_const).div_const
      _).mul continuousAt_const
  have hN : ∀ᶠ t : ℝ in atTop, 0 ≤ t ^ (γ * p + (β * δ - η * γ)) / log t ^ k := by
    filter_upwards [eventually_gt_atTop 1] with t ht
    exact div_nonneg (Real.rpow_pos_of_pos (one_pos.trans ht) _).le
      (pow_pos (Real.log_pos ht) _).le
  have hanti : ∀ᶠ t : ℝ in atTop, ∀ b b' d d', 0 < b → b ≤ b' → 0 < d → d ≤ d' →
      modelKernel ρ 1 b' d' γ p q δ Q κ r (fun _ _ ↦ w₀) (fun _ _ ↦ a₀) t ≤
        modelKernel ρ 1 b d γ p q δ Q κ r (fun _ _ ↦ w₀) (fun _ _ ↦ a₀) t := by
    filter_upwards [eventually_ge_atTop (exp 1)] with t ht
    intro b b' d d' hb hbb' hd' hdd'
    exact modelKernel_const_anti_spectator hρ hq ha₀ hw₀ hβ hη hδ hκ hΔ hrJ hd hb hbb' hd' hdd' ht
  have key := tendsto_of_antitone_param2 hB₀ hD₀ hB hD hN hanti hlim hL
  have hfin := hA.mul key
  have e : A₀ * L B₀ D₀ = A₀ * w₀ * Gamma β * (B₀ * a₀) ^ (-β) * (ρ / D₀) ^ (q * η) / η *
      (volume (facePolytope (fun j ↦ κ (Sum.inr j)) (fun j ↦ Q (Sum.inr j)) δ γ)).toReal /
      |(transMat (fun j ↦ κ (Sum.inr j)) (fun j ↦ Q (Sum.inr j))).det| *
      ∏ i, ρ ^ specd β η Q κ r i / specd β η Q κ r i := by
    rw [hLdef]
    ring
  rw [e] at hfin
  refine hfin.congr' (Eventually.of_forall fun t ↦ ?_)
  beta_reduce
  rw [modelKernel_eq_A_mul (A := A t)]
  ring

end Spectator

end Laplace.Multi
