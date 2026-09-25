/-
Copyright (c) 2026 Timaeus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Timaeus
-/
import Laplace.Multi.ActiveTruthGeneralUniform
import Laplace.Multi.ActiveTruthSpectatorGeneral
import Laplace.Multi.ActiveTruthParam

/-!
# The general-unit face theorem with moving constants

The squeeze of `ActiveTruthParam.lean` needs the units fixed, because a moving cut constant `D`
enters the unit argument `u = D t^{-γ/q} ∏ x^{-Q/q}`. The way around is a **time change**: for
`γ > 0` the cut at `(D, t)` is the cut at `(D₀, τ)` with `τ = t (D₀/D)^{q/γ}` (`cutVar_cutTime`),
and the remaining constants absorb the change (`modelKernel_cutTime`: the kernel at `(A, B, D, t)`
is the kernel at `(A (D₀/D)^{qp}, B (D₀/D)^{-qδ/γ}, D₀, τ)`, exactly). Moving `D` is thereby
reduced to moving `A, B` along the reparametrised time, and `B` enters only through the
exponential, which is antitone for any nonnegative units (`modelIntegrand_anti_B`), so the
one-parameter squeeze applies to the general-unit kernel at fixed `D₀`
(`modelKernel_anti_B_general`, finiteness from `normalised_lintegral_leG`). The normaliser ratio
`N(t)/N(τ)` tends to `1` (`tendsto_normaliser_ratio`). Result: `tendsto_modelKernel_general_param`,
the trace theorem with `A(t) → A₀`, `B(t) → B₀ > 0`, `D(t) → D₀ > 0`.
-/

open Real MeasureTheory Set Filter Topology
open scoped ENNReal Matrix

namespace Laplace.Multi

/-- The time change absorbing a moving cut constant: `τ = t (D₀/D)^{q/γ}`. -/
noncomputable def cutTime (D₀ γ q D t : ℝ) : ℝ := t * (D₀ / D) ^ (q / γ)

theorem cutTime_pos {D₀ γ q D t : ℝ} (hD : 0 < D) (hD₀ : 0 < D₀) (ht : 0 < t) :
    0 < cutTime D₀ γ q D t :=
  mul_pos ht (Real.rpow_pos_of_pos (div_pos hD₀ hD) _)

theorem rpow_cutTime {D₀ γ q D t : ℝ} (hD : 0 < D) (hD₀ : 0 < D₀) (ht : 0 < t) (e : ℝ) :
    cutTime D₀ γ q D t ^ e = t ^ e * (D₀ / D) ^ (q / γ * e) := by
  unfold cutTime
  rw [Real.mul_rpow ht.le (Real.rpow_nonneg (div_pos hD₀ hD).le _),
    ← Real.rpow_mul (div_pos hD₀ hD).le]

/-- The cut at `(D, t)` is the cut at `(D₀, τ)`. -/
theorem cutVar_cutTime {ι : Type*} [Fintype ι] {D₀ γ q D t : ℝ} (hD : 0 < D) (hD₀ : 0 < D₀)
    (hγ : 0 < γ) (hq : 0 < q) (ht : 0 < t) (Q : ι → ℝ) (x : ι → ℝ) :
    cutVar D₀ γ q Q (cutTime D₀ γ q D t) x = cutVar D γ q Q t x := by
  unfold cutVar
  congr 1
  rw [rpow_cutTime hD hD₀ ht, show q / γ * (-(γ / q)) = -1 by field_simp, Real.rpow_neg_one,
    inv_div]
  field_simp

/-- **The kernel under the time change**: moving `D` is moving `A, B` at the reparametrised time. -/
theorem modelKernel_cutTime {ι : Type*} [Fintype ι] {ρ A B D D₀ γ p q δ t : ℝ} {Q κ r : ι → ℝ}
    {W a : (ι → ℝ) → ℝ → ℝ} (hD : 0 < D) (hD₀ : 0 < D₀) (hγ : 0 < γ) (hq : 0 < q) (ht : 0 < t) :
    modelKernel ρ A B D γ p q δ Q κ r W a t =
      modelKernel ρ (A * (D₀ / D) ^ (q * p)) (B * (D₀ / D) ^ (-(q * δ / γ))) D₀ γ p q δ Q κ r W a
        (cutTime D₀ γ q D t) := by
  have hc : 0 < D₀ / D := div_pos hD₀ hD
  have hA : A * (D₀ / D) ^ (q * p) * cutTime D₀ γ q D t ^ (-(γ * p)) = A * t ^ (-(γ * p)) := by
    rw [rpow_cutTime hD hD₀ ht]
    have : (D₀ / D) ^ (q * p) * (D₀ / D) ^ (q / γ * -(γ * p)) = 1 := by
      rw [← Real.rpow_add hc, show q * p + q / γ * -(γ * p) = 0 by field_simp; ring,
        Real.rpow_zero]
    linear_combination (A * t ^ (-(γ * p))) * this
  have hB : B * (D₀ / D) ^ (-(q * δ / γ)) * cutTime D₀ γ q D t ^ δ = B * t ^ δ := by
    rw [rpow_cutTime hD hD₀ ht]
    have : (D₀ / D) ^ (-(q * δ / γ)) * (D₀ / D) ^ (q / γ * δ) = 1 := by
      rw [← Real.rpow_add hc, show -(q * δ / γ) + q / γ * δ = 0 by field_simp; ring,
        Real.rpow_zero]
    linear_combination (B * t ^ δ) * this
  unfold modelKernel
  rw [hA]
  congr 1
  refine integral_congr_ae (Eventually.of_forall fun x ↦ ?_)
  unfold modelIntegrand modelDomain
  simp only [cutVar_cutTime hD hD₀ hγ hq ht]
  rw [hB]

/-- The general-unit integrand is antitone in `B` for nonnegative units. -/
theorem modelIntegrand_anti_B {ι : Type*} [Fintype ι] {ρ B B' D γ q δ t : ℝ} {Q κ r : ι → ℝ}
    {W a : (ι → ℝ) → ℝ → ℝ} (hBB' : B ≤ B') (ht : 0 ≤ t) (hW : ∀ x u, 0 ≤ W x u)
    (ha : ∀ x u, 0 ≤ a x u) (x : ι → ℝ) :
    modelIntegrand ρ B' D γ q δ Q κ r W a t x ≤ modelIntegrand ρ B D γ q δ Q κ r W a t x := by
  unfold modelIntegrand
  by_cases hx : x ∈ modelDomain ρ D γ q Q t
  · have hx0 : ∀ i, 0 < x i := fun i ↦ ((Set.mem_univ_pi.mp hx.1) i).1
    rw [Set.indicator_of_mem hx, Set.indicator_of_mem hx]
    have hr0 : 0 ≤ ∏ j, x j ^ r j := Finset.prod_nonneg fun j _ ↦ Real.rpow_nonneg (hx0 j).le _
    have hκ0 : 0 ≤ ∏ j, x j ^ κ j := Finset.prod_nonneg fun j _ ↦ Real.rpow_nonneg (hx0 j).le _
    refine mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr (neg_le_neg ?_)) (mul_nonneg (hW _ _) hr0)
    exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right hBB' (Real.rpow_nonneg ht _)) (ha _ _)) hκ0
  · rw [Set.indicator_of_notMem hx, Set.indicator_of_notMem hx]

/-- The kernel of nonnegative measurable units as the real part of a `lintegral`. -/
theorem modelKernel_eq_toReal_of_nonneg {ι : Type*} [Fintype ι] {ρ A B D γ p q δ t : ℝ}
    {Q κ r : ι → ℝ} {W a : (ι → ℝ) → ℝ → ℝ} (hWm : Measurable (Function.uncurry W))
    (ham : Measurable (Function.uncurry a)) (hW : ∀ x u, 0 ≤ W x u) :
    modelKernel ρ A B D γ p q δ Q κ r W a t = A * t ^ (-(γ * p)) *
      (∫⁻ x, ENNReal.ofReal (modelIntegrand ρ B D γ q δ Q κ r W a t x)).toReal := by
  unfold modelKernel
  rw [integral_eq_lintegral_of_nonneg_ae (ae_of_all _ (modelIntegrand_nonneg_of_nonneg hW))
    (measurable_modelIntegrand hWm ham t).aestronglyMeasurable]

variable {k : ℕ}

/-- Finiteness of the general-unit integral, from the uniform bound. -/
theorem lintegral_modelIntegrand_general_ne_top {ρ B D γ q δ β η t : ℝ}
    {Q κ r : Fin k ⊕ Fin 2 → ℝ} (hρ : 0 < ρ) (hD : 0 < D) (hq : 0 < q) (hB : 0 < B) (hβ : 0 < β)
    (hη : 0 < η) (hδ : 0 ≤ δ) (hκ : ∀ i, 0 < κ i) (hΔ : (transMat κ Q).det ≠ 0)
    (hr : ∀ i, r i + 1 = β * κ i - η * Q i) {W a : (Fin k ⊕ Fin 2 → ℝ) → ℝ → ℝ}
    {Wstar amin : ℝ} (hamin : 0 < amin) (hWm : Measurable (Function.uncurry W))
    (ham : Measurable (Function.uncurry a)) (hWb : ∀ x u, 0 ≤ W x u ∧ W x u ≤ Wstar)
    (hab : ∀ x u, amin ≤ a x u) (ht : exp 1 ≤ t) :
    ∫⁻ x, ENNReal.ofReal (modelIntegrand ρ B D γ q δ Q κ r W a t x) ≠ ⊤ := by
  intro htop
  have h := normalised_lintegral_leG (γ := γ) hρ hD hq hB hβ hη hδ hκ hΔ hr hamin hWm ham hWb hab
    ht
  have ht1 : 1 < t := one_lt_of_exp_one_le ht
  have hc : 0 < t ^ (β * δ - η * γ) / log t ^ k :=
    div_pos (Real.rpow_pos_of_pos (by linarith) _) (pow_pos (Real.log_pos ht1) _)
  rw [htop, ENNReal.mul_top (ENNReal.ofReal_pos.mpr hc).ne'] at h
  exact ENNReal.ofReal_ne_top (top_le_iff.mp h)

/-- The general-unit kernel (`A = 1`) is antitone in `B` for `t ≥ e`. -/
theorem modelKernel_anti_B_general {ρ B B' D γ p q δ β η t : ℝ} {Q κ r : Fin k ⊕ Fin 2 → ℝ}
    (hρ : 0 < ρ) (hD : 0 < D) (hq : 0 < q) (hβ : 0 < β) (hη : 0 < η) (hδ : 0 ≤ δ)
    (hκ : ∀ i, 0 < κ i) (hΔ : (transMat κ Q).det ≠ 0) (hr : ∀ i, r i + 1 = β * κ i - η * Q i)
    {W a : (Fin k ⊕ Fin 2 → ℝ) → ℝ → ℝ} {Wstar amin : ℝ} (hamin : 0 < amin)
    (hWm : Measurable (Function.uncurry W)) (ham : Measurable (Function.uncurry a))
    (hWb : ∀ x u, 0 ≤ W x u ∧ W x u ≤ Wstar) (hab : ∀ x u, amin ≤ a x u) (hB : 0 < B)
    (hBB' : B ≤ B') (ht : exp 1 ≤ t) :
    modelKernel ρ 1 B' D γ p q δ Q κ r W a t ≤ modelKernel ρ 1 B D γ p q δ Q κ r W a t := by
  have ht0 : 0 < t := zero_lt_one.trans (one_lt_of_exp_one_le ht)
  rw [modelKernel_eq_toReal_of_nonneg hWm ham (fun x u ↦ (hWb x u).1),
    modelKernel_eq_toReal_of_nonneg hWm ham (fun x u ↦ (hWb x u).1)]
  refine mul_le_mul_of_nonneg_left ?_ (by positivity)
  refine ENNReal.toReal_mono (lintegral_modelIntegrand_general_ne_top hρ hD hq hB hβ hη hδ hκ hΔ hr
    hamin hWm ham hWb hab ht) (lintegral_mono fun x ↦ ENNReal.ofReal_le_ofReal ?_)
  exact modelIntegrand_anti_B hBB' ht0.le (fun x u ↦ (hWb x u).1)
    (fun x u ↦ hamin.le.trans (hab x u)) x

/-- The normaliser `t^λ/(log t)^k` at `t` and at `t c(t)` have ratio tending to `1` when
`c(t) → 1`. -/
theorem tendsto_normaliser_ratio {c : ℝ → ℝ} (hc : Tendsto c atTop (𝓝 1)) (lam : ℝ) (k : ℕ) :
    Tendsto (fun t ↦ (t ^ lam / log t ^ k) / ((t * c t) ^ lam / log (t * c t) ^ k)) atTop
      (𝓝 1) := by
  have hcpos : ∀ᶠ t in atTop, 0 < c t := hc.eventually_const_lt one_pos |>.mono fun t ht ↦ by
    linarith
  have hlogc : Tendsto (fun t ↦ log (c t)) atTop (𝓝 0) := by
    have := (Real.continuousAt_log one_ne_zero).tendsto.comp hc
    rwa [Real.log_one] at this
  have hq : Tendsto (fun t ↦ log (c t) / log t) atTop (𝓝 0) :=
    hlogc.div_atTop Real.tendsto_log_atTop
  have hpow : Tendsto (fun t ↦ (c t) ^ (-lam)) atTop (𝓝 1) := by
    have := hc.rpow_const (p := -lam) (Or.inl one_ne_zero)
    rwa [Real.one_rpow] at this
  have hlim : Tendsto (fun t ↦ (c t) ^ (-lam) * (1 + log (c t) / log t) ^ k) atTop (𝓝 1) := by
    have := hpow.mul (((tendsto_const_nhds (x := (1 : ℝ))).add hq).pow k)
    simpa using this
  refine hlim.congr' ?_
  filter_upwards [eventually_gt_atTop 1, hcpos] with t ht hct
  have ht0 : 0 < t := zero_lt_one.trans ht
  have hL : 0 < log t := Real.log_pos ht
  rw [Real.mul_rpow ht0.le hct.le, Real.log_mul ht0.ne' hct.ne', Real.rpow_neg hct.le]
  have h1 : t ^ lam ≠ 0 := (Real.rpow_pos_of_pos ht0 _).ne'
  have h2 : c t ^ lam ≠ 0 := (Real.rpow_pos_of_pos hct _).ne'
  have h3 : log t ^ k ≠ 0 := (pow_pos hL _).ne'
  have h4 : (1 + log (c t) / log t) ^ k = (log t + log (c t)) ^ k / log t ^ k := by
    rw [← div_pow]
    congr 1
    field_simp
  rw [h4]
  field_simp

/-- **The general-unit face theorem with moving constants**: `A(t) → A₀`, `B(t) → B₀ > 0`,
`D(t) → D₀ > 0`, `γ > 0`, jointly measurable bounded units with traces. -/
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
        ∫ u in Ioo (0 : ℝ) ρ, u ^ (q * η - 1) * (Wtr u * atr u ^ (-β)))) := by
  obtain ⟨lam, hlam⟩ : ∃ lam : ℝ, lam = γ * p + (β * δ - η * γ) := ⟨_, rfl⟩
  obtain ⟨N, hN⟩ : ∃ N : ℝ → ℝ, N = fun t ↦ t ^ lam / log t ^ k := ⟨_, rfl⟩
  obtain ⟨c, hcdef⟩ : ∃ c : ℝ → ℝ, c = fun t ↦ (D₀ / D t) ^ (q / γ) := ⟨_, rfl⟩
  obtain ⟨τ, hτdef⟩ : ∃ τ : ℝ → ℝ, τ = fun t ↦ t * c t := ⟨_, rfl⟩
  obtain ⟨A', hA'def⟩ : ∃ A' : ℝ → ℝ, A' = fun t ↦ A t * (D₀ / D t) ^ (q * p) := ⟨_, rfl⟩
  obtain ⟨B', hB'def⟩ : ∃ B' : ℝ → ℝ, B' = fun t ↦ B t * (D₀ / D t) ^ (-(q * δ / γ)) := ⟨_, rfl⟩
  have hDpos : ∀ᶠ t in atTop, 0 < D t :=
    (hD.eventually_const_lt (half_lt_self hD₀)).mono fun t ht ↦ by linarith
  have hratio : Tendsto (fun t ↦ D₀ / D t) atTop (𝓝 1) := by
    have := (tendsto_const_nhds (x := D₀)).div hD hD₀.ne'
    rwa [div_self hD₀.ne'] at this
  have hc : Tendsto c atTop (𝓝 1) := by
    rw [hcdef]
    have := hratio.rpow_const (p := q / γ) (Or.inl one_ne_zero)
    rwa [Real.one_rpow] at this
  have hτ : Tendsto τ atTop atTop := by
    rw [hτdef]
    exact tendsto_id.atTop_mul_pos one_pos hc
  have hA' : Tendsto A' atTop (𝓝 A₀) := by
    rw [hA'def]
    have := hA.mul (hratio.rpow_const (p := q * p) (Or.inl one_ne_zero))
    rwa [Real.one_rpow, mul_one] at this
  have hB' : Tendsto B' atTop (𝓝 B₀) := by
    rw [hB'def]
    have := hB.mul (hratio.rpow_const (p := -(q * δ / γ)) (Or.inl one_ne_zero))
    rwa [Real.one_rpow, mul_one] at this
  -- the fixed-`b` limits along the reparametrised time
  obtain ⟨L, hLdef⟩ : ∃ L : ℝ → ℝ, L = fun b ↦ 1 * Gamma β * b ^ (-β) * q * D₀ ^ (-(q * η)) *
      (volume (facePolytope κ Q δ γ)).toReal / |(transMat κ Q).det| *
      ∫ u in Ioo (0 : ℝ) ρ, u ^ (q * η - 1) * (Wtr u * atr u ^ (-β)) := ⟨_, rfl⟩
  have hlim : ∀ b, 0 < b → Tendsto (fun t ↦ N (τ t) * modelKernel ρ 1 b D₀ γ p q δ Q κ r W a (τ t))
      atTop (𝓝 (L b)) := fun b hb ↦ by
    rw [hLdef, hN, hlam]
    exact (tendsto_modelKernel_general (A := 1) hρ hD₀ hq hb hβ hη hδ hκ hΔ hc₀ hc₁ hr hamin hWm
      ham hWb hab hWtrm hatrm hWtrb hatrb hWtr hatr).comp hτ
  have hL : ContinuousAt L B₀ := by
    rw [hLdef]
    have h1 : ContinuousAt (fun b : ℝ ↦ b ^ (-β)) B₀ := continuousAt_id.rpow_const (Or.inl hB₀.ne')
    exact (((((continuousAt_const.mul h1).mul continuousAt_const).mul continuousAt_const).mul
      continuousAt_const).div_const _).mul continuousAt_const
  have hτe : ∀ᶠ t in atTop, exp 1 ≤ τ t := hτ.eventually (eventually_ge_atTop _)
  have hNτ : ∀ᶠ t in atTop, 0 ≤ N (τ t) := by
    filter_upwards [hτe] with t ht
    rw [hN]
    exact div_nonneg (Real.rpow_pos_of_pos (zero_lt_one.trans (one_lt_of_exp_one_le ht)) _).le
      (pow_pos (Real.log_pos (one_lt_of_exp_one_le ht)) _).le
  have hanti : ∀ᶠ t in atTop, ∀ b b', 0 < b → b ≤ b' →
      modelKernel ρ 1 b' D₀ γ p q δ Q κ r W a (τ t) ≤
        modelKernel ρ 1 b D₀ γ p q δ Q κ r W a (τ t) := by
    filter_upwards [hτe] with t ht
    intro b b' hb hbb'
    exact modelKernel_anti_B_general hρ hD₀ hq hβ hη hδ hκ hΔ hr hamin hWm ham hWb hab hb hbb' ht
  have key := tendsto_of_antitone_param
    (f := fun b t ↦ modelKernel ρ 1 b D₀ γ p q δ Q κ r W a (τ t)) (N := fun t ↦ N (τ t))
    hB₀ hB' hNτ hanti hlim hL
  have hrat := tendsto_normaliser_ratio hc lam k
  have hfin := hrat.mul (hA'.mul key)
  have e : 1 * (A₀ * L B₀) = A₀ * Gamma β * B₀ ^ (-β) * q * D₀ ^ (-(q * η)) *
      (volume (facePolytope κ Q δ γ)).toReal / |(transMat κ Q).det| *
      ∫ u in Ioo (0 : ℝ) ρ, u ^ (q * η - 1) * (Wtr u * atr u ^ (-β)) := by
    rw [hLdef]
    ring
  rw [e] at hfin
  refine hfin.congr' ?_
  filter_upwards [eventually_gt_atTop 1, hDpos, hτe] with t ht hDt hτt
  have ht0 : 0 < t := zero_lt_one.trans ht
  have hτ1 : 1 < τ t := one_lt_of_exp_one_le hτt
  have hNτ0 : N (τ t) ≠ 0 := by
    rw [hN]
    exact (div_pos (Real.rpow_pos_of_pos (zero_lt_one.trans hτ1) _)
      (pow_pos (Real.log_pos hτ1) _)).ne'
  have hker : modelKernel ρ (A t) (B t) (D t) γ p q δ Q κ r W a t =
      A' t * modelKernel ρ 1 (B' t) D₀ γ p q δ Q κ r W a (τ t) := by
    rw [modelKernel_cutTime hDt hD₀ hγ hq ht0, modelKernel_eq_A_mul, hA'def, hB'def, hτdef, hcdef]
    rfl
  have hτt' : τ t = t * c t := by rw [hτdef]
  rw [hker, ← hlam]
  simp only [hN]
  rw [hτt']
  have hc0 : 0 < t * c t := by
    rw [← hτt']
    exact zero_lt_one.trans hτ1
  have h1 : (t * c t) ^ lam ≠ 0 := (Real.rpow_pos_of_pos hc0 _).ne'
  have h2 : log (t * c t) ≠ 0 := (Real.log_pos (by rw [← hτt']; exact hτ1)).ne'
  have h3 : log t ≠ 0 := (Real.log_pos ht).ne'
  field_simp

end Laplace.Multi
