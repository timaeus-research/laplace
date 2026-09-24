/-
Copyright (c) 2026 Timaeus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Timaeus
-/
import Laplace.Multi.PartialTiedModel

/-!
# Parameter stability of the partially tied model kernel

The constant-unit model kernel with `Q = 0` is a decreasing function of the scale `B`
(`modelKernel_const_anti`), independent of the cutoff constant `D` once the cutoff is inside the
box (`modelKernel_const_of_cut`), and linear in the prefactor `A`. A limit theorem for fixed
constants therefore transfers to moving constants `A t → A₀`, `B t → B₀ > 0`,
`D t · t^{-γ/q} → 0` by a squeeze between the fixed kernels at `B₀ ± η` and continuity of the
limit in `B` (`tendsto_of_antitone_param`): the partially tied theorem
`tendsto_modelKernel_partial` becomes `tendsto_modelKernel_partial_param` with no new analysis
(Astra, round 5, target 1: parameter stability of the partial-face coefficient).
-/

open Real MeasureTheory Set Filter Topology

namespace Laplace.Multi

/-! ### The abstract squeeze -/

/-- A family `f b t`, antitone in the parameter `b`, whose normalised limits `L b` exist for every
fixed `b > 0` and are continuous at `B₀`, converges along any `B t → B₀ > 0`. -/
theorem tendsto_of_antitone_param {f : ℝ → ℝ → ℝ} {N L B : ℝ → ℝ} {B₀ : ℝ} (hB₀ : 0 < B₀)
    (hB : Tendsto B atTop (𝓝 B₀)) (hN : ∀ᶠ t in atTop, 0 ≤ N t)
    (hanti : ∀ᶠ t in atTop, ∀ b b', 0 < b → b ≤ b' → f b' t ≤ f b t)
    (hlim : ∀ b, 0 < b → Tendsto (fun t ↦ N t * f b t) atTop (𝓝 (L b)))
    (hL : ContinuousAt L B₀) :
    Tendsto (fun t ↦ N t * f (B t) t) atTop (𝓝 (L B₀)) := by
  rw [Metric.tendsto_nhds]
  intro ε hε
  obtain ⟨η, hη, hLη⟩ := Metric.continuousAt_iff.mp hL (ε / 2) (by positivity)
  obtain ⟨d, hd⟩ : ∃ d : ℝ, d = min (η / 2) (B₀ / 2) := ⟨_, rfl⟩
  have hd0 : 0 < d := by rw [hd]; exact lt_min (by positivity) (by positivity)
  have hdη : d < η := by rw [hd]; exact (min_le_left _ _).trans_lt (by linarith)
  have hdB : d < B₀ := by rw [hd]; exact (min_le_right _ _).trans_lt (by linarith)
  have hlo : 0 < B₀ - d := by linarith
  have hhi : 0 < B₀ + d := by linarith
  have hLlo : dist (L (B₀ - d)) (L B₀) < ε / 2 := by
    refine hLη ?_
    rw [Real.dist_eq, show B₀ - d - B₀ = -d by ring, abs_neg, abs_of_pos hd0]
    exact hdη
  have hLhi : dist (L (B₀ + d)) (L B₀) < ε / 2 := by
    refine hLη ?_
    rw [Real.dist_eq, show B₀ + d - B₀ = d by ring, abs_of_pos hd0]
    exact hdη
  have h1 := (hlim _ hlo).eventually (Metric.ball_mem_nhds _ (half_pos hε))
  have h2 := (hlim _ hhi).eventually (Metric.ball_mem_nhds _ (half_pos hε))
  have hBlo : ∀ᶠ t in atTop, B₀ - d < B t := hB.eventually_const_lt (by linarith)
  have hBhi : ∀ᶠ t in atTop, B t < B₀ + d := hB.eventually_lt_const (by linarith)
  filter_upwards [h1, h2, hBlo, hBhi, hN, hanti] with t h1 h2 hlo' hhi' hNt hanti
  rw [Real.dist_eq] at h1 h2
  rw [Real.dist_eq] at hLlo hLhi
  have hup : N t * f (B t) t ≤ N t * f (B₀ - d) t :=
    mul_le_mul_of_nonneg_left (hanti _ _ hlo hlo'.le) hNt
  have hdown : N t * f (B₀ + d) t ≤ N t * f (B t) t :=
    mul_le_mul_of_nonneg_left (hanti _ _ (by linarith) hhi'.le) hNt
  rw [Real.dist_eq, abs_lt]
  constructor
  · linarith [(abs_lt.mp h2).1, (abs_lt.mp hLhi).1]
  · linarith [(abs_lt.mp h1).2, (abs_lt.mp hLlo).2]

/-! ### The constant-unit model kernel in its constants -/

variable {ι : Type*} [Fintype ι]

theorem modelKernel_eq_A_mul {ρ A B D γ p q δ : ℝ} {Q κ r : ι → ℝ} {W a : (ι → ℝ) → ℝ → ℝ}
    (t : ℝ) :
    modelKernel ρ A B D γ p q δ Q κ r W a t = A * modelKernel ρ 1 B D γ p q δ Q κ r W a t := by
  unfold modelKernel
  ring

/-- With `Q = 0` and constant unit and weight, the integrand does not see the cutoff constant once
the cutoff is inside the box. -/
theorem modelIntegrand_const_of_cut {ρ B D D' γ q δ : ℝ} {κ r : ι → ℝ} {w₀ a₀ t : ℝ}
    (hcut : D * t ^ (-(γ / q)) < ρ) (hcut' : D' * t ^ (-(γ / q)) < ρ) :
    modelIntegrand ρ B D γ q δ (0 : ι → ℝ) κ r (fun _ _ ↦ w₀) (fun _ _ ↦ a₀) t =
      modelIntegrand ρ B D' γ q δ (0 : ι → ℝ) κ r (fun _ _ ↦ w₀) (fun _ _ ↦ a₀) t := by
  unfold modelIntegrand
  rw [modelDomain_eq_of_Q_zero' hcut, modelDomain_eq_of_Q_zero' hcut']

theorem modelKernel_const_of_cut {ρ A B D D' γ p q δ : ℝ} {κ r : ι → ℝ} {w₀ a₀ t : ℝ}
    (hcut : D * t ^ (-(γ / q)) < ρ) (hcut' : D' * t ^ (-(γ / q)) < ρ) :
    modelKernel ρ A B D γ p q δ (0 : ι → ℝ) κ r (fun _ _ ↦ w₀) (fun _ _ ↦ a₀) t =
      modelKernel ρ A B D' γ p q δ (0 : ι → ℝ) κ r (fun _ _ ↦ w₀) (fun _ _ ↦ a₀) t := by
  unfold modelKernel
  rw [modelIntegrand_const_of_cut hcut hcut']

/-- The constant-unit integrand is antitone in the scale `B`. -/
theorem modelIntegrand_const_anti {ρ B B' D γ q δ : ℝ} {κ r : ι → ℝ} {w₀ a₀ t : ℝ}
    (hBB' : B ≤ B') (ht : 0 < t) (ha₀ : 0 ≤ a₀) (hw₀ : 0 ≤ w₀) (x : ι → ℝ) :
    modelIntegrand ρ B' D γ q δ (0 : ι → ℝ) κ r (fun _ _ ↦ w₀) (fun _ _ ↦ a₀) t x ≤
      modelIntegrand ρ B D γ q δ (0 : ι → ℝ) κ r (fun _ _ ↦ w₀) (fun _ _ ↦ a₀) t x := by
  unfold modelIntegrand
  by_cases hx : x ∈ modelDomain ρ D γ q (0 : ι → ℝ) t
  · rw [Set.indicator_of_mem hx, Set.indicator_of_mem hx]
    have hxj : ∀ j, 0 < x j := fun j ↦ (Set.mem_univ_pi.mp hx.1 j).1
    have hr0 : 0 ≤ ∏ j, x j ^ r j := Finset.prod_nonneg fun j _ ↦ rpow_nonneg (hxj j).le _
    have hκ0 : 0 ≤ ∏ j, x j ^ κ j := Finset.prod_nonneg fun j _ ↦ rpow_nonneg (hxj j).le _
    refine mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr ?_) (mul_nonneg hw₀ hr0)
    have h0 : 0 ≤ t ^ δ * a₀ * ∏ j, x j ^ κ j :=
      mul_nonneg (mul_nonneg (rpow_pos_of_pos ht _).le ha₀) hκ0
    have : B * t ^ δ * a₀ * ∏ j, x j ^ κ j ≤ B' * t ^ δ * a₀ * ∏ j, x j ^ κ j := by
      calc B * t ^ δ * a₀ * ∏ j, x j ^ κ j = B * (t ^ δ * a₀ * ∏ j, x j ^ κ j) := by ring
        _ ≤ B' * (t ^ δ * a₀ * ∏ j, x j ^ κ j) := mul_le_mul_of_nonneg_right hBB' h0
        _ = B' * t ^ δ * a₀ * ∏ j, x j ^ κ j := by ring
    linarith
  · rw [Set.indicator_of_notMem hx, Set.indicator_of_notMem hx]

/-- Integrability of the constant-unit integrand with `Q = 0` past the cutoff. -/
theorem integrable_modelIntegrand_const {ρ B D γ q δ : ℝ} {κ r : ι → ℝ} {w₀ a₀ t : ℝ}
    (hρ : 0 < ρ) (hr : ∀ i, -1 < r i) (hcut : D * t ^ (-(γ / q)) < ρ) (hB : 0 ≤ B) (ht : 0 < t)
    (ha₀ : 0 ≤ a₀) :
    Integrable (modelIntegrand ρ B D γ q δ (0 : ι → ℝ) κ r (fun _ _ ↦ w₀) (fun _ _ ↦ a₀) t) := by
  refine Integrable.mono' ((integrable_box_prod_rpow' hρ hr).const_mul |w₀|)
    (measurable_modelIntegrand measurable_const measurable_const t).aestronglyMeasurable
    (Eventually.of_forall fun x ↦ ?_)
  unfold modelIntegrand
  rw [modelDomain_eq_of_Q_zero' hcut]
  by_cases hx : x ∈ Set.pi univ fun _ : ι ↦ Ioo (0 : ℝ) ρ
  · rw [Set.indicator_of_mem hx, Set.indicator_of_mem hx]
    beta_reduce
    have hxj : ∀ j, 0 < x j := fun j ↦ (Set.mem_univ_pi.mp hx j).1
    have hr0 : 0 ≤ ∏ j, x j ^ r j := Finset.prod_nonneg fun j _ ↦ rpow_nonneg (hxj j).le _
    have hκ0 : 0 ≤ ∏ j, x j ^ κ j := Finset.prod_nonneg fun j _ ↦ rpow_nonneg (hxj j).le _
    rw [Real.norm_eq_abs, abs_mul, abs_mul, abs_of_nonneg hr0, abs_of_pos (exp_pos _)]
    have hexp : exp (-(B * t ^ δ * a₀ * ∏ j, x j ^ κ j)) ≤ 1 := by
      rw [Real.exp_le_one_iff]
      have : 0 ≤ B * t ^ δ * a₀ * ∏ j, x j ^ κ j :=
        mul_nonneg (mul_nonneg (mul_nonneg hB (rpow_pos_of_pos ht _).le) ha₀) hκ0
      linarith
    calc |w₀| * (∏ j, x j ^ r j) * exp (-(B * t ^ δ * a₀ * ∏ j, x j ^ κ j))
        ≤ |w₀| * (∏ j, x j ^ r j) * 1 :=
          mul_le_mul_of_nonneg_left hexp (mul_nonneg (abs_nonneg _) hr0)
      _ = |w₀| * ∏ j, x j ^ r j := by ring
  · rw [Set.indicator_of_notMem hx, Set.indicator_of_notMem hx, norm_zero, mul_zero]

/-- The constant-unit model kernel with prefactor `1` is antitone in the scale `B`. -/
theorem modelKernel_const_anti {ρ B B' D γ p q δ : ℝ} {κ r : ι → ℝ} {w₀ a₀ t : ℝ} (hρ : 0 < ρ)
    (hr : ∀ i, -1 < r i) (hcut : D * t ^ (-(γ / q)) < ρ) (hB : 0 < B) (hBB' : B ≤ B') (ht : 0 < t)
    (ha₀ : 0 ≤ a₀) (hw₀ : 0 ≤ w₀) :
    modelKernel ρ 1 B' D γ p q δ (0 : ι → ℝ) κ r (fun _ _ ↦ w₀) (fun _ _ ↦ a₀) t ≤
      modelKernel ρ 1 B D γ p q δ (0 : ι → ℝ) κ r (fun _ _ ↦ w₀) (fun _ _ ↦ a₀) t := by
  unfold modelKernel
  refine mul_le_mul_of_nonneg_left ?_ (mul_nonneg zero_le_one (rpow_pos_of_pos ht _).le)
  exact integral_mono (integrable_modelIntegrand_const hρ hr hcut (hB.le.trans hBB') ht ha₀)
    (integrable_modelIntegrand_const hρ hr hcut hB.le ht ha₀)
    (modelIntegrand_const_anti hBB' ht ha₀ hw₀)

/-! ### The partially tied theorem along moving constants -/

variable {k : ℕ} {ν : Type*} [Fintype ν]

/-- **The partially tied power–log law with moving constants** `A t → A₀`, `B t → B₀ > 0`,
`D t · t^{-γ/q} → 0`. -/
theorem tendsto_modelKernel_partial_param {ρ γ p q δ : ℝ} {κ r : Fin (k + 1) ⊕ ν → ℝ}
    {w₀ a₀ : ℝ} {A B D : ℝ → ℝ} {A₀ B₀ : ℝ} (hρ : 0 < ρ) (hκ : ∀ i, 0 < κ i) {lam : ℝ}
    (hlam : 0 < lam) (htied : ∀ i, (r (Sum.inl i) + 1) / κ (Sum.inl i) = lam)
    (hgap : ∀ j, lam * κ (Sum.inr j) < r (Sum.inr j) + 1) (hA : Tendsto A atTop (𝓝 A₀))
    (hB : Tendsto B atTop (𝓝 B₀)) (hB₀ : 0 < B₀) (ha₀ : 0 < a₀) (hw₀ : 0 ≤ w₀) (hδ : 0 < δ)
    (hDcut : Tendsto (fun t ↦ D t * t ^ (-(γ / q))) atTop (𝓝 0)) (hγq : 0 < γ / q) :
    Tendsto (fun t ↦ t ^ (γ * p + δ * lam) / log t ^ k *
        modelKernel ρ (A t) (B t) (D t) γ p q δ (0 : Fin (k + 1) ⊕ ν → ℝ) κ r (fun _ _ ↦ w₀)
          (fun _ _ ↦ a₀) t)
      atTop
      (𝓝 (A₀ * w₀ * ((B₀ * a₀) ^ (-lam) * δ ^ k *
        (Gamma lam / k.factorial * ∏ i, 1 / κ (Sum.inl i)) *
        ∫ z in Set.pi univ (fun _ : ν ↦ Ioo (0 : ℝ) ρ),
          ∏ j, z j ^ (r (Sum.inr j) - lam * κ (Sum.inr j))))) := by
  have hr : ∀ i, -1 < r i := by
    rintro (i | j)
    · have h := htied i
      rw [div_eq_iff (hκ (Sum.inl i)).ne'] at h
      nlinarith [mul_pos hlam (hκ (Sum.inl i))]
    · have := hgap j
      nlinarith [mul_pos hlam (hκ (Sum.inr j))]
  -- the fixed-constant limits, as a function of the scale
  obtain ⟨L, hLdef⟩ : ∃ L : ℝ → ℝ, L = fun b ↦ 1 * w₀ * ((b * a₀) ^ (-lam) * δ ^ k *
      (Gamma lam / k.factorial * ∏ i, 1 / κ (Sum.inl i)) *
      ∫ z in Set.pi univ (fun _ : ν ↦ Ioo (0 : ℝ) ρ),
        ∏ j, z j ^ (r (Sum.inr j) - lam * κ (Sum.inr j))) := ⟨_, rfl⟩
  have hlim : ∀ b, 0 < b → Tendsto (fun t ↦ t ^ (γ * p + δ * lam) / log t ^ k *
      modelKernel ρ 1 b 1 γ p q δ (0 : Fin (k + 1) ⊕ ν → ℝ) κ r (fun _ _ ↦ w₀) (fun _ _ ↦ a₀) t)
      atTop (𝓝 (L b)) := fun b hb ↦ by
    rw [hLdef]
    exact tendsto_modelKernel_partial (A := 1) (D := 1) hρ hκ hlam htied hgap hb ha₀ hδ hγq
  have hL : ContinuousAt L B₀ := by
    rw [hLdef]
    have h1 : ContinuousAt (fun b : ℝ ↦ (b * a₀) ^ (-lam)) B₀ :=
      (continuousAt_id.mul continuousAt_const).rpow_const (Or.inl (mul_pos hB₀ ha₀).ne')
    exact continuousAt_const.mul (((h1.mul continuousAt_const).mul continuousAt_const).mul
      continuousAt_const)
  have hcut1 : ∀ᶠ t : ℝ in atTop, (1 : ℝ) * t ^ (-(γ / q)) < ρ := by
    have : Tendsto (fun t : ℝ ↦ (1 : ℝ) * t ^ (-(γ / q))) atTop (𝓝 0) := by
      simpa using (tendsto_rpow_neg_atTop hγq).const_mul (1 : ℝ)
    exact this.eventually_lt_const hρ
  have hcutD : ∀ᶠ t : ℝ in atTop, D t * t ^ (-(γ / q)) < ρ := hDcut.eventually_lt_const hρ
  have hN : ∀ᶠ t : ℝ in atTop, 0 ≤ t ^ (γ * p + δ * lam) / log t ^ k := by
    filter_upwards [eventually_gt_atTop 1] with t ht
    exact div_nonneg (rpow_pos_of_pos (one_pos.trans ht) _).le
      (pow_pos (Real.log_pos ht) _).le
  have hanti : ∀ᶠ t : ℝ in atTop, ∀ b b', 0 < b → b ≤ b' →
      modelKernel ρ 1 b' 1 γ p q δ (0 : Fin (k + 1) ⊕ ν → ℝ) κ r (fun _ _ ↦ w₀) (fun _ _ ↦ a₀) t ≤
      modelKernel ρ 1 b 1 γ p q δ (0 : Fin (k + 1) ⊕ ν → ℝ) κ r (fun _ _ ↦ w₀)
        (fun _ _ ↦ a₀) t := by
    filter_upwards [eventually_gt_atTop 0, hcut1] with t ht hcut
    intro b b' hb hbb'
    exact modelKernel_const_anti hρ hr hcut hb hbb' ht ha₀.le hw₀
  have key := tendsto_of_antitone_param hB₀ hB hN hanti hlim hL
  have hfin := hA.mul key
  have e : A₀ * L B₀ = A₀ * w₀ * ((B₀ * a₀) ^ (-lam) * δ ^ k *
      (Gamma lam / k.factorial * ∏ i, 1 / κ (Sum.inl i)) *
      ∫ z in Set.pi univ (fun _ : ν ↦ Ioo (0 : ℝ) ρ),
        ∏ j, z j ^ (r (Sum.inr j) - lam * κ (Sum.inr j))) := by
    rw [hLdef]
    ring
  rw [e] at hfin
  refine hfin.congr' ?_
  filter_upwards [hcut1, hcutD] with t hcut1 hcutD
  rw [modelKernel_const_of_cut hcutD hcut1, modelKernel_eq_A_mul (A := A t) (B := B t) (D := 1)]
  ring

end Laplace.Multi
