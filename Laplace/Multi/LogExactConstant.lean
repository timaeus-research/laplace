/-
Copyright (c) 2026 Timaeus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Timaeus
-/
import Laplace.Multi.LogSandwich

/-!
# The exact constant of a fully tied logarithmic face

`LogSandwich` squeezes a fully tied model kernel (`Q = 0`) with moving unit and weight between two
constant-unit kernels, whose constants `tiedConst A B δ κ r λ R a w` depend on the unit `a`, the
weight `w` and the box radius `R`. The key observation is that the box radius cancels on a tied
face: `R^{∑(r_i+1)} (B a R^{∑κ_i})^{-λ} = (B a)^{-λ}` because `r_i + 1 = λ κ_i`
(`tiedConst_eq`). Hence the kernel over a big box and the kernel over a small box have the *same*
power–log constant, the difference (the part of the integral away from the face point) is
negligible at the `(λ, k)` normalisation, and the exact constant is read off at the face point:
for `W`, `a` continuous at `(0, 0)` (the face point and the vanishing cut variable),

`t^{γp + δλ} / (log t)^k · K(t) → A W(0,0) (B a(0,0))^{-λ} δ^k Γ(λ)/k! ∏ 1/κ_i`

(`tendsto_modelKernel_tied`). No Fubini and no induction on the dimension is needed: the upper
bound is the small-box constant kernel at `(a₀ − η, w₀ + η)` plus the difference of two big/small
constant kernels at the global bounds, the lower bound the small-box constant kernel at
`(a₀ + η, max 0 (w₀ − η))`.
-/

open Real MeasureTheory Set Filter Topology

namespace Laplace.Multi

variable {k : ℕ}

/-- On a tied face the box radius cancels from the power–log constant. -/
theorem tiedConst_eq {A B δ : ℝ} {κ r : Fin (k + 1) → ℝ} {lam R a w : ℝ} (hR : 0 < R)
    (hBa : 0 < B * a) (hκ : ∀ i, 0 < κ i) (htied : ∀ i, (r i + 1) / κ i = lam) :
    tiedConst A B δ κ r lam R a w =
      A * w * (B * a) ^ (-lam) * δ ^ k * (Gamma lam / k.factorial * ∏ i, 1 / κ i) := by
  unfold tiedConst
  have hsum : ∑ i, (r i + 1) = lam * ∑ i, κ i := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ ↦ ?_
    have h := htied i
    rw [div_eq_iff (hκ i).ne'] at h
    exact h
  have e : R ^ (∑ i, (r i + 1)) * (B * a * R ^ (∑ i, κ i)) ^ (-lam) = (B * a) ^ (-lam) := by
    rw [Real.mul_rpow hBa.le (rpow_nonneg hR.le _), ← Real.rpow_mul hR.le, hsum]
    have h1 : R ^ (lam * ∑ i, κ i) * R ^ ((∑ i, κ i) * -lam) = 1 := by
      rw [← Real.rpow_add hR]
      have : lam * ∑ i, κ i + (∑ i, κ i) * -lam = 0 := by ring
      rw [this, Real.rpow_zero]
    calc R ^ (lam * ∑ i, κ i) * ((B * a) ^ (-lam) * R ^ ((∑ i, κ i) * -lam))
        = (B * a) ^ (-lam) * (R ^ (lam * ∑ i, κ i) * R ^ ((∑ i, κ i) * -lam)) := by ring
      _ = (B * a) ^ (-lam) := by rw [h1, mul_one]
  calc A * w * R ^ (∑ i, (r i + 1)) * (B * a * R ^ (∑ i, κ i)) ^ (-lam) * δ ^ k *
        (Gamma lam / k.factorial * ∏ i, 1 / κ i)
      = A * w * (R ^ (∑ i, (r i + 1)) * (B * a * R ^ (∑ i, κ i)) ^ (-lam)) * δ ^ k *
        (Gamma lam / k.factorial * ∏ i, 1 / κ i) := by ring
    _ = _ := by rw [e]

variable {ρ A B D γ p q δ : ℝ} {κ r : Fin (k + 1) → ℝ} {W a : (Fin (k + 1) → ℝ) → ℝ → ℝ}

/-- The model integrand with `Q = 0` only sees the unit and the weight at the cut value
`v₀ = D t^{-γ/q}`. -/
theorem modelIntegrand_Q_zero_freeze (t : ℝ) :
    modelIntegrand ρ B D γ q δ (0 : Fin (k + 1) → ℝ) κ r W a t =
      modelIntegrand ρ B D γ q δ (0 : Fin (k + 1) → ℝ) κ r
        (fun x _ ↦ W x (D * t ^ (-(γ / q)))) (fun x _ ↦ a x (D * t ^ (-(γ / q)))) t := by
  funext x
  unfold modelIntegrand
  simp only [cutVar_Q_zero]

/-- **The exact power–log constant of a fully tied model kernel** with moving unit and weight,
continuous at the face point. -/
theorem tendsto_modelKernel_tied (hρ : 0 < ρ) (hA : 0 ≤ A) (hD : 0 ≤ D) (hκ : ∀ i, 0 < κ i)
    {lam : ℝ} (hlam : 0 < lam) (htied : ∀ i, (r i + 1) / κ i = lam) (hB : 0 < B) (hδ : 0 < δ)
    (hγq : 0 < γ / q) {aL wU : ℝ} (haL : 0 < aL) (hW : Measurable (Function.uncurry W))
    (ha : Measurable (Function.uncurry a)) (hW0 : ∀ x v, 0 ≤ W x v) (hWup : ∀ x v, W x v ≤ wU)
    (halow : ∀ x v, (∀ j, x j ∈ Ioo (0 : ℝ) ρ) → 0 ≤ v → v < ρ → aL ≤ a x v)
    {w₀ a₀ : ℝ} (ha₀ : 0 < a₀) (hw₀ : 0 ≤ w₀)
    (hWlim : Tendsto (Function.uncurry W) (𝓝 (0, 0)) (𝓝 w₀))
    (halim : Tendsto (Function.uncurry a) (𝓝 (0, 0)) (𝓝 a₀)) :
    Tendsto (fun t ↦ t ^ (γ * p + δ * lam) / log t ^ k *
        modelKernel ρ A B D γ p q δ (0 : Fin (k + 1) → ℝ) κ r W a t) atTop
      (𝓝 (tiedConst A B δ κ r lam ρ a₀ w₀)) := by
  have hr : ∀ i, -1 < r i := fun i ↦ by
    have h := htied i
    have hk := hκ i
    rw [div_eq_iff hk.ne'] at h
    nlinarith [mul_pos hlam hk]
  have hwU : 0 ≤ wU := (hW0 0 0).trans (hWup 0 0)
  -- the exact constant as a function of the unit and the weight
  set Cf : ℝ → ℝ → ℝ := fun a w ↦
    A * w * (B * a) ^ (-lam) * δ ^ k * (Gamma lam / k.factorial * ∏ i, 1 / κ i) with hCf
  have hC : ∀ {R a' w'}, 0 < R → 0 < a' → tiedConst A B δ κ r lam R a' w' = Cf a' w' :=
    fun hR ha' ↦ tiedConst_eq hR (mul_pos hB ha') hκ htied
  have hcont : ContinuousAt (fun z : ℝ × ℝ ↦ Cf z.1 z.2) (a₀, w₀) := by
    rw [hCf]
    refine ((((continuousAt_const.mul continuousAt_snd).mul ?_).mul continuousAt_const).mul
      continuousAt_const)
    exact (continuousAt_const.mul continuousAt_fst).rpow_const (Or.inl (mul_pos hB ha₀).ne')
  clear_value Cf
  rw [hC hρ ha₀, Metric.tendsto_nhds]
  intro ε hε
  obtain ⟨ε', hε'pos, hε'⟩ := Metric.continuousAt_iff.mp hcont (ε / 3) (by positivity)
  obtain ⟨η, hη⟩ : ∃ η : ℝ, η = min (ε' / 2) (a₀ / 2) := ⟨_, rfl⟩
  have hηpos : 0 < η := by rw [hη]; exact lt_min (by positivity) (by positivity)
  have hηa : η < a₀ := by rw [hη]; exact (min_le_right _ _).trans_lt (by linarith)
  have hηε : η < ε' := by rw [hη]; exact (min_le_left _ _).trans_lt (by linarith)
  -- the neighbourhoods of the face point
  obtain ⟨δW, hδW, hWnear⟩ := Metric.tendsto_nhds_nhds.mp hWlim η hηpos
  obtain ⟨δa, hδa, hanear⟩ := Metric.tendsto_nhds_nhds.mp halim η hηpos
  obtain ⟨ρ', hρ'def⟩ : ∃ ρ' : ℝ, ρ' = min ρ (min δW δa / 2) := ⟨_, rfl⟩
  have hmin : 0 < min δW δa := lt_min hδW hδa
  have hρ' : 0 < ρ' := by rw [hρ'def]; exact lt_min hρ (by positivity)
  have hρ'ρ : ρ' ≤ ρ := by rw [hρ'def]; exact min_le_left _ _
  have hρ'm : ρ' < min δW δa := by rw [hρ'def]; exact (min_le_right _ _).trans_lt (by linarith)
  have hnear : ∀ x : Fin (k + 1) → ℝ, ∀ v : ℝ, (∀ j, x j ∈ Ioo (0 : ℝ) ρ') → 0 ≤ v → v < ρ' →
      |W x v - w₀| < η ∧ |a x v - a₀| < η := by
    intro x v hx hv0 hv
    have hdist : dist (x, v) ((0 : Fin (k + 1) → ℝ), (0 : ℝ)) < min δW δa := by
      rw [Prod.dist_eq, dist_zero_right, dist_zero_right, Real.norm_eq_abs, abs_of_nonneg hv0]
      refine max_lt ?_ (hv.trans hρ'm)
      rw [pi_norm_lt_iff hmin]
      intro j
      rw [Real.norm_eq_abs, abs_of_pos (hx j).1]
      exact (hx j).2.trans hρ'm
    constructor
    · have := hWnear (hdist.trans_le (min_le_left _ _))
      rwa [Function.uncurry_apply_pair, Real.dist_eq] at this
    · have := hanear (hdist.trans_le (min_le_right _ _))
      rwa [Function.uncurry_apply_pair, Real.dist_eq] at this
  -- the four constants
  obtain ⟨aL', haL'⟩ : ∃ x : ℝ, x = a₀ - η := ⟨_, rfl⟩
  obtain ⟨aU', haU'⟩ : ∃ x : ℝ, x = a₀ + η := ⟨_, rfl⟩
  obtain ⟨wL', hwL'⟩ : ∃ x : ℝ, x = max 0 (w₀ - η) := ⟨_, rfl⟩
  obtain ⟨wU', hwU'⟩ : ∃ x : ℝ, x = w₀ + η := ⟨_, rfl⟩
  have haL'pos : 0 < aL' := by rw [haL']; linarith
  have haU'pos : 0 < aU' := by rw [haU']; linarith
  have hwL'0 : 0 ≤ wL' := by rw [hwL']; exact le_max_left _ _
  have hwU'0 : 0 ≤ wU' := by rw [hwU']; linarith
  have hwL'le : ∀ y, 0 ≤ y → w₀ - η < y → wL' ≤ y := fun y h0 h1 ↦ by
    rw [hwL']; exact max_le h0 h1.le
  have hCU : dist (Cf aL' wU') (Cf a₀ w₀) < ε / 3 := by
    refine hε' (x := (aL', wU')) ?_
    rw [Prod.dist_eq, Real.dist_eq, Real.dist_eq, haL', hwU']
    refine max_lt ?_ ?_ <;> [rw [show a₀ - η - a₀ = -η by ring, abs_neg];
      rw [show w₀ + η - w₀ = η by ring]] <;> rwa [abs_of_pos hηpos]
  have hCL : dist (Cf aU' wL') (Cf a₀ w₀) < ε / 3 := by
    refine hε' (x := (aU', wL')) ?_
    rw [Prod.dist_eq, Real.dist_eq, Real.dist_eq, haU', hwL']
    refine max_lt ?_ ?_
    · rw [show a₀ + η - a₀ = η by ring, abs_of_pos hηpos]; exact hηε
    · rw [abs_lt]
      constructor
      · have : w₀ - η ≤ max 0 (w₀ - η) := le_max_right _ _
        linarith
      · rcases le_or_gt 0 (w₀ - η) with h | h
        · rw [max_eq_right h]; linarith
        · rw [max_eq_left h.le]; linarith
  -- the limits of the constant kernels
  have hU1 := tendsto_tiedConst (A := A) (D := D) (p := p) (w₀ := wU') (a₀ := aL') hρ' hκ hlam
    htied hB haL'pos hδ hγq
  have hU2 := tendsto_tiedConst (A := A) (D := D) (p := p) (w₀ := wU) (a₀ := aL) hρ hκ hlam htied
    hB haL hδ hγq
  have hU3 := tendsto_tiedConst (A := A) (D := D) (p := p) (w₀ := wU) (a₀ := aL) hρ' hκ hlam htied
    hB haL hδ hγq
  have hL := tendsto_tiedConst (A := A) (D := D) (p := p) (w₀ := wL') (a₀ := aU') hρ' hκ hlam
    htied hB haU'pos hδ hγq
  rw [hC hρ' haL'pos] at hU1
  rw [hC hρ haL] at hU2
  rw [hC hρ' haL] at hU3
  rw [hC hρ' haU'pos] at hL
  have hUp : Tendsto (fun t ↦ t ^ (γ * p + δ * lam) / log t ^ k *
      (modelKernel ρ' A B D γ p q δ (0 : Fin (k + 1) → ℝ) κ r (fun _ _ ↦ wU') (fun _ _ ↦ aL') t +
        (modelKernel ρ A B D γ p q δ (0 : Fin (k + 1) → ℝ) κ r (fun _ _ ↦ wU) (fun _ _ ↦ aL) t -
          modelKernel ρ' A B D γ p q δ (0 : Fin (k + 1) → ℝ) κ r (fun _ _ ↦ wU) (fun _ _ ↦ aL) t)))
      atTop (𝓝 (Cf aL' wU')) := by
    have := (hU1.add (hU2.sub hU3))
    rw [show Cf aL' wU' + (Cf aL wU - Cf aL wU) = Cf aL' wU' by ring] at this
    refine this.congr fun t ↦ ?_
    ring
  have hcut : ∀ᶠ t : ℝ in atTop, D * t ^ (-(γ / q)) < ρ' := by
    have : Tendsto (fun t : ℝ ↦ D * t ^ (-(γ / q))) atTop (𝓝 0) := by
      simpa using (tendsto_rpow_neg_atTop hγq).const_mul D
    exact this.eventually_lt_const hρ'
  filter_upwards [hUp.eventually (Metric.ball_mem_nhds _ (show (0 : ℝ) < ε / 3 by positivity)),
    hL.eventually (Metric.ball_mem_nhds _ (show (0 : ℝ) < ε / 3 by positivity)), hcut,
    eventually_gt_atTop 1] with t hu hl hcut ht
  have ht0 : 0 < t := one_pos.trans ht
  have hcutρ : D * t ^ (-(γ / q)) < ρ := hcut.trans_le hρ'ρ
  have hv0 : 0 ≤ D * t ^ (-(γ / q)) := mul_nonneg hD (rpow_pos_of_pos ht0 _).le
  have hnorm : 0 ≤ t ^ (γ * p + δ * lam) / log t ^ k :=
    div_nonneg (rpow_pos_of_pos ht0 _).le (pow_pos (Real.log_pos ht) _).le
  have hAt : 0 ≤ A * t ^ (-(γ * p)) := mul_nonneg hA (rpow_pos_of_pos ht0 _).le
  -- integrability of the four integrands
  have hI1 := integrable_modelIntegrand_tied (D := D) (γ := γ) (q := q) (δ := δ) (κ := κ)
    (W := fun _ _ ↦ wU') (a := fun _ _ ↦ aL') hρ' hr hB ht0 measurable_const measurable_const
    (wU := wU') (fun _ _ ↦ hwU'0) (fun _ _ ↦ le_rfl) (fun _ _ _ ↦ haL'pos.le)
  have hI2 := integrable_modelIntegrand_tied (D := D) (γ := γ) (q := q) (δ := δ) (κ := κ)
    (W := fun _ _ ↦ wU) (a := fun _ _ ↦ aL) hρ hr hB ht0 measurable_const measurable_const
    (wU := wU) (fun _ _ ↦ hwU) (fun _ _ ↦ le_rfl) (fun _ _ _ ↦ haL.le)
  have hI3 := integrable_modelIntegrand_tied (D := D) (γ := γ) (q := q) (δ := δ) (κ := κ)
    (W := fun _ _ ↦ wU) (a := fun _ _ ↦ aL) hρ' hr hB ht0 measurable_const measurable_const
    (wU := wU) (fun _ _ ↦ hwU) (fun _ _ ↦ le_rfl) (fun _ _ _ ↦ haL.le)
  have hIL := integrable_modelIntegrand_tied (D := D) (γ := γ) (q := q) (δ := δ) (κ := κ)
    (W := fun _ _ ↦ wL') (a := fun _ _ ↦ aU') hρ' hr hB ht0 measurable_const measurable_const
    (wU := wL') (fun _ _ ↦ hwL'0) (fun _ _ ↦ le_rfl) (fun _ _ _ ↦ haU'pos.le)
  -- the pointwise bounds at the frozen cut value
  obtain ⟨v₀, hv₀⟩ : ∃ v : ℝ, v = D * t ^ (-(γ / q)) := ⟨_, rfl⟩
  have hcut' : v₀ < ρ' := hv₀ ▸ hcut
  have hcutρ' : v₀ < ρ := hv₀ ▸ hcutρ
  have hv0' : 0 ≤ v₀ := hv₀ ▸ hv0
  have hI : Integrable (modelIntegrand ρ B D γ q δ (0 : Fin (k + 1) → ℝ) κ r W a t) := by
    rw [modelIntegrand_Q_zero_freeze, ← hv₀]
    exact integrable_modelIntegrand_tied (D := D) (γ := γ) (q := q) (δ := δ) (κ := κ)
      (W := fun x _ ↦ W x v₀) (a := fun x _ ↦ a x v₀) hρ hr hB ht0
      (hW.comp (measurable_fst.prodMk measurable_const))
      (ha.comp (measurable_fst.prodMk measurable_const)) (fun x _ ↦ hW0 x v₀)
      (fun x _ ↦ hWup x v₀) fun x _ hx ↦ haL.le.trans (halow x v₀ hx hv0' hcutρ')
  have hbox' : ∀ x : Fin (k + 1) → ℝ, x ∈ Set.pi univ (fun _ : Fin (k + 1) ↦ Ioo (0 : ℝ) ρ') →
      x ∈ Set.pi univ fun _ : Fin (k + 1) ↦ Ioo (0 : ℝ) ρ := fun x hx ↦
    Set.mem_univ_pi.mpr fun j ↦
      ⟨(Set.mem_univ_pi.mp hx j).1, (Set.mem_univ_pi.mp hx j).2.trans_le hρ'ρ⟩
  have hup_pt : ∀ x, modelIntegrand ρ B D γ q δ (0 : Fin (k + 1) → ℝ) κ r W a t x ≤
      modelIntegrand ρ' B D γ q δ (0 : Fin (k + 1) → ℝ) κ r (fun _ _ ↦ wU') (fun _ _ ↦ aL') t x +
        (modelIntegrand ρ B D γ q δ (0 : Fin (k + 1) → ℝ) κ r (fun _ _ ↦ wU) (fun _ _ ↦ aL) t x -
          modelIntegrand ρ' B D γ q δ (0 : Fin (k + 1) → ℝ) κ r (fun _ _ ↦ wU) (fun _ _ ↦ aL)
            t x) := by
    intro x
    unfold modelIntegrand
    rw [modelDomain_eq_of_Q_zero hcut, modelDomain_eq_of_Q_zero hcutρ]
    simp only [cutVar_Q_zero, ← hv₀]
    by_cases hx' : x ∈ Set.pi univ fun _ : Fin (k + 1) ↦ Ioo (0 : ℝ) ρ'
    · have hx := hbox' x hx'
      have hxj : ∀ j, x j ∈ Ioo (0 : ℝ) ρ' := Set.mem_univ_pi.mp hx'
      rw [Set.indicator_of_mem hx, Set.indicator_of_mem hx', Set.indicator_of_mem hx,
        Set.indicator_of_mem hx', sub_self, add_zero]
      have hr0 : 0 ≤ ∏ j, x j ^ r j := Finset.prod_nonneg fun j _ ↦ rpow_nonneg (hxj j).1.le _
      have hκ0 : 0 ≤ ∏ j, x j ^ κ j := Finset.prod_nonneg fun j _ ↦ rpow_nonneg (hxj j).1.le _
      have hBt : 0 ≤ B * t ^ δ := mul_nonneg hB.le (rpow_pos_of_pos ht0 _).le
      obtain ⟨hWn, han⟩ := hnear x v₀ hxj hv0' hcut'
      have hWle : W x v₀ ≤ wU' := by rw [hwU']; linarith [(abs_lt.mp hWn).2]
      have hage : aL' ≤ a x v₀ := by rw [haL']; linarith [(abs_lt.mp han).1]
      refine mul_le_mul (mul_le_mul_of_nonneg_right hWle hr0) (Real.exp_le_exp.mpr ?_)
        (exp_pos _).le (mul_nonneg hwU'0 hr0)
      have key := mul_le_mul_of_nonneg_left hage (mul_nonneg hBt hκ0)
      linarith [key]
    · rw [Set.indicator_of_notMem hx', Set.indicator_of_notMem hx', zero_add, sub_zero]
      by_cases hx : x ∈ Set.pi univ fun _ : Fin (k + 1) ↦ Ioo (0 : ℝ) ρ
      · have hxj : ∀ j, x j ∈ Ioo (0 : ℝ) ρ := Set.mem_univ_pi.mp hx
        rw [Set.indicator_of_mem hx, Set.indicator_of_mem hx]
        have hr0 : 0 ≤ ∏ j, x j ^ r j := Finset.prod_nonneg fun j _ ↦ rpow_nonneg (hxj j).1.le _
        have hκ0 : 0 ≤ ∏ j, x j ^ κ j := Finset.prod_nonneg fun j _ ↦ rpow_nonneg (hxj j).1.le _
        have hBt : 0 ≤ B * t ^ δ := mul_nonneg hB.le (rpow_pos_of_pos ht0 _).le
        refine mul_le_mul (mul_le_mul_of_nonneg_right (hWup _ _) hr0) (Real.exp_le_exp.mpr ?_)
          (exp_pos _).le (mul_nonneg hwU hr0)
        have key := mul_le_mul_of_nonneg_left (halow x v₀ hxj hv0' hcutρ') (mul_nonneg hBt hκ0)
        linarith [key]
      · rw [Set.indicator_of_notMem hx, Set.indicator_of_notMem hx]
  have hlow_pt : ∀ x,
      modelIntegrand ρ' B D γ q δ (0 : Fin (k + 1) → ℝ) κ r (fun _ _ ↦ wL') (fun _ _ ↦ aU') t x ≤
        modelIntegrand ρ B D γ q δ (0 : Fin (k + 1) → ℝ) κ r W a t x := by
    intro x
    unfold modelIntegrand
    rw [modelDomain_eq_of_Q_zero hcut, modelDomain_eq_of_Q_zero hcutρ]
    simp only [cutVar_Q_zero, ← hv₀]
    by_cases hx' : x ∈ Set.pi univ fun _ : Fin (k + 1) ↦ Ioo (0 : ℝ) ρ'
    · have hx := hbox' x hx'
      have hxj : ∀ j, x j ∈ Ioo (0 : ℝ) ρ' := Set.mem_univ_pi.mp hx'
      rw [Set.indicator_of_mem hx, Set.indicator_of_mem hx']
      have hr0 : 0 ≤ ∏ j, x j ^ r j := Finset.prod_nonneg fun j _ ↦ rpow_nonneg (hxj j).1.le _
      have hκ0 : 0 ≤ ∏ j, x j ^ κ j := Finset.prod_nonneg fun j _ ↦ rpow_nonneg (hxj j).1.le _
      have hBt : 0 ≤ B * t ^ δ := mul_nonneg hB.le (rpow_pos_of_pos ht0 _).le
      obtain ⟨hWn, han⟩ := hnear x v₀ hxj hv0' hcut'
      have hWge : wL' ≤ W x v₀ := hwL'le _ (hW0 _ _) (by linarith [(abs_lt.mp hWn).1])
      have hale : a x v₀ ≤ aU' := by rw [haU']; linarith [(abs_lt.mp han).2]
      refine mul_le_mul (mul_le_mul_of_nonneg_right hWge hr0) (Real.exp_le_exp.mpr ?_)
        (exp_pos _).le (mul_nonneg (hW0 _ _) hr0)
      have key := mul_le_mul_of_nonneg_left hale (mul_nonneg hBt hκ0)
      linarith [key]
    · rw [Set.indicator_of_notMem hx']
      exact Set.indicator_nonneg (fun x hx ↦ mul_nonneg (mul_nonneg (hW0 _ _)
        (Finset.prod_nonneg fun j _ ↦ rpow_nonneg (Set.mem_univ_pi.mp hx j).1.le _))
        (exp_pos _).le) x
  -- the kernel bounds
  have hK_le : modelKernel ρ A B D γ p q δ (0 : Fin (k + 1) → ℝ) κ r W a t ≤
      modelKernel ρ' A B D γ p q δ (0 : Fin (k + 1) → ℝ) κ r (fun _ _ ↦ wU') (fun _ _ ↦ aL') t +
        (modelKernel ρ A B D γ p q δ (0 : Fin (k + 1) → ℝ) κ r (fun _ _ ↦ wU) (fun _ _ ↦ aL) t -
          modelKernel ρ' A B D γ p q δ (0 : Fin (k + 1) → ℝ) κ r (fun _ _ ↦ wU) (fun _ _ ↦ aL)
            t) := by
    unfold modelKernel
    have hI23 : Integrable (fun x ↦
        modelIntegrand ρ B D γ q δ (0 : Fin (k + 1) → ℝ) κ r (fun _ _ ↦ wU) (fun _ _ ↦ aL) t x -
          modelIntegrand ρ' B D γ q δ (0 : Fin (k + 1) → ℝ) κ r (fun _ _ ↦ wU) (fun _ _ ↦ aL)
            t x) := hI2.sub hI3
    have hI123 : Integrable (fun x ↦
        modelIntegrand ρ' B D γ q δ (0 : Fin (k + 1) → ℝ) κ r (fun _ _ ↦ wU') (fun _ _ ↦ aL') t x +
          (modelIntegrand ρ B D γ q δ (0 : Fin (k + 1) → ℝ) κ r (fun _ _ ↦ wU) (fun _ _ ↦ aL) t x -
            modelIntegrand ρ' B D γ q δ (0 : Fin (k + 1) → ℝ) κ r (fun _ _ ↦ wU) (fun _ _ ↦ aL)
              t x)) := hI1.add hI23
    rw [← mul_sub, ← mul_add, ← integral_sub hI2 hI3, ← integral_add hI1 hI23]
    exact mul_le_mul_of_nonneg_left (integral_mono hI hI123 hup_pt) hAt
  have hK_ge : modelKernel ρ' A B D γ p q δ (0 : Fin (k + 1) → ℝ) κ r (fun _ _ ↦ wL')
      (fun _ _ ↦ aU') t ≤ modelKernel ρ A B D γ p q δ (0 : Fin (k + 1) → ℝ) κ r W a t := by
    unfold modelKernel
    exact mul_le_mul_of_nonneg_left (integral_mono hIL hI hlow_pt) hAt
  rw [Real.dist_eq] at hu hl
  rw [Real.dist_eq] at hCU hCL
  have hu' := (abs_lt.mp hu).2
  have hl' := (abs_lt.mp hl).1
  have hCU' := (abs_lt.mp hCU).2
  have hCL' := (abs_lt.mp hCL).1
  have h1 := mul_le_mul_of_nonneg_left hK_le hnorm
  have h2 := mul_le_mul_of_nonneg_left hK_ge hnorm
  rw [Real.dist_eq, abs_lt]
  constructor
  · linarith only [h2, hl', hCL', hε]
  · linarith only [h1, hu', hCU', hε]

end Laplace.Multi
