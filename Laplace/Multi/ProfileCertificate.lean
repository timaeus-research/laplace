/-
Copyright (c) 2026 Timaeus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Timaeus
-/
import Laplace.Multi.RescaledData

/-!
# Profile certificates: the certified moving-kernel limit

Astra's lemma 3 (`research_kernel_asymptotics_v1`): a family `K t` (a chart kernel along a schedule)
is certified by finitely many pieces `e`, each a `RescaledData` instance on its own measure space
`(X e, μ e)`, together with the exact decomposition `K t = L t · ∑ e ∫ w e t u e^{-G e t u}`
(`ProfileCertificate`). Then `K t / L t → C = ∑ e ∫ w₀ e u e^{-Φ₀ e u}` (`tendsto_K_div_L`), a
numerator
with a bounded observable whose pullback converges under the same maps has `Q t / L t → J`
(`tendsto_Q_div_L`, through `RescaledData.tendsto_den_moving`), the energy numerator
`∑ e ∫ w G e^{-G}` converges likewise (`tendsto_energy_div_L`), and `Q t / K t → J / C` when
`C ≠ 0`
(`tendsto_ratio`); `C > 0` when the limiting weights are nonnegative and one piece has positive
mass (`limit_pos`). This separates the geometry of the certificate (rescalings, cutoffs, face
variables) from the dominated-convergence argument, which is `RescaledData`.
-/

open Real MeasureTheory Filter Topology

namespace Laplace.Multi

namespace RescaledData

variable {X : Type*} [MeasurableSpace X] {T : Type*} {l : Filter T} [l.IsCountablyGenerated]
  {μ : Measure X} {G w : T → X → ℝ} {Φ₀ w₀ W : X → ℝ} {c : ℝ}

/-- Weighted partition function with a MOVING bounded observable `g t → g₀`. -/
theorem tendsto_den_moving (hd : RescaledData l μ G w Φ₀ w₀ W c) {g : T → X → ℝ}
    (hg : ∀ t, Measurable (g t)) {g₀ : X → ℝ}
    (hglim : ∀ u, Tendsto (fun t ↦ g t u) l (𝓝 (g₀ u))) {Mg : ℝ} (hMg : ∀ t u, |g t u| ≤ Mg)
    (hMg0 : 0 ≤ Mg) :
    Tendsto (fun t ↦ ∫ u, w t u * (g t u * Real.exp (-(G t u))) ∂μ) l
      (𝓝 (∫ u, w₀ u * (g₀ u * Real.exp (-Φ₀ u)) ∂μ)) := by
  refine tendsto_integral_filter_of_dominated_convergence
    (fun u ↦ Mg * (W u * Real.exp (-(c * Φ₀ u)))) (Filter.Eventually.of_forall fun t ↦ ?_) ?_
    (hd.int.const_mul Mg) (Filter.Eventually.of_forall fun u ↦ ?_)
  · have h1 := hd.w_meas t
    have h2 := hd.G_meas t
    have h3 := hg t
    exact Measurable.aestronglyMeasurable (by fun_prop)
  · filter_upwards [hd.lower] with t hl
    refine Filter.Eventually.of_forall fun u ↦ ?_
    rw [Real.norm_eq_abs, abs_mul, abs_mul, Real.abs_exp]
    calc |w t u| * (|g t u| * Real.exp (-(G t u)))
        = |g t u| * (|w t u| * Real.exp (-(G t u))) := by ring
      _ ≤ Mg * (W u * Real.exp (-(c * Φ₀ u))) :=
          mul_le_mul (hMg t u) (hd.bound_den hl u) (by positivity) hMg0
  · exact (hd.w_lim u).mul ((hglim u).mul
      ((Real.continuous_exp.tendsto _).comp (hd.G_lim u).neg))

end RescaledData

/-- **A profile certificate** for the family `K` with normalisation `L`: finitely many rescaled
pieces, each a `RescaledData` instance, and the exact decomposition of `K`. -/
structure ProfileCertificate {T : Type*} (l : Filter T) (K L : T → ℝ) {ι : Type*} [Fintype ι]
    (X : ι → Type*) [∀ e, MeasurableSpace (X e)] (μ : ∀ e, Measure (X e))
    (G w : ∀ e, T → X e → ℝ) (Φ₀ w₀ W : ∀ e, X e → ℝ) (c : ι → ℝ) : Prop where
  pieces : ∀ e, RescaledData l (μ e) (G e) (w e) (Φ₀ e) (w₀ e) (W e) (c e)
  L_ne : ∀ᶠ t in l, L t ≠ 0
  K_eq : ∀ᶠ t in l, K t = L t * ∑ e, ∫ u, w e t u * Real.exp (-(G e t u)) ∂μ e

namespace ProfileCertificate

variable {T : Type*} {l : Filter T} [l.IsCountablyGenerated] {K L : T → ℝ} {ι : Type*} [Fintype ι]
  {X : ι → Type*} [∀ e, MeasurableSpace (X e)] {μ : ∀ e, Measure (X e)}
  {G w : ∀ e, T → X e → ℝ} {Φ₀ w₀ W : ∀ e, X e → ℝ} {c : ι → ℝ}

/-- The limiting constant `C = ∑ e ∫ w₀ e^{-Φ₀}`. -/
noncomputable def limit (_ : ProfileCertificate l K L X μ G w Φ₀ w₀ W c) : ℝ :=
  ∑ e, ∫ u, w₀ e u * Real.exp (-(Φ₀ e u)) ∂μ e

/-- **The certified limit** `K / L → C`. -/
theorem tendsto_K_div_L (hc : ProfileCertificate l K L X μ G w Φ₀ w₀ W c) :
    Tendsto (fun t ↦ K t / L t) l (𝓝 hc.limit) := by
  have h := tendsto_finsetSum Finset.univ fun e _ ↦ (hc.pieces e).tendsto_den (g := fun _ ↦ (1 : ℝ))
    measurable_const (Mg := 1) (fun _ ↦ by simp) zero_le_one
  simp only [one_mul] at h
  refine h.congr' ?_
  filter_upwards [hc.K_eq, hc.L_ne] with t hK hL
  rw [hK, mul_div_cancel_left₀ _ hL]

/-- A numerator with a bounded observable whose pullback converges: `Q / L → J`. -/
theorem tendsto_Q_div_L (hc : ProfileCertificate l K L X μ G w Φ₀ w₀ W c) {Q : T → ℝ}
    {g : ∀ e, T → X e → ℝ} (hg : ∀ e t, Measurable (g e t)) {g₀ : ∀ e, X e → ℝ}
    (hglim : ∀ e u, Tendsto (fun t ↦ g e t u) l (𝓝 (g₀ e u))) {Mg : ℝ}
    (hMg : ∀ e t u, |g e t u| ≤ Mg) (hMg0 : 0 ≤ Mg)
    (hQ : ∀ᶠ t in l, Q t = L t * ∑ e, ∫ u, w e t u * (g e t u * Real.exp (-(G e t u))) ∂μ e) :
    Tendsto (fun t ↦ Q t / L t) l
      (𝓝 (∑ e, ∫ u, w₀ e u * (g₀ e u * Real.exp (-(Φ₀ e u))) ∂μ e)) := by
  have h := tendsto_finsetSum Finset.univ fun e _ ↦
    (hc.pieces e).tendsto_den_moving (hg e) (hglim e) (hMg e) hMg0
  refine h.congr' ?_
  filter_upwards [hQ, hc.L_ne] with t hQt hL
  rw [hQt, mul_div_cancel_left₀ _ hL]

/-- The energy numerator `∑ e ∫ w G e^{-G}`: `E / L → ∑ e ∫ w₀ Φ₀ e^{-Φ₀}`. -/
theorem tendsto_energy_div_L (hc : ProfileCertificate l K L X μ G w Φ₀ w₀ W c) {E : T → ℝ}
    (hE : ∀ᶠ t in l, E t = L t * ∑ e, ∫ u, w e t u * (G e t u * Real.exp (-(G e t u))) ∂μ e) :
    Tendsto (fun t ↦ E t / L t) l
      (𝓝 (∑ e, ∫ u, w₀ e u * (Φ₀ e u * Real.exp (-(Φ₀ e u))) ∂μ e)) := by
  have h := tendsto_finsetSum Finset.univ fun e _ ↦ (hc.pieces e).tendsto_num (g := fun _ ↦ (1 : ℝ))
    measurable_const (Mg := 1) (fun _ ↦ by simp) zero_le_one
  simp only [one_mul] at h
  refine h.congr' ?_
  filter_upwards [hE, hc.L_ne] with t hEt hL
  rw [hEt, mul_div_cancel_left₀ _ hL]

/-- The ratio of two certified families with the same normalisation: `Q / K → J / C`. -/
theorem tendsto_ratio (hc : ProfileCertificate l K L X μ G w Φ₀ w₀ W c) {Q : T → ℝ} {J : ℝ}
    (hQ : Tendsto (fun t ↦ Q t / L t) l (𝓝 J)) (hC : hc.limit ≠ 0) :
    Tendsto (fun t ↦ Q t / K t) l (𝓝 (J / hc.limit)) := by
  refine (hQ.div hc.tendsto_K_div_L hC).congr' ?_
  filter_upwards [hc.L_ne] with t hL
  simp only [Pi.div_apply]
  rw [div_div_div_cancel_right₀ hL]

omit [l.IsCountablyGenerated] in
/-- Positivity of the limiting constant from nonnegative limiting weights and one massive piece. -/
theorem limit_pos (hc : ProfileCertificate l K L X μ G w Φ₀ w₀ W c) (hw : ∀ e u, 0 ≤ w₀ e u)
    (hpos : ∃ e, 0 < ∫ u, w₀ e u * Real.exp (-(Φ₀ e u)) ∂μ e) : 0 < hc.limit := by
  obtain ⟨e, he⟩ := hpos
  exact Finset.sum_pos' (fun e _ ↦ integral_nonneg fun u ↦ mul_nonneg (hw e u) (exp_pos _).le)
    ⟨e, Finset.mem_univ _, he⟩

end ProfileCertificate

end Laplace.Multi
