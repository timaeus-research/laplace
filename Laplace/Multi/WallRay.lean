/-
Copyright (c) 2026 Timaeus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Timaeus
-/
import Mathlib
import Laplace.Multi.InteriorThreshold
import Laplace.Multi.ArcsineLength

/-!
# The first wall theorem: ray concentration and directional covariance collapse

For bounded features the response chart has no finite wall: every finite coefficient is a chart
point. The walls are at infinity. Along the ray `a − (λ/t) u`, `λ → ∞` (the member
`P_{t, a − (λ/t)u} ∝ e^{−t L_a + λ R_u} π` pushed towards large `R_u`), with `β` an everywhere upper
bound of `R_u` that is approached with positive prior mass:

* the response in the direction `u` converges to the face value, `u · m_t(a − (λ/t)u) → β`
  (`tendsto_dot_meanMap_ray`, the response form of `tendsto_thresholdFun`);
* the covariance in the ray direction collapses, `Var_{t, a − (λ/t)u}(R_u) → 0`
  (`tendsto_segVar_ray`), and with it the response form `G(u, u) = t² Var(R_u) → 0`
  (`tendsto_responseForm_ray`): by the Bhatia–Davis inequality the variance is at most
  `(‖R_u‖_∞ + |β|)` times the remaining gap `β − u·m` (`segVar_ray_le`).

So along a feature ray the response approaches the exposed face `{u · M = β}` of the moment body
and the response metric degenerates in the ray direction — the covariance-degeneration mechanism
of the wall, in its sharpest quantitative form. (Tangential covariance need not vanish, and the
response need not converge to a point of the face unless the face is a singleton.)
-/

open MeasureTheory Filter Topology Set

namespace Laplace.Multi

variable {X : Type*} [MeasurableSpace X] {μ : Measure X} {ι : Type*} [Fintype ι]

section

variable [Nonempty X] {π L₀ : X → ℝ} (hπm : Measurable π) (hπi : Integrable π μ)
  (hπ : ∀ x, 0 < π x) (hπpos : 0 < ∫ x, π x ∂μ) (hL₀m : Measurable L₀) {M₀ : ℝ}
  (hL₀ : ∀ x, |L₀ x| ≤ M₀) {R : ι → X → ℝ} (hR : ∀ i, Bdd (R i)) {t : ℝ} (ht : 0 < t)
include hπm hπi hπ hπpos hL₀m hL₀ hR ht

omit ht in
/-- The tilted mean stays below the everywhere bound. -/
theorem thresholdFun_le (a u : ι → ℝ) {β : ℝ} (hβ : ∀ x, dirLoss R u x ≤ β) (lam : ℝ) :
    thresholdFun μ π L₀ R t a u lam ≤ β := by
  have hZ := (affZ_pos hπm hπi hπ hπpos hL₀m hL₀ hR (t := t) (a - (lam / t) • u)).ne'
  unfold thresholdFun
  calc priorExp μ π (affLoss L₀ R (a - (lam / t) • u)) (dirLoss R u) t
      ≤ priorExp μ π (affLoss L₀ R (a - (lam / t) • u)) (fun _ ↦ β) t :=
        priorExp_mono_bdd hπm hπi hπ hπpos hL₀m hL₀ hR _ (bdd_dirLoss hR u) (Bdd.const β) hβ
    _ = β := priorExp_const_fun hZ β

omit ht in
/-- **Bhatia–Davis along the ray**: the variance in the ray direction is bounded by the gap to the
face, `Var(R_u) ≤ (‖R_u‖_∞ + |β|) (β − u·m)`. -/
theorem segVar_ray_le (a u : ι → ℝ) {β : ℝ} (hβ : ∀ x, dirLoss R u x ≤ β) {Mu : ℝ}
    (hMu : ∀ x, |dirLoss R u x| ≤ Mu) (lam : ℝ) :
    priorCov μ π (affLoss L₀ R (a - (lam / t) • u)) (dirLoss R u) (dirLoss R u) t ≤
      (Mu + |β|) * (β - thresholdFun μ π L₀ R t a u lam) := by
  have hlo : ∀ x, -Mu ≤ dirLoss R u x := fun x ↦ neg_le_of_abs_le (hMu x)
  have h := priorCov_self_le_mul_of_bounds hπm hπi hπ hπpos hL₀m hL₀ hR (t := t)
    (a - (lam / t) • u) (bdd_dirLoss hR u) hlo hβ
  have hle := thresholdFun_le hπm hπi hπ hπpos hL₀m hL₀ hR (t := t) a u hβ lam
  unfold thresholdFun at hle ⊢
  calc priorCov μ π (affLoss L₀ R (a - (lam / t) • u)) (dirLoss R u) (dirLoss R u) t
      ≤ (priorExp μ π (affLoss L₀ R (a - (lam / t) • u)) (dirLoss R u) t - -Mu) *
          (β - priorExp μ π (affLoss L₀ R (a - (lam / t) • u)) (dirLoss R u) t) := h
    _ ≤ (Mu + |β|) * (β - priorExp μ π (affLoss L₀ R (a - (lam / t) • u)) (dirLoss R u) t) := by
        refine mul_le_mul_of_nonneg_right ?_ (by linarith)
        linarith [le_abs_self β]

/-- **The response approaches the exposed face**: `u · m_t(a − (λ/t)u) → β`. -/
theorem tendsto_dot_meanMap_ray (a u : ι → ℝ) {β : ℝ} (hβ : ∀ x, dirLoss R u x ≤ β)
    (hmass : ∀ ε > 0, 0 < ∫ x in {x | β - ε < dirLoss R u x}, π x ∂μ) :
    Tendsto (fun lam : ℝ ↦ ∑ i, u i * meanMap μ π L₀ R t (a - (lam / t) • u) i) atTop (𝓝 β) := by
  have h := tendsto_thresholdFun hπm hπi hπ hπpos hL₀m hL₀ hR ht a u (ae_of_all μ hβ) hmass
  refine h.congr fun lam ↦ ?_
  exact thresholdFun_eq_sum hπm hπi hπ hπpos hL₀m hL₀ hR (t := t) a u lam

/-- **Directional covariance collapse**: `Var_{t, a − (λ/t)u}(R_u) → 0` along the ray. -/
theorem tendsto_segVar_ray (a u : ι → ℝ) {β : ℝ} (hβ : ∀ x, dirLoss R u x ≤ β)
    (hmass : ∀ ε > 0, 0 < ∫ x in {x | β - ε < dirLoss R u x}, π x ∂μ) :
    Tendsto (fun lam : ℝ ↦
      priorCov μ π (affLoss L₀ R (a - (lam / t) • u)) (dirLoss R u) (dirLoss R u) t) atTop
      (𝓝 0) := by
  obtain ⟨_, Mu, hMu⟩ := bdd_dirLoss hR u
  have hth := tendsto_thresholdFun hπm hπi hπ hπpos hL₀m hL₀ hR ht a u (ae_of_all μ hβ) hmass
  have hup : Tendsto (fun lam : ℝ ↦ (Mu + |β|) * (β - thresholdFun μ π L₀ R t a u lam)) atTop
      (𝓝 ((Mu + |β|) * (β - β))) := (tendsto_const_nhds.sub hth).const_mul _
  rw [sub_self, mul_zero] at hup
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hup (fun lam ↦ ?_)
    (fun lam ↦ segVar_ray_le hπm hπi hπ hπpos hL₀m hL₀ hR (t := t) a u hβ hMu lam)
  exact priorCov_self_nonneg' hπm hπi hπ hπpos hL₀m hL₀ hR (t := t) _ (bdd_dirLoss hR u)

/-- **The response metric degenerates in the ray direction**: `G_{a − (λ/t)u}(u, u) → 0`. -/
theorem tendsto_responseForm_ray (a u : ι → ℝ) {β : ℝ} (hβ : ∀ x, dirLoss R u x ≤ β)
    (hmass : ∀ ε > 0, 0 < ∫ x in {x | β - ε < dirLoss R u x}, π x ∂μ) :
    Tendsto (fun lam : ℝ ↦ responseForm μ π L₀ R (a - (lam / t) • u) t u u) atTop (𝓝 0) := by
  have h := (tendsto_segVar_ray hπm hπi hπ hπpos hL₀m hL₀ hR ht a u hβ hmass).const_mul (t ^ 2)
  rw [mul_zero] at h
  exact h

end

end Laplace.Multi
