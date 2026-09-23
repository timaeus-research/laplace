/-
Copyright (c) 2026 Timaeus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Timaeus
-/
import Laplace.Multi.FullLawResolvent
import Laplace.Multi.MinibatchScaled

/-!
# The E8 corrections at the anchored scaling: both grow linearly in `t`

At the β-scaled step `h = η/t` with a fixed gradient-noise covariance `C`, fixed Hessian deviations
`Dᵢ` and a fixed coefficient `c`
(the note's `c = h²t²(1−m/n)/(m(n−1)) = η²(1−m/n)/(m(n−1))` is `t`-independent at this scaling):
* the minibatch stationary covariance has an `O(1)` limit, `Σ^{mb}(t) → Σ∞ = QŜ∞Qᵀ`, `Ŝ∞ₖₗ =
η²Ĉₖₗ/(1−αₖαₗ)` (`mbCov_tendsto`);
* the first-order Hessian-fluctuation correction to the LLC of tide 115 grows linearly in `t` with
slope
  `σ₁ = ½c∑ⱼλⱼ(QᵀB(Σ∞)Q)ⱼⱼ/(1−αⱼ²)` (`firstOrder_slope_tendsto`);
* the constant-noise inflation `LLC^{mb} − LLC^{ULA}` grows linearly with slope `σ_mb =
(η/4)∑ⱼĈⱼⱼ/(1−ηλⱼ/2)` (`mb_slope_tendsto`), the
  "grows linearly in `t`" of the note's Summary 2;
* hence the full-law LLC mean exceeds the exact-gradient value by at least `t(σ_mb + σ₁) + o(t)`
(`fullLaw_lower_slope_tendsto`).
-/

open Matrix Filter Topology

namespace Laplace.Multi

section Scaled

variable {d : ℕ} {Q : Matrix (Fin d) (Fin d) ℝ} {lam : Fin d → ℝ} {g η : ℝ}

/-- The frame entries of the minibatch covariance converge: `(QᵀΣ^{mb}Q)ₖₗ → η²Ĉₖₗ/(1−αₖαₗ)`. -/
theorem mbCov_frame_tendsto (hlam : ∀ i, 0 < lam i) (hQ : Qᵀ * Q = 1) (hη : 0 < η)
    (hηl : ∀ i, η * lam i < 2) (C : Matrix (Fin d) (Fin d) ℝ) (k l : Fin d) :
    Tendsto (fun t : ℝ => (Qᵀ * Laplace.Sampler.lyapunovVia Q (fun i => 1 - η / t * (t * lam i +
        g)) (Laplace.Sampler.minibatchNoise (η / t) t C) * Q) k l) atTop
      (𝓝 (η ^ 2 * (Qᵀ * C * Q) k l / (1 - (1 - η * lam k) * (1 - η * lam l)))) := by
  have e : ∀ t : ℝ, (Qᵀ * Laplace.Sampler.lyapunovVia Q (fun i => 1 - η / t * (t * lam i + g))
      (Laplace.Sampler.minibatchNoise (η / t) t C) * Q) k l =
      (2 * (η / t) * (if k = l then 1 else 0) + (η / t) ^ 2 * t ^ 2 * (Qᵀ * C * Q) k l) /
        (1 - (1 - η / t * (t * lam k + g)) * (1 - η / t * (t * lam l + g))) := fun t => by
    rw [Laplace.Sampler.minibatchCov_frame_apply (p := fun i => t * lam i + g) hQ (η / t) t C k l]
    congr 1
    ring
  exact (mbEntry_scaled_tendsto (g := g) (hlam k) (hlam l) hη (hηl k) (hηl l) (if k = l then 1 else
      0)
    ((Qᵀ * C * Q) k l)).congr' (Filter.Eventually.of_forall fun t => (e t).symm)

/-- **The minibatch stationary covariance has an `O(1)` limit at fixed relative step**: `Σ^{mb}(t)
→ QŜ∞Qᵀ`. -/
theorem mbCov_tendsto (hlam : ∀ i, 0 < lam i) (hQ : Qᵀ * Q = 1) (hη : 0 < η) (hηl : ∀ i, η * lam i
    < 2)
    (C : Matrix (Fin d) (Fin d) ℝ) :
    Tendsto (fun t : ℝ => Laplace.Sampler.lyapunovVia Q (fun i => 1 - η / t * (t * lam i + g))
        (Laplace.Sampler.minibatchNoise (η / t) t C)) atTop (𝓝 (Q * (Matrix.of fun k l : Fin d => η
            ^ 2 * (Qᵀ * C * Q) k l / (1 - (1 - η * lam k) * (1 - η * lam l))) * Qᵀ)) := by
  have hfr : Tendsto (fun t : ℝ => Qᵀ * Laplace.Sampler.lyapunovVia Q (fun i => 1 - η / t * (t *
      lam i + g)) (Laplace.Sampler.minibatchNoise (η / t) t C) * Q) atTop (𝓝 (Matrix.of fun k l :
          Fin d => η ^ 2 * (Qᵀ * C * Q) k l / (1 - (1 - η * lam k) * (1 - η * lam l)))) :=
    tendsto_pi_nhds.2 fun k => tendsto_pi_nhds.2 fun l => by
      simpa [Matrix.of_apply] using mbCov_frame_tendsto hlam hQ hη hηl C k l
  have hc : Continuous fun X : Matrix (Fin d) (Fin d) ℝ => Q * X * Qᵀ :=
    (continuous_const.matrix_mul continuous_id).matrix_mul continuous_const
  refine ((hc.tendsto _).comp hfr).congr' (Filter.Eventually.of_forall fun t => ?_)
  simp only [Function.comp_def]
  exact Laplace.Sampler.conj_transpose_mul_mul_self hQ _

/-- `Σ ↦ (Qᵀ B(Σ) Q)ⱼⱼ` is continuous. -/
theorem continuous_stateTerm_frame_diag {n : ℕ} (Q : Matrix (Fin d) (Fin d) ℝ)
    (D : Fin n → Matrix (Fin d) (Fin d) ℝ) (j : Fin d) :
    Continuous fun X : Matrix (Fin d) (Fin d) ℝ => (Qᵀ * Laplace.Sampler.stateTerm D X * Q) j j :=
        by
  have hst : Continuous fun X : Matrix (Fin d) (Fin d) ℝ => Laplace.Sampler.stateTerm D X := by
    unfold Laplace.Sampler.stateTerm
    exact continuous_finsetSum _ fun i _ =>
      (continuous_const.matrix_mul continuous_id).matrix_mul continuous_const
  exact (continuous_apply j).comp ((continuous_apply j).comp
    ((continuous_const.matrix_mul hst).matrix_mul continuous_const))

/-- **The first-order Hessian-fluctuation correction grows linearly in `t`**, with slope
`σ₁ = ½c∑ⱼλⱼ(QᵀB(Σ∞)Q)ⱼⱼ/(1−αⱼ²)`. -/
theorem firstOrder_slope_tendsto {n : ℕ} (hlam : ∀ i, 0 < lam i) (hQ : Qᵀ * Q = 1) (hη : 0 < η)
    (hηl : ∀ i, η * lam i < 2) (C : Matrix (Fin d) (Fin d) ℝ) (D : Fin n → Matrix (Fin d) (Fin d) ℝ)
    (c : ℝ) :
    Tendsto (fun t : ℝ => 1 / t * (t / 2 * (c * ∑ j, lam j * ((Qᵀ * Laplace.Sampler.stateTerm D
      (Laplace.Sampler.lyapunovVia Q (fun i => 1 - η / t * (t * lam i + g))
      (Laplace.Sampler.minibatchNoise (η / t) t C)) * Q) j j / (1 - (1 - η / t * (t * lam j + g)) *
      (1 - η / t * (t * lam j + g))))))) atTop (𝓝 (1 / 2 * (c * ∑ j, lam j * ((Qᵀ *
      Laplace.Sampler.stateTerm D (Q * (Matrix.of fun k l : Fin d => η ^ 2 * (Qᵀ * C * Q) k l / (1 -
      (1 - η * lam k) * (1 - η * lam l))) * Qᵀ) * Q) j j / (1 - (1 - η * lam j) * (1 - η * lam
      j)))))) := by
  have hB : ∀ j, Tendsto (fun t : ℝ => (Qᵀ * Laplace.Sampler.stateTerm D
      (Laplace.Sampler.lyapunovVia Q (fun i => 1 - η / t * (t * lam i + g))
          (Laplace.Sampler.minibatchNoise (η / t) t C)) * Q) j j) atTop
      (𝓝 ((Qᵀ * Laplace.Sampler.stateTerm D (Q * (Matrix.of fun k l : Fin d => η ^ 2 * (Qᵀ * C * Q)
          k l / (1 - (1 - η * lam k) * (1 - η * lam l))) * Qᵀ) * Q) j j)) := fun j =>
    ((continuous_stateTerm_frame_diag Q D j).tendsto _).comp (mbCov_tendsto hlam hQ hη hηl C)
  have hmode : ∀ j, Tendsto (fun t : ℝ => lam j * ((Qᵀ * Laplace.Sampler.stateTerm D
      (Laplace.Sampler.lyapunovVia Q (fun i => 1 - η / t * (t * lam i + g))
          (Laplace.Sampler.minibatchNoise (η / t) t C)) * Q) j j /
      (1 - (1 - η / t * (t * lam j + g)) * (1 - η / t * (t * lam j + g))))) atTop (𝓝 (lam j * ((Qᵀ
          * Laplace.Sampler.stateTerm D (Q * (Matrix.of fun k l : Fin d => η ^ 2 * (Qᵀ * C * Q) k l
              / (1 - (1 - η * lam k) * (1 - η * lam l))) * Qᵀ) * Q) j j /
      (1 - (1 - η * lam j) * (1 - η * lam j))))) := fun j =>
    (tendsto_const_nhds (x := lam j)).mul ((hB j).div (one_sub_rho_mul_scaled_tendsto (lam j) (lam
        j) g η)
      (one_sub_rho_mul_pos (hlam j) (hlam j) hη (hηl j) (hηl j)).ne')
  have h := ((tendsto_finsetSum Finset.univ fun j _ => hmode j).const_mul c).const_mul (1 / 2)
  refine h.congr' ?_
  filter_upwards [eventually_ne_atTop (0 : ℝ)] with t ht
  rw [← mul_assoc (1 / t) (t / 2), show (1 : ℝ) / t * (t / 2) = 1 / 2 by field_simp]

/-- **The constant-noise inflation grows linearly in `t`**: `(LLC^{mb} − LLC^{ULA})/t →
(η/4)∑ⱼĈⱼⱼ/(1−ηλⱼ/2)`. -/
theorem mb_slope_tendsto (hlam : ∀ i, 0 < lam i) (hg : 0 ≤ g) (hηl : ∀ i, η * lam i < 2)
    (C : Matrix (Fin d) (Fin d) ℝ) :
    Tendsto (fun t : ℝ => 1 / t * (t / 2 * ∑ i, lam i * ((1 + η / t * t ^ 2 * (Qᵀ * C * Q) i i / 2)
      / ((t * lam i + g) * (1 - η / t * (t * lam i + g) / 2))) - t / 2 * ∑ i, lam i * (1 / ((t * lam
      i + g) * (1 - η / t * (t * lam i + g) / 2))))) atTop (𝓝 (η / 4 * ∑ i, (Qᵀ * C * Q) i i * (1 /
      (1 - η * lam i / 2)))) := by
  have hev : ∀ᶠ t : ℝ in atTop, 0 < t ∧ ∀ i, 0 < 1 - η / t * (t * lam i + g) / 2 :=
    (eventually_gt_atTop 0).and (Filter.eventually_all.2 fun i =>
      (scaledStep_eventually (g := g) (hηl i)).mono fun _ h => h.2)
  have h := (tendsto_finsetSum Finset.univ fun j _ => (tendsto_const_nhds (x := (Qᵀ * C * Q) j
      j)).mul
    (ulaScaledStep_factor_tendsto (g := g) (hlam j) (hηl j))).const_mul (η / 4)
  refine h.congr' ?_
  filter_upwards [hev] with t ⟨ht, hκ⟩
  have ht0 := ht.ne'
  simp only [Finset.mul_sum, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun j _ => ?_
  have hp : t * lam j + g ≠ 0 := by
    have := hlam j
    positivity
  have hκj := (hκ j).ne'
  field_simp
  ring

/-- **The full-law LLC mean exceeds the exact-gradient value by at least `t(σ_mb + σ₁) + o(t)`**. -/
theorem fullLaw_lower_slope_tendsto {n : ℕ} (hlam : ∀ i, 0 < lam i) (hQ : Qᵀ * Q = 1) (hg : 0 ≤ g)
    (hη : 0 < η)
    (hηl : ∀ i, η * lam i < 2) (C : Matrix (Fin d) (Fin d) ℝ) (D : Fin n → Matrix (Fin d) (Fin d) ℝ)
    (c : ℝ) :
    Tendsto (fun t : ℝ => 1 / t * (t / 2 * ∑ i, lam i * ((1 + η / t * t ^ 2 * (Qᵀ * C * Q) i i / 2)
      / ((t * lam i + g) * (1 - η / t * (t * lam i + g) / 2))) + t / 2 * (c * ∑ j, lam j * ((Qᵀ *
      Laplace.Sampler.stateTerm D (Laplace.Sampler.lyapunovVia Q (fun i => 1 - η / t * (t * lam i +
      g)) (Laplace.Sampler.minibatchNoise (η / t) t C)) * Q) j j / (1 - (1 - η / t * (t * lam j +
      g)) * (1 - η / t * (t * lam j + g))))) - t / 2 * ∑ i, lam i * (1 / ((t * lam i + g) * (1 - η /
      t * (t * lam i + g) / 2))))) atTop (𝓝 (η / 4 * ∑ i, (Qᵀ * C * Q) i i * (1 / (1 - η * lam i /
      2)) + 1 / 2 * (c * ∑ j, lam j * ((Qᵀ * Laplace.Sampler.stateTerm D (Q * (Matrix.of fun k l :
      Fin d => η ^ 2 * (Qᵀ * C * Q) k l / (1 - (1 - η * lam k) * (1 - η * lam l))) * Qᵀ) * Q) j j /
      (1 - (1 - η * lam j) * (1 - η * lam j)))))) := by
  have h := (mb_slope_tendsto (Q := Q) hlam hg hηl C).add
    (firstOrder_slope_tendsto (g := g) hlam hQ hη hηl C D c)
  refine h.congr' (Filter.Eventually.of_forall fun t => ?_)
  ring

end Scaled

end Laplace.Multi
