/-
Copyright (c) 2026 Timaeus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Laplace.Grammar.SignedReflectionGeneral

/-!
# Headline XIX: the phase-dressed leading term on the symmetric box

Unit 217 (Astra #23 programme D2, step 2): interior coordinates with phase. On the orthant
`x = σ·u` (`u ∈ (0,1]^d`, `σ ∈ {±1}^d`) one has `x^{2k} = u^{2k}`, `x^h = χ_h(σ) u^h` and
`x^k ξ(x) = ε_σ u^k ξ(σu)` with `χ_h(σ) = ∏ σᵢ^{hᵢ}`, `ε_σ = ∏ σᵢ^{kᵢ}` (`phaseSign h σ`,
`phaseSign k σ`), so the symmetric-box dressed integral is the sum over orthants of unit-box chart
integrals with phase `ε_σ ξ∘σ` and amplitude `χ_h(σ) η∘σ` (`symBox_phase_eq_sum`), and
Headline XIII on each orthant gives
```
∫_{(-1,1]^d} η x^h e^{-βN²x^{2k}+βNx^kξ(x)} dx / (N^{-p}(log N)^{m-1})
  → ∑_σ phaseCoeff h k λ β (ε_σ ξ∘σ) (χ_h(σ) η∘σ)                (headline_symmetric_phase_leading).
```
For the **absolute density** `|x|^h = ∏|xᵢ|^{hᵢ}` (a positive resolved measure) the sign `χ_h(σ)`
disappears (`headline_symmetric_abs_phase_leading`). Odd `kᵢ` flip the phase on the corresponding
reflection (`J_p(a)` versus `J_p(-a)`): no parity cancellation is asserted in general; the
zero-phase parity rule of unit 197 is the special case `ξ = 0`. Zero `sorry`/`axiom`.
-/

open MeasureTheory Filter Topology Real Set

namespace Laplace.Grammar

/-- `χ_e(σ) = ∏ᵢ sgn(σᵢ)^{eᵢ}`. -/
noncomputable def phaseSign {d : ℕ} (e : Fin d → ℕ) (σ : Fin d → Bool) : ℝ :=
  ∏ i, sgn (σ i) ^ e i

theorem phaseSign_sq {d : ℕ} (e : Fin d → ℕ) (σ : Fin d → Bool) : phaseSign e σ ^ 2 = 1 := by
  unfold phaseSign
  rw [← Finset.prod_pow]
  refine Finset.prod_eq_one fun i _ => ?_
  rw [← pow_mul, mul_comm, pow_mul, sgn_sq, one_pow]

theorem abs_sgn (b : Bool) : |sgn b| = 1 := by cases b <;> simp [sgn]

/-- The monomial on a reflected point. -/
theorem prod_reflect_pow {d : ℕ} (e : Fin d → ℕ) (σ : Fin d → Bool) (u : Fin d → ℝ) :
    ∏ i, reflect σ u i ^ e i = phaseSign e σ * ∏ i, u i ^ e i := by
  unfold phaseSign reflect
  rw [← Finset.prod_mul_distrib]
  exact Finset.prod_congr rfl fun i _ => by rw [mul_pow]

/-- The absolute monomial on a reflected point of the positive orthant. -/
theorem prod_abs_reflect_pow {d : ℕ} (e : Fin d → ℕ) (σ : Fin d → Bool) (u : Fin d → ℝ)
    (hu : u ∈ unitBox d) : ∏ i, |reflect σ u i| ^ e i = ∏ i, u i ^ e i := by
  refine Finset.prod_congr rfl fun i _ => ?_
  rw [reflect, abs_mul, abs_sgn, one_mul, abs_of_pos (hu i (mem_univ i)).1]

/-- Reflecting the scale variable moves the sign onto the phase (`ε² = 1`). -/
theorem quadKernel_mul_sign (β a ε s : ℝ) (hε : ε ^ 2 = 1) :
    quadKernel β a (ε * s) = quadKernel β (ε * a) s := by
  unfold quadKernel
  congr 1
  rw [mul_pow, hε, one_mul]
  ring

/-- **Orthant decomposition of the phase-dressed integral (signed monomial density).** -/
theorem symBox_phase_eq_sum {d : ℕ} (β N : ℝ) (h k : Fin d → ℕ) (ξ η : (Fin d → ℝ) → ℝ)
    (hξ : Continuous ξ) (hη : Continuous η) :
    ∫ x in symBox d, η x * ((∏ i, x i ^ h i) * quadKernel β (ξ x) (N * ∏ i, x i ^ k i)) =
      ∑ σ : Fin d → Bool, chartIntegral d h k β N (fun u => phaseSign k σ * ξ (reflect σ u))
        (fun u => phaseSign h σ * η (reflect σ u)) := by
  rw [integral_symBox_eq_sum_reflect d _ (continuous_phaseIntegrand β N h k ξ η hξ hη)]
  refine Finset.sum_congr rfl fun σ _ => ?_
  unfold chartIntegral
  refine setIntegral_congr_fun (measurableSet_unitBox d) fun u _ => ?_
  rw [prod_reflect_pow h, prod_reflect_pow k,
    show N * (phaseSign k σ * ∏ i, u i ^ k i) = phaseSign k σ * (N * ∏ i, u i ^ k i) by ring,
    quadKernel_mul_sign _ _ _ _ (phaseSign_sq k σ)]
  ring

/-- **Orthant decomposition of the phase-dressed integral (absolute density `|x|^h`).** -/
theorem symBox_abs_phase_eq_sum {d : ℕ} (β N : ℝ) (h k : Fin d → ℕ) (ξ η : (Fin d → ℝ) → ℝ)
    (hξ : Continuous ξ) (hη : Continuous η) :
    ∫ x in symBox d, η x * ((∏ i, |x i| ^ h i) * quadKernel β (ξ x) (N * ∏ i, x i ^ k i)) =
      ∑ σ : Fin d → Bool, chartIntegral d h k β N (fun u => phaseSign k σ * ξ (reflect σ u))
        (fun u => η (reflect σ u)) := by
  have hcont : Continuous fun x : Fin d → ℝ =>
      η x * ((∏ i, |x i| ^ h i) * quadKernel β (ξ x) (N * ∏ i, x i ^ k i)) := by
    have hP := continuous_prod_pow k
    have hQ : Continuous fun x : Fin d → ℝ => quadKernel β (ξ x) (N * ∏ i, x i ^ k i) := by
      unfold quadKernel
      exact Real.continuous_exp.comp ((continuous_const.mul ((continuous_const.mul hP).pow 2)).add
        ((continuous_const.mul hξ).mul (continuous_const.mul hP)))
    exact hη.mul ((continuous_finsetProd _ fun i _ =>
      (continuous_abs.comp (continuous_apply i)).pow _).mul hQ)
  rw [integral_symBox_eq_sum_reflect d _ hcont]
  refine Finset.sum_congr rfl fun σ _ => ?_
  unfold chartIntegral
  refine setIntegral_congr_fun (measurableSet_unitBox d) fun u hu => ?_
  rw [prod_abs_reflect_pow h σ u hu, prod_reflect_pow k,
    show N * (phaseSign k σ * ∏ i, u i ^ k i) = phaseSign k σ * (N * ∏ i, u i ^ k i) by ring,
    quadKernel_mul_sign _ _ _ _ (phaseSign_sq k σ)]

/-- **Headline XIX (symmetric box with phase, signed monomial density)**. -/
theorem headline_symmetric_phase_leading (m : ℕ) (h k : Fin (m + 1) → ℕ) (hk : ∀ i, 0 < k i)
    (l β : ℝ) (hl : 0 < l) (hβ : 0 < β) (hmin : ∀ i, l ≤ ((h i : ℝ) + 1) / (2 * (k i : ℝ)))
    (hatt : ∃ i, ((h i : ℝ) + 1) / (2 * (k i : ℝ)) = l) (ξ η : (Fin (m + 1) → ℝ) → ℝ)
    (hξ : Continuous ξ) (hη : Continuous η) :
    Tendsto (fun N : ℝ => (∫ x in symBox (m + 1), η x * ((∏ i, x i ^ h i) *
        Real.exp (-(β * N ^ 2 * ∏ i, x i ^ (2 * k i)) + β * (N * ∏ i, x i ^ k i) * ξ x))) /
        (N ^ (-(2 * l)) * Real.log N ^ (multCount (ratioExp h k) l - 1))) atTop
      (𝓝 (∑ σ : Fin (m + 1) → Bool, phaseCoeff h k l β (fun u => phaseSign k σ * ξ (reflect σ u))
        (fun u => phaseSign h σ * η (reflect σ u)))) := by
  have hT := tendsto_finsetSum Finset.univ fun σ _ =>
    phase_leading_tendsto m h k hk l β hl hβ hmin hatt (fun u => phaseSign k σ * ξ (reflect σ u))
      (fun u => phaseSign h σ * η (reflect σ u))
      (continuous_const.mul (hξ.comp (continuous_reflect σ)))
      (continuous_const.mul (hη.comp (continuous_reflect σ)))
  refine hT.congr' (Eventually.of_forall fun N => ?_)
  rw [← Finset.sum_div]
  congr 1
  have hs := symBox_phase_eq_sum β N h k ξ η hξ hη
  unfold chartIntegral at hs
  beta_reduce at hs
  rw [← hs]
  refine setIntegral_congr_fun (MeasurableSet.univ_pi fun _ => measurableSet_Ioc) fun x _ => ?_
  rw [paperKernel_eq_quadKernel]

/-- **Headline XIX, absolute density `|x|^h`**: no sign factor on the amplitude. -/
theorem headline_symmetric_abs_phase_leading (m : ℕ) (h k : Fin (m + 1) → ℕ) (hk : ∀ i, 0 < k i)
    (l β : ℝ) (hl : 0 < l) (hβ : 0 < β) (hmin : ∀ i, l ≤ ((h i : ℝ) + 1) / (2 * (k i : ℝ)))
    (hatt : ∃ i, ((h i : ℝ) + 1) / (2 * (k i : ℝ)) = l) (ξ η : (Fin (m + 1) → ℝ) → ℝ)
    (hξ : Continuous ξ) (hη : Continuous η) :
    Tendsto (fun N : ℝ => (∫ x in symBox (m + 1), η x * ((∏ i, |x i| ^ h i) *
        Real.exp (-(β * N ^ 2 * ∏ i, x i ^ (2 * k i)) + β * (N * ∏ i, x i ^ k i) * ξ x))) /
        (N ^ (-(2 * l)) * Real.log N ^ (multCount (ratioExp h k) l - 1))) atTop
      (𝓝 (∑ σ : Fin (m + 1) → Bool, phaseCoeff h k l β (fun u => phaseSign k σ * ξ (reflect σ u))
        (fun u => η (reflect σ u)))) := by
  have hT := tendsto_finsetSum Finset.univ fun σ _ =>
    phase_leading_tendsto m h k hk l β hl hβ hmin hatt (fun u => phaseSign k σ * ξ (reflect σ u))
      (fun u => η (reflect σ u)) (continuous_const.mul (hξ.comp (continuous_reflect σ)))
      (hη.comp (continuous_reflect σ))
  refine hT.congr' (Eventually.of_forall fun N => ?_)
  rw [← Finset.sum_div]
  congr 1
  have hs := symBox_abs_phase_eq_sum β N h k ξ η hξ hη
  unfold chartIntegral at hs
  beta_reduce at hs
  rw [← hs]
  refine setIntegral_congr_fun (MeasurableSet.univ_pi fun _ => measurableSet_Ioc) fun x _ => ?_
  rw [paperKernel_eq_quadKernel]

end Laplace.Grammar
