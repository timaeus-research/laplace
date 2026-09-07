/-
Copyright (c) 2026 Timaeus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Laplace.Grammar.HeadlineAssembly

/-!
# Lipschitz dependence of the normalised chart integral on phase and amplitude

Unit 209 (Astra #22 programme A2, step 1). To transfer Headline XIII to *random* phases and
amplitudes one needs remainder control along varying inputs. The mechanism is an eventual
equi-Lipschitz estimate: for `|ξ|, |ξ'| ≤ M` and `|η'| ≤ A` on the cube,
```
|I_N(ξ,η) − I_N(ξ',η')| ≤ ‖η−η'‖ · G₀(N) + β A ‖ξ−ξ'‖ · G₁(N),
G₀(N) = ∫ u^h e^{-βs²+βMs},  G₁(N) = ∫ u^h s e^{-βs²+βMs},  s = N u^k,
```
and both `G₀/S_N`, `G₁/S_N` converge (Headline XIII at constant phase `M`, exponents `h` and
`h + k`), so the normalised integral `F_N = I_N/S_N` is eventually Lipschitz on bounded input sets
with a constant `L` independent of `N` and of the inputs (`normalised_lipschitz_eventually`).

* (`abs_exp_sub_exp_le` from `MixedBlockEnvelope`: `|e^x − e^y| ≤ |x − y| e^{max x y}`);
* `quadKernel_sub_le`: `|quadKernel β a s − quadKernel β a' s| ≤ β s |a − a'| quadKernel β M s`
  for `s ≥ 0`, `|a|, |a'| ≤ M`; `quadKernel_le_of_le`: monotonicity in the phase;
* `chartIntegral_sub_le`: the integral estimate;
* `chartIntegral_shift_mul`: `G₁(N) = N · chartIntegral (h+k) …`;
* `normalised_lipschitz_eventually`.

Zero `sorry`/`axiom`.
-/

open MeasureTheory Filter Topology Real Set

namespace Laplace.Grammar

/-- Monotonicity of the dressed kernel in the phase, for `s ≥ 0`. -/
theorem quadKernel_le_of_le (β a M s : ℝ) (hβ : 0 < β) (hs : 0 ≤ s) (haM : a ≤ M) :
    quadKernel β a s ≤ quadKernel β M s := by
  unfold quadKernel
  apply Real.exp_le_exp.2
  have := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left haM hβ.le) hs
  linarith

/-- Lipschitz dependence of the dressed kernel on the phase:
`|quadKernel β a s − quadKernel β a' s| ≤ β s |a − a'| quadKernel β M s`. -/
theorem quadKernel_sub_le (β a a' M s : ℝ) (hβ : 0 < β) (hs : 0 ≤ s) (ha : |a| ≤ M)
    (ha' : |a'| ≤ M) :
    |quadKernel β a s - quadKernel β a' s| ≤ β * s * |a - a'| * quadKernel β M s := by
  unfold quadKernel
  have hsplit : ∀ b : ℝ, Real.exp (-β * s ^ 2 + β * b * s) =
      Real.exp (-β * s ^ 2) * Real.exp (β * b * s) := fun b => by rw [← Real.exp_add]
  rw [hsplit a, hsplit a', hsplit M, ← mul_sub, abs_mul, abs_of_pos (Real.exp_pos _)]
  have h1 := abs_exp_sub_exp_le (β * a * s) (β * a' * s)
  have hmax : max (β * a * s) (β * a' * s) ≤ β * M * s := by
    refine max_le ?_ ?_
    · exact mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left ((le_abs_self a).trans ha) hβ.le) hs
    · exact mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left ((le_abs_self a').trans ha') hβ.le) hs
  have h2 : |β * a * s - β * a' * s| = β * s * |a - a'| := by
    rw [show β * a * s - β * a' * s = (β * s) * (a - a') by ring, abs_mul,
      abs_of_nonneg (mul_nonneg hβ.le hs)]
  calc Real.exp (-β * s ^ 2) * |Real.exp (β * a * s) - Real.exp (β * a' * s)|
      ≤ Real.exp (-β * s ^ 2) *
          (|β * a * s - β * a' * s| * Real.exp (max (β * a * s) (β * a' * s))) :=
        mul_le_mul_of_nonneg_left h1 (Real.exp_pos _).le
    _ ≤ Real.exp (-β * s ^ 2) * (|β * a * s - β * a' * s| * Real.exp (β * M * s)) := by
        gcongr
    _ = β * s * |a - a'| * (Real.exp (-β * s ^ 2) * Real.exp (β * M * s)) := by
        rw [h2]
        ring

/-- `G₁(N) = ∫ u^h (N u^k) quadKernel β M (N u^k) = N · chartIntegral (h + k) …`. -/
theorem chartIntegral_shift_mul (d : ℕ) (h k : Fin d → ℕ) (β N M : ℝ) :
    ∫ u in unitBox d, (∏ i, u i ^ h i) * ((N * ∏ i, u i ^ k i) *
        quadKernel β M (N * ∏ i, u i ^ k i)) =
      N * chartIntegral d (phaseShift h k 1) k β N (fun _ => M) (fun _ => 1) := by
  unfold chartIntegral
  rw [← integral_const_mul]
  refine setIntegral_congr_fun (measurableSet_unitBox d) fun u _ => ?_
  rw [prod_pow_phaseShift, pow_one]
  ring

/-- **Integral Lipschitz estimate**: for `|ξ|, |ξ'| ≤ M`, `|η'| ≤ A`, `|η − η'| ≤ δη`,
`|ξ − ξ'| ≤ δξ` on the closed cube, and `N ≥ 0`,
`|I_N(ξ,η) − I_N(ξ',η')| ≤ δη G₀(N) + β A δξ G₁(N)`. -/
theorem chartIntegral_sub_le (d : ℕ) (h k : Fin d → ℕ) (β N M A δξ δη : ℝ) (hβ : 0 < β)
    (hN : 0 ≤ N) (ξ ξ' η η' : (Fin d → ℝ) → ℝ) (hξ : Continuous ξ) (hξ' : Continuous ξ')
    (hη : Continuous η) (hη' : Continuous η') (hξM : ∀ x ∈ closedCube d, |ξ x| ≤ M)
    (hξ'M : ∀ x ∈ closedCube d, |ξ' x| ≤ M) (hη'A : ∀ x ∈ closedCube d, |η' x| ≤ A)
    (hδξ : ∀ x ∈ closedCube d, |ξ x - ξ' x| ≤ δξ) (hδη : ∀ x ∈ closedCube d, |η x - η' x| ≤ δη) :
    |chartIntegral d h k β N ξ η - chartIntegral d h k β N ξ' η'| ≤
      δη * chartIntegral d h k β N (fun _ => M) (fun _ => 1) +
        β * A * δξ * (N * chartIntegral d (phaseShift h k 1) k β N (fun _ => M) (fun _ => 1)) := by
  have hA0 : 0 ≤ A := (abs_nonneg _).trans (hη'A 0 fun i _ => ⟨le_rfl, zero_le_one⟩)
  have hδξ0 : 0 ≤ δξ := (abs_nonneg _).trans (hδξ 0 fun i _ => ⟨le_rfl, zero_le_one⟩)
  have hδη0 : 0 ≤ δη := (abs_nonneg _).trans (hδη 0 fun i _ => ⟨le_rfl, zero_le_one⟩)
  have hI := integrableOn_unitBox_of_continuous _ (continuous_phaseIntegrand β N h k ξ η hξ hη)
  have hI' := integrableOn_unitBox_of_continuous _ (continuous_phaseIntegrand β N h k ξ' η' hξ' hη')
  have hG0 : IntegrableOn (fun u : Fin d → ℝ =>
      (fun _ : Fin d → ℝ => (1 : ℝ)) u *
        ((∏ i, u i ^ h i) * quadKernel β ((fun _ => M) u) (N * ∏ i, u i ^ k i))) (unitBox d) :=
    integrableOn_unitBox_of_continuous _
      (continuous_phaseIntegrand β N h k (fun _ => M) (fun _ => 1) continuous_const
        continuous_const)
  have hG1 : IntegrableOn (fun u : Fin d → ℝ => (∏ i, u i ^ h i) * ((N * ∏ i, u i ^ k i) *
      quadKernel β M (N * ∏ i, u i ^ k i))) (unitBox d) := by
    refine integrableOn_unitBox_of_continuous _ ?_
    have hP := continuous_prod_pow k
    have hQ : Continuous fun u : Fin d → ℝ => quadKernel β M (N * ∏ i, u i ^ k i) := by
      unfold quadKernel
      exact Real.continuous_exp.comp ((continuous_const.mul ((continuous_const.mul hP).pow 2)).add
        (continuous_const.mul (continuous_const.mul hP)))
    exact (continuous_prod_pow h).mul ((continuous_const.mul hP).mul hQ)
  have hbd : IntegrableOn (fun u : Fin d → ℝ => δη *
      ((fun _ : Fin d → ℝ => (1 : ℝ)) u *
        ((∏ i, u i ^ h i) * quadKernel β ((fun _ => M) u) (N * ∏ i, u i ^ k i))) +
      β * A * δξ * ((∏ i, u i ^ h i) * ((N * ∏ i, u i ^ k i) *
        quadKernel β M (N * ∏ i, u i ^ k i)))) (unitBox d) :=
    (hG0.const_mul _).add (hG1.const_mul _)
  have hpt : ∀ᵐ u ∂(volume.restrict (unitBox d)),
      ‖η u * ((∏ i, u i ^ h i) * quadKernel β (ξ u) (N * ∏ i, u i ^ k i)) -
        η' u * ((∏ i, u i ^ h i) * quadKernel β (ξ' u) (N * ∏ i, u i ^ k i))‖ ≤
      δη * ((fun _ : Fin d → ℝ => (1 : ℝ)) u *
        ((∏ i, u i ^ h i) * quadKernel β ((fun _ => M) u) (N * ∏ i, u i ^ k i))) +
      β * A * δξ * ((∏ i, u i ^ h i) * ((N * ∏ i, u i ^ k i) *
        quadKernel β M (N * ∏ i, u i ^ k i))) := by
    refine (ae_restrict_iff' (measurableSet_unitBox _)).2 (Eventually.of_forall fun u hu => ?_)
    have huc : u ∈ closedCube d := unitBox_subset_closedCube _ hu
    have hs0 : 0 ≤ N * ∏ i, u i ^ k i :=
      mul_nonneg hN (Finset.prod_nonneg fun i _ => pow_nonneg (hu i (mem_univ i)).1.le _)
    have huh : 0 ≤ ∏ i, u i ^ h i :=
      Finset.prod_nonneg fun i _ => pow_nonneg (hu i (mem_univ i)).1.le _
    set s := N * ∏ i, u i ^ k i with hs
    set P := ∏ i, u i ^ h i with hP
    have hK := quadKernel_sub_le β (ξ u) (ξ' u) M s hβ hs0 (hξM u huc) (hξ'M u huc)
    have hKle := quadKernel_le_of_le β (ξ u) M s hβ hs0 ((le_abs_self _).trans (hξM u huc))
    have hKpos := quadKernel_pos β (ξ u) s
    have hKM := quadKernel_pos β M s
    -- ηK − η'K' = (η − η')K + η'(K − K')
    have hdecomp : η u * (P * quadKernel β (ξ u) s) - η' u * (P * quadKernel β (ξ' u) s) =
        (η u - η' u) * (P * quadKernel β (ξ u) s) +
          η' u * (P * (quadKernel β (ξ u) s - quadKernel β (ξ' u) s)) := by ring
    rw [Real.norm_eq_abs, hdecomp]
    calc |(η u - η' u) * (P * quadKernel β (ξ u) s) +
          η' u * (P * (quadKernel β (ξ u) s - quadKernel β (ξ' u) s))|
        ≤ |η u - η' u| * (P * quadKernel β (ξ u) s) +
          |η' u| * (P * |quadKernel β (ξ u) s - quadKernel β (ξ' u) s|) := by
          refine (abs_add_le _ _).trans ?_
          rw [abs_mul, abs_mul, abs_mul, abs_mul, abs_of_nonneg huh, abs_of_pos hKpos]
      _ ≤ δη * (P * quadKernel β M s) + A * (P * (β * s * |ξ u - ξ' u| * quadKernel β M s)) := by
          gcongr
          · exact hδη u huc
          · exact hη'A u huc
      _ ≤ δη * (P * quadKernel β M s) + A * (P * (β * s * δξ * quadKernel β M s)) := by
          gcongr
          exact hδξ u huc
      _ = δη * ((fun _ : Fin d → ℝ => (1 : ℝ)) u * (P * quadKernel β M s)) +
          β * A * δξ * (P * (s * quadKernel β M s)) := by
          beta_reduce
          ring
  have hnorm := norm_integral_le_of_norm_le hbd hpt
  rw [Real.norm_eq_abs, integral_add (hG0.const_mul _) (hG1.const_mul _),
    integral_const_mul (β * A * δξ), integral_const_mul δη] at hnorm
  unfold chartIntegral
  rw [← integral_sub hI hI']
  refine hnorm.trans (le_of_eq ?_)
  rw [chartIntegral_shift_mul]
  unfold chartIntegral
  rfl

/-- The normalising scale. -/
noncomputable def leadScale {d : ℕ} (h k : Fin d → ℕ) (l N : ℝ) : ℝ :=
  N ^ (-(2 * l)) * Real.log N ^ (multCount (ratioExp h k) l - 1)

/-- `G₁(N)/S_N → phaseCoeff (h+k) k (λ+1/2) β M 1`. -/
theorem shifted_const_phase_tendsto (d : ℕ) (h k : Fin (d + 1) → ℕ) (hk : ∀ i, 0 < k i) (l β M : ℝ)
    (hl : 0 < l) (hβ : 0 < β) (hmin : ∀ i, l ≤ ratioExp h k i) (hatt : ∃ i, ratioExp h k i = l) :
    Tendsto (fun N : ℝ =>
        N * chartIntegral (d + 1) (phaseShift h k 1) k β N (fun _ => M) (fun _ => 1) /
          leadScale h k l N) atTop
      (𝓝 (phaseCoeff (phaseShift h k 1) k (l + 1 / 2) β (fun _ => M) (fun _ => 1))) := by
  have hmin' : ∀ i, l + 1 / 2 ≤ ratioExp (phaseShift h k 1) k i := fun i => by
    rw [ratioExp_phaseShift h k hk 1 i]
    have := hmin i
    push_cast
    linarith
  have hatt' : ∃ i, ratioExp (phaseShift h k 1) k i = l + 1 / 2 := by
    obtain ⟨i, hi⟩ := hatt
    exact ⟨i, by rw [ratioExp_phaseShift h k hk 1 i, hi]; push_cast; ring⟩
  have hT := phase_leading_tendsto d (phaseShift h k 1) k hk (l + 1 / 2) β (by positivity) hβ hmin'
    hatt' (fun _ => M) (fun _ => 1) continuous_const continuous_const
  have hm : multCount (ratioExp (phaseShift h k 1) k) (l + 1 / 2) = multCount (ratioExp h k) l := by
    have := multCount_phaseShift h k hk 1 l
    push_cast at this
    exact this
  rw [hm] at hT
  refine hT.congr' ?_
  filter_upwards [eventually_gt_atTop (1 : ℝ)] with N hN
  have hN0 : 0 < N := by linarith
  unfold leadScale chartIntegral
  have h1 : N ^ (-(2 * (l + 1 / 2))) = N ^ (-(2 * l)) * N⁻¹ := by
    rw [show -(2 * (l + 1 / 2)) = -(2 * l) + (-1 : ℝ) by ring, Real.rpow_add hN0,
      Real.rpow_neg_one]
  rw [h1]
  have hpow : N ^ (-(2 * l)) ≠ 0 := (Real.rpow_pos_of_pos hN0 _).ne'
  have hlog : Real.log N ^ (multCount (ratioExp h k) l - 1) ≠ 0 :=
    pow_ne_zero _ (Real.log_pos hN).ne'
  field_simp

/-- **Eventual equi-Lipschitz estimate for the normalised chart integral**: there is `L` depending
only on `(h, k, β, M, A)` such that, for all large `N` and all continuous inputs bounded by `M`
(phases) and `A` (the second amplitude) on the closed cube,
`|F_N(ξ,η) − F_N(ξ',η')| ≤ L (δξ + δη)` whenever `|ξ − ξ'| ≤ δξ`, `|η − η'| ≤ δη` on the cube. -/
theorem normalised_lipschitz_eventually (d : ℕ) (h k : Fin (d + 1) → ℕ) (hk : ∀ i, 0 < k i)
    (l β M A : ℝ) (hl : 0 < l) (hβ : 0 < β) (hmin : ∀ i, l ≤ ratioExp h k i)
    (hatt : ∃ i, ratioExp h k i = l) :
    ∃ L : ℝ, 0 ≤ L ∧ ∀ᶠ N in atTop, ∀ (ξ ξ' η η' : (Fin (d + 1) → ℝ) → ℝ) (δξ δη : ℝ),
      Continuous ξ → Continuous ξ' → Continuous η → Continuous η' →
      (∀ x ∈ closedCube (d + 1), |ξ x| ≤ M) → (∀ x ∈ closedCube (d + 1), |ξ' x| ≤ M) →
      (∀ x ∈ closedCube (d + 1), |η' x| ≤ A) →
      (∀ x ∈ closedCube (d + 1), |ξ x - ξ' x| ≤ δξ) →
      (∀ x ∈ closedCube (d + 1), |η x - η' x| ≤ δη) →
      |chartIntegral (d + 1) h k β N ξ η / leadScale h k l N -
        chartIntegral (d + 1) h k β N ξ' η' / leadScale h k l N| ≤ L * (δξ + δη) := by
  have hG0 := phase_leading_tendsto d h k hk l β hl hβ hmin hatt (fun _ => M) (fun _ => 1)
    continuous_const continuous_const
  have hG1 := shifted_const_phase_tendsto d h k hk l β M hl hβ hmin hatt
  obtain ⟨C₀, hC₀⟩ : ∃ C, C = phaseCoeff h k l β (fun _ => M) (fun _ => 1) := ⟨_, rfl⟩
  obtain ⟨C₁, hC₁⟩ : ∃ C,
      C = phaseCoeff (phaseShift h k 1) k (l + 1 / 2) β (fun _ => M) (fun _ => 1) := ⟨_, rfl⟩
  refine ⟨(|C₀| + 1) + β * |A| * (|C₁| + 1), by positivity, ?_⟩
  have hev0 : ∀ᶠ N in atTop, chartIntegral (d + 1) h k β N (fun _ => M) (fun _ => 1) /
      leadScale h k l N ≤ |C₀| + 1 := by
    rw [← hC₀] at hG0
    exact hG0.eventually (eventually_le_nhds (by linarith [le_abs_self C₀]))
  have hev1 : ∀ᶠ N in atTop, N * chartIntegral (d + 1) (phaseShift h k 1) k β N (fun _ => M)
      (fun _ => 1) / leadScale h k l N ≤ |C₁| + 1 := by
    rw [← hC₁] at hG1
    exact hG1.eventually (eventually_le_nhds (by linarith [le_abs_self C₁]))
  filter_upwards [eventually_gt_atTop (1 : ℝ), hev0, hev1] with N hN hb0 hb1
  intro ξ ξ' η η' δξ δη hξ hξ' hη hη' hξM hξ'M hη'A hδξ hδη
  have hN0 : 0 < N := by linarith
  have hS : 0 < leadScale h k l N :=
    mul_pos (Real.rpow_pos_of_pos hN0 _) (pow_pos (Real.log_pos hN) _)
  have hA0 : 0 ≤ A := (abs_nonneg _).trans (hη'A 0 fun i _ => ⟨le_rfl, zero_le_one⟩)
  have hδξ0 : 0 ≤ δξ := (abs_nonneg _).trans (hδξ 0 fun i _ => ⟨le_rfl, zero_le_one⟩)
  have hδη0 : 0 ≤ δη := (abs_nonneg _).trans (hδη 0 fun i _ => ⟨le_rfl, zero_le_one⟩)
  have hmain := chartIntegral_sub_le (d + 1) h k β N M A δξ δη hβ hN0.le ξ ξ' η η' hξ hξ' hη hη'
    hξM hξ'M hη'A hδξ hδη
  rw [← sub_div, abs_div, abs_of_pos hS, div_le_iff₀ hS]
  have hG0le : chartIntegral (d + 1) h k β N (fun _ => M) (fun _ => 1) ≤
      (|C₀| + 1) * leadScale h k l N := by rwa [div_le_iff₀ hS] at hb0
  have hG1le : N * chartIntegral (d + 1) (phaseShift h k 1) k β N (fun _ => M) (fun _ => 1) ≤
      (|C₁| + 1) * leadScale h k l N := by rwa [div_le_iff₀ hS] at hb1
  have hA' : |A| = A := abs_of_nonneg hA0
  have e1 : 0 ≤ leadScale h k l N * ((|C₀| + 1) * δξ) := by positivity
  have e2 : 0 ≤ leadScale h k l N * (β * A * (|C₁| + 1) * δη) := by positivity
  calc |chartIntegral (d + 1) h k β N ξ η - chartIntegral (d + 1) h k β N ξ' η'|
      ≤ δη * chartIntegral (d + 1) h k β N (fun _ => M) (fun _ => 1) +
        β * A * δξ *
          (N * chartIntegral (d + 1) (phaseShift h k 1) k β N (fun _ => M) (fun _ => 1)) :=
        hmain
    _ ≤ δη * ((|C₀| + 1) * leadScale h k l N) + β * A * δξ * ((|C₁| + 1) * leadScale h k l N) := by
        gcongr
    _ ≤ ((|C₀| + 1) + β * |A| * (|C₁| + 1)) * (δξ + δη) * leadScale h k l N := by
        rw [hA']
        nlinarith [e1, e2]

end Laplace.Grammar
