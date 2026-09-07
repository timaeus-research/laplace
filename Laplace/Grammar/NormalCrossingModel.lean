/-
Copyright (c) 2026 Timaeus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Laplace.Grammar.HeadlineSymmetricPhase
import Laplace.Grammar.PhaseLipschitz
import Laplace.Grammar.PhasePosterior
import Mathlib.Probability.Distributions.Gaussian.Real

/-!
# An end-to-end normal-crossing example: the model `N(x₀x₁, 1)`

Unit 218 (Astra #24, programme H2-lite). Observations `y₁,…,yₙ` are modelled as `N(x₀x₁, 1)`
with parameter `x = (x₀,x₁)` in the symmetric box `(-1,1]²` and a continuous prior density `ρ`.
Against the truth `N(0,1)` the likelihood ratio is **exactly** the phase-dressed normal-crossing
kernel of the grammar paper:
```
∏ᵢ φ(yᵢ - x₀x₁) / ∏ᵢ φ(yᵢ) = exp(-(n/2)(x₀x₁)² + √n Zₙ x₀x₁),   Zₙ = n^{-1/2} ∑ yᵢ,
```
i.e. `β = 1/2`, `N = √n`, `h = 0`, `k = (1,1)`, phase `ξ = 2Zₙ` (`ncLikelihood_eq`). No
resolution of singularities, no likelihood remainder and no empirical-process limit is needed: the
four-quadrant decomposition is `symBox_phase_eq_sum` and the phase `Zₙ` is a datum.

The fluctuation variable is `√n x₀x₁`; its posterior moment generating function is a ratio of two
such integrals with phases `2Zₙ + 2θ` and `2Zₙ` (`ncKernel_tilt`). Headline XIX (moving-phase form
`chart_const_phase_tendsto_moving`) and the closed form `J₁(a) + J₁(-a) = √(π/β) e^{βa²/4}`
give the **end-to-end theorem** (`ncFluctMGF_tendsto`): along any data sequence with `Zₙ → z`,
```
E_post[exp(θ √n x₀x₁)] → exp(zθ + θ²/2),
```
the moment generating function of `N(z, 1)`: at each fixed `θ` the posterior moment generating
function of `√n x₀x₁` is asymptotically that of `N(Zₙ, 1)`, centred at the empirical score `Zₙ`
(weak convergence of the posterior law and rates are not asserted). The analytic statement needs only
`ρ(0) > 0` and allows signed weights; for a genuine prior (`ρ ≥ 0` on the box) the evidence is
positive at every sample size, see `NormalCrossingPrior.lean`. Zero `sorry`/`axiom`.
-/

open MeasureTheory Filter Topology Real Set ProbabilityTheory

namespace Laplace.Grammar

/-! ### The full-line Gaussian with linear term -/

/-- Completing the square: `-βs² + βas = -β(s - a/2)² + βa²/4`. -/
theorem quadKernel_eq_shift (β a s : ℝ) :
    quadKernel β a s = Real.exp (β * a ^ 2 / 4) * Real.exp (-β * (s - a / 2) ^ 2) := by
  unfold quadKernel
  rw [← Real.exp_add]
  congr 1
  ring

theorem integrable_quadKernel (β a : ℝ) (hβ : 0 < β) : Integrable (quadKernel β a) := by
  have h := ((integrable_exp_neg_mul_sq hβ).comp_sub_right (a / 2)).const_mul
    (Real.exp (β * a ^ 2 / 4))
  exact h.congr (ae_of_all _ fun s => (quadKernel_eq_shift β a s).symm)

/-- `∫_ℝ e^{-βs²+βas} ds = √(π/β) e^{βa²/4}`. -/
theorem integral_quadKernel (β a : ℝ) :
    ∫ s, quadKernel β a s = Real.sqrt (Real.pi / β) * Real.exp (β * a ^ 2 / 4) := by
  simp only [quadKernel_eq_shift β a]
  rw [integral_const_mul]
  rw [integral_sub_right_eq_self (μ := volume) (fun s : ℝ => Real.exp (-β * s ^ 2)) (a / 2),
    integral_gaussian, mul_comm]

/-- The two half-line moments at `p = 1` with opposite phases sum to the full-line Gaussian:
`J₁(a) + J₁(-a) = √(π/β) e^{βa²/4}`. -/
theorem phaseMoment_one_add_neg (β a : ℝ) (hβ : 0 < β) :
    phaseMoment β 1 a + phaseMoment β 1 (-a) =
      Real.sqrt (Real.pi / β) * Real.exp (β * a ^ 2 / 4) := by
  have h1 : ∀ b, phaseMoment β 1 b = ∫ s in Ioi (0 : ℝ), quadKernel β b s := fun b => by
    unfold phaseMoment
    refine setIntegral_congr_fun measurableSet_Ioi fun s _ => ?_
    simp
  have hneg : ∫ s in Ioi (0 : ℝ), quadKernel β (-a) s = ∫ s in Iic (0 : ℝ), quadKernel β a s := by
    have : ∀ s, quadKernel β (-a) s = quadKernel β a (-s) := fun s => by
      unfold quadKernel
      congr 1
      ring
    simp only [this]
    rw [integral_comp_neg_Ioi, neg_zero]
  rw [h1, h1, hneg, add_comm, intervalIntegral.integral_Iic_add_Ioi
    (integrable_quadKernel β a hβ).integrableOn (integrable_quadKernel β a hβ).integrableOn,
    integral_quadKernel β a]

/-! ### Moving constant phases -/

/-- **Moving constant phase.** If `cₙ → c₀` and `Nₙ → ∞`, the normalised chart integral with the
constant phase `cₙ` converges to the leading coefficient at `c₀` (eventual Lipschitz dependence on
the phase plus the fixed-phase limit). -/
theorem chart_const_phase_tendsto_moving (d : ℕ) (h k : Fin (d + 1) → ℕ) (hk : ∀ i, 0 < k i)
    (l β : ℝ) (hl : 0 < l) (hβ : 0 < β) (hmin : ∀ i, l ≤ ratioExp h k i)
    (hatt : ∃ i, ratioExp h k i = l) (η : (Fin (d + 1) → ℝ) → ℝ) (hη : Continuous η)
    (Nseq : ℕ → ℝ) (hN : Tendsto Nseq atTop atTop) (c : ℕ → ℝ) (c₀ : ℝ)
    (hc : Tendsto c atTop (𝓝 c₀)) :
    Tendsto (fun n => chartIntegral (d + 1) h k β (Nseq n) (fun _ => c n) η /
      leadScale h k l (Nseq n)) atTop (𝓝 (phaseCoeff h k l β (fun _ => c₀) η)) := by
  obtain ⟨A, -, hA⟩ := exists_bound_closedCube η hη
  obtain ⟨L, -, hL⟩ := normalised_lipschitz_eventually d h k hk l β (|c₀| + 1) A hl hβ hmin hatt
  have hpt : Tendsto (fun n => chartIntegral (d + 1) h k β (Nseq n) (fun _ => c₀) η /
      leadScale h k l (Nseq n)) atTop (𝓝 (phaseCoeff h k l β (fun _ => c₀) η)) :=
    (phase_leading_tendsto d h k hk l β hl hβ hmin hatt (fun _ => c₀) η continuous_const hη).comp hN
  have hc0 : Tendsto (fun n => c n - c₀) atTop (𝓝 0) := by
    simpa using hc.sub_const c₀
  have h1 : ∀ᶠ n in atTop, |c n - c₀| ≤ 1 := by
    have := (Metric.tendsto_nhds.mp hc0) 1 one_pos
    filter_upwards [this] with n hn
    rw [Real.dist_eq, sub_zero] at hn
    exact hn.le
  have hdiff : Tendsto (fun n => chartIntegral (d + 1) h k β (Nseq n) (fun _ => c n) η /
      leadScale h k l (Nseq n) - chartIntegral (d + 1) h k β (Nseq n) (fun _ => c₀) η /
      leadScale h k l (Nseq n)) atTop (𝓝 0) := by
    refine squeeze_zero_norm' (a := fun n => L * (|c n - c₀| + 0)) ?_ ?_
    · filter_upwards [hN.eventually hL, h1] with n hLn hcn
      rw [Real.norm_eq_abs]
      refine hLn (fun _ => c n) (fun _ => c₀) η η (|c n - c₀|) 0 continuous_const continuous_const
        hη hη (fun x _ => ?_) (fun x _ => ?_) (fun x hx => hA x hx) (fun x _ => le_rfl)
        (fun x _ => by simp)
      · calc |c n| = |c₀ + (c n - c₀)| := by ring_nf
          _ ≤ |c₀| + |c n - c₀| := abs_add_le _ _
          _ ≤ |c₀| + 1 := by linarith
      · linarith [abs_nonneg c₀]
    · have : Tendsto (fun n => L * (|c n - c₀| + 0)) atTop (𝓝 (L * (|(0 : ℝ)| + 0))) :=
        tendsto_const_nhds.mul (hc0.abs.add tendsto_const_nhds)
      simpa using this
  have := hdiff.add hpt
  rw [zero_add] at this
  exact this.congr fun n => by ring

/-! ### The statistical model -/

/-- The likelihood of the data `y` under the model `N(x₀x₁, 1)` at the parameter `x`. -/
noncomputable def ncLikelihood (n : ℕ) (y : Fin n → ℝ) (x : Fin 2 → ℝ) : ℝ :=
  ∏ i, gaussianPDFReal (x 0 * x 1) 1 (y i)

/-- The empirical phase `Zₙ = n^{-1/2} ∑ᵢ yᵢ`. -/
noncomputable def ncPhase (n : ℕ) (y : Fin n → ℝ) : ℝ := (∑ i, y i) / Real.sqrt n

/-- The normal-crossing kernel of the model: `exp(-(N x₀x₁)²/2 + N z x₀x₁)`. -/
noncomputable def ncKernel (N z : ℝ) (x : Fin 2 → ℝ) : ℝ :=
  Real.exp (-(N ^ 2 * (x 0 * x 1) ^ 2) / 2 + N * z * (x 0 * x 1))

/-- Posterior mean of `φ` under the prior density `ρ` on the symmetric box `(-1,1]²`. -/
noncomputable def ncPosteriorMean (n : ℕ) (y : Fin n → ℝ) (ρ φ : (Fin 2 → ℝ) → ℝ) : ℝ :=
  (∫ x in symBox 2, φ x * ρ x * ncLikelihood n y x) / ∫ x in symBox 2, ρ x * ncLikelihood n y x

/-- Posterior moment generating function of the fluctuation variable `√n x₀x₁`. -/
noncomputable def ncFluctMGF (n : ℕ) (y : Fin n → ℝ) (ρ : (Fin 2 → ℝ) → ℝ) (θ : ℝ) : ℝ :=
  ncPosteriorMean n y ρ (fun x => Real.exp (θ * (Real.sqrt n * (x 0 * x 1))))

/-- **Exact likelihood identity**: the likelihood factorises as the truth's likelihood (constant in
`x`) times the normal-crossing kernel at `N = √n`, phase `Zₙ`. -/
theorem ncLikelihood_eq (n : ℕ) (hn : 0 < n) (y : Fin n → ℝ) (x : Fin 2 → ℝ) :
    ncLikelihood n y x =
      (∏ i, gaussianPDFReal 0 1 (y i)) * ncKernel (Real.sqrt n) (ncPhase n y) x := by
  have hsqrt : Real.sqrt n ≠ 0 := by
    rw [Ne, Real.sqrt_eq_zero']
    push Not
    exact_mod_cast hn
  have hsz : Real.sqrt n * ncPhase n y = ∑ i, y i := by
    unfold ncPhase
    field_simp
  have hN2 : Real.sqrt n ^ 2 = n := Real.sq_sqrt (Nat.cast_nonneg n)
  unfold ncLikelihood ncKernel
  simp only [gaussianPDFReal_def, NNReal.coe_one, mul_one]
  rw [Finset.prod_mul_distrib, Finset.prod_mul_distrib, ← Real.exp_sum, ← Real.exp_sum, mul_assoc,
    ← Real.exp_add]
  congr 2
  have key : ∀ i, -(y i - x 0 * x 1) ^ 2 / 2 =
      -(y i - 0) ^ 2 / 2 + (y i * (x 0 * x 1) - (x 0 * x 1) ^ 2 / 2) := fun i => by ring
  simp only [key, Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.sum_mul,
    Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  rw [show Real.sqrt n * ncPhase n y * (x 0 * x 1) = (Real.sqrt n * ncPhase n y) * (x 0 * x 1) by
    ring, hsz, hN2]
  ring

/-- The truth's likelihood cancels: the posterior mean is a ratio of kernel integrals. -/
theorem ncPosteriorMean_eq (n : ℕ) (hn : 0 < n) (y : Fin n → ℝ) (ρ φ : (Fin 2 → ℝ) → ℝ) :
    ncPosteriorMean n y ρ φ =
      (∫ x in symBox 2, φ x * ρ x * ncKernel (Real.sqrt n) (ncPhase n y) x) /
        ∫ x in symBox 2, ρ x * ncKernel (Real.sqrt n) (ncPhase n y) x := by
  have hC : 0 < ∏ i, gaussianPDFReal 0 1 (y i) :=
    Finset.prod_pos fun i _ => gaussianPDFReal_pos _ _ _ one_ne_zero
  unfold ncPosteriorMean
  simp only [ncLikelihood_eq n hn y]
  have h1 : ∫ x in symBox 2, φ x * ρ x * ((∏ i, gaussianPDFReal 0 1 (y i)) *
      ncKernel (Real.sqrt n) (ncPhase n y) x) = (∏ i, gaussianPDFReal 0 1 (y i)) *
      ∫ x in symBox 2, φ x * ρ x * ncKernel (Real.sqrt n) (ncPhase n y) x := by
    rw [← integral_const_mul]
    exact integral_congr_ae (ae_of_all _ fun x => by ring)
  have h2 : ∫ x in symBox 2, ρ x * ((∏ i, gaussianPDFReal 0 1 (y i)) *
      ncKernel (Real.sqrt n) (ncPhase n y) x) = (∏ i, gaussianPDFReal 0 1 (y i)) *
      ∫ x in symBox 2, ρ x * ncKernel (Real.sqrt n) (ncPhase n y) x := by
    rw [← integral_const_mul]
    exact integral_congr_ae (ae_of_all _ fun x => by ring)
  rw [h1, h2, mul_div_mul_left _ _ hC.ne']

/-- The exponential tilt by the fluctuation variable shifts the phase:
`e^{θ N x₀x₁} K_z = K_{z+θ}`. -/
theorem ncKernel_tilt (N z θ : ℝ) (x : Fin 2 → ℝ) :
    Real.exp (θ * (N * (x 0 * x 1))) * ncKernel N z x = ncKernel N (z + θ) x := by
  unfold ncKernel
  rw [← Real.exp_add]
  congr 1
  ring

/-- The model kernel is the paper's kernel with `β = 1/2`, `h = 0`, `k = (1,1)`, phase `2z`. -/
theorem ncKernel_eq (N z : ℝ) (x : Fin 2 → ℝ) :
    ncKernel N z x = (∏ i, x i ^ (fun _ : Fin 2 => (0 : ℕ)) i) *
      quadKernel (1 / 2) ((fun _ : Fin 2 → ℝ => 2 * z) x)
        (N * ∏ i, x i ^ (fun _ : Fin 2 => 1) i) := by
  simp only [pow_zero, Finset.prod_const_one, one_mul, pow_one, Fin.prod_univ_two]
  unfold ncKernel quadKernel
  congr 1
  ring

/-! ### The limit of the model integrals -/

theorem reflect_zero {d : ℕ} (σ : Fin d → Bool) : reflect σ 0 = 0 := by
  funext i
  simp [reflect]

theorem nc_ratioExp (i : Fin 2) :
    ratioExp (fun _ : Fin 2 => (0 : ℕ)) (fun _ : Fin 2 => (1 : ℕ)) i = 1 / 2 := by
  simp [ratioExp]

/-- The symmetric-box model integral as a sum over the four quadrants. -/
theorem nc_integral_eq_sum (ρ : (Fin 2 → ℝ) → ℝ) (hρ : Continuous ρ) (N z : ℝ) :
    ∫ x in symBox 2, ρ x * ncKernel N z x =
      ∑ σ : Fin 2 → Bool, chartIntegral 2 (fun _ => 0) (fun _ => 1) (1 / 2) N
        (fun _ => phaseSign (fun _ : Fin 2 => 1) σ * (2 * z))
        (fun u => phaseSign (fun _ : Fin 2 => 0) σ * ρ (reflect σ u)) := by
  have h := symBox_phase_eq_sum (1 / 2) N (fun _ : Fin 2 => (0 : ℕ)) (fun _ => 1)
    (fun _ => 2 * z) ρ continuous_const hρ
  rw [← h]
  exact integral_congr_ae (ae_of_all _ fun x => by beta_reduce; rw [ncKernel_eq])

/-- **Normalised model integral, moving phase.** Along `Nₙ → ∞` and `zₙ → z₀`,
`∫_{(-1,1]²} ρ K_{Nₙ,zₙ} / (Nₙ⁻¹ log Nₙ) → 2ρ(0) √(2π) e^{z₀²/2}`. -/
theorem nc_integral_tendsto (ρ : (Fin 2 → ℝ) → ℝ) (hρ : Continuous ρ) (Nseq : ℕ → ℝ)
    (hN : Tendsto Nseq atTop atTop) (z : ℕ → ℝ) (z₀ : ℝ) (hz : Tendsto z atTop (𝓝 z₀)) :
    Tendsto (fun n => (∫ x in symBox 2, ρ x * ncKernel (Nseq n) (z n) x) /
        leadScale (fun _ : Fin 2 => 0) (fun _ => 1) (1 / 2) (Nseq n)) atTop
      (𝓝 (2 * ρ 0 * (Real.sqrt (2 * Real.pi) * Real.exp (z₀ ^ 2 / 2)))) := by
  simp only [nc_integral_eq_sum ρ hρ, Finset.sum_div]
  have hσ : ∀ σ : Fin 2 → Bool, Tendsto (fun n => chartIntegral 2 (fun _ => 0) (fun _ => 1)
      (1 / 2) (Nseq n) (fun _ => phaseSign (fun _ : Fin 2 => 1) σ * (2 * z n))
      (fun u => phaseSign (fun _ : Fin 2 => 0) σ * ρ (reflect σ u)) /
      leadScale (fun _ : Fin 2 => 0) (fun _ => 1) (1 / 2) (Nseq n)) atTop
      (𝓝 (phaseCoeff (fun _ : Fin 2 => 0) (fun _ => 1) (1 / 2) (1 / 2)
        (fun _ => phaseSign (fun _ : Fin 2 => 1) σ * (2 * z₀))
        (fun u => phaseSign (fun _ : Fin 2 => 0) σ * ρ (reflect σ u)))) := fun σ =>
    chart_const_phase_tendsto_moving 1 (fun _ => 0) (fun _ => 1) (fun _ => one_pos) (1 / 2) (1 / 2)
      (by norm_num) (by norm_num) (fun i => (nc_ratioExp i).symm.le) ⟨0, nc_ratioExp 0⟩ _
      (continuous_const.mul (hρ.comp (continuous_reflect σ))) Nseq hN _ _
      ((hz.const_mul 2).const_mul _)
  have hsum := tendsto_finsetSum Finset.univ fun σ _ => hσ σ
  convert hsum using 2
  simp only [phaseCoeff_equal 1 (fun _ : Fin 2 => (0 : ℕ)) (fun _ => 1) (1 / 2) (1 / 2)
    nc_ratioExp]
  rw [← (piFinTwoEquiv fun _ => Bool).symm.sum_comp, Fintype.sum_prod_type]
  simp only [Fintype.sum_bool, piFinTwoEquiv, Equiv.coe_fn_symm_mk, phaseSign, Fin.prod_univ_two,
    Fin.cons_zero, Fin.cons_one, reflect_zero, sgn, Nat.factorial_one, Nat.cast_one]
  simp only [Bool.false_eq_true, ↓reduceIte, pow_zero, pow_one, mul_one, one_mul,
    neg_mul, neg_neg, mul_neg]
  have hM := phaseMoment_one_add_neg (1 / 2) (2 * z₀) (by norm_num)
  rw [show Real.pi / (1 / 2) = 2 * Real.pi by ring, show (1 / 2 : ℝ) * (2 * z₀) ^ 2 / 4 = z₀ ^ 2 / 2
    by ring] at hM
  rw [← hM]
  ring_nf

/-! ### The end-to-end theorem -/

/-- **End-to-end normal-crossing example.** For the model `N(x₀x₁, 1)` on `(-1,1]²` with a
continuous prior density `ρ`, `ρ(0) > 0`, and data `yₙ` whose empirical phase
`Zₙ = n^{-1/2} ∑ yᵢ` converges to `z`, the posterior moment generating function of the
fluctuation variable `√n x₀x₁` converges to that of `N(z, 1)`:
`E_post[e^{θ √n x₀x₁}] → e^{zθ + θ²/2}`. -/
theorem ncFluctMGF_tendsto (ρ : (Fin 2 → ℝ) → ℝ) (hρ : Continuous ρ) (hρ0 : 0 < ρ 0) (θ z : ℝ)
    (y : (n : ℕ) → Fin n → ℝ) (hz : Tendsto (fun n => ncPhase n (y n)) atTop (𝓝 z)) :
    Tendsto (fun n => ncFluctMGF n (y n) ρ θ) atTop (𝓝 (Real.exp (z * θ + θ ^ 2 / 2))) := by
  have hN : Tendsto (fun n : ℕ => Real.sqrt n) atTop atTop :=
    Real.tendsto_sqrt_atTop.comp tendsto_natCast_atTop_atTop
  have hden := nc_integral_tendsto ρ hρ _ hN _ z hz
  have hnum := nc_integral_tendsto ρ hρ _ hN (fun n => ncPhase n (y n) + θ) (z + θ)
    (hz.add_const θ)
  have hpos : (0 : ℝ) < 2 * ρ 0 * (Real.sqrt (2 * Real.pi) * Real.exp (z ^ 2 / 2)) := by
    positivity
  have hlim := hnum.div hden hpos.ne'
  have hratio : 2 * ρ 0 * (Real.sqrt (2 * Real.pi) * Real.exp ((z + θ) ^ 2 / 2)) /
      (2 * ρ 0 * (Real.sqrt (2 * Real.pi) * Real.exp (z ^ 2 / 2))) =
      Real.exp (z * θ + θ ^ 2 / 2) := by
    rw [mul_div_mul_left _ _ (by positivity), mul_div_mul_left _ _ (by positivity), ← Real.exp_sub]
    congr 1
    ring
  rw [hratio] at hlim
  refine hlim.congr' ?_
  filter_upwards [eventually_gt_atTop 0, hN.eventually (eventually_gt_atTop 1)] with n hn hN1
  have hS : leadScale (fun _ : Fin 2 => (0 : ℕ)) (fun _ => 1) (1 / 2) (Real.sqrt n) ≠ 0 := by
    unfold leadScale
    exact (mul_pos (Real.rpow_pos_of_pos (by linarith) _)
      (pow_pos (Real.log_pos hN1) _)).ne'
  simp only [Pi.div_apply]
  rw [div_div_div_cancel_right₀ hS, ncFluctMGF, ncPosteriorMean_eq n hn]
  congr 1
  exact integral_congr_ae (ae_of_all _ fun x => by
    beta_reduce
    rw [← ncKernel_tilt]
    ring)

end Laplace.Grammar
