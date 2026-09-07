/-
Copyright (c) 2026 Timaeus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Laplace.Grammar.NormalCrossingModel
import Mathlib.Probability.Moments.Variance
import Mathlib.Probability.HasLaw
import Mathlib.Probability.Independence.Basic
import Mathlib.MeasureTheory.Function.ConvergenceInMeasure

/-!
# The normal-crossing example with Gaussian data

Unit 219 (Astra #24, programme H2-lite, step 2). Unit 218 proved the posterior moment generating
function limit along data sequences whose empirical phase `Zₙ` converges. Here the data are random:
`Yᵢ` i.i.d. `N(0,1)` (the truth), so `Zₙ = n^{-1/2} ∑_{i<n} Yᵢ` has mean `0` and variance `1` for
every `n ≥ 1`, and Chebyshev gives tightness. Combined with **uniform convergence on compact phase
sets** of the posterior moment generating function (eventual equi-Lipschitz dependence on the phase
plus the pointwise limit; `tendstoUniformlyOn_ncRatio`) this yields the **in-probability statement**
(`ncFluctMGF_tendstoInMeasure`):
```
E_post[exp(θ √n x₀x₁)] - exp(Zₙ θ + θ²/2) → 0   in P-probability,
```
i.e. at each fixed `θ` the posterior moment generating function of `√n x₀x₁` is asymptotically that
of `N(Zₙ, 1)` with the random centre `Zₙ`. The tightness argument uses only the zero means, unit
variances and pairwise independence implied by the i.i.d. Gaussian hypotheses. Zero `sorry`/`axiom`.
-/

open MeasureTheory Filter Topology Real Set ProbabilityTheory

namespace Laplace.Grammar

/-! ### Uniform convergence on compact sets of the real line -/

/-- Eventual equi-Lipschitz maps converging pointwise on a compact set to a continuous limit
converge uniformly there (finite net). -/
theorem tendstoUniformlyOn_of_lipschitz_eventually {ι : Type*} {l : Filter ι} {F : ι → ℝ → ℝ}
    {f : ℝ → ℝ} {K : Set ℝ} (hK : IsCompact K) (L : ℝ) (hL : 0 ≤ L)
    (hF : ∀ᶠ n in l, ∀ x ∈ K, ∀ y ∈ K, |F n x - F n y| ≤ L * |x - y|)
    (hf : ContinuousOn f K) (hpt : ∀ x ∈ K, Tendsto (fun n => F n x) l (𝓝 (f x))) :
    TendstoUniformlyOn F f l K := by
  rw [Metric.tendstoUniformlyOn_iff]
  intro ε hε
  obtain ⟨δ₁, hδ₁, hunif⟩ := Metric.uniformContinuousOn_iff.mp
    (hK.uniformContinuousOn_of_continuous hf) (ε / 3) (by positivity)
  set δ : ℝ := min δ₁ (ε / (3 * (L + 1))) with hδ
  have hδpos : 0 < δ := lt_min hδ₁ (by positivity)
  obtain ⟨t, htK, htfin, hcover⟩ := finite_cover_balls_of_compact hK hδpos
  have hev : ∀ᶠ n in l, ∀ y ∈ t, dist (f y) (F n y) < ε / 3 := by
    rw [Filter.eventually_all_finite htfin]
    intro y hy
    exact (Metric.tendsto_nhds.mp (hpt y (htK hy)) (ε / 3) (by positivity)).mono fun n hn => by
      rw [dist_comm]; exact hn
  filter_upwards [hF, hev] with n hFn hevn
  intro x hx
  obtain ⟨y, hy, hxy⟩ := Set.mem_iUnion₂.mp (hcover hx)
  rw [Metric.mem_ball] at hxy
  have hyK := htK hy
  have h1 := hFn x hx y hyK
  have h2 := hevn y hy
  have h3 := hunif x hx y hyK (hxy.trans_le (min_le_left _ _))
  rw [Real.dist_eq] at h2 h3 hxy ⊢
  have hLδ : L * |x - y| ≤ L * (ε / (3 * (L + 1))) :=
    mul_le_mul_of_nonneg_left (hxy.le.trans (min_le_right _ _)) hL
  have hbound : L * (ε / (3 * (L + 1))) < ε / 3 := by
    rw [← mul_div_assoc, div_lt_div_iff₀ (by positivity) (by positivity)]
    nlinarith
  calc |f x - F n x| = |(f x - f y) + (f y - F n y) + (F n y - F n x)| := by ring_nf
    _ ≤ |f x - f y| + |f y - F n y| + |F n y - F n x| := abs_add_three _ _ _
    _ < ε / 3 + ε / 3 + ε / 3 := by
      rw [abs_sub_comm (F n y)]
      linarith
    _ = ε := by ring

/-- Uniform convergence of quotients when the limiting denominators are bounded below by a positive
constant and the limiting numerators are bounded. -/
theorem tendstoUniformlyOn_div_of_pos {ι : Type*} {l : Filter ι} {F G : ι → ℝ → ℝ} {f g : ℝ → ℝ}
    {K : Set ℝ} (hF : TendstoUniformlyOn F f l K) (hG : TendstoUniformlyOn G g l K) (B c : ℝ)
    (hB : 0 ≤ B) (hc : 0 < c) (hfB : ∀ x ∈ K, |f x| ≤ B) (hgc : ∀ x ∈ K, c ≤ g x) :
    TendstoUniformlyOn (fun n x => F n x / G n x) (fun x => f x / g x) l K := by
  rw [Metric.tendstoUniformlyOn_iff] at hF hG ⊢
  intro ε hε
  set η : ℝ := min (c / 2) (ε * c ^ 2 / (8 * (B + c))) with hη
  have hηpos : 0 < η := lt_min (by positivity) (by positivity)
  have hη1 : η ≤ c / 2 := min_le_left _ _
  have hη2 : η * (B + c) ≤ ε * c ^ 2 / 8 := by
    calc η * (B + c) ≤ ε * c ^ 2 / (8 * (B + c)) * (B + c) :=
          mul_le_mul_of_nonneg_right (min_le_right _ _) (by positivity)
      _ = ε * c ^ 2 / 8 := by field_simp
  have hηc : η * c ≤ ε * c ^ 2 / 8 := by nlinarith
  have hηB : η * B ≤ ε * c ^ 2 / 8 := by nlinarith
  filter_upwards [hF η hηpos, hG η hηpos] with n hFn hGn
  intro x hx
  have h1 := hFn x hx
  have h2 := hGn x hx
  rw [Real.dist_eq] at h1 h2 ⊢
  have hq := hgc x hx
  have hp := hfB x hx
  have hb : c / 2 ≤ G n x := by
    have := (abs_lt.mp h2).2
    linarith
  have hb0 : 0 < G n x := by linarith
  have hq0 : 0 < g x := by linarith
  rw [div_sub_div _ _ hq0.ne' hb0.ne', abs_div, abs_of_pos (mul_pos hq0 hb0),
    div_lt_iff₀ (mul_pos hq0 hb0)]
  have hsplit : f x * G n x - g x * F n x = f x * (G n x - g x) + g x * (f x - F n x) := by ring
  rw [hsplit]
  calc |f x * (G n x - g x) + g x * (f x - F n x)|
      ≤ |f x| * |G n x - g x| + g x * |f x - F n x| := by
        refine (abs_add_le _ _).trans ?_
        rw [abs_mul, abs_mul, abs_of_pos hq0]
    _ ≤ B * η + g x * η := by
        rw [abs_sub_comm (G n x)]
        gcongr
    _ = η * B + η * g x := by ring
    _ < ε * (g x * G n x) := by
        have hηg : η * g x ≤ ε * c / 8 * g x := by
          have : η ≤ ε * c / 8 := by
            have hc' : 0 < c := hc
            calc η = η * c / c := by field_simp
              _ ≤ ε * c ^ 2 / 8 / c := by gcongr
              _ = ε * c / 8 := by field_simp
          exact mul_le_mul_of_nonneg_right this hq0.le
        have hcq : ε * c ^ 2 / 8 ≤ ε * c / 8 * g x := by
          have : c ^ 2 ≤ c * g x := by nlinarith
          calc ε * c ^ 2 / 8 = ε / 8 * c ^ 2 := by ring
            _ ≤ ε / 8 * (c * g x) := by gcongr
            _ = ε * c / 8 * g x := by ring
        have hcb : ε * c / 8 * g x + ε * c / 8 * g x ≤ ε * (g x * G n x) / 2 := by
          have : ε * c / 8 * g x + ε * c / 8 * g x = ε * g x * (c / 4) := by ring
          rw [this]
          have : ε * g x * (c / 4) ≤ ε * g x * (G n x / 2) := by
            apply mul_le_mul_of_nonneg_left _ (by positivity)
            linarith
          linarith
        have hpos : 0 < ε * (g x * G n x) := by positivity
        linarith

/-! ### The model: normalised integrals and the moment generating function as a ratio -/

/-- The normalised model denominator `∫_{(-1,1]²} ρ K_{N,z} / (N⁻¹ log N)`. -/
noncomputable def ncNorm (ρ : (Fin 2 → ℝ) → ℝ) (N z : ℝ) : ℝ :=
  (∫ x in symBox 2, ρ x * ncKernel N z x) / leadScale (fun _ : Fin 2 => 0) (fun _ => 1) (1 / 2) N

/-- Its limit `2ρ(0)√(2π) e^{z²/2}`. -/
noncomputable def ncLimit (ρ : (Fin 2 → ℝ) → ℝ) (z : ℝ) : ℝ :=
  2 * ρ 0 * (Real.sqrt (2 * Real.pi) * Real.exp (z ^ 2 / 2))

/-- The posterior moment generating function as a function of the chart variable and the phase. -/
noncomputable def ncRatio (ρ : (Fin 2 → ℝ) → ℝ) (N z θ : ℝ) : ℝ :=
  (∫ x in symBox 2, ρ x * ncKernel N (z + θ) x) / ∫ x in symBox 2, ρ x * ncKernel N z x

theorem ncFluctMGF_eq (n : ℕ) (hn : 0 < n) (y : Fin n → ℝ) (ρ : (Fin 2 → ℝ) → ℝ) (θ : ℝ) :
    ncFluctMGF n y ρ θ = ncRatio ρ (Real.sqrt n) (ncPhase n y) θ := by
  rw [ncFluctMGF, ncPosteriorMean_eq n hn, ncRatio]
  congr 1
  exact integral_congr_ae (ae_of_all _ fun x => by
    beta_reduce
    rw [← ncKernel_tilt]
    ring)

theorem ncRatio_eq_div_ncNorm (ρ : (Fin 2 → ℝ) → ℝ) (N z θ : ℝ) (hN : 1 < N) :
    ncRatio ρ N z θ = ncNorm ρ N (z + θ) / ncNorm ρ N z := by
  have hS : leadScale (fun _ : Fin 2 => (0 : ℕ)) (fun _ => 1) (1 / 2) N ≠ 0 := by
    unfold leadScale
    exact (mul_pos (Real.rpow_pos_of_pos (by linarith) _) (pow_pos (Real.log_pos hN) _)).ne'
  rw [ncRatio, ncNorm, ncNorm, div_div_div_cancel_right₀ hS]

theorem abs_phaseSign {d : ℕ} (e : Fin d → ℕ) (σ : Fin d → Bool) : |phaseSign e σ| = 1 := by
  unfold phaseSign
  rw [Finset.abs_prod]
  exact Finset.prod_eq_one fun i _ => by rw [abs_pow, abs_sgn, one_pow]

/-- Eventual Lipschitz dependence of the normalised model integral on the phase, uniformly on
`[-M, M]`. -/
theorem ncNorm_lipschitz_eventually (ρ : (Fin 2 → ℝ) → ℝ) (hρ : Continuous ρ) (M : ℝ)
    (Nseq : ℕ → ℝ) (hN : Tendsto Nseq atTop atTop) :
    ∃ L : ℝ, 0 ≤ L ∧ ∀ᶠ n in atTop, ∀ z ∈ Icc (-M) M, ∀ z' ∈ Icc (-M) M,
      |ncNorm ρ (Nseq n) z - ncNorm ρ (Nseq n) z'| ≤ L * |z - z'| := by
  have hη : ∀ σ : Fin 2 → Bool,
      Continuous fun u => phaseSign (fun _ : Fin 2 => (0 : ℕ)) σ * ρ (reflect σ u) :=
    fun σ => continuous_const.mul (hρ.comp (continuous_reflect σ))
  have hA : ∀ σ : Fin 2 → Bool, ∃ A : ℝ, 0 ≤ A ∧ ∀ x ∈ closedCube 2,
      |phaseSign (fun _ : Fin 2 => (0 : ℕ)) σ * ρ (reflect σ x)| ≤ A :=
    fun σ => exists_bound_closedCube _ (hη σ)
  choose A _ hA using hA
  have hL : ∀ σ : Fin 2 → Bool, ∃ L : ℝ, 0 ≤ L ∧ ∀ᶠ N in atTop,
      ∀ (ξ ξ' η η' : (Fin (1 + 1) → ℝ) → ℝ) (δξ δη : ℝ),
      Continuous ξ → Continuous ξ' → Continuous η → Continuous η' →
      (∀ x ∈ closedCube (1 + 1), |ξ x| ≤ 2 * M) → (∀ x ∈ closedCube (1 + 1), |ξ' x| ≤ 2 * M) →
      (∀ x ∈ closedCube (1 + 1), |η' x| ≤ A σ) →
      (∀ x ∈ closedCube (1 + 1), |ξ x - ξ' x| ≤ δξ) →
      (∀ x ∈ closedCube (1 + 1), |η x - η' x| ≤ δη) →
      |chartIntegral (1 + 1) (fun _ => 0) (fun _ => 1) (1 / 2) N ξ η /
          leadScale (fun _ => 0) (fun _ => 1) (1 / 2) N -
        chartIntegral (1 + 1) (fun _ => 0) (fun _ => 1) (1 / 2) N ξ' η' /
          leadScale (fun _ => 0) (fun _ => 1) (1 / 2) N| ≤ L * (δξ + δη) :=
    fun σ => normalised_lipschitz_eventually 1 (fun _ => 0) (fun _ => 1) (fun _ => one_pos) (1 / 2)
      (1 / 2) (2 * M) (A σ) (by norm_num) (by norm_num) (fun i => (nc_ratioExp i).symm.le)
      ⟨0, nc_ratioExp 0⟩
  choose L hL0 hL using hL
  refine ⟨∑ σ, 2 * L σ, Finset.sum_nonneg fun σ _ => by linarith [hL0 σ], ?_⟩
  have hev : ∀ᶠ n in atTop, ∀ σ : Fin 2 → Bool, _ := Filter.eventually_all.2 fun σ =>
    hN.eventually (hL σ)
  filter_upwards [hev] with n hn
  intro z hz z' hz'
  have hzM : |2 * z| ≤ 2 * M := by
    rw [abs_mul, abs_two]
    exact mul_le_mul_of_nonneg_left (abs_le.2 hz) (by norm_num)
  have hz'M : |2 * z'| ≤ 2 * M := by
    rw [abs_mul, abs_two]
    exact mul_le_mul_of_nonneg_left (abs_le.2 hz') (by norm_num)
  unfold ncNorm
  rw [nc_integral_eq_sum ρ hρ, nc_integral_eq_sum ρ hρ, Finset.sum_div, Finset.sum_div,
    ← Finset.sum_sub_distrib, Finset.sum_mul]
  refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun σ _ => ?_)
  have h := hn σ (fun _ => phaseSign (fun _ : Fin 2 => 1) σ * (2 * z))
    (fun _ => phaseSign (fun _ : Fin 2 => 1) σ * (2 * z'))
    (fun u => phaseSign (fun _ : Fin 2 => (0 : ℕ)) σ * ρ (reflect σ u))
    (fun u => phaseSign (fun _ : Fin 2 => (0 : ℕ)) σ * ρ (reflect σ u)) (2 * |z - z'|) 0
    continuous_const continuous_const (hη σ) (hη σ)
    (fun x _ => by rw [abs_mul, abs_phaseSign, one_mul]; exact hzM)
    (fun x _ => by rw [abs_mul, abs_phaseSign, one_mul]; exact hz'M)
    (fun x hx => hA σ x hx)
    (fun x _ => by
      rw [← mul_sub, abs_mul, abs_phaseSign, one_mul, ← mul_sub, abs_mul, abs_two])
    (fun x _ => by simp)
  rw [add_zero] at h
  exact h.trans (le_of_eq (by ring))

/-- **Uniform convergence of the normalised model integral on compact phase sets.** -/
theorem tendstoUniformlyOn_ncNorm (ρ : (Fin 2 → ℝ) → ℝ) (hρ : Continuous ρ) (M : ℝ)
    (Nseq : ℕ → ℝ) (hN : Tendsto Nseq atTop atTop) :
    TendstoUniformlyOn (fun n z => ncNorm ρ (Nseq n) z) (ncLimit ρ) atTop (Icc (-M) M) := by
  obtain ⟨L, hL0, hL⟩ := ncNorm_lipschitz_eventually ρ hρ M Nseq hN
  refine tendstoUniformlyOn_of_lipschitz_eventually isCompact_Icc L hL0 hL ?_ fun z _ => ?_
  · exact (continuous_const.mul (continuous_const.mul
      (Real.continuous_exp.comp ((continuous_pow 2).div_const 2)))).continuousOn
  · exact nc_integral_tendsto ρ hρ Nseq hN (fun _ => z) z tendsto_const_nhds

theorem ncLimit_pos (ρ : (Fin 2 → ℝ) → ℝ) (hρ0 : 0 < ρ 0) (z : ℝ) :
    2 * ρ 0 * Real.sqrt (2 * Real.pi) ≤ ncLimit ρ z := by
  unfold ncLimit
  rw [← mul_assoc]
  exact le_mul_of_one_le_right (by positivity) (Real.one_le_exp (by positivity))

theorem ncLimit_div (ρ : (Fin 2 → ℝ) → ℝ) (hρ0 : 0 < ρ 0) (z θ : ℝ) :
    ncLimit ρ (z + θ) / ncLimit ρ z = Real.exp (z * θ + θ ^ 2 / 2) := by
  unfold ncLimit
  rw [mul_div_mul_left _ _ (by positivity), mul_div_mul_left _ _ (by positivity), ← Real.exp_sub]
  congr 1
  ring

/-- **Uniform convergence of the posterior moment generating function on compact phase sets.** -/
theorem tendstoUniformlyOn_ncRatio (ρ : (Fin 2 → ℝ) → ℝ) (hρ : Continuous ρ) (hρ0 : 0 < ρ 0)
    (θ M : ℝ) (Nseq : ℕ → ℝ) (hN : Tendsto Nseq atTop atTop) :
    TendstoUniformlyOn (fun n z => ncRatio ρ (Nseq n) z θ)
      (fun z => Real.exp (z * θ + θ ^ 2 / 2)) atTop (Icc (-M) M) := by
  have hden := tendstoUniformlyOn_ncNorm ρ hρ M Nseq hN
  have hnum : TendstoUniformlyOn (fun n z => ncNorm ρ (Nseq n) (z + θ)) (fun z => ncLimit ρ (z + θ))
      atTop (Icc (-M) M) := by
    have h := (tendstoUniformlyOn_ncNorm ρ hρ (M + |θ|) Nseq hN).comp
      (fun z => z + θ)
    refine h.mono fun z hz => ?_
    simp only [Set.mem_preimage, Set.mem_Icc] at hz ⊢
    constructor <;> linarith [hz.1, hz.2, neg_abs_le θ, le_abs_self θ]
  have hquot := tendstoUniformlyOn_div_of_pos hnum hden
    (2 * ρ 0 * (Real.sqrt (2 * Real.pi) * Real.exp ((M + |θ|) ^ 2 / 2)))
    (2 * ρ 0 * Real.sqrt (2 * Real.pi)) (by positivity) (by positivity)
    (fun z hz => ?_) (fun z _ => ncLimit_pos ρ hρ0 z)
  · refine (hquot.congr ?_).congr_right fun z _ => ncLimit_div ρ hρ0 z θ
    filter_upwards [hN.eventually (eventually_gt_atTop 1)] with n hn
    intro z _
    exact (ncRatio_eq_div_ncNorm ρ (Nseq n) z θ hn).symm
  · unfold ncLimit
    rw [abs_of_pos (by positivity)]
    have hzθ : |z + θ| ≤ M + |θ| := by
      rw [Set.mem_Icc] at hz
      calc |z + θ| ≤ |z| + |θ| := abs_add_le _ _
        _ ≤ M + |θ| := by gcongr; exact abs_le.2 hz
    have hsq : (z + θ) ^ 2 ≤ (M + |θ|) ^ 2 := by
      rw [← sq_abs (z + θ)]
      exact pow_le_pow_left₀ (abs_nonneg _) hzθ 2
    gcongr

/-! ### Gaussian data -/

/-- The empirical phase as a random variable: `Zₙ = n^{-1/2} ∑_{i<n} Yᵢ`. -/
noncomputable def ncPhaseRV {Ω : Type*} (Y : ℕ → Ω → ℝ) (n : ℕ) (ω : Ω) : ℝ :=
  ncPhase n fun i : Fin n => Y i ω

theorem ncPhaseRV_eq {Ω : Type*} (Y : ℕ → Ω → ℝ) (n : ℕ) :
    ncPhaseRV Y n = (Real.sqrt n)⁻¹ • ∑ i : Fin n, Y i := by
  funext ω
  simp only [ncPhaseRV, ncPhase, Pi.smul_apply, Finset.sum_apply, smul_eq_mul]
  ring

variable {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]

omit [IsProbabilityMeasure P] in
theorem memLp_two_of_hasLaw_gaussian {Y : Ω → ℝ} (hY : HasLaw Y (gaussianReal 0 1) P) :
    MemLp Y 2 P := by
  have h := memLp_id_gaussianReal (μ := 0) (v := 1) 2
  rw [← hY.map_eq, memLp_map_measure_iff aestronglyMeasurable_id hY.aemeasurable] at h
  simpa using h

omit [IsProbabilityMeasure P] in
theorem variance_of_hasLaw_gaussian {Y : Ω → ℝ} (hY : HasLaw Y (gaussianReal 0 1) P) :
    Var[Y; P] = 1 := by
  rw [hY.variance_eq, variance_id_gaussianReal]
  simp

omit [IsProbabilityMeasure P] in
theorem integral_of_hasLaw_gaussian {Y : Ω → ℝ} (hY : HasLaw Y (gaussianReal 0 1) P) :
    ∫ ω, Y ω ∂P = 0 := by
  rw [hY.integral_eq, integral_id_gaussianReal]

omit [IsProbabilityMeasure P] in
theorem memLp_ncPhaseRV (Y : ℕ → Ω → ℝ) (hY : ∀ i, HasLaw (Y i) (gaussianReal 0 1) P) (n : ℕ) :
    MemLp (ncPhaseRV Y n) 2 P := by
  rw [ncPhaseRV_eq]
  exact (memLp_finsetSum' (f := fun i : Fin n => Y i) Finset.univ fun i _ =>
    memLp_two_of_hasLaw_gaussian P (hY i)).const_smul _

theorem integral_ncPhaseRV (Y : ℕ → Ω → ℝ) (hY : ∀ i, HasLaw (Y i) (gaussianReal 0 1) P)
    (n : ℕ) : ∫ ω, ncPhaseRV Y n ω ∂P = 0 := by
  rw [ncPhaseRV_eq]
  simp only [Pi.smul_apply, Finset.sum_apply, smul_eq_mul]
  rw [integral_const_mul, integral_finsetSum (f := fun i : Fin n => Y i) _ fun i _ =>
    (memLp_two_of_hasLaw_gaussian P (hY i)).integrable one_le_two]
  simp [integral_of_hasLaw_gaussian P (hY _)]

omit [IsProbabilityMeasure P] in
/-- `Var[Zₙ] = 1` for every `n ≥ 1`. -/
theorem variance_ncPhaseRV (Y : ℕ → Ω → ℝ) (hY : ∀ i, HasLaw (Y i) (gaussianReal 0 1) P)
    (hind : iIndepFun Y P) (n : ℕ) (hn : 0 < n) : Var[ncPhaseRV Y n; P] = 1 := by
  rw [ncPhaseRV_eq, variance_smul, IndepFun.variance_sum (X := fun i : Fin n => Y i)
    (fun i _ => memLp_two_of_hasLaw_gaussian P (hY i))
    (fun i _ j _ hij => hind.indepFun (Fin.val_injective.ne hij))]
  simp only [variance_of_hasLaw_gaussian P (hY _), Finset.sum_const, Finset.card_univ,
    Fintype.card_fin, nsmul_eq_mul, mul_one]
  have hsqrt : Real.sqrt n ≠ 0 := by
    rw [Ne, Real.sqrt_eq_zero']
    push Not
    exact_mod_cast hn
  rw [inv_pow, Real.sq_sqrt (Nat.cast_nonneg n), inv_mul_cancel₀]
  exact_mod_cast hn.ne'

/-- **Chebyshev tightness of the empirical phase**: `P(|Zₙ| ≥ M) ≤ 1/M²`. -/
theorem meas_abs_ncPhaseRV_ge_le (Y : ℕ → Ω → ℝ) (hY : ∀ i, HasLaw (Y i) (gaussianReal 0 1) P)
    (hind : iIndepFun Y P) (n : ℕ) (hn : 0 < n) (M : ℝ) (hM : 0 < M) :
    P {ω | M ≤ |ncPhaseRV Y n ω|} ≤ ENNReal.ofReal (1 / M ^ 2) := by
  have h := meas_ge_le_variance_div_sq (μ := P) (memLp_ncPhaseRV P Y hY n) hM
  rw [integral_ncPhaseRV P Y hY n, variance_ncPhaseRV P Y hY hind n hn] at h
  simpa using h

/-- **The normal-crossing example with Gaussian data (in probability).** For `Yᵢ` i.i.d. `N(0,1)`,
a continuous prior density `ρ` on `(-1,1]²` with `ρ(0) > 0`, and any `θ`, the posterior moment
generating function of `√n x₀x₁` given `Y₁,…,Yₙ` differs from that of `N(Zₙ, 1)` by a quantity
tending to zero in probability. -/
theorem ncFluctMGF_tendstoInMeasure (Y : ℕ → Ω → ℝ) (hY : ∀ i, HasLaw (Y i) (gaussianReal 0 1) P)
    (hind : iIndepFun Y P) (ρ : (Fin 2 → ℝ) → ℝ) (hρ : Continuous ρ) (hρ0 : 0 < ρ 0) (θ : ℝ) :
    TendstoInMeasure P (fun n ω => ncFluctMGF n (fun i : Fin n => Y i ω) ρ θ -
      Real.exp (ncPhaseRV Y n ω * θ + θ ^ 2 / 2)) atTop 0 := by
  rw [tendstoInMeasure_iff_norm]
  intro ε hε
  rw [ENNReal.tendsto_nhds_zero]
  intro δ hδ
  by_cases hδtop : δ = ⊤
  · exact Eventually.of_forall fun n => hδtop ▸ le_top
  have hδ' : 0 < δ.toReal := ENNReal.toReal_pos hδ.ne' hδtop
  set M : ℝ := max 1 (1 / δ.toReal) with hMdef
  have hM1 : 1 ≤ M := le_max_left _ _
  have hM0 : 0 < M := by linarith
  have hMδ : 1 / M ^ 2 ≤ δ.toReal := by
    have hM2 : 1 / δ.toReal ≤ M := le_max_right _ _
    have hMM : M ≤ M ^ 2 := by nlinarith
    calc 1 / M ^ 2 ≤ 1 / M := one_div_le_one_div_of_le hM0 hMM
      _ ≤ 1 / (1 / δ.toReal) := one_div_le_one_div_of_le (by positivity) hM2
      _ = δ.toReal := one_div_one_div _
  have hN : Tendsto (fun n : ℕ => Real.sqrt n) atTop atTop :=
    Real.tendsto_sqrt_atTop.comp tendsto_natCast_atTop_atTop
  have hunif := Metric.tendstoUniformlyOn_iff.mp
    (tendstoUniformlyOn_ncRatio ρ hρ hρ0 θ M _ hN) ε hε
  filter_upwards [hunif, eventually_gt_atTop 0] with n hn hn0
  calc P {ω | ε ≤ ‖ncFluctMGF n (fun i : Fin n => Y i ω) ρ θ -
          Real.exp (ncPhaseRV Y n ω * θ + θ ^ 2 / 2) - (0 : Ω → ℝ) ω‖}
      ≤ P {ω | M ≤ |ncPhaseRV Y n ω|} := by
        refine measure_mono fun ω hω => ?_
        simp only [Set.mem_ofPred_eq, Pi.zero_apply, sub_zero, Real.norm_eq_abs] at hω ⊢
        by_contra hlt
        push Not at hlt
        have hz : ncPhaseRV Y n ω ∈ Icc (-M) M := abs_le.1 hlt.le
        have := hn _ hz
        rw [Real.dist_eq, ncFluctMGF_eq n hn0] at *
        rw [abs_sub_comm] at hω
        exact absurd (hω.trans_lt this) (lt_irrefl _)
    _ ≤ ENNReal.ofReal (1 / M ^ 2) := meas_abs_ncPhaseRV_ge_le P Y hY hind n hn0 M hM0
    _ ≤ δ := by
        rw [← ENNReal.ofReal_toReal hδtop]
        exact ENNReal.ofReal_le_ofReal hMδ

end Laplace.Grammar
