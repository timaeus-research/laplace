/-
Copyright (c) 2026 Timaeus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniel Murfet
-/
import Laplace.Patterning.OUBrownian
import Mathlib.Probability.Kernel.CondDistrib

/-!
# The Markov property of the Ornstein–Uhlenbeck process

The process-level content of "the OU equation is the Markov process with transition kernel
`ouStep`", again without an Itô integral. The key is the **restart identity**: for a continuous
driving path `w`, the pathwise solution satisfies

  `X_{s+r} = e^{-rH} X_s + X⁰_r(w^{(s)})`,   `w^{(s)}_u = w_{s+u} − w_s`,

where `X⁰(w^{(s)})` is the solution from `0` driven by the restarted path (`ouSol_restart`, by
uniqueness of continuous solutions). For Brownian motion the restarted path is again a Brownian
motion (`IsBrownianVec.shift`), so the noise term `Y_{s,r}` has law `N(0, C_r)` by the marginal
theorem, and it is independent of `X_s` because past and future Brownian increments are
uncorrelated hence independent (`indepFun_ouProcess_restartNoise`). The two-time law follows:

  `Law(X_s, X_{s+r}) = (Law X_s ⊗ N(0, C_r)) ∘ (x, z) ↦ (x, e^{-rH} x + z)⁻¹`,

which is the composition of `Law X_s` with the Gaussian transition kernel `x ↦ N(e^{-rH} x, C_r)`
(`ou_two_time_law`, `ou_two_time_law_compProd`).
-/

namespace Laplace.Patterning

open Matrix NormedSpace MeasureTheory ProbabilityTheory Filter Topology intervalIntegral Finset
open Laplace.Sampler
open scoped NNReal

variable {ι : Type*} [Fintype ι] [DecidableEq ι]
variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}

attribute [local instance] Matrix.linftyOpNormedRing Matrix.linftyOpNormedAlgebra

noncomputable section

/-! ### The deterministic restart identity -/

section Deterministic

variable (H σ : Matrix ι ι ℝ)

/-- The solution is affine in the initial point: `X(x₀) = e^{-rH} x₀ + X(0)`. -/
theorem ouSol_add_left (x₀ : ι → ℝ) (w : ℝ → ι → ℝ) (r : ℝ) :
    ouSol H σ x₀ w r = ouFlow H r *ᵥ x₀ + ouSol H σ 0 w r := by
  simp only [ouSol, Matrix.mulVec_zero, zero_add]
  abel

/-- `ouSol` at time `r ≥ 0` depends on the path only through its values on `[0, r]`. -/
theorem ouSol_congr (x₀ : ι → ℝ) {w w' : ℝ → ι → ℝ} {r : ℝ} (hr : 0 ≤ r)
    (h : ∀ u ∈ Set.Icc (0 : ℝ) r, w u = w' u) :
    ouSol H σ x₀ w r = ouSol H σ x₀ w' r := by
  simp only [ouSol]
  rw [h r ⟨hr, le_rfl⟩]
  congr 1
  refine integral_congr fun u hu => ?_
  rw [Set.uIcc_of_le hr] at hu
  simp only [h u hu]

/-- **Restart identity.** `X_{s+r} = e^{-rH} X_s + X⁰_r(u ↦ w_{s+u} − w_s)` for every continuous
path and all real `s`, `r`. -/
theorem ouSol_restart (x₀ : ι → ℝ) {w : ℝ → ι → ℝ} (hw : Continuous w) (s r : ℝ) :
    ouSol H σ x₀ w (s + r)
      = ouFlow H r *ᵥ ouSol H σ x₀ w s + ouSol H σ 0 (fun u => w (s + u) - w s) r := by
  have hXc : Continuous (ouSol H σ x₀ w) := continuous_ouSol hw
  have hw'c : Continuous fun u => w (s + u) - w s :=
    (hw.comp (continuous_const.add continuous_id)).sub continuous_const
  have hZc : Continuous fun u => ouSol H σ x₀ w (s + u) :=
    hXc.comp (continuous_const.add continuous_id)
  have hint : Continuous fun v => H *ᵥ ouSol H σ x₀ w v := continuous_const.matrix_mulVec hXc
  have hZ : ∀ u, ouSol H σ x₀ w (s + u) = ouSol H σ x₀ w s
      - (∫ v in (0 : ℝ)..u, H *ᵥ ouSol H σ x₀ w (s + v)) + σ *ᵥ (w (s + u) - w s) := by
    intro u
    have h1 := ouSol_integral_equation (H := H) (σ := σ) (x₀ := x₀) hw (s + u)
    have h2 := ouSol_integral_equation (H := H) (σ := σ) (x₀ := x₀) hw s
    have hsplit : ∫ v in (0 : ℝ)..s + u, H *ᵥ ouSol H σ x₀ w v
        = (∫ v in (0 : ℝ)..s, H *ᵥ ouSol H σ x₀ w v)
          + ∫ v in s..s + u, H *ᵥ ouSol H σ x₀ w v :=
      (integral_add_adjacent_intervals (hint.intervalIntegrable _ _)
        (hint.intervalIntegrable _ _)).symm
    have htrans : ∫ v in (0 : ℝ)..u, H *ᵥ ouSol H σ x₀ w (s + v)
        = ∫ v in s..s + u, H *ᵥ ouSol H σ x₀ w v := by
      have := intervalIntegral.integral_comp_add_left (fun v => H *ᵥ ouSol H σ x₀ w v)
        (a := 0) (b := u) s
      simpa using this
    rw [htrans, h1, h2, hsplit, Matrix.mulVec_sub]
    abel
  have hu := ouSol_unique (H := H) (σ := σ) (x₀ := ouSol H σ x₀ w s) hw'c hZc hZ r
  rw [hu, ouSol_add_left]

end Deterministic

/-! ### The restarted Brownian motion -/

/-- The Brownian motion restarted at time `s`: `t ↦ W_{s+t} − W_s`. -/
def brownianShift (W : ℝ≥0 → Ω → EuclideanSpace ℝ ι) (s t : ℝ≥0) (ω : Ω) : EuclideanSpace ℝ ι :=
  W (s + t) ω - W s ω

@[simp] theorem brownianShift_zero (W : ℝ≥0 → Ω → EuclideanSpace ℝ ι) (s : ℝ≥0) (ω : Ω) :
    brownianShift W s 0 ω = 0 := by
  simp [brownianShift]

namespace IsBrownianVec

variable {W : ℝ≥0 → Ω → EuclideanSpace ℝ ι}

/-- **The restarted Brownian motion is a Brownian motion.** -/
theorem shift (hW : IsBrownianVec W P) (s : ℝ≥0) : IsBrownianVec (brownianShift W s) P := by
  have := hW.isProbabilityMeasure
  refine ⟨hW.gauss.shift s, fun t i => ?_, fun u v i j => ?_, ?_⟩
  · simp only [brownianShift, PiLp.sub_apply]
    rw [integral_sub (hW.integrable_coord _ _) (hW.integrable_coord _ _), hW.centered,
      hW.centered, sub_zero]
  · simp only [brownianShift, PiLp.sub_apply]
    rw [covariance_fun_sub_fun_sub (hW.memLp_coord _ _) (hW.memLp_coord _ _)
      (hW.memLp_coord _ _) (hW.memLp_coord _ _)]
    simp only [hW.cov]
    by_cases hij : i = j
    · subst hij
      simp only [if_true, min_add_add_left, min_eq_right (le_self_add : s ≤ s + u),
        min_eq_left (le_self_add : s ≤ s + v), min_self]
      push_cast
      ring
    · simp [hij]
  · filter_upwards [hW.cont] with ω hω
    exact (hω.comp (continuous_const.add continuous_id)).sub continuous_const

/-- The OU process is almost everywhere measurable (extracted from the marginal-law proof). -/
theorem aemeasurable_ouProcess (hW : IsBrownianVec W P) (H σ : Matrix ι ι ℝ)
    (x₀ : EuclideanSpace ℝ ι) {s : ℝ} (hs : 0 ≤ s) : AEMeasurable (ouProcess W H σ x₀ s) P :=
  aemeasurable_of_tendsto_metrizable_ae atTop
    (fun n => (measurable_const_add _).comp_aemeasurable
      (hW.hasGaussianLaw_ouIncrement H σ s n).aemeasurable)
    (tendsto_ouApprox hW H σ x₀ hs)

/-- **Stochastic restart identity.** Almost surely,
`X_{s+r} = e^{-rH} X_s + Y_{s,r}` with `Y_{s,r}` the OU process from `0` driven by the Brownian
motion restarted at `s`. -/
theorem ouProcess_restart (hW : IsBrownianVec W P) (H σ : Matrix ι ι ℝ) (x₀ : EuclideanSpace ℝ ι)
    {s r : ℝ} (hs : 0 ≤ s) (hr : 0 ≤ r) :
    ∀ᵐ ω ∂P, ouProcess W H σ x₀ (s + r) ω
      = euclid (ouFlow H r) (ouProcess W H σ x₀ s ω)
        + ouProcess (brownianShift W (Real.toNNReal s)) H σ 0 r ω := by
  filter_upwards [hW.cont] with ω hcont
  set w : ℝ → ι → ℝ := fun u => WithLp.ofLp (W (Real.toNNReal u) ω) with hw
  have hwc : Continuous w :=
    (PiLp.continuous_ofLp (p := 2) (β := fun _ : ι => ℝ)).comp
      (hcont.comp continuous_real_toNNReal)
  have key : ouSol H σ (WithLp.ofLp x₀) w (s + r)
      = ouFlow H r *ᵥ ouSol H σ (WithLp.ofLp x₀) w s
        + ouSol H σ 0 (fun u => WithLp.ofLp (brownianShift W (Real.toNNReal s) (Real.toNNReal u) ω))
          r := by
    rw [ouSol_restart H σ _ hwc s r]
    congr 1
    refine ouSol_congr H σ _ hr fun u hu => ?_
    simp only [hw, brownianShift, WithLp.ofLp_sub, Real.toNNReal_add hs hu.1]
  ext i
  simp only [ouProcess]
  rw [← hw, key]
  simp [ofLp_toEuclideanCLM]

/-- **Law of the restart noise**: `Y_{s,r} ∼ N(0, ∫₀ʳ e^{-uH} σσᵀ e^{-uH} du)`. -/
theorem restartNoise_law (hW : IsBrownianVec W P) (H σ : Matrix ι ι ℝ) (hH : Hᵀ = H) (s : ℝ≥0)
    {r : ℝ} (hr : 0 ≤ r) :
    P.map (ouProcess (brownianShift W s) H σ 0 r)
      = multivariateGaussian 0 (ouCovInt H (σ * σᵀ) r) := by
  rw [ou_marginal_law (hW.shift s) H σ hH 0 hr, map_zero]

end IsBrownianVec

/-! ### Independence of the past and the restart noise -/

section Independence

variable {W : ℝ≥0 → Ω → EuclideanSpace ℝ ι}

/-- The increments of the restarted motion are increments of `W`. -/
theorem incr_brownianShift (W : ℝ≥0 → Ω → EuclideanSpace ℝ ι) (s' : ℝ≥0) (r : ℝ) (m k : ℕ)
    (ω : Ω) :
    incr (brownianShift W s') r m k ω = W (s' + nodeT r m (k + 1)) ω - W (s' + nodeT r m k) ω := by
  simp only [incr, brownianShift]
  abel

/-- A single increment coordinate as a continuous linear image of `W` restricted to two times. -/
def incrCLM (t₁ t₂ : ℝ≥0) (i : ι) :
    (({t₁, t₂} : Finset ℝ≥0) → EuclideanSpace ℝ ι) →L[ℝ] ℝ where
  toFun z := (z ⟨t₂, by simp⟩ - z ⟨t₁, by simp⟩) i
  map_add' z z' := by
    simp only [Pi.add_apply, PiLp.sub_apply, PiLp.add_apply]
    ring
  map_smul' c z := by
    simp only [Pi.smul_apply, PiLp.sub_apply, PiLp.smul_apply, smul_eq_mul, RingHom.id_apply]
    ring
  cont := by fun_prop

/-- The past increments (over `[0, s]`) and the future increments (over `[s, s + r]`) form a
jointly Gaussian family. -/
theorem isGaussianProcess_incrFamily (hW : IsBrownianVec W P) (s r : ℝ) (n m : ℕ) :
    IsGaussianProcess (Sum.elim (fun (p : Fin (n + 1) × ι) ω => incr W s n p.1 ω p.2)
      (fun (q : Fin (m + 1) × ι) ω =>
        incr (brownianShift W (Real.toNNReal s)) r m q.1 ω q.2)) P := by
  refine hW.gauss.of_isGaussianProcess fun x => ?_
  rcases x with p | q
  · refine ⟨{nodeT s n p.1, nodeT s n (p.1 + 1)},
      incrCLM (nodeT s n p.1) (nodeT s n (p.1 + 1)) p.2, fun ω => ?_⟩
    simp [incrCLM, incr, Finset.restrict_def]
  · refine ⟨{Real.toNNReal s + nodeT r m q.1, Real.toNNReal s + nodeT r m (q.1 + 1)},
      incrCLM _ _ q.2, fun ω => ?_⟩
    simp [incrCLM, incr_brownianShift, Finset.restrict_def]

/-- **Past and future increments are uncorrelated.** -/
theorem cov_incr_past_future (hW : IsBrownianVec W P) {s r : ℝ} (hs : 0 ≤ s) (hr : 0 ≤ r)
    (n m : ℕ) (p : Fin (n + 1) × ι) (q : Fin (m + 1) × ι) :
    cov[fun ω => incr W s n p.1 ω p.2,
      fun ω => incr (brownianShift W (Real.toNNReal s)) r m q.1 ω q.2; P] = 0 := by
  have := hW.isProbabilityMeasure
  simp only [incr_brownianShift]
  simp only [incr, PiLp.sub_apply]
  rw [covariance_fun_sub_fun_sub (hW.memLp_coord _ _) (hW.memLp_coord _ _) (hW.memLp_coord _ _)
    (hW.memLp_coord _ _)]
  simp only [hW.cov]
  have h1 : nodeT s n (p.1 + 1) ≤ Real.toNNReal s :=
    Real.toNNReal_le_toNNReal (node_le hs (by omega))
  have h2 : nodeT s n p.1 ≤ Real.toNNReal s :=
    Real.toNNReal_le_toNNReal (node_le hs (by omega))
  have h3 : Real.toNNReal s ≤ Real.toNNReal s + nodeT r m q.1 := le_self_add
  have h4 : Real.toNNReal s ≤ Real.toNNReal s + nodeT r m (q.1 + 1) := le_self_add
  rw [min_eq_left (h1.trans h4), min_eq_left (h1.trans h3), min_eq_left (h2.trans h4),
    min_eq_left (h2.trans h3)]
  split_ifs <;> ring

/-- The Gaussian approximants of `X_s` and of the restart noise are independent. -/
theorem indepFun_ouApprox_restart (hW : IsBrownianVec W P) (H σ : Matrix ι ι ℝ)
    (x₀ : EuclideanSpace ℝ ι) {s r : ℝ} (hs : 0 ≤ s) (hr : 0 ≤ r) (n : ℕ) :
    IndepFun (fun ω => euclid (ouFlow H s) x₀ + ouIncrement W H σ s n ω)
      (fun ω => euclid (ouFlow H r) 0
        + ouIncrement (brownianShift W (Real.toNNReal s)) H σ r n ω) P := by
  have := hW.isProbabilityMeasure
  have hind := (isGaussianProcess_incrFamily hW s r n n).indepFun_of_covariance_eq_zero
    (fun p => (hW.memLp_incr_coord s n p.1 p.2).aestronglyMeasurable.aemeasurable)
    (fun q => ((hW.shift _).memLp_incr_coord r n q.1 q.2).aestronglyMeasurable.aemeasurable)
    (fun p q => cov_incr_past_future hW hs hr n n p q)
  let Φ : (Fin (n + 1) × ι → ℝ) → EuclideanSpace ℝ ι := fun z =>
    euclid (ouFlow H s) x₀ + ∑ k : Fin (n + 1),
      euclid (ouFlow H (s - node s n k) * σ) (WithLp.toLp 2 fun i => z (k, i))
  let Ψ : (Fin (n + 1) × ι → ℝ) → EuclideanSpace ℝ ι := fun z =>
    euclid (ouFlow H r) 0 + ∑ k : Fin (n + 1),
      euclid (ouFlow H (r - node r n k) * σ) (WithLp.toLp 2 fun i => z (k, i))
  have hcont : ∀ (m : EuclideanSpace ℝ ι) (F : Fin (n + 1) → Matrix ι ι ℝ),
      Continuous fun z : Fin (n + 1) × ι → ℝ =>
        m + ∑ k : Fin (n + 1), euclid (F k) (WithLp.toLp 2 fun i => z (k, i)) := fun m F =>
    continuous_const.add (continuous_finset_sum _ fun k _ => (euclid (F k)).continuous.comp
      ((PiLp.continuous_toLp (p := 2) (β := fun _ : ι => ℝ)).comp
        (continuous_pi fun i => continuous_apply (k, i))))
  have hΦ : Measurable Φ := (hcont _ _).measurable
  have hΨ : Measurable Ψ := (hcont _ _).measurable
  refine (hind.comp hΦ hΨ).congr (Filter.Eventually.of_forall fun ω => ?_)
    (Filter.Eventually.of_forall fun ω => ?_)
  · simp only [Function.comp_apply, Φ, ouIncrement]
  · simp only [Function.comp_apply, Ψ, ouIncrement]

end Independence

/-! ### Independence passes to almost sure limits -/

section Limits

variable {G : Type*} [NormedAddCommGroup G] [NormedSpace ℝ G] [MeasurableSpace G] [BorelSpace G]
  [SecondCountableTopology G]

/-- Dual characteristic functions of a.s. convergent sequences converge (dominated convergence). -/
theorem tendsto_charFunDual_map [IsProbabilityMeasure P] {Zn : ℕ → Ω → G} {Z : Ω → G}
    (hZn : ∀ n, AEMeasurable (Zn n) P) (hZ : AEMeasurable Z P)
    (hlim : ∀ᵐ ω ∂P, Tendsto (fun n => Zn n ω) atTop (𝓝 (Z ω))) (L : StrongDual ℝ G) :
    Tendsto (fun n => charFunDual (P.map (Zn n)) L) atTop (𝓝 (charFunDual (P.map Z) L)) := by
  have hcont : Continuous fun v : G => Complex.exp ((L v : ℝ) * Complex.I) := by fun_prop
  have key : ∀ (Y : Ω → G), AEMeasurable Y P →
      charFunDual (P.map Y) L = ∫ ω, Complex.exp ((L (Y ω) : ℝ) * Complex.I) ∂P := fun Y hY => by
    rw [charFunDual_apply, integral_map hY hcont.aestronglyMeasurable]
  have hfun : (fun n => charFunDual (P.map (Zn n)) L)
      = fun n => ∫ ω, Complex.exp ((L (Zn n ω) : ℝ) * Complex.I) ∂P :=
    funext fun n => key _ (hZn n)
  rw [hfun, key Z hZ]
  refine tendsto_integral_of_dominated_convergence (fun _ => (1 : ℝ))
    (fun n => hcont.comp_aestronglyMeasurable (hZn n).aestronglyMeasurable) (integrable_const 1)
    (fun n => Filter.Eventually.of_forall fun ω => ?_) ?_
  · rw [Complex.norm_exp_ofReal_mul_I]
  · filter_upwards [hlim] with ω hω
    exact (hcont.tendsto _).comp hω

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
  [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]
  [MeasurableSpace F] [BorelSpace F] [SecondCountableTopology F]

/-- **Independence passes to almost sure limits.** -/
theorem indepFun_of_tendsto_ae [IsProbabilityMeasure P] {Xn : ℕ → Ω → E} {Yn : ℕ → Ω → F}
    {X : Ω → E} {Y : Ω → F} (h : ∀ n, IndepFun (Xn n) (Yn n) P)
    (hXn : ∀ n, AEMeasurable (Xn n) P) (hYn : ∀ n, AEMeasurable (Yn n) P)
    (hX : AEMeasurable X P) (hY : AEMeasurable Y P)
    (hlimX : ∀ᵐ ω ∂P, Tendsto (fun n => Xn n ω) atTop (𝓝 (X ω)))
    (hlimY : ∀ᵐ ω ∂P, Tendsto (fun n => Yn n ω) atTop (𝓝 (Y ω))) :
    IndepFun X Y P := by
  rw [indepFun_iff_charFunDual_prod hX hY]
  intro L
  have hn : ∀ n, charFunDual (P.map fun ω => (Xn n ω, Yn n ω)) L
      = charFunDual (P.map (Xn n)) (L.comp (.inl ℝ E F))
        * charFunDual (P.map (Yn n)) (L.comp (.inr ℝ E F)) := fun n =>
    (indepFun_iff_charFunDual_prod (hXn n) (hYn n)).mp (h n) L
  have h1 : Tendsto (fun n => charFunDual (P.map fun ω => (Xn n ω, Yn n ω)) L) atTop
      (𝓝 (charFunDual (P.map fun ω => (X ω, Y ω)) L)) := by
    refine tendsto_charFunDual_map (fun n => (hXn n).prodMk (hYn n)) (hX.prodMk hY) ?_ L
    filter_upwards [hlimX, hlimY] with ω h1 h2
    exact h1.prodMk_nhds h2
  have h2 := (tendsto_charFunDual_map hXn hX hlimX (L.comp (.inl ℝ E F))).mul
    (tendsto_charFunDual_map hYn hY hlimY (L.comp (.inr ℝ E F)))
  exact tendsto_nhds_unique h1 (h2.congr fun n => (hn n).symm)

end Limits

/-! ### The two-time law -/

namespace IsBrownianVec

variable {W : ℝ≥0 → Ω → EuclideanSpace ℝ ι}

/-- **The restart noise is independent of the present state.** -/
theorem indepFun_ouProcess_restartNoise (hW : IsBrownianVec W P) (H σ : Matrix ι ι ℝ)
    (x₀ : EuclideanSpace ℝ ι) {s r : ℝ} (hs : 0 ≤ s) (hr : 0 ≤ r) :
    IndepFun (ouProcess W H σ x₀ s) (ouProcess (brownianShift W (Real.toNNReal s)) H σ 0 r) P := by
  have := hW.isProbabilityMeasure
  refine indepFun_of_tendsto_ae (fun n => indepFun_ouApprox_restart hW H σ x₀ hs hr n)
    (fun n => (measurable_const_add _).comp_aemeasurable
      (hW.hasGaussianLaw_ouIncrement H σ s n).aemeasurable)
    (fun n => (measurable_const_add _).comp_aemeasurable
      ((hW.shift _).hasGaussianLaw_ouIncrement H σ r n).aemeasurable)
    (hW.aemeasurable_ouProcess H σ x₀ hs) ((hW.shift _).aemeasurable_ouProcess H σ 0 hr)
    (tendsto_ouApprox hW H σ x₀ hs) (tendsto_ouApprox (hW.shift _) H σ 0 hr)

/-- **The two-time law.** `Law(X_s, X_{s+r})` is the image of `Law(X_s) ⊗ N(0, C_r)` under
`(x, z) ↦ (x, e^{-rH} x + z)`: the transition from `X_s` is the Gaussian kernel
`N(e^{-rH} x, C_r)`. -/
theorem ou_two_time_law (hW : IsBrownianVec W P) (H σ : Matrix ι ι ℝ) (hH : Hᵀ = H)
    (x₀ : EuclideanSpace ℝ ι) {s r : ℝ} (hs : 0 ≤ s) (hr : 0 ≤ r) :
    P.map (fun ω => (ouProcess W H σ x₀ s ω, ouProcess W H σ x₀ (s + r) ω))
      = ((P.map (ouProcess W H σ x₀ s)).prod
          (multivariateGaussian 0 (ouCovInt H (σ * σᵀ) r))).map
            (fun p : EuclideanSpace ℝ ι × EuclideanSpace ℝ ι =>
              (p.1, euclid (ouFlow H r) p.1 + p.2)) := by
  have := hW.isProbabilityMeasure
  have hX : AEMeasurable (ouProcess W H σ x₀ s) P := hW.aemeasurable_ouProcess H σ x₀ hs
  have hY : AEMeasurable (ouProcess (brownianShift W (Real.toNNReal s)) H σ 0 r) P :=
    (hW.shift _).aemeasurable_ouProcess H σ 0 hr
  have hT : Measurable fun p : EuclideanSpace ℝ ι × EuclideanSpace ℝ ι =>
      (p.1, euclid (ouFlow H r) p.1 + p.2) :=
    (continuous_fst.prodMk ((euclid (ouFlow H r)).continuous.comp continuous_fst |>.add
      continuous_snd)).measurable
  have h1 : P.map (fun ω => (ouProcess W H σ x₀ s ω, ouProcess W H σ x₀ (s + r) ω))
      = P.map (fun ω => (ouProcess W H σ x₀ s ω,
          euclid (ouFlow H r) (ouProcess W H σ x₀ s ω)
            + ouProcess (brownianShift W (Real.toNNReal s)) H σ 0 r ω)) := by
    apply Measure.map_congr
    filter_upwards [hW.ouProcess_restart H σ x₀ hs hr] with ω hω
    rw [hω]
  rw [h1, ← hW.restartNoise_law H σ hH (Real.toNNReal s) hr,
    ← (indepFun_iff_map_prod_eq_prod_map_map hX hY).mp
      (hW.indepFun_ouProcess_restartNoise H σ x₀ hs hr),
    AEMeasurable.map_map_of_aemeasurable hT.aemeasurable (hX.prodMk hY)]
  rfl

end IsBrownianVec

/-! ### The Gaussian transition kernel -/

section Kernel

variable (H σ : Matrix ι ι ℝ) (r : ℝ)

theorem measurable_ouShiftMap :
    Measurable fun p : EuclideanSpace ℝ ι × EuclideanSpace ℝ ι => euclid (ouFlow H r) p.1 + p.2 :=
  (((euclid (ouFlow H r)).continuous.comp continuous_fst).add continuous_snd).measurable

/-- The transition kernel `x ↦ N(e^{-rH} x, C_r)`, built as the image of the fixed noise law
`N(0, C_r)` under `z ↦ e^{-rH} x + z`. -/
def ouKernel : Kernel (EuclideanSpace ℝ ι) (EuclideanSpace ℝ ι) :=
  Kernel.map
    ((Kernel.deterministic (id : EuclideanSpace ℝ ι → EuclideanSpace ℝ ι) measurable_id)
      ×ₖ Kernel.const (EuclideanSpace ℝ ι) (multivariateGaussian 0 (ouCovInt H (σ * σᵀ) r)))
    (fun p : EuclideanSpace ℝ ι × EuclideanSpace ℝ ι => euclid (ouFlow H r) p.1 + p.2)

instance : IsMarkovKernel (ouKernel H σ r) :=
  Kernel.IsMarkovKernel.map _ (measurable_ouShiftMap H r)

theorem ouKernel_apply (x : EuclideanSpace ℝ ι) :
    ouKernel H σ r x = (multivariateGaussian 0 (ouCovInt H (σ * σᵀ) r)).map
      (fun z => euclid (ouFlow H r) x + z) := by
  rw [ouKernel, Kernel.map_apply _ (measurable_ouShiftMap H r), Kernel.prod_apply,
    Kernel.deterministic_apply, Kernel.const_apply, Measure.dirac_prod,
    Measure.map_map (measurable_ouShiftMap H r) measurable_prodMk_left]
  rfl

/-- **The transition kernel is the Gaussian `N(e^{-rH} x, C_r)`.** -/
theorem ouKernel_eq (hH : Hᵀ = H) (hr : 0 ≤ r) (x : EuclideanSpace ℝ ι) :
    ouKernel H σ r x
      = multivariateGaussian (euclid (ouFlow H r) x) (ouCovInt H (σ * σᵀ) r) := by
  rw [ouKernel_apply]
  have : IsProbabilityMeasure ((multivariateGaussian 0 (ouCovInt H (σ * σᵀ) r)).map
      (fun z => euclid (ouFlow H r) x + z)) :=
    Measure.isProbabilityMeasure_map (measurable_const_add _).aemeasurable
  apply Measure.ext_of_charFun
  funext t
  rw [charFun_map_const_add, charFun_multivariateGaussian (ouCovInt_posSemidef H σ hH hr),
    charFun_multivariateGaussian (ouCovInt_posSemidef H σ hH hr), ← Complex.exp_add]
  congr 1
  rw [inner_zero_right, real_inner_comm]
  push_cast
  ring

/-- Pushing `μ ⊗ N(0, C_r)` forward by `(x, z) ↦ (x, e^{-rH} x + z)` is the composition
`μ ⊗ₘ κ_r` with the transition kernel. -/
theorem prod_map_eq_compProd_ouKernel (μ : Measure (EuclideanSpace ℝ ι)) [SFinite μ] :
    (μ.prod (multivariateGaussian 0 (ouCovInt H (σ * σᵀ) r))).map
        (fun p : EuclideanSpace ℝ ι × EuclideanSpace ℝ ι => (p.1, euclid (ouFlow H r) p.1 + p.2))
      = μ ⊗ₘ ouKernel H σ r := by
  have hT : Measurable fun p : EuclideanSpace ℝ ι × EuclideanSpace ℝ ι =>
      (p.1, euclid (ouFlow H r) p.1 + p.2) :=
    measurable_fst.prodMk (measurable_ouShiftMap H r)
  ext S hS
  rw [Measure.map_apply hT hS, Measure.prod_apply (hT hS), Measure.compProd_apply hS]
  refine lintegral_congr fun x => ?_
  rw [ouKernel_apply, Measure.map_apply (measurable_const_add _) (measurable_prodMk_left hS)]
  rfl

end Kernel

namespace IsBrownianVec

variable {W : ℝ≥0 → Ω → EuclideanSpace ℝ ι}

/-- **The two-time law as a composition with the transition kernel.** -/
theorem ou_two_time_law_compProd (hW : IsBrownianVec W P) (H σ : Matrix ι ι ℝ) (hH : Hᵀ = H)
    (x₀ : EuclideanSpace ℝ ι) {s r : ℝ} (hs : 0 ≤ s) (hr : 0 ≤ r) :
    P.map (fun ω => (ouProcess W H σ x₀ s ω, ouProcess W H σ x₀ (s + r) ω))
      = (P.map (ouProcess W H σ x₀ s)) ⊗ₘ ouKernel H σ r := by
  have := hW.isProbabilityMeasure
  have : IsProbabilityMeasure (P.map (ouProcess W H σ x₀ s)) :=
    Measure.isProbabilityMeasure_map (hW.aemeasurable_ouProcess H σ x₀ hs)
  rw [hW.ou_two_time_law H σ hH x₀ hs hr, prod_map_eq_compProd_ouKernel]

/-- **The conditional law of `X_{s+r}` given `X_s` is `N(e^{-rH} X_s, C_r)`**: the regular
conditional distribution is the transition kernel. -/
theorem condDistrib_ouProcess [IsProbabilityMeasure P] (hW : IsBrownianVec W P)
    (H σ : Matrix ι ι ℝ) (hH : Hᵀ = H) (x₀ : EuclideanSpace ℝ ι) {s r : ℝ} (hs : 0 ≤ s)
    (hr : 0 ≤ r) :
    condDistrib (ouProcess W H σ x₀ (s + r)) (ouProcess W H σ x₀ s) P
      =ᵐ[P.map (ouProcess W H σ x₀ s)] ouKernel H σ r :=
  condDistrib_ae_eq_of_measure_eq_compProd _
    (hW.aemeasurable_ouProcess H σ x₀ (by linarith)) (hW.ou_two_time_law_compProd H σ hH x₀ hs hr)

end IsBrownianVec

end

end Laplace.Patterning
