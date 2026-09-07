/-
Copyright (c) 2026 Timaeus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Laplace.Grammar.NormalCrossingData
import Laplace.Grammar.ApproxInDistribution
import Mathlib.Probability.Independence.CharacteristicFunction

/-!
# The normal-crossing example: exact law of the phase and convergence in distribution

Unit 220 (Astra #24, programme H2-lite, final step). For `Yᵢ` i.i.d. `N(0,1)` the empirical phase
`Zₙ = n^{-1/2} ∑_{i<n} Yᵢ` is **exactly** standard normal for every `n ≥ 1` (characteristic
functions: `iIndepFun.charFun_map_sum_eq_prod`, `charFun_gaussianReal`, `Measure.ext_of_charFun`;
`hasLaw_ncPhaseRV`). Hence `Zₙ ⇒ Z ~ N(0,1)` trivially, and Slutsky
(`TendstoInDistribution.add_of_tendstoInMeasure_const`) with the in-probability statement of
unit 219 gives the **convergence in distribution** of the posterior moment generating function
(`ncFluctMGF_tendstoInDistribution`):
```
E_post[exp(θ √n x₀x₁)] ⇒ exp(Z θ + θ²/2),   Z ~ N(0,1),
```
the moment generating function of `N(Z, 1)` evaluated at a standard-normal `Z`. Measurability of the
posterior moment generating function in the data is obtained from continuity of the model integrals
in the phase (dominated convergence, `continuous_nc_integral`). Zero `sorry`/`axiom`.
-/

open MeasureTheory Filter Topology Real Set ProbabilityTheory

namespace Laplace.Grammar

/-! ### Continuity of the model integral in the phase -/

theorem measurableSet_symBox (d : ℕ) : MeasurableSet (symBox d) :=
  MeasurableSet.univ_pi fun _ => measurableSet_Ioc

theorem ncKernel_pos (N z : ℝ) (x : Fin 2 → ℝ) : 0 < ncKernel N z x := Real.exp_pos _

theorem ncKernel_le (N z : ℝ) (x : Fin 2 → ℝ) (hx : x ∈ symBox 2) (R : ℝ) (hz : |z| ≤ R) :
    ncKernel N z x ≤ Real.exp (|N| * R) := by
  unfold ncKernel
  apply Real.exp_le_exp.2
  have h0 : |x 0| ≤ 1 := abs_le.2 ⟨(hx 0 (Set.mem_univ _)).1.le, (hx 0 (Set.mem_univ _)).2⟩
  have h1 : |x 1| ≤ 1 := abs_le.2 ⟨(hx 1 (Set.mem_univ _)).1.le, (hx 1 (Set.mem_univ _)).2⟩
  have hprod : |x 0 * x 1| ≤ 1 := by
    rw [abs_mul]
    exact mul_le_one₀ h0 (abs_nonneg _) h1
  have hR : 0 ≤ R := (abs_nonneg z).trans hz
  calc -(N ^ 2 * (x 0 * x 1) ^ 2) / 2 + N * z * (x 0 * x 1) ≤ N * z * (x 0 * x 1) := by
        have : 0 ≤ N ^ 2 * (x 0 * x 1) ^ 2 := by positivity
        linarith
    _ ≤ |N * z * (x 0 * x 1)| := le_abs_self _
    _ = |N| * |z| * |x 0 * x 1| := by rw [abs_mul, abs_mul]
    _ ≤ |N| * R * 1 := by gcongr
    _ = |N| * R := mul_one _

theorem continuous_ncKernel_phase (N : ℝ) (x : Fin 2 → ℝ) : Continuous fun z => ncKernel N z x := by
  unfold ncKernel
  fun_prop

theorem continuous_ncKernel (N z : ℝ) : Continuous fun x : Fin 2 → ℝ => ncKernel N z x := by
  unfold ncKernel
  fun_prop

/-- The model integral is continuous in the phase (dominated convergence on the box). -/
theorem continuous_nc_integral (ρ : (Fin 2 → ℝ) → ℝ) (hρ : Continuous ρ) (N : ℝ) :
    Continuous fun z => ∫ x in symBox 2, ρ x * ncKernel N z x := by
  refine continuous_iff_continuousAt.2 fun z₀ => ?_
  obtain ⟨A, hA⟩ := (isCompact_univ_pi fun _ : Fin 2 => isCompact_Icc (a := (-1 : ℝ)) (b := 1))
    |>.exists_bound_of_continuousOn hρ.continuousOn
  have hsub : symBox 2 ⊆ Set.pi Set.univ fun _ : Fin 2 => Icc (-1 : ℝ) 1 :=
    Set.pi_mono fun _ _ => Ioc_subset_Icc_self
  refine continuousAt_of_dominated (bound := fun _ => A * Real.exp (|N| * (|z₀| + 1)))
    (Eventually.of_forall fun z => (hρ.mul (continuous_ncKernel N z)).aestronglyMeasurable) ?_
    (integrableOn_piBox_Ioc_of_continuous 2 (-1) 1 _ continuous_const) ?_
  · filter_upwards [Metric.ball_mem_nhds z₀ one_pos] with z hz
    refine ae_restrict_of_forall_mem (measurableSet_symBox 2) fun x hx => ?_
    rw [Metric.mem_ball, Real.dist_eq] at hz
    have hzR : |z| ≤ |z₀| + 1 := by
      calc |z| = |z₀ + (z - z₀)| := by ring_nf
        _ ≤ |z₀| + |z - z₀| := abs_add_le _ _
        _ ≤ |z₀| + 1 := by linarith
    rw [Real.norm_eq_abs, abs_mul, abs_of_pos (ncKernel_pos N z x)]
    have hAx : |ρ x| ≤ A := by
      have := hA x (hsub hx)
      rwa [Real.norm_eq_abs] at this
    exact mul_le_mul hAx (ncKernel_le N z x hx _ hzR) (ncKernel_pos N z x).le
      ((abs_nonneg _).trans hAx)
  · exact Eventually.of_forall fun x =>
      (continuous_const.mul (continuous_ncKernel_phase N x)).continuousAt

theorem measurable_ncRatio (ρ : (Fin 2 → ℝ) → ℝ) (hρ : Continuous ρ) (N θ : ℝ) :
    Measurable fun z => ncRatio ρ N z θ := by
  have h := continuous_nc_integral ρ hρ N
  exact (h.comp (continuous_add_const θ)).measurable.div h.measurable

/-! ### The exact law of the empirical phase -/

variable {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]

omit [IsProbabilityMeasure P] in
theorem aemeasurable_ncPhaseRV (Y : ℕ → Ω → ℝ) (hY : ∀ i, AEMeasurable (Y i) P) (n : ℕ) :
    AEMeasurable (ncPhaseRV Y n) P := by
  rw [ncPhaseRV_eq]
  exact (Finset.aemeasurable_sum (f := fun i : Fin n => Y i) Finset.univ fun i _ =>
    hY i).const_smul _

/-- **The law of the sum of `n` i.i.d. standard normals is `N(0, n)`** (characteristic
functions). -/
theorem map_sum_gaussian (Y : ℕ → Ω → ℝ) (hY : ∀ i, HasLaw (Y i) (gaussianReal 0 1) P)
    (hind : iIndepFun Y P) (n : ℕ) :
    P.map (∑ i : Fin n, Y i) = gaussianReal 0 (n : NNReal) := by
  have hX : iIndepFun (fun i : Fin n => Y i) P := hind.precomp Fin.val_injective
  have hmX : ∀ i : Fin n, AEMeasurable (fun ω => Y i ω) P := fun i => (hY i).aemeasurable
  refine Measure.ext_of_charFun (funext fun t => ?_)
  rw [hX.charFun_map_sum_eq_prod hmX]
  simp only [(hY _).map_eq, Finset.prod_const, Finset.card_univ, Fintype.card_fin, Pi.pow_apply,
    charFun_gaussianReal, ← Complex.exp_nat_mul]
  congr 1
  push_cast
  ring

/-- **`Zₙ` is exactly standard normal** for every `n ≥ 1`. -/
theorem hasLaw_ncPhaseRV (Y : ℕ → Ω → ℝ) (hY : ∀ i, HasLaw (Y i) (gaussianReal 0 1) P)
    (hind : iIndepFun Y P) (n : ℕ) (hn : 0 < n) : HasLaw (ncPhaseRV Y n) (gaussianReal 0 1) P := by
  have hS : HasLaw (∑ i : Fin n, Y i) (gaussianReal 0 (n : NNReal)) P :=
    ⟨Finset.aemeasurable_sum (f := fun i : Fin n => Y i) Finset.univ fun i _ => (hY i).aemeasurable,
      map_sum_gaussian P Y hY hind n⟩
  have h := gaussianReal_const_mul hS (Real.sqrt n)⁻¹
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  have hv : (NNReal.mk ((Real.sqrt n)⁻¹ ^ 2) (sq_nonneg _) * (n : NNReal)) = 1 := by
    refine NNReal.eq ?_
    push_cast
    rw [inv_pow, Real.sq_sqrt hn'.le, inv_mul_cancel₀ hn'.ne']
  rw [mul_zero, hv] at h
  convert h using 1
  rw [ncPhaseRV_eq]
  funext ω
  simp

/-- `Zₙ ⇒ Z ~ N(0,1)` (the law is exact for `n ≥ 1`). -/
theorem tendstoInDistribution_ncPhaseRV (Y : ℕ → Ω → ℝ)
    (hY : ∀ i, HasLaw (Y i) (gaussianReal 0 1) P) (hind : iIndepFun Y P) :
    TendstoInDistribution (ncPhaseRV Y) atTop (id : ℝ → ℝ) (fun _ => P) (gaussianReal 0 1) where
  forall_aemeasurable := fun n => aemeasurable_ncPhaseRV P Y (fun i => (hY i).aemeasurable) n
  aemeasurable_limit := aemeasurable_id
  tendsto := by
    refine tendsto_const_nhds.congr' ?_
    filter_upwards [eventually_gt_atTop 0] with n hn
    exact Subtype.ext (by
      change Measure.map id (gaussianReal 0 1) = Measure.map (ncPhaseRV Y n) P
      rw [Measure.map_id, (hasLaw_ncPhaseRV P Y hY hind n hn).map_eq])

/-! ### Convergence in distribution of the posterior moment generating function -/

omit [IsProbabilityMeasure P] in
theorem aemeasurable_ncFluctMGF (Y : ℕ → Ω → ℝ) (hY : ∀ i, AEMeasurable (Y i) P)
    (ρ : (Fin 2 → ℝ) → ℝ) (hρ : Continuous ρ) (θ : ℝ) (n : ℕ) :
    AEMeasurable (fun ω => ncFluctMGF n (fun i : Fin n => Y i ω) ρ θ) P := by
  rcases Nat.eq_zero_or_pos n with hn | hn
  · subst hn
    have : (fun ω => ncFluctMGF 0 (fun i : Fin 0 => Y i ω) ρ θ) =
        fun _ => ncFluctMGF 0 (fun i : Fin 0 => (0 : ℝ)) ρ θ :=
      funext fun ω => by
        congr 1
        exact funext fun i => i.elim0
    rw [this]
    exact aemeasurable_const
  · have : (fun ω => ncFluctMGF n (fun i : Fin n => Y i ω) ρ θ) =
        fun ω => ncRatio ρ (Real.sqrt n) (ncPhaseRV Y n ω) θ :=
      funext fun ω => ncFluctMGF_eq n hn _ ρ θ
    rw [this]
    exact (measurable_ncRatio ρ hρ _ θ).comp_aemeasurable (aemeasurable_ncPhaseRV P Y hY n)

/-- **Headline XX'' (convergence in distribution).** For `Yᵢ` i.i.d. `N(0,1)`, a continuous prior
density `ρ` on `(-1,1]²` with `ρ(0) > 0`, and any `θ`, the posterior moment generating function of
the fluctuation variable `√n x₀x₁` converges in distribution to `exp(Zθ + θ²/2)` with
`Z ~ N(0,1)`. -/
theorem ncFluctMGF_tendstoInDistribution (Y : ℕ → Ω → ℝ)
    (hY : ∀ i, HasLaw (Y i) (gaussianReal 0 1) P) (hind : iIndepFun Y P)
    (ρ : (Fin 2 → ℝ) → ℝ) (hρ : Continuous ρ) (hρ0 : 0 < ρ 0) (θ : ℝ) :
    TendstoInDistribution (fun n ω => ncFluctMGF n (fun i : Fin n => Y i ω) ρ θ) atTop
      (fun z : ℝ => Real.exp (z * θ + θ ^ 2 / 2)) (fun _ => P) (gaussianReal 0 1) := by
  have hg : Continuous fun z : ℝ => Real.exp (z * θ + θ ^ 2 / 2) := by fun_prop
  have hX := (tendstoInDistribution_ncPhaseRV P Y hY hind).continuous_comp hg
  have hD := ncFluctMGF_tendstoInMeasure P Y hY hind ρ hρ hρ0 θ
  have hmeas : ∀ n, AEMeasurable (fun ω => ncFluctMGF n (fun i : Fin n => Y i ω) ρ θ -
      Real.exp (ncPhaseRV Y n ω * θ + θ ^ 2 / 2)) P := fun n =>
    (aemeasurable_ncFluctMGF P Y (fun i => (hY i).aemeasurable) ρ hρ θ n).sub
      ((hg.measurable.comp_aemeasurable
        (aemeasurable_ncPhaseRV P Y (fun i => (hY i).aemeasurable) n)))
  have h := hX.add_of_tendstoInMeasure_const (c := 0) hD hmeas
  refine h.congr (fun n => ae_of_all _ fun ω => ?_) (ae_of_all _ fun z => ?_)
  · simp only [Pi.add_apply, Function.comp]
    ring
  · simp

end Laplace.Grammar
