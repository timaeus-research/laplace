/-
Copyright (c) 2026 Timaeus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Timaeus
-/
import Laplace.Multi.ActiveTruthSpectatorGeneral
import Laplace.Multi.ActiveTruthChart

/-!
# The chart-level active-truth term with spectator coordinates

Astra round 10, item (a): the spectator face theorem with general units applied to a chart of
the wall atlas whose coordinates split, through `e : Fin n ⊕ (Fin k ⊕ Fin 2) ≃ Fin m`, into `n`
spectators, `k` free active coordinates and the two solved active coordinates. The chart weight
and unit are jointly continuous, so their traces as the active coordinates tend to `0` are their
values at the point `bridgePt (specPt e ξ) u` (spectators `ξ`, active coordinates `0`, truth
`u`). The leading measure is the push-forward under `(ξ, u) ↦ rep(bridgePt (specPt e ξ) u)` of the
density `C ∏ ξ_l^{d_l − 1} u^{qη−1} (wt |b|) |a|^{-β}` on `(0,ρ)^n × (0,ρ)`, with
`C = A Γ(β) B^{-β} q D^{-qη} vol(F')/|det M|` (`activeTruthSpecMeasure`,
`tendsto_modelKernelOf_activeTruthSpectator`, `TermData.activeTruthSpectator`).
-/

open Real MeasureTheory Set Filter Topology
open scoped ENNReal Matrix

namespace Laplace.Multi

variable {m k n : ℕ}

/-- The chart point with spectator coordinates `ξ` and active coordinates `0`. -/
def specPt (e : Fin n ⊕ (Fin k ⊕ Fin 2) ≃ Fin m) (ξ : Fin n → ℝ) : Fin m → ℝ :=
  fun j ↦ Sum.elim ξ 0 (e.symm j)

theorem continuous_specPt (e : Fin n ⊕ (Fin k ⊕ Fin 2) ≃ Fin m) : Continuous (specPt e) := by
  refine continuous_pi fun j ↦ ?_
  rcases hj : e.symm j with l | l
  · simp only [specPt, hj, Sum.elim_inl]
    exact continuous_apply l
  · simp only [specPt, hj, Sum.elim_inr, Pi.zero_apply]
    exact continuous_const

theorem continuous_elim_reindex (e : Fin n ⊕ (Fin k ⊕ Fin 2) ≃ Fin m) (ξ : Fin n → ℝ) :
    Continuous fun x' : Fin k ⊕ Fin 2 → ℝ ↦ fun j ↦ Sum.elim ξ x' (e.symm j) := by
  refine continuous_pi fun j ↦ ?_
  rcases hj : e.symm j with l | l
  · simp only [Sum.elim_inl]
    exact continuous_const
  · simp only [Sum.elim_inr]
    exact continuous_apply l

namespace WallChartsData.Phase

variable {ℓ : Fin (m + 1)} {L' : Set (Fin (m + 1) → ℝ)} {D : WallChartsData m ℓ L'}
  {F : (Fin (m + 1) → ℝ) → ℝ} (P : D.Phase F) {i : D.ι} {ε : Fin m → Bool} {b : Bool}
  {σ γ β η : ℝ} {φ : (Fin (m + 1) → ℝ) → ℝ}

/-- The geometric constant of the active face in the presence of spectators: `vol(F')/|det M|`
for the solved pair chosen by `e`. -/
noncomputable def faceConstSpec (i : D.ι) (γ : ℝ) (e : Fin n ⊕ (Fin k ⊕ Fin 2) ≃ Fin m) : ℝ :=
  (volume (facePolytope (fun j ↦ (P.kappa i ∘ e) (Sum.inr j)) (fun j ↦ (D.Qexp i ∘ e) (Sum.inr j))
    (P.phaseExp i γ) γ)).toReal /
    |(transMat (fun j ↦ (P.kappa i ∘ e) (Sum.inr j)) (fun j ↦ (D.Qexp i ∘ e) (Sum.inr j))).det|

theorem faceConstSpec_nonneg (i : D.ι) (γ : ℝ) (e : Fin n ⊕ (Fin k ⊕ Fin 2) ≃ Fin m) :
    0 ≤ P.faceConstSpec i γ e :=
  div_nonneg ENNReal.toReal_nonneg (abs_nonneg _)

/-- The density of the spectator active-truth measure on `(spectators, truth)`, before the cut. -/
noncomputable def activeTruthSpecDensityFn (i : D.ι) (ε : Fin m → Bool) (b : Bool) (σ γ β η : ℝ)
    (e : Fin n ⊕ (Fin k ⊕ Fin 2) ≃ Fin m) (ξ : Fin n → ℝ) (u : ℝ) : ℝ :=
  P.constA i σ * Gamma β * P.constB i σ ^ (-β) * (D.q i (D.k i) : ℝ) *
    D.constD i σ ^ (-((D.q i (D.k i) : ℝ) * η)) * P.faceConstSpec i γ e *
    ((∏ l, ξ l ^ (specd β η (D.Qexp i ∘ e) (P.kappa i ∘ e) (P.rExp i ∘ e) l - 1)) *
      (u ^ ((D.q i (D.k i) : ℝ) * η - 1) *
        ((P.wt i (D.bridgePt i ε b (specPt e ξ) u) * |P.b i (D.bridgePt i ε b (specPt e ξ) u)|) *
          |P.a i (D.bridgePt i ε b (specPt e ξ) u)| ^ (-β))))

/-- The density of the spectator active-truth measure, cut to `(0,ρ)^n × (0,ρ)`. -/
noncomputable def activeTruthSpecDensity (i : D.ι) (ε : Fin m → Bool) (b : Bool) (σ γ β η : ℝ)
    (e : Fin n ⊕ (Fin k ⊕ Fin 2) ≃ Fin m) (p : (Fin n → ℝ) × ℝ) : ℝ :=
  (specBox n (D.ρ i) ×ˢ Ioo (0 : ℝ) (D.ρ i)).indicator
    (Function.uncurry (P.activeTruthSpecDensityFn i ε b σ γ β η e)) p

/-- The leading measure of an active-truth chart with spectators: the density pushed forward along
`(ξ, u) ↦ rep(bridgePt (specPt e ξ) u)`. -/
noncomputable def activeTruthSpecMeasure (i : D.ι) (ε : Fin m → Bool) (b : Bool) (σ γ β η : ℝ)
    (e : Fin n ⊕ (Fin k ⊕ Fin 2) ≃ Fin m) : Measure (Fin (m + 1) → ℝ) :=
  ((volume : Measure ((Fin n → ℝ) × ℝ)).withDensity fun p ↦
      ENNReal.ofReal (P.activeTruthSpecDensity i ε b σ γ β η e p)).map
    (fun p ↦ D.rep i (D.bridgePt i ε b (specPt e p.1) p.2))

theorem continuous_specTruthPt (i : D.ι) (ε : Fin m → Bool) (b : Bool)
    (e : Fin n ⊕ (Fin k ⊕ Fin 2) ≃ Fin m) :
    Continuous fun p : (Fin n → ℝ) × ℝ ↦ D.bridgePt i ε b (specPt e p.1) p.2 :=
  (D.continuous_bridgePt i ε b).comp
    (((continuous_specPt e).comp continuous_fst).prodMk continuous_snd)

theorem specTruthPt_mem_ball (i : D.ι) (ε : Fin m → Bool) (b : Bool)
    (e : Fin n ⊕ (Fin k ⊕ Fin 2) ≃ Fin m) {ξ : Fin n → ℝ} (hξ : ξ ∈ specBox n (D.ρ i)) {u : ℝ}
    (hu : u ∈ Ioo (0 : ℝ) (D.ρ i)) :
    D.bridgePt i ε b (specPt e ξ) u ∈ Metric.ball (0 : Fin (m + 1) → ℝ) (D.ρ i) := by
  refine D.bridgePt_mem_ball_of_abs_lt i ε b (D.ρ_pos i) (fun j ↦ ?_)
    (by rw [abs_of_pos hu.1]; exact hu.2)
  rcases hj : e.symm j with l | l
  · simp only [specPt, hj, Sum.elim_inl]
    have := (Set.mem_univ_pi.mp hξ) l
    rw [abs_of_pos this.1]
    exact this.2
  · simp only [specPt, hj, Sum.elim_inr, Pi.zero_apply, abs_zero]
    exact D.ρ_pos i

theorem measurable_activeTruthSpecDensityFn (i : D.ι) (ε : Fin m → Bool) (b : Bool)
    (σ γ β η : ℝ) (e : Fin n ⊕ (Fin k ⊕ Fin 2) ≃ Fin m) :
    Measurable (Function.uncurry (P.activeTruthSpecDensityFn i ε b σ γ β η e)) := by
  have hpt := continuous_specTruthPt (D := D) i ε b e
  have e1 : Function.uncurry (P.activeTruthSpecDensityFn i ε b σ γ β η e) =
      fun p : (Fin n → ℝ) × ℝ ↦ P.constA i σ * Gamma β * P.constB i σ ^ (-β) *
        (D.q i (D.k i) : ℝ) * D.constD i σ ^ (-((D.q i (D.k i) : ℝ) * η)) * P.faceConstSpec i γ e *
        ((∏ l, p.1 l ^ (specd β η (D.Qexp i ∘ e) (P.kappa i ∘ e) (P.rExp i ∘ e) l - 1)) *
          (p.2 ^ ((D.q i (D.k i) : ℝ) * η - 1) *
            ((P.wt i (D.bridgePt i ε b (specPt e p.1) p.2) *
                |P.b i (D.bridgePt i ε b (specPt e p.1) p.2)|) *
              |P.a i (D.bridgePt i ε b (specPt e p.1) p.2)| ^ (-β)))) := by
    funext p
    rfl
  rw [e1]
  refine measurable_const.mul ?_
  refine (Finset.measurable_prod _ fun l _ ↦ ((measurable_pi_apply l).comp measurable_fst).pow_const
    _).mul ?_
  refine (measurable_snd.pow_const _).mul ?_
  refine (((P.wt_cont i).comp hpt).mul (continuous_abs.comp ((P.b_cont i).comp hpt))).measurable.mul
    ?_
  exact ((continuous_abs.comp ((P.a_cont i).comp hpt)).measurable).pow_const _

theorem measurable_activeTruthSpecDensity (i : D.ι) (ε : Fin m → Bool) (b : Bool) (σ γ β η : ℝ)
    (e : Fin n ⊕ (Fin k ⊕ Fin 2) ≃ Fin m) :
    Measurable (P.activeTruthSpecDensity i ε b σ γ β η e) :=
  (P.measurable_activeTruthSpecDensityFn i ε b σ γ β η e).indicator
    ((measurableSet_specBox n _).prod measurableSet_Ioo)

theorem activeTruthSpecDensity_nonneg (i : D.ι) (ε : Fin m → Bool) (b : Bool) (σ γ η : ℝ)
    {β : ℝ} (hβ : 0 < β) (e : Fin n ⊕ (Fin k ⊕ Fin 2) ≃ Fin m) (p : (Fin n → ℝ) × ℝ) :
    0 ≤ P.activeTruthSpecDensity i ε b σ γ β η e p := by
  unfold activeTruthSpecDensity
  refine Set.indicator_nonneg (fun p hp ↦ ?_) p
  rw [Function.uncurry_apply_pair]
  unfold activeTruthSpecDensityFn
  have h1 := P.constA_nonneg (i := i) (σ := σ)
  have h2 := (Real.Gamma_pos_of_pos hβ).le
  have h3 : 0 ≤ P.constB i σ ^ (-β) := Real.rpow_nonneg (Real.rpow_nonneg (abs_nonneg _) _) _
  have h4 : 0 ≤ D.constD i σ ^ (-((D.q i (D.k i) : ℝ) * η)) :=
    Real.rpow_nonneg (D.constD_nonneg i σ) _
  have h5 := P.faceConstSpec_nonneg i γ e
  have h6 : 0 ≤ p.2 ^ ((D.q i (D.k i) : ℝ) * η - 1) := Real.rpow_nonneg hp.2.1.le _
  have h7 : 0 ≤ P.wt i (D.bridgePt i ε b (specPt e p.1) p.2) *
      |P.b i (D.bridgePt i ε b (specPt e p.1) p.2)| :=
    mul_nonneg (P.wt_nonneg i _) (abs_nonneg _)
  have h8 : 0 ≤ |P.a i (D.bridgePt i ε b (specPt e p.1) p.2)| ^ (-β) :=
    Real.rpow_nonneg (abs_nonneg _) _
  have h9 : (0 : ℝ) ≤ (D.q i (D.k i) : ℝ) := Nat.cast_nonneg _
  have h10 : 0 ≤ ∏ l, p.1 l ^ (specd β η (D.Qexp i ∘ e) (P.kappa i ∘ e) (P.rExp i ∘ e) l - 1) :=
    Finset.prod_nonneg fun l _ ↦ Real.rpow_nonneg ((Set.mem_univ_pi.mp hp.1) l).1.le _
  exact mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg h1 h2) h3) h9) h4)
    h5) (mul_nonneg h10 (mul_nonneg h6 (mul_nonneg h7 h8)))

theorem integral_activeTruthSpecMeasure (i : D.ι) (ε : Fin m → Bool) (b : Bool) (σ γ η : ℝ)
    {β : ℝ} (hβ : 0 < β) (e : Fin n ⊕ (Fin k ⊕ Fin 2) ≃ Fin m) (hφm : Measurable φ) :
    ∫ x, φ x ∂(P.activeTruthSpecMeasure i ε b σ γ β η e) =
      ∫ p : (Fin n → ℝ) × ℝ, φ (D.rep i (D.bridgePt i ε b (specPt e p.1) p.2)) *
        P.activeTruthSpecDensity i ε b σ γ β η e p := by
  unfold activeTruthSpecMeasure
  have hm : Measurable fun p ↦ ENNReal.ofReal (P.activeTruthSpecDensity i ε b σ γ β η e p) :=
    ENNReal.measurable_ofReal.comp (P.measurable_activeTruthSpecDensity i ε b σ γ β η e)
  have hmap : Measurable fun p : (Fin n → ℝ) × ℝ ↦ D.rep i (D.bridgePt i ε b (specPt e p.1) p.2) :=
    (D.rep_cont i).measurable.comp (continuous_specTruthPt (D := D) i ε b e).measurable
  rw [integral_map hmap.aemeasurable hφm.aestronglyMeasurable,
    integral_withDensity_eq_integral_toReal_smul₀ hm.aemeasurable
      (ae_of_all _ fun _ ↦ ENNReal.ofReal_lt_top)]
  refine integral_congr_ae (Eventually.of_forall fun p ↦ ?_)
  simp only [smul_eq_mul]
  rw [ENNReal.toReal_ofReal (P.activeTruthSpecDensity_nonneg i ε b σ γ η hβ e p), mul_comm]

/-- The density is integrable: the product density `∏ ξ^{d−1} u^{qη−1}` against the bounded
chart factors. -/
theorem integrable_activeTruthSpecDensity (i : D.ι) (ε : Fin m → Bool) (b : Bool) (σ γ : ℝ)
    {β η : ℝ} (hβ : 0 < β) (hη : 0 < η) (e : Fin n ⊕ (Fin k ⊕ Fin 2) ≃ Fin m)
    (hd : ∀ l, 0 < specd β η (D.Qexp i ∘ e) (P.kappa i ∘ e) (P.rExp i ∘ e) l) :
    Integrable (P.activeTruthSpecDensity i ε b σ γ β η e) := by
  have hρ := D.ρ_pos i
  have hq : (0 : ℝ) < D.q i (D.k i) := Nat.cast_pos.mpr (D.q_pos i)
  have hdq : 0 < (D.q i (D.k i) : ℝ) * η := mul_pos hq hη
  have hset : MeasurableSet (specBox n (D.ρ i) ×ˢ Ioo (0 : ℝ) (D.ρ i)) :=
    (measurableSet_specBox n _).prod measurableSet_Ioo
  unfold activeTruthSpecDensity
  rw [integrable_indicator_iff hset]
  have hg : ∀ l, IntegrableOn
      (fun x : ℝ ↦ x ^ (specd β η (D.Qexp i ∘ e) (P.kappa i ∘ e) (P.rExp i ∘ e) l - 1))
      (Ioo (0 : ℝ) (D.ρ i)) := by
    intro l
    have := integrableOn_rpow_mul_log_pow (hd l) zero_le_one le_rfl hρ 0
    refine this.congr_fun (fun x _ ↦ ?_) measurableSet_Ioo
    simp
  have hP : Integrable fun ξ : Fin n → ℝ ↦ ∏ l, (Ioo (0 : ℝ) (D.ρ i)).indicator
      (fun x ↦ x ^ (specd β η (D.Qexp i ∘ e) (P.kappa i ∘ e) (P.rExp i ∘ e) l - 1)) (ξ l) := by
    have := Integrable.fintype_prod (μ := fun _ : Fin n ↦ (volume : Measure ℝ))
      (f := fun l x ↦ (Ioo (0 : ℝ) (D.ρ i)).indicator
        (fun x ↦ x ^ (specd β η (D.Qexp i ∘ e) (P.kappa i ∘ e) (P.rExp i ∘ e) l - 1)) x)
      (fun l ↦ (hg l).integrable_indicator measurableSet_Ioo)
    rw [volume_pi]
    exact this
  have hu : Integrable ((Ioo (0 : ℝ) (D.ρ i)).indicator
      fun u : ℝ ↦ u ^ ((D.q i (D.k i) : ℝ) * η - 1)) := by
    have := integrableOn_rpow_mul_log_pow hdq zero_le_one le_rfl hρ 0
    refine (this.congr_fun (fun x _ ↦ ?_) measurableSet_Ioo).integrable_indicator measurableSet_Ioo
    simp
  have hprod : Integrable (fun p : (Fin n → ℝ) × ℝ ↦
      (∏ l, (Ioo (0 : ℝ) (D.ρ i)).indicator
        (fun x ↦ x ^ (specd β η (D.Qexp i ∘ e) (P.kappa i ∘ e) (P.rExp i ∘ e) l - 1)) (p.1 l)) *
      (Ioo (0 : ℝ) (D.ρ i)).indicator (fun u : ℝ ↦ u ^ ((D.q i (D.k i) : ℝ) * η - 1)) p.2) := by
    rw [Measure.volume_eq_prod]
    exact hP.mul_prod hu
  obtain ⟨C, hC⟩ : ∃ C : ℝ, C = P.constA i σ * Gamma β * P.constB i σ ^ (-β) *
    (D.q i (D.k i) : ℝ) * D.constD i σ ^ (-((D.q i (D.k i) : ℝ) * η)) * P.faceConstSpec i γ e :=
    ⟨_, rfl⟩
  refine (hprod.const_mul (|C| * (P.Mb i * P.ma i ^ (-β)))).integrableOn.mono' ?_ ?_
  · exact (P.measurable_activeTruthSpecDensityFn i ε b σ γ β η e).aestronglyMeasurable
  · rw [ae_restrict_iff' hset]
    refine Eventually.of_forall fun p hp ↦ ?_
    have hξ : p.1 ∈ specBox n (D.ρ i) := hp.1
    have hu' : p.2 ∈ Ioo (0 : ℝ) (D.ρ i) := hp.2
    rw [prod_indicator_Ioo_of_mem _ hξ, Set.indicator_of_mem hu', Function.uncurry_apply_pair]
    have hcb : D.bridgePt i ε b (specPt e p.1) p.2 ∈
        Metric.closedBall (0 : Fin (m + 1) → ℝ) (D.ρ i) :=
      Metric.ball_subset_closedBall (specTruthPt_mem_ball (D := D) i ε b e hξ hu')
    have hb := (P.b_bounds i _ hcb).2
    have ha := (P.a_bounds i _ hcb).1
    have hu0 : 0 ≤ p.2 ^ ((D.q i (D.k i) : ℝ) * η - 1) := Real.rpow_nonneg hu'.1.le _
    have hP0 : 0 ≤ ∏ l, p.1 l ^ (specd β η (D.Qexp i ∘ e) (P.kappa i ∘ e) (P.rExp i ∘ e) l - 1) :=
      Finset.prod_nonneg fun l _ ↦ Real.rpow_nonneg ((Set.mem_univ_pi.mp hξ) l).1.le _
    have hapow : |P.a i (D.bridgePt i ε b (specPt e p.1) p.2)| ^ (-β) ≤ P.ma i ^ (-β) := by
      rw [Real.rpow_neg (abs_nonneg _), Real.rpow_neg (P.ma_pos i).le]
      exact inv_anti₀ (Real.rpow_pos_of_pos (P.ma_pos i) _)
        (Real.rpow_le_rpow (P.ma_pos i).le ha hβ.le)
    have hwb : P.wt i (D.bridgePt i ε b (specPt e p.1) p.2) *
        |P.b i (D.bridgePt i ε b (specPt e p.1) p.2)| ≤ P.Mb i := by
      calc P.wt i (D.bridgePt i ε b (specPt e p.1) p.2) *
            |P.b i (D.bridgePt i ε b (specPt e p.1) p.2)| ≤ 1 * P.Mb i :=
            mul_le_mul (P.wt_le_one i _) hb (abs_nonneg _) zero_le_one
        _ = P.Mb i := one_mul _
    have h7 : 0 ≤ P.wt i (D.bridgePt i ε b (specPt e p.1) p.2) *
        |P.b i (D.bridgePt i ε b (specPt e p.1) p.2)| :=
      mul_nonneg (P.wt_nonneg i _) (abs_nonneg _)
    have h8 : 0 ≤ |P.a i (D.bridgePt i ε b (specPt e p.1) p.2)| ^ (-β) :=
      Real.rpow_nonneg (abs_nonneg _) _
    unfold activeTruthSpecDensityFn
    rw [hC, Real.norm_eq_abs, abs_mul,
      abs_of_nonneg (mul_nonneg hP0 (mul_nonneg hu0 (mul_nonneg h7 h8)))]
    calc |P.constA i σ * Gamma β * P.constB i σ ^ (-β) * (D.q i (D.k i) : ℝ) *
          D.constD i σ ^ (-((D.q i (D.k i) : ℝ) * η)) * P.faceConstSpec i γ e| *
          ((∏ l, p.1 l ^ (specd β η (D.Qexp i ∘ e) (P.kappa i ∘ e) (P.rExp i ∘ e) l - 1)) *
            (p.2 ^ ((D.q i (D.k i) : ℝ) * η - 1) *
              (P.wt i (D.bridgePt i ε b (specPt e p.1) p.2) *
                |P.b i (D.bridgePt i ε b (specPt e p.1) p.2)| *
                |P.a i (D.bridgePt i ε b (specPt e p.1) p.2)| ^ (-β))))
        ≤ |P.constA i σ * Gamma β * P.constB i σ ^ (-β) * (D.q i (D.k i) : ℝ) *
          D.constD i σ ^ (-((D.q i (D.k i) : ℝ) * η)) * P.faceConstSpec i γ e| *
          ((∏ l, p.1 l ^ (specd β η (D.Qexp i ∘ e) (P.kappa i ∘ e) (P.rExp i ∘ e) l - 1)) *
            (p.2 ^ ((D.q i (D.k i) : ℝ) * η - 1) * (P.Mb i * P.ma i ^ (-β)))) :=
          mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left
            (mul_le_mul hwb hapow h8 P.Mb_nonneg) hu0) hP0) (abs_nonneg _)
      _ = _ := by ring

theorem isFiniteMeasure_activeTruthSpecMeasure (i : D.ι) (ε : Fin m → Bool) (b : Bool) (σ γ : ℝ)
    {β η : ℝ} (hβ : 0 < β) (hη : 0 < η) (e : Fin n ⊕ (Fin k ⊕ Fin 2) ≃ Fin m)
    (hd : ∀ l, 0 < specd β η (D.Qexp i ∘ e) (P.kappa i ∘ e) (P.rExp i ∘ e) l) :
    IsFiniteMeasure (P.activeTruthSpecMeasure i ε b σ γ β η e) := by
  unfold activeTruthSpecMeasure
  have := isFiniteMeasure_withDensity_ofReal
    (P.integrable_activeTruthSpecDensity i ε b σ γ hβ hη e hd).hasFiniteIntegral
  infer_instance

/-- **The active-truth chart term with spectators**: the normalised model kernel of an active-truth
chart with `n` spectator coordinates converges to the integral of the observable against the
spectator active-truth measure. -/
theorem tendsto_modelKernelOf_activeTruthSpectator (e : Fin n ⊕ (Fin k ⊕ Fin 2) ≃ Fin m)
    (hσ : σ ≠ 0) (hβ : 0 < β) (hη : 0 < η) (hδ : 0 ≤ P.phaseExp i γ) (hκ : ∀ j, 0 < P.kappa i j)
    (hΔ : (transMat (fun j ↦ (P.kappa i ∘ e) (Sum.inr j))
      (fun j ↦ (D.Qexp i ∘ e) (Sum.inr j))).det ≠ 0)
    (hc₀ : fibreCoef (fun j ↦ (P.kappa i ∘ e) (Sum.inr j)) (fun j ↦ (D.Qexp i ∘ e) (Sum.inr j))
        0 ≠ 0 ∨
      fibreA (fun j ↦ (P.kappa i ∘ e) (Sum.inr j)) (fun j ↦ (D.Qexp i ∘ e) (Sum.inr j))
        (P.phaseExp i γ) γ 0 ≠ 0)
    (hc₁ : fibreCoef (fun j ↦ (P.kappa i ∘ e) (Sum.inr j)) (fun j ↦ (D.Qexp i ∘ e) (Sum.inr j))
        1 ≠ 0 ∨
      fibreA (fun j ↦ (P.kappa i ∘ e) (Sum.inr j)) (fun j ↦ (D.Qexp i ∘ e) (Sum.inr j))
        (P.phaseExp i γ) γ 1 ≠ 0)
    (hr : ∀ j, P.rExp i (e (Sum.inr j)) + 1 =
      β * P.kappa i (e (Sum.inr j)) - η * D.Qexp i (e (Sum.inr j)))
    (hd : ∀ l, 0 < specd β η (D.Qexp i ∘ e) (P.kappa i ∘ e) (P.rExp i ∘ e) l)
    (hφc : Continuous φ) (hφ : ∀ z, 0 ≤ φ z) {Mφ : ℝ} (hMφ : ∀ z, φ z ≤ Mφ)
    (hφL : ∀ z, φ z ≠ 0 → z ∈ L') :
    Tendsto (fun t ↦ t ^ (γ * P.pExp i + (β * P.phaseExp i γ - η * γ)) / log t ^ k *
        P.modelKernelOf i φ ε b t γ σ) atTop
      (𝓝 (∫ x, φ x ∂(P.activeTruthSpecMeasure i ε b σ γ β η e))) := by
  have hρ := D.ρ_pos i
  have hq : (0 : ℝ) < D.q i (D.k i) := Nat.cast_pos.mpr (D.q_pos i)
  have hDpos : 0 < D.constD i σ := Real.rpow_pos_of_pos (abs_pos.mpr hσ) _
  have hB := P.constB_pos (i := i) hσ
  set We : (Fin n ⊕ (Fin k ⊕ Fin 2) → ℝ) → ℝ → ℝ :=
    fun y v ↦ P.weightFn i φ ε b (fun j ↦ y (e.symm j)) v with hWe
  set ae' : (Fin n ⊕ (Fin k ⊕ Fin 2) → ℝ) → ℝ → ℝ :=
    fun y v ↦ max (P.unitFn i ε b (fun j ↦ y (e.symm j)) v) (P.ma i) with hae
  set Wtr : (Fin n → ℝ) → ℝ → ℝ := fun ξ u ↦ P.weightFn i φ ε b (specPt e ξ) u with hWtr
  set atr : (Fin n → ℝ) → ℝ → ℝ := fun ξ u ↦ max (P.unitFn i ε b (specPt e ξ) u) (P.ma i)
    with hatr
  -- the reindexed kernel with the unit modified off the domain
  have hK : ∀ᶠ t in atTop, P.modelKernelOf i φ ε b t γ σ =
      modelKernel (D.ρ i) (P.constA i σ) (P.constB i σ) (D.constD i σ) γ (P.pExp i)
        (D.q i (D.k i)) (P.phaseExp i γ) (D.Qexp i ∘ e) (P.kappa i ∘ e) (P.rExp i ∘ e)
        We ae' t := by
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with t ht
    unfold modelKernelOf
    rw [modelKernel_reindex e]
    refine modelKernel_congr_unit fun x hx ↦ ?_
    rw [hae]
    simp only
    symm
    refine max_eq_left (P.ma_le_unitFn_of_mem_ball ?_)
    have hx0 : ∀ j, 0 < x j := fun j ↦ ((Set.mem_univ_pi.mp hx.1) j).1
    have hcut : cutVar (D.constD i σ) γ (D.q i (D.k i)) (D.Qexp i ∘ e) t x < D.ρ i := hx.2
    have hcut0 : 0 ≤ cutVar (D.constD i σ) γ (D.q i (D.k i)) (D.Qexp i ∘ e) t x := by
      unfold cutVar
      exact mul_nonneg (mul_nonneg hDpos.le (Real.rpow_nonneg ht.le _))
        (Finset.prod_nonneg fun j _ ↦ Real.rpow_nonneg (hx0 j).le _)
    exact (D.bridgePt_mem_ball_iff i ε b hρ (fun j ↦ hx0 _) hcut0).mpr
      ⟨fun j ↦ ((Set.mem_univ_pi.mp hx.1) _).2, hcut⟩
  -- the traces
  have hmap : ∀ (ξ : Fin n → ℝ) (u : ℝ), Tendsto
      (fun x' : Fin k ⊕ Fin 2 → ℝ ↦ ((fun j ↦ Sum.elim ξ x' (e.symm j)), u)) (𝓝 0)
      (𝓝 (specPt e ξ, u)) := fun ξ u ↦
    ((continuous_elim_reindex e ξ).tendsto 0).prodMk_nhds tendsto_const_nhds
  have hWtrc : ∀ ξ ∈ specBox n (D.ρ i), ∀ u ∈ Ioo (0 : ℝ) (D.ρ i),
      Tendsto (fun x' ↦ We (Sum.elim ξ x') u)
        (𝓝[Set.pi univ fun _ : Fin k ⊕ Fin 2 ↦ Ioo (0 : ℝ) (D.ρ i)] 0) (𝓝 (Wtr ξ u)) :=
    fun ξ hξ u hu ↦
      (((P.continuousAt_weightFn hφc hφL (specTruthPt_mem_ball (D := D) i ε b e hξ hu)).tendsto.comp
        (hmap ξ u))).mono_left nhdsWithin_le_nhds
  have hatrc : ∀ ξ ∈ specBox n (D.ρ i), ∀ u ∈ Ioo (0 : ℝ) (D.ρ i),
      Tendsto (fun x' ↦ ae' (Sum.elim ξ x') u)
        (𝓝[Set.pi univ fun _ : Fin k ⊕ Fin 2 ↦ Ioo (0 : ℝ) (D.ρ i)] 0) (𝓝 (atr ξ u)) :=
    fun ξ _ u _ ↦ by
      have h1 : Tendsto (fun x' ↦ ae' (Sum.elim ξ x') u) (𝓝 0) (𝓝 (atr ξ u)) :=
        ((P.continuousAt_unitFn (i := i) (ε := ε) (b := b) (specPt e ξ, u)).tendsto.comp
          (hmap ξ u)).max (tendsto_const_nhds (x := P.ma i))
      exact h1.mono_left nhdsWithin_le_nhds
  have hgen := tendsto_modelKernel_general_spectator (m := n) (k := k) (ρ := D.ρ i)
    (A := P.constA i σ) (B := P.constB i σ) (D := D.constD i σ) (γ := γ) (p := P.pExp i)
    (q := D.q i (D.k i)) (δ := P.phaseExp i γ) (β := β) (η := η) (Q := D.Qexp i ∘ e)
    (κ := P.kappa i ∘ e) (r := P.rExp i ∘ e) (W := We) (a := ae') (Wstar := Mφ * P.Mb i)
    (amin := P.ma i) (Wtr := Wtr) (atr := atr)
    hρ hDpos hq hB hβ hη hδ (fun j ↦ hκ _) hΔ hc₀ hc₁ (fun j ↦ hr j) hd (P.ma_pos i)
    ((P.measurable_weightFn hφc.measurable).comp
      (((continuous_reindex e).measurable.comp measurable_fst).prodMk measurable_snd))
    ((P.measurable_unitFn.comp
      (((continuous_reindex e).measurable.comp measurable_fst).prodMk measurable_snd)).max
      measurable_const)
    (fun x u ↦ ⟨P.weightFn_nonneg hφ _ _, (le_abs_self _).trans (P.abs_weightFn_le hφ hMφ _ _)⟩)
    (fun _ _ ↦ le_max_right _ _)
    ((P.measurable_weightFn hφc.measurable).comp
      (((continuous_specPt e).measurable.comp measurable_fst).prodMk measurable_snd))
    ((P.measurable_unitFn.comp
      (((continuous_specPt e).measurable.comp measurable_fst).prodMk measurable_snd)).max
      measurable_const)
    (fun ξ u _ ↦ ⟨P.weightFn_nonneg hφ _ _, (le_abs_self _).trans (P.abs_weightFn_le hφ hMφ _ _)⟩)
    (fun _ _ _ ↦ le_max_right _ _) (ae_of_all _ hWtrc) (ae_of_all _ hatrc)
  -- the limit value is the integral against the spectator active-truth measure
  obtain ⟨C, hC⟩ : ∃ C : ℝ, C = P.constA i σ * Gamma β * P.constB i σ ^ (-β) *
    (D.q i (D.k i) : ℝ) * D.constD i σ ^ (-((D.q i (D.k i) : ℝ) * η)) * P.faceConstSpec i γ e :=
    ⟨_, rfl⟩
  have hval : ∫ x, φ x ∂(P.activeTruthSpecMeasure i ε b σ γ β η e) =
      P.constA i σ * Gamma β * P.constB i σ ^ (-β) * (D.q i (D.k i) : ℝ) *
        D.constD i σ ^ (-((D.q i (D.k i) : ℝ) * η)) *
        (volume (facePolytope (fun j ↦ (P.kappa i ∘ e) (Sum.inr j))
          (fun j ↦ (D.Qexp i ∘ e) (Sum.inr j)) (P.phaseExp i γ) γ)).toReal /
        |(transMat (fun j ↦ (P.kappa i ∘ e) (Sum.inr j))
          (fun j ↦ (D.Qexp i ∘ e) (Sum.inr j))).det| *
        ∫ ξ in specBox n (D.ρ i),
          (∏ l, ξ l ^ (specd β η (D.Qexp i ∘ e) (P.kappa i ∘ e) (P.rExp i ∘ e) l - 1)) *
            ∫ u in Ioo (0 : ℝ) (D.ρ i), u ^ ((D.q i (D.k i) : ℝ) * η - 1) *
              (Wtr ξ u * atr ξ u ^ (-β)) := by
    rw [P.integral_activeTruthSpecMeasure i ε b σ γ η hβ e hφc.measurable]
    have hint : Integrable (fun p : (Fin n → ℝ) × ℝ ↦
        φ (D.rep i (D.bridgePt i ε b (specPt e p.1) p.2)) *
          P.activeTruthSpecDensity i ε b σ γ β η e p) := by
      refine Integrable.bdd_mul (c := Mφ)
        (P.integrable_activeTruthSpecDensity i ε b σ γ hβ hη e hd) ?_
        (Eventually.of_forall fun p ↦ ?_)
      · exact (hφc.comp ((D.rep_cont i).comp
          (continuous_specTruthPt (D := D) i ε b e))).measurable.aestronglyMeasurable
      · rw [Real.norm_eq_abs, abs_of_nonneg (hφ _)]
        exact hMφ _
    rw [Measure.volume_eq_prod (Fin n → ℝ) ℝ] at hint ⊢
    rw [integral_prod _ hint]
    have hout : ∀ ξ : Fin n → ℝ,
        (∫ u, φ (D.rep i (D.bridgePt i ε b (specPt e ξ) u)) *
          P.activeTruthSpecDensity i ε b σ γ β η e (ξ, u)) =
        (specBox n (D.ρ i)).indicator (fun ξ ↦ C *
          ((∏ l, ξ l ^ (specd β η (D.Qexp i ∘ e) (P.kappa i ∘ e) (P.rExp i ∘ e) l - 1)) *
            ∫ u in Ioo (0 : ℝ) (D.ρ i), u ^ ((D.q i (D.k i) : ℝ) * η - 1) *
              (Wtr ξ u * atr ξ u ^ (-β)))) ξ := by
      intro ξ
      by_cases hξ : ξ ∈ specBox n (D.ρ i)
      · rw [Set.indicator_of_mem hξ]
        have hpt : ∀ u, P.activeTruthSpecDensity i ε b σ γ β η e (ξ, u) =
            (Ioo (0 : ℝ) (D.ρ i)).indicator
              (fun u ↦ P.activeTruthSpecDensityFn i ε b σ γ β η e ξ u) u := by
          intro u
          unfold activeTruthSpecDensity
          by_cases hu : u ∈ Ioo (0 : ℝ) (D.ρ i)
          · rw [Set.indicator_of_mem (Set.mk_mem_prod hξ hu), Set.indicator_of_mem hu,
              Function.uncurry_apply_pair]
          · rw [Set.indicator_of_notMem (s := specBox n (D.ρ i) ×ˢ Ioo (0 : ℝ) (D.ρ i))
              (fun h ↦ hu h.2), Set.indicator_of_notMem hu]
        simp_rw [hpt]
        simp_rw [← Set.indicator_mul_right _
          (fun u ↦ φ (D.rep i (D.bridgePt i ε b (specPt e ξ) u)))]
        rw [integral_indicator measurableSet_Ioo, ← mul_assoc, ← integral_const_mul]
        refine setIntegral_congr_fun measurableSet_Ioo fun u hu ↦ ?_
        have hball := specTruthPt_mem_ball (D := D) i ε b e hξ hu
        have hcb : D.bridgePt i ε b (specPt e ξ) u ∈
            Metric.closedBall (0 : Fin (m + 1) → ℝ) (D.ρ i) := Metric.ball_subset_closedBall hball
        simp only [hWtr, hatr]
        rw [P.weightFn_eq_of_mem_closedBall hφL hcb, max_eq_left (P.ma_le_unitFn_of_mem_ball hball)]
        unfold activeTruthSpecDensityFn unitFn
        rw [hC]
        ring
      · rw [Set.indicator_of_notMem hξ]
        have hpt : ∀ u, P.activeTruthSpecDensity i ε b σ γ β η e (ξ, u) = 0 := fun u ↦
          Set.indicator_of_notMem (s := specBox n (D.ρ i) ×ˢ Ioo (0 : ℝ) (D.ρ i))
            (fun h ↦ hξ h.1) _
        simp_rw [hpt, mul_zero, integral_zero]
    simp_rw [hout]
    rw [integral_indicator (measurableSet_specBox n _), ← integral_const_mul]
    congr 1
    rw [hC]
    unfold faceConstSpec
    ring
  rw [hval]
  refine hgen.congr' ?_
  filter_upwards [hK] with t ht
  rw [ht]

open scoped Classical in
/-- **The active-truth term with spectators**: `(γp + βδ − ηγ, k, activeTruthSpecMeasure)`. -/
noncomputable def TermData.activeTruthSpectator (e : Fin n ⊕ (Fin k ⊕ Fin 2) ≃ Fin m)
    (hσ : σ ≠ 0) {p : WallChartsData.Phase.TermIdx D} (hadm : D.admissible p.1 p.2.1 p.2.2 σ)
    (hβ : 0 < β) (hη : 0 < η) (hδ : 0 ≤ P.phaseExp p.1 γ) (hκ : ∀ j, 0 < P.kappa p.1 j)
    (hΔ : (transMat (fun j ↦ (P.kappa p.1 ∘ e) (Sum.inr j))
      (fun j ↦ (D.Qexp p.1 ∘ e) (Sum.inr j))).det ≠ 0)
    (hc₀ : fibreCoef (fun j ↦ (P.kappa p.1 ∘ e) (Sum.inr j))
        (fun j ↦ (D.Qexp p.1 ∘ e) (Sum.inr j)) 0 ≠ 0 ∨
      fibreA (fun j ↦ (P.kappa p.1 ∘ e) (Sum.inr j)) (fun j ↦ (D.Qexp p.1 ∘ e) (Sum.inr j))
        (P.phaseExp p.1 γ) γ 0 ≠ 0)
    (hc₁ : fibreCoef (fun j ↦ (P.kappa p.1 ∘ e) (Sum.inr j))
        (fun j ↦ (D.Qexp p.1 ∘ e) (Sum.inr j)) 1 ≠ 0 ∨
      fibreA (fun j ↦ (P.kappa p.1 ∘ e) (Sum.inr j)) (fun j ↦ (D.Qexp p.1 ∘ e) (Sum.inr j))
        (P.phaseExp p.1 γ) γ 1 ≠ 0)
    (hr : ∀ j, P.rExp p.1 (e (Sum.inr j)) + 1 =
      β * P.kappa p.1 (e (Sum.inr j)) - η * D.Qexp p.1 (e (Sum.inr j)))
    (hd : ∀ l, 0 < specd β η (D.Qexp p.1 ∘ e) (P.kappa p.1 ∘ e) (P.rExp p.1 ∘ e) l) :
    P.TermData σ γ p where
  lam := γ * P.pExp p.1 + (β * P.phaseExp p.1 γ - η * γ)
  kk := k
  μ := P.activeTruthSpecMeasure p.1 p.2.1 p.2.2 σ γ β η e
  finite := P.isFiniteMeasure_activeTruthSpecMeasure p.1 p.2.1 p.2.2 σ γ hβ hη e hd
  tendsto := fun φ hφc hφ ⟨M, hM⟩ hφL ↦ by
    have h := P.tendsto_modelKernelOf_activeTruthSpectator (ε := p.2.1) (b := p.2.2) e hσ hβ hη
      hδ hκ hΔ hc₀ hc₁ hr hd hφc hφ hM hφL
    refine h.congr' (Eventually.of_forall fun t ↦ ?_)
    unfold termKernel
    simp only [if_pos hadm]

end WallChartsData.Phase

end Laplace.Multi
