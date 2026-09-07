/-
Copyright (c) 2026 Timaeus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Laplace.Grammar.PhaseCoeffLipschitz

/-!
# Uniform convergence of the normalised chart integral on compact input sets

Unit 211 (programme A2, step 3). Inputs are now points of the Polish space
`E = C([0,1]^d, ℝ) × C([0,1]^d, ℝ)` (phase, amplitude) with the sup metric; a continuous function
on the closed cube is extended to `ℝ^d` by the coordinatewise clamp `u ↦ (max 0 (min 1 uᵢ))ᵢ`
(`extCube`), which is continuous, bounded by the sup norm, and the identity on the cube. With
`F_N(x) = chartIntegral (extCube x.1) (extCube x.2) / leadScale` and `F(x) = phaseCoeff …`:

* `tendsto_normChart` — pointwise convergence `F_N(x) → F(x)` (Headline XIII);
* `normChart_lipschitz_eventually`, `limChart_lipschitz` — Lipschitz on the closed ball of
  radius `R` in `E`, uniformly in `N` for `N ≥ N₀(R)` (units 209–210);
* `tendstoUniformlyOn_normChart` — **uniform convergence on every compact `K ⊆ E`**, by the
  finite-net argument: `K` is bounded and totally bounded, equi-Lipschitz on the ball plus
  pointwise convergence at the finitely many net points gives uniformity.

This is the deterministic input to the random-phase transfer (unit 212). Zero `sorry`/`axiom`.
-/

open MeasureTheory Filter Topology Real Set

namespace Laplace.Grammar

instance compactSpace_closedCube (d : ℕ) : CompactSpace (closedCube d) :=
  isCompact_iff_compactSpace.mp (isCompact_closedCube d)

/-- Coordinatewise clamp of `ℝ^d` onto the closed cube. -/
def clampCube (d : ℕ) (x : Fin d → ℝ) : closedCube d :=
  ⟨fun i => max 0 (min 1 (x i)), fun _ _ =>
    ⟨le_max_left _ _, max_le zero_le_one (min_le_left _ _)⟩⟩

theorem continuous_clampCube (d : ℕ) : Continuous (clampCube d) :=
  Continuous.subtype_mk (continuous_pi fun i =>
    continuous_const.max (continuous_const.min (continuous_apply i))) _

theorem clampCube_of_mem {d : ℕ} {x : Fin d → ℝ} (hx : x ∈ closedCube d) :
    ((clampCube d x : closedCube d) : Fin d → ℝ) = x := by
  funext i
  have h := hx i (mem_univ i)
  simp only [clampCube]
  rw [min_eq_right h.2, max_eq_right h.1]

/-- Extension of a continuous function on the closed cube to `ℝ^d` by clamping. -/
noncomputable def extCube {d : ℕ} (f : C(closedCube d, ℝ)) : (Fin d → ℝ) → ℝ :=
  fun x => f (clampCube d x)

theorem continuous_extCube {d : ℕ} (f : C(closedCube d, ℝ)) : Continuous (extCube f) :=
  f.continuous.comp (continuous_clampCube d)

theorem abs_extCube_le {d : ℕ} (f : C(closedCube d, ℝ)) (x : Fin d → ℝ) : |extCube f x| ≤ ‖f‖ := by
  have := f.norm_coe_le_norm (clampCube d x)
  rwa [Real.norm_eq_abs] at this

theorem abs_extCube_sub_le {d : ℕ} (f g : C(closedCube d, ℝ)) (x : Fin d → ℝ) :
    |extCube f x - extCube g x| ≤ dist f g := by
  have := ContinuousMap.dist_apply_le_dist (f := f) (g := g) (clampCube d x)
  rwa [Real.dist_eq] at this

/-- The input space: (phase, amplitude) pairs of continuous functions on the closed cube. -/
abbrev InputSpace (d : ℕ) := C(closedCube d, ℝ) × C(closedCube d, ℝ)

/-- The normalised chart integral as a function of the input pair. -/
noncomputable def normChart {d : ℕ} (h k : Fin d → ℕ) (l β N : ℝ) (x : InputSpace d) : ℝ :=
  chartIntegral d h k β N (extCube x.1) (extCube x.2) / leadScale h k l N

/-- The limit functional as a function of the input pair. -/
noncomputable def limChart {d : ℕ} (h k : Fin d → ℕ) (l β : ℝ) (x : InputSpace d) : ℝ :=
  phaseCoeff h k l β (extCube x.1) (extCube x.2)

theorem norm_fst_le_of_mem_closedBall {d : ℕ} {x : InputSpace d} {R : ℝ}
    (hx : x ∈ Metric.closedBall (0 : InputSpace d) R) : ‖x.1‖ ≤ R := by
  rw [mem_closedBall_zero_iff, Prod.norm_def] at hx
  exact (le_max_left _ _).trans hx

theorem norm_snd_le_of_mem_closedBall {d : ℕ} {x : InputSpace d} {R : ℝ}
    (hx : x ∈ Metric.closedBall (0 : InputSpace d) R) : ‖x.2‖ ≤ R := by
  rw [mem_closedBall_zero_iff, Prod.norm_def] at hx
  exact (le_max_right _ _).trans hx

/-- **Pointwise convergence** `F_N(x) → F(x)`. -/
theorem tendsto_normChart (d : ℕ) (h k : Fin (d + 1) → ℕ) (hk : ∀ i, 0 < k i) (l β : ℝ)
    (hl : 0 < l) (hβ : 0 < β) (hmin : ∀ i, l ≤ ratioExp h k i) (hatt : ∃ i, ratioExp h k i = l)
    (x : InputSpace (d + 1)) :
    Tendsto (fun N => normChart h k l β N x) atTop (𝓝 (limChart h k l β x)) :=
  phase_leading_tendsto d h k hk l β hl hβ hmin hatt (extCube x.1) (extCube x.2)
    (continuous_extCube x.1) (continuous_extCube x.2)

/-- **Eventual Lipschitz bound** for `F_N` on the closed ball of radius `R`. -/
theorem normChart_lipschitz_eventually (d : ℕ) (h k : Fin (d + 1) → ℕ) (hk : ∀ i, 0 < k i)
    (l β R : ℝ) (hl : 0 < l) (hβ : 0 < β) (hmin : ∀ i, l ≤ ratioExp h k i)
    (hatt : ∃ i, ratioExp h k i = l) :
    ∃ L : ℝ, 0 ≤ L ∧ ∀ᶠ N in atTop, ∀ x y : InputSpace (d + 1),
      x ∈ Metric.closedBall 0 R → y ∈ Metric.closedBall 0 R →
      |normChart h k l β N x - normChart h k l β N y| ≤ L * dist x y := by
  obtain ⟨L, hL0, hL⟩ := normalised_lipschitz_eventually d h k hk l β R R hl hβ hmin hatt
  refine ⟨2 * L, by positivity, ?_⟩
  filter_upwards [hL] with N hN
  intro x y hx hy
  have h1 := hN (extCube x.1) (extCube y.1) (extCube x.2) (extCube y.2) (dist x.1 y.1) (dist x.2 y.2)
    (continuous_extCube _) (continuous_extCube _) (continuous_extCube _) (continuous_extCube _)
    (fun u _ => (abs_extCube_le _ u).trans (norm_fst_le_of_mem_closedBall hx))
    (fun u _ => (abs_extCube_le _ u).trans (norm_fst_le_of_mem_closedBall hy))
    (fun u _ => (abs_extCube_le _ u).trans (norm_snd_le_of_mem_closedBall hy))
    (fun u _ => abs_extCube_sub_le _ _ u) (fun u _ => abs_extCube_sub_le _ _ u)
  unfold normChart
  refine h1.trans ?_
  have hd1 : dist x.1 y.1 ≤ dist x y := by rw [Prod.dist_eq]; exact le_max_left _ _
  have hd2 : dist x.2 y.2 ≤ dist x y := by rw [Prod.dist_eq]; exact le_max_right _ _
  nlinarith [dist_nonneg (x := x) (y := y)]

/-- **Lipschitz bound** for the limit functional on the closed ball of radius `R`. -/
theorem limChart_lipschitz (d : ℕ) (h k : Fin (d + 1) → ℕ) (hk : ∀ i, 0 < k i) (l β R : ℝ)
    (hl : 0 < l) (hβ : 0 < β) (hmin : ∀ i, l ≤ ratioExp h k i) :
    ∃ L : ℝ, 0 ≤ L ∧ ∀ x y : InputSpace (d + 1),
      x ∈ Metric.closedBall 0 R → y ∈ Metric.closedBall 0 R →
      |limChart h k l β x - limChart h k l β y| ≤ L * dist x y := by
  have hW : 0 ≤ ∫ u in unitBox (d + 1), residualWeight h k l u :=
    setIntegral_nonneg (measurableSet_unitBox _) fun u hu => residualWeight_nonneg h k l u hu
  have hJ0 : 0 ≤ phaseMoment β (2 * l) R := (phaseMoment_pos β (2 * l) R hβ (by positivity)).le
  have hJ1 : 0 ≤ phaseMoment β (2 * l + 1) R := (phaseMoment_pos β _ R hβ (by positivity)).le
  have hD : 0 ≤ (2 : ℝ) ^ (multCount (ratioExp h k) l - 1) * 2 * faceNorm h k l := by
    have := faceNorm_nonneg h k l
    positivity
  have hR : 0 ≤ |R| := abs_nonneg R
  refine ⟨(2 : ℝ) ^ (multCount (ratioExp h k) l - 1) * 2 * faceNorm h k l *
    ((phaseMoment β (2 * l) R + β * |R| * phaseMoment β (2 * l + 1) R) *
      ∫ u in unitBox (d + 1), residualWeight h k l u), by positivity, ?_⟩
  intro x y hx hy
  have h1 := phaseCoeff_sub_le (d + 1) h k hk l β R R (dist x.1 y.1) (dist x.2 y.2) hl hβ hmin
    (extCube x.1) (extCube y.1) (extCube x.2) (extCube y.2)
    (continuous_extCube _) (continuous_extCube _) (continuous_extCube _) (continuous_extCube _)
    (fun u _ => (abs_extCube_le _ u).trans (norm_fst_le_of_mem_closedBall hx))
    (fun u _ => (abs_extCube_le _ u).trans (norm_fst_le_of_mem_closedBall hy))
    (fun u _ => (abs_extCube_le _ u).trans (norm_snd_le_of_mem_closedBall hy))
    (fun u _ => abs_extCube_sub_le _ _ u) (fun u _ => abs_extCube_sub_le _ _ u)
  unfold limChart
  refine h1.trans ?_
  have hd1 : dist x.1 y.1 ≤ dist x y := by rw [Prod.dist_eq]; exact le_max_left _ _
  have hd2 : dist x.2 y.2 ≤ dist x y := by rw [Prod.dist_eq]; exact le_max_right _ _
  have hR0 : 0 ≤ R := (norm_nonneg _).trans (norm_fst_le_of_mem_closedBall hx)
  rw [abs_of_nonneg hR0]
  have hdn := dist_nonneg (x := x) (y := y)
  have hd1' := dist_nonneg (x := x.1) (y := y.1)
  have hd2' := dist_nonneg (x := x.2) (y := y.2)
  have key : dist x.2 y.2 * phaseMoment β (2 * l) R + β * R * dist x.1 y.1 * phaseMoment β (2 * l + 1) R ≤
      (phaseMoment β (2 * l) R + β * R * phaseMoment β (2 * l + 1) R) * dist x y := by
    nlinarith [mul_le_mul_of_nonneg_left hd2 hJ0, mul_le_mul_of_nonneg_left hd1 (by positivity : 0 ≤ β * R * phaseMoment β (2 * l + 1) R)]
  calc _ ≤ (2 : ℝ) ^ (multCount (ratioExp h k) l - 1) * 2 * faceNorm h k l *
        (((phaseMoment β (2 * l) R + β * R * phaseMoment β (2 * l + 1) R) * dist x y) *
          ∫ u in unitBox (d + 1), residualWeight h k l u) := by gcongr
    _ = _ := by ring

/-- **Uniform convergence on compact input sets**. -/
theorem tendstoUniformlyOn_normChart (d : ℕ) (h k : Fin (d + 1) → ℕ) (hk : ∀ i, 0 < k i) (l β : ℝ)
    (hl : 0 < l) (hβ : 0 < β) (hmin : ∀ i, l ≤ ratioExp h k i) (hatt : ∃ i, ratioExp h k i = l)
    (K : Set (InputSpace (d + 1))) (hK : IsCompact K) :
    TendstoUniformlyOn (fun N x => normChart h k l β N x) (limChart h k l β) atTop K := by
  obtain ⟨R, hR⟩ := hK.isBounded.subset_closedBall (0 : InputSpace (d + 1))
  obtain ⟨L, hL0, hL⟩ := normChart_lipschitz_eventually d h k hk l β R hl hβ hmin hatt
  obtain ⟨L', hL'0, hL'⟩ := limChart_lipschitz d h k hk l β R hl hβ hmin
  rw [Metric.tendstoUniformlyOn_iff]
  intro ε hε
  set δ : ℝ := ε / (3 * (L + L' + 1)) with hδ
  have hδ0 : 0 < δ := by positivity
  obtain ⟨T, hTK, hTfin, hTcov⟩ := finite_cover_balls_of_compact hK hδ0
  have hpt : ∀ᶠ N in atTop, ∀ t ∈ T,
      dist (limChart h k l β t) (normChart h k l β N t) < ε / 3 := by
    rw [Filter.eventually_all_finite hTfin]
    intro t _
    have := (tendsto_normChart d h k hk l β hl hβ hmin hatt t).eventually
      (Metric.ball_mem_nhds (limChart h k l β t) (by positivity : (0 : ℝ) < ε / 3))
    filter_upwards [this] with N hN
    rwa [dist_comm]
  filter_upwards [hL, hpt] with N hLN hptN
  intro x hx
  obtain ⟨t, htT, hxt⟩ := Set.mem_iUnion₂.1 (hTcov hx)
  rw [Metric.mem_ball] at hxt
  have hxB := hR hx
  have htB := hR (hTK htT)
  have h1 : dist (limChart h k l β x) (limChart h k l β t) ≤ L' * δ := by
    rw [Real.dist_eq]
    exact (hL' x t hxB htB).trans (mul_le_mul_of_nonneg_left hxt.le hL'0)
  have h3 : dist (normChart h k l β N t) (normChart h k l β N x) ≤ L * δ := by
    rw [Real.dist_eq]
    refine (hLN t x htB hxB).trans ?_
    rw [dist_comm]
    exact mul_le_mul_of_nonneg_left hxt.le hL0
  have h2 := hptN t htT
  have hsum : (L + L') * δ ≤ ε / 3 := by
    rw [hδ, mul_div_assoc', div_le_div_iff₀ (by positivity) (by positivity)]
    nlinarith [hε.le, hL0, hL'0]
  calc dist (limChart h k l β x) (normChart h k l β N x)
      ≤ dist (limChart h k l β x) (limChart h k l β t) +
        dist (limChart h k l β t) (normChart h k l β N t) +
        dist (normChart h k l β N t) (normChart h k l β N x) := dist_triangle4 _ _ _ _
    _ < ε := by linarith

end Laplace.Grammar
