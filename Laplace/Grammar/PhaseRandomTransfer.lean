/-
Copyright (c) 2026 Timaeus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib.Topology.ContinuousMap.SecondCountableSpace
import Mathlib.MeasureTheory.Measure.Tight
import Laplace.Grammar.PhaseUniform

/-!
# Random phases and amplitudes in general dimension: the stochastic transfer

Unit 212 (programme A2, step 4). Random inputs `X n : Ω → InputSpace (d+1)` (phase, amplitude
pairs in `C([0,1]^d)²`) converging in distribution to `Z`, along a countably generated filter, with
scales `N n → ∞`:
```
F_{N n}(X n) ⇒ F(Z),   F_N = normChart (Headline XIII normalised integral), F = limChart.
```
(`tendstoInDistribution_normChart`). Proof: `F(X n) ⇒ F(Z)` by continuous mapping (`F` is
continuous, being Lipschitz on balls), and `F_{N n}(X n) − F(X n) → 0` in probability: the limit
law
is tight in the Polish space `InputSpace` (Mathlib's `isTightMeasureSet_singleton`), so most of
`Z` lies in a compact `K`; by portmanteau most of `X n` lies in the open `δ`-thickening of `K`;
there the uniform convergence on `K` (unit 211) extends by the Lipschitz bounds (units 209–210).
Mathlib's
`TendstoInDistribution.add_of_tendstoInMeasure_const` (Slutsky) finishes.

Also: `C([0,1]^d)` carries the Borel σ-algebra (so `InputSpace` has the product = Borel one); `continuous_limChart`, `continuous_normChart`
(for `N ≥ 0`). No `N`-dependence of the amplitude beyond the input pair is allowed; the scales
`N n ≥ 0` are deterministic. Zero `sorry`/`axiom`.
-/

open MeasureTheory Filter Topology Real Set

namespace Laplace.Grammar

instance instMeasurableSpaceCCube (d : ℕ) : MeasurableSpace C(closedCube d, ℝ) := borel _
instance instBorelSpaceCCube (d : ℕ) : BorelSpace C(closedCube d, ℝ) := ⟨rfl⟩

example (d : ℕ) : SecondCountableTopology (InputSpace d) := inferInstance
example (d : ℕ) : CompleteSpace (InputSpace d) := inferInstance
example (d : ℕ) : BorelSpace (InputSpace d) := inferInstance

/-- Lipschitz bound for `F_N` on a ball at a fixed scale `N ≥ 0`. -/
theorem normChart_lipschitzOn (d : ℕ) (h k : Fin (d + 1) → ℕ) (l β N R : ℝ) (hβ : 0 < β)
    (hN : 0 ≤ N) :
    ∃ L : ℝ, 0 ≤ L ∧ ∀ x y : InputSpace (d + 1),
      x ∈ Metric.closedBall 0 R → y ∈ Metric.closedBall 0 R →
      |normChart h k l β N x - normChart h k l β N y| ≤ L * dist x y := by
  set G₀ := chartIntegral (d + 1) h k β N (fun _ => R) (fun _ => 1) with hG₀
  set G₁ := N * chartIntegral (d + 1) (phaseShift h k 1) k β N (fun _ => R) (fun _ => 1) with hG₁
  set S := leadScale h k l N with hS
  refine ⟨(|G₀| + β * |R| * |G₁|) / |S|, by positivity, ?_⟩
  intro x y hx hy
  have h1 := chartIntegral_sub_le (d + 1) h k β N R R (dist x.1 y.1) (dist x.2 y.2) hβ hN
    (extCube x.1) (extCube y.1) (extCube x.2) (extCube y.2)
    (continuous_extCube _) (continuous_extCube _) (continuous_extCube _) (continuous_extCube _)
    (fun u _ => (abs_extCube_le _ u).trans (norm_fst_le_of_mem_closedBall hx))
    (fun u _ => (abs_extCube_le _ u).trans (norm_fst_le_of_mem_closedBall hy))
    (fun u _ => (abs_extCube_le _ u).trans (norm_snd_le_of_mem_closedBall hy))
    (fun u _ => abs_extCube_sub_le _ _ u) (fun u _ => abs_extCube_sub_le _ _ u)
  have hd1 : dist x.1 y.1 ≤ dist x y := by rw [Prod.dist_eq]; exact le_max_left _ _
  have hd2 : dist x.2 y.2 ≤ dist x y := by rw [Prod.dist_eq]; exact le_max_right _ _
  have hR0 : 0 ≤ R := (norm_nonneg _).trans (norm_fst_le_of_mem_closedBall hx)
  have hdn := dist_nonneg (x := x) (y := y)
  have hd1' := dist_nonneg (x := x.1) (y := y.1)
  have hd2' := dist_nonneg (x := x.2) (y := y.2)
  have h2 : |chartIntegral (d + 1) h k β N (extCube x.1) (extCube x.2) -
      chartIntegral (d + 1) h k β N (extCube y.1) (extCube y.2)| ≤
      (|G₀| + β * |R| * |G₁|) * dist x y := by
    refine h1.trans ?_
    rw [abs_of_nonneg hR0]
    have e0 : dist x.2 y.2 * G₀ ≤ dist x y * |G₀| := by
      refine (le_abs_self _).trans ?_
      rw [abs_mul, abs_of_nonneg hd2']
      exact mul_le_mul_of_nonneg_right hd2 (abs_nonneg _)
    have e1 : β * R * dist x.1 y.1 * G₁ ≤ β * R * dist x y * |G₁| := by
      refine (le_abs_self _).trans ?_
      rw [abs_mul, abs_of_nonneg (by positivity : 0 ≤ β * R * dist x.1 y.1)]
      exact mul_le_mul_of_nonneg_right (by gcongr) (abs_nonneg _)
    nlinarith
  unfold normChart
  rw [← sub_div, abs_div, ← hS]
  rcases eq_or_ne S 0 with hS0 | hS0
  · rw [hS0, abs_zero, div_zero, div_zero, zero_mul]
  · calc |chartIntegral (d + 1) h k β N (extCube x.1) (extCube x.2) -
          chartIntegral (d + 1) h k β N (extCube y.1) (extCube y.2)| / |S|
        ≤ (|G₀| + β * |R| * |G₁|) * dist x y / |S| :=
          div_le_div_of_nonneg_right h2 (abs_nonneg _)
      _ = (|G₀| + β * |R| * |G₁|) / |S| * dist x y := by ring

/-- `F_N` is continuous on the input space for each fixed scale `N ≥ 0`. -/
theorem continuous_normChart (d : ℕ) (h k : Fin (d + 1) → ℕ) (l β N : ℝ) (hβ : 0 < β)
    (hN : 0 ≤ N) : Continuous (normChart h k l β N) := by
  refine continuous_iff_continuousAt.2 fun x₀ => ?_
  obtain ⟨L, hL0, hL⟩ := normChart_lipschitzOn d h k l β N (‖x₀‖ + 1) hβ hN
  have hlip : LipschitzOnWith ⟨L, hL0⟩ (normChart h k l β N) (Metric.closedBall 0 (‖x₀‖ + 1)) :=
    lipschitzOnWith_iff_dist_le_mul.2 fun x hx y hy => by
      rw [Real.dist_eq]
      exact hL x y hx hy
  exact hlip.continuousOn.continuousAt
    (Metric.closedBall_mem_nhds_of_mem (mem_ball_zero_iff.2 (lt_add_one _)))

/-- The limit functional `F` is continuous on the input space. -/
theorem continuous_limChart (d : ℕ) (h k : Fin (d + 1) → ℕ) (hk : ∀ i, 0 < k i) (l β : ℝ)
    (hl : 0 < l) (hβ : 0 < β) (hmin : ∀ i, l ≤ ratioExp h k i) :
    Continuous (limChart h k l β : InputSpace (d + 1) → ℝ) := by
  refine continuous_iff_continuousAt.2 fun x₀ => ?_
  obtain ⟨L, hL0, hL⟩ := limChart_lipschitz d h k hk l β (‖x₀‖ + 1) hl hβ hmin
  have hlip : LipschitzOnWith ⟨L, hL0⟩ (limChart h k l β) (Metric.closedBall 0 (‖x₀‖ + 1)) :=
    lipschitzOnWith_iff_dist_le_mul.2 fun x hx y hy => by
      rw [Real.dist_eq]
      exact hL x y hx hy
  exact hlip.continuousOn.continuousAt
    (Metric.closedBall_mem_nhds_of_mem (mem_ball_zero_iff.2 (lt_add_one _)))

variable {ι Ω Ω' : Type*} [MeasurableSpace Ω] [MeasurableSpace Ω'] {μ : Measure Ω}
  [IsProbabilityMeasure μ] {μ' : Measure Ω'} [IsProbabilityMeasure μ'] {L : Filter ι}
  [L.IsCountablyGenerated]

omit [L.IsCountablyGenerated] in
/-- **The normalised error converges to zero in probability** along random inputs converging in
distribution: tightness of the limit law, portmanteau on the closed complement of a thickening,
uniform convergence on the compact core, Lipschitz extension to the thickening. -/
theorem tendstoInMeasure_normChart_sub (d : ℕ) (h k : Fin (d + 1) → ℕ) (hk : ∀ i, 0 < k i)
    (l β : ℝ) (hl : 0 < l) (hβ : 0 < β) (hmin : ∀ i, l ≤ ratioExp h k i)
    (hatt : ∃ i, ratioExp h k i = l) (X : ι → Ω → InputSpace (d + 1)) (Z : Ω' → InputSpace (d + 1))
    (hZm : Measurable Z) (hX : TendstoInDistribution X L Z (fun _ => μ) μ') (Nseq : ι → ℝ)
    (hN : Tendsto Nseq L atTop) :
    TendstoInMeasure μ (fun n ω => normChart h k l β (Nseq n) (X n ω) - limChart h k l β (X n ω))
      L (fun _ => 0) := by
  rw [tendstoInMeasure_iff_norm]
  intro ε hε
  rw [ENNReal.tendsto_nhds_zero]
  intro η hη
  by_cases hηtop : η = ⊤
  · exact Eventually.of_forall fun n => by rw [hηtop]; exact le_top
  -- tightness of the law of `Z`
  obtain ⟨K, hKc, hKle⟩ := isTightMeasureSet_iff_exists_isCompact_measure_compl_le.1
    (isTightMeasureSet_singleton (μ := μ'.map Z)) (η / 2) (ENNReal.half_pos hη.ne')
  have hZK : μ' (Z ⁻¹' Kᶜ) ≤ η / 2 := by
    have := hKle (μ'.map Z) (Set.mem_singleton _)
    rwa [Measure.map_apply hZm hKc.isClosed.measurableSet.compl] at this
  -- Lipschitz constants on the ball of radius `R + 1`
  obtain ⟨R, hR⟩ := hKc.isBounded.subset_closedBall (0 : InputSpace (d + 1))
  obtain ⟨Lc, hLc0, hLc⟩ := normChart_lipschitz_eventually d h k hk l β (R + 1) hl hβ hmin hatt
  obtain ⟨L', hL'0, hL'⟩ := limChart_lipschitz d h k hk l β (R + 1) hl hβ hmin
  set δ : ℝ := min 1 (ε / (3 * (Lc + L' + 1))) with hδ
  have hδ0 : 0 < δ := lt_min one_pos (by positivity)
  have hδ1 : δ ≤ 1 := min_le_left _ _
  have hδε : (Lc + L') * δ ≤ ε / 3 := by
    calc (Lc + L') * δ ≤ (Lc + L') * (ε / (3 * (Lc + L' + 1))) :=
          mul_le_mul_of_nonneg_left (min_le_right _ _) (by positivity)
      _ ≤ ε / 3 := by
          rw [mul_div_assoc', div_le_div_iff₀ (by positivity) (by positivity)]
          nlinarith [hε.le, hLc0, hL'0]
  -- uniform convergence on `K`
  have hunif := (Metric.tendstoUniformlyOn_iff.1
    (tendstoUniformlyOn_normChart d h k hk l β hl hβ hmin hatt K hKc)) (ε / 3) (by positivity)
  -- portmanteau on the closed set `Fc = (thickening δ K)ᶜ`
  set Fc : Set (InputSpace (d + 1)) := (Metric.thickening δ K)ᶜ with hFc
  have hFcl : IsClosed Fc := Metric.isOpen_thickening.isClosed_compl
  have hFm : MeasurableSet Fc := hFcl.measurableSet
  have hport := ProbabilityMeasure.limsup_measure_closed_le_of_tendsto hX.tendsto hFcl
  simp only [ProbabilityMeasure.coe_mk] at hport
  have hmap : ∀ n, (μ.map (X n)) Fc = μ (X n ⁻¹' Fc) := fun n =>
    Measure.map_apply_of_aemeasurable (hX.forall_aemeasurable n) hFm
  simp only [hmap, Measure.map_apply_of_aemeasurable hX.aemeasurable_limit hFm] at hport
  have hZFc : μ' (Z ⁻¹' Fc) ≤ η / 2 := by
    refine le_trans (measure_mono ?_) hZK
    intro ω hω hK
    exact hω (Metric.self_subset_thickening hδ0 K hK)
  have hlt : limsup (fun n => μ (X n ⁻¹' Fc)) L < η :=
    lt_of_le_of_lt hport (lt_of_le_of_lt hZFc (ENNReal.half_lt_self hη.ne' hηtop))
  filter_upwards [eventually_lt_of_limsup_lt hlt, hN.eventually hLc, hN.eventually hunif]
    with n hn hLcn hunifn
  refine le_trans (measure_mono ?_) hn.le
  intro ω hω
  by_contra hcon
  rw [Set.mem_preimage, hFc, Set.mem_compl_iff, not_not] at hcon
  obtain ⟨y, hyK, hxy⟩ := Metric.mem_thickening_iff.1 hcon
  have hyR : ‖y‖ ≤ R := by
    have := hR hyK
    rwa [Metric.mem_closedBall, dist_zero_right] at this
  have hyB : y ∈ Metric.closedBall 0 (R + 1) := by
    rw [Metric.mem_closedBall, dist_zero_right]
    linarith
  have hxB : X n ω ∈ Metric.closedBall 0 (R + 1) := by
    rw [Metric.mem_closedBall, dist_zero_right]
    have := dist_triangle (X n ω) y 0
    simp only [dist_zero_right] at this
    linarith
  have e1 := hLcn (X n ω) y hxB hyB
  have e2 := hunifn y hyK
  have e3 := hL' y (X n ω) hyB hxB
  rw [Real.dist_eq] at e2
  rw [dist_comm] at e3
  have hsum : (Lc + L') * dist (X n ω) y ≤ ε / 3 :=
    (mul_le_mul_of_nonneg_left hxy.le (by positivity)).trans hδε
  have hlt' : |normChart h k l β (Nseq n) (X n ω) - limChart h k l β (X n ω)| < ε := by
    calc |normChart h k l β (Nseq n) (X n ω) - limChart h k l β (X n ω)|
        = |(normChart h k l β (Nseq n) (X n ω) - normChart h k l β (Nseq n) y) +
            (normChart h k l β (Nseq n) y - limChart h k l β y) +
            (limChart h k l β y - limChart h k l β (X n ω))| := by ring_nf
      _ ≤ |normChart h k l β (Nseq n) (X n ω) - normChart h k l β (Nseq n) y| +
            |normChart h k l β (Nseq n) y - limChart h k l β y| +
            |limChart h k l β y - limChart h k l β (X n ω)| := abs_add_three _ _ _
      _ < Lc * dist (X n ω) y + ε / 3 + L' * dist (X n ω) y := by
          have e2' : |normChart h k l β (Nseq n) y - limChart h k l β y| < ε / 3 := by
            rwa [abs_sub_comm]
          linarith
      _ ≤ ε := by nlinarith
  rw [Set.mem_ofPred_eq, sub_zero, Real.norm_eq_abs] at hω
  exact absurd hω (not_le.2 hlt')

/-- **Headline XVI (random phases and amplitudes, general dimension)**: if the random inputs
`X n ⇒ Z` in `C([0,1]^d)²` and the deterministic scales `N n → ∞`, then the normalised chart
integrals converge in distribution to the limit functional of the limiting input:
`F_{N n}(X n) ⇒ F(Z)`. -/
theorem tendstoInDistribution_normChart (d : ℕ) (h k : Fin (d + 1) → ℕ) (hk : ∀ i, 0 < k i)
    (l β : ℝ) (hl : 0 < l) (hβ : 0 < β) (hmin : ∀ i, l ≤ ratioExp h k i)
    (hatt : ∃ i, ratioExp h k i = l) (X : ι → Ω → InputSpace (d + 1)) (hXm : ∀ n, Measurable (X n))
    (Z : Ω' → InputSpace (d + 1)) (hZm : Measurable Z)
    (hX : TendstoInDistribution X L Z (fun _ => μ) μ') (Nseq : ι → ℝ) (hN : Tendsto Nseq L atTop)
    (hN0 : ∀ n, 0 ≤ Nseq n) :
    TendstoInDistribution (fun n ω => normChart h k l β (Nseq n) (X n ω)) L
      (fun ω => limChart h k l β (Z ω)) (fun _ => μ) μ' := by
  have hlim := hX.continuous_comp (continuous_limChart d h k hk l β hl hβ hmin)
  have herr := tendstoInMeasure_normChart_sub d h k hk l β hl hβ hmin hatt X Z hZm hX Nseq hN
  have hmeas : ∀ n, AEMeasurable (fun ω =>
      normChart h k l β (Nseq n) (X n ω) - limChart h k l β (X n ω)) μ := fun n =>
    (((continuous_normChart d h k l β (Nseq n) hβ (hN0 n)).measurable.comp (hXm n)).sub
      ((continuous_limChart d h k hk l β hl hβ hmin).measurable.comp (hXm n))).aemeasurable
  have hsum := hlim.add_of_tendstoInMeasure_const herr hmeas
  refine hsum.congr (fun n => Eventually.of_forall fun ω => ?_) (Eventually.of_forall fun ω => ?_)
  · simp only [Pi.add_apply, Function.comp]
    ring
  · simp

end Laplace.Grammar
