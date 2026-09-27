/-
Copyright (c) 2026 Timaeus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Timaeus
-/
import Laplace.Multi.ResponseSingularCovariance
import Laplace.Multi.ResponseTestingData
import Laplace.Multi.ResponseMinimaxTwoPoint

/-!
# The resolution floor along an attainable direction

The margin chamber theorem of `ResponseEmpiricalRisk` bounds the probability of misclassifying the
chamber of a mean from above. The matching lower bound is a two-point testing obstruction along an
**attainable direction**: a displacement `e` of the mean annihilated by the covariance kernel of the
data law, realised by the least-information score `h_e = ⟨e*, S⟩` of `ResponseSingularCovariance`.
Along the alternatives `D_s ∝ e^{s h_e} D`

* the mean moves in the direction `e` at unit speed, `d/ds ⟨u, m(D_s)⟩|₀ = ⟨u, e⟩`
  (`hasDerivAt_dotJ_mean_tilted_dataDualSing`), and
* the information cost is `KL(D_s ‖ D)/s² → ⟨e, Σ_D⁺ e⟩/2`
(`tendsto_klDiv_tilted_dataDualSing_div_sq`),

so at the scale `s_n = a/√n` the two laws have means `a e/√n` apart to first order
(`tendsto_sqrt_mul_dotJ_mean_sub`) while every test between `n` samples of `D` and of `D_{s_n}`
has error at least `(1 − √(a² ⟨e,Σ_D⁺e⟩/2))/2` in the limit (`chamber_resolution_floor`). Two
chambers separated only by a displacement of order `a e/√n` along an attainable direction with
`a² ⟨e, Σ_D⁺ e⟩ < 2` cannot be resolved reliably by any procedure: chambers below the local
information scale are unresolvable when they are separated along an attainable direction. There is
no universal Euclidean `n^{-1/2}` statement: the scale is the pseudo-inverse covariance form, and
directions off the annihilator are not reached by dominated bounded-score alternatives at all.
-/

open MeasureTheory ProbabilityTheory Filter Topology Set InformationTheory

namespace Laplace.Multi

section Attainable

variable {X : Type*} [MeasurableSpace X] [Nonempty X] {J : Type*} [Fintype J] [Nonempty J]
  {S : J → X → ℝ} (hS : ∀ j, Bdd (S j)) (ν : Measure X) [IsProbabilityMeasure ν]
  (D : Measure X) [IsProbabilityMeasure D]
include hS

/-- The direction space. -/
local notation "𝕍" => dirSpan ν (fun _ ↦ (1 : ℝ)) S

/-- The least-information score of an annihilated displacement. -/
local notation "hE" he => dirLoss S (dataDualSing hS ν D he : J → ℝ)

omit [Nonempty J] [IsProbabilityMeasure ν] in
/-- **The information cost of the attainable alternatives**:
`KL(D_s ‖ D)/s² → Σ_D(e*, e*)/2 = ⟨e, Σ_D⁺ e⟩/2`. -/
theorem tendsto_klDiv_tilted_dataDualSing_div_sq {e : J → ℝ}
    (he : ∀ u ∈ dataKer hS ν D, dotJ (u : J → ℝ) e = 0) :
    Tendsto (fun s ↦ (klDiv (D.tilted fun x ↦ s * (hE he) x) D).toReal / s ^ 2) (𝓝[≠] 0)
      (𝓝 (dataBilin hS ν D (dataDualSing hS ν D he) (dataDualSing hS ν D he) / 2)) :=
  tendsto_klDiv_tilted_div_sq D (bdd_dirLoss hS _)

omit [Nonempty J] [IsProbabilityMeasure ν] in
/-- **The attainable alternatives move the mean in the direction `e`**:
`d/ds ⟨u, m(D_s)⟩|₀ = ⟨u, e⟩` for every `u ∈ W`. -/
theorem hasDerivAt_dotJ_mean_tilted_dataDualSing {e : J → ℝ}
    (he : ∀ u ∈ dataKer hS ν D, dotJ (u : J → ℝ) e = 0) (u : 𝕍) :
    HasDerivAt (fun s ↦ dotJ (u : J → ℝ) (fun i ↦ ∫ x, S i x ∂(D.tilted fun x ↦ s * (hE he) x)))
      (dotJ (u : J → ℝ) e) 0 := by
  set f := hE he with hf
  have hfb : Bdd f := bdd_dirLoss hS _
  have h : ∀ i, HasDerivAt (fun s ↦ ∫ x, S i x ∂(D.tilted fun x ↦ s * f x))
      (∫ x, S i x * f x ∂(D.tilted fun x ↦ (0 : ℝ) * f x) -
        (∫ x, S i x ∂(D.tilted fun x ↦ (0 : ℝ) * f x)) *
          ∫ x, f x ∂(D.tilted fun x ↦ (0 : ℝ) * f x)) 0 :=
    fun i ↦ hasDerivAt_dataResponsePath hS D hfb i 0
  have h0 : ∀ g : X → ℝ, ∫ x, g x ∂(D.tilted fun x ↦ (0 : ℝ) * f x) = ∫ x, g x ∂D := fun g ↦ by
    have e : (fun x ↦ (0 : ℝ) * f x) = 0 := by
      funext x
      simp
    rw [e, tilted_zero]
  have hsum : HasDerivAt (fun s ↦ ∑ i, (u : J → ℝ) i *
      ∫ x, S i x ∂(D.tilted fun x ↦ s * f x)) (∑ i, (u : J → ℝ) i * lawCov D (S i) f) 0 := by
    refine HasDerivAt.fun_sum fun i _ ↦ ?_
    have := (h i).const_mul ((u : J → ℝ) i)
    simp only [h0] at this
    exact this
  have e1 : ∑ i, (u : J → ℝ) i * lawCov D (S i) f = dotJ (u : J → ℝ) e := by
    rw [← lawCov_dirLoss_left hS D (u : J → ℝ) f hfb, hf, ← dataBilin_apply hS ν D,
      dataBilin_comm hS ν D, dataBilin_dataDualSing hS ν D he]
  rw [← e1]
  exact hsum

omit [Nonempty J] [IsProbabilityMeasure ν] in
/-- **At the sampling scale the alternatives are `a e/√n` apart**:
`√n (⟨u, m(D_{a/√n})⟩ − ⟨u, m_D⟩) → a ⟨u, e⟩`. -/
theorem tendsto_sqrt_mul_dotJ_mean_sub {e : J → ℝ}
    (he : ∀ u ∈ dataKer hS ν D, dotJ (u : J → ℝ) e = 0) (u : 𝕍) {a : ℝ} (ha : 0 < a) :
    Tendsto (fun n : ℕ ↦ Real.sqrt n *
      (dotJ (u : J → ℝ) (fun i ↦ ∫ x, S i x ∂(D.tilted fun x ↦ (a / Real.sqrt n) * (hE he) x)) -
        dotJ (u : J → ℝ) (fun i ↦ ∫ x, S i x ∂D))) atTop (𝓝 (a * dotJ (u : J → ℝ) e)) := by
  have hslope := (hasDerivAt_iff_tendsto_slope_zero.1
    (hasDerivAt_dotJ_mean_tilted_dataDualSing hS ν D he u)).comp (tendsto_scale ha)
  refine (hslope.const_mul a).congr' ?_
  filter_upwards [eventually_gt_atTop 0] with n hn
  have hn' : (0 : ℝ) < n := Nat.cast_pos.mpr hn
  have hs : 0 < Real.sqrt n := Real.sqrt_pos.2 hn'
  simp only [Function.comp_def, zero_add, smul_eq_mul, tilted_zero_mul_eq]
  field_simp

omit [Nonempty J] [IsProbabilityMeasure ν] in
/-- **THE RESOLUTION FLOOR ALONG AN ATTAINABLE DIRECTION**: for the alternatives `D_{a/√n}` tilted
by the least-information score of an annihilated displacement `e`, the two-point testing bound
`L_n = (1 − √(n KL(D_{a/√n} ‖ D)))/2` converges to `(1 − √(a² ⟨e, Σ_D⁺ e⟩/2))/2`, and every test
`φ` between `n` samples of `D` and of `D_{a/√n}` has error at least `L_n`. -/
theorem chamber_resolution_floor {e : J → ℝ}
    (he : ∀ u ∈ dataKer hS ν D, dotJ (u : J → ℝ) e = 0) {a : ℝ} (ha : 0 < a) :
    ∃ L : ℕ → ℝ,
      Tendsto L atTop (𝓝 ((1 - √(a ^ 2 *
        dataBilin hS ν D (dataDualSing hS ν D he) (dataDualSing hS ν D he) / 2)) / 2)) ∧
      ∀ n : ℕ, ∀ φ : (Fin n → X) → ℝ, Measurable φ → (∀ z, 0 ≤ φ z) → (∀ z, φ z ≤ 1) →
        L n ≤ ((∫ z, φ z ∂(Measure.pi fun _ : Fin n ↦ D.tilted fun x ↦ (a / Real.sqrt n) *
            (hE he) x)) + ∫ z, (1 - φ z) ∂(Measure.pi fun _ : Fin n ↦ D)) / 2 := by
  set σ2 := dataBilin hS ν D (dataDualSing hS ν D he) (dataDualSing hS ν D he) with hσ2
  set t : ℕ → ℝ := fun n ↦ a / Real.sqrt n with ht
  set KL : ℕ → ℝ := fun n ↦ (klDiv (D.tilted fun x ↦ t n * (hE he) x) D).toReal with hKL
  refine ⟨fun n ↦ (1 - √(n * KL n)) / 2, ?_, fun n φ hφm hφ0 hφ1 ↦ ?_⟩
  · have hkl := (tendsto_klDiv_tilted_dataDualSing_div_sq hS ν D he).comp (tendsto_scale ha)
    have e2 : ∀ n : ℕ, 0 < n → (n : ℝ) * KL n = a ^ 2 * (KL n / (t n) ^ 2) := by
      intro n hn
      have hn' : (0 : ℝ) < n := Nat.cast_pos.mpr hn
      have hs : 0 < Real.sqrt n := Real.sqrt_pos.2 hn'
      rw [ht]
      simp only
      rw [div_pow, Real.sq_sqrt hn'.le]
      field_simp
    have hB : Tendsto (fun n : ℕ ↦ (n : ℝ) * KL n) atTop (𝓝 (a ^ 2 * (σ2 / 2))) := by
      refine (hkl.const_mul (a ^ 2)).congr' ?_
      filter_upwards [eventually_gt_atTop 0] with n hn
      rw [e2 n hn]
      rfl
    have hlim := ((tendsto_const_nhds (x := (1 : ℝ))).sub
      ((Real.continuous_sqrt.tendsto _).comp hB)).div_const 2
    rw [show a ^ 2 * σ2 / 2 = a ^ 2 * (σ2 / 2) by ring]
    exact hlim
  · exact testing_error_tilted_ge D (bdd_dirLoss hS _) (t n) n hφm hφ0 hφ1

end Attainable

end Laplace.Multi
