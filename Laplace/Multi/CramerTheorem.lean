/-
Copyright (c) 2026 Timaeus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Timaeus
-/
import Mathlib
import Laplace.Multi.RateFunction
import Laplace.Multi.LargeDeviationBounds

/-!
# Cramér's theorem for the empirical response of the featureless member

With the extended rate `𝓘` of `RateFunction`, the sampling of `n` independent responses from the
featureless member `Q = P_{t,0}` obeys the two halves of Cramér's theorem in the
eventual-exponential form (which is exactly the usable content and needs no extended logarithm):

* **upper bound, closed sets** (`cramer_upper`): if `c < 𝓘` on the closed set `F`, then for every
  `ε > 0` and all large `n`, `Q^{⊗n}(R̄_n ∈ F) ≤ e^{−n(c−ε)}` — from the closed-set Chernoff bound
  through the feature box, each point of `F` supplying a Chernoff score above `c`;
* **lower bound, open sets** (`cramer_lower`): if some `M ∈ G` has `𝓘(M) < c`, then
  `Q^{⊗n}(R̄_n ∈ G) ≥ e^{−nc}` for all large `n`. Interior points of the moment body are tilted
  means, where the tilt lower bound applies with `𝓘(m_t(b)) = KL(P_{t,b} ‖ Q)`
  (`cramer_lower_interior`); a boundary point with finite rate is approached radially from the
  featureless response, `M_ε = (1−ε)M + ε m_t(0) ∈ int K` (`radial_mem_interior`), along which the
  rate does not increase (`rateFun_combo_le`, `rateFun_radial_le`), and `M_ε ∈ G` for small `ε`.

Thus on the whole feature space `limsup (1/n) log Q^{⊗n}(R̄_n ∈ F) ≤ −inf_F 𝓘` and
`liminf (1/n) log Q^{⊗n}(R̄_n ∈ G) ≥ −inf_G 𝓘`, the rate being the information distance to the
featureless member on the response space and `+∞` off the moment body.
-/

open MeasureTheory Filter Topology Set
open scoped ENNReal

namespace Laplace.Multi

variable {X : Type*} [MeasurableSpace X] {μ : Measure X} {ι : Type*} [Fintype ι]

/-- The Chernoff score is affine in the response. -/
theorem chernoffScore_combo (π L₀ : X → ℝ) (R : ι → X → ℝ) (t : ℝ) (M M₀ q : ι → ℝ) (ε : ℝ) :
    chernoffScore μ π L₀ R t ((1 - ε) • M + ε • M₀) q =
      (1 - ε) * chernoffScore μ π L₀ R t M q + ε * chernoffScore μ π L₀ R t M₀ q := by
  unfold chernoffScore
  rw [(isLinearMap_dotJ q).map_add, (isLinearMap_dotJ q).map_smul, (isLinearMap_dotJ q).map_smul,
    smul_eq_mul, smul_eq_mul]
  ring

/-- **The rate is convex along segments** (finite endpoints). -/
theorem rateFun_combo_le (π L₀ : X → ℝ) (R : ι → X → ℝ) (t : ℝ) {M M₀ : ι → ℝ}
    (hM : rateFun μ π L₀ R t M ≠ ⊤) (hM₀ : rateFun μ π L₀ R t M₀ ≠ ⊤) {ε : ℝ} (hε : 0 ≤ ε)
    (hε1 : ε ≤ 1) :
    rateFun μ π L₀ R t ((1 - ε) • M + ε • M₀) ≤
      ENNReal.ofReal ((1 - ε) * (rateFun μ π L₀ R t M).toReal +
        ε * (rateFun μ π L₀ R t M₀).toReal) := by
  refine iSup_le fun q ↦ ENNReal.ofReal_le_ofReal ?_
  rw [chernoffScore_combo]
  have h1 : chernoffScore μ π L₀ R t M q ≤ (rateFun μ π L₀ R t M).toReal :=
    (ENNReal.ofReal_le_iff_le_toReal hM).1
      (le_iSup (fun q ↦ ENNReal.ofReal (chernoffScore μ π L₀ R t M q)) q)
  have h2 : chernoffScore μ π L₀ R t M₀ q ≤ (rateFun μ π L₀ R t M₀).toReal :=
    (ENNReal.ofReal_le_iff_le_toReal hM₀).1
      (le_iSup (fun q ↦ ENNReal.ofReal (chernoffScore μ π L₀ R t M₀ q)) q)
  exact add_le_add (mul_le_mul_of_nonneg_left h1 (by linarith)) (mul_le_mul_of_nonneg_left h2 hε)

section

variable [Nonempty ι] [Nonempty X] {π L₀ : X → ℝ} (hπm : Measurable π) (hπi : Integrable π μ)
  (hπ : ∀ x, 0 < π x) (hπpos : 0 < ∫ x, π x ∂μ) (hL₀m : Measurable L₀) {M₀ : ℝ}
  (hL₀ : ∀ x, |L₀ x| ≤ M₀) {R : ι → X → ℝ} (hR : ∀ i, Bdd (R i)) {t : ℝ} (ht : 0 < t)
  (hnd : ∀ v : ι → ℝ, v ≠ 0 → ¬ ∃ c : ℝ, ∀ᵐ x ∂μ, π x ≠ 0 → dirLoss R v x = c)
include hπm hπi hπ hπpos hL₀m hL₀ hR ht hnd

omit [Fintype ι] [Nonempty ι] [Nonempty X] hπm hπi hπ hπpos hL₀m hL₀ hR ht hnd in
/-- **Radial interior approximation**: the segment from a point of the moment body to an interior
point lies in the interior except possibly at its start. -/
theorem radial_mem_interior {M N : ι → ℝ} (hM : M ∈ momentBody μ π R)
    (hN : N ∈ interior (momentBody μ π R)) {ε : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1) :
    (1 - ε) • M + ε • N ∈ interior (momentBody μ π R) :=
  (convex_momentBody R).combo_closure_interior_mem_interior (subset_closure hM) hN (by linarith)
    hε (by ring)

omit [Nonempty ι] hnd in
/-- Along the radial segment towards the featureless response the rate does not increase. -/
theorem rateFun_radial_le {M : ι → ℝ} (hM : rateFun μ π L₀ R t M ≠ ⊤) {ε : ℝ} (hε : 0 ≤ ε)
    (hε1 : ε ≤ 1) :
    rateFun μ π L₀ R t ((1 - ε) • M + ε • meanMap μ π L₀ R t 0) ≤ rateFun μ π L₀ R t M := by
  have h0 := rateFun_meanMap_zero hπm hπi hπ hπpos hL₀m hL₀ hR ht
  calc rateFun μ π L₀ R t ((1 - ε) • M + ε • meanMap μ π L₀ R t 0)
      ≤ ENNReal.ofReal ((1 - ε) * (rateFun μ π L₀ R t M).toReal +
          ε * (rateFun μ π L₀ R t (meanMap μ π L₀ R t 0)).toReal) :=
        rateFun_combo_le π L₀ R t hM (by rw [h0]; exact ENNReal.zero_ne_top) hε hε1
    _ ≤ ENNReal.ofReal (rateFun μ π L₀ R t M).toReal := by
        rw [h0, ENNReal.toReal_zero, mul_zero, add_zero]
        exact ENNReal.ofReal_le_ofReal
          (mul_le_of_le_one_left ENNReal.toReal_nonneg (by linarith))
    _ = rateFun μ π L₀ R t M := ENNReal.ofReal_toReal hM

omit [Nonempty ι] ht hnd in
/-- **Cramér's upper bound, closed sets**: if `c < 𝓘` on the closed set `F`, then
`Q^{⊗n}(R̄_n ∈ F) ≤ e^{−n(c−ε)}` for all large `n`. -/
theorem cramer_upper {F : Set (ι → ℝ)} (hF : IsClosed F) {Mb : ι → ℝ} (hMb : ∀ i x, |R i x| ≤ Mb i)
    {c : ℝ} (hc : ∀ x ∈ F, ENNReal.ofReal c < rateFun μ π L₀ R t x) {ε : ℝ} (hε : 0 < ε) :
    ∃ N₀ : ℕ, ∀ n : ℕ, N₀ ≤ n → 0 < n →
      (Measure.pi fun _ : Fin n ↦ familyMeasure μ π L₀ R t 0).real {x | empMean R n x ∈ F} ≤
        Real.exp (-(n * (c - ε))) := by
  have := isProbabilityMeasure_familyMeasure hπm hπi hπ hπpos hL₀m hL₀ hR (t := t) 0
  refine eventually_measureReal_empMean_le_closed (familyMeasure μ π L₀ R t 0) hR hMb hF ?_ hε
  intro x hx _
  obtain ⟨q, hq⟩ := lt_iSup_iff.1 (hc x hx)
  exact ⟨q, (ENNReal.ofReal_lt_ofReal_iff'.1 hq).1⟩

/-- **Cramér's lower bound at an interior response**: if `M ∈ int K` lies in the open set `G` and
`𝓘(M) < c`, then `Q^{⊗n}(R̄_n ∈ G) ≥ e^{−nc}` for all large `n`. -/
theorem cramer_lower_interior {G : Set (ι → ℝ)} (hG : IsOpen G) {M : ι → ℝ}
    (hMint : M ∈ interior (momentBody μ π R)) (hMG : M ∈ G) {c : ℝ}
    (hc : rateFun μ π L₀ R t M < ENNReal.ofReal c) :
    ∃ N₀ : ℕ, ∀ n : ℕ, N₀ ≤ n →
      Real.exp (-(n * c)) ≤
        (Measure.pi fun _ : Fin n ↦ familyMeasure μ π L₀ R t 0).real {x | empMean R n x ∈ G} := by
  have hrange : M ∈ Set.range (meanMap μ π L₀ R t) := by
    rw [range_meanMap_slice hπm hπi hπ hπpos hL₀m hL₀ hR ht hnd]; exact hMint
  obtain ⟨b, rfl⟩ := hrange
  rw [rateFun_meanMap hπm hπi hπ hπpos hL₀m hL₀ hR ht b] at hc
  have hKL := (ENNReal.ofReal_lt_ofReal_iff'.1 hc).1
  obtain ⟨N, hN⟩ := open_lower_bound hπm hπi hπ hπpos hL₀m hL₀ hR ht hG 0 b hMG
    (sub_pos.2 hKL)
  refine ⟨N, fun n hn ↦ ?_⟩
  have h := hN n hn
  rwa [add_sub_cancel] at h

/-- **Cramér's lower bound, open sets**: if some `M ∈ G` has `𝓘(M) < c`, then
`Q^{⊗n}(R̄_n ∈ G) ≥ e^{−nc}` for all large `n`. -/
theorem cramer_lower {G : Set (ι → ℝ)} (hG : IsOpen G) {M : ι → ℝ} (hMG : M ∈ G) {c : ℝ}
    (hc : rateFun μ π L₀ R t M < ENNReal.ofReal c) :
    ∃ N₀ : ℕ, ∀ n : ℕ, N₀ ≤ n →
      Real.exp (-(n * c)) ≤
        (Measure.pi fun _ : Fin n ↦ familyMeasure μ π L₀ R t 0).real {x | empMean R n x ∈ G} := by
  have hne : rateFun μ π L₀ R t M ≠ ⊤ := ne_top_of_lt hc
  have hMK : M ∈ momentBody μ π R := by
    by_contra h
    exact hne (rateFun_eq_top_of_not_mem hπm hπi hπ hπpos hL₀m hL₀ hR h)
  have h0 := meanMap_mem_interior hπm hπi hπ hπpos hL₀m hL₀ hR ht hnd 0
  -- the radial segment enters `G` immediately
  have hcont : Continuous fun ε : ℝ ↦ (1 - ε) • M + ε • meanMap μ π L₀ R t 0 := by fun_prop
  have hev : ∀ᶠ ε in 𝓝 (0 : ℝ),
      ((1 - ε) • M + ε • meanMap μ π L₀ R t 0 ∈ G) ∧ ε < 1 := by
    refine (hcont.tendsto 0 |>.eventually (hG.mem_nhds ?_)).and (eventually_lt_nhds zero_lt_one)
    simpa using hMG
  obtain ⟨ε, hε0, hεG, hε1⟩ := hev.exists_gt
  have hint := radial_mem_interior (μ := μ) (π := π) (R := R) hMK h0 hε0 hε1.le
  have hrate := rateFun_radial_le hπm hπi hπ hπpos hL₀m hL₀ hR ht hne hε0.le hε1.le
  exact cramer_lower_interior hπm hπi hπ hπpos hL₀m hL₀ hR ht hnd hG hint hεG (hrate.trans_lt hc)

end

end Laplace.Multi
