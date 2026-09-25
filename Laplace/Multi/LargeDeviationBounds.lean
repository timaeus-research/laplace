/-
Copyright (c) 2026 Timaeus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Timaeus
-/
import Mathlib
import Laplace.Multi.AsymptoticUpperBound
import Laplace.Multi.TiltLowerBound

/-!
# The bounded-feature large-deviation bounds: closed sets from above, open sets from below

For bounded features `|Rᵢ| ≤ Mᵢ` the empirical response lies in the box `B = ∏ [−Mᵢ, Mᵢ]`
(`abs_empMean_le`), so a closed set `F` is hit exactly when the compact set `F ∩ B` is, and the
compact-cover Chernoff bound extends to closed sets with no exponential-tightness machinery
(`closed_cover_chernoff`, asymptotic form `eventually_measureReal_empMean_le_closed`).

From below, the tilt lower bound of `TiltLowerBound` at any tilted mean `m_t(b)` lying in an open
set `G` gives `P_a^{⊗n}(R̄_n ∈ G) ≥ e^{−n(KL(P_b ‖ P_a) + δ)}` for all large `n`
(`open_lower_bound`, log form `eventually_le_log_measureReal_empMean_div`): the rate of an open
set is at most the information distance to any member whose response it contains — and every
interior response is such a member by the global chart, so the infimum runs over `G ∩ int K`.
-/

open MeasureTheory Filter Topology Set

namespace Laplace.Multi

variable {X : Type*} [MeasurableSpace X] {ι : Type*} [Fintype ι]

section Closed

variable (ν : Measure X) [IsProbabilityMeasure ν] {R : ι → X → ℝ} (hR : ∀ i, Bdd (R i))
include hR

omit [MeasurableSpace X] [Fintype ι] [IsProbabilityMeasure ν] hR in
/-- The empirical response lies in the feature box. -/
theorem abs_empMean_le {M : ι → ℝ} (hM : ∀ i x, |R i x| ≤ M i) (hM0 : ∀ i, 0 ≤ M i) (n : ℕ)
    (x : Fin n → X) (i : ι) : |empMean R n x i| ≤ M i := by
  unfold empMean
  rcases Nat.eq_zero_or_pos n with h0 | hn
  · subst h0; simp [hM0 i]
  · rw [abs_div, Nat.abs_cast, div_le_iff₀ (by exact_mod_cast hn)]
    calc |∑ k, R i (x k)| ≤ ∑ k, |R i (x k)| := Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ _k : Fin n, M i := Finset.sum_le_sum fun k _ ↦ hM i (x k)
      _ = M i * n := by simp [mul_comm]

/-- **The closed-set Chernoff bound**: for bounded features and a closed set `F` with pointwise dual
witnesses on `F ∩ B`, `P(R̄_n ∈ F) ≤ N e^{−nα}`. -/
theorem closed_cover_chernoff [Nonempty X] {M : ι → ℝ} (hM : ∀ i x, |R i x| ≤ M i)
    {F : Set (ι → ℝ)} (hF : IsClosed F) {α : ℝ}
    (hwit : ∀ x ∈ F, (∀ i, |x i| ≤ M i) → ∃ θ : ι → ℝ, α < ∑ i, θ i * x i - featCgf ν R θ) :
    ∃ N : ℕ, ∀ n : ℕ, 0 < n →
      (Measure.pi fun _ : Fin n ↦ ν).real {x | empMean R n x ∈ F} ≤ N * Real.exp (-(n * α)) := by
  have hM0 : ∀ i, 0 ≤ M i := fun i ↦ (abs_nonneg _).trans (hM i (Classical.arbitrary X))
  have hBc : IsCompact (Set.pi Set.univ fun i ↦ Icc (-M i) (M i)) :=
    isCompact_univ_pi fun i ↦ isCompact_Icc
  have hFB : IsCompact (F ∩ Set.pi Set.univ fun i ↦ Icc (-M i) (M i)) := hBc.inter_left hF
  have hwit' : ∀ x ∈ F ∩ Set.pi Set.univ fun i ↦ Icc (-M i) (M i),
      ∃ θ : ι → ℝ, α < ∑ i, θ i * x i - featCgf ν R θ :=
    fun x hx ↦ hwit x hx.1 fun i ↦ abs_le.2 (Set.mem_univ_pi.1 hx.2 i)
  obtain ⟨N, hN⟩ := compact_cover_chernoff ν hR hFB hwit'
  refine ⟨N, fun n hn ↦ ?_⟩
  have hset : {x : Fin n → X | empMean R n x ∈ F} =
      {x | empMean R n x ∈ F ∩ Set.pi Set.univ fun i ↦ Icc (-M i) (M i)} :=
    Set.ext fun x ↦ ⟨fun h ↦ ⟨h, Set.mem_univ_pi.2 fun i ↦
      abs_le.1 (abs_empMean_le hM hM0 n x i)⟩, fun h ↦ h.1⟩
  rw [hset]
  exact hN n hn

/-- The closed-set bound in asymptotic root form. -/
theorem eventually_measureReal_empMean_le_closed [Nonempty X] {M : ι → ℝ}
    (hM : ∀ i x, |R i x| ≤ M i) {F : Set (ι → ℝ)} (hF : IsClosed F) {α : ℝ}
    (hwit : ∀ x ∈ F, (∀ i, |x i| ≤ M i) → ∃ θ : ι → ℝ, α < ∑ i, θ i * x i - featCgf ν R θ)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ N₀ : ℕ, ∀ n : ℕ, N₀ ≤ n → 0 < n →
      (Measure.pi fun _ : Fin n ↦ ν).real {x | empMean R n x ∈ F} ≤
        Real.exp (-(n * (α - ε))) := by
  obtain ⟨N, hN⟩ := closed_cover_chernoff ν hR hM hF hwit
  refine ⟨⌈Real.log N / ε⌉₊, fun n hn hn0 ↦ ?_⟩
  have hNe : (N : ℝ) ≤ Real.exp (n * ε) := by
    rcases Nat.eq_zero_or_pos N with h0 | hNpos
    · rw [h0, Nat.cast_zero]
      exact (Real.exp_pos _).le
    · have hNpos' : (0 : ℝ) < N := by exact_mod_cast hNpos
      rw [← Real.log_le_iff_le_exp hNpos']
      have h1 : Real.log N / ε ≤ n := Nat.ceil_le.1 hn
      rwa [div_le_iff₀ hε] at h1
  calc (Measure.pi fun _ : Fin n ↦ ν).real {x | empMean R n x ∈ F}
      ≤ N * Real.exp (-(n * α)) := hN n hn0
    _ ≤ Real.exp (n * ε) * Real.exp (-(n * α)) :=
        mul_le_mul_of_nonneg_right hNe (Real.exp_pos _).le
    _ = Real.exp (-(n * (α - ε))) := by rw [← Real.exp_add]; congr 1; ring

end Closed

section Open

variable [Nonempty X] {μ : Measure X} {π L₀ : X → ℝ} (hπm : Measurable π) (hπi : Integrable π μ)
  (hπ : ∀ x, 0 < π x) (hπpos : 0 < ∫ x, π x ∂μ) (hL₀m : Measurable L₀) {M₀ : ℝ}
  (hL₀ : ∀ x, |L₀ x| ≤ M₀) {R : ι → X → ℝ} (hR : ∀ i, Bdd (R i)) {t : ℝ} (ht : 0 < t)
include hπm hπi hπ hπpos hL₀m hL₀ hR ht

/-- **The open-set lower bound at a tilted mean**: if the open set `G` contains the response
`m_t(b)`, then `P_a^{⊗n}(R̄_n ∈ G) ≥ e^{−n(KL(P_b ‖ P_a) + δ)}` for all large `n`. -/
theorem open_lower_bound {G : Set (ι → ℝ)} (hG : IsOpen G) (a b : ι → ℝ)
    (hb : meanMap μ π L₀ R t b ∈ G) {δ : ℝ} (hδ : 0 < δ) :
    ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
      Real.exp (-(n * (famKL μ π L₀ R t b a + δ))) ≤
        (Measure.pi fun _ : Fin n ↦ familyMeasure μ π L₀ R t a).real {x | empMean R n x ∈ G} := by
  obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.1 hG _ hb
  have e : a - (1 / t) • (t • (a - b)) = b := by
    rw [smul_smul, one_div_mul_cancel ht.ne', one_smul, sub_sub_cancel]
  obtain ⟨N, hN⟩ := tilt_lower_bound hπm hπi hπ hπpos hL₀m hL₀ hR ht a (t • (a - b)) (lam := 1)
    zero_le_one hε hδ
  refine ⟨N, fun n hn ↦ ?_⟩
  have h := hN n hn
  rw [e] at h
  have := isProbabilityMeasure_familyMeasure hπm hπi hπ hπpos hL₀m hL₀ hR (t := t) a
  refine h.trans (measureReal_mono fun x hx ↦ ?_)
  refine hball ?_
  rw [Metric.mem_ball, dist_pi_lt_iff hε]
  intro i
  rw [Real.dist_eq]
  exact hx i

/-- The open-set lower bound in log form: `−(KL(P_b ‖ P_a) + δ) ≤ (1/n) log P_a^{⊗n}(R̄_n ∈ G)`. -/
theorem eventually_le_log_measureReal_empMean_div {G : Set (ι → ℝ)} (hG : IsOpen G)
    (a b : ι → ℝ) (hb : meanMap μ π L₀ R t b ∈ G) {δ : ℝ} (hδ : 0 < δ) :
    ∃ N : ℕ, ∀ n : ℕ, N ≤ n → 0 < n →
      -(famKL μ π L₀ R t b a + δ) ≤
        Real.log ((Measure.pi fun _ : Fin n ↦ familyMeasure μ π L₀ R t a).real
          {x | empMean R n x ∈ G}) / n := by
  obtain ⟨N, hN⟩ := open_lower_bound hπm hπi hπ hπpos hL₀m hL₀ hR ht hG a b hb hδ
  refine ⟨N, fun n hn hn0 ↦ ?_⟩
  have h := Real.log_le_log (Real.exp_pos _) (hN n hn)
  rw [Real.log_exp] at h
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn0
  rw [le_div_iff₀ hn']
  linarith

end Open

end Laplace.Multi
