/-
Copyright (c) 2026 Timaeus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Laplace.Grammar.PolydiscCoeff

/-!
# The Taylor tree under the paper's analytic hypothesis, every dimension (Stage 7e)

Unit 264 (Astra #31 route R2, unit 8 of the tranche). For `F : (Fin d → ℂ) → ℂ` holomorphic on the
open polydisc `{|zᵢ| < R}` and `0 < b < r < R`, the real parts of the several-variable Cauchy
coefficients at radius `r` form a coefficient family `polyRealCoeff d r F` with
`∑_γ |c_γ| b^{|γ|} < ∞` (`absSummableAt_polyRealCoeff`) that represents `Re F` on the box `(0,b]^d`
(`evalF_polyRealCoeff`). Hence

**Headline XXXII** (`thm_TaylorTree_analytic`): for real `ξ, η` on `(0,b]^d` with holomorphic
extensions `Fξ, Fη` to a polydisc of radius `R > b` (`Re Fξ = ξ`, `Re Fη = η` on the box), the
Taylor-tree conclusion holds for their Cauchy-coefficient families and the family standard
integral is the original `Z(N) = ∫_{(0,b]^d} η u^h e^{-βN u^{2k} + β√N u^k ξ(u)} du` —
`thm:TaylorTree` / `cor:standardintegralexp` **applies under the paper's hypothesis**, in every
dimension. The formal matching assumption is the weaker real-part agreement `Re Fξ = ξ` on the
positive box (a genuine holomorphic extension of a real-analytic `ξ` satisfies it); the intermediate
radius `r ∈ (b, R)` always exists (`thm_TaylorTree_analytic'`). Not part of this statement: the
identification of the Cauchy coefficients with derivatives, `polyCoeff γ F = ∂^γ F(0)/γ!` (complex)
and hence `polyRealCoeff γ F = Re(∂^γ F(0)/γ!)`, and its linkage to derivatives of the given real
`ξ` at `0` (which needs the genuine extension, not box agreement). No `sorry` and no additional
`axiom` declarations.
-/

open MeasureTheory Set Real Filter Topology Complex

namespace Laplace.Grammar

open MonoRep CoeffFamily

/-- The real parts of the several-variable Cauchy coefficients, as a coefficient family. -/
noncomputable def polyRealCoeff (d : ℕ) (r : ℝ) (F : (Fin d → ℂ) → ℂ) : CoeffFamily d :=
  fun γ => (polyCoeff d r F γ).re

/-- A holomorphic function on the open polydisc of radius `R` is bounded on the closed polydisc of
radius `r < R`. -/
theorem exists_bound_closedPolydisc {d : ℕ} {R r : ℝ} (hrR : r < R) {F : (Fin d → ℂ) → ℂ}
    (hF : DifferentiableOn ℂ F (openPolydisc d R)) :
    ∃ M, ∀ w ∈ closedPolydisc d r, ‖F w‖ ≤ M :=
  (isCompact_closedPolydisc d r).exists_bound_of_continuousOn
    (hF.continuousOn.mono (closedPolydisc_subset_openPolydisc d hrR))

theorem const_mem_openPolydisc {d : ℕ} {b r : ℝ} (hb : 0 ≤ b) (hbr : b < r) :
    (fun _ : Fin d => (b : ℂ)) ∈ openPolydisc d r := by
  rw [mem_openPolydisc]; intro _; simpa [abs_of_nonneg hb] using hbr

/-- **Weighted summability** of the real Cauchy coefficients at every radius `b < r`. -/
theorem absSummableAt_polyRealCoeff {d : ℕ} {R r b : ℝ} (hr : 0 < r) (hrR : r < R) (hb : 0 ≤ b)
    (hbr : b < r) {F : (Fin d → ℂ) → ℂ} (hF : DifferentiableOn ℂ F (openPolydisc d R)) :
    AbsSummableAt (polyRealCoeff d r F) b := by
  obtain ⟨M, hM⟩ := exists_bound_closedPolydisc hrR hF
  have hMt : ∀ w ∈ torusSet d r, ‖F w‖ ≤ M := fun w hw =>
    hM w (torusSet_subset_closedPolydisc d r hw)
  have hs := summable_norm_polyCoeff_mul_pow hr hMt (const_mem_openPolydisc hb hbr)
  unfold AbsSummableAt polyRealCoeff
  refine Summable.of_nonneg_of_le (fun γ => by positivity) (fun γ => ?_) hs
  rw [norm_mul, norm_prod]
  simp only [norm_pow, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hb,
    Finset.prod_pow_eq_pow_sum]
  exact mul_le_mul_of_nonneg_right (Complex.abs_re_le_norm _) (by positivity)

/-- Points of the real box `(0,b]^d` lie in the open polydisc of radius `r > b`. -/
theorem ofReal_mem_openPolydisc {d : ℕ} {b r : ℝ} (hbr : b < r) {u : Fin d → ℝ}
    (hu : u ∈ piBox d (Ioc 0 b)) : (fun i => (u i : ℂ)) ∈ openPolydisc d r := by
  rw [mem_openPolydisc]
  intro i
  have hi := hu i (Set.mem_univ _)
  rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos hi.1]
  linarith [hi.2]

/-- **Representation**: the real Cauchy-coefficient family represents `Re F` on `(0,b]^d`. -/
theorem evalF_polyRealCoeff {d : ℕ} {R r b : ℝ} (hr : 0 < r) (hrR : r < R) (hbr : b < r)
    {F : (Fin d → ℂ) → ℂ} (hF : DifferentiableOn ℂ F (openPolydisc d R)) {u : Fin d → ℝ}
    (hu : u ∈ piBox d (Ioc 0 b)) :
    evalF (polyRealCoeff d r F) u = (F fun i => (u i : ℂ)).re := by
  obtain ⟨M, hM⟩ := exists_bound_closedPolydisc hrR hF
  have hslice := sliceHolo_of_differentiableOn d hr hrR hF
  have h := hasSum_polyCoeff d hr hslice hM (ofReal_mem_openPolydisc hbr hu)
  have h2 := h.mapL Complex.reCLM
  unfold evalF polyRealCoeff
  refine (h2.congr_fun fun γ => ?_).tsum_eq
  simp only [Complex.reCLM_apply]
  rw [show (∏ i, ((u i : ℂ)) ^ γ i) = ((∏ i, u i ^ γ i : ℝ) : ℂ) by push_cast; rfl,
    Complex.re_mul_ofReal]
  rfl

/-- The original standard integral on `(0,b]^d` for real `ξ, η`. -/
noncomputable def origPhaseIntegral (n : ℕ) (h k : Fin (n + 1) → ℕ) (β N b : ℝ)
    (ξ η : (Fin (n + 1) → ℝ) → ℝ) : ℝ :=
  ∫ u in piBox (n + 1) (Ioc 0 b), η u * (∏ i, u i ^ h i) *
    Real.exp (-(β * N * ∏ i, u i ^ (2 * k i)) + β * (Real.sqrt N * ∏ i, u i ^ k i) * ξ u)

theorem familyPhaseIntegralBox_eq_orig (n : ℕ) (h k : Fin (n + 1) → ℕ) (β N b : ℝ)
    {cξ cη : CoeffFamily (n + 1)} {ξ η : (Fin (n + 1) → ℝ) → ℝ}
    (hξ : ∀ u ∈ piBox (n + 1) (Ioc 0 b), evalF cξ u = ξ u)
    (hη : ∀ u ∈ piBox (n + 1) (Ioc 0 b), evalF cη u = η u) :
    familyPhaseIntegralBox n h k β N b cξ cη = origPhaseIntegral n h k β N b ξ η := by
  unfold familyPhaseIntegralBox origPhaseIntegral
  refine setIntegral_congr_fun (measurableSet_piBox _ _ measurableSet_Ioc) fun u hu => ?_
  rw [hξ u hu, hη u hu]

/-- **Headline XXXII — `thm:TaylorTree` under the paper's hypothesis, every dimension.** Let `ξ, η`
be real functions on `(0,b]^d` with holomorphic extensions `Fξ, Fη` to the polydisc `{|zᵢ| < R}`,
`R > b > 0` (`Re Fξ = ξ`, `Re Fη = η` on the box). Then for any `r ∈ (b, R)` the real
Cauchy-coefficient families of `Fξ, Fη` at radius `r` satisfy the Taylor-tree conclusion, and their
family standard integral is the original `Z(N)`. -/
theorem thm_TaylorTree_analytic (n : ℕ) (h k : Fin (n + 1) → ℕ) (hk : ∀ i, 0 < k i) (β : ℝ)
    (hβ : 0 < β) {b r R : ℝ} (hb : 0 < b) (hbr : b < r) (hrR : r < R)
    {Fξ Fη : (Fin (n + 1) → ℂ) → ℂ} {ξ η : (Fin (n + 1) → ℝ) → ℝ}
    (hFξ : DifferentiableOn ℂ Fξ (openPolydisc (n + 1) R))
    (hFη : DifferentiableOn ℂ Fη (openPolydisc (n + 1) R))
    (hξ : ∀ u ∈ piBox (n + 1) (Ioc 0 b), (Fξ fun i => (u i : ℂ)).re = ξ u)
    (hη : ∀ u ∈ piBox (n + 1) (Ioc 0 b), (Fη fun i => (u i : ℂ)).re = η u) :
    ∃ C : ℝ → ℕ → ℝ,
      TaylorTreeConclusion n h k β b (polyRealCoeff (n + 1) r Fξ) (polyRealCoeff (n + 1) r Fη) C ∧
      ∀ N, familyPhaseIntegralBox n h k β N b (polyRealCoeff (n + 1) r Fξ)
        (polyRealCoeff (n + 1) r Fη) = origPhaseIntegral n h k β N b ξ η := by
  have hr : 0 < r := lt_trans hb hbr
  obtain ⟨C, hC⟩ := thm_TaylorTree_coeffFamily n h k hk β hβ hb
    (absSummableAt_polyRealCoeff hr hrR hb.le hbr hFξ)
    (absSummableAt_polyRealCoeff hr hrR hb.le hbr hFη)
  refine ⟨C, hC, fun N => familyPhaseIntegralBox_eq_orig n h k β N b ?_ ?_⟩
  · intro u hu; rw [evalF_polyRealCoeff hr hrR hbr hFξ hu, hξ u hu]
  · intro u hu; rw [evalF_polyRealCoeff hr hrR hbr hFη hu, hη u hu]

/-- **Headline XXXII, paper-facing form**: the same conclusion from `0 < b < R` alone (the
intermediate radius `r = (b + R)/2` is chosen inside the proof). -/
theorem thm_TaylorTree_analytic' (n : ℕ) (h k : Fin (n + 1) → ℕ) (hk : ∀ i, 0 < k i) (β : ℝ)
    (hβ : 0 < β) {b R : ℝ} (hb : 0 < b) (hbR : b < R)
    {Fξ Fη : (Fin (n + 1) → ℂ) → ℂ} {ξ η : (Fin (n + 1) → ℝ) → ℝ}
    (hFξ : DifferentiableOn ℂ Fξ (openPolydisc (n + 1) R))
    (hFη : DifferentiableOn ℂ Fη (openPolydisc (n + 1) R))
    (hξ : ∀ u ∈ piBox (n + 1) (Ioc 0 b), (Fξ fun i => (u i : ℂ)).re = ξ u)
    (hη : ∀ u ∈ piBox (n + 1) (Ioc 0 b), (Fη fun i => (u i : ℂ)).re = η u) :
    ∃ (cξ cη : CoeffFamily (n + 1)) (C : ℝ → ℕ → ℝ),
      TaylorTreeConclusion n h k β b cξ cη C ∧
      ∀ N, familyPhaseIntegralBox n h k β N b cξ cη = origPhaseIntegral n h k β N b ξ η := by
  have hbr : b < (b + R) / 2 := by linarith
  have hrR : (b + R) / 2 < R := by linarith
  obtain ⟨C, hC, hZ⟩ := thm_TaylorTree_analytic n h k hk β hβ hb hbr hrR hFξ hFη hξ hη
  exact ⟨_, _, C, hC, hZ⟩

end Laplace.Grammar
