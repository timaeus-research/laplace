/-
Copyright (c) 2026 Timaeus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib
import Laplace.Multi.LocationRecovery

/-!
# The translation bridge for localized posterior moments

`Laplace.Multi.LocationRecovery` models the moments of a loss located
at `c` as anchored moments of translated observables
(`locatedMoment`), leaving the identification with the posterior
integral of the actual translated loss `w ↦ L (w - c)` on the
translated region as an unformalised change of variables. This file
closes that gap with a generic unrescaled layer: `regionIntegralQ` /
`regionMomentQ` (the `U`-restricted Gibbs integral and normalized
moment of an arbitrary loss over an arbitrary region, at scale `q`)
and the direct-temperature `regionMomentT`. The package moments are
these objects verbatim (`posteriorMoment_eq_regionMomentQ`), Lebesgue
translation invariance identifies the translated-loss moment with the
located moment (`regionMomentQ_translate`,
`locatedMomentT_eq_regionMomentT`), all identities junk-safe (the
numerator and denominator are individually equal, so no denominator
control is needed), and normalized moments are invariant under
constant shifts of the loss (`regionMomentQ_sub_const`).

Bonus: at analytic points every iterated derivative is symmetric
(`AnalyticAt.iteratedFDeriv_isSymm`, via ω-regularity), which lets
analytic corollaries discharge the `IsSymm` hypotheses of the
recovery headlines.
-/

open Real MeasureTheory Filter Topology Asymptotics
open scoped ContDiff

namespace Laplace.Multi

variable {d : ℕ}

/-! ## The generic unrescaled region layer -/

/-- The `V`-restricted unnormalized Gibbs integral of an observable
`φ` against the loss `Λ` at scale `q` (temperature `t = q⁻²`). -/
noncomputable def regionIntegralQ (Λ : EuclidD d → ℝ)
    (V : Set (EuclidD d)) (φ : EuclidD d → ℝ) (q : ℝ) : ℝ :=
  ∫ w : EuclidD d,
    Set.indicator V (fun w ↦ φ w * Real.exp (-(Λ w / q ^ 2))) w

/-- The normalized `V`-restricted moment at scale `q`. -/
noncomputable def regionMomentQ (Λ : EuclidD d → ℝ)
    (V : Set (EuclidD d)) (φ : EuclidD d → ℝ) (q : ℝ) : ℝ :=
  regionIntegralQ Λ V φ q / regionIntegralQ Λ V (fun _ ↦ 1) q

/-- The normalized `V`-restricted moment at temperature `t`, in the
physical Gibbs form `e^{-tΛ}`. -/
noncomputable def regionMomentT (Λ : EuclidD d → ℝ)
    (V : Set (EuclidD d)) (φ : EuclidD d → ℝ) (t : ℝ) : ℝ :=
  (∫ w : EuclidD d,
      Set.indicator V (fun w ↦ φ w * Real.exp (-(t * Λ w))) w) /
    ∫ w : EuclidD d,
      Set.indicator V (fun w ↦ (1 : ℝ) * Real.exp (-(t * Λ w))) w

/-- The region translated to a center `p`. -/
def translatedRegion (p : EuclidD d) (U : Set (EuclidD d)) :
    Set (EuclidD d) :=
  {w | w - p ∈ U}

@[simp] theorem mem_translatedRegion {p : EuclidD d}
    {U : Set (EuclidD d)} {w : EuclidD d} :
    w ∈ translatedRegion p U ↔ w - p ∈ U :=
  Iff.rfl

/-! ## The package moments are region moments verbatim -/

variable {L : EuclidD d → ℝ} {H : Matrix (Fin d) (Fin d) ℝ}

theorem LocalLaplaceDomain.posteriorIntegral_eq_regionIntegralQ
    (A : LocalLaplaceDomain L H) (f : EuclidD d → ℝ) (q : ℝ) :
    A.posteriorIntegral f q = regionIntegralQ L A.U f q :=
  rfl

theorem LocalLaplaceDomain.posteriorMoment_eq_regionMomentQ
    (A : LocalLaplaceDomain L H) (f : EuclidD d → ℝ) (q : ℝ) :
    A.posteriorMoment f q = regionMomentQ L A.U f q :=
  rfl

/-! ## Translation invariance -/

/-- **Translation of the unnormalized region integral**: the Gibbs
integral of the translated loss over the translated region is the
centred integral of the translated observable. Junk-safe: an exact
Lebesgue substitution, valid for every `q`. -/
theorem regionIntegralQ_translate (Λ : EuclidD d → ℝ) (p : EuclidD d)
    (V : Set (EuclidD d)) (φ : EuclidD d → ℝ) (q : ℝ) :
    regionIntegralQ (fun w ↦ Λ (w - p)) (translatedRegion p V) φ q =
      regionIntegralQ Λ V (fun y ↦ φ (p + y)) q := by
  unfold regionIntegralQ
  rw [← integral_add_left_eq_self
    (fun w ↦ Set.indicator (translatedRegion p V)
      (fun w ↦ φ w * Real.exp (-(Λ (w - p) / q ^ 2))) w) p]
  refine integral_congr_ae (Filter.Eventually.of_forall fun y ↦ ?_)
  beta_reduce
  by_cases hy : y ∈ V
  · rw [Set.indicator_of_mem
      (show p + y ∈ translatedRegion p V by simp [hy]),
      Set.indicator_of_mem hy]
    simp
  · rw [Set.indicator_of_notMem
      (show p + y ∉ translatedRegion p V by simp [hy]),
      Set.indicator_of_notMem hy]

/-- **Translation of the normalized region moment.** -/
theorem regionMomentQ_translate (Λ : EuclidD d → ℝ) (p : EuclidD d)
    (V : Set (EuclidD d)) (φ : EuclidD d → ℝ) (q : ℝ) :
    regionMomentQ (fun w ↦ Λ (w - p)) (translatedRegion p V) φ q =
      regionMomentQ Λ V (fun y ↦ φ (p + y)) q := by
  unfold regionMomentQ
  rw [regionIntegralQ_translate, regionIntegralQ_translate]

/-- **The located moment is the actual moment of the translated
loss** (discharging the definition-level caveat of
`LocationRecovery`): the normalized moment of `w ↦ L (w - p)` over
the translated localization region equals `locatedMoment`. -/
theorem LocalLaplaceDomain.regionMomentQ_translate_eq_locatedMoment
    (A : LocalLaplaceDomain L H) (p : EuclidD d)
    (f : EuclidD d → ℝ) (q : ℝ) :
    regionMomentQ (fun w ↦ L (w - p)) (translatedRegion p A.U) f q =
      A.locatedMoment p f q := by
  rw [regionMomentQ_translate]
  rfl

/-! ## Constant-shift invariance of the normalized moment -/

/-- Subtracting a constant from the loss multiplies the region
integral by a fixed positive factor. -/
theorem regionIntegralQ_sub_const (Λ : EuclidD d → ℝ)
    (V : Set (EuclidD d)) (φ : EuclidD d → ℝ) (q a : ℝ) :
    regionIntegralQ (fun w ↦ Λ w - a) V φ q =
      Real.exp (a / q ^ 2) * regionIntegralQ Λ V φ q := by
  unfold regionIntegralQ
  rw [← integral_const_mul]
  refine integral_congr_ae (Filter.Eventually.of_forall fun w ↦ ?_)
  beta_reduce
  by_cases hw : w ∈ V
  · rw [Set.indicator_of_mem hw, Set.indicator_of_mem hw,
      show -((Λ w - a) / q ^ 2) = a / q ^ 2 + -(Λ w / q ^ 2) from
        by ring,
      Real.exp_add]
    ring
  · rw [Set.indicator_of_notMem hw, Set.indicator_of_notMem hw,
      mul_zero]

/-- **The normalized moment ignores constant shifts of the loss**
(junk-safe: the factor cancels identically). -/
theorem regionMomentQ_sub_const (Λ : EuclidD d → ℝ)
    (V : Set (EuclidD d)) (φ : EuclidD d → ℝ) (q a : ℝ) :
    regionMomentQ (fun w ↦ Λ w - a) V φ q =
      regionMomentQ Λ V φ q := by
  unfold regionMomentQ
  rw [regionIntegralQ_sub_const, regionIntegralQ_sub_const,
    mul_div_mul_left _ _ (Real.exp_pos (a / q ^ 2)).ne']

/-! ## The direct-temperature bridge -/

/-- For positive temperature the physical Gibbs form agrees with the
scale-`q` form under `q = (√t)⁻¹`. -/
theorem regionMomentT_eq_regionMomentQ (Λ : EuclidD d → ℝ)
    (V : Set (EuclidD d)) (φ : EuclidD d → ℝ) {t : ℝ} (ht : 0 < t) :
    regionMomentT Λ V φ t =
      regionMomentQ Λ V φ ((Real.sqrt t)⁻¹) := by
  have hq2 : ((Real.sqrt t)⁻¹ : ℝ) ^ 2 = t⁻¹ := by
    rw [← Real.sqrt_inv]
    exact Real.sq_sqrt (by positivity)
  have hexp : ∀ w : EuclidD d,
      Real.exp (-(t * Λ w)) =
        Real.exp (-(Λ w / ((Real.sqrt t)⁻¹) ^ 2)) := by
    intro w
    rw [hq2]
    congr 1
    rw [div_inv_eq_mul]
    ring
  unfold regionMomentT regionMomentQ regionIntegralQ
  congr 1 <;>
    exact integral_congr_ae (Filter.Eventually.of_forall fun w ↦ by
      by_cases hw : w ∈ V
      · rw [Set.indicator_of_mem hw, Set.indicator_of_mem hw, hexp]
      · rw [Set.indicator_of_notMem hw, Set.indicator_of_notMem hw])

/-- **The located temperature moment is the actual physical Gibbs
moment of the translated loss**, for positive temperature. -/
theorem LocalLaplaceDomain.regionMomentT_translate_eq_locatedMomentT
    (A : LocalLaplaceDomain L H) (p : EuclidD d)
    (φ : EuclidD d → ℝ) {t : ℝ} (ht : 0 < t) :
    regionMomentT (fun w ↦ L (w - p)) (translatedRegion p A.U) φ t =
      A.locatedMomentT p φ t := by
  rw [regionMomentT_eq_regionMomentQ _ _ _ ht,
    A.regionMomentQ_translate_eq_locatedMoment]
  rfl

/-! ## Symmetry of iterated derivatives at analytic points -/

/-- **At an analytic point every iterated derivative is symmetric**:
the ω-regularity permutation invariance, packaged as the corpus's
`IsSymm`. Lets analytic corollaries discharge the symmetry
hypotheses of the recovery headlines. -/
theorem _root_.AnalyticAt.iteratedFDeriv_isSymm
    {L : EuclidD d → ℝ} {x : EuclidD d}
    (hL : AnalyticAt ℝ L x) (k : ℕ) :
    (iteratedFDeriv ℝ k L x).IsSymm := by
  intro σ v
  exact (hL.contDiffAt (n := ω)).iteratedFDeriv_comp_perm v σ

end Laplace.Multi
