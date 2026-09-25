/-
Copyright (c) 2026 Timaeus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Timaeus
-/
import Mathlib
import Laplace.Multi.FullMeanGeometry
import Laplace.Multi.SliceVariational

/-!
# Profile geometry: the temperature slice inside the full family

The full family `P_θ ∝ e^{−θ·S}π` has the full mean `μ(θ) = (u, M)`, `u = ⟨L₀⟩`, `M = ⟨R⟩`, and the
dual potential `J(μ) = −θ(μ)·μ − A(θ(μ))`; the temperature-`t` slice has the response `M = m_t(a)`
and the dual potential `I_t(M) = −t a·M − A_t(a)`. The slice is the **profile** of the full family
over the base loss:

* **the profile gap is a divergence** (`profile_gap_eq_famKL`): for every joint point `θ` and slice
  point `a` with the same response `M`,
  `J(μ(θ)) + t u(θ) − I_t(M) = KL(P_θ ‖ P_{t,a})`, so `I_t(M) = min_u {J(u, M) + t u}` with the
  slice point as the unique minimiser (`profile_le`, `profile_gap_self`) — the quantitative form of
  the constrained minimum `slice_variational`;
* **the exact Pythagorean decomposition** (`famKL_pythagoras_slice`): for any joint point `θ`
  with response `M = m_t(a)` and any slice reference `b`,
  `KL(P_θ ‖ P_{t,b}) = KL(P_θ ‖ P_{t,a}) + KL(P_{t,a} ‖ P_{t,b})` — a fixed-response temperature leg
  from `P_θ` to its slice lift, then a slice response leg;
* **rate contraction** (`dualPotential_add_affLogZ_zero`, `profile_rate_contraction`): the profiled
  full rate relative to the featureless member `P_{t,0}` is the slice rate,
  `inf_u {J(u,M) + t u + A_t(0)} = I_t(M) + A_t(0) = KL(P_{t,a} ‖ P_{t,0})`;
* **entropy balance along arbitrary full mean paths** (`hasFDerivAt_relEntropy_fullMean`,
  `hasDerivAt_relEntropy_fullMean_path`): `d𝒮/ds = ⟨θ(μ(s)), μ'(s)⟩`, the mean-coordinate form of
  `d𝒮 = −G(θ, ·)`.

The infinitesimal companions — the mixed-coordinate metric `δ dt² + dMᵀC⁻¹dM` with
`δ = Var(H)` (`natForm_sliceInv_deriv`) and `∂_t 𝒮|_M = −t δ` (`hasDerivAt_relEntropy_temp`) — were
landed earlier: temperature and response directions are orthogonal in the mixed chart.
-/

open MeasureTheory Filter Topology Set

namespace Laplace.Multi

variable {X : Type*} [MeasurableSpace X] {μ : Measure X} {ι : Type*} [Fintype ι]

section

variable [Nonempty X] {π L₀ : X → ℝ} (hπm : Measurable π) (hπi : Integrable π μ)
  (hπ : ∀ x, 0 < π x) (hπpos : 0 < ∫ x, π x ∂μ) (hL₀m : Measurable L₀) {M₀ : ℝ}
  (hL₀ : ∀ x, |L₀ x| ≤ M₀) {R : ι → X → ℝ} (hR : ∀ i, Bdd (R i)) {t : ℝ} (ht : 0 < t)
  (hnd : ∀ v : ι → ℝ, v ≠ 0 → ¬ ∃ c : ℝ, ∀ᵐ x ∂μ, π x ≠ 0 → dirLoss R v x = c)
  (hjnd : ∀ v : Option ι → ℝ, v ≠ 0 →
    ¬ ∃ c : ℝ, ∀ᵐ x ∂μ, π x ≠ 0 → dirLoss (jointStat L₀ R) v x = c)
include hπm hπi hπ hπpos hL₀m hL₀ hR ht hnd hjnd

/-- **The profile gap is a divergence**: `J(μ(θ)) + t u(θ) − I_t(m_t(a)) = KL(P_θ ‖ P_{t,a})`
whenever the joint point `θ` and the slice point `a` share the response `M`. -/
theorem profile_gap_eq_famKL (θ : Option ι → ℝ) (a : ι → ℝ)
    (hM : ∀ i, fullMean μ π L₀ R θ (some i) = meanMap μ π L₀ R t a i) :
    dualPotential μ π (fun _ ↦ (0 : ℝ)) (jointStat L₀ R) 1 (fullMean μ π L₀ R θ) +
        t * fullMean μ π L₀ R θ none - dualPotential μ π L₀ R t (meanMap μ π L₀ R t a) =
      famKL μ π (fun _ ↦ (0 : ℝ)) (jointStat L₀ R) 1 θ (natCoord t a) := by
  unfold fullMean at hM ⊢
  rw [famKL, natKL_eq hπm hπi hπ hπpos hL₀m hL₀ hR θ (natCoord t a), affLogZ_natCoord,
    dualPotential_meanMap hπm hπi (fun x ↦ (hπ x).le) hπpos measurable_const abs_zero_fun_le
      (bdd_jointStat hL₀m hL₀ hR) one_pos hjnd θ,
    dualPotential_meanMap hπm hπi (fun x ↦ (hπ x).le) hπpos hL₀m hL₀ hR ht hnd a]
  simp only [dotJ, Fintype.sum_option, natCoord_none, natCoord_some, hM, sub_mul,
    Finset.sum_sub_distrib, mul_assoc, ← Finset.mul_sum]
  ring

/-- At the slice point itself the profile gap vanishes. -/
theorem profile_gap_self (a : ι → ℝ) :
    dualPotential μ π (fun _ ↦ (0 : ℝ)) (jointStat L₀ R) 1 (fullMean μ π L₀ R (natCoord t a)) +
        t * fullMean μ π L₀ R (natCoord t a) none -
        dualPotential μ π L₀ R t (meanMap μ π L₀ R t a) = 0 := by
  rw [profile_gap_eq_famKL hπm hπi hπ hπpos hL₀m hL₀ hR ht hnd hjnd (natCoord t a) a
    (fun i ↦ meanMap_natCoord_some π L₀ R t a i), famKL,
    natKL_eq hπm hπi hπ hπpos hL₀m hL₀ hR]
  simp

/-- **The slice dual potential is the profile of the full dual potential**:
`I_t(M) ≤ J(u, M) + t u` for every joint point with response `M`. -/
theorem profile_le (θ : Option ι → ℝ) (a : ι → ℝ)
    (hM : ∀ i, fullMean μ π L₀ R θ (some i) = meanMap μ π L₀ R t a i) :
    dualPotential μ π L₀ R t (meanMap μ π L₀ R t a) ≤
      dualPotential μ π (fun _ ↦ (0 : ℝ)) (jointStat L₀ R) 1 (fullMean μ π L₀ R θ) +
        t * fullMean μ π L₀ R θ none := by
  have h := profile_gap_eq_famKL hπm hπi hπ hπpos hL₀m hL₀ hR ht hnd hjnd θ a hM
  have h0 := famKL_nonneg hπm hπi hπ hπpos measurable_const abs_zero_fun_le
    (bdd_jointStat hL₀m hL₀ hR) one_pos θ (natCoord t a)
  linarith

omit hjnd in
/-- The slice rate relative to the featureless member:
`I_t(m(a)) + A_t(0) = KL(P_{t,a} ‖ P_{t,0})`. -/
theorem dualPotential_add_affLogZ_zero (a : ι → ℝ) :
    dualPotential μ π L₀ R t (meanMap μ π L₀ R t a) + affLogZ μ π L₀ R t 0 =
      famKL μ π L₀ R t a 0 := by
  rw [famKL, mixKL_eq_bregman_dual hπm hπi (fun x ↦ (hπ x).le) hπpos hL₀m hL₀ hR ht hnd 0 a,
    dualPotential_meanMap hπm hπi (fun x ↦ (hπ x).le) hπpos hL₀m hL₀ hR ht hnd 0, dotJ_zero_left,
    dotJ_zero_left]
  ring

/-- **Rate contraction**: the profiled full rate relative to `P_{t,0}` is the slice rate:
`KL(P_{t,a} ‖ P_{t,0}) ≤ J(u, M) + t u + A_t(0)` for every joint point with response `M = m(a)`,
with equality at the slice lift. -/
theorem profile_rate_contraction (θ : Option ι → ℝ) (a : ι → ℝ)
    (hM : ∀ i, fullMean μ π L₀ R θ (some i) = meanMap μ π L₀ R t a i) :
    famKL μ π L₀ R t a 0 ≤
      dualPotential μ π (fun _ ↦ (0 : ℝ)) (jointStat L₀ R) 1 (fullMean μ π L₀ R θ) +
        t * fullMean μ π L₀ R θ none + affLogZ μ π L₀ R t 0 := by
  rw [← dualPotential_add_affLogZ_zero hπm hπi hπ hπpos hL₀m hL₀ hR ht hnd a]
  linarith [profile_le hπm hπi hπ hπpos hL₀m hL₀ hR ht hnd hjnd θ a hM]

omit ht hnd hjnd in
/-- **The exact Pythagorean decomposition**: for a joint point `θ` with response `m_t(a)` and any
slice reference `b`, `KL(P_θ ‖ P_{t,b}) = KL(P_θ ‖ P_{t,a}) + KL(P_{t,a} ‖ P_{t,b})`. -/
theorem famKL_pythagoras_slice (θ : Option ι → ℝ) (a b : ι → ℝ)
    (hM : ∀ i, fullMean μ π L₀ R θ (some i) = meanMap μ π L₀ R t a i) :
    famKL μ π (fun _ ↦ (0 : ℝ)) (jointStat L₀ R) 1 θ (natCoord t b) =
      famKL μ π (fun _ ↦ (0 : ℝ)) (jointStat L₀ R) 1 θ (natCoord t a) +
        famKL μ π L₀ R t a b := by
  unfold fullMean at hM
  simp only [famKL]
  rw [natKL_eq hπm hπi hπ hπpos hL₀m hL₀ hR, natKL_eq hπm hπi hπ hπpos hL₀m hL₀ hR,
    affLogZ_natCoord, affLogZ_natCoord, mixKL_aff_eq hπm hπi (fun x ↦ (hπ x).le) hπpos hL₀m hL₀ hR]
  simp only [Fintype.sum_option, natCoord_none, natCoord_some, hM, sub_mul,
    Finset.sum_sub_distrib, mul_assoc, mul_sub, Finset.mul_sum]
  ring

omit ht hnd in
/-- **The relative entropy has gradient `θ` in full mean coordinates** (Fréchet form). -/
theorem hasFDerivAt_relEntropy_fullMean (θ : Option ι → ℝ) :
    HasFDerivAt (fun M ↦ relEntropy μ π L₀ R (Function.invFun (fullMean μ π L₀ R) M))
      (dotCLM θ) (fullMean μ π L₀ R θ) := by
  have hS := bdd_jointStat hL₀m hL₀ hR
  have hI := hasFDerivAt_dualPotential hπm hπi (fun x ↦ (hπ x).le) hπpos measurable_const
    abs_zero_fun_le hS one_pos hjnd θ
  have h := (hasFDerivAt_const (dualPotential μ π (fun _ ↦ (0 : ℝ)) (jointStat L₀ R) 1
    (fullMean μ π L₀ R 0)) (fullMean μ π L₀ R θ)).sub hI
  have hev : (fun M ↦ dualPotential μ π (fun _ ↦ (0 : ℝ)) (jointStat L₀ R) 1
      (fullMean μ π L₀ R 0) - dualPotential μ π (fun _ ↦ (0 : ℝ)) (jointStat L₀ R) 1 M) =ᶠ[𝓝
      (fullMean μ π L₀ R θ)]
      fun M ↦ relEntropy μ π L₀ R (Function.invFun (fullMean μ π L₀ R) M) := by
    have hopen : IsOpen (Set.range (fullMean μ π L₀ R)) :=
      isOpen_range_meanMap hπm hπi (fun x ↦ (hπ x).le) hπpos measurable_const abs_zero_fun_le hS
        one_pos hjnd
    filter_upwards [hopen.mem_nhds ⟨θ, rfl⟩] with M hM
    obtain ⟨ϑ, rfl⟩ := hM
    have e : Function.invFun (fullMean μ π L₀ R) (fullMean μ π L₀ R ϑ) = ϑ :=
      invFun_meanMap hπm hπi (fun x ↦ (hπ x).le) hπpos measurable_const abs_zero_fun_le hS one_pos
        hjnd ϑ
    rw [e, relEntropy_eq_meanEntropy hπm hπi hπ hπpos hL₀m hL₀ hR hjnd ϑ]
    unfold fullMean
    rw [meanEntropy_eq_dual hπm hπi hπ hπpos measurable_const abs_zero_fun_le hS one_pos hjnd ϑ]
  refine (h.congr_of_eventuallyEq hev.symm).congr_fderiv ?_
  ext v
  simp [dotCLM_apply]

omit ht hnd in
/-- **Entropy balance along an arbitrary full mean path**: `d𝒮/ds = ⟨θ(μ(s)), μ'(s)⟩`. -/
theorem hasDerivAt_relEntropy_fullMean_path {p : ℝ → Option ι → ℝ} {p' : Option ι → ℝ} {s : ℝ}
    (hp : HasDerivAt p p' s) (θ : Option ι → ℝ) (hθ : p s = fullMean μ π L₀ R θ) :
    HasDerivAt (fun s ↦ relEntropy μ π L₀ R (Function.invFun (fullMean μ π L₀ R) (p s)))
      (dotJ p' θ) s := by
  have h := hasFDerivAt_relEntropy_fullMean hπm hπi hπ hπpos hL₀m hL₀ hR hjnd θ
  rw [← hθ] at h
  have h2 := h.comp_hasDerivAt s hp
  exact h2.congr_deriv (dotCLM_apply θ p')

end

end Laplace.Multi
