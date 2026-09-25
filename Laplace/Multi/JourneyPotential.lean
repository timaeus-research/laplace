/-
Copyright (c) 2026 Timaeus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Timaeus
-/
import Mathlib
import Laplace.Multi.NaturalCoordinates
import Laplace.Multi.DualPotential

/-!
# The journey theorem: information along an arbitrary path

In the natural coordinates `η` of the joint family `P_η ∝ e^{−⟨η,S⟩}π` (`S = (L₀, R)`), the
information acquired from a base point `η₀` along ANY differentiable path `η(s)` is the integral of
the Fisher form paired between the displacement and the velocity:

  `d/ds KL(P_{η(s)} ‖ P_{η₀}) = G_{η(s)}(η(s) − η₀, η'(s))`   (`hasDerivAt_natKL_path`),
  `KL(P_{η(1)} ‖ P_{η(0)}) = ∫₀¹ G_{η(s)}(η(s) − η(0), η'(s)) ds`   (`natKL_path_eq_integral`),

with `G_η(u, v) = Cov_η(S_u, S_v)`: the endpoint divergence is the potential whose differential is
the Fisher pairing with the displacement, so the total information of a journey from the featureless
point to the data is path-independent and computed along any route (for the natural segment
`η₀ + s d` the integrand is `s G(d, d)`, `natKL_segment_eq_integral`). Unlike the segment integrand,
the general integrand need not be pointwise nonnegative.
-/

open MeasureTheory Filter Topology Set

namespace Laplace.Multi

variable {X : Type*} [MeasurableSpace X] {μ : Measure X} {ι : Type*} [Fintype ι]

section

variable [Nonempty X] {π L₀ : X → ℝ} (hπm : Measurable π) (hπi : Integrable π μ) (hπ : ∀ x, 0 < π x)
  (hπpos : 0 < ∫ x, π x ∂μ) (hL₀m : Measurable L₀) {M₀ : ℝ} (hL₀ : ∀ x, |L₀ x| ≤ M₀)
  {R : ι → X → ℝ} (hR : ∀ i, Bdd (R i))
include hπm hπi hπ hπpos hL₀m hL₀ hR

/-- **The differential of the endpoint divergence along a path**:
`d/ds KL(P_{η(s)} ‖ P_{η₀}) = Cov_{η(s)}(S_{η(s) − η₀}, S_{η'(s)})`. -/
theorem hasDerivAt_natKL_path (η₀ : Option ι → ℝ) {η : ℝ → Option ι → ℝ} {η' : Option ι → ℝ}
    {s : ℝ} (hη : HasDerivAt η η' s) :
    HasDerivAt (fun s ↦ mixKL μ π (affLoss (fun _ ↦ (0 : ℝ)) (jointStat L₀ R) (η s))
        (dirLoss (jointStat L₀ R) (η₀ - η s)) 1 0 1)
      (priorCov μ π (affLoss (fun _ ↦ (0 : ℝ)) (jointStat L₀ R) (η s))
        (dirLoss (jointStat L₀ R) (η s - η₀)) (dirLoss (jointStat L₀ R) η') 1) s := by
  have hS' := bdd_jointStat hL₀m hL₀ hR
  have h0 : ∀ x, |(fun _ : X ↦ (0 : ℝ)) x| ≤ 0 := fun x ↦ by simp
  have e : (fun s ↦ mixKL μ π (affLoss (fun _ ↦ (0 : ℝ)) (jointStat L₀ R) (η s))
      (dirLoss (jointStat L₀ R) (η₀ - η s)) 1 0 1) = fun s ↦
      affLogZ μ π (fun _ ↦ (0 : ℝ)) (jointStat L₀ R) 1 η₀ -
        affLogZ μ π (fun _ ↦ (0 : ℝ)) (jointStat L₀ R) 1 (η s) +
        ∑ j, (η₀ j - η s j) * meanMap μ π (fun _ ↦ (0 : ℝ)) (jointStat L₀ R) 1 (η s) j :=
    funext fun s ↦ natKL_eq hπm hπi hπ hπpos hL₀m hL₀ hR (η s) η₀
  rw [e]
  have hZ : priorZ μ π (affLoss (fun _ ↦ (0 : ℝ)) (jointStat L₀ R) (η s)) 1 ≠ 0 :=
    (affZ_pos hπm hπi hπ hπpos measurable_const h0 hS' (t := 1) (η s)).ne'
  have hA : HasDerivAt (fun s ↦ affLogZ μ π (fun _ ↦ (0 : ℝ)) (jointStat L₀ R) 1 (η s))
      (((-1 : ℝ) • dotCLM (meanMap μ π (fun _ ↦ (0 : ℝ)) (jointStat L₀ R) 1 (η s))) η') s :=
    (hasFDerivAt_affLogZ hπm hπi (fun x ↦ (hπ x).le) hπpos measurable_const h0 hS' one_pos
      (η s)).comp_hasDerivAt s hη
  have hm : HasDerivAt (fun s ↦ meanMap μ π (fun _ ↦ (0 : ℝ)) (jointStat L₀ R) 1 (η s))
      (meanMapDeriv μ π (fun _ ↦ (0 : ℝ)) (jointStat L₀ R) 1 (η s) η') s :=
    (hasFDerivAt_meanMap hπm hπi (fun x ↦ (hπ x).le) measurable_const h0 hS' one_pos
      hZ).comp_hasDerivAt s hη
  have hmj : ∀ j, HasDerivAt (fun s ↦ meanMap μ π (fun _ ↦ (0 : ℝ)) (jointStat L₀ R) 1 (η s) j)
      (meanMapDeriv μ π (fun _ ↦ (0 : ℝ)) (jointStat L₀ R) 1 (η s) η' j) s := fun j ↦
    hasDerivAt_pi.1 hm j
  have hηj : ∀ j, HasDerivAt (fun s ↦ η₀ j - η s j) (-η' j) s := fun j ↦
    (hasDerivAt_pi.1 hη j).const_sub (η₀ j)
  have hsum : HasDerivAt (fun s ↦ ∑ j, (η₀ j - η s j) *
      meanMap μ π (fun _ ↦ (0 : ℝ)) (jointStat L₀ R) 1 (η s) j)
      (∑ j, (-η' j * meanMap μ π (fun _ ↦ (0 : ℝ)) (jointStat L₀ R) 1 (η s) j +
        (η₀ j - η s j) * meanMapDeriv μ π (fun _ ↦ (0 : ℝ)) (jointStat L₀ R) 1 (η s) η' j)) s :=
    HasDerivAt.fun_sum fun j _ ↦ (hηj j).mul (hmj j)
  have h := ((hasDerivAt_const s (affLogZ μ π (fun _ ↦ (0 : ℝ)) (jointStat L₀ R) 1 η₀)).sub
    hA).add hsum
  refine h.congr_deriv ?_
  have hν : Integrable (baseWeight π (affLoss (fun _ ↦ (0 : ℝ)) (jointStat L₀ R) (η s)) 1) μ :=
    (tiltData_aff hπm hπi (fun x ↦ (hπ x).le) hπpos measurable_const h0 hS' (η s) (η s)
      1).choose_spec.ν_int
  rw [← sum_mul_priorCov_eq hν hS' (bdd_dirLoss hS' η') (η s - η₀)]
  simp only [_root_.smul_apply, smul_eq_mul, dotCLM_apply, dotJ, Finset.sum_add_distrib,
    Pi.sub_apply, meanMapDeriv_apply hπm hπi (fun x ↦ (hπ x).le) measurable_const h0 hS' one_pos
    hZ]
  have e1 : ∑ j, η' j * meanMap μ π (fun _ ↦ (0 : ℝ)) (jointStat L₀ R) 1 (η s) j +
      ∑ j, -η' j * meanMap μ π (fun _ ↦ (0 : ℝ)) (jointStat L₀ R) 1 (η s) j = 0 := by
    rw [← Finset.sum_add_distrib]
    exact Finset.sum_eq_zero fun j _ ↦ by ring
  have e2 : ∑ j, (η₀ j - η s j) * (-1 * priorCov μ π
      (affLoss (fun _ ↦ (0 : ℝ)) (jointStat L₀ R) (η s)) (jointStat L₀ R j)
      (dirLoss (jointStat L₀ R) η') 1) =
      ∑ j, (η s j - η₀ j) * priorCov μ π (affLoss (fun _ ↦ (0 : ℝ)) (jointStat L₀ R) (η s))
        (jointStat L₀ R j) (dirLoss (jointStat L₀ R) η') 1 :=
    Finset.sum_congr rfl fun j _ ↦ by ring
  linarith [e1, e2]

/-- The Fisher pairing `Cov_θ(S_u, S_v)` is continuous in `(θ, u, v)` along continuous paths. -/
theorem continuous_natCov_path {θ u v : ℝ → Option ι → ℝ} (hθ : Continuous θ) (hu : Continuous u)
    (hv : Continuous v) :
    Continuous (fun s ↦ priorCov μ π (affLoss (fun _ ↦ (0 : ℝ)) (jointStat L₀ R) (θ s))
      (dirLoss (jointStat L₀ R) (u s)) (dirLoss (jointStat L₀ R) (v s)) 1) := by
  classical
  have hS' := bdd_jointStat hL₀m hL₀ hR
  have h0 : ∀ x, |(fun _ : X ↦ (0 : ℝ)) x| ≤ 0 := fun x ↦ by simp
  have hν : ∀ ϑ, Integrable (baseWeight π (affLoss (fun _ ↦ (0 : ℝ)) (jointStat L₀ R) ϑ) 1) μ :=
    fun ϑ ↦ (tiltData_aff hπm hπi (fun x ↦ (hπ x).le) hπpos measurable_const h0 hS' ϑ ϑ
      1).choose_spec.ν_int
  -- bilinear expansion in the coordinates
  have e : ∀ s, priorCov μ π (affLoss (fun _ ↦ (0 : ℝ)) (jointStat L₀ R) (θ s))
      (dirLoss (jointStat L₀ R) (u s)) (dirLoss (jointStat L₀ R) (v s)) 1 =
      ∑ j, u s j * ∑ k, v s k * priorCov μ π (affLoss (fun _ ↦ (0 : ℝ)) (jointStat L₀ R) (θ s))
        (jointStat L₀ R j) (jointStat L₀ R k) 1 := by
    intro s
    rw [← sum_mul_priorCov_eq (hν (θ s)) hS' (bdd_dirLoss hS' (v s)) (u s)]
    refine Finset.sum_congr rfl fun j _ ↦ ?_
    congr 1
    rw [priorCov_comm π _ (jointStat L₀ R j) _ 1,
      ← sum_mul_priorCov_eq (hν (θ s)) hS' (hS' j) (v s)]
    exact Finset.sum_congr rfl fun k _ ↦ by rw [priorCov_comm π _ (jointStat L₀ R k) _ 1]
  simp only [e]
  refine continuous_finsetSum _ fun j _ ↦ ((continuous_apply j).comp hu).mul ?_
  refine continuous_finsetSum _ fun k _ ↦ ((continuous_apply k).comp hv).mul ?_
  -- `Cov_θ(S_j, S_k) = −obsMapDeriv θ e_k`, continuous in `θ`
  obtain ⟨hjm, Mj, hjb⟩ := hS' j
  have hc := (continuous_obsMapDeriv hπm hπi hπ hπpos measurable_const h0 hS' hjm hjb one_pos).comp
    hθ
  have hc' := hc.clm_apply (continuous_const (y := (Pi.single k 1 : Option ι → ℝ)))
  have e2 : ∀ s, priorCov μ π (affLoss (fun _ ↦ (0 : ℝ)) (jointStat L₀ R) (θ s))
      (jointStat L₀ R j) (jointStat L₀ R k) 1 =
      -(obsMapDeriv μ π (fun _ ↦ (0 : ℝ)) (jointStat L₀ R j) (jointStat L₀ R) 1 (θ s)
        (Pi.single k 1)) := by
    intro s
    rw [obsMapDeriv_apply hπm hπi hπ hπpos measurable_const h0 hS' hjm hjb one_pos]
    have : dirLoss (jointStat L₀ R) (Pi.single k 1) = jointStat L₀ R k := by
      funext x; simp [dirLoss, Pi.single_apply]
    rw [this]; ring
  simp only [e2]
  exact hc'.neg

/-- **The journey theorem**: for a `C¹` path `η` in the natural coordinates,
`KL(P_{η(1)} ‖ P_{η(0)}) = ∫₀¹ Cov_{η(s)}(S_{η(s) − η(0)}, S_{η'(s)}) ds`. -/
theorem natKL_path_eq_integral {η η' : ℝ → Option ι → ℝ} (hη : ∀ s, HasDerivAt η (η' s) s)
    (hη' : Continuous η') :
    mixKL μ π (affLoss (fun _ ↦ (0 : ℝ)) (jointStat L₀ R) (η 1))
        (dirLoss (jointStat L₀ R) (η 0 - η 1)) 1 0 1 =
      ∫ s in (0 : ℝ)..1, priorCov μ π (affLoss (fun _ ↦ (0 : ℝ)) (jointStat L₀ R) (η s))
        (dirLoss (jointStat L₀ R) (η s - η 0)) (dirLoss (jointStat L₀ R) (η' s)) 1 := by
  have hηc : Continuous η := continuous_iff_continuousAt.2 fun s ↦ (hη s).continuousAt
  have hu : Continuous (fun s ↦ η s - η 0) := hηc.sub continuous_const
  have hcont := continuous_natCov_path hπm hπi hπ hπpos hL₀m hL₀ hR (u := fun s ↦ η s - η 0)
    (v := η') hηc hu hη'
  have hftc := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun s _ ↦ hasDerivAt_natKL_path hπm hπi hπ hπpos hL₀m hL₀ hR (η 0) (hη s))
    (hcont.intervalIntegrable 0 1)
  rw [hftc]
  have h00 : mixKL μ π (affLoss (fun _ ↦ (0 : ℝ)) (jointStat L₀ R) (η 0))
      (dirLoss (jointStat L₀ R) (η 0 - η 0)) 1 0 1 = 0 := by
    rw [natKL_eq hπm hπi hπ hπpos hL₀m hL₀ hR]
    simp
  rw [h00, sub_zero]

/-- The natural segment `η₀ + s d`: the integrand is `s G(d, d)`. -/
theorem natKL_segment_eq_integral (η₀ d : Option ι → ℝ) :
    mixKL μ π (affLoss (fun _ ↦ (0 : ℝ)) (jointStat L₀ R) (η₀ + d))
        (dirLoss (jointStat L₀ R) (η₀ - (η₀ + d))) 1 0 1 =
      ∫ s in (0 : ℝ)..1, s * priorCov μ π (affLoss (fun _ ↦ (0 : ℝ)) (jointStat L₀ R) (η₀ + s • d))
        (dirLoss (jointStat L₀ R) d) (dirLoss (jointStat L₀ R) d) 1 := by
  have hη : ∀ s : ℝ, HasDerivAt (fun s : ℝ ↦ η₀ + s • d) ((fun _ ↦ d) s) s := fun s ↦
    hasDerivAt_affineLine η₀ d s
  have h := natKL_path_eq_integral hπm hπi hπ hπpos hL₀m hL₀ hR hη continuous_const
  simp only [one_smul, zero_smul, add_zero] at h
  rw [h]
  refine intervalIntegral.integral_congr fun s _ ↦ ?_
  rw [show η₀ + s • d - η₀ = s • d by abel, dirLoss_smul, priorCov_const_mul_left]

end

end Laplace.Multi
