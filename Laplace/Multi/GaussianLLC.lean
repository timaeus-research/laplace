/-
Copyright (c) 2026 Timaeus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniel Murfet
-/
import Laplace.Multi.GaussianIBP

/-!
# The quadratic Gaussian expectation and the localised LLC

For the quadratic loss `L(w) = ½ ⟨w, H w⟩` and the localised weight
`exp(-t L(w) - (γ/2) |w|²) = exp(-½ ⟨w, P w⟩)`, `P = t H + γ`, the expectation of the
excess loss `K = L` under the normalised weight is `½ tr(H P⁻¹)`; with `γ = 0` this is
`t ⟨K⟩ = d/2`. This is the Hessian-route prediction for the local learning coefficient
tested in experiment E3 of the note *Sanity on Sampling*, derived from the seabed's
Gaussian second-moment identity `gaussian_second_moment_eq_inverse_entry`.
-/

namespace Laplace.Multi

open MeasureTheory

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

noncomputable section

/-- The pairing `∑ i j, H_ij (P⁻¹)_ij = tr(Hᵀ P⁻¹)` of the matrices of `H` and `Pinv` read off
in the standard basis; for symmetric `H` this is `tr(H P⁻¹)`. -/
def hessInvPairing (H Pinv : (ι → ℝ) →L[ℝ] (ι → ℝ)) : ℝ :=
  ∑ i, ∑ j, (H (Pi.single (M := fun _ : ι => ℝ) j (1 : ℝ))) i *
    (Pinv (Pi.single (M := fun _ : ι => ℝ) j (1 : ℝ))) i

/-- `H u = ∑ j, u j • H e_j`, coordinatewise. -/
lemma clm_apply_eq_sum (H : (ι → ℝ) →L[ℝ] (ι → ℝ)) (u : ι → ℝ) (i : ι) :
    (H u) i = ∑ j, u j * (H (Pi.single (M := fun _ : ι => ℝ) j (1 : ℝ))) i := by
  conv_lhs => rw [eq_sum_stdBasis u]
  rw [map_sum, Finset.sum_apply]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [map_smul, Pi.smul_apply, smul_eq_mul]


/-- The quadratic form as a double sum over coordinates. -/
lemma quadForm_eq_double_sum (H : (ι → ℝ) →L[ℝ] (ι → ℝ)) (u : ι → ℝ) :
    quadForm H u = ∑ i, ∑ j, (H (Pi.single (M := fun _ : ι => ℝ) j (1 : ℝ))) i * (u i * u j) := by
  unfold quadForm
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [clm_apply_eq_sum H u i, Finset.mul_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  ring


/-- **Quadratic Gaussian expectation.**
`∫ ⟨u, H u⟩ e^{-½⟨u,Pu⟩} du = Z(P) · ∑ i j, H_ij (P⁻¹)_ij`. -/
theorem gaussian_quadForm_integral
    (H P Pinv : (ι → ℝ) →L[ℝ] (ι → ℝ))
    (hPinv : P.comp Pinv = ContinuousLinearMap.id ℝ (ι → ℝ))
    (hP_inj : Function.Injective P)
    (h_int_gW : Integrable (gaussianWeight P))
    (h_int_uk_uj_gW : ∀ k j : ι, Integrable
      (fun u : ι → ℝ => u k * u j * gaussianWeight P u))
    (h_int_uj_Pi_gW : ∀ j i : ι, Integrable
      (fun u : ι → ℝ => u j * (P u) i * gaussianWeight P u))
    (h_fubini : ∀ i j : ι, FubiniIBPHypothesis P i j) :
    ∫ u : ι → ℝ, quadForm H u * gaussianWeight P u = gaussianZ P * hessInvPairing H Pinv := by
  have hpt : ∀ u : ι → ℝ, quadForm H u * gaussianWeight P u
      = ∑ i, ∑ j, (H (Pi.single (M := fun _ : ι => ℝ) j (1 : ℝ))) i *
          (u i * u j * gaussianWeight P u) := by
    intro u
    rw [quadForm_eq_double_sum, Finset.sum_mul]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Finset.sum_mul]
    refine Finset.sum_congr rfl fun j _ => ?_
    ring
  have h2 : ∀ i j : ι, ∫ u : ι → ℝ, u i * u j * gaussianWeight P u
      = gaussianZ P * (Pinv (Pi.single (M := fun _ : ι => ℝ) j (1 : ℝ))) i := fun i j =>
    gaussian_second_moment_eq_inverse_entry_scalar P Pinv hPinv hP_inj i j h_int_gW
      (fun k => h_int_uk_uj_gW k j) (fun i => h_int_uj_Pi_gW j i) (fun i => h_fubini i j)
  simp_rw [hpt]
  rw [integral_finsetSum _ (fun i _ => integrable_finsetSum _
    (fun j _ => (h_int_uk_uj_gW i j).const_mul _))]
  simp_rw [integral_finsetSum _ (fun j _ => (h_int_uk_uj_gW _ j).const_mul _),
    integral_const_mul, h2]
  simp only [hessInvPairing, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  ring


/-- **Localised Gaussian LLC.** With `P = t H + γ`, the normalised expectation of
`K = ½ ⟨u, H u⟩` is `½ ∑ i j, H_ij (P⁻¹)_ij`, i.e. `½ tr(H P⁻¹)` for symmetric `H`. -/
theorem localised_gaussian_K_expectation
    (H Pinv : (ι → ℝ) →L[ℝ] (ι → ℝ)) (t γ : ℝ)
    (hPinv : (t • H + γ • ContinuousLinearMap.id ℝ (ι → ℝ)).comp Pinv
      = ContinuousLinearMap.id ℝ (ι → ℝ))
    (hP_inj : Function.Injective (t • H + γ • ContinuousLinearMap.id ℝ (ι → ℝ)))
    (hZ : gaussianZ (t • H + γ • ContinuousLinearMap.id ℝ (ι → ℝ)) ≠ 0)
    (h_int_gW : Integrable (gaussianWeight (t • H + γ • ContinuousLinearMap.id ℝ (ι → ℝ))))
    (h_int_uk_uj_gW : ∀ k j : ι, Integrable
      (fun u : ι → ℝ => u k * u j *
        gaussianWeight (t • H + γ • ContinuousLinearMap.id ℝ (ι → ℝ)) u))
    (h_int_uj_Pi_gW : ∀ j i : ι, Integrable
      (fun u : ι → ℝ => u j * ((t • H + γ • ContinuousLinearMap.id ℝ (ι → ℝ)) u) i *
        gaussianWeight (t • H + γ • ContinuousLinearMap.id ℝ (ι → ℝ)) u))
    (h_fubini : ∀ i j : ι,
      FubiniIBPHypothesis (t • H + γ • ContinuousLinearMap.id ℝ (ι → ℝ)) i j) :
    (∫ u : ι → ℝ, (1 / 2 * quadForm H u) *
        gaussianWeight (t • H + γ • ContinuousLinearMap.id ℝ (ι → ℝ)) u) /
      gaussianZ (t • H + γ • ContinuousLinearMap.id ℝ (ι → ℝ))
      = 1 / 2 * hessInvPairing H Pinv := by
  have h := gaussian_quadForm_integral H _ Pinv hPinv hP_inj h_int_gW h_int_uk_uj_gW
    h_int_uj_Pi_gW h_fubini
  have hhalf : (∫ u : ι → ℝ, (1 / 2 * quadForm H u) *
      gaussianWeight (t • H + γ • ContinuousLinearMap.id ℝ (ι → ℝ)) u)
      = 1 / 2 * ∫ u : ι → ℝ, quadForm H u *
          gaussianWeight (t • H + γ • ContinuousLinearMap.id ℝ (ι → ℝ)) u := by
    rw [← integral_const_mul]
    congr 1
    funext u
    ring
  rw [hhalf, h]
  field_simp


/-- For symmetric `H` the pairing with `(1/t) H⁻¹` is `d / t`. -/
lemma hessInvPairing_self_inv
    (H Hinv : (ι → ℝ) →L[ℝ] (ι → ℝ)) (t : ℝ)
    (hHinv : H.comp Hinv = ContinuousLinearMap.id ℝ (ι → ℝ))
    (hHsym : ∀ i j, (H (Pi.single (M := fun _ : ι => ℝ) j (1 : ℝ))) i
      = (H (Pi.single (M := fun _ : ι => ℝ) i (1 : ℝ))) j) :
    hessInvPairing H ((1 / t) • Hinv) = Fintype.card ι / t := by
  have hHH : ∀ j : ι, H (Hinv (Pi.single (M := fun _ : ι => ℝ) j (1 : ℝ)))
      = Pi.single (M := fun _ : ι => ℝ) j (1 : ℝ) := fun j => by
    have := congrArg (fun L : (ι → ℝ) →L[ℝ] (ι → ℝ) => L (Pi.single j 1)) hHinv
    simpa using this
  simp only [hessInvPairing, smul_apply, Pi.smul_apply, smul_eq_mul]
  rw [Finset.sum_comm]
  calc ∑ j, ∑ i, (H (Pi.single (M := fun _ : ι => ℝ) j (1 : ℝ))) i *
        (1 / t * (Hinv (Pi.single (M := fun _ : ι => ℝ) j (1 : ℝ))) i)
      = 1 / t * ∑ j, ∑ i, (Hinv (Pi.single (M := fun _ : ι => ℝ) j (1 : ℝ))) i *
          (H (Pi.single (M := fun _ : ι => ℝ) i (1 : ℝ))) j := by
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun j _ => ?_
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [hHsym i j]
        ring
    _ = 1 / t * ∑ j, (H (Hinv (Pi.single (M := fun _ : ι => ℝ) j (1 : ℝ)))) j := by
        congr 1
        refine Finset.sum_congr rfl fun j _ => ?_
        rw [clm_apply_eq_sum]
    _ = 1 / t * ∑ j : ι, (Pi.single (M := fun _ : ι => ℝ) j (1 : ℝ) : ι → ℝ) j := by
        simp_rw [hHH]
    _ = Fintype.card ι / t := by
        simp [Finset.card_univ]
        ring


/-- **Without localisation, `t ⟨K⟩ = d / 2`.** -/
theorem gaussian_K_expectation_eq_half_dim
    (H Hinv : (ι → ℝ) →L[ℝ] (ι → ℝ)) (t : ℝ) (ht : t ≠ 0)
    (hHinv : H.comp Hinv = ContinuousLinearMap.id ℝ (ι → ℝ))
    (hHsym : ∀ i j, (H (Pi.single (M := fun _ : ι => ℝ) j (1 : ℝ))) i
      = (H (Pi.single (M := fun _ : ι => ℝ) i (1 : ℝ))) j)
    (hH_inj : Function.Injective H)
    (hZ : gaussianZ (t • H) ≠ 0)
    (h_int_gW : Integrable (gaussianWeight (t • H)))
    (h_int_uk_uj_gW : ∀ k j : ι, Integrable
      (fun u : ι → ℝ => u k * u j * gaussianWeight (t • H) u))
    (h_int_uj_Pi_gW : ∀ j i : ι, Integrable
      (fun u : ι → ℝ => u j * ((t • H) u) i * gaussianWeight (t • H) u))
    (h_fubini : ∀ i j : ι, FubiniIBPHypothesis (t • H) i j) :
    t * ((∫ u : ι → ℝ, (1 / 2 * quadForm H u) * gaussianWeight (t • H) u) / gaussianZ (t • H))
      = Fintype.card ι / 2 := by
  have hPinv : (t • H).comp ((1 / t) • Hinv) = ContinuousLinearMap.id ℝ (ι → ℝ) := by
    rw [ContinuousLinearMap.comp_smul, ContinuousLinearMap.smul_comp, smul_smul,
      one_div_mul_cancel ht, one_smul, hHinv]
  have hP_inj : Function.Injective (t • H) := by
    intro u v huv
    apply hH_inj
    have : t • H u = t • H v := by simpa using huv
    exact smul_right_injective _ ht this
  have h := gaussian_quadForm_integral H (t • H) ((1 / t) • Hinv) hPinv hP_inj h_int_gW
    h_int_uk_uj_gW h_int_uj_Pi_gW h_fubini
  have hhalf : (∫ u : ι → ℝ, (1 / 2 * quadForm H u) * gaussianWeight (t • H) u)
      = 1 / 2 * ∫ u : ι → ℝ, quadForm H u * gaussianWeight (t • H) u := by
    rw [← integral_const_mul]
    congr 1
    funext u
    ring
  rw [hhalf, h, hessInvPairing_self_inv H Hinv t hHinv hHsym]
  field_simp


end

end Laplace.Multi
