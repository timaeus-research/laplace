import Laplace.Multi.QuadraticApprox
import Laplace.Multi.GaussianDomination
import Mathlib.MeasureTheory.Integral.IntegralEqImproper

/-!
# Multivariate Gaussian integration by parts

For a continuous linear operator `H : (ι → ℝ) →L[ℝ] (ι → ℝ)` that is
symmetric and coercive (`quadForm H u ≥ c · ∑ uᵢ²` for some `c > 0`),
this file proves the Gaussian second-moment identity

  `∫ uᵢ uⱼ · exp(-(1/2) quadForm H u) du = Z · Σ_{ij}`

where `Z := ∫ exp(-(1/2) quadForm H u) du` and `Σ` is an inverse witness
of `H` (i.e., `H ∘ Σ = id`). The proof is by coordinatewise integration
by parts and avoids spectral / determinant theory entirely.

## Strategy

Per the GPT-5.5 Pro Phase 4 strategy memo (`gpt_responses/phase4_ibp.md`):

1. **Linear algebra helpers** (this file, below): expand any `u : ι → ℝ`
   in the standard basis `Pi.single k 1`; expand `(H u)ᵢ` as a sum over
   matrix entries `H_{ki} := (H (Pi.single k 1))ᵢ`; symmetry gives
   `H_{ki} = H_{ik}`; quadratic-increment formula for `quadForm H`.
2. **1D full-line FTC**: for sufficiently decaying `f` and `f'`,
   `∫ f' = 0` over ℝ.
3. **Derivative of `exp(-Q)`**: in coordinate `i`, the partial derivative
   of `exp(-(1/2) quadForm H u)` is `-(H u)ᵢ · exp(-Q)`.
4. **Core IBP** (`gaussian_ibp_coord`): coordinate-wise IBP after Fubini
   reduction, gives `0 = δ_{ij} · Z - ∑_k H_{ik} · M_{jk}`.
5. **Column form** (`gaussian_ibp_column`): repackages step 4 as
   `H · M_col_j = Z · eⱼ`.
6. **Inverse-entry corollary** (`gaussian_second_moment_eq_inverse_entry`):
   given an inverse witness `Σ` of `H`, deduce `M_{jk} = Z · Σ_{jk}`.

The hypotheses on `H` are explicit (symmetry + coercivity), as in the
rest of the multivariate Laplace pipeline.
-/

namespace Laplace.Multi

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

section LinearAlgebraHelpers

/-- Decomposition of a Pi-typed vector along the standard basis:
`u = ∑ k, u k • Pi.single k 1`. -/
lemma eq_sum_stdBasis (u : ι → ℝ) :
    u = ∑ k, u k • (Pi.single (M := fun _ : ι => ℝ) k (1 : ℝ)) := by
  ext i
  simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
  -- Bridge `u k * Pi.single k 1 i = Pi.single k (u k) i`, then `Fintype.sum_pi_single`.
  have heq : ∀ k, u k * (Pi.single (M := fun _ : ι => ℝ) k (1 : ℝ)) i =
      (Pi.single (M := fun _ : ι => ℝ) k (u k)) i := by
    intro k
    by_cases hk : k = i
    · subst hk; simp
    · rw [Pi.single_eq_of_ne (Ne.symm hk), Pi.single_eq_of_ne (Ne.symm hk),
          mul_zero]
  simp only [heq]
  exact (Fintype.sum_pi_single (M := fun _ : ι => ℝ) i (fun k => u k)).symm

/-- Expansion of `(H u)ᵢ` as a sum over standard-basis matrix entries:
`(H u) i = ∑ k, u k * (H (Pi.single k 1)) i`. -/
lemma H_apply_eq_sum
    (H : (ι → ℝ) →L[ℝ] (ι → ℝ)) (u : ι → ℝ) (i : ι) :
    (H u) i = ∑ k, u k * (H (Pi.single (M := fun _ : ι => ℝ) k (1 : ℝ))) i := by
  conv_lhs => rw [eq_sum_stdBasis u]
  rw [map_sum]
  simp only [Finset.sum_apply, ContinuousLinearMap.map_smul, Pi.smul_apply,
    smul_eq_mul]

/-- Quadratic-form increment along a basis direction (assuming `H` symmetric):
`quadForm H (u + h • e_i) = quadForm H u + 2 h (H u)ᵢ + h² (H e_i)ᵢ`. -/
lemma quadForm_add_smul_stdBasis
    (H : (ι → ℝ) →L[ℝ] (ι → ℝ))
    (hSymm : ∀ x y, ∑ k, x k * (H y) k = ∑ k, y k * (H x) k)
    (i : ι) (u : ι → ℝ) (h : ℝ) :
    quadForm H (u + h • (Pi.single (M := fun _ : ι => ℝ) i (1 : ℝ))) =
      quadForm H u + 2 * h * (H u) i +
        h ^ 2 * (H (Pi.single (M := fun _ : ι => ℝ) i (1 : ℝ))) i := by
  classical
  set e : ι → ℝ := Pi.single (M := fun _ : ι => ℝ) i (1 : ℝ) with he_def
  -- Expand H(u + h•e) = H u + h • (H e).
  have hH_lin : H (u + h • e) = H u + h • H e := by
    rw [map_add, ContinuousLinearMap.map_smul]
  -- Symmetry specialized to (u, e): ∑ u_k (H e)_k = ∑ e_k (H u)_k = (H u)_i.
  have h_sym_ue : ∑ k, u k * (H e) k = (H u) i := by
    have := hSymm u e
    rw [this]
    -- ∑ k, e_k * (H u)_k = (H u)_i since e_k = δ_{ki}
    simp [he_def, Pi.single, Function.update, Finset.sum_ite_eq', Finset.mem_univ]
  -- Compute quadForm at u + h•e using quadForm_def and bilinear expansion.
  unfold quadForm
  have h_expand :
      ∑ k, (u + h • e) k * (H (u + h • e)) k =
        (∑ k, u k * (H u) k) + h * ((H u) i + ∑ k, u k * (H e) k)
          + h ^ 2 * ∑ k, e k * (H e) k := by
    have heq : ∀ k,
        (u + h • e) k * (H (u + h • e)) k =
          u k * (H u) k + h * (e k * (H u) k) + h * (u k * (H e) k) +
            h ^ 2 * (e k * (H e) k) := by
      intro k
      rw [hH_lin]
      simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
      ring
    simp only [heq, Finset.sum_add_distrib, ← Finset.mul_sum]
    have h_e_Hu : ∑ k, e k * (H u) k = (H u) i := by
      simp [he_def, Pi.single, Function.update, Finset.sum_ite_eq', Finset.mem_univ]
    rw [h_e_Hu]
    ring
  rw [h_expand, h_sym_ue]
  have h_e_He : ∑ k, e k * (H e) k = (H e) i := by
    simp [he_def, Pi.single, Function.update, Finset.sum_ite_eq', Finset.mem_univ]
  rw [h_e_He]
  ring

/-- Symmetry transferred to the standard-basis matrix entries:
`(H eₖ)ᵢ = (H eᵢ)ₖ`. -/
lemma H_coord_symm
    (H : (ι → ℝ) →L[ℝ] (ι → ℝ))
    (hSymm : ∀ x y, ∑ k, x k * (H y) k = ∑ k, y k * (H x) k)
    (i k : ι) :
    (H (Pi.single (M := fun _ : ι => ℝ) k (1 : ℝ))) i =
      (H (Pi.single (M := fun _ : ι => ℝ) i (1 : ℝ))) k := by
  have h := hSymm (Pi.single (M := fun _ : ι => ℝ) i (1 : ℝ))
                  (Pi.single (M := fun _ : ι => ℝ) k (1 : ℝ))
  -- LHS of `h`: ∑ j, e_i j * (H e_k) j = (H e_k) i
  -- RHS of `h`: ∑ j, e_k j * (H e_i) j = (H e_i) k
  simpa [Pi.single, Function.update, Finset.sum_ite_eq', Finset.mem_univ] using h

end LinearAlgebraHelpers

section FullLineFTC

open MeasureTheory

/-- **1D full-line FTC**: if `f` is differentiable everywhere with derivative
`f'`, `f'` is integrable on `ℝ`, and `f` tends to `0` at both `±∞`, then
`∫ f' = 0`. Composes Mathlib's `integral_Ioi_of_hasDerivAt_of_tendsto'` and
`integral_Iic_of_hasDerivAt_of_tendsto'` via the half-line split.

Used in the IBP step to discard the boundary term after Fubini reduction
to a single coordinate. -/
lemma integral_full_line_deriv_eq_zero
    (f f' : ℝ → ℝ)
    (hf : ∀ x, HasDerivAt f (f' x) x)
    (hf'_int : Integrable f')
    (hf_top : Filter.Tendsto f Filter.atTop (nhds 0))
    (hf_bot : Filter.Tendsto f Filter.atBot (nhds 0)) :
    ∫ x : ℝ, f' x = 0 := by
  have hf'_Ioi : IntegrableOn f' (Set.Ioi (0 : ℝ)) := hf'_int.integrableOn
  have hf'_Iic : IntegrableOn f' (Set.Iic (0 : ℝ)) := hf'_int.integrableOn
  have h_Ioi : ∫ x in Set.Ioi (0 : ℝ), f' x = 0 - f 0 :=
    integral_Ioi_of_hasDerivAt_of_tendsto' (fun x _ => hf x) hf'_Ioi hf_top
  have h_Iic : ∫ x in Set.Iic (0 : ℝ), f' x = f 0 - 0 :=
    integral_Iic_of_hasDerivAt_of_tendsto' (fun x _ => hf x) hf'_Iic hf_bot
  have h_split : ∫ x : ℝ, f' x =
      (∫ x in Set.Iic (0 : ℝ), f' x) + (∫ x in Set.Ioi (0 : ℝ), f' x) := by
    rw [← intervalIntegral.integral_Iic_add_Ioi hf'_Iic hf'_Ioi]
  rw [h_split, h_Iic, h_Ioi]; ring

end FullLineFTC

end Laplace.Multi
