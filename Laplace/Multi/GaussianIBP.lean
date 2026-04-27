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

section DerivativeOfExpNegQ

/-- Derivative of `s ↦ quadForm H (u + s • eᵢ)` at `t`, assuming `H` symmetric,
equals `2 · (H (u + t • eᵢ))ᵢ`. -/
lemma hasDerivAt_quadForm_along_basis
    (H : (ι → ℝ) →L[ℝ] (ι → ℝ))
    (hSymm : ∀ x y, ∑ k, x k * (H y) k = ∑ k, y k * (H x) k)
    (u : ι → ℝ) (i : ι) (t : ℝ) :
    HasDerivAt
      (fun s : ℝ => quadForm H (u + s • (Pi.single (M := fun _ : ι => ℝ) i (1 : ℝ))))
      (2 * (H (u + t • (Pi.single (M := fun _ : ι => ℝ) i (1 : ℝ)))) i)
      t := by
  classical
  set e : ι → ℝ := Pi.single (M := fun _ : ι => ℝ) i (1 : ℝ) with he_def
  -- Polynomial form: quadForm H (u + s•e) = Q₀ + 2 s · A + s² · B
  set Q0 : ℝ := quadForm H u with hQ0
  set A : ℝ := (H u) i with hA
  set B : ℝ := (H e) i with hB
  have h_poly : ∀ s : ℝ,
      quadForm H (u + s • e) = Q0 + 2 * s * A + s ^ 2 * B := by
    intro s
    simpa [Q0, A, B, he_def] using
      quadForm_add_smul_stdBasis H hSymm i u s
  -- Derivative of `s ↦ Q₀ + 2 s A + s² B` at `t` is `2 A + 2 t B`.
  have h_at : HasDerivAt (fun s : ℝ => Q0 + 2 * s * A + s ^ 2 * B)
      (2 * A + 2 * t * B) t := by
    have h1 : HasDerivAt (fun s : ℝ => Q0) 0 t := hasDerivAt_const t Q0
    have h2 : HasDerivAt (fun s : ℝ => 2 * s * A) (2 * A) t := by
      have h := (hasDerivAt_id t).const_mul 2
      have h' := h.mul_const A
      simpa using h'
    have h3 : HasDerivAt (fun s : ℝ => s ^ 2 * B) (2 * t * B) t := by
      have h := (hasDerivAt_pow 2 t).mul_const B
      simpa [pow_one] using h
    have := (h1.add h2).add h3
    simpa using this
  -- Express the derivative in terms of (H (u + t•e)) i.
  have h_deriv_eq :
      2 * A + 2 * t * B = 2 * (H (u + t • e)) i := by
    have hH_lin : H (u + t • e) = H u + t • H e := by
      rw [map_add, ContinuousLinearMap.map_smul]
    have h_apply : (H (u + t • e)) i = (H u) i + t * (H e) i := by
      rw [hH_lin]
      simp [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    rw [h_apply]
    simp [A, B]
    ring
  -- Replace polynomial form with quadForm form via `congr` of HasDerivAt.
  have h_final : HasDerivAt (fun s : ℝ => quadForm H (u + s • e))
      (2 * A + 2 * t * B) t := by
    apply HasDerivAt.congr_of_eventuallyEq h_at
    apply Filter.Eventually.of_forall
    intro s
    exact h_poly s
  rw [h_deriv_eq] at h_final
  exact h_final

/-- Derivative of `s ↦ exp(-(1/2) · quadForm H (u + s • eᵢ))` at `t` equals
`-(H (u + t • eᵢ))ᵢ · exp(-(1/2) · quadForm H (u + t • eᵢ))`, assuming
`H` symmetric. -/
lemma hasDerivAt_exp_neg_half_quadForm_along_basis
    (H : (ι → ℝ) →L[ℝ] (ι → ℝ))
    (hSymm : ∀ x y, ∑ k, x k * (H y) k = ∑ k, y k * (H x) k)
    (u : ι → ℝ) (i : ι) (t : ℝ) :
    HasDerivAt
      (fun s : ℝ =>
        Real.exp (-(1/2) *
          quadForm H (u + s • (Pi.single (M := fun _ : ι => ℝ) i (1 : ℝ)))))
      (-((H (u + t • (Pi.single (M := fun _ : ι => ℝ) i (1 : ℝ)))) i) *
        Real.exp (-(1/2) *
          quadForm H (u + t • (Pi.single (M := fun _ : ι => ℝ) i (1 : ℝ)))))
      t := by
  set e : ι → ℝ := Pi.single (M := fun _ : ι => ℝ) i (1 : ℝ) with he_def
  -- Step 1: HasDerivAt of -(1/2) * quadForm H (u + s • e).
  have h_inner : HasDerivAt
      (fun s : ℝ => -(1/2) * quadForm H (u + s • e))
      (-((H (u + t • e)) i)) t := by
    have h := (hasDerivAt_quadForm_along_basis H hSymm u i t).const_mul (-(1/2))
    convert h using 1
    ring
  -- Step 2: chain with exp.
  have h_exp := h_inner.exp
  -- Reorder factors: `exp(...) * (-(H ...) i)` ↔ `(-(H ...) i) * exp(...)`.
  convert h_exp using 1
  ring

end DerivativeOfExpNegQ

section Definitions

open MeasureTheory

/-- The Gaussian weight `exp(-(1/2) · quadForm H u)`. -/
noncomputable def gaussianWeight
    (H : (ι → ℝ) →L[ℝ] (ι → ℝ)) (u : ι → ℝ) : ℝ :=
  Real.exp (-(1/2) * quadForm H u)

/-- The Gaussian normalising constant `Z := ∫ exp(-(1/2) quadForm H u) du`. -/
noncomputable def gaussianZ
    (H : (ι → ℝ) →L[ℝ] (ι → ℝ)) : ℝ :=
  ∫ u : ι → ℝ, gaussianWeight H u

/-- The `j`-th column of the Gaussian second-moment matrix:
`(momentColumn H j) k = ∫ uₖ uⱼ · exp(-(1/2) quadForm H u) du`. -/
noncomputable def momentColumn
    (H : (ι → ℝ) →L[ℝ] (ι → ℝ)) (j : ι) : ι → ℝ :=
  fun k => ∫ u : ι → ℝ, u k * u j * gaussianWeight H u

omit [DecidableEq ι] in
/-- Definitional unfolding for `gaussianWeight`. -/
lemma gaussianWeight_def (H : (ι → ℝ) →L[ℝ] (ι → ℝ)) (u : ι → ℝ) :
    gaussianWeight H u = Real.exp (-(1/2) * quadForm H u) := rfl

omit [DecidableEq ι] in
/-- The Gaussian weight is positive. -/
lemma gaussianWeight_pos (H : (ι → ℝ) →L[ℝ] (ι → ℝ)) (u : ι → ℝ) :
    0 < gaussianWeight H u := Real.exp_pos _

end Definitions

section SliceDerivative

open MeasureTheory

/-- The "slice integrand" for the IBP step: for fixed basepoint `u₀` and
coordinate `i, j`, this is the function

  `s ↦ (u₀ + s • eᵢ)_j · gaussianWeight H (u₀ + s • eᵢ)`

whose derivative we will integrate to zero (assuming Gaussian decay) to
extract the IBP identity. -/
noncomputable def sliceIntegrand
    (H : (ι → ℝ) →L[ℝ] (ι → ℝ)) (i j : ι) (u₀ : ι → ℝ) : ℝ → ℝ :=
  fun s => (u₀ + s • (Pi.single (M := fun _ : ι => ℝ) i (1 : ℝ))) j *
    gaussianWeight H (u₀ + s • (Pi.single (M := fun _ : ι => ℝ) i (1 : ℝ)))

/-- Slice derivative (product rule):

  `d/ds [(u₀ + s•eᵢ)_j · exp(-Q)] = δ_{ij} · exp(-Q)
       - (u₀ + s•eᵢ)_j · (H (u₀ + s•eᵢ))_i · exp(-Q)`.

This is the analytic identity that the IBP step exploits: integrating the
LHS over ℝ gives `0` (boundary terms vanish), so the integrals of the two
RHS terms are equal up to sign. -/
lemma hasDerivAt_sliceIntegrand
    (H : (ι → ℝ) →L[ℝ] (ι → ℝ))
    (hSymm : ∀ x y, ∑ k, x k * (H y) k = ∑ k, y k * (H x) k)
    (i j : ι) (u₀ : ι → ℝ) (t : ℝ) :
    HasDerivAt (sliceIntegrand H i j u₀)
      ((if i = j then 1 else 0) *
          gaussianWeight H (u₀ + t • (Pi.single (M := fun _ : ι => ℝ) i (1 : ℝ)))
        - (u₀ + t • (Pi.single (M := fun _ : ι => ℝ) i (1 : ℝ))) j *
          (H (u₀ + t • (Pi.single (M := fun _ : ι => ℝ) i (1 : ℝ)))) i *
          gaussianWeight H (u₀ + t • (Pi.single (M := fun _ : ι => ℝ) i (1 : ℝ))))
      t := by
  classical
  set e : ι → ℝ := Pi.single (M := fun _ : ι => ℝ) i (1 : ℝ) with he_def
  -- Slice u(s) := u₀ + s • e.
  -- Inner derivative of u(s) j: it's e_j = δ_{ij} as constant in s.
  have h_ej : e j = if i = j then (1 : ℝ) else 0 := by
    by_cases hij : i = j
    · subst hij; simp [he_def]
    · rw [if_neg hij, he_def]
      exact Pi.single_eq_of_ne (Ne.symm hij) 1
  have h_func_eq : (fun s : ℝ => (u₀ + s • e) j) = fun s => u₀ j + s * e j := by
    funext s; simp [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  have h_uj_deriv : HasDerivAt (fun s : ℝ => (u₀ + s • e) j)
      (if i = j then (1 : ℝ) else 0) t := by
    rw [h_func_eq, ← h_ej]
    have h := ((hasDerivAt_id t).mul_const (e j)).const_add (u₀ j)
    simpa using h
  -- Derivative of gaussianWeight along slice (Step 3).
  have h_gW_deriv : HasDerivAt
      (fun s : ℝ => gaussianWeight H (u₀ + s • e))
      (-((H (u₀ + t • e)) i) * gaussianWeight H (u₀ + t • e)) t := by
    unfold gaussianWeight
    exact hasDerivAt_exp_neg_half_quadForm_along_basis H hSymm u₀ i t
  -- Product rule.
  have h_prod := h_uj_deriv.mul h_gW_deriv
  -- Adjust the form.
  unfold sliceIntegrand
  convert h_prod using 1
  ring

/-- The derivative of the slice integrand, expressed as a function of `s`.

This is the function whose integral over `ℝ` will vanish (the IBP step).
It equals `∂_s sliceIntegrand = δ_{ij} · gW - u_j · (H u)_i · gW`,
where `u = u₀ + s • eᵢ`. -/
noncomputable def sliceDeriv
    (H : (ι → ℝ) →L[ℝ] (ι → ℝ)) (i j : ι) (u₀ : ι → ℝ) : ℝ → ℝ :=
  fun s =>
    (if i = j then (1 : ℝ) else 0) *
      gaussianWeight H (u₀ + s • (Pi.single (M := fun _ : ι => ℝ) i (1 : ℝ)))
    - (u₀ + s • (Pi.single (M := fun _ : ι => ℝ) i (1 : ℝ))) j *
      (H (u₀ + s • (Pi.single (M := fun _ : ι => ℝ) i (1 : ℝ)))) i *
      gaussianWeight H (u₀ + s • (Pi.single (M := fun _ : ι => ℝ) i (1 : ℝ)))

/-- The slice derivative is indeed the pointwise derivative of `sliceIntegrand`. -/
lemma hasDerivAt_sliceIntegrand_eq_sliceDeriv
    (H : (ι → ℝ) →L[ℝ] (ι → ℝ))
    (hSymm : ∀ x y, ∑ k, x k * (H y) k = ∑ k, y k * (H x) k)
    (i j : ι) (u₀ : ι → ℝ) (t : ℝ) :
    HasDerivAt (sliceIntegrand H i j u₀) (sliceDeriv H i j u₀ t) t := by
  unfold sliceDeriv
  exact hasDerivAt_sliceIntegrand H hSymm i j u₀ t

/-- **Slice IBP**: under decay-at-infinity and integrability hypotheses, the
slice derivative integrates to zero on ℝ. This is the 1D-FTC content of the
multivariate IBP step. -/
lemma integral_sliceDeriv_eq_zero
    (H : (ι → ℝ) →L[ℝ] (ι → ℝ))
    (hSymm : ∀ x y, ∑ k, x k * (H y) k = ∑ k, y k * (H x) k)
    (i j : ι) (u₀ : ι → ℝ)
    (h_deriv_int : Integrable (sliceDeriv H i j u₀))
    (h_top : Filter.Tendsto (sliceIntegrand H i j u₀) Filter.atTop (nhds 0))
    (h_bot : Filter.Tendsto (sliceIntegrand H i j u₀) Filter.atBot (nhds 0)) :
    ∫ s : ℝ, sliceDeriv H i j u₀ s = 0 :=
  integral_full_line_deriv_eq_zero
    (sliceIntegrand H i j u₀)
    (sliceDeriv H i j u₀)
    (fun t => hasDerivAt_sliceIntegrand_eq_sliceDeriv H hSymm i j u₀ t)
    h_deriv_int h_top h_bot

end SliceDerivative

end Laplace.Multi
