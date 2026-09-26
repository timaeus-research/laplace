/-
Copyright (c) 2026 Timaeus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Timaeus
-/
import Laplace.Multi.BasepointCurvature

/-!
# The response-information lower bound

The rate `𝓘_ν(M)` measures the information a data law must carry to move the responses from the
featureless response `m₀ = E_ν S` to `M`. A uniform bound on the fluctuations of the visible
statistics turns this into a quadratic lower bound: if `‖S − m₀‖ ≤ B` almost surely, then

  `𝓘_ν(M) ≥ ‖M − m₀‖² / (2 B²)`   for every response `M`   (`genRate_ge_quadratic`).

The proof integrates the covariance bound twice along the ray `s ↦ s q` in the cumulant generating
function (`featCgf_le_quadratic`: `Λ(q) ≤ ⟨q, m₀⟩ + K/2` when `Var_{ν_{sq}}⟨q, S⟩ ≤ K` on
`[0, 1]`),
and evaluates the Chernoff supremum at `q = (M − m₀)/B²`. The variance bound under every tilt
comes
from Cauchy–Schwarz (`lawCov_dirLoss_le_of_bdd`): `Var_ρ⟨q, S⟩ ≤ E_ρ⟨q, S − m₀⟩² ≤ B² ‖q‖²` for
every law `ρ ≪ ν`. No tail or Chernoff theorem is used.
-/

open MeasureTheory Filter Topology Set
open scoped ENNReal

namespace Laplace.Multi

section Scalar

variable {X : Type*} [MeasurableSpace X] [Nonempty X] (ν : Measure X) [IsProbabilityMeasure ν]

/-- The log-partition function along a ray has derivative the tilted mean. -/
theorem hasDerivAt_log_integral_exp {f : X → ℝ} (hf : Bdd f) (s₀ : ℝ) :
    HasDerivAt (fun s ↦ Real.log (∫ x, Real.exp (s * f x) ∂ν))
      (∫ x, f x ∂ν.tilted (fun x ↦ s₀ * f x)) s₀ := by
  have hpos : 0 < ∫ x, Real.exp (s₀ * f x) ∂ν :=
    integral_exp_pos (integrable_exp_of_bdd ν (Bdd.const_mul s₀ hf))
  have h := (hasDerivAt_integral_exp_mul ν hf s₀).log hpos.ne'
  rw [integral_tilted_eq_div]
  exact h

/-- **The second-order bound on the cumulant generating function along a ray**: if the tilted
variance of `f` is at most `K` on `[0, 1]`, then `log E_ν e^f ≤ E_ν f + K / 2`. -/
theorem log_integral_exp_le_of_var_le {f : X → ℝ} (hf : Bdd f) {K : ℝ}
    (hK : ∀ s ∈ Icc (0 : ℝ) 1, lawCov (ν.tilted (fun x ↦ s * f x)) f f ≤ K) :
    Real.log (∫ x, Real.exp (f x) ∂ν) ≤ (∫ x, f x ∂ν) + K / 2 := by
  -- the mean along the ray
  have hm : ∀ s, HasDerivAt (fun s ↦ ∫ x, f x ∂ν.tilted (fun x ↦ s * f x))
      (lawCov (ν.tilted (fun x ↦ s * f x)) f f) s := fun s ↦ hasDerivAt_integral_tilted ν hf hf s
  have hφ : ∀ s, HasDerivAt (fun s ↦ Real.log (∫ x, Real.exp (s * f x) ∂ν))
      (∫ x, f x ∂ν.tilted (fun x ↦ s * f x)) s := fun s ↦ hasDerivAt_log_integral_exp ν hf s
  have h0 : ν.tilted (fun x ↦ (0 : ℝ) * f x) = ν := tilted_zero_mul ν f
  -- first integration: the tilted mean grows at most linearly
  have hd₁ : ∀ s, HasDerivAt (fun s ↦ (∫ x, f x ∂ν.tilted (fun x ↦ s * f x)) - K * s)
      (lawCov (ν.tilted (fun x ↦ s * f x)) f f - K * 1) s :=
    fun s ↦ (hm s).sub ((hasDerivAt_id s).const_mul K)
  have hψ₁ : AntitoneOn (fun s ↦ (∫ x, f x ∂ν.tilted (fun x ↦ s * f x)) - K * s) (Icc 0 1) := by
    refine antitoneOn_of_deriv_nonpos (convex_Icc 0 1) ?_ ?_ ?_
    · exact fun s _ ↦ (hd₁ s).continuousAt.continuousWithinAt
    · exact fun s _ ↦ (hd₁ s).differentiableAt.differentiableWithinAt
    · intro s hs
      rw [interior_Icc] at hs
      rw [(hd₁ s).deriv]
      have := hK s ⟨hs.1.le, hs.2.le⟩
      linarith
  have hlin : ∀ s ∈ Icc (0 : ℝ) 1,
      ∫ x, f x ∂ν.tilted (fun x ↦ s * f x) ≤ (∫ x, f x ∂ν) + K * s := by
    intro s hs
    have := hψ₁ ⟨le_rfl, zero_le_one⟩ hs hs.1
    simp only [h0, mul_zero, sub_zero] at this
    linarith
  -- second integration: the log-partition function is at most its quadratic majorant
  have hψ₂ : AntitoneOn (fun s ↦ Real.log (∫ x, Real.exp (s * f x) ∂ν) -
      (∫ x, f x ∂ν) * s - K * s ^ 2 / 2) (Icc 0 1) := by
    have hd : ∀ s, HasDerivAt (fun s ↦ Real.log (∫ x, Real.exp (s * f x) ∂ν) -
        (∫ x, f x ∂ν) * s - K * s ^ 2 / 2)
        ((∫ x, f x ∂ν.tilted (fun x ↦ s * f x)) - (∫ x, f x ∂ν) - K * s) s := by
      intro s
      have h1 := ((hφ s).sub ((hasDerivAt_id s).const_mul (∫ x, f x ∂ν))).sub
        (((hasDerivAt_pow 2 s).const_mul K).div_const 2)
      refine h1.congr_deriv ?_
      simp only [mul_one]
      ring
    refine antitoneOn_of_deriv_nonpos (convex_Icc 0 1) ?_ ?_ ?_
    · exact fun s _ ↦ (hd s).continuousAt.continuousWithinAt
    · exact fun s _ ↦ (hd s).differentiableAt.differentiableWithinAt
    · intro s hs
      rw [interior_Icc] at hs
      rw [(hd s).deriv]
      have := hlin s ⟨hs.1.le, hs.2.le⟩
      linarith
  have := hψ₂ ⟨le_rfl, zero_le_one⟩ ⟨zero_le_one, le_rfl⟩ zero_le_one
  simp only [zero_mul, Real.exp_zero, integral_const, measureReal_def, measure_univ,
    ENNReal.toReal_one, smul_eq_mul, one_mul, Real.log_one, mul_zero, sub_zero, zero_pow,
    ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_div, one_pow, mul_one] at this
  linarith

omit [Nonempty X] in
/-- The variance is at most the second moment about any centre. -/
theorem lawCov_self_le_integral_sq (ρ : Measure X) [IsProbabilityMeasure ρ] {g : X → ℝ}
    (hg : Bdd g) (c : ℝ) : lawCov ρ g g ≤ ∫ x, (g x - c) * (g x - c) ∂ρ := by
  have hi := integrable_of_bdd_prob ρ hg
  have hi2 := integrable_of_bdd_prob ρ (hg.mul hg)
  have e : ∀ x, (g x - c) * (g x - c) = g x * g x - (2 * c) * g x + c ^ 2 := fun x ↦ by ring
  simp_rw [e]
  have hA : Integrable (fun x ↦ g x * g x - (2 * c) * g x) ρ := hi2.sub (hi.const_mul _)
  rw [integral_add hA (integrable_const _), integral_sub hi2 (hi.const_mul _), integral_const_mul,
    integral_const]
  simp only [measureReal_def, measure_univ, ENNReal.toReal_one, smul_eq_mul, one_mul, lawCov]
  nlinarith [sq_nonneg ((∫ x, g x ∂ρ) - c)]

end Scalar

section Bound

variable {X : Type*} [MeasurableSpace X] [Nonempty X] {J : Type*} [Fintype J]
  {S : J → X → ℝ} (hS : ∀ j, Bdd (S j)) (ν : Measure X) [IsProbabilityMeasure ν]
include hS

omit [Nonempty X] [IsProbabilityMeasure ν] in
/-- **Cauchy–Schwarz for the tilted variance of a visible contrast**: if `‖S − m₀‖ ≤ B` a.s.
under `ν`, then `Var_ρ⟨q, S⟩ ≤ B² ‖q‖²` for every law `ρ ≪ ν`. -/
theorem lawCov_dirLoss_le_of_bdd {m₀ : J → ℝ} {B : ℝ}
    (hB : ∀ᵐ x ∂ν, dotJ (statPoint S x - m₀) (statPoint S x - m₀) ≤ B ^ 2)
    (ρ : Measure X) [IsProbabilityMeasure ρ] (hρ : ρ ≪ ν) (q : J → ℝ) :
    lawCov ρ (dirLoss S q) (dirLoss S q) ≤ B ^ 2 * dotJ q q := by
  refine (lawCov_self_le_integral_sq ρ (bdd_dirLoss hS q) (dotJ q m₀)).trans ?_
  have hbdd : Bdd fun x ↦ (dirLoss S q x - dotJ q m₀) * (dirLoss S q x - dotJ q m₀) :=
    ((bdd_dirLoss hS q).sub (Bdd.const (dotJ q m₀))).mul
      ((bdd_dirLoss hS q).sub (Bdd.const (dotJ q m₀)))
  calc ∫ x, (dirLoss S q x - dotJ q m₀) * (dirLoss S q x - dotJ q m₀) ∂ρ
      ≤ ∫ _, B ^ 2 * dotJ q q ∂ρ := by
        refine integral_mono_ae (integrable_of_bdd_prob ρ hbdd) (integrable_const _) ?_
        filter_upwards [hρ.ae_le hB] with x hx
        have e : dirLoss S q x - dotJ q m₀ = dotJ q (statPoint S x - m₀) := by
          simp only [dirLoss, dotJ, statPoint, Pi.sub_apply, mul_sub, Finset.sum_sub_distrib]
        rw [e]
        have hcs := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ q (statPoint S x - m₀)
        have e1 : dotJ q (statPoint S x - m₀) = ∑ i, q i * (statPoint S x - m₀) i := rfl
        have e2 : dotJ q q = ∑ i, q i ^ 2 := Finset.sum_congr rfl fun i _ ↦ (sq _).symm
        have e3 : dotJ (statPoint S x - m₀) (statPoint S x - m₀) =
            ∑ i, (statPoint S x - m₀) i ^ 2 := Finset.sum_congr rfl fun i _ ↦ (sq _).symm
        rw [e1, e2, mul_comm, ← sq]
        refine hcs.trans ?_
        rw [← e3, mul_comm (B ^ 2)]
        exact mul_le_mul_of_nonneg_left hx (Finset.sum_nonneg fun i _ ↦ sq_nonneg (q i))
    _ = B ^ 2 * dotJ q q := by
        rw [integral_const]
        simp [measureReal_def]

/-- **The cumulant generating function is at most its quadratic majorant**:
`Λ_ν(q) ≤ ⟨q, m₀⟩ + B² ‖q‖² / 2` when `‖S − m₀‖ ≤ B` a.s. and `m₀ = E_ν S`. -/
theorem featCgf_le_quadratic {B : ℝ}
    (hB : ∀ᵐ x ∂ν, dotJ (statPoint S x - fun i ↦ ∫ x, S i x ∂ν)
      (statPoint S x - fun i ↦ ∫ x, S i x ∂ν) ≤ B ^ 2) (q : J → ℝ) :
    featCgf ν S q ≤ dotJ q (fun i ↦ ∫ x, S i x ∂ν) + B ^ 2 * dotJ q q / 2 := by
  have h := log_integral_exp_le_of_var_le ν (bdd_dirLoss hS q) (K := B ^ 2 * dotJ q q)
    fun s _ ↦ by
      have := isProbabilityMeasure_tilted
        (integrable_exp_of_bdd ν (Bdd.const_mul s (bdd_dirLoss hS q)))
      exact lawCov_dirLoss_le_of_bdd hS ν hB (ν.tilted fun x ↦ s * dirLoss S q x)
        (tilted_absolutelyContinuous ν _) q
  unfold featCgf
  rw [dotJ_integral_eq ν hS q]
  exact h

/-- **The response-information lower bound**: if `‖S − m₀‖ ≤ B` a.s., then
`𝓘_ν(M) ≥ ‖M − m₀‖² / (2 B²)` for every response `M`. -/
theorem genRate_ge_quadratic {B : ℝ} (hB0 : 0 < B)
    (hB : ∀ᵐ x ∂ν, dotJ (statPoint S x - fun i ↦ ∫ x, S i x ∂ν)
      (statPoint S x - fun i ↦ ∫ x, S i x ∂ν) ≤ B ^ 2) (M : J → ℝ) :
    ENNReal.ofReal (dotJ (M - fun i ↦ ∫ x, S i x ∂ν) (M - fun i ↦ ∫ x, S i x ∂ν) / (2 * B ^ 2)) ≤
      genRate ν S M := by
  obtain ⟨v, hv⟩ : ∃ v : J → ℝ, v = M - fun i ↦ ∫ x, S i x ∂ν := ⟨_, rfl⟩
  rw [← hv]
  refine le_iSup_of_le ((B ^ 2)⁻¹ • v) (ENNReal.ofReal_le_ofReal ?_)
  have h := featCgf_le_quadratic hS ν hB ((B ^ 2)⁻¹ • v)
  have hB2 : (0 : ℝ) < B ^ 2 := by positivity
  have e1 : dotJ ((B ^ 2)⁻¹ • v) M - dotJ ((B ^ 2)⁻¹ • v) (fun i ↦ ∫ x, S i x ∂ν) =
      (B ^ 2)⁻¹ * dotJ v v := by
    rw [dotJ_smul_left, dotJ_smul_left, ← mul_sub, ← (isLinearMap_dotJ v).map_sub, ← hv]
  have e2 : dotJ ((B ^ 2)⁻¹ • v) ((B ^ 2)⁻¹ • v) = (B ^ 2)⁻¹ * ((B ^ 2)⁻¹ * dotJ v v) := by
    rw [dotJ_smul_left, dotJ_comm, dotJ_smul_left, dotJ_comm]
  have hvv : 0 ≤ dotJ v v := Finset.sum_nonneg fun i _ ↦ mul_self_nonneg _
  rw [e2] at h
  have key : dotJ v v / (2 * B ^ 2) ≤ dotJ ((B ^ 2)⁻¹ • v) M - featCgf ν S ((B ^ 2)⁻¹ • v) := by
    have : dotJ ((B ^ 2)⁻¹ • v) M - featCgf ν S ((B ^ 2)⁻¹ • v) ≥
        dotJ ((B ^ 2)⁻¹ • v) M - (dotJ ((B ^ 2)⁻¹ • v) (fun i ↦ ∫ x, S i x ∂ν) +
          B ^ 2 * ((B ^ 2)⁻¹ * ((B ^ 2)⁻¹ * dotJ v v)) / 2) := by linarith
    have e3 : dotJ ((B ^ 2)⁻¹ • v) M - (dotJ ((B ^ 2)⁻¹ • v) (fun i ↦ ∫ x, S i x ∂ν) +
        B ^ 2 * ((B ^ 2)⁻¹ * ((B ^ 2)⁻¹ * dotJ v v)) / 2) = dotJ v v / (2 * B ^ 2) := by
      have e4 := e1
      rw [sub_eq_iff_eq_add] at e4
      rw [e4]
      field_simp
      ring
    linarith
  exact key

end Bound

end Laplace.Multi
