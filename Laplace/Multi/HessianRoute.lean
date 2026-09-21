/-
Copyright (c) 2026 Timaeus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Timaeus
-/
import Laplace.Multi.CovarianceSharp
import Laplace.Multi.CovarianceExplicit
import Laplace.Multi.GaussianWickPosDef
import Laplace.Multi.OneLoop
import Laplace.TwoD.ValleyQuadratic

/-!
# The Hessian route with only positive definiteness

The sanity note's Hessian-route equations `eq:cov`, `eq:llc`, `eq:mean`, `eq:covK` are tagged with
the seabed's `gibbsCov_first_order_rate_sharp`, `gibbsExpectation_first_order_rate_explicit` and
`gibbsCov_first_order_rate_explicit`, each of which carries a Gaussian hypothesis package on the
pair `(H, Hinv)`. Those packages hold for `H = matCLM P`, `Hinv = matCLM P⁻¹`, `P.PosDef`
(`GaussianWickPosDef.lean`), so the three theorems specialise to turnkey versions whose only
Gaussian input is positive definiteness (`…_posDef`).

Two consequences of the note:

* **`eq:llc`**: for the exact quadratic observable `K = ½ wᵀPw` (packaged as `quadObservable`),
  `2t⟨K⟩ → trASig (matCLM P) (matCLM P⁻¹) = card ι`, i.e. `t⟨K⟩ → d/2` with an `O(1/t)` rate for
  every regular potential (`llc_first_order_rate_posDef`);
* **`eq:mean`**: the first-order mean shift `−½ S (tT:S)` as a functional (`meanShift`) is exactly
  the Gibbs mean minus the minimiser on every quadratic valley
  (`gibbsMean_quadValley_eq_meanShift`).
-/

open Matrix

namespace Laplace.Multi

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-! ### Turnkey rate theorems -/

/-- **`eq:cov` with only positive definiteness**: `t Cov[φ, ψ] → aᵀ P⁻¹ b` at rate `O(1/t)`. -/
theorem gibbsCov_first_order_rate_sharp_posDef [Nonempty ι] (V φ ψ : (ι → ℝ) → ℝ)
    {P : Matrix ι ι ℝ} (hP : P.PosDef) (a b : ι → ℝ)
    (hV : PotentialJetApprox V (matCLM P)) (hφ : ObservableJetApprox φ a)
    (hψ : ObservableJetApprox ψ b) :
    ∃ K T₀ : ℝ, 1 ≤ T₀ ∧ ∀ t : ℝ, T₀ ≤ t →
      |t * gibbsCov V t φ ψ - dot a (matCLM P⁻¹ b)| ≤ K / t :=
  gibbsCov_first_order_rate_sharp V φ ψ (matCLM P) (matCLM P⁻¹) a b hV hφ hψ
    (laplaceCovHypotheses_matCLM hP)

/-- **`eq:llc`/`eq:mean` with only positive definiteness**: the explicit first-order expectation. -/
theorem gibbsExpectation_first_order_rate_explicit_posDef [Nonempty ι] (V φ : (ι → ℝ) → ℝ)
    {P : Matrix ι ι ℝ} (hP : P.PosDef) (a : ι → ℝ)
    (hV : PotentialQuinticApprox V (matCLM P)) (hφ : ObservableTensorApprox φ a) :
    ∃ K T₀ : ℝ, 1 ≤ T₀ ∧ ∀ t : ℝ, T₀ ≤ t →
      |2 * t * gibbsExpectation V t φ - trASig hφ.A (matCLM P⁻¹)
          + dot (matCLM P⁻¹ a) (tensorContractMatrix hV.T (matCLM P⁻¹))| ≤ K / t :=
  gibbsExpectation_first_order_rate_explicit V φ (matCLM P) (matCLM P⁻¹) a hV hφ
    (laplaceCov4MomentHypotheses_matCLM hP)

/-- **`eq:covK` with only positive definiteness**: the explicit second-order covariance. -/
theorem gibbsCov_first_order_rate_explicit_posDef [Nonempty ι] (V φ ψ : (ι → ℝ) → ℝ)
    {P : Matrix ι ι ℝ} (hP : P.PosDef) (a b : ι → ℝ)
    (hV : PotentialQuinticApprox V (matCLM P)) (hφ : ObservableQuinticApprox φ a)
    (hψ : ObservableTensorApprox ψ b) (h_phi_grad_zero : a = 0) :
    ∃ K T₀ : ℝ, 1 ≤ T₀ ∧ ∀ t : ℝ, T₀ ≤ t →
      |t ^ 2 * gibbsCov V t φ ψ -
          cov2Coefficient V φ ψ (matCLM P) (matCLM P⁻¹) a b
            hV.toPotentialTensorApprox hφ.toObservableTensorApprox hψ| ≤ K / t :=
  gibbsCov_first_order_rate_explicit V φ ψ (matCLM P) (matCLM P⁻¹) a b hV hφ hψ h_phi_grad_zero
    (laplaceCov6MomentHypotheses_matCLM hP)

/-! ### The exact quadratic observable -/

omit [DecidableEq ι] in
theorem abs_coord_le_norm (w : ι → ℝ) (i : ι) : |w i| ≤ ‖w‖ := by
  have := norm_le_pi_norm w i
  simpa [Real.norm_eq_abs] using this

/-- `|wᵀPw| ≤ (∑ᵢⱼ |Pᵢⱼ|) ‖w‖²` in the sup norm. -/
theorem abs_quadForm_matCLM_le (P : Matrix ι ι ℝ) (w : ι → ℝ) :
    |quadForm (matCLM P) w| ≤ (∑ i, ∑ j, |P i j|) * ‖w‖ ^ 2 := by
  have hq : quadForm (matCLM P) w = ∑ i, ∑ j, w i * (P i j * w j) := by
    simp only [quadForm, matCLM_apply, Matrix.mulVec, dotProduct, Finset.mul_sum]
  rw [hq]
  calc |∑ i, ∑ j, w i * (P i j * w j)| ≤ ∑ i, ∑ j, |w i * (P i j * w j)| :=
        (Finset.abs_sum_le_sum_abs _ _).trans
          (Finset.sum_le_sum fun i _ => Finset.abs_sum_le_sum_abs _ _)
    _ ≤ ∑ i, ∑ j, |P i j| * ‖w‖ ^ 2 := by
        refine Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j _ => ?_
        rw [abs_mul, abs_mul, sq]
        calc |w i| * (|P i j| * |w j|) = |P i j| * (|w i| * |w j|) := by ring
          _ ≤ |P i j| * (‖w‖ * ‖w‖) := by
              gcongr
              · exact abs_coord_le_norm w i
              · exact abs_coord_le_norm w j
    _ = (∑ i, ∑ j, |P i j|) * ‖w‖ ^ 2 := by
        rw [Finset.sum_mul]
        simp_rw [Finset.sum_mul]

/-- The exact quadratic `K = ½ wᵀPw` as an observable with gradient `0`, Hessian `P`, no cubic
tensor and no remainders. -/
noncomputable def quadObservable (P : Matrix ι ι ℝ) (hP : P.PosDef) :
    ObservableTensorApprox (fun w : ι → ℝ => (1 / 2 : ℝ) * quadForm (matCLM P) w) 0 where
  phi_continuous := (continuous_quadForm (matCLM P)).const_smul (1 / 2 : ℝ)
  phi_zero := by simp [quadForm]
  local_radius := 1
  local_const := (1 / 2) * ∑ i, ∑ j, |P i j|
  local_radius_pos := one_pos
  local_const_nonneg := by positivity
  local_bound := fun w _ => by
    have h := abs_quadForm_matCLM_le P w
    simp only [dot, Pi.zero_apply, zero_mul, Finset.sum_const_zero, sub_zero, abs_mul,
      abs_of_pos (by norm_num : (0 : ℝ) < 1 / 2)]
    nlinarith [h]
  poly_growth := ⟨(1 / 2) * ∑ i, ∑ j, |P i j|, 2, by positivity, fun w => by
    have h := abs_quadForm_matCLM_le P w
    have h0 : 0 ≤ ∑ i, ∑ j, |P i j| := by positivity
    rw [abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 1 / 2)]
    nlinarith [h, h0]⟩
  qφ := fun w => (1 / 2 : ℝ) * quadForm (matCLM P) w
  qφ_continuous := (continuous_quadForm (matCLM P)).const_smul (1 / 2 : ℝ)
  qφ_even := fun w => by simp [quadForm_neg]
  qφ_bound_const := (1 / 2) * ∑ i, ∑ j, |P i j|
  qφ_bound_const_nonneg := by positivity
  qφ_bound := fun w => by
    have h := abs_quadForm_matCLM_le P w
    rw [abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 1 / 2)]
    nlinarith [h]
  jet_radius := 1
  jet_const := 0
  jet_radius_pos := one_pos
  jet_const_nonneg := le_rfl
  jet_bound := fun w _ => by simp [dot]
  A := matCLM P
  A_symm := fun u v => quadForm_symm_matCLM hP u v
  qφ_eq_A_diag := fun _ => rfl
  Φ := 0
  Φ_symm := fun _ _ => by simp
  Φ_jet_bound := fun w _ => by simp [dot]

theorem quadObservable_A (P : Matrix ι ι ℝ) (hP : P.PosDef) : (quadObservable P hP).A = matCLM P :=
  rfl

/-- `trASig (matCLM P) (matCLM P⁻¹) = tr(P P⁻¹) = d`. -/
theorem trASig_matCLM_inv {P : Matrix ι ι ℝ} (hP : P.PosDef) :
    trASig (matCLM P) (matCLM P⁻¹) = Fintype.card ι := by
  unfold trASig
  have hPP : P * P⁻¹ = 1 := Matrix.mul_nonsing_inv P (isUnit_iff_ne_zero.mpr hP.det_pos.ne')
  simp only [matCLM_apply, Matrix.mulVec_mulVec, hPP, Matrix.one_mulVec, Pi.single_eq_same,
    Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_one]

/-- **`eq:llc` for every regular potential**: `2t⟨½wᵀPw⟩ → d` at rate `O(1/t)`, i.e. the LLC
estimate `t⟨K⟩` tends to `d/2`. -/
theorem llc_first_order_rate_posDef [Nonempty ι] (V : (ι → ℝ) → ℝ) {P : Matrix ι ι ℝ}
    (hP : P.PosDef) (hV : PotentialQuinticApprox V (matCLM P)) :
    ∃ K T₀ : ℝ, 1 ≤ T₀ ∧ ∀ t : ℝ, T₀ ≤ t →
      |2 * t * gibbsExpectation V t (fun w => (1 / 2 : ℝ) * quadForm (matCLM P) w) -
        Fintype.card ι| ≤ K / t := by
  obtain ⟨K, T₀, hT, h⟩ := gibbsExpectation_first_order_rate_explicit_posDef V _ hP 0 hV
    (quadObservable P hP)
  refine ⟨K, T₀, hT, fun t ht => ?_⟩
  have := h t ht
  rw [quadObservable_A, trASig_matCLM_inv hP, map_zero] at this
  simpa [dot] using this

/-! ### The loss itself as an observable -/

/-- The potential `V` as an observable with gradient `0`, Hessian `P` and cubic tensor `T`. -/
noncomputable def potentialObservable {V : (ι → ℝ) → ℝ} {P : Matrix ι ι ℝ} (hP : P.PosDef)
    (hV : PotentialTensorApprox V (matCLM P)) : ObservableTensorApprox V 0 where
  phi_continuous := hV.V_continuous
  phi_zero := hV.V_zero
  local_radius := hV.local_radius
  local_const := (1 / 2) * ∑ i, ∑ j, |P i j| + hV.local_const * hV.local_radius
  local_radius_pos := hV.local_radius_pos
  local_const_nonneg := by
    have := hV.local_const_nonneg
    have := hV.local_radius_pos
    positivity
  local_bound := fun w hw => by
    have h1 := hV.local_bound w hw
    have h2 := abs_quadForm_matCLM_le P w
    have hR : ‖w‖ ^ 3 ≤ hV.local_radius * ‖w‖ ^ 2 := by
      rw [show ‖w‖ ^ 3 = ‖w‖ * ‖w‖ ^ 2 by ring]
      exact mul_le_mul_of_nonneg_right hw (by positivity)
    simp only [dot, Pi.zero_apply, zero_mul, Finset.sum_const_zero, sub_zero]
    calc |V w| = |(V w - (1 / 2) * quadForm (matCLM P) w) + (1 / 2) * quadForm (matCLM P) w| := by
          ring_nf
      _ ≤ |V w - (1 / 2) * quadForm (matCLM P) w| + |(1 / 2) * quadForm (matCLM P) w| :=
          abs_add_le _ _
      _ ≤ hV.local_const * ‖w‖ ^ 3 + (1 / 2) * ((∑ i, ∑ j, |P i j|) * ‖w‖ ^ 2) := by
          refine add_le_add h1 ?_
          rw [abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 1 / 2)]
          exact mul_le_mul_of_nonneg_left h2 (by norm_num)
      _ ≤ hV.local_const * (hV.local_radius * ‖w‖ ^ 2) +
            (1 / 2) * ((∑ i, ∑ j, |P i j|) * ‖w‖ ^ 2) :=
          add_le_add (mul_le_mul_of_nonneg_left hR hV.local_const_nonneg) le_rfl
      _ = ((1 / 2) * ∑ i, ∑ j, |P i j| + hV.local_const * hV.local_radius) * ‖w‖ ^ 2 := by ring
  poly_growth := hV.poly_growth
  qφ := fun w => (1 / 2 : ℝ) * quadForm (matCLM P) w
  qφ_continuous := (continuous_quadForm (matCLM P)).const_smul (1 / 2 : ℝ)
  qφ_even := fun w => by simp [quadForm_neg]
  qφ_bound_const := (1 / 2) * ∑ i, ∑ j, |P i j|
  qφ_bound_const_nonneg := by positivity
  qφ_bound := fun w => by
    have h := abs_quadForm_matCLM_le P w
    rw [abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 1 / 2)]
    nlinarith [h]
  jet_radius := min hV.local_radius hV.jet_radius
  jet_const := max hV.local_const hV.jet_const
  jet_radius_pos := lt_min hV.local_radius_pos hV.jet_radius_pos
  jet_const_nonneg := le_max_of_le_left hV.local_const_nonneg
  jet_bound := fun w hw => by
    have h1 := hV.local_bound w (hw.trans (min_le_left _ _))
    simp only [dot, Pi.zero_apply, zero_mul, Finset.sum_const_zero, zero_add]
    exact h1.trans (mul_le_mul_of_nonneg_right (le_max_left _ _) (by positivity))
  A := matCLM P
  A_symm := fun u v => quadForm_symm_matCLM hP u v
  qφ_eq_A_diag := fun _ => rfl
  Φ := hV.T
  Φ_symm := hV.T_symm
  Φ_jet_bound := fun w hw => by
    have h1 := hV.T_jet_bound w (hw.trans (min_le_right _ _))
    simp only [dot, Pi.zero_apply, zero_mul, Finset.sum_const_zero, zero_add]
    exact h1.trans (mul_le_mul_of_nonneg_right (le_max_right _ _) (by positivity))

/-- **`eq:llc` for the loss itself**: `2t⟨V⟩_{V,t} → d`, i.e. the LLC estimate `t⟨L⟩ → d/2` for
every regular potential, at rate `O(1/t)`. -/
theorem llc_potential_first_order_rate_posDef [Nonempty ι] (V : (ι → ℝ) → ℝ) {P : Matrix ι ι ℝ}
    (hP : P.PosDef) (hV : PotentialQuinticApprox V (matCLM P)) :
    ∃ K T₀ : ℝ, 1 ≤ T₀ ∧ ∀ t : ℝ, T₀ ≤ t →
      |2 * t * gibbsExpectation V t V - Fintype.card ι| ≤ K / t := by
  obtain ⟨K, T₀, hT, h⟩ := gibbsExpectation_first_order_rate_explicit_posDef V V hP 0 hV
    (potentialObservable hP hV.toPotentialTensorApprox)
  refine ⟨K, T₀, hT, fun t ht => ?_⟩
  have := h t ht
  rw [show (potentialObservable hP hV.toPotentialTensorApprox).A = matCLM P from rfl,
    trASig_matCLM_inv hP, map_zero] at this
  simpa [dot] using this

/-- The exact quadratic observable also satisfies the quintic (odd-part) package trivially. -/
noncomputable def quadObservableQuintic (P : Matrix ι ι ℝ) (hP : P.PosDef) :
    ObservableQuinticApprox (fun w : ι → ℝ => (1 / 2 : ℝ) * quadForm (matCLM P) w) 0 where
  toObservableTensorApprox := quadObservable P hP
  Q_const := 0
  Q_const_nn := le_rfl
  φ_odd_quintic_bound := fun w _ => by simp [quadForm_neg, dot, quadObservable]

/-- **`eq:covK` with only positive definiteness**, for the quadratic observable `K = ½wᵀPw`. -/
theorem covK_first_order_rate_posDef [Nonempty ι] (V ψ : (ι → ℝ) → ℝ) {P : Matrix ι ι ℝ}
    (hP : P.PosDef) (b : ι → ℝ) (hV : PotentialQuinticApprox V (matCLM P))
    (hψ : ObservableTensorApprox ψ b) :
    ∃ K T₀ : ℝ, 1 ≤ T₀ ∧ ∀ t : ℝ, T₀ ≤ t →
      |t ^ 2 * gibbsCov V t (fun w => (1 / 2 : ℝ) * quadForm (matCLM P) w) ψ -
          cov2Coefficient V (fun w => (1 / 2 : ℝ) * quadForm (matCLM P) w) ψ (matCLM P) (matCLM P⁻¹)
            0 b hV.toPotentialTensorApprox (quadObservable P hP) hψ| ≤ K / t :=
  gibbsCov_first_order_rate_explicit_posDef V _ ψ hP 0 b hV (quadObservableQuintic P hP) hψ rfl

end Laplace.Multi

/-! ### `eq:mean`: the first-order mean shift, exact on quadratic valleys -/

namespace Laplace.Multi

/-- The note's first-order mean shift `−½ S (tT:S)`, `S = (tH)⁻¹`. -/
noncomputable def meanShift {d : ℕ} (t : ℝ) (H : Matrix (Fin d) (Fin d) ℝ)
    (T : Fin d → Fin d → Fin d → ℝ) : Fin d → ℝ :=
  (-(1 / 2 : ℝ)) • ((t • H)⁻¹ *ᵥ (t • contractT T (t • H)⁻¹))

end Laplace.Multi

namespace Laplace.TwoD

open Laplace.Multi

variable {μ b c e a t : ℝ}

/-- On the quadratic valley the first-order mean shift is `(0, b/t)`. -/
theorem meanShift_quadValley (ha : 0 < a) (ht : 0 < t) :
    meanShift t (quadValleyHess μ b c a) (quadValleyT μ b c a) = ![0, b / t] := by
  unfold meanShift
  rw [quadValleyHess_smul_inv ha ht, contractT_quadValley ha.ne']
  ext i
  fin_cases i <;> simp [quadValleySigma] <;> field_simp <;> ring

/-- **`eq:mean` is exact on quadratic valleys**: the Gibbs mean of `(x, y)` minus the minimiser
`(μ, g(μ))` equals the first-order shift `−½ S (tT:S)` at every `t`. -/
theorem gibbsMean_quadValley_eq_meanShift (ha : 0 < a) (ht : 0 < t) :
    ![gibbsExpectation (valley μ (quadFn b c e) a) t (fun q => q.1),
      gibbsExpectation (valley μ (quadFn b c e) a) t (fun q => q.2)] - ![μ, quadFn b c e μ] =
      meanShift t (quadValleyHess μ b c a) (quadValleyT μ b c a) := by
  rw [meanShift_quadValley ha ht, gibbsExpectation_quadValley_fst ha ht,
    gibbsExpectation_quadValley_snd ha ht]
  ext i
  fin_cases i <;> simp

end Laplace.TwoD
