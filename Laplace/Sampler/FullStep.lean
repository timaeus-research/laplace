/-
Copyright (c) 2026 Timaeus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniel Murfet
-/
import Mathlib.Analysis.Matrix.Normed
import Mathlib.Topology.MetricSpace.Contracting
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Laplace.Sampler.GaussianInvariance

/-!
# The state-dependent minibatch covariance law as an affine contraction

Minibatch SGLD on a Gaussian target with per-sample Hessians `H_i` has gradient noise whose
covariance depends on the state; the note *Sanity on Sampling* (E8) writes the stationary
covariance as the solution of the *full law*
`Σ = A Σ Aᵀ + N + c ∑ᵢ Dᵢ Σ Dᵢᵀ` (`Dᵢ = Hᵢ - H`) and solves it by iteration. This file treats the
full law as an affine map `fullStep` on matrices with linear part `fullLinear`. In the
`ℓ∞`-operator norm the linear part is Lipschitz with constant
`‖A‖ ‖Aᵀ‖ + c ∑ᵢ ‖Dᵢ‖ ‖Dᵢᵀ‖`; when this is `< 1` the full law has a unique solution, the iteration
converges to it from every start, the solution is positive semidefinite, and it dominates the
solution of the additive law `covStep A N` by at least the first-order inflation `c ∑ᵢ Dᵢ S Dᵢᵀ`.
-/

open Matrix Filter Topology
open scoped Matrix.Norms.Operator

namespace Laplace.Sampler

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {n : ℕ}

/-- The state-dependent noise term `∑ᵢ Dᵢ X Dᵢᵀ`. -/
def stateTerm (D : Fin n → Matrix ι ι ℝ) (X : Matrix ι ι ℝ) : Matrix ι ι ℝ :=
  ∑ i, D i * X * (D i)ᵀ

/-- The linear part of the full law. -/
def fullLinear (A : Matrix ι ι ℝ) (D : Fin n → Matrix ι ι ℝ) (c : ℝ) (X : Matrix ι ι ℝ) :
    Matrix ι ι ℝ :=
  A * X * Aᵀ + c • stateTerm D X

/-- The full state-dependent covariance step `X ↦ A X Aᵀ + N + c ∑ᵢ Dᵢ X Dᵢᵀ`. -/
def fullStep (A N : Matrix ι ι ℝ) (D : Fin n → Matrix ι ι ℝ) (c : ℝ) (X : Matrix ι ι ℝ) :
    Matrix ι ι ℝ :=
  fullLinear A D c X + N

omit [DecidableEq ι] in
theorem stateTerm_sub (D : Fin n → Matrix ι ι ℝ) (X Y : Matrix ι ι ℝ) :
    stateTerm D X - stateTerm D Y = stateTerm D (X - Y) := by
  simp only [stateTerm, Matrix.mul_sub, Matrix.sub_mul, Finset.sum_sub_distrib]

omit [DecidableEq ι] in
theorem fullLinear_sub (A : Matrix ι ι ℝ) (D : Fin n → Matrix ι ι ℝ) (c : ℝ) (X Y : Matrix ι ι ℝ) :
    fullLinear A D c X - fullLinear A D c Y = fullLinear A D c (X - Y) := by
  simp only [fullLinear, ← stateTerm_sub, Matrix.mul_sub, Matrix.sub_mul, smul_sub]
  abel

omit [DecidableEq ι] in
theorem fullStep_sub (A N : Matrix ι ι ℝ) (D : Fin n → Matrix ι ι ℝ) (c : ℝ) (X Y : Matrix ι ι ℝ) :
    fullStep A N D c X - fullStep A N D c Y = fullLinear A D c (X - Y) := by
  simp only [fullStep, add_sub_add_right_eq_sub, fullLinear_sub]

omit [DecidableEq ι] in
theorem fullStep_sub_covStep (A N : Matrix ι ι ℝ) (D : Fin n → Matrix ι ι ℝ) (c : ℝ)
    (X : Matrix ι ι ℝ) : fullStep A N D c X - covStep A N X = c • stateTerm D X := by
  simp only [fullStep, fullLinear, covStep]
  abel

/-! ### The contraction -/

/-- The Lipschitz constant of the linear part in the `ℓ∞`-operator norm. -/
noncomputable def fullLipschitz (A : Matrix ι ι ℝ) (D : Fin n → Matrix ι ι ℝ) (c : ℝ) : ℝ :=
  ‖A‖ * ‖Aᵀ‖ + c * ∑ i, ‖D i‖ * ‖(D i)ᵀ‖

theorem fullLipschitz_nonneg (A : Matrix ι ι ℝ) (D : Fin n → Matrix ι ι ℝ) {c : ℝ} (hc : 0 ≤ c) :
    0 ≤ fullLipschitz A D c := by
  unfold fullLipschitz
  positivity

theorem norm_stateTerm_le (D : Fin n → Matrix ι ι ℝ) (X : Matrix ι ι ℝ) :
    ‖stateTerm D X‖ ≤ (∑ i, ‖D i‖ * ‖(D i)ᵀ‖) * ‖X‖ := by
  unfold stateTerm
  refine (norm_sum_le _ _).trans ?_
  rw [Finset.sum_mul]
  refine Finset.sum_le_sum fun i _ => ?_
  calc ‖D i * X * (D i)ᵀ‖ ≤ ‖D i * X‖ * ‖(D i)ᵀ‖ := linfty_opNorm_mul _ _
    _ ≤ ‖D i‖ * ‖X‖ * ‖(D i)ᵀ‖ := by gcongr; exact linfty_opNorm_mul _ _
    _ = ‖D i‖ * ‖(D i)ᵀ‖ * ‖X‖ := by ring

theorem norm_fullLinear_le (A : Matrix ι ι ℝ) (D : Fin n → Matrix ι ι ℝ) {c : ℝ} (hc : 0 ≤ c)
    (X : Matrix ι ι ℝ) : ‖fullLinear A D c X‖ ≤ fullLipschitz A D c * ‖X‖ := by
  unfold fullLinear fullLipschitz
  refine (norm_add_le _ _).trans ?_
  rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg hc, add_mul]
  refine add_le_add ?_ ?_
  · calc ‖A * X * Aᵀ‖ ≤ ‖A * X‖ * ‖Aᵀ‖ := linfty_opNorm_mul _ _
      _ ≤ ‖A‖ * ‖X‖ * ‖Aᵀ‖ := by gcongr; exact linfty_opNorm_mul _ _
      _ = ‖A‖ * ‖Aᵀ‖ * ‖X‖ := by ring
  · calc c * ‖stateTerm D X‖ ≤ c * ((∑ i, ‖D i‖ * ‖(D i)ᵀ‖) * ‖X‖) :=
        mul_le_mul_of_nonneg_left (norm_stateTerm_le D X) hc
      _ = c * (∑ i, ‖D i‖ * ‖(D i)ᵀ‖) * ‖X‖ := by ring

theorem lipschitzWith_fullStep (A N : Matrix ι ι ℝ) (D : Fin n → Matrix ι ι ℝ) {c : ℝ}
    (hc : 0 ≤ c) :
    LipschitzWith ⟨fullLipschitz A D c, fullLipschitz_nonneg A D hc⟩ (fullStep A N D c) := by
  refine LipschitzWith.of_dist_le_mul fun X Y => ?_
  rw [dist_eq_norm, dist_eq_norm, fullStep_sub]
  exact norm_fullLinear_le A D hc (X - Y)

/-- **The full law is a contraction** when `‖A‖ ‖Aᵀ‖ + c ∑ᵢ ‖Dᵢ‖ ‖Dᵢᵀ‖ < 1`. -/
theorem contractingWith_fullStep (A N : Matrix ι ι ℝ) (D : Fin n → Matrix ι ι ℝ) {c : ℝ}
    (hc : 0 ≤ c) (hK : fullLipschitz A D c < 1) :
    ContractingWith ⟨fullLipschitz A D c, fullLipschitz_nonneg A D hc⟩ (fullStep A N D c) :=
  ⟨by exact_mod_cast hK, lipschitzWith_fullStep A N D hc⟩

set_option linter.unusedFintypeInType false in
instance : CompleteSpace (Matrix ι ι ℝ) := FiniteDimensional.complete ℝ _

/-- The solution of the full law. -/
noncomputable def fullFixed (A N : Matrix ι ι ℝ) (D : Fin n → Matrix ι ι ℝ) {c : ℝ} (hc : 0 ≤ c)
    (hK : fullLipschitz A D c < 1) : Matrix ι ι ℝ :=
  (contractingWith_fullStep A N D hc hK).fixedPoint (fullStep A N D c)

theorem fullStep_fullFixed (A N : Matrix ι ι ℝ) (D : Fin n → Matrix ι ι ℝ) {c : ℝ} (hc : 0 ≤ c)
    (hK : fullLipschitz A D c < 1) :
    fullStep A N D c (fullFixed A N D hc hK) = fullFixed A N D hc hK :=
  (contractingWith_fullStep A N D hc hK).fixedPoint_isFixedPt

/-- **Uniqueness**: every solution of the full law is `fullFixed`. -/
theorem eq_fullFixed_of_fixed (A N : Matrix ι ι ℝ) (D : Fin n → Matrix ι ι ℝ) {c : ℝ} (hc : 0 ≤ c)
    (hK : fullLipschitz A D c < 1) {X : Matrix ι ι ℝ} (hX : fullStep A N D c X = X) :
    X = fullFixed A N D hc hK :=
  (contractingWith_fullStep A N D hc hK).fixedPoint_unique hX

/-- **The iteration converges** from every start. -/
theorem tendsto_iterate_fullFixed (A N : Matrix ι ι ℝ) (D : Fin n → Matrix ι ι ℝ) {c : ℝ}
    (hc : 0 ≤ c) (hK : fullLipschitz A D c < 1) (X₀ : Matrix ι ι ℝ) :
    Tendsto (fun k => (fullStep A N D c)^[k] X₀) atTop (𝓝 (fullFixed A N D hc hK)) :=
  (contractingWith_fullStep A N D hc hK).tendsto_iterate_fixedPoint X₀

/-! ### Positivity -/

omit [DecidableEq ι] in
theorem stateTerm_posSemidef (D : Fin n → Matrix ι ι ℝ) {X : Matrix ι ι ℝ} (hX : X.PosSemidef) :
    (stateTerm D X).PosSemidef := by
  unfold stateTerm
  exact Finset.sum_induction _ (fun M : Matrix ι ι ℝ => M.PosSemidef) (fun _ _ ha hb => ha.add hb)
    Matrix.PosSemidef.zero fun i _ => posSemidef_conj hX (D i)

omit [DecidableEq ι] in
theorem fullStep_posSemidef (A : Matrix ι ι ℝ) {N : Matrix ι ι ℝ} (hN : N.PosSemidef)
    (D : Fin n → Matrix ι ι ℝ) {c : ℝ} (hc : 0 ≤ c) {X : Matrix ι ι ℝ} (hX : X.PosSemidef) :
    (fullStep A N D c X).PosSemidef :=
  ((posSemidef_conj hX A).add ((stateTerm_posSemidef D hX).smul hc)).add hN

omit [DecidableEq ι] in
theorem fullStep_iterate_posSemidef (A : Matrix ι ι ℝ) {N : Matrix ι ι ℝ} (hN : N.PosSemidef)
    (D : Fin n → Matrix ι ι ℝ) {c : ℝ} (hc : 0 ≤ c) {X : Matrix ι ι ℝ} (hX : X.PosSemidef)
    (k : ℕ) : ((fullStep A N D c)^[k] X).PosSemidef := by
  induction k with
  | zero => simpa using hX
  | succ k ih => rw [Function.iterate_succ_apply']; exact fullStep_posSemidef A hN D hc ih

omit [DecidableEq ι] in
set_option linter.unusedFintypeInType false in
/-- Matrix entries are continuous in the operator-norm topology. -/
theorem continuous_entry (i j : ι) : Continuous fun X : Matrix ι ι ℝ => X i j :=
  (Matrix.entryLinearMap ℝ ℝ i j).continuous_of_finiteDimensional

omit [DecidableEq ι] in
set_option linter.unusedFintypeInType false in
/-- The quadratic forms of Mathlib's `PosSemidef` are continuous in the matrix argument. -/
theorem continuous_quadForm_matrix (v : ι →₀ ℝ) :
    Continuous fun X : Matrix ι ι ℝ =>
      v.sum fun i xi => v.sum fun j xj => star xi * X i j * xj := by
  simp only [Finsupp.sum]
  exact continuous_finsetSum _ fun i _ => continuous_finsetSum _ fun j _ =>
    (continuous_const.mul (continuous_entry i j)).mul continuous_const

omit [DecidableEq ι] in
set_option linter.unusedFintypeInType false in
/-- The positive semidefinite cone is closed: a limit of PSD matrices is PSD. -/
theorem posSemidef_of_tendsto {X : ℕ → Matrix ι ι ℝ} {L : Matrix ι ι ℝ}
    (hX : ∀ k, (X k).PosSemidef) (hlim : Tendsto X atTop (𝓝 L)) : L.PosSemidef := by
  refine ⟨Matrix.IsHermitian.ext fun i j => ?_, fun v => ?_⟩
  · have h1 : Tendsto (fun k => X k j i) atTop (𝓝 (L j i)) :=
      ((continuous_entry j i).tendsto L).comp hlim
    have h2 : Tendsto (fun k => X k i j) atTop (𝓝 (L i j)) :=
      ((continuous_entry i j).tendsto L).comp hlim
    have heq : (fun k => X k j i) = fun k => X k i j := by
      funext k
      have := (hX k).1.apply i j
      simpa using this
    rw [star_trivial]
    exact tendsto_nhds_unique (heq ▸ h1) h2
  · have h := ((continuous_quadForm_matrix v).tendsto L).comp hlim
    exact ge_of_tendsto' h fun k => (hX k).2 v

/-- **The solution of the full law is positive semidefinite.** -/
theorem fullFixed_posSemidef (A : Matrix ι ι ℝ) {N : Matrix ι ι ℝ} (hN : N.PosSemidef)
    (D : Fin n → Matrix ι ι ℝ) {c : ℝ} (hc : 0 ≤ c) (hK : fullLipschitz A D c < 1) :
    (fullFixed A N D hc hK).PosSemidef :=
  posSemidef_of_tendsto (fun k => fullStep_iterate_posSemidef A hN D hc Matrix.PosSemidef.zero k)
    (tendsto_iterate_fullFixed A N D hc hK 0)

/-! ### Domination of the additive law -/

omit [DecidableEq ι] in
/-- Iterating the full law from a PSD fixed point `S` of the additive law stays `⪰ S`. -/
theorem fullStep_iterate_sub_posSemidef (A N : Matrix ι ι ℝ)
    (D : Fin n → Matrix ι ι ℝ) {c : ℝ} (hc : 0 ≤ c) {S : Matrix ι ι ℝ} (hS : covStep A N S = S)
    (hSpsd : S.PosSemidef) (k : ℕ) : ((fullStep A N D c)^[k] S - S).PosSemidef := by
  induction k with
  | zero => simpa using Matrix.PosSemidef.zero
  | succ k ih =>
    rw [Function.iterate_succ_apply']
    have hXk : ((fullStep A N D c)^[k] S).PosSemidef := by
      have := ih.add hSpsd
      simpa using this
    have h2 : fullStep A N D c ((fullStep A N D c)^[k] S) - covStep A N S =
        A * ((fullStep A N D c)^[k] S - S) * Aᵀ + c • stateTerm D ((fullStep A N D c)^[k] S) := by
      simp only [fullStep, fullLinear, covStep, Matrix.mul_sub, Matrix.sub_mul]
      abel
    have h3 : fullStep A N D c ((fullStep A N D c)^[k] S) - S =
        A * ((fullStep A N D c)^[k] S - S) * Aᵀ + c • stateTerm D ((fullStep A N D c)^[k] S) := by
      rw [← h2, hS]
    rw [h3]
    exact (posSemidef_conj ih A).add ((stateTerm_posSemidef D hXk).smul hc)

/-- **Domination**: the solution of the full law dominates the PSD solution of the additive law. -/
theorem fullFixed_sub_posSemidef (A N : Matrix ι ι ℝ)
    (D : Fin n → Matrix ι ι ℝ) {c : ℝ} (hc : 0 ≤ c) (hK : fullLipschitz A D c < 1)
    {S : Matrix ι ι ℝ} (hS : covStep A N S = S) (hSpsd : S.PosSemidef) :
    (fullFixed A N D hc hK - S).PosSemidef :=
  posSemidef_of_tendsto (fullStep_iterate_sub_posSemidef A N D hc hS hSpsd)
    ((tendsto_iterate_fullFixed A N D hc hK S).sub_const S)

/-- **First-order lower bound on the inflation**: `Σ_full - Σ_add ⪰ c ∑ᵢ Dᵢ Σ_add Dᵢᵀ`. -/
theorem fullFixed_sub_sub_posSemidef (A N : Matrix ι ι ℝ)
    (D : Fin n → Matrix ι ι ℝ) {c : ℝ} (hc : 0 ≤ c) (hK : fullLipschitz A D c < 1)
    {S : Matrix ι ι ℝ} (hS : covStep A N S = S) (hSpsd : S.PosSemidef) :
    (fullFixed A N D hc hK - S - c • stateTerm D S).PosSemidef := by
  have hΔ := fullFixed_sub_posSemidef A N D hc hK hS hSpsd
  have hid : fullFixed A N D hc hK - S - c • stateTerm D S =
      A * (fullFixed A N D hc hK - S) * Aᵀ + c • stateTerm D (fullFixed A N D hc hK - S) := by
    have h2 : fullStep A N D c (fullFixed A N D hc hK) - covStep A N S - c • stateTerm D S =
        A * (fullFixed A N D hc hK - S) * Aᵀ + c • stateTerm D (fullFixed A N D hc hK - S) := by
      simp only [fullStep, fullLinear, covStep, ← stateTerm_sub, Matrix.mul_sub, Matrix.sub_mul,
        smul_sub]
      abel
    rw [← h2, hS, fullStep_fullFixed]
  rw [hid]
  exact (posSemidef_conj hΔ A).add ((stateTerm_posSemidef D hΔ).smul hc)

/-! ### The minibatch coefficient of the note -/

/-- The note's state-dependent coefficient `c = h² t² (1 - m/n) / (m n)` for batches of size `m`
drawn without replacement from `n` samples. -/
noncomputable def minibatchCoeff (h t : ℝ) (m n : ℕ) : ℝ :=
  h ^ 2 * t ^ 2 * (1 - (m : ℝ) / n) / (m * n)

theorem minibatchCoeff_nonneg (h t : ℝ) {m n : ℕ} (hm : 0 < m) (hmn : m ≤ n) :
    0 ≤ minibatchCoeff h t m n := by
  have hn : (0 : ℝ) < n := by exact_mod_cast hm.trans_le hmn
  have hm' : (0 : ℝ) < m := by exact_mod_cast hm
  have hle : (m : ℝ) / n ≤ 1 := (div_le_one hn).mpr (by exact_mod_cast hmn)
  unfold minibatchCoeff
  apply div_nonneg
  · exact mul_nonneg (by positivity) (by linarith)
  · positivity

/-- The E8 full law of the note: ULA step, additive minibatch noise, and the state-dependent term
with `Dᵢ = Hᵢ - H` (per-sample Hessians `Hs i` minus their mean `H`). -/
noncomputable def e8FullStep (P : Matrix ι ι ℝ) (h t : ℝ) (C : Matrix ι ι ℝ)
    (Hs : Fin n → Matrix ι ι ℝ) (H : Matrix ι ι ℝ) (m : ℕ) (X : Matrix ι ι ℝ) : Matrix ι ι ℝ :=
  fullStep (ulaStep P h) (minibatchNoise h t C) (fun i => Hs i - H) (minibatchCoeff h t m n) X

end Laplace.Sampler
