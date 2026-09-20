/-
Copyright (c) 2026 Timaeus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Timaeus
-/
import Mathlib
import Laplace.Multi.AllOrders

/-!
# Taylor expansion of a test function into coordinate monomials

For a smooth compactly supported `φ : (ι → ℝ) → ℝ` and a point `p`, the Taylor
polynomial of order `n` at `p` is a finite linear combination of the coordinate
monomials `x ↦ ∏ⱼ (x (m j) - p (m j))` over words `m : Fin k → ι`, `k ≤ n`
(`iteratedFDeriv_apply_const_eq_sum_words`), and the remainder is bounded by a
constant times `‖x - p‖^{n+1}` uniformly in `x`
(`exists_taylor_remainder_bound`). Both are consumed by
`CutoffMonomialFamily`, where they transfer superpolynomial agreement of a
projective family from the cutoff monomials to every smooth test supported near
`p`.
-/

open Asymptotics Filter
open scoped ContDiff

namespace Laplace

variable {ι : Type*} [Fintype ι]

/-- The coordinate monomial of the word `m` centred at `p`. -/
def coordMonomial (p : ι → ℝ) {k : ℕ} (m : Fin k → ι) (x : ι → ℝ) : ℝ :=
  ∏ j, (x (m j) - p (m j))

omit [Fintype ι] in
theorem coordMonomial_continuous (p : ι → ℝ) {k : ℕ} (m : Fin k → ι) :
    Continuous (coordMonomial p m) := by
  unfold coordMonomial
  fun_prop

theorem coordMonomial_contDiff (p : ι → ℝ) {k : ℕ} (m : Fin k → ι) :
    ContDiff ℝ ∞ (coordMonomial p m) := by
  unfold coordMonomial
  fun_prop

/-- **Multilinear expansion**: `D^kφ(p)[v, …, v] = ∑_m (∏ⱼ v (m j)) · D^kφ(p)[e_{m 0}, …]`. -/
theorem continuousMultilinearMap_apply_const_eq_sum_words [DecidableEq ι] {k : ℕ}
    (T : ContinuousMultilinearMap ℝ (fun _ : Fin k ↦ (ι → ℝ)) ℝ) (v : ι → ℝ) :
    T (fun _ ↦ v) = ∑ m : Fin k → ι, (∏ j, v (m j)) * T (fun j ↦ Pi.single (m j) (1 : ℝ)) := by
  have hv : v = ∑ i, v i • (Pi.single i (1 : ℝ) : ι → ℝ) := by
    ext j
    simp [Finset.sum_apply, Pi.single_apply]
  have h := T.map_sum (fun (_ : Fin k) (i : ι) ↦ v i • (Pi.single i (1 : ℝ) : ι → ℝ))
  calc T (fun _ ↦ v) = T (fun _ ↦ ∑ i, v i • (Pi.single i (1 : ℝ) : ι → ℝ)) := by rw [← hv]
    _ = ∑ r : Fin k → ι, T (fun i ↦ v (r i) • (Pi.single (r i) (1 : ℝ) : ι → ℝ)) := h
    _ = ∑ m : Fin k → ι, (∏ j, v (m j)) * T (fun j ↦ Pi.single (m j) (1 : ℝ)) := by
        refine Finset.sum_congr rfl fun m _ ↦ ?_
        rw [T.map_smul_univ (fun j ↦ v (m j)) (fun j ↦ Pi.single (m j) (1 : ℝ)), smul_eq_mul]

/-- The Taylor term of order `k` at `p`, evaluated at `x`, as a combination of the
coordinate monomials of the words of length `k`. -/
theorem iteratedFDeriv_apply_const_eq_sum_words [DecidableEq ι] {φ : (ι → ℝ) → ℝ} (p x : ι → ℝ)
    (k : ℕ) :
    iteratedFDeriv ℝ k φ p (fun _ ↦ x - p) =
      ∑ m : Fin k → ι, iteratedFDeriv ℝ k φ p (fun j ↦ Pi.single (m j) (1 : ℝ)) *
        coordMonomial p m x := by
  rw [continuousMultilinearMap_apply_const_eq_sum_words]
  refine Finset.sum_congr rfl fun m _ ↦ ?_
  unfold coordMonomial
  simp only [Pi.sub_apply]
  ring

omit [Fintype ι] in
/-- A continuous compactly supported function into a normed space is bounded. -/
theorem HasCompactSupport.exists_norm_le {E : Type*} [NormedAddCommGroup E]
    {f : (ι → ℝ) → E} (hf : Continuous f) (hs : HasCompactSupport f) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ x, ‖f x‖ ≤ B := by
  obtain ⟨C, hC⟩ := hs.isCompact.exists_bound_of_continuousOn hf.continuousOn
  refine ⟨max C 0, le_max_right _ _, fun x ↦ ?_⟩
  by_cases hx : x ∈ tsupport f
  · exact (hC x hx).trans (le_max_left _ _)
  · rw [image_eq_zero_of_notMem_tsupport hx, norm_zero]
    exact le_max_right _ _

/-- **Taylor remainder bound.** For smooth compactly supported `φ`, the order-`n`
Taylor polynomial at `p` approximates `φ` to `M ‖x - p‖^{n+1}` uniformly. -/
theorem exists_taylor_remainder_bound {φ : (ι → ℝ) → ℝ} (hφ : ContDiff ℝ ∞ φ)
    (hφs : HasCompactSupport φ) (p : ι → ℝ) (n : ℕ) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ x : ι → ℝ,
      |φ x - ∑ k ∈ Finset.range (n + 1),
        ((k.factorial : ℝ)⁻¹) * iteratedFDeriv ℝ k φ p (fun _ ↦ x - p)| ≤
        M * ‖x - p‖ ^ (n + 1) := by
  -- a global bound on the `(n+1)`-st derivative
  obtain ⟨B, hB0, hB⟩ := HasCompactSupport.exists_norm_le
    (hφ.continuous_iteratedFDeriv (natCast_le_infty (n + 1))) (hφs.iteratedFDeriv (n + 1))
  refine ⟨B / n.factorial, by positivity, fun x ↦ ?_⟩
  set v : ι → ℝ := x - p with hv_def
  -- the line through `p` in direction `v`
  set ℓ : ℝ →L[ℝ] (ι → ℝ) := (ContinuousLinearMap.id ℝ ℝ).smulRight v with hℓ_def
  have hℓ : ∀ s : ℝ, ℓ s = s • v := fun s ↦ by simp [hℓ_def]
  set φ' : (ι → ℝ) → ℝ := fun w ↦ φ (p + w) with hφ'_def
  have hφ' : ContDiff ℝ ∞ φ' := hφ.comp (contDiff_const.add contDiff_id)
  set g : ℝ → ℝ := fun s ↦ φ' (ℓ s) with hg_def
  have hg : ContDiff ℝ ∞ g := hφ'.comp ℓ.contDiff
  -- iterated derivatives of `g` along the line
  have hgd : ∀ (k : ℕ) (s : ℝ), iteratedDeriv k g s =
      iteratedFDeriv ℝ k φ (p + s • v) (fun _ ↦ v) := by
    intro k s
    rw [iteratedDeriv_eq_iteratedFDeriv]
    have h1 := ℓ.iteratedFDeriv_comp_right hφ' s (natCast_le_infty k)
    have h2 : iteratedFDeriv ℝ k (φ' ∘ ℓ) s = iteratedFDeriv ℝ k g s := rfl
    rw [← h2, h1, ContinuousMultilinearMap.compContinuousLinearMap_apply]
    simp only [hℓ, one_smul, hφ'_def]
    rw [iteratedFDeriv_comp_add_left]
  -- Taylor's theorem on `[0, 1]`
  have hgOn : ContDiffOn ℝ (n + 1) g (Set.Icc 0 1) :=
    (hg.of_le (natCast_le_infty (n + 1))).contDiffOn
  have hU : UniqueDiffOn ℝ (Set.Icc (0 : ℝ) 1) := uniqueDiffOn_Icc zero_lt_one
  have hwithin : ∀ (k : ℕ) (y : ℝ), y ∈ Set.Icc (0 : ℝ) 1 →
      iteratedDerivWithin k g (Set.Icc 0 1) y = iteratedDeriv k g y := fun k y hy ↦
    iteratedDerivWithin_eq_iteratedDeriv hU (hg.contDiffAt.of_le (natCast_le_infty k)) hy
  have hC : ∀ y ∈ Set.Icc (0 : ℝ) 1, ‖iteratedDerivWithin (n + 1) g (Set.Icc 0 1) y‖ ≤
      B * ‖v‖ ^ (n + 1) := by
    intro y hy
    rw [hwithin _ y hy, hgd]
    calc ‖iteratedFDeriv ℝ (n + 1) φ (p + y • v) (fun _ ↦ v)‖
        ≤ ‖iteratedFDeriv ℝ (n + 1) φ (p + y • v)‖ * ∏ _j : Fin (n + 1), ‖v‖ :=
          ContinuousMultilinearMap.le_opNorm _ _
      _ = ‖iteratedFDeriv ℝ (n + 1) φ (p + y • v)‖ * ‖v‖ ^ (n + 1) := by
          rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin]
      _ ≤ B * ‖v‖ ^ (n + 1) := mul_le_mul_of_nonneg_right (hB _) (by positivity)
  have htay := taylor_mean_remainder_bound (f := g) (a := 0) (b := 1) (x := 1) zero_le_one
    hgOn (Set.right_mem_Icc.mpr zero_le_one) hC
  rw [taylor_within_apply] at htay
  -- identify the pieces
  have hg1 : g 1 = φ x := by
    simp only [hg_def, hφ'_def, hℓ, one_smul, hv_def]
    congr 1
    abel
  have hterms : ∀ k ∈ Finset.range (n + 1),
      (((k.factorial : ℝ)⁻¹ * (1 - 0) ^ k) • iteratedDerivWithin k g (Set.Icc 0 1) 0) =
        ((k.factorial : ℝ)⁻¹) * iteratedFDeriv ℝ k φ p (fun _ ↦ x - p) := by
    intro k _
    rw [hwithin k 0 (Set.left_mem_Icc.mpr zero_le_one), hgd, zero_smul, add_zero, smul_eq_mul,
      sub_zero, one_pow, mul_one]
  rw [Finset.sum_congr rfl hterms, hg1, Real.norm_eq_abs, sub_zero, one_pow, mul_one] at htay
  calc |φ x - ∑ k ∈ Finset.range (n + 1),
        ((k.factorial : ℝ)⁻¹) * iteratedFDeriv ℝ k φ p (fun _ ↦ x - p)|
      ≤ B * ‖v‖ ^ (n + 1) / n.factorial := htay
    _ = B / n.factorial * ‖x - p‖ ^ (n + 1) := by
        rw [hv_def]
        ring

end Laplace
