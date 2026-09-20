/-
Copyright (c) 2026 Timaeus Research. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniel Murfet
-/
import Mathlib
import Laplace.Multi.GradeRecovery

/-!
# Integerized weights, weighted degrees and the weighted dilation

Infrastructure for the weighted-jet induction (germbij §7.4(b), the
semi-quasi-homogeneous recovery). Positive rational weights `q i = a i / D` are
represented by an `IntWeights` structure with natural-number data, so that

* the weighted degree `wdeg α = ∑ a i * α i` of a monomial is a natural number,
* the dilation `dil ε u = (ε ^ a i * u i)` uses natural powers only,
* a leading part `P` of weighted degree `D` satisfies `P (dil ε u) = ε ^ D * P u`,
  so that at temperature `t = ε ^ (-D)` the rescaled loss is `P + corrections`
  entering at the natural rates `ε ^ (wdeg α − D)`.

Also: the volume scaling of the dilation (from the diagonal-map Haar theorem), the
change of variables for integrals, polynomial growth measured against `P`
(`PolyBoundedBy`) with its closure properties, coordinate growth from a
natural-power coercivity hypothesis, and integrability of `P`-polynomials against
`e^{-cP}` from integrability of `e^{-cP}` alone.
-/

open Real MeasureTheory Filter Topology

namespace Laplace.Multi

variable {ι : Type*}

/-- Integerized positive weights: the real weights are `a i / D`. -/
structure IntWeights (ι : Type*) where
  /-- The common denominator (the weighted degree of the leading part). -/
  D : ℕ
  D_pos : 0 < D
  /-- The integer weights of the coordinates. -/
  a : ι → ℕ
  a_pos : ∀ i, 0 < a i

namespace IntWeights

variable (W : IntWeights ι)

/-- The weighted degree of a monomial exponent. -/
def wdeg [Fintype ι] (α : ι → ℕ) : ℕ := ∑ i, W.a i * α i

/-- The weighted dilation `u ↦ (ε ^ a i * u i)_i`. -/
def dil (ε : ℝ) (u : ι → ℝ) : ι → ℝ := fun i ↦ ε ^ W.a i * u i

@[simp] theorem dil_apply (ε : ℝ) (u : ι → ℝ) (i : ι) : W.dil ε u i = ε ^ W.a i * u i := rfl

theorem mvMonomial_dil [Fintype ι] (α : ι → ℕ) (ε : ℝ) (u : ι → ℝ) :
    mvMonomial α (W.dil ε u) = ε ^ W.wdeg α * mvMonomial α u := by
  unfold mvMonomial wdeg
  simp only [dil_apply, mul_pow, ← pow_mul]
  rw [Finset.prod_mul_distrib, Finset.prod_pow_eq_pow_sum]

theorem dil_eq_diagonalMap (ε : ℝ) : W.dil ε = ⇑(diagonalMap fun i ↦ ε ^ W.a i) := rfl

theorem measurable_dil (ε : ℝ) : Measurable (W.dil ε) :=
  measurable_pi_lambda _ fun i ↦ (measurable_pi_apply i).const_mul _

/-- The total weight `∑ a i` (the homogeneity of the volume under the dilation). -/
def total [Fintype ι] : ℕ := ∑ i, W.a i

theorem total_pos [Fintype ι] [Nonempty ι] : 0 < W.total :=
  Finset.sum_pos (fun i _ ↦ W.a_pos i) Finset.univ_nonempty

/-- **Volume scaling of the dilation**: `(dil ε)_* vol = ε^{-∑ a} • vol`. -/
theorem map_dil_volume [Fintype ι] {ε : ℝ} (hε : 0 < ε) :
    Measure.map (W.dil ε) (volume : Measure (ι → ℝ)) =
      ENNReal.ofReal ((ε ^ W.total)⁻¹) • volume := by
  have hdet : LinearMap.det (diagonalMap fun i ↦ ε ^ W.a i) = ε ^ W.total := by
    rw [det_diagonalMap, Finset.prod_pow_eq_pow_sum]
    rfl
  have hne : LinearMap.det (diagonalMap fun i ↦ ε ^ W.a i) ≠ 0 := by
    rw [hdet]
    positivity
  have hmap := Measure.map_linearMap_addHaar_pi_eq_smul_addHaar hne (volume : Measure (ι → ℝ))
  rw [hdet] at hmap
  rw [dil_eq_diagonalMap, hmap]
  congr 1
  rw [abs_of_pos (inv_pos.mpr (by positivity))]

/-- **Change of variables along the dilation**. -/
theorem integral_dil [Fintype ι] {ε : ℝ} (hε : 0 < ε) {f : (ι → ℝ) → ℝ}
    (hf : AEStronglyMeasurable f (volume : Measure (ι → ℝ))) :
    ∫ x, f x = ε ^ W.total * ∫ u, f (W.dil ε u) := by
  have hmap := W.map_dil_volume hε
  have hfm : AEStronglyMeasurable f (Measure.map (W.dil ε) volume) := by
    rw [hmap]
    exact hf.smul_measure _
  have h := integral_map (W.measurable_dil ε).aemeasurable hfm
  rw [hmap, integral_smul_measure, ENNReal.toReal_ofReal (by positivity), smul_eq_mul] at h
  have hpos : (0 : ℝ) < ε ^ W.total := by positivity
  rw [← h]
  field_simp

/-- Integrability transfers along the dilation. -/
theorem integrable_comp_dil_iff [Fintype ι] {ε : ℝ} (hε : 0 < ε) {f : (ι → ℝ) → ℝ}
    (hf : AEStronglyMeasurable f (volume : Measure (ι → ℝ))) :
    Integrable (fun u ↦ f (W.dil ε u)) ↔ Integrable f := by
  have hmap := W.map_dil_volume hε
  have hfm : AEStronglyMeasurable f (Measure.map (W.dil ε) volume) := by
    rw [hmap]
    exact hf.smul_measure _
  rw [show (fun u ↦ f (W.dil ε u)) = f ∘ W.dil ε from rfl,
    ← integrable_map_measure hfm (W.measurable_dil ε).aemeasurable, hmap]
  exact integrable_smul_measure
    (by simp only [ne_eq, ENNReal.ofReal_eq_zero, inv_nonpos, not_le]; positivity)
    ENNReal.ofReal_ne_top

end IntWeights

/-! ### Polynomial growth measured against the leading part -/

/-- `f` is bounded by a polynomial in `P`: `|f u| ≤ C (1 + P u)^N`. -/
def PolyBoundedBy (P f : (ι → ℝ) → ℝ) : Prop :=
  ∃ (C : ℝ) (N : ℕ), 0 ≤ C ∧ ∀ u, |f u| ≤ C * (1 + P u) ^ N

namespace PolyBoundedBy

variable {P : (ι → ℝ) → ℝ}

theorem const (c : ℝ) : PolyBoundedBy P fun _ ↦ c :=
  ⟨|c|, 0, abs_nonneg c, fun _ ↦ by simp⟩

theorem of_le {f g : (ι → ℝ) → ℝ} (hg : PolyBoundedBy P g) (h : ∀ u, |f u| ≤ |g u|) :
    PolyBoundedBy P f := by
  obtain ⟨C, N, hC, hb⟩ := hg
  exact ⟨C, N, hC, fun u ↦ (h u).trans (hb u)⟩

theorem abs {f : (ι → ℝ) → ℝ} (hf : PolyBoundedBy P f) : PolyBoundedBy P fun u ↦ |f u| :=
  hf.of_le fun u ↦ by rw [abs_abs]

theorem mul (hP0 : ∀ u, 0 ≤ P u) {f g : (ι → ℝ) → ℝ} (hf : PolyBoundedBy P f)
    (hg : PolyBoundedBy P g) : PolyBoundedBy P fun u ↦ f u * g u := by
  obtain ⟨C₁, N₁, hC₁, h₁⟩ := hf
  obtain ⟨C₂, N₂, hC₂, h₂⟩ := hg
  refine ⟨C₁ * C₂, N₁ + N₂, by positivity, fun u ↦ ?_⟩
  rw [abs_mul, pow_add]
  have := hP0 u
  calc |f u| * |g u| ≤ (C₁ * (1 + P u) ^ N₁) * (C₂ * (1 + P u) ^ N₂) :=
        mul_le_mul (h₁ u) (h₂ u) (abs_nonneg _) (by positivity)
    _ = C₁ * C₂ * ((1 + P u) ^ N₁ * (1 + P u) ^ N₂) := by ring

theorem add (hP0 : ∀ u, 0 ≤ P u) {f g : (ι → ℝ) → ℝ} (hf : PolyBoundedBy P f)
    (hg : PolyBoundedBy P g) : PolyBoundedBy P fun u ↦ f u + g u := by
  obtain ⟨C₁, N₁, hC₁, h₁⟩ := hf
  obtain ⟨C₂, N₂, hC₂, h₂⟩ := hg
  refine ⟨C₁ + C₂, N₁ + N₂, by positivity, fun u ↦ ?_⟩
  have hP := hP0 u
  have h1 : (1 + P u) ^ N₁ ≤ (1 + P u) ^ (N₁ + N₂) :=
    pow_le_pow_right₀ (by linarith) (Nat.le_add_right _ _)
  have h2 : (1 + P u) ^ N₂ ≤ (1 + P u) ^ (N₁ + N₂) :=
    pow_le_pow_right₀ (by linarith) (Nat.le_add_left _ _)
  calc |f u + g u| ≤ |f u| + |g u| := abs_add_le _ _
    _ ≤ C₁ * (1 + P u) ^ N₁ + C₂ * (1 + P u) ^ N₂ := add_le_add (h₁ u) (h₂ u)
    _ ≤ C₁ * (1 + P u) ^ (N₁ + N₂) + C₂ * (1 + P u) ^ (N₁ + N₂) :=
        add_le_add (mul_le_mul_of_nonneg_left h1 hC₁) (mul_le_mul_of_nonneg_left h2 hC₂)
    _ = (C₁ + C₂) * (1 + P u) ^ (N₁ + N₂) := by ring

theorem const_mul (c : ℝ) {f : (ι → ℝ) → ℝ} (hf : PolyBoundedBy P f) :
    PolyBoundedBy P fun u ↦ c * f u := by
  obtain ⟨C, N, hC, h⟩ := hf
  refine ⟨|c| * C, N, by positivity, fun u ↦ ?_⟩
  rw [abs_mul, mul_assoc]
  exact mul_le_mul_of_nonneg_left (h u) (abs_nonneg c)

theorem finset_sum (hP0 : ∀ u, 0 ≤ P u) {κ : Type*} (s : Finset κ) {f : κ → (ι → ℝ) → ℝ}
    (hf : ∀ j ∈ s, PolyBoundedBy P (f j)) : PolyBoundedBy P fun u ↦ ∑ j ∈ s, f j u := by
  classical
  induction s using Finset.induction_on with
  | empty => exact ⟨0, 0, le_rfl, fun u ↦ by simp⟩
  | insert b s hb ih =>
    have h1 := (hf b (Finset.mem_insert_self b s)).add hP0
      (ih fun j hj ↦ hf j (Finset.mem_insert_of_mem hj))
    refine h1.of_le fun u ↦ ?_
    rw [Finset.sum_insert hb]

end PolyBoundedBy

/-! ### Coordinate growth from natural-power coercivity -/

namespace IntWeights

variable (W : IntWeights ι)

/-- **Coordinate growth from coercivity**: if `|u i|^D ≤ κ P(u)^{a i}` then
`|u i| ≤ 1 + κ P(u)^{a i}`. -/
theorem abs_coord_le_of_coercive {P : (ι → ℝ) → ℝ} {κ : ℝ} (hκ : 0 ≤ κ) (hP0 : ∀ u, 0 ≤ P u)
    (hcoer : ∀ u i, |u i| ^ W.D ≤ κ * P u ^ W.a i) (u : ι → ℝ) (i : ι) :
    |u i| ≤ 1 + κ * P u ^ W.a i := by
  rcases le_or_gt |u i| 1 with h | h
  · have := mul_nonneg hκ (pow_nonneg (hP0 u) (W.a i))
    linarith
  · calc |u i| ≤ |u i| ^ W.D := le_self_pow₀ h.le W.D_pos.ne'
      _ ≤ κ * P u ^ W.a i := hcoer u i
      _ ≤ 1 + κ * P u ^ W.a i := by linarith

theorem polyBoundedBy_coord {P : (ι → ℝ) → ℝ} {κ : ℝ} (hκ : 0 ≤ κ) (hP0 : ∀ u, 0 ≤ P u)
    (hcoer : ∀ u i, |u i| ^ W.D ≤ κ * P u ^ W.a i) (i : ι) :
    PolyBoundedBy P fun u ↦ u i := by
  refine ⟨1 + κ, W.a i, by positivity, fun u ↦ ?_⟩
  have hP := hP0 u
  have h1 : (1 : ℝ) ≤ (1 + P u) ^ W.a i := one_le_pow₀ (by linarith)
  have h2 : P u ^ W.a i ≤ (1 + P u) ^ W.a i := pow_le_pow_left₀ hP (by linarith) _
  calc |u i| ≤ 1 + κ * P u ^ W.a i := W.abs_coord_le_of_coercive hκ hP0 hcoer u i
    _ ≤ (1 + P u) ^ W.a i + κ * (1 + P u) ^ W.a i :=
        add_le_add h1 (mul_le_mul_of_nonneg_left h2 hκ)
    _ = (1 + κ) * (1 + P u) ^ W.a i := by ring

theorem polyBoundedBy_mvMonomial [Fintype ι] {P : (ι → ℝ) → ℝ} {κ : ℝ} (hκ : 0 ≤ κ)
    (hP0 : ∀ u, 0 ≤ P u) (hcoer : ∀ u i, |u i| ^ W.D ≤ κ * P u ^ W.a i) (α : ι → ℕ) :
    PolyBoundedBy P (mvMonomial α) := by
  classical
  have : PolyBoundedBy P fun u ↦ ∏ i ∈ (Finset.univ : Finset ι), u i ^ α i := by
    induction (Finset.univ : Finset ι) using Finset.induction_on with
    | empty => exact ⟨1, 0, zero_le_one, fun u ↦ by simp⟩
    | insert b s hb ih =>
      have hpow : PolyBoundedBy P fun u ↦ u b ^ α b := by
        induction α b with
        | zero => exact ⟨1, 0, zero_le_one, fun u ↦ by simp⟩
        | succ n ihn =>
          have := (W.polyBoundedBy_coord hκ hP0 hcoer b).mul hP0 ihn
          exact this.of_le fun u ↦ by rw [pow_succ']
      refine (hpow.mul hP0 ih).of_le fun u ↦ ?_
      rw [Finset.prod_insert hb]
  exact this

end IntWeights

/-! ### Integrability of `P`-polynomials against `e^{-cP}` -/

/-- `(1 + x)^N e^{-c x}` is bounded on `x ≥ 0`. -/
theorem exists_one_add_pow_mul_exp_neg_le {c : ℝ} (hc : 0 < c) (N : ℕ) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ x : ℝ, 0 ≤ x → (1 + x) ^ N * Real.exp (-(c * x)) ≤ K := by
  refine ⟨2 ^ N * (1 + N.factorial / c ^ N), by positivity, fun x hx ↦ ?_⟩
  have hexp : Real.exp (-(c * x)) ≤ 1 := by
    rw [Real.exp_le_one_iff]
    nlinarith
  have hxN : x ^ N * Real.exp (-(c * x)) ≤ N.factorial / c ^ N := by
    have h := Real.pow_div_factorial_le_exp (c * x) (by positivity) N
    rw [mul_pow] at h
    have hcN : (0 : ℝ) < c ^ N := by positivity
    have hfac : (0 : ℝ) < N.factorial := by positivity
    have hepos := Real.exp_pos (c * x)
    rw [Real.exp_neg, ← div_eq_mul_inv, div_le_div_iff₀ hepos hcN]
    rw [div_le_iff₀ hfac] at h
    nlinarith [h]
  have h1x : (1 + x) ^ N ≤ 2 ^ N * (1 + x ^ N) := by
    rcases le_or_gt x 1 with h | h
    · have : (1 + x) ^ N ≤ 2 ^ N := pow_le_pow_left₀ (by linarith) (by linarith) N
      have : (0 : ℝ) ≤ x ^ N := by positivity
      nlinarith [pow_nonneg (zero_le_two (α := ℝ)) N]
    · have : (1 + x) ^ N ≤ (2 * x) ^ N := pow_le_pow_left₀ (by linarith) (by linarith) N
      rw [mul_pow] at this
      have : (0 : ℝ) ≤ 2 ^ N := by positivity
      nlinarith
  have he0 : 0 ≤ Real.exp (-(c * x)) := (Real.exp_pos _).le
  calc (1 + x) ^ N * Real.exp (-(c * x)) ≤ 2 ^ N * (1 + x ^ N) * Real.exp (-(c * x)) :=
        mul_le_mul_of_nonneg_right h1x he0
    _ = 2 ^ N * (Real.exp (-(c * x)) + x ^ N * Real.exp (-(c * x))) := by ring
    _ ≤ 2 ^ N * (1 + N.factorial / c ^ N) := by
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        linarith

/-- **Integrability of `P`-polynomials against `e^{-cP}`** from integrability of the
exponentials alone. -/
theorem integrable_mul_exp_neg_of_polyBoundedBy [Fintype ι] {P f : (ι → ℝ) → ℝ}
    (hPm : Measurable P) (hP0 : ∀ u, 0 ≤ P u)
    (hint : ∀ c : ℝ, 0 < c → Integrable fun u : ι → ℝ ↦ Real.exp (-(c * P u)))
    (hf : PolyBoundedBy P f) (hfm : AEStronglyMeasurable f (volume : Measure (ι → ℝ)))
    {c : ℝ} (hc : 0 < c) :
    Integrable fun u : ι → ℝ ↦ f u * Real.exp (-(c * P u)) := by
  obtain ⟨C, N, hC, hb⟩ := hf
  obtain ⟨K, hK, hKb⟩ := exists_one_add_pow_mul_exp_neg_le (half_pos hc) N
  have hint' := (hint (c / 2) (half_pos hc)).const_mul (C * K)
  refine hint'.mono' (hfm.mul (Real.measurable_exp.comp
    ((hPm.const_mul c).neg)).aestronglyMeasurable) ?_
  refine Filter.Eventually.of_forall fun u ↦ ?_
  have hP := hP0 u
  rw [Real.norm_eq_abs, abs_mul, abs_of_pos (Real.exp_pos _)]
  have hsplit : Real.exp (-(c * P u)) = Real.exp (-(c / 2 * P u)) * Real.exp (-(c / 2 * P u)) := by
    rw [← Real.exp_add]
    congr 1
    ring
  calc |f u| * Real.exp (-(c * P u)) ≤ C * (1 + P u) ^ N * Real.exp (-(c * P u)) :=
        mul_le_mul_of_nonneg_right (hb u) (Real.exp_pos _).le
    _ = C * ((1 + P u) ^ N * Real.exp (-(c / 2 * P u))) * Real.exp (-(c / 2 * P u)) := by
        rw [hsplit]
        ring
    _ ≤ C * K * Real.exp (-(c / 2 * P u)) := by
        apply mul_le_mul_of_nonneg_right _ (Real.exp_pos _).le
        exact mul_le_mul_of_nonneg_left (hKb (P u) hP) hC

end Laplace.Multi
