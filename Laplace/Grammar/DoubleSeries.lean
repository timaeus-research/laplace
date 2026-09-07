/-
Copyright (c) 2026 Timaeus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Laplace.Grammar.ConstantKernelUnequal

/-!
# Double power series with a radius margin (grammar §4.2, analytic bridge)

The algebra of a coefficient array `c : ℕ × ℕ → ℝ` with `|c_{ij}| ρ^{i+j} ≤ H` on the box
`[0, b]²`, `b < ρ` (Astra #6(a)): absolute summability of `∑ c_{ij} u^i v^j`, the faces
`a_i(v) = ∑_j c_{ij} v^j`, `b_j(u) = ∑_i c_{ij} u^i`, the face remainders
`|a_i(v) − ∑_{j<M} c_{ij} v^j| ≤ H ρ^{-i-M} v^M/(1 − v/ρ)`, the exact rectangular identity

  `Φ − ∑_{i<M₁} u^i a_i − ∑_{j<M₂} v^j b_j + ∑_{i<M₁,j<M₂} c_{ij} u^i v^j
     = ∑_{i,j} c_{M₁+i, M₂+j} u^{M₁+i} v^{M₂+j}`,

and the tail bound `H ρ^{-M₁-M₂} u^{M₁} v^{M₂}/((1−u/ρ)(1−v/ρ))`. Compatibility of the face jets
is automatic (both faces are built from the same `c_{ij}`), so no symmetry of mixed partial
derivatives is needed. Zero `sorry`/`axiom`.
-/

open Real

namespace Laplace.Grammar

/-- The geometric double bound: `|d_{ij}| ≤ A r^i t^j` gives absolute summability and
`∑ |d_{ij}| ≤ A/((1−r)(1−t))`. -/
theorem summable_abs_of_geom (d : ℕ × ℕ → ℝ) (A r t : ℝ) (hA : 0 ≤ A) (hr0 : 0 ≤ r) (hr1 : r < 1)
    (ht0 : 0 ≤ t) (ht1 : t < 1) (hd : ∀ ij, |d ij| ≤ A * r ^ ij.1 * t ^ ij.2) :
    (Summable fun ij => |d ij|) ∧ ∑' ij, |d ij| ≤ A / ((1 - r) * (1 - t)) := by
  have hgr : Summable fun i : ℕ => A * r ^ i := (summable_geometric_of_lt_one hr0 hr1).mul_left A
  have hgt : Summable fun j : ℕ => t ^ j := summable_geometric_of_lt_one ht0 ht1
  have hgr' : Summable fun i : ℕ => ‖A * r ^ i‖ := by
    refine hgr.congr fun i => ?_
    rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
  have hgt' : Summable fun j : ℕ => ‖t ^ j‖ := by
    refine hgt.congr fun j => ?_
    rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
  have hprod : Summable fun ij : ℕ × ℕ => (A * r ^ ij.1) * t ^ ij.2 :=
    summable_mul_of_summable_norm hgr' hgt'
  have hd' : ∀ ij, |d ij| ≤ (A * r ^ ij.1) * t ^ ij.2 := hd
  have hsum : Summable fun ij => |d ij| :=
    Summable.of_nonneg_of_le (fun ij => abs_nonneg _) hd' hprod
  refine ⟨hsum, ?_⟩
  calc ∑' ij, |d ij| ≤ ∑' ij : ℕ × ℕ, (A * r ^ ij.1) * t ^ ij.2 := hsum.tsum_le_tsum hd' hprod
    _ = (∑' i : ℕ, A * r ^ i) * ∑' j : ℕ, t ^ j := (tsum_mul_tsum_of_summable_norm hgr' hgt').symm
    _ = A / ((1 - r) * (1 - t)) := by
        rw [tsum_mul_left, tsum_geometric_of_lt_one hr0 hr1, tsum_geometric_of_lt_one ht0 ht1]
        field_simp

/-- The term bound from the coefficient envelope. -/
theorem coeff_term_le (c : ℕ × ℕ → ℝ) (ρ H u v : ℝ) (hρ : 0 < ρ)
    (hc : ∀ ij, |c ij| * ρ ^ (ij.1 + ij.2) ≤ H) (hu : 0 ≤ u) (hv : 0 ≤ v) (ij : ℕ × ℕ) :
    |c ij * u ^ ij.1 * v ^ ij.2| ≤ H * (u / ρ) ^ ij.1 * (v / ρ) ^ ij.2 := by
  have hρi : 0 < ρ ^ (ij.1 + ij.2) := pow_pos hρ _
  have hcb : |c ij| ≤ H / ρ ^ (ij.1 + ij.2) := by
    rw [le_div_iff₀ hρi]; exact hc ij
  rw [pow_add] at hcb
  rw [abs_mul, abs_mul, abs_of_nonneg (pow_nonneg hu _), abs_of_nonneg (pow_nonneg hv _),
    div_pow, div_pow]
  calc |c ij| * u ^ ij.1 * v ^ ij.2 ≤ H / (ρ ^ ij.1 * ρ ^ ij.2) * u ^ ij.1 * v ^ ij.2 := by
        gcongr
    _ = _ := by field_simp

/-- The double series `Φ(u,v) = ∑ c_{ij} u^i v^j`. -/
noncomputable def dblSum (c : ℕ × ℕ → ℝ) (u v : ℝ) : ℝ := ∑' ij : ℕ × ℕ, c ij * u ^ ij.1 * v ^ ij.2

/-- The `u`-face `a_i(v) = ∑_j c_{ij} v^j`. -/
noncomputable def faceU (c : ℕ × ℕ → ℝ) (i : ℕ) (v : ℝ) : ℝ := ∑' j : ℕ, c (i, j) * v ^ j

/-- The `v`-face `b_j(u) = ∑_i c_{ij} u^i`. -/
noncomputable def faceV (c : ℕ × ℕ → ℝ) (j : ℕ) (u : ℝ) : ℝ := ∑' i : ℕ, c (i, j) * u ^ i

/-- Absolute summability of the double series on `[0, ρ)²`. -/
theorem dbl_summable_abs (c : ℕ × ℕ → ℝ) (ρ H u v : ℝ) (hρ : 0 < ρ) (hH : 0 ≤ H)
    (hc : ∀ ij, |c ij| * ρ ^ (ij.1 + ij.2) ≤ H) (hu : 0 ≤ u) (huρ : u < ρ) (hv : 0 ≤ v)
    (hvρ : v < ρ) :
    Summable fun ij : ℕ × ℕ => |c ij * u ^ ij.1 * v ^ ij.2| :=
  (summable_abs_of_geom _ H (u / ρ) (v / ρ) hH (by positivity) ((div_lt_one hρ).2 huρ)
    (by positivity) ((div_lt_one hρ).2 hvρ) (coeff_term_le c ρ H u v hρ hc hu hv)).1

theorem dbl_summable (c : ℕ × ℕ → ℝ) (ρ H u v : ℝ) (hρ : 0 < ρ) (hH : 0 ≤ H)
    (hc : ∀ ij, |c ij| * ρ ^ (ij.1 + ij.2) ≤ H) (hu : 0 ≤ u) (huρ : u < ρ) (hv : 0 ≤ v)
    (hvρ : v < ρ) :
    Summable fun ij : ℕ × ℕ => c ij * u ^ ij.1 * v ^ ij.2 :=
  (dbl_summable_abs c ρ H u v hρ hH hc hu huρ hv hvρ).of_abs

/-- The face series converges absolutely, with the geometric bound
`|c_{ij} v^j| ≤ Hρ^{-i}(v/ρ)^j`. -/
theorem faceU_term_le (c : ℕ × ℕ → ℝ) (ρ H v : ℝ) (hρ : 0 < ρ)
    (hc : ∀ ij, |c ij| * ρ ^ (ij.1 + ij.2) ≤ H) (hv : 0 ≤ v) (i j : ℕ) :
    |c (i, j) * v ^ j| ≤ H * (ρ ^ i)⁻¹ * (v / ρ) ^ j := by
  have h := coeff_term_le c ρ H 1 v hρ hc zero_le_one hv (i, j)
  simp only [one_pow, mul_one] at h
  have h1 : (1 / ρ) ^ i = (ρ ^ i)⁻¹ := by rw [one_div, inv_pow]
  rw [h1] at h
  exact h

theorem faceU_summable_abs (c : ℕ × ℕ → ℝ) (ρ H v : ℝ) (hρ : 0 < ρ)
    (hc : ∀ ij, |c ij| * ρ ^ (ij.1 + ij.2) ≤ H) (hv : 0 ≤ v) (hvρ : v < ρ) (i : ℕ) :
    Summable fun j : ℕ => |c (i, j) * v ^ j| := by
  have hg : Summable fun j : ℕ => H * (ρ ^ i)⁻¹ * (v / ρ) ^ j :=
    (summable_geometric_of_lt_one (by positivity) ((div_lt_one hρ).2 hvρ)).mul_left _
  exact Summable.of_nonneg_of_le (fun j => abs_nonneg _) (faceU_term_le c ρ H v hρ hc hv i) hg

/-- **The face remainder bound**:
`|a_i(v) − ∑_{j<M} c_{ij} v^j| ≤ H ρ^{-i} (v/ρ)^M / (1 − v/ρ)`. -/
theorem faceU_rem_le (c : ℕ × ℕ → ℝ) (ρ H v : ℝ) (hρ : 0 < ρ)
    (hc : ∀ ij, |c ij| * ρ ^ (ij.1 + ij.2) ≤ H) (hv : 0 ≤ v) (hvρ : v < ρ) (i M : ℕ) :
    |faceU c i v - ∑ j ∈ Finset.range M, c (i, j) * v ^ j|
      ≤ H * (ρ ^ i)⁻¹ * (v / ρ) ^ M / (1 - v / ρ) := by
  have hs := (faceU_summable_abs c ρ H v hρ hc hv hvρ i).of_abs
  have hsplit := hs.sum_add_tsum_nat_add M
  unfold faceU
  rw [← hsplit, add_sub_cancel_left]
  have hshift : Summable fun j : ℕ => ‖c (i, j + M) * v ^ (j + M)‖ := by
    have := (faceU_summable_abs c ρ H v hρ hc hv hvρ i)
    have h2 := (summable_nat_add_iff (f := fun j => |c (i, j) * v ^ j|) M).2 this
    simpa [Real.norm_eq_abs] using h2
  refine (norm_tsum_le_tsum_norm hshift).trans ?_
  have hterm : ∀ j : ℕ, ‖c (i, j + M) * v ^ (j + M)‖
      ≤ H * (ρ ^ i)⁻¹ * (v / ρ) ^ M * (v / ρ) ^ j := by
    intro j
    rw [Real.norm_eq_abs]
    have := faceU_term_le c ρ H v hρ hc hv i (j + M)
    rw [pow_add (v / ρ)] at this
    calc |c (i, j + M) * v ^ (j + M)| ≤ H * (ρ ^ i)⁻¹ * ((v / ρ) ^ j * (v / ρ) ^ M) := this
      _ = _ := by ring
  have hgeo : Summable fun j : ℕ => H * (ρ ^ i)⁻¹ * (v / ρ) ^ M * (v / ρ) ^ j :=
    (summable_geometric_of_lt_one (by positivity) ((div_lt_one hρ).2 hvρ)).mul_left _
  calc ∑' j : ℕ, ‖c (i, j + M) * v ^ (j + M)‖
      ≤ ∑' j : ℕ, H * (ρ ^ i)⁻¹ * (v / ρ) ^ M * (v / ρ) ^ j := hshift.tsum_le_tsum hterm hgeo
    _ = H * (ρ ^ i)⁻¹ * (v / ρ) ^ M * (1 - v / ρ)⁻¹ := by
        rw [tsum_mul_left, tsum_geometric_of_lt_one (by positivity) ((div_lt_one hρ).2 hvρ)]
    _ = _ := by ring

/-- **The rectangular identity**: the remainder of the face-jet decomposition is the tail
`∑_{i,j} c_{M₁+i, M₂+j} u^{M₁+i} v^{M₂+j}`. -/
theorem dbl_rect_identity (c : ℕ × ℕ → ℝ) (ρ H u v : ℝ) (hρ : 0 < ρ) (hH : 0 ≤ H)
    (hc : ∀ ij, |c ij| * ρ ^ (ij.1 + ij.2) ≤ H) (hu : 0 ≤ u) (huρ : u < ρ) (hv : 0 ≤ v)
    (hvρ : v < ρ) (M₁ M₂ : ℕ) :
    dblSum c u v - ∑ i ∈ Finset.range M₁, u ^ i * faceU c i v
        - ∑ j ∈ Finset.range M₂, v ^ j * faceV c j u
        + ∑ i ∈ Finset.range M₁, ∑ j ∈ Finset.range M₂, c (i, j) * (u ^ i * v ^ j)
      = ∑' ij : ℕ × ℕ, c (M₁ + ij.1, M₂ + ij.2) * u ^ (M₁ + ij.1) * v ^ (M₂ + ij.2) := by
  set f : ℕ × ℕ → ℝ := fun ij => c ij * u ^ ij.1 * v ^ ij.2 with hf
  have hfs : Summable f := dbl_summable c ρ H u v hρ hH hc hu huρ hv hvρ
  have hfa : Summable fun ij => |f ij| := dbl_summable_abs c ρ H u v hρ hH hc hu huρ hv hvρ
  -- fibre summabilities
  have hrow : ∀ i, Summable fun j => f (i, j) := fun i => hfs.prod_factor i
  have hcol : ∀ j, Summable fun i => f (i, j) := fun j => hfs.prod_symm.prod_factor j
  have hrowabs : ∀ i, Summable fun j => |f (i, j)| := fun i => hfa.prod_factor i
  have hrowsum : Summable fun i => ∑' j, |f (i, j)| :=
    ((summable_prod_of_nonneg (fun ij => abs_nonneg (f ij))).1 hfa).2
  -- the tails
  set T : ℕ → ℝ := fun i => ∑' j, f (i, j + M₂) with hT
  have hTs : Summable T := by
    refine Summable.of_norm_bounded hrowsum fun i => ?_
    have h1 : Summable fun j => ‖f (i, j + M₂)‖ := by
      have := (summable_nat_add_iff (f := fun j => |f (i, j)|) M₂).2 (hrowabs i)
      simpa [Real.norm_eq_abs] using this
    refine (norm_tsum_le_tsum_norm h1).trans ?_
    have h2 := (hrowabs i).sum_add_tsum_nat_add M₂
    have h3 : 0 ≤ ∑ j ∈ Finset.range M₂, |f (i, j)| := Finset.sum_nonneg fun j _ => abs_nonneg _
    simp only [Real.norm_eq_abs]
    linarith
  -- faces as fibre sums
  have hfaceU : ∀ i, u ^ i * faceU c i v = ∑' j, f (i, j) := by
    intro i
    unfold faceU
    rw [← tsum_mul_left]
    exact tsum_congr fun j => by simp only [hf]; ring
  have hfaceV : ∀ j, v ^ j * faceV c j u = ∑' i, f (i, j) := by
    intro j
    unfold faceV
    rw [← tsum_mul_left]
    exact tsum_congr fun i => by simp only [hf]; ring
  -- the double sum as an iterated sum, split at `M₂` in `j`
  have hΦ : dblSum c u v = ∑' i, (∑ j ∈ Finset.range M₂, f (i, j) + T i) := by
    unfold dblSum
    rw [hfs.tsum_prod]
    exact tsum_congr fun i => ((hrow i).sum_add_tsum_nat_add M₂).symm
  have hfin : ∀ j, Summable fun i => f (i, j) := hcol
  have hΦ' : dblSum c u v
      = ∑ j ∈ Finset.range M₂, ∑' i, f (i, j) + ∑' i, T i := by
    rw [hΦ, Summable.tsum_add (summable_sum fun j _ => hfin j) hTs,
      Summable.tsum_finsetSum fun j _ => hfin j]
  -- split the columns at `M₁`
  have hcolsplit : ∀ j, ∑' i, f (i, j)
      = ∑ i ∈ Finset.range M₁, f (i, j) + ∑' i, f (i + M₁, j) := fun j =>
    ((hcol j).sum_add_tsum_nat_add M₁).symm
  -- split the tails at `M₁`
  have hTsplit : ∑' i, T i = ∑ i ∈ Finset.range M₁, T i + ∑' i, T (i + M₁) :=
    (hTs.sum_add_tsum_nat_add M₁).symm
  -- the shifted double tail
  have hshift : Summable fun ij : ℕ × ℕ => f (M₁ + ij.1, M₂ + ij.2) := by
    refine hfs.comp_injective (i := fun ij : ℕ × ℕ => (M₁ + ij.1, M₂ + ij.2)) ?_
    intro a b hab
    simp only [Prod.mk.injEq] at hab
    obtain ⟨h1, h2⟩ := hab
    ext <;> omega
  have htail : ∑' i, T (i + M₁)
      = ∑' ij : ℕ × ℕ, c (M₁ + ij.1, M₂ + ij.2) * u ^ (M₁ + ij.1) * v ^ (M₂ + ij.2) := by
    rw [hshift.tsum_prod]
    refine tsum_congr fun i => ?_
    simp only [hT, hf]
    exact tsum_congr fun j => by rw [add_comm i M₁, add_comm j M₂]
  -- the face sums
  have hA : ∑ i ∈ Finset.range M₁, u ^ i * faceU c i v
      = ∑ i ∈ Finset.range M₁, (∑ j ∈ Finset.range M₂, f (i, j) + T i) := by
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [hfaceU i]
    exact ((hrow i).sum_add_tsum_nat_add M₂).symm
  have hB : ∑ j ∈ Finset.range M₂, v ^ j * faceV c j u
      = ∑ j ∈ Finset.range M₂, (∑ i ∈ Finset.range M₁, f (i, j) + ∑' i, f (i + M₁, j)) := by
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [hfaceV j, hcolsplit j]
  have hC : ∑ i ∈ Finset.range M₁, ∑ j ∈ Finset.range M₂, c (i, j) * (u ^ i * v ^ j)
      = ∑ i ∈ Finset.range M₁, ∑ j ∈ Finset.range M₂, f (i, j) := by
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    simp only [hf]; ring
  rw [hΦ', hA, hB, hC, hTsplit, ← htail]
  simp only [Finset.sum_add_distrib, Finset.sum_congr rfl fun j _ => hcolsplit j]
  rw [Finset.sum_comm (f := fun j i => f (i, j))]
  ring

/-- **The tail bound**:
`|∑ c_{M₁+i,M₂+j} u^{M₁+i} v^{M₂+j}| ≤ H ρ^{-M₁-M₂} u^{M₁} v^{M₂}/((1−u/ρ)(1−v/ρ))`. -/
theorem dbl_tail_le (c : ℕ × ℕ → ℝ) (ρ H u v : ℝ) (hρ : 0 < ρ) (hH : 0 ≤ H)
    (hc : ∀ ij, |c ij| * ρ ^ (ij.1 + ij.2) ≤ H) (hu : 0 ≤ u) (huρ : u < ρ) (hv : 0 ≤ v)
    (hvρ : v < ρ) (M₁ M₂ : ℕ) :
    |∑' ij : ℕ × ℕ, c (M₁ + ij.1, M₂ + ij.2) * u ^ (M₁ + ij.1) * v ^ (M₂ + ij.2)|
      ≤ H * (ρ ^ (M₁ + M₂))⁻¹ * (u ^ M₁ * v ^ M₂) / ((1 - u / ρ) * (1 - v / ρ)) := by
  set A : ℝ := H * (ρ ^ (M₁ + M₂))⁻¹ * (u ^ M₁ * v ^ M₂) with hA
  have hA0 : 0 ≤ A := by positivity
  have hd : ∀ ij : ℕ × ℕ, |c (M₁ + ij.1, M₂ + ij.2) * u ^ (M₁ + ij.1) * v ^ (M₂ + ij.2)|
      ≤ A * (u / ρ) ^ ij.1 * (v / ρ) ^ ij.2 := by
    intro ij
    have h := coeff_term_le c ρ H u v hρ hc hu hv (M₁ + ij.1, M₂ + ij.2)
    simp only at h
    refine h.trans (le_of_eq ?_)
    rw [hA]
    simp only [div_pow, pow_add]
    field_simp
    try ring
  obtain ⟨hs, hle⟩ := summable_abs_of_geom _ A (u / ρ) (v / ρ) hA0 (by positivity)
    ((div_lt_one hρ).2 huρ) (by positivity) ((div_lt_one hρ).2 hvρ) hd
  have hs' : Summable fun ij : ℕ × ℕ =>
      ‖c (M₁ + ij.1, M₂ + ij.2) * u ^ (M₁ + ij.1) * v ^ (M₂ + ij.2)‖ := by
    simpa [Real.norm_eq_abs] using hs
  calc |∑' ij : ℕ × ℕ, c (M₁ + ij.1, M₂ + ij.2) * u ^ (M₁ + ij.1) * v ^ (M₂ + ij.2)|
      ≤ ∑' ij : ℕ × ℕ, |c (M₁ + ij.1, M₂ + ij.2) * u ^ (M₁ + ij.1) * v ^ (M₂ + ij.2)| := by
        have := norm_tsum_le_tsum_norm hs'
        simpa [Real.norm_eq_abs] using this
    _ ≤ A / ((1 - u / ρ) * (1 - v / ρ)) := hle

end Laplace.Grammar
