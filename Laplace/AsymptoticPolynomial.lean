/-
Copyright (c) 2026 Timaeus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib

/-!
# Asymptotic polynomials at the origin

Stage 1 of the germbij forward-expansion programme: the expansion
predicate and coefficient uniqueness. `IsAsymptoticExpansionTo f c N`
says the function `f` of the scale `q` agrees with the degree-`N`
polynomial with coefficients `c` up to `o(q^N)` at `0⁺`. Coefficients
are unique through order `N` (`isAsymptoticExpansionTo_coeff_eq`):
divide by `q^j`, the polynomial part tends to the `j`-th coefficient
gap while the error tends to zero, and limits are unique. The
uniqueness lemma is Laplace-independent and canonicalizes any later
choice-based coefficient function.
-/

open Filter Topology Asymptotics

namespace Laplace

/-- `f` admits the degree-`N` asymptotic polynomial with coefficients
`c` at `0⁺`. -/
def IsAsymptoticExpansionTo (f : ℝ → ℝ) (c : ℕ → ℝ) (N : ℕ) : Prop :=
  (fun q : ℝ ↦ f q - ∑ j ∈ Finset.range (N + 1), c j * q ^ j)
    =o[𝓝[>] (0 : ℝ)] fun q : ℝ ↦ q ^ N

/-- The tail of a polynomial above a fixed index, divided by the
power at that index, tends to the coefficient at the index. -/
theorem tendsto_poly_div_pow {N : ℕ} (e : ℕ → ℝ) {j₀ : ℕ}
    (hj₀ : j₀ ≤ N) (hlow : ∀ i < j₀, e i = 0) :
    Tendsto (fun q : ℝ ↦
      (∑ j ∈ Finset.range (N + 1), e j * q ^ j) / q ^ j₀)
      (𝓝[>] (0 : ℝ)) (𝓝 (e j₀)) := by
  have hev : (fun q : ℝ ↦
      ∑ j ∈ Finset.range (N + 1), e j * q ^ (j - j₀) *
        (if j < j₀ then (0:ℝ) else 1))
      =ᶠ[𝓝[>] (0 : ℝ)]
      fun q : ℝ ↦
        (∑ j ∈ Finset.range (N + 1), e j * q ^ j) / q ^ j₀ := by
    filter_upwards [self_mem_nhdsWithin] with q hq
    have hq0 : (q : ℝ) ≠ 0 := ne_of_gt hq
    rw [Finset.sum_div]
    refine Finset.sum_congr rfl fun j hj ↦ ?_
    by_cases hlt : j < j₀
    · rw [if_pos hlt, hlow j hlt]
      ring
    · rw [if_neg hlt, mul_one]
      push Not at hlt
      rw [mul_div_assoc]
      congr 1
      rw [eq_div_iff (pow_ne_zero j₀ hq0), ← pow_add]
      congr 1
      omega
  have hterm : Tendsto (fun q : ℝ ↦
      ∑ j ∈ Finset.range (N + 1), e j * q ^ (j - j₀) *
        (if j < j₀ then (0:ℝ) else 1))
      (𝓝[>] (0 : ℝ)) (𝓝 (e j₀)) := by
    have hsum : Tendsto (fun q : ℝ ↦
        ∑ j ∈ Finset.range (N + 1), e j * q ^ (j - j₀) *
          (if j < j₀ then (0:ℝ) else 1))
        (𝓝 (0 : ℝ))
        (𝓝 (∑ j ∈ Finset.range (N + 1), e j * (0:ℝ) ^ (j - j₀) *
          (if j < j₀ then (0:ℝ) else 1))) := by
      refine tendsto_finset_sum _ fun j hj ↦ ?_
      exact (((continuous_pow (j - j₀)).tendsto (0:ℝ)).const_mul
        (e j)).mul_const _
    have hval : ∑ j ∈ Finset.range (N + 1),
        e j * (0:ℝ) ^ (j - j₀) * (if j < j₀ then (0:ℝ) else 1) =
        e j₀ := by
      rw [Finset.sum_eq_single j₀]
      · rw [Nat.sub_self, pow_zero, mul_one, if_neg (lt_irrefl j₀),
          mul_one]
      · intro j hj hne
        rcases lt_or_gt_of_ne hne with hlt | hgt
        · rw [if_pos hlt, mul_zero]
        · rw [zero_pow (by omega : j - j₀ ≠ 0)]
          ring
      · intro hj
        exact absurd (Finset.mem_range.mpr (by omega)) hj
    rw [hval] at hsum
    exact hsum.mono_left nhdsWithin_le_nhds
  exact hterm.congr' hev

/-- **Coefficient uniqueness**: two coefficient systems expanding the
same function to order `N` agree through order `N`. -/
theorem isAsymptoticExpansionTo_coeff_eq {f : ℝ → ℝ} {c e : ℕ → ℝ}
    {N : ℕ}
    (hc : IsAsymptoticExpansionTo f c N)
    (he : IsAsymptoticExpansionTo f e N) :
    ∀ j ≤ N, c j = e j := by
  have hdiff : (fun q : ℝ ↦
      ∑ j ∈ Finset.range (N + 1), (c j - e j) * q ^ j)
      =o[𝓝[>] (0 : ℝ)] fun q : ℝ ↦ q ^ N := by
    have h := he.sub hc
    refine h.congr' ?_ (Filter.EventuallyEq.refl _ _)
    filter_upwards with q
    have hswap : (f q - ∑ j ∈ Finset.range (N + 1), e j * q ^ j) -
        (f q - ∑ j ∈ Finset.range (N + 1), c j * q ^ j) =
        (∑ j ∈ Finset.range (N + 1), c j * q ^ j) -
        ∑ j ∈ Finset.range (N + 1), e j * q ^ j := by ring
    rw [hswap, ← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun j _ ↦ by ring
  intro j₀ hj₀
  induction j₀ using Nat.strong_induction_on with
  | _ j₀ ih =>
    have hlow : ∀ i < j₀, (fun j ↦ c j - e j) i = 0 := by
      intro i hi
      have := ih i hi (by omega)
      simp only []
      linarith
    have hpoly := tendsto_poly_div_pow (fun j ↦ c j - e j) hj₀ hlow
    have hzero : Tendsto (fun q : ℝ ↦
        (∑ j ∈ Finset.range (N + 1), (c j - e j) * q ^ j) / q ^ j₀)
        (𝓝[>] (0 : ℝ)) (𝓝 0) := by
      have hlittle : (fun q : ℝ ↦
          (∑ j ∈ Finset.range (N + 1), (c j - e j) * q ^ j) / q ^ j₀)
          =o[𝓝[>] (0 : ℝ)] fun q : ℝ ↦ q ^ (N - j₀) := by
        have := hdiff.mul_isBigO
          (isBigO_refl (fun q : ℝ ↦ ((q ^ j₀)⁻¹ : ℝ)) (𝓝[>] (0:ℝ)))
        refine this.congr' ?_ ?_
        · filter_upwards with q
          rw [div_eq_mul_inv]
        · filter_upwards [self_mem_nhdsWithin] with q hq
          have hq0 : (q : ℝ) ≠ 0 := ne_of_gt hq
          exact (pow_sub₀ q hq0 hj₀).symm
      have hbound : (fun q : ℝ ↦ (q : ℝ) ^ (N - j₀)) =O[𝓝[>] (0:ℝ)]
          fun _ : ℝ ↦ (1 : ℝ) := by
        rw [isBigO_iff]
        refine ⟨1, ?_⟩
        filter_upwards [Ioo_mem_nhdsGT (one_pos : (0:ℝ) < 1)]
          with q hq
        obtain ⟨hq0, hq1⟩ := hq
        rw [Real.norm_eq_abs, Real.norm_eq_abs,
          abs_of_pos (pow_pos hq0 _), abs_one, one_mul]
        exact pow_le_one₀ hq0.le hq1.le
      exact (isLittleO_one_iff ℝ).mp (hlittle.trans_isBigO hbound)
    have := tendsto_nhds_unique hpoly hzero
    linarith

end Laplace
