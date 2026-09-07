/-
Copyright (c) 2026 Daniel Murfet. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniel Murfet
-/
import Laplace.Grammar.MonomialMixedAsymptotic

/-!
# Cutoff scaling for the normal moment integral

The paper's bare normal moment integral lives on the box `[0,b]^{|I|}` with an arbitrary cutoff
`b > 0`; the monomial milestones (units 175, 181) are stated on the unit box. The substitution
`u = b v` gives the exact identity

  `∫_{(0,b]^d} u^h e^{-βN u^{2k}} du = b^{∑(hᵢ+1)} · ∫_{(0,1]^d} v^h e^{-β (N b^{2∑kᵢ}) v^{2k}} dv`

(`monomialBoxRealCutoff_eq`), so every unit-box asymptotic transfers: the cutoff multiplies the
leading constant by `b^{∑ᵢ(hᵢ+1-2kᵢλ)} = ∏_{i∉J} b^{hᵢ+1-2kᵢλ}` — exactly the `b`-dependence of the
paper's Laurent coefficient `a_{-|J|}` (eq. `a_minus_m_explicit`), and no `b`-dependence at all in
the equal-ratio case (`monomialBoxRealCutoff_mixed_isEquivalent`,
`monomialBoxRealCutoff_equal_isEquivalent`).
-/

open MeasureTheory Set Filter Topology Asymptotics
open scoped Pointwise

namespace Laplace.Grammar

/-- The box `(0,b]^d`. -/
def cutoffBox (d : ℕ) (b : ℝ) : Set (Fin d → ℝ) := Set.pi univ fun _ => Ioc (0 : ℝ) b

theorem cutoffBox_eq_smul (d : ℕ) (b : ℝ) (hb : 0 < b) : cutoffBox d b = b • unitBox d := by
  ext x
  simp only [cutoffBox, unitBox, Set.mem_smul_set, Set.mem_pi, Set.mem_univ, true_implies,
    Set.mem_Ioc]
  constructor
  · intro hx
    refine ⟨b⁻¹ • x, fun i => ?_, by rw [smul_smul, mul_inv_cancel₀ hb.ne', one_smul]⟩
    simp only [Pi.smul_apply, smul_eq_mul]
    exact ⟨mul_pos (inv_pos.2 hb) (hx i).1, by rw [inv_mul_le_iff₀ hb, mul_one]; exact (hx i).2⟩
  · rintro ⟨y, hy, rfl⟩ i
    simp only [Pi.smul_apply, smul_eq_mul]
    exact ⟨mul_pos hb (hy i).1, mul_le_of_le_one_right hb.le (hy i).2⟩

/-- The monomial box integral with cutoff `b`. -/
noncomputable def monomialBoxRealCutoff (d : ℕ) (h k : Fin d → ℕ) (b β N : ℝ) : ℝ :=
  ∫ x in cutoffBox d b, (∏ i, x i ^ h i) * Real.exp (-(β * N * ∏ i, x i ^ (2 * k i)))

/-- **Cutoff scaling**: `M_b(N) = b^{∑(hᵢ+1)} M_1(N b^{2∑kᵢ})`. -/
theorem monomialBoxRealCutoff_eq (d : ℕ) (h k : Fin d → ℕ) (b β N : ℝ) (hb : 0 < b) :
    monomialBoxRealCutoff d h k b β N =
      b ^ (∑ i, (h i + 1)) * monomialBoxReal d h k β (N * b ^ (2 * ∑ i, k i)) := by
  unfold monomialBoxRealCutoff monomialBoxReal
  rw [cutoffBox_eq_smul d b hb]
  set f : (Fin d → ℝ) → ℝ := fun x =>
    (∏ i, x i ^ h i) * Real.exp (-(β * N * ∏ i, x i ^ (2 * k i))) with hf
  have h1 := MeasureTheory.Measure.setIntegral_comp_smul_of_pos volume f (unitBox d) hb
  rw [Module.finrank_fin_fun, smul_eq_mul] at h1
  have h2 : ∫ x in b • unitBox d, f x = b ^ d * ∫ x in unitBox d, f (b • x) := by
    rw [h1, ← mul_assoc, mul_inv_cancel₀ (pow_ne_zero _ hb.ne'), one_mul]
  have h3 : ∫ x in unitBox d, f (b • x) = b ^ (∑ i, h i) *
      ∫ x in unitBox d, (∏ i, x i ^ h i) *
        Real.exp (-(β * (N * b ^ (2 * ∑ i, k i)) * ∏ i, x i ^ (2 * k i))) := by
    rw [← integral_const_mul]
    refine setIntegral_congr_fun (measurableSet_unitBox d) fun x _ => ?_
    simp only [hf, Pi.smul_apply, smul_eq_mul, mul_pow, Finset.prod_mul_distrib,
      Finset.prod_pow_eq_pow_sum]
    rw [← Finset.mul_sum]
    ring_nf
  change ∫ x in b • unitBox d, f x = _
  rw [h2, h3, Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
    smul_eq_mul, mul_one, pow_add]
  ring

/-- The cutoff power `b^{∑(hᵢ+1) - 2λ∑kᵢ}` as a product of the two scaling factors. -/
theorem cutoff_power_eq (d : ℕ) (h k : Fin d → ℕ) (b l : ℝ) (hb : 0 < b) :
    b ^ (((∑ i, (h i + 1) : ℕ) : ℝ) - 2 * l * ((∑ i, k i : ℕ) : ℝ)) =
      b ^ (∑ i, (h i + 1)) * (b ^ (2 * ∑ i, k i)) ^ (-l) := by
  rw [← Real.rpow_natCast b (∑ i, (h i + 1)), ← Real.rpow_natCast b (2 * ∑ i, k i),
    ← Real.rpow_mul hb.le, ← Real.rpow_add hb]
  congr 1
  push_cast
  ring

/-- `(log (N c) / log N)^r → 1` for a fixed scale `c > 0`. -/
theorem tendsto_log_scale_pow (c : ℝ) (hc : 0 < c) (r : ℕ) :
    Tendsto (fun N => (Real.log (N * c) / Real.log N) ^ r) atTop (𝓝 1) := by
  have h1 := (Real.tendsto_log_atTop.inv_tendsto_atTop).const_mul (Real.log c)
  rw [mul_zero] at h1
  have h2 := (tendsto_const_nhds (x := (1 : ℝ))).add h1
  rw [add_zero] at h2
  have h3 : Tendsto (fun N => (1 + Real.log c * (Real.log N)⁻¹) ^ r) atTop (𝓝 1) := by
    simpa using h2.pow r
  refine h3.congr' ?_
  filter_upwards [eventually_gt_atTop (1 : ℝ)] with N hN
  have hN0 : 0 < N := by linarith
  have hlog : Real.log N ≠ 0 := (Real.log_pos hN).ne'
  rw [Real.log_mul hN0.ne' hc.ne']
  field_simp

/-- **Mixed-ratio asymptotic with cutoff (ratio form)**: the leading constant acquires the factor
`b^{∑ᵢ(hᵢ+1) - 2λ∑ᵢkᵢ} = ∏_{i∉J} b^{hᵢ+1-2kᵢλ}`. -/
theorem monomialBoxRealCutoff_mixed_tendsto (d : ℕ) (h k : Fin (d + 1) → ℕ)
    (hk : ∀ i, 0 < k i) (b l β : ℝ) (hb : 0 < b) (hl : 0 < l) (hβ : 0 < β)
    (hmin : ∀ i, l ≤ ratioExp h k i) (hatt : ∃ i, ratioExp h k i = l) :
    Tendsto (fun N => monomialBoxRealCutoff (d + 1) h k b β N /
        (N ^ (-l) * Real.log N ^ (multCount (ratioExp h k) l - 1))) atTop
      (𝓝 (b ^ (((∑ i, (h i + 1) : ℕ) : ℝ) - 2 * l * ((∑ i, k i : ℕ) : ℝ)) *
        monomialMixedConst h k l β)) := by
  set c : ℝ := b ^ (2 * ∑ i, k i) with hc
  have hc0 : 0 < c := by positivity
  set r : ℕ := multCount (ratioExp h k) l - 1 with hr
  have hT := monomialBoxReal_mixed_tendsto d h k hk l β hl hβ hmin hatt
  have hT' : Tendsto (fun N => monomialBoxReal (d + 1) h k β (N * c) /
      ((N * c) ^ (-l) * Real.log (N * c) ^ r)) atTop (𝓝 (monomialMixedConst h k l β)) :=
    hT.comp (tendsto_id.atTop_mul_const hc0)
  have hprod := (hT'.mul (tendsto_log_scale_pow c hc0 r)).const_mul
    (b ^ (∑ i, (h i + 1)) * c ^ (-l))
  rw [mul_one] at hprod
  rw [cutoff_power_eq (d + 1) h k b l hb, ← hc]
  refine hprod.congr' ?_
  filter_upwards [eventually_gt_atTop (max 1 (1 / c))] with N hN
  have hN1 : 1 < N := lt_of_le_of_lt (le_max_left _ _) hN
  have hN0 : 0 < N := by linarith
  have hNc : 1 < N * c := by
    have : 1 / c < N := lt_of_le_of_lt (le_max_right _ _) hN
    rwa [div_lt_iff₀ hc0] at this
  have hlogN : Real.log N ≠ 0 := (Real.log_pos hN1).ne'
  have hlogNc : Real.log (N * c) ≠ 0 := (Real.log_pos hNc).ne'
  have hpN : N ^ (-l) ≠ 0 := (Real.rpow_pos_of_pos hN0 _).ne'
  have hpc : c ^ (-l) ≠ 0 := (Real.rpow_pos_of_pos hc0 _).ne'
  have hlogNr : Real.log N ^ r ≠ 0 := pow_ne_zero _ hlogN
  have hlogNcr : Real.log (N * c) ^ r ≠ 0 := pow_ne_zero _ hlogNc
  rw [monomialBoxRealCutoff_eq (d + 1) h k b β N hb, ← hc, Real.mul_rpow hN0.le hc0.le, div_pow]
  field_simp

/-- **Mixed-ratio asymptotic with cutoff (equivalence form)**. -/
theorem monomialBoxRealCutoff_mixed_isEquivalent (d : ℕ) (h k : Fin (d + 1) → ℕ)
    (hk : ∀ i, 0 < k i) (b l β : ℝ) (hb : 0 < b) (hl : 0 < l) (hβ : 0 < β)
    (hmin : ∀ i, l ≤ ratioExp h k i) (hatt : ∃ i, ratioExp h k i = l) :
    (fun N => monomialBoxRealCutoff (d + 1) h k b β N) ~[atTop]
      fun N => b ^ (((∑ i, (h i + 1) : ℕ) : ℝ) - 2 * l * ((∑ i, k i : ℕ) : ℝ)) *
        monomialMixedConst h k l β * N ^ (-l) *
        Real.log N ^ (multCount (ratioExp h k) l - 1) := by
  have hC : 0 < b ^ (((∑ i, (h i + 1) : ℕ) : ℝ) - 2 * l * ((∑ i, k i : ℕ) : ℝ)) *
      monomialMixedConst h k l β :=
    mul_pos (Real.rpow_pos_of_pos hb _) (monomialMixedConst_pos h k hk l β hl hβ hmin)
  refine isEquivalent_of_tendsto_one ?_
  have hT := (monomialBoxRealCutoff_mixed_tendsto d h k hk b l β hb hl hβ hmin hatt).div_const
    (b ^ (((∑ i, (h i + 1) : ℕ) : ℝ) - 2 * l * ((∑ i, k i : ℕ) : ℝ)) * monomialMixedConst h k l β)
  rw [div_self hC.ne'] at hT
  refine hT.congr' ?_
  filter_upwards [eventually_gt_atTop (1 : ℝ)] with N hN
  have hN0 : 0 < N := by linarith
  have hpow : N ^ (-l) ≠ 0 := (Real.rpow_pos_of_pos hN0 _).ne'
  have hlog : Real.log N ^ (multCount (ratioExp h k) l - 1) ≠ 0 :=
    pow_ne_zero _ (Real.log_pos hN).ne'
  simp only [Pi.div_apply]
  field_simp

/-- In the **equal-ratio** case the cutoff power is `b^0 = 1`: the leading constant is independent
of the cutoff. -/
theorem cutoff_power_eq_one_of_equal (d : ℕ) (h k : Fin d → ℕ) (hk : ∀ i, 0 < k i) (l : ℝ)
    (hratio : ∀ i, ratioExp h k i = l) :
    ((∑ i, (h i + 1) : ℕ) : ℝ) - 2 * l * ((∑ i, k i : ℕ) : ℝ) = 0 := by
  push_cast
  rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
  refine Finset.sum_eq_zero fun i _ => ?_
  have hki : (k i : ℝ) ≠ 0 := Nat.cast_ne_zero.2 (hk i).ne'
  have := hratio i
  unfold ratioExp at this
  field_simp at this
  linarith

end Laplace.Grammar
