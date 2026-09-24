/-
Copyright (c) 2026 Timaeus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Timaeus
-/
import Mathlib

/-!
# The polytope-fibre asymptotic

The reusable core of the transverse active-truth face theorem (Astra, round 7): in logarithmic
coordinates the fibre of the two transverse constraints at scale `L = log t` is the polytope
`{z ≥ 0 | c₁·z ≤ a₁L + b₁, c₂·z ≤ a₂L + b₂}` in the `k` free coordinates, whose volume is
`L^k` times the volume of `{α ≥ 0 | c₁·α ≤ a₁ + b₁/L, c₂·α ≤ a₂ + b₂/L}` (`volume_fibre2`), and the
latter converges to the volume of the limiting face polytope `{α ≥ 0 | c₁·α ≤ a₁, c₂·α ≤ a₂}`
(`tendsto_volume_poly2`, dominated convergence of indicators off the null hyperplanes, for
nonzero `c₁, c₂` and a bounded enlarged polytope). So the fibre volume is `L^k · vol(F') + o(L^k)`:
the logarithmic exponent is the dimension of the optimal face, with the face volume in the
projected coordinates (the Jacobian of the projection replaces the coarea factor `H^k(F_J)/𝒥`).
-/

open Real MeasureTheory Set Filter Topology
open scoped ENNReal Matrix Pointwise

namespace Laplace.Multi

variable {k : ℕ}

/-- The linear functional `y ↦ c ⬝ᵥ y`. -/
def dotLin (c : Fin k → ℝ) : (Fin k → ℝ) →ₗ[ℝ] ℝ where
  toFun y := c ⬝ᵥ y
  map_add' x y := dotProduct_add c x y
  map_smul' r y := dotProduct_smul r c y

theorem dotLin_apply (c y : Fin k → ℝ) : dotLin c y = c ⬝ᵥ y := rfl

/-- A hyperplane `{c·x = a}`, `c ≠ 0`, is Lebesgue-null. -/
theorem volume_hyperplane {c : Fin k → ℝ} (hc : c ≠ 0) (a : ℝ) :
    volume {x : Fin k → ℝ | c ⬝ᵥ x = a} = 0 := by
  have hcc : c ⬝ᵥ c ≠ 0 := fun h ↦ hc (dotProduct_self_eq_zero.mp h)
  obtain ⟨x₀, hx₀⟩ : ∃ x₀ : Fin k → ℝ, c ⬝ᵥ x₀ = a :=
    ⟨(a / (c ⬝ᵥ c)) • c, by rw [dotProduct_smul, smul_eq_mul, div_mul_cancel₀ _ hcc]⟩
  have hset : {x : Fin k → ℝ | c ⬝ᵥ x = a} =
      (fun x ↦ x + (-x₀)) ⁻¹' (LinearMap.ker (dotLin c) : Set (Fin k → ℝ)) := by
    ext x
    simp only [Set.mem_ofPred_eq, mem_preimage, SetLike.mem_coe, LinearMap.mem_ker, dotLin_apply,
      dotProduct_add, dotProduct_neg, hx₀]
    constructor
    · intro h
      linarith
    · intro h
      linarith
  rw [hset, measure_preimage_add_right]
  refine Measure.addHaar_submodule volume _ fun h ↦ hc ?_
  have : c ∈ LinearMap.ker (dotLin c) := by
    rw [h]
    exact Submodule.mem_top
  rw [LinearMap.mem_ker, dotLin_apply] at this
  exact dotProduct_self_eq_zero.mp this

/-- A hyperplane `{c·x = a}` with `(c, a) ≠ (0, 0)` is Lebesgue-null (empty when `c = 0`). -/
theorem volume_hyperplane' {c : Fin k → ℝ} {a : ℝ} (h : c ≠ 0 ∨ a ≠ 0) :
    volume {x : Fin k → ℝ | c ⬝ᵥ x = a} = 0 := by
  by_cases hc : c = 0
  · have ha : a ≠ 0 := h.resolve_left (not_not.mpr hc)
    have : {x : Fin k → ℝ | c ⬝ᵥ x = a} = ∅ := by
      ext x
      simp [hc, ha.symm]
    rw [this, measure_empty]
  · exact volume_hyperplane hc a

/-- The coordinate hyperplane `{x i = 0}` is null. -/
theorem volume_coordHyperplane (i : Fin k) : volume {x : Fin k → ℝ | x i = 0} = 0 := by
  have := volume_hyperplane (c := Pi.single i 1) (by simp) 0
  simpa [single_dotProduct] using this

/-- The polytope of the two transverse constraints in the free coordinates. -/
def poly2 (c₁ c₂ : Fin k → ℝ) (a₁ a₂ : ℝ) : Set (Fin k → ℝ) :=
  {x | (∀ i, 0 ≤ x i) ∧ c₁ ⬝ᵥ x ≤ a₁ ∧ c₂ ⬝ᵥ x ≤ a₂}

variable {c₁ c₂ : Fin k → ℝ} {a₁ a₂ : ℝ}

theorem measurable_dotProduct_left (c : Fin k → ℝ) : Measurable fun x : Fin k → ℝ ↦ c ⬝ᵥ x :=
  (dotLin c).continuous_of_finiteDimensional.measurable

theorem measurableSet_poly2 : MeasurableSet (poly2 c₁ c₂ a₁ a₂) := by
  have h0 : MeasurableSet {x : Fin k → ℝ | ∀ i, 0 ≤ x i} := by
    have : {x : Fin k → ℝ | ∀ i, 0 ≤ x i} = Set.pi univ fun _ ↦ Ici (0 : ℝ) := by
      ext x
      simp only [Set.mem_univ_pi, mem_Ici, Set.mem_ofPred_eq]
    rw [this]
    exact MeasurableSet.pi countable_univ fun _ _ ↦ measurableSet_Ici
  exact h0.inter ((measurableSet_le (measurable_dotProduct_left c₁) measurable_const).inter
    (measurableSet_le (measurable_dotProduct_left c₂) measurable_const))

theorem poly2_mono {a₁' a₂' : ℝ} (h₁ : a₁ ≤ a₁') (h₂ : a₂ ≤ a₂') :
    poly2 c₁ c₂ a₁ a₂ ⊆ poly2 c₁ c₂ a₁' a₂' := fun _ hx ↦
  ⟨hx.1, hx.2.1.trans h₁, hx.2.2.trans h₂⟩

/-- The fibre at scale `L`: `{z ≥ 0 | c₁·z ≤ a₁L + b₁, c₂·z ≤ a₂L + b₂}`. -/
def fibre2 (c₁ c₂ : Fin k → ℝ) (a₁ a₂ b₁ b₂ L : ℝ) : Set (Fin k → ℝ) :=
  {z | (∀ i, 0 ≤ z i) ∧ c₁ ⬝ᵥ z ≤ a₁ * L + b₁ ∧ c₂ ⬝ᵥ z ≤ a₂ * L + b₂}

/-- The fibre is the scaled polytope. -/
theorem fibre2_eq_smul {b₁ b₂ L : ℝ} (hL : 0 < L) :
    fibre2 c₁ c₂ a₁ a₂ b₁ b₂ L = L • poly2 c₁ c₂ (a₁ + b₁ / L) (a₂ + b₂ / L) := by
  ext z
  rw [Set.mem_smul_set_iff_inv_smul_mem₀ hL.ne']
  have key : ∀ (c : Fin k → ℝ) (a b : ℝ), c ⬝ᵥ (L⁻¹ • z) ≤ a + b / L ↔ c ⬝ᵥ z ≤ a * L + b := by
    intro c a b
    rw [dotProduct_smul, smul_eq_mul, inv_mul_le_iff₀ hL]
    have : L * (a + b / L) = a * L + b := by field_simp
    rw [this]
  have hpos : (∀ i, 0 ≤ (L⁻¹ • z) i) ↔ ∀ i, 0 ≤ z i := by
    refine forall_congr' fun i ↦ ?_
    rw [Pi.smul_apply, smul_eq_mul]
    exact ⟨fun h ↦ nonneg_of_mul_nonneg_right h (inv_pos.mpr hL),
      fun h ↦ mul_nonneg (inv_pos.mpr hL).le h⟩
  simp only [fibre2, poly2, Set.mem_ofPred_eq, hpos, key]

/-- The volume of the fibre is `L^k` times the volume of the scaled polytope. -/
theorem volume_fibre2 {b₁ b₂ L : ℝ} (hL : 0 < L) :
    volume (fibre2 c₁ c₂ a₁ a₂ b₁ b₂ L) =
      ENNReal.ofReal (L ^ k) * volume (poly2 c₁ c₂ (a₁ + b₁ / L) (a₂ + b₂ / L)) := by
  rw [fibre2_eq_smul hL, Measure.addHaar_smul, Module.finrank_fin_fun, abs_of_pos (pow_pos hL _)]

/-- **The polytope-fibre asymptotic.** For nondegenerate constraints (`(c_j, a_j) ≠ (0, 0)`) and a
bounded enlarged polytope, the
volume of `{α ≥ 0 | c₁·α ≤ a₁ + b₁/L, c₂·α ≤ a₂ + b₂/L}` converges to the volume of the limiting
polytope `{α ≥ 0 | c₁·α ≤ a₁, c₂·α ≤ a₂}`. -/
theorem tendsto_volume_poly2 (hc₁ : c₁ ≠ 0 ∨ a₁ ≠ 0) (hc₂ : c₂ ≠ 0 ∨ a₂ ≠ 0) (b₁ b₂ : ℝ)
    (hbdd : Bornology.IsBounded (poly2 c₁ c₂ (a₁ + 1) (a₂ + 1))) :
    Tendsto (fun L ↦ volume (poly2 c₁ c₂ (a₁ + b₁ / L) (a₂ + b₂ / L))) atTop
      (𝓝 (volume (poly2 c₁ c₂ a₁ a₂))) := by
  simp_rw [← lintegral_indicator_one (μ := volume) (measurableSet_poly2 (c₁ := c₁) (c₂ := c₂))]
  refine tendsto_lintegral_filter_of_dominated_convergence
    ((poly2 c₁ c₂ (a₁ + 1) (a₂ + 1)).indicator 1)
    (Eventually.of_forall fun L ↦ measurable_const.indicator measurableSet_poly2) ?_ ?_ ?_
  · filter_upwards [eventually_ge_atTop (max 1 (max |b₁| |b₂|))] with L hL
    have hL1 : 1 ≤ L := (le_max_left _ _).trans hL
    have hb : ∀ b : ℝ, |b| ≤ L → b / L ≤ 1 := fun b hbL ↦ by
      rw [div_le_one (zero_lt_one.trans_le hL1)]
      exact (le_abs_self b).trans hbL
    refine Eventually.of_forall fun x ↦ ?_
    refine Set.indicator_le_indicator_of_subset (poly2_mono ?_ ?_) (fun _ ↦ zero_le) x
    · exact add_le_add le_rfl (hb b₁ ((le_max_left _ _).trans ((le_max_right _ _).trans hL)))
    · exact add_le_add le_rfl (hb b₂ ((le_max_right _ _).trans ((le_max_right _ _).trans hL)))
  · rw [lintegral_indicator_one measurableSet_poly2]
    exact hbdd.measure_lt_top.ne
  · have hnull : volume ({x : Fin k → ℝ | c₁ ⬝ᵥ x = a₁} ∪ {x | c₂ ⬝ᵥ x = a₂} ∪
        ⋃ i, {x : Fin k → ℝ | x i = 0}) = 0 := by
      refine measure_union_null (measure_union_null (volume_hyperplane' hc₁)
        (volume_hyperplane' hc₂)) (measure_iUnion_null fun i ↦ volume_coordHyperplane i)
    filter_upwards [compl_mem_ae_iff.mpr hnull] with x hx
    simp only [mem_compl_iff, mem_union, mem_iUnion, Set.mem_ofPred_eq, not_or, not_exists] at hx
    obtain ⟨⟨hx1, hx2⟩, hx0⟩ := hx
    have h1 : Tendsto (fun L ↦ a₁ + b₁ / L) atTop (𝓝 a₁) := by
      have := (tendsto_const_nhds (x := b₁)).div_atTop tendsto_id
      simpa using (tendsto_const_nhds (x := a₁)).add this
    have h2 : Tendsto (fun L ↦ a₂ + b₂ / L) atTop (𝓝 a₂) := by
      have := (tendsto_const_nhds (x := b₂)).div_atTop tendsto_id
      simpa using (tendsto_const_nhds (x := a₂)).add this
    by_cases hxP : x ∈ poly2 c₁ c₂ a₁ a₂
    · rw [Set.indicator_of_mem hxP]
      have hlt1 : c₁ ⬝ᵥ x < a₁ := lt_of_le_of_ne hxP.2.1 hx1
      have hlt2 : c₂ ⬝ᵥ x < a₂ := lt_of_le_of_ne hxP.2.2 hx2
      refine tendsto_const_nhds.congr' ?_
      filter_upwards [h1.eventually_const_lt hlt1, h2.eventually_const_lt hlt2] with L hL1 hL2
      rw [Set.indicator_of_mem (show x ∈ poly2 c₁ c₂ (a₁ + b₁ / L) (a₂ + b₂ / L) from
        ⟨hxP.1, hL1.le, hL2.le⟩)]
    · rw [Set.indicator_of_notMem hxP]
      refine tendsto_const_nhds.congr' ?_
      have hcases : (∃ i, x i < 0) ∨ a₁ < c₁ ⬝ᵥ x ∨ a₂ < c₂ ⬝ᵥ x := by
        by_contra h
        push Not at h
        exact hxP ⟨h.1, h.2.1, h.2.2⟩
      rcases hcases with ⟨i, hi⟩ | h | h
      · refine Eventually.of_forall fun L ↦ ?_
        beta_reduce
        rw [Set.indicator_of_notMem (fun hm : x ∈ poly2 c₁ c₂ (a₁ + b₁ / L) (a₂ + b₂ / L) ↦
          absurd (hm.1 i) (not_le.mpr hi))]
      · filter_upwards [h1.eventually_lt_const h] with L hL
        rw [Set.indicator_of_notMem (fun hm : x ∈ poly2 c₁ c₂ (a₁ + b₁ / L) (a₂ + b₂ / L) ↦
          absurd hm.2.1 (not_le.mpr hL))]
      · filter_upwards [h2.eventually_lt_const h] with L hL
        rw [Set.indicator_of_notMem (fun hm : x ∈ poly2 c₁ c₂ (a₁ + b₁ / L) (a₂ + b₂ / L) ↦
          absurd hm.2.2 (not_le.mpr hL))]

end Laplace.Multi
