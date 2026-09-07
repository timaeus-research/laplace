/-
Copyright (c) 2026 Timaeus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Laplace.Grammar.FamilyTaylorTree
import Laplace.Grammar.BoxPeel

/-!
# Scaling to a general box side `b` (Stage 4h)

Unit 248 (Taylor-tree programme; Astra #28 candidate D). The paper's standard integral lives on
`[0,b]^d`; substituting `u = b v` gives the exact identity
```
Z_b(N; ξ, η) = b^{|h|+d} · Z_1(N b^{2|k|}; ξ(b·), η(b·)),
```
where `ξ(b·)` has the rescaled coefficient family `c_γ b^{|γ|}` (`CoeffFamily.scale`), absolutely
summable when `∑ |c_γ| b^{|γ|} < ∞` — the weighted mass at radius `b` (`familyPhaseIntegralBox_eq`,
via the Haar scaling `Measure.integral_comp_smul`). The Taylor tree on `(0,b]^d` therefore follows
from Headline XXVII at the rescaled sample size (unit 249). No `sorry` and no additional `axiom`
declarations.
-/

open MeasureTheory Set Real Filter Topology

namespace Laplace.Grammar

open MonoRep CoeffFamily

namespace CoeffFamily

variable {d : ℕ}

/-- The rescaled coefficient family `c_γ b^{|γ|}` of `u ↦ ξ(b u)`. -/
noncomputable def scale (c : CoeffFamily d) (b : ℝ) : CoeffFamily d := fun γ => c γ * b ^ (∑ i, γ i)

/-- The weighted mass `∑ |c_γ| b^{|γ|}` is finite. -/
def AbsSummableAt (c : CoeffFamily d) (b : ℝ) : Prop := Summable fun γ => |c γ| * b ^ (∑ i, γ i)

theorem AbsSummable.of_scale {c : CoeffFamily d} {b : ℝ} (hb : 0 ≤ b) (hc : AbsSummableAt c b) :
    AbsSummable (scale c b) := by
  unfold AbsSummable scale
  refine hc.congr fun γ => ?_
  rw [abs_mul, abs_of_nonneg (pow_nonneg hb _)]

theorem mono_smul (γ : Fin d → ℕ) (b : ℝ) (u : Fin d → ℝ) :
    mono γ (b • u) = b ^ (∑ i, γ i) * mono γ u := by
  unfold mono
  rw [← Finset.prod_pow_eq_pow_sum, ← Finset.prod_mul_distrib]
  exact Finset.prod_congr rfl fun i _ => by rw [Pi.smul_apply, smul_eq_mul, mul_pow]

/-- `eval (scale c b) u = eval c (b • u)`. -/
theorem evalF_scale (c : CoeffFamily d) (b : ℝ) (u : Fin d → ℝ) :
    evalF (scale c b) u = evalF c (b • u) := by
  unfold evalF scale
  refine tsum_congr fun γ => ?_
  rw [mono_smul]
  ring

end CoeffFamily

/-- The standard integral on the box `(0,b]^d` for coefficient-family data. -/
noncomputable def familyPhaseIntegralBox (n : ℕ) (h k : Fin (n + 1) → ℕ) (β N b : ℝ)
    (cξ cη : CoeffFamily (n + 1)) : ℝ :=
  ∫ u in piBox (n + 1) (Ioc 0 b), evalF cη u * (∏ i, u i ^ h i) *
    Real.exp (-(β * N * ∏ i, u i ^ (2 * k i)) + β * (Real.sqrt N * ∏ i, u i ^ k i) * evalF cξ u)

theorem smul_mem_piBox_Ioc_iff {d : ℕ} {b : ℝ} (hb : 0 < b) (v : Fin d → ℝ) :
    b • v ∈ piBox d (Ioc 0 b) ↔ v ∈ unitBox d := by
  unfold piBox unitBox
  simp only [Set.mem_pi, Set.mem_univ, true_implies, Pi.smul_apply, smul_eq_mul, Set.mem_Ioc]
  refine forall_congr' fun i => ?_
  constructor
  · rintro ⟨h1, h2⟩
    exact ⟨pos_of_mul_pos_right h1 hb.le, by nlinarith⟩
  · rintro ⟨h1, h2⟩
    exact ⟨by positivity, by nlinarith⟩

/-- **General-box scaling**: `Z_b(N) = b^{|h|+d} Z_1(N b^{2|k|}; ξ(b·), η(b·))` for `b > 0`,
`N ≥ 0`. -/
theorem familyPhaseIntegralBox_eq (n : ℕ) (h k : Fin (n + 1) → ℕ) (β : ℝ) {N b : ℝ} (hN : 0 ≤ N)
    (hb : 0 < b) (cξ cη : CoeffFamily (n + 1)) :
    familyPhaseIntegralBox n h k β N b cξ cη =
      b ^ (∑ i, h i + (n + 1)) *
        familyPhaseIntegral n h k β (N * b ^ (2 * ∑ i, k i)) (scale cξ b) (scale cη b) := by
  set F : (Fin (n + 1) → ℝ) → ℝ := fun u => evalF cη u * (∏ i, u i ^ h i) *
    Real.exp (-(β * N * ∏ i, u i ^ (2 * k i)) + β * (Real.sqrt N * ∏ i, u i ^ k i) * evalF cξ u)
    with hF
  set G : (Fin (n + 1) → ℝ) → ℝ := fun v => evalF (scale cη b) v * (∏ i, v i ^ h i) *
    Real.exp (-(β * (N * b ^ (2 * ∑ i, k i)) * ∏ i, v i ^ (2 * k i)) +
      β * (Real.sqrt (N * b ^ (2 * ∑ i, k i)) * ∏ i, v i ^ k i) * evalF (scale cξ b) v) with hG
  -- the integrand at `b • v`
  have hFG : ∀ v, F (b • v) = b ^ (∑ i, h i) * G v := by
    intro v
    simp only [hF, hG, Pi.smul_apply, smul_eq_mul, evalF_scale]
    have h1 : ∏ i, (b * v i) ^ h i = b ^ (∑ i, h i) * ∏ i, v i ^ h i := by
      rw [← Finset.prod_pow_eq_pow_sum, ← Finset.prod_mul_distrib]
      exact Finset.prod_congr rfl fun i _ => mul_pow _ _ _
    have h2 : ∏ i, (b * v i) ^ (2 * k i) = b ^ (2 * ∑ i, k i) * ∏ i, v i ^ (2 * k i) := by
      rw [Finset.mul_sum, ← Finset.prod_pow_eq_pow_sum, ← Finset.prod_mul_distrib]
      exact Finset.prod_congr rfl fun i _ => mul_pow _ _ _
    have h3 : Real.sqrt N * ∏ i, (b * v i) ^ k i =
        Real.sqrt (N * b ^ (2 * ∑ i, k i)) * ∏ i, v i ^ k i := by
      rw [Real.sqrt_mul hN, pow_mul', Real.sqrt_sq (pow_nonneg hb.le _),
        ← Finset.prod_pow_eq_pow_sum,
        mul_assoc, ← Finset.prod_mul_distrib]
      congr 1
      exact Finset.prod_congr rfl fun i _ => mul_pow _ _ _
    rw [h1, h2, h3]
    ring
  have hind : ∀ v, (piBox (n + 1) (Ioc 0 b)).indicator F (b • v) =
      (unitBox (n + 1)).indicator (fun v => b ^ (∑ i, h i) * G v) v := by
    intro v
    by_cases hv : v ∈ unitBox (n + 1)
    · rw [Set.indicator_of_mem hv, Set.indicator_of_mem ((smul_mem_piBox_Ioc_iff hb v).2 hv), hFG]
    · rw [Set.indicator_of_notMem hv,
        Set.indicator_of_notMem (fun h' => hv ((smul_mem_piBox_Ioc_iff hb v).1 h'))]
  have hscale := Measure.integral_comp_smul (volume : Measure (Fin (n + 1) → ℝ))
    ((piBox (n + 1) (Ioc 0 b)).indicator F) b
  rw [Module.finrank_fin_fun, smul_eq_mul, abs_of_nonneg (inv_nonneg.2 (pow_nonneg hb.le _)),
    integral_indicator (measurableSet_piBox _ _ measurableSet_Ioc)] at hscale
  simp_rw [hind] at hscale
  rw [integral_indicator (measurableSet_unitBox _), integral_const_mul] at hscale
  -- `hscale : b^{|h|} ∫_{unitBox} G = (b^d)⁻¹ * Z_b`
  unfold familyPhaseIntegralBox familyPhaseIntegral
  have hpos : (0 : ℝ) < b ^ (n + 1) := pow_pos hb _
  have : ∫ u in piBox (n + 1) (Ioc 0 b), F u =
      b ^ (n + 1) * (b ^ (∑ i, h i) * ∫ v in unitBox (n + 1), G v) := by
    rw [hscale]; field_simp
  rw [pow_add]
  calc _ = ∫ u in piBox (n + 1) (Ioc 0 b), F u := rfl
    _ = _ := this
    _ = _ := by ring

end Laplace.Grammar
