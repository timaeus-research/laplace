/-
Copyright (c) 2026 Timaeus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Laplace.Grammar.CircleOperator

/-!
# The iterated Cauchy formula on a polydisc (Stage 7b)

Unit 261 (Astra #31 route R2). The **iterated circle operator** `A_r^{[d]}` is defined by recursion
along `Fin.cons`: `A_r^{[0]} G = G ()`, `A_r^{[d+1]} G = A_r (w ↦ A_r^{[d]} (w' ↦ G (w :: w')))`
(`iterOp`). It is linear, bounded by the supremum of `‖G‖` on the torus `{∀ i, ‖wᵢ‖ = r}`
(`norm_iterOp_le`), and satisfies the **iterated Cauchy formula**
```
A_r^{[d]} (w ↦ F w ∏ᵢ (1 − zᵢ/wᵢ)⁻¹) = F z          (‖zᵢ‖ < r)
```
(`iterOp_cauchy`) for `F` in the class `SliceHolo d r`: continuous on the closed polydisc and
holomorphic in the first coordinate on the disc for every tail in the closed polydisc, recursively
for the tails (`SliceHolo`). This internal class is supplied by the paper's hypothesis, joint
differentiability on the open polydisc of a larger radius (`sliceHolo_of_differentiableOn`). The
induction is on slices of `F` itself, never on coefficient functions. No `sorry` and no additional
`axiom` declarations.
-/

open MeasureTheory Set Real Filter Topology Complex

namespace Laplace.Grammar

/-- The closed polydisc `{z | ∀ i, ‖z i‖ ≤ r}`. -/
def closedPolydisc (d : ℕ) (r : ℝ) : Set (Fin d → ℂ) := Set.pi univ fun _ => Metric.closedBall 0 r

/-- The open polydisc `{z | ∀ i, ‖z i‖ < r}`. -/
def openPolydisc (d : ℕ) (r : ℝ) : Set (Fin d → ℂ) := Set.pi univ fun _ => Metric.ball 0 r

/-- The torus `{w | ∀ i, ‖w i‖ = r}`. -/
def torusSet (d : ℕ) (r : ℝ) : Set (Fin d → ℂ) := Set.pi univ fun _ => Metric.sphere 0 r

theorem mem_closedPolydisc {d : ℕ} {r : ℝ} {z : Fin d → ℂ} :
    z ∈ closedPolydisc d r ↔ ∀ i, ‖z i‖ ≤ r := by
  simp [closedPolydisc, Set.mem_pi]

theorem mem_openPolydisc {d : ℕ} {r : ℝ} {z : Fin d → ℂ} :
    z ∈ openPolydisc d r ↔ ∀ i, ‖z i‖ < r := by
  simp [openPolydisc, Set.mem_pi]

theorem mem_torusSet {d : ℕ} {r : ℝ} {w : Fin d → ℂ} : w ∈ torusSet d r ↔ ∀ i, ‖w i‖ = r := by
  simp [torusSet, Set.mem_pi]

theorem isCompact_closedPolydisc (d : ℕ) (r : ℝ) : IsCompact (closedPolydisc d r) :=
  isCompact_univ_pi fun _ => isCompact_closedBall _ _

theorem openPolydisc_subset_closedPolydisc (d : ℕ) {r R : ℝ} (h : r ≤ R) :
    openPolydisc d r ⊆ closedPolydisc d R :=
  Set.pi_mono fun _ _ => Metric.ball_subset_closedBall.trans (Metric.closedBall_subset_closedBall h)

theorem closedPolydisc_subset_openPolydisc (d : ℕ) {r R : ℝ} (h : r < R) :
    closedPolydisc d r ⊆ openPolydisc d R :=
  Set.pi_mono fun _ _ => Metric.closedBall_subset_ball h

theorem torusSet_subset_closedPolydisc (d : ℕ) (r : ℝ) : torusSet d r ⊆ closedPolydisc d r :=
  Set.pi_mono fun _ _ => Metric.sphere_subset_closedBall

theorem cons_mem_closedPolydisc {d : ℕ} {r : ℝ} {w : ℂ} (hw : ‖w‖ ≤ r) {w' : Fin d → ℂ}
    (hw' : w' ∈ closedPolydisc d r) : Fin.cons w w' ∈ closedPolydisc (d + 1) r := by
  rw [mem_closedPolydisc] at hw' ⊢
  intro i
  refine Fin.cases ?_ (fun j => ?_) i
  · simpa using hw
  · simpa using hw' j

theorem cons_mem_openPolydisc {d : ℕ} {r : ℝ} {w : ℂ} (hw : ‖w‖ < r) {w' : Fin d → ℂ}
    (hw' : w' ∈ openPolydisc d r) : Fin.cons w w' ∈ openPolydisc (d + 1) r := by
  rw [mem_openPolydisc] at hw' ⊢
  intro i
  refine Fin.cases ?_ (fun j => ?_) i
  · simpa using hw
  · simpa using hw' j

theorem cons_mem_torusSet {d : ℕ} {r : ℝ} {w : ℂ} (hw : ‖w‖ = r) {w' : Fin d → ℂ}
    (hw' : w' ∈ torusSet d r) : Fin.cons w w' ∈ torusSet (d + 1) r := by
  rw [mem_torusSet] at hw' ⊢
  intro i
  refine Fin.cases ?_ (fun j => ?_) i
  · simpa using hw
  · simpa using hw' j

theorem tail_mem_openPolydisc {d : ℕ} {r : ℝ} {z : Fin (d + 1) → ℂ} (hz : z ∈ openPolydisc (d +
1) r) :
    Fin.tail z ∈ openPolydisc d r := by
  rw [mem_openPolydisc] at hz ⊢
  exact fun j => hz j.succ

/-! ### The iterated circle operator -/

/-- `A_r^{[d]}`: iterated normalised circle operator along `Fin.cons`. -/
noncomputable def iterOp : (d : ℕ) → ℝ → ((Fin d → ℂ) → ℂ) → ℂ
  | 0, _, G => G Fin.elim0
  | d + 1, r, G => circleOp r fun w => iterOp d r fun w' => G (Fin.cons w w')

theorem circleOp_congr {r : ℝ} (hr : 0 ≤ r) {g₁ g₂ : ℂ → ℂ} (h : EqOn g₁ g₂ (Metric.sphere 0 r)) :
    circleOp r g₁ = circleOp r g₂ := by
  unfold circleOp
  congr 1
  exact circleIntegral.integral_congr hr fun w hw => by rw [h hw]

theorem circleOp_const_mul (r : ℝ) (c : ℂ) (g : ℂ → ℂ) :
    circleOp r (fun w => c * g w) = c * circleOp r g := by
  unfold circleOp
  have : (fun w : ℂ => w⁻¹ * (c * g w)) = fun w => c • (w⁻¹ * g w) := by
    funext w; simp only [smul_eq_mul]; ring
  rw [this, circleIntegral.integral_smul, smul_eq_mul]
  ring

theorem iterOp_const_mul : ∀ (d : ℕ) (r : ℝ) (c : ℂ) (G : (Fin d → ℂ) → ℂ),
    iterOp d r (fun w => c * G w) = c * iterOp d r G
  | 0, _, _, _ => rfl
  | d + 1, r, c, G => by
    simp only [iterOp]
    rw [← circleOp_const_mul]
    congr 1
    funext w
    exact iterOp_const_mul d r c _

theorem iterOp_congr : ∀ (d : ℕ) {r : ℝ}, 0 ≤ r → ∀ {G₁ G₂ : (Fin d → ℂ) → ℂ},
    EqOn G₁ G₂ (torusSet d r) → iterOp d r G₁ = iterOp d r G₂
  | 0, _, _, G₁, G₂, h => by
    simp only [iterOp]
    exact h (by simp [torusSet])
  | d + 1, r, hr, G₁, G₂, h => by
    simp only [iterOp]
    refine circleOp_congr hr fun w hw => ?_
    refine iterOp_congr d hr fun w' hw' => ?_
    exact h (cons_mem_torusSet (by simpa using hw) hw')

/-- **Torus bound**: `‖A_r^{[d]} G‖ ≤ C` if `‖G w‖ ≤ C` on the torus. -/
theorem norm_iterOp_le : ∀ (d : ℕ) {r C : ℝ}, 0 < r → ∀ {G : (Fin d → ℂ) → ℂ},
    (∀ w ∈ torusSet d r, ‖G w‖ ≤ C) → ‖iterOp d r G‖ ≤ C
  | 0, _, _, _, G, h => by
    simp only [iterOp]
    exact h _ (by simp [torusSet])
  | d + 1, r, C, hr, G, h => by
    simp only [iterOp]
    refine norm_circleOp_le hr fun w hw => ?_
    refine norm_iterOp_le d hr fun w' hw' => ?_
    exact h _ (cons_mem_torusSet (by simpa using hw) hw')

/-! ### Slice holomorphy -/

/-- Recursive slice hypothesis: `F` continuous on the closed polydisc, holomorphic in the first
coordinate on the disc for every tail in the closed polydisc, and recursively so for every
first-coordinate value on the closed disc. -/
def SliceHolo : (d : ℕ) → ℝ → ((Fin d → ℂ) → ℂ) → Prop
  | 0, _, _ => True
  | d + 1, r, F => ContinuousOn F (closedPolydisc (d + 1) r) ∧
      (∀ w' ∈ closedPolydisc d r, DiffContOnCl ℂ (fun t => F (Fin.cons t w')) (Metric.ball 0 r)) ∧
      (∀ w : ℂ, ‖w‖ ≤ r → SliceHolo d r fun w' => F (Fin.cons w w'))

/-- **The iterated Cauchy formula**: `A_r^{[d]} (w ↦ F w ∏ (1 − zᵢ/wᵢ)⁻¹) = F z` on the open
polydisc. -/
theorem iterOp_cauchy : ∀ (d : ℕ) {r : ℝ}, 0 < r → ∀ {F : (Fin d → ℂ) → ℂ}, SliceHolo d r F →
    ∀ {z : Fin d → ℂ}, z ∈ openPolydisc d r →
      iterOp d r (fun w => F w * ∏ i, (1 - z i / w i)⁻¹) = F z
  | 0, _, _, F, _, z, _ => by
    simp only [iterOp, Finset.univ_eq_empty, Finset.prod_empty, mul_one]
    congr 1
    exact Subsingleton.elim _ _
  | d + 1, r, hr, F, hF, z, hz => by
    obtain ⟨_, hslice, htail⟩ := hF
    have hz0 : ‖z 0‖ < r := (mem_openPolydisc.1 hz) 0
    have hzt : Fin.tail z ∈ openPolydisc d r := tail_mem_openPolydisc hz
    simp only [iterOp]
    -- on the circle, the inner operator evaluates to `(1 − z 0 / w)⁻¹ * F (w :: tail z)`
    have hinner : EqOn (fun w => iterOp d r fun w' : Fin d → ℂ =>
        F (Fin.cons w w') * ∏ i, (1 - z i / (Fin.cons w w' : Fin (d + 1) → ℂ) i)⁻¹)
        (fun w => (1 - z 0 / w)⁻¹ * F (Fin.cons w (Fin.tail z))) (Metric.sphere 0 r) := by
      intro w hw
      have hw' : ‖w‖ ≤ r := by simp at hw; linarith [hw]
      have hprod : ∀ w' : Fin d → ℂ, ∏ i, (1 - z i / (Fin.cons w w' : Fin (d + 1) → ℂ) i)⁻¹ =
          (1 - z 0 / w)⁻¹ * ∏ j, (1 - Fin.tail z j / w' j)⁻¹ := by
        intro w'
        rw [Fin.prod_univ_succ]
        simp [Fin.tail]
      simp only
      have : (fun w' : Fin d → ℂ => F (Fin.cons w w') *
          ∏ i, (1 - z i / (Fin.cons w w' : Fin (d + 1) → ℂ) i)⁻¹) =
          fun w' => (1 - z 0 / w)⁻¹ * (F (Fin.cons w w') * ∏ j, (1 - Fin.tail z j / w' j)⁻¹) := by
        funext w'; rw [hprod]; ring
      rw [this, iterOp_const_mul, iterOp_cauchy d hr (htail w hw') hzt]
    rw [circleOp_congr hr.le hinner]
    have hcl : Fin.tail z ∈ closedPolydisc d r :=
      openPolydisc_subset_closedPolydisc d le_rfl hzt
    rw [circleOp_cauchy hr (hslice _ hcl) hz0, Fin.cons_self_tail]

/-! ### Supplying the slice hypothesis from joint holomorphy -/

theorem differentiable_cons_left {d : ℕ} (w' : Fin d → ℂ) :
    Differentiable ℂ fun t : ℂ => (Fin.cons t w' : Fin (d + 1) → ℂ) := by
  rw [differentiable_pi]
  intro i
  refine Fin.cases ?_ (fun j => ?_) i
  · simp
  · simp

theorem differentiable_cons_right {d : ℕ} (w : ℂ) :
    Differentiable ℂ fun w' : Fin d → ℂ => (Fin.cons w w' : Fin (d + 1) → ℂ) := by
  rw [differentiable_pi]
  intro i
  refine Fin.cases ?_ (fun j => ?_) i
  · simp
  · exact differentiable_apply j

/-- Joint differentiability on the open polydisc of radius `R > r` supplies `SliceHolo d r`. -/
theorem sliceHolo_of_differentiableOn : ∀ (d : ℕ) {r R : ℝ}, 0 < r → r < R →
    ∀ {F : (Fin d → ℂ) → ℂ}, DifferentiableOn ℂ F (openPolydisc d R) → SliceHolo d r F
  | 0, _, _, _, _, _, _ => trivial
  | d + 1, r, R, hr, hrR, F, hF => by
    refine ⟨?_, ?_, ?_⟩
    · exact hF.continuousOn.mono (closedPolydisc_subset_openPolydisc _ hrR)
    · intro w' hw'
      have hdiff : DifferentiableOn ℂ (fun t : ℂ => F (Fin.cons t w')) (Metric.ball 0 R) := by
        refine hF.comp (differentiable_cons_left w').differentiableOn fun t ht => ?_
        exact cons_mem_openPolydisc (by simpa using ht)
          (closedPolydisc_subset_openPolydisc d hrR hw')
      exact hdiff.diffContOnCl_ball (Metric.closedBall_subset_ball hrR)
    · intro w hw
      refine sliceHolo_of_differentiableOn d hr hrR ?_
      refine hF.comp (differentiable_cons_right w).differentiableOn fun w' hw' => ?_
      exact cons_mem_openPolydisc (lt_of_le_of_lt hw hrR) hw'

end Laplace.Grammar
