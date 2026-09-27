/-
Copyright (c) 2026 Timaeus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Timaeus
-/
import Laplace.Multi.ResponseFisherCurvature

/-!
# The sign of the Fisher curvature: a third-cumulant inequality defect

The **inverse Fisher form** `G*_θ(x,y) = G_θ(A_θ⁻¹x, A_θ⁻¹y) = −⟨x, A_θ⁻¹y⟩`
(`inverseFisherInner`) is an inner product on the direction space, and the mixture Christoffel
operator lowers to it: `G_θ(C_θ(u,v), C_θ(x,y)) = G*_θ(T_θ(u,v), T_θ(x,y))`
(`fisherInner_mChristoffel_mChristoffel`). Hence the numerator of the sectional curvature of the
Fisher metric is

  `G_θ(R⁰_θ(u,v)v, u) = ¼ (G*_θ(T(u,v),T(u,v)) − G*_θ(T(u,u),T(v,v)))`
  (`fisherCurvature_numerator`),

**a Gram-type inequality defect of the third cumulants**: the Fisher metric is nonpositively curved
on the plane of `u,v` exactly when `G*(T(u,v),T(u,v)) ≤ G*(T(u,u),T(v,v))`
(`fisherCurvature_numerator_nonpos_iff`), an inequality that ordinary Cauchy–Schwarz does not give
and that has no universal sign. The lowered `α`-curvature `G(R^α(u,v)w, x)` is
`−((1−α²)/4)(G*(T(u,x),T(v,w)) − G*(T(v,x),T(u,w)))` (`fisherInner_alphaCurvature`), with the
symmetries of an algebraic curvature tensor for every `α` (`alphaCurvature_bianchi`,
`fisherInner_alphaCurvature_antisymm_right`, `fisherInner_alphaCurvature_pair`), and vanishes
whenever the endomorphisms `C_θ(u,·)` commute (`alphaCurvature_eq_zero_of_comm`).
-/

open MeasureTheory Filter Topology Set

namespace Laplace.Multi

section Sign

variable {X : Type*} [MeasurableSpace X] [Nonempty X] {J : Type*} [Fintype J] [Nonempty J]
  {S : J → X → ℝ} (hS : ∀ j, Bdd (S j)) (ν : Measure X) [IsProbabilityMeasure ν]
include hS

/-- The direction space. -/
local notation "𝕍" => dirSpan ν (fun _ ↦ (1 : ℝ)) S

/-- The chart derivative. -/
local notation "CD" => chartDeriv measurable_const (integrable_const 1) (fun _ ↦ one_pos)
  (one_integral_pos ν) hS

/-- The chart derivative equivalence. -/
local notation "CDE" => chartDerivEquiv measurable_const (integrable_const 1) (fun _ ↦ one_pos)
  (one_integral_pos ν) hS

/-- **The inverse Fisher form** `G*_θ(x,y) = G_θ(A_θ⁻¹x, A_θ⁻¹y)`. -/
noncomputable def inverseFisherInner (θ x y : 𝕍) : ℝ :=
  fisherInner S ν θ ((CDE θ).symm x) ((CDE θ).symm y)

theorem inverseFisherInner_comm (θ x y : 𝕍) :
    inverseFisherInner hS ν θ x y = inverseFisherInner hS ν θ y x :=
  fisherInner_comm hS ν θ _ _

/-- `G*_θ(x,y) = −⟨x, A_θ⁻¹ y⟩`. -/
theorem inverseFisherInner_eq_neg_dotJ (θ x y : 𝕍) :
    inverseFisherInner hS ν θ x y = -dotJ (x : J → ℝ) ((CDE θ).symm y : J → ℝ) := by
  unfold inverseFisherInner
  rw [fisherInner_chartDerivEquiv_symm hS ν θ _ y.2,
    ← dotJ_symm_chartDeriv hS ν θ x ((CDE θ).symm y), chartDeriv_chartDerivEquiv_symm hS ν]

theorem inverseFisherInner_self_nonneg (θ x : 𝕍) : 0 ≤ inverseFisherInner hS ν θ x x :=
  fisherVar_nonneg hS ν _ _

theorem inverseFisherInner_self_pos (θ : 𝕍) {x : 𝕍} (hx : x ≠ 0) :
    0 < inverseFisherInner hS ν θ x x :=
  fisherInner_self_pos hS ν θ fun h ↦ hx (by simpa using congrArg (CDE θ) h)

/-- **The mixture Christoffel operator lowers to the inverse Fisher form**:
`G_θ(C_θ(u,v), C_θ(x,y)) = G*_θ(T_θ(u,v), T_θ(x,y))`. -/
theorem fisherInner_mChristoffel_mChristoffel (θ u v x y : 𝕍) :
    fisherInner S ν θ (mChristoffel hS ν θ u v) (mChristoffel hS ν θ x y) =
      inverseFisherInner hS ν θ (thirdOp hS ν θ u v) (thirdOp hS ν θ x y) := rfl

/-- The lowered Christoffel operator is symmetric in its first two slots. -/
theorem fisherInner_mChristoffel_symm₁₂ (θ u v w : 𝕍) :
    fisherInner S ν θ (mChristoffel hS ν θ u v) w =
      fisherInner S ν θ (mChristoffel hS ν θ v u) w := by
  rw [mChristoffel_symm hS ν]

/-- Moving the outer Christoffel operator across the Fisher form:
`G(C(u, x), y) = G(C(u, y), x)` in the form needed for curvature. -/
theorem fisherInner_mChristoffel_apply_eq (θ u x y : 𝕍) :
    fisherInner S ν θ (mChristoffel hS ν θ u x) y = fisherInner S ν θ (mChristoffel hS ν θ u y) x :=
  fisherInner_mChristoffel_swap hS ν θ u x y

/-- **The lowered `α`-curvature**:
`G(R^α(u,v)w, x) = −((1−α²)/4) (G*(T(u,x),T(v,w)) − G*(T(v,x),T(u,w)))`. -/
theorem fisherInner_alphaCurvature (α : ℝ) (θ u v w x : 𝕍) :
    fisherInner S ν θ (alphaCurvature hS ν α θ u v w) x =
      (-((1 - α ^ 2) / 4)) *
        (inverseFisherInner hS ν θ (thirdOp hS ν θ u x) (thirdOp hS ν θ v w) -
          inverseFisherInner hS ν θ (thirdOp hS ν θ v x) (thirdOp hS ν θ u w)) := by
  rw [alphaCurvature_eq hS ν, fisherInner_smul_left, fisherInner_sub_left hS ν,
    fisherInner_mChristoffel_apply_eq hS ν θ u _ x, fisherInner_mChristoffel_apply_eq hS ν θ v _ x,
    fisherInner_mChristoffel_mChristoffel hS ν, fisherInner_mChristoffel_mChristoffel hS ν]

/-- **The numerator of the sectional curvature of the Fisher metric is a Gram-type inequality
defect of the third cumulants**: `G(R⁰(u,v)v, u) = ¼ (G(C(u,v),C(u,v)) − G(C(u,u),C(v,v)))`. -/
theorem fisherCurvature_numerator (θ u v : 𝕍) :
    fisherInner S ν θ (alphaCurvature hS ν 0 θ u v v) u =
      (1 / 4 : ℝ) *
        (fisherInner S ν θ (mChristoffel hS ν θ u v) (mChristoffel hS ν θ u v) -
          fisherInner S ν θ (mChristoffel hS ν θ u u) (mChristoffel hS ν θ v v)) := by
  rw [alphaCurvature_zero hS ν, fisherInner_smul_left, fisherInner_sub_left hS ν,
    fisherInner_mChristoffel_apply_eq hS ν θ u _ u, fisherInner_mChristoffel_apply_eq hS ν θ v _ u,
    fisherInner_comm hS ν θ (mChristoffel hS ν θ v u), mChristoffel_symm hS ν θ v u]
  ring

/-- The curvature numerator in terms of the inverse Fisher form of the third cumulants. -/
theorem fisherCurvature_numerator_eq_inverse (θ u v : 𝕍) :
    fisherInner S ν θ (alphaCurvature hS ν 0 θ u v v) u =
      (1 / 4 : ℝ) *
        (inverseFisherInner hS ν θ (thirdOp hS ν θ u v) (thirdOp hS ν θ u v) -
          inverseFisherInner hS ν θ (thirdOp hS ν θ u u) (thirdOp hS ν θ v v)) := by
  rw [fisherCurvature_numerator hS ν, fisherInner_mChristoffel_mChristoffel hS ν,
    fisherInner_mChristoffel_mChristoffel hS ν]

/-- **Nonpositive curvature on a plane is a reverse Gram inequality for the third cumulants**:
`G(R⁰(u,v)v,u) ≤ 0 ↔ G*(T(u,v),T(u,v)) ≤ G*(T(u,u),T(v,v))`. -/
theorem fisherCurvature_numerator_nonpos_iff (θ u v : 𝕍) :
    fisherInner S ν θ (alphaCurvature hS ν 0 θ u v v) u ≤ 0 ↔
      inverseFisherInner hS ν θ (thirdOp hS ν θ u v) (thirdOp hS ν θ u v) ≤
        inverseFisherInner hS ν θ (thirdOp hS ν θ u u) (thirdOp hS ν θ v v) := by
  rw [fisherCurvature_numerator_eq_inverse hS ν]
  constructor
  · intro h
    nlinarith
  · intro h
    nlinarith

/-- **The sectional curvature of the Fisher metric** on the plane of `u, v`. -/
noncomputable def fisherSectional (θ u v : 𝕍) : ℝ :=
  fisherInner S ν θ (alphaCurvature hS ν 0 θ u v v) u /
    (fisherInner S ν θ u u * fisherInner S ν θ v v - fisherInner S ν θ u v ^ 2)

/-- On a nondegenerate plane the sign of the sectional curvature is the sign of the third-cumulant
defect. -/
theorem fisherSectional_nonpos_iff (θ u v : 𝕍)
    (hden : 0 < fisherInner S ν θ u u * fisherInner S ν θ v v - fisherInner S ν θ u v ^ 2) :
    fisherSectional hS ν θ u v ≤ 0 ↔
      inverseFisherInner hS ν θ (thirdOp hS ν θ u v) (thirdOp hS ν θ u v) ≤
        inverseFisherInner hS ν θ (thirdOp hS ν θ u u) (thirdOp hS ν θ v v) := by
  rw [← fisherCurvature_numerator_nonpos_iff hS ν, fisherSectional, div_nonpos_iff]
  constructor
  · rintro (⟨-, h⟩ | ⟨h, -⟩)
    · exact absurd hden (not_lt.2 h)
    · exact h
  · intro h
    exact Or.inr ⟨h, hden.le⟩

/-- The `α`-curvature tensor is antisymmetric in its last two slots once lowered:
`G(R^α(u,v)w, x) = −G(R^α(u,v)x, w)`. -/
theorem fisherInner_alphaCurvature_antisymm_right (α : ℝ) (θ u v w x : 𝕍) :
    fisherInner S ν θ (alphaCurvature hS ν α θ u v w) x =
      -fisherInner S ν θ (alphaCurvature hS ν α θ u v x) w := by
  rw [fisherInner_alphaCurvature hS ν, fisherInner_alphaCurvature hS ν,
    inverseFisherInner_comm hS ν θ (thirdOp hS ν θ u w), inverseFisherInner_comm hS ν θ
    (thirdOp hS ν θ v w)]
  ring

/-- The pair symmetry of the lowered `α`-curvature: `G(R^α(u,v)w, x) = G(R^α(w,x)u, v)`. -/
theorem fisherInner_alphaCurvature_pair (α : ℝ) (θ u v w x : 𝕍) :
    fisherInner S ν θ (alphaCurvature hS ν α θ u v w) x =
      fisherInner S ν θ (alphaCurvature hS ν α θ w x u) v := by
  rw [fisherInner_alphaCurvature hS ν, fisherInner_alphaCurvature hS ν, thirdOp_symm hS ν θ w v,
    thirdOp_symm hS ν θ x u, thirdOp_symm hS ν θ x v, thirdOp_symm hS ν θ w u,
    inverseFisherInner_comm hS ν θ (thirdOp hS ν θ v w), inverseFisherInner_comm hS ν θ
    (thirdOp hS ν θ v x)]

/-- **The first Bianchi identity** for every `α`-curvature. -/
theorem alphaCurvature_bianchi (α : ℝ) (θ u v w : 𝕍) :
    alphaCurvature hS ν α θ u v w + alphaCurvature hS ν α θ v w u +
      alphaCurvature hS ν α θ w u v = 0 := by
  rw [alphaCurvature_eq hS ν, alphaCurvature_eq hS ν, alphaCurvature_eq hS ν,
    mChristoffel_symm hS ν θ w u, mChristoffel_symm hS ν θ v u, mChristoffel_symm hS ν θ w v]
  module

/-- If the endomorphisms `C_θ(u, ·)` commute, every `α`-curvature vanishes at `θ`. -/
theorem alphaCurvature_eq_zero_of_comm (θ : 𝕍)
    (hcomm : ∀ u v w : 𝕍, mChristoffel hS ν θ u (mChristoffel hS ν θ v w) =
      mChristoffel hS ν θ v (mChristoffel hS ν θ u w)) (α : ℝ) (u v w : 𝕍) :
    alphaCurvature hS ν α θ u v w = 0 := by
  rw [alphaCurvature_eq hS ν, hcomm, sub_self, smul_zero]

end Sign

end Laplace.Multi
