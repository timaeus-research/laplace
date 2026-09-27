/-
Copyright (c) 2026 Timaeus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Timaeus
-/
import Laplace.Multi.ResponseObservableSamplingGeometry
import Laplace.Multi.ResponseSimplexIdentification

/-!
# The uniform regression bound on a finite configuration

On a finite configuration `X` every model law `P_θ` charges every atom, and the regression
direction `u_F(θ)` of a bounded observable is, together with its intercept, the weighted affine
least-squares fit of `F` on the features with weights `p_θ(x) = P_θ{x}`. The regression directions
are **uniformly bounded over the whole model** (`exists_uniform_regressionDir_bound`), although the
weights degenerate at the boundary of the polytope and the Fisher form with them.

The proof needs no polyhedral vertex theory. Write `β(θ) = (c_F(θ), u_F(θ))` for the coefficient
vector, `r = F − c − ⟨u, S⟩` for the residual and `σ(θ) = sign r(θ)` for its sign pattern. The
closed **sign cell** `C_σ` of a pattern consists of the coefficient vectors whose residual has
weakly the sign `σ_x` at every atom, with equality where `σ_x = 0` (`signCell`). Every `β(θ)` lies
in the cell of its own pattern (`regCoef_mem_signCell`), and the cell of a *realised* pattern is
bounded
(`norm_le_cellRadius`): for `b ∈ C_{σ(θ)}` with residual `s`, the normal equations of `θ` give
`Σ_x p_x r_x s_x = Σ_x p_x r_x² =: E` with every term nonnegative, so `|s_x| ≤ E/(p_x |r_x|)` where
`r_x ≠ 0` and `s_x = 0` where `r_x = 0`; the design map `(c,u) ↦ (c + ⟨u,S(x)⟩)_x` is injective on
`ℝ × W` (a direction with constant loss contrast is invisible), hence has a bounded inverse on its
range, and the coefficients are bounded by the bounded values. Finitely many patterns, one witness
each, and a finite maximum give the uniform bound.
-/

open MeasureTheory Filter Topology Set

namespace Laplace.Multi

section Design

variable {X : Type*} [MeasurableSpace X] {J : Type*} [Fintype J] (S : J → X → ℝ) (ν : Measure X)

/-- The direction space. -/
local notation "𝕍" => dirSpan ν (fun _ ↦ (1 : ℝ)) S

/-- **The affine design map** `(c, u) ↦ (x ↦ c + ⟨u, S(x)⟩)` on `ℝ × W`. -/
noncomputable def design : ℝ × 𝕍 →ₗ[ℝ] (X → ℝ) where
  toFun b := fun x ↦ b.1 + dirLoss S (b.2 : J → ℝ) x
  map_add' b b' := by
    funext x
    simp only [Prod.fst_add, Prod.snd_add, Submodule.coe_add, dirLoss_add, Pi.add_apply]
    ring
  map_smul' c b := by
    funext x
    simp only [Prod.smul_fst, Prod.smul_snd, Submodule.coe_smul, dirLoss_smul, Pi.smul_apply,
      smul_eq_mul, RingHom.id_apply]
    ring

theorem design_apply (b : ℝ × 𝕍) (x : X) : design S ν b x = b.1 + dirLoss S (b.2 : J → ℝ) x := rfl

/-- **The closed sign cell** of a pattern: the coefficient vectors whose residual has weakly the
sign `σ_x` at every atom, with equality where `σ_x = 0`. -/
def signCell (F : X → ℝ) (σ : X → SignType) : Set (ℝ × 𝕍) :=
  {b | ∀ x, 0 ≤ (σ x : ℝ) * (F x - design S ν b x) ∧ (σ x = 0 → F x - design S ν b x = 0)}

end Design

section Uniform

variable {X : Type*} [MeasurableSpace X] [Nonempty X] [Fintype X] [MeasurableSingletonClass X]
  {J : Type*} [Fintype J] [Nonempty J] {S : J → X → ℝ} (hS : ∀ j, Bdd (S j)) (ν : Measure X)
  [IsProbabilityMeasure ν]
include hS

set_option linter.unusedFintypeInType false

/-- The reconstructed family. -/
local notation "Pfam" => familyMeasure ν (fun _ ↦ (1 : ℝ)) (fun _ ↦ (0 : ℝ)) S 1

/-- The direction space. -/
local notation "𝕍" => dirSpan ν (fun _ ↦ (1 : ℝ)) S

/-- The regression direction. -/
local notation "uF" => regressionDir hS ν

/-- The atom masses. -/
local notation "pθ" => atomMass S ν

omit [Fintype X] [MeasurableSingletonClass X] [Nonempty J] [IsProbabilityMeasure ν] in
/-- The design map is injective: a direction with constant loss contrast is invisible. -/
theorem design_ker : LinearMap.ker (design S ν) = ⊥ := by
  rw [LinearMap.ker_eq_bot']
  intro b hb
  have hx : ∀ x, b.1 + dirLoss S (b.2 : J → ℝ) x = 0 := fun x ↦ congrFun hb x
  have hu : b.2 = 0 := by
    apply logLift_injective hS ν
    rw [logLift_apply, map_zero, Submodule.Quotient.mk_eq_zero, Submodule.mem_span_singleton]
    refine ⟨-b.1, ?_⟩
    funext x
    simp only [Pi.smul_apply, Pi.one_apply, smul_eq_mul, mul_one]
    linarith [hx x]
  have x : X := Classical.arbitrary X
  have hc : b.1 = 0 := by
    have := hx x
    rw [hu, Submodule.coe_zero] at this
    simpa [dirLoss] using this
  exact Prod.ext hc hu

omit [MeasurableSingletonClass X] [Nonempty J] [IsProbabilityMeasure ν] in
/-- The design map has a bounded inverse on its range. -/
theorem exists_design_bound : ∃ K : ℝ, 0 ≤ K ∧ ∀ b : ℝ × 𝕍, ‖b‖ ≤ K * ‖design S ν b‖ := by
  obtain ⟨K, -, hanti⟩ := (design S ν).exists_antilipschitzWith (design_ker hS ν)
  refine ⟨K, K.coe_nonneg, fun b ↦ ?_⟩
  have := hanti.le_mul_dist b 0
  rwa [dist_zero_right, map_zero, dist_zero_right] at this

/-- The intercept of the affine regression: `c_F(θ) = E_θ F − E_θ⟨u_F, S⟩`. -/
noncomputable def intercept (F : X → ℝ) (θ : 𝕍) : ℝ :=
  (∫ x, F x ∂Pfam (θ : J → ℝ)) - ∫ x, dirLoss S (uF F θ : J → ℝ) x ∂Pfam (θ : J → ℝ)

/-- The affine regression coefficients `β_F(θ) = (c_F(θ), u_F(θ))`. -/
noncomputable def regCoef (F : X → ℝ) (θ : 𝕍) : ℝ × 𝕍 := (intercept hS ν F θ, uF F θ)

/-- The regression residual `r_F(θ)(x) = F(x) − c_F(θ) − ⟨u_F(θ), S(x)⟩`. -/
noncomputable def regResid (F : X → ℝ) (θ : 𝕍) (x : X) : ℝ :=
  F x - design S ν (regCoef hS ν F θ) x

/-- **The normal equations in barycentric form**: the residual is orthogonal to every affine
function of the features, `Σ_x p_x r_x (c + ⟨v, S(x)⟩) = 0`. -/
theorem sum_atomMass_mul_regResid_mul_design {F : X → ℝ} (hF : Bdd F) (θ : 𝕍) (b : ℝ × 𝕍) :
    ∑ x, pθ (θ : J → ℝ) x * (regResid hS ν F θ x * design S ν b x) = 0 := by
  have hP := isProbabilityMeasure_family hS ν (θ : J → ℝ)
  have hcov := lawCov_regressionResidual_dirLoss hS ν hF θ b.2
  unfold lawCov at hcov
  rw [integral_familyMeasure_eq_sum hS ν, integral_familyMeasure_eq_sum hS ν,
    integral_familyMeasure_eq_sum hS ν] at hcov
  have hc : intercept hS ν F θ =
      (∑ x, pθ (θ : J → ℝ) x * F x) - ∑ x, pθ (θ : J → ℝ) x * dirLoss S (uF F θ : J → ℝ) x := by
    unfold intercept
    rw [integral_familyMeasure_eq_sum hS ν, integral_familyMeasure_eq_sum hS ν]
  have hsum := sum_atomMass hS ν (θ : J → ℝ)
  have e : ∀ x, pθ (θ : J → ℝ) x * (regResid hS ν F θ x * design S ν b x) =
      b.1 * (pθ (θ : J → ℝ) x * F x) - (b.1 * intercept hS ν F θ) * pθ (θ : J → ℝ) x -
        b.1 * (pθ (θ : J → ℝ) x * dirLoss S (uF F θ : J → ℝ) x) +
        (pθ (θ : J → ℝ) x * (F x * dirLoss S (b.2 : J → ℝ) x) -
          pθ (θ : J → ℝ) x * (dirLoss S (uF F θ : J → ℝ) x * dirLoss S (b.2 : J → ℝ) x)) -
        intercept hS ν F θ * (pθ (θ : J → ℝ) x * dirLoss S (b.2 : J → ℝ) x) := by
    intro x
    simp only [regResid, regCoef, design_apply]
    ring
  simp_rw [e]
  simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum, hsum, mul_one]
  simp only [mul_sub, sub_mul, Finset.sum_sub_distrib] at hcov
  rw [hc]
  linear_combination hcov

/-- The sign pattern of the residual. -/
noncomputable def regPattern (F : X → ℝ) (θ : 𝕍) (x : X) : SignType :=
  SignType.sign (regResid hS ν F θ x)

omit [Fintype X] [MeasurableSingletonClass X] in
/-- Every coefficient vector lies in the cell of its own pattern. -/
theorem regCoef_mem_signCell (F : X → ℝ) (θ : 𝕍) :
    regCoef hS ν F θ ∈ signCell S ν F (regPattern hS ν F θ) := by
  intro x
  refine ⟨?_, fun h0 ↦ ?_⟩
  · change 0 ≤ (SignType.sign (regResid hS ν F θ x) : ℝ) * regResid hS ν F θ x
    rw [sign_mul_self]
    exact abs_nonneg _
  · exact sign_eq_zero_iff.1 h0

/-- The residual energy `E_F(θ) = Σ_x p_x r_x²`. -/
noncomputable def residEnergy (F : X → ℝ) (θ : 𝕍) : ℝ :=
  ∑ x, pθ (θ : J → ℝ) x * regResid hS ν F θ x ^ 2

omit [MeasurableSingletonClass X] in
theorem residEnergy_nonneg (hν : ∀ x, ν {x} ≠ 0) (F : X → ℝ) (θ : 𝕍) :
    0 ≤ residEnergy hS ν F θ :=
  Finset.sum_nonneg fun x _ ↦ mul_nonneg (atomMass_pos hS ν hν _ x).le (sq_nonneg _)

/-- **The cell of a realised pattern has bounded design values**: for `b` in the cell of `σ(θ)`,
`|c + ⟨u, S(x)⟩| ≤ |F(x)| + E_F(θ)/(p_x |r_x|)` at every atom. -/
theorem abs_design_le_of_mem_signCell (hν : ∀ x, ν {x} ≠ 0) {F : X → ℝ} (hF : Bdd F) (θ : 𝕍)
    {b : ℝ × 𝕍}
    (hb : b ∈ signCell S ν F (regPattern hS ν F θ)) (x : X) :
    |design S ν b x| ≤
      |F x| + residEnergy hS ν F θ / (pθ (θ : J → ℝ) x * |regResid hS ν F θ x|) := by
  -- the residual of `b` against that of `θ`
  have hkey : ∑ y, pθ (θ : J → ℝ) y * (regResid hS ν F θ y * (F y - design S ν b y)) =
      residEnergy hS ν F θ := by
    have h0 := sum_atomMass_mul_regResid_mul_design hS ν hF θ (regCoef hS ν F θ - b)
    unfold residEnergy
    rw [← sub_eq_zero, ← Finset.sum_sub_distrib, ← h0]
    refine Finset.sum_congr rfl fun y _ ↦ ?_
    rw [map_sub]
    simp only [regResid, Pi.sub_apply]
    ring
  have hnn : ∀ y, 0 ≤ pθ (θ : J → ℝ) y * (regResid hS ν F θ y * (F y - design S ν b y)) := by
    intro y
    refine mul_nonneg (atomMass_pos hS ν hν _ y).le ?_
    have h1 := (hb y).1
    change 0 ≤ (SignType.sign (regResid hS ν F θ y) : ℝ) * (F y - design S ν b y) at h1
    calc (0 : ℝ) ≤ |regResid hS ν F θ y| *
          ((SignType.sign (regResid hS ν F θ y) : ℝ) * (F y - design S ν b y)) :=
          mul_nonneg (abs_nonneg _) h1
      _ = regResid hS ν F θ y * (F y - design S ν b y) := by
          rw [← mul_assoc, abs_mul_sign]
  have hle : pθ (θ : J → ℝ) x * (regResid hS ν F θ x * (F x - design S ν b x)) ≤
      residEnergy hS ν F θ := by
    rw [← hkey]
    exact Finset.single_le_sum (fun y _ ↦ hnn y) (Finset.mem_univ x)
  have hs : |F x - design S ν b x| ≤
      residEnergy hS ν F θ / (pθ (θ : J → ℝ) x * |regResid hS ν F θ x|) := by
    by_cases hr : regResid hS ν F θ x = 0
    · have h2 := (hb x).2
      change SignType.sign (regResid hS ν F θ x) = 0 → _ at h2
      rw [h2 (sign_eq_zero_iff.2 hr), hr, abs_zero, mul_zero, div_zero]
    · have hpos : 0 < pθ (θ : J → ℝ) x * |regResid hS ν F θ x| :=
        mul_pos (atomMass_pos hS ν hν _ x) (abs_pos.2 hr)
      rw [le_div_iff₀ hpos]
      calc |F x - design S ν b x| * (pθ (θ : J → ℝ) x * |regResid hS ν F θ x|)
          = pθ (θ : J → ℝ) x * |regResid hS ν F θ x * (F x - design S ν b x)| := by
            rw [abs_mul]; ring
        _ = pθ (θ : J → ℝ) x * (regResid hS ν F θ x * (F x - design S ν b x)) := by
            rw [abs_of_nonneg]
            have := hnn x
            exact nonneg_of_mul_nonneg_right this (atomMass_pos hS ν hν _ x)
        _ ≤ residEnergy hS ν F θ := hle
  calc |design S ν b x| = |F x - (F x - design S ν b x)| := by ring_nf
    _ ≤ |F x| + |F x - design S ν b x| := abs_sub _ _
    _ ≤ _ := add_le_add le_rfl hs

/-- The radius of the cell of a realised pattern, for a design constant `K`. -/
noncomputable def cellRadius (K : ℝ) (F : X → ℝ) (θ : 𝕍) : ℝ :=
  K * ∑ x, (|F x| + residEnergy hS ν F θ / (pθ (θ : J → ℝ) x * |regResid hS ν F θ x|))

/-- **The cell of a realised pattern is bounded.** -/
theorem norm_le_cellRadius (hν : ∀ x, ν {x} ≠ 0) {K : ℝ} (hK0 : 0 ≤ K)
    (hK : ∀ b : ℝ × 𝕍, ‖b‖ ≤ K * ‖design S ν b‖) {F : X → ℝ} (hF : Bdd F) (θ : 𝕍) {b : ℝ × 𝕍}
    (hb : b ∈ signCell S ν F (regPattern hS ν F θ)) :
    ‖b‖ ≤ cellRadius hS ν K F θ := by
  have hterm : ∀ x, 0 ≤ |F x| +
      residEnergy hS ν F θ / (pθ (θ : J → ℝ) x * |regResid hS ν F θ x|) := fun x ↦
    add_nonneg (abs_nonneg _) (div_nonneg (residEnergy_nonneg hS ν hν F θ)
      (mul_nonneg (atomMass_pos hS ν hν _ x).le (abs_nonneg _)))
  refine (hK b).trans (mul_le_mul_of_nonneg_left ?_ hK0)
  rw [pi_norm_le_iff_of_nonneg (Finset.sum_nonneg fun x _ ↦ hterm x)]
  intro x
  rw [Real.norm_eq_abs]
  exact (abs_design_le_of_mem_signCell hS ν hν hF θ hb x).trans
    (Finset.single_le_sum (fun y _ ↦ hterm y) (Finset.mem_univ x))

/-- **The coefficient vectors are uniformly bounded over the model.** -/
theorem exists_uniform_regCoef_bound (hν : ∀ x, ν {x} ≠ 0) {F : X → ℝ} (hF : Bdd F) :
    ∃ L : ℝ, ∀ θ : 𝕍, ‖regCoef hS ν F θ‖ ≤ L := by
  classical
  obtain ⟨K, hK0, hK⟩ := exists_design_bound hS ν
  let bound : (X → SignType) → ℝ := fun σ ↦
    if h : ∃ θ : 𝕍, regPattern hS ν F θ = σ then cellRadius hS ν K F h.choose else 0
  refine ⟨∑ σ, |bound σ|, fun θ ↦ ?_⟩
  have h : ∃ θ' : 𝕍, regPattern hS ν F θ' = regPattern hS ν F θ := ⟨θ, rfl⟩
  have hmem : regCoef hS ν F θ ∈ signCell S ν F (regPattern hS ν F h.choose) := by
    rw [h.choose_spec]
    exact regCoef_mem_signCell hS ν F θ
  calc ‖regCoef hS ν F θ‖ ≤ cellRadius hS ν K F h.choose :=
        norm_le_cellRadius hS ν hν hK0 hK hF _ hmem
    _ = bound (regPattern hS ν F θ) := by simp only [bound, dif_pos h]
    _ ≤ |bound (regPattern hS ν F θ)| := le_abs_self _
    _ ≤ ∑ σ, |bound σ| :=
        Finset.single_le_sum (f := fun σ ↦ |bound σ|) (fun σ _ ↦ abs_nonneg _) (Finset.mem_univ _)

/-- **THE UNIFORM REGRESSION BOUND**: on a finite configuration the regression directions of a
bounded observable are uniformly bounded over the whole model, `‖u_F(θ)‖ ≤ L_F` for every `θ`,
although the weights and the Fisher form degenerate at the boundary of the polytope. -/
theorem exists_uniform_regressionDir_bound (hν : ∀ x, ν {x} ≠ 0) {F : X → ℝ} (hF : Bdd F) :
    ∃ L : ℝ, ∀ θ : 𝕍, ‖(uF F θ : J → ℝ)‖ ≤ L := by
  obtain ⟨L, hL⟩ := exists_uniform_regCoef_bound hS ν hν hF
  exact ⟨L, fun θ ↦ (norm_snd_le (regCoef hS ν F θ)).trans (hL θ)⟩

/-- The uniform bound in the sup-norm pairing form: `Σ_j |u_F(θ)_j| ≤ |J| L_F`. -/
theorem exists_uniform_sum_abs_regressionDir_bound (hν : ∀ x, ν {x} ≠ 0) {F : X → ℝ}
    (hF : Bdd F) :
    ∃ L : ℝ, 0 ≤ L ∧ ∀ θ : 𝕍, ∑ j, |(uF F θ : J → ℝ) j| ≤ L := by
  obtain ⟨L, hL⟩ := exists_uniform_regressionDir_bound hS ν hν hF
  refine ⟨Fintype.card J * |L|, by positivity, fun θ ↦ ?_⟩
  calc ∑ j, |(uF F θ : J → ℝ) j| ≤ ∑ _j : J, ‖(uF F θ : J → ℝ)‖ :=
        Finset.sum_le_sum fun j _ ↦ by
          rw [← Real.norm_eq_abs]
          exact norm_le_pi_norm _ j
    _ = Fintype.card J * ‖(uF F θ : J → ℝ)‖ := by
        rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
    _ ≤ Fintype.card J * |L| :=
        mul_le_mul_of_nonneg_left ((hL θ).trans (le_abs_self L)) (Nat.cast_nonneg _)

end Uniform

end Laplace.Multi
