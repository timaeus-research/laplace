/-
Copyright (c) 2026 Timaeus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Timaeus
-/
import Laplace.Multi.InformationBudget

/-!
# Density bounds of the family on bounded parameter regions

If the visible statistics satisfy `‖S − m₀‖ ≤ B` almost surely and the natural coordinate satisfies
`‖θ‖ ≤ r` (Euclidean norms, written with `dotJ`), the member `P_θ ∝ e^{−⟨θ,S⟩} ν` has density
between `e^{−2Br}` and `e^{2Br}` relative to `ν` (`familyMeasure_density_ge`), so expectations of
nonnegative statistics are comparable (`integral_familyMeasure_ge`) and

  `Var_{P_θ}(g) ≥ e^{−2Br} Var_ν(g)`   (`lawCov_familyMeasure_ge`):

the susceptibility never degenerates faster than exponentially in the distance travelled in natural
coordinates. This is the analytic input of the quantitative inverse stability of the chart.
-/

open MeasureTheory Filter Topology Set
open scoped ENNReal

namespace Laplace.Multi

variable {X : Type*} [MeasurableSpace X] [Nonempty X] {J : Type*} [Fintype J]
  {S : J → X → ℝ} (hS : ∀ j, Bdd (S j)) (ν : Measure X) [IsProbabilityMeasure ν]
include hS

omit [Nonempty X] hS in
/-- Cauchy–Schwarz for the pairing: `|⟨θ, v⟩| ≤ r B` when `⟨θ,θ⟩ ≤ r²` and `⟨v,v⟩ ≤ B²`. -/
theorem abs_dotJ_le_of_sq_le {θ v : J → ℝ} {r B : ℝ} (hr : 0 ≤ r) (hB : 0 ≤ B)
    (hθ : dotJ θ θ ≤ r ^ 2) (hv : dotJ v v ≤ B ^ 2) : |dotJ θ v| ≤ r * B := by
  have hcs := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ θ v
  have e1 : dotJ θ v = ∑ i, θ i * v i := rfl
  have e2 : dotJ θ θ = ∑ i, θ i ^ 2 := Finset.sum_congr rfl fun i _ ↦ (sq _).symm
  have e3 : dotJ v v = ∑ i, v i ^ 2 := Finset.sum_congr rfl fun i _ ↦ (sq _).symm
  rw [e2] at hθ
  rw [e3] at hv
  rw [e1]
  have h1 : (∑ i, θ i * v i) ^ 2 ≤ (r * B) ^ 2 := by
    calc (∑ i, θ i * v i) ^ 2 ≤ (∑ i, θ i ^ 2) * ∑ i, v i ^ 2 := hcs
      _ ≤ r ^ 2 * B ^ 2 := mul_le_mul hθ hv (Finset.sum_nonneg fun i _ ↦ sq_nonneg _)
          (by positivity)
      _ = (r * B) ^ 2 := by ring
  exact abs_le_of_sq_le_sq' h1 (by positivity) |>.2 |> fun h ↦ abs_le.2 ⟨by
    have := abs_le_of_sq_le_sq' h1 (by positivity); linarith [this.1], h⟩

variable {m₀ : J → ℝ} {B r : ℝ} (hB0 : 0 ≤ B) (hr0 : 0 ≤ r)
  (hB : ∀ᵐ x ∂ν, dotJ (statPoint S x - m₀) (statPoint S x - m₀) ≤ B ^ 2)
include hB0 hr0 hB

omit [Nonempty X] [IsProbabilityMeasure ν] hS in
/-- The exponential weight of a bounded natural coordinate is pinched between `e^{∓Br}` times a
constant, almost surely. -/
theorem exp_neg_dirLoss_bounds {θ : J → ℝ} (hθ : dotJ θ θ ≤ r ^ 2) :
    ∀ᵐ x ∂ν, Real.exp (-dotJ θ m₀) * Real.exp (-(r * B)) ≤ Real.exp (-dirLoss S θ x) ∧
      Real.exp (-dirLoss S θ x) ≤ Real.exp (-dotJ θ m₀) * Real.exp (r * B) := by
  filter_upwards [hB] with x hx
  have e : dirLoss S θ x = dotJ θ m₀ + dotJ θ (statPoint S x - m₀) := by
    rw [← (isLinearMap_dotJ θ).map_add, add_sub_cancel]
    rfl
  have hcs := abs_dotJ_le_of_sq_le hr0 hB0 hθ hx
  rw [abs_le] at hcs
  constructor
  · rw [← Real.exp_add, e]
    exact Real.exp_le_exp.2 (by linarith [hcs.2])
  · rw [← Real.exp_add, e]
    exact Real.exp_le_exp.2 (by linarith [hcs.1])

/-- **The density of a family member relative to the reference law is at least `e^{−2Br}`** on the
parameter region `⟨θ,θ⟩ ≤ r²`: for every nonnegative bounded statistic,
`E_{P_θ} φ ≥ e^{−2Br} E_ν φ`. -/
theorem integral_familyMeasure_ge {θ : J → ℝ} (hθ : dotJ θ θ ≤ r ^ 2) {φ : X → ℝ} (hφ : Bdd φ)
    (hφ0 : ∀ x, 0 ≤ φ x) :
    Real.exp (-(2 * (r * B))) * ∫ x, φ x ∂ν ≤
      ∫ x, φ x ∂familyMeasure ν (fun _ ↦ (1 : ℝ)) (fun _ ↦ (0 : ℝ)) S 1 θ := by
  have h0 : ∀ x, |(fun _ : X ↦ (0 : ℝ)) x| ≤ 0 := fun x ↦ by simp
  have hfam : familyMeasure ν (fun _ ↦ (1 : ℝ)) (fun _ ↦ (0 : ℝ)) S 1 θ =
      ν.tilted (fun x ↦ -(1 : ℝ) * dirLoss S θ x) := by
    rw [familyMeasure_eq_tilted measurable_const (integrable_const 1) (fun _ ↦ one_pos)
      (one_integral_pos ν) measurable_const h0 hS one_pos θ, familyMeasure_one_zero]
  rw [hfam, integral_tilted]
  simp only [neg_one_mul, smul_eq_mul]
  -- the normaliser is at most `e^{−⟨θ,m₀⟩} e^{Br}`
  have hbounds := exp_neg_dirLoss_bounds ν hB0 hr0 hB hθ
  have hZle : ∫ x, Real.exp (-dirLoss S θ x) ∂ν ≤ Real.exp (-dotJ θ m₀) * Real.exp (r * B) := by
    have hint : Integrable (fun x ↦ Real.exp (-dirLoss S θ x)) ν := by
      have := integrable_exp_of_bdd ν (Bdd.const_mul (-1) (bdd_dirLoss hS θ))
      simpa only [neg_one_mul] using this
    calc ∫ x, Real.exp (-dirLoss S θ x) ∂ν
        ≤ ∫ _, Real.exp (-dotJ θ m₀) * Real.exp (r * B) ∂ν :=
          integral_mono_ae hint (integrable_const _) (hbounds.mono fun x hx ↦ hx.2)
      _ = Real.exp (-dotJ θ m₀) * Real.exp (r * B) := by
          rw [integral_const]
          simp [measureReal_def]
  have hZpos : 0 < ∫ x, Real.exp (-dirLoss S θ x) ∂ν := by
    have := integrable_exp_of_bdd ν (Bdd.const_mul (-1) (bdd_dirLoss hS θ))
    simp only [neg_one_mul] at this
    exact integral_exp_pos this
  -- pointwise: `e^{−⟨θ,S⟩}/Z ≥ e^{−2Br}`
  have hpt : ∀ᵐ x ∂ν, Real.exp (-(2 * (r * B))) * φ x ≤
      Real.exp (-dirLoss S θ x) / (∫ x, Real.exp (-dirLoss S θ x) ∂ν) * φ x := by
    filter_upwards [hbounds] with x hx
    refine mul_le_mul_of_nonneg_right ?_ (hφ0 x)
    rw [le_div_iff₀ hZpos]
    calc Real.exp (-(2 * (r * B))) * ∫ x, Real.exp (-dirLoss S θ x) ∂ν
        ≤ Real.exp (-(2 * (r * B))) * (Real.exp (-dotJ θ m₀) * Real.exp (r * B)) :=
          mul_le_mul_of_nonneg_left hZle (Real.exp_pos _).le
      _ = Real.exp (-dotJ θ m₀) * Real.exp (-(r * B)) := by
          rw [← Real.exp_add, ← Real.exp_add, ← Real.exp_add]
          congr 1
          ring
      _ ≤ Real.exp (-dirLoss S θ x) := hx.1
  have hint1 : Integrable (fun x ↦ Real.exp (-(2 * (r * B))) * φ x) ν :=
    (integrable_of_bdd_prob ν hφ).const_mul _
  have hint2 : Integrable (fun x ↦ Real.exp (-dirLoss S θ x) /
      (∫ x, Real.exp (-dirLoss S θ x) ∂ν) * φ x) ν := by
    have hb : Bdd fun x ↦ Real.exp (-dirLoss S θ x) / ∫ x, Real.exp (-dirLoss S θ x) ∂ν := by
      obtain ⟨hm, K, hK⟩ := bdd_dirLoss hS θ
      refine ⟨by fun_prop, Real.exp K / ∫ x, Real.exp (-dirLoss S θ x) ∂ν, fun x ↦ ?_⟩
      rw [abs_of_nonneg (div_nonneg (Real.exp_pos _).le hZpos.le)]
      refine div_le_div_of_nonneg_right ?_ hZpos.le
      exact Real.exp_le_exp.2 (by linarith [(abs_le.1 (hK x)).1])
    exact integrable_of_bdd_prob ν (hb.mul hφ)
  rw [← integral_const_mul]
  exact integral_mono_ae hint1 hint2 hpt

/-- **Variance comparison on a bounded parameter region**:
`Var_{P_θ}(g) ≥ e^{−2Br} Var_ν(g)` for `⟨θ,θ⟩ ≤ r²`. -/
theorem lawCov_familyMeasure_ge {θ : J → ℝ} (hθ : dotJ θ θ ≤ r ^ 2) {g : X → ℝ} (hg : Bdd g) :
    Real.exp (-(2 * (r * B))) * lawCov ν g g ≤
      lawCov (familyMeasure ν (fun _ ↦ (1 : ℝ)) (fun _ ↦ (0 : ℝ)) S 1 θ) g g := by
  have h0 : ∀ x, |(fun _ : X ↦ (0 : ℝ)) x| ≤ 0 := fun x ↦ by simp
  have hP := isProbabilityMeasure_familyMeasure measurable_const (integrable_const 1)
    (fun _ ↦ one_pos) (one_integral_pos ν) measurable_const h0 hS (t := 1) θ
  obtain ⟨c, hc⟩ : ∃ c : ℝ,
      c = ∫ x, g x ∂familyMeasure ν (fun _ ↦ (1 : ℝ)) (fun _ ↦ (0 : ℝ)) S 1 θ := ⟨_, rfl⟩
  have hφ : Bdd fun x ↦ (g x - c) * (g x - c) := (hg.sub (Bdd.const c)).mul (hg.sub (Bdd.const c))
  -- under `P_θ` the variance is the second moment about its own mean
  have hvar : lawCov (familyMeasure ν (fun _ ↦ (1 : ℝ)) (fun _ ↦ (0 : ℝ)) S 1 θ) g g =
      ∫ x, (g x - c) * (g x - c) ∂familyMeasure ν (fun _ ↦ (1 : ℝ)) (fun _ ↦ (0 : ℝ)) S 1 θ := by
    have hi := integrable_of_bdd_prob (familyMeasure ν (fun _ ↦ (1 : ℝ)) (fun _ ↦ (0 : ℝ)) S 1 θ) hg
    have hi2 := integrable_of_bdd_prob (familyMeasure ν (fun _ ↦ (1 : ℝ)) (fun _ ↦ (0 : ℝ)) S 1 θ)
      (hg.mul hg)
    have e : ∀ x, (g x - c) * (g x - c) = g x * g x - (2 * c) * g x + c ^ 2 := fun x ↦ by ring
    simp_rw [e]
    have hA : Integrable (fun x ↦ g x * g x - (2 * c) * g x)
        (familyMeasure ν (fun _ ↦ (1 : ℝ)) (fun _ ↦ (0 : ℝ)) S 1 θ) := hi2.sub (hi.const_mul _)
    rw [integral_add hA (integrable_const _), integral_sub hi2 (hi.const_mul _), integral_const_mul,
      integral_const]
    simp only [measureReal_def, measure_univ, ENNReal.toReal_one, smul_eq_mul, one_mul, lawCov]
    rw [← hc]
    ring
  rw [hvar]
  calc Real.exp (-(2 * (r * B))) * lawCov ν g g
      ≤ Real.exp (-(2 * (r * B))) * ∫ x, (g x - c) * (g x - c) ∂ν :=
        mul_le_mul_of_nonneg_left (lawCov_self_le_integral_sq ν hg c) (Real.exp_pos _).le
    _ ≤ _ := integral_familyMeasure_ge hS ν hB0 hr0 hB hθ hφ fun x ↦ mul_self_nonneg _

end Laplace.Multi
