/-
Copyright (c) 2026 Timaeus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Timaeus
-/
import Laplace.Multi.ResponseLocalTesting
import Laplace.Multi.PolyhedralRecovery
import Laplace.Multi.NormalGeometry

/-!
# `L¹` stability of covariance forms, uniformly on bounded sets and under bounded tilts

For two laws `Q₁ = q₁ ν`, `Q₂ = q₂ ν` with densities, bounded observables have `L¹`-stable
expectations, `|E_{Q₁} F − E_{Q₂} F| ≤ ‖F‖_∞ ‖q₁ − q₂‖₁` (`abs_integral_withDensity_sub_le`), hence
`L¹`-stable covariances,

`|Cov_{Q₁}(f,g) − Cov_{Q₂}(f,g)| ≤ 3 ‖f‖_∞ ‖g‖_∞ ‖q₁ − q₂‖₁`   (`abs_lawCov_withDensity_sub_le`),

and for the visible contrasts `⟨w,S⟩` with `‖S − a‖₂ ≤ B`

`|Var_{Q₁}⟨w,S⟩ − Var_{Q₂}⟨w,S⟩| ≤ 3 B² ‖w‖₂² ‖q₁ − q₂‖₁`   (`abs_lawCov_dirLoss_sub_le`):

`L¹` convergence of laws gives **uniform convergence of the covariance forms on bounded sets** of
directions, hence on compacts (`abs_lawCov_dirLoss_sub_le_of_le`). Under a common bounded tilt
`h` the `L¹` distance of the tilted densities is controlled by `2 e^{2‖h‖_∞} ‖q₁ − q₂‖₁`
(`integral_abs_tiltedDens_sub_le`), so the convergence is uniform over all common tilts bounded by a
constant. This is the continuity input for the response forms along the data manifold.
-/

open MeasureTheory Filter Topology Set

namespace Laplace.Multi

section Density

variable {X : Type*} [MeasurableSpace X] (ν : Measure X) [IsProbabilityMeasure ν]

variable {q₁ q₂ : X → ℝ} (hq₁m : Measurable q₁) (hq₁0 : ∀ x, 0 ≤ q₁ x) (hq₁i : Integrable q₁ ν)
  (hq₂m : Measurable q₂) (hq₂0 : ∀ x, 0 ≤ q₂ x) (hq₂i : Integrable q₂ ν)
include hq₁m hq₁0 hq₁i hq₂m hq₂0 hq₂i

omit [IsProbabilityMeasure ν] in
/-- **Bounded observables have `L¹`-stable expectations.** -/
theorem abs_integral_withDensity_sub_le {F : X → ℝ} (hF : Measurable F) {K : ℝ}
    (hK : ∀ x, |F x| ≤ K) :
    |(∫ x, F x ∂(ν.withDensity fun x ↦ ENNReal.ofReal (q₁ x))) -
        ∫ x, F x ∂(ν.withDensity fun x ↦ ENNReal.ofReal (q₂ x))| ≤
      K * ∫ x, |q₁ x - q₂ x| ∂ν := by
  rw [integral_withDensity_ofReal ν hq₁m hq₁0 F, integral_withDensity_ofReal ν hq₂m hq₂0 F]
  have h1 : Integrable (fun x ↦ q₁ x * F x) ν :=
    hq₁i.mul_bdd hF.aestronglyMeasurable (Eventually.of_forall fun x ↦ by
      rw [Real.norm_eq_abs]; exact hK x)
  have h2 : Integrable (fun x ↦ q₂ x * F x) ν :=
    hq₂i.mul_bdd hF.aestronglyMeasurable (Eventually.of_forall fun x ↦ by
      rw [Real.norm_eq_abs]; exact hK x)
  have h12 : Integrable (fun x ↦ (q₁ x - q₂ x) * F x) ν :=
    (h1.sub h2).congr (Eventually.of_forall fun x ↦ by simp only [Pi.sub_apply]; ring)
  have hn := norm_integral_le_integral_norm (μ := ν) (fun x ↦ (q₁ x - q₂ x) * F x)
  simp only [Real.norm_eq_abs] at hn
  calc |(∫ x, q₁ x * F x ∂ν) - ∫ x, q₂ x * F x ∂ν| = |∫ x, (q₁ x - q₂ x) * F x ∂ν| := by
        rw [← integral_sub h1 h2]
        congr 1
        exact integral_congr_ae (Eventually.of_forall fun x ↦ by ring)
    _ ≤ ∫ x, |(q₁ x - q₂ x) * F x| ∂ν := hn
    _ ≤ ∫ x, |q₁ x - q₂ x| * K ∂ν :=
        integral_mono h12.abs ((hq₁i.sub hq₂i).abs.mul_const K) fun x ↦ by
          rw [abs_mul]
          exact mul_le_mul_of_nonneg_left (hK x) (abs_nonneg _)
    _ = K * ∫ x, |q₁ x - q₂ x| ∂ν := by rw [integral_mul_const, mul_comm]

variable (hq₁1 : ∫ x, q₁ x ∂ν = 1) (hq₂1 : ∫ x, q₂ x ∂ν = 1)
include hq₁1 hq₂1

omit [IsProbabilityMeasure ν] in
/-- **Covariances are `L¹`-stable**:
`|Cov_{Q₁}(f,g) − Cov_{Q₂}(f,g)| ≤ 3 ‖f‖_∞ ‖g‖_∞ ‖q₁ − q₂‖₁`. -/
theorem abs_lawCov_withDensity_sub_le {f g : X → ℝ} (hf : Measurable f) (hg : Measurable g)
    {K L : ℝ} (hK0 : 0 ≤ K) (hK : ∀ x, |f x| ≤ K) (hL : ∀ x, |g x| ≤ L) :
    |lawCov (ν.withDensity fun x ↦ ENNReal.ofReal (q₁ x)) f g -
        lawCov (ν.withDensity fun x ↦ ENNReal.ofReal (q₂ x)) f g| ≤
      3 * K * L * ∫ x, |q₁ x - q₂ x| ∂ν := by
  have hP₁ := isProbabilityMeasure_withDensity_ofReal ν hq₁0 hq₁i hq₁1
  have hP₂ := isProbabilityMeasure_withDensity_ofReal ν hq₂0 hq₂i hq₂1
  have hfg := abs_integral_withDensity_sub_le ν hq₁m hq₁0 hq₁i hq₂m hq₂0 hq₂i
    (F := fun x ↦ f x * g x) (hf.mul hg) (K := K * L) fun x ↦ by
      rw [abs_mul]
      exact mul_le_mul (hK x) (hL x) (abs_nonneg _) hK0
  have hf' := abs_integral_withDensity_sub_le ν hq₁m hq₁0 hq₁i hq₂m hq₂0 hq₂i hf hK
  have hg' := abs_integral_withDensity_sub_le ν hq₁m hq₁0 hq₁i hq₂m hq₂0 hq₂i hg hL
  have hb₁ : |∫ x, f x ∂(ν.withDensity fun x ↦ ENNReal.ofReal (q₁ x))| ≤ K := by
    have := norm_integral_le_of_norm_le_const (μ := ν.withDensity fun x ↦ ENNReal.ofReal (q₁ x))
      (f := f) (C := K) (Eventually.of_forall fun x ↦ by rw [Real.norm_eq_abs]; exact hK x)
    simpa [probReal_univ] using this
  have hb₂ : |∫ x, g x ∂(ν.withDensity fun x ↦ ENNReal.ofReal (q₂ x))| ≤ L := by
    have := norm_integral_le_of_norm_le_const (μ := ν.withDensity fun x ↦ ENNReal.ofReal (q₂ x))
      (f := g) (C := L) (Eventually.of_forall fun x ↦ by rw [Real.norm_eq_abs]; exact hL x)
    simpa [probReal_univ] using this
  set d := ∫ x, |q₁ x - q₂ x| ∂ν with hd
  set A₁ := ∫ x, f x * g x ∂(ν.withDensity fun x ↦ ENNReal.ofReal (q₁ x)) with hA₁
  set A₂ := ∫ x, f x * g x ∂(ν.withDensity fun x ↦ ENNReal.ofReal (q₂ x)) with hA₂
  set a₁ := ∫ x, f x ∂(ν.withDensity fun x ↦ ENNReal.ofReal (q₁ x)) with ha₁
  set a₂ := ∫ x, f x ∂(ν.withDensity fun x ↦ ENNReal.ofReal (q₂ x)) with ha₂
  set b₁ := ∫ x, g x ∂(ν.withDensity fun x ↦ ENNReal.ofReal (q₁ x)) with hb₁'
  set b₂ := ∫ x, g x ∂(ν.withDensity fun x ↦ ENNReal.ofReal (q₂ x)) with hb₂'
  have e : lawCov (ν.withDensity fun x ↦ ENNReal.ofReal (q₁ x)) f g -
      lawCov (ν.withDensity fun x ↦ ENNReal.ofReal (q₂ x)) f g =
      (A₁ - A₂) - (a₁ * (b₁ - b₂) + (a₁ - a₂) * b₂) := by
    simp only [lawCov]
    ring
  rw [e]
  calc |(A₁ - A₂) - (a₁ * (b₁ - b₂) + (a₁ - a₂) * b₂)| ≤
        |A₁ - A₂| + |a₁ * (b₁ - b₂) + (a₁ - a₂) * b₂| := abs_sub _ _
    _ ≤ |A₁ - A₂| + (|a₁| * |b₁ - b₂| + |a₁ - a₂| * |b₂|) :=
        add_le_add le_rfl ((abs_add_le _ _).trans (by rw [abs_mul, abs_mul]))
    _ ≤ K * L * d + (K * (L * d) + K * d * L) :=
        add_le_add hfg (add_le_add (mul_le_mul hb₁ hg' (abs_nonneg _) hK0)
          (mul_le_mul hf' hb₂ (abs_nonneg _) (by positivity)))
    _ = 3 * K * L * d := by ring

end Density

section Visible

variable {X : Type*} [MeasurableSpace X] {J : Type*} [Fintype J] {S : J → X → ℝ}
  (hS : ∀ j, Bdd (S j)) (ν : Measure X)
  {q₁ q₂ : X → ℝ} (hq₁m : Measurable q₁) (hq₁0 : ∀ x, 0 ≤ q₁ x) (hq₁i : Integrable q₁ ν)
  (hq₁1 : ∫ x, q₁ x ∂ν = 1) (hq₂m : Measurable q₂) (hq₂0 : ∀ x, 0 ≤ q₂ x)
  (hq₂i : Integrable q₂ ν) (hq₂1 : ∫ x, q₂ x ∂ν = 1)
include hS hq₁m hq₁0 hq₁i hq₁1 hq₂m hq₂0 hq₂i hq₂1

/-- **The visible variances are `L¹`-stable, uniformly on bounded sets of directions**:
with `‖S − a‖₂ ≤ B`, `|Var_{Q₁}⟨w,S⟩ − Var_{Q₂}⟨w,S⟩| ≤ 3 B² ‖w‖₂² ‖q₁ − q₂‖₁`. -/
theorem abs_lawCov_dirLoss_sub_le {a : J → ℝ} {B : ℝ} (hB0 : 0 ≤ B)
    (hB : ∀ x, dotJ (statPoint S x - a) (statPoint S x - a) ≤ B ^ 2) (w : J → ℝ) :
    |lawCov (ν.withDensity fun x ↦ ENNReal.ofReal (q₁ x)) (dirLoss S w) (dirLoss S w) -
        lawCov (ν.withDensity fun x ↦ ENNReal.ofReal (q₂ x)) (dirLoss S w) (dirLoss S w)| ≤
      3 * B ^ 2 * dotJ w w * ∫ x, |q₁ x - q₂ x| ∂ν := by
  have hP₁ := isProbabilityMeasure_withDensity_ofReal ν hq₁0 hq₁i hq₁1
  have hP₂ := isProbabilityMeasure_withDensity_ofReal ν hq₂0 hq₂i hq₂1
  have hww := dotJ_self_nonneg w
  have hK : ∀ x, |dirLoss S w x - dotJ w a| ≤ √(dotJ w w) * B := fun x ↦ by
    rw [dirLoss_eq_dotJ_statPoint, ← (isLinearMap_dotJ w).map_sub, ← Real.sqrt_sq_eq_abs]
    calc √(dotJ w (statPoint S x - a) ^ 2) ≤
          √(dotJ w w * dotJ (statPoint S x - a) (statPoint S x - a)) :=
          Real.sqrt_le_sqrt (sq_dotJ_le _ _)
      _ ≤ √(dotJ w w * B ^ 2) := Real.sqrt_le_sqrt (mul_le_mul_of_nonneg_left (hB x) hww)
      _ = √(dotJ w w) * B := by rw [Real.sqrt_mul hww, Real.sqrt_sq hB0]
  rw [← lawCov_sub_const_self _ (bdd_dirLoss hS w) (dotJ w a),
    ← lawCov_sub_const_self _ (bdd_dirLoss hS w) (dotJ w a)]
  have h := abs_lawCov_withDensity_sub_le ν hq₁m hq₁0 hq₁i hq₂m hq₂0 hq₂i hq₁1 hq₂1
    ((bdd_dirLoss hS w).1.sub measurable_const) ((bdd_dirLoss hS w).1.sub measurable_const)
    (by positivity) hK hK
  refine h.trans (le_of_eq ?_)
  have hs := Real.mul_self_sqrt hww
  linear_combination (3 * B ^ 2 * ∫ x, |q₁ x - q₂ x| ∂ν) * hs

/-- **Compact-uniform `L¹` stability**: on `‖w‖₂ ≤ R` the visible variances differ by at most
`3 B² R² ‖q₁ − q₂‖₁`. -/
theorem abs_lawCov_dirLoss_sub_le_of_le {a : J → ℝ} {B : ℝ} (hB0 : 0 ≤ B)
    (hB : ∀ x, dotJ (statPoint S x - a) (statPoint S x - a) ≤ B ^ 2) {R : ℝ} {w : J → ℝ}
    (hw : dotJ w w ≤ R ^ 2) :
    |lawCov (ν.withDensity fun x ↦ ENNReal.ofReal (q₁ x)) (dirLoss S w) (dirLoss S w) -
        lawCov (ν.withDensity fun x ↦ ENNReal.ofReal (q₂ x)) (dirLoss S w) (dirLoss S w)| ≤
      3 * B ^ 2 * R ^ 2 * ∫ x, |q₁ x - q₂ x| ∂ν := by
  refine (abs_lawCov_dirLoss_sub_le hS ν hq₁m hq₁0 hq₁i hq₁1 hq₂m hq₂0 hq₂i hq₂1 hB0 hB w).trans ?_
  have hd : 0 ≤ ∫ x, |q₁ x - q₂ x| ∂ν := integral_nonneg fun x ↦ abs_nonneg _
  have : 3 * B ^ 2 * dotJ w w ≤ 3 * B ^ 2 * R ^ 2 :=
    mul_le_mul_of_nonneg_left hw (by positivity)
  exact mul_le_mul_of_nonneg_right this hd

end Visible

section Tilt

variable {X : Type*} [MeasurableSpace X] (ν : Measure X) [IsProbabilityMeasure ν]

/-- The tilted density `e^h q / ∫ e^h q`. -/
noncomputable def tiltedDens (h q : X → ℝ) (x : X) : ℝ :=
  q x * Real.exp (h x) / ∫ y, q y * Real.exp (h y) ∂ν

variable {q : X → ℝ} (hq0 : ∀ x, 0 ≤ q x) (hqi : Integrable q ν) (hq1 : ∫ x, q x ∂ν = 1)
  {h : X → ℝ} (hh : Bdd h) {K : ℝ} (hK : ∀ x, |h x| ≤ K)
include hh hK

omit [IsProbabilityMeasure ν] hq0 hq1 in
theorem integrable_mul_exp (hqi : Integrable q ν) : Integrable (fun x ↦ q x * Real.exp (h x)) ν :=
  hqi.mul_bdd hh.1.exp.aestronglyMeasurable (Eventually.of_forall fun x ↦ by
    rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
    exact Real.exp_le_exp.2 (abs_le.1 (hK x)).2)

omit [IsProbabilityMeasure ν] in
include hq0 hqi hq1 in
/-- The tilt normaliser is at least `e^{−K}`. -/
theorem exp_neg_le_integral_mul_exp : Real.exp (-K) ≤ ∫ x, q x * Real.exp (h x) ∂ν := by
  calc Real.exp (-K) = ∫ x, q x * Real.exp (-K) ∂ν := by rw [integral_mul_const, hq1, one_mul]
    _ ≤ ∫ x, q x * Real.exp (h x) ∂ν :=
        integral_mono (hqi.mul_const _) (integrable_mul_exp ν hh hK hqi) fun x ↦
          mul_le_mul_of_nonneg_left (Real.exp_le_exp.2 (abs_le.1 (hK x)).1) (hq0 x)

end Tilt

section TiltStability

variable {X : Type*} [MeasurableSpace X] (ν : Measure X) [IsProbabilityMeasure ν]
  {q₁ q₂ : X → ℝ} (hq₁0 : ∀ x, 0 ≤ q₁ x) (hq₁i : Integrable q₁ ν) (hq₁1 : ∫ x, q₁ x ∂ν = 1)
  (hq₂0 : ∀ x, 0 ≤ q₂ x) (hq₂i : Integrable q₂ ν) (hq₂1 : ∫ x, q₂ x ∂ν = 1)
  {h : X → ℝ} (hh : Bdd h) {K : ℝ} (hK : ∀ x, |h x| ≤ K)
include hq₁0 hq₁i hq₁1 hq₂0 hq₂i hq₂1 hh hK

omit [IsProbabilityMeasure ν] in
/-- **Tilting is uniformly `L¹`-continuous over bounded common tilts**:
`‖tilt_h q₁ − tilt_h q₂‖₁ ≤ 2 e^{2K} ‖q₁ − q₂‖₁` for `|h| ≤ K`. -/
theorem integral_abs_tiltedDens_sub_le :
    ∫ x, |tiltedDens ν h q₁ x - tiltedDens ν h q₂ x| ∂ν ≤
      2 * Real.exp (2 * K) * ∫ x, |q₁ x - q₂ x| ∂ν := by
  set Z₁ := ∫ y, q₁ y * Real.exp (h y) ∂ν with hZ₁def
  set Z₂ := ∫ y, q₂ y * Real.exp (h y) ∂ν with hZ₂def
  set d := ∫ x, |q₁ x - q₂ x| ∂ν with hd
  have hZ₁lo : Real.exp (-K) ≤ Z₁ := exp_neg_le_integral_mul_exp ν hq₁0 hq₁i hq₁1 hh hK
  have hZ₂lo : Real.exp (-K) ≤ Z₂ := exp_neg_le_integral_mul_exp ν hq₂0 hq₂i hq₂1 hh hK
  have hZ₁ : 0 < Z₁ := (Real.exp_pos _).trans_le hZ₁lo
  have hZ₂ : 0 < Z₂ := (Real.exp_pos _).trans_le hZ₂lo
  have hinvZ₁ : Z₁⁻¹ ≤ Real.exp K := by
    rw [inv_le_comm₀ hZ₁ (Real.exp_pos _), ← Real.exp_neg]
    exact hZ₁lo
  have hexp : ∀ x, Real.exp (h x) ≤ Real.exp K := fun x ↦ Real.exp_le_exp.2 (abs_le.1 (hK x)).2
  have i₁ := integrable_mul_exp ν hh hK hq₁i
  have i₂ := integrable_mul_exp ν hh hK hq₂i
  have hd0 : 0 ≤ d := integral_nonneg fun x ↦ abs_nonneg _
  -- the normalisers are `L¹`-close
  have hZd : |Z₁ - Z₂| ≤ Real.exp K * d := by
    have hn := norm_integral_le_integral_norm (μ := ν) (fun x ↦ (q₁ x - q₂ x) * Real.exp (h x))
    simp only [Real.norm_eq_abs] at hn
    calc |Z₁ - Z₂| = |∫ x, (q₁ x - q₂ x) * Real.exp (h x) ∂ν| := by
          rw [hZ₁def, hZ₂def, ← integral_sub i₁ i₂]
          congr 1
          exact integral_congr_ae (Eventually.of_forall fun x ↦ by ring)
      _ ≤ ∫ x, |(q₁ x - q₂ x) * Real.exp (h x)| ∂ν := hn
      _ ≤ ∫ x, |q₁ x - q₂ x| * Real.exp K ∂ν :=
          integral_mono ((i₁.sub i₂).congr (Eventually.of_forall fun x ↦ by
              simp only [Pi.sub_apply]; ring)).abs
            ((hq₁i.sub hq₂i).abs.mul_const _) fun x ↦ by
              rw [abs_mul, abs_of_pos (Real.exp_pos _)]
              exact mul_le_mul_of_nonneg_left (hexp x) (abs_nonneg _)
      _ = Real.exp K * d := by rw [integral_mul_const, mul_comm]
  -- pointwise bound
  have hpt : ∀ x, |tiltedDens ν h q₁ x - tiltedDens ν h q₂ x| ≤
      |q₁ x - q₂ x| * Real.exp K * Z₁⁻¹ + q₂ x * Real.exp (h x) * (|Z₁ - Z₂| * (Z₁⁻¹ * Z₂⁻¹)) :=
    fun x ↦ by
    have e : tiltedDens ν h q₁ x - tiltedDens ν h q₂ x =
        (q₁ x - q₂ x) * Real.exp (h x) * Z₁⁻¹ +
          q₂ x * Real.exp (h x) * ((Z₂ - Z₁) * (Z₁⁻¹ * Z₂⁻¹)) := by
      simp only [tiltedDens, ← hZ₁def, ← hZ₂def]
      field_simp
      ring
    rw [e]
    refine (abs_add_le _ _).trans (add_le_add ?_ ?_)
    · rw [abs_mul, abs_mul, abs_of_pos (Real.exp_pos _), abs_of_pos (inv_pos.2 hZ₁)]
      exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left (hexp x) (abs_nonneg _))
        (inv_pos.2 hZ₁).le
    · rw [abs_mul, abs_mul, abs_mul, abs_of_nonneg (hq₂0 x), abs_of_pos (Real.exp_pos _),
        abs_sub_comm Z₂ Z₁, abs_of_pos (mul_pos (inv_pos.2 hZ₁) (inv_pos.2 hZ₂))]
  have hint₁ : Integrable (fun x ↦ |q₁ x - q₂ x| * Real.exp K * Z₁⁻¹) ν :=
    ((hq₁i.sub hq₂i).abs.mul_const _).mul_const _
  have hint₂ : Integrable (fun x ↦ q₂ x * Real.exp (h x) * (|Z₁ - Z₂| * (Z₁⁻¹ * Z₂⁻¹))) ν :=
    i₂.mul_const _
  have hintL : Integrable (fun x ↦ |tiltedDens ν h q₁ x - tiltedDens ν h q₂ x|) ν := by
    have : Integrable (fun x ↦ tiltedDens ν h q₁ x - tiltedDens ν h q₂ x) ν := by
      simp only [tiltedDens, ← hZ₁def, ← hZ₂def]
      exact (i₁.div_const _).sub (i₂.div_const _)
    exact this.abs
  calc ∫ x, |tiltedDens ν h q₁ x - tiltedDens ν h q₂ x| ∂ν ≤
        ∫ x, (|q₁ x - q₂ x| * Real.exp K * Z₁⁻¹ +
          q₂ x * Real.exp (h x) * (|Z₁ - Z₂| * (Z₁⁻¹ * Z₂⁻¹))) ∂ν :=
        integral_mono hintL (hint₁.add hint₂) hpt
    _ = d * Real.exp K * Z₁⁻¹ + Z₂ * (|Z₁ - Z₂| * (Z₁⁻¹ * Z₂⁻¹)) := by
        rw [integral_add hint₁ hint₂, integral_mul_const, integral_mul_const, integral_mul_const]
    _ = d * Real.exp K * Z₁⁻¹ + |Z₁ - Z₂| * Z₁⁻¹ := by
        congr 1
        field_simp
    _ ≤ d * Real.exp K * Real.exp K + Real.exp K * d * Real.exp K :=
        add_le_add (mul_le_mul_of_nonneg_left hinvZ₁ (by positivity))
          (mul_le_mul hZd hinvZ₁ (inv_pos.2 hZ₁).le (by positivity))
    _ = 2 * Real.exp (2 * K) * d := by
        rw [show (2 : ℝ) * K = K + K by ring, Real.exp_add]
        ring

end TiltStability

end Laplace.Multi
