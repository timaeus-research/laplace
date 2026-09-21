/-
Copyright (c) 2026 Timaeus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib
import Laplace.Multi.MorseBottLeading

/-!
# Curved Morse–Bott zero manifolds as graphs: transport to adapted coordinates

The zero manifold is now the graph `W = {x = φ(y)}` of a continuous `φ : ℝⁿ → ℝʳ`, in ambient
coordinates `(x, y)`, and the loss is `L(x, y) = ½ (x - φ(y))ᵀ H(y) (x - φ(y)) + R(x - φ(y), y)`
with the transverse cutoff centred on the graph, `χ₁(x - φ(y)) χ₂(y)`. The fibrewise translation
`(x, y) ↦ (x - φ(y), y)` (`graphShift`) preserves Lebesgue measure (a skew product of the identity
with translations, `graphShift_measurePreserving`), so every curved expectation is an adapted
one of the transported test (`mbcExp_eq`): no manifold change of variables is needed.

For a general continuous test `G` the adapted leading order is
`(√t)^r ∫ G w_t → ∫ G(0, y) χ₂ ρ_H` (`tendsto_sqrt_pow_mul_integral_cont`, dominated convergence
with the bound of `G` on the compact set `closedBall 0 δ ×ˢ tsupport χ₂`). Hence, in the curved
model (`tendsto_mbcExp`, `tendsto_mul_mbcExp_centred_second`):

* `E_t[F] → ∫ F(φ(y), y) dμ`, `dμ = χ₂ ρ_H dy / ∫ χ₂ ρ_H`: every continuous ambient test sees the
  Morse–Bott measure pushed forward to the graph, `ι_# μ` with `ι(y) = (φ(y), y)`;
* `t E_t[(x - φ(y))ᵢ (x - φ(y))ₖ g(y)] → ∫ g (H⁻¹)ᵢₖ dμ`: the centred rescaled second moments see
  the transverse covariance in the graph coordinates;
* the free energy is unchanged: `-log Z_t - (r/2) log t → -log ∫ χ₂ ρ_H`.

Identification given the graph (`mbc_identification_of_graph`): two curved models over the same
graph with eventually equal tangential and centred second-moment expectations have equal Hessian
fields on `{χ₂ ≠ 0}`. Not done: recovering `H` from *ambient polynomial* data alone — the centred
observables are not ambient polynomials (Astra, `research_germbij_next_arc_v1`: the
"ambient-polynomial bridge").
-/

open Real MeasureTheory Filter Topology
open scoped Matrix

namespace Laplace.Multi

variable {r n : ℕ}

/-! ### The fibrewise translation -/

/-- `(x, y) ↦ (x - φ(y), y)`. -/
def graphShift (φ : EuclidD n → EuclidD r) (z : EuclidD r × EuclidD n) : EuclidD r × EuclidD n :=
  (z.1 - φ z.2, z.2)

/-- `(z, y) ↦ (z + φ(y), y)`. -/
def graphUnshift (φ : EuclidD n → EuclidD r) (z : EuclidD r × EuclidD n) :
    EuclidD r × EuclidD n :=
  (z.1 + φ z.2, z.2)

theorem graphUnshift_graphShift (φ : EuclidD n → EuclidD r) (z : EuclidD r × EuclidD n) :
    graphUnshift φ (graphShift φ z) = z := by
  simp [graphShift, graphUnshift]

theorem graphShift_graphUnshift (φ : EuclidD n → EuclidD r) (z : EuclidD r × EuclidD n) :
    graphShift φ (graphUnshift φ z) = z := by
  simp [graphShift, graphUnshift]

/-- The fibrewise translation as a homeomorphism. -/
def graphShiftHomeo {φ : EuclidD n → EuclidD r} (hφ : Continuous φ) :
    (EuclidD r × EuclidD n) ≃ₜ (EuclidD r × EuclidD n) where
  toFun := graphShift φ
  invFun := graphUnshift φ
  left_inv := graphUnshift_graphShift φ
  right_inv := graphShift_graphUnshift φ
  continuous_toFun := by
    unfold graphShift
    fun_prop
  continuous_invFun := by
    unfold graphUnshift
    fun_prop

/-- **The fibrewise translation preserves Lebesgue measure.** -/
theorem graphShift_measurePreserving {φ : EuclidD n → EuclidD r} (hφ : Continuous φ) :
    MeasurePreserving (graphShift φ) (volume : Measure (EuclidD r × EuclidD n)) volume := by
  -- `graphShift φ = swap ∘ S ∘ swap` with `S (y, x) = (y, x - φ y)` a skew product
  have hS : MeasurePreserving (fun p : EuclidD n × EuclidD r ↦ (p.1, p.2 - φ p.1))
      ((volume : Measure (EuclidD n)).prod volume) ((volume : Measure (EuclidD n)).prod volume) :=
    MeasurePreserving.skew_product (MeasurePreserving.id _)
      (g := fun y x ↦ x - φ y)
      (measurable_snd.sub (hφ.measurable.comp measurable_fst))
      (Filter.Eventually.of_forall fun y ↦ (measurePreserving_sub_right volume (φ y)).map_eq)
  have hsw₁ : MeasurePreserving Prod.swap ((volume : Measure (EuclidD r)).prod volume)
      ((volume : Measure (EuclidD n)).prod volume) := Measure.measurePreserving_swap
  have hsw₂ : MeasurePreserving Prod.swap ((volume : Measure (EuclidD n)).prod volume)
      ((volume : Measure (EuclidD r)).prod volume) := Measure.measurePreserving_swap
  have hcomp := hsw₂.comp (hS.comp hsw₁)
  have heq : (Prod.swap ∘ (fun p : EuclidD n × EuclidD r ↦ (p.1, p.2 - φ p.1)) ∘ Prod.swap) =
      graphShift φ := by
    funext z
    simp [graphShift]
  rw [heq] at hcomp
  rw [Measure.volume_eq_prod]
  exact hcomp

/-- Transport of integrals along the fibrewise translation. -/
theorem integral_comp_graphShift {φ : EuclidD n → EuclidD r} (hφ : Continuous φ)
    (G : EuclidD r × EuclidD n → ℝ) : ∫ z, G (graphShift φ z) = ∫ z, G z :=
  (graphShift_measurePreserving hφ).integral_comp (graphShiftHomeo hφ).measurableEmbedding G

/-! ### The curved model -/

/-- The weight `χ₁(x - φ(y)) χ₂(y) e^{-tL(x, y)}` of the curved model. -/
noncomputable def mbcWeight (H : EuclidD n → Matrix (Fin r) (Fin r) ℝ)
    (R : EuclidD r → EuclidD n → ℝ) (φ : EuclidD n → EuclidD r) (χ₁ : EuclidD r → ℝ)
    (χ₂ : EuclidD n → ℝ) (t : ℝ) (z : EuclidD r × EuclidD n) : ℝ :=
  mbgWeight H R χ₁ χ₂ t (graphShift φ z)

/-- The normalised expectation of the curved model. -/
noncomputable def mbcExp (H : EuclidD n → Matrix (Fin r) (Fin r) ℝ)
    (R : EuclidD r → EuclidD n → ℝ) (φ : EuclidD n → EuclidD r) (χ₁ : EuclidD r → ℝ)
    (χ₂ : EuclidD n → ℝ) (t : ℝ) (F : EuclidD r × EuclidD n → ℝ) : ℝ :=
  (∫ z, F z * mbcWeight H R φ χ₁ χ₂ t z) / ∫ z, mbcWeight H R φ χ₁ χ₂ t z

/-- **Transport**: a curved expectation is the adapted expectation of the transported test
`(z, y) ↦ F(z + φ(y), y)`. -/
theorem mbcExp_eq {H : EuclidD n → Matrix (Fin r) (Fin r) ℝ} {R : EuclidD r → EuclidD n → ℝ}
    {φ : EuclidD n → EuclidD r} (hφ : Continuous φ) (χ₁ : EuclidD r → ℝ) (χ₂ : EuclidD n → ℝ)
    (t : ℝ) (F : EuclidD r × EuclidD n → ℝ) :
    mbcExp H R φ χ₁ χ₂ t F = mbgExp H R χ₁ χ₂ t fun z ↦ F (graphUnshift φ z) := by
  unfold mbcExp mbgExp mbcWeight
  have h1 : (∫ z, F z * mbgWeight H R χ₁ χ₂ t (graphShift φ z)) =
      ∫ z, F (graphUnshift φ z) * mbgWeight H R χ₁ χ₂ t z := by
    rw [← integral_comp_graphShift hφ (fun z ↦ F (graphUnshift φ z) * mbgWeight H R χ₁ χ₂ t z)]
    refine integral_congr_ae (Filter.Eventually.of_forall fun z ↦ ?_)
    simp only
    rw [graphUnshift_graphShift]
  have h2 : (∫ z, mbgWeight H R χ₁ χ₂ t (graphShift φ z)) = ∫ z, mbgWeight H R χ₁ χ₂ t z :=
    integral_comp_graphShift hφ _
  rw [h1, h2]

/-! ### Leading order for a general continuous test (adapted model) -/

/-- The support of `G · w_t` lies in `closedBall 0 δ ×ˢ tsupport χ₂`. -/
theorem hasCompactSupport_mul_mbgWeight {H : EuclidD n → Matrix (Fin r) (Fin r) ℝ}
    {R : EuclidD r → EuclidD n → ℝ} {χ₁ : EuclidD r → ℝ} {χ₂ : EuclidD n → ℝ} {c C δ : ℝ}
    (h : MBGenData H R χ₁ χ₂ c C δ) (G : EuclidD r × EuclidD n → ℝ) (t : ℝ) :
    HasCompactSupport fun z : EuclidD r × EuclidD n ↦ G z * mbgWeight H R χ₁ χ₂ t z := by
  have hK : IsCompact ((Metric.closedBall (0 : EuclidD r) δ) ×ˢ tsupport χ₂) :=
    (isCompact_closedBall _ _).prod h.base.χ_supp
  refine IsCompact.of_isClosed_subset hK (isClosed_tsupport _) ?_
  refine closure_minimal ?_ (Metric.isClosed_closedBall.prod (isClosed_tsupport _))
  intro z hz
  rw [Function.mem_support] at hz
  refine ⟨?_, ?_⟩
  · rw [Metric.mem_closedBall, dist_zero_right]
    by_contra hcon
    push Not at hcon
    apply hz
    simp [mbgWeight, h.χ₁_supp _ hcon]
  · by_contra hcon
    apply hz
    simp [mbgWeight, image_eq_zero_of_notMem_tsupport hcon]

theorem continuous_mul_mbgWeight {H : EuclidD n → Matrix (Fin r) (Fin r) ℝ}
    {R : EuclidD r → EuclidD n → ℝ} {χ₁ : EuclidD r → ℝ} {χ₂ : EuclidD n → ℝ} {c C δ : ℝ}
    (h : MBGenData H R χ₁ χ₂ c C δ) {G : EuclidD r × EuclidD n → ℝ} (hG : Continuous G)
    (t : ℝ) : Continuous fun z : EuclidD r × EuclidD n ↦ G z * mbgWeight H R χ₁ χ₂ t z := by
  unfold mbgWeight mbgLoss
  exact hG.mul (((h.χ₁_cont.comp continuous_fst).mul (h.base.χ_cont.comp continuous_snd)).mul
    (Real.continuous_exp.comp (continuous_const.mul
      (((continuous_qform_param h.base.cont).div_const 2).add h.R_cont)).neg))

/-- The scaled inner integral for a general test. -/
noncomputable def innerScaledG (H : EuclidD n → Matrix (Fin r) (Fin r) ℝ)
    (R : EuclidD r → EuclidD n → ℝ) (χ₁ : EuclidD r → ℝ) (G : EuclidD r × EuclidD n → ℝ) (t : ℝ)
    (y : EuclidD n) : ℝ :=
  ∫ u : EuclidD r, G ((Real.sqrt t)⁻¹ • u, y) * χ₁ ((Real.sqrt t)⁻¹ • u) *
    Real.exp (-(qform (H y) u / 2 + t * R ((Real.sqrt t)⁻¹ • u) y))

theorem continuous_scaledG_integrand {H : EuclidD n → Matrix (Fin r) (Fin r) ℝ}
    {R : EuclidD r → EuclidD n → ℝ} {χ₁ : EuclidD r → ℝ} {χ₂ : EuclidD n → ℝ} {c C δ : ℝ}
    (h : MBGenData H R χ₁ χ₂ c C δ) {G : EuclidD r × EuclidD n → ℝ} (hG : Continuous G) (t : ℝ) :
    Continuous fun p : EuclidD n × EuclidD r ↦ G ((Real.sqrt t)⁻¹ • p.2, p.1) *
      χ₁ ((Real.sqrt t)⁻¹ • p.2) *
      Real.exp (-(qform (H p.1) p.2 / 2 + t * R ((Real.sqrt t)⁻¹ • p.2) p.1)) := by
  have hR : Continuous fun p : EuclidD n × EuclidD r ↦ R ((Real.sqrt t)⁻¹ • p.2) p.1 := by
    have := h.R_cont.comp (show Continuous (fun p : EuclidD n × EuclidD r ↦
      ((Real.sqrt t)⁻¹ • p.2, p.1)) by fun_prop)
    exact this
  have hq : Continuous fun p : EuclidD n × EuclidD r ↦ qform (H p.1) p.2 := by
    have := (continuous_qform_param h.base.cont).comp
      (show Continuous (fun p : EuclidD n × EuclidD r ↦ (p.2, p.1)) by fun_prop)
    exact this
  have hG' : Continuous fun p : EuclidD n × EuclidD r ↦ G ((Real.sqrt t)⁻¹ • p.2, p.1) := by
    have := hG.comp (show Continuous (fun p : EuclidD n × EuclidD r ↦
      ((Real.sqrt t)⁻¹ • p.2, p.1)) by fun_prop)
    exact this
  have hχ : Continuous fun p : EuclidD n × EuclidD r ↦ χ₁ ((Real.sqrt t)⁻¹ • p.2) := by
    have := h.χ₁_cont.comp (show Continuous (fun p : EuclidD n × EuclidD r ↦
      (Real.sqrt t)⁻¹ • p.2) by fun_prop)
    exact this
  have hexp : Continuous fun p : EuclidD n × EuclidD r ↦
      Real.exp (-(qform (H p.1) p.2 / 2 + t * R ((Real.sqrt t)⁻¹ • p.2) p.1)) :=
    Real.continuous_exp.comp ((hq.div_const 2).add (continuous_const.mul hR)).neg
  exact (hG'.mul hχ).mul hexp

/-- Dilation identity for a general test: `(√t)^r ∫ G(x, y) χ₁ e^{-tL(x,y)} dx = innerScaledG`. -/
theorem sqrt_pow_mul_integral_eq_innerScaledG {H : EuclidD n → Matrix (Fin r) (Fin r) ℝ}
    {R : EuclidD r → EuclidD n → ℝ} {χ₁ : EuclidD r → ℝ} (G : EuclidD r × EuclidD n → ℝ) {t : ℝ}
    (ht : 0 < t) (y : EuclidD n) :
    Real.sqrt t ^ r *
      ∫ x : EuclidD r, G (x, y) * χ₁ x * Real.exp (-(t * (qform (H y) x / 2 + R x y))) =
      innerScaledG H R χ₁ G t y := by
  set q : ℝ := (Real.sqrt t)⁻¹ with hq
  have hst : 0 < Real.sqrt t := Real.sqrt_pos.mpr ht
  have hqpos : 0 < q := inv_pos.mpr hst
  have hq2 : t * q ^ 2 = 1 := by
    rw [hq, sqrt_inv_sq ht, mul_inv_cancel₀ ht.ne']
  have hdil := integral_dilation (d := r)
    (fun x ↦ G (x, y) * χ₁ x * Real.exp (-(t * (qform (H y) x / 2 + R x y)))) hqpos
  rw [hdil]
  unfold innerScaledG
  rw [← hq]
  have hpt : ∀ u : EuclidD r,
      G (q • u, y) * χ₁ (q • u) * Real.exp (-(t * (qform (H y) (q • u) / 2 + R (q • u) y))) =
        G (q • u, y) * χ₁ (q • u) * Real.exp (-(qform (H y) u / 2 + t * R (q • u) y)) := by
    intro u
    rw [qform_smul]
    have : t * (q ^ 2 * qform (H y) u / 2 + R (q • u) y) =
        qform (H y) u / 2 + t * R (q • u) y := by
      have : t * q ^ 2 * qform (H y) u = qform (H y) u := by rw [hq2, one_mul]
      linear_combination (1 / 2 : ℝ) * this
    rw [this]
  simp only [hpt]
  have hone : Real.sqrt t ^ r * q ^ r = 1 := by
    rw [← mul_pow, hq, mul_inv_cancel₀ hst.ne', one_pow]
  rw [← mul_assoc, hone, one_mul]

/-- Fubini for a general test. -/
theorem integral_mul_mbgWeight_eq {H : EuclidD n → Matrix (Fin r) (Fin r) ℝ}
    {R : EuclidD r → EuclidD n → ℝ} {χ₁ : EuclidD r → ℝ} {χ₂ : EuclidD n → ℝ} {c C δ : ℝ}
    (h : MBGenData H R χ₁ χ₂ c C δ) {G : EuclidD r × EuclidD n → ℝ} (hG : Continuous G) (t : ℝ) :
    ∫ z : EuclidD r × EuclidD n, G z * mbgWeight H R χ₁ χ₂ t z =
      ∫ y, χ₂ y *
        ∫ x : EuclidD r, G (x, y) * χ₁ x * Real.exp (-(t * (qform (H y) x / 2 + R x y))) := by
  have hi : Integrable fun z : EuclidD r × EuclidD n ↦ G z * mbgWeight H R χ₁ χ₂ t z :=
    (continuous_mul_mbgWeight h hG t).integrable_of_hasCompactSupport
      (hasCompactSupport_mul_mbgWeight h G t)
  rw [Measure.volume_eq_prod] at hi ⊢
  rw [integral_prod_symm _ hi]
  refine integral_congr_ae (Filter.Eventually.of_forall fun y ↦ ?_)
  simp only [mbgWeight, mbgLoss]
  rw [← integral_const_mul]
  refine integral_congr_ae (Filter.Eventually.of_forall fun x ↦ ?_)
  simp only
  ring

/-- Uniform bound of the scaled integrand by `M e^{-c|u|²/4}` for `y` in the tangential support. -/
theorem abs_scaledG_integrand_le {H : EuclidD n → Matrix (Fin r) (Fin r) ℝ}
    {R : EuclidD r → EuclidD n → ℝ} {χ₁ : EuclidD r → ℝ} {χ₂ : EuclidD n → ℝ} {c C δ : ℝ}
    (h : MBGenData H R χ₁ χ₂ c C δ) {G : EuclidD r × EuclidD n → ℝ} {M : ℝ}
    (hM : ∀ p ∈ (Metric.closedBall (0 : EuclidD r) δ) ×ˢ tsupport χ₂, |G p| ≤ M) {t : ℝ}
    (ht : 0 < t) (u : EuclidD r) {y : EuclidD n} (hy : y ∈ tsupport χ₂) :
    |G ((Real.sqrt t)⁻¹ • u, y) * χ₁ ((Real.sqrt t)⁻¹ • u) *
      Real.exp (-(qform (H y) u / 2 + t * R ((Real.sqrt t)⁻¹ • u) y))| ≤
      M * Real.exp (-(c / 4) * ‖u‖ ^ 2) := by
  by_cases hwin : ‖(Real.sqrt t)⁻¹ • u‖ ≤ δ
  · have hmem : ((Real.sqrt t)⁻¹ • u, y) ∈ (Metric.closedBall (0 : EuclidD r) δ) ×ˢ tsupport χ₂ :=
      ⟨by rwa [Metric.mem_closedBall, dist_zero_right], hy⟩
    rw [mul_assoc, abs_mul]
    exact mul_le_mul (hM _ hmem) (abs_cutoff_mul_exp_le h ht u y) (abs_nonneg _)
      ((abs_nonneg _).trans (hM _ hmem))
  · push Not at hwin
    rw [h.χ₁_supp _ hwin, mul_zero, zero_mul, abs_zero]
    have hM0 : 0 ≤ M := (abs_nonneg _).trans (hM (0, y) ⟨by simp [h.δ_pos.le], hy⟩)
    positivity

theorem tendsto_scaledG_integrand {H : EuclidD n → Matrix (Fin r) (Fin r) ℝ}
    {R : EuclidD r → EuclidD n → ℝ} {χ₁ : EuclidD r → ℝ} {χ₂ : EuclidD n → ℝ} {c C δ : ℝ}
    (h : MBGenData H R χ₁ χ₂ c C δ) {G : EuclidD r × EuclidD n → ℝ} (hG : Continuous G)
    (u : EuclidD r) (y : EuclidD n) :
    Tendsto (fun t : ℝ ↦ G ((Real.sqrt t)⁻¹ • u, y) * χ₁ ((Real.sqrt t)⁻¹ • u) *
        Real.exp (-(qform (H y) u / 2 + t * R ((Real.sqrt t)⁻¹ • u) y))) atTop
      (𝓝 (G (0, y) * quadKernel (H y) u)) := by
  have hu : Tendsto (fun t : ℝ ↦ (Real.sqrt t)⁻¹ • u) atTop (𝓝 0) := by
    simpa using tendsto_sqrt_inv.smul_const u
  have h0 : Tendsto (fun t : ℝ ↦ G ((Real.sqrt t)⁻¹ • u, y)) atTop (𝓝 (G (0, y))) :=
    (hG.tendsto (0, y)).comp (hu.prodMk_nhds tendsto_const_nhds)
  have h1 := tendsto_cutoff_scaled h.χ₁_cont h.χ₁_zero u
  have h2 : Tendsto (fun t : ℝ ↦ Real.exp (-(qform (H y) u / 2 + t * R ((Real.sqrt t)⁻¹ • u) y)))
      atTop (𝓝 (Real.exp (-(qform (H y) u / 2 + 0)))) :=
    (Real.continuous_exp.tendsto _).comp
      ((tendsto_const_nhds.add (tendsto_mul_remainder_scaled h u y)).neg)
  have h3 := (h0.mul h1).mul h2
  rw [mul_one, add_zero] at h3
  unfold quadKernel
  rw [neg_div]
  exact h3

/-- Inner dominated convergence for `y` in the tangential support. -/
theorem tendsto_innerScaledG {H : EuclidD n → Matrix (Fin r) (Fin r) ℝ}
    {R : EuclidD r → EuclidD n → ℝ} {χ₁ : EuclidD r → ℝ} {χ₂ : EuclidD n → ℝ} {c C δ : ℝ}
    (h : MBGenData H R χ₁ χ₂ c C δ) {G : EuclidD r × EuclidD n → ℝ} (hG : Continuous G) {M : ℝ}
    (hM : ∀ p ∈ (Metric.closedBall (0 : EuclidD r) δ) ×ˢ tsupport χ₂, |G p| ≤ M) {y : EuclidD n}
    (hy : y ∈ tsupport χ₂) :
    Tendsto (fun t ↦ innerScaledG H R χ₁ G t y) atTop (𝓝 (G (0, y) * mbDensity H y)) := by
  unfold innerScaledG mbDensity
  rw [← integral_const_mul]
  refine tendsto_integral_filter_of_dominated_convergence
    (fun u ↦ M * Real.exp (-(c / 4) * ‖u‖ ^ 2))
    (Filter.Eventually.of_forall fun t ↦ ?_) ?_
    ((integrable_exp_neg_mul_sq_norm (by have := h.base.c_pos; positivity)).const_mul M)
    (Filter.Eventually.of_forall fun u ↦ tendsto_scaledG_integrand h hG u y)
  · exact ((continuous_scaledG_integrand h hG t).comp
      (continuous_const.prodMk continuous_id)).aestronglyMeasurable
  · filter_upwards [eventually_gt_atTop 0] with t ht
    exact Filter.Eventually.of_forall fun u ↦ by
      rw [Real.norm_eq_abs]
      exact abs_scaledG_integrand_le h hM ht u hy

theorem abs_innerScaledG_le {H : EuclidD n → Matrix (Fin r) (Fin r) ℝ}
    {R : EuclidD r → EuclidD n → ℝ} {χ₁ : EuclidD r → ℝ} {χ₂ : EuclidD n → ℝ} {c C δ : ℝ}
    (h : MBGenData H R χ₁ χ₂ c C δ) {G : EuclidD r × EuclidD n → ℝ} {M : ℝ}
    (hM : ∀ p ∈ (Metric.closedBall (0 : EuclidD r) δ) ×ˢ tsupport χ₂, |G p| ≤ M) {t : ℝ}
    (ht : 0 < t) {y : EuclidD n} (hy : y ∈ tsupport χ₂) :
    |innerScaledG H R χ₁ G t y| ≤ ∫ u : EuclidD r, M * Real.exp (-(c / 4) * ‖u‖ ^ 2) := by
  unfold innerScaledG
  rw [← Real.norm_eq_abs]
  exact norm_integral_le_of_norm_le
    ((integrable_exp_neg_mul_sq_norm (by have := h.base.c_pos; positivity)).const_mul M)
    (Filter.Eventually.of_forall fun u ↦ by
      rw [Real.norm_eq_abs]
      exact abs_scaledG_integrand_le h hM ht u hy)

theorem stronglyMeasurable_innerScaledG {H : EuclidD n → Matrix (Fin r) (Fin r) ℝ}
    {R : EuclidD r → EuclidD n → ℝ} {χ₁ : EuclidD r → ℝ} {χ₂ : EuclidD n → ℝ} {c C δ : ℝ}
    (h : MBGenData H R χ₁ χ₂ c C δ) {G : EuclidD r × EuclidD n → ℝ} (hG : Continuous G) (t : ℝ) :
    StronglyMeasurable (innerScaledG H R χ₁ G t) := by
  unfold innerScaledG
  exact (continuous_scaledG_integrand h hG t).stronglyMeasurable.integral_prod_right'

/-- **Leading order for a general continuous test** (adapted model):
`(√t)^r ∫ G w_t → ∫ G(0, y) χ₂ ρ_H`. -/
theorem tendsto_sqrt_pow_mul_integral_cont {H : EuclidD n → Matrix (Fin r) (Fin r) ℝ}
    {R : EuclidD r → EuclidD n → ℝ} {χ₁ : EuclidD r → ℝ} {χ₂ : EuclidD n → ℝ} {c C δ : ℝ}
    (h : MBGenData H R χ₁ χ₂ c C δ) {G : EuclidD r × EuclidD n → ℝ} (hG : Continuous G) :
    Tendsto (fun t ↦ Real.sqrt t ^ r *
        ∫ z : EuclidD r × EuclidD n, G z * mbgWeight H R χ₁ χ₂ t z) atTop
      (𝓝 (∫ y, G (0, y) * (χ₂ y * mbDensity H y))) := by
  -- the compact bound on `G`
  have hK : IsCompact ((Metric.closedBall (0 : EuclidD r) δ) ×ˢ tsupport χ₂) :=
    (isCompact_closedBall _ _).prod h.base.χ_supp
  obtain ⟨M, hM⟩ := hK.exists_bound_of_continuousOn hG.continuousOn
  have hM' : ∀ p ∈ (Metric.closedBall (0 : EuclidD r) δ) ×ˢ tsupport χ₂, |G p| ≤ M :=
    fun p hp ↦ by rw [← Real.norm_eq_abs]; exact hM p hp
  -- rewrite as the outer integral of the scaled inner integral
  have hrew : ∀ᶠ t : ℝ in atTop, Real.sqrt t ^ r *
      (∫ z : EuclidD r × EuclidD n, G z * mbgWeight H R χ₁ χ₂ t z) =
      ∫ y, χ₂ y * innerScaledG H R χ₁ G t y := by
    filter_upwards [eventually_gt_atTop 0] with t ht
    rw [integral_mul_mbgWeight_eq h hG t, ← integral_const_mul]
    refine integral_congr_ae (Filter.Eventually.of_forall fun y ↦ ?_)
    simp only
    rw [← sqrt_pow_mul_integral_eq_innerScaledG G ht y]
    ring
  refine Tendsto.congr' (hrew.mono fun t ht ↦ ht.symm) ?_
  set I : ℝ := ∫ u : EuclidD r, M * Real.exp (-(c / 4) * ‖u‖ ^ 2) with hI
  have hχ : Integrable fun y ↦ |χ₂ y| * I :=
    ((h.base.χ_cont.integrable_of_hasCompactSupport h.base.χ_supp).abs).mul_const I
  refine tendsto_integral_filter_of_dominated_convergence (fun y ↦ |χ₂ y| * I) ?_ ?_ hχ
    (Filter.Eventually.of_forall fun y ↦ ?_)
  · exact Filter.Eventually.of_forall fun t ↦
      (h.base.χ_cont.stronglyMeasurable.mul (stronglyMeasurable_innerScaledG h hG t))
        |>.aestronglyMeasurable
  · filter_upwards [eventually_gt_atTop 0] with t ht
    refine Filter.Eventually.of_forall fun y ↦ ?_
    rw [Real.norm_eq_abs, abs_mul]
    by_cases hy : y ∈ tsupport χ₂
    · exact mul_le_mul_of_nonneg_left (abs_innerScaledG_le h hM' ht hy) (abs_nonneg _)
    · rw [image_eq_zero_of_notMem_tsupport hy, abs_zero, zero_mul, zero_mul]
  · by_cases hy : y ∈ tsupport χ₂
    · have := (tendsto_innerScaledG h hG hM' hy).const_mul (χ₂ y)
      convert this using 1
      ring_nf
    · rw [image_eq_zero_of_notMem_tsupport hy]
      simp

/-! ### The curved model: leading order and identification -/

/-- **Ambient continuous tests see the Morse–Bott measure pushed forward to the graph**:
`E_t[F] → ∫ F(φ(y), y) χ₂ ρ_H / ∫ χ₂ ρ_H`. -/
theorem tendsto_mbcExp {H : EuclidD n → Matrix (Fin r) (Fin r) ℝ} {R : EuclidD r → EuclidD n → ℝ}
    {χ₁ : EuclidD r → ℝ} {χ₂ : EuclidD n → ℝ} {c C δ : ℝ} (h : MBGenData H R χ₁ χ₂ c C δ)
    {φ : EuclidD n → EuclidD r} (hφ : Continuous φ) {y₀ : EuclidD n} (hy₀ : χ₂ y₀ ≠ 0)
    {F : EuclidD r × EuclidD n → ℝ} (hF : Continuous F) :
    Tendsto (fun t ↦ mbcExp H R φ χ₁ χ₂ t F) atTop
      (𝓝 ((∫ y, F (φ y, y) * (χ₂ y * mbDensity H y)) / ∫ y, χ₂ y * mbDensity H y)) := by
  have hG : Continuous fun z ↦ F (graphUnshift φ z) := by
    unfold graphUnshift
    fun_prop
  have hnum := tendsto_sqrt_pow_mul_integral_cont h hG
  have hden := tendsto_sqrt_pow_mul_partition h
  have hA : (∫ y, χ₂ y * mbDensity H y) ≠ 0 :=
    (integral_cutoff_mul_mbDensity_pos h.base hy₀).ne'
  have hlim := hnum.div hden hA
  have heq : (fun y ↦ F (graphUnshift φ (0, y)) * (χ₂ y * mbDensity H y)) =
      fun y ↦ F (φ y, y) * (χ₂ y * mbDensity H y) := by
    funext y
    simp [graphUnshift]
  rw [heq] at hlim
  refine hlim.congr' ?_
  filter_upwards [eventually_gt_atTop 0] with t ht
  have hne : Real.sqrt t ^ r ≠ 0 := pow_ne_zero _ (Real.sqrt_pos.mpr ht).ne'
  rw [mbcExp_eq hφ]
  simp only [mbgExp, Pi.div_apply]
  rw [mul_div_mul_left _ _ hne]

/-- The partition function of the curved model is that of the adapted one. -/
theorem integral_mbcWeight {H : EuclidD n → Matrix (Fin r) (Fin r) ℝ}
    {R : EuclidD r → EuclidD n → ℝ} {φ : EuclidD n → EuclidD r} (hφ : Continuous φ)
    (χ₁ : EuclidD r → ℝ) (χ₂ : EuclidD n → ℝ) (t : ℝ) :
    ∫ z, mbcWeight H R φ χ₁ χ₂ t z = ∫ z, mbgWeight H R χ₁ χ₂ t z :=
  integral_comp_graphShift hφ _

/-- **Centred rescaled second moments see the transverse covariance in graph coordinates**:
`t E_t[(x - φ(y))ᵢ (x - φ(y))ₖ g(y)] → ∫ g χ₂ σ_H^{ik} / ∫ χ₂ ρ_H`. -/
theorem tendsto_mul_mbcExp_centred_second {H : EuclidD n → Matrix (Fin r) (Fin r) ℝ}
    {R : EuclidD r → EuclidD n → ℝ} {χ₁ : EuclidD r → ℝ} {χ₂ : EuclidD n → ℝ} {c C δ : ℝ}
    (h : MBGenData H R χ₁ χ₂ c C δ) {φ : EuclidD n → EuclidD r} (hφ : Continuous φ)
    {y₀ : EuclidD n} (hy₀ : χ₂ y₀ ≠ 0) (i k : Fin r) {g : EuclidD n → ℝ} (hg : Continuous g) :
    Tendsto (fun t ↦ t * mbcExp H R φ χ₁ χ₂ t
        (fun z ↦ (z.1 - φ z.2) i * (z.1 - φ z.2) k * g z.2)) atTop
      (𝓝 ((∫ y, g y * (χ₂ y * mbSecond H i k y)) / ∫ y, χ₂ y * mbDensity H y)) := by
  have hnum := tendsto_sqrt_pow_mul_integral h (g := fun x : EuclidD r ↦ x i * x k)
    (((continuous_apply i).comp (PiLp.continuous_ofLp 2 (fun _ : Fin r ↦ ℝ))).mul
      ((continuous_apply k).comp (PiLp.continuous_ofLp 2 (fun _ : Fin r ↦ ℝ)))) (Cg := 1)
    (k := 2) (abs_coord_mul_coord_le i k) (coord_mul_coord_hom i k) hg
  have hden := tendsto_sqrt_pow_mul_partition h
  have hA : (∫ y, χ₂ y * mbDensity H y) ≠ 0 :=
    (integral_cutoff_mul_mbDensity_pos h.base hy₀).ne'
  have hlim := hnum.div hden hA
  have heq : (∫ y, g y * χ₂ y * ∫ u : EuclidD r, u i * u k * quadKernel (H y) u) =
      ∫ y, g y * (χ₂ y * mbSecond H i k y) := by
    refine integral_congr_ae (Filter.Eventually.of_forall fun y ↦ ?_)
    simp only [mbSecond]
    ring
  rw [heq] at hlim
  refine hlim.congr' ?_
  filter_upwards [eventually_gt_atTop 0] with t ht
  have hne : Real.sqrt t ^ r ≠ 0 := pow_ne_zero _ (Real.sqrt_pos.mpr ht).ne'
  rw [mbcExp_eq hφ]
  simp only [mbgExp, Pi.div_apply]
  simp only [graphUnshift, add_sub_cancel_right]
  rw [pow_add, Real.sq_sqrt ht.le, mul_assoc, mul_div_mul_left _ _ hne, mul_div_assoc]

/-- **Free energy of the curved model**: `-log Z_t - (r/2) log t → -log ∫ χ₂ ρ_H`. -/
theorem tendsto_neg_log_curved_partition_sub {H : EuclidD n → Matrix (Fin r) (Fin r) ℝ}
    {R : EuclidD r → EuclidD n → ℝ} {χ₁ : EuclidD r → ℝ} {χ₂ : EuclidD n → ℝ} {c C δ : ℝ}
    (h : MBGenData H R χ₁ χ₂ c C δ) {φ : EuclidD n → EuclidD r} (hφ : Continuous φ)
    {y₀ : EuclidD n} (hy₀ : χ₂ y₀ ≠ 0) :
    Tendsto (fun t ↦ -Real.log (∫ z, mbcWeight H R φ χ₁ χ₂ t z) - (r / 2 : ℝ) * Real.log t)
      atTop (𝓝 (-Real.log (∫ y, χ₂ y * mbDensity H y))) := by
  simp only [integral_mbcWeight hφ]
  exact tendsto_neg_log_partition_sub h hy₀

/-- **Identification given the graph**: two curved models over the same graph `φ` with the same
cutoffs whose tangential monomial expectations and centred second-moment expectations are
eventually equal have equal Hessian fields on `{χ₂ ≠ 0}`. -/
theorem mbc_identification_of_graph {H₁ H₂ : EuclidD n → Matrix (Fin r) (Fin r) ℝ}
    {R₁ R₂ : EuclidD r → EuclidD n → ℝ} {χ₁ : EuclidD r → ℝ} {χ₂ : EuclidD n → ℝ}
    {c₁ C₁ δ₁ c₂ C₂ δ₂ : ℝ} (h₁ : MBGenData H₁ R₁ χ₁ χ₂ c₁ C₁ δ₁)
    (h₂ : MBGenData H₂ R₂ χ₁ χ₂ c₂ C₂ δ₂) {φ : EuclidD n → EuclidD r} (hφ : Continuous φ)
    {y₀ : EuclidD n} (hy₀ : χ₂ y₀ ≠ 0)
    (hT : ∀ (q : ℕ) (w : Fin q → Fin n), ∀ᶠ t in atTop,
      mbcExp H₁ R₁ φ χ₁ χ₂ t (fun z ↦ monomialTest w z.2) =
        mbcExp H₂ R₂ φ χ₁ χ₂ t (fun z ↦ monomialTest w z.2))
    (hN : ∀ (i k : Fin r) (q : ℕ) (w : Fin q → Fin n), ∀ᶠ t in atTop,
      mbcExp H₁ R₁ φ χ₁ χ₂ t (fun z ↦ (z.1 - φ z.2) i * (z.1 - φ z.2) k * monomialTest w z.2) =
        mbcExp H₂ R₂ φ χ₁ χ₂ t
          (fun z ↦ (z.1 - φ z.2) i * (z.1 - φ z.2) k * monomialTest w z.2)) :
    ∀ y, χ₂ y ≠ 0 → H₁ y = H₂ y := by
  refine mbg_identification h₁ h₂ hy₀ (fun q w ↦ ?_) (fun i k q w ↦ ?_)
  · filter_upwards [hT q w] with t ht
    rw [mbcExp_eq hφ, mbcExp_eq hφ] at ht
    simpa [graphUnshift] using ht
  · filter_upwards [hN i k q w] with t ht
    rw [mbcExp_eq hφ, mbcExp_eq hφ] at ht
    simpa [graphUnshift] using ht

end Laplace.Multi
