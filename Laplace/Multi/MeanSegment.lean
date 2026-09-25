/-
Copyright (c) 2026 Timaeus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Timaeus
-/
import Mathlib
import Laplace.Multi.SliceVariational
import Laplace.Multi.ObservableRegression
import Laplace.Multi.SegmentDivergence

/-!
# The mean segment: continuity of the inverse Jacobian and transport in mean coordinates

The inverse Jacobian `a ↦ (Dm(a))⁻¹` of the mean map is continuous (`continuous_invJac`; the
Jacobian is continuous and inversion is continuous on units of the Banach algebra of
endomorphisms). Along the **mean segment** `y_s = m(a₀) + s (m(a₁) − m(a₀))` — the `m`-geodesic of
the dual affine structure — with data path `γ_s = m⁻¹(y_s)` and the dual quadratic form
`Q(s) = ⟨d, D²I(y_s) d⟩`:

* **transport of an observable** `⟨φ⟩_{a₁} − ⟨φ⟩_{a₀} = ∫₀¹ DΦ(y_s) d ds` (`obsMean_segment_eq`);
* **the dual segment identities** `KL(P_{a₁} ‖ P_{a₀}) = ∫₀¹ (1 − s) Q(s) ds` and
  `KL(P_{a₀} ‖ P_{a₁}) = ∫₀¹ s Q(s) ds` (`mixKL_eq_integral_dual_one_sub`,
  `mixKL_eq_integral_dual_mul`), the mean-coordinate mirror of `SegmentDivergence`.
-/

open MeasureTheory Filter Topology Set

namespace Laplace.Multi

variable {X : Type*} [MeasurableSpace X] {μ : Measure X} {ι : Type*} [Fintype ι]

section Continuity

variable [Nonempty X] {π L₀ : X → ℝ} (hπm : Measurable π) (hπi : Integrable π μ) (hπ : ∀ x, 0 ≤ π x)
  (hπpos : 0 < ∫ x, π x ∂μ) (hL₀m : Measurable L₀) {M₀ : ℝ} (hL₀ : ∀ x, |L₀ x| ≤ M₀)
  {R : ι → X → ℝ} (hR : ∀ i, Bdd (R i)) {t : ℝ} (ht : 0 < t)
include hπm hπi hπ hπpos hL₀m hL₀ hR ht

/-- **The Jacobian of the mean map is continuous** (as a map into the endomorphisms). -/
theorem continuous_meanMapDeriv : Continuous (meanMapDeriv μ π L₀ R t) := by
  have hZ : ∀ a, priorZ μ π (affLoss L₀ R a) t ≠ 0 := fun a ↦
    (tiltData_aff hπm hπi hπ hπpos hL₀m hL₀ hR a 0 t).choose_spec.ν_pos.ne'
  -- the entries
  have hent : ∀ i, Continuous (fun a ↦
      (priorZ μ π (affLoss L₀ R a) t)⁻¹ • affNumDeriv μ π L₀ (R i) R t a -
        ((∫ x, R i x * Real.exp (-(t * affLoss L₀ R a x)) * π x ∂μ) *
          (priorZ μ π (affLoss L₀ R a) t ^ 2)⁻¹) • affNumDeriv μ π L₀ (fun _ ↦ 1) R t a) := by
    intro i
    refine continuous_iff_continuousAt.2 fun a₀ ↦ ?_
    obtain ⟨_, hZ'⟩ := hasFDerivAt_affNum hπm hπi hπ hL₀m hL₀ hR (φ := fun _ ↦ (1 : ℝ))
      measurable_const (Mφ := 1) (fun _ ↦ by simp) ht a₀
    obtain ⟨Mi, hMi⟩ := (hR i).2
    obtain ⟨_, hN'⟩ := hasFDerivAt_affNum hπm hπi hπ hL₀m hL₀ hR (φ := R i) (hR i).1 hMi ht a₀
    have hZc : ContinuousAt (fun a ↦ priorZ μ π (affLoss L₀ R a) t) a₀ := by
      have := hZ'.continuousAt
      simp only [one_mul] at this
      exact this
    have hNc : ContinuousAt
        (fun a ↦ ∫ x, R i x * Real.exp (-(t * affLoss L₀ R a x)) * π x ∂μ) a₀ := hN'.continuousAt
    have hDi : ContinuousAt (fun a ↦ affNumDeriv μ π L₀ (R i) R t a) a₀ :=
      continuousAt_affNumDeriv hπm hπi hπ hL₀m hL₀ hR (hR i).1 hMi ht a₀
    have hD1 : ContinuousAt (fun a ↦ affNumDeriv μ π L₀ (fun _ ↦ (1 : ℝ)) R t a) a₀ :=
      continuousAt_affNumDeriv hπm hπi hπ hL₀m hL₀ hR measurable_const (Mφ := 1)
        (fun _ ↦ by simp) ht a₀
    exact ((hZc.inv₀ (hZ a₀)).smul hDi).sub
      ((hNc.mul ((hZc.pow 2).inv₀ (pow_ne_zero 2 (hZ a₀)))).smul hD1)
  -- assembling the entries is a linear map between finite-dimensional spaces
  let Φ : (ι → (ι → ℝ) →L[ℝ] ℝ) →ₗ[ℝ] ((ι → ℝ) →L[ℝ] (ι → ℝ)) :=
    { toFun := ContinuousLinearMap.pi
      map_add' := fun f g ↦ by
        ext v i
        simp [ContinuousLinearMap.pi_apply]
      map_smul' := fun c f ↦ by
        ext v i
        simp [ContinuousLinearMap.pi_apply] }
  have hΦ : Continuous Φ := Φ.continuous_of_finiteDimensional
  have e : meanMapDeriv μ π L₀ R t = fun a ↦ Φ (fun i ↦
      (priorZ μ π (affLoss L₀ R a) t)⁻¹ • affNumDeriv μ π L₀ (R i) R t a -
        ((∫ x, R i x * Real.exp (-(t * affLoss L₀ R a x)) * π x ∂μ) *
          (priorZ μ π (affLoss L₀ R a) t ^ 2)⁻¹) • affNumDeriv μ π L₀ (fun _ ↦ 1) R t a) := by
    funext a; rfl
  rw [e]
  exact hΦ.comp (continuous_pi hent)

variable (hnd : ∀ v : ι → ℝ, v ≠ 0 → ¬ ∃ c : ℝ, ∀ᵐ x ∂μ, π x ≠ 0 → dirLoss R v x = c)
include hnd

/-- The Jacobian composed with the inverse Jacobian is the identity. -/
theorem meanMapDeriv_comp_invJac (a : ι → ℝ) :
    (meanMapDeriv μ π L₀ R t a).comp (invJac hπm hπi hπ hπpos hL₀m hL₀ hR ht hnd a) =
      ContinuousLinearMap.id ℝ (ι → ℝ) := by
  have h := coe_meanMapDerivEquiv (μ := μ)
    (meanMapDeriv_injective hπm hπi hπ hπpos hL₀m hL₀ hR ht hnd a)
  unfold invJac
  rw [← h]
  exact ContinuousLinearEquiv.coe_comp_coe_symm _

/-- The Jacobian at `a` as a unit of the algebra of endomorphisms. -/
noncomputable def meanMapDerivUnit (a : ι → ℝ) : ((ι → ℝ) →L[ℝ] (ι → ℝ))ˣ where
  val := meanMapDeriv μ π L₀ R t a
  inv := invJac hπm hπi hπ hπpos hL₀m hL₀ hR ht hnd a
  val_inv := by
    rw [ContinuousLinearMap.mul_def, meanMapDeriv_comp_invJac hπm hπi hπ hπpos hL₀m hL₀ hR ht hnd a]
    rfl
  inv_val := by
    rw [ContinuousLinearMap.mul_def, ContinuousLinearMap.one_def]
    exact meanMapInverse_deriv_comp hπm hπi hπ hπpos hL₀m hL₀ hR ht hnd a

theorem invJac_eq_inverse (a : ι → ℝ) :
    invJac hπm hπi hπ hπpos hL₀m hL₀ hR ht hnd a = Ring.inverse (meanMapDeriv μ π L₀ R t a) := by
  rw [show meanMapDeriv μ π L₀ R t a =
      (meanMapDerivUnit hπm hπi hπ hπpos hL₀m hL₀ hR ht hnd a : (ι → ℝ) →L[ℝ] (ι → ℝ)) from rfl,
    Ring.inverse_unit]
  rfl

/-- **The inverse Jacobian is continuous.** -/
theorem continuous_invJac : Continuous (fun a ↦ invJac hπm hπi hπ hπpos hL₀m hL₀ hR ht hnd a) := by
  have e : (fun a ↦ invJac hπm hπi hπ hπpos hL₀m hL₀ hR ht hnd a) =
      fun a ↦ Ring.inverse (meanMapDeriv μ π L₀ R t a) :=
    funext fun a ↦ invJac_eq_inverse hπm hπi hπ hπpos hL₀m hL₀ hR ht hnd a
  rw [e]
  refine continuous_iff_continuousAt.2 fun a ↦ ?_
  have h1 : ContinuousAt Ring.inverse (meanMapDeriv μ π L₀ R t a) :=
    NormedRing.inverse_continuousAt (meanMapDerivUnit hπm hπi hπ hπpos hL₀m hL₀ hR ht hnd a)
  exact h1.comp (continuous_meanMapDeriv hπm hπi hπ hπpos hL₀m hL₀ hR ht).continuousAt

end Continuity

/-! ### Cauchy–Schwarz for `√(fg)` on `[0,1]` -/

omit [MeasurableSpace X] in
/-- `(∫₀¹ √(f g))² ≤ (∫₀¹ f)(∫₀¹ g)` for nonnegative `f, g` continuous on `[0,1]`. -/
theorem sq_integral_sqrt_mul_le {f g : ℝ → ℝ} (hf : ContinuousOn f (Icc 0 1))
    (hg : ContinuousOn g (Icc 0 1)) (hf0 : ∀ s ∈ Icc (0 : ℝ) 1, 0 ≤ f s)
    (hg0 : ∀ s ∈ Icc (0 : ℝ) 1, 0 ≤ g s) :
    (∫ s in (0 : ℝ)..1, Real.sqrt (f s * g s)) ^ 2 ≤
      (∫ s in (0 : ℝ)..1, f s) * ∫ s in (0 : ℝ)..1, g s := by
  set A := ∫ s in (0 : ℝ)..1, f s with hA
  set B := ∫ s in (0 : ℝ)..1, g s with hB
  have hA0 : 0 ≤ A := intervalIntegral.integral_nonneg zero_le_one fun s hs ↦ hf0 s hs
  have hB0 : 0 ≤ B := intervalIntegral.integral_nonneg zero_le_one fun s hs ↦ hg0 s hs
  have hIf : IntervalIntegrable f volume 0 1 := by
    refine ContinuousOn.intervalIntegrable ?_; rwa [uIcc_of_le zero_le_one]
  have hIg : IntervalIntegrable g volume 0 1 := by
    refine ContinuousOn.intervalIntegrable ?_; rwa [uIcc_of_le zero_le_one]
  have hIs : IntervalIntegrable (fun s ↦ Real.sqrt (f s * g s)) volume 0 1 := by
    refine ContinuousOn.intervalIntegrable ?_
    rw [uIcc_of_le zero_le_one]
    exact Real.continuous_sqrt.comp_continuousOn (hf.mul hg)
  have hS0 : 0 ≤ ∫ s in (0 : ℝ)..1, Real.sqrt (f s * g s) :=
    intervalIntegral.integral_nonneg zero_le_one fun s _ ↦ Real.sqrt_nonneg _
  -- AM–GM with a free weight
  have key : ∀ lam : ℝ, 0 < lam →
      ∫ s in (0 : ℝ)..1, Real.sqrt (f s * g s) ≤ (lam * A + B / lam) / 2 := by
    intro lam hlam
    have hpt : ∀ s ∈ Icc (0 : ℝ) 1, Real.sqrt (f s * g s) ≤ (lam * f s + g s / lam) / 2 := by
      intro s hs
      have hfs := hf0 s hs
      have hgs := hg0 s hs
      have e : (lam * f s + g s / lam) / 2 - Real.sqrt (f s * g s) =
          (lam ^ 2 * f s + g s - 2 * lam * Real.sqrt (f s * g s)) / (2 * lam) := by
        field_simp
      have h2 : 2 * lam * Real.sqrt (f s * g s) ≤ lam ^ 2 * f s + g s := by
        rw [Real.sqrt_mul hfs]
        nlinarith [sq_nonneg (lam * Real.sqrt (f s) - Real.sqrt (g s)), Real.sq_sqrt hfs,
          Real.sq_sqrt hgs, Real.sqrt_nonneg (f s), Real.sqrt_nonneg (g s)]
      have : 0 ≤ (lam * f s + g s / lam) / 2 - Real.sqrt (f s * g s) := by
        rw [e]; exact div_nonneg (by linarith) (by positivity)
      linarith
    calc ∫ s in (0 : ℝ)..1, Real.sqrt (f s * g s)
        ≤ ∫ s in (0 : ℝ)..1, (lam * f s + g s / lam) / 2 :=
          intervalIntegral.integral_mono_on zero_le_one hIs
            (((hIf.const_mul lam).add (hIg.div_const lam)).div_const 2) hpt
      _ = (lam * A + B / lam) / 2 := by
          rw [intervalIntegral.integral_div, intervalIntegral.integral_add (hIf.const_mul lam)
            (hIg.div_const lam), intervalIntegral.integral_const_mul, intervalIntegral.integral_div]
  -- `λ = √((B + ε)/(A + ε))` and `ε → 0`
  have hlim : Tendsto (fun ε : ℝ ↦ (A + ε) * (B + ε)) (𝓝[>] 0) (𝓝 (A * B)) := by
    have : Tendsto (fun ε : ℝ ↦ (A + ε) * (B + ε)) (𝓝 0) (𝓝 ((A + 0) * (B + 0))) :=
      ((continuous_const.add continuous_id).mul (continuous_const.add continuous_id)).tendsto 0
    simpa using this.mono_left nhdsWithin_le_nhds
  by_contra hcon
  push Not at hcon
  obtain ⟨ε, hlt, hε⟩ := ((hlim.eventually (gt_mem_nhds hcon)).and self_mem_nhdsWithin).exists
  have hε' : (0 : ℝ) < ε := hε
  have hAε : 0 < A + ε := by linarith
  have hBε : 0 < B + ε := by linarith
  set lam := Real.sqrt ((B + ε) / (A + ε)) with hlam
  have hlam0 : 0 < lam := Real.sqrt_pos.2 (div_pos hBε hAε)
  have hlamsq : lam ^ 2 = (B + ε) / (A + ε) := Real.sq_sqrt (div_pos hBε hAε).le
  have h := key lam hlam0
  -- `(B + ε)/λ = λ (A + ε)`, so the bound is `λ (A + ε)`, whose square is `(A+ε)(B+ε)`
  have e1 : (B + ε) / lam = lam * (A + ε) := by
    rw [div_eq_iff hlam0.ne']
    have : lam * (A + ε) * lam = lam ^ 2 * (A + ε) := by ring
    rw [this, hlamsq]
    field_simp
  have hbound : (lam * A + B / lam) / 2 ≤ lam * (A + ε) := by
    have h1 : lam * A ≤ lam * (A + ε) := by nlinarith
    have h2 : B / lam ≤ (B + ε) / lam := div_le_div_of_nonneg_right (by linarith) hlam0.le
    linarith
  have hsq : (lam * (A + ε)) ^ 2 = (A + ε) * (B + ε) := by
    rw [mul_pow, hlamsq]
    field_simp
  have hfin : (∫ s in (0 : ℝ)..1, Real.sqrt (f s * g s)) ^ 2 ≤ (A + ε) * (B + ε) := by
    rw [← hsq]
    exact pow_le_pow_left₀ hS0 (h.trans hbound) 2
  linarith

omit [MeasurableSpace X] in
theorem dotJ_comm (a b : ι → ℝ) : dotJ a b = dotJ b a := by
  simp [dotJ, mul_comm]

/-! ### The mean segment -/

section Segment

variable [Nonempty ι] [Nonempty X] {π L₀ : X → ℝ} (hπm : Measurable π) (hπi : Integrable π μ)
  (hπ : ∀ x, 0 < π x) (hπpos : 0 < ∫ x, π x ∂μ) (hL₀m : Measurable L₀) {M₀ : ℝ}
  (hL₀ : ∀ x, |L₀ x| ≤ M₀) {R : ι → X → ℝ} (hR : ∀ i, Bdd (R i)) {t : ℝ} (ht : 0 < t)
  (hnd : ∀ v : ι → ℝ, v ≠ 0 → ¬ ∃ c : ℝ, ∀ᵐ x ∂μ, π x ≠ 0 → dirLoss R v x = c) (a₀ a₁ : ι → ℝ)
include hπm hπi hπ hπpos hL₀m hL₀ hR ht hnd

/-- The mean segment `y_s = m(a₀) + s (m(a₁) − m(a₀))`. -/
noncomputable def meanSeg (μ : Measure X) (π L₀ : X → ℝ) (R : ι → X → ℝ) (t : ℝ) (a₀ a₁ : ι → ℝ)
    (s : ℝ) : ι → ℝ :=
  meanMap μ π L₀ R t a₀ + s • (meanMap μ π L₀ R t a₁ - meanMap μ π L₀ R t a₀)

/-- The data path `γ_s = m⁻¹(y_s)` over the mean segment. -/
noncomputable def dataPath (μ : Measure X) (π L₀ : X → ℝ) (R : ι → X → ℝ) (t : ℝ) (a₀ a₁ : ι → ℝ)
    (s : ℝ) : ι → ℝ :=
  Function.invFun (meanMap μ π L₀ R t) (meanSeg μ π L₀ R t a₀ a₁ s)

omit [Nonempty ι] [Nonempty X] hπm hπi hπ hπpos hL₀m hL₀ hR ht hnd in
theorem meanSeg_eq_comb (s : ℝ) :
    meanSeg μ π L₀ R t a₀ a₁ s = (1 - s) • meanMap μ π L₀ R t a₀ + s • meanMap μ π L₀ R t a₁ := by
  unfold meanSeg; module

theorem meanSeg_mem_range {s : ℝ} (hs : s ∈ Icc (0 : ℝ) 1) :
    meanSeg μ π L₀ R t a₀ a₁ s ∈ Set.range (meanMap μ π L₀ R t) := by
  have hconv : Convex ℝ (Set.range (meanMap μ π L₀ R t)) := by
    rw [range_meanMap_slice hπm hπi hπ hπpos hL₀m hL₀ hR ht hnd]
    exact (convex_momentBody R).interior
  rw [meanSeg_eq_comb]
  exact hconv ⟨a₀, rfl⟩ ⟨a₁, rfl⟩ (by linarith [hs.2]) hs.1 (by ring)

theorem meanMap_dataPath {s : ℝ} (hs : s ∈ Icc (0 : ℝ) 1) :
    meanMap μ π L₀ R t (dataPath μ π L₀ R t a₀ a₁ s) = meanSeg μ π L₀ R t a₀ a₁ s :=
  meanMap_invFun (meanSeg_mem_range hπm hπi hπ hπpos hL₀m hL₀ hR ht hnd a₀ a₁ hs)

omit [Nonempty ι] in
theorem dataPath_zero : dataPath μ π L₀ R t a₀ a₁ 0 = a₀ := by
  unfold dataPath meanSeg
  rw [zero_smul, add_zero, invFun_meanMap hπm hπi (fun x ↦ (hπ x).le) hπpos hL₀m hL₀ hR ht hnd]

omit [Nonempty ι] in
theorem dataPath_one : dataPath μ π L₀ R t a₀ a₁ 1 = a₁ := by
  unfold dataPath meanSeg
  rw [one_smul, add_sub_cancel, invFun_meanMap hπm hπi (fun x ↦ (hπ x).le) hπpos hL₀m hL₀ hR ht hnd]

set_option linter.unusedFintypeInType false in
/-- The data path is differentiable on the segment, with velocity `(Dm)⁻¹ d`. -/
theorem hasDerivAt_dataPath {s : ℝ} (hs : s ∈ Icc (0 : ℝ) 1) :
    HasDerivAt (dataPath μ π L₀ R t a₀ a₁)
      (invJac hπm hπi (fun x ↦ (hπ x).le) hπpos hL₀m hL₀ hR ht hnd (dataPath μ π L₀ R t a₀ a₁ s)
        (meanMap μ π L₀ R t a₁ - meanMap μ π L₀ R t a₀)) s := by
  have hθ := (hasStrictFDerivAt_invFun_meanMap hπm hπi (fun x ↦ (hπ x).le) hπpos hL₀m hL₀ hR ht hnd
    (dataPath μ π L₀ R t a₀ a₁ s)).hasFDerivAt
  rw [meanMap_dataPath hπm hπi hπ hπpos hL₀m hL₀ hR ht hnd a₀ a₁ hs] at hθ
  have hline := hasDerivAt_affineLine (meanMap μ π L₀ R t a₀)
    (meanMap μ π L₀ R t a₁ - meanMap μ π L₀ R t a₀) s
  exact hθ.comp_hasDerivAt s hline

theorem continuousOn_dataPath : ContinuousOn (dataPath μ π L₀ R t a₀ a₁) (Icc 0 1) := by
  have hseg : Continuous (meanSeg μ π L₀ R t a₀ a₁) := by
    unfold meanSeg
    exact continuous_const.add ((continuous_id : Continuous fun s : ℝ ↦ s).smul continuous_const)
  exact (continuousOn_invFun_meanMap hπm hπi (fun x ↦ (hπ x).le) hπpos hL₀m hL₀ hR ht hnd).comp
    hseg.continuousOn fun s hs ↦ meanSeg_mem_range hπm hπi hπ hπpos hL₀m hL₀ hR ht hnd a₀ a₁ hs

/-- The velocity `s ↦ (Dm(γ_s))⁻¹ d` is continuous on the segment. -/
theorem continuousOn_dataPath_velocity :
    ContinuousOn (fun s ↦ invJac hπm hπi (fun x ↦ (hπ x).le) hπpos hL₀m hL₀ hR ht hnd
      (dataPath μ π L₀ R t a₀ a₁ s) (meanMap μ π L₀ R t a₁ - meanMap μ π L₀ R t a₀)) (Icc 0 1) :=
  ((continuous_invJac hπm hπi (fun x ↦ (hπ x).le) hπpos hL₀m hL₀ hR ht hnd).clm_apply
    continuous_const).comp_continuousOn (continuousOn_dataPath hπm hπi hπ hπpos hL₀m hL₀ hR ht hnd
    a₀ a₁)

/-- **Transport of an observable along the mean segment**:
`⟨φ⟩_{a₁} − ⟨φ⟩_{a₀} = ∫₀¹ D⟨φ⟩(γ_s)[(Dm(γ_s))⁻¹ d] ds`. -/
theorem obsMean_segment_eq {φ : X → ℝ} (hφm : Measurable φ) {Mφ : ℝ} (hφ : ∀ x, |φ x| ≤ Mφ) :
    priorExp μ π (affLoss L₀ R a₁) φ t - priorExp μ π (affLoss L₀ R a₀) φ t =
      ∫ s in (0 : ℝ)..1, obsMapDeriv μ π L₀ φ R t (dataPath μ π L₀ R t a₀ a₁ s)
        (invJac hπm hπi (fun x ↦ (hπ x).le) hπpos hL₀m hL₀ hR ht hnd (dataPath μ π L₀ R t a₀ a₁ s)
          (meanMap μ π L₀ R t a₁ - meanMap μ π L₀ R t a₀)) := by
  have hderiv : ∀ s ∈ uIcc (0 : ℝ) 1,
      HasDerivAt (fun s ↦ priorExp μ π (affLoss L₀ R (dataPath μ π L₀ R t a₀ a₁ s)) φ t)
        (obsMapDeriv μ π L₀ φ R t (dataPath μ π L₀ R t a₀ a₁ s)
          (invJac hπm hπi (fun x ↦ (hπ x).le) hπpos hL₀m hL₀ hR ht hnd (dataPath μ π L₀ R t a₀ a₁ s)
            (meanMap μ π L₀ R t a₁ - meanMap μ π L₀ R t a₀))) s := by
    intro s hs
    rw [uIcc_of_le zero_le_one] at hs
    exact (hasFDerivAt_obsMap hπm hπi hπ hπpos hL₀m hL₀ hR hφm hφ ht _).comp_hasDerivAt s
      (hasDerivAt_dataPath hπm hπi hπ hπpos hL₀m hL₀ hR ht hnd a₀ a₁ hs)
  have hint : IntervalIntegrable (fun s ↦ obsMapDeriv μ π L₀ φ R t (dataPath μ π L₀ R t a₀ a₁ s)
      (invJac hπm hπi (fun x ↦ (hπ x).le) hπpos hL₀m hL₀ hR ht hnd (dataPath μ π L₀ R t a₀ a₁ s)
        (meanMap μ π L₀ R t a₁ - meanMap μ π L₀ R t a₀))) volume 0 1 := by
    refine ContinuousOn.intervalIntegrable ?_
    rw [uIcc_of_le zero_le_one]
    exact ((continuous_obsMapDeriv hπm hπi hπ hπpos hL₀m hL₀ hR hφm hφ ht).comp_continuousOn
      (continuousOn_dataPath hπm hπi hπ hπpos hL₀m hL₀ hR ht hnd a₀ a₁)).clm_apply
      (continuousOn_dataPath_velocity hπm hπi hπ hπpos hL₀m hL₀ hR ht hnd a₀ a₁)
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv hint,
    dataPath_one hπm hπi hπ hπpos hL₀m hL₀ hR ht hnd,
    dataPath_zero hπm hπi hπ hπpos hL₀m hL₀ hR ht hnd]

/-- The dual quadratic form along the mean segment, `Q(s) = ⟨d, D²I(y_s) d⟩`. -/
noncomputable def dualQuad (s : ℝ) : ℝ :=
  dotJ (meanMap μ π L₀ R t a₁ - meanMap μ π L₀ R t a₀)
    (dualHessian hπm hπi (fun x ↦ (hπ x).le) hπpos hL₀m hL₀ hR ht hnd (dataPath μ π L₀ R t a₀ a₁ s)
      (meanMap μ π L₀ R t a₁ - meanMap μ π L₀ R t a₀))

omit [Nonempty ι] in
theorem dualQuad_eq (s : ℝ) :
    dualQuad hπm hπi hπ hπpos hL₀m hL₀ hR ht hnd a₀ a₁ s =
      -t * dotJ (meanMap μ π L₀ R t a₁ - meanMap μ π L₀ R t a₀)
        (invJac hπm hπi (fun x ↦ (hπ x).le) hπpos hL₀m hL₀ hR ht hnd (dataPath μ π L₀ R t a₀ a₁ s)
          (meanMap μ π L₀ R t a₁ - meanMap μ π L₀ R t a₀)) := by
  unfold dualQuad dualHessian
  rw [_root_.smul_apply, (isLinearMap_dotJ _).map_smul, smul_eq_mul]

theorem continuousOn_dualQuad :
    ContinuousOn (dualQuad hπm hπi hπ hπpos hL₀m hL₀ hR ht hnd a₀ a₁) (Icc 0 1) := by
  have e : dualQuad hπm hπi hπ hπpos hL₀m hL₀ hR ht hnd a₀ a₁ = fun s ↦
      -t * dotJ (meanMap μ π L₀ R t a₁ - meanMap μ π L₀ R t a₀)
        (invJac hπm hπi (fun x ↦ (hπ x).le) hπpos hL₀m hL₀ hR ht hnd (dataPath μ π L₀ R t a₀ a₁ s)
          (meanMap μ π L₀ R t a₁ - meanMap μ π L₀ R t a₀)) :=
    funext fun s ↦ dualQuad_eq hπm hπi hπ hπpos hL₀m hL₀ hR ht hnd a₀ a₁ s
  rw [e]
  exact ((continuous_dotJ_right _).comp_continuousOn
    (continuousOn_dataPath_velocity hπm hπi hπ hπpos hL₀m hL₀ hR ht hnd a₀ a₁)).const_smul (-t)
    |>.congr fun s _ ↦ rfl

set_option linter.unusedFintypeInType false in
/-- The dual potential along the mean segment has derivative `−t ⟨d, γ_s⟩`. -/
theorem hasDerivAt_dualPotential_meanSeg {s : ℝ} (hs : s ∈ Icc (0 : ℝ) 1) :
    HasDerivAt (fun s ↦ dualPotential μ π L₀ R t (meanSeg μ π L₀ R t a₀ a₁ s))
      (-t * dotJ (meanMap μ π L₀ R t a₁ - meanMap μ π L₀ R t a₀) (dataPath μ π L₀ R t a₀ a₁ s))
      s := by
  have hI := hasFDerivAt_dualPotential hπm hπi (fun x ↦ (hπ x).le) hπpos hL₀m hL₀ hR ht hnd
    (dataPath μ π L₀ R t a₀ a₁ s)
  rw [meanMap_dataPath hπm hπi hπ hπpos hL₀m hL₀ hR ht hnd a₀ a₁ hs] at hI
  have hline := hasDerivAt_affineLine (meanMap μ π L₀ R t a₀)
    (meanMap μ π L₀ R t a₁ - meanMap μ π L₀ R t a₀) s
  have h := hI.comp_hasDerivAt s hline
  refine h.congr_deriv ?_
  rw [_root_.smul_apply, dotCLM_apply, smul_eq_mul]

set_option linter.unusedFintypeInType false in
/-- `s ↦ ⟨d, γ_s⟩` has derivative `⟨d, (Dm(γ_s))⁻¹ d⟩`. -/
theorem hasDerivAt_dot_dataPath {s : ℝ} (hs : s ∈ Icc (0 : ℝ) 1) :
    HasDerivAt (fun s ↦ dotJ (meanMap μ π L₀ R t a₁ - meanMap μ π L₀ R t a₀)
        (dataPath μ π L₀ R t a₀ a₁ s))
      (dotJ (meanMap μ π L₀ R t a₁ - meanMap μ π L₀ R t a₀)
        (invJac hπm hπi (fun x ↦ (hπ x).le) hπpos hL₀m hL₀ hR ht hnd (dataPath μ π L₀ R t a₀ a₁ s)
          (meanMap μ π L₀ R t a₁ - meanMap μ π L₀ R t a₀))) s := by
  set d := meanMap μ π L₀ R t a₁ - meanMap μ π L₀ R t a₀ with hd
  have e : (fun s ↦ dotJ d (dataPath μ π L₀ R t a₀ a₁ s)) =
      fun s ↦ dotCLM d (dataPath μ π L₀ R t a₀ a₁ s) := by
    funext s; rw [dotCLM_apply, dotJ_comm]
  rw [e]
  have h := (dotCLM d).hasFDerivAt.comp_hasDerivAt s
    (hasDerivAt_dataPath hπm hπi hπ hπpos hL₀m hL₀ hR ht hnd a₀ a₁ hs)
  refine h.congr_deriv ?_
  rw [dotCLM_apply, dotJ_comm]

/-- **The dual segment identity (forward)**: `KL(P_{a₁} ‖ P_{a₀}) = ∫₀¹ (1 − s) Q(s) ds`. -/
theorem mixKL_eq_integral_dual_one_sub :
    mixKL μ π (affLoss L₀ R a₁) (dirLoss R (a₀ - a₁)) t 0 1 =
      ∫ s in (0 : ℝ)..1, (1 - s) * dualQuad hπm hπi hπ hπpos hL₀m hL₀ hR ht hnd a₀ a₁ s := by
  set d := meanMap μ π L₀ R t a₁ - meanMap μ π L₀ R t a₀ with hd
  -- the primitive `G(s) = I(y_s) − I(y_0) + (1 − s)(−t⟨d, γ_s⟩) + t⟨d, γ_0⟩`
  have hG : ∀ s ∈ uIcc (0 : ℝ) 1, HasDerivAt (fun s ↦
      dualPotential μ π L₀ R t (meanSeg μ π L₀ R t a₀ a₁ s) -
        dualPotential μ π L₀ R t (meanSeg μ π L₀ R t a₀ a₁ 0) +
        (1 - s) * (-t * dotJ d (dataPath μ π L₀ R t a₀ a₁ s)) +
        t * dotJ d (dataPath μ π L₀ R t a₀ a₁ 0))
      ((1 - s) * dualQuad hπm hπi hπ hπpos hL₀m hL₀ hR ht hnd a₀ a₁ s) s := by
    intro s hs
    rw [uIcc_of_le zero_le_one] at hs
    have h1 := hasDerivAt_dualPotential_meanSeg hπm hπi hπ hπpos hL₀m hL₀ hR ht hnd a₀ a₁ hs
    have h2 := hasDerivAt_dot_dataPath hπm hπi hπ hπpos hL₀m hL₀ hR ht hnd a₀ a₁ hs
    have h := ((h1.sub (hasDerivAt_const s
      (dualPotential μ π L₀ R t (meanSeg μ π L₀ R t a₀ a₁ 0)))).add
      (((hasDerivAt_id s).const_sub 1).mul (h2.const_mul (-t)))).add
      (hasDerivAt_const s (t * dotJ d (dataPath μ π L₀ R t a₀ a₁ 0)))
    refine h.congr_deriv ?_
    rw [dualQuad_eq]
    simp only [id_eq]
    ring
  have hint : IntervalIntegrable
      (fun s ↦ (1 - s) * dualQuad hπm hπi hπ hπpos hL₀m hL₀ hR ht hnd a₀ a₁ s) volume 0 1 := by
    refine ContinuousOn.intervalIntegrable ?_
    rw [uIcc_of_le zero_le_one]
    exact (continuous_const.sub continuous_id).continuousOn.mul
      (continuousOn_dualQuad hπm hπi hπ hπpos hL₀m hL₀ hR ht hnd a₀ a₁)
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hG hint,
    dataPath_one hπm hπi hπ hπpos hL₀m hL₀ hR ht hnd,
    dataPath_zero hπm hπi hπ hπpos hL₀m hL₀ hR ht hnd,
    mixKL_eq_bregman_dual hπm hπi (fun x ↦ (hπ x).le) hπpos hL₀m hL₀ hR ht hnd a₀ a₁]
  have e0 : meanSeg μ π L₀ R t a₀ a₁ 0 = meanMap μ π L₀ R t a₀ := by
    unfold meanSeg; rw [zero_smul, add_zero]
  have e1 : meanSeg μ π L₀ R t a₀ a₁ 1 = meanMap μ π L₀ R t a₁ := by
    unfold meanSeg; rw [one_smul, add_sub_cancel]
  rw [e0, e1, dotJ_comm a₀]
  ring

/-- **The dual segment identity (reverse)**: `KL(P_{a₀} ‖ P_{a₁}) = ∫₀¹ s Q(s) ds`. -/
theorem mixKL_eq_integral_dual_mul :
    mixKL μ π (affLoss L₀ R a₀) (dirLoss R (a₁ - a₀)) t 0 1 =
      ∫ s in (0 : ℝ)..1, s * dualQuad hπm hπi hπ hπpos hL₀m hL₀ hR ht hnd a₀ a₁ s := by
  set d := meanMap μ π L₀ R t a₁ - meanMap μ π L₀ R t a₀ with hd
  -- the primitive `G(s) = s(−t⟨d, γ_s⟩) − I(y_s) + I(y_0)`
  have hG : ∀ s ∈ uIcc (0 : ℝ) 1, HasDerivAt (fun s ↦
      s * (-t * dotJ d (dataPath μ π L₀ R t a₀ a₁ s)) -
        dualPotential μ π L₀ R t (meanSeg μ π L₀ R t a₀ a₁ s) +
        dualPotential μ π L₀ R t (meanSeg μ π L₀ R t a₀ a₁ 0))
      (s * dualQuad hπm hπi hπ hπpos hL₀m hL₀ hR ht hnd a₀ a₁ s) s := by
    intro s hs
    rw [uIcc_of_le zero_le_one] at hs
    have h1 := hasDerivAt_dualPotential_meanSeg hπm hπi hπ hπpos hL₀m hL₀ hR ht hnd a₀ a₁ hs
    have h2 := hasDerivAt_dot_dataPath hπm hπi hπ hπpos hL₀m hL₀ hR ht hnd a₀ a₁ hs
    have h := (((hasDerivAt_id s).mul (h2.const_mul (-t))).sub h1).add
      (hasDerivAt_const s (dualPotential μ π L₀ R t (meanSeg μ π L₀ R t a₀ a₁ 0)))
    refine h.congr_deriv ?_
    rw [dualQuad_eq]
    simp only [id_eq]
    ring
  have hint : IntervalIntegrable
      (fun s ↦ s * dualQuad hπm hπi hπ hπpos hL₀m hL₀ hR ht hnd a₀ a₁ s) volume 0 1 := by
    refine ContinuousOn.intervalIntegrable ?_
    rw [uIcc_of_le zero_le_one]
    exact continuous_id.continuousOn.mul
      (continuousOn_dualQuad hπm hπi hπ hπpos hL₀m hL₀ hR ht hnd a₀ a₁)
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hG hint,
    dataPath_one hπm hπi hπ hπpos hL₀m hL₀ hR ht hnd,
    mixKL_eq_bregman_dual hπm hπi (fun x ↦ (hπ x).le) hπpos hL₀m hL₀ hR ht hnd a₁ a₀]
  have e0 : meanSeg μ π L₀ R t a₀ a₁ 0 = meanMap μ π L₀ R t a₀ := by
    unfold meanSeg; rw [zero_smul, add_zero]
  have e1 : meanSeg μ π L₀ R t a₀ a₁ 1 = meanMap μ π L₀ R t a₁ := by
    unfold meanSeg; rw [one_smul, add_sub_cancel]
  have e2 : dotJ a₁ (meanMap μ π L₀ R t a₀ - meanMap μ π L₀ R t a₁) = -dotJ d a₁ := by
    rw [show meanMap μ π L₀ R t a₀ - meanMap μ π L₀ R t a₁ = -d by rw [hd]; abel,
      (isLinearMap_dotJ a₁).map_neg, dotJ_comm]
  rw [e0, e1, e2]
  ring

/-- **The energy of the mean segment is the Jeffreys divergence**:
`∫₀¹ Q = KL(a₁‖a₀) + KL(a₀‖a₁)`. -/
theorem integral_dualQuad_eq :
    ∫ s in (0 : ℝ)..1, dualQuad hπm hπi hπ hπpos hL₀m hL₀ hR ht hnd a₀ a₁ s =
      mixKL μ π (affLoss L₀ R a₁) (dirLoss R (a₀ - a₁)) t 0 1 +
        mixKL μ π (affLoss L₀ R a₀) (dirLoss R (a₁ - a₀)) t 0 1 := by
  rw [mixKL_eq_integral_dual_one_sub hπm hπi hπ hπpos hL₀m hL₀ hR ht hnd a₀ a₁,
    mixKL_eq_integral_dual_mul hπm hπi hπ hπpos hL₀m hL₀ hR ht hnd a₀ a₁]
  have hc := continuousOn_dualQuad hπm hπi hπ hπpos hL₀m hL₀ hR ht hnd a₀ a₁
  have h1 : IntervalIntegrable
      (fun s ↦ (1 - s) * dualQuad hπm hπi hπ hπpos hL₀m hL₀ hR ht hnd a₀ a₁ s) volume 0 1 := by
    refine ContinuousOn.intervalIntegrable ?_
    rw [uIcc_of_le zero_le_one]; exact (continuous_const.sub continuous_id).continuousOn.mul hc
  have h2 : IntervalIntegrable (fun s ↦ s * dualQuad hπm hπi hπ hπpos hL₀m hL₀ hR ht hnd a₀ a₁ s)
      volume 0 1 := by
    refine ContinuousOn.intervalIntegrable ?_
    rw [uIcc_of_le zero_le_one]; exact continuous_id.continuousOn.mul hc
  rw [← intervalIntegral.integral_add h1 h2]
  exact intervalIntegral.integral_congr fun s _ ↦ by ring

/-- The posterior variance of `φ` along the data path is continuous on the segment. -/
theorem continuousOn_var_dataPath {φ : X → ℝ} (hφm : Measurable φ) {Mφ : ℝ}
    (hφ : ∀ x, |φ x| ≤ Mφ) :
    ContinuousOn (fun s ↦ priorCov μ π (affLoss L₀ R (dataPath μ π L₀ R t a₀ a₁ s)) φ φ t)
      (Icc 0 1) := by
  have hφ2 : ∀ x, |φ x * φ x| ≤ Mφ * Mφ := fun x ↦ by
    rw [abs_mul]
    exact mul_le_mul (hφ x) (hφ x) (abs_nonneg _) ((abs_nonneg _).trans (hφ x))
  have h1 := continuous_obsMap hπm hπi hπ hπpos hL₀m hL₀ hR (φ := fun x ↦ φ x * φ x)
    (hφm.mul hφm) hφ2 ht
  have h2 := continuous_obsMap hπm hπi hπ hπpos hL₀m hL₀ hR hφm hφ ht
  have hc : Continuous (fun a ↦ priorCov μ π (affLoss L₀ R a) φ φ t) := by
    unfold priorCov
    exact h1.sub (h2.mul h2)
  exact hc.comp_continuousOn (continuousOn_dataPath hπm hπi hπ hπpos hL₀m hL₀ hR ht hnd a₀ a₁)

/-- **The response of an observable is controlled by the Jeffreys divergence**:
`|⟨φ⟩_{a₁} − ⟨φ⟩_{a₀}|² ≤ (∫₀¹ Var_{γ_s}(φ) ds) · (KL(a₁‖a₀) + KL(a₀‖a₁))`. -/
theorem sq_obsMean_sub_le_jeffreys {φ : X → ℝ} (hφm : Measurable φ) {Mφ : ℝ}
    (hφ : ∀ x, |φ x| ≤ Mφ) :
    (priorExp μ π (affLoss L₀ R a₁) φ t - priorExp μ π (affLoss L₀ R a₀) φ t) ^ 2 ≤
      (∫ s in (0 : ℝ)..1, priorCov μ π (affLoss L₀ R (dataPath μ π L₀ R t a₀ a₁ s)) φ φ t) *
        (mixKL μ π (affLoss L₀ R a₁) (dirLoss R (a₀ - a₁)) t 0 1 +
          mixKL μ π (affLoss L₀ R a₀) (dirLoss R (a₁ - a₀)) t 0 1) := by
  set d := meanMap μ π L₀ R t a₁ - meanMap μ π L₀ R t a₀ with hd
  set γ := dataPath μ π L₀ R t a₀ a₁ with hγ
  set E := fun s ↦ invJac hπm hπi (fun x ↦ (hπ x).le) hπpos hL₀m hL₀ hR ht hnd (γ s) d with hE
  rw [obsMean_segment_eq hπm hπi hπ hπpos hL₀m hL₀ hR ht hnd a₀ a₁ hφm hφ,
    ← integral_dualQuad_eq hπm hπi hπ hπpos hL₀m hL₀ hR ht hnd a₀ a₁]
  -- pointwise: `|DΦ(y_s) d| ≤ √Var · √Q`
  have hpt : ∀ s ∈ Icc (0 : ℝ) 1, |obsMapDeriv μ π L₀ φ R t (γ s) (E s)| ≤
      Real.sqrt (priorCov μ π (affLoss L₀ R (γ s)) φ φ t *
        dualQuad hπm hπi hπ hπpos hL₀m hL₀ hR ht hnd a₀ a₁ s) := by
    intro s _
    have h := abs_obsMean_deriv_le hπm hπi hπ hπpos hL₀m hL₀ hR ht hnd hφm hφ (γ s) (E s)
    have hid : meanMapDeriv μ π L₀ R t (γ s) (E s) = d := by
      have := congrArg (fun L : (ι → ℝ) →L[ℝ] (ι → ℝ) ↦ L d)
        (meanMapDeriv_comp_invJac hπm hπi (fun x ↦ (hπ x).le) hπpos hL₀m hL₀ hR ht hnd (γ s))
      simpa [hE] using this
    rw [hid, ContinuousLinearMap.comp_apply] at h
    rw [Real.sqrt_mul (priorCov_self_nonneg' hπm hπi hπ hπpos hL₀m hL₀ hR (γ s) ⟨hφm, Mφ, hφ⟩)]
    unfold dualQuad
    exact h
  have hVc := continuousOn_var_dataPath hπm hπi hπ hπpos hL₀m hL₀ hR ht hnd a₀ a₁ hφm hφ
  have hQc := continuousOn_dualQuad hπm hπi hπ hπpos hL₀m hL₀ hR ht hnd a₀ a₁
  have hV0 : ∀ s ∈ Icc (0 : ℝ) 1, 0 ≤ priorCov μ π (affLoss L₀ R (γ s)) φ φ t := fun s _ ↦
    priorCov_self_nonneg' hπm hπi hπ hπpos hL₀m hL₀ hR (γ s) ⟨hφm, Mφ, hφ⟩
  have hQ0 : ∀ s ∈ Icc (0 : ℝ) 1, 0 ≤ dualQuad hπm hπi hπ hπpos hL₀m hL₀ hR ht hnd a₀ a₁ s := by
    intro s hs
    rw [dualQuad_eq]
    have hid : meanMapDeriv μ π L₀ R t (γ s) (E s) = d := by
      have := congrArg (fun L : (ι → ℝ) →L[ℝ] (ι → ℝ) ↦ L d)
        (meanMapDeriv_comp_invJac hπm hπi (fun x ↦ (hπ x).le) hπpos hL₀m hL₀ hR ht hnd (γ s))
      simpa [hE] using this
    have hq := dualHessian_quadratic_form hπm hπi (fun x ↦ (hπ x).le) hπpos hL₀m hL₀ hR ht hnd
      (γ s) (E s)
    rw [hid] at hq
    unfold dualHessian at hq
    rw [_root_.smul_apply, (isLinearMap_dotJ _).map_smul, smul_eq_mul] at hq
    rw [hq]
    unfold responseForm
    exact mul_nonneg (sq_nonneg _)
      (priorCov_self_nonneg' hπm hπi hπ hπpos hL₀m hL₀ hR (γ s) (bdd_dirLoss hR (E s)))
  -- integrate the pointwise bound and apply Cauchy–Schwarz
  have hI : IntervalIntegrable (fun s ↦ obsMapDeriv μ π L₀ φ R t (γ s) (E s)) volume 0 1 := by
    refine ContinuousOn.intervalIntegrable ?_
    rw [uIcc_of_le zero_le_one]
    exact ((continuous_obsMapDeriv hπm hπi hπ hπpos hL₀m hL₀ hR hφm hφ ht).comp_continuousOn
      (continuousOn_dataPath hπm hπi hπ hπpos hL₀m hL₀ hR ht hnd a₀ a₁)).clm_apply
      (continuousOn_dataPath_velocity hπm hπi hπ hπpos hL₀m hL₀ hR ht hnd a₀ a₁)
  have hIs : IntervalIntegrable (fun s ↦ Real.sqrt (priorCov μ π (affLoss L₀ R (γ s)) φ φ t *
      dualQuad hπm hπi hπ hπpos hL₀m hL₀ hR ht hnd a₀ a₁ s)) volume 0 1 := by
    refine ContinuousOn.intervalIntegrable ?_
    rw [uIcc_of_le zero_le_one]
    exact Real.continuous_sqrt.comp_continuousOn (hVc.mul hQc)
  have habs : |∫ s in (0 : ℝ)..1, obsMapDeriv μ π L₀ φ R t (γ s) (E s)| ≤
      ∫ s in (0 : ℝ)..1, Real.sqrt (priorCov μ π (affLoss L₀ R (γ s)) φ φ t *
        dualQuad hπm hπi hπ hπpos hL₀m hL₀ hR ht hnd a₀ a₁ s) := by
    refine (intervalIntegral.abs_integral_le_integral_abs zero_le_one).trans ?_
    exact intervalIntegral.integral_mono_on zero_le_one hI.abs hIs hpt
  have hcs := sq_integral_sqrt_mul_le hVc hQc hV0 hQ0
  calc (∫ s in (0 : ℝ)..1, obsMapDeriv μ π L₀ φ R t (γ s) (E s)) ^ 2
      = |∫ s in (0 : ℝ)..1, obsMapDeriv μ π L₀ φ R t (γ s) (E s)| ^ 2 := (sq_abs _).symm
    _ ≤ (∫ s in (0 : ℝ)..1, Real.sqrt (priorCov μ π (affLoss L₀ R (γ s)) φ φ t *
          dualQuad hπm hπi hπ hπpos hL₀m hL₀ hR ht hnd a₀ a₁ s)) ^ 2 :=
        pow_le_pow_left₀ (abs_nonneg _) habs 2
    _ ≤ _ := hcs

end Segment

end Laplace.Multi
