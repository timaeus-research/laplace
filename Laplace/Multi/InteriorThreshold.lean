/-
Copyright (c) 2026 Timaeus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Timaeus
-/
import Mathlib
import Laplace.Multi.HalfspaceProjection
import Laplace.Multi.FaceInfinite
import Laplace.Multi.FeaturelessPoint

/-!
# Interior thresholds admit a finite tilt

Along the tilt ray `a_λ = a − (λ/t) u` the response in the direction `u`,
`r(λ) = u · m_t(a_λ)` (`thresholdFun`), is monotone with derivative the variance `Var_{a_λ}(R_u)`
(`hasDerivAt_thresholdFun`), and it converges to the essential supremum `β` of `u · R` as
`λ → ∞` (`tendsto_thresholdFun`) — with no positive-mass hypothesis on the exposed face: the tilted
mean of a bounded statistic always concentrates at its essential extremum
(`tendsto_priorExp_face_inf`).

Hence **every threshold `u · m_t(a) < r < β` is attained by a finite tilt `λ ≥ 0`**
(`exists_threshold_tilt`), and the information-projection certificate of `HalfspaceProjection`
applies: the Chernoff rate in direction `u` at level `r` is the least divergence to the halfspace,
`sup_{μ ≥ 0} {μ r − Λ_a(μu)} = inf {KL(P_b ‖ P_a) | u · m_t(b) ≥ r}` (`chernoff_rate_eq_inf_KL`).
Under feature nondegeneracy the tilt is unique (`thresholdFun_strictMono`).
-/

open MeasureTheory Filter Topology Set

namespace Laplace.Multi

variable {X : Type*} [MeasurableSpace X] {μ : Measure X}

/-- Scaling the loss scales the temperature. -/
theorem priorExp_const_mul_loss (π L φ : X → ℝ) (c s : ℝ) :
    priorExp μ π (fun x ↦ c * L x) φ s = priorExp μ π L φ (s * c) := by
  unfold priorExp priorZ
  simp only [show ∀ x, -(s * (c * L x)) = -(s * c * L x) from fun x ↦ by ring]

/-- The expectation of the negative of an observable. -/
theorem priorExp_neg_obs (π L φ : X → ℝ) (s : ℝ) :
    priorExp μ π L (fun x ↦ -φ x) s = -priorExp μ π L φ s := by
  have e : (fun x ↦ -φ x) = fun x ↦ (-1 : ℝ) * φ x := funext fun x ↦ by ring
  rw [e, priorExp_const_mul_bdd]
  ring

section Face

variable [Nonempty X] {π : X → ℝ} (hπm : Measurable π) (hπi : Integrable π μ) (hπ : ∀ x, 0 < π x)
  (hπpos : 0 < ∫ x, π x ∂μ) {V : X → ℝ} (hVm : Measurable V) {M : ℝ} (hV : ∀ x, |V x| ≤ M)
  {α : ℝ} (hα : ∀ᵐ x ∂μ, α ≤ V x)
include hπm hπi hπ hπpos hVm hV hα

/-- The tilted mean of `V` is at least its essential lower bound. -/
theorem priorExp_face_ge (lam : ℝ) : α ≤ priorExp μ π V V lam := by
  have hZ := priorZ_face_pos hπm hπi hπ hπpos hVm hV lam
  have hw : Integrable (fun x ↦ Real.exp (-(lam * V x)) * π x) μ :=
    (integrable_face_weight hπm hπi hπ hVm lam (f := fun _ ↦ (1 : ℝ)) measurable_const (Mf := 1)
      (fun _ ↦ by simp) hπpos hV).congr (Eventually.of_forall fun x ↦ by simp)
  have hVw : Integrable (fun x ↦ V x * Real.exp (-(lam * V x)) * π x) μ :=
    (integrable_face_weight hπm hπi hπ hVm lam hVm hV hπpos hV).congr
      (Eventually.of_forall fun x ↦ by ring)
  unfold priorExp
  rw [le_div_iff₀ hZ]
  have e : α * priorZ μ π V lam = ∫ x, α * (Real.exp (-(lam * V x)) * π x) ∂μ := by
    unfold priorZ
    rw [integral_const_mul]
  rw [e]
  refine integral_mono_ae (hw.const_mul α) hVw ?_
  filter_upwards [hα] with x hx
  have : 0 ≤ Real.exp (-(lam * V x)) * π x := (mul_pos (Real.exp_pos _) (hπ x)).le
  nlinarith

omit hα in
/-- The tilted mean exceeds the essential lower bound by at most `ε` plus a multiple of the tilted
mass outside the `ε`-neighbourhood of the face. -/
theorem priorExp_face_sub_le {ε : ℝ} (hε : 0 < ε) (lam : ℝ) :
    priorExp μ π V V lam - α ≤ ε + (M + |α|) *
      ((∫ x in {x | V x < α + ε}ᶜ, Real.exp (-(lam * V x)) * π x ∂μ) / priorZ μ π V lam) := by
  have hZ := priorZ_face_pos hπm hπi hπ hπpos hVm hV lam
  have hA : MeasurableSet {x | V x < α + ε} := measurableSet_lt hVm measurable_const
  have hw : Integrable (fun x ↦ Real.exp (-(lam * V x)) * π x) μ :=
    (integrable_face_weight hπm hπi hπ hVm lam (f := fun _ ↦ (1 : ℝ)) measurable_const (Mf := 1)
      (fun _ ↦ by simp) hπpos hV).congr (Eventually.of_forall fun x ↦ by simp)
  have hw0 : ∀ x, 0 ≤ Real.exp (-(lam * V x)) * π x := fun x ↦
    (mul_pos (Real.exp_pos _) (hπ x)).le
  have hVw : Integrable (fun x ↦ V x * Real.exp (-(lam * V x)) * π x) μ :=
    (integrable_face_weight hπm hπi hπ hVm lam hVm hV hπpos hV).congr
      (Eventually.of_forall fun x ↦ by ring)
  have hsub : Integrable (fun x ↦ (V x - α) * (Real.exp (-(lam * V x)) * π x)) μ :=
    (hVw.sub (hw.const_mul α)).congr (Eventually.of_forall fun x ↦ by
      simp only [Pi.sub_apply]; ring)
  -- the centred numerator
  have e : priorExp μ π V V lam - α =
      (∫ x, (V x - α) * (Real.exp (-(lam * V x)) * π x) ∂μ) / priorZ μ π V lam := by
    unfold priorExp
    rw [eq_div_iff hZ.ne', sub_mul, div_mul_cancel₀ _ hZ.ne']
    have e1 : (∫ x, (V x - α) * (Real.exp (-(lam * V x)) * π x) ∂μ) =
        (∫ x, V x * Real.exp (-(lam * V x)) * π x ∂μ) -
          ∫ x, α * (Real.exp (-(lam * V x)) * π x) ∂μ := by
      rw [← integral_sub hVw (hw.const_mul α)]
      exact integral_congr_ae (Eventually.of_forall fun x ↦ by ring)
    rw [e1, integral_const_mul]
    rfl
  rw [e, div_le_iff₀ hZ]
  have hsplit := integral_add_compl₀ hA.nullMeasurableSet hsub
  -- inside the neighbourhood
  have h1 : (∫ x in {x | V x < α + ε}, (V x - α) * (Real.exp (-(lam * V x)) * π x) ∂μ) ≤
      ε * priorZ μ π V lam := by
    calc (∫ x in {x | V x < α + ε}, (V x - α) * (Real.exp (-(lam * V x)) * π x) ∂μ)
        ≤ ∫ x in {x | V x < α + ε}, ε * (Real.exp (-(lam * V x)) * π x) ∂μ := by
          refine setIntegral_mono_on hsub.integrableOn (hw.integrableOn.const_mul _) hA
            fun x hx ↦ ?_
          have hx' : V x < α + ε := hx
          exact mul_le_mul_of_nonneg_right (by linarith) (hw0 x)
      _ = ε * ∫ x in {x | V x < α + ε}, Real.exp (-(lam * V x)) * π x ∂μ := integral_const_mul _ _
      _ ≤ ε * priorZ μ π V lam :=
          mul_le_mul_of_nonneg_left (setIntegral_le_integral hw (ae_of_all _ hw0)) hε.le
  -- outside the neighbourhood
  have h2 : (∫ x in {x | V x < α + ε}ᶜ, (V x - α) * (Real.exp (-(lam * V x)) * π x) ∂μ) ≤
      (M + |α|) * ∫ x in {x | V x < α + ε}ᶜ, Real.exp (-(lam * V x)) * π x ∂μ := by
    rw [← integral_const_mul]
    refine setIntegral_mono_on hsub.integrableOn (hw.integrableOn.const_mul _) hA.compl
      fun x _ ↦ ?_
    refine mul_le_mul_of_nonneg_right ?_ (hw0 x)
    have := hV x
    have := le_abs_self (V x)
    have := neg_le_abs α
    linarith
  have hmul : (ε + (M + |α|) * ((∫ x in {x | V x < α + ε}ᶜ,
      Real.exp (-(lam * V x)) * π x ∂μ) / priorZ μ π V lam)) * priorZ μ π V lam =
      ε * priorZ μ π V lam + (M + |α|) *
        ∫ x in {x | V x < α + ε}ᶜ, Real.exp (-(lam * V x)) * π x ∂μ := by
    field_simp
  rw [hmul, ← hsplit]
  linarith

/-- **The tilted mean of a bounded statistic concentrates at its essential extremum**:
`⟨V⟩_λ → α` as `λ → ∞`, assuming only that every neighbourhood of the face carries mass. -/
theorem tendsto_priorExp_face_inf (hmass : ∀ ε > 0, 0 < ∫ x in {x | V x < α + ε}, π x ∂μ) :
    Tendsto (fun lam : ℝ ↦ priorExp μ π V V lam) atTop (𝓝 α) := by
  refine tendsto_order.2 ⟨fun c hc ↦ Eventually.of_forall fun lam ↦
    lt_of_lt_of_le hc (priorExp_face_ge hπm hπi hπ hπpos hVm hV hα lam), fun c hc ↦ ?_⟩
  set ε := (c - α) / 2 with hεdef
  have hε : 0 < ε := by rw [hεdef]; linarith
  have hm : 0 < ∫ x in {x | V x < α + ε / 2}, π x ∂μ := hmass (ε / 2) (by positivity)
  have htend := (tendsto_tilt_mass_compl hπm hπi hπ hπpos hVm hV hε hm).const_mul (M + |α|)
  rw [mul_zero] at htend
  filter_upwards [htend.eventually (gt_mem_nhds hε)] with lam hlam
  have := priorExp_face_sub_le hπm hπi hπ hπpos hVm hV (α := α) hε lam
  linarith

end Face

section Family

variable {ι : Type*} [Fintype ι] [Nonempty X] {π L₀ : X → ℝ} (hπm : Measurable π)
  (hπi : Integrable π μ) (hπ : ∀ x, 0 < π x) (hπpos : 0 < ∫ x, π x ∂μ) (hL₀m : Measurable L₀)
  {M₀ : ℝ} (hL₀ : ∀ x, |L₀ x| ≤ M₀) {R : ι → X → ℝ} (hR : ∀ i, Bdd (R i)) {t : ℝ} (ht : 0 < t)
include hπm hπi hπ hπpos hL₀m hL₀ hR ht

/-- The response in direction `u` along the tilt ray `a − (λ/t) u`. -/
noncomputable def thresholdFun (μ : Measure X) (π L₀ : X → ℝ) (R : ι → X → ℝ) (t : ℝ)
    (a u : ι → ℝ) (lam : ℝ) : ℝ :=
  priorExp μ π (affLoss L₀ R (a - (lam / t) • u)) (dirLoss R u) t

omit [Nonempty X] hπm hπi hπ hπpos hL₀m hL₀ hR ht in
theorem thresholdFun_zero (a u : ι → ℝ) :
    thresholdFun μ π L₀ R t a u 0 = priorExp μ π (affLoss L₀ R a) (dirLoss R u) t := by
  simp [thresholdFun]

omit [Nonempty X] ht in
theorem thresholdFun_eq_sum (a u : ι → ℝ) (lam : ℝ) :
    thresholdFun μ π L₀ R t a u lam = ∑ i, u i * meanMap μ π L₀ R t (a - (lam / t) • u) i :=
  priorExp_dirLoss (tiltData_aff hπm hπi (fun x ↦ (hπ x).le) hπpos hL₀m hL₀ hR
    (a - (lam / t) • u) (a - (lam / t) • u) t).choose_spec.ν_int hR u

omit [MeasurableSpace X] [Fintype ι] [Nonempty X] hπm hπi hπ hπpos hL₀m hL₀ hR ht in
theorem sub_div_smul_eq (a u : ι → ℝ) (s : ℝ) : a + s • (-(1 / t) • u) = a - (s / t) • u := by
  ext i
  simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
  ring

/-- **The threshold function has derivative the variance**: `d/dλ u·m(a_λ) = Var_{a_λ}(R_u)`. -/
theorem hasDerivAt_thresholdFun (a u : ι → ℝ) (lam₀ : ℝ) :
    HasDerivAt (thresholdFun μ π L₀ R t a u)
      (priorCov μ π (affLoss L₀ R (a - (lam₀ / t) • u)) (dirLoss R u) (dirLoss R u) t) lam₀ := by
  have h := hasDerivAt_priorExp_line hπm hπi hπ hπpos hL₀m hL₀ hR ht a (-(1 / t) • u) lam₀
    (bdd_dirLoss hR u)
  have e : (fun s ↦ priorExp μ π (affLoss L₀ R (a + s • (-(1 / t) • u))) (dirLoss R u) t) =
      thresholdFun μ π L₀ R t a u := by
    funext s
    simp only [thresholdFun, sub_div_smul_eq]
  rw [e, sub_div_smul_eq] at h
  refine h.congr_deriv ?_
  rw [dirLoss_smul, priorCov_const_mul_right']
  field_simp

theorem thresholdFun_monotone (a u : ι → ℝ) : Monotone (thresholdFun μ π L₀ R t a u) := by
  refine monotone_of_deriv_nonneg
    (fun lam ↦ (hasDerivAt_thresholdFun hπm hπi hπ hπpos hL₀m hL₀ hR ht a u lam).differentiableAt)
    fun lam ↦ ?_
  rw [(hasDerivAt_thresholdFun hπm hπi hπ hπpos hL₀m hL₀ hR ht a u lam).deriv]
  exact priorCov_self_nonneg' hπm hπi hπ hπpos hL₀m hL₀ hR (t := t) _ (bdd_dirLoss hR u)

theorem thresholdFun_continuous (a u : ι → ℝ) : Continuous (thresholdFun μ π L₀ R t a u) :=
  continuous_iff_continuousAt.2 fun lam ↦
    (hasDerivAt_thresholdFun hπm hπi hπ hπpos hL₀m hL₀ hR ht a u lam).continuousAt

/-- Under feature nondegeneracy the threshold function is strictly increasing. -/
theorem thresholdFun_strictMono
    (hnd : ∀ v : ι → ℝ, v ≠ 0 → ¬ ∃ c : ℝ, ∀ᵐ x ∂μ, π x ≠ 0 → dirLoss R v x = c)
    (a : ι → ℝ) {u : ι → ℝ} (hu : u ≠ 0) : StrictMono (thresholdFun μ π L₀ R t a u) := by
  refine strictMono_of_deriv_pos fun lam ↦ ?_
  rw [(hasDerivAt_thresholdFun hπm hπi hπ hπpos hL₀m hL₀ hR ht a u lam).deriv]
  have := segVar_pos hπm hπi hπ hπpos hL₀m hL₀ hR ht hnd (a - (lam / t) • u) u hu 0
  unfold segVar at this
  rwa [zero_smul, add_zero] at this

omit [MeasurableSpace X] [Nonempty X] hπm hπi hπ hπpos hL₀m hL₀ hR ht in
theorem affLoss_affLoss (L₀ : X → ℝ) (R : ι → X → ℝ) (a b : ι → ℝ) :
    affLoss (affLoss L₀ R a) R b = affLoss L₀ R (a + b) := by
  funext x
  simp only [affLoss, Pi.add_apply, add_mul, Finset.sum_add_distrib]
  ring

/-- **The threshold function converges to the essential supremum** of `u·R` as `λ → ∞`. -/
theorem tendsto_thresholdFun (a u : ι → ℝ) {β : ℝ} (hβ : ∀ᵐ x ∂μ, dirLoss R u x ≤ β)
    (hmass : ∀ ε > 0, 0 < ∫ x in {x | β - ε < dirLoss R u x}, π x ∂μ) :
    Tendsto (thresholdFun μ π L₀ R t a u) atTop (𝓝 β) := by
  obtain ⟨hLam, Ma, hLab⟩ := bdd_affLoss hL₀m hL₀ hR a
  obtain ⟨hDm, MD, hDb⟩ := bdd_dirLoss hR u
  -- the tilted base `π' = e^{−t L_a} π` and the statistic `V' = −u·R`
  have hπ'm : Measurable (tiltedPrior π (affLoss L₀ R a) t) := measurable_tiltedPrior hπm hLam t
  have hπ'i : Integrable (tiltedPrior π (affLoss L₀ R a) t) μ :=
    integrable_tiltedPrior hπi hLam hLab ht
  have hπ' : ∀ x, 0 < tiltedPrior π (affLoss L₀ R a) t x := tiltedPrior_pos hπ _ t
  have hπ'pos : 0 < ∫ x, tiltedPrior π (affLoss L₀ R a) t x ∂μ :=
    integral_tiltedPrior_pos hπm hπi (fun x ↦ (hπ x).le) hπpos hLam hLab hR t
  have hV'm : Measurable (fun x ↦ -dirLoss R u x) := hDm.neg
  have hV' : ∀ x, |(fun x ↦ -dirLoss R u x) x| ≤ MD := fun x ↦ by
    simp only [abs_neg]
    exact hDb x
  have hα' : ∀ᵐ x ∂μ, -β ≤ (fun x ↦ -dirLoss R u x) x := by
    filter_upwards [hβ] with x hx
    show -β ≤ -dirLoss R u x
    linarith
  have hmass' : ∀ ε > 0, 0 < ∫ x in {x | (fun x ↦ -dirLoss R u x) x < -β + ε},
      tiltedPrior π (affLoss L₀ R a) t x ∂μ := by
    intro ε hε
    have hset : {x | (fun x ↦ -dirLoss R u x) x < -β + ε} = {x | β - ε < dirLoss R u x} := by
      ext x
      simp only [Set.mem_ofPred_eq]
      constructor <;> intro h <;> linarith
    rw [hset]
    have h1 := hmass ε hε
    rw [setIntegral_pos_iff_support_of_nonneg_ae (Eventually.of_forall fun x ↦ (hπ x).le)
      hπi.integrableOn] at h1
    rw [setIntegral_pos_iff_support_of_nonneg_ae (Eventually.of_forall fun x ↦ (hπ' x).le)
      hπ'i.integrableOn]
    have hs1 : Function.support π ∩ {x | β - ε < dirLoss R u x} = {x | β - ε < dirLoss R u x} :=
      Set.inter_eq_right.2 fun x _ ↦ (hπ x).ne'
    have hs2 : Function.support (tiltedPrior π (affLoss L₀ R a) t) ∩
        {x | β - ε < dirLoss R u x} = {x | β - ε < dirLoss R u x} :=
      Set.inter_eq_right.2 fun x _ ↦ (hπ' x).ne'
    rw [hs1] at h1
    rwa [hs2]
  have h := tendsto_priorExp_face_inf hπ'm hπ'i hπ' hπ'pos hV'm hV' hα' hmass'
  have h2 := h.neg
  rw [neg_neg] at h2
  refine h2.congr fun lam ↦ ?_
  -- transport the threshold function to the tilt of `π'`
  have e1 : thresholdFun μ π L₀ R t a u lam =
      priorExp μ (tiltedPrior π (affLoss L₀ R a) t) (dirLoss R u) (dirLoss R u) (-lam) := by
    unfold thresholdFun
    rw [← sub_div_smul_eq, ← affLoss_affLoss, priorExp_ray_eq_tilted, dirLoss_smul,
      priorExp_const_mul_loss]
    congr 1
    field_simp
  have e2 : priorExp μ (tiltedPrior π (affLoss L₀ R a) t) (fun x ↦ -dirLoss R u x)
      (fun x ↦ -dirLoss R u x) lam =
      -priorExp μ (tiltedPrior π (affLoss L₀ R a) t) (dirLoss R u) (dirLoss R u) (-lam) := by
    have e3 : (fun x ↦ -dirLoss R u x) = fun x ↦ (-1 : ℝ) * dirLoss R u x :=
      funext fun x ↦ by ring
    conv_lhs => rw [e3, priorExp_const_mul_loss, ← e3, priorExp_neg_obs]
    rw [mul_neg_one]
  rw [e1, e2, neg_neg]

/-- **Every interior threshold is attained by a finite tilt**: if `u·m(a) < r < β` then some
`λ ≥ 0` has `u·m(a − (λ/t)u) = r`. -/
theorem exists_threshold_tilt (a u : ι → ℝ) {β : ℝ} (hβ : ∀ᵐ x ∂μ, dirLoss R u x ≤ β)
    (hmass : ∀ ε > 0, 0 < ∫ x in {x | β - ε < dirLoss R u x}, π x ∂μ) {r : ℝ}
    (hr₁ : priorExp μ π (affLoss L₀ R a) (dirLoss R u) t < r) (hr₂ : r < β) :
    ∃ lam, 0 ≤ lam ∧ thresholdFun μ π L₀ R t a u lam = r := by
  have hlim := tendsto_thresholdFun hπm hπi hπ hπpos hL₀m hL₀ hR ht a u hβ hmass
  obtain ⟨Λ, hΛ⟩ := (hlim.eventually (lt_mem_nhds hr₂)).exists
  have h0 : thresholdFun μ π L₀ R t a u 0 < r := by rwa [thresholdFun_zero]
  have hΛ0 : 0 ≤ Λ := by
    by_contra hneg
    have := thresholdFun_monotone hπm hπi hπ hπpos hL₀m hL₀ hR ht a u (le_of_lt (not_le.1 hneg))
    linarith
  have hIVT := intermediate_value_Icc hΛ0
    (thresholdFun_continuous hπm hπi hπ hπpos hL₀m hL₀ hR ht a u).continuousOn
    ⟨h0.le, hΛ.le⟩
  obtain ⟨lam, ⟨hlam0, _⟩, hlam⟩ := hIVT
  exact ⟨lam, hlam0, hlam⟩

/-- **Interior thresholds have information projections**: for `u·m(a) < r < β` there is a tilt
`λ ≥ 0` whose member `a* = a − (λ/t)u` is the least-divergence member of the halfspace and whose
divergence is the greatest Chernoff rate. -/
theorem exists_halfspace_projection (a u : ι → ℝ) {β : ℝ} (hβ : ∀ᵐ x ∂μ, dirLoss R u x ≤ β)
    (hmass : ∀ ε > 0, 0 < ∫ x in {x | β - ε < dirLoss R u x}, π x ∂μ) {r : ℝ}
    (hr₁ : ∑ i, u i * meanMap μ π L₀ R t a i < r) (hr₂ : r < β) :
    ∃ lam, 0 ≤ lam ∧
      IsLeast {k | ∃ b, r ≤ ∑ i, u i * meanMap μ π L₀ R t b i ∧ k = famKL μ π L₀ R t b a}
        (famKL μ π L₀ R t (a - (lam / t) • u) a) ∧
      IsGreatest {d | ∃ mu, 0 ≤ mu ∧ d = mu * r - famCgf μ π L₀ R t a (mu • u)}
        (famKL μ π L₀ R t (a - (lam / t) • u) a) := by
  have hr₁' : priorExp μ π (affLoss L₀ R a) (dirLoss R u) t < r := by
    have := thresholdFun_eq_sum hπm hπi hπ hπpos hL₀m hL₀ hR (t := t) a u 0
    rw [thresholdFun_zero] at this
    rw [this]
    simpa using hr₁
  obtain ⟨lam, hlam0, hlam⟩ :=
    exists_threshold_tilt hπm hπi hπ hπpos hL₀m hL₀ hR ht a u hβ hmass hr₁' hr₂
  rw [thresholdFun_eq_sum hπm hπi hπ hπpos hL₀m hL₀ hR] at hlam
  have hslack : lam * (∑ i, u i * meanMap μ π L₀ R t (a - (lam / t) • u) i - r) = 0 := by
    rw [hlam, sub_self, mul_zero]
  exact ⟨lam, hlam0,
    isLeast_famKL_halfspace hπm hπi hπ hπpos hL₀m hL₀ hR ht a u r lam hlam0 hlam.ge hslack,
    isGreatest_chernoffRate hπm hπi hπ hπpos hL₀m hL₀ hR ht a u r lam hlam0 hlam.ge hslack⟩

/-- **Cramér's rate is the information distance to the halfspace**: for interior thresholds,
`sup_{μ ≥ 0} {μ r − Λ_a(μu)} = inf {KL(P_b ‖ P_a) | u·m_t(b) ≥ r}`. -/
theorem chernoff_rate_eq_inf_KL (a u : ι → ℝ) {β : ℝ} (hβ : ∀ᵐ x ∂μ, dirLoss R u x ≤ β)
    (hmass : ∀ ε > 0, 0 < ∫ x in {x | β - ε < dirLoss R u x}, π x ∂μ) {r : ℝ}
    (hr₁ : ∑ i, u i * meanMap μ π L₀ R t a i < r) (hr₂ : r < β) :
    sSup {d | ∃ mu, 0 ≤ mu ∧ d = mu * r - famCgf μ π L₀ R t a (mu • u)} =
      sInf {k | ∃ b, r ≤ ∑ i, u i * meanMap μ π L₀ R t b i ∧ k = famKL μ π L₀ R t b a} := by
  obtain ⟨lam, _, hleast, hgreatest⟩ :=
    exists_halfspace_projection hπm hπi hπ hπpos hL₀m hL₀ hR ht a u hβ hmass hr₁ hr₂
  rw [hgreatest.csSup_eq, hleast.csInf_eq]

end Family

end Laplace.Multi
