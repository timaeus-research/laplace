/-
Copyright (c) 2026 Timaeus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Timaeus
-/
import Mathlib
import Laplace.Multi.QuotientMeanMap
import Laplace.Multi.EntropyDuality
import Laplace.Multi.RadialLaws
import Laplace.Multi.RayChart

/-!
# Natural coordinates: the joint exponential family of temperature and data

The posteriors `P_{t,a} ∝ e^{-t L_a} π`, `L_a = L₀ + ∑ aᵢRᵢ`, form ONE exponential family with the
augmented statistic `S = (L₀, R₁, …, R_k)` and natural parameter `θ = Θ(t,a) = (t, t a)`:
`t L_a = ⟨θ, S⟩`. Everything landed for the affine family at a fixed temperature applies to `S` at
temperature `1`, and pulls back along `Θ`.

* **Pull-back of the slice quantities.** `⟨φ⟩_{θ=Θ(t,a)} = ⟨φ⟩_{t,a}` (`priorExp_natCoord`), the
  joint mean map restricts to the physical mean map (`meanMap_natCoord_some`) with the extra
  component `⟨L₀⟩_{t,a}` (`meanMap_natCoord_none`), the joint free energy `ψ(Θ(t,a)) = log Z_t(L_a)`
  (`affLogZ_natCoord`), and the joint response form in the tangent direction `DΘ(t,a)(s,v) =
  (s, a s + t v)` is `Var_{t,a}(s L_a + t R_v)` (`responseForm_natTangent`): the Fisher metric of
  the full family in physical coordinates has the blocks `Var(L_a)`, `t Cov(L_a,R_v)` and
  `t² Cov(R_v,R_w)`.
* **The joint kernel.** The invisible directions of the joint family are the `(s,v)` with
  `s L₀ + R_v` a.e. constant; the purely data directions `(0, v)` are invisible iff `v` is invisible
  for the slice (`dataDir_mem_invisibleSet_iff`), and a joint invisible direction with `s ≠ 0`
  exhibits `L₀` as an a.e. affine combination of the contrasts (`invisible_temperature_dir`).
* **KL is the Bregman divergence of `ψ`** in natural coordinates (`natKL_eq`), and on a physical
  slice it is the slice KL (`natKL_natCoord`).
* **The featureless anchor.** `KL(P_θ ‖ P_0) = ∫₀¹ s Var_{sθ}(S_θ) ds` (`natKL_zero_eq_integral`):
  the divergence from the distinguished prior is the integrated response form along the natural
  ray, with the linear weight `s`. This is the joint form of the ray-chart Legendre identity.
* **The ray inside the joint family.** `Θ(u,a) = u Θ(1,a)` (`natCoord_eq_smul`) and the ray
  chart coordinate of `RayChart` is `⟨L_a⟩_{u,a} = η₀ + a·M` (`lawMean_lossLaw_eq`,
  `lawMean_eq_dot_meanMap`), the joint mean map evaluated on the ray.
-/

open MeasureTheory Filter Topology Set

namespace Laplace.Multi

variable {X : Type*} [MeasurableSpace X] {μ : Measure X} {ι : Type*} [Fintype ι]

/-! ### The augmented statistic and the natural coordinates -/

/-- The augmented statistic `S = (L₀, R)`, indexed by `Option ι` (`none ↦ L₀`). -/
def jointStat (L₀ : X → ℝ) (R : ι → X → ℝ) : Option ι → X → ℝ := fun j ↦ j.elim L₀ R

/-- The natural coordinates `Θ(t, a) = (t, t a)`. -/
def natCoord (t : ℝ) (a : ι → ℝ) : Option ι → ℝ := fun j ↦ j.elim t fun i ↦ t * a i

/-- The tangent map `DΘ(t,a)(s, v) = (s, a s + t v)`. -/
def natTangent (t : ℝ) (a : ι → ℝ) (s : ℝ) (v : ι → ℝ) : Option ι → ℝ :=
  fun j ↦ j.elim s fun i ↦ a i * s + t * v i

/-- A purely data direction `(0, v)` in the joint tangent space. -/
def dataDir (v : ι → ℝ) : Option ι → ℝ := fun j ↦ j.elim 0 v

omit [MeasurableSpace X] in
theorem dirLoss_jointStat_natCoord (L₀ : X → ℝ) (R : ι → X → ℝ) (t : ℝ) (a : ι → ℝ) (x : X) :
    dirLoss (jointStat L₀ R) (natCoord t a) x = t * affLoss L₀ R a x := by
  simp only [dirLoss, jointStat, natCoord, affLoss, Fintype.sum_option, Option.elim,
    Finset.mul_sum, mul_add]
  refine congrArg _ (Finset.sum_congr rfl fun i _ ↦ ?_)
  ring

omit [MeasurableSpace X] in
theorem affLoss_zero_jointStat_natCoord (L₀ : X → ℝ) (R : ι → X → ℝ) (t : ℝ) (a : ι → ℝ) :
    affLoss (fun _ ↦ (0 : ℝ)) (jointStat L₀ R) (natCoord t a) =
      fun x ↦ t * affLoss L₀ R a x + 0 := by
  funext x
  have := dirLoss_jointStat_natCoord L₀ R t a x
  simp only [dirLoss] at this
  simp only [affLoss, zero_add, add_zero]
  simpa [affLoss] using this

omit [MeasurableSpace X] in
theorem dirLoss_jointStat_dataDir (L₀ : X → ℝ) (R : ι → X → ℝ) (v : ι → ℝ) (x : X) :
    dirLoss (jointStat L₀ R) (dataDir v) x = dirLoss R v x := by
  simp [dirLoss, jointStat, dataDir, Fintype.sum_option, Option.elim]

omit [MeasurableSpace X] in
theorem dirLoss_jointStat_natTangent (L₀ : X → ℝ) (R : ι → X → ℝ) (t : ℝ) (a : ι → ℝ) (s : ℝ)
    (v : ι → ℝ) (x : X) :
    dirLoss (jointStat L₀ R) (natTangent t a s v) x =
      s * affLoss L₀ R a x + t * dirLoss R v x := by
  simp only [dirLoss, jointStat, natTangent, affLoss, Fintype.sum_option, Option.elim, mul_add,
    Finset.mul_sum, add_mul, Finset.sum_add_distrib]
  rw [add_assoc]
  refine congrArg _ (congrArg₂ _ (Finset.sum_congr rfl fun i _ ↦ ?_)
    (Finset.sum_congr rfl fun i _ ↦ ?_)) <;> ring

omit [MeasurableSpace X] [Fintype ι] in
theorem natCoord_eq_smul (u : ℝ) (a : ι → ℝ) : natCoord u a = u • natCoord 1 a := by
  funext j
  cases j <;> simp [natCoord, Option.elim]

omit [Fintype ι] in
theorem bdd_jointStat {L₀ : X → ℝ} (hL₀m : Measurable L₀) {M₀ : ℝ} (hL₀ : ∀ x, |L₀ x| ≤ M₀)
    {R : ι → X → ℝ} (hR : ∀ i, Bdd (R i)) : ∀ j, Bdd (jointStat L₀ R j) := by
  intro j
  cases j with
  | none => exact ⟨hL₀m, M₀, hL₀⟩
  | some i => exact hR i

/-! ### The joint kernel -/

/-- A purely data direction is invisible for the joint family iff it is invisible for the slice. -/
theorem dataDir_mem_invisibleSet_iff (L₀ : X → ℝ) (R : ι → X → ℝ) (v : ι → ℝ) :
    dataDir v ∈ invisibleSet μ (jointStat L₀ R) ↔ v ∈ invisibleSet μ R := by
  simp only [invisibleSet, mem_ofPred_eq, dirLoss_jointStat_dataDir]

/-- A joint invisible direction with nonzero temperature component exhibits `L₀` as an a.e. affine
combination of the contrasts: `L₀ = c/s − R_{v/s}` a.e. -/
theorem invisible_temperature_dir (L₀ : X → ℝ) (R : ι → X → ℝ) {w : Option ι → ℝ}
    (hw : w ∈ invisibleSet μ (jointStat L₀ R)) (hs : w none ≠ 0) :
    ∃ c : ℝ, ∀ᵐ x ∂μ, L₀ x = c - dirLoss R (fun i ↦ w (some i) / w none) x := by
  obtain ⟨c, hc⟩ := hw
  refine ⟨c / w none, ?_⟩
  filter_upwards [hc] with x hx
  simp only [dirLoss, jointStat, Fintype.sum_option, Option.elim] at hx
  simp only [dirLoss]
  have e : (∑ i, w (some i) / w none * R i x) = (∑ i, w (some i) * R i x) / w none := by
    rw [Finset.sum_div]
    exact Finset.sum_congr rfl fun i _ ↦ by ring
  rw [e, ← hx]
  field_simp
  ring

/-! ### Pull-back of the slice quantities -/

section Slice

variable (π : X → ℝ) (L₀ : X → ℝ) (R : ι → X → ℝ) (t : ℝ) (a : ι → ℝ)

/-- `⟨φ⟩_{Θ(t,a)} = ⟨φ⟩_{t,a}`. -/
theorem priorExp_natCoord (φ : X → ℝ) :
    priorExp μ π (affLoss (fun _ ↦ (0 : ℝ)) (jointStat L₀ R) (natCoord t a)) φ 1 =
      priorExp μ π (affLoss L₀ R a) φ t := by
  rw [affLoss_zero_jointStat_natCoord, priorExp_smul_add, mul_one]

theorem priorZ_natCoord :
    priorZ μ π (affLoss (fun _ ↦ (0 : ℝ)) (jointStat L₀ R) (natCoord t a)) 1 =
      priorZ μ π (affLoss L₀ R a) t := by
  rw [affLoss_zero_jointStat_natCoord]
  unfold priorZ
  simp only [one_mul, add_zero]

theorem priorCov_natCoord (φ ψ : X → ℝ) :
    priorCov μ π (affLoss (fun _ ↦ (0 : ℝ)) (jointStat L₀ R) (natCoord t a)) φ ψ 1 =
      priorCov μ π (affLoss L₀ R a) φ ψ t := by
  unfold priorCov
  rw [priorExp_natCoord, priorExp_natCoord, priorExp_natCoord]

/-- The joint free energy on the slice is the slice free energy. -/
theorem affLogZ_natCoord :
    affLogZ μ π (fun _ ↦ (0 : ℝ)) (jointStat L₀ R) 1 (natCoord t a) = affLogZ μ π L₀ R t a := by
  unfold affLogZ
  rw [priorZ_natCoord]

/-- The joint mean map restricted to the data components is the physical mean map. -/
theorem meanMap_natCoord_some (i : ι) :
    meanMap μ π (fun _ ↦ (0 : ℝ)) (jointStat L₀ R) 1 (natCoord t a) (some i) =
      meanMap μ π L₀ R t a i := by
  unfold meanMap
  rw [priorExp_natCoord]
  rfl

/-- The temperature component of the joint mean map is the mean base loss. -/
theorem meanMap_natCoord_none :
    meanMap μ π (fun _ ↦ (0 : ℝ)) (jointStat L₀ R) 1 (natCoord t a) none =
      priorExp μ π (affLoss L₀ R a) L₀ t := by
  unfold meanMap
  rw [priorExp_natCoord]
  rfl

/-- **The pulled-back Fisher metric**: in the physical tangent direction `(s, v)` the joint
response form is `Var_{t,a}(s L_a + t R_v)`. -/
theorem responseForm_natTangent (s : ℝ) (v : ι → ℝ) :
    responseForm μ π (fun _ ↦ (0 : ℝ)) (jointStat L₀ R) (natCoord t a) 1 (natTangent t a s v)
      (natTangent t a s v) =
      priorCov μ π (affLoss L₀ R a) (fun x ↦ s * affLoss L₀ R a x + t * dirLoss R v x)
        (fun x ↦ s * affLoss L₀ R a x + t * dirLoss R v x) t := by
  unfold responseForm
  rw [one_pow, one_mul, priorCov_natCoord]
  congr 1 <;> funext x <;> exact dirLoss_jointStat_natTangent L₀ R t a s v x

end Slice

/-! ### The ray inside the joint family -/

section Ray

/-- The ray-chart coordinate of `RayChart` is the mean loss of the slice: `m(u) = ⟨L_a⟩_{u,a}`. -/
theorem lawMean_lossLaw_eq {π L₀ : X → ℝ} (hπm : Measurable π) (hπ : ∀ x, 0 ≤ π x)
    (hL₀m : Measurable L₀) {R : ι → X → ℝ} (hR : ∀ i, Bdd (R i)) (a : ι → ℝ) (u : ℝ) :
    lawMean (lossLaw μ π (affLoss L₀ R a)) u =
      priorExp μ π (affLoss L₀ R a) (affLoss L₀ R a) u := by
  have hLm : Measurable (affLoss L₀ R a) := hL₀m.add (bdd_dirLoss hR a).1
  have := priorExp_comp_eq_lawExp (μ := μ) hπm hπ hLm (f := fun ℓ ↦ ℓ) measurable_id u
  unfold lawMean lawExp lawMoment at *
  simp only [pow_one, pow_zero, one_mul] at this ⊢
  exact this.symm

end Ray

/-! ### KL as the Bregman divergence of `ψ`, and the featureless anchor -/

section Bregman

variable [Nonempty X] {π L₀ : X → ℝ} (hπm : Measurable π) (hπi : Integrable π μ)
  (hπ : ∀ x, 0 < π x) (hπpos : 0 < ∫ x, π x ∂μ) (hL₀m : Measurable L₀) {M₀ : ℝ}
  (hL₀ : ∀ x, |L₀ x| ≤ M₀) {R : ι → X → ℝ} (hR : ∀ i, Bdd (R i))
include hπm hπi hπ hπpos hL₀m hL₀ hR

/-- **KL is the Bregman divergence of the joint free energy**:
`KL(P_θ ‖ P_ϑ) = ψ(ϑ) − ψ(θ) + ⟨ϑ − θ, M(θ)⟩` (recall `∇ψ = −M`). -/
theorem natKL_eq (θ ϑ : Option ι → ℝ) :
    mixKL μ π (affLoss (fun _ ↦ (0 : ℝ)) (jointStat L₀ R) θ) (dirLoss (jointStat L₀ R) (ϑ - θ))
        1 0 1 =
      affLogZ μ π (fun _ ↦ (0 : ℝ)) (jointStat L₀ R) 1 ϑ -
        affLogZ μ π (fun _ ↦ (0 : ℝ)) (jointStat L₀ R) 1 θ +
        ∑ j, (ϑ j - θ j) * meanMap μ π (fun _ ↦ (0 : ℝ)) (jointStat L₀ R) 1 θ j := by
  have hS : ∀ j, Bdd (jointStat L₀ R j) := bdd_jointStat hL₀m hL₀ hR
  have h0 : ∀ x, |(fun _ : X ↦ (0 : ℝ)) x| ≤ 0 := fun _ ↦ by simp
  have h := mixKL_aff_eq hπm hπi (fun x ↦ (hπ x).le) hπpos measurable_const h0 hS 1 θ ϑ
  rwa [one_mul] at h

/-- On a physical slice the joint KL is the slice KL. -/
theorem natKL_natCoord (t : ℝ) (a b : ι → ℝ) :
    mixKL μ π (affLoss (fun _ ↦ (0 : ℝ)) (jointStat L₀ R) (natCoord t a))
        (dirLoss (jointStat L₀ R) (natCoord t b - natCoord t a)) 1 0 1 =
      mixKL μ π (affLoss L₀ R a) (dirLoss R (b - a)) t 0 1 := by
  rw [natKL_eq hπm hπi hπ hπpos hL₀m hL₀ hR,
    mixKL_aff_eq hπm hπi (fun x ↦ (hπ x).le) hπpos hL₀m hL₀ hR t a b, affLogZ_natCoord,
    affLogZ_natCoord, Fintype.sum_option]
  simp only [natCoord, Option.elim, sub_self, zero_mul, zero_add, meanMap_natCoord_some,
    Finset.mul_sum]
  refine congrArg _ (Finset.sum_congr rfl fun i _ ↦ ?_)
  ring

/-- The line derivative of the free energy at every point of the line:
`d/ds A_t(a + s v) = −t ⟨R_v⟩_{a + s v}`. -/
theorem hasDerivAt_affLogZ_line (t : ℝ) (a v : ι → ℝ) (s : ℝ) :
    HasDerivAt (fun s : ℝ ↦ affLogZ μ π L₀ R t (a + s • v))
      (-t * priorExp μ π (affLoss L₀ R (a + s • v)) (dirLoss R v) t) s := by
  obtain ⟨hLm, ML, hLb⟩ := bdd_affLoss hL₀m hL₀ hR (a + s • v)
  have h : TiltData μ (baseWeight π (affLoss L₀ R (a + s • v)) t) (fun _ ↦ 0) 0 :=
    tiltData_baseWeight_of_bounded μ hπm hπi (fun x ↦ (hπ x).le) hπpos hLm hLb measurable_const
      (fun _ ↦ by simp) t
  have key := h.hasDerivAt_affLogZ_dir hR v
  have key' : HasDerivAt (fun ε : ℝ ↦ affLogZ μ π L₀ R t (a + s • v + ε • v))
      (-t * priorExp μ π (affLoss L₀ R (a + s • v)) (dirLoss R v) t) (s - s) := by
    rw [sub_self]; exact key
  have h2 := key'.comp_sub_const s s
  refine h2.congr_of_eventuallyEq (Filter.Eventually.of_forall fun s' ↦ ?_)
  change affLogZ μ π L₀ R t (a + s' • v) = affLogZ μ π L₀ R t (a + s • v + (s' - s) • v)
  congr 1
  module

omit [Nonempty X] in
/-- The mean contrast along a line is the dot product with the mean map. -/
theorem priorExp_dirLoss_eq_dot (t : ℝ) (a v : ι → ℝ) :
    priorExp μ π (affLoss L₀ R a) (dirLoss R v) t = ∑ i, v i * meanMap μ π L₀ R t a i :=
  priorExp_dirLoss
    (tiltData_aff hπm hπi (fun x ↦ (hπ x).le) hπpos hL₀m hL₀ hR a a t).choose_spec.ν_int hR v

/-- **The featureless anchor**: for the joint family,
`KL(P_θ ‖ P_0) = ∫₀¹ s Var_{sθ}(S_θ) ds` — the divergence from the distinguished prior is the
integrated response form along the natural ray, weighted by `s`. -/
theorem natKL_zero_eq_integral (θ : Option ι → ℝ) :
    mixKL μ π (affLoss (fun _ ↦ (0 : ℝ)) (jointStat L₀ R) θ) (dirLoss (jointStat L₀ R) (0 - θ))
        1 0 1 =
      ∫ s in (0 : ℝ)..1, s * priorCov μ π (affLoss (fun _ ↦ (0 : ℝ)) (jointStat L₀ R) (s • θ))
        (dirLoss (jointStat L₀ R) θ) (dirLoss (jointStat L₀ R) θ) 1 := by
  set S := jointStat L₀ R with hS
  have hS' : ∀ j, Bdd (S j) := bdd_jointStat hL₀m hL₀ hR
  have h0 : ∀ x, |(fun _ : X ↦ (0 : ℝ)) x| ≤ 0 := fun x ↦ by simp
  obtain ⟨hθm, Mθ, hθb⟩ := bdd_dirLoss hS' θ
  -- the two line derivatives
  have hψ : ∀ s, HasDerivAt (fun s : ℝ ↦ affLogZ μ π (fun _ ↦ (0 : ℝ)) S 1 (0 + s • θ))
      (-1 * priorExp μ π (affLoss (fun _ ↦ (0 : ℝ)) S (0 + s • θ)) (dirLoss S θ) 1) s := fun s ↦
    hasDerivAt_affLogZ_line hπm hπi hπ hπpos measurable_const h0 hS' 1 0 θ s
  have hD : ∀ s, HasDerivAt (fun s ↦ priorExp μ π (affLoss (fun _ ↦ (0 : ℝ)) S (0 + s • θ))
      (dirLoss S θ) 1) (obsMapDeriv μ π (fun _ ↦ (0 : ℝ)) (dirLoss S θ) S 1 (0 + s • θ) θ) s :=
    fun s ↦ by
    have h := (hasFDerivAt_obsMap hπm hπi hπ hπpos measurable_const h0 hS' hθm hθb one_pos
      (0 + s • θ)).comp_hasDerivAt s (hasDerivAt_affineLine 0 θ s)
    exact h
  -- the primitive `g(s) = ψ(0) − ψ(sθ) − s D(s)`
  have hg : ∀ s, HasDerivAt (fun s ↦ affLogZ μ π (fun _ ↦ (0 : ℝ)) S 1 0 -
      affLogZ μ π (fun _ ↦ (0 : ℝ)) S 1 (0 + s • θ) -
      s * priorExp μ π (affLoss (fun _ ↦ (0 : ℝ)) S (0 + s • θ)) (dirLoss S θ) 1)
      (-(s * obsMapDeriv μ π (fun _ ↦ (0 : ℝ)) (dirLoss S θ) S 1 (0 + s • θ) θ)) s := fun s ↦ by
    have h := ((hasDerivAt_const s (affLogZ μ π (fun _ ↦ (0 : ℝ)) S 1 0)).sub (hψ s)).sub
      ((hasDerivAt_id s).mul (hD s))
    refine h.congr_deriv ?_
    simp only [id_eq]
    ring
  have hlc : Continuous (fun s : ℝ ↦ (0 : Option ι → ℝ) + s • θ) :=
    continuous_const.add ((continuous_id : Continuous fun s : ℝ ↦ s).smul
      (continuous_const : Continuous fun _ : ℝ ↦ θ))
  have hcont : Continuous (fun s ↦ -(s * obsMapDeriv μ π (fun _ ↦ (0 : ℝ)) (dirLoss S θ) S 1
      (0 + s • θ) θ)) :=
    (continuous_id.mul (((continuous_obsMapDeriv hπm hπi hπ hπpos measurable_const h0 hS' hθm hθb
      one_pos).comp hlc).clm_apply continuous_const)).neg
  have hftc := intervalIntegral.integral_eq_sub_of_hasDerivAt (fun s _ ↦ hg s)
    (hcont.intervalIntegrable (μ := volume) 0 1)
  have hint : (∫ s in (0 : ℝ)..1, -(s * obsMapDeriv μ π (fun _ ↦ (0 : ℝ)) (dirLoss S θ) S 1
      (0 + s • θ) θ)) = ∫ s in (0 : ℝ)..1, s * priorCov μ π (affLoss (fun _ ↦ (0 : ℝ)) S (s • θ))
        (dirLoss S θ) (dirLoss S θ) 1 :=
    intervalIntegral.integral_congr fun s _ ↦ by
      rw [obsMapDeriv_apply hπm hπi hπ hπpos measurable_const h0 hS' hθm hθb one_pos (0 + s • θ) θ,
        zero_add]
      ring
  rw [← hint, hftc, natKL_eq hπm hπi hπ hπpos hL₀m hL₀ hR, ← hS]
  simp only [one_smul, zero_smul, add_zero, zero_add, zero_mul, sub_zero, sub_self, one_mul]
  rw [priorExp_dirLoss_eq_dot hπm hπi hπ hπpos measurable_const h0 hS' 1 θ θ]
  simp only [Pi.zero_apply, zero_sub, neg_mul, Finset.sum_neg_distrib]
  ring

omit [Nonempty X] in
/-- **The ray chart coordinate in the joint family**: `⟨L_a⟩_{u,a} = η₀ + a·M` where `η = (η₀, M)`
is the joint mean map at `Θ(u,a)`. -/
theorem lawMean_eq_dot_meanMap (a : ι → ℝ) (u : ℝ) :
    lawMean (lossLaw μ π (affLoss L₀ R a)) u =
      ∑ j, natCoord 1 a j * meanMap μ π (fun _ ↦ (0 : ℝ)) (jointStat L₀ R) 1 (natCoord u a) j := by
  rw [lawMean_lossLaw_eq hπm (fun x ↦ (hπ x).le) hL₀m hR, Fintype.sum_option]
  simp only [natCoord, Option.elim, one_mul, meanMap_natCoord_none, meanMap_natCoord_some]
  have hν : Integrable (baseWeight π (affLoss L₀ R a) u) μ :=
    (tiltData_aff hπm hπi (fun x ↦ (hπ x).le) hπpos hL₀m hL₀ hR a a u).choose_spec.ν_int
  have hint0 : Integrable (fun x ↦ L₀ x * Real.exp (-(u * affLoss L₀ R a x)) * π x) μ := by
    have := hν.bdd_mul hL₀m.aestronglyMeasurable
      (Filter.Eventually.of_forall fun x ↦ (Real.norm_eq_abs _).trans_le (hL₀ x))
    exact this.congr (Filter.Eventually.of_forall fun x ↦ by simp [baseWeight]; ring)
  have hint1 : Integrable (fun x ↦ dirLoss R a x * Real.exp (-(u * affLoss L₀ R a x)) * π x) μ := by
    obtain ⟨ham, Ma, hab⟩ := bdd_dirLoss hR a
    have := hν.bdd_mul ham.aestronglyMeasurable
      (Filter.Eventually.of_forall fun x ↦ (Real.norm_eq_abs _).trans_le (hab x))
    exact this.congr (Filter.Eventually.of_forall fun x ↦ by simp [baseWeight]; ring)
  have e : priorExp μ π (affLoss L₀ R a) (affLoss L₀ R a) u =
      priorExp μ π (affLoss L₀ R a) (fun x ↦ L₀ x + dirLoss R a x) u := rfl
  rw [e, priorExp_add_of_integrable hint0 hint1, priorExp_dirLoss hν hR]
  rfl

end Bregman

end Laplace.Multi
