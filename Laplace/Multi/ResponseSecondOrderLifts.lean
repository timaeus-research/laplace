/-
Copyright (c) 2026 Timaeus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Timaeus
-/
import Laplace.Multi.ResponseDataHessian
import Laplace.Multi.ResponseTiltPathBudget
import Laplace.Multi.ResponseSubmersionCalculus
import Laplace.Multi.ObservableCurvature

/-!
# Second-order lifts: response accelerations along general journeys and prescribed two-jets

The response Hessian theorem (`ResponseDataHessian`) was proved along the straight journeys
`g + t k`. Here it is extended to **coefficient journeys** `ρ_t = ν.tilted (⟨a(t), h⟩)` with `C²`
coefficients `a` (`hasDerivAt_responseVel_coeff`), and combined with the linearity of the response
velocity and of the Hessian in the direction (`responseVel_dirLoss`, `responseHess_dirLoss`) to give
the **acceleration of the response along any such journey**:

  `(Φ ∘ g)'' = DΦ_{g_t}[g''_t] + H_{g_t}(g'_t, g'_t)`   (`hasDerivAt_coeffVel`).

For the polynomial journey `g + t k + t²/2 b` this reads `(Φ∘g)''(0) = DΦ_g[b] + H_g(k,k)`
(`hasDerivAt_jetVel_zero`). Since the differential is onto the direction space, with the horizontal
lift as a right inverse, **every response two-jet can be prescribed**: for any `v ∈ W` the choice
`b = hor_g(v − H_g(k,k))` gives a data journey whose response has initial velocity `DΦ_g[k]` and
acceleration `v` (`exists_jet_accel`, `exists_journey_two_jet`); in particular a journey with
`DΦ_g[k] = 0` can be made stationary under the response through second order
(`exists_jet_stationary`). This is a two-jet statement, not an exact fibre curve.
-/

open MeasureTheory Filter Topology Set

namespace Laplace.Multi

section Coeff

variable {X : Type*} [MeasurableSpace X] [Nonempty X] {J : Type*} [Fintype J] [Nonempty J]
  {S : J → X → ℝ} (hS : ∀ j, Bdd (S j)) (ν : Measure X) [IsProbabilityMeasure ν]
  {ι : Type*} [Fintype ι] {h : ι → X → ℝ} (hh : ∀ j, Bdd (h j)) {a a' : ℝ → ι → ℝ}
  (ha : ∀ t, HasDerivAt a (a' t) t) (ha' : Continuous a')
include hS hh ha ha'

/-- The direction space. -/
local notation "𝕍" => dirSpan ν (fun _ ↦ (1 : ℝ)) S

/-- The response (inverse chart). -/
local notation "θr" => responseTheta measurable_const (integrable_const 1) (fun _ ↦ one_pos)
  (one_integral_pos ν) hS

/-- The chart derivative equivalence. -/
local notation "CDE" => chartDerivEquiv measurable_const (integrable_const 1) (fun _ ↦ one_pos)
  (one_integral_pos ν) hS

omit [Fintype J] [Nonempty J] hS in
/-- **Covariances move by third cumulants along a coefficient journey**:
`d/dt Cov_{ρ_t}(φ,ψ) = κ_{ρ_t}(φ, ψ, ġ_t)`. -/
theorem hasDerivAt_lawCov_coeff {φ ψ : X → ℝ} (hφ : Bdd φ) (hψ : Bdd ψ) (t₀ : ℝ) :
    HasDerivAt (fun t ↦ lawCov (ν.tilted (dirLoss h (a t))) φ ψ)
      (thirdCentral (ν.tilted (dirLoss h (a t₀))) φ ψ (dirLoss h (a' t₀))) t₀ := by
  have hP : IsProbabilityMeasure (ν.tilted (dirLoss h (a t₀))) :=
    isProbabilityMeasure_tilted (integrable_exp_of_bdd ν (bdd_dirLoss hh (a t₀)))
  have h1 := hasDerivAt_integral_tilted_dirLoss ν hh ha ha' (hφ.mul hψ) t₀
  have h2 := hasDerivAt_integral_tilted_dirLoss ν hh ha ha' hφ t₀
  have h3 := hasDerivAt_integral_tilted_dirLoss ν hh ha ha' hψ t₀
  have h := h1.sub (h2.mul h3)
  unfold lawCov
  refine h.congr_deriv ?_
  rw [thirdCentral_eq _ hφ hψ (bdd_dirLoss hh _)]
  unfold lawCov
  ring

/-- **The forcing moves by the data cumulant along a coefficient journey.** -/
theorem hasDerivAt_forcing_coeff {ℓ : X → ℝ} (hℓ : Bdd ℓ) (t₀ : ℝ) :
    HasDerivAt (fun t ↦ forcing S ν (dirLoss h (a t)) ℓ)
      (dataThird hS ν (bdd_dirLoss hh (a t₀)) (bdd_dirLoss hh (a' t₀)) hℓ : J → ℝ) t₀ := by
  refine hasDerivAt_pi.2 fun j ↦ ?_
  rw [dataThird_apply]
  have h := hasDerivAt_lawCov_coeff ν hh ha ha' (hS j) hℓ t₀
  rw [thirdCentral_comm₂₃] at h
  exact h

omit hh ha ha' in
theorem responseOf_coeff_eq (t : ℝ) :
    responseOf hS ν (dirLoss h (a t)) = θr (coeffMean S ν h a t) := rfl

omit ha ha' in
theorem responseVel_coeff_eq {ℓ : X → ℝ} (hℓ : Bdd ℓ) (t : ℝ) :
    responseVel hS ν (bdd_dirLoss hh (a t)) hℓ =
      (CDE (θr (coeffMean S ν h a t))).symm ⟨forcing S ν (dirLoss h (a t)) ℓ,
        forcing_mem_dirSpan hS ν (bdd_dirLoss hh (a t)) hℓ⟩ := by
  rw [responseVel, responseOf_coeff_eq hS ν t]

/-- **The response Hessian theorem along a coefficient journey**: the velocity field
`t ↦ DΦ_{g_t}[ℓ]` has derivative `H_{g_t}(ġ_t, ℓ)`. -/
theorem hasDerivAt_responseVel_coeff {ℓ : X → ℝ} (hℓ : Bdd ℓ) (t₀ : ℝ) :
    HasDerivAt (fun t ↦ responseVel hS ν (bdd_dirLoss hh (a t)) hℓ)
      (responseHess hS ν (bdd_dirLoss hh (a t₀)) (bdd_dirLoss hh (a' t₀)) hℓ) t₀ := by
  have hrel := coeffMean_mem_intrinsicInterior hS ν hh (a := a) t₀
  have hmemz : ∀ t, coeffMean S ν h a t - coeffMean S ν h a t₀ ∈ 𝕍 := fun t ↦
    sub_mem_dirSpan_of_mem_momentBody' hS ν (intrinsicInterior_subset hrel)
      (intrinsicInterior_subset (coeffMean_mem_intrinsicInterior hS ν hh (a := a) t))
  obtain ⟨z, hzdef⟩ : ∃ z : ℝ → 𝕍,
      z = fun t ↦ ⟨coeffMean S ν h a t - coeffMean S ν h a t₀, hmemz t⟩ := ⟨_, rfl⟩
  have hz : HasDerivAt z ⟨forcing S ν (dirLoss h (a t₀)) (dirLoss h (a' t₀)),
      forcing_mem_dirSpan hS ν (bdd_dirLoss hh (a t₀)) (bdd_dirLoss hh (a' t₀))⟩ t₀ := by
    rw [hzdef]
    exact hasDerivAt_subtype_of_hasDerivAt _ ((hasDerivAt_coeffMean hS ν hh ha ha' t₀).sub_const _)
  have hz0 : z t₀ = 0 := by
    rw [hzdef]
    exact Subtype.ext (sub_self _)
  have hinv0 := hasFDerivAt_inverse_response hS ν hrel
  rw [← hz0] at hinv0
  have hinv := hinv0.comp_hasDerivAt t₀ hz
  obtain ⟨F, hFdef⟩ : ∃ F : ℝ → 𝕍, F = fun t ↦
      ⟨forcing S ν (dirLoss h (a t)) ℓ, forcing_mem_dirSpan hS ν (bdd_dirLoss hh (a t)) hℓ⟩ :=
    ⟨_, rfl⟩
  have hF : HasDerivAt F (dataThird hS ν (bdd_dirLoss hh (a t₀)) (bdd_dirLoss hh (a' t₀)) hℓ)
      t₀ := by
    rw [hFdef]
    exact hasDerivAt_subtype_of_hasDerivAt _ (hasDerivAt_forcing_coeff hS ν hh ha ha' hℓ t₀)
  have hD := hinv.clm_apply hF
  refine (hD.congr_of_eventuallyEq (Eventually.of_forall fun t ↦ ?_)).congr_deriv ?_
  · change responseVel hS ν (bdd_dirLoss hh (a t)) hℓ =
      (CDE (θr (coeffMean S ν h a t₀ + (z t : J → ℝ)))).symm (F t)
    rw [hzdef, hFdef]
    change responseVel hS ν (bdd_dirLoss hh (a t)) hℓ =
      (CDE (θr (coeffMean S ν h a t₀ + (coeffMean S ν h a t - coeffMean S ν h a t₀)))).symm
        ⟨forcing S ν (dirLoss h (a t)) ℓ, _⟩
    simp only [add_sub_cancel]
    rfl
  · simp only [Function.comp_def, hz0, Submodule.coe_zero, add_zero, hFdef]
    rw [← ContinuousLinearMap.flip_apply, inverse_response_deriv_apply, responseHess, map_sub,
      responseOf_coeff_eq hS ν t₀, responseVel_coeff_eq hS ν hh (bdd_dirLoss hh (a' t₀)) t₀,
      responseVel_coeff_eq hS ν hh hℓ t₀, sub_eq_neg_add]
    rfl

end Coeff

section Linear

variable {X : Type*} [MeasurableSpace X] [Nonempty X] {J : Type*} [Fintype J] [Nonempty J]
  {S : J → X → ℝ} (hS : ∀ j, Bdd (S j)) (ν : Measure X) [IsProbabilityMeasure ν]
  {g : X → ℝ} (hg : Bdd g)
include hS hg

/-- The direction space. -/
local notation "𝕍" => dirSpan ν (fun _ ↦ (1 : ℝ)) S

omit [Nonempty X] [Fintype J] [Nonempty J] hS [IsProbabilityMeasure ν] hg in
/-- A visible contrast is a linear combination in the score space. -/
theorem bddSpace_dirLoss_eq {ι : Type*} [Fintype ι] {h : ι → X → ℝ} (hh : ∀ i, Bdd (h i))
    (c : ι → ℝ) :
    (⟨dirLoss h c, bdd_dirLoss hh c⟩ : bddSpace X) = ∑ i, c i • (⟨h i, hh i⟩ : bddSpace X) := by
  apply Subtype.ext
  rw [Submodule.coe_sum]
  funext x
  simp [dirLoss, Finset.sum_apply]

/-- **The response velocity is linear in the direction.** -/
theorem responseVel_dirLoss {ι : Type*} [Fintype ι] {h : ι → X → ℝ} (hh : ∀ i, Bdd (h i))
    (c : ι → ℝ) :
    responseVel hS ν hg (bdd_dirLoss hh c) = ∑ i, c i • responseVel hS ν hg (hh i) := by
  have e := congrArg (velLin hS ν hg) (bddSpace_dirLoss_eq hh c)
  rw [map_sum] at e
  simp only [map_smul, velLin_apply] at e
  exact e

/-- The data cumulant is linear in its second direction. -/
theorem dataThird_dirLoss {ι : Type*} [Fintype ι] {h : ι → X → ℝ} (hh : ∀ i, Bdd (h i))
    (c : ι → ℝ) {k : X → ℝ} (hk : Bdd k) :
    dataThird hS ν hg hk (bdd_dirLoss hh c) = ∑ i, c i • dataThird hS ν hg hk (hh i) := by
  have := isProbabilityMeasure_tilted (integrable_exp_of_bdd ν hg)
  apply Subtype.ext
  rw [Submodule.coe_sum]
  funext j
  rw [Finset.sum_apply, dataThird_apply, thirdCentral_comm₂₃, thirdCentral_comm₁₂,
    thirdCentral_dirLoss_left _ hh c (hS j) hk]
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  rw [Submodule.coe_smul, Pi.smul_apply, smul_eq_mul, dataThird_apply, thirdCentral_comm₁₂,
    thirdCentral_comm₂₃]

omit hg in
/-- The Hessian depends only on the three functions. -/
theorem responseHess_congr' {g g' k k' ℓ ℓ' : X → ℝ} (hg : Bdd g) (hg' : Bdd g') (hk : Bdd k)
    (hk' : Bdd k') (hℓ : Bdd ℓ) (hℓ' : Bdd ℓ') (eg : g = g') (ek : k = k') (eℓ : ℓ = ℓ') :
    responseHess hS ν hg hk hℓ = responseHess hS ν hg' hk' hℓ' := by
  subst eg
  subst ek
  subst eℓ
  rfl

/-- **The response Hessian is linear in its second direction.** -/
theorem responseHess_dirLoss {ι : Type*} [Fintype ι] {h : ι → X → ℝ} (hh : ∀ i, Bdd (h i))
    (c : ι → ℝ) {k : X → ℝ} (hk : Bdd k) :
    responseHess hS ν hg hk (bdd_dirLoss hh c) = ∑ i, c i • responseHess hS ν hg hk (hh i) := by
  unfold responseHess
  rw [dataThird_dirLoss hS ν hg hh c hk, responseVel_dirLoss hS ν hg hh c, map_sum]
  simp only [map_smul]
  rw [← Finset.sum_sub_distrib, map_sum]
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  rw [← smul_sub, map_smul]

end Linear

section Second

variable {X : Type*} [MeasurableSpace X] [Nonempty X] {J : Type*} [Fintype J] [Nonempty J]
  {S : J → X → ℝ} (hS : ∀ j, Bdd (S j)) (ν : Measure X) [IsProbabilityMeasure ν]
  {ι : Type*} [Fintype ι] {h : ι → X → ℝ} (hh : ∀ j, Bdd (h j)) {a a' a'' : ℝ → ι → ℝ}
  (ha : ∀ t, HasDerivAt a (a' t) t) (ha' : Continuous a') (ha'' : ∀ t, HasDerivAt a' (a'' t) t)
include hS hh ha ha' ha''

/-- **The acceleration of the response along a `C²` coefficient journey**:
`d/dt DΦ_{g_t}[ġ_t] = DΦ_{g_t}[g̈_t] + H_{g_t}(ġ_t, ġ_t)`. -/
theorem hasDerivAt_coeffVel (t₀ : ℝ) :
    HasDerivAt (fun t ↦ responseVel hS ν (bdd_dirLoss hh (a t)) (bdd_dirLoss hh (a' t)))
      (responseVel hS ν (bdd_dirLoss hh (a t₀)) (bdd_dirLoss hh (a'' t₀)) +
        responseHess hS ν (bdd_dirLoss hh (a t₀)) (bdd_dirLoss hh (a' t₀))
          (bdd_dirLoss hh (a' t₀))) t₀ := by
  have hi : ∀ i, HasDerivAt (fun t ↦ a' t i • responseVel hS ν (bdd_dirLoss hh (a t)) (hh i))
      (a' t₀ i • responseHess hS ν (bdd_dirLoss hh (a t₀)) (bdd_dirLoss hh (a' t₀)) (hh i) +
        a'' t₀ i • responseVel hS ν (bdd_dirLoss hh (a t₀)) (hh i)) t₀ := fun i ↦
    (hasDerivAt_pi.1 (ha'' t₀) i).smul (hasDerivAt_responseVel_coeff hS ν hh ha ha' (hh i) t₀)
  have hsum := HasDerivAt.fun_sum (u := Finset.univ) fun i _ ↦ hi i
  refine (hsum.congr_of_eventuallyEq (Eventually.of_forall fun t ↦
    responseVel_dirLoss hS ν (bdd_dirLoss hh (a t)) hh (a' t))).congr_deriv ?_
  rw [Finset.sum_add_distrib, responseVel_dirLoss hS ν (bdd_dirLoss hh (a t₀)) hh (a'' t₀),
    responseHess_dirLoss hS ν (bdd_dirLoss hh (a t₀)) hh (a' t₀) (bdd_dirLoss hh (a' t₀)),
    add_comm]

end Second

section Jet

variable {X : Type*} [MeasurableSpace X] [Nonempty X] {J : Type*} [Fintype J] [Nonempty J]
  {S : J → X → ℝ} (hS : ∀ j, Bdd (S j)) (ν : Measure X) [IsProbabilityMeasure ν]
  {g k b : X → ℝ} (hg : Bdd g) (hk : Bdd k) (hb : Bdd b)
include hS hg hk hb

/-- The direction space. -/
local notation "𝕍" => dirSpan ν (fun _ ↦ (1 : ℝ)) S

omit [MeasurableSpace X] [Nonempty X] [Fintype J] [Nonempty J] hS [IsProbabilityMeasure ν] hg hk
  hb in
/-- The coefficients of the polynomial journey `g + t k + t²/2 b`. -/
noncomputable def jetCoeff (t : ℝ) : Fin 3 → ℝ := ![1, t, t ^ 2 / 2]

omit [MeasurableSpace X] [Nonempty X] [Fintype J] [Nonempty J] hS [IsProbabilityMeasure ν] hg hk
  hb in
/-- The velocity coefficients `(0, 1, t)`. -/
def jetCoeff' (t : ℝ) : Fin 3 → ℝ := ![0, 1, t]

omit [MeasurableSpace X] [Nonempty X] [Fintype J] [Nonempty J] hS [IsProbabilityMeasure ν] hg hk
  hb in
/-- The acceleration coefficients `(0, 0, 1)`. -/
def jetCoeff'' (_t : ℝ) : Fin 3 → ℝ := ![0, 0, 1]

omit [Nonempty X] [Fintype J] [Nonempty J] hS [IsProbabilityMeasure ν] in
theorem jetFamily_bdd : ∀ i, Bdd (![g, k, b] i) := fun i ↦ by
  fin_cases i
  exacts [hg, hk, hb]

omit [MeasurableSpace X] [Nonempty X] [Fintype J] [Nonempty J] hS [IsProbabilityMeasure ν] hg hk
  hb in
theorem hasDerivAt_jetCoeff (t : ℝ) : HasDerivAt jetCoeff (jetCoeff' t) t := by
  refine hasDerivAt_pi.2 fun i ↦ ?_
  fin_cases i
  · exact hasDerivAt_const t (1 : ℝ)
  · exact hasDerivAt_id t
  · have := (hasDerivAt_pow 2 t).div_const 2
    refine this.congr_deriv ?_
    change ((2 : ℕ) : ℝ) * t ^ (2 - 1) / 2 = t
    norm_num

omit [MeasurableSpace X] [Nonempty X] [Fintype J] [Nonempty J] hS [IsProbabilityMeasure ν] hg hk
  hb in
theorem hasDerivAt_jetCoeff' (t : ℝ) : HasDerivAt jetCoeff' (jetCoeff'' t) t := by
  refine hasDerivAt_pi.2 fun i ↦ ?_
  fin_cases i
  · exact hasDerivAt_const t (0 : ℝ)
  · exact hasDerivAt_const t (1 : ℝ)
  · exact hasDerivAt_id t

omit [MeasurableSpace X] [Nonempty X] [Fintype J] [Nonempty J] hS [IsProbabilityMeasure ν] hg hk
  hb in
theorem continuous_jetCoeff' : Continuous jetCoeff' := by
  refine continuous_pi fun i ↦ ?_
  fin_cases i
  · exact continuous_const
  · exact continuous_const
  · exact continuous_id

omit [MeasurableSpace X] [Nonempty X] [Fintype J] [Nonempty J] hS [IsProbabilityMeasure ν] hg hk
  hb in
theorem dirLoss_jetCoeff_zero : dirLoss ![g, k, b] (jetCoeff 0) = g := by
  funext x
  simp [dirLoss, jetCoeff, Fin.sum_univ_three]

omit [MeasurableSpace X] [Nonempty X] [Fintype J] [Nonempty J] hS [IsProbabilityMeasure ν] hg hk
  hb in
theorem dirLoss_jetCoeff'_zero : dirLoss ![g, k, b] (jetCoeff' 0) = k := by
  funext x
  simp [dirLoss, jetCoeff', Fin.sum_univ_three]

omit [MeasurableSpace X] [Nonempty X] [Fintype J] [Nonempty J] hS [IsProbabilityMeasure ν] hg hk
  hb in
theorem dirLoss_jetCoeff''_zero : dirLoss ![g, k, b] (jetCoeff'' 0) = b := by
  funext x
  simp [dirLoss, jetCoeff'', Fin.sum_univ_three]

/-- **The response acceleration of the polynomial journey** `g + t k + t²/2 b` at `t = 0` is
`DΦ_g[b] + H_g(k,k)`. -/
theorem hasDerivAt_jetVel_zero :
    HasDerivAt (fun t ↦ responseVel hS ν (bdd_dirLoss (jetFamily_bdd hg hk hb) (jetCoeff t))
        (bdd_dirLoss (jetFamily_bdd hg hk hb) (jetCoeff' t)))
      (responseVel hS ν hg hb + responseHess hS ν hg hk hk) 0 := by
  have h := hasDerivAt_coeffVel hS ν (jetFamily_bdd hg hk hb) hasDerivAt_jetCoeff
    continuous_jetCoeff' hasDerivAt_jetCoeff' 0
  refine h.congr_deriv ?_
  rw [responseVel_congr hS ν _ _ hg hb (dirLoss_jetCoeff_zero (g := g) (k := k) (b := b))
    (dirLoss_jetCoeff''_zero (g := g) (k := k) (b := b))]
  congr 1
  exact responseHess_congr' hS ν _ hg _ hk _ hk (dirLoss_jetCoeff_zero (g := g) (k := k) (b := b))
    (dirLoss_jetCoeff'_zero (g := g) (k := k) (b := b))
    (dirLoss_jetCoeff'_zero (g := g) (k := k) (b := b))

omit hb in
/-- **Every response acceleration can be prescribed** by the quadratic term of the journey: for any
`v ∈ W` there is a bounded `b` with `DΦ_g[b] + H_g(k,k) = v`. -/
theorem exists_jet_accel (v : 𝕍) :
    ∃ b : X → ℝ, ∃ hb : Bdd b, responseVel hS ν hg hb + responseHess hS ν hg hk hk = v :=
  ⟨_, bdd_horizontalLift hS ν hg (v - responseHess hS ν hg hk hk), by
    rw [responseVel_horizontalLift, sub_add_cancel]⟩

omit hb in
/-- **A journey with invisible initial direction can be made stationary under the response through
second order**: if `DΦ_g[k] = 0`, some `b` gives zero response velocity and zero acceleration. -/
theorem exists_jet_stationary (hk0 : responseVel hS ν hg hk = 0) :
    ∃ b : X → ℝ, ∃ hb : Bdd b, responseVel hS ν hg hk = 0 ∧
      responseVel hS ν hg hb + responseHess hS ν hg hk hk = 0 := by
  obtain ⟨b, hb, hacc⟩ := exists_jet_accel hS ν hg hk 0
  exact ⟨b, hb, hk0, hacc⟩

end Jet

end Laplace.Multi
