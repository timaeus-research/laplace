/-
Copyright (c) 2026 Timaeus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Timaeus
-/
import Laplace.Multi.PolytopeProjectionSupport
import Laplace.Multi.PathEnergy

/-!
# Vertex gaps extinguish the off-face mass

Let `F = conv{v ∈ V : ⟨u,v⟩ = β}` be an exposed face of the charged polytope `P = conv V` and
`A = {⟨u,S⟩ = β}` its fibre.  For a natural parameter `η` write `c = min_{w ∈ V∩F} ⟨η,w⟩` and let
`γ` be a lower bound on the **vertex gaps** `⟨η,v⟩ − c`, `v ∈ V∖F`.  The deterministic inequality

  `c − ⟨η,s⟩ ≤ −γ d(s)/D`,  `d(s) = β − ⟨u,s⟩`, `D ≥ max_V d`   (`sub_dotJ_le_of_vertexGaps`)

holds for every `s ∈ P` (no convex representation has to be chosen measurably), so the family law
`P_η = e^{−⟨η,S⟩}ν/Z` gives the off-face fibre mass at most `(1/m) ∫_{Aᶜ} e^{−γ d(S)/D} dν`, `m` a
lower bound on the vertex fibre masses (`offFaceRatio_le`).  When the gaps of a sequence `η_n`
diverge, dominated convergence extinguishes the off-face mass (`tendsto_offFaceRatio`), and since
`|E_{P_η} S − E_{P_η(·|A)} S| ≤ 2‖S‖ P_η(Aᶜ)` (`abs_mean_sub_faceMean_le`), the mean of the family
law converges to `M` as soon as the mean of the face-conditional family does
(`tendsto_meanMap_of_faceMean_of_vertexGaps`): the reverse half of the vertex-gap criterion,
valid for every target `M` on the face.
-/

open MeasureTheory Filter Topology Set

namespace Laplace.Multi

section Geometry

variable {J : Type*} [Fintype J] (V : Finset (J → ℝ)) (u : J → ℝ) (β : ℝ)

/-- **The deterministic gap inequality**: `c − ⟨η,s⟩ ≤ −γ d(s)/D` on the polytope. -/
theorem sub_dotJ_le_of_vertexGaps (hV : ∀ v ∈ V, dotJ u v ≤ β) (η : J → ℝ) {c γ D : ℝ}
    (hc : ∀ w ∈ V, dotJ u w = β → c ≤ dotJ η w)
    (hγ : ∀ v ∈ V, dotJ u v < β → γ ≤ dotJ η v - c) (hγ0 : 0 ≤ γ)
    (hD : ∀ v ∈ V, β - dotJ u v ≤ D) (hD0 : 0 < D) {s : J → ℝ}
    (hs : s ∈ convexHull ℝ (V : Set (J → ℝ))) :
    c - dotJ η s ≤ -(γ * ((β - dotJ u s) / D)) := by
  classical
  obtain ⟨w, hw0, hw1, rfl⟩ := Finset.mem_convexHull'.1 hs
  rw [dotJ_finset_sum_smul, dotJ_finset_sum_smul]
  have hc' : c = ∑ y ∈ V, w y * c := by rw [← Finset.sum_mul, hw1, one_mul]
  have hβ' : β = ∑ y ∈ V, w y * β := by rw [← Finset.sum_mul, hw1, one_mul]
  -- the off-face weight `λ_off = Σ_{d(v) > 0} w v`
  have hoff : ∀ y ∈ V, w y * c - w y * dotJ η y ≤ w y * (if dotJ u y < β then -γ else 0) := by
    intro y hy
    split_ifs with hlt
    · have := hγ y hy hlt
      nlinarith [hw0 y hy]
    · have heq : dotJ u y = β := le_antisymm (hV y hy) (not_lt.1 hlt)
      have := hc y hy heq
      nlinarith [hw0 y hy]
  have hslack : ∀ y ∈ V, w y * β - w y * dotJ u y ≤ w y * (if dotJ u y < β then D else 0) := by
    intro y hy
    split_ifs with hlt
    · have := hD y hy
      nlinarith [hw0 y hy]
    · have heq : dotJ u y = β := le_antisymm (hV y hy) (not_lt.1 hlt)
      rw [heq]
      simp
  have h1 : c - ∑ y ∈ V, w y * dotJ η y ≤ -(γ * ∑ y ∈ V, if dotJ u y < β then w y else 0) := by
    have e : c - ∑ y ∈ V, w y * dotJ η y = ∑ y ∈ V, (w y * c - w y * dotJ η y) := by
      rw [Finset.sum_sub_distrib, ← hc']
    rw [e]
    calc ∑ y ∈ V, (w y * c - w y * dotJ η y)
        ≤ ∑ y ∈ V, w y * (if dotJ u y < β then -γ else 0) := Finset.sum_le_sum hoff
      _ = -(γ * ∑ y ∈ V, if dotJ u y < β then w y else 0) := by
          rw [Finset.mul_sum, ← Finset.sum_neg_distrib]
          refine Finset.sum_congr rfl fun y _ ↦ ?_
          split_ifs <;> ring
  have h2 : β - ∑ y ∈ V, w y * dotJ u y ≤ D * ∑ y ∈ V, if dotJ u y < β then w y else 0 := by
    have e : β - ∑ y ∈ V, w y * dotJ u y = ∑ y ∈ V, (w y * β - w y * dotJ u y) := by
      rw [Finset.sum_sub_distrib, ← hβ']
    rw [e]
    calc ∑ y ∈ V, (w y * β - w y * dotJ u y)
        ≤ ∑ y ∈ V, w y * (if dotJ u y < β then D else 0) := Finset.sum_le_sum hslack
      _ = D * ∑ y ∈ V, if dotJ u y < β then w y else 0 := by
          rw [Finset.mul_sum]
          refine Finset.sum_congr rfl fun y _ ↦ ?_
          split_ifs <;> ring
  have h3 : (β - ∑ y ∈ V, w y * dotJ u y) / D ≤ ∑ y ∈ V, if dotJ u y < β then w y else 0 := by
    rw [div_le_iff₀ hD0, mul_comm]
    exact h2
  calc c - ∑ y ∈ V, w y * dotJ η y ≤ -(γ * ∑ y ∈ V, if dotJ u y < β then w y else 0) := h1
    _ ≤ -(γ * ((β - ∑ y ∈ V, w y * dotJ u y) / D)) := by
        rw [neg_le_neg_iff]
        exact mul_le_mul_of_nonneg_left h3 hγ0

/-- The ratio bound `|(N_A + N_off)/(A + off) − N_A/A| ≤ 2B off/(A + off)`. -/
theorem abs_ratio_sub_ratio_le {NA Noff A off B : ℝ} (hA : 0 < A) (hoff : 0 ≤ off)
    (h1 : |NA| ≤ B * A) (h2 : |Noff| ≤ B * off) :
    |(NA + Noff) / (A + off) - NA / A| ≤ 2 * B * (off / (A + off)) := by
  have hAoff : 0 < A + off := by linarith
  have e : (NA + Noff) / (A + off) - NA / A = (A * Noff - NA * off) / (A * (A + off)) := by
    field_simp
    ring
  rw [e, abs_div, abs_of_pos (mul_pos hA hAoff), div_le_iff₀ (mul_pos hA hAoff)]
  calc |A * Noff - NA * off| ≤ |A * Noff| + |NA * off| := abs_sub _ _
    _ = A * |Noff| + |NA| * off := by
        rw [abs_mul, abs_mul, abs_of_pos hA, abs_of_nonneg hoff]
    _ ≤ A * (B * off) + B * A * off :=
        add_le_add (mul_le_mul_of_nonneg_left h2 hA.le) (mul_le_mul_of_nonneg_right h1 hoff)
    _ = 2 * B * (off / (A + off)) * (A * (A + off)) := by
        field_simp
        ring

end Geometry

section Extinction

variable {X : Type*} [MeasurableSpace X] [Nonempty X] {J : Type*} [Fintype J] [Nonempty J]
  {S : J → X → ℝ} (hS : ∀ j, Bdd (S j)) (ν : Measure X) [IsProbabilityMeasure ν]
  (V : Finset (J → ℝ)) (u : J → ℝ) (β : ℝ)
include hS

omit [Nonempty X] [Nonempty J] hS [IsProbabilityMeasure ν] in
/-- The off-face mass at `t = 0` is the integral of the weight off the face. -/
theorem offFaceMass_zero (η : J → ℝ) :
    offFaceMass S ν η u β 0 = ∫ x in {x | dirLoss S u x = β}ᶜ, famWeight S η x ∂ν := by
  unfold offFaceMass
  simp

omit [Nonempty X] [Nonempty J] in
/-- The normaliser is the face mass plus the off-face mass. -/
theorem famZ_eq_faceMass_add (η : J → ℝ) :
    famZ S ν η = faceMass S ν η u β + offFaceMass S ν η u β 0 := by
  have := famZ_ray hS ν η u β 0
  rwa [zero_smul, sub_zero, zero_mul, Real.exp_zero, one_mul] at this

omit [Nonempty X] [Nonempty J] in
/-- **The off-face mass is extinguished by the vertex gaps**: with `c = min_{V∩F}⟨η,·⟩` attained
at a tight vertex whose fibre has mass at least `m`, and gap lower bound `γ ≥ 0`,
`P_η(Aᶜ) ≤ (1/m) ∫_{Aᶜ} e^{−γ d(S)/D} dν`. -/
theorem offFaceRatio_le
    (hpoly : momentBody ν (fun _ ↦ (1 : ℝ)) S = convexHull ℝ (V : Set (J → ℝ)))
    (hV : ∀ v ∈ V, dotJ u v ≤ β) (η : J → ℝ) {c γ D m : ℝ} {w : J → ℝ}
    (hwc : dotJ η w = c) (hc : ∀ w ∈ V, dotJ u w = β → c ≤ dotJ η w)
    (hγ : ∀ v ∈ V, dotJ u v < β → γ ≤ dotJ η v - c) (hγ0 : 0 ≤ γ)
    (hD : ∀ v ∈ V, β - dotJ u v ≤ D) (hD0 : 0 < D) (hm0 : 0 < m)
    (hm : m ≤ ν.real (statFibre S w)) :
    offFaceMass S ν η u β 0 / famZ S ν η ≤
      (1 / m) * ∫ x in {x | dirLoss S u x = β}ᶜ,
        Real.exp (-(γ * ((β - dirLoss S u x) / D))) ∂ν := by
  have hF := measurableSet_faceFibre hS u β
  have hmw : Measurable (famWeight S η) := Real.measurable_exp.comp (bdd_dirLoss hS η).1.neg
  have hmg : Measurable fun x ↦ β - dirLoss S u x := (bdd_dirLoss hS u).1.const_sub β
  -- the denominator: `Z ≥ e^{−c} ν(S = w)`
  have hZ : Real.exp (-c) * m ≤ famZ S ν η := by
    calc Real.exp (-c) * m ≤ Real.exp (-c) * ν.real (statFibre S w) :=
          mul_le_mul_of_nonneg_left hm (Real.exp_pos _).le
      _ = ∫ x in statFibre S w, famWeight S η x ∂ν := by
          rw [setIntegral_congr_fun (measurableSet_statFibre hS w)
            (fun x hx ↦ famWeight_eq_of_mem_statFibre η hx), setIntegral_const, smul_eq_mul,
            mul_comm, hwc]
      _ ≤ famZ S ν η :=
          setIntegral_le_integral (integrable_famWeight hS ν η)
            (Eventually.of_forall fun x ↦ (famWeight_pos η x).le)
  -- the numerator: `∫_{Aᶜ} e^{−⟨η,S⟩} ≤ e^{−c} ∫_{Aᶜ} e^{−γ d(S)/D}`
  obtain ⟨-, K, hK⟩ := bdd_dirLoss hS u
  have hmeas : Measurable fun x ↦ Real.exp (-(γ * ((β - dirLoss S u x) / D))) :=
    ((hmg.div_const D).const_mul γ).neg.exp
  have hint : Integrable (fun x ↦ Real.exp (-(γ * ((β - dirLoss S u x) / D)))) ν := by
    refine (integrable_const (Real.exp (γ * ((|β| + K) / D)))).mono' hmeas.aestronglyMeasurable
      (Eventually.of_forall fun x ↦ ?_)
    rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
    refine Real.exp_le_exp.2 ?_
    have h1 : -(β - dirLoss S u x) ≤ |β| + K := by
      have := hK x
      have := neg_abs_le β
      have := abs_le.1 (hK x)
      linarith
    have h2 : -(γ * ((β - dirLoss S u x) / D)) = γ * (-(β - dirLoss S u x) / D) := by ring
    rw [h2]
    exact mul_le_mul_of_nonneg_left (div_le_div_of_nonneg_right h1 hD0.le) hγ0
  have hI0 : 0 ≤ ∫ x in {x | dirLoss S u x = β}ᶜ,
      Real.exp (-(γ * ((β - dirLoss S u x) / D))) ∂ν :=
    integral_nonneg fun x ↦ (Real.exp_pos _).le
  have hnum : offFaceMass S ν η u β 0 ≤ Real.exp (-c) *
      ∫ x in {x | dirLoss S u x = β}ᶜ, Real.exp (-(γ * ((β - dirLoss S u x) / D))) ∂ν := by
    rw [offFaceMass_zero, ← integral_const_mul]
    refine integral_mono_ae (integrable_famWeight hS ν η).integrableOn
      (hint.const_mul _).integrableOn ?_
    filter_upwards [ae_restrict_of_ae
      (ae_statPoint_mem_essRange (μ := ν) measurable_const (fun _ ↦ one_pos) hS)] with x hx
    have hmem : statPoint S x ∈ convexHull ℝ (V : Set (J → ℝ)) := by
      rw [← hpoly]
      exact essRange_subset_momentBody S hx
    have key := sub_dotJ_le_of_vertexGaps V u β hV η hc hγ hγ0 hD hD0 hmem
    rw [famWeight, ← Real.exp_add]
    refine Real.exp_le_exp.2 ?_
    rw [dirLoss_eq_dotJ_statPoint, dirLoss_eq_dotJ_statPoint]
    linarith
  calc offFaceMass S ν η u β 0 / famZ S ν η
      ≤ (Real.exp (-c) * ∫ x in {x | dirLoss S u x = β}ᶜ,
          Real.exp (-(γ * ((β - dirLoss S u x) / D))) ∂ν) / (Real.exp (-c) * m) :=
        div_le_div₀ (mul_nonneg (Real.exp_pos _).le hI0) hnum (mul_pos (Real.exp_pos _) hm0) hZ
    _ = _ := by
        rw [mul_div_mul_left _ _ (Real.exp_pos _).ne', one_div, inv_mul_eq_div]

omit [Nonempty X] [Nonempty J] in
/-- **Dominated convergence**: divergent gaps kill the off-face exponential integral. -/
theorem tendsto_integral_exp_gap (hβ : ∀ᵐ x ∂ν, dirLoss S u x ≤ β) {D : ℝ} (hD0 : 0 < D)
    {γ : ℕ → ℝ} (hγ : Tendsto γ atTop atTop) :
    Tendsto (fun n ↦ ∫ x in {x | dirLoss S u x = β}ᶜ,
      Real.exp (-(γ n * ((β - dirLoss S u x) / D))) ∂ν) atTop (𝓝 0) := by
  have hF := measurableSet_faceFibre hS u β
  have hmg : Measurable fun x ↦ β - dirLoss S u x := (bdd_dirLoss hS u).1.const_sub β
  have h := tendsto_integral_filter_of_dominated_convergence
    (μ := ν.restrict {x | dirLoss S u x = β}ᶜ) (l := (atTop : Filter ℕ))
    (F := fun n x ↦ Real.exp (-(γ n * ((β - dirLoss S u x) / D))))
    (f := fun _ ↦ (0 : ℝ)) (fun _ ↦ (1 : ℝ))
    (Eventually.of_forall fun n ↦
      (((hmg.div_const D).const_mul (γ n)).neg.exp).aestronglyMeasurable) ?_
    (integrable_const _) ?_
  · simpa using h
  · filter_upwards [hγ.eventually_ge_atTop 0] with n hn
    filter_upwards [ae_restrict_of_ae hβ] with x hx
    rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
    refine Real.exp_le_one_iff.2 (neg_nonpos.2 ?_)
    exact mul_nonneg hn (div_nonneg (sub_nonneg.2 hx) hD0.le)
  · rw [ae_restrict_iff' hF.compl]
    filter_upwards [hβ] with x hx hxF
    have hne : dirLoss S u x ≠ β := hxF
    have hg : 0 < β - dirLoss S u x := lt_of_le_of_ne (sub_nonneg.2 hx) fun h ↦ hne (by linarith)
    have hmul : Tendsto (fun n ↦ γ n * ((β - dirLoss S u x) / D)) atTop atTop :=
      Tendsto.atTop_mul_const (div_pos hg hD0) hγ
    exact Real.tendsto_exp_neg_atTop_nhds_zero.comp hmul

omit [Nonempty X] [Nonempty J] in
/-- **The mean under the family law is close to the face-conditional mean**:
`|E_{P_η} f − E_{P_η(·|A)} f| ≤ 2‖f‖_∞ P_η(Aᶜ)`. -/
theorem abs_integral_family_sub_faceFamily_le (hp : 0 < ν.real {x | dirLoss S u x = β})
    (η : J → ℝ) {f : X → ℝ} (hf : Bdd f) {B : ℝ} (hB : ∀ x, |f x| ≤ B) :
    |(∫ x, f x ∂familyMeasure ν (fun _ ↦ (1 : ℝ)) (fun _ ↦ (0 : ℝ)) S 1 η) -
        ∫ x, f x ∂familyMeasure (faceMeasure ν {x | dirLoss S u x = β}) (fun _ ↦ (1 : ℝ))
          (fun _ ↦ (0 : ℝ)) S 1 η| ≤
      2 * B * (offFaceMass S ν η u β 0 / famZ S ν η) := by
  have hF := measurableSet_faceFibre hS u β
  have hA := faceMass_pos hS ν η u β hp
  have hoff := offFaceMass_nonneg hS ν η u β 0
  have hint : Integrable (fun x ↦ famWeight S η x * f x) ν :=
    ((integrable_famWeight hS ν η).bdd_mul hf.1.aestronglyMeasurable
      (Eventually.of_forall fun x ↦ by rw [Real.norm_eq_abs]; exact hB x)).congr
      (Eventually.of_forall fun x ↦ mul_comm _ _)
  have e1 : ∫ x, f x ∂familyMeasure ν (fun _ ↦ (1 : ℝ)) (fun _ ↦ (0 : ℝ)) S 1 η =
      (∫ x, famWeight S η x * f x ∂ν) / famZ S ν η := by
    rw [integral_famDens_mul hS ν η f, ← integral_div]
    exact integral_congr_ae (Eventually.of_forall fun x ↦ by
      simp only [famDens]
      ring)
  have e2 : ∫ x, f x ∂familyMeasure (faceMeasure ν {x | dirLoss S u x = β}) (fun _ ↦ (1 : ℝ))
      (fun _ ↦ (0 : ℝ)) S 1 η =
      (∫ x in {x | dirLoss S u x = β}, famWeight S η x * f x ∂ν) / faceMass S ν η u β := by
    rw [familyMeasure_faceMeasure_eq hS ν η u β hp,
      integral_withDensity_ofReal ν (measurable_faceDens hS ν η u β) (faceDens_nonneg ν η u β) f,
      ← integral_div, ← integral_indicator hF]
    refine integral_congr_ae (Eventually.of_forall fun x ↦ ?_)
    beta_reduce
    rw [faceDens, ← Set.indicator_mul_left]
    refine congrArg (fun g ↦ Set.indicator {x | dirLoss S u x = β} g x) ?_
    funext y
    ring
  have hsplit : ∫ x, famWeight S η x * f x ∂ν =
      (∫ x in {x | dirLoss S u x = β}, famWeight S η x * f x ∂ν) +
        ∫ x in {x | dirLoss S u x = β}ᶜ, famWeight S η x * f x ∂ν :=
    (integral_add_compl₀ hF.nullMeasurableSet hint).symm
  have hbound : ∀ T : Set X, |∫ x in T, famWeight S η x * f x ∂ν| ≤
      B * ∫ x in T, famWeight S η x ∂ν := fun T ↦ by
    refine abs_integral_le_integral_abs.trans ?_
    rw [← integral_const_mul]
    refine integral_mono hint.abs.integrableOn
      ((integrable_famWeight hS ν η).const_mul B).integrableOn fun x ↦ ?_
    rw [abs_mul, abs_of_pos (famWeight_pos η x), mul_comm]
    exact mul_le_mul_of_nonneg_right (hB x) (famWeight_pos η x).le
  rw [e1, e2, hsplit, famZ_eq_faceMass_add hS ν u β η]
  refine abs_ratio_sub_ratio_le hA hoff ?_ ?_
  · exact hbound _
  · rw [offFaceMass_zero]
    exact hbound _

omit [Nonempty J] in
/-- **The reverse vertex-gap criterion**: if the face-conditional means converge to `M` and every
off-face vertex gap `⟨η_n, v − v₀⟩` diverges, the means of the family laws converge to `M`. -/
theorem tendsto_meanMap_of_faceMean_of_vertexGaps
    (hpoly : momentBody ν (fun _ ↦ (1 : ℝ)) S = convexHull ℝ (V : Set (J → ℝ)))
    (hcharged : ∀ v ∈ V, 0 < ν.real (statFibre S v)) (hV : ∀ v ∈ V, dotJ u v ≤ β)
    {v₀ : J → ℝ} (hv₀V : v₀ ∈ V) (hv₀β : dotJ u v₀ = β) {η : ℕ → J → ℝ} {M : J → ℝ}
    (hface : Tendsto (fun n ↦ meanMap (faceMeasure ν {x | dirLoss S u x = β}) (fun _ ↦ (1 : ℝ))
      (fun _ ↦ (0 : ℝ)) S 1 (η n)) atTop (𝓝 M))
    (hgap : ∀ v ∈ V, dotJ u v < β → Tendsto (fun n ↦ dotJ (η n) (v - v₀)) atTop atTop) :
    Tendsto (fun n ↦ meanMap ν (fun _ ↦ (1 : ℝ)) (fun _ ↦ (0 : ℝ)) S 1 (η n)) atTop (𝓝 M) := by
  classical
  have hp : 0 < ν.real {x | dirLoss S u x = β} :=
    faceFibre_pos_of_charged ν V hcharged hv₀V hv₀β
  have hβ := ae_dirLoss_le_of_polytope hS ν V u β hpoly hV
  have hF0 : ν {x | dirLoss S u x = β} ≠ 0 := (ENNReal.toReal_pos_iff.1 hp).1.ne'
  have hPF := isProbabilityMeasure_faceMeasure ν hF0
  have hVne : V.Nonempty := ⟨v₀, hv₀V⟩
  -- the slack bound `D` and the fibre mass bound `m`
  obtain ⟨D, hDdef⟩ : ∃ D : ℝ, D = V.sup' hVne (fun v ↦ β - dotJ u v) + 1 := ⟨_, rfl⟩
  have hD : ∀ v ∈ V, β - dotJ u v ≤ D := fun v hv ↦ by
    rw [hDdef]
    linarith [Finset.le_sup' (fun v ↦ β - dotJ u v) hv]
  have hD0 : 0 < D := by
    have h := Finset.le_sup' (fun v ↦ β - dotJ u v) hv₀V
    simp only [hv₀β, sub_self] at h
    rw [hDdef]
    linarith
  obtain ⟨m, hmdef⟩ : ∃ m : ℝ, m = V.inf' hVne fun v ↦ ν.real (statFibre S v) := ⟨_, rfl⟩
  have hm0 : 0 < m := by
    rw [hmdef, Finset.lt_inf'_iff hVne]
    exact hcharged
  have hm : ∀ v ∈ V, m ≤ ν.real (statFibre S v) := fun v hv ↦ by
    rw [hmdef]
    exact Finset.inf'_le _ hv
  -- the minimal tight vertex and the gap sequence
  have hFne : (V.filter fun v ↦ dotJ u v = β).Nonempty := ⟨v₀, Finset.mem_filter.2 ⟨hv₀V, hv₀β⟩⟩
  obtain ⟨c, hcdef⟩ : ∃ c : ℕ → ℝ, c = fun n ↦ (V.filter fun v ↦ dotJ u v = β).inf' hFne
    (dotJ (η n)) := ⟨_, rfl⟩
  have hcle : ∀ n, ∀ w ∈ V, dotJ u w = β → c n ≤ dotJ (η n) w := fun n w hw hwβ ↦ by
    rw [hcdef]
    exact Finset.inf'_le _ (Finset.mem_filter.2 ⟨hw, hwβ⟩)
  have hwex : ∀ n, ∃ w ∈ V.filter (fun v ↦ dotJ u v = β), c n = dotJ (η n) w := fun n ↦ by
    rw [hcdef]
    exact Finset.exists_mem_eq_inf' hFne _
  choose w hwmem hwc using hwex
  obtain ⟨γ, hγdef⟩ : ∃ γ : ℕ → ℝ, γ = fun n ↦
    if hoff : (V.filter fun v ↦ dotJ u v < β).Nonempty then
      (V.filter fun v ↦ dotJ u v < β).inf' hoff (fun v ↦ dotJ (η n) (v - v₀)) else (n : ℝ) :=
    ⟨_, rfl⟩
  have hγ : ∀ n, ∀ v ∈ V, dotJ u v < β → γ n ≤ dotJ (η n) v - c n := fun n v hv hvβ ↦ by
    have hoff : (V.filter fun v ↦ dotJ u v < β).Nonempty := ⟨v, Finset.mem_filter.2 ⟨hv, hvβ⟩⟩
    rw [hγdef]
    simp only [dif_pos hoff]
    calc (V.filter fun v ↦ dotJ u v < β).inf' hoff (fun v ↦ dotJ (η n) (v - v₀))
        ≤ dotJ (η n) (v - v₀) := Finset.inf'_le _ (Finset.mem_filter.2 ⟨hv, hvβ⟩)
      _ = dotJ (η n) v - dotJ (η n) v₀ := (isLinearMap_dotJ (η n)).map_sub _ _
      _ ≤ dotJ (η n) v - c n := by linarith [hcle n v₀ hv₀V hv₀β]
  have hγlim : Tendsto γ atTop atTop := by
    rw [hγdef]
    by_cases hoff : (V.filter fun v ↦ dotJ u v < β).Nonempty
    · simp only [dif_pos hoff]
      refine tendsto_atTop.2 fun A ↦ ?_
      have hall := (eventually_all_finset (V.filter fun v ↦ dotJ u v < β)).2 fun v hv ↦
        (hgap v (Finset.mem_filter.1 hv).1 (Finset.mem_filter.1 hv).2).eventually_ge_atTop A
      filter_upwards [hall] with n hn
      exact Finset.le_inf' hoff _ hn
    · simp only [dif_neg hoff]
      exact tendsto_natCast_atTop_atTop
  -- the extinction of the off-face mass
  have hI := tendsto_integral_exp_gap hS ν u β hβ hD0 hγlim
  have hratio : ∀ᶠ n in atTop, offFaceMass S ν (η n) u β 0 / famZ S ν (η n) ≤
      (1 / m) * ∫ x in {x | dirLoss S u x = β}ᶜ,
        Real.exp (-(γ n * ((β - dirLoss S u x) / D))) ∂ν := by
    filter_upwards [hγlim.eventually_ge_atTop 0] with n hn
    exact offFaceRatio_le hS ν V u β hpoly hV (η n) (hwc n).symm (hcle n) (hγ n) hn hD hD0 hm0
      (hm _ (Finset.mem_filter.1 (hwmem n)).1)
  have hratio0 : Tendsto (fun n ↦ offFaceMass S ν (η n) u β 0 / famZ S ν (η n)) atTop (𝓝 0) := by
    refine squeeze_zero' (Eventually.of_forall fun n ↦
      div_nonneg (offFaceMass_nonneg hS ν _ u β 0) (famZ_pos hS ν _).le) hratio ?_
    simpa using hI.const_mul (1 / m)
  -- coordinatewise comparison of the two means
  have hdiff : Tendsto (fun n ↦ meanMap ν (fun _ ↦ (1 : ℝ)) (fun _ ↦ (0 : ℝ)) S 1 (η n) -
      meanMap (faceMeasure ν {x | dirLoss S u x = β}) (fun _ ↦ (1 : ℝ)) (fun _ ↦ (0 : ℝ)) S 1
        (η n)) atTop (𝓝 0) := by
    refine tendsto_pi_nhds.2 fun j ↦ ?_
    obtain ⟨-, B, hB⟩ := hS j
    have hB0 : 0 ≤ B := by
      obtain ⟨x⟩ := ‹Nonempty X›
      exact (abs_nonneg _).trans (hB x)
    have hcoord : ∀ n, (meanMap ν (fun _ ↦ (1 : ℝ)) (fun _ ↦ (0 : ℝ)) S 1 (η n) -
        meanMap (faceMeasure ν {x | dirLoss S u x = β}) (fun _ ↦ (1 : ℝ)) (fun _ ↦ (0 : ℝ)) S 1
          (η n)) j =
        (∫ x, S j x ∂familyMeasure ν (fun _ ↦ (1 : ℝ)) (fun _ ↦ (0 : ℝ)) S 1 (η n)) -
          ∫ x, S j x ∂familyMeasure (faceMeasure ν {x | dirLoss S u x = β}) (fun _ ↦ (1 : ℝ))
            (fun _ ↦ (0 : ℝ)) S 1 (η n) := fun n ↦ by
      rw [Pi.sub_apply, ← mean_familyMeasure_one_zero hS ν (η n),
        ← mean_familyMeasure_one_zero hS (faceMeasure ν {x | dirLoss S u x = β}) (η n)]
    simp only [Pi.zero_apply]
    rw [tendsto_iff_norm_sub_tendsto_zero]
    refine squeeze_zero' (Eventually.of_forall fun n ↦ norm_nonneg _)
      (Eventually.of_forall fun n ↦ ?_) (by simpa using hratio0.const_mul (2 * B))
    rw [sub_zero, Real.norm_eq_abs, hcoord n]
    exact abs_integral_family_sub_faceFamily_le hS ν u β hp (η n) (hS j) hB
  have := hface.add hdiff
  rw [add_zero] at this
  refine this.congr fun n ↦ ?_
  simp

end Extinction

end Laplace.Multi
