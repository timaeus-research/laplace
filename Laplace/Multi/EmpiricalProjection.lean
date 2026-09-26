/-
Copyright (c) 2026 Timaeus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Timaeus
-/
import Mathlib
import Laplace.Multi.LegendreClosure
import Laplace.Multi.EndpointTail

/-!
# The atlas under sampling: empirical response projections are consistent

For a finite-rate response `M` and an interior response `M'`,

  `KL(Π(M) ‖ Π(M')) = 𝓘(M) − 𝓘(M') + ⟨θ(M'), M − M'⟩`   (`toReal_klDiv_responseProjection_interior`)

(the exact endpoint identity of `EndpointTail` with a general interior target). For i.i.d.
samples `X₁, X₂, …` from a data law `D ≪ ν` whose response `M_D = E_D S` lies in the relative
interior of the moment body, the empirical responses `M̂_n = (1/n) ∑ S(Xᵢ)` converge almost
surely to `M_D` (`ae_tendsto_empMean`, the strong law coordinatewise), lie in the moment body
(`ae_empMean_mem_momentBody`), are eventually in the relative interior
(`eventually_mem_intrinsicInterior_of_tendsto`), and the projected representatives converge in
information:

  `KL(Π(M̂_n) ‖ Π(M_D)) → 0` almost surely   (`ae_tendsto_klDiv_responseProjection_empMean`)

by continuity of the rate on the relative interior along the visible directions. This is the
operational content of the atlas: the response coordinates of a finite sample determine a law that
converges to the population representative in information, hence in total variation.
-/

open MeasureTheory Filter Topology Set InformationTheory ProbabilityTheory
open scoped ENNReal

namespace Laplace.Multi

section Interior

variable {X : Type*} [MeasurableSpace X] [Nonempty X] {J : Type*} [Fintype J] [Nonempty J]
  {S : J → X → ℝ} (hS : ∀ j, Bdd (S j)) (ν : Measure X) [IsProbabilityMeasure ν]
include hS

/-- Interior responses have finite rate. -/
theorem genRate_ne_top_of_mem_intrinsicInterior {M : J → ℝ}
    (hrel : M ∈ intrinsicInterior ℝ (momentBody ν (fun _ ↦ (1 : ℝ)) S)) : genRate ν S M ≠ ⊤ := by
  have hm := meanMap_responseTheta measurable_const (integrable_const 1) (fun _ ↦ one_pos)
    (one_integral_pos ν) hS hrel
  have h := genRate_meanMap_neg hS ν (-(responseTheta measurable_const (integrable_const 1)
    (fun _ ↦ one_pos) (one_integral_pos ν) hS M : J → ℝ))
  rw [neg_neg, hm] at h
  rw [h]
  exact ENNReal.ofReal_ne_top

/-- **The interior divergence identity**: for a finite-rate `M` and an interior `M'`,
`KL(Π(M) ‖ Π(M')) = 𝓘(M) − 𝓘(M') + ⟨θ(M'), M − M'⟩`. -/
theorem toReal_klDiv_responseProjection_interior {M M' : J → ℝ} (hfin : genRate ν S M ≠ ⊤)
    (hrel' : M' ∈ intrinsicInterior ℝ (momentBody ν (fun _ ↦ (1 : ℝ)) S)) :
    (klDiv (responseProjection hS ν M) (responseProjection hS ν M')).toReal =
      (genRate ν S M).toReal - (genRate ν S M').toReal +
        dotJ (responseTheta measurable_const (integrable_const 1) (fun _ ↦ one_pos)
          (one_integral_pos ν) hS M' : J → ℝ) (M - M') := by
  obtain ⟨hQP, hQM, hQkl, -⟩ := responseProjection_spec hS ν hfin
  obtain ⟨Q, hQ⟩ : ∃ Q, Q = responseProjection hS ν M := ⟨_, rfl⟩
  rw [← hQ] at hQM hQkl ⊢
  have hQP' : IsProbabilityMeasure Q := by
    rw [hQ]
    exact hQP
  have hQkl' : klDiv Q ν ≠ ⊤ := by
    rw [hQkl]
    exact hfin
  have hQν : Q ≪ ν := (klDiv_ne_top_iff.1 hQkl').1
  obtain ⟨θ', hθ'⟩ : ∃ θ' : J → ℝ, θ' = (responseTheta measurable_const (integrable_const 1)
    (fun _ ↦ one_pos) (one_integral_pos ν) hS M' : J → ℝ) := ⟨_, rfl⟩
  rw [responseProjection_eq_familyMeasure_responseTheta hS ν hrel', ← hθ',
    familyMeasure_one_zero_eq_tilted hS ν]
  have hbdd : Bdd (fun x ↦ -1 * dirLoss S θ' x) := Bdd.const_mul (-1) (bdd_dirLoss hS _)
  rw [klDiv_tilted_right_eq ν Q hQν hQkl' hbdd, hQkl]
  have hmean : ∫ x, -1 * dirLoss S θ' x ∂Q = -dotJ θ' M := by
    rw [MeasureTheory.integral_const_mul, ← dotJ_integral_eq Q hS _, hQM]
    ring
  have hlog : Real.log (∫ x, Real.exp (-1 * dirLoss S θ' x) ∂ν) = featCgf ν S (-θ') := by
    unfold featCgf
    congr 1
    refine integral_congr_ae (Eventually.of_forall fun x ↦ ?_)
    beta_reduce
    rw [dirLoss_neg (S := S)]
    ring_nf
  have hm' := meanMap_responseTheta measurable_const (integrable_const 1) (fun _ ↦ one_pos)
    (one_integral_pos ν) hS hrel'
  rw [← hθ'] at hm'
  have hrate : (genRate ν S M').toReal = -dotJ θ' M' - featCgf ν S (-θ') := by
    obtain ⟨-, h⟩ := featCgf_eq_dotJ_sub_genRate_meanMap hS ν (-θ')
    rw [neg_neg, hm', dotJ_neg_left] at h
    linarith
  have hnn : 0 ≤ (genRate ν S M).toReal - -dotJ θ' M + featCgf ν S (-θ') := by
    have hF := dotJ_sub_genRate_le_featCgf ν hfin (-θ')
    rw [dotJ_neg_left] at hF
    linarith
  rw [hmean, hlog, ENNReal.toReal_ofReal hnn, hrate, (isLinearMap_dotJ θ').map_sub M M']
  ring

end Interior

section Openness

variable {J : Type*}

/-- A sequence in a set converging to a point of its relative interior is eventually in the
relative interior. -/
theorem eventually_mem_intrinsicInterior_of_tendsto {K : Set (J → ℝ)} {M : ℕ → J → ℝ} {L : J → ℝ}
    (hM : ∀ n, M n ∈ K) (hL : L ∈ intrinsicInterior ℝ K) (hlim : Tendsto M atTop (𝓝 L)) :
    ∀ᶠ n in atTop, M n ∈ intrinsicInterior ℝ K := by
  obtain ⟨y, hy, hyL⟩ := mem_intrinsicInterior.1 hL
  have hsub : ∀ n, M n ∈ affineSpan ℝ K := fun n ↦ subset_affineSpan ℝ K (hM n)
  have hlim' : Tendsto (fun n ↦ (⟨M n, hsub n⟩ : affineSpan ℝ K)) atTop (𝓝 y) := by
    rw [tendsto_subtype_rng]
    simpa [hyL] using hlim
  filter_upwards [hlim'.eventually (isOpen_interior.mem_nhds hy)] with n hn
  exact mem_intrinsicInterior.2 ⟨⟨M n, hsub n⟩, hn, rfl⟩

end Openness

section Sampling

variable {X : Type*} {J : Type*} {Ω : Type*}

/-- The empirical response of the first `n` samples. -/
noncomputable def sampleResponse (S : J → X → ℝ) (Xs : ℕ → Ω → X) (n : ℕ) (ω : Ω) : J → ℝ :=
  fun j ↦ (∑ i ∈ Finset.range n, S j (Xs i ω)) / n

variable [MeasurableSpace X] [Fintype J] {S : J → X → ℝ} (hS : ∀ j, Bdd (S j)) (ν : Measure X)
  [MeasurableSpace Ω] (P : Measure Ω) (D : Measure X) (hDν : D ≪ ν) (Xs : ℕ → Ω → X)
  (hXm : ∀ i, Measurable (Xs i)) (hind : Pairwise fun i k ↦ IndepFun (Xs i) (Xs k) P)
  (hid : ∀ i, IdentDistrib (Xs i) (Xs 0) P P) (hlaw : P.map (Xs 0) = D)

include hS hXm hind hid hlaw in
set_option linter.unusedFintypeInType false in
/-- **The strong law for the empirical response**: `M̂_n → M_D` almost surely. -/
theorem ae_tendsto_sampleResponse [IsProbabilityMeasure P] :
    ∀ᵐ ω ∂P, Tendsto (fun n ↦ sampleResponse S Xs n ω) atTop (𝓝 fun j ↦ ∫ x, S j x ∂D) := by
  have hcoord : ∀ j, ∀ᵐ ω ∂P,
      Tendsto (fun n ↦ (∑ i ∈ Finset.range n, S j (Xs i ω)) / n) atTop (𝓝 (∫ x, S j x ∂D)) := by
    intro j
    obtain ⟨hjm, L, hL⟩ := hS j
    have hint : Integrable (fun ω ↦ S j (Xs 0 ω)) P :=
      Integrable.of_bound (hjm.comp (hXm 0)).aestronglyMeasurable L
        (Eventually.of_forall fun ω ↦ by rw [Real.norm_eq_abs]; exact hL _)
    have hindep : Pairwise fun i k ↦ IndepFun (fun ω ↦ S j (Xs i ω)) (fun ω ↦ S j (Xs k ω)) P :=
      fun i k hik ↦ (hind hik).comp hjm hjm
    have hident : ∀ i, IdentDistrib (fun ω ↦ S j (Xs i ω)) (fun ω ↦ S j (Xs 0 ω)) P P :=
      fun i ↦ (hid i).comp hjm
    have h := strong_law_ae_real (fun i ω ↦ S j (Xs i ω)) hint hindep hident
    have hE : P[fun ω ↦ S j (Xs 0 ω)] = ∫ x, S j x ∂D := by
      rw [← hlaw, integral_map (hXm 0).aemeasurable hjm.aestronglyMeasurable]
    rw [hE] at h
    exact h
  have hall := (ae_all_iff (ι := J)).2 hcoord
  filter_upwards [hall] with ω hω
  rw [tendsto_pi_nhds]
  exact hω

include hS hDν hXm hid hlaw in
set_option linter.unusedFintypeInType false in
/-- **The empirical responses lie in the moment body** almost surely, for every `n ≥ 1`. -/
theorem ae_sampleResponse_mem_momentBody :
    ∀ᵐ ω ∂P, ∀ n, 0 < n → sampleResponse S Xs n ω ∈ momentBody ν (fun _ ↦ (1 : ℝ)) S := by
  have hpt : ∀ i, ∀ᵐ ω ∂P, statPoint S (Xs i ω) ∈ momentBody ν (fun _ ↦ (1 : ℝ)) S := by
    intro i
    have hν : ∀ᵐ x ∂ν, statPoint S x ∈ momentBody ν (fun _ ↦ (1 : ℝ)) S := by
      filter_upwards [ae_statPoint_mem_essRange measurable_const (fun _ ↦ one_pos) hS] with x hx
      exact essRange_subset_momentBody S hx
    have hD' : ∀ᵐ x ∂D, statPoint S x ∈ momentBody ν (fun _ ↦ (1 : ℝ)) S := hDν.ae_le hν
    have hmap : P.map (Xs i) = D := by rw [(hid i).map_eq, hlaw]
    rw [← hmap] at hD'
    exact ae_of_ae_map (hXm i).aemeasurable hD'
  filter_upwards [(ae_all_iff (ι := ℕ)).2 hpt] with ω hω n hn
  have e : sampleResponse S Xs n ω =
      ∑ i ∈ Finset.range n, ((n : ℝ)⁻¹) • statPoint S (Xs i ω) := by
    funext j
    simp only [sampleResponse, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, statPoint,
      div_eq_inv_mul, Finset.mul_sum]
  rw [e]
  refine (convex_momentBody S).sum_mem (fun i _ ↦ inv_nonneg.2 (Nat.cast_nonneg n)) ?_
    fun i _ ↦ hω i
  rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
  have hn' : (n : ℝ) ≠ 0 := by exact_mod_cast hn.ne'
  field_simp

end Sampling

section Consistency

variable {X : Type*} [MeasurableSpace X] [Nonempty X] {J : Type*} [Fintype J] [Nonempty J]
  {S : J → X → ℝ} (hS : ∀ j, Bdd (S j)) (ν : Measure X) [IsProbabilityMeasure ν]
include hS

/-- Divergences from a finite-rate response to an interior response are finite. -/
theorem klDiv_responseProjection_interior_ne_top {M M' : J → ℝ} (hfin : genRate ν S M ≠ ⊤)
    (hrel' : M' ∈ intrinsicInterior ℝ (momentBody ν (fun _ ↦ (1 : ℝ)) S)) :
    klDiv (responseProjection hS ν M) (responseProjection hS ν M') ≠ ⊤ := by
  obtain ⟨hQP, -, hQkl, -⟩ := responseProjection_spec hS ν hfin
  obtain ⟨Q, hQ⟩ : ∃ Q, Q = responseProjection hS ν M := ⟨_, rfl⟩
  rw [← hQ] at hQkl ⊢
  have hQP' : IsProbabilityMeasure Q := by
    rw [hQ]
    exact hQP
  have hQkl' : klDiv Q ν ≠ ⊤ := by
    rw [hQkl]
    exact hfin
  have hQν : Q ≪ ν := (klDiv_ne_top_iff.1 hQkl').1
  rw [responseProjection_eq_familyMeasure_responseTheta hS ν hrel',
    familyMeasure_one_zero_eq_tilted hS ν,
    klDiv_tilted_right_eq ν Q hQν hQkl' (Bdd.const_mul (-1) (bdd_dirLoss hS _))]
  exact ENNReal.ofReal_ne_top

/-- **Consistency of the empirical projection**: for i.i.d. samples from `D ≪ ν` whose response
lies in the relative interior of the moment body, `KL(Π(M̂_n) ‖ Π(M_D)) → 0` almost surely. -/
theorem ae_tendsto_klDiv_responseProjection_sampleResponse {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (D : Measure X) (hDν : D ≪ ν) (Xs : ℕ → Ω → X)
    (hXm : ∀ i, Measurable (Xs i)) (hind : Pairwise fun i k ↦ IndepFun (Xs i) (Xs k) P)
    (hid : ∀ i, IdentDistrib (Xs i) (Xs 0) P P) (hlaw : P.map (Xs 0) = D)
    (hrel : (fun j ↦ ∫ x, S j x ∂D) ∈ intrinsicInterior ℝ (momentBody ν (fun _ ↦ (1 : ℝ)) S)) :
    ∀ᵐ ω ∂P, Tendsto (fun n ↦ klDiv (responseProjection hS ν (sampleResponse S Xs n ω))
      (responseProjection hS ν fun j ↦ ∫ x, S j x ∂D)) atTop (𝓝 0) := by
  obtain ⟨MD, hMD⟩ : ∃ MD : J → ℝ, MD = fun j ↦ ∫ x, S j x ∂D := ⟨_, rfl⟩
  rw [← hMD] at hrel ⊢
  have hlim0 := ae_tendsto_sampleResponse hS P D Xs hXm hind hid hlaw
  rw [← hMD] at hlim0
  filter_upwards [hlim0, ae_sampleResponse_mem_momentBody hS ν P D hDν Xs hXm hid hlaw] with ω hlim
    hmem
  rw [← tendsto_add_atTop_iff_nat 1]
  obtain ⟨m₀, hm₀⟩ : ∃ m₀ : J → ℝ, m₀ = meanMap ν (fun _ ↦ (1 : ℝ)) (fun _ ↦ (0 : ℝ)) S 1 0 :=
    ⟨_, rfl⟩
  obtain ⟨θD, hθD⟩ : ∃ θD : J → ℝ, θD = (responseTheta measurable_const (integrable_const 1)
    (fun _ ↦ one_pos) (one_integral_pos ν) hS MD : J → ℝ) := ⟨_, rfl⟩
  have hlim' : Tendsto (fun n ↦ sampleResponse S Xs (n + 1) ω) atTop (𝓝 MD) :=
    hlim.comp (tendsto_add_atTop_nat 1)
  have hmem' : ∀ n, sampleResponse S Xs (n + 1) ω ∈ momentBody ν (fun _ ↦ (1 : ℝ)) S :=
    fun n ↦ hmem (n + 1) n.succ_pos
  have hev := eventually_mem_intrinsicInterior_of_tendsto hmem' hrel hlim'
  have hθ := hasFDerivAt_genRate_chart hS ν (responseTheta measurable_const (integrable_const 1)
    (fun _ ↦ one_pos) (one_integral_pos ν) hS MD)
  rw [chartV_responseTheta measurable_const (integrable_const 1) (fun _ ↦ one_pos)
    (one_integral_pos ν) hS hrel, ← hm₀] at hθ
  have h1 : ∀ n, (toV ν (fun _ ↦ (1 : ℝ)) S (sampleResponse S Xs (n + 1) ω) : J → ℝ) =
      sampleResponse S Xs (n + 1) ω - m₀ := fun n ↦ by
    rw [hm₀]
    exact toV_apply (sub_mem_dirSpan_of_mem_momentBody measurable_const (integrable_const 1)
      (fun _ ↦ one_pos) (one_integral_pos ν) hS (hmem' n))
  have h2 : (toV ν (fun _ ↦ (1 : ℝ)) S MD : J → ℝ) = MD - m₀ := by
    rw [hm₀]
    exact toV_apply (sub_mem_dirSpan_of_mem_momentBody measurable_const (integrable_const 1)
      (fun _ ↦ one_pos) (one_integral_pos ν) hS (intrinsicInterior_subset hrel))
  have hv : Tendsto (fun n ↦ toV ν (fun _ ↦ (1 : ℝ)) S (sampleResponse S Xs (n + 1) ω)) atTop
      (𝓝 (toV ν (fun _ ↦ (1 : ℝ)) S MD)) := by
    rw [tendsto_subtype_rng, h2]
    simp only [h1]
    exact hlim'.sub tendsto_const_nhds
  have hrate := hθ.continuousAt.tendsto.comp hv
  have e1 : ∀ n, m₀ + (toV ν (fun _ ↦ (1 : ℝ)) S (sampleResponse S Xs (n + 1) ω) : J → ℝ) =
      sampleResponse S Xs (n + 1) ω := fun n ↦ by rw [h1 n, add_sub_cancel]
  have e2 : m₀ + (toV ν (fun _ ↦ (1 : ℝ)) S MD : J → ℝ) = MD := by rw [h2, add_sub_cancel]
  simp only [Function.comp_def, e1, e2] at hrate
  have hdot : Tendsto (fun n ↦ dotJ θD (sampleResponse S Xs (n + 1) ω - MD)) atTop (𝓝 0) := by
    have hc : Continuous fun M : J → ℝ ↦ dotJ θD M := by
      simp only [dotJ]
      fun_prop
    have h := (hc.tendsto (MD - MD)).comp (hlim'.sub (tendsto_const_nhds (x := MD)))
    rw [sub_self] at h
    simpa [Function.comp_def, dotJ] using h
  have hg : Tendsto (fun n ↦ (genRate ν S (sampleResponse S Xs (n + 1) ω)).toReal -
      (genRate ν S MD).toReal + dotJ θD (sampleResponse S Xs (n + 1) ω - MD)) atTop (𝓝 0) := by
    have h := (hrate.sub (tendsto_const_nhds (x := (genRate ν S MD).toReal))).add hdot
    rwa [sub_self, add_zero] at h
  have h0 := ENNReal.tendsto_ofReal hg
  rw [ENNReal.ofReal_zero] at h0
  refine h0.congr' ?_
  filter_upwards [hev] with n hn
  rw [← ENNReal.ofReal_toReal (klDiv_responseProjection_interior_ne_top hS ν
    (genRate_ne_top_of_mem_intrinsicInterior hS ν hn) hrel),
    toReal_klDiv_responseProjection_interior hS ν (genRate_ne_top_of_mem_intrinsicInterior hS ν hn)
    hrel, ← hθD]

end Consistency

end Laplace.Multi
