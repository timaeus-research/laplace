/-
Copyright (c) 2026 Timaeus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Timaeus
-/
import Laplace.Multi.FiniteEntropySupport

/-!
# The completed family is continuous on the moment polytope

On a finite alphabet with a full-support reference law `ν`:

* `entVec ν p = Σ_x p x log (p x / ν{x})` is the relative entropy of a probability vector,
  continuous on the simplex (`continuous_entVec`), and it is the real value of Mathlib's `klDiv`
  (`toReal_klDiv_vecMeasure`, via the Radon–Nikodym derivative of `count.withDensity`);
* the completed family `q*(M)` minimises `entVec` over the fibre of `M` (`entVec_qStarVec_le`)
  and is its unique minimiser (`eq_qStarVec_of_entVec_le`);
* **additive recovery** on the finite simplex: if `a_n → r` and `supp r ⊆ supp p` then
  `b_n = p + a_n − r` is eventually a probability vector, `b_n → p`, and the response is additive
  (`eventually_add_sub_mem_stdSimplex`, `tendsto_add_sub`, `vecMoment_add_sub`);
* **limits of minimisers are minimisers** (`qStarVec_limit_eq`): with `m_n → M` and
  `q*(m_n) → r`, maximal support gives `supp r ⊆ supp q*(M)`, the recovery vectors
  `b_n = q*(M) + q*(m_n) − r` are feasible for `m_n`, optimality `entVec q*(m_n) ≤ entVec b_n`
  passes to the limit, and uniqueness forces `r = q*(M)`;
* **the completed family is continuous on the polytope** (`tendsto_qStarVec`,
  `continuousOn_qStarVec`) by compactness of the simplex, and so is the rate
  (`continuousOn_genRate_toReal`).
-/

open MeasureTheory Filter Topology Set InformationTheory
open scoped ENNReal

namespace Laplace.Multi

section Entropy

variable {X : Type*} [Fintype X] [MeasurableSpace X] [MeasurableSingletonClass X]
  (ν : Measure X) [IsProbabilityMeasure ν]

/-- The relative entropy of a vector against `ν`, `Σ_x p x log (p x / ν{x})`. -/
noncomputable def entVec (p : X → ℝ) : ℝ := ∑ x, p x * Real.log (p x / ν.real {x})

variable (hν : ∀ x, 0 < ν {x})
include hν

omit [Fintype X] [MeasurableSingletonClass X] in
theorem measureReal_singleton_pos (x : X) : 0 < ν.real {x} :=
  ENNReal.toReal_pos (hν x).ne' (measure_ne_top _ _)

omit [MeasurableSingletonClass X] in
theorem entVec_eq (p : X → ℝ) :
    entVec ν p = ∑ x, (p x * Real.log (p x) - p x * Real.log (ν.real {x})) := by
  refine Finset.sum_congr rfl fun x _ ↦ ?_
  by_cases h : p x = 0
  · simp [h]
  · rw [Real.log_div h (measureReal_singleton_pos ν hν x).ne']
    ring

omit [MeasurableSingletonClass X] in
/-- The relative entropy is continuous. -/
theorem continuous_entVec : Continuous (entVec ν) := by
  have e : entVec ν = fun p ↦ ∑ x, (p x * Real.log (p x) - p x * Real.log (ν.real {x})) :=
    funext fun p ↦ entVec_eq ν hν p
  rw [e]
  exact continuous_finsetSum _ fun x _ ↦
    (Real.continuous_mul_log.comp (continuous_apply x)).sub
      ((continuous_apply x).mul continuous_const)

omit [Fintype X] [MeasurableSingletonClass X] [IsProbabilityMeasure ν] in
/-- Almost-everywhere statements are everywhere statements under a full-support law. -/
theorem forall_of_ae_full_support {P : X → Prop} (h : ∀ᵐ x ∂ν, P x) : ∀ x, P x := by
  intro x
  by_contra hx
  rw [ae_iff] at h
  exact (hν x).ne' (le_antisymm ((measure_mono (singleton_subset_iff.2 hx)).trans h.le) zero_le)

omit [Fintype X] [IsProbabilityMeasure ν] hν in
/-- A full-support law is the counting measure with density `ν {·}`. -/
theorem count_withDensity_singleton [Finite X] : Measure.count.withDensity (fun x ↦ ν {x}) = ν := by
  rw [count_withDensity, Measure.sum_smul_dirac]

omit [Fintype X] in
/-- The vector measure as a density against `ν`. -/
theorem vecMeasure_eq_withDensity [Finite X] (p : X → ℝ) :
    vecMeasure p = ν.withDensity fun x ↦ ENNReal.ofReal (p x) / ν {x} := by
  calc vecMeasure p = Measure.count.withDensity
        ((fun x ↦ ν {x}) * fun x ↦ ENNReal.ofReal (p x) / ν {x}) := by
        unfold vecMeasure
        congr 1
        funext x
        rw [Pi.mul_apply, ENNReal.mul_div_cancel (hν x).ne' (measure_ne_top _ _)]
    _ = (Measure.count.withDensity fun x ↦ ν {x}).withDensity
        fun x ↦ ENNReal.ofReal (p x) / ν {x} :=
        withDensity_mul _ (measurable_of_countable _) (measurable_of_countable _)
    _ = ν.withDensity fun x ↦ ENNReal.ofReal (p x) / ν {x} := by
        rw [count_withDensity_singleton ν]

omit [Fintype X] in
theorem llr_vecMeasure [Finite X] {p : X → ℝ} (hp : ∀ x, 0 ≤ p x) (x : X) :
    llr (vecMeasure p) ν x = Real.log (p x / ν.real {x}) := by
  have h := Measure.rnDeriv_withDensity ν
    (f := fun x ↦ ENNReal.ofReal (p x) / ν {x}) (measurable_of_countable _)
  rw [← vecMeasure_eq_withDensity ν hν] at h
  have hx := forall_of_ae_full_support ν hν h x
  unfold llr
  rw [hx, ENNReal.toReal_div, ENNReal.toReal_ofReal (hp x), measureReal_def]

/-- **The bridge**: the real relative entropy of a probability vector is `entVec`. -/
theorem toReal_klDiv_vecMeasure {p : X → ℝ} (hp : p ∈ stdSimplex ℝ X) :
    (klDiv (vecMeasure p) ν).toReal = entVec ν p := by
  have hP := isProbabilityMeasure_vecMeasure hp
  rw [toReal_klDiv (absolutelyContinuous_of_full_support hν _) Integrable.of_finite, probReal_univ,
    probReal_univ, add_sub_cancel_right, integral_vecMeasure hp.1]
  exact Finset.sum_congr rfl fun x _ ↦ by rw [llr_vecMeasure ν hν hp.1]

end Entropy

section Recovery

variable {X : Type*} [Fintype X]

/-- **Additive recovery on the finite simplex**: if `a_n → r` and `supp r ⊆ supp p`, then
`p + a_n − r` is eventually a probability vector. -/
theorem eventually_add_sub_mem_stdSimplex {p r : X → ℝ} (hp : p ∈ stdSimplex ℝ X)
    (hr : r ∈ stdSimplex ℝ X) (hsupp : ∀ x, 0 < r x → 0 < p x) {a : ℕ → X → ℝ}
    (ha : ∀ n, a n ∈ stdSimplex ℝ X) (hlim : Tendsto a atTop (𝓝 r)) :
    ∀ᶠ n in atTop, p + a n - r ∈ stdSimplex ℝ X := by
  have hsum : ∀ n, ∑ x, (p + a n - r) x = 1 := fun n ↦ by
    simp only [Pi.add_apply, Pi.sub_apply, Finset.sum_sub_distrib, Finset.sum_add_distrib, hp.2,
      (ha n).2, hr.2]
    ring
  have hcoord : ∀ x, ∀ᶠ n in atTop, 0 ≤ (p + a n - r) x := fun x ↦ by
    rcases eq_or_lt_of_le (hp.1 x) with h0 | hpos
    · have hr0 : r x = 0 := le_antisymm (not_lt.1 fun h ↦ (hsupp x h).ne' h0.symm) (hr.1 x)
      exact Eventually.of_forall fun n ↦ by
        simp only [Pi.add_apply, Pi.sub_apply, ← h0, hr0, zero_add, sub_zero]
        exact (ha n).1 x
    · have ht : Tendsto (fun n ↦ (p + a n - r) x) atTop (𝓝 (p x)) := by
        have := ((tendsto_pi_nhds.1 hlim x).const_add (p x)).sub_const (r x)
        simpa using this
      exact (ht.eventually (lt_mem_nhds hpos)).mono fun n hn ↦ hn.le
  filter_upwards [eventually_all.2 hcoord] with n hn
  exact ⟨hn, hsum n⟩

omit [Fintype X] in
theorem tendsto_add_sub {p r : X → ℝ} {a : ℕ → X → ℝ} (hlim : Tendsto a atTop (𝓝 r)) :
    Tendsto (fun n ↦ p + a n - r) atTop (𝓝 p) := by
  have := (hlim.const_add p).sub_const r
  simpa using this

theorem vecMoment_add_sub {J : Type*} (S : J → X → ℝ) (p a r : X → ℝ) :
    vecMoment S (p + a - r) = vecMoment S p + vecMoment S a - vecMoment S r := by
  funext j
  simp only [vecMoment, Pi.add_apply, Pi.sub_apply, add_mul, sub_mul, Finset.sum_add_distrib,
    Finset.sum_sub_distrib]

/-- The response map of vectors is continuous. -/
theorem continuous_vecMoment {J : Type*} (S : J → X → ℝ) : Continuous (vecMoment S) :=
  continuous_pi fun _ ↦ continuous_finsetSum _ fun x _ ↦ (continuous_apply x).mul continuous_const

end Recovery

section Continuity

variable {X : Type*} [Fintype X] [MeasurableSpace X] [MeasurableSingletonClass X] [Nonempty X]
  {J : Type*} [Fintype J] [Nonempty J] {S : J → X → ℝ} (hS : ∀ j, Bdd (S j)) (ν : Measure X)
  [IsProbabilityMeasure ν] (hν : ∀ x, 0 < ν {x})
include hS hν

/-- The moment polytope `conv S(X)`. -/
local notation "hull" => convexHull ℝ (range (statPoint S))

/-- **The completed family minimises the relative entropy over its fibre.** -/
theorem entVec_qStarVec_le {M : J → ℝ} (hM : M ∈ hull) {b : X → ℝ} (hb : b ∈ stdSimplex ℝ X)
    (hbM : vecMoment S b = M) : entVec ν (qStarVec hS ν M) ≤ entVec ν b := by
  have hfin := genRate_ne_top_of_mem_convexHull hS ν hν hM
  have hPb := isProbabilityMeasure_vecMeasure hb
  have h1 : genRate ν S M ≤ klDiv (vecMeasure b) ν := by
    rw [← entropyProj_eq_genRate hS ν M]
    exact entropyProj_le_klDiv ν (vecMeasure b) (by rw [integral_stat_vecMeasure S hb.1, hbM])
  have hPq := isProbabilityMeasure_vecMeasure (qStarVec_mem_stdSimplex hS ν hfin)
  rw [← toReal_klDiv_vecMeasure ν hν hb, ← toReal_klDiv_vecMeasure ν hν
    (qStarVec_mem_stdSimplex hS ν hfin), vecMeasure_qStarVec hS ν hfin,
    (responseProjection_spec hS ν hfin).2.2.1]
  exact ENNReal.toReal_mono (klDiv_ne_top_of_full_support hν _) h1

/-- **The completed family is the unique minimiser.** -/
theorem eq_qStarVec_of_entVec_le {M : J → ℝ} (hM : M ∈ hull) {r : X → ℝ} (hr : r ∈ stdSimplex ℝ X)
    (hrM : vecMoment S r = M) (hle : entVec ν r ≤ entVec ν (qStarVec hS ν M)) :
    r = qStarVec hS ν M := by
  have hfin := genRate_ne_top_of_mem_convexHull hS ν hν hM
  have hPr := isProbabilityMeasure_vecMeasure hr
  have hrM' : (fun i ↦ ∫ x, S i x ∂vecMeasure r) = M := by
    rw [integral_stat_vecMeasure S hr.1, hrM]
  have h1 : genRate ν S M ≤ klDiv (vecMeasure r) ν := by
    rw [← entropyProj_eq_genRate hS ν M]
    exact entropyProj_le_klDiv ν (vecMeasure r) hrM'
  have hPq := isProbabilityMeasure_vecMeasure (qStarVec_mem_stdSimplex hS ν hfin)
  have h2 : klDiv (vecMeasure r) ν ≤ genRate ν S M := by
    rw [← (responseProjection_spec hS ν hfin).2.2.1, ← vecMeasure_qStarVec hS ν hfin]
    exact (ENNReal.toReal_le_toReal (klDiv_ne_top_of_full_support hν _)
      (klDiv_ne_top_of_full_support hν _)).1 (by
        rwa [toReal_klDiv_vecMeasure ν hν hr,
          toReal_klDiv_vecMeasure ν hν (qStarVec_mem_stdSimplex hS ν hfin)])
  obtain ⟨ρ, -, huniq⟩ := exists_unique_entropy_minimiser hS ν hfin
  have e1 := huniq (vecMeasure r) ⟨hPr, hrM', le_antisymm h2 h1⟩
  have e2 := huniq (responseProjection hS ν M) ⟨(responseProjection_spec hS ν hfin).1,
    (responseProjection_spec hS ν hfin).2.1, (responseProjection_spec hS ν hfin).2.2.1⟩
  funext x
  have hx := congrArg (fun μ : Measure X ↦ μ.real {x}) (e1.trans e2.symm)
  rw [measureReal_def, vecMeasure_apply_singleton, ENNReal.toReal_ofReal (hr.1 x)] at hx
  exact hx

omit [Fintype X] in
/-- **Limits of minimisers are minimisers**: if `m_n → M` in the polytope and `q*(m_n) → r`, then
`r = q*(M)`. -/
theorem qStarVec_limit_eq [Finite X] {M : J → ℝ} (hM : M ∈ hull) {m : ℕ → J → ℝ}
    (hm : ∀ n, m n ∈ hull) (hlim : Tendsto m atTop (𝓝 M)) {r : X → ℝ}
    (hr : Tendsto (fun n ↦ qStarVec hS ν (m n)) atTop (𝓝 r)) : r = qStarVec hS ν M := by
  cases nonempty_fintype X
  have hfin := genRate_ne_top_of_mem_convexHull hS ν hν hM
  have hfinn : ∀ n, genRate ν S (m n) ≠ ⊤ := fun n ↦
    genRate_ne_top_of_mem_convexHull hS ν hν (hm n)
  have hqn : ∀ n, qStarVec hS ν (m n) ∈ stdSimplex ℝ X := fun n ↦
    qStarVec_mem_stdSimplex hS ν (hfinn n)
  have hrΔ : r ∈ stdSimplex ℝ X :=
    IsClosed.mem_of_tendsto (isClosed_stdSimplex ℝ X) hr (Eventually.of_forall hqn)
  have hrM : vecMoment S r = M := by
    have h1 : Tendsto (fun n ↦ vecMoment S (qStarVec hS ν (m n))) atTop (𝓝 (vecMoment S r)) :=
      ((continuous_vecMoment S).tendsto r).comp hr
    have e : (fun n ↦ vecMoment S (qStarVec hS ν (m n))) = m :=
      funext fun n ↦ vecMoment_qStarVec hS ν (hfinn n)
    rw [e] at h1
    exact tendsto_nhds_unique h1 hlim
  have hPq := (responseProjection_spec hS ν hfin).1
  have hsupp : ∀ x, 0 < r x → 0 < qStarVec hS ν M x := fun x hx ↦
    ENNReal.toReal_pos (responseProjection_singleton_pos_of_vec hS ν hν hfin hrΔ hrM hx).ne'
      (measure_ne_top _ _)
  have hb := eventually_add_sub_mem_stdSimplex (qStarVec_mem_stdSimplex hS ν hfin) hrΔ hsupp hqn hr
  have hle : ∀ᶠ n in atTop,
      entVec ν (qStarVec hS ν (m n)) ≤ entVec ν (qStarVec hS ν M + qStarVec hS ν (m n) - r) := by
    filter_upwards [hb] with n hn
    refine entVec_qStarVec_le hS ν hν (hm n) hn ?_
    rw [vecMoment_add_sub, vecMoment_qStarVec hS ν hfin, vecMoment_qStarVec hS ν (hfinn n), hrM]
    abel
  have hlim1 : Tendsto (fun n ↦ entVec ν (qStarVec hS ν (m n))) atTop (𝓝 (entVec ν r)) :=
    ((continuous_entVec ν hν).tendsto r).comp hr
  have hlim2 : Tendsto (fun n ↦ entVec ν (qStarVec hS ν M + qStarVec hS ν (m n) - r)) atTop
      (𝓝 (entVec ν (qStarVec hS ν M))) :=
    ((continuous_entVec ν hν).tendsto _).comp (tendsto_add_sub hr)
  exact eq_qStarVec_of_entVec_le hS ν hν hM hrΔ hrM (le_of_tendsto_of_tendsto hlim1 hlim2 hle)

omit [Fintype X] in
/-- **The completed family is sequentially continuous on the polytope.** -/
theorem tendsto_qStarVec [Finite X] {M : J → ℝ} (hM : M ∈ hull) {m : ℕ → J → ℝ}
    (hm : ∀ n, m n ∈ hull) (hlim : Tendsto m atTop (𝓝 M)) :
    Tendsto (fun n ↦ qStarVec hS ν (m n)) atTop (𝓝 (qStarVec hS ν M)) := by
  cases nonempty_fintype X
  refine tendsto_of_subseq_tendsto fun ns hns ↦ ?_
  obtain ⟨a, -, φ, hφ, ha⟩ := (isCompact_stdSimplex ℝ X).tendsto_subseq
    (x := fun n ↦ qStarVec hS ν (m (ns n))) fun n ↦
      qStarVec_mem_stdSimplex hS ν (genRate_ne_top_of_mem_convexHull hS ν hν (hm (ns n)))
  refine ⟨φ, ?_⟩
  have ha' : Tendsto (fun n ↦ qStarVec hS ν (m (ns (φ n)))) atTop (𝓝 a) := ha
  have := qStarVec_limit_eq hS ν hν hM (m := fun n ↦ m (ns (φ n))) (fun n ↦ hm _)
    (hlim.comp (hns.comp hφ.tendsto_atTop)) ha'
  rw [← this]
  exact ha'

omit [Fintype X] in
/-- **The completed family is continuous on the moment polytope.** -/
theorem continuousOn_qStarVec [Finite X] : ContinuousOn (qStarVec hS ν) hull := by
  rw [continuousOn_iff_continuous_domRestrict]
  refine continuous_iff_seqContinuous.2 fun u M hu ↦ ?_
  have h := tendsto_qStarVec hS ν hν M.2 (m := fun n ↦ (u n : J → ℝ)) (fun n ↦ (u n).2)
    ((continuous_subtype_val.tendsto M).comp hu)
  exact h

omit [Fintype X] in
/-- **The rate is continuous on the moment polytope.** -/
theorem continuousOn_genRate_toReal [Finite X] :
    ContinuousOn (fun M ↦ (genRate ν S M).toReal) hull := by
  cases nonempty_fintype X
  have e : ∀ M ∈ hull, (genRate ν S M).toReal = entVec ν (qStarVec hS ν M) := fun M hM ↦ by
    have hfin := genRate_ne_top_of_mem_convexHull hS ν hν hM
    rw [← (responseProjection_spec hS ν hfin).2.2.1, ← vecMeasure_qStarVec hS ν hfin,
      toReal_klDiv_vecMeasure ν hν (qStarVec_mem_stdSimplex hS ν hfin)]
  exact ((continuous_entVec ν hν).comp_continuousOn (continuousOn_qStarVec hS ν hν)).congr e

end Continuity

end Laplace.Multi
