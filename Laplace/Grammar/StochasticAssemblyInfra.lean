/-
Copyright (c) 2026 Timaeus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Laplace.Grammar.PhaseRandomPosterior

/-!
# Infrastructure for the stochastic chart assembly

Unit 214 (Astra #23 programme G, step 1). Generic probabilistic lemmas, and the joint vector form of
Headline XVI over a finite family of charts with their own dimensions:

* `tendstoInMeasure_const_of_tendsto`: a deterministic convergent sequence converges in measure;
* `tendstoInMeasure_pi_zero`: finitely many sequences converging to `0` in measure give a vector
  converging to `0` in measure (sup norm);
* `tendstoInDistribution_prodMk_tendsto_const`: Slutsky pairing with a deterministic convergent
  sequence (wrapper around Mathlib's `prodMk_of_tendstoInMeasure_const`);
* `tendstoInDistribution_normChart_vec`: for charts `a : κ` (finite), jointly convergent random
  phases `X n : Ω → Π a, C([0,1]^{d a + 1}, ℝ)` and fixed amplitudes `g a`, the vector of normalised
  chart integrals converges in distribution to the vector of limit functionals.

Zero `sorry`/`axiom`.
-/

open MeasureTheory Filter Topology Real Set

namespace Laplace.Grammar

variable {ι Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} {L : Filter ι}

/-- A deterministic convergent sequence converges in measure. -/
theorem tendstoInMeasure_const_of_tendsto {E : Type*} [SeminormedAddCommGroup E] (c : ι → E)
    (c₀ : E) (hc : Tendsto c L (𝓝 c₀)) :
    TendstoInMeasure μ (fun n (_ : Ω) => c n) L (fun _ => c₀) := by
  rw [tendstoInMeasure_iff_norm]
  intro ε hε
  have hev : ∀ᶠ n in L, μ {ω : Ω | ε ≤ ‖c n - c₀‖} = 0 := by
    filter_upwards [(tendsto_iff_norm_sub_tendsto_zero.1 hc).eventually (gt_mem_nhds hε)] with n hn
    exact measure_mono_null (fun ω hω => (not_le.2 hn hω).elim) measure_empty
  exact tendsto_const_nhds.congr' (hev.mono fun n hn => hn.symm)

/-- Finitely many sequences converging to `0` in measure give a vector converging to `0`. -/
theorem tendstoInMeasure_pi_zero {κ E : Type*} [Fintype κ] [SeminormedAddCommGroup E]
    (f : κ → ι → Ω → E) (hf : ∀ a, TendstoInMeasure μ (f a) L (fun _ => 0)) :
    TendstoInMeasure μ (fun n ω a => f a n ω) L (fun _ => (0 : κ → E)) := by
  rw [tendstoInMeasure_iff_norm]
  intro ε hε
  have hf' : ∀ a, Tendsto (fun n => μ {ω | ε ≤ ‖f a n ω - 0‖}) L (𝓝 0) := fun a => by
    have := hf a
    rw [tendstoInMeasure_iff_norm] at this
    exact this ε hε
  have hsum : Tendsto (fun n => ∑ a, μ {ω | ε ≤ ‖f a n ω - 0‖}) L (𝓝 0) := by
    simpa using tendsto_finsetSum Finset.univ fun a _ => hf' a
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hsum (fun _ => zero_le)
    fun n => ?_
  refine le_trans (measure_mono ?_) (measure_iUnion_fintype_le _ _)
  intro ω hω
  by_contra hcon
  simp only [Set.mem_iUnion, not_exists] at hcon
  have hlt : ‖(fun a => f a n ω) - (0 : κ → E)‖ < ε := by
    rw [sub_zero, pi_norm_lt_iff hε]
    intro a
    have := hcon a
    simpa [not_le] using this
  exact absurd hω (not_le.2 hlt)

variable [IsProbabilityMeasure μ] {Ω' : Type*} [MeasurableSpace Ω'] {μ' : Measure Ω'}
  [IsProbabilityMeasure μ'] [L.IsCountablyGenerated]

/-- **Slutsky pairing with a deterministic convergent sequence.** -/
theorem tendstoInDistribution_prodMk_tendsto_const {E E' : Type*} [SeminormedAddCommGroup E]
    [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E] [MeasurableSpace E']
    [SeminormedAddCommGroup E'] [SecondCountableTopology E'] [BorelSpace E'] (X : ι → Ω → E)
    (Z : Ω' → E)
    (hX : TendstoInDistribution X L Z (fun _ => μ) μ') (c : ι → E') (c₀ : E')
    (hc : Tendsto c L (𝓝 c₀)) :
    TendstoInDistribution (fun n ω => (X n ω, c n)) L (fun ω => (Z ω, c₀)) (fun _ => μ) μ' :=
  hX.prodMk_of_tendstoInMeasure_const X (fun n _ => c n) Z
    (tendstoInMeasure_const_of_tendsto c c₀ hc) fun _ => aemeasurable_const

/-- The finite product of chart input phase spaces. -/
abbrev PhaseSpaces (κ : Type*) (d : κ → ℕ) := (a : κ) → C(closedCube (d a + 1), ℝ)

/-- **Joint vector form of Headline XVI**: over finitely many charts with jointly convergent random
phases and fixed amplitudes, the vector of normalised chart integrals converges in distribution to
the vector of limit functionals. -/
theorem tendstoInDistribution_normChart_vec {κ : Type*} [Fintype κ] (d : κ → ℕ)
    (h k : (a : κ) → Fin (d a + 1) → ℕ) (hk : ∀ a i, 0 < k a i) (l : κ → ℝ) (β : ℝ)
    (hl : ∀ a, 0 < l a) (hβ : 0 < β) (hmin : ∀ a i, l a ≤ ratioExp (h a) (k a) i)
    (hatt : ∀ a, ∃ i, ratioExp (h a) (k a) i = l a) (X : ι → Ω → PhaseSpaces κ d)
    (hXm : ∀ n, Measurable (X n)) (Z : Ω' → PhaseSpaces κ d) (hZm : Measurable Z)
    (hX : TendstoInDistribution X L Z (fun _ => μ) μ') (Nseq : ι → ℝ) (hN : Tendsto Nseq L atTop)
    (hN0 : ∀ n, 0 ≤ Nseq n) (g : (a : κ) → C(closedCube (d a + 1), ℝ)) :
    TendstoInDistribution (fun n ω a => normChart (h a) (k a) (l a) β (Nseq n) (X n ω a, g a)) L
      (fun ω a => limChart (h a) (k a) (l a) β (Z ω a, g a)) (fun _ => μ) μ' := by
  have hcontlim : ∀ a, Continuous fun x : PhaseSpaces κ d =>
      limChart (h a) (k a) (l a) β (x a, g a) := fun a =>
    (continuous_limChart (d a) (h a) (k a) (hk a) (l a) β (hl a) hβ (hmin a)).comp
      ((continuous_pair_const (g a)).comp (continuous_apply a))
  have hlim : TendstoInDistribution (fun n ω a => limChart (h a) (k a) (l a) β (X n ω a, g a)) L
      (fun ω a => limChart (h a) (k a) (l a) β (Z ω a, g a)) (fun _ => μ) μ' :=
    hX.continuous_comp (continuous_pi hcontlim)
  have herr : TendstoInMeasure μ (fun n ω a =>
      normChart (h a) (k a) (l a) β (Nseq n) (X n ω a, g a) -
        limChart (h a) (k a) (l a) β (X n ω a, g a)) L (fun _ => (0 : κ → ℝ)) := by
    refine tendstoInMeasure_pi_zero _ fun a => ?_
    have hca : Continuous fun x : PhaseSpaces κ d => ((x a, g a) : InputSpace (d a + 1)) :=
      (continuous_pair_const (g a)).comp (continuous_apply a)
    have hXa : TendstoInDistribution (fun n ω => ((X n ω a, g a) : InputSpace (d a + 1))) L
        (fun ω => (Z ω a, g a)) (fun _ => μ) μ' := hX.continuous_comp hca
    exact tendstoInMeasure_normChart_sub (d a) (h a) (k a) (hk a) (l a) β (hl a) hβ (hmin a)
      (hatt a) _ _ ((measurable_pi_apply a).comp hZm |>.prodMk measurable_const) hXa Nseq hN
  have hmeas : ∀ n, AEMeasurable (fun ω a =>
      normChart (h a) (k a) (l a) β (Nseq n) (X n ω a, g a) -
        limChart (h a) (k a) (l a) β (X n ω a, g a)) μ := fun n => by
    refine (measurable_pi_iff.2 fun a => ?_).aemeasurable
    have hm : Measurable fun ω => ((X n ω a, g a) : InputSpace (d a + 1)) :=
      ((measurable_pi_apply a).comp (hXm n)).prodMk measurable_const
    exact ((continuous_normChart (d a) (h a) (k a) (l a) β (Nseq n) hβ (hN0 n)).measurable.comp
      hm).sub ((continuous_limChart (d a) (h a) (k a) (hk a) (l a) β (hl a) hβ
        (hmin a)).measurable.comp hm)
  have hsum := hlim.add_of_tendstoInMeasure_const herr hmeas
  refine hsum.congr (fun n => Eventually.of_forall fun ω => ?_) (Eventually.of_forall fun ω => ?_)
  · funext a
    simp only [Pi.add_apply]
    ring
  · simp

end Laplace.Grammar
