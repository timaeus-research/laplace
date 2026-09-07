/-
Copyright (c) 2026 Timaeus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Laplace.Grammar.StochasticAssemblyInfra

/-!
# Headline XVIII: the assembled stochastic posterior quotient

Unit 215 (Astra #23 programme G, step 2). Finitely many charts `a : κ`, each with its own dimension,
exponents, deterministic continuous observable `φ a` and density `c a > 0`, a common `β`, jointly
convergent random phases `X n ⇒ Z` in `Π a, C([0,1]^{d a + 1})`, deterministic scales `N n → ∞`
(`N n > 1`):
```
∑_a ∫ φ_a c_a u^h e^{-βN²u^{2k}+βNu^k X_n^a} / ∑_a ∫ c_a u^h e^{-βN²u^{2k}+βNu^k X_n^a}
   ⇒ ∑_{a selected} phaseCoeff_a(Z^a, φ_a c_a) / ∑_{a selected} phaseCoeff_a(Z^a, c_a),
```
the selected charts being those with minimal exponent `p_a = 2λ_a` and, among those, maximal
multiplicity (`headline_stochastic_assembled_posterior`). Proof: the vector of per-chart normalised
numerators and denominators converges jointly (joint Headline XVI), the deterministic scale ratios
`S_a(N)/S_*(N)` converge to the selection indicators, Slutsky pairs them, continuous summation gives
the assembled numerator and denominator, the selected limiting denominator is strictly positive, and
the common scale cancels exactly.

Conditional as in Headline XV: that the posterior is such a sum of chart integrals is the paper's
input; the empirical phases' joint convergence is a hypothesis; densities are deterministic and
strictly positive. Zero `sorry`/`axiom`.
-/

open MeasureTheory Filter Topology Real Set

namespace Laplace.Grammar

variable {ι Ω Ω' : Type*} [MeasurableSpace Ω] [MeasurableSpace Ω'] {μ : Measure Ω}
  [IsProbabilityMeasure μ] {μ' : Measure Ω'} [IsProbabilityMeasure μ'] {L : Filter ι}
  [L.IsCountablyGenerated]

/-- **Joint pair-vector form of Headline XVI**: numerator and denominator amplitudes on every
chart. -/
theorem tendstoInDistribution_normChart_pairVec {κ : Type*} [Fintype κ] (d : κ → ℕ)
    (h k : (a : κ) → Fin (d a + 1) → ℕ) (hk : ∀ a i, 0 < k a i) (l : κ → ℝ) (β : ℝ)
    (hl : ∀ a, 0 < l a) (hβ : 0 < β) (hmin : ∀ a i, l a ≤ ratioExp (h a) (k a) i)
    (hatt : ∀ a, ∃ i, ratioExp (h a) (k a) i = l a) (X : ι → Ω → PhaseSpaces κ d)
    (hXm : ∀ n, Measurable (X n)) (Z : Ω' → PhaseSpaces κ d) (hZm : Measurable Z)
    (hX : TendstoInDistribution X L Z (fun _ => μ) μ') (Nseq : ι → ℝ) (hN : Tendsto Nseq L atTop)
    (hN0 : ∀ n, 0 ≤ Nseq n) (g₁ g₂ : (a : κ) → C(closedCube (d a + 1), ℝ)) :
    TendstoInDistribution (fun n ω a =>
        (normChart (h a) (k a) (l a) β (Nseq n) (X n ω a, g₁ a),
          normChart (h a) (k a) (l a) β (Nseq n) (X n ω a, g₂ a))) L
      (fun ω a => (limChart (h a) (k a) (l a) β (Z ω a, g₁ a),
        limChart (h a) (k a) (l a) β (Z ω a, g₂ a))) (fun _ => μ) μ' := by
  have hcont : ∀ (a : κ) (g : C(closedCube (d a + 1), ℝ)), Continuous fun x : PhaseSpaces κ d =>
      limChart (h a) (k a) (l a) β (x a, g) := fun a g =>
    (continuous_limChart (d a) (h a) (k a) (hk a) (l a) β (hl a) hβ (hmin a)).comp
      ((continuous_pair_const g).comp (continuous_apply a))
  have hlim : TendstoInDistribution (fun n ω a =>
      (limChart (h a) (k a) (l a) β (X n ω a, g₁ a),
        limChart (h a) (k a) (l a) β (X n ω a, g₂ a))) L
      (fun ω a => (limChart (h a) (k a) (l a) β (Z ω a, g₁ a),
        limChart (h a) (k a) (l a) β (Z ω a, g₂ a))) (fun _ => μ) μ' :=
    hX.continuous_comp (continuous_pi fun a => (hcont a (g₁ a)).prodMk (hcont a (g₂ a)))
  have herr : TendstoInMeasure μ (fun n ω a =>
      (normChart (h a) (k a) (l a) β (Nseq n) (X n ω a, g₁ a) -
          limChart (h a) (k a) (l a) β (X n ω a, g₁ a),
        normChart (h a) (k a) (l a) β (Nseq n) (X n ω a, g₂ a) -
          limChart (h a) (k a) (l a) β (X n ω a, g₂ a))) L (fun _ => (0 : κ → ℝ × ℝ)) := by
    refine tendstoInMeasure_pi_zero _ fun a => ?_
    have hsub : ∀ g : C(closedCube (d a + 1), ℝ), TendstoInMeasure μ (fun n ω =>
        normChart (h a) (k a) (l a) β (Nseq n) (X n ω a, g) -
          limChart (h a) (k a) (l a) β (X n ω a, g)) L (fun _ => 0) := fun g => by
      have hca : Continuous fun x : PhaseSpaces κ d => ((x a, g) : InputSpace (d a + 1)) :=
        (continuous_pair_const g).comp (continuous_apply a)
      have hXa : TendstoInDistribution (fun n ω => ((X n ω a, g) : InputSpace (d a + 1))) L
          (fun ω => (Z ω a, g)) (fun _ => μ) μ' := hX.continuous_comp hca
      exact tendstoInMeasure_normChart_sub (d a) (h a) (k a) (hk a) (l a) β (hl a) hβ (hmin a)
        (hatt a) _ _ ((measurable_pi_apply a).comp hZm |>.prodMk measurable_const) hXa Nseq hN
    exact tendstoInMeasure_prodMk_zero μ _ _ (hsub (g₁ a)) (hsub (g₂ a))
  have hmeas : ∀ n, AEMeasurable (fun ω a =>
      (normChart (h a) (k a) (l a) β (Nseq n) (X n ω a, g₁ a) -
          limChart (h a) (k a) (l a) β (X n ω a, g₁ a),
        normChart (h a) (k a) (l a) β (Nseq n) (X n ω a, g₂ a) -
          limChart (h a) (k a) (l a) β (X n ω a, g₂ a))) μ := fun n => by
    refine (measurable_pi_iff.2 fun a => ?_).aemeasurable
    have hm : ∀ g : C(closedCube (d a + 1), ℝ),
        Measurable fun ω => ((X n ω a, g) : InputSpace (d a + 1)) := fun g =>
      ((measurable_pi_apply a).comp (hXm n)).prodMk measurable_const
    have hcomp : ∀ g : C(closedCube (d a + 1), ℝ), Measurable fun ω =>
        normChart (h a) (k a) (l a) β (Nseq n) (X n ω a, g) -
          limChart (h a) (k a) (l a) β (X n ω a, g) := fun g =>
      ((continuous_normChart (d a) (h a) (k a) (l a) β (Nseq n) hβ (hN0 n)).measurable.comp
        (hm g)).sub ((continuous_limChart (d a) (h a) (k a) (hk a) (l a) β (hl a) hβ
          (hmin a)).measurable.comp (hm g))
    exact (hcomp (g₁ a)).prodMk (hcomp (g₂ a))
  have hsum := hlim.add_of_tendstoInMeasure_const herr hmeas
  refine hsum.congr (fun n => Eventually.of_forall fun ω => ?_) (Eventually.of_forall fun ω => ?_)
  · funext a
    simp only [Pi.add_apply, Prod.mk_add_mk]
    congr 1 <;> ring
  · simp

/-- **Headline XVIII (assembled stochastic posterior quotient)**. -/
theorem headline_stochastic_assembled_posterior {κ : Type*} [Fintype κ] [Nonempty κ] (d : κ → ℕ)
    (h k : (a : κ) → Fin (d a + 1) → ℕ) (hk : ∀ a i, 0 < k a i) (l : κ → ℝ) (β : ℝ)
    (hl : ∀ a, 0 < l a) (hβ : 0 < β) (hmin : ∀ a i, l a ≤ ratioExp (h a) (k a) i)
    (hatt : ∀ a, ∃ i, ratioExp (h a) (k a) i = l a) (X : ι → Ω → PhaseSpaces κ d)
    (hXm : ∀ n, Measurable (X n)) (Z : Ω' → PhaseSpaces κ d) (hZm : Measurable Z)
    (hX : TendstoInDistribution X L Z (fun _ => μ) μ') (Nseq : ι → ℝ) (hN : Tendsto Nseq L atTop)
    (hN1 : ∀ n, 1 < Nseq n) (φ c : (a : κ) → C(closedCube (d a + 1), ℝ))
    (hcpos : ∀ a x, 0 < c a x) :
    TendstoInDistribution (fun n ω =>
        (∑ a, chartIntegral (d a + 1) (h a) (k a) β (Nseq n) (extCube (X n ω a))
            (extCube (φ a * c a))) /
          ∑ a, chartIntegral (d a + 1) (h a) (k a) β (Nseq n) (extCube (X n ω a)) (extCube (c a)))
      L
      (fun ω => (∑ a ∈ Finset.univ.filter (fun a => 2 * l a = leadExp (fun b => 2 * l b) ∧
            multCount (ratioExp (h a) (k a)) (l a) =
              leadMult (fun b => 2 * l b) (fun b => multCount (ratioExp (h b) (k b)) (l b))),
          limChart (h a) (k a) (l a) β (Z ω a, φ a * c a)) /
        ∑ a ∈ Finset.univ.filter (fun a => 2 * l a = leadExp (fun b => 2 * l b) ∧
            multCount (ratioExp (h a) (k a)) (l a) =
              leadMult (fun b => 2 * l b) (fun b => multCount (ratioExp (h b) (k b)) (l b))),
          limChart (h a) (k a) (l a) β (Z ω a, c a)) (fun _ => μ) μ' := by
  have hm1 : ∀ a, 1 ≤ multCount (ratioExp (h a) (k a)) (l a) := fun a =>
    multCount_pos_of_att _ _ _ (hatt a)
  have hN0 : ∀ n, 0 ≤ Nseq n := fun n => by linarith [hN1 n]
  -- the joint pair vector
  have hV := tendstoInDistribution_normChart_pairVec d h k hk l β hl hβ hmin hatt X hXm Z hZm hX
    Nseq hN hN0 (fun a => φ a * c a) c
  -- deterministic scale ratios and their limits (selection indicators)
  have hcoef : Tendsto (fun n => fun a => leadScale (h a) (k a) (l a) (Nseq n) /
      ((Nseq n) ^ (-(leadExp fun b => 2 * l b)) * Real.log (Nseq n) ^
        (leadMult (fun b => 2 * l b) (fun b => multCount (ratioExp (h b) (k b)) (l b)) - 1))) L
      (𝓝 fun a => if 2 * l a = leadExp (fun b => 2 * l b) ∧
          multCount (ratioExp (h a) (k a)) (l a) =
            leadMult (fun b => 2 * l b) (fun b => multCount (ratioExp (h b) (k b)) (l b))
        then (1 : ℝ) else 0) := by
    rw [tendsto_pi_nhds]
    intro a
    exact (scale_ratio_tendsto (fun b => 2 * l b) (fun b => multCount (ratioExp (h b) (k b)) (l b))
      hm1 a).comp hN
  have hpair := tendstoInDistribution_prodMk_tendsto_const _ _ hV _ _ hcoef
  have hg : Continuous fun q : (κ → ℝ × ℝ) × (κ → ℝ) =>
      (∑ a, q.2 a * (q.1 a).1, ∑ a, q.2 a * (q.1 a).2) := by
    refine (continuous_finsetSum _ fun a _ => ?_).prodMk (continuous_finsetSum _ fun a _ => ?_)
    · exact ((continuous_apply a).comp continuous_snd).mul
        (continuous_fst.comp ((continuous_apply a).comp continuous_fst))
    · exact ((continuous_apply a).comp continuous_snd).mul
        (continuous_snd.comp ((continuous_apply a).comp continuous_fst))
  have hsum := hpair.continuous_comp hg
  -- measurability of the assembled numerator and denominator
  have hVm : ∀ n, Measurable fun ω => fun a =>
      (normChart (h a) (k a) (l a) β (Nseq n) (X n ω a, φ a * c a),
        normChart (h a) (k a) (l a) β (Nseq n) (X n ω a, c a)) := fun n => by
    refine measurable_pi_iff.2 fun a => ?_
    have hm : ∀ g : C(closedCube (d a + 1), ℝ),
        Measurable fun ω => ((X n ω a, g) : InputSpace (d a + 1)) := fun g =>
      ((measurable_pi_apply a).comp (hXm n)).prodMk measurable_const
    exact ((continuous_normChart (d a) (h a) (k a) (l a) β (Nseq n) hβ (hN0 n)).measurable.comp
      (hm _)).prodMk ((continuous_normChart (d a) (h a) (k a) (l a) β (Nseq n) hβ
        (hN0 n)).measurable.comp (hm _))
  have hV₀m : Measurable fun ω => fun a =>
      (limChart (h a) (k a) (l a) β (Z ω a, φ a * c a),
        limChart (h a) (k a) (l a) β (Z ω a, c a)) := by
    refine measurable_pi_iff.2 fun a => ?_
    have hm : ∀ g : C(closedCube (d a + 1), ℝ),
        Measurable fun ω => ((Z ω a, g) : InputSpace (d a + 1)) := fun g =>
      ((measurable_pi_apply a).comp hZm).prodMk measurable_const
    exact ((continuous_limChart (d a) (h a) (k a) (hk a) (l a) β (hl a) hβ (hmin a)).measurable.comp
      (hm _)).prodMk ((continuous_limChart (d a) (h a) (k a) (hk a) (l a) β (hl a) hβ
        (hmin a)).measurable.comp (hm _))
  have hGm : ∀ n, Measurable fun ω => (fun q : (κ → ℝ × ℝ) × (κ → ℝ) =>
      (∑ a, q.2 a * (q.1 a).1, ∑ a, q.2 a * (q.1 a).2))
        ((fun a => (normChart (h a) (k a) (l a) β (Nseq n) (X n ω a, φ a * c a),
          normChart (h a) (k a) (l a) β (Nseq n) (X n ω a, c a))),
          fun a => leadScale (h a) (k a) (l a) (Nseq n) /
            ((Nseq n) ^ (-(leadExp fun b => 2 * l b)) * Real.log (Nseq n) ^
              (leadMult (fun b => 2 * l b)
                (fun b => multCount (ratioExp (h b) (k b)) (l b)) - 1))) :=
    fun n => hg.measurable.comp ((hVm n).prodMk measurable_const)
  have hG₀m : Measurable fun ω => (fun q : (κ → ℝ × ℝ) × (κ → ℝ) =>
      (∑ a, q.2 a * (q.1 a).1, ∑ a, q.2 a * (q.1 a).2))
        ((fun a => (limChart (h a) (k a) (l a) β (Z ω a, φ a * c a),
          limChart (h a) (k a) (l a) β (Z ω a, c a))),
          fun a => if 2 * l a = leadExp (fun b => 2 * l b) ∧
              multCount (ratioExp (h a) (k a)) (l a) =
                leadMult (fun b => 2 * l b) (fun b => multCount (ratioExp (h b) (k b)) (l b))
            then (1 : ℝ) else 0) :=
    hg.measurable.comp (hV₀m.prodMk measurable_const)
  -- the selected limiting denominator is positive
  have hsel : ∀ ω, (∑ a, (if 2 * l a = leadExp (fun b => 2 * l b) ∧
      multCount (ratioExp (h a) (k a)) (l a) =
        leadMult (fun b => 2 * l b) (fun b => multCount (ratioExp (h b) (k b)) (l b))
      then (1 : ℝ) else 0) * limChart (h a) (k a) (l a) β (Z ω a, c a)) =
      ∑ a ∈ Finset.univ.filter (fun a => 2 * l a = leadExp (fun b => 2 * l b) ∧
        multCount (ratioExp (h a) (k a)) (l a) =
          leadMult (fun b => 2 * l b) (fun b => multCount (ratioExp (h b) (k b)) (l b))),
        limChart (h a) (k a) (l a) β (Z ω a, c a) := fun ω => by
    rw [Finset.sum_filter]
    exact Finset.sum_congr rfl fun a _ => boole_mul _ _
  have hselφ : ∀ ω, (∑ a, (if 2 * l a = leadExp (fun b => 2 * l b) ∧
      multCount (ratioExp (h a) (k a)) (l a) =
        leadMult (fun b => 2 * l b) (fun b => multCount (ratioExp (h b) (k b)) (l b))
      then (1 : ℝ) else 0) * limChart (h a) (k a) (l a) β (Z ω a, φ a * c a)) =
      ∑ a ∈ Finset.univ.filter (fun a => 2 * l a = leadExp (fun b => 2 * l b) ∧
        multCount (ratioExp (h a) (k a)) (l a) =
          leadMult (fun b => 2 * l b) (fun b => multCount (ratioExp (h b) (k b)) (l b))),
        limChart (h a) (k a) (l a) β (Z ω a, φ a * c a) := fun ω => by
    rw [Finset.sum_filter]
    exact Finset.sum_congr rfl fun a _ => boole_mul _ _
  have hpos : ∀ᵐ ω ∂μ', 0 < ∑ a, (if 2 * l a = leadExp (fun b => 2 * l b) ∧
      multCount (ratioExp (h a) (k a)) (l a) =
        leadMult (fun b => 2 * l b) (fun b => multCount (ratioExp (h b) (k b)) (l b))
      then (1 : ℝ) else 0) * limChart (h a) (k a) (l a) β (Z ω a, c a) := by
    refine Eventually.of_forall fun ω => ?_
    rw [hsel ω]
    refine Finset.sum_pos (fun a _ => phaseCoeff_pos (d a + 1) (h a) (k a) (hk a) (l a) β (hl a) hβ
      (hmin a) (extCube (Z ω a)) (extCube (c a)) (continuous_extCube _) (continuous_extCube _)
      (fun x _ => hcpos a _)) ?_
    obtain ⟨a, ha1, ha2⟩ := exists_leadMult (fun b => 2 * l b)
      (fun b => multCount (ratioExp (h b) (k b)) (l b)) hm1
    exact ⟨a, Finset.mem_filter.2 ⟨Finset.mem_univ a, ha1, ha2⟩⟩
  have hdiv := tendstoInDistribution_div_of_pos _ _ _ _ (fun n => (hGm n).fst)
    (fun n => (hGm n).snd) hG₀m.fst hG₀m.snd hsum hpos
  refine hdiv.congr (fun n => Eventually.of_forall fun ω => ?_) (Eventually.of_forall fun ω => ?_)
  · -- cancel the scales: (Σ_a (s_a/S) (I_a/s_a)) / (Σ_a (s_a/S) (I'_a/s_a)) = (Σ I_a)/(Σ I'_a)
    have hN0' : 0 < Nseq n := by linarith [hN1 n]
    have hS : (Nseq n) ^ (-(leadExp fun b => 2 * l b)) * Real.log (Nseq n) ^
        (leadMult (fun b => 2 * l b) (fun b => multCount (ratioExp (h b) (k b)) (l b)) - 1) ≠ 0 :=
      (mul_pos (Real.rpow_pos_of_pos hN0' _) (pow_pos (Real.log_pos (hN1 n)) _)).ne'
    have hsa : ∀ a, leadScale (h a) (k a) (l a) (Nseq n) ≠ 0 := fun a =>
      (mul_pos (Real.rpow_pos_of_pos hN0' _) (pow_pos (Real.log_pos (hN1 n)) _)).ne'
    have hterm : ∀ (a : κ) (I : ℝ), leadScale (h a) (k a) (l a) (Nseq n) /
        ((Nseq n) ^ (-(leadExp fun b => 2 * l b)) * Real.log (Nseq n) ^
          (leadMult (fun b => 2 * l b) (fun b => multCount (ratioExp (h b) (k b)) (l b)) - 1)) *
        (I / leadScale (h a) (k a) (l a) (Nseq n)) =
        I / ((Nseq n) ^ (-(leadExp fun b => 2 * l b)) * Real.log (Nseq n) ^
          (leadMult (fun b => 2 * l b) (fun b => multCount (ratioExp (h b) (k b)) (l b)) - 1)) :=
      fun a I => by
        rw [div_mul_div_comm, mul_comm (leadScale _ _ _ _) I, mul_div_mul_right _ _ (hsa a)]
    simp only [normChart]
    simp only [hterm]
    rw [← Finset.sum_div, ← Finset.sum_div, div_div_div_cancel_right₀ hS]
  · simp only []
    rw [hselφ ω, hsel ω]

end Laplace.Grammar
