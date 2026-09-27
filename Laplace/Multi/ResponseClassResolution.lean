/-
Copyright (c) 2026 Timaeus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Timaeus
-/
import Laplace.Multi.FisherNormalisedSampling
import Laplace.Multi.TangentPythagoras

/-!
# Chamber resolution: the probability of a sampling-induced class change

The wall-and-chamber picture partitions the space of structural coordinates into classes
(chambers). Sampling replaces the true coordinate `m = E_D S` by the empirical response `M̂_n`;
the class is resolved when `M̂_n` stays in the chamber of `m`. The **Fisher margin** of a chamber
`C` at `m` is a radius `r` such that the Fisher-normalised ball `{m + z : z ∈ W, q_θ(z) < r²}` is
contained in `C`, where `q_θ` is the sampling energy of `FisherNormalisedSampling`.

Since `M̂_n − m ∈ W` almost surely (`ae_sampleResponse_sub_mem_dirSpan`), a class change forces
`q_θ(M̂_n − m) ≥ r²`, and Markov's inequality with the trace identity gives

`P(M̂_n ∉ C) ≤ tr(R_θ C_D) / (n r²)`   (`measureReal_sampleResponse_notMem_le`),

and at a matched law `D = P_θ`

`P(M̂_n ∉ C) ≤ dim W / (n r²)`   (`measureReal_sampleResponse_notMem_le_family`).

The chamber is resolved by `n` samples as soon as `n r² ≫ dim W`: the "typical size" of a chamber
in the Fisher metric of the response, compared with the scale-free sampling noise `√(dim W / n)`,
decides whether two data distributions with different response geometry can be told apart. The
class partition is abstract, so that it later instantiates to the germ classes of the atlas.
-/

open MeasureTheory ProbabilityTheory Filter Topology Set

namespace Laplace.Multi

section Resolution

variable {X : Type*} [MeasurableSpace X] [Nonempty X] {J : Type*} [Fintype J] [Nonempty J]
  [DecidableEq J] {Ω : Type*} {S : J → X → ℝ} (hS : ∀ j, Bdd (S j)) (ν : Measure X)
  [IsProbabilityMeasure ν] [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
  (D : Measure X) [IsProbabilityMeasure D] (hDν : D ≪ ν) (Xs : ℕ → Ω → X)
  (hXm : ∀ i, Measurable (Xs i)) (hid : ∀ i, IdentDistrib (Xs i) (Xs 0) P P)
  (hlaw : P.map (Xs 0) = D) (hind : ∀ i k, i ≠ k → IndepFun (Xs i) (Xs k) P)
include hS hXm hid hlaw

/-- The direction space. -/
local notation "𝕍" => dirSpan ν (fun _ ↦ (1 : ℝ)) S

/-- The reconstructed family. -/
local notation "Pfam" => familyMeasure ν (fun _ ↦ (1 : ℝ)) (fun _ ↦ (0 : ℝ)) S 1

omit [DecidableEq J] [IsProbabilityMeasure P] in
include hDν in
set_option linter.unusedFintypeInType false in
/-- **The empirical error lies in the direction space** almost surely. -/
theorem ae_sampleResponse_sub_mem_dirSpan {n : ℕ} (hn : 0 < n) :
    ∀ᵐ ω ∂P, (fun j ↦ sampleResponse S Xs n ω j - ∫ x, S j x ∂D) ∈ 𝕍 := by
  filter_upwards [ae_sampleResponse_mem_momentBody hS ν P D hDν Xs hXm hid hlaw] with ω hω
  exact sub_mem_dirSpan_of_mem_momentBody' hS ν (mean_mem_momentBody_of_ac hS ν D hDν) (hω n hn)

omit [DecidableEq J] hid hlaw in
/-- The sampling energy of the empirical error is integrable. -/
theorem integrable_samplingEnergy (θ : 𝕍) (p : (J → ℝ) →ₗ[ℝ] 𝕍) {n : ℕ} (hn : 0 < n) :
    Integrable (fun ω ↦ samplingEnergy hS ν θ p
      (fun j ↦ sampleResponse S Xs n ω j - ∫ x, S j x ∂D)) P := by
  classical
  have hexp : ∀ ω, samplingEnergy hS ν θ p (fun j ↦ sampleResponse S Xs n ω j - ∫ x, S j x ∂D) =
      ∑ a, ∑ b, (-samplingOp hS ν θ p (Pi.single b 1) a) *
        ((sampleResponse S Xs n ω a - ∫ x, S a x ∂D) *
          (sampleResponse S Xs n ω b - ∫ x, S b x ∂D)) := fun ω ↦ by
    rw [samplingEnergy, dotJ_samplingOp_eq, ← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun a _ ↦ ?_
    rw [← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun b _ ↦ ?_
    ring
  have hint : Integrable (fun ω ↦ ∑ a, ∑ b, (-samplingOp hS ν θ p (Pi.single b 1) a) *
      ((sampleResponse S Xs n ω a - ∫ x, S a x ∂D) *
        (sampleResponse S Xs n ω b - ∫ x, S b x ∂D))) P :=
    integrable_finsetSum _ fun a _ ↦ integrable_finsetSum _ fun b _ ↦
      (integrable_sampleResponse_sub_mul hS P D Xs hXm hn a b).const_mul _
  exact hint.congr (Eventually.of_forall fun ω ↦ (hexp ω).symm)

include hDν hind in
/-- **Markov for the Fisher-normalised error**:
`r² · P(q_θ(M̂_n − m) ≥ r²) ≤ −tr(R_θ C_D) / n`. -/
theorem mul_measureReal_samplingEnergy_ge_le (θ : 𝕍) (p : (J → ℝ) →ₗ[ℝ] 𝕍)
    (hp : ∀ w : 𝕍, p (w : J → ℝ) = w) {n : ℕ} (hn : 0 < n) (ε : ℝ) :
    ε * P.real {ω | ε ≤ samplingEnergy hS ν θ p
      (fun j ↦ sampleResponse S Xs n ω j - ∫ x, S j x ∂D)} ≤
      -(∑ a, ∑ b, samplingOp hS ν θ p (Pi.single b 1) a * lawCov D (S a) (S b)) / n := by
  rw [← integral_samplingEnergy hS ν P D Xs hXm hid hlaw hind θ p hn]
  refine mul_meas_ge_le_integral_of_nonneg ?_ (integrable_samplingEnergy hS ν P D Xs hXm θ p hn) ε
  filter_upwards [ae_sampleResponse_sub_mem_dirSpan hS ν P D hDν Xs hXm hid hlaw hn] with ω hω
  change 0 ≤ samplingEnergy hS ν θ p (fun j ↦ sampleResponse S Xs n ω j - ∫ x, S j x ∂D)
  rw [samplingEnergy_eq_fisherVar hS ν θ p hp hω]
  exact fisherVar_nonneg hS ν _ _

include hDν hind in
/-- **Chamber resolution**: if the Fisher-normalised ball of radius `r` around `m` lies in the
class `C`, the empirical response leaves `C` with probability at most `−tr(R_θ C_D) / (n r²)`. -/
theorem measureReal_sampleResponse_notMem_le (θ : 𝕍) (p : (J → ℝ) →ₗ[ℝ] 𝕍)
    (hp : ∀ w : 𝕍, p (w : J → ℝ) = w) {C : Set (J → ℝ)} {r : ℝ} (hr : 0 < r)
    (hmargin : ∀ z ∈ 𝕍, samplingEnergy hS ν θ p z < r ^ 2 →
      (fun j ↦ ∫ x, S j x ∂D) + z ∈ C) {n : ℕ} (hn : 0 < n) :
    P.real {ω | sampleResponse S Xs n ω ∉ C} ≤
      -(∑ a, ∑ b, samplingOp hS ν θ p (Pi.single b 1) a * lawCov D (S a) (S b)) / n / r ^ 2 := by
  have hsub : {ω | sampleResponse S Xs n ω ∉ C} ≤ᵐ[P]
      {ω | r ^ 2 ≤ samplingEnergy hS ν θ p
        (fun j ↦ sampleResponse S Xs n ω j - ∫ x, S j x ∂D)} := by
    filter_upwards [ae_sampleResponse_sub_mem_dirSpan hS ν P D hDν Xs hXm hid hlaw hn] with ω hω hC
    by_contra hlt
    apply hC
    have := hmargin _ hω (lt_of_not_ge hlt)
    convert this using 1
    funext j
    simp
  have h1 : P.real {ω | sampleResponse S Xs n ω ∉ C} ≤
      P.real {ω | r ^ 2 ≤ samplingEnergy hS ν θ p
        (fun j ↦ sampleResponse S Xs n ω j - ∫ x, S j x ∂D)} := by
    rw [measureReal_def, measureReal_def]
    exact ENNReal.toReal_mono (measure_ne_top _ _) (measure_mono_ae hsub)
  have h2 := mul_measureReal_samplingEnergy_ge_le hS ν P D hDν Xs hXm hid hlaw hind θ p hp hn
    (r ^ 2)
  rw [le_div_iff₀ (by positivity)]
  calc P.real {ω | sampleResponse S Xs n ω ∉ C} * r ^ 2 ≤
        P.real {ω | r ^ 2 ≤ samplingEnergy hS ν θ p
          (fun j ↦ sampleResponse S Xs n ω j - ∫ x, S j x ∂D)} * r ^ 2 :=
        mul_le_mul_of_nonneg_right h1 (by positivity)
    _ = r ^ 2 * P.real {ω | r ^ 2 ≤ samplingEnergy hS ν θ p
          (fun j ↦ sampleResponse S Xs n ω j - ∫ x, S j x ∂D)} := mul_comm _ _
    _ ≤ _ := h2

end Resolution

section Matched

variable {X : Type*} [MeasurableSpace X] [Nonempty X] {J : Type*} [Fintype J] [Nonempty J]
  {Ω : Type*} {S : J → X → ℝ} (hS : ∀ j, Bdd (S j)) (ν : Measure X)
  [IsProbabilityMeasure ν] [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
  (Xs : ℕ → Ω → X) (hXm : ∀ i, Measurable (Xs i)) (hid : ∀ i, IdentDistrib (Xs i) (Xs 0) P P)
  (hind : ∀ i k, i ≠ k → IndepFun (Xs i) (Xs k) P)
include hS hXm hid hind

/-- The direction space. -/
local notation "𝕍" => dirSpan ν (fun _ ↦ (1 : ℝ)) S

/-- The reconstructed family. -/
local notation "Pfam" => familyMeasure ν (fun _ ↦ (1 : ℝ)) (fun _ ↦ (0 : ℝ)) S 1

/-- **Chamber resolution at a matched law**: with `n` samples from `P_θ` and a Fisher margin `r`
of the class `C` at `m(θ)`, `P(M̂_n ∉ C) ≤ dim W / (n r²)`. -/
theorem measureReal_sampleResponse_notMem_le_family (θ : 𝕍) (p : (J → ℝ) →ₗ[ℝ] 𝕍)
    (hp : ∀ w : 𝕍, p (w : J → ℝ) = w) (hlaw : P.map (Xs 0) = Pfam (θ : J → ℝ))
    {C : Set (J → ℝ)} {r : ℝ} (hr : 0 < r)
    (hmargin : ∀ z ∈ 𝕍, samplingEnergy hS ν θ p z < r ^ 2 →
      (fun j ↦ ∫ x, S j x ∂(Pfam (θ : J → ℝ))) + z ∈ C) {n : ℕ} (hn : 0 < n) :
    P.real {ω | sampleResponse S Xs n ω ∉ C} ≤ (Module.finrank ℝ 𝕍 : ℝ) / (n * r ^ 2) := by
  classical
  have := isProbabilityMeasure_family hS ν (θ : J → ℝ)
  have hac : Pfam (θ : J → ℝ) ≪ ν := by
    rw [familyMeasure_eq_withDensity_famDens]
    exact withDensity_absolutelyContinuous _ _
  have h := measureReal_sampleResponse_notMem_le hS ν P _ hac Xs hXm hid hlaw hind θ p hp hr
    hmargin hn
  rw [sum_samplingOp_lawCov_family hS ν θ p hp, neg_neg, div_div] at h
  exact h

end Matched

end Laplace.Multi
