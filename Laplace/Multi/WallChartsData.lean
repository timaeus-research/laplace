/-
Copyright (c) 2026 Timaeus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Timaeus
-/
import Laplace.Multi.FibreKernel

/-!
# The Euclidean wall data and the fibre identity

The Euclidean interface exported by a wall atlas (hironaka branch `wall-atlas`,
`WallAtlas.lintegral_eq_sum_charts_box`): finitely many chart representatives `rep i` (globally
measurable, e.g. the clamped representatives), chart domains `dom i`, nonnegative densities
`dens i` (partition weight times absolute Jacobian), on each domain the truth coordinate
`z ℓ ∘ rep i = truthMono (S i) (q i)` exactly, and the weighted transport identity
`∫⁻_{L'} Ψ = ∑_i ∫⁻_{dom i} Ψ(rep_i u) · dens_i(u) du` (`WallChartsData`).

Consequences, with `K_θ(s) = ∑_i fibreKernel (k i) (S i) (q i) (chartFun θ i) s` the total fibre
kernel: the push-forward identity `∫⁻_{L'} θ(z) η(z ℓ) dz = ∫⁻ η(s) K_θ(s) ds`
(`lintegral_mul_comp_coord`), and the **fibre identity**: when `L' = {z | z ℓ ∈ B, z' ∈ A}`, the
ambient fibre integral `s ↦ ∫⁻_{z' ∈ A} θ(z', s)` equals `K_θ` for almost every `s ∈ B`
(`fibre_ae`, by uniqueness of densities). This is the chart-side expression of the fibre integral
that the one-dimensional reduction of the note consumes.
-/

open Real MeasureTheory Set Filter
open scoped ENNReal

namespace Laplace.Multi

variable {m : ℕ}

/-- The Euclidean export of a wall atlas over a region `L'`. -/
structure WallChartsData (m : ℕ) (ℓ : Fin (m + 1)) (L' : Set (Fin (m + 1) → ℝ)) where
  /-- The finite chart index. -/
  ι : Type
  [fin : Fintype ι]
  /-- The chart representatives (globally measurable). -/
  rep : ι → (Fin (m + 1) → ℝ) → (Fin (m + 1) → ℝ)
  rep_meas : ∀ i, Measurable (rep i)
  /-- The chart domains. -/
  dom : ι → Set (Fin (m + 1) → ℝ)
  dom_meas : ∀ i, MeasurableSet (dom i)
  /-- The chart densities (weight times absolute Jacobian). -/
  dens : ι → (Fin (m + 1) → ℝ) → ℝ
  dens_meas : ∀ i, Measurable (dens i)
  dens_nonneg : ∀ i u, 0 ≤ dens i u
  /-- Sign, exponents and solve index of the truth monomial of each chart. -/
  S : ι → ℝ
  S_ne : ∀ i, S i ≠ 0
  q : ι → Fin (m + 1) → ℕ
  k : ι → Fin (m + 1)
  q_pos : ∀ i, 0 < q i (k i)
  /-- On the domain, the truth coordinate of the representative is the exact monomial. -/
  truth : ∀ i, ∀ u ∈ dom i, rep i u ℓ = truthMono (S i) (q i) u
  /-- The weighted transport identity. -/
  transport : ∀ Ψ : (Fin (m + 1) → ℝ) → ℝ≥0∞, Measurable Ψ →
    ∫⁻ z in L', Ψ z = ∑ i, ∫⁻ u in dom i, Ψ (rep i u) * ENNReal.ofReal (dens i u)

attribute [instance] WallChartsData.fin

namespace WallChartsData

variable {ℓ : Fin (m + 1)} {L' : Set (Fin (m + 1) → ℝ)} (D : WallChartsData m ℓ L')

/-- The coordinate splitting at `ℓ`. -/
local notation "splitAt" => MeasurableEquiv.piFinSuccAbove (fun _ : Fin (m + 1) ↦ ℝ) ℓ

/-- The chart integrand of `θ`: `θ ∘ rep` times the density, carried by the domain. -/
noncomputable def chartFun (θ : (Fin (m + 1) → ℝ) → ℝ≥0∞) (i : D.ι) (u : Fin (m + 1) → ℝ) :
    ℝ≥0∞ :=
  (D.dom i).indicator (fun u ↦ θ (D.rep i u) * ENNReal.ofReal (D.dens i u)) u

theorem measurable_chartFun {θ : (Fin (m + 1) → ℝ) → ℝ≥0∞} (hθ : Measurable θ) (i : D.ι) :
    Measurable (D.chartFun θ i) :=
  ((hθ.comp (D.rep_meas i)).mul (ENNReal.measurable_ofReal.comp (D.dens_meas i))).indicator
    (D.dom_meas i)

/-- The total fibre kernel of `θ`. -/
noncomputable def totalKernel (θ : (Fin (m + 1) → ℝ) → ℝ≥0∞) (s : ℝ) : ℝ≥0∞ :=
  ∑ i, fibreKernel (D.k i) (D.S i) (D.q i) (D.chartFun θ i) s

theorem measurable_fibreKernel (k : Fin (m + 1)) (S : ℝ) (q : Fin (m + 1) → ℕ)
    {Φ : (Fin (m + 1) → ℝ) → ℝ≥0∞} (hΦ : Measurable Φ) : Measurable (fibreKernel k S q Φ) :=
  (measurable_branchKernel_uncurry k S q hΦ).lintegral_prod_left'

theorem measurable_totalKernel {θ : (Fin (m + 1) → ℝ) → ℝ≥0∞} (hθ : Measurable θ) :
    Measurable (D.totalKernel θ) :=
  Finset.measurable_sum _ fun i _ ↦
    measurable_fibreKernel (D.k i) (D.S i) (D.q i) (D.measurable_chartFun hθ i)

/-- **The push-forward identity.** For nonnegative measurable `θ` and `η`,
`∫⁻_{L'} θ(z) η(z ℓ) dz = ∫⁻ η(s) K_θ(s) ds`. -/
theorem lintegral_mul_comp_coord {θ : (Fin (m + 1) → ℝ) → ℝ≥0∞} (hθ : Measurable θ)
    {η : ℝ → ℝ≥0∞} (hη : Measurable η) :
    ∫⁻ z in L', θ z * η (z ℓ) = ∫⁻ s, η s * D.totalKernel θ s := by
  rw [D.transport (fun z ↦ θ z * η (z ℓ)) (hθ.mul (hη.comp (measurable_pi_apply ℓ)))]
  unfold totalKernel
  simp_rw [Finset.mul_sum]
  rw [lintegral_finsetSum (f := fun i s ↦ η s * fibreKernel (D.k i) (D.S i) (D.q i)
    (D.chartFun θ i) s) _ fun i _ ↦
    hη.mul (measurable_fibreKernel (D.k i) (D.S i) (D.q i) (D.measurable_chartFun hθ i))]
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  rw [← lintegral_mul_comp_truthMono (D.k i) (D.S_ne i) (D.q_pos i) (D.measurable_chartFun hθ i)
    hη, ← lintegral_indicator (D.dom_meas i)]
  refine lintegral_congr fun u ↦ ?_
  unfold chartFun
  by_cases hu : u ∈ D.dom i
  · rw [indicator_of_mem hu, indicator_of_mem hu, D.truth i u hu]
    ring
  · rw [indicator_of_notMem hu, indicator_of_notMem hu, zero_mul]

/-- **The fibre identity (almost everywhere).** When `L'` is the product region
`{z | z ℓ ∈ B ∧ z' ∈ A}` (read through the coordinate splitting at `ℓ`), the ambient fibre integral
`s ↦ ∫⁻_{z' ∈ A} θ(z', s)` agrees with the total fibre kernel for almost every `s ∈ B`. -/
theorem fibre_ae {B : Set ℝ} (hB : MeasurableSet B) {A : Set (Fin m → ℝ)} (hA : MeasurableSet A)
    (D : WallChartsData m ℓ (splitAt ⁻¹' (B ×ˢ A)))
    {θ : (Fin (m + 1) → ℝ) → ℝ≥0∞} (hθ : Measurable θ) :
    (fun s ↦ ∫⁻ z' in A, θ (ℓ.insertNth s z')) =ᵐ[volume.restrict B] D.totalKernel θ := by
  have hmp : MeasurePreserving splitAt volume volume :=
    volume_preserving_piFinSuccAbove (fun _ : Fin (m + 1) ↦ ℝ) ℓ
  have hθe : Measurable fun p : ℝ × (Fin m → ℝ) ↦ θ ((splitAt).symm p) :=
    hθ.comp (splitAt).symm.measurable
  have hG : Measurable fun s ↦ ∫⁻ z' in A, θ (ℓ.insertNth s z') := hθe.lintegral_prod_right'
  refine ae_eq_of_forall_setLIntegral_eq_of_sigmaFinite₀ hG.aemeasurable
    (D.measurable_totalKernel hθ).aemeasurable fun E hE _ ↦ ?_
  rw [Measure.restrict_restrict hE]
  have hEB : MeasurableSet (E ∩ B) := hE.inter hB
  set η : ℝ → ℝ≥0∞ := (E ∩ B).indicator (fun _ ↦ 1) with hη
  have hηm : Measurable η := measurable_const.indicator hEB
  have key := D.lintegral_mul_comp_coord hθ hηm
  have hR : ∫⁻ s, η s * D.totalKernel θ s = ∫⁻ s in E ∩ B, D.totalKernel θ s := by
    rw [← lintegral_indicator hEB]
    refine lintegral_congr fun s ↦ ?_
    by_cases hs : s ∈ E ∩ B
    · simp only [hη, indicator_of_mem hs, one_mul]
    · simp only [hη, indicator_of_notMem hs, zero_mul]
  have hL : ∫⁻ z in splitAt ⁻¹' (B ×ˢ A), θ z * η (z ℓ) =
      ∫⁻ s in E ∩ B, ∫⁻ z' in A, θ (ℓ.insertNth s z') := by
    have hmeas : Measurable fun p : ℝ × (Fin m → ℝ) ↦ θ ((splitAt).symm p) * η p.1 :=
      hθe.mul (hηm.comp measurable_fst)
    have h1 := (hmp.restrict_preimage (hB.prod hA)).lintegral_comp_emb
      (splitAt).measurableEmbedding (fun p : ℝ × (Fin m → ℝ) ↦ θ ((splitAt).symm p) * η p.1)
    simp only [MeasurableEquiv.symm_apply_apply] at h1
    change ∫⁻ z in splitAt ⁻¹' (B ×ˢ A), θ z * η (splitAt z).1 = _
    rw [h1, Measure.volume_eq_prod, ← Measure.prod_restrict, lintegral_prod _ hmeas.aemeasurable]
    have h2 : ∀ s, ∫⁻ z', θ ((splitAt).symm (s, z')) * η s ∂(volume.restrict A) =
        (∫⁻ z' in A, θ (ℓ.insertNth s z')) * η s := fun s ↦
      lintegral_mul_const (η s) (hθ.comp ((splitAt).symm.measurable.comp
        (measurable_const.prodMk measurable_id)))
    simp_rw [h2]
    have h3 : ∀ s, (∫⁻ z' in A, θ (ℓ.insertNth s z')) * η s =
        (E ∩ B).indicator (fun s ↦ ∫⁻ z' in A, θ (ℓ.insertNth s z')) s := by
      intro s
      by_cases hs : s ∈ E ∩ B
      · simp only [hη, indicator_of_mem hs, mul_one]
      · simp only [hη, indicator_of_notMem hs, mul_zero]
    simp_rw [h3]
    rw [lintegral_indicator hEB, Measure.restrict_restrict hEB, inter_assoc, inter_self]
  rw [← hL, key, hR]

end WallChartsData

end Laplace.Multi
