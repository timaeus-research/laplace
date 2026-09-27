/-
Copyright (c) 2026 Timaeus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Timaeus
-/
import Laplace.Multi.ResponseTwoScaleCertificate
import Laplace.Multi.ResponseClassResolution

/-!
# The Fisher-normalised noise bridge and the probabilistic resolution theorem

The two-scale certificate of `ResponseTwoScaleCertificate` is stated in the coordinate norm of
`W`, while the sampling-risk identities of the seabed are stated for the Fisher-normalised
**mean-noise energy** `q_θ(z) = G_θ(A_θ⁻¹ z, A_θ⁻¹ z)` (the seabed's `samplingEnergy`,
`meanNoiseEnergy_eq_samplingEnergy`). The bridge is the coercivity of the Fisher form on `W`
(`fisherVar_coercive`): `c ‖v‖² ≤ G_θ(v,v)`, which gives

* `norm_le_of_meanNoiseEnergy`: `‖z‖ ≤ (‖A_θ‖/√c) √q_θ(z)`,
* `abs_apply_inv_le_of_meanNoiseEnergy`: `|ℓ(A_θ⁻¹ z)| ≤ (‖ℓ‖/√c) √q_θ(z)`,

and hence the **certificate in Fisher radius** (`twoScale_sign_certificate_fisher`): on
`q_θ₀(ξ) ≤ r²`,

`ℓ(θ̂) − ℓ(θ₀) ≥ t ℓ(A⁻¹e) − (‖ℓ‖/√c) r − ‖ℓ‖ K (|t|‖e‖ + (‖A‖/√c) r)²`.

**The probabilistic resolution theorem** (`measureReal_sign_certified_ge`): for `n` i.i.d. samples
from a data law `D ≪ ν` whose mean is `m(θ₀) + t e`, the empirical response (in the local inverse
chart at `θ₀`) exists and moves across the wall `ℓ` in the direction of the truth shift with
probability at least `1 − τ₀(D)/(n r²)`, `τ₀ = −tr(R_{θ₀} C_D)`, whenever the Fisher-radius
certificate at radius `r` is positive and `|t|‖e‖ + (‖A‖/√c) r ≤ δ`. Failure of the certificate
means *not certified*, not statistical impossibility.
-/

open MeasureTheory ProbabilityTheory Filter Topology Set

namespace Laplace.Multi

section Bridge

variable {X : Type*} [MeasurableSpace X] [Nonempty X] {J : Type*} [Fintype J] [Nonempty J]
  {S : J → X → ℝ} (hS : ∀ j, Bdd (S j)) (ν : Measure X) [IsProbabilityMeasure ν]
include hS

/-- The direction space. -/
local notation "𝕍" => dirSpan ν (fun _ ↦ (1 : ℝ)) S

/-- The chart derivative. -/
local notation "CD" => chartDeriv measurable_const (integrable_const 1) (fun _ ↦ one_pos)
  (one_integral_pos ν) hS

/-- The chart derivative equivalence. -/
local notation "CDE" => chartDerivEquiv measurable_const (integrable_const 1) (fun _ ↦ one_pos)
  (one_integral_pos ν) hS

/-- The mean map. -/
local notation "mean" => meanMap ν (fun _ ↦ (1 : ℝ)) (fun _ ↦ (0 : ℝ)) S 1

/-- The natural coordinate of a response. -/
local notation "θr" => responseTheta measurable_const (integrable_const 1) (fun _ ↦ one_pos)
  (one_integral_pos ν) hS

/-- The Fisher form. -/
local notation "G" => fisherInner S ν

/-- **The mean-noise energy** `q_θ(z) = G_θ(A_θ⁻¹ z, A_θ⁻¹ z)`. -/
noncomputable def meanNoiseEnergy (θ : 𝕍) (z : 𝕍) : ℝ :=
  G θ ((CDE θ).symm z) ((CDE θ).symm z)

/-- The mean-noise energy is the seabed's Fisher-normalised sampling energy. -/
theorem meanNoiseEnergy_eq_samplingEnergy (θ : 𝕍) (p : (J → ℝ) →ₗ[ℝ] 𝕍)
    (hp : ∀ w : 𝕍, p (w : J → ℝ) = w) (z : 𝕍) :
    samplingEnergy hS ν θ p (z : J → ℝ) = meanNoiseEnergy hS ν θ z := by
  rw [samplingEnergy_eq_fisherVar hS ν θ p hp z.2]
  rfl

theorem meanNoiseEnergy_nonneg (θ z : 𝕍) : 0 ≤ meanNoiseEnergy hS ν θ z :=
  fisherVar_nonneg hS ν _ _

omit [Nonempty J] in
/-- **Coercivity of the Fisher form on `W`**: `c ‖v‖² ≤ G_θ(v,v)` for some `c > 0`. -/
theorem exists_fisher_coercive (θ : 𝕍) : ∃ c > 0, ∀ v : 𝕍, c * ‖v‖ ^ 2 ≤ G θ v v := by
  obtain ⟨lam, hlam, h⟩ := fisherVar_coercive hS ν (θ : J → ℝ)
  exact ⟨lam, hlam, fun v ↦ h v v.2⟩

/-- A Fisher-coercive bound gives a coordinate bound on `A_θ⁻¹ z`. -/
theorem norm_inv_le_of_meanNoiseEnergy (θ : 𝕍) {c : ℝ} (hc : 0 < c)
    (hcoer : ∀ v : 𝕍, c * ‖v‖ ^ 2 ≤ G θ v v) (z : 𝕍) :
    ‖(CDE θ).symm z‖ ≤ Real.sqrt (meanNoiseEnergy hS ν θ z) / Real.sqrt c := by
  have h := hcoer ((CDE θ).symm z)
  have hq : ‖(CDE θ).symm z‖ ^ 2 ≤ meanNoiseEnergy hS ν θ z / c := by
    rw [le_div_iff₀ hc]
    unfold meanNoiseEnergy
    linarith [h]
  calc ‖(CDE θ).symm z‖ = Real.sqrt (‖(CDE θ).symm z‖ ^ 2) := (Real.sqrt_sq (norm_nonneg _)).symm
    _ ≤ Real.sqrt (meanNoiseEnergy hS ν θ z / c) := Real.sqrt_le_sqrt hq
    _ = Real.sqrt (meanNoiseEnergy hS ν θ z) / Real.sqrt c :=
        Real.sqrt_div (meanNoiseEnergy_nonneg hS ν θ z) c

/-- **The coordinate norm of a mean displacement is controlled by its Fisher-normalised
energy**: `‖z‖ ≤ (‖A_θ‖/√c) √q_θ(z)`. -/
theorem norm_le_of_meanNoiseEnergy (θ : 𝕍) {c : ℝ} (hc : 0 < c)
    (hcoer : ∀ v : 𝕍, c * ‖v‖ ^ 2 ≤ G θ v v) (z : 𝕍) :
    ‖z‖ ≤ ‖(CD θ : 𝕍 →L[ℝ] 𝕍)‖ / Real.sqrt c * Real.sqrt (meanNoiseEnergy hS ν θ z) := by
  have hz : z = CD θ ((CDE θ).symm z) := (chartDeriv_chartDerivEquiv_symm hS ν θ z).symm
  calc ‖z‖ = ‖CD θ ((CDE θ).symm z)‖ := by rw [← hz]
    _ ≤ ‖(CD θ : 𝕍 →L[ℝ] 𝕍)‖ * ‖(CDE θ).symm z‖ := (CD θ).le_opNorm _
    _ ≤ ‖(CD θ : 𝕍 →L[ℝ] 𝕍)‖ * (Real.sqrt (meanNoiseEnergy hS ν θ z) / Real.sqrt c) :=
        mul_le_mul_of_nonneg_left (norm_inv_le_of_meanNoiseEnergy hS ν θ hc hcoer z) (norm_nonneg _)
    _ = ‖(CD θ : 𝕍 →L[ℝ] 𝕍)‖ / Real.sqrt c * Real.sqrt (meanNoiseEnergy hS ν θ z) := by ring

/-- **A wall functional of the linearised response is controlled by the Fisher-normalised
energy**: `|ℓ(A_θ⁻¹ z)| ≤ (‖ℓ‖/√c) √q_θ(z)`. -/
theorem abs_apply_inv_le_of_meanNoiseEnergy (θ : 𝕍) {c : ℝ} (hc : 0 < c)
    (hcoer : ∀ v : 𝕍, c * ‖v‖ ^ 2 ≤ G θ v v) (ℓ : 𝕍 →L[ℝ] ℝ) (z : 𝕍) :
    |ℓ ((CDE θ).symm z)| ≤ ‖ℓ‖ / Real.sqrt c * Real.sqrt (meanNoiseEnergy hS ν θ z) := by
  have h1 : |ℓ ((CDE θ).symm z)| ≤ ‖ℓ‖ * ‖(CDE θ).symm z‖ := by
    have := ℓ.le_opNorm ((CDE θ).symm z)
    rwa [Real.norm_eq_abs] at this
  calc |ℓ ((CDE θ).symm z)| ≤ ‖ℓ‖ * ‖(CDE θ).symm z‖ := h1
    _ ≤ ‖ℓ‖ * (Real.sqrt (meanNoiseEnergy hS ν θ z) / Real.sqrt c) :=
        mul_le_mul_of_nonneg_left (norm_inv_le_of_meanNoiseEnergy hS ν θ hc hcoer z) (norm_nonneg _)
    _ = ‖ℓ‖ / Real.sqrt c * Real.sqrt (meanNoiseEnergy hS ν θ z) := by ring

/-- **The two-scale sign certificate in Fisher radius**: on `q_{θ₀}(ξ) ≤ r²`,
`ℓ(θ̂) − ℓ(θ₀) ≥ t ℓ(A⁻¹e) − (‖ℓ‖/√c) r − ‖ℓ‖ K (|t|‖e‖ + (‖A‖/√c) r)²`. -/
theorem twoScale_sign_certificate_fisher (θ₀ : 𝕍) {c : ℝ} (hc : 0 < c)
    (hcoer : ∀ v : 𝕍, c * ‖v‖ ^ 2 ≤ G θ₀ v v) {δ K : ℝ} (hK : 0 ≤ K)
    (hrem : ∀ z : 𝕍, ‖z‖ ≤ δ →
      ‖θr (mean (θ₀ : J → ℝ) + (z : J → ℝ)) - θ₀ - (CDE θ₀).symm z‖ ≤ K * ‖z‖ ^ 2)
    (ℓ : 𝕍 →L[ℝ] ℝ) (e ξ : 𝕍) (t r : ℝ) (hr0 : 0 ≤ r) (hr : meanNoiseEnergy hS ν θ₀ ξ ≤ r ^ 2)
    (hδ : |t| * ‖e‖ + ‖(CD θ₀ : 𝕍 →L[ℝ] 𝕍)‖ / Real.sqrt c * r ≤ δ) :
    t * ℓ (((CDE θ₀).symm : 𝕍 →L[ℝ] 𝕍) e) - ‖ℓ‖ / Real.sqrt c * r -
        ‖ℓ‖ * K * (|t| * ‖e‖ + ‖(CD θ₀ : 𝕍 →L[ℝ] 𝕍)‖ / Real.sqrt c * r) ^ 2 ≤
      ℓ (θr (mean (θ₀ : J → ℝ) + ((t • e + ξ : 𝕍) : J → ℝ))) - ℓ θ₀ := by
  set B₀ := ‖(CD θ₀ : 𝕍 →L[ℝ] 𝕍)‖ / Real.sqrt c with hB₀
  have hsqrt : Real.sqrt (meanNoiseEnergy hS ν θ₀ ξ) ≤ r := by
    rw [Real.sqrt_le_left hr0]; exact hr
  have hB₀nn : 0 ≤ B₀ := by positivity
  -- the coordinate radius of the sampling displacement
  have hξ : ‖ξ‖ ≤ B₀ * r := by
    calc ‖ξ‖ ≤ B₀ * Real.sqrt (meanNoiseEnergy hS ν θ₀ ξ) :=
          norm_le_of_meanNoiseEnergy hS ν θ₀ hc hcoer ξ
      _ ≤ B₀ * r := mul_le_mul_of_nonneg_left hsqrt hB₀nn
  have hδ' : ‖t • e + ξ‖ ≤ δ := by
    calc ‖t • e + ξ‖ ≤ ‖t • e‖ + ‖ξ‖ := norm_add_le _ _
      _ ≤ |t| * ‖e‖ + B₀ * r := by rw [norm_smul, Real.norm_eq_abs]; linarith
      _ ≤ δ := hδ
  have hcert := twoScale_sign_certificate hS ν θ₀ hK hrem ℓ e ξ t (B₀ * r) hξ hδ'
  -- the linear noise term is controlled by the Fisher radius, not by `‖B‖ B₀ r`
  set Bop : 𝕍 →L[ℝ] 𝕍 := ((CDE θ₀).symm : 𝕍 →L[ℝ] 𝕍) with hBop
  set R : 𝕍 := θr (mean (θ₀ : J → ℝ) + ((t • e + ξ : 𝕍) : J → ℝ)) - θ₀ - Bop (t • e + ξ) with hR
  have hR' : ‖R‖ ≤ K * ‖t • e + ξ‖ ^ 2 := hrem _ hδ'
  have hznorm : ‖t • e + ξ‖ ≤ |t| * ‖e‖ + B₀ * r := by
    calc ‖t • e + ξ‖ ≤ ‖t • e‖ + ‖ξ‖ := norm_add_le _ _
      _ ≤ |t| * ‖e‖ + B₀ * r := by rw [norm_smul, Real.norm_eq_abs]; linarith
  have hsq : ‖t • e + ξ‖ ^ 2 ≤ (|t| * ‖e‖ + B₀ * r) ^ 2 := pow_le_pow_left₀ (norm_nonneg _) hznorm 2
  have hℓR : -(‖ℓ‖ * K * (|t| * ‖e‖ + B₀ * r) ^ 2) ≤ ℓ R := by
    have h1 : |ℓ R| ≤ ‖ℓ‖ * ‖R‖ := by
      have := ℓ.le_opNorm R
      rwa [Real.norm_eq_abs] at this
    have h2 : ‖ℓ‖ * ‖R‖ ≤ ‖ℓ‖ * K * (|t| * ‖e‖ + B₀ * r) ^ 2 := by
      calc ‖ℓ‖ * ‖R‖ ≤ ‖ℓ‖ * (K * ‖t • e + ξ‖ ^ 2) := mul_le_mul_of_nonneg_left hR' (norm_nonneg _)
        _ ≤ ‖ℓ‖ * (K * (|t| * ‖e‖ + B₀ * r) ^ 2) :=
            mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hsq hK) (norm_nonneg _)
        _ = ‖ℓ‖ * K * (|t| * ‖e‖ + B₀ * r) ^ 2 := by ring
    linarith [neg_abs_le (ℓ R)]
  have hℓξ : -(‖ℓ‖ / Real.sqrt c * r) ≤ ℓ (Bop ξ) := by
    have h := abs_apply_inv_le_of_meanNoiseEnergy hS ν θ₀ hc hcoer ℓ ξ
    have h2 : ‖ℓ‖ / Real.sqrt c * Real.sqrt (meanNoiseEnergy hS ν θ₀ ξ) ≤ ‖ℓ‖ / Real.sqrt c * r :=
      mul_le_mul_of_nonneg_left hsqrt (by positivity)
    have h3 : |ℓ (Bop ξ)| ≤ ‖ℓ‖ / Real.sqrt c * r := by
      change |ℓ ((CDE θ₀).symm ξ)| ≤ _
      exact h.trans h2
    linarith [neg_abs_le (ℓ (Bop ξ))]
  have hlin : ℓ (Bop (t • e + ξ)) = t * ℓ (Bop e) + ℓ (Bop ξ) := by
    rw [map_add, map_smul, map_add, map_smul, smul_eq_mul]
  have hsplit : ℓ (θr (mean (θ₀ : J → ℝ) + ((t • e + ξ : 𝕍) : J → ℝ))) - ℓ θ₀ =
      ℓ R + ℓ (Bop (t • e + ξ)) := by
    rw [← map_sub, ← map_add]
    congr 1
    rw [hR]; abel
  rw [hsplit, hlin]
  have : ℓ (Bop e) = ℓ (((CDE θ₀).symm : 𝕍 →L[ℝ] 𝕍) e) := rfl
  rw [this] at *
  linarith

end Bridge

section Probabilistic

variable {X : Type*} [MeasurableSpace X] [Nonempty X] {J : Type*} [Fintype J] [Nonempty J]
  [DecidableEq J] {Ω : Type*} {S : J → X → ℝ} (hS : ∀ j, Bdd (S j)) (ν : Measure X)
  [IsProbabilityMeasure ν] [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
  (D : Measure X) [IsProbabilityMeasure D] (hDν : D ≪ ν) (Xs : ℕ → Ω → X)
  (hXm : ∀ i, Measurable (Xs i)) (hid : ∀ i, IdentDistrib (Xs i) (Xs 0) P P)
  (hlaw : P.map (Xs 0) = D) (hind : ∀ i k, i ≠ k → IndepFun (Xs i) (Xs k) P)
include hS hXm hid hlaw hDν hind

/-- The direction space. -/
local notation "𝕍" => dirSpan ν (fun _ ↦ (1 : ℝ)) S

/-- The chart derivative. -/
local notation "CD" => chartDeriv measurable_const (integrable_const 1) (fun _ ↦ one_pos)
  (one_integral_pos ν) hS

/-- The chart derivative equivalence. -/
local notation "CDE" => chartDerivEquiv measurable_const (integrable_const 1) (fun _ ↦ one_pos)
  (one_integral_pos ν) hS

/-- The mean map. -/
local notation "mean" => meanMap ν (fun _ ↦ (1 : ℝ)) (fun _ ↦ (0 : ℝ)) S 1

/-- The natural coordinate of a response. -/
local notation "θr" => responseTheta measurable_const (integrable_const 1) (fun _ ↦ one_pos)
  (one_integral_pos ν) hS

/-- The Fisher form. -/
local notation "G" => fisherInner S ν

/-- **Chebyshev in Fisher radius**: `P(q_{θ}(M̂_n − m_D) ≥ r²) ≤ τ_θ(D) / (n r²)`. -/
theorem measureReal_samplingEnergy_ge_le (θ : 𝕍) (p : (J → ℝ) →ₗ[ℝ] 𝕍)
    (hp : ∀ w : 𝕍, p (w : J → ℝ) = w) {n : ℕ} (hn : 0 < n) {r : ℝ} (hr : 0 < r) :
    P.real {ω | r ^ 2 ≤ samplingEnergy hS ν θ p
        (fun j ↦ sampleResponse S Xs n ω j - ∫ x, S j x ∂D)} ≤
      -(∑ a, ∑ b, samplingOp hS ν θ p (Pi.single b 1) a * lawCov D (S a) (S b)) / n / r ^ 2 := by
  have h := mul_measureReal_samplingEnergy_ge_le hS ν P D hDν Xs hXm hid hlaw hind θ p hp hn (r ^ 2)
  rw [le_div_iff₀ (by positivity), mul_comm]
  exact h

/-- **The probabilistic resolution theorem**: if the data mean is `m(θ₀) + t e` and the
Fisher-radius certificate at radius `r` is positive, then with probability at least
`1 − τ_{θ₀}(D)/(n r²)` the empirical mean lies in the local chart at `θ₀` and its response moves
across the wall `ℓ` in the direction of the truth shift. -/
theorem measureReal_sign_certified_ge (θ₀ : 𝕍) (p : (J → ℝ) →ₗ[ℝ] 𝕍)
    (hp : ∀ w : 𝕍, p (w : J → ℝ) = w) {c : ℝ} (hc : 0 < c)
    (hcoer : ∀ v : 𝕍, c * ‖v‖ ^ 2 ≤ G θ₀ v v) {δ K : ℝ} (hK : 0 ≤ K)
    (hrem : ∀ z : 𝕍, ‖z‖ ≤ δ →
      ‖θr (mean (θ₀ : J → ℝ) + (z : J → ℝ)) - θ₀ - (CDE θ₀).symm z‖ ≤ K * ‖z‖ ^ 2)
    (ℓ : 𝕍 →L[ℝ] ℝ) (e : 𝕍) (t r : ℝ) (hr : 0 < r)
    (hmean : (fun j ↦ ∫ x, S j x ∂D) = mean (θ₀ : J → ℝ) + t • (e : J → ℝ))
    (hδ : |t| * ‖e‖ + ‖(CD θ₀ : 𝕍 →L[ℝ] 𝕍)‖ / Real.sqrt c * r ≤ δ)
    (hcert : 0 < t * ℓ (((CDE θ₀).symm : 𝕍 →L[ℝ] 𝕍) e) - ‖ℓ‖ / Real.sqrt c * r -
      ‖ℓ‖ * K * (|t| * ‖e‖ + ‖(CD θ₀ : 𝕍 →L[ℝ] 𝕍)‖ / Real.sqrt c * r) ^ 2)
    {n : ℕ} (hn : 0 < n) :
    1 - -(∑ a, ∑ b, samplingOp hS ν θ₀ p (Pi.single b 1) a * lawCov D (S a) (S b)) / n / r ^ 2 ≤
      P.real {ω | ℓ θ₀ < ℓ (θr (sampleResponse S Xs n ω))} := by
  -- the certified event contains the small-energy event, almost surely
  have hsub : {ω | samplingEnergy hS ν θ₀ p
      (fun j ↦ sampleResponse S Xs n ω j - ∫ x, S j x ∂D) < r ^ 2} ≤ᵐ[P]
      {ω | ℓ θ₀ < ℓ (θr (sampleResponse S Xs n ω))} := by
    filter_upwards [ae_sampleResponse_sub_mem_dirSpan hS ν P D hDν Xs hXm hid hlaw hn] with ω hω hlt
    set ξ : 𝕍 := ⟨fun j ↦ sampleResponse S Xs n ω j - ∫ x, S j x ∂D, hω⟩ with hξ
    have hE : meanNoiseEnergy hS ν θ₀ ξ ≤ r ^ 2 := by
      rw [← meanNoiseEnergy_eq_samplingEnergy hS ν θ₀ p hp ξ]
      exact le_of_lt hlt
    have h := twoScale_sign_certificate_fisher hS ν θ₀ hc hcoer hK hrem ℓ e ξ t r hr.le hE hδ
    have hpt : sampleResponse S Xs n ω = mean (θ₀ : J → ℝ) + ((t • e + ξ : 𝕍) : J → ℝ) := by
      rw [Submodule.coe_add, Submodule.coe_smul, hξ]
      funext j
      simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
      have := congrFun hmean j
      simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul] at this
      linarith
    change ℓ θ₀ < ℓ (θr (sampleResponse S Xs n ω))
    rw [hpt]
    linarith
  have hcompl : {ω | ℓ θ₀ < ℓ (θr (sampleResponse S Xs n ω))}ᶜ ≤ᵐ[P]
      {ω | r ^ 2 ≤ samplingEnergy hS ν θ₀ p
        (fun j ↦ sampleResponse S Xs n ω j - ∫ x, S j x ∂D)} := by
    filter_upwards [hsub] with ω hω hnot
    by_contra hlt
    exact hnot (hω (lt_of_not_ge hlt))
  have h1 : P.real {ω | ℓ θ₀ < ℓ (θr (sampleResponse S Xs n ω))}ᶜ ≤
      P.real {ω | r ^ 2 ≤ samplingEnergy hS ν θ₀ p
        (fun j ↦ sampleResponse S Xs n ω j - ∫ x, S j x ∂D)} := by
    rw [measureReal_def, measureReal_def]
    exact ENNReal.toReal_mono (measure_ne_top _ _) (measure_mono_ae hcompl)
  have h2 := measureReal_samplingEnergy_ge_le hS ν P D hDν Xs hXm hid hlaw hind θ₀ p hp hn hr
  have h3 : (1 : ℝ) ≤ P.real {ω | ℓ θ₀ < ℓ (θr (sampleResponse S Xs n ω))} +
      P.real {ω | ℓ θ₀ < ℓ (θr (sampleResponse S Xs n ω))}ᶜ := by
    have := measureReal_union_le (μ := P) {ω | ℓ θ₀ < ℓ (θr (sampleResponse S Xs n ω))}
      {ω | ℓ θ₀ < ℓ (θr (sampleResponse S Xs n ω))}ᶜ
    rwa [Set.union_compl_self, probReal_univ] at this
  linarith

end Probabilistic

end Laplace.Multi
