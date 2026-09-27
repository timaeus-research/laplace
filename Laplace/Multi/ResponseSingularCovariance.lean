/-
Copyright (c) 2026 Timaeus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Timaeus
-/
import Laplace.Multi.ResponseMismatchResolution

/-!
# Singular data covariance: accessible and noiseless response directions

Off the model the data covariance form `Σ_D` on the direction space `W` may be singular even at
an interior mean (a law concentrated on a single feature value has an interior mean and zero
covariance). The correct geometry is that of the **covariance kernel**
`N = {u ∈ W | Σ_D(u, u) = 0}` (`dataKer`, the directions whose feature is `D`-a.s. constant) and
its annihilator:

* the form descends to a nondegenerate form on `W/N` (`quotBilin`, `quotBilin_nondegenerate`), so
  every displacement `e` annihilated by `N` has a **covariance dual** `e* ∈ W` with
  `Σ_D(e*, u) = ⟨u, e⟩` for all `u` (`dataDualSing`, `dataBilin_dataDualSing`);
* **finite optimal signal-to-noise on the annihilator** (`isGreatest_snr_sing`):
  `sup_{Σ_D(u,u) ≤ 1} ⟨u, e⟩² = Σ_D(e*, e*) = ⟨e, Σ_D⁺ e⟩`;
* **noiseless witnesses off the annihilator** (`not_bddAbove_snr_of_not_annihilator`): if some
  `u ∈ N` has `⟨u, e⟩ ≠ 0`, the signal-to-noise ratios are unbounded — a displacement with a
  component along a `D`-a.s. constant feature is detected without noise, and is not a regular local
  alternative through `D`;
* **minimum-information lifts exist exactly on the annihilator** (`annihilator_of_lift`,
  `isLeast_information_lift_sing`): a bounded score `h` with `Cov_D(⟨u,S⟩, h) = ⟨u, e⟩` for all
  `u ∈ W` forces `⟨u, e⟩ = 0` on `N`, and conversely on the annihilator the least variance of such a
  lift is `Σ_D(e*, e*)`, attained at `⟨e*, S⟩`.
-/

open MeasureTheory

namespace Laplace.Multi

section Singular

variable {X : Type*} [MeasurableSpace X] [Nonempty X] {J : Type*} [Fintype J] [Nonempty J]
  {S : J → X → ℝ} (hS : ∀ j, Bdd (S j)) (ν : Measure X) [IsProbabilityMeasure ν]
  (D : Measure X) [IsProbabilityMeasure D]
include hS

/-- The direction space. -/
local notation "𝕍" => dirSpan ν (fun _ ↦ (1 : ℝ)) S

/-- **The covariance kernel**: the directions with `D`-a.s. constant feature, `Σ_D(u, ·) = 0`. -/
noncomputable def dataKer : Submodule ℝ 𝕍 := LinearMap.ker (dataBilin hS ν D)

omit [Nonempty X] [Nonempty J] [IsProbabilityMeasure ν] in
theorem mem_dataKer_iff (u : 𝕍) : u ∈ dataKer hS ν D ↔ dataBilin hS ν D u u = 0 := by
  constructor
  · intro hu
    have : dataBilin hS ν D u = 0 := hu
    rw [this, LinearMap.zero_apply]
  · intro hu
    change dataBilin hS ν D u = 0
    ext v
    have hcs := dataBilin_sq_le hS ν D u v
    rw [hu, zero_mul] at hcs
    rw [LinearMap.zero_apply]
    exact pow_eq_zero_iff (n := 2) (by norm_num) |>.1 (le_antisymm hcs (sq_nonneg _))

omit [Nonempty X] [Nonempty J] [IsProbabilityMeasure ν] in
theorem dataBilin_eq_zero_of_mem_dataKer {u : 𝕍} (hu : u ∈ dataKer hS ν D) (v : 𝕍) :
    dataBilin hS ν D u v = 0 := by
  have : dataBilin hS ν D u = 0 := hu
  rw [this, LinearMap.zero_apply]

omit [Nonempty X] [Nonempty J] [IsProbabilityMeasure ν] in
theorem dataKer_le_ker : dataKer hS ν D ≤ LinearMap.ker (dataBilin hS ν D) := fun _ hu ↦ hu

/-- The quotient of the direction space by the covariance kernel. -/
local notation "Q" => 𝕍 ⧸ dataKer hS ν D

omit [Nonempty X] [Nonempty J] [IsProbabilityMeasure ν] in
theorem dataKer_le_ker_flip :
    dataKer hS ν D ≤ LinearMap.ker
      ((dataKer hS ν D).liftQ (dataBilin hS ν D) (dataKer_le_ker hS ν D)).flip := by
  intro u hu
  rw [LinearMap.mem_ker]
  ext v
  simp only [LinearMap.flip_apply, LinearMap.comp_apply, Submodule.mkQ_apply,
    LinearMap.zero_apply]
  change dataBilin hS ν D v u = 0
  rw [dataBilin_comm]
  exact dataBilin_eq_zero_of_mem_dataKer hS ν D hu v

/-- **The descended covariance form** on `W/N`. -/
noncomputable def quotBilin : LinearMap.BilinForm ℝ Q :=
  ((dataKer hS ν D).liftQ ((dataKer hS ν D).liftQ (dataBilin hS ν D) (dataKer_le_ker hS ν D)).flip
    (dataKer_le_ker_flip hS ν D)).flip

omit [Nonempty X] [Nonempty J] [IsProbabilityMeasure ν] in
theorem quotBilin_mk (u v : 𝕍) :
    quotBilin hS ν D (Submodule.Quotient.mk u) (Submodule.Quotient.mk v) =
      dataBilin hS ν D u v := rfl

omit [Nonempty X] [Nonempty J] [IsProbabilityMeasure ν] in
theorem quotBilin_comm (q r : Q) : quotBilin hS ν D q r = quotBilin hS ν D r q := by
  induction q using Submodule.Quotient.induction_on with
  | H u =>
    induction r using Submodule.Quotient.induction_on with
    | H v => rw [quotBilin_mk, quotBilin_mk, dataBilin_comm]

omit [Nonempty X] [Nonempty J] [IsProbabilityMeasure ν] in
/-- The descended form is nondegenerate. -/
theorem quotBilin_nondegenerate : (quotBilin hS ν D).Nondegenerate := by
  have hrefl : (quotBilin hS ν D).IsRefl := fun q r h ↦ by
    rw [quotBilin_comm] at h
    exact h
  refine hrefl.nondegenerate_iff_separatingLeft.2 fun q hq ↦ ?_
  induction q using Submodule.Quotient.induction_on with
  | H u =>
    rw [Submodule.Quotient.mk_eq_zero]
    change dataBilin hS ν D u = 0
    ext v
    rw [LinearMap.zero_apply, ← quotBilin_mk hS ν D]
    exact hq _

omit [Nonempty X] [Nonempty J] hS [IsProbabilityMeasure ν] in
/-- The pairing functional `u ↦ ⟨u, e⟩` on the direction space. -/
noncomputable def pairFunctional (e : J → ℝ) : Module.Dual ℝ 𝕍 :=
  (pairCLM ν e : 𝕍 →L[ℝ] ℝ).toLinearMap

omit [Nonempty X] [Nonempty J] hS [IsProbabilityMeasure ν] in
theorem pairFunctional_apply (e : J → ℝ) (u : 𝕍) :
    pairFunctional ν e u = dotJ (u : J → ℝ) e := by
  rw [pairFunctional, ContinuousLinearMap.coe_coe, pairCLM_apply, dotJ_comm]

omit [Nonempty X] [Nonempty J] [IsProbabilityMeasure ν] in
/-- A displacement annihilated by the kernel descends to a functional on `W/N`. -/
theorem dataKer_le_ker_pairFunctional {e : J → ℝ}
    (he : ∀ u ∈ dataKer hS ν D, dotJ (u : J → ℝ) e = 0) :
    dataKer hS ν D ≤ LinearMap.ker (pairFunctional ν e) := fun u hu ↦ by
  rw [LinearMap.mem_ker, pairFunctional_apply]
  exact he u hu

/-- **The covariance dual of an annihilated displacement**: a representative in `W` of the
Riesz representative of `⟨·, e⟩` on `W/N`, so `Σ_D(e*, u) = ⟨u, e⟩` for every `u`. -/
noncomputable def dataDualSing {e : J → ℝ} (he : ∀ u ∈ dataKer hS ν D, dotJ (u : J → ℝ) e = 0) :
    𝕍 :=
  Quotient.out (((quotBilin hS ν D).toDual (quotBilin_nondegenerate hS ν D)).symm
    ((dataKer hS ν D).liftQ (pairFunctional ν e) (dataKer_le_ker_pairFunctional hS ν D he)))

omit [Nonempty X] [Nonempty J] [IsProbabilityMeasure ν] in
/-- The defining property of the singular covariance dual. -/
theorem dataBilin_dataDualSing {e : J → ℝ} (he : ∀ u ∈ dataKer hS ν D, dotJ (u : J → ℝ) e = 0)
    (u : 𝕍) : dataBilin hS ν D (dataDualSing hS ν D he) u = dotJ (u : J → ℝ) e := by
  have h := LinearMap.BilinForm.apply_toDual_symm_apply (B := quotBilin hS ν D)
    (hB := quotBilin_nondegenerate hS ν D)
    ((dataKer hS ν D).liftQ (pairFunctional ν e) (dataKer_le_ker_pairFunctional hS ν D he))
    (Submodule.Quotient.mk u)
  rw [Submodule.liftQ_apply, pairFunctional_apply] at h
  rw [← h, ← quotBilin_mk hS ν D]
  congr 2
  exact Submodule.Quotient.mk_out (((quotBilin hS ν D).toDual (quotBilin_nondegenerate hS ν D)).symm
    ((dataKer hS ν D).liftQ (pairFunctional ν e) (dataKer_le_ker_pairFunctional hS ν D he)))

omit [Nonempty X] [Nonempty J] [IsProbabilityMeasure ν] in
theorem dataBilin_dataDualSing_self {e : J → ℝ}
    (he : ∀ u ∈ dataKer hS ν D, dotJ (u : J → ℝ) e = 0) :
    dataBilin hS ν D (dataDualSing hS ν D he) (dataDualSing hS ν D he) =
      dotJ (dataDualSing hS ν D he : J → ℝ) e :=
  dataBilin_dataDualSing hS ν D he _

omit [Nonempty X] [Nonempty J] [IsProbabilityMeasure ν] in
/-- `⟨u, e⟩² ≤ Σ_D(u, u) · Σ_D(e*, e*)` on the annihilator. -/
theorem sq_dotJ_le_dataBilin_mul_sing {e : J → ℝ}
    (he : ∀ u ∈ dataKer hS ν D, dotJ (u : J → ℝ) e = 0) (u : 𝕍) :
    dotJ (u : J → ℝ) e ^ 2 ≤ dataBilin hS ν D u u *
      dataBilin hS ν D (dataDualSing hS ν D he) (dataDualSing hS ν D he) := by
  rw [← dataBilin_dataDualSing hS ν D he u, dataBilin_comm hS ν D]
  exact dataBilin_sq_le hS ν D u _

omit [Nonempty X] [Nonempty J] [IsProbabilityMeasure ν] in
/-- **Finite optimal signal-to-noise on the annihilator**:
`sup_{Σ_D(u,u) ≤ 1} ⟨u, e⟩² = Σ_D(e*, e*)`, attained. -/
theorem isGreatest_snr_sing {e : J → ℝ} (he : ∀ u ∈ dataKer hS ν D, dotJ (u : J → ℝ) e = 0) :
    IsGreatest {r | ∃ u : 𝕍, dataBilin hS ν D u u ≤ 1 ∧ r = dotJ (u : J → ℝ) e ^ 2}
      (dataBilin hS ν D (dataDualSing hS ν D he) (dataDualSing hS ν D he)) := by
  set σ2 := dataBilin hS ν D (dataDualSing hS ν D he) (dataDualSing hS ν D he) with hσ2
  have hσ0 : 0 ≤ σ2 := dataBilin_self_nonneg hS ν D _
  constructor
  · rcases eq_or_lt_of_le hσ0 with h0 | hpos
    · refine ⟨0, by simp, ?_⟩
      rw [Submodule.coe_zero]
      simp only [dotJ, Pi.zero_apply, zero_mul, Finset.sum_const_zero, ne_eq, OfNat.ofNat_ne_zero,
        not_false_eq_true, zero_pow]
      exact h0.symm
    · refine ⟨(Real.sqrt σ2)⁻¹ • dataDualSing hS ν D he, ?_, ?_⟩
      · simp only [map_smul, LinearMap.smul_apply, smul_eq_mul]
        rw [← hσ2, ← mul_assoc, ← sq, inv_pow, Real.sq_sqrt hσ0, inv_mul_cancel₀ hpos.ne']
      · rw [Submodule.coe_smul, dotJ_smul_left, mul_pow, inv_pow, Real.sq_sqrt hσ0,
          ← dataBilin_dataDualSing_self hS ν D he, ← hσ2, sq]
        field_simp
  · rintro r ⟨u, hu, rfl⟩
    calc dotJ (u : J → ℝ) e ^ 2 ≤ dataBilin hS ν D u u * σ2 :=
          sq_dotJ_le_dataBilin_mul_sing hS ν D he u
      _ ≤ 1 * σ2 := mul_le_mul_of_nonneg_right hu hσ0
      _ = σ2 := one_mul _

omit [Nonempty X] [Nonempty J] [IsProbabilityMeasure ν] in
/-- **Noiseless witnesses**: a displacement not annihilated by the covariance kernel has unbounded
signal-to-noise ratios. -/
theorem not_bddAbove_snr_of_not_annihilator {e : J → ℝ} {u₀ : 𝕍} (hu₀ : u₀ ∈ dataKer hS ν D)
    (hne : dotJ (u₀ : J → ℝ) e ≠ 0) :
    ¬ BddAbove {r | ∃ u : 𝕍, dataBilin hS ν D u u ≤ 1 ∧ r = dotJ (u : J → ℝ) e ^ 2} := by
  rintro ⟨M, hM⟩
  have hpos : 0 < dotJ (u₀ : J → ℝ) e ^ 2 := by positivity
  obtain ⟨t, ht⟩ := exists_nat_gt (M / dotJ (u₀ : J → ℝ) e ^ 2)
  have hmem : (t : ℝ) ^ 2 * dotJ (u₀ : J → ℝ) e ^ 2 ∈
      {r | ∃ u : 𝕍, dataBilin hS ν D u u ≤ 1 ∧ r = dotJ (u : J → ℝ) e ^ 2} := by
    refine ⟨(t : ℝ) • u₀, ?_, ?_⟩
    · simp only [map_smul, LinearMap.smul_apply, smul_eq_mul]
      rw [(mem_dataKer_iff hS ν D u₀).1 hu₀, mul_zero, mul_zero]
      exact zero_le_one
    · rw [Submodule.coe_smul, dotJ_smul_left, mul_pow]
  have h1 := hM hmem
  have h2 : M < (t : ℝ) ^ 2 * dotJ (u₀ : J → ℝ) e ^ 2 := by
    rw [div_lt_iff₀ hpos] at ht
    have hsq : (t : ℝ) ≤ (t : ℝ) ^ 2 := by
      have : t ≤ t ^ 2 := Nat.le_self_pow (by norm_num) t
      exact_mod_cast this
    have := mul_le_mul_of_nonneg_right hsq hpos.le
    linarith
  linarith

omit [Nonempty X] [Nonempty J] [IsProbabilityMeasure ν] in
/-- A score realising a response velocity annihilates the covariance kernel: kernel directions have
`D`-a.s. constant features, hence zero covariance with every bounded score. -/
theorem annihilator_of_lift {e : J → ℝ} {h : X → ℝ} (hh : Bdd h)
    (hcov : ∀ u : 𝕍, lawCov D (dirLoss S (u : J → ℝ)) h = dotJ (u : J → ℝ) e) :
    ∀ u ∈ dataKer hS ν D, dotJ (u : J → ℝ) e = 0 := by
  intro u hu
  rw [← hcov u]
  have hcs := lawCov_sq_le D (bdd_dirLoss hS (u : J → ℝ)) hh
  have h0 : lawCov D (dirLoss S (u : J → ℝ)) (dirLoss S (u : J → ℝ)) = 0 :=
    (mem_dataKer_iff hS ν D u).1 hu
  rw [h0, zero_mul] at hcs
  exact pow_eq_zero_iff (n := 2) (by norm_num) |>.1 (le_antisymm hcs (sq_nonneg _))

omit [Nonempty X] [Nonempty J] [IsProbabilityMeasure ν] in
/-- **The minimum-information lift on the annihilator**: the least variance of a bounded score
realising the response velocity `⟨·, e⟩` is `Σ_D(e*, e*)`, attained at `⟨e*, S⟩`. -/
theorem isLeast_information_lift_sing {e : J → ℝ}
    (he : ∀ u ∈ dataKer hS ν D, dotJ (u : J → ℝ) e = 0) :
    IsLeast {v | ∃ h : X → ℝ, Bdd h ∧
        (∀ u : 𝕍, lawCov D (dirLoss S (u : J → ℝ)) h = dotJ (u : J → ℝ) e) ∧
        v = lawCov D h h}
      (dataBilin hS ν D (dataDualSing hS ν D he) (dataDualSing hS ν D he)) := by
  constructor
  · refine ⟨dirLoss S (dataDualSing hS ν D he : J → ℝ), bdd_dirLoss hS _, fun u ↦ ?_, rfl⟩
    rw [← dataBilin_apply hS ν D, dataBilin_comm hS ν D, dataBilin_dataDualSing hS ν D he]
  · rintro v ⟨h, hh, hcov, rfl⟩
    have h1 : lawCov D (dirLoss S (dataDualSing hS ν D he : J → ℝ)) h =
        dataBilin hS ν D (dataDualSing hS ν D he) (dataDualSing hS ν D he) := by
      rw [hcov, dataBilin_dataDualSing_self hS ν D he]
    have hcs := lawCov_sq_le D (bdd_dirLoss hS (dataDualSing hS ν D he : J → ℝ)) hh
    rw [h1, ← dataBilin_apply hS ν D] at hcs
    rcases eq_or_lt_of_le (dataBilin_self_nonneg hS ν D (dataDualSing hS ν D he)) with h0 | hpos
    · rw [← h0]
      exact lawCov_self_nonneg D hh
    · rw [sq] at hcs
      exact le_of_mul_le_mul_left hcs hpos

end Singular

end Laplace.Multi
