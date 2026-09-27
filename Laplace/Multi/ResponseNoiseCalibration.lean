/-
Copyright (c) 2026 Timaeus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Timaeus
-/
import Laplace.Multi.FisherNormalisedSampling
import Laplace.Multi.ResponseBilinearForm
import Laplace.Multi.TangentPythagoras
import Laplace.Multi.DataRayBlocks
import Laplace.Multi.ExtremeMeanSupport

/-!
# Noise calibration: the effective dimension under covariance mismatch

The Fisher form `⟪u, v⟫_θ = Cov_{P_θ}(⟨u,S⟩, ⟨v,S⟩)` is an inner product on the direction space
(`fisherCore`), so `W` has a Fisher-orthonormal basis. In such a basis the Fisher-normalised
sampling energy is `q_θ(z) = ∑_i ⟨e_i, z⟩²` on `W`, and for any data law `D ≪ ν` the effective
dimension `d_eff(D) = tr(R_θ C_D)` of the sampling noise is the sum of the data variances of the
basis contrasts:

`d_eff(D) = ∑_i Var_D⟨e_i, S⟩`   (`effDim_eq_sum_lawCov`).

Hence a covariance comparison `Var_D⟨w,S⟩ ≤ κ Var_{P_θ}⟨w,S⟩` gives `d_eff(D) ≤ κ dim W`
(`effDim_le_of_relCov`): the sampling floor `√(d_eff/n)` of the structural coordinate is at most
`√(κ dim W / n)`, with equality `dim W` at matching. The largest covariance-mismatch factor
controls both the differential amplification of the response and its sampling noise.
-/

open MeasureTheory Filter Topology Set

namespace Laplace.Multi

section Form

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

omit hS in
variable (S) in
/-- **The Fisher form at `θ` on the direction space**: `⟪u, v⟫_θ = Cov_{P_θ}(⟨u,S⟩, ⟨v,S⟩)`. -/
noncomputable def fisherInner (θ u v : 𝕍) : ℝ :=
  lawCov (familyMeasure ν (fun _ ↦ (1 : ℝ)) (fun _ ↦ (0 : ℝ)) S 1 (θ : J → ℝ))
    (dirLoss S (u : J → ℝ)) (dirLoss S (v : J → ℝ))

omit [Nonempty X] [Nonempty J] hS [IsProbabilityMeasure ν] in
theorem fisherInner_self (θ v : 𝕍) :
    fisherInner S ν θ v v = fisherVar S ν (θ : J → ℝ) (v : J → ℝ) := rfl

omit [Nonempty J] in
theorem fisherInner_comm (θ u v : 𝕍) : fisherInner S ν θ u v = fisherInner S ν θ v u := by
  have := isProbabilityMeasure_family hS ν (θ : J → ℝ)
  exact lawCov_comm _ _ _

omit [Nonempty J] in
theorem fisherInner_add_left (θ u u' v : 𝕍) :
    fisherInner S ν θ (u + u') v = fisherInner S ν θ u v + fisherInner S ν θ u' v := by
  have := isProbabilityMeasure_family hS ν (θ : J → ℝ)
  unfold fisherInner
  rw [Submodule.coe_add, dirLoss_add,
    lawCov_add_left_eq _ (bdd_dirLoss hS _) (bdd_dirLoss hS _) (bdd_dirLoss hS _)]

omit [Nonempty X] [Nonempty J] hS [IsProbabilityMeasure ν] in
theorem fisherInner_smul_left (θ : 𝕍) (r : ℝ) (u v : 𝕍) :
    fisherInner S ν θ (r • u) v = r * fisherInner S ν θ u v := by
  unfold fisherInner
  rw [Submodule.coe_smul, dirLoss_smul, lawCov_const_mul_left_eq]

/-- The Fisher form is the pairing against the chart derivative. -/
theorem fisherInner_eq_neg_dotJ (θ u v : 𝕍) :
    fisherInner S ν θ u v = -dotJ (u : J → ℝ) (CD θ v : J → ℝ) := by
  rw [dotJ_chartDeriv_eq_neg_lawCov hS ν θ u v, neg_neg]
  rfl

/-- `⟪u, (Dm(θ)|_W)⁻¹ z⟫_θ = −⟨u, z⟩` for `z ∈ W`. -/
theorem fisherInner_chartDerivEquiv_symm (θ u : 𝕍) {z : J → ℝ} (hz : z ∈ 𝕍) :
    fisherInner S ν θ u ((CDE θ).symm ⟨z, hz⟩) = -dotJ (u : J → ℝ) z := by
  rw [fisherInner_eq_neg_dotJ hS ν]
  congr 2
  exact meanMapDeriv_chartDerivEquiv_symm hS ν θ ⟨z, hz⟩

/-- **The Fisher form is an inner product on the direction space.** -/
@[instance_reducible]
noncomputable def fisherCore (θ : 𝕍) : InnerProductSpace.Core ℝ 𝕍 where
  inner u v := fisherInner S ν θ u v
  conj_inner_symm x y := by
    simp only [conj_trivial]
    exact fisherInner_comm hS ν θ _ _
  re_inner_nonneg x := by
    simp only [RCLike.re_to_real]
    exact fisherVar_nonneg hS ν _ _
  add_left x y z := fisherInner_add_left hS ν θ x y z
  smul_left x y r := by
    simp only [conj_trivial]
    exact fisherInner_smul_left ν θ r x y
  definite x hx := by
    by_contra h
    exact (fisherVar_pos_of_ne_zero hS ν θ h).ne' hx

variable (S) in
/-- **The direction space with the Fisher inner product at `θ`** (a type synonym, so that the
Fisher inner product does not collide with the ambient sup norm). -/
def FisherSpace (_hS : ∀ j, Bdd (S j)) (_θ : 𝕍) : Type _ := 𝕍

instance (θ : 𝕍) : AddCommGroup (FisherSpace S ν hS θ) := inferInstanceAs (AddCommGroup 𝕍)

instance (θ : 𝕍) : Module ℝ (FisherSpace S ν hS θ) := inferInstanceAs (Module ℝ 𝕍)

noncomputable instance (θ : 𝕍) : InnerProductSpace.Core ℝ (FisherSpace S ν hS θ) :=
  fisherCore hS ν θ

noncomputable instance (θ : 𝕍) : NormedAddCommGroup (FisherSpace S ν hS θ) :=
  { InnerProductSpace.Core.toNormedAddCommGroup (𝕜 := ℝ) (F := FisherSpace S ν hS θ) with
    toAddCommGroup := inferInstanceAs (AddCommGroup 𝕍) }

noncomputable instance (θ : 𝕍) : InnerProductSpace ℝ (FisherSpace S ν hS θ) :=
  { InnerProductSpace.ofCore (fisherCore hS ν θ).toCore with
    toModule := inferInstanceAs (Module ℝ 𝕍) }

set_option linter.unusedFintypeInType false in
instance (θ : 𝕍) : FiniteDimensional ℝ (FisherSpace S ν hS θ) :=
  inferInstanceAs (FiniteDimensional ℝ 𝕍)

/-- The underlying direction of a Fisher-space vector. -/
def ofFisher (θ : 𝕍) (u : FisherSpace S ν hS θ) : 𝕍 := u

/-- A direction as a Fisher-space vector. -/
def toFisher (θ : 𝕍) (u : 𝕍) : FisherSpace S ν hS θ := u

theorem inner_fisherSpace (θ : 𝕍) (u v : FisherSpace S ν hS θ) :
    inner ℝ u v = fisherInner S ν θ (ofFisher hS ν θ u) (ofFisher hS ν θ v) := rfl

omit [Nonempty X] [Fintype J] [Nonempty J] [IsProbabilityMeasure ν] in
theorem ofFisher_toFisher (θ u : 𝕍) : ofFisher hS ν θ (toFisher hS ν θ u) = u := rfl

/-- **The effective dimension is the sum of the data variances of a Fisher-orthonormal basis**,
and is at most `κ dim W` under the covariance comparison `Var_D⟨w,S⟩ ≤ κ Var_{P_θ}⟨w,S⟩`. -/
theorem effDim_le_of_relCov [DecidableEq J] (θ : 𝕍) (p : (J → ℝ) →ₗ[ℝ] 𝕍)
    (hp : ∀ w : 𝕍, p (w : J → ℝ) = w) (D : Measure X) [IsProbabilityMeasure D] (hDν : D ≪ ν)
    {κ : ℝ} (hκ : ∀ w : J → ℝ, lawCov D (dirLoss S w) (dirLoss S w) ≤
      κ * fisherVar S ν (θ : J → ℝ) w) :
    -(∑ a, ∑ b, samplingOp hS ν θ p (Pi.single b 1) a * lawCov D (S a) (S b)) ≤
      κ * (Module.finrank ℝ 𝕍 : ℝ) := by
  classical
  obtain ⟨e, hedef⟩ : ∃ e : OrthonormalBasis (Fin (Module.finrank ℝ (FisherSpace S ν hS θ))) ℝ
      (FisherSpace S ν hS θ), e = stdOrthonormalBasis ℝ (FisherSpace S ν hS θ) := ⟨_, rfl⟩
  have hrank : Module.finrank ℝ (FisherSpace S ν hS θ) = Module.finrank ℝ 𝕍 := rfl
  -- the sampling energy on `W` in the orthonormal basis
  have hq : ∀ z ∈ 𝕍, samplingEnergy hS ν θ p z =
      ∑ i, dotJ (ofFisher hS ν θ (e i) : J → ℝ) z ^ 2 := by
    intro z hz
    have h1 : samplingEnergy hS ν θ p z = inner ℝ (toFisher hS ν θ ((CDE θ).symm ⟨z, hz⟩))
        (toFisher hS ν θ ((CDE θ).symm ⟨z, hz⟩)) := by
      rw [samplingEnergy_eq_fisherVar hS ν θ p hp hz, ← fisherInner_self]
      rfl
    rw [h1, real_inner_self_eq_norm_sq, ← e.sum_sq_inner_right]
    refine Finset.sum_congr rfl fun i _ ↦ ?_
    rw [inner_fisherSpace, ofFisher_toFisher, fisherInner_chartDerivEquiv_symm hS ν θ _ hz, neg_sq]
  -- the data mean and the a.e. membership of the centred statistic
  obtain ⟨m, hmdef⟩ : ∃ m : J → ℝ, m = fun i ↦ ∫ x, S i x ∂D := ⟨_, rfl⟩
  have hmB : m ∈ momentBody ν (fun _ ↦ (1 : ℝ)) S := by
    rw [hmdef]
    exact mean_mem_momentBody_of_ac hS ν D hDν
  have hae : ∀ᵐ x ∂D, statPoint S x - m ∈ 𝕍 := ae_statPoint_sub_mem_dirSpan hS ν D hDν hmB
  have hbdd : ∀ a, Bdd fun x ↦ (statPoint S x - m) a := fun a ↦ by
    have : (fun x ↦ (statPoint S x - m) a) = fun x ↦ S a x - m a := funext fun x ↦ rfl
    rw [this]
    exact (hS a).sub (Bdd.const _)
  -- the effective dimension is the mean sampling energy of the centred statistic
  have h2 : -(∑ a, ∑ b, samplingOp hS ν θ p (Pi.single b 1) a * lawCov D (S a) (S b)) =
      ∫ x, samplingEnergy hS ν θ p (statPoint S x - m) ∂D := by
    have e1 : ∀ x, samplingEnergy hS ν θ p (statPoint S x - m) =
        ∑ a, ∑ b, (-samplingOp hS ν θ p (Pi.single b 1) a) *
          ((statPoint S x - m) b * (statPoint S x - m) a) := fun x ↦ by
      rw [samplingEnergy, dotJ_samplingOp_eq, ← Finset.sum_neg_distrib]
      refine Finset.sum_congr rfl fun a _ ↦ ?_
      rw [← Finset.sum_neg_distrib]
      refine Finset.sum_congr rfl fun b _ ↦ ?_
      ring
    simp_rw [e1]
    rw [integral_finsetSum _ fun a _ ↦ integrable_finsetSum _ fun b _ ↦
      (integrable_of_bdd_prob D ((hbdd b).mul (hbdd a))).const_mul _]
    simp_rw [integral_finsetSum _ fun b _ ↦
      (integrable_of_bdd_prob D ((hbdd b).mul (hbdd _))).const_mul _, integral_const_mul]
    rw [← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun a _ ↦ ?_
    rw [← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun b _ ↦ ?_
    rw [lawCov_eq_integral_centred D (hS a) (hS b)]
    have e2 : ∫ x, (statPoint S x - m) b * (statPoint S x - m) a ∂D =
        ∫ x, (S a x - ∫ y, S a y ∂D) * (S b x - ∫ y, S b y ∂D) ∂D :=
      integral_congr_ae (Eventually.of_forall fun x ↦ by
        simp only [statPoint, Pi.sub_apply, hmdef]
        ring)
    rw [e2]
    ring
  -- the basis contrasts
  have hrw : ∀ i x, dotJ (ofFisher hS ν θ (e i) : J → ℝ) (statPoint S x - m) =
      dirLoss S (ofFisher hS ν θ (e i) : J → ℝ) x - dotJ (ofFisher hS ν θ (e i) : J → ℝ) m :=
    fun i x ↦ by rw [(isLinearMap_dotJ _).map_sub, dirLoss_eq_dotJ_statPoint]
  have hbi : ∀ i, Bdd fun x ↦ dirLoss S (ofFisher hS ν θ (e i) : J → ℝ) x -
      dotJ (ofFisher hS ν θ (e i) : J → ℝ) m := fun i ↦ (bdd_dirLoss hS _).sub (Bdd.const _)
  have h3 : ∫ x, samplingEnergy hS ν θ p (statPoint S x - m) ∂D =
      ∑ i, lawCov D (dirLoss S (ofFisher hS ν θ (e i) : J → ℝ))
        (dirLoss S (ofFisher hS ν θ (e i) : J → ℝ)) := by
    rw [integral_congr_ae (hae.mono fun x hx ↦ hq _ hx)]
    simp_rw [hrw]
    rw [integral_finsetSum _ fun i _ ↦ by
      simpa [sq] using integrable_of_bdd_prob D ((hbi i).mul (hbi i))]
    refine Finset.sum_congr rfl fun i _ ↦ ?_
    rw [lawCov_eq_integral_centred D (bdd_dirLoss hS _) (bdd_dirLoss hS _),
      integral_dirLoss_eq_dotJ (ofFisher hS ν θ (e i) : J → ℝ) D hS, ← hmdef]
    exact integral_congr_ae (Eventually.of_forall fun x ↦ by ring)
  -- each basis variance is at most `κ`
  have hone : ∀ i, fisherVar S ν (θ : J → ℝ) (ofFisher hS ν θ (e i) : J → ℝ) = 1 := fun i ↦ by
    rw [← fisherInner_self, ← inner_fisherSpace, real_inner_self_eq_norm_sq, e.orthonormal.1 i,
      one_pow]
  rw [h2, h3]
  calc ∑ i, lawCov D (dirLoss S (ofFisher hS ν θ (e i) : J → ℝ))
        (dirLoss S (ofFisher hS ν θ (e i) : J → ℝ)) ≤
        ∑ i, κ * fisherVar S ν (θ : J → ℝ) (ofFisher hS ν θ (e i) : J → ℝ) :=
        Finset.sum_le_sum fun i _ ↦ hκ _
    _ = ∑ _i : Fin (Module.finrank ℝ (FisherSpace S ν hS θ)), κ * 1 := by simp only [hone]
    _ = κ * (Module.finrank ℝ 𝕍 : ℝ) := by
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, mul_one, hrank,
          mul_comm]

end Form

end Laplace.Multi
