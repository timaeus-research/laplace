/-
Copyright (c) 2026 Timaeus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Timaeus
-/
import Laplace.Multi.FisherCompletionLaws
import Laplace.Multi.NormalTiltFisherComparison
import Laplace.Multi.FisherCauchyRealisation
import Laplace.Multi.PolyhedralCompletion

/-!
# Face mass under Hellinger control, and translated short paths

The square root of the mass of a measurable set `A` is `1`-Lipschitz for the Hellinger
distance: `|√P_θ(A) − √P_η(A)| ≤ H(θ, η)`, as the `L²(ν.restrict A)` norm of the root
densities. Along a Fisher path this keeps the face mass bounded below by
`√P_{γ 0}(A) − ½ length`, so **a short path starting near face mass one stays in
`P(A) ≥ 1/4`**, and by the normal-tilt comparison its translate by a normal-cone vector
`b` has at most twice its length. This is the middle side of the normal-cone coalescence
grid.
-/

open MeasureTheory Filter Topology Set Real

namespace Laplace.Multi

section Mass

variable {X : Type*} [MeasurableSpace X] [Nonempty X] {J : Type*} [Fintype J]
  {S : J → X → ℝ} (hS : ∀ j, Bdd (S j)) (ν : Measure X) [IsProbabilityMeasure ν]
include hS

/-- The family of tilts. -/
local notation "Pfam" => familyMeasure ν (fun _ ↦ (1 : ℝ)) (fun _ ↦ (0 : ℝ)) S 1

omit [Nonempty X] in
/-- The mass of `A` is the `L²(ν.restrict A)` norm squared of the root density. -/
theorem real_family_eq_integral_rootDens_mul_self (θ : J → ℝ) {A : Set X}
    (hA : MeasurableSet A) :
    (Pfam θ).real A = ∫ x in A, rootDens S ν θ x * rootDens S ν θ x ∂ν := by
  rw [familyMeasure_eq_withDensity_famDens,
    measureReal_withDensity_ofReal ν (famDens_nonneg hS ν θ) (integrable_famDens hS ν θ) hA]
  exact setIntegral_congr_fun hA fun x _ ↦ by rw [← sq, rootDens_sq hS ν]

omit [Nonempty X] in
/-- **Root face mass is Hellinger-Lipschitz**: `|√P_θ(A) − √P_η(A)| ≤ H(θ, η)`. -/
theorem abs_sqrt_real_sub_le_hellingerDist (θ η : J → ℝ) {A : Set X} (hA : MeasurableSet A) :
    |√((Pfam θ).real A) - √((Pfam η).real A)| ≤ hellingerDist S ν θ η := by
  have hf : MemLp (rootDens S ν θ) 2 (ν.restrict A) := (memLp_rootDens hS ν θ).restrict A
  have hg : MemLp (rootDens S ν η) 2 (ν.restrict A) := (memLp_rootDens hS ν η).restrict A
  have hnf : √((Pfam θ).real A) = ‖hf.toLp _‖ := by
    rw [real_family_eq_integral_rootDens_mul_self hS ν θ hA, ← norm_toLp_sq (ν.restrict A) hf,
      Real.sqrt_sq (norm_nonneg _)]
  have hng : √((Pfam η).real A) = ‖hg.toLp _‖ := by
    rw [real_family_eq_integral_rootDens_mul_self hS ν η hA, ← norm_toLp_sq (ν.restrict A) hg,
      Real.sqrt_sq (norm_nonneg _)]
  rw [hnf, hng]
  refine (abs_norm_sub_norm_le _ _).trans ?_
  rw [← MemLp.toLp_sub, ← Real.sqrt_sq (norm_nonneg _), norm_toLp_sq (ν.restrict A), hellingerDist]
  refine Real.sqrt_le_sqrt (setIntegral_le_integral ?_ (Eventually.of_forall fun x ↦ ?_))
  · have hb : Bdd fun x ↦ rootDens S ν θ x - rootDens S ν η x :=
      (bdd_rootDens hS ν θ).sub (bdd_rootDens hS ν η)
    exact integrable_of_bdd_prob ν (hb.mul hb)
  · exact mul_self_nonneg _

end Mass

section Paths

variable {X : Type*} [MeasurableSpace X] [Nonempty X] {J : Type*} [Fintype J]
  {S : J → X → ℝ} (hS : ∀ j, Bdd (S j)) (ν : Measure X) [IsProbabilityMeasure ν]
include hS

/-- The family of tilts. -/
local notation "Pfam" => familyMeasure ν (fun _ ↦ (1 : ℝ)) (fun _ ↦ (0 : ℝ)) S 1

/-- **Face mass along a path**: `√P_{γ 0}(A) − ½ ∫₀¹ |γ'|_F ≤ √P_{γ s}(A)` for `s ∈ [0, 1]`. -/
theorem sqrt_real_sub_half_integral_le {η η' : ℝ → J → ℝ}
    (hη : ∀ s, η s ∈ dirSpan ν (fun _ ↦ (1 : ℝ)) S) (hd : ∀ s, HasDerivAt η (η' s) s)
    (hd' : Continuous η') {A : Set X} (hA : MeasurableSet A) {s : ℝ} (hs : s ∈ Icc (0 : ℝ) 1) :
    √((Pfam (η 0)).real A) - 1 / 2 * ∫ r in (0 : ℝ)..1, fisherNorm S ν (η r) (η' r) ≤
      √((Pfam (η s)).real A) := by
  have hηc : Continuous η := continuous_iff_continuousAt.2 fun r ↦ (hd r).continuousAt
  have hcont : Continuous fun r ↦ fisherNorm S ν (η r) (η' r) :=
    continuous_fisherNorm_comp hS ν hηc hd'
  have h1 := abs_sqrt_real_sub_le_hellingerDist hS ν (η s) (η 0) hA
  have h2 := hellingerDist_le_half_fisherDist hS ν ⟨η 0, hη 0⟩ ⟨η s, hη s⟩
  have h3 := fisherDist_le_integral hS ν hη hd hd' hs.1
  have h4 : ∫ r in (0 : ℝ)..s, fisherNorm S ν (η r) (η' r) ≤
      ∫ r in (0 : ℝ)..1, fisherNorm S ν (η r) (η' r) :=
    intervalIntegral.integral_mono_interval le_rfl hs.1 hs.2
      (Eventually.of_forall fun r ↦ fisherNorm_nonneg S ν _ _) (hcont.intervalIntegrable _ _)
  simp only at h2
  have := (abs_sub_le_iff.1 h1).2
  linarith

/-- **Translating a path by a normal-cone vector** along which the face mass stays `≥ q`
costs at most the factor `1/√q`. -/
theorem fisherDist_add_le_integral_div_sqrt {η η' : ℝ → J → ℝ}
    (hη : ∀ s, η s ∈ dirSpan ν (fun _ ↦ (1 : ℝ)) S) (hd : ∀ s, HasDerivAt η (η' s) s)
    (hd' : Continuous η') {b : J → ℝ} (hb : b ∈ dirSpan ν (fun _ ↦ (1 : ℝ)) S) {c : ℝ}
    {A : Set X} (hA : MeasurableSet A) (hc : ∀ᵐ x ∂ν, x ∈ A → dirLoss S b x = c)
    (hge : ∀ᵐ x ∂ν, c ≤ dirLoss S b x) {q : ℝ} (hq : 0 < q)
    (hq' : ∀ s ∈ Icc (0 : ℝ) 1, q ≤ (Pfam (η s)).real A) :
    fisherDist S ν ⟨η 0 + b, Submodule.add_mem _ (hη 0) hb⟩
        ⟨η 1 + b, Submodule.add_mem _ (hη 1) hb⟩ ≤
      (∫ r in (0 : ℝ)..1, fisherNorm S ν (η r) (η' r)) / √q := by
  have hηc : Continuous η := continuous_iff_continuousAt.2 fun r ↦ (hd r).continuousAt
  have hcont : Continuous fun r ↦ fisherNorm S ν (η r) (η' r) :=
    continuous_fisherNorm_comp hS ν hηc hd'
  have hcont' : Continuous fun r ↦ fisherNorm S ν (η r + b) (η' r) :=
    continuous_fisherNorm_comp hS ν (hηc.add continuous_const) hd'
  have hmem : ∀ s, η s + b ∈ dirSpan ν (fun _ ↦ (1 : ℝ)) S := fun s ↦
    Submodule.add_mem _ (hη s) hb
  have h1 := fisherDist_le_integral hS ν (η := fun s ↦ η s + b) (η' := η') hmem
    (fun s ↦ (hd s).add_const b) hd' zero_le_one
  refine h1.trans ?_
  rw [← intervalIntegral.integral_div]
  refine intervalIntegral.integral_mono_on zero_le_one (hcont'.intervalIntegrable _ _)
    ((hcont.div_const _).intervalIntegrable _ _) fun s hs ↦ ?_
  have hpos : 0 < (Pfam (η s)).real A := hq.trans_le (hq' s hs)
  refine (fisherNorm_add_le_div_sqrt hS ν (η s) b (η' s) hA hc hge hpos).trans ?_
  exact div_le_div_of_nonneg_left (fisherNorm_nonneg S ν _ _) (Real.sqrt_pos.2 hq)
    (Real.sqrt_le_sqrt (hq' s hs))

/-- **Short paths near face mass one translate at cost two**: if `P_x(A) ≥ 3/4` and a path
from `x` to `y` has length `≤ 1/2`, then `d_F(x + b, y + b) ≤ 2 · length` for every
normal-cone vector `b`. -/
theorem fisherDist_add_le_two_mul_length {x y : dirSpan ν (fun _ ↦ (1 : ℝ)) S}
    (p : FisherPath S ν x y) {A : Set X} (hA : MeasurableSet A)
    (hxA : 3 / 4 ≤ (Pfam (x : J → ℝ)).real A) (hlen : p.length ≤ 1 / 2) {b : J → ℝ}
    (hb : b ∈ dirSpan ν (fun _ ↦ (1 : ℝ)) S) {c : ℝ} (hc : ∀ᵐ x ∂ν, x ∈ A → dirLoss S b x = c)
    (hge : ∀ᵐ x ∂ν, c ≤ dirLoss S b x) :
    fisherDist S ν ⟨(x : J → ℝ) + b, Submodule.add_mem _ x.2 hb⟩
        ⟨(y : J → ℝ) + b, Submodule.add_mem _ y.2 hb⟩ ≤ 2 * p.length := by
  have hη : ∀ s, (p.toFun s : J → ℝ) ∈ dirSpan ν (fun _ ↦ (1 : ℝ)) S := fun s ↦ (p.toFun s).2
  have hd := p.hasDerivAt_coe ν
  have hd' : Continuous fun s ↦ (p.vel s : J → ℝ) := continuous_subtype_val.comp p.continuous_vel
  have hq' : ∀ s ∈ Icc (0 : ℝ) 1, 1 / 4 ≤ (Pfam (p.toFun s : J → ℝ)).real A := fun s hs ↦ by
    have h := sqrt_real_sub_half_integral_le hS ν hη hd hd' hA hs
    have hlen' : ∫ r in (0 : ℝ)..1, fisherNorm S ν (p.toFun r : J → ℝ) (p.vel r : J → ℝ) ≤ 1 / 2 :=
      hlen
    have h0 : (p.toFun 0 : J → ℝ) = x := by rw [p.source]
    rw [h0] at h
    have hx : (17 / 20 : ℝ) ≤ √((Pfam (x : J → ℝ)).real A) :=
      (Real.le_sqrt (by norm_num) (by linarith)).2 (by nlinarith)
    have hs' : (1 / 2 : ℝ) ≤ √((Pfam (p.toFun s : J → ℝ)).real A) := by linarith
    have := (Real.le_sqrt (by norm_num) measureReal_nonneg).1 hs'
    linarith
  have h := fisherDist_add_le_integral_div_sqrt hS ν hη hd hd' hb hA hc hge (by norm_num) hq'
  have e0 : (⟨(p.toFun 0 : J → ℝ) + b, Submodule.add_mem _ (hη 0) hb⟩ :
      dirSpan ν (fun _ ↦ (1 : ℝ)) S) = ⟨(x : J → ℝ) + b, Submodule.add_mem _ x.2 hb⟩ :=
    Subtype.ext (by simp [p.source])
  have e1 : (⟨(p.toFun 1 : J → ℝ) + b, Submodule.add_mem _ (hη 1) hb⟩ :
      dirSpan ν (fun _ ↦ (1 : ℝ)) S) = ⟨(y : J → ℝ) + b, Submodule.add_mem _ y.2 hb⟩ :=
    Subtype.ext (by simp [p.target])
  rw [e0, e1] at h
  refine h.trans (le_of_eq ?_)
  rw [show √(1 / 4 : ℝ) = 1 / 2 by
    rw [show (1 / 4 : ℝ) = (1 / 2) ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]]
  unfold FisherPath.length
  ring

end Paths

end Laplace.Multi
