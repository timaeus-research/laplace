/-
Copyright (c) 2026 Timaeus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Timaeus
-/
import Laplace.Multi.ResponseTransport
import Laplace.Multi.SecondOrderTransport
import Laplace.Multi.NaturalGradientAtlas
import Laplace.Multi.UniformBias
import Laplace.Multi.InvisibleQuadratic
import Laplace.Multi.DifferentialRetraction

/-!
# Response geometry: projection, invisible bending, averaged curvature

The closing package of the response-map programme. For a data law `D = d ν` with bounded positive
density and interior response `M* = E_D S`, along the affine data path `D_t = (1−t)ν + tD` with
response path `M_t = m₀ + t δ`:

1. **factorisation and projection**: the reconstruction `Π(M*)` has response `M*`, is
   idempotent, `M ↦ [q_M]` is differentiable in `L¹(ν)` with derivative `u ↦ [q_M ℓ_{M,u}]`, and
   the moment map inverts the derivative;
2. **whole-law transport**: `G_F(M*) − G_F(m₀) = ∫₀¹ lin_{F,M_s}(δ) ds` for every bounded `F`;
3. **invisible bending**: `G_F(M_t) = G_F(m₀) + t lin_{F,m₀}(δ) + ∫₀ᵗ (t−r) b_{F,M_r}(δ,δ)dr`,
   and the exact identity `∫ (1, S) (q_{M+h} − q_M − q_M ℓ_{M,h}) dν = 0`: every nonlinear
   deviation of the reconstruction from its tangent prediction is invisible to the features;
4. **sampling averages the bending**: the reconstruction bias of the truncated plug-in is
   `½ Σ Γ_ab b_F(e_a, e_b)`, uniformly over `‖F‖∞ ≤ 1`;
5. **the atlas is a natural-gradient trajectory**: `M(τ) = M_{1−e^{−τ}}` solves `M' = −(M − M*)`,
   converges to `M*`, and dissipates `KL(Q_{M*} ‖ Q_M)` at the squared Fisher speed.

(`response_geometry`.) Data move the moments; reconstruction lifts that motion visibly; its
nonlinear bending preserves those moments; sampling averages that bending into bias; and the
straight moment atlas is a natural-gradient flow after changing its clock.
-/

open MeasureTheory Filter Topology Set ProbabilityTheory

namespace Laplace.Multi

variable {X : Type*} [MeasurableSpace X] [Nonempty X] {J : Type*} [Fintype J] [Nonempty J]
  {S : J → X → ℝ} (hS : ∀ j, Bdd (S j)) (ν : Measure X) [IsProbabilityMeasure ν]
include hS

/-- The family `θ ↦ P_θ` in natural coordinates. -/
local notation "Pfam" => familyMeasure ν (fun _ ↦ (1 : ℝ)) (fun _ ↦ (0 : ℝ)) S 1

/-- The direction subspace. -/
local notation "𝕍" => dirSpan ν (fun _ ↦ (1 : ℝ)) S

/-- The natural coordinate of a response. -/
local notation "θr" => responseTheta measurable_const (integrable_const 1) (fun _ ↦ one_pos)
  (one_integral_pos ν) hS

/-- The featureless response. -/
local notation "m₀" => meanMap ν (fun _ ↦ (1 : ℝ)) (fun _ ↦ (0 : ℝ)) S 1 0

variable {M : J → ℝ} (hrel : M ∈ intrinsicInterior ℝ (momentBody ν (fun _ ↦ (1 : ℝ)) S))
include hrel

/-- **The nonlinear deviation of the reconstruction has zero mass**:
`∫ (q_{M+h} − q_M − q_M ℓ_{M,h}) dν = 0`. -/
theorem integral_deviation_eq_zero (h : 𝕍) :
    ∫ x, (famDens S ν (θr (M + h)) x - famDens S ν (θr M) x -
      famDens S ν (θr M) x * responseScore hS ν M h x) ∂ν = 0 := by
  have hP := isProbabilityMeasure_family_responseTheta hS ν (M := M)
  have h12 : Integrable (fun x ↦ famDens S ν (θr (M + h)) x - famDens S ν (θr M) x) ν :=
    (integrable_famDens hS ν _).sub (integrable_famDens hS ν _)
  rw [integral_sub h12 (integrable_famDens_mul_responseScore hS ν h),
    integral_sub (integrable_famDens hS ν _) (integrable_famDens hS ν _), integral_famDens hS ν,
    integral_famDens hS ν, ← integral_famDens_mul hS ν, integral_responseScore hS ν hrel]
  ring

/-- **The nonlinear deviation of the reconstruction has zero feature moments**:
`∫ S_j (q_{M+h} − q_M − q_M ℓ_{M,h}) dν = 0`. Together with the zero-mass identity: every nonlinear
deviation from the tangent prediction is invisible to the features. -/
theorem integral_stat_mul_deviation_eq_zero (h : 𝕍)
    (hh : M + (h : J → ℝ) ∈ intrinsicInterior ℝ (momentBody ν (fun _ ↦ (1 : ℝ)) S)) (j : J) :
    ∫ x, S j x * (famDens S ν (θr (M + h)) x - famDens S ν (θr M) x -
      famDens S ν (θr M) x * responseScore hS ν M h x) ∂ν = 0 := by
  have hP := isProbabilityMeasure_family_responseTheta hS ν (M := M)
  have hP' := isProbabilityMeasure_family_responseTheta hS ν (M := M + h)
  have h1 : Integrable (fun x ↦ S j x * famDens S ν (θr (M + h)) x) ν :=
    ((integrable_famDens hS ν _).bdd_mul (hS j).1.aestronglyMeasurable
      (Eventually.of_forall fun x ↦ by rw [Real.norm_eq_abs]; exact (hS j).2.choose_spec x))
  have h2 : Integrable (fun x ↦ S j x * famDens S ν (θr M) x) ν :=
    ((integrable_famDens hS ν _).bdd_mul (hS j).1.aestronglyMeasurable
      (Eventually.of_forall fun x ↦ by rw [Real.norm_eq_abs]; exact (hS j).2.choose_spec x))
  have h3 : Integrable (fun x ↦ S j x * (famDens S ν (θr M) x * responseScore hS ν M h x)) ν :=
    ((integrable_famDens_mul_responseScore hS ν h).bdd_mul (hS j).1.aestronglyMeasurable
      (Eventually.of_forall fun x ↦ by rw [Real.norm_eq_abs]; exact (hS j).2.choose_spec x))
  have e : (fun x ↦ S j x * (famDens S ν (θr (M + h)) x - famDens S ν (θr M) x -
      famDens S ν (θr M) x * responseScore hS ν M h x)) = fun x ↦
      S j x * famDens S ν (θr (M + h)) x - S j x * famDens S ν (θr M) x -
        S j x * (famDens S ν (θr M) x * responseScore hS ν M h x) := by
    funext x; ring
  have h12 : Integrable (fun x ↦ S j x * famDens S ν (θr (M + h)) x -
      S j x * famDens S ν (θr M) x) ν := h1.sub h2
  rw [e, integral_sub h12 h3, integral_sub h1 h2,
    moment_famDens_mul_responseScore hS ν hrel h j]
  have hm : ∀ N, N ∈ intrinsicInterior ℝ (momentBody ν (fun _ ↦ (1 : ℝ)) S) →
      ∫ x, S j x * famDens S ν (θr N) x ∂ν = N j := fun N hN ↦ by
    have := congrFun (integral_stat_responseTheta hS ν hN) j
    rw [integral_famDens_mul hS ν] at this
    rw [← this]
    exact integral_congr_ae (Eventually.of_forall fun x ↦ mul_comm _ _)
  rw [hm _ hh, hm _ hrel, Pi.add_apply]
  ring

/-- **Every nonlinear deviation of the reconstruction is invisible to `(1, S)`.** -/
theorem deviation_invisible (h : 𝕍)
    (hh : M + (h : J → ℝ) ∈ intrinsicInterior ℝ (momentBody ν (fun _ ↦ (1 : ℝ)) S)) :
    (∫ x, (famDens S ν (θr (M + h)) x - famDens S ν (θr M) x -
      famDens S ν (θr M) x * responseScore hS ν M h x) ∂ν = 0) ∧
    ∀ j, ∫ x, S j x * (famDens S ν (θr (M + h)) x - famDens S ν (θr M) x -
      famDens S ν (θr M) x * responseScore hS ν M h x) ∂ν = 0 :=
  ⟨integral_deviation_eq_zero hS ν hrel h, integral_stat_mul_deviation_eq_zero hS ν hrel h hh⟩

section Package

variable {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P] (D : Measure X)
  [IsProbabilityMeasure D] (Xs : ℕ → Ω → X) (hXm : ∀ i, Measurable (Xs i))
  (hind : iIndepFun Xs P) (hid : ∀ i, IdentDistrib (Xs i) (Xs 0) P P) (hlaw : P.map (Xs 0) = D)
include hXm hind hid hlaw

omit hrel in
/-- **Response geometry: projection, invisible bending, and averaged curvature.**
For data `D ≪ ν` with interior response `M* = E_D S`, i.i.d. samples, and a compact convex
interior neighbourhood `C` of `M*`:

1. the reconstruction `Π(M*)` is the family member `Q_{M*}`, has response `M*`, is idempotent
   (`Π(E_{Q_θ} S) = Q_θ`), `M ↦ [q_M]` is `L¹`-differentiable at `M*` with derivative
   `u ↦ [q_{M*} ℓ_{M*,u}]`, and the moment map inverts the derivative;
2. whole-law transport along the atlas: `G_F(M*) − G_F(m₀) = ∫₀¹ lin_{F,M_s}(M* − m₀) ds`;
3. invisible bending: `G_F(M_t) = G_F(m₀) + t lin_{F,m₀}(δ) + ∫₀ᵗ (t−r) b_{F,M_r}(δ,δ) dr`, and
   `∫ (1, S)(q_{M*+h} − q_{M*} − q_{M*} ℓ_{M*,h}) dν = 0` for every interior `M* + h`;
4. sampling averages the bending: `n (E Ĝ_{F,n} − G_F(M*)) → ½ Σ Γ_ab b_F(e_a, e_b)` uniformly
   over `‖F‖∞ ≤ 1`;
5. the atlas is a natural-gradient trajectory: `M(τ) = M_{1−e^{−τ}}` starts at `m₀`, solves
   `M' = −(M − M*)`, converges to `M*`, and dissipates `KL(Q_{M*} ‖ Q_M)` at the Fisher rate. -/
theorem response_geometry [DecidableEq J] (hDν : D ≪ ν)
    (hrel : dataMoment D S ∈ intrinsicInterior ℝ (momentBody ν (fun _ ↦ (1 : ℝ)) S))
    {C : Set (J → ℝ)} [DecidablePred (· ∈ C)] (hC : IsCompact C) (hCc : Convex ℝ C)
    (hCK : C ⊆ intrinsicInterior ℝ (momentBody ν (fun _ ↦ (1 : ℝ)) S)) {r : ℝ} (hr : 0 < r)
    (hCnhd : ∀ M' ∈ momentBody ν (fun _ ↦ (1 : ℝ)) S, ‖M' - dataMoment D S‖ ≤ r → M' ∈ C) :
    -- (1) factorisation, projection, idempotence, differential, inverse
    (responseProjection hS ν (dataMoment D S) = Pfam (θr (dataMoment D S)) ∧
      (fun i ↦ ∫ x, S i x ∂(Pfam (θr (dataMoment D S)))) = dataMoment D S ∧
      (∀ θ : J → ℝ, responseProjection hS ν (fun k ↦ ∫ x, S k x ∂(Pfam θ)) = Pfam θ) ∧
      HasFDerivAt (fun z : 𝕍 ↦ reconstructionL1 hS ν (dataMoment D S + z))
        (reconstructionDeriv hS ν (dataMoment D S)) 0 ∧
      ∀ u : 𝕍, (fun j ↦ ∫ x, S j x * (famDens S ν (θr (dataMoment D S)) x *
        responseScore hS ν (dataMoment D S) u x) ∂ν) = (u : J → ℝ)) ∧
    -- (2) whole-law transport
    (∀ {F : X → ℝ} (hF : Bdd F),
      (∫ x, F x ∂(Pfam (θr (dataMoment D S)))) - (∫ x, F x ∂(Pfam (θr m₀))) =
        ∫ s in (0 : ℝ)..1, linForm hS ν (atlasPath S ν (dataMoment D S) s) hF
          (dataMoment D S - m₀)) ∧
    -- (3) invisible bending
    ((∀ {t : ℝ}, 0 ≤ t → t < 1 → ∀ {F : X → ℝ} (hF : Bdd F) {BF : ℝ}, (∀ x, |F x| ≤ BF) →
      obsResponse hS ν F (atlasPath S ν (dataMoment D S) t) =
        obsResponse hS ν F m₀ + t * linForm hS ν m₀ hF (dataMoment D S - m₀) +
          ∫ r in (0 : ℝ)..t, (t - r) * biasForm hS ν (atlasPath S ν (dataMoment D S) r) hF
            (dataMoment D S - m₀) (dataMoment D S - m₀)) ∧
      ∀ h : 𝕍, dataMoment D S + (h : J → ℝ) ∈
          intrinsicInterior ℝ (momentBody ν (fun _ ↦ (1 : ℝ)) S) →
        (∫ x, (famDens S ν (θr (dataMoment D S + h)) x - famDens S ν (θr (dataMoment D S)) x -
          famDens S ν (θr (dataMoment D S)) x * responseScore hS ν (dataMoment D S) h x) ∂ν
            = 0) ∧
        ∀ j, ∫ x, S j x * (famDens S ν (θr (dataMoment D S + h)) x -
          famDens S ν (θr (dataMoment D S)) x -
          famDens S ν (θr (dataMoment D S)) x * responseScore hS ν (dataMoment D S) h x) ∂ν
            = 0) ∧
    -- (4) sampling averages the bending, uniformly over the unit ball of observables
    (∀ η > 0, ∃ N : ℕ, ∀ n ≥ N, ∀ {F : X → ℝ} (hF : Bdd F), (∀ x, |F x| ≤ 1) →
      |(n : ℝ) * ((∫ ω, plugIn hS ν F C (dataMoment D S) (sampleResponse S Xs n ω) ∂P) -
          obsResponse hS ν F (dataMoment D S)) -
        (1 / 2) * ∑ a, ∑ b,
          (∫ x, (S a x - dataMoment D S a) * (S b x - dataMoment D S b) ∂D) *
            biasForm hS ν (dataMoment D S) hF (coordUnit a) (coordUnit b)| < η) ∧
    -- (5) the atlas is a natural-gradient trajectory
    (natFlow S ν (dataMoment D S) 0 = m₀ ∧
      (∀ τ, HasDerivAt (natFlow S ν (dataMoment D S))
        (-(natFlow S ν (dataMoment D S) τ - dataMoment D S)) τ) ∧
      Tendsto (natFlow S ν (dataMoment D S)) atTop (𝓝 (dataMoment D S)) ∧
      ∀ {τ : ℝ} (hτ : 0 ≤ τ),
        HasDerivAt (fun τ ↦ natLoss hS ν (dataMoment D S) (natFlow S ν (dataMoment D S) τ))
          (-fisherForm hS ν (natFlow S ν (dataMoment D S) τ)
            ⟨natFlow S ν (dataMoment D S) τ - dataMoment D S,
              sub_mem_dirSpan_of_mem_momentBody' hS ν (intrinsicInterior_subset hrel)
                (intrinsicInterior_subset
                  (natFlow_mem_intrinsicInterior hS ν (dataMoment D S) hrel hτ))⟩
            ⟨natFlow S ν (dataMoment D S) τ - dataMoment D S,
              sub_mem_dirSpan_of_mem_momentBody' hS ν (intrinsicInterior_subset hrel)
                (intrinsicInterior_subset
                  (natFlow_mem_intrinsicInterior hS ν (dataMoment D S) hrel hτ))⟩) τ) := by
  have hfin := genRate_ne_top_of_mem_intrinsicInterior hS ν hrel
  refine ⟨⟨responseProjection_eq_familyMeasure_responseTheta hS ν hrel,
      integral_stat_responseTheta hS ν hrel,
      fun θ ↦ responseProjection_mean_familyMeasure hS ν θ,
      hasFDerivAt_reconstructionL1 hS ν hrel,
      fun u ↦ famDens_mul_responseScore_moment_eq hS ν hrel u⟩,
    fun {F} hF ↦ integral_response_sub_featureless_eq_integral_atlas hS ν hrel hF,
    ⟨fun {t} ht0 ht1 {F} hF {BF} hBF ↦
        obsResponse_atlas_eq_second_order hS ν hfin ht0 ht1 hF hBF,
      fun h hh ↦ deviation_invisible hS ν hrel h hh⟩,
    reconstruction_bias_uniform_of_nhd hS ν P D Xs hXm hind hid hlaw hDν hrel hC hCc hCK hr hCnhd,
    natFlow_zero ν _, hasDerivAt_natFlow ν _, tendsto_natFlow ν _,
    fun {τ} hτ ↦ hasDerivAt_natLoss_natFlow hS ν _ hrel hτ⟩

end Package

end Laplace.Multi
