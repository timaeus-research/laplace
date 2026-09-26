/-
Copyright (c) 2026 Timaeus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Timaeus
-/
import Laplace.Multi.ResponseHessian

/-!
# Second-order transport along curved response paths

For a `C²` path of interior responses `M_t = M + γ(t)`, the reconstruction curve
`t ↦ [q_{M_t}] ∈ L¹(ν)` has velocity `[q_{M_t} ℓ_{M_t, γ'(t)}]` and acceleration
`[q_{M_t} N_{M_t}(ℓ_{γ'}²)] + [q_{M_t} ℓ_{M_t, γ''(t)}]` (`hasDerivAt_deriv_reconstructionL1_path`):
the invisible bending of the response family in the direction of the velocity, plus the visible
lift of the acceleration of the prescribed response. Its feature moments are exactly `γ''(t)`
(`momentL1_deriv_deriv_reconstructionL1_path`): along curved paths the second derivative is
invisible precisely when the response does not accelerate.
-/

open MeasureTheory Filter Topology Set
open scoped ContDiff

namespace Laplace.Multi

/-- Translation invariance of the Fréchet derivative. -/
theorem fderiv_comp_sub_const' {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] (f : E → F) (a x : E) :
    fderiv ℝ (fun z ↦ f (z - a)) x = fderiv ℝ f (x - a) := by
  by_cases h : DifferentiableAt ℝ f (x - a)
  · have := (h.hasFDerivAt.comp x ((hasFDerivAt_id x).sub_const a)).fderiv
    rw [ContinuousLinearMap.comp_id] at this
    exact this
  · have h' : ¬ DifferentiableAt ℝ (fun z ↦ f (z - a)) x := fun hd ↦ h (by
      have := DifferentiableAt.comp (x - a) (g := fun z ↦ f (z - a)) (f := fun y ↦ y + a)
        (by rw [sub_add_cancel]; exact hd) (differentiableAt_id.add_const a)
      simpa [Function.comp_def] using this)
    rw [fderiv_zero_of_not_differentiableAt h, fderiv_zero_of_not_differentiableAt h']

variable {X : Type*} [MeasurableSpace X] [Nonempty X] {J : Type*} [Fintype J] [Nonempty J]
  {S : J → X → ℝ} (hS : ∀ j, Bdd (S j)) (ν : Measure X) [IsProbabilityMeasure ν]
include hS

/-- The direction subspace. -/
local notation "𝕍" => dirSpan ν (fun _ ↦ (1 : ℝ)) S

/-- The natural coordinate of a response. -/
local notation "θr" => responseTheta measurable_const (integrable_const 1) (fun _ ↦ one_pos)
  (one_integral_pos ν) hS

/-- The interior response domain. -/
local notation "Ω" => intrinsicInterior ℝ (momentBody ν (fun _ ↦ (1 : ℝ)) S)

variable {M : J → ℝ} (hrel : M ∈ intrinsicInterior ℝ (momentBody ν (fun _ ↦ (1 : ℝ)) S))
include hrel

/-- The reconstruction as a function of the displacement from `M`. -/
local notation "P" => fun z : 𝕍 ↦ reconstructionL1 hS ν (M + z)

/-- The reconstruction is `C^∞` at every interior displacement. -/
theorem contDiffAt_reconstructionL1_add_of_mem {z₀ : 𝕍} (hz₀ : M + (z₀ : J → ℝ) ∈ Ω) :
    ContDiffAt ℝ ∞ P z₀ :=
  (contDiffOn_reconstructionL1_add hS ν hrel).contDiffAt
    ((isOpen_addDomain hS ν hrel).mem_nhds hz₀)

omit hrel in
/-- The displacement map re-based at `M + z₀`. -/
theorem reconstructionL1_add_eq_sub (z₀ : 𝕍) :
    P = fun z : 𝕍 ↦ reconstructionL1 hS ν (M + z₀ + ((z - z₀ : 𝕍) : J → ℝ)) := by
  funext z
  congr 1
  rw [Submodule.coe_sub]
  abel

omit hrel in
/-- **The first derivative at an interior displacement** is the reconstruction derivative there. -/
theorem fderiv_reconstructionL1_add_of_mem {z₀ : 𝕍} (hz₀ : M + (z₀ : J → ℝ) ∈ Ω) :
    fderiv ℝ P z₀ = reconstructionDeriv hS ν (M + z₀) := by
  rw [reconstructionL1_add_eq_sub hS ν z₀]
  have h := fderiv_comp_sub_const' (fun w : 𝕍 ↦ reconstructionL1 hS ν (M + z₀ + w)) z₀ z₀
  beta_reduce at h
  rw [h, sub_self]
  exact (hasFDerivAt_reconstructionL1 hS ν hz₀).fderiv

omit hrel in
/-- **The second derivative at an interior displacement** is the invisible Hessian there. -/
theorem fderiv_fderiv_reconstructionL1_add_of_mem {z₀ : 𝕍} (hz₀ : M + (z₀ : J → ℝ) ∈ Ω)
    (u v : 𝕍) :
    fderiv ℝ (fderiv ℝ P) z₀ u v =
      (integrable_famDens_mul_of_bdd hS ν (M := M + z₀) (bdd_normalProj hS ν
        ((bdd_responseScore hS ν (M + z₀) u).mul (bdd_responseScore hS ν (M + z₀) v)))).toL1
        (fun x ↦ famDens S ν (θr (M + z₀)) x * normalProj hS ν (M + z₀)
          ((bdd_responseScore hS ν (M + z₀) u).mul (bdd_responseScore hS ν (M + z₀) v)) x) := by
  have hf : fderiv ℝ P = fun z : 𝕍 ↦ fderiv ℝ (fun w : 𝕍 ↦ reconstructionL1 hS ν
      (M + z₀ + w)) (z - z₀) := by
    funext z
    rw [reconstructionL1_add_eq_sub hS ν z₀]
    have h := fderiv_comp_sub_const' (fun w : 𝕍 ↦ reconstructionL1 hS ν (M + z₀ + w)) z₀ z
    beta_reduce at h
    exact h
  rw [hf]
  have h2 := fderiv_comp_sub_const'
    (fderiv ℝ (fun w : 𝕍 ↦ reconstructionL1 hS ν (M + z₀ + w))) z₀ z₀
  beta_reduce at h2
  rw [h2, sub_self]
  exact fderiv_fderiv_reconstructionL1_add hS ν hz₀ u v

section Path

variable {γ γ' : ℝ → dirSpan ν (fun _ ↦ (1 : ℝ)) S}
  (hγΩ : ∀ t, M + (γ t : J → ℝ) ∈ intrinsicInterior ℝ (momentBody ν (fun _ ↦ (1 : ℝ)) S))
  (hγ : ∀ t, HasDerivAt γ (γ' t) t)
include hγΩ hγ

/-- **First-order transport along a curved path**: `d/dt [q_{M+γ(t)}] = DP_{γ(t)}[γ'(t)]`. -/
theorem hasDerivAt_reconstructionL1_path (t : ℝ) :
    HasDerivAt (fun t ↦ reconstructionL1 hS ν (M + γ t)) (fderiv ℝ P (γ t) (γ' t)) t :=
  HasFDerivAt.comp_hasDerivAt t (l := P) (f := γ)
    ((contDiffAt_reconstructionL1_add_of_mem hS ν hrel (hγΩ t)).differentiableAt
      (by simp)).hasFDerivAt (hγ t)

/-- The velocity of the reconstruction along a curved path. -/
theorem deriv_reconstructionL1_path :
    deriv (fun t ↦ reconstructionL1 hS ν (M + γ t)) = fun t ↦ fderiv ℝ P (γ t) (γ' t) :=
  funext fun t ↦ (hasDerivAt_reconstructionL1_path hS ν hrel hγΩ hγ t).deriv

variable {t₀ : ℝ} {γ'' : dirSpan ν (fun _ ↦ (1 : ℝ)) S} (hγ' : HasDerivAt γ' γ'' t₀)
include hγ'

/-- **Second-order transport along a curved path**:
`d²/dt² [q_{M+γ(t)}] = D²P_{γ}[γ', γ'] + DP_{γ}[γ'']`. -/
theorem hasDerivAt_deriv_reconstructionL1_path_fderiv :
    HasDerivAt (deriv (fun t ↦ reconstructionL1 hS ν (M + γ t)))
      (fderiv ℝ (fderiv ℝ P) (γ t₀) (γ' t₀) (γ' t₀) + fderiv ℝ P (γ t₀) γ'') t₀ := by
  rw [deriv_reconstructionL1_path hS ν hrel hγΩ hγ]
  have hP2 : HasFDerivAt (fderiv ℝ P) (fderiv ℝ (fderiv ℝ P) (γ t₀)) (γ t₀) :=
    (((contDiffAt_reconstructionL1_add_of_mem hS ν hrel (hγΩ t₀)).of_le
      (by exact_mod_cast natCast_le_infty 2)).fderiv_right_succ.differentiableAt
        one_ne_zero).hasFDerivAt
  exact (HasFDerivAt.comp_hasDerivAt t₀ hP2 (hγ t₀)).clm_apply hγ'

/-- **Second-order transport along a curved path, explicitly**: the acceleration of the
reconstruction is the invisible bending `[q N(ℓ_{γ'}²)]` plus the visible lift `[q ℓ_{γ''}]` of the
response acceleration. -/
theorem hasDerivAt_deriv_reconstructionL1_path :
    HasDerivAt (deriv (fun t ↦ reconstructionL1 hS ν (M + γ t)))
      ((integrable_famDens_mul_of_bdd hS ν (M := M + γ t₀) (bdd_normalProj hS ν
        ((bdd_responseScore hS ν (M + γ t₀) (γ' t₀)).mul
          (bdd_responseScore hS ν (M + γ t₀) (γ' t₀))))).toL1
        (fun x ↦ famDens S ν (θr (M + γ t₀)) x * normalProj hS ν (M + γ t₀)
          ((bdd_responseScore hS ν (M + γ t₀) (γ' t₀)).mul
            (bdd_responseScore hS ν (M + γ t₀) (γ' t₀))) x) +
        reconstructionDeriv hS ν (M + γ t₀) γ'') t₀ := by
  have h := hasDerivAt_deriv_reconstructionL1_path_fderiv hS ν hrel hγΩ hγ hγ'
  rwa [fderiv_fderiv_reconstructionL1_add_of_mem hS ν (hγΩ t₀),
    fderiv_reconstructionL1_add_of_mem hS ν (hγΩ t₀)] at h

/-- **The feature moments of the acceleration are the response acceleration**:
`∫ S d²/dt²[q_{M_t}] = γ''(t)`; the bending is invisible, the acceleration is visible. -/
theorem momentL1_deriv_deriv_reconstructionL1_path :
    momentL1 hS ν (deriv (deriv (fun t ↦ reconstructionL1 hS ν (M + γ t))) t₀) =
      (γ'' : J → ℝ) := by
  rw [(hasDerivAt_deriv_reconstructionL1_path_fderiv hS ν hrel hγΩ hγ hγ').deriv, map_add,
    fderiv_reconstructionL1_add_of_mem hS ν (hγΩ t₀),
    momentL1_reconstructionDeriv hS ν (hγΩ t₀) γ'',
    fderiv_fderiv_reconstructionL1_add_of_mem hS ν (hγΩ t₀)]
  have hz := (momentL1_fderiv_fderiv_eq_zero hS ν (hγΩ t₀) (γ' t₀) (γ' t₀)).1
  rw [fderiv_fderiv_reconstructionL1_add hS ν (hγΩ t₀)] at hz
  rw [hz, zero_add]

end Path

end Laplace.Multi
