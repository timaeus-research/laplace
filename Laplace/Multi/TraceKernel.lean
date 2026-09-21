/-
Copyright (c) 2026 Timaeus Research. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniel Murfet
-/
import Mathlib
import Laplace.Multi.TraceVisibility
import Laplace.Multi.AllOrders

/-!
# The trace kernel of the degree-`≤ m` monomial design (part 1: calculus)

Infrastructure for the exact kernel theorem (`TraceKernelMain`): nested coordinate derivatives
along a list of coordinates (`wordPD`), products and coordinates as smooth homogeneous functions,
Stein's identity for products, the centered identity
`Cov(x_i P, Q) = E[P ∂_i Q] + Cov(∂_i P, Q)`, commutation of coordinate derivatives with the
iterated Laplacian (Schwarz), and the Euler jet detection lemma: a smooth homogeneous function of
degree `s` all of whose `s`-fold coordinate derivatives vanish at `0` is zero.
-/

open Real MeasureTheory Filter Topology
open scoped ContDiff

namespace Laplace.Multi

variable {d : ℕ}

local notation "K₁" => quadKernel (1 : Matrix (Fin d) (Fin d) ℝ)
local notation "E₁" => gaussianExpectation (1 : Matrix (Fin d) (Fin d) ℝ)
local notation "Cov₁" => gaussianCovariance (1 : Matrix (Fin d) (Fin d) ℝ)

/-- Nested coordinate derivatives along a list: `wordPD (i :: w) f = ∂_i (wordPD w f)`. -/
noncomputable def wordPD : List (Fin d) → (EuclidD d → ℝ) → (EuclidD d → ℝ)
  | [], f => f
  | i :: w, f => pd i (wordPD w f)

@[simp] theorem wordPD_nil (f : EuclidD d → ℝ) : wordPD [] f = f := rfl

@[simp] theorem wordPD_cons (i : Fin d) (w : List (Fin d)) (f : EuclidD d → ℝ) :
    wordPD (i :: w) f = pd i (wordPD w f) := rfl

/-- The monomial of a list of coordinates. -/
def listMon : List (Fin d) → EuclidD d → ℝ
  | [], _ => 1
  | i :: v, x => x i * listMon v x

@[simp] theorem listMon_nil (x : EuclidD d) : listMon ([] : List (Fin d)) x = 1 := rfl

@[simp] theorem listMon_cons (i : Fin d) (v : List (Fin d)) (x : EuclidD d) :
    listMon (i :: v) x = x i * listMon v x := rfl

/-! ### Smooth homogeneous functions: products, coordinates, word derivatives -/

theorem SmoothHomog.mul {m n : ℕ} {f g : EuclidD d → ℝ} (hf : SmoothHomog m f)
    (hg : SmoothHomog n g) : SmoothHomog (m + n) fun x ↦ f x * g x := by
  refine ⟨hf.smooth.mul hg.smooth, fun a x ↦ ?_⟩
  simp only [hf.homog a x, hg.homog a x, pow_add]
  ring

theorem SmoothHomog.one : SmoothHomog 0 fun _ : EuclidD d ↦ (1 : ℝ) :=
  ⟨contDiff_const, fun a x ↦ by simp⟩

theorem SmoothHomog.const (c : ℝ) : SmoothHomog 0 fun _ : EuclidD d ↦ c :=
  ⟨contDiff_const, fun a x ↦ by simp⟩

theorem SmoothHomog.coord (i : Fin d) : SmoothHomog 1 fun x : EuclidD d ↦ x i :=
  ⟨contDiff_coord i, fun a x ↦ by simp⟩

theorem SmoothHomog.const_mul {n : ℕ} (c : ℝ) {f : EuclidD d → ℝ} (hf : SmoothHomog n f) :
    SmoothHomog n fun x ↦ c * f x := by
  have := (SmoothHomog.const (d := d) c).mul hf
  rwa [zero_add] at this

theorem SmoothHomog.add {n : ℕ} {f g : EuclidD d → ℝ} (hf : SmoothHomog n f)
    (hg : SmoothHomog n g) : SmoothHomog n fun x ↦ f x + g x :=
  ⟨hf.smooth.add hg.smooth, fun a x ↦ by rw [hf.homog a x, hg.homog a x]; ring⟩

theorem SmoothHomog.listMonomial : ∀ v : List (Fin d), SmoothHomog v.length (listMon v)
  | [] => SmoothHomog.one
  | i :: v => by
    have := (SmoothHomog.coord i).mul (SmoothHomog.listMonomial v)
    simp only [List.length_cons]
    rw [add_comm] at this
    exact this

theorem SmoothHomog.wordDeriv {k : ℕ} {Q : EuclidD d → ℝ} (hQ : SmoothHomog k Q) :
    ∀ w : List (Fin d), SmoothHomog (k - w.length) (wordPD w Q)
  | [] => by simpa using hQ
  | i :: w => by
    have := (SmoothHomog.wordDeriv hQ w).deriv i
    simp only [List.length_cons, wordPD_cons]
    rwa [Nat.sub_sub] at this

theorem SmoothHomog.zero_fun (n : ℕ) : SmoothHomog n fun _ : EuclidD d ↦ (0 : ℝ) :=
  ⟨contDiff_const, fun a x ↦ by simp⟩

/-! ### Expectations: linearity and Stein -/

theorem E₁_const (c : ℝ) : E₁ (fun _ : EuclidD d ↦ c) = c := by
  unfold gaussianExpectation
  rw [integral_const_mul, mul_div_assoc,
    div_self (integral_quadKernel_pos Matrix.PosDef.one).ne', mul_one]

theorem E₁_add {m n : ℕ} {f g : EuclidD d → ℝ} (hf : SmoothHomog m f) (hg : SmoothHomog n g) :
    E₁ (fun x ↦ f x + g x) = E₁ f + E₁ g :=
  gaussianExpectation_add Matrix.PosDef.one hf.smooth.continuous hf.growth hg.smooth.continuous
    hg.growth

theorem E₁_sub {m n : ℕ} {f g : EuclidD d → ℝ} (hf : SmoothHomog m f) (hg : SmoothHomog n g) :
    E₁ (fun x ↦ f x - g x) = E₁ f - E₁ g := by
  have h := E₁_add hf (hg.const_mul (-1))
  rw [gaussianExpectation_const_mul] at h
  have : (fun x ↦ f x - g x) = fun x ↦ f x + -1 * g x := by
    funext x
    ring
  rw [this, h]
  ring

/-- Stein for the expectation: `E[x_i f] = E[∂_i f]`. -/
theorem E₁_coord_mul {n : ℕ} {f : EuclidD d → ℝ} (hf : SmoothHomog n f) (i : Fin d) :
    E₁ (fun x ↦ x i * f x) = E₁ (pd i f) := by
  unfold gaussianExpectation
  congr 1
  exact stein_coord hf.smooth hf.growth i (hf.deriv i).growth

/-- The product rule for coordinate derivatives. -/
theorem pd_mul {m n : ℕ} {f g : EuclidD d → ℝ} (hf : SmoothHomog m f) (hg : SmoothHomog n g)
    (i : Fin d) : pd i (fun x ↦ f x * g x) = fun x ↦ pd i f x * g x + f x * pd i g x := by
  funext x
  have hd : HasFDerivAt (fun x ↦ f x * g x) ((f x) • fderiv ℝ g x + (g x) • fderiv ℝ f x) x :=
    (hf.differentiable x).hasFDerivAt.mul (hg.differentiable x).hasFDerivAt
  unfold pd
  rw [hd.fderiv, add_apply, smul_apply, smul_apply, smul_eq_mul, smul_eq_mul]
  ring

/-- **Stein for products**: `E[x_i f g] = E[∂_i f · g] + E[f · ∂_i g]`. -/
theorem E₁_coord_mul_mul {m n : ℕ} {f g : EuclidD d → ℝ} (hf : SmoothHomog m f)
    (hg : SmoothHomog n g) (i : Fin d) :
    E₁ (fun x ↦ x i * (f x * g x)) = E₁ (fun x ↦ pd i f x * g x) + E₁ (fun x ↦ f x * pd i g x) := by
  rw [E₁_coord_mul (hf.mul hg) i, pd_mul hf hg i]
  exact E₁_add ((hf.deriv i).mul hg) (hf.mul (hg.deriv i))

/-- **The centered identity**: `Cov(x_i P, Q) = E[P ∂_i Q] + Cov(∂_i P, Q)`. -/
theorem Cov₁_coord_mul {m n : ℕ} {P Q : EuclidD d → ℝ} (hP : SmoothHomog m P)
    (hQ : SmoothHomog n Q) (i : Fin d) :
    Cov₁ (fun x ↦ x i * P x) Q = E₁ (fun x ↦ P x * pd i Q x) + Cov₁ (pd i P) Q := by
  unfold gaussianCovariance
  have h1 : E₁ (fun x ↦ (fun x ↦ x i * P x) x * Q x) = E₁ (fun x ↦ x i * (P x * Q x)) := by
    congr 1
    funext x
    ring
  rw [h1, E₁_coord_mul_mul hP hQ i, E₁_coord_mul hP i]
  ring

/-! ### Commutation of coordinate derivatives with the Laplacian -/

theorem pd_smooth {f : EuclidD d → ℝ} (hf : ContDiff ℝ ∞ f) (i : Fin d) :
    ContDiff ℝ ∞ (pd i f) :=
  (contDiff_infty_iff_fderiv.mp hf).2.clm_apply contDiff_const

theorem lap_smooth {f : EuclidD d → ℝ} (hf : ContDiff ℝ ∞ f) : ContDiff ℝ ∞ (lap f) :=
  ContDiff.sum fun i _ ↦ pd_smooth (pd_smooth hf i) i

theorem iterate_lap_smooth {f : EuclidD d → ℝ} (hf : ContDiff ℝ ∞ f) :
    ∀ r : ℕ, ContDiff ℝ ∞ (lap^[r] f)
  | 0 => hf
  | r + 1 => by
    rw [Function.iterate_succ_apply']
    exact lap_smooth (iterate_lap_smooth hf r)

/-- Schwarz: coordinate derivatives commute on smooth functions. -/
theorem pd_comm {f : EuclidD d → ℝ} (hf : ContDiff ℝ ∞ f) (i j : Fin d) :
    pd i (pd j f) = pd j (pd i f) := by
  funext x
  have hd : Differentiable ℝ (fderiv ℝ f) :=
    (contDiff_infty_iff_fderiv.mp hf).2.differentiable (by simp)
  have hsymm : IsSymmSndFDerivAt ℝ f x :=
    hf.contDiffAt.isSymmSndFDerivAt (by
      rw [show minSmoothness ℝ 2 = 2 by simp]
      exact_mod_cast natCast_le_infty 2)
  have key : ∀ a b : Fin d, pd a (pd b f) x =
      fderiv ℝ (fderiv ℝ f) x (EuclideanSpace.single a 1) (EuclideanSpace.single b 1) := by
    intro a b
    unfold pd
    rw [fderiv_clm_apply (hd x) (differentiableAt_const _)]
    simp
  rw [key i j, key j i]
  exact hsymm _ _

theorem pd_sum {ι : Type*} (s : Finset ι) {g : ι → EuclidD d → ℝ}
    (hg : ∀ k, ContDiff ℝ ∞ (g k)) (i : Fin d) :
    pd i (fun x ↦ ∑ k ∈ s, g k x) = fun x ↦ ∑ k ∈ s, pd i (g k) x := by
  funext x
  unfold pd
  have hd := HasFDerivAt.sum (u := s) (A := g) (A' := fun k ↦ fderiv ℝ (g k) x)
    fun k _ ↦ ((hg k).differentiable (by simp) x).hasFDerivAt
  have hfun : (∑ k ∈ s, g k) = fun x ↦ ∑ k ∈ s, g k x := funext fun x ↦ Finset.sum_apply x s g
  rw [hfun] at hd
  rw [hd.fderiv, sum_apply]

theorem pd_lap_comm {f : EuclidD d → ℝ} (hf : ContDiff ℝ ∞ f) (i : Fin d) :
    pd i (lap f) = lap (pd i f) := by
  unfold lap
  rw [pd_sum Finset.univ (fun j ↦ pd_smooth (pd_smooth hf j) j) i]
  funext x
  refine Finset.sum_congr rfl fun j _ ↦ ?_
  rw [pd_comm (pd_smooth hf j) i j, pd_comm hf j i]

theorem pd_iterate_lap_comm {f : EuclidD d → ℝ} (hf : ContDiff ℝ ∞ f) (i : Fin d) :
    ∀ r : ℕ, pd i (lap^[r] f) = lap^[r] (pd i f)
  | 0 => rfl
  | r + 1 => by
    rw [Function.iterate_succ_apply', Function.iterate_succ_apply',
      pd_lap_comm (iterate_lap_smooth hf r) i, pd_iterate_lap_comm hf i r]

theorem wordPD_smooth {f : EuclidD d → ℝ} (hf : ContDiff ℝ ∞ f) :
    ∀ w : List (Fin d), ContDiff ℝ ∞ (wordPD w f)
  | [] => hf
  | i :: w => pd_smooth (wordPD_smooth hf w) i

theorem wordPD_iterate_lap_comm {f : EuclidD d → ℝ} (hf : ContDiff ℝ ∞ f) (r : ℕ) :
    ∀ w : List (Fin d), wordPD w (lap^[r] f) = lap^[r] (wordPD w f)
  | [] => rfl
  | i :: w => by
    rw [wordPD_cons, wordPD_cons, wordPD_iterate_lap_comm hf r w,
      pd_iterate_lap_comm (wordPD_smooth hf w) i r]

theorem wordPD_append (f : EuclidD d → ℝ) :
    ∀ (w : List (Fin d)) (i : Fin d), wordPD w (pd i f) = wordPD (w ++ [i]) f
  | [], i => rfl
  | j :: w, i => by
    rw [List.cons_append, wordPD_cons, wordPD_cons, wordPD_append f w i]

/-! ### Euler jet detection -/

/-- Pointwise Euler: `n f(x) = Σ_i x_i ∂_i f(x)` for smooth homogeneous `f` of degree `n`. -/
theorem SmoothHomog.euler {n : ℕ} {f : EuclidD d → ℝ} (hf : SmoothHomog n f) (x : EuclidD d) :
    (n : ℝ) * f x = ∑ i, x i * pd i f x := by
  have he := fderiv_apply_self_of_isHomogeneous hf.differentiable hf.homog x
  have hx : ∑ i, x i • EuclideanSpace.single i (1 : ℝ) = x := by
    simpa [EuclideanSpace.basisFun_apply, EuclideanSpace.basisFun_repr] using
      (EuclideanSpace.basisFun (Fin d) ℝ).sum_repr x
  have hlin : ∀ ℓ : EuclidD d →L[ℝ] ℝ, ℓ x = ∑ i, x i * ℓ (EuclideanSpace.single i 1) := by
    intro ℓ
    conv_lhs => rw [← hx]
    rw [map_sum]
    refine Finset.sum_congr rfl fun i _ ↦ ?_
    rw [map_smul, smul_eq_mul]
  rw [← he, hlin (fderiv ℝ f x)]
  rfl

/-- **Coordinate-jet detection**: a smooth homogeneous function of degree `s` whose `s`-fold
coordinate derivatives all vanish at `0` is zero. -/
theorem SmoothHomog.eq_zero_of_wordPD_zero :
    ∀ (s : ℕ) (R : EuclidD d → ℝ), SmoothHomog s R →
      (∀ w : List (Fin d), w.length = s → wordPD w R 0 = 0) → R = 0 := by
  intro s
  induction s with
  | zero =>
    intro R hR hw
    funext x
    rw [hR.const_eq x]
    exact hw [] rfl
  | succ n ih =>
    intro R hR hw
    have hpd : ∀ i, pd i R = 0 := by
      intro i
      refine ih (pd i R) (by simpa using hR.deriv i) fun w hwl ↦ ?_
      rw [wordPD_append]
      exact hw (w ++ [i]) (by simp [hwl])
    funext x
    have he := hR.euler x
    simp only [hpd, Pi.zero_apply, mul_zero, Finset.sum_const_zero] at he
    have hn : ((n + 1 : ℕ) : ℝ) ≠ 0 := by positivity
    exact (mul_eq_zero.mp he).resolve_left hn

end Laplace.Multi
