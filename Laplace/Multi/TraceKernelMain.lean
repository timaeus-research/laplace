/-
Copyright (c) 2026 Timaeus Research. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniel Murfet
-/
import Mathlib
import Laplace.Multi.TraceKernel

/-!
# The trace kernel of the degree-`≤ m` monomial design (part 2: the theorem)

For the standard Gaussian and `Q` smooth homogeneous of degree `k`, the covariances
`Cov(x^w, Q)` over all monomial words of length `≤ t` vanish iff all derivative expectations
`E[∂_w Q]` with `1 ≤ |w| ≤ t` vanish (`cov_words_iff_derivExp`), by a triangular induction on
mixed moments `E[P · ∂_w Q]` with `P` ranging over polynomials of degree `≤ q`, `q + |w| ≤ t`
(`LowPoly`), using Stein's identity for products and the centered identity
`Cov(x_i P, Q) = E[P ∂_i Q] + Cov(∂_i P, Q)`. Since `E[∂_w Q] = (∂_w Δ^a Q)(0)/(2a)!!` when
`k − |w| = 2a` and `0` otherwise, and a homogeneous function is detected by its top coordinate
jet, the exact kernel follows (`cov_words_le_iff_iterate_lap_eq_zero`): for `Q` of degree
`s + 2r` with `s ≥ 1`,

  `(∀ words w, |w| ≤ s → Cov(x^w, Q) = 0)  ↔  Δ^r Q = 0`.

The general design degree `m` reduces to this by parity (`trace_kernel_iff`): for `m < k` the
relevant `s` is `m` or `m − 1` according to the parity of `k − m`, and the tests of the wrong
parity vanish automatically.
-/

open Real MeasureTheory Filter Topology
open scoped ContDiff

namespace Laplace.Multi

variable {d : ℕ}

local notation "E₁" => gaussianExpectation (1 : Matrix (Fin d) (Fin d) ℝ)
local notation "Cov₁" => gaussianCovariance (1 : Matrix (Fin d) (Fin d) ℝ)

/-! ### Calculus for `LowPoly` tests against homogeneous functions -/

theorem LowPoly.differentiable {q : ℕ} {P : EuclidD d → ℝ} (hP : LowPoly q P) :
    Differentiable ℝ P := hP.contDiff.differentiable (by simp)

theorem LowPoly.pd_growth {q : ℕ} {P : EuclidD d → ℝ} (hP : LowPoly q P) (i : Fin d) :
    HasPolynomialGrowth (pd i P) := (hP.deriv_dir _).growth

theorem LowPoly.pd_lowPoly {q : ℕ} {P : EuclidD d → ℝ} (hP : LowPoly q P) (i : Fin d) :
    LowPoly q (pd i P) := hP.deriv_dir _

/-- The product rule for differentiable functions. -/
theorem pd_mul' {f g : EuclidD d → ℝ} (hf : Differentiable ℝ f) (hg : Differentiable ℝ g)
    (i : Fin d) : pd i (fun x ↦ f x * g x) = fun x ↦ pd i f x * g x + f x * pd i g x := by
  funext x
  have hd : HasFDerivAt (fun x ↦ f x * g x) ((f x) • fderiv ℝ g x + (g x) • fderiv ℝ f x) x :=
    (hf x).hasFDerivAt.mul (hg x).hasFDerivAt
  unfold pd
  rw [hd.fderiv, add_apply, smul_apply, smul_apply, smul_eq_mul, smul_eq_mul]
  ring

theorem E₁_add' {f g : EuclidD d → ℝ} (hfc : Continuous f) (hfg : HasPolynomialGrowth f)
    (hgc : Continuous g) (hgg : HasPolynomialGrowth g) :
    E₁ (fun x ↦ f x + g x) = E₁ f + E₁ g :=
  gaussianExpectation_add Matrix.PosDef.one hfc hfg hgc hgg

/-- Stein for the expectation, for smooth polynomial-growth functions with polynomial-growth
derivative. -/
theorem E₁_coord_mul' {f : EuclidD d → ℝ} (hf : ContDiff ℝ ∞ f) (hfg : HasPolynomialGrowth f)
    (i : Fin d) (hf' : HasPolynomialGrowth (pd i f)) :
    E₁ (fun x ↦ x i * f x) = E₁ (pd i f) := by
  unfold gaussianExpectation
  congr 1
  exact stein_coord hf hfg i hf'

/-- **Stein for products** `P · F` with `P` a low-degree polynomial and `F` smooth homogeneous. -/
theorem E₁_coord_mul_lowPoly_homog {q n : ℕ} {P F : EuclidD d → ℝ} (hP : LowPoly q P)
    (hF : SmoothHomog n F) (i : Fin d) :
    E₁ (fun x ↦ x i * (P x * F x)) = E₁ (fun x ↦ pd i P x * F x) + E₁ (fun x ↦ P x * pd i F x) := by
  have hprod := pd_mul' hP.differentiable hF.differentiable i
  rw [E₁_coord_mul' (hP.contDiff.mul hF.smooth) (hP.growth.mul hF.growth) i
    (by
      rw [hprod]
      exact ((hP.pd_growth i).mul hF.growth).add (hP.growth.mul (hF.deriv i).growth)),
    hprod]
  exact E₁_add' ((hP.pd_lowPoly i).contDiff.continuous.mul hF.smooth.continuous)
    ((hP.pd_growth i).mul hF.growth) (hP.contDiff.continuous.mul (hF.deriv i).smooth.continuous)
    (hP.growth.mul (hF.deriv i).growth)

/-- **The centered identity** for low-degree polynomial tests:
`Cov(x_i P, Q) = E[P ∂_i Q] + Cov(∂_i P, Q)`. -/
theorem Cov₁_coord_mul_lowPoly {q n : ℕ} {P Q : EuclidD d → ℝ} (hP : LowPoly q P)
    (hQ : SmoothHomog n Q) (i : Fin d) :
    Cov₁ (fun x ↦ x i * P x) Q = E₁ (fun x ↦ P x * pd i Q x) + Cov₁ (pd i P) Q := by
  unfold gaussianCovariance
  have h1 : E₁ (fun x ↦ (fun x ↦ x i * P x) x * Q x) = E₁ (fun x ↦ x i * (P x * Q x)) := by
    congr 1
    funext x
    ring
  rw [h1, E₁_coord_mul_lowPoly_homog hP hQ i,
    E₁_coord_mul' hP.contDiff hP.growth i (hP.pd_growth i)]
  ring

theorem Cov₁_add_left {P₁ P₂ Q : EuclidD d → ℝ} (h1c : Continuous P₁) (h1g : HasPolynomialGrowth P₁)
    (h2c : Continuous P₂) (h2g : HasPolynomialGrowth P₂) (hQc : Continuous Q)
    (hQg : HasPolynomialGrowth Q) :
    Cov₁ (fun x ↦ P₁ x + P₂ x) Q = Cov₁ P₁ Q + Cov₁ P₂ Q := by
  have hfun : (fun x ↦ P₁ x + P₂ x) = P₁ + P₂ := by
    funext x
    rfl
  rw [hfun, gaussianCovariance_comm, gaussianCovariance_add_right Matrix.PosDef.one hQc hQg h1c
    h1g h2c h2g, gaussianCovariance_comm (f := Q), gaussianCovariance_comm (f := Q)]

theorem Cov₁_const_mul_left (c : ℝ) (P Q : EuclidD d → ℝ) :
    Cov₁ (fun x ↦ c * P x) Q = c * Cov₁ P Q := by
  have : (fun x ↦ c * P x) = c • P := by
    funext x
    simp
  rw [gaussianCovariance_comm, this, gaussianCovariance_const_smul_right, gaussianCovariance_comm]

theorem Cov₁_const_left (c : ℝ) (Q : EuclidD d → ℝ) : Cov₁ (fun _ ↦ c) Q = 0 := by
  unfold gaussianCovariance
  rw [E₁_const, ← gaussianExpectation_const_mul]
  simp

/-! ### The three annihilation conditions -/

/-- Covariances with all monomial words of length `≤ t` vanish. -/
def CovWords (t : ℕ) (Q : EuclidD d → ℝ) : Prop :=
  ∀ q ≤ t, ∀ w : Fin q → Fin d, Cov₁ (monomialTest w) Q = 0

/-- Covariances with all polynomials of degree `≤ t` vanish. -/
def CovLow (t : ℕ) (Q : EuclidD d → ℝ) : Prop :=
  ∀ q ≤ t, ∀ P : EuclidD d → ℝ, LowPoly q P → Cov₁ P Q = 0

/-- Mixed moments `E[P ∂_w Q]` vanish for `1 ≤ |w|`, `deg P + |w| ≤ t`. -/
def MixedZero (t : ℕ) (Q : EuclidD d → ℝ) : Prop :=
  ∀ q (P : EuclidD d → ℝ), LowPoly q P → ∀ w : List (Fin d), 1 ≤ w.length → q + w.length ≤ t →
    E₁ (fun x ↦ P x * wordPD w Q x) = 0

/-- Derivative expectations `E[∂_w Q]` vanish for `1 ≤ |w| ≤ t`. -/
def DerivExpZero (t : ℕ) (Q : EuclidD d → ℝ) : Prop :=
  ∀ w : List (Fin d), 1 ≤ w.length → w.length ≤ t → E₁ (wordPD w Q) = 0

variable {k : ℕ} {Q : EuclidD d → ℝ} (hQ : SmoothHomog k Q)
include hQ

omit hQ in
theorem SmoothHomog.derivExpZero_of_mixedZero {t : ℕ} (h : MixedZero t Q) : DerivExpZero t Q := by
  intro w hw1 hwt
  have := h 0 (fun _ ↦ 1) (LowPoly.const 0 1) w hw1 (by simpa using hwt)
  simpa using this

/-- One level of `J_t ⇒ M_t`: from the lower levels. -/
theorem SmoothHomog.mixed_step {t q : ℕ} (hJ : DerivExpZero t Q)
    (hlow : ∀ q' < q, ∀ P : EuclidD d → ℝ, LowPoly q' P → ∀ w : List (Fin d), 1 ≤ w.length →
      q' + w.length ≤ t → E₁ (fun x ↦ P x * wordPD w Q x) = 0)
    {P : EuclidD d → ℝ} (hP : LowPoly q P) :
    ∀ w : List (Fin d), 1 ≤ w.length → q + w.length ≤ t → E₁ (fun x ↦ P x * wordPD w Q x) = 0 := by
  induction hP with
  | const q c =>
    intro w hw1 hwt
    rw [gaussianExpectation_const_mul, hJ w hw1 (by omega), mul_zero]
  | @coord_mul q' i P' hP' _ =>
    intro w hw1 hwt
    have hF := hQ.wordDeriv w
    have h1 : E₁ (fun x ↦ (fun x ↦ x i * P' x) x * wordPD w Q x) =
        E₁ (fun x ↦ x i * (P' x * wordPD w Q x)) := by
      congr 1
      funext x
      ring
    rw [h1, E₁_coord_mul_lowPoly_homog hP' hF i]
    have hA := hlow q' (by omega) (pd i P') (hP'.pd_lowPoly i) w hw1 (by omega)
    have hB := hlow q' (by omega) P' hP' (i :: w) (by simp) (by simp; omega)
    rw [wordPD_cons] at hB
    rw [hA, hB, add_zero]
  | @add q P₁ P₂ hP₁ hP₂ ih₁ ih₂ =>
    intro w hw1 hwt
    have hF := hQ.wordDeriv w
    have h1 : (fun x ↦ (fun x ↦ P₁ x + P₂ x) x * wordPD w Q x) =
        fun x ↦ P₁ x * wordPD w Q x + P₂ x * wordPD w Q x := by
      funext x
      ring
    rw [h1, E₁_add' (f := fun x ↦ P₁ x * wordPD w Q x) (g := fun x ↦ P₂ x * wordPD w Q x)
      (hP₁.contDiff.continuous.mul hF.smooth.continuous) (hP₁.growth.mul hF.growth)
      (hP₂.contDiff.continuous.mul hF.smooth.continuous) (hP₂.growth.mul hF.growth),
      ih₁ hlow w hw1 hwt, ih₂ hlow w hw1 hwt, add_zero]
  | @smul q c P' hP' ih =>
    intro w hw1 hwt
    have h1 : (fun x ↦ (fun x ↦ c * P' x) x * wordPD w Q x) =
        fun x ↦ c * (P' x * wordPD w Q x) := by
      funext x
      ring
    rw [h1, gaussianExpectation_const_mul, ih hlow w hw1 hwt, mul_zero]
  | @mono q' P' hP' _ =>
    intro w hw1 hwt
    exact hlow q' (by omega) P' hP' w hw1 (by omega)

theorem SmoothHomog.mixedZero_of_derivExpZero {t : ℕ} (hJ : DerivExpZero t Q) : MixedZero t Q := by
  intro q
  induction q using Nat.strong_induction_on with
  | _ q ih => exact fun P hP ↦ hQ.mixed_step hJ (fun q' hq' P' hP' ↦ ih q' hq' P' hP') hP

/-- One level of `M_t ⇒ C'_t`. -/
theorem SmoothHomog.covLow_step {t q : ℕ} (hM : MixedZero t Q) (hqt : q ≤ t)
    (hlow : ∀ q' < q, ∀ P : EuclidD d → ℝ, LowPoly q' P → Cov₁ P Q = 0)
    {P : EuclidD d → ℝ} (hP : LowPoly q P) : Cov₁ P Q = 0 := by
  induction hP with
  | const q c => exact Cov₁_const_left c Q
  | @coord_mul q' i P' hP' _ =>
    rw [Cov₁_coord_mul_lowPoly hP' hQ i]
    have hA := hM q' P' hP' [i] (by simp) (by simp; omega)
    rw [wordPD_cons, wordPD_nil] at hA
    rw [hA, hlow q' (by omega) (pd i P') (hP'.pd_lowPoly i), add_zero]
  | @add q P₁ P₂ hP₁ hP₂ ih₁ ih₂ =>
    rw [Cov₁_add_left hP₁.contDiff.continuous hP₁.growth hP₂.contDiff.continuous hP₂.growth
      hQ.smooth.continuous hQ.growth, ih₁ hqt hlow, ih₂ hqt hlow, add_zero]
  | @smul q c P' hP' ih =>
    rw [Cov₁_const_mul_left, ih hqt hlow, mul_zero]
  | @mono q' P' hP' _ =>
    exact hlow q' (by omega) P' hP'

theorem SmoothHomog.covLow_of_mixedZero {t : ℕ} (hM : MixedZero t Q) : CovLow t Q := by
  intro q
  induction q using Nat.strong_induction_on with
  | _ q ih =>
    exact fun hqt P hP ↦ hQ.covLow_step hM hqt (fun q' hq' P' hP' ↦ ih q' hq' (by omega) P' hP') hP

omit hQ in
theorem covWords_of_covLow {t : ℕ} (h : CovLow t Q) : CovWords t Q :=
  fun q hqt w ↦ h q hqt _ (lowPoly_monomialTest w)

omit hQ in
/-- A list monomial is a monomial word. -/
theorem listMon_eq_monomialTest : ∀ v : List (Fin d),
    listMon v = monomialTest (fun j : Fin v.length ↦ v.get j)
  | [] => by
    funext x
    simp [monomialTest]
  | i :: v => by
    funext x
    rw [listMon_cons, listMon_eq_monomialTest v]
    simp only [monomialTest, List.length_cons, Fin.prod_univ_succ, List.get_cons_zero,
      List.get_cons_succ']

omit hQ in
/-- `C_t ⇒ C'_t`: covariances with all low-degree polynomials vanish once they vanish on words,
by structural induction with an auxiliary word factor. -/
theorem covLow_of_covWords {t : ℕ} (hQc : Continuous Q) (hQg : HasPolynomialGrowth Q)
    (h : CovWords t Q) : CovLow t Q := by
  have key : ∀ {q : ℕ} {P : EuclidD d → ℝ}, LowPoly q P → ∀ v : List (Fin d),
      v.length + q ≤ t → Cov₁ (fun x ↦ listMon v x * P x) Q = 0 := by
    intro q P hP
    induction hP with
    | const q c =>
      intro v hv
      have : (fun x ↦ listMon v x * c) = fun x ↦ c * listMon v x := by
        funext x
        ring
      rw [this, Cov₁_const_mul_left, listMon_eq_monomialTest, h v.length (by omega), mul_zero]
    | @coord_mul q' i P' _ ih =>
      intro v hv
      have : (fun x ↦ listMon v x * (x i * P' x)) = fun x ↦ listMon (i :: v) x * P' x := by
        funext x
        rw [listMon_cons]
        ring
      rw [this]
      exact ih (i :: v) (by simp; omega)
    | @add q P₁ P₂ hP₁ hP₂ ih₁ ih₂ =>
      intro v hv
      have : (fun x ↦ listMon v x * (P₁ x + P₂ x)) =
          fun x ↦ listMon v x * P₁ x + listMon v x * P₂ x := by
        funext x
        ring
      have hv' := (SmoothHomog.listMonomial v)
      rw [this, Cov₁_add_left (P₁ := fun x ↦ listMon v x * P₁ x) (P₂ := fun x ↦ listMon v x * P₂ x)
        (hv'.smooth.continuous.mul hP₁.contDiff.continuous)
        (hv'.growth.mul hP₁.growth) (hv'.smooth.continuous.mul hP₂.contDiff.continuous)
        (hv'.growth.mul hP₂.growth) hQc hQg, ih₁ v hv, ih₂ v hv, add_zero]
    | @smul q c P' _ ih =>
      intro v hv
      have : (fun x ↦ listMon v x * (c * P' x)) = fun x ↦ c * (listMon v x * P' x) := by
        funext x
        ring
      rw [this, Cov₁_const_mul_left, ih v hv, mul_zero]
    | @mono q' P' _ ih =>
      intro v hv
      exact ih v (by omega)
  intro q hqt P hP
  have := key hP [] (by simpa using hqt)
  simpa using this

/-- `C'_t ⇒ M_t`: induction on the derivative word. -/
theorem SmoothHomog.mixedZero_of_covLow {t : ℕ} (h : CovLow t Q) : MixedZero t Q := by
  intro q P hP w
  induction w generalizing q P with
  | nil => intro h1; simp at h1
  | cons i u ih =>
    intro _ hwt
    rw [wordPD_cons]
    have hF := hQ.wordDeriv u
    -- `E[P ∂_i F] = E[x_i (P F)] − E[∂_i P · F]`
    have hstein := E₁_coord_mul_lowPoly_homog hP hF i
    have hE : E₁ (fun x ↦ P x * pd i (wordPD u Q) x) =
        E₁ (fun x ↦ x i * (P x * wordPD u Q x)) - E₁ (fun x ↦ pd i P x * wordPD u Q x) := by
      linarith
    rw [hE]
    rcases u with _ | ⟨j, u'⟩
    · -- `u = []`: use the centered identity
      simp only [wordPD_nil] at *
      have hc := Cov₁_coord_mul_lowPoly hP hQ i
      have h1 : Cov₁ (fun x ↦ x i * P x) Q = 0 :=
        h (q + 1) (by simp at hwt; omega) _ (LowPoly.coord_mul i hP)
      have h2 : Cov₁ (pd i P) Q = 0 := h q (by simp at hwt; omega) _ (hP.pd_lowPoly i)
      rw [h1, h2] at hc
      -- `hc : 0 = E[P ∂_i Q] + 0`; the target is `E[x_i (P Q)] − E[∂_i P Q]`, equal to `E[P ∂_i Q]`
      have hstein' := E₁_coord_mul_lowPoly_homog hP hQ i
      linarith
    · -- `u = j :: u'` nonempty: both terms have the shorter word `u`
      have hA := ih (q + 1) (fun x ↦ x i * P x) (LowPoly.coord_mul i hP) (by simp)
        (by simp at hwt ⊢; omega)
      have hB := ih q (pd i P) (hP.pd_lowPoly i) (by simp) (by simp at hwt ⊢; omega)
      have hA' : E₁ (fun x ↦ x i * (P x * wordPD (j :: u') Q x)) = 0 := by
        rw [← hA]
        congr 1
        funext x
        ring
      rw [hA', hB, sub_zero]

/-- **The triangular equivalence**: covariances with all words of length `≤ t` vanish iff all
derivative expectations `E[∂_w Q]`, `1 ≤ |w| ≤ t`, vanish. -/
theorem SmoothHomog.covWords_iff_derivExpZero (t : ℕ) : CovWords t Q ↔ DerivExpZero t Q := by
  constructor
  · intro h
    exact SmoothHomog.derivExpZero_of_mixedZero (hQ.mixedZero_of_covLow
      (covLow_of_covWords hQ.smooth.continuous hQ.growth h))
  · intro h
    exact covWords_of_covLow (hQ.covLow_of_mixedZero (hQ.mixedZero_of_derivExpZero h))

/-! ### Derivative expectations are traces -/

omit hQ in
theorem SmoothHomog.iterate_lap {n : ℕ} {f : EuclidD d → ℝ} (hf : SmoothHomog n f) :
    ∀ r : ℕ, SmoothHomog (n - 2 * r) (lap^[r] f)
  | 0 => by simpa using hf
  | r + 1 => by
    rw [Function.iterate_succ_apply']
    have := (SmoothHomog.iterate_lap hf r).laplacian
    rwa [show n - 2 * r - 2 = n - 2 * (r + 1) by omega] at this

omit hQ in
theorem pd_zero_fun (i : Fin d) : pd i (fun _ : EuclidD d ↦ (0 : ℝ)) = fun _ ↦ 0 := by
  funext x
  simp [pd]

omit hQ in
theorem lap_zero_fun : lap (fun _ : EuclidD d ↦ (0 : ℝ)) = fun _ ↦ 0 := by
  funext x
  simp [lap, pd_zero_fun]

omit hQ in
theorem iterate_lap_zero_fun : ∀ r : ℕ, lap^[r] (fun _ : EuclidD d ↦ (0 : ℝ)) = fun _ ↦ 0
  | 0 => rfl
  | r + 1 => by rw [Function.iterate_succ_apply', iterate_lap_zero_fun r, lap_zero_fun]

omit hQ in
theorem wordPD_zero_fun : ∀ w : List (Fin d), wordPD w (fun _ : EuclidD d ↦ (0 : ℝ)) = fun _ ↦ 0
  | [] => rfl
  | i :: w => by rw [wordPD_cons, wordPD_zero_fun w, pd_zero_fun]

/-- `E[∂_w Q] = 0` when `k − |w|` is odd. -/
theorem SmoothHomog.E₁_wordPD_odd (w : List (Fin d)) (hodd : (k - w.length) % 2 = 1) :
    E₁ (wordPD w Q) = 0 := by
  unfold gaussianExpectation
  rw [(integral_smoothHomog_K₁ (k - w.length) _ (hQ.wordDeriv w)).1 hodd, zero_div]

/-- `E[∂_w Q] = (∂_w Δ^a Q)(0) / (2a)!!` when `k − |w| = 2a`. -/
theorem SmoothHomog.E₁_wordPD_even (w : List (Fin d)) {a : ℕ} (hev : k - w.length = 2 * a) :
    E₁ (wordPD w Q) = wordPD w (lap^[a] Q) 0 / dfac2 a := by
  unfold gaussianExpectation
  rw [(integral_smoothHomog_K₁ (k - w.length) _ (hQ.wordDeriv w)).2 a hev,
    wordPD_iterate_lap_comm hQ.smooth a w,
    mul_div_assoc, div_self (integral_quadKernel_pos Matrix.PosDef.one).ne', mul_one]

/-! ### The core kernel theorem -/

/-- **The trace kernel**: for `Q` smooth homogeneous of degree `s + 2r` with `s ≥ 1`, the
covariances with all monomial words of length `≤ s` vanish iff `Δ^r Q = 0`. -/
theorem SmoothHomog.covWords_iff_iterate_lap_eq_zero {s r : ℕ} (hs : 1 ≤ s) (hk : k = s + 2 * r) :
    CovWords s Q ↔ lap^[r] Q = 0 := by
  rw [hQ.covWords_iff_derivExpZero]
  have hR : SmoothHomog s (lap^[r] Q) := by
    have := hQ.iterate_lap r
    rwa [hk, Nat.add_sub_cancel] at this
  constructor
  · intro hJ
    refine SmoothHomog.eq_zero_of_wordPD_zero s (lap^[r] Q) hR fun w hw ↦ ?_
    have h := hJ w (by omega) hw.le
    rw [hQ.E₁_wordPD_even w (a := r) (by omega)] at h
    exact (div_eq_zero_iff.mp h).resolve_right (dfac2_pos r).ne'
  · intro hzero w hw1 hws
    rcases Nat.even_or_odd (k - w.length) with ⟨a, ha⟩ | ⟨a, ha⟩
    · -- `k − |w| = 2a` with `a ≥ r`
      have hak : k - w.length = 2 * a := by omega
      rw [hQ.E₁_wordPD_even w hak]
      obtain ⟨b, hb⟩ : ∃ b, a = b + r := ⟨a - r, by omega⟩
      rw [hb, Function.iterate_add_apply, hzero, show (0 : EuclidD d → ℝ) = fun _ ↦ 0 from rfl,
        iterate_lap_zero_fun, wordPD_zero_fun]
      simp
    · exact hQ.E₁_wordPD_odd w (by omega)

/-- Tests of the wrong parity vanish automatically: if `|w| + k` is odd then
`Cov(x^w, Q) = 0`. -/
theorem SmoothHomog.Cov₁_monomialTest_eq_zero_of_odd {q : ℕ} (w : Fin q → Fin d)
    (hodd : (q + k) % 2 = 1) : Cov₁ (monomialTest w) Q = 0 := by
  have hw : SmoothHomog q (monomialTest w) :=
    ⟨(contDiff_of_mem_homogPolySpan (monomialTest_mem_homogPolySpan w)),
      monomialTest_isHomogeneous w⟩
  unfold gaussianCovariance gaussianExpectation
  have hprod := (integral_smoothHomog_K₁ (q + k) _ (hw.mul hQ)).1 hodd
  rw [hprod, zero_div]
  rcases Nat.even_or_odd q with ⟨a, ha⟩ | ⟨a, ha⟩
  · have hk : k % 2 = 1 := by omega
    rw [(integral_smoothHomog_K₁ k Q hQ).1 hk]
    simp
  · have hq : q % 2 = 1 := by omega
    rw [(integral_smoothHomog_K₁ q _ hw).1 hq]
    simp

/-- **The general design degree.** For `Q` smooth homogeneous of degree `k = s + 2r` with
`1 ≤ s ≤ m ≤ s + 1` (so `s` is the largest degree `≤ m` of the parity of `k`), the degree-`≤ m`
monomial design annihilates `Q` iff `Δ^r Q = 0`. -/
theorem SmoothHomog.trace_kernel_iff {m s r : ℕ} (hs : 1 ≤ s) (hk : k = s + 2 * r) (hsm : s ≤ m)
    (hms : m ≤ s + 1) : CovWords m Q ↔ lap^[r] Q = 0 := by
  rw [← hQ.covWords_iff_iterate_lap_eq_zero hs hk]
  constructor
  · intro h q hq w
    exact h q (by omega) w
  · intro h q hq w
    rcases Nat.lt_or_ge q (s + 1) with hlt | hge
    · exact h q (by omega) w
    · have hqs : q = s + 1 := by omega
      exact hQ.Cov₁_monomialTest_eq_zero_of_odd w (by omega)

/-- **Beyond the design degree with no compatible parity**: if `m = 0`, or `m = 1` and `k` is
even, the design sees nothing of `Q`. -/
theorem SmoothHomog.covWords_of_no_parity {m : ℕ} (hm : m = 0 ∨ (m = 1 ∧ k % 2 = 0)) :
    CovWords m Q := by
  intro q hq w
  rcases hm with rfl | ⟨rfl, hk2⟩
  · have hq0 : q = 0 := by omega
    subst hq0
    have : monomialTest w = fun _ ↦ (1 : ℝ) := by
      funext x
      simp [monomialTest]
    rw [this]
    exact Cov₁_const_left 1 Q
  · rcases Nat.lt_or_ge q 1 with h0 | h1
    · have hq0 : q = 0 := by omega
      subst hq0
      have : monomialTest w = fun _ ↦ (1 : ℝ) := by
        funext x
        simp [monomialTest]
      rw [this]
      exact Cov₁_const_left 1 Q
    · have hq1 : q = 1 := by omega
      subst hq1
      exact hQ.Cov₁_monomialTest_eq_zero_of_odd w (by omega)

end Laplace.Multi
