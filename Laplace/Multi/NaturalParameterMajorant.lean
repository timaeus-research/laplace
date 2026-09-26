/-
Copyright (c) 2026 Timaeus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Timaeus
-/
import Laplace.Multi.FiniteCompletionClosure

/-!
# Explicit factorial bounds along natural-parameter lines (series-free)

Along the natural-parameter line `t ↦ [q_{θ + t v}] ∈ L¹(ν)`, with `Y = ⟨v, S⟩` bounded by `L > 0`
and `ρ = log(3/2)/L`:

* `natZ_smul_natCurve`: the normalised identity `Z(t) • p(t) = w(t)` with `w(t) = [q_θ e^{−tY}]` and
  `Z(t) = E_{Q_θ} e^{−tY}`;
* `norm_iteratedDeriv_natW_le`, `abs_iteratedDeriv_natZ_le`: `‖w^{(k)}(t)‖₁ ≤ L^k Z(t)`,
  `|Z^{(j)}(t)| ≤ L^j Z(t)` (the jets of `w` are the pointwise jets `[q_θ (−Y)^k e^{−tY}]`);
* **`norm_iteratedDeriv_natCurve_le_rec`**: the Leibniz recurrence
  `b_k ≤ L^k + Σ_{i<k} C(k,i+1) L^{i+1} b_{k−(i+1)}` for `b_k = ‖p^{(k)}(t)‖₁`;
* `sum_weighted_le_three`: the purely numerical majorant lemma — any sequence obeying the
  recurrence has `Σ_{k≤N} ρ^k b_k / k! ≤ 3`;
* **`sum_norm_iteratedDeriv_natCurve_le`**: `Σ_{k≤N} ρ^k ‖p^{(k)}(t)‖₁ / k! ≤ 3` at every `t`,
  hence **`norm_iteratedDeriv_natCurve_le`**: `‖p^{(k)}(t)‖₁ ≤ 3 k! ρ^{−k}` — explicit Cauchy-type
  estimates for the analytic tilt map, with no power series.
-/

open MeasureTheory Filter Topology Set Finset
open scoped ContDiff

namespace Laplace.Multi

section Numerics

/-- The triangle rearrangement
`Σ_{k≤N} Σ_{i<k} a(i+1) c(k−(i+1)) = Σ_{i<N} a(i+1) Σ_{m<N−i} c m`. -/
theorem sum_range_convolution (a c : ℕ → ℝ) (N : ℕ) :
    ∑ k ∈ range (N + 1), ∑ i ∈ range k, a (i + 1) * c (k - (i + 1)) =
      ∑ i ∈ range N, a (i + 1) * ∑ m ∈ range (N - i), c m := by
  induction N with
  | zero => simp
  | succ N ih =>
    rw [sum_range_succ, ih]
    conv_rhs => rw [sum_range_succ]
    have e : ∀ i ∈ range N, a (i + 1) * ∑ m ∈ range (N + 1 - i), c m =
        a (i + 1) * ∑ m ∈ range (N - i), c m + a (i + 1) * c (N - i) := fun i hi ↦ by
      have hi' : i < N := mem_range.1 hi
      rw [show N + 1 - i = N - i + 1 by omega, sum_range_succ, mul_add]
    rw [sum_congr rfl e, sum_add_distrib,
      sum_range_succ (f := fun i ↦ a (i + 1) * c (N + 1 - (i + 1)))]
    have e2 : ∀ i ∈ range N, a (i + 1) * c (N + 1 - (i + 1)) = a (i + 1) * c (N - i) :=
      fun i _ ↦ by rw [show N + 1 - (i + 1) = N - i by omega]
    rw [sum_congr rfl e2]
    simp only [Nat.sub_self, Nat.add_sub_cancel_left, range_one, sum_singleton]
    ring

/-- **The majorant lemma**: a sequence with `b_k ≤ L^k + Σ_{i<k} C(k,i+1) L^{i+1} b_{k−i−1}` has
`Σ_{k≤N} ρ^k b_k/k! ≤ 3` for `ρ = log(3/2)/L`. -/
theorem sum_weighted_le_three {L : ℝ} (hL : 0 < L) {b : ℕ → ℝ}
    (hrec : ∀ k, b k ≤ L ^ k +
      ∑ i ∈ range k, (k.choose (i + 1) : ℝ) * L ^ (i + 1) * b (k - (i + 1)))
    (N : ℕ) : ∑ k ∈ range (N + 1), (Real.log (3 / 2) / L) ^ k * b k / k.factorial ≤ 3 := by
  set ρ := Real.log (3 / 2) / L with hρ
  have hρ0 : 0 ≤ ρ := div_nonneg (Real.log_nonneg (by norm_num)) hL.le
  have hexp : Real.exp (L * ρ) = 3 / 2 := by
    rw [hρ, mul_div_cancel₀ _ hL.ne', Real.exp_log (by norm_num)]
  obtain ⟨c, hc⟩ : ∃ c : ℕ → ℝ, c = fun k ↦ ρ ^ k * b k / k.factorial := ⟨_, rfl⟩
  obtain ⟨e, he⟩ : ∃ e : ℕ → ℝ, e = fun k ↦ (L * ρ) ^ k / k.factorial := ⟨_, rfl⟩
  have he0 : ∀ k, 0 ≤ e k := fun k ↦ by
    rw [he]
    positivity
  -- the weighted recurrence `c_k ≤ e_k + Σ_{i<k} e_{i+1} c_{k−(i+1)}`
  have hcrec : ∀ k, c k ≤ e k + ∑ i ∈ range k, e (i + 1) * c (k - (i + 1)) := fun k ↦ by
    rw [hc, he]
    simp only
    have h := hrec k
    have hk : (0 : ℝ) < k.factorial := by positivity
    rw [div_le_iff₀ hk]
    calc ρ ^ k * b k ≤ ρ ^ k * (L ^ k + ∑ i ∈ range k, (k.choose (i + 1) : ℝ) * L ^ (i + 1) *
          b (k - (i + 1))) := mul_le_mul_of_nonneg_left h (pow_nonneg hρ0 _)
      _ = ((L * ρ) ^ k / k.factorial + ∑ i ∈ range k,
            (L * ρ) ^ (i + 1) / (i + 1).factorial *
              (ρ ^ (k - (i + 1)) * b (k - (i + 1)) / (k - (i + 1)).factorial)) * k.factorial := by
          rw [add_mul, sum_mul, mul_add, mul_sum]
          congr 1
          · rw [mul_pow]
            field_simp
          · refine sum_congr rfl fun i hi ↦ ?_
            have hi' : i + 1 ≤ k := mem_range.1 hi
            have hchoose : (k.choose (i + 1) : ℝ) =
                k.factorial / ((i + 1).factorial * (k - (i + 1)).factorial) := by
              rw [Nat.choose_eq_factorial_div_factorial hi', Nat.cast_div
                (Nat.factorial_mul_factorial_dvd_factorial hi') (by positivity), Nat.cast_mul]
            rw [hchoose]
            have e3 : ρ ^ k = ρ ^ (i + 1) * ρ ^ (k - (i + 1)) := by
              rw [← pow_add, Nat.add_sub_cancel' hi']
            rw [e3, mul_pow]
            field_simp
  -- the partial sums of the exponential series
  have hE1 : ∀ K : ℕ, ∑ k ∈ range (K + 1), e k ≤ 3 / 2 := fun K ↦ by
    rw [he]
    exact (Real.sum_le_exp_of_nonneg (by positivity) _).trans hexp.le
  have hE2 : ∀ N : ℕ, ∑ i ∈ range N, e (i + 1) ≤ 3 / 2 - 1 := fun N ↦ by
    have h := Real.sum_le_exp_of_nonneg (x := L * ρ) (by positivity) (N + 1)
    rw [sum_range_succ', hexp] at h
    simp only [pow_zero, Nat.factorial_zero, Nat.cast_one, div_one] at h
    simp only [he]
    linarith
  -- strong induction on `N`
  induction N using Nat.strong_induction_on with
  | _ N ih =>
    have hsplit : ∀ K, ∑ k ∈ range (K + 1), ρ ^ k * b k / k.factorial = ∑ k ∈ range (K + 1), c k :=
      fun K ↦ by rw [hc]
    rw [hsplit]
    have hIH : ∀ i ∈ range N, ∑ m ∈ range (N - i), c m ≤ 3 := fun i hi ↦ by
      have hi' : i < N := mem_range.1 hi
      have := ih (N - i - 1) (by omega)
      rw [hsplit, show N - i - 1 + 1 = N - i by omega] at this
      exact this
    calc ∑ k ∈ range (N + 1), c k ≤
          ∑ k ∈ range (N + 1), (e k + ∑ i ∈ range k, e (i + 1) * c (k - (i + 1))) :=
          sum_le_sum fun k _ ↦ hcrec k
      _ = ∑ k ∈ range (N + 1), e k + ∑ i ∈ range N, e (i + 1) * ∑ m ∈ range (N - i), c m := by
          rw [sum_add_distrib, sum_range_convolution]
      _ ≤ 3 / 2 + ∑ i ∈ range N, e (i + 1) * 3 :=
          add_le_add (hE1 N)
            (sum_le_sum fun i hi ↦ mul_le_mul_of_nonneg_left (hIH i hi) (he0 _))
      _ ≤ 3 / 2 + (3 / 2 - 1) * 3 := by
          rw [← sum_mul]
          linarith [mul_le_mul_of_nonneg_right (hE2 N) (by norm_num : (0 : ℝ) ≤ 3)]
      _ = 3 := by norm_num

end Numerics

section Line

variable {X : Type*} [MeasurableSpace X] [Nonempty X] {J : Type*} [Fintype J] [Nonempty J]
  {S : J → X → ℝ} (hS : ∀ j, Bdd (S j)) (ν : Measure X) [IsProbabilityMeasure ν] (θ v : J → ℝ)
include hS

/-- The natural-parameter curve `t ↦ [q_{θ + t v}] ∈ L¹(ν)`. -/
noncomputable def natCurve (t : ℝ) : X →₁[ν] ℝ := densL1 hS ν (θ + t • v)

omit hS in
variable (S) in
/-- The normaliser ratio `Z(t) = Z(θ + tv)/Z(θ) = E_{Q_θ} e^{−tY}`. -/
noncomputable def natZ (t : ℝ) : ℝ := famZ S ν (θ + t • v) / famZ S ν θ

/-- The unnormalised curve `w(t) = [q_θ e^{−tY}]`. -/
noncomputable def natW (t : ℝ) : X →₁[ν] ℝ :=
  (famZ S ν θ)⁻¹ • weightL1 hS ν (Bdd.const 1) (θ + t • v)

omit [Nonempty X] [Nonempty J] in
theorem natZ_pos (t : ℝ) : 0 < natZ S ν θ v t := div_pos (famZ_pos hS ν _) (famZ_pos hS ν _)

omit [Nonempty X] [Nonempty J] in
/-- **The normalised identity** `Z(t) • p(t) = w(t)`. -/
theorem natZ_smul_natCurve (t : ℝ) :
    natZ S ν θ v t • natCurve hS ν θ v t = natW hS ν θ v t := by
  unfold natZ natCurve natW
  rw [densL1_eq, smul_smul]
  congr 1
  rw [div_mul_eq_mul_div, mul_inv_cancel₀ (famZ_pos hS ν _).ne', one_div]

omit [Nonempty X] [Nonempty J] in
theorem natW_eq_smul (t : ℝ) : natW hS ν θ v t = natZ S ν θ v t • natCurve hS ν θ v t :=
  (natZ_smul_natCurve hS ν θ v t).symm

omit [Nonempty J] in
theorem contDiff_natCurve : ContDiff ℝ ∞ (natCurve hS ν θ v) :=
  (contDiff_densL1 hS ν).comp (contDiff_const.add (contDiff_id.smul contDiff_const))

omit [Nonempty J] in
theorem contDiff_natZ : ContDiff ℝ ∞ (natZ S ν θ v) :=
  ((contDiff_famZ hS ν).comp (contDiff_const.add (contDiff_id.smul contDiff_const))).div_const _

omit [Nonempty X] [Nonempty J] in
theorem contDiff_natW : ContDiff ℝ ∞ (natW hS ν θ v) :=
  ((contDiff_infty_weightL1 hS ν (Bdd.const 1)).comp
    (contDiff_const.add (contDiff_id.smul contDiff_const))).const_smul _

omit [Nonempty X] [Nonempty J] hS [IsProbabilityMeasure ν] in
/-- The pointwise tilt identity `q_θ(x) e^{−tY(x)} = Z(θ)⁻¹ e^{−⟨θ + tv, S(x)⟩}`. -/
theorem famDens_mul_exp_eq (t : ℝ) (x : X) :
    famDens S ν θ x * Real.exp (-t * dirLoss S v x) =
      (famZ S ν θ)⁻¹ * famWeight S (θ + t • v) x := by
  have e : dirLoss S (θ + t • v) x = dirLoss S θ x + t * dirLoss S v x := by
    rw [dirLoss_add, dirLoss_smul]
  unfold famDens famWeight
  rw [e, neg_add, Real.exp_add]
  field_simp

omit hS in
variable (S) in
/-- The pointwise jets of the unnormalised curve. -/
noncomputable def natWJet (k : ℕ) (t : ℝ) (x : X) : ℝ :=
  famDens S ν θ x * ((-dirLoss S v x) ^ k * Real.exp (-t * dirLoss S v x))

omit [Nonempty X] [Nonempty J] hS [IsProbabilityMeasure ν] in
variable (S) in
theorem hasDerivAt_natWJet (k : ℕ) (t : ℝ) (x : X) :
    HasDerivAt (fun u ↦ natWJet S ν θ v k u x) (natWJet S ν θ v (k + 1) t x) t := by
  have h : HasDerivAt (fun u ↦ Real.exp (-u * dirLoss S v x))
      (Real.exp (-t * dirLoss S v x) * (-dirLoss S v x)) t := by
    have := ((hasDerivAt_id t).neg.mul_const (dirLoss S v x)).exp
    simpa using this
  have h2 := h.const_mul (famDens S ν θ x * (-dirLoss S v x) ^ k)
  refine (h2.congr_of_eventuallyEq (Eventually.of_forall fun u ↦ ?_)).congr_deriv ?_
  · unfold natWJet
    ring
  · unfold natWJet
    ring

omit [Nonempty X] [Nonempty J] in
theorem coeFn_natW (t : ℝ) :
    ((natW hS ν θ v t : X →₁[ν] ℝ) : X → ℝ) =ᵐ[ν] natWJet S ν θ v 0 t := by
  have h1 := Lp.coeFn_smul ((famZ S ν θ)⁻¹) (weightL1 hS ν (Bdd.const 1) (θ + t • v))
  have h2 := Integrable.coeFn_toL1 (integrable_mul_famWeight hS ν (Bdd.const 1) (θ + t • v))
  filter_upwards [h1, h2] with x hx1 hx2
  unfold natW
  rw [hx1, Pi.smul_apply]
  unfold weightL1
  rw [hx2, smul_eq_mul]
  unfold natWJet
  simp only [pow_zero, one_mul]
  rw [famDens_mul_exp_eq]

omit [Nonempty X] [Nonempty J] in
/-- **The jets of the unnormalised curve are the pointwise jets** `[q_θ (−Y)^k e^{−tY}]`. -/
theorem coeFn_iteratedDeriv_natW (k : ℕ) (t : ℝ) :
    ((iteratedDeriv k (natW hS ν θ v) t : X →₁[ν] ℝ) : X → ℝ) =ᵐ[ν] natWJet S ν θ v k t := by
  induction k generalizing t with
  | zero =>
    rw [iteratedDeriv_zero]
    exact coeFn_natW hS ν θ v t
  | succ k ih =>
    refine coeFn_hasDerivAt_L1_ae ν (hasDerivAt_iteratedDeriv_of_contDiffOn isOpen_univ
      (contDiff_natW hS ν θ v).contDiffOn k (mem_univ t))
      (Eventually.of_forall fun u ↦ ih u)
      fun x ↦ hasDerivAt_natWJet S ν θ v k t x

omit [Nonempty X] [Nonempty J] in
theorem integrable_natWJet (k : ℕ) (t : ℝ) : Integrable (natWJet S ν θ v k t) ν :=
  (L1.integrable_coeFn _).congr (coeFn_iteratedDeriv_natW hS ν θ v k t)

omit [Nonempty X] [Nonempty J] hS [IsProbabilityMeasure ν] in
/-- `Z(t) = ∫ q_θ e^{−tY} dν`. -/
theorem natZ_eq_integral (t : ℝ) : natZ S ν θ v t = ∫ x, natWJet S ν θ v 0 t x ∂ν := by
  have e : ∀ x, natWJet S ν θ v 0 t x = (famZ S ν θ)⁻¹ * famWeight S (θ + t • v) x := fun x ↦ by
    unfold natWJet
    simp only [pow_zero, one_mul]
    exact famDens_mul_exp_eq ν θ v t x
  simp_rw [e]
  rw [integral_const_mul]
  unfold natZ famZ
  rw [div_eq_inv_mul]

variable {L : ℝ} (hY : ∀ x, |dirLoss S v x| ≤ L)
include hY

omit [Nonempty J] in
/-- `‖w^{(k)}(t)‖₁ ≤ L^k Z(t)`. -/
theorem norm_iteratedDeriv_natW_le (k : ℕ) (t : ℝ) :
    ‖iteratedDeriv k (natW hS ν θ v) t‖ ≤ L ^ k * natZ S ν θ v t := by
  have hL0 : 0 ≤ L := (abs_nonneg _).trans (hY (Classical.arbitrary X))
  have hae : (fun a ↦ ‖((iteratedDeriv k (natW hS ν θ v) t : X →₁[ν] ℝ) : X → ℝ) a‖) =ᵐ[ν]
      fun a ↦ ‖natWJet S ν θ v k t a‖ :=
    (coeFn_iteratedDeriv_natW hS ν θ v k t).mono fun a ha ↦ by
      beta_reduce
      rw [ha]
  rw [L1.norm_eq_integral_norm, natZ_eq_integral ν θ v, ← integral_const_mul,
    integral_congr_ae hae]
  refine integral_mono (integrable_natWJet hS ν θ v k t).norm
    ((integrable_natWJet hS ν θ v 0 t).const_mul _) fun x ↦ ?_
  simp only [natWJet, Real.norm_eq_abs, pow_zero, one_mul]
  have hq := famDens_nonneg hS ν θ x
  have he := (Real.exp_pos (-t * dirLoss S v x)).le
  rw [abs_mul, abs_mul, abs_of_nonneg hq, abs_of_nonneg he, abs_pow, abs_neg]
  have := pow_le_pow_left₀ (abs_nonneg _) (hY x) k
  calc famDens S ν θ x * (|dirLoss S v x| ^ k * Real.exp (-t * dirLoss S v x)) ≤
        famDens S ν θ x * (L ^ k * Real.exp (-t * dirLoss S v x)) := by gcongr
    _ = L ^ k * (famDens S ν θ x * Real.exp (-t * dirLoss S v x)) := by ring

omit [Nonempty X] [Nonempty J] hY in
/-- `Z^{(j)}(t) = ∫ w^{(j)}(t)`. -/
theorem iteratedDeriv_natZ_eq (j : ℕ) (t : ℝ) :
    iteratedDeriv j (natZ S ν θ v) t = L1.integralCLM (iteratedDeriv j (natW hS ν θ v) t) := by
  have e : natZ S ν θ v = fun t ↦ L1.integralCLM (natW hS ν θ v t) := by
    funext t
    rw [← L1.integral_eq, L1.integral_eq_integral, natZ_eq_integral ν θ v]
    exact integral_congr_ae (coeFn_natW hS ν θ v t).symm
  rw [e]
  have h := (L1.integralCLM : (X →₁[ν] ℝ) →L[ℝ] ℝ).iteratedFDeriv_comp_left
    (contDiff_natW hS ν θ v).contDiffAt (x := t) (i := j) (by exact_mod_cast natCast_le_infty j)
  rw [iteratedDeriv_eq_iteratedFDeriv, iteratedDeriv_eq_iteratedFDeriv]
  change iteratedFDeriv ℝ j (L1.integralCLM ∘ natW hS ν θ v) t (fun _ ↦ 1) = _
  rw [h]
  rfl

omit [Nonempty J] in
/-- `|Z^{(j)}(t)| ≤ L^j Z(t)`. -/
theorem abs_iteratedDeriv_natZ_le (j : ℕ) (t : ℝ) :
    |iteratedDeriv j (natZ S ν θ v) t| ≤ L ^ j * natZ S ν θ v t := by
  rw [iteratedDeriv_natZ_eq hS ν θ v, ← Real.norm_eq_abs]
  refine ((L1.integralCLM : (X →₁[ν] ℝ) →L[ℝ] ℝ).le_opNorm _).trans ?_
  calc ‖(L1.integralCLM : (X →₁[ν] ℝ) →L[ℝ] ℝ)‖ * ‖iteratedDeriv j (natW hS ν θ v) t‖ ≤
        1 * ‖iteratedDeriv j (natW hS ν θ v) t‖ :=
        mul_le_mul_of_nonneg_right L1.norm_Integral_le_one (norm_nonneg _)
    _ ≤ L ^ j * natZ S ν θ v t := by
        rw [one_mul]
        exact norm_iteratedDeriv_natW_le hS ν θ v hY j t

omit [Nonempty J] hY in
/-- **Leibniz along the line**: `w^{(k)} = Σ_i C(k,i) Z^{(i)} • p^{(k−i)}`. -/
theorem iteratedDeriv_natW_eq_sum (k : ℕ) (t : ℝ) :
    iteratedDeriv k (natW hS ν θ v) t = ∑ i ∈ range (k + 1),
      k.choose i • (iteratedDeriv i (natZ S ν θ v) t •
        iteratedDeriv (k - i) (natCurve hS ν θ v) t) := by
  have e : natW hS ν θ v = natZ S ν θ v • natCurve hS ν θ v := funext fun t ↦ by
    rw [Pi.smul_apply', natW_eq_smul]
  rw [e]
  have hZ' := ((contDiff_natZ hS ν θ v).of_le (m := k)
    (by exact_mod_cast natCast_le_infty k)).contDiffAt (x := t)
  have hC' := ((contDiff_natCurve hS ν θ v).of_le (m := k)
    (by exact_mod_cast natCast_le_infty k)).contDiffAt (x := t)
  have h := iteratedDerivWithin_smul (mem_univ t) uniqueDiffOn_univ hZ'.contDiffWithinAt
    hC'.contDiffWithinAt (n := k)
  simpa only [iteratedDerivWithin_univ] using h

omit [Nonempty J] in
/-- **The Leibniz recurrence**: `b_k ≤ L^k + Σ_{i<k} C(k,i+1) L^{i+1} b_{k−(i+1)}` for
`b_k = ‖p^{(k)}(t)‖₁`. -/
theorem norm_iteratedDeriv_natCurve_le_rec (k : ℕ) (t : ℝ) :
    ‖iteratedDeriv k (natCurve hS ν θ v) t‖ ≤ L ^ k + ∑ i ∈ range k,
      (k.choose (i + 1) : ℝ) * L ^ (i + 1) *
        ‖iteratedDeriv (k - (i + 1)) (natCurve hS ν θ v) t‖ := by
  have hZ := natZ_pos hS ν θ v t
  have hL := iteratedDeriv_natW_eq_sum hS ν θ v k t
  rw [sum_range_succ', Nat.choose_zero_right, one_smul, iteratedDeriv_zero, Nat.sub_zero] at hL
  -- isolate the top term
  have hiso : natZ S ν θ v t • iteratedDeriv k (natCurve hS ν θ v) t =
      iteratedDeriv k (natW hS ν θ v) t - ∑ i ∈ range k,
        (k.choose (i + 1)) • (iteratedDeriv (i + 1) (natZ S ν θ v) t •
          iteratedDeriv (k - (i + 1)) (natCurve hS ν θ v) t) := by
    rw [hL, add_sub_cancel_left]
  have hnorm : natZ S ν θ v t * ‖iteratedDeriv k (natCurve hS ν θ v) t‖ ≤
      natZ S ν θ v t * (L ^ k + ∑ i ∈ range k, (k.choose (i + 1) : ℝ) * L ^ (i + 1) *
        ‖iteratedDeriv (k - (i + 1)) (natCurve hS ν θ v) t‖) := by
    calc natZ S ν θ v t * ‖iteratedDeriv k (natCurve hS ν θ v) t‖ =
          ‖natZ S ν θ v t • iteratedDeriv k (natCurve hS ν θ v) t‖ := by
          rw [norm_smul, Real.norm_eq_abs, abs_of_pos hZ]
      _ ≤ ‖iteratedDeriv k (natW hS ν θ v) t‖ + ‖∑ i ∈ range k,
          (k.choose (i + 1)) • (iteratedDeriv (i + 1) (natZ S ν θ v) t •
            iteratedDeriv (k - (i + 1)) (natCurve hS ν θ v) t)‖ := by
          rw [hiso]
          exact norm_sub_le _ _
      _ ≤ L ^ k * natZ S ν θ v t + ∑ i ∈ range k,
          (k.choose (i + 1) : ℝ) * ((L ^ (i + 1) * natZ S ν θ v t) *
            ‖iteratedDeriv (k - (i + 1)) (natCurve hS ν θ v) t‖) := by
          refine add_le_add (norm_iteratedDeriv_natW_le hS ν θ v hY k t)
            ((norm_sum_le _ _).trans (sum_le_sum fun i _ ↦ ?_))
          rw [← Nat.cast_smul_eq_nsmul ℝ, norm_smul, norm_smul, Real.norm_natCast,
            Real.norm_eq_abs]
          exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right
            (abs_iteratedDeriv_natZ_le hS ν θ v hY (i + 1) t) (norm_nonneg _)) (by positivity)
      _ = natZ S ν θ v t * (L ^ k + ∑ i ∈ range k, (k.choose (i + 1) : ℝ) * L ^ (i + 1) *
          ‖iteratedDeriv (k - (i + 1)) (natCurve hS ν θ v) t‖) := by
          rw [mul_add, mul_sum]
          congr 1
          · ring
          · exact sum_congr rfl fun i _ ↦ by ring
  exact le_of_mul_le_mul_left hnorm hZ

omit [Nonempty J] in
/-- **Explicit factorial bounds along natural-parameter lines**:
`Σ_{k≤N} ρ^k ‖p^{(k)}(t)‖₁ / k! ≤ 3` with `ρ = log(3/2)/L`, at every `t`. -/
theorem sum_norm_iteratedDeriv_natCurve_le (hL : 0 < L) (t : ℝ) (N : ℕ) :
    ∑ k ∈ range (N + 1),
      (Real.log (3 / 2) / L) ^ k * ‖iteratedDeriv k (natCurve hS ν θ v) t‖ / k.factorial ≤ 3 :=
  sum_weighted_le_three hL (fun k ↦ norm_iteratedDeriv_natCurve_le_rec hS ν θ v hY k t) N

omit [Nonempty J] in
/-- **Cauchy-type estimate**: `‖p^{(k)}(t)‖₁ ≤ 3 k! ρ^{−k}`. -/
theorem norm_iteratedDeriv_natCurve_le (hL : 0 < L) (k : ℕ) (t : ℝ) :
    ‖iteratedDeriv k (natCurve hS ν θ v) t‖ ≤ 3 * k.factorial / (Real.log (3 / 2) / L) ^ k := by
  have hρ : 0 < Real.log (3 / 2) / L := div_pos (Real.log_pos (by norm_num)) hL
  have h := sum_norm_iteratedDeriv_natCurve_le hS ν θ v hY hL t k
  have hk : (Real.log (3 / 2) / L) ^ k * ‖iteratedDeriv k (natCurve hS ν θ v) t‖ /
      k.factorial ≤ 3 :=
    (single_le_sum (f := fun k ↦ (Real.log (3 / 2) / L) ^ k *
      ‖iteratedDeriv k (natCurve hS ν θ v) t‖ / k.factorial) (fun i _ ↦ by positivity)
      (mem_range.2 (Nat.lt_succ_self k))).trans h
  rw [div_le_iff₀ (by positivity)] at hk
  rw [le_div_iff₀ (pow_pos hρ k)]
  linarith

end Line


end Laplace.Multi
