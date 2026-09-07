/-
Copyright (c) 2026 Timaeus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Laplace.Grammar.PhaseNormalMoment

/-!
# The phase-dressed leading term in general dimension

Unit 202 (programme A, step 4): the deterministic core of the general-`d` phase-dressed leading
asymptotic. For continuous phase `ξ` and amplitude `η` on `ℝ^d`, exponents `h`, `k` with
`λ = min_i (hᵢ+1)/(2kᵢ)`, minimiser set `J`, `m = |J|`, `p = 2λ`,
```
I_N = ∫_{(0,1]^d} η(u) u^h e^{-β(Nu^k)² + β(Nu^k)ξ(u)} du,
I_N / (N^{-p}(log N)^{m-1}) → phaseCoeff h k λ β ξ η
  = 2^{m-1}·2·faceNorm · ∫_{(0,1]^d} η(πu) S^{(β)}_{p/2}(ξ(πu)) ∏_{i∉J} uᵢ^{hᵢ-2kᵢλ} du,
```
with `π = faceProj` (the minimising coordinates set to `0`),
`S^{(β)}_{p/2}(a) = phaseMoment β p a`, and `faceNorm = 1/((m-1)! ∏_{i∈J} 2kᵢ)`; the paper-facing
constant `2^{m-1}·2·faceNorm = 1/((m-1)! ∏_{i∈J} kᵢ)` is evaluated in the headline unit.

**Method (Taylor-in-phase).** `e^{βsξ} = Σ_{j<2K} (βsξ)^j/j! + R_{2K}` with `s = Nu^k`. Each term is
the shifted-exponent theorem of unit 200 (`shifted_term_tendsto`), the `N`-side remainder is bounded
by `tailCoeff · Mη · ∫ u^h e^{-(β/4)N²u^{2k}}` (unit 199, bare monomial theorem at `β/4`), and the
distance of `phaseCoeff` to the finite Taylor coefficient sum is bounded by the same tail against the
limiting face measure (unit 201, `phaseMoment_taylor_le`). `tendsto_of_approx` assembles.

Zero `sorry`/`axiom`.
-/

open MeasureTheory Filter Topology Real Set

namespace Laplace.Grammar

/-- `1/((m-1)! ∏_{i∈J} 2kᵢ)`, the face normalisation without the Gamma factor. -/
noncomputable def faceNorm {d : ℕ} (h k : Fin d → ℕ) (l : ℝ) : ℝ :=
  1 / ((multCount (ratioExp h k) l - 1).factorial : ℝ) *
    ∏ i, if ratioExp h k i = l then 1 / (2 * (k i : ℝ)) else 1

theorem faceNorm_nonneg {d : ℕ} (h k : Fin d → ℕ) (l : ℝ) : 0 ≤ faceNorm h k l := by
  unfold faceNorm
  refine mul_nonneg (by positivity) (Finset.prod_nonneg fun i _ => ?_)
  split_ifs <;> positivity

/-- **The phase-dressed leading coefficient**
`2^{m-1}·2·faceNorm · ∫ η(πu) S^{(β)}_{λ}(ξ(πu)) ∏_{i∉J} uᵢ^{hᵢ-2kᵢλ} du`. -/
noncomputable def phaseCoeff {d : ℕ} (h k : Fin d → ℕ) (l β : ℝ) (ξ η : (Fin d → ℝ) → ℝ) : ℝ :=
  2 ^ (multCount (ratioExp h k) l - 1) * 2 * faceNorm h k l *
    ∫ u in unitBox d, (η (faceProj h k l u) * phaseMoment β (2 * l) (ξ (faceProj h k l u))) *
      residualWeight h k l u

theorem exists_bound_closedCube {d : ℕ} (f : (Fin d → ℝ) → ℝ) (hf : Continuous f) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ x ∈ closedCube d, |f x| ≤ M := by
  obtain ⟨C, hC⟩ := (isCompact_closedCube d).exists_bound_of_continuousOn hf.continuousOn
  refine ⟨max C 0, le_max_right _ _, fun x hx => ?_⟩
  have := hC x hx
  rw [Real.norm_eq_abs] at this
  exact this.trans (le_max_left _ _)

theorem integrableOn_unitBox_of_continuous {d : ℕ} (f : (Fin d → ℝ) → ℝ) (hf : Continuous f) :
    IntegrableOn f (unitBox d) :=
  (hf.continuousOn.integrableOn_compact (isCompact_closedCube d)).mono_set
    (unitBox_subset_closedCube d)

/-- `(N ∏ xᵢ^{kᵢ})² = N² ∏ xᵢ^{2kᵢ}`. -/
theorem sq_mul_prod_pow {d : ℕ} (k : Fin d → ℕ) (N : ℝ) (x : Fin d → ℝ) :
    (N * ∏ i, x i ^ k i) ^ 2 = N ^ 2 * ∏ i, x i ^ (2 * k i) := by
  rw [mul_pow, ← Finset.prod_pow]
  congr 1
  exact Finset.prod_congr rfl fun i _ => by rw [pow_mul']

/-- The dressed kernel splits into the phase factor and the Gaussian. -/
theorem quadKernel_eq_phase_mul_gauss {d : ℕ} (β N : ℝ) (k : Fin d → ℕ) (ξ : (Fin d → ℝ) → ℝ)
    (x : Fin d → ℝ) :
    quadKernel β (ξ x) (N * ∏ i, x i ^ k i) =
      Real.exp ((N * ∏ i, x i ^ k i) * (β * ξ x)) *
        Real.exp (-(β * N ^ 2 * ∏ i, x i ^ (2 * k i))) := by
  unfold quadKernel
  rw [← Real.exp_add]
  congr 1
  rw [mul_assoc β (N ^ 2), ← sq_mul_prod_pow k N x]
  ring

/-- The `j`-th Taylor term of the phase expansion, rewritten as a shifted-exponent integrand. -/
theorem taylor_term_eq {d : ℕ} (β N : ℝ) (h k : Fin d → ℕ) (ξ η : (Fin d → ℝ) → ℝ) (j : ℕ)
    (x : Fin d → ℝ) :
    β ^ j / (j.factorial : ℝ) * (N ^ j * ((ξ x ^ j * η x) * ((∏ i, x i ^ phaseShift h k j i) *
        Real.exp (-(β * N ^ 2 * ∏ i, x i ^ (2 * k i)))))) =
      η x * ((∏ i, x i ^ h i) * (((N * ∏ i, x i ^ k i) * (β * ξ x)) ^ j / (j.factorial : ℝ) *
        Real.exp (-(β * N ^ 2 * ∏ i, x i ^ (2 * k i))))) := by
  rw [prod_pow_phaseShift, mul_pow, mul_pow]
  ring

/-- The pointwise remainder of the truncated phase expansion. -/
theorem phase_diff_eq {d : ℕ} (β N : ℝ) (h k : Fin d → ℕ) (ξ η : (Fin d → ℝ) → ℝ) (K : ℕ)
    (x : Fin d → ℝ) :
    η x * ((∏ i, x i ^ h i) * quadKernel β (ξ x) (N * ∏ i, x i ^ k i)) -
      ∑ j ∈ Finset.range (2 * K), η x * ((∏ i, x i ^ h i) *
        (((N * ∏ i, x i ^ k i) * (β * ξ x)) ^ j / (j.factorial : ℝ) *
          Real.exp (-(β * N ^ 2 * ∏ i, x i ^ (2 * k i))))) =
    η x * ((∏ i, x i ^ h i) * ((Real.exp ((N * ∏ i, x i ^ k i) * (β * ξ x)) -
      ∑ j ∈ Finset.range (2 * K), ((N * ∏ i, x i ^ k i) * (β * ξ x)) ^ j / (j.factorial : ℝ)) *
        Real.exp (-(β * N ^ 2 * ∏ i, x i ^ (2 * k i))))) := by
  rw [quadKernel_eq_phase_mul_gauss]
  simp only [mul_sub, sub_mul, Finset.mul_sum, Finset.sum_mul]

theorem continuous_phaseIntegrand {d : ℕ} (β N : ℝ) (h k : Fin d → ℕ) (ξ η : (Fin d → ℝ) → ℝ)
    (hξ : Continuous ξ) (hη : Continuous η) :
    Continuous fun x : Fin d → ℝ =>
      η x * ((∏ i, x i ^ h i) * quadKernel β (ξ x) (N * ∏ i, x i ^ k i)) := by
  have hP := continuous_prod_pow k
  have hQ : Continuous fun x : Fin d → ℝ => quadKernel β (ξ x) (N * ∏ i, x i ^ k i) := by
    unfold quadKernel
    exact Real.continuous_exp.comp ((continuous_const.mul ((continuous_const.mul hP).pow 2)).add
      ((continuous_const.mul hξ).mul (continuous_const.mul hP)))
  exact hη.mul ((continuous_prod_pow h).mul hQ)

theorem continuous_taylorTerm {d : ℕ} (β N : ℝ) (h k : Fin d → ℕ) (ξ η : (Fin d → ℝ) → ℝ)
    (hξ : Continuous ξ) (hη : Continuous η) (j : ℕ) :
    Continuous fun x : Fin d → ℝ => η x * ((∏ i, x i ^ h i) *
      (((N * ∏ i, x i ^ k i) * (β * ξ x)) ^ j / (j.factorial : ℝ) *
        Real.exp (-(β * N ^ 2 * ∏ i, x i ^ (2 * k i))))) := by
  have hP := continuous_prod_pow k
  have hP2 := continuous_prod_pow fun i => 2 * k i
  exact hη.mul ((continuous_prod_pow h).mul
    ((((continuous_const.mul hP).mul (continuous_const.mul hξ)).pow j).div_const _ |>.mul
      (Real.continuous_exp.comp (continuous_const.mul hP2).neg)))

/-- **`N`-side remainder**: the phase-dressed integral minus its `2K`-term Taylor approximant is
bounded by `Mη · tailCoeff · ∫ u^h e^{-(β/4)N²u^{2k}}`, where `|η| ≤ Mη` and `|βξ| ≤ b` on the cube. -/
theorem phase_remainder_le (d : ℕ) (h k : Fin d → ℕ) (β N b Mη : ℝ) (hβ : 0 < β) (hN : 0 ≤ N)
    (ξ η : (Fin d → ℝ) → ℝ) (hξ : Continuous ξ) (hη : Continuous η)
    (hb : ∀ x ∈ closedCube d, |β * ξ x| ≤ b) (hMη0 : 0 ≤ Mη)
    (hMη : ∀ x ∈ closedCube d, |η x| ≤ Mη) (K : ℕ) :
    |(∫ x in unitBox d, η x * ((∏ i, x i ^ h i) * quadKernel β (ξ x) (N * ∏ i, x i ^ k i))) -
      ∑ j ∈ Finset.range (2 * K), β ^ j / (j.factorial : ℝ) * (N ^ j * ∫ x in unitBox d,
        (ξ x ^ j * η x) * ((∏ i, x i ^ phaseShift h k j i) *
          Real.exp (-(β * N ^ 2 * ∏ i, x i ^ (2 * k i)))))| ≤
      Mη * tailCoeff β b K * monomialBoxReal d h k (β / 4) (N ^ 2) := by
  have hTj : ∀ j : ℕ, IntegrableOn (fun x : Fin d → ℝ => η x * ((∏ i, x i ^ h i) *
      (((N * ∏ i, x i ^ k i) * (β * ξ x)) ^ j / (j.factorial : ℝ) *
        Real.exp (-(β * N ^ 2 * ∏ i, x i ^ (2 * k i)))))) (unitBox d) :=
    fun j => integrableOn_unitBox_of_continuous _ (continuous_taylorTerm β N h k ξ η hξ hη j)
  have hsum : ∑ j ∈ Finset.range (2 * K), β ^ j / (j.factorial : ℝ) * (N ^ j * ∫ x in unitBox d,
        (ξ x ^ j * η x) * ((∏ i, x i ^ phaseShift h k j i) *
          Real.exp (-(β * N ^ 2 * ∏ i, x i ^ (2 * k i))))) =
      ∫ x in unitBox d, ∑ j ∈ Finset.range (2 * K), η x * ((∏ i, x i ^ h i) *
        (((N * ∏ i, x i ^ k i) * (β * ξ x)) ^ j / (j.factorial : ℝ) *
          Real.exp (-(β * N ^ 2 * ∏ i, x i ^ (2 * k i))))) := by
    rw [integral_finsetSum _ fun j _ => hTj j]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [← integral_const_mul, ← integral_const_mul]
    exact setIntegral_congr_fun (measurableSet_unitBox _) fun x _ => taylor_term_eq β N h k ξ η j x
  have hI : IntegrableOn (fun x : Fin d → ℝ =>
      η x * ((∏ i, x i ^ h i) * quadKernel β (ξ x) (N * ∏ i, x i ^ k i))) (unitBox d) :=
    integrableOn_unitBox_of_continuous _ (continuous_phaseIntegrand β N h k ξ η hξ hη)
  rw [hsum, ← integral_sub hI (integrable_finsetSum _ fun j _ => hTj j)]
  have hbd : IntegrableOn (fun x : Fin d → ℝ => Mη * tailCoeff β b K *
      ((∏ i, x i ^ h i) * Real.exp (-(β / 4 * N ^ 2 * ∏ i, x i ^ (2 * k i))))) (unitBox d) :=
    (monomialBox_integrableOn d h k (β / 4) (N ^ 2)).const_mul _
  have hpt : ∀ᵐ x ∂(volume.restrict (unitBox d)),
      ‖η x * ((∏ i, x i ^ h i) * quadKernel β (ξ x) (N * ∏ i, x i ^ k i)) -
        ∑ j ∈ Finset.range (2 * K), η x * ((∏ i, x i ^ h i) *
          (((N * ∏ i, x i ^ k i) * (β * ξ x)) ^ j / (j.factorial : ℝ) *
            Real.exp (-(β * N ^ 2 * ∏ i, x i ^ (2 * k i)))))‖ ≤
      Mη * tailCoeff β b K *
        ((∏ i, x i ^ h i) * Real.exp (-(β / 4 * N ^ 2 * ∏ i, x i ^ (2 * k i)))) := by
    refine (ae_restrict_iff' (measurableSet_unitBox _)).2 (Eventually.of_forall fun x hx => ?_)
    have hxc : x ∈ closedCube d := unitBox_subset_closedCube _ hx
    have hs0 : 0 ≤ N * ∏ i, x i ^ k i :=
      mul_nonneg hN (Finset.prod_nonneg fun i _ => pow_nonneg (hx i (mem_univ i)).1.le _)
    have hxh : 0 ≤ ∏ i, x i ^ h i :=
      Finset.prod_nonneg fun i _ => pow_nonneg (hx i (mem_univ i)).1.le _
    have htail := phase_tail_le β b (N * ∏ i, x i ^ k i) (β * ξ x) hβ hs0 (hb x hxc) K
    rw [sq_mul_prod_pow k N x, ← mul_assoc β (N ^ 2), ← mul_assoc (β / 4) (N ^ 2)] at htail
    rw [phase_diff_eq, Real.norm_eq_abs, abs_mul, abs_mul, abs_mul, abs_of_nonneg hxh,
      abs_of_pos (Real.exp_pos _)]
    calc |η x| * ((∏ i, x i ^ h i) * (|Real.exp ((N * ∏ i, x i ^ k i) * (β * ξ x)) -
          ∑ j ∈ Finset.range (2 * K), ((N * ∏ i, x i ^ k i) * (β * ξ x)) ^ j / (j.factorial : ℝ)| *
            Real.exp (-(β * N ^ 2 * ∏ i, x i ^ (2 * k i)))))
        ≤ Mη * ((∏ i, x i ^ h i) *
          (tailCoeff β b K * Real.exp (-(β / 4 * N ^ 2 * ∏ i, x i ^ (2 * k i))))) := by
          gcongr
          exact hMη x hxc
      _ = Mη * tailCoeff β b K *
          ((∏ i, x i ^ h i) * Real.exp (-(β / 4 * N ^ 2 * ∏ i, x i ^ (2 * k i)))) := by ring
  have hnorm := norm_integral_le_of_norm_le hbd hpt
  rw [Real.norm_eq_abs, integral_const_mul] at hnorm
  exact hnorm

/-- Integrability of `f ∘ faceProj · residualWeight` on the box for continuous `f`. -/
theorem integrableOn_face_mul {d : ℕ} (h k : Fin d → ℕ) (hk : ∀ i, 0 < k i) (l : ℝ)
    (hmin : ∀ i, l ≤ ratioExp h k i) (f : (Fin d → ℝ) → ℝ) (hf : Continuous f) :
    IntegrableOn (fun u => f (faceProj h k l u) * residualWeight h k l u) (unitBox d) :=
  integrableOn_comp_mul_of_continuous d (unitBox d) (measurableSet_unitBox _) (faceProj h k l)
    (faceProj_mapsTo h k l) (measurable_faceProj h k l) (residualWeight h k l)
    (residualWeight_integrableOn h k hk l hmin) f hf

/-- **Face-side remainder**: the distance from `phaseCoeff` to the `2K`-term Taylor coefficient sum
is bounded by the same tail constant against the limiting face measure. -/
theorem phaseCoeff_remainder_le (d : ℕ) (h k : Fin d → ℕ) (hk : ∀ i, 0 < k i) (l β b Mη : ℝ)
    (hl : 0 < l) (hβ : 0 < β) (hmin : ∀ i, l ≤ ratioExp h k i)
    (ξ η : (Fin d → ℝ) → ℝ) (hξ : Continuous ξ) (hη : Continuous η)
    (hb : ∀ x ∈ closedCube d, |β * ξ x| ≤ b) (hMη0 : 0 ≤ Mη)
    (hMη : ∀ x ∈ closedCube d, |η x| ≤ Mη) (K : ℕ) :
    |phaseCoeff h k l β ξ η - ∑ j ∈ Finset.range (2 * K), β ^ j / (j.factorial : ℝ) *
        ((2 : ℝ) ^ (multCount (ratioExp h k) l - 1) *
          amplitudeCoeff (phaseShift h k j) k (l + j / 2) β (fun x => ξ x ^ j * η x))| ≤
      tailCoeff β b K * ((2 : ℝ) ^ (multCount (ratioExp h k) l - 1) * 2 * faceNorm h k l *
        (Mη * gaussTail β (2 * l) * ∫ u in unitBox d, residualWeight h k l u)) := by
  have hpoly : ∀ j : ℕ, IntegrableOn (fun u => (η (faceProj h k l u) *
      ((β * ξ (faceProj h k l u)) ^ j / (j.factorial : ℝ) *
        (Real.Gamma (l + j / 2) * β ^ (-(l + j / 2)) / 2))) * residualWeight h k l u)
      (unitBox d) :=
    fun j => integrableOn_face_mul h k hk l hmin (fun x => η x * ((β * ξ x) ^ j / (j.factorial : ℝ) *
      (Real.Gamma (l + j / 2) * β ^ (-(l + j / 2)) / 2))) (by fun_prop)
  have hterm : ∀ j : ℕ, IntegrableOn (fun u => (fun x => ξ x ^ j * η x) (faceProj h k l u) *
      residualWeight h k l u) (unitBox d) :=
    fun j => integrableOn_face_mul h k hk l hmin _ ((hξ.pow j).mul hη)
  have hsum : ∑ j ∈ Finset.range (2 * K), β ^ j / (j.factorial : ℝ) *
        ((2 : ℝ) ^ (multCount (ratioExp h k) l - 1) *
          amplitudeCoeff (phaseShift h k j) k (l + j / 2) β (fun x => ξ x ^ j * η x)) =
      2 ^ (multCount (ratioExp h k) l - 1) * 2 * faceNorm h k l *
        ∫ u in unitBox d, (η (faceProj h k l u) * ∑ j ∈ Finset.range (2 * K),
          (β * ξ (faceProj h k l u)) ^ j / (j.factorial : ℝ) *
            (Real.Gamma (l + j / 2) * β ^ (-(l + j / 2)) / 2)) * residualWeight h k l u := by
    have hfun : (fun u => (η (faceProj h k l u) * ∑ j ∈ Finset.range (2 * K),
        (β * ξ (faceProj h k l u)) ^ j / (j.factorial : ℝ) *
          (Real.Gamma (l + j / 2) * β ^ (-(l + j / 2)) / 2)) * residualWeight h k l u) =
        fun u => ∑ j ∈ Finset.range (2 * K), (η (faceProj h k l u) *
          ((β * ξ (faceProj h k l u)) ^ j / (j.factorial : ℝ) *
            (Real.Gamma (l + j / 2) * β ^ (-(l + j / 2)) / 2))) * residualWeight h k l u := by
      funext u
      rw [Finset.mul_sum, Finset.sum_mul]
    rw [hfun, integral_finsetSum _ fun j _ => hpoly j, Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [amplitudeCoeff_phaseShift h k hk j l β, ← integral_const_mul, ← integral_const_mul,
      ← integral_const_mul, ← integral_const_mul]
    refine setIntegral_congr_fun (measurableSet_unitBox _) fun u _ => ?_
    simp only [faceNorm]
    rw [mul_pow]
    ring
  have hS : IntegrableOn (fun u => (η (faceProj h k l u) *
      phaseMoment β (2 * l) (ξ (faceProj h k l u))) * residualWeight h k l u) (unitBox d) :=
    integrableOn_face_mul h k hk l hmin (fun x => η x * phaseMoment β (2 * l) (ξ x))
      (hη.mul ((continuous_phaseMoment β (2 * l) hβ (by positivity)).comp hξ))
  have hP : IntegrableOn (fun u => (η (faceProj h k l u) * ∑ j ∈ Finset.range (2 * K),
      (β * ξ (faceProj h k l u)) ^ j / (j.factorial : ℝ) *
        (Real.Gamma (l + j / 2) * β ^ (-(l + j / 2)) / 2)) * residualWeight h k l u) (unitBox d) :=
    integrableOn_face_mul h k hk l hmin (fun x => η x * ∑ j ∈ Finset.range (2 * K),
      (β * ξ x) ^ j / (j.factorial : ℝ) * (Real.Gamma (l + j / 2) * β ^ (-(l + j / 2)) / 2))
      (by fun_prop)
  rw [hsum, phaseCoeff, ← mul_sub, ← integral_sub hS hP, abs_mul,
    abs_of_nonneg (by have := faceNorm_nonneg h k l; positivity)]
  have hbd : IntegrableOn (fun u => Mη * (tailCoeff β b K * gaussTail β (2 * l)) *
      residualWeight h k l u) (unitBox d) :=
    (residualWeight_integrableOn h k hk l hmin).const_mul _
  have hpt : ∀ᵐ u ∂(volume.restrict (unitBox d)),
      ‖(η (faceProj h k l u) * phaseMoment β (2 * l) (ξ (faceProj h k l u))) *
          residualWeight h k l u -
        (η (faceProj h k l u) * ∑ j ∈ Finset.range (2 * K),
          (β * ξ (faceProj h k l u)) ^ j / (j.factorial : ℝ) *
            (Real.Gamma (l + j / 2) * β ^ (-(l + j / 2)) / 2)) * residualWeight h k l u‖ ≤
      Mη * (tailCoeff β b K * gaussTail β (2 * l)) * residualWeight h k l u := by
    refine (ae_restrict_iff' (measurableSet_unitBox _)).2 (Eventually.of_forall fun u hu => ?_)
    have hπ : faceProj h k l u ∈ closedCube d := faceProj_mapsTo h k l hu
    have hw := residualWeight_nonneg h k l u hu
    have htay := phaseMoment_taylor_le β (2 * l) (ξ (faceProj h k l u)) b hβ (by positivity)
      (hb _ hπ) K
    have h2l : 2 * l / 2 = l := by ring
    simp only [h2l] at htay
    rw [← sub_mul, ← mul_sub, Real.norm_eq_abs, abs_mul, abs_mul, abs_of_nonneg hw]
    gcongr
    exact hMη _ hπ
  have hnorm := norm_integral_le_of_norm_le hbd hpt
  rw [Real.norm_eq_abs, integral_const_mul] at hnorm
  calc 2 ^ (multCount (ratioExp h k) l - 1) * 2 * faceNorm h k l * |∫ u in unitBox d,
        (η (faceProj h k l u) * phaseMoment β (2 * l) (ξ (faceProj h k l u))) *
            residualWeight h k l u -
          (η (faceProj h k l u) * ∑ j ∈ Finset.range (2 * K),
            (β * ξ (faceProj h k l u)) ^ j / (j.factorial : ℝ) *
              (Real.Gamma (l + j / 2) * β ^ (-(l + j / 2)) / 2)) * residualWeight h k l u|
      ≤ 2 ^ (multCount (ratioExp h k) l - 1) * 2 * faceNorm h k l *
          (Mη * (tailCoeff β b K * gaussTail β (2 * l)) *
            ∫ u in unitBox d, residualWeight h k l u) := by
        gcongr
        have := faceNorm_nonneg h k l
        positivity
    _ = tailCoeff β b K * ((2 : ℝ) ^ (multCount (ratioExp h k) l - 1) * 2 * faceNorm h k l *
          (Mη * gaussTail β (2 * l) * ∫ u in unitBox d, residualWeight h k l u)) := by ring

/-- **General-dimensional phase-dressed leading asymptotic (deterministic core)**:
`∫ η(u) u^h e^{-β(Nu^k)² + β(Nu^k)ξ(u)} du / (N^{-2λ}(log N)^{m-1}) → phaseCoeff h k λ β ξ η`. -/
theorem phase_leading_tendsto (d : ℕ) (h k : Fin (d + 1) → ℕ) (hk : ∀ i, 0 < k i) (l β : ℝ)
    (hl : 0 < l) (hβ : 0 < β) (hmin : ∀ i, l ≤ ratioExp h k i) (hatt : ∃ i, ratioExp h k i = l)
    (ξ η : (Fin (d + 1) → ℝ) → ℝ) (hξ : Continuous ξ) (hη : Continuous η) :
    Tendsto (fun N : ℝ => (∫ x in unitBox (d + 1),
        η x * ((∏ i, x i ^ h i) * quadKernel β (ξ x) (N * ∏ i, x i ^ k i))) /
        (N ^ (-(2 * l)) * Real.log N ^ (multCount (ratioExp h k) l - 1))) atTop
      (𝓝 (phaseCoeff h k l β ξ η)) := by
  obtain ⟨M, hM0, hM⟩ := exists_bound_closedCube ξ hξ
  obtain ⟨Mη, hMη0, hMη⟩ := exists_bound_closedCube η hη
  have hb : ∀ x ∈ closedCube (d + 1), |β * ξ x| ≤ β * M := fun x hx => by
    rw [abs_mul, abs_of_pos hβ]
    exact mul_le_mul_of_nonneg_left (hM x hx) hβ.le
  -- the `N`-side normalising limit at `β/4`
  have hmono := tendsto_powLog_comp_sq (fun T => monomialBoxReal (d + 1) h k (β / 4) T) l _
    (multCount (ratioExp h k) l - 1)
    (monomialBoxReal_mixed_tendsto d h k hk l (β / 4) hl (by positivity) hmin hatt)
  obtain ⟨L, hL⟩ : ∃ L : ℝ, L = (2 : ℝ) ^ (multCount (ratioExp h k) l - 1) *
    monomialMixedConst h k l (β / 4) := ⟨_, rfl⟩
  have hL0 : 0 ≤ L := by
    rw [hL]
    have := monomialMixedConst_pos h k hk l (β / 4) hl (by positivity) hmin
    positivity
  rw [← hL] at hmono
  have hLev : ∀ᶠ N in atTop, monomialBoxReal (d + 1) h k (β / 4) (N ^ 2) /
      (N ^ (-(2 * l)) * Real.log N ^ (multCount (ratioExp h k) l - 1)) ≤ L + 1 :=
    hmono.eventually (eventually_le_nhds (lt_add_one L))
  -- constants
  obtain ⟨C₁, hC₁⟩ : ∃ C : ℝ, C = Mη * (L + 1) := ⟨_, rfl⟩
  obtain ⟨C₂, hC₂⟩ : ∃ C : ℝ, C = (2 : ℝ) ^ (multCount (ratioExp h k) l - 1) * 2 * faceNorm h k l *
    (Mη * gaussTail β (2 * l) * ∫ u in unitBox (d + 1), residualWeight h k l u) := ⟨_, rfl⟩
  have hC₁0 : 0 ≤ C₁ := by rw [hC₁]; positivity
  have hC₂0 : 0 ≤ C₂ := by
    rw [hC₂]
    have hW : 0 ≤ ∫ u in unitBox (d + 1), residualWeight h k l u :=
      setIntegral_nonneg (measurableSet_unitBox _) fun u hu => residualWeight_nonneg h k l u hu
    have hG : 0 ≤ gaussTail β (2 * l) :=
      setIntegral_nonneg measurableSet_Ioi fun s hs => by
        have : (0 : ℝ) < s := hs
        positivity
    have := faceNorm_nonneg h k l
    positivity
  refine tendsto_of_approx _ _ fun ε hε => ?_
  have hτ := tendsto_tailCoeff β (β * M) hβ
  have hK₁ : ∀ᶠ K in atTop, tailCoeff β (β * M) K < ε / (C₁ + 1) :=
    hτ.eventually_lt_const (by positivity)
  have hK₂ : ∀ᶠ K in atTop, tailCoeff β (β * M) K < ε / (C₂ + 1) :=
    hτ.eventually_lt_const (by positivity)
  obtain ⟨K, hK₁, hK₂⟩ := (hK₁.and hK₂).exists
  have hτ1 : tailCoeff β (β * M) K * C₁ ≤ ε := by
    calc tailCoeff β (β * M) K * C₁ ≤ ε / (C₁ + 1) * C₁ :=
          mul_le_mul_of_nonneg_right hK₁.le hC₁0
      _ ≤ ε := by
          rw [div_mul_eq_mul_div, div_le_iff₀ (by positivity)]
          nlinarith
  have hτ2 : tailCoeff β (β * M) K * C₂ ≤ ε := by
    calc tailCoeff β (β * M) K * C₂ ≤ ε / (C₂ + 1) * C₂ :=
          mul_le_mul_of_nonneg_right hK₂.le hC₂0
      _ ≤ ε := by
          rw [div_mul_eq_mul_div, div_le_iff₀ (by positivity)]
          nlinarith
  refine ⟨fun N => ∑ j ∈ Finset.range (2 * K), β ^ j / (j.factorial : ℝ) *
      ((N ^ j * ∫ x in unitBox (d + 1), (ξ x ^ j * η x) * ((∏ i, x i ^ phaseShift h k j i) *
        Real.exp (-(β * N ^ 2 * ∏ i, x i ^ (2 * k i))))) /
        (N ^ (-(2 * l)) * Real.log N ^ (multCount (ratioExp h k) l - 1))),
    ∑ j ∈ Finset.range (2 * K), β ^ j / (j.factorial : ℝ) *
      ((2 : ℝ) ^ (multCount (ratioExp h k) l - 1) *
        amplitudeCoeff (phaseShift h k j) k (l + j / 2) β (fun x => ξ x ^ j * η x)), ?_, ?_, ?_⟩
  · exact tendsto_finsetSum _ fun j _ =>
      (shifted_term_tendsto d h k hk l β hl hβ hmin hatt (fun x => ξ x ^ j * η x)
        ((hξ.pow j).mul hη) j).const_mul _
  · filter_upwards [eventually_gt_atTop (1 : ℝ), hLev] with N hN hLN
    have hN0 : 0 < N := by linarith
    have hscale : 0 < N ^ (-(2 * l)) * Real.log N ^ (multCount (ratioExp h k) l - 1) :=
      mul_pos (Real.rpow_pos_of_pos hN0 _) (pow_pos (Real.log_pos hN) _)
    have hg : ∑ j ∈ Finset.range (2 * K), β ^ j / (j.factorial : ℝ) *
        ((N ^ j * ∫ x in unitBox (d + 1), (ξ x ^ j * η x) * ((∏ i, x i ^ phaseShift h k j i) *
          Real.exp (-(β * N ^ 2 * ∏ i, x i ^ (2 * k i))))) /
          (N ^ (-(2 * l)) * Real.log N ^ (multCount (ratioExp h k) l - 1))) =
        (∑ j ∈ Finset.range (2 * K), β ^ j / (j.factorial : ℝ) *
          (N ^ j * ∫ x in unitBox (d + 1), (ξ x ^ j * η x) * ((∏ i, x i ^ phaseShift h k j i) *
            Real.exp (-(β * N ^ 2 * ∏ i, x i ^ (2 * k i)))))) /
          (N ^ (-(2 * l)) * Real.log N ^ (multCount (ratioExp h k) l - 1)) := by
      rw [Finset.sum_div]
      exact Finset.sum_congr rfl fun j _ => (mul_div_assoc _ _ _).symm
    rw [hg, ← sub_div, abs_div, abs_of_pos hscale, div_le_iff₀ hscale]
    calc |(∫ x in unitBox (d + 1),
          η x * ((∏ i, x i ^ h i) * quadKernel β (ξ x) (N * ∏ i, x i ^ k i))) -
          ∑ j ∈ Finset.range (2 * K), β ^ j / (j.factorial : ℝ) *
            (N ^ j * ∫ x in unitBox (d + 1), (ξ x ^ j * η x) * ((∏ i, x i ^ phaseShift h k j i) *
              Real.exp (-(β * N ^ 2 * ∏ i, x i ^ (2 * k i)))))|
        ≤ Mη * tailCoeff β (β * M) K * monomialBoxReal (d + 1) h k (β / 4) (N ^ 2) :=
          phase_remainder_le (d + 1) h k β N (β * M) Mη hβ hN0.le ξ η hξ hη hb hMη0 hMη K
      _ = Mη * tailCoeff β (β * M) K * (monomialBoxReal (d + 1) h k (β / 4) (N ^ 2) /
            (N ^ (-(2 * l)) * Real.log N ^ (multCount (ratioExp h k) l - 1))) *
            (N ^ (-(2 * l)) * Real.log N ^ (multCount (ratioExp h k) l - 1)) := by
          rw [mul_assoc _ (_ / _), div_mul_cancel₀ _ hscale.ne']
      _ ≤ Mη * tailCoeff β (β * M) K * (L + 1) *
            (N ^ (-(2 * l)) * Real.log N ^ (multCount (ratioExp h k) l - 1)) := by
          gcongr
          exact mul_nonneg hMη0 (tailCoeff_nonneg β (β * M) hβ K)
      _ = tailCoeff β (β * M) K * C₁ *
            (N ^ (-(2 * l)) * Real.log N ^ (multCount (ratioExp h k) l - 1)) := by
          rw [hC₁]
          ring
      _ ≤ ε * (N ^ (-(2 * l)) * Real.log N ^ (multCount (ratioExp h k) l - 1)) :=
          mul_le_mul_of_nonneg_right hτ1 hscale.le
  · have := phaseCoeff_remainder_le (d + 1) h k hk l β (β * M) Mη hl hβ hmin ξ η hξ hη hb hMη0
      hMη K
    rw [← hC₂] at this
    exact this.trans hτ2

end Laplace.Grammar
