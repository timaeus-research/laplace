/-
Copyright (c) 2026 Daniel Murfet. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniel Murfet
-/
import Laplace.Grammar.HeadlineStochasticLog
import Laplace.Grammar.SymmetricBox
import Laplace.Grammar.QuadraticMonomialBridge

/-!
# Signed reflections of an amplitude on symmetric boxes

Astra #18/#19's rank-2 extension. For an amplitude `η` on the symmetric box `(-1,1]^d`, the
coordinate reflections produce the **signed symmetrisation**

  `η_sym(u) = ∑_{σ ∈ {±1}^d} (∏ᵢ σᵢ^{hᵢ}) η(σ · u)`

(`symAmp`, indexed by `σ : Fin d → Bool`), which is continuous when `η` is, evaluates at the origin
to `η(0) ∏ᵢ (1 + (-1)^{hᵢ})` (`symAmp_zero`), and reduces the symmetric-box dressed integral exactly
to the unit-box one:

  `∫_{(-1,1]^d} η(x) x^h e^{-βN x^{2k}} dx = ∫_{(0,1]^d} η_sym(u) u^h e^{-βN u^{2k}} du`

(`integral_symBox_eq_symAmp`). The proof peels the first coordinate on both boxes (unit 188), splits
the sign sum along `Fin.consEquiv`, and uses the one-dimensional signed reflection
`∫_{(-1,1]} g = ∫_{(0,1]} (g(a) + g(-a)) da`. The asymptotic consequences (amplitude theorem
applied to `η_sym`; an odd exponent kills the equal-ratio corner coefficient but not the integral)
are the next unit.
-/

open MeasureTheory Set Filter Topology

namespace Laplace.Grammar

/-- The sign attached to a Boolean: `true ↦ -1`, `false ↦ 1`. -/
def sgn (b : Bool) : ℝ := if b then -1 else 1

theorem sgn_sq (b : Bool) : sgn b ^ 2 = 1 := by cases b <;> simp [sgn]

theorem sgn_pow_even (b : Bool) (k : ℕ) : sgn b ^ (2 * k) = 1 := by
  rw [pow_mul, sgn_sq, one_pow]

/-- The reflected point `σ · u`. -/
def reflect {d : ℕ} (σ : Fin d → Bool) (u : Fin d → ℝ) : Fin d → ℝ := fun i => sgn (σ i) * u i

theorem continuous_reflect {d : ℕ} (σ : Fin d → Bool) : Continuous (reflect σ) :=
  continuous_pi fun i => continuous_const.mul (continuous_apply i)

/-- **Signed symmetrisation** `η_sym(u) = ∑_σ (∏ᵢ sgn(σᵢ)^{hᵢ}) η(σ · u)`. -/
noncomputable def symAmp {d : ℕ} (h : Fin d → ℕ) (η : (Fin d → ℝ) → ℝ) (u : Fin d → ℝ) : ℝ :=
  ∑ σ : Fin d → Bool, (∏ i, sgn (σ i) ^ h i) * η (reflect σ u)

theorem continuous_symAmp {d : ℕ} (h : Fin d → ℕ) (η : (Fin d → ℝ) → ℝ) (hη : Continuous η) :
    Continuous (symAmp h η) :=
  continuous_finsetSum _ fun σ _ => continuous_const.mul (hη.comp (continuous_reflect σ))

/-- `η_sym(0) = η(0) ∏ᵢ (1 + (-1)^{hᵢ})`. -/
theorem symAmp_zero {d : ℕ} (h : Fin d → ℕ) (η : (Fin d → ℝ) → ℝ) :
    symAmp h η 0 = η 0 * ∏ i, (1 + (-1 : ℝ) ^ h i) := by
  unfold symAmp
  have hr : ∀ σ : Fin d → Bool, reflect σ (0 : Fin d → ℝ) = 0 := fun σ => by
    funext i; simp [reflect]
  simp_rw [hr, ← Finset.sum_mul]
  rw [mul_comm]
  congr 1
  have hb : ∀ i, (1 + (-1 : ℝ) ^ h i) = ∑ b : Bool, sgn b ^ h i := fun i => by
    simp [sgn, add_comm]
  simp_rw [hb]
  rw [Finset.prod_univ_sum (fun _ : Fin d => (Finset.univ : Finset Bool)) (fun i b => sgn b ^ h i),
    Fintype.piFinset_univ]

theorem reflect_cons {d : ℕ} (b : Bool) (τ : Fin d → Bool) (a : ℝ) (w : Fin d → ℝ) :
    reflect (Fin.cons b τ : Fin (d + 1) → Bool) (Fin.cons a w) =
      Fin.cons (sgn b * a) (reflect τ w) := by
  funext i
  refine Fin.cases ?_ (fun j => ?_) i
  · simp [reflect]
  · simp [reflect]

/-- **Splitting the sign sum along the first coordinate.** -/
theorem symAmp_cons {d : ℕ} (h : Fin (d + 1) → ℕ) (η : (Fin (d + 1) → ℝ) → ℝ) (a : ℝ)
    (w : Fin d → ℝ) :
    symAmp h η (Fin.cons a w) =
      symAmp (Fin.tail h) (fun w' => η (Fin.cons a w')) w +
        (-1) ^ h 0 * symAmp (Fin.tail h) (fun w' => η (Fin.cons (-a) w')) w := by
  unfold symAmp
  rw [← (Fin.consEquiv fun _ : Fin (d + 1) => Bool).sum_comp, Fintype.sum_prod_type,
    Fintype.sum_bool, Finset.mul_sum]
  simp only [Fin.consEquiv, Equiv.coe_fn_mk, Fin.prod_univ_succ, Fin.cons_zero, Fin.cons_succ,
    reflect_cons, Fin.tail]
  rw [add_comm]
  congr 1
  · refine Finset.sum_congr rfl fun τ _ => ?_
    simp [sgn]
  · refine Finset.sum_congr rfl fun τ _ => ?_
    simp [sgn]
    ring

/-- The integrand `η(x) x^h e^{-βN x^{2k}}` is integrable on any compact-closure box. -/
theorem dressed_integrableOn_piBox (d : ℕ) (h k : Fin d → ℕ) (β N : ℝ) (η : (Fin d → ℝ) → ℝ)
    (hη : Continuous η) (c : ℝ) :
    IntegrableOn (fun x : Fin d → ℝ =>
      η x * ((∏ i, x i ^ h i) * Real.exp (-(β * N * ∏ i, x i ^ (2 * k i)))))
      (piBox d (Ioc (-c) 1)) := by
  have hcont : Continuous fun x : Fin d → ℝ =>
      η x * ((∏ i, x i ^ h i) * Real.exp (-(β * N * ∏ i, x i ^ (2 * k i)))) :=
    hη.mul ((continuous_finsetProd _ fun i _ => (continuous_apply i).pow _).mul
      (Real.continuous_exp.comp (continuous_const.mul
        (continuous_finsetProd _ fun i _ => (continuous_apply i).pow _)).neg))
  have hcpt : IsCompact (Set.pi univ fun _ : Fin d => Icc (-c) (1 : ℝ)) :=
    isCompact_univ_pi fun _ => isCompact_Icc
  exact (hcont.continuousOn.integrableOn_compact hcpt).mono_set
    (pi_mono fun _ _ => Ioc_subset_Icc_self)

/-- The one-dimensional signed reflection: `∫_{(-1,1]} g = ∫_{(0,1]} (g(a) + g(-a)) da`. -/
theorem integral_Ioc_symm_add (g : ℝ → ℝ) (hg : IntegrableOn g (Ioc (-1 : ℝ) 1)) :
    ∫ a in Ioc (-1 : ℝ) 1, g a = ∫ a in Ioc (0 : ℝ) 1, (g a + g (-a)) := by
  have h1 : IntervalIntegrable g volume (-1) 0 :=
    (intervalIntegrable_iff_integrableOn_Ioc_of_le (by norm_num)).2
      (hg.mono_set (Ioc_subset_Ioc_right zero_le_one))
  have h2 : IntervalIntegrable g volume 0 1 :=
    (intervalIntegrable_iff_integrableOn_Ioc_of_le zero_le_one).2
      (hg.mono_set (Ioc_subset_Ioc_left (by norm_num)))
  have h3 : IntervalIntegrable (fun a => g (-a)) volume 0 1 := by
    have := (IntervalIntegrable.iff_comp_neg (f := g) (a := (-1 : ℝ)) (b := 0)).mp h1
    simpa using this.symm
  rw [← intervalIntegral.integral_of_le (by norm_num : (-1 : ℝ) ≤ 1),
    ← intervalIntegral.integral_add_adjacent_intervals h1 h2,
    ← intervalIntegral.integral_of_le zero_le_one, intervalIntegral.integral_add h2 h3, add_comm]
  congr 1
  have := intervalIntegral.integral_comp_neg (a := (0 : ℝ)) (b := 1) g
  simp only [neg_zero] at this
  exact this.symm

/-- **Exact signed-reflection reduction**:
`∫_{(-1,1]^d} η x^h e^{-βN x^{2k}} = ∫_{(0,1]^d} η_sym u^h e^{-βN u^{2k}}`. -/
theorem integral_symBox_eq_symAmp (β : ℝ) :
    ∀ (d : ℕ) (h k : Fin d → ℕ) (N : ℝ) (η : (Fin d → ℝ) → ℝ), Continuous η →
      ∫ x in symBox d, η x * ((∏ i, x i ^ h i) * Real.exp (-(β * N * ∏ i, x i ^ (2 * k i)))) =
        ∫ u in unitBox d, symAmp h η u *
          ((∏ i, u i ^ h i) * Real.exp (-(β * N * ∏ i, u i ^ (2 * k i)))) := by
  intro d
  induction d with
  | zero =>
    intro h k N η _
    have hu : unitBox 0 = piBox 0 (Ioc (0 : ℝ) 1) := rfl
    unfold symBox
    rw [hu, integral_piBox_zero, integral_piBox_zero]
    simp only [symAmp, Fintype.sum_unique, Finset.univ_eq_empty, Finset.prod_empty, one_mul]
    congr 2
    funext i
    exact Fin.elim0 i
  | succ d ih =>
    intro h k N η hη
    have hu : unitBox (d + 1) = piBox (d + 1) (Ioc (0 : ℝ) 1) := rfl
    have hu' : unitBox d = piBox d (Ioc (0 : ℝ) 1) := rfl
    unfold symBox
    rw [integral_pi_box_succ d _ _ (by
      have := dressed_integrableOn_piBox (d + 1) h k β N η hη 1
      exact this)]
    rw [hu, integral_pi_box_succ d _ _ (by
      have := dressed_integrableOn_piBox (d + 1) h k β N (symAmp h η)
        (continuous_symAmp h η hη) 0
      simpa using this)]
    -- the inner integrals: peel the amplitude and the monomial factor
    have hinner : ∀ (S : Set ℝ) (_ : MeasurableSet S) (ζ : (Fin (d + 1) → ℝ) → ℝ) (a : ℝ),
        ∫ b in piBox d S, ζ (Fin.cons a b) *
          ((∏ i, (Fin.cons a b : Fin (d + 1) → ℝ) i ^ h i) *
            Real.exp (-(β * N * ∏ i, (Fin.cons a b : Fin (d + 1) → ℝ) i ^ (2 * k i)))) =
        a ^ h 0 * ∫ b in piBox d S, ζ (Fin.cons a b) * ((∏ i, b i ^ Fin.tail h i) *
          Real.exp (-(β * (N * a ^ (2 * k 0)) * ∏ i, b i ^ (2 * Fin.tail k i)))) := by
      intro S hS ζ a
      rw [← integral_const_mul]
      refine setIntegral_congr_fun (measurableSet_piBox d S hS) fun b _ => ?_
      simp only [Fin.prod_univ_succ, Fin.cons_zero, Fin.cons_succ, Fin.tail]
      ring_nf
    have hs := hinner (Ioc (-1 : ℝ) 1) measurableSet_Ioc η
    have hu2 := hinner (Ioc (0 : ℝ) 1) measurableSet_Ioc (symAmp h η)
    simp_rw [hs, hu2]
    -- inner symmetric integrals by the induction hypothesis
    have hIH : ∀ a : ℝ, (∫ b in piBox d (Ioc (-1 : ℝ) 1), η (Fin.cons a b) *
        ((∏ i, b i ^ Fin.tail h i) *
          Real.exp (-(β * (N * a ^ (2 * k 0)) * ∏ i, b i ^ (2 * Fin.tail k i))))) =
        ∫ b in piBox d (Ioc (0 : ℝ) 1), symAmp (Fin.tail h) (fun w => η (Fin.cons a w)) b *
          ((∏ i, b i ^ Fin.tail h i) *
            Real.exp (-(β * (N * a ^ (2 * k 0)) * ∏ i, b i ^ (2 * Fin.tail k i)))) := by
      intro a
      have := ih (Fin.tail h) (Fin.tail k) (N * a ^ (2 * k 0)) (fun w => η (Fin.cons a w))
        (hη.comp (continuous_finCons d a))
      simpa [symBox, hu'] using this
    simp_rw [hIH]
    -- the peeled coordinate: signed reflection
    set G : ℝ → ℝ := fun a => ∫ b in piBox d (Ioc (0 : ℝ) 1),
      symAmp (Fin.tail h) (fun w => η (Fin.cons a w)) b *
        ((∏ i, b i ^ Fin.tail h i) *
          Real.exp (-(β * (N * a ^ (2 * k 0)) * ∏ i, b i ^ (2 * Fin.tail k i)))) with hG
    have hint : IntegrableOn (fun a : ℝ => a ^ h 0 * G a) (Ioc (-1 : ℝ) 1) := by
      have hm := integrableOn_pi_box_marginal d (Ioc (-1 : ℝ) 1) _
        (dressed_integrableOn_piBox (d + 1) h k β N η hη 1)
      refine hm.congr_fun (fun a _ => ?_) measurableSet_Ioc
      beta_reduce
      rw [hs a, hIH a]
    rw [integral_Ioc_symm_add _ hint]
    refine setIntegral_congr_fun measurableSet_Ioc fun a _ => ?_
    -- expand `symAmp h η (Fin.cons a b)` on the right
    have hsplit : ∫ b in piBox d (Ioc (0 : ℝ) 1), symAmp h η (Fin.cons a b) *
        ((∏ i, b i ^ Fin.tail h i) *
          Real.exp (-(β * (N * a ^ (2 * k 0)) * ∏ i, b i ^ (2 * Fin.tail k i)))) =
        G a + (-1) ^ h 0 * G (-a) := by
      simp only [hG, Even.neg_pow (even_two_mul (k 0)) a]
      rw [← integral_const_mul, ← integral_add]
      · refine setIntegral_congr_fun (measurableSet_piBox d _ measurableSet_Ioc) fun b _ => ?_
        rw [symAmp_cons]
        ring
      · have := dressed_integrableOn_piBox d (Fin.tail h) (Fin.tail k) β (N * a ^ (2 * k 0))
          (symAmp (Fin.tail h) fun w => η (Fin.cons a w))
          (continuous_symAmp _ _ (hη.comp (continuous_finCons d a))) 0
        rw [neg_zero] at this
        exact this
      · have := dressed_integrableOn_piBox d (Fin.tail h) (Fin.tail k) β (N * a ^ (2 * k 0))
          (symAmp (Fin.tail h) fun w => η (Fin.cons (-a) w))
          (continuous_symAmp _ _ (hη.comp (continuous_finCons d (-a)))) 0
        rw [neg_zero] at this
        exact this.const_mul ((-1 : ℝ) ^ h 0)
    rw [hsplit, neg_pow a (h 0)]
    ring

end Laplace.Grammar
