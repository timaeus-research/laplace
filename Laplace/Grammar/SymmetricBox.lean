/-
Copyright (c) 2026 Daniel Murfet. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniel Murfet
-/
import Laplace.Grammar.ExpGapLocalisation

/-!
# Symmetric normal boxes: the bare parity identity

Interior normal coordinates range over `(-1,1]` rather than `(0,1]`. For the bare monomial integral
the reflections `uᵢ ↦ -uᵢ` give the exact identity

  `∫_{(-1,1]^d} u^h e^{-βN u^{2k}} du = ∏ᵢ (1 + (-1)^{hᵢ}) · ∫_{(0,1]^d} u^h e^{-βN u^{2k}} du`

(`monomialSymReal_eq`): each odd exponent kills the integral, each even exponent doubles it. This is
the paper's parity factor `(1+(-1)^{hᵢ})` (without the `1/2` normalisation of an averaged measure).
Consequently the symmetric-box integral has the mixed-ratio asymptotic with the constant multiplied
by the parity product (`monomialSymReal_tendsto`), which vanishes as soon as one exponent is odd.

For a general amplitude the reflections produce the signed combination
`∑_σ ∏ σᵢ^{hᵢ} η(σ·u)`, not a scalar factor; that reduction is left to a later unit.
-/

open MeasureTheory Set Filter Topology Asymptotics

namespace Laplace.Grammar

/-- Marginal integrability from the Bochner peel: the inner integral is integrable in the peeled
coordinate. -/
theorem integrableOn_pi_box_marginal (d : ℕ) (S : Set ℝ) (F : (Fin (d + 1) → ℝ) → ℝ)
    (hF : IntegrableOn F (piBox (d + 1) S)) :
    IntegrableOn (fun a => ∫ b in piBox d S, F (Fin.cons a b)) S := by
  set μ : Fin (d + 1) → Measure ℝ := fun _ => (volume : Measure ℝ).restrict S with hμ
  have hmp := measurePreserving_piFinSuccAbove μ 0
  set e := MeasurableEquiv.piFinSuccAbove (fun _ : Fin (d + 1) => ℝ) 0 with he
  have hsymm : ∀ y : ℝ × (Fin d → ℝ), e.symm y = Fin.cons y.1 y.2 := by
    intro y
    change Fin.insertNth (α := fun _ : Fin (d + 1) => ℝ) 0 y.1 y.2 = _
    exact Fin.insertNth_zero' y.1 y.2
  unfold IntegrableOn at hF ⊢
  rw [restrict_piBox] at hF
  have hint : Integrable (fun y => F (e.symm y)) (((volume : Measure ℝ).restrict S).prod
      (Measure.pi fun _ : Fin d => (volume : Measure ℝ).restrict S)) :=
    ((hmp.symm e).integrable_comp_emb e.symm.measurableEmbedding).2 hF
  have h := hint.integral_prod_left
  rw [restrict_piBox]
  simpa only [hsymm] using h

/-- **Reflection identity on `(-1,1]`**: an integrable `g` with `g(-a) = (-1)^h g(a)` satisfies
`∫_{(-1,1]} g = (1 + (-1)^h) ∫_{(0,1]} g`. -/
theorem integral_Ioc_symm_of_parity (g : ℝ → ℝ) (h : ℕ) (hg : IntegrableOn g (Ioc (-1 : ℝ) 1))
    (hsym : ∀ a, g (-a) = (-1) ^ h * g a) :
    ∫ a in Ioc (-1 : ℝ) 1, g a = (1 + (-1) ^ h) * ∫ a in Ioc (0 : ℝ) 1, g a := by
  have h1 : IntervalIntegrable g volume (-1) 0 :=
    (intervalIntegrable_iff_integrableOn_Ioc_of_le (by norm_num)).2
      (hg.mono_set (Ioc_subset_Ioc_right zero_le_one))
  have h2 : IntervalIntegrable g volume 0 1 :=
    (intervalIntegrable_iff_integrableOn_Ioc_of_le zero_le_one).2
      (hg.mono_set (Ioc_subset_Ioc_left (by norm_num)))
  rw [← intervalIntegral.integral_of_le (by norm_num : (-1 : ℝ) ≤ 1),
    ← intervalIntegral.integral_add_adjacent_intervals h1 h2,
    ← intervalIntegral.integral_of_le zero_le_one]
  have h3 : ∫ a in (-1 : ℝ)..0, g a = (-1) ^ h * ∫ a in (0 : ℝ)..1, g a := by
    have := intervalIntegral.integral_comp_neg (a := (0 : ℝ)) (b := 1) g
    simp only [neg_zero] at this
    rw [← this, ← intervalIntegral.integral_const_mul]
    exact intervalIntegral.integral_congr fun a _ => hsym a
  rw [h3]
  ring

/-- The symmetric box `(-1,1]^d`. -/
def symBox (d : ℕ) : Set (Fin d → ℝ) := piBox d (Ioc (-1 : ℝ) 1)

/-- The monomial integral over the symmetric box. -/
noncomputable def monomialSymReal (d : ℕ) (h k : Fin d → ℕ) (β N : ℝ) : ℝ :=
  ∫ x in symBox d, (∏ i, x i ^ h i) * Real.exp (-(β * N * ∏ i, x i ^ (2 * k i)))

theorem monomialSym_integrableOn (d : ℕ) (h k : Fin d → ℕ) (β N : ℝ) :
    IntegrableOn (fun x : Fin d → ℝ =>
      (∏ i, x i ^ h i) * Real.exp (-(β * N * ∏ i, x i ^ (2 * k i)))) (symBox d) := by
  have hcont : Continuous fun x : Fin d → ℝ =>
      (∏ i, x i ^ h i) * Real.exp (-(β * N * ∏ i, x i ^ (2 * k i))) :=
    (continuous_finsetProd _ fun i _ => (continuous_apply i).pow _).mul
      (Real.continuous_exp.comp (continuous_const.mul
        (continuous_finsetProd _ fun i _ => (continuous_apply i).pow _)).neg)
  have hcpt : IsCompact (Set.pi univ fun _ : Fin d => Icc (-1 : ℝ) 1) :=
    isCompact_univ_pi fun _ => isCompact_Icc
  exact (hcont.continuousOn.integrableOn_compact hcpt).mono_set
    (pi_mono fun _ _ => Ioc_subset_Icc_self)

/-- **Bare parity identity**:
`∫_{(-1,1]^d} u^h e^{-βN u^{2k}} du = ∏ᵢ (1 + (-1)^{hᵢ}) · ∫_{(0,1]^d} u^h e^{-βN u^{2k}} du`. -/
theorem monomialSymReal_eq (β : ℝ) :
    ∀ (d : ℕ) (h k : Fin d → ℕ) (N : ℝ),
      monomialSymReal d h k β N = (∏ i, (1 + (-1 : ℝ) ^ h i)) * monomialBoxReal d h k β N := by
  intro d
  induction d with
  | zero =>
    intro h k N
    unfold monomialSymReal monomialBoxReal symBox
    rw [integral_piBox_zero]
    have : unitBox 0 = piBox 0 (Ioc (0 : ℝ) 1) := rfl
    rw [this, integral_piBox_zero]
    simp
  | succ d ih =>
    intro h k N
    -- peel the first coordinate on both boxes
    unfold monomialSymReal symBox
    rw [integral_pi_box_succ d _ _ (monomialSym_integrableOn (d + 1) h k β N)]
    have hunit : unitBox (d + 1) = piBox (d + 1) (Ioc (0 : ℝ) 1) := rfl
    have hunit' : unitBox d = piBox d (Ioc (0 : ℝ) 1) := rfl
    unfold monomialBoxReal
    rw [hunit, integral_pi_box_succ d _ _ (by
      have := monomialBox_integrableOn (d + 1) h k β N
      rwa [hunit] at this)]
    -- the inner integrals are the `d`-dimensional integrals at the scaled parameter
    have hinner : ∀ (S : Set ℝ) (_ : MeasurableSet S) (a : ℝ), ∫ b in piBox d S,
        (∏ i, (Fin.cons a b : Fin (d + 1) → ℝ) i ^ h i) *
          Real.exp (-(β * N * ∏ i, (Fin.cons a b : Fin (d + 1) → ℝ) i ^ (2 * k i))) =
        a ^ h 0 * ∫ b in piBox d S, (∏ i, b i ^ Fin.tail h i) *
          Real.exp (-(β * (N * a ^ (2 * k 0)) * ∏ i, b i ^ (2 * Fin.tail k i))) := by
      intro S hS a
      rw [← integral_const_mul]
      refine setIntegral_congr_fun (measurableSet_piBox d S hS) fun b _ => ?_
      simp only [Fin.prod_univ_succ, Fin.cons_zero, Fin.cons_succ, Fin.tail]
      ring_nf
    have hs := hinner (Ioc (-1 : ℝ) 1) measurableSet_Ioc
    have hu := hinner (Ioc (0 : ℝ) 1) measurableSet_Ioc
    -- the symmetric inner integral by the induction hypothesis
    have hsym_eq : ∀ a : ℝ, (∫ b in piBox d (Ioc (-1 : ℝ) 1), (∏ i, b i ^ Fin.tail h i) *
        Real.exp (-(β * (N * a ^ (2 * k 0)) * ∏ i, b i ^ (2 * Fin.tail k i)))) =
        (∏ i, (1 + (-1 : ℝ) ^ Fin.tail h i)) *
          monomialBoxReal d (Fin.tail h) (Fin.tail k) β (N * a ^ (2 * k 0)) :=
      fun a => ih (Fin.tail h) (Fin.tail k) (N * a ^ (2 * k 0))
    have hunit_eq : ∀ a : ℝ, (∫ b in piBox d (Ioc (0 : ℝ) 1), (∏ i, b i ^ Fin.tail h i) *
        Real.exp (-(β * (N * a ^ (2 * k 0)) * ∏ i, b i ^ (2 * Fin.tail k i)))) =
        monomialBoxReal d (Fin.tail h) (Fin.tail k) β (N * a ^ (2 * k 0)) := fun a => rfl
    -- integrability of the symmetric marginal
    have hint_g : IntegrableOn (fun a : ℝ => a ^ h 0 * ((∏ i, (1 + (-1 : ℝ) ^ Fin.tail h i)) *
        monomialBoxReal d (Fin.tail h) (Fin.tail k) β (N * a ^ (2 * k 0)))) (Ioc (-1 : ℝ) 1) := by
      refine (integrableOn_pi_box_marginal d (Ioc (-1 : ℝ) 1) _
        (monomialSym_integrableOn (d + 1) h k β N)).congr_fun (fun a _ => ?_) measurableSet_Ioc
      beta_reduce
      rw [hs a, hsym_eq a]
    have hsymg : ∀ a : ℝ, (-a) ^ h 0 * ((∏ i, (1 + (-1 : ℝ) ^ Fin.tail h i)) *
        monomialBoxReal d (Fin.tail h) (Fin.tail k) β (N * (-a) ^ (2 * k 0))) =
        (-1) ^ h 0 * (a ^ h 0 * ((∏ i, (1 + (-1 : ℝ) ^ Fin.tail h i)) *
          monomialBoxReal d (Fin.tail h) (Fin.tail k) β (N * a ^ (2 * k 0)))) := by
      intro a
      rw [neg_pow a (h 0), Even.neg_pow (even_two_mul (k 0)) a]
      ring
    simp_rw [hs, hu, hsym_eq, hunit_eq]
    rw [integral_Ioc_symm_of_parity _ (h 0) hint_g hsymg, Fin.prod_univ_succ]
    have hP : ∫ a in Ioc (0 : ℝ) 1, a ^ h 0 * ((∏ i, (1 + (-1 : ℝ) ^ Fin.tail h i)) *
        monomialBoxReal d (Fin.tail h) (Fin.tail k) β (N * a ^ (2 * k 0))) =
        (∏ i, (1 + (-1 : ℝ) ^ Fin.tail h i)) * ∫ a in Ioc (0 : ℝ) 1, a ^ h 0 *
          monomialBoxReal d (Fin.tail h) (Fin.tail k) β (N * a ^ (2 * k 0)) := by
      rw [← integral_const_mul]
      exact integral_congr_ae (Eventually.of_forall fun a => by ring)
    rw [hP]
    simp only [Fin.tail]
    ring

/-- **Symmetric-box asymptotic**: the mixed-ratio leading constant times the parity product
`∏ᵢ (1 + (-1)^{hᵢ})`, which vanishes as soon as one exponent is odd. -/
theorem monomialSymReal_tendsto (d : ℕ) (h k : Fin (d + 1) → ℕ) (hk : ∀ i, 0 < k i) (l β : ℝ)
    (hl : 0 < l) (hβ : 0 < β) (hmin : ∀ i, l ≤ ratioExp h k i) (hatt : ∃ i, ratioExp h k i = l) :
    Tendsto (fun N => monomialSymReal (d + 1) h k β N /
        (N ^ (-l) * Real.log N ^ (multCount (ratioExp h k) l - 1))) atTop
      (𝓝 ((∏ i, (1 + (-1 : ℝ) ^ h i)) * monomialMixedConst h k l β)) := by
  refine ((monomialBoxReal_mixed_tendsto d h k hk l β hl hβ hmin hatt).const_mul _).congr'
    (Eventually.of_forall fun N => ?_)
  beta_reduce
  rw [monomialSymReal_eq β (d + 1) h k N, mul_div_assoc]

end Laplace.Grammar
