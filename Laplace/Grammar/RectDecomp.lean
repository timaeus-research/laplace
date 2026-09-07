/-
Copyright (c) 2026 Timaeus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Laplace.Grammar.MixedShiftBound

/-!
# The rectangular face-jet decomposition (grammar §4.2, higher-order `d = 2`)

For face jets `a_i(v, s)`, `b_j(u, s)` and corner jets `c_{ij}(s)`, the rectangular remainder is

  `R = Φ − ∑_{i<M₁} u^i a_i(v,s) − ∑_{j<M₂} v^j b_j(u,s) + ∑_{i<M₁} ∑_{j<M₂} c_{ij}(s) u^i v^j`

(`rectRem`), and the block integral decomposes accordingly (`twoDAmp_rect`). The monomial weights
are absorbed into the exponents (`twoDAmp_pow_absorb`, `twoDAmp_pow_absorb'`, `twoDAmp_corner`),
so that each face term is a one-variable amplitude with shifted exponents, exactly the input of the
face-term expansion (unit 104), and the remainder is the input of the shifted mixed bound
(unit 105). Zero `sorry`/`axiom`.
-/

open Real MeasureTheory Set

namespace Laplace.Grammar

/-- The rectangular remainder of the face-jet decomposition. -/
noncomputable def rectRem (Φ : ℝ → ℝ → ℝ → ℝ) (a b : ℕ → ℝ → ℝ → ℝ) (c : ℕ → ℕ → ℝ → ℝ)
    (M₁ M₂ : ℕ) (u v s : ℝ) : ℝ :=
  Φ u v s - ∑ i ∈ Finset.range M₁, u ^ i * a i v s - ∑ j ∈ Finset.range M₂, v ^ j * b j u s
    + ∑ i ∈ Finset.range M₁, ∑ j ∈ Finset.range M₂, c i j s * (u ^ i * v ^ j)

theorem rectRem_continuous (Φ : ℝ → ℝ → ℝ → ℝ) (a b : ℕ → ℝ → ℝ → ℝ) (c : ℕ → ℕ → ℝ → ℝ)
    (M₁ M₂ : ℕ) (hΦ : Continuous fun x : ℝ × ℝ × ℝ => Φ x.1 x.2.1 x.2.2)
    (ha : ∀ i, Continuous (Function.uncurry (a i)))
    (hb : ∀ j, Continuous (Function.uncurry (b j))) (hc : ∀ i j, Continuous (c i j)) :
    Continuous fun x : ℝ × ℝ × ℝ => rectRem Φ a b c M₁ M₂ x.1 x.2.1 x.2.2 := by
  unfold rectRem
  refine ((hΦ.sub (continuous_finsetSum _ fun i _ => ?_)).sub
    (continuous_finsetSum _ fun j _ => ?_)).add
    (continuous_finsetSum _ fun i _ => continuous_finsetSum _ fun j _ => ?_)
  · exact (continuous_fst.pow i).mul ((ha i).comp
      ((continuous_fst.comp continuous_snd).prodMk (continuous_snd.comp continuous_snd)))
  · exact ((continuous_fst.comp continuous_snd).pow j).mul
      ((hb j).comp (continuous_fst.prodMk (continuous_snd.comp continuous_snd)))
  · exact ((hc i j).comp (continuous_snd.comp continuous_snd)).mul
      ((continuous_fst.pow i).mul ((continuous_fst.comp continuous_snd).pow j))

/-- Linearity of the product-form integrand in the amplitude. -/
theorem twoDIntegrand_rectRem (β N : ℝ) (h₁ h₂ k₁ k₂ : ℕ) (Φ : ℝ → ℝ → ℝ → ℝ)
    (a b : ℕ → ℝ → ℝ → ℝ) (c : ℕ → ℕ → ℝ → ℝ) (M₁ M₂ : ℕ) (z : ℝ × ℝ) :
    twoDIntegrand β N h₁ h₂ k₁ k₂ (rectRem Φ a b c M₁ M₂) z
      = twoDIntegrand β N h₁ h₂ k₁ k₂ Φ z
        - ∑ i ∈ Finset.range M₁, twoDIntegrand β N h₁ h₂ k₁ k₂ (fun u v s => u ^ i * a i v s) z
        - ∑ j ∈ Finset.range M₂, twoDIntegrand β N h₁ h₂ k₁ k₂ (fun u v s => v ^ j * b j u s) z
        + ∑ i ∈ Finset.range M₁, ∑ j ∈ Finset.range M₂,
            twoDIntegrand β N h₁ h₂ k₁ k₂ (fun u v s => c i j s * (u ^ i * v ^ j)) z := by
  unfold twoDIntegrand rectRem
  simp only [mul_sub, mul_add, Finset.mul_sum]

/-- **The rectangular decomposition of the block integral.** -/
theorem twoDAmp_rect (β b N : ℝ) (h₁ h₂ k₁ k₂ : ℕ) (Φ : ℝ → ℝ → ℝ → ℝ) (a bj : ℕ → ℝ → ℝ → ℝ)
    (c : ℕ → ℕ → ℝ → ℝ) (M₁ M₂ : ℕ) (hΦ : Continuous fun x : ℝ × ℝ × ℝ => Φ x.1 x.2.1 x.2.2)
    (ha : ∀ i, Continuous (Function.uncurry (a i)))
    (hb : ∀ j, Continuous (Function.uncurry (bj j))) (hc : ∀ i j, Continuous (c i j)) :
    twoDAmp β b N h₁ h₂ k₁ k₂ Φ
      = (∑ i ∈ Finset.range M₁, twoDAmp β b N h₁ h₂ k₁ k₂ (fun u v s => u ^ i * a i v s))
        + (∑ j ∈ Finset.range M₂, twoDAmp β b N h₁ h₂ k₁ k₂ (fun u v s => v ^ j * bj j u s))
        - (∑ i ∈ Finset.range M₁, ∑ j ∈ Finset.range M₂,
            twoDAmp β b N h₁ h₂ k₁ k₂ (fun u v s => c i j s * (u ^ i * v ^ j)))
        + twoDAmp β b N h₁ h₂ k₁ k₂ (rectRem Φ a bj c M₁ M₂) := by
  have hA : ∀ i, Continuous fun x : ℝ × ℝ × ℝ => x.1 ^ i * a i x.2.1 x.2.2 := fun i =>
    (continuous_fst.pow i).mul ((ha i).comp
      ((continuous_fst.comp continuous_snd).prodMk (continuous_snd.comp continuous_snd)))
  have hB : ∀ j, Continuous fun x : ℝ × ℝ × ℝ => x.2.1 ^ j * bj j x.1 x.2.2 := fun j =>
    ((continuous_fst.comp continuous_snd).pow j).mul
      ((hb j).comp (continuous_fst.prodMk (continuous_snd.comp continuous_snd)))
  have hC : ∀ i j, Continuous fun x : ℝ × ℝ × ℝ => c i j x.2.2 * (x.1 ^ i * x.2.1 ^ j) :=
    fun i j => ((hc i j).comp (continuous_snd.comp continuous_snd)).mul
      ((continuous_fst.pow i).mul ((continuous_fst.comp continuous_snd).pow j))
  have hR := rectRem_continuous Φ a bj c M₁ M₂ hΦ ha hb hc
  have iΦ := twoDIntegrand_integrable β b N h₁ h₂ k₁ k₂ Φ hΦ
  have iA : ∀ i ∈ Finset.range M₁, Integrable
      (twoDIntegrand β N h₁ h₂ k₁ k₂ (fun u v s => u ^ i * a i v s)) (boxMeasure₂ b) :=
    fun i _ => twoDIntegrand_integrable β b N h₁ h₂ k₁ k₂ _ (hA i)
  have iB : ∀ j ∈ Finset.range M₂, Integrable
      (twoDIntegrand β N h₁ h₂ k₁ k₂ (fun u v s => v ^ j * bj j u s)) (boxMeasure₂ b) :=
    fun j _ => twoDIntegrand_integrable β b N h₁ h₂ k₁ k₂ _ (hB j)
  have iC : ∀ i ∈ Finset.range M₁, Integrable (fun z => ∑ j ∈ Finset.range M₂,
      twoDIntegrand β N h₁ h₂ k₁ k₂ (fun u v s => c i j s * (u ^ i * v ^ j)) z) (boxMeasure₂ b) :=
    fun i _ => integrable_finsetSum _ fun j _ =>
      twoDIntegrand_integrable β b N h₁ h₂ k₁ k₂ _ (hC i j)
  have iSA : Integrable (fun z => ∑ i ∈ Finset.range M₁,
      twoDIntegrand β N h₁ h₂ k₁ k₂ (fun u v s => u ^ i * a i v s) z) (boxMeasure₂ b) :=
    integrable_finsetSum _ iA
  have iSB : Integrable (fun z => ∑ j ∈ Finset.range M₂,
      twoDIntegrand β N h₁ h₂ k₁ k₂ (fun u v s => v ^ j * bj j u s) z) (boxMeasure₂ b) :=
    integrable_finsetSum _ iB
  have iSC : Integrable (fun z => ∑ i ∈ Finset.range M₁, ∑ j ∈ Finset.range M₂,
      twoDIntegrand β N h₁ h₂ k₁ k₂ (fun u v s => c i j s * (u ^ i * v ^ j)) z) (boxMeasure₂ b) :=
    integrable_finsetSum _ iC
  -- the integral of the remainder integrand
  have hSA : ∑ i ∈ Finset.range M₁, twoDAmp β b N h₁ h₂ k₁ k₂ (fun u v s => u ^ i * a i v s)
      = ∫ z, ∑ i ∈ Finset.range M₁,
          twoDIntegrand β N h₁ h₂ k₁ k₂ (fun u v s => u ^ i * a i v s) z ∂(boxMeasure₂ b) := by
    rw [integral_finsetSum _ iA]
    exact Finset.sum_congr rfl fun i _ => twoDAmp_eq_prod β b N h₁ h₂ k₁ k₂ _ (hA i)
  have hSB : ∑ j ∈ Finset.range M₂, twoDAmp β b N h₁ h₂ k₁ k₂ (fun u v s => v ^ j * bj j u s)
      = ∫ z, ∑ j ∈ Finset.range M₂,
          twoDIntegrand β N h₁ h₂ k₁ k₂ (fun u v s => v ^ j * bj j u s) z ∂(boxMeasure₂ b) := by
    rw [integral_finsetSum _ iB]
    exact Finset.sum_congr rfl fun j _ => twoDAmp_eq_prod β b N h₁ h₂ k₁ k₂ _ (hB j)
  have hSC : ∑ i ∈ Finset.range M₁, ∑ j ∈ Finset.range M₂,
        twoDAmp β b N h₁ h₂ k₁ k₂ (fun u v s => c i j s * (u ^ i * v ^ j))
      = ∫ z, ∑ i ∈ Finset.range M₁, ∑ j ∈ Finset.range M₂,
          twoDIntegrand β N h₁ h₂ k₁ k₂ (fun u v s => c i j s * (u ^ i * v ^ j)) z
          ∂(boxMeasure₂ b) := by
    rw [integral_finsetSum _ iC]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [integral_finsetSum _ fun j _ => twoDIntegrand_integrable β b N h₁ h₂ k₁ k₂ _ (hC i j)]
    exact Finset.sum_congr rfl fun j _ => twoDAmp_eq_prod β b N h₁ h₂ k₁ k₂ _ (hC i j)
  have i1 : Integrable (fun z => twoDIntegrand β N h₁ h₂ k₁ k₂ Φ z - ∑ i ∈ Finset.range M₁,
      twoDIntegrand β N h₁ h₂ k₁ k₂ (fun u v s => u ^ i * a i v s) z) (boxMeasure₂ b) :=
    iΦ.sub iSA
  have i2 : Integrable (fun z => (twoDIntegrand β N h₁ h₂ k₁ k₂ Φ z - ∑ i ∈ Finset.range M₁,
      twoDIntegrand β N h₁ h₂ k₁ k₂ (fun u v s => u ^ i * a i v s) z)
      - ∑ j ∈ Finset.range M₂,
        twoDIntegrand β N h₁ h₂ k₁ k₂ (fun u v s => v ^ j * bj j u s) z) (boxMeasure₂ b) :=
    i1.sub iSB
  have hrem : twoDAmp β b N h₁ h₂ k₁ k₂ (rectRem Φ a bj c M₁ M₂)
      = twoDAmp β b N h₁ h₂ k₁ k₂ Φ
        - (∑ i ∈ Finset.range M₁, twoDAmp β b N h₁ h₂ k₁ k₂ (fun u v s => u ^ i * a i v s))
        - (∑ j ∈ Finset.range M₂, twoDAmp β b N h₁ h₂ k₁ k₂ (fun u v s => v ^ j * bj j u s))
        + ∑ i ∈ Finset.range M₁, ∑ j ∈ Finset.range M₂,
            twoDAmp β b N h₁ h₂ k₁ k₂ (fun u v s => c i j s * (u ^ i * v ^ j)) := by
    rw [twoDAmp_eq_prod β b N h₁ h₂ k₁ k₂ _ hR, twoDAmp_eq_prod β b N h₁ h₂ k₁ k₂ Φ hΦ, hSA, hSB,
      hSC, ← integral_sub iΦ iSA, ← integral_sub i1 iSB, ← integral_add i2 iSC]
    exact integral_congr_ae (Filter.Eventually.of_forall fun z =>
      twoDIntegrand_rectRem β N h₁ h₂ k₁ k₂ Φ a bj c M₁ M₂ z)
  rw [hrem]
  ring

/-- Absorbing a `u`-monomial into the first exponent. -/
theorem twoDAmp_pow_absorb (β b N : ℝ) (h₁ h₂ k₁ k₂ i : ℕ) (Ψ : ℝ → ℝ → ℝ) :
    twoDAmp β b N h₁ h₂ k₁ k₂ (fun u v s => u ^ i * Ψ v s)
      = twoDAmp β b N (h₁ + i) h₂ k₁ k₂ (fun _ v s => Ψ v s) := by
  unfold twoDAmp
  refine setIntegral_congr_fun measurableSet_Ioc fun u _ => ?_
  have hin : ∫ v in Ioc (0 : ℝ) b, v ^ h₂ * (Real.exp (-β * (N * (u ^ k₁ * v ^ k₂)) ^ 2)
        * (u ^ i * Ψ v (N * (u ^ k₁ * v ^ k₂))))
      = u ^ i * ∫ v in Ioc (0 : ℝ) b, v ^ h₂ * (Real.exp (-β * (N * (u ^ k₁ * v ^ k₂)) ^ 2)
        * Ψ v (N * (u ^ k₁ * v ^ k₂))) := by
    rw [← integral_const_mul]
    exact setIntegral_congr_fun measurableSet_Ioc fun v _ => by ring
  rw [hin, pow_add]
  ring

/-- Absorbing a `v`-monomial into the second exponent. -/
theorem twoDAmp_pow_absorb' (β b N : ℝ) (h₁ h₂ k₁ k₂ j : ℕ) (Ψ : ℝ → ℝ → ℝ) :
    twoDAmp β b N h₁ h₂ k₁ k₂ (fun u v s => v ^ j * Ψ u s)
      = twoDAmp β b N h₁ (h₂ + j) k₁ k₂ (fun u _ s => Ψ u s) := by
  unfold twoDAmp
  refine setIntegral_congr_fun measurableSet_Ioc fun u _ => ?_
  have hin : ∫ v in Ioc (0 : ℝ) b, v ^ h₂ * (Real.exp (-β * (N * (u ^ k₁ * v ^ k₂)) ^ 2)
        * (v ^ j * Ψ u (N * (u ^ k₁ * v ^ k₂))))
      = ∫ v in Ioc (0 : ℝ) b, v ^ (h₂ + j) * (Real.exp (-β * (N * (u ^ k₁ * v ^ k₂)) ^ 2)
        * Ψ u (N * (u ^ k₁ * v ^ k₂))) :=
    setIntegral_congr_fun measurableSet_Ioc fun v _ => by rw [pow_add]; ring
  rw [hin]

/-- A corner monomial `c(s) u^i v^j` is the constant amplitude with both exponents shifted. -/
theorem twoDAmp_corner (β b N : ℝ) (h₁ h₂ k₁ k₂ i j : ℕ) (c : ℝ → ℝ) :
    twoDAmp β b N h₁ h₂ k₁ k₂ (fun u v s => c s * (u ^ i * v ^ j))
      = twoDAmp β b N (h₁ + i) (h₂ + j) k₁ k₂ (fun _ _ s => c s) := by
  unfold twoDAmp
  refine setIntegral_congr_fun measurableSet_Ioc fun u _ => ?_
  have hin : ∫ v in Ioc (0 : ℝ) b, v ^ h₂ * (Real.exp (-β * (N * (u ^ k₁ * v ^ k₂)) ^ 2)
        * (c (N * (u ^ k₁ * v ^ k₂)) * (u ^ i * v ^ j)))
      = u ^ i * ∫ v in Ioc (0 : ℝ) b, v ^ (h₂ + j) * (Real.exp (-β * (N * (u ^ k₁ * v ^ k₂)) ^ 2)
        * c (N * (u ^ k₁ * v ^ k₂))) := by
    rw [← integral_const_mul]
    exact setIntegral_congr_fun measurableSet_Ioc fun v _ => by rw [pow_add]; ring
  rw [hin, pow_add]
  ring

end Laplace.Grammar
