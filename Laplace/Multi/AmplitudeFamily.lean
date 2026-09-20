/-
Copyright (c) 2026 Timaeus Research. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniel Murfet
-/
import Mathlib
import Laplace.Multi.CutoffMonomialFamily

/-!
# A positive-weight amplitude family: forcing agreement on all amplitudes `a · g`

`CutoffMonomialFamily` proves that a fixed *plateau* cutoff `χ` (equal to `1` on a ball
around the zero `p`) times all coordinate monomials is a sufficient family: projective
agreement beyond all orders on `χ · coordMonomial p m` forces germ equality of the losses.
There the plateau hypothesis `χ = 1 near p` is used only to reconstruct an arbitrary smooth
test `φ` supported near `p` as `φ = χ · φ`.

Here we drop the plateau. Let `a ≥ 0` be any continuous compactly supported *weight* whose
coercivity bound `L₁ ≥ c ‖w − p‖^ν` holds on `tsupport a`. If projective agreement holds
beyond all orders on the weighted family `a · coordMonomial p m` over all words `m`, then it
holds for every amplitude `a · g` with `g` smooth and compactly supported
(`superPoly_projDiff_of_weighted_monomials`).

The proof is the majorant engine of `superPoly_projDiff_of_cutoff_monomials` with the test
taken to be `a · g` from the outset: the Taylor decomposition `a · g = a · T + a · (g − T)`
needs no plateau reconstruction. `a · T` is a finite combination of the family; `a · (g − T)`
is dominated by `M · (a · ρ')` for the polynomial majorant `ρ' = ∑ᵢ (wᵢ − pᵢ)^{2N}`, whose
`L₁`-Boltzmann mass is `O(t^{-2N/ν})` by the coercivity bound and whose `L₂`-mass is
transferred by the family up to `C(t)` and beyond-all-orders errors.

This is the "positive-weight version of Q1" (germbij research note, Rank 1) and the
foundation for the non-product-cutoff common-cylinder theorem, where `a` is the tangential
marginal `a(x) = ∫ χ(x, y) dy` of an arbitrary product-space cutoff.
-/

open Asymptotics Filter MeasureTheory
open scoped ENNReal Topology ContDiff

namespace Laplace

variable {ι : Type*} [Fintype ι]
variable {L₁ L₂ : (ι → ℝ) → ℝ} {C : ℝ → ℝ}

/-- **Transfer from a weighted monomial family to all amplitudes.** Let `a ≥ 0` be a
continuous compactly supported weight with `L₁ ≥ c ‖w − p‖^ν` on `tsupport a` and `C`
polynomially bounded. If the projective difference is superpolynomially small on the family
`a · coordMonomial p m` for every word `m`, then it is superpolynomially small on every
amplitude `a · g` with `g` smooth and compactly supported. No plateau (`a = 1 near p`) is
needed. -/
theorem superPoly_projDiff_of_weighted_monomials
    (h1c : Continuous L₁) (h2c : Continuous L₂)
    {a : (ι → ℝ) → ℝ} (hac : Continuous a) (has : HasCompactSupport a) (ha0 : ∀ w, 0 ≤ a w)
    {p : ι → ℝ} {c ν : ℝ} (hc : 0 < c) (hν : 0 < ν)
    (hcoer : ∀ w ∈ tsupport a, c * ‖w - p‖ ^ ν ≤ L₁ w)
    {A : ℝ} (hA : 0 ≤ A) (hCbound : ∀ᶠ t in atTop, |C t| ≤ A * t ^ (Fintype.card ι))
    (hfam : ∀ (k : ℕ) (m : Fin k → ι),
      SuperPoly (projDiff L₁ L₂ C fun w ↦ a w * coordMonomial p m w))
    {g : (ι → ℝ) → ℝ} (hg : ContDiff ℝ ∞ g) (hgs : HasCompactSupport g) :
    SuperPoly (projDiff L₁ L₂ C fun w ↦ a w * g w) := by
  classical
  refine superPoly_of_forall_eventually_le fun N₀ ↦ ?_
  set d : ℕ := Fintype.card ι with hd_def
  -- the Taylor order
  obtain ⟨N, hN1, hNa⟩ : ∃ N : ℕ, 0 < N ∧ (N₀ : ℝ) + d + 1 ≤ ((2 * N : ℕ) : ℝ) / ν := by
    refine ⟨⌈ν * ((N₀ : ℝ) + d + 1) / 2⌉₊ + 1, Nat.succ_pos _, ?_⟩
    rw [le_div_iff₀ hν]
    have := Nat.le_ceil (ν * ((N₀ : ℝ) + d + 1) / 2)
    push_cast
    linarith
  set n : ℕ := 2 * N - 1 with hn_def
  have hn1 : n + 1 = 2 * N := by omega
  obtain ⟨M, hM0, hM⟩ := exists_taylor_remainder_bound hg hgs p n
  rw [hn1] at hM
  set T : (ι → ℝ) → ℝ := fun x ↦ ∑ k ∈ Finset.range (2 * N),
    ((k.factorial : ℝ)⁻¹) * iteratedFDeriv ℝ k g p (fun _ ↦ x - p) with hT_def
  have hTc : Continuous T := by
    refine continuous_finsetSum _ fun k _ ↦ continuous_const.mul ?_
    exact (iteratedFDeriv ℝ k g p).coe_continuous.comp
      (continuous_pi fun _ ↦ continuous_id.sub continuous_const)
  -- the decomposition `a · g = a · T + a · (g − T)` (no plateau reconstruction needed)
  have hsplit : (fun w ↦ a w * g w) = fun w ↦ a w * T w + a w * (g w - T w) := by
    funext x; ring
  have haT_c : Continuous fun w ↦ a w * T w := hac.mul hTc
  have haT_s : HasCompactSupport fun w ↦ a w * T w := has.mul_right
  have hrem_c : Continuous fun w ↦ a w * (g w - T w) := hac.mul (hg.continuous.sub hTc)
  have hrem_s : HasCompactSupport fun w ↦ a w * (g w - T w) := has.mul_right
  have hdecomp : ∀ t, projDiff L₁ L₂ C (fun w ↦ a w * g w) t =
      projDiff L₁ L₂ C (fun w ↦ a w * T w) t +
      projDiff L₁ L₂ C (fun w ↦ a w * (g w - T w)) t := by
    intro t
    rw [← projDiff_add h1c h2c haT_c haT_s hrem_c hrem_s]
    conv_lhs => rw [hsplit]
  -- (1) the Taylor part is a finite combination of the family
  set coef : (k : ℕ) → (Fin k → ι) → ℝ := fun k m ↦
    (k.factorial : ℝ)⁻¹ * iteratedFDeriv ℝ k g p (fun j ↦ Pi.single (m j) (1 : ℝ)) with hcoef_def
  have hTexp : (fun w ↦ a w * T w) = fun w ↦ ∑ k ∈ Finset.range (2 * N),
      ∑ m : Fin k → ι, coef k m * (a w * coordMonomial p m w) := by
    funext w
    simp only [hT_def, Finset.mul_sum]
    refine Finset.sum_congr rfl fun k _ ↦ ?_
    rw [iteratedFDeriv_apply_const_eq_sum_words, Finset.mul_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun m _ ↦ ?_
    simp only [hcoef_def]
    ring
  have hmono_c : ∀ (k : ℕ) (m : Fin k → ι), Continuous fun w ↦ a w * coordMonomial p m w :=
    fun k m ↦ hac.mul (coordMonomial_continuous p m)
  have hmono_s : ∀ (k : ℕ) (m : Fin k → ι), HasCompactSupport fun w ↦ a w * coordMonomial p m w :=
    fun k m ↦ has.mul_right
  have hTpart : SuperPoly (projDiff L₁ L₂ C fun w ↦ a w * T w) := by
    have key : ∀ t, projDiff L₁ L₂ C (fun w ↦ ∑ k ∈ Finset.range (2 * N),
        ∑ m : Fin k → ι, coef k m * (a w * coordMonomial p m w)) t =
        ∑ k ∈ Finset.range (2 * N), ∑ m : Fin k → ι,
          coef k m * projDiff L₁ L₂ C (fun w ↦ a w * coordMonomial p m w) t := by
      intro t
      rw [projDiff_finset_sum _ h1c h2c
        (fun k w ↦ ∑ m : Fin k → ι, coef k m * (a w * coordMonomial p m w))
        (fun k ↦ continuous_finsetSum _ fun m _ ↦ continuous_const.mul (hmono_c k m))
        (fun k ↦ hasCompactSupport_finset_sum' _ _ fun m ↦ (hmono_s k m).mul_left)]
      refine Finset.sum_congr rfl fun k _ ↦ ?_
      rw [projDiff_finset_sum _ h1c h2c (fun m w ↦ coef k m * (a w * coordMonomial p m w))
        (fun m ↦ continuous_const.mul (hmono_c k m)) (fun m ↦ (hmono_s k m).mul_left)]
      refine Finset.sum_congr rfl fun m _ ↦ ?_
      exact projDiff_const_mul _ _ _
    have hS : SuperPoly fun t ↦ ∑ k ∈ Finset.range (2 * N), ∑ m : Fin k → ι,
        coef k m * projDiff L₁ L₂ C (fun w ↦ a w * coordMonomial p m w) t :=
      SuperPoly.finset_sum _ fun k _ ↦ SuperPoly.finset_sum _ fun m _ ↦ (hfam k m).const_mul _
    rw [hTexp]
    intro N'
    exact (hS N').congr' (Eventually.of_forall fun t ↦ (key t).symm) EventuallyEq.rfl
  -- (2) the remainder part, via the polynomial majorant
  obtain ⟨K, hK0, hK⟩ := exists_pow_mul_exp_neg_rpow_bound hc hν N
  set expo : ℝ := ((2 * N : ℕ) : ℝ) / ν with hexpo_def
  set ρ' : (ι → ℝ) → ℝ := fun w ↦ ∑ i, (w i - p i) ^ (2 * N) with hρ'_def
  have hρ'c : Continuous ρ' := by
    simp only [hρ'_def]
    fun_prop
  have hρ'0 : ∀ w, 0 ≤ ρ' w := fun w ↦
    Finset.sum_nonneg fun i _ ↦ Even.pow_nonneg (even_two_mul N) _
  have hremle : ∀ w, |a w * (g w - T w)| ≤ M * (a w * ρ' w) := by
    intro w
    have h1 : ‖w - p‖ ^ (2 * N) ≤ ρ' w := by
      have := norm_pow_le_sum_pow (w - p) hN1
      simpa [hρ'_def] using this
    rw [abs_mul, abs_of_nonneg (ha0 w)]
    calc a w * |g w - T w| ≤ a w * (M * ‖w - p‖ ^ (2 * N)) :=
          mul_le_mul_of_nonneg_left (hM w) (ha0 w)
      _ ≤ a w * (M * ρ' w) :=
          mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left h1 hM0) (ha0 w)
      _ = M * (a w * ρ' w) := by ring
  have haint : Integrable a := hac.integrable_of_hasCompactSupport has
  have hann : 0 ≤ ∫ w, a w := integral_nonneg ha0
  -- the `L₁`-mass of the majorant
  have hL1maj : ∀ t : ℝ, 0 < t →
      ∫ w, a w * ρ' w * Real.exp (-(t * L₁ w)) ≤ d * K * t ^ (-expo) * ∫ w, a w := by
    intro t ht
    have hpt : ∀ w, a w * ρ' w * Real.exp (-(t * L₁ w)) ≤ (d * K * t ^ (-expo)) * a w := by
      intro w
      by_cases hw : a w = 0
      · simp [hw]
      · have hwsupp : w ∈ tsupport a := subset_tsupport a hw
        have hco := hcoer w hwsupp
        have hρ'le : ρ' w ≤ d * ‖w - p‖ ^ (2 * N) := by
          have := sum_pow_le_card_mul_norm_pow (w - p) N
          simpa [hρ'_def, hd_def] using this
        have hexple : Real.exp (-(t * L₁ w)) ≤ Real.exp (-(t * (c * ‖w - p‖ ^ ν))) :=
          Real.exp_le_exp.mpr (neg_le_neg (mul_le_mul_of_nonneg_left hco ht.le))
        have hsup := hK t ht ‖w - p‖ (norm_nonneg _)
        have hd0 : (0 : ℝ) ≤ d := by positivity
        calc a w * ρ' w * Real.exp (-(t * L₁ w))
            ≤ a w * (d * ‖w - p‖ ^ (2 * N)) * Real.exp (-(t * (c * ‖w - p‖ ^ ν))) :=
              mul_le_mul (mul_le_mul_of_nonneg_left hρ'le (ha0 w)) hexple (Real.exp_pos _).le
                (mul_nonneg (ha0 w) (by positivity))
          _ = a w * d * (‖w - p‖ ^ (2 * N) * Real.exp (-(t * (c * ‖w - p‖ ^ ν)))) := by ring
          _ ≤ a w * d * (K * t ^ (-expo)) :=
              mul_le_mul_of_nonneg_left hsup (mul_nonneg (ha0 w) hd0)
          _ = (d * K * t ^ (-expo)) * a w := by ring
    calc ∫ w, a w * ρ' w * Real.exp (-(t * L₁ w))
        ≤ ∫ w, (d * K * t ^ (-expo)) * a w :=
          integral_mono (integrable_mul_exp_neg_of_compactSupport (hac.mul hρ'c)
            has.mul_right h1c t) (haint.const_mul _) hpt
      _ = d * K * t ^ (-expo) * ∫ w, a w := integral_const_mul _ _
  -- the `L₂`-mass of the majorant via the family
  have hmaj_eq : ∀ w, a w * ρ' w =
      ∑ i, a w * coordMonomial p (fun _ : Fin (2 * N) ↦ i) w := by
    intro w
    simp only [hρ'_def, sum_pow_eq_sum_coordMonomial, Finset.mul_sum]
  have hL2maj : ∀ t : ℝ, ∫ w, a w * ρ' w * Real.exp (-(t * L₂ w)) =
      C t * (∫ w, a w * ρ' w * Real.exp (-(t * L₁ w))) +
        ∑ i, projDiff L₁ L₂ C (fun w ↦ a w * coordMonomial p (fun _ : Fin (2 * N) ↦ i) w) t := by
    intro t
    have h2 : ∫ w, a w * ρ' w * Real.exp (-(t * L₂ w)) =
        ∑ i, ∫ w, a w * coordMonomial p (fun _ : Fin (2 * N) ↦ i) w * Real.exp (-(t * L₂ w)) := by
      rw [← integral_finsetSum _ fun i _ ↦
        integrable_mul_exp_neg_of_compactSupport (hmono_c _ _) (hmono_s _ _) h2c t]
      congr 1
      funext w
      rw [hmaj_eq w, Finset.sum_mul]
    have h1 : ∫ w, a w * ρ' w * Real.exp (-(t * L₁ w)) =
        ∑ i, ∫ w, a w * coordMonomial p (fun _ : Fin (2 * N) ↦ i) w * Real.exp (-(t * L₁ w)) := by
      rw [← integral_finsetSum _ fun i _ ↦
        integrable_mul_exp_neg_of_compactSupport (hmono_c _ _) (hmono_s _ _) h1c t]
      congr 1
      funext w
      rw [hmaj_eq w, Finset.sum_mul]
    rw [h2, h1, Finset.mul_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun i _ ↦ ?_
    unfold projDiff
    ring
  have hfamsum : SuperPoly fun t ↦
      ∑ i, projDiff L₁ L₂ C (fun w ↦ a w * coordMonomial p (fun _ : Fin (2 * N) ↦ i) w) t :=
    SuperPoly.finset_sum _ fun i _ ↦ hfam (2 * N) _
  -- eventual bounds on the two superpolynomial pieces
  have hTev : ∀ᶠ t in atTop, |projDiff L₁ L₂ C (fun w ↦ a w * T w) t| ≤ t ^ (-(N₀ : ℝ)) := by
    have := isLittleO_iff.mp (hTpart N₀) one_pos
    filter_upwards [this, eventually_gt_atTop (0 : ℝ)] with t ht htpos
    rw [Real.norm_eq_abs, Real.norm_of_nonneg (Real.rpow_nonneg htpos.le _), one_mul] at ht
    exact ht
  have hFev : ∀ᶠ t in atTop, |∑ i, projDiff L₁ L₂ C
      (fun w ↦ a w * coordMonomial p (fun _ : Fin (2 * N) ↦ i) w) t| ≤ t ^ (-(N₀ : ℝ)) := by
    have := isLittleO_iff.mp (hfamsum N₀) one_pos
    filter_upwards [this, eventually_gt_atTop (0 : ℝ)] with t ht htpos
    rw [Real.norm_eq_abs, Real.norm_of_nonneg (Real.rpow_nonneg htpos.le _), one_mul] at ht
    exact ht
  refine ⟨1 + 2 * M * A * d * K * (∫ w, a w) + M, ?_⟩
  filter_upwards [hTev, hFev, hCbound, eventually_ge_atTop (1 : ℝ)] with t hT hF hCt ht1
  have htpos : 0 < t := lt_of_lt_of_le one_pos ht1
  have htN : 0 ≤ t ^ (-(N₀ : ℝ)) := Real.rpow_nonneg htpos.le _
  -- `t^d t^{-expo} ≤ t^{-N₀}`
  have hpow : (t : ℝ) ^ d * t ^ (-expo) ≤ t ^ (-(N₀ : ℝ)) := by
    rw [← Real.rpow_natCast, ← Real.rpow_add htpos]
    exact Real.rpow_le_rpow_of_exponent_le ht1 (by linarith)
  -- the remainder part
  set R₂ : ℝ := ∫ w, a w * (g w - T w) * Real.exp (-(t * L₂ w)) with hR₂_def
  set R₁ : ℝ := ∫ w, a w * (g w - T w) * Real.exp (-(t * L₁ w)) with hR₁_def
  set J₂ : ℝ := ∫ w, a w * ρ' w * Real.exp (-(t * L₂ w)) with hJ₂_def
  set J₁ : ℝ := ∫ w, a w * ρ' w * Real.exp (-(t * L₁ w)) with hJ₁_def
  have hJ₁0 : 0 ≤ J₁ := integral_nonneg fun w ↦
    mul_nonneg (mul_nonneg (ha0 w) (hρ'0 w)) (Real.exp_pos _).le
  have hRle : ∀ (L : (ι → ℝ) → ℝ), Continuous L →
      |∫ w, a w * (g w - T w) * Real.exp (-(t * L w))| ≤
        M * ∫ w, a w * ρ' w * Real.exp (-(t * L w)) := by
    intro L hLc
    calc |∫ w, a w * (g w - T w) * Real.exp (-(t * L w))|
        ≤ ∫ w, |a w * (g w - T w) * Real.exp (-(t * L w))| := abs_integral_le_integral_abs
      _ ≤ ∫ w, M * (a w * ρ' w * Real.exp (-(t * L w))) := by
          refine integral_mono (integrable_mul_exp_neg_of_compactSupport hrem_c hrem_s hLc t).abs
            ((integrable_mul_exp_neg_of_compactSupport (hac.mul hρ'c) has.mul_right hLc t).const_mul
              M) fun w ↦ ?_
          rw [abs_mul, abs_of_pos (Real.exp_pos _)]
          calc |a w * (g w - T w)| * Real.exp (-(t * L w))
              ≤ M * (a w * ρ' w) * Real.exp (-(t * L w)) :=
                mul_le_mul_of_nonneg_right (hremle w) (Real.exp_pos _).le
            _ = M * (a w * ρ' w * Real.exp (-(t * L w))) := by ring
      _ = M * ∫ w, a w * ρ' w * Real.exp (-(t * L w)) := integral_const_mul _ _
  have hR₂le : |R₂| ≤ M * J₂ := hRle L₂ h2c
  have hR₁le : |R₁| ≤ M * J₁ := hRle L₁ h1c
  have hJ₁le : J₁ ≤ d * K * t ^ (-expo) * ∫ w, a w := hL1maj t htpos
  have hJ₂le : J₂ ≤ |C t| * J₁ + t ^ (-(N₀ : ℝ)) := by
    have := hL2maj t
    rw [← hJ₂_def, ← hJ₁_def] at this
    rw [this]
    have h1 : C t * J₁ ≤ |C t| * J₁ := mul_le_mul_of_nonneg_right (le_abs_self _) hJ₁0
    have h2 := le_abs_self (∑ i, projDiff L₁ L₂ C
      (fun w ↦ a w * coordMonomial p (fun _ : Fin (2 * N) ↦ i) w) t)
    linarith
  have hCJ : |C t| * J₁ ≤ A * d * K * (∫ w, a w) * t ^ (-(N₀ : ℝ)) := by
    calc |C t| * J₁ ≤ (A * t ^ d) * (d * K * t ^ (-expo) * ∫ w, a w) :=
          mul_le_mul hCt hJ₁le hJ₁0 (by positivity)
      _ = A * d * K * (∫ w, a w) * (t ^ d * t ^ (-expo)) := by ring
      _ ≤ A * d * K * (∫ w, a w) * t ^ (-(N₀ : ℝ)) := by gcongr
  have hRpart : |projDiff L₁ L₂ C (fun w ↦ a w * (g w - T w)) t| ≤
      (2 * M * A * d * K * (∫ w, a w) + M) * t ^ (-(N₀ : ℝ)) := by
    have hexpand : projDiff L₁ L₂ C (fun w ↦ a w * (g w - T w)) t = R₂ - C t * R₁ := rfl
    rw [hexpand]
    calc |R₂ - C t * R₁| ≤ |R₂| + |C t| * |R₁| := by
          rw [← abs_mul]
          exact abs_sub _ _
      _ ≤ M * J₂ + |C t| * (M * J₁) :=
          add_le_add hR₂le (mul_le_mul_of_nonneg_left hR₁le (abs_nonneg _))
      _ ≤ M * (|C t| * J₁ + t ^ (-(N₀ : ℝ))) + M * (|C t| * J₁) := by
          have := mul_le_mul_of_nonneg_left hJ₂le hM0
          nlinarith [mul_nonneg (abs_nonneg (C t)) hJ₁0]
      _ = 2 * M * (|C t| * J₁) + M * t ^ (-(N₀ : ℝ)) := by ring
      _ ≤ 2 * M * (A * d * K * (∫ w, a w) * t ^ (-(N₀ : ℝ))) + M * t ^ (-(N₀ : ℝ)) := by
          gcongr
      _ = (2 * M * A * d * K * (∫ w, a w) + M) * t ^ (-(N₀ : ℝ)) := by ring
  rw [hdecomp t]
  calc |projDiff L₁ L₂ C (fun w ↦ a w * T w) t +
        projDiff L₁ L₂ C (fun w ↦ a w * (g w - T w)) t|
      ≤ |projDiff L₁ L₂ C (fun w ↦ a w * T w) t| +
        |projDiff L₁ L₂ C (fun w ↦ a w * (g w - T w)) t| := abs_add_le _ _
    _ ≤ t ^ (-(N₀ : ℝ)) + (2 * M * A * d * K * (∫ w, a w) + M) * t ^ (-(N₀ : ℝ)) :=
        add_le_add hT hRpart
    _ = (1 + 2 * M * A * d * K * (∫ w, a w) + M) * t ^ (-(N₀ : ℝ)) := by ring

end Laplace
