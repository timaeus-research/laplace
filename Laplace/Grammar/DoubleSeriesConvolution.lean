/-
Copyright (c) 2026 Timaeus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Laplace.Grammar.TaylorProjections

/-!
# Weighted convolution of double series (grammar §4.2, analytic bridge)

The Cauchy product of two double power series, encoded on coefficient arrays `ℕ × ℕ → ℝ`:
`(f * g)_k = ∑_{a ≤ k} f_a g_{k-a}` (`conv`), with the weighted `ℓ¹` norm
`N_ρ(f) = ∑ |f_k| ρ^{|k|}` (`wnorm`) and weighted summability (`WSummable`). The two results
(Astra #7(a)) are the closure `N_ρ(f * g) ≤ N_ρ(f) N_ρ(g)` (`wnorm_conv_le`, with `WSummable` of the
product) and multiplicativity of evaluation `∑ (f*g)_k u^i v^j = (∑ f_k u^i v^j)(∑ g_k u^i v^j)` for
`|u|, |v| ≤ ρ` (`dblSum_conv`). Both come from one finite-fiber bridge: the fibre of the addition
map `(ℕ²)² → ℕ²` over `k` is in bijection with the box `{a ≤ k}` (`fiber_tsum_eq`), so
`HasSum.tsum_fiberwise` regroups the product family. Zero `sorry`/`axiom`.
-/

open Real

namespace Laplace.Grammar

/-- Componentwise truncated subtraction on `ℕ × ℕ`. -/
def psub (k a : ℕ × ℕ) : ℕ × ℕ := (k.1 - a.1, k.2 - a.2)

/-- The box `{a : a ≤ k}` of multi-indices below `k`. -/
def box (k : ℕ × ℕ) : Finset (ℕ × ℕ) := Finset.range (k.1 + 1) ×ˢ Finset.range (k.2 + 1)

theorem mem_box {k a : ℕ × ℕ} : a ∈ box k ↔ a.1 ≤ k.1 ∧ a.2 ≤ k.2 := by
  simp [box]

theorem add_psub_of_mem {k a : ℕ × ℕ} (ha : a ∈ box k) : a + psub k a = k := by
  rw [mem_box] at ha
  ext
  · simp only [Prod.fst_add, psub]; omega
  · simp only [Prod.snd_add, psub]; omega

/-- The convolution `(f * g)_k = ∑_{a ≤ k} f_a g_{k-a}`. -/
noncomputable def conv (f g : ℕ × ℕ → ℝ) (k : ℕ × ℕ) : ℝ := ∑ a ∈ box k, f a * g (psub k a)

/-- Weighted summability at radius `ρ`. -/
def WSummable (ρ : ℝ) (f : ℕ × ℕ → ℝ) : Prop := Summable fun k => |f k| * ρ ^ (k.1 + k.2)

/-- The weighted `ℓ¹` norm `N_ρ(f) = ∑ |f_k| ρ^{|k|}`. -/
noncomputable def wnorm (ρ : ℝ) (f : ℕ × ℕ → ℝ) : ℝ := ∑' k, |f k| * ρ ^ (k.1 + k.2)

/-- The fibre of the addition map over `k`, as a subtype. -/
abbrev addFiber (k : ℕ × ℕ) : Type := ↥((fun p : (ℕ × ℕ) × (ℕ × ℕ) => p.1 + p.2) ⁻¹' {k})

/-- The box `{a ≤ k}` is in bijection with the fibre `{(a, b) : a + b = k}`. -/
noncomputable def fiberEquiv (k : ℕ × ℕ) : ↥(box k) ≃ addFiber k where
  toFun a := ⟨(a.1, psub k a.1), by
    simp only [Set.mem_preimage, Set.mem_singleton_iff]
    exact add_psub_of_mem a.2⟩
  invFun p := ⟨p.1.1, by
    have h := p.2
    simp only [Set.mem_preimage, Set.mem_singleton_iff] at h
    rw [mem_box]
    have h1 := congrArg Prod.fst h
    have h2 := congrArg Prod.snd h
    simp only [Prod.fst_add, Prod.snd_add] at h1 h2
    omega⟩
  left_inv a := by simp
  right_inv p := by
    have h := p.2
    simp only [Set.mem_preimage, Set.mem_singleton_iff] at h
    have h1 := congrArg Prod.fst h
    have h2 := congrArg Prod.snd h
    simp only [Prod.fst_add, Prod.snd_add] at h1 h2
    apply Subtype.ext
    show ((p.1.1, psub k p.1.1) : (ℕ × ℕ) × (ℕ × ℕ)) = p.1
    refine Prod.ext rfl (Prod.ext ?_ ?_)
    · simp only [psub]; omega
    · simp only [psub]; omega

/-- **The finite-fibre bridge**: the sum over the fibre `{(a,b) : a + b = k}` is the finite sum
over the box. -/
theorem fiber_tsum_eq (H : (ℕ × ℕ) × (ℕ × ℕ) → ℝ) (k : ℕ × ℕ) :
    ∑' p : addFiber k, H p = ∑ a ∈ box k, H (a, psub k a) := by
  rw [← (fiberEquiv k).tsum_eq]
  change ∑' c : ↥(box k), H (c.1, psub k c.1) = _
  exact Finset.tsum_subtype (box k) (fun a => H (a, psub k a))

/-- The degrees add along the fibre. -/
theorem deg_add_psub {k a : ℕ × ℕ} (ha : a ∈ box k) :
    (a.1 + a.2) + ((psub k a).1 + (psub k a).2) = k.1 + k.2 := by
  rw [mem_box] at ha
  simp only [psub]
  omega

/-- **Weighted closure**: the convolution of weighted-summable arrays is weighted-summable with
`N_ρ(f * g) ≤ N_ρ(f) N_ρ(g)`. -/
theorem wnorm_conv_le (ρ : ℝ) (hρ : 0 < ρ) (f g : ℕ × ℕ → ℝ) (hf : WSummable ρ f)
    (hg : WSummable ρ g) :
    WSummable ρ (conv f g) ∧ wnorm ρ (conv f g) ≤ wnorm ρ f * wnorm ρ g := by
  -- the weighted absolute product family
  set F : ℕ × ℕ → ℝ := fun a => |f a| * ρ ^ (a.1 + a.2) with hF
  set G : ℕ × ℕ → ℝ := fun b => |g b| * ρ ^ (b.1 + b.2) with hG
  have hF' : Summable fun a => ‖F a‖ := by
    refine hf.congr fun a => ?_
    have : 0 ≤ F a := by simp only [hF]; positivity
    exact (Real.norm_of_nonneg this).symm
  have hG' : Summable fun b => ‖G b‖ := by
    refine hg.congr fun b => ?_
    have : 0 ≤ G b := by simp only [hG]; positivity
    exact (Real.norm_of_nonneg this).symm
  have hP : Summable fun p : (ℕ × ℕ) × (ℕ × ℕ) => F p.1 * G p.2 :=
    summable_mul_of_summable_norm hF' hG'
  have hPsum : HasSum (fun p : (ℕ × ℕ) × (ℕ × ℕ) => F p.1 * G p.2) (wnorm ρ f * wnorm ρ g) := by
    have := hP.hasSum
    rwa [← tsum_mul_tsum_of_summable_norm hF' hG'] at this
  -- group along the fibres of addition
  have hgrp := hPsum.tsum_fiberwise (fun p => p.1 + p.2)
  -- the fibre sums
  set B : ℕ × ℕ → ℝ := fun k => ρ ^ (k.1 + k.2) * ∑ a ∈ box k, |f a| * |g (psub k a)| with hB
  have hfib : ∀ k, ∑' p : addFiber k,
      F (p : (ℕ × ℕ) × (ℕ × ℕ)).1 * G (p : (ℕ × ℕ) × (ℕ × ℕ)).2 = B k := by
    intro k
    rw [fiber_tsum_eq (fun p => F p.1 * G p.2) k]
    simp only [hB, hF, hG, Finset.mul_sum]
    refine Finset.sum_congr rfl fun a ha => ?_
    rw [← deg_add_psub ha, pow_add]
    ring
  have hBsum : HasSum B (wnorm ρ f * wnorm ρ g) := by
    refine hgrp.congr_fun ?_
    intro k
    exact (hfib k).symm
  have hB0 : ∀ k, 0 ≤ B k := fun k => by
    simp only [hB]
    exact mul_nonneg (by positivity) (Finset.sum_nonneg fun a _ => by positivity)
  have hle : ∀ k, |conv f g k| * ρ ^ (k.1 + k.2) ≤ B k := by
    intro k
    simp only [hB, conv]
    rw [mul_comm]
    refine mul_le_mul_of_nonneg_left ?_ (by positivity)
    refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun a _ => ?_)
    rw [abs_mul]
  refine ⟨Summable.of_nonneg_of_le (fun k => by positivity) hle hBsum.summable, ?_⟩
  rw [← hBsum.tsum_eq]
  unfold wnorm
  exact (Summable.of_nonneg_of_le (fun k => by positivity) hle hBsum.summable).tsum_le_tsum hle
    hBsum.summable

/-- The evaluation family is absolutely summable for `|u|, |v| ≤ ρ`, with sum at most `N_ρ(f)`. -/
theorem dblSum_abs_le_wnorm (ρ u v : ℝ) (f : ℕ × ℕ → ℝ) (hf : WSummable ρ f)
    (hu : |u| ≤ ρ) (hv : |v| ≤ ρ) :
    (Summable fun k : ℕ × ℕ => ‖f k * u ^ k.1 * v ^ k.2‖) ∧
      ∑' k : ℕ × ℕ, ‖f k * u ^ k.1 * v ^ k.2‖ ≤ wnorm ρ f := by
  have hρ : 0 ≤ ρ := (abs_nonneg u).trans hu
  have hle : ∀ k : ℕ × ℕ, ‖f k * u ^ k.1 * v ^ k.2‖ ≤ |f k| * ρ ^ (k.1 + k.2) := by
    intro k
    rw [Real.norm_eq_abs, abs_mul, abs_mul, abs_pow, abs_pow, pow_add, mul_assoc]
    refine mul_le_mul_of_nonneg_left ?_ (abs_nonneg _)
    exact mul_le_mul (pow_le_pow_left₀ (abs_nonneg _) hu _) (pow_le_pow_left₀ (abs_nonneg _) hv _)
      (by positivity) (by positivity)
  have hs : Summable fun k : ℕ × ℕ => ‖f k * u ^ k.1 * v ^ k.2‖ :=
    Summable.of_nonneg_of_le (fun k => norm_nonneg _) hle hf
  exact ⟨hs, hs.tsum_le_tsum hle hf⟩

/-- **Multiplicativity of evaluation**: `∑ (f*g)_k u^i v^j = (∑ f_k u^i v^j)(∑ g_k u^i v^j)`. -/
theorem dblSum_conv (ρ u v : ℝ) (f g : ℕ × ℕ → ℝ) (hf : WSummable ρ f) (hg : WSummable ρ g)
    (hu : |u| ≤ ρ) (hv : |v| ≤ ρ) :
    dblSum (conv f g) u v = dblSum f u v * dblSum g u v := by
  set Fe : ℕ × ℕ → ℝ := fun a => f a * u ^ a.1 * v ^ a.2 with hFe
  set Ge : ℕ × ℕ → ℝ := fun b => g b * u ^ b.1 * v ^ b.2 with hGe
  have hF' : Summable fun a => ‖Fe a‖ := (dblSum_abs_le_wnorm ρ u v f hf hu hv).1
  have hG' : Summable fun b => ‖Ge b‖ := (dblSum_abs_le_wnorm ρ u v g hg hu hv).1
  have hP : Summable fun p : (ℕ × ℕ) × (ℕ × ℕ) => Fe p.1 * Ge p.2 :=
    summable_mul_of_summable_norm hF' hG'
  have hPsum : HasSum (fun p : (ℕ × ℕ) × (ℕ × ℕ) => Fe p.1 * Ge p.2)
      (dblSum f u v * dblSum g u v) := by
    have := hP.hasSum
    unfold dblSum
    rwa [← tsum_mul_tsum_of_summable_norm hF' hG'] at this
  have hgrp := hPsum.tsum_fiberwise (fun p => p.1 + p.2)
  have hfib : ∀ k, ∑' p : addFiber k,
      Fe (p : (ℕ × ℕ) × (ℕ × ℕ)).1 * Ge (p : (ℕ × ℕ) × (ℕ × ℕ)).2
        = conv f g k * u ^ k.1 * v ^ k.2 := by
    intro k
    rw [fiber_tsum_eq (fun p => Fe p.1 * Ge p.2) k]
    simp only [conv, hFe, hGe, Finset.sum_mul]
    refine Finset.sum_congr rfl fun a ha => ?_
    have ha' := mem_box.1 ha
    have h1 : a.1 + (psub k a).1 = k.1 := by simp only [psub]; omega
    have h2 : a.2 + (psub k a).2 = k.2 := by simp only [psub]; omega
    rw [← h1, ← h2, pow_add, pow_add]
    ring
  have hconv : HasSum (fun k => conv f g k * u ^ k.1 * v ^ k.2) (dblSum f u v * dblSum g u v) :=
    hgrp.congr_fun fun k => (hfib k).symm
  unfold dblSum
  exact hconv.tsum_eq

end Laplace.Grammar
