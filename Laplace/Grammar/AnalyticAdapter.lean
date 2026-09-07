/-
Copyright (c) 2026 Timaeus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Laplace.Grammar.DoubleSeries

/-!
# The analytic amplitude adapter (grammar §4.2, analytic bridge)

An amplitude given on the box by a double power series with a radius margin,
`Φ(u, v, s) = ∑ c_{ij}(s) u^i v^j` with `|c_{ij}(s)| ρ^{i+j} ≤ H(s)`, `b < ρ`, is packaged into the
data of the `d = 2` cutoff theorem (Astra #6 route D): the continuous amplitude `anaAmp`
(coordinates clamped to `[0, b]` so that the series converges everywhere), the compatible
faces `anaFaceU`,
`anaFaceV` (`faceU`/`faceV` of unit 113), the face remainders with envelopes
`H(s) ρ^{-i-M₂}/(1−θ)`, `θ = b/ρ`, and the mixed remainder bound
`C₀ ρ^{-M₁-M₂}/(1−θ)² · u^{M₁} v^{M₂} (1+s)^D e^{βsL}`. Continuity in `s` is obtained from a locally
uniform bound (`continuous_tsum_of_locally_bounded`). Zero `sorry`/`axiom`.
-/

open Real Set

namespace Laplace.Grammar

/-- A series of continuous functions with a locally bounded dominating family is continuous. -/
theorem continuous_tsum_of_locally_bounded {X : Type*} [PseudoMetricSpace X] [ProperSpace X]
    {ι : Type*} (f : ι → X → ℝ) (hf : ∀ n, Continuous (f n)) (u : ι → ℝ) (hu : Summable u)
    (hu0 : ∀ n, 0 ≤ u n) (G : X → ℝ) (hG : Continuous G) (hbound : ∀ n x, |f n x| ≤ G x * u n) :
    Continuous fun x => ∑' n, f n x := by
  rw [continuous_iff_continuousAt]
  intro x₀
  obtain ⟨C, hC⟩ := (isCompact_closedBall x₀ 1).exists_bound_of_continuousOn hG.continuousOn
  have hcont : ContinuousOn (fun x => ∑' n, f n x) (Metric.closedBall x₀ 1) := by
    refine continuousOn_tsum (u := fun n => C * u n) (fun n => (hf n).continuousOn)
      (hu.mul_left C) fun n x hx => ?_
    rw [Real.norm_eq_abs]
    have hGx : G x ≤ C := by
      have := hC x hx
      rw [Real.norm_eq_abs] at this
      exact (le_abs_self _).trans this
    calc |f n x| ≤ G x * u n := hbound n x
      _ ≤ C * u n := mul_le_mul_of_nonneg_right hGx (hu0 n)
  exact hcont.continuousAt (Metric.closedBall_mem_nhds x₀ zero_lt_one)

/-- The product of two geometric families is summable. -/
theorem summable_geom_prod (θ : ℝ) (h0 : 0 ≤ θ) (h1 : θ < 1) :
    Summable fun ij : ℕ × ℕ => θ ^ ij.1 * θ ^ ij.2 := by
  have hg : Summable fun i : ℕ => ‖θ ^ i‖ := by
    refine (summable_geometric_of_lt_one h0 h1).congr fun i => ?_
    rw [Real.norm_eq_abs, abs_of_nonneg (pow_nonneg h0 _)]
  exact summable_mul_of_summable_norm hg hg

/-- The clamp of a coordinate to `[0, b]`. -/
noncomputable def clampB (b x : ℝ) : ℝ := max 0 (min b x)

theorem clampB_continuous (b : ℝ) : Continuous (clampB b) :=
  continuous_const.max (continuous_const.min continuous_id)

theorem clampB_nonneg (b x : ℝ) : 0 ≤ clampB b x := le_max_left _ _

theorem clampB_le (b x : ℝ) (hb : 0 ≤ b) : clampB b x ≤ b :=
  max_le hb (min_le_left _ _)

theorem clampB_of_mem (b x : ℝ) (hx : x ∈ Icc (0 : ℝ) b) : clampB b x = x := by
  unfold clampB
  rw [min_eq_right hx.2, max_eq_right hx.1]

/-- The analytic amplitude, with coordinates clamped to the box. -/
noncomputable def anaAmp (c : ℕ × ℕ → ℝ → ℝ) (b u v s : ℝ) : ℝ :=
  dblSum (fun ij => c ij s) (clampB b u) (clampB b v)

/-- The `u`-faces `a_i(v, s) = ∑_j c_{ij}(s) v^j` (clamped). -/
noncomputable def anaFaceU (c : ℕ × ℕ → ℝ → ℝ) (b : ℝ) (i : ℕ) (v s : ℝ) : ℝ :=
  faceU (fun ij => c ij s) i (clampB b v)

/-- The `v`-faces `b_j(u, s) = ∑_i c_{ij}(s) u^i` (clamped). -/
noncomputable def anaFaceV (c : ℕ × ℕ → ℝ → ℝ) (b : ℝ) (j : ℕ) (u s : ℝ) : ℝ :=
  faceV (fun ij => c ij s) j (clampB b u)

/-- The swapped coefficient array. -/
def swapC (c : ℕ × ℕ → ℝ → ℝ) : ℕ × ℕ → ℝ → ℝ := fun ij s => c (ij.2, ij.1) s

theorem anaFaceV_eq_swap (c : ℕ × ℕ → ℝ → ℝ) (b : ℝ) (j : ℕ) (u s : ℝ) :
    anaFaceV c b j u s = anaFaceU (swapC c) b j u s := rfl

theorem swapC_bound (c : ℕ × ℕ → ℝ → ℝ) (ρ : ℝ) (H : ℝ → ℝ)
    (hc : ∀ ij s, |c ij s| * ρ ^ (ij.1 + ij.2) ≤ H s) :
    ∀ ij s, |swapC c ij s| * ρ ^ (ij.1 + ij.2) ≤ H s := by
  intro ij s
  have := hc (ij.2, ij.1) s
  simp only at this
  rw [add_comm] at this
  exact this

/-- **Continuity of the analytic amplitude** in `(u, v, s)`. -/
theorem anaAmp_continuous (c : ℕ × ℕ → ℝ → ℝ) (b ρ : ℝ) (H : ℝ → ℝ) (hb : 0 < b) (hbρ : b < ρ)
    (hcc : ∀ ij, Continuous (c ij)) (hH : Continuous H)
    (hc : ∀ ij s, |c ij s| * ρ ^ (ij.1 + ij.2) ≤ H s) :
    Continuous fun x : ℝ × ℝ × ℝ => anaAmp c b x.1 x.2.1 x.2.2 := by
  have hρ : 0 < ρ := lt_trans hb hbρ
  have hθ0 : 0 ≤ b / ρ := by positivity
  have hθ1 : b / ρ < 1 := (div_lt_one hρ).2 hbρ
  unfold anaAmp dblSum
  refine continuous_tsum_of_locally_bounded
    (fun ij (x : ℝ × ℝ × ℝ) => c ij x.2.2 * (clampB b x.1) ^ ij.1 * (clampB b x.2.1) ^ ij.2)
    (fun ij => ?_) (fun ij => (b / ρ) ^ ij.1 * (b / ρ) ^ ij.2) (summable_geom_prod _ hθ0 hθ1)
    (fun ij => by positivity) (fun x => H x.2.2) (hH.comp (continuous_snd.comp continuous_snd))
    (fun ij x => ?_)
  · exact (((hcc ij).comp (continuous_snd.comp continuous_snd)).mul
      (((clampB_continuous b).comp continuous_fst).pow _)).mul
      (((clampB_continuous b).comp (continuous_fst.comp continuous_snd)).pow _)
  · have h := coeff_term_le (fun ij => c ij x.2.2) ρ (H x.2.2) (clampB b x.1) (clampB b x.2.1) hρ
      (fun ij => hc ij x.2.2) (clampB_nonneg _ _) (clampB_nonneg _ _) ij
    refine h.trans ?_
    have hH0 : 0 ≤ H x.2.2 := le_trans (by positivity) (hc (0, 0) x.2.2)
    have h1 : clampB b x.1 / ρ ≤ b / ρ := by gcongr; exact clampB_le b _ hb.le
    have h2 : clampB b x.2.1 / ρ ≤ b / ρ := by gcongr; exact clampB_le b _ hb.le
    have h1' : 0 ≤ clampB b x.1 / ρ := by have := clampB_nonneg b x.1; positivity
    have h2' : 0 ≤ clampB b x.2.1 / ρ := by have := clampB_nonneg b x.2.1; positivity
    calc H x.2.2 * (clampB b x.1 / ρ) ^ ij.1 * (clampB b x.2.1 / ρ) ^ ij.2
        ≤ H x.2.2 * (b / ρ) ^ ij.1 * (b / ρ) ^ ij.2 := by gcongr
      _ = _ := by ring

/-- **Continuity of the faces** in `(v, s)`. -/
theorem anaFaceU_continuous (c : ℕ × ℕ → ℝ → ℝ) (b ρ : ℝ) (H : ℝ → ℝ) (hb : 0 < b) (hbρ : b < ρ)
    (hcc : ∀ ij, Continuous (c ij)) (hH : Continuous H)
    (hc : ∀ ij s, |c ij s| * ρ ^ (ij.1 + ij.2) ≤ H s) (i : ℕ) :
    Continuous (Function.uncurry (anaFaceU c b i)) := by
  have hρ : 0 < ρ := lt_trans hb hbρ
  have hθ0 : 0 ≤ b / ρ := by positivity
  have hθ1 : b / ρ < 1 := (div_lt_one hρ).2 hbρ
  have hρi : 0 ≤ (ρ ^ i)⁻¹ := by positivity
  show Continuous fun p : ℝ × ℝ => ∑' j : ℕ, c (i, j) p.2 * (clampB b p.1) ^ j
  refine continuous_tsum_of_locally_bounded
    (fun j (p : ℝ × ℝ) => c (i, j) p.2 * (clampB b p.1) ^ j) (fun j => ?_)
    (fun j => (ρ ^ i)⁻¹ * (b / ρ) ^ j)
    ((summable_geometric_of_lt_one hθ0 hθ1).mul_left _) (fun j => by positivity)
    (fun p => H p.2) (hH.comp continuous_snd) (fun j p => ?_)
  · exact ((hcc (i, j)).comp continuous_snd).mul
      (((clampB_continuous b).comp continuous_fst).pow _)
  · have h := faceU_term_le (fun ij => c ij p.2) ρ (H p.2) (clampB b p.1) hρ
      (fun ij => hc ij p.2) (clampB_nonneg _ _) i j
    refine h.trans ?_
    have hH0 : 0 ≤ H p.2 := le_trans (by positivity) (hc (0, 0) p.2)
    have h1 : clampB b p.1 / ρ ≤ b / ρ := by gcongr; exact clampB_le b _ hb.le
    have h1' : 0 ≤ clampB b p.1 / ρ := by have := clampB_nonneg b p.1; positivity
    calc H p.2 * (ρ ^ i)⁻¹ * (clampB b p.1 / ρ) ^ j
        ≤ H p.2 * (ρ ^ i)⁻¹ * (b / ρ) ^ j := by gcongr
      _ = _ := by ring

theorem anaFaceV_continuous (c : ℕ × ℕ → ℝ → ℝ) (b ρ : ℝ) (H : ℝ → ℝ) (hb : 0 < b) (hbρ : b < ρ)
    (hcc : ∀ ij, Continuous (c ij)) (hH : Continuous H)
    (hc : ∀ ij s, |c ij s| * ρ ^ (ij.1 + ij.2) ≤ H s) (j : ℕ) :
    Continuous (Function.uncurry (anaFaceV c b j)) :=
  anaFaceU_continuous (swapC c) b ρ H hb hbρ (fun ij => hcc (ij.2, ij.1)) hH
    (swapC_bound c ρ H hc) j

/-- **The face remainder** on `(0, b]`:
`|a_i(v,s) − ∑_{m<M} c_{im}(s) v^m| ≤ H(s) ρ^{-i-M}/(1−b/ρ) · v^M`. -/
theorem anaFaceU_rem (c : ℕ × ℕ → ℝ → ℝ) (b ρ : ℝ) (H : ℝ → ℝ) (hb : 0 < b) (hbρ : b < ρ)
    (hc : ∀ ij s, |c ij s| * ρ ^ (ij.1 + ij.2) ≤ H s) (i M : ℕ) (v s : ℝ)
    (hv : v ∈ Ioc (0 : ℝ) b) :
    |anaFaceU c b i v s - ∑ m ∈ Finset.range M, c (i, m) s * v ^ m|
      ≤ H s * (ρ ^ i)⁻¹ * (ρ ^ M)⁻¹ / (1 - b / ρ) * v ^ M := by
  have hρ : 0 < ρ := lt_trans hb hbρ
  have hvρ : v < ρ := lt_of_le_of_lt hv.2 hbρ
  have hH0 : 0 ≤ H s := le_trans (by positivity) (hc (0, 0) s)
  unfold anaFaceU
  rw [clampB_of_mem b v ⟨hv.1.le, hv.2⟩]
  have h := faceU_rem_le (fun ij => c ij s) ρ (H s) v hρ (fun ij => hc ij s) hv.1.le hvρ i M
  refine h.trans ?_
  have h1 : 0 < 1 - v / ρ := by
    have : v / ρ < 1 := (div_lt_one hρ).2 hvρ
    linarith
  have h2 : 0 < 1 - b / ρ := by
    have : b / ρ < 1 := (div_lt_one hρ).2 hbρ
    linarith
  have h3 : 1 - b / ρ ≤ 1 - v / ρ := by
    have : v / ρ ≤ b / ρ := by gcongr; exact hv.2
    linarith
  have hv0 : 0 < v := hv.1
  have hne : (1 - b / ρ) ≠ 0 := h2.ne'
  have hρb : ρ - b ≠ 0 := by linarith
  have hX : 0 ≤ H s * (ρ ^ i)⁻¹ * (ρ ^ M)⁻¹ / (1 - b / ρ) * v ^ M := by positivity
  rw [div_pow, div_le_iff₀ h1]
  calc H s * (ρ ^ i)⁻¹ * (v ^ M / ρ ^ M) = H s * (ρ ^ i)⁻¹ * (ρ ^ M)⁻¹ * v ^ M := by ring
    _ = H s * (ρ ^ i)⁻¹ * (ρ ^ M)⁻¹ / (1 - b / ρ) * v ^ M * (1 - b / ρ) := by
        rw [div_mul_eq_mul_div, div_mul_cancel₀ _ hne]
    _ ≤ H s * (ρ ^ i)⁻¹ * (ρ ^ M)⁻¹ / (1 - b / ρ) * v ^ M * (1 - v / ρ) :=
        mul_le_mul_of_nonneg_left h3 hX

theorem anaFaceV_rem (c : ℕ × ℕ → ℝ → ℝ) (b ρ : ℝ) (H : ℝ → ℝ) (hb : 0 < b) (hbρ : b < ρ)
    (hc : ∀ ij s, |c ij s| * ρ ^ (ij.1 + ij.2) ≤ H s) (j M : ℕ) (u s : ℝ)
    (hu : u ∈ Ioc (0 : ℝ) b) :
    |anaFaceV c b j u s - ∑ m ∈ Finset.range M, c (m, j) s * u ^ m|
      ≤ H s * (ρ ^ j)⁻¹ * (ρ ^ M)⁻¹ / (1 - b / ρ) * u ^ M := by
  rw [anaFaceV_eq_swap]
  exact anaFaceU_rem (swapC c) b ρ H hb hbρ (swapC_bound c ρ H hc) j M u s hu

/-- **The mixed remainder** on the box:
`|R(u,v,s)| ≤ H(s) ρ^{-M₁-M₂}/(1−b/ρ)² · u^{M₁} v^{M₂}`. -/
theorem anaAmp_rectRem_le (c : ℕ × ℕ → ℝ → ℝ) (b ρ : ℝ) (H : ℝ → ℝ) (hb : 0 < b) (hbρ : b < ρ)
    (hc : ∀ ij s, |c ij s| * ρ ^ (ij.1 + ij.2) ≤ H s) (M₁ M₂ : ℕ) (u v s : ℝ)
    (hu : u ∈ Icc (0 : ℝ) b) (hv : v ∈ Icc (0 : ℝ) b) :
    |rectRem (anaAmp c b) (anaFaceU c b) (anaFaceV c b) (fun i j s => c (i, j) s) M₁ M₂ u v s|
      ≤ H s * (ρ ^ (M₁ + M₂))⁻¹ / (1 - b / ρ) ^ 2 * (u ^ M₁ * v ^ M₂) := by
  have hρ : 0 < ρ := lt_trans hb hbρ
  have huρ : u < ρ := lt_of_le_of_lt hu.2 hbρ
  have hvρ : v < ρ := lt_of_le_of_lt hv.2 hbρ
  have hH0 : 0 ≤ H s := le_trans (by positivity) (hc (0, 0) s)
  have hθ : b / ρ < 1 := (div_lt_one hρ).2 hbρ
  have h1 : 0 < 1 - b / ρ := by linarith
  have hu1 : 1 - b / ρ ≤ 1 - u / ρ := by
    have : u / ρ ≤ b / ρ := by gcongr; exact hu.2
    linarith
  have hv1 : 1 - b / ρ ≤ 1 - v / ρ := by
    have : v / ρ ≤ b / ρ := by gcongr; exact hv.2
    linarith
  unfold rectRem anaAmp anaFaceU anaFaceV
  rw [clampB_of_mem b u hu, clampB_of_mem b v hv,
    dbl_rect_identity (fun ij => c ij s) ρ (H s) u v hρ hH0 (fun ij => hc ij s) hu.1 huρ hv.1
      hvρ M₁ M₂]
  refine (dbl_tail_le (fun ij => c ij s) ρ (H s) u v hρ hH0 (fun ij => hc ij s) hu.1 huρ hv.1
    hvρ M₁ M₂).trans ?_
  have hnum : 0 ≤ H s * (ρ ^ (M₁ + M₂))⁻¹ * (u ^ M₁ * v ^ M₂) := by
    have := pow_nonneg hu.1 M₁
    have := pow_nonneg hv.1 M₂
    positivity
  have hden : (1 - b / ρ) ^ 2 ≤ (1 - u / ρ) * (1 - v / ρ) := by
    rw [sq]
    exact mul_le_mul hu1 hv1 h1.le (by linarith)
  calc H s * (ρ ^ (M₁ + M₂))⁻¹ * (u ^ M₁ * v ^ M₂) / ((1 - u / ρ) * (1 - v / ρ))
      ≤ H s * (ρ ^ (M₁ + M₂))⁻¹ * (u ^ M₁ * v ^ M₂) / (1 - b / ρ) ^ 2 :=
        div_le_div_of_nonneg_left hnum (by positivity) hden
    _ = _ := by ring

/-- The coefficient envelope `|c_{ij}(s)| ≤ H(s) ρ^{-i-j}`. -/
theorem anaCoeff_abs_le (c : ℕ × ℕ → ℝ → ℝ) (ρ : ℝ) (H : ℝ → ℝ) (hρ : 0 < ρ)
    (hc : ∀ ij s, |c ij s| * ρ ^ (ij.1 + ij.2) ≤ H s) (ij : ℕ × ℕ) (s : ℝ) :
    |c ij s| ≤ H s * (ρ ^ (ij.1 + ij.2))⁻¹ := by
  have hρi : 0 < ρ ^ (ij.1 + ij.2) := pow_pos hρ _
  rw [← div_eq_mul_inv, le_div_iff₀ hρi]
  exact hc ij s

end Laplace.Grammar
