/-
Copyright (c) 2026 Timaeus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Laplace.Grammar.ProductDensityCore

/-!
# Power–log representations and the one-coordinate convolution calculus

Unit 223 (Taylor-tree programme, Stage 1a; Astra #26). The exact state density of a monomial on
the unit box is a finite combination of `τ^{μ-1} (-log τ)^j` (`powLogBasis μ j`). We represent such
combinations concretely as lists of triples `(μ, j, c)` (`PowLogRep`, evaluated by
`PowLogRep.eval`), and prove that peeling one coordinate of weight `t^{w-1}`,
```
(powLogConv w v)(z) = ∫_{[z,1]} t^{w-1} v(z/t) dt,
```
acts on representations by an explicit linear map `PowLogRep.conv w` (`eval_conv`). The kernel
identity is `t^{w-1} (z/t)^{μ-1} (-log(z/t))^j = z^{μ-1} t^{α-1} (log t - log z)^j`,
`α = w - μ + 1`, and the one-dimensional integrals `G_j(z) = ∫_z^1 t^{α-1} (log t - log z)^j dt`
obey `G_0 = (1 - z^α)/α`, `G_{j+1} = (-log z)^{j+1}/α - ((j+1)/α) G_j` for `α ≠ 0` (partial
fractions: the new exponent `w+1` appears **only at logarithmic degree 0**), and
`G_j = (-log z)^{j+1}/(j+1)` for `α = 0` (coincident exponents raise the degree by one). Hence the
two invariants used by the density induction hold term by term: exponents stay in
`P ∪ {w+1}` (`conv_exponent_mem`) and logarithmic degrees stay below the multiplicity, which
increases by one at `w+1` (`conv_degree_lt`). Zero `sorry`/`axiom`.
-/

open MeasureTheory Set Real intervalIntegral

namespace Laplace.Grammar

/-- The basis function `τ^{μ-1} (-log τ)^j`. -/
noncomputable def powLogBasis (μ : ℝ) (j : ℕ) (τ : ℝ) : ℝ := τ ^ (μ - 1) * (-Real.log τ) ^ j

/-- A finite power–log combination: triples `(exponent, log degree, coefficient)`. -/
abbrev PowLogRep := List (ℝ × ℕ × ℝ)

namespace PowLogRep

/-- Evaluation `∑ c · τ^{μ-1} (-log τ)^j`. -/
noncomputable def eval (c : PowLogRep) (τ : ℝ) : ℝ :=
  (c.map fun t => t.2.2 * powLogBasis t.1 t.2.1 τ).sum

@[simp] theorem eval_nil (τ : ℝ) : eval ([] : PowLogRep) τ = 0 := rfl

@[simp] theorem eval_cons (t : ℝ × ℕ × ℝ) (c : PowLogRep) (τ : ℝ) :
    eval (t :: c) τ = t.2.2 * powLogBasis t.1 t.2.1 τ + eval c τ := rfl

theorem eval_append (a b : PowLogRep) (τ : ℝ) : eval (a ++ b) τ = eval a τ + eval b τ := by
  unfold eval
  rw [List.map_append, List.sum_append]

/-- Scalar multiplication of the coefficients. -/
def smul (r : ℝ) (c : PowLogRep) : PowLogRep := c.map fun t => (t.1, t.2.1, r * t.2.2)

theorem eval_smul (r : ℝ) (c : PowLogRep) (τ : ℝ) : eval (smul r c) τ = r * eval c τ := by
  induction c with
  | nil => simp [smul]
  | cons t c ih =>
    simp only [smul, List.map_cons, eval_cons] at ih ⊢
    rw [ih]
    ring

/-- Multiplication by `τ^a`: shifts every exponent by `a` (valid for `τ > 0`). -/
def shift (a : ℝ) (c : PowLogRep) : PowLogRep := c.map fun t => (t.1 + a, t.2.1, t.2.2)

theorem eval_shift (a : ℝ) (c : PowLogRep) {τ : ℝ} (hτ : 0 < τ) :
    eval (shift a c) τ = τ ^ a * eval c τ := by
  induction c with
  | nil => simp [shift]
  | cons t c ih =>
    simp only [shift, List.map_cons, eval_cons] at ih ⊢
    rw [ih]
    unfold powLogBasis
    rw [show t.1 + a - 1 = a + (t.1 - 1) by ring, Real.rpow_add hτ]
    ring

theorem eval_flatMap (c : PowLogRep) (f : ℝ × ℕ × ℝ → PowLogRep) (τ : ℝ) :
    eval (c.flatMap f) τ = (c.map fun t => eval (f t) τ).sum := by
  induction c with
  | nil => simp
  | cons t c ih =>
    rw [List.flatMap_cons, eval_append, ih, List.map_cons, List.sum_cons]

end PowLogRep

/-! ### The one-dimensional integrals `G_j(z) = ∫_z^1 t^{α-1} (log t - log z)^j dt` -/

theorem intervalIntegrable_G (α : ℝ) (j : ℕ) {z : ℝ} (hz : 0 < z) (hz1 : z ≤ 1) :
    IntervalIntegrable (fun t : ℝ => t ^ (α - 1) * (Real.log t - Real.log z) ^ j) volume z 1 := by
  refine ContinuousOn.intervalIntegrable ?_
  rw [uIcc_of_le hz1]
  refine ContinuousOn.mul (continuousOn_id.rpow_const fun t ht => Or.inl (hz.trans_le ht.1).ne') ?_
  exact ((Real.continuousOn_log.mono fun t ht => (hz.trans_le ht.1).ne').sub
    continuousOn_const).pow j

theorem hasDerivAt_G_antideriv (α : ℝ) (j : ℕ) (z : ℝ) {t : ℝ} (ht : 0 < t) :
    HasDerivAt (fun t => t ^ α * (Real.log t - Real.log z) ^ (j + 1))
      (α * t ^ (α - 1) * (Real.log t - Real.log z) ^ (j + 1) +
        ((j : ℝ) + 1) * t ^ (α - 1) * (Real.log t - Real.log z) ^ j) t := by
  have h1 := Real.hasDerivAt_rpow_const (x := t) (p := α) (Or.inl ht.ne')
  have h2 := (((Real.hasDerivAt_log ht.ne').sub_const (Real.log z)).pow (j + 1))
  refine (h1.mul h2).congr_deriv ?_
  simp only [Nat.add_sub_cancel, Pi.pow_apply]
  rw [Real.rpow_sub_one ht.ne']
  push_cast
  ring

/-- `G_0(z) = (1 - z^α)/α` for `α ≠ 0`. -/
theorem integral_G_zero {α : ℝ} (hα : α ≠ 0) {z : ℝ} (hz : 0 < z) (hz1 : z ≤ 1) :
    ∫ t in z..1, t ^ (α - 1) * (Real.log t - Real.log z) ^ 0 = (1 - z ^ α) / α := by
  have hderiv : ∀ t ∈ uIcc z 1, HasDerivAt (fun t => t ^ α / α)
      (t ^ (α - 1) * (Real.log t - Real.log z) ^ 0) t := by
    intro t ht
    rw [uIcc_of_le hz1] at ht
    have ht0 : 0 < t := hz.trans_le ht.1
    have h := (Real.hasDerivAt_rpow_const (x := t) (p := α) (Or.inl ht0.ne')).div_const α
    refine h.congr_deriv ?_
    rw [pow_zero, mul_one]
    field_simp
  rw [integral_eq_sub_of_hasDerivAt hderiv (intervalIntegrable_G α 0 hz hz1), Real.one_rpow]
  ring

/-- `G_{j+1}(z) = (-log z)^{j+1}/α - ((j+1)/α) G_j(z)` for `α ≠ 0`. -/
theorem integral_G_succ {α : ℝ} (hα : α ≠ 0) (j : ℕ) {z : ℝ} (hz : 0 < z) (hz1 : z ≤ 1) :
    ∫ t in z..1, t ^ (α - 1) * (Real.log t - Real.log z) ^ (j + 1) =
      (-Real.log z) ^ (j + 1) / α -
        ((j : ℝ) + 1) / α * ∫ t in z..1, t ^ (α - 1) * (Real.log t - Real.log z) ^ j := by
  have hderiv : ∀ t ∈ uIcc z 1,
      HasDerivAt (fun t => t ^ α * (Real.log t - Real.log z) ^ (j + 1) / α)
      (t ^ (α - 1) * (Real.log t - Real.log z) ^ (j + 1) +
        ((j : ℝ) + 1) / α * (t ^ (α - 1) * (Real.log t - Real.log z) ^ j)) t := by
    intro t ht
    rw [uIcc_of_le hz1] at ht
    have ht0 : 0 < t := hz.trans_le ht.1
    have h := (hasDerivAt_G_antideriv α j z ht0).div_const α
    refine h.congr_deriv ?_
    field_simp
  have hint : IntervalIntegrable (fun t => t ^ (α - 1) * (Real.log t - Real.log z) ^ (j + 1) +
      ((j : ℝ) + 1) / α * (t ^ (α - 1) * (Real.log t - Real.log z) ^ j)) volume z 1 :=
    (intervalIntegrable_G α (j + 1) hz hz1).add ((intervalIntegrable_G α j hz hz1).const_mul _)
  have h := integral_eq_sub_of_hasDerivAt hderiv hint
  rw [integral_add (intervalIntegrable_G α (j + 1) hz hz1)
    ((intervalIntegrable_G α j hz hz1).const_mul _), intervalIntegral.integral_const_mul] at h
  simp only [Real.one_rpow, one_mul, Real.log_one, zero_sub, sub_self,
    zero_pow (Nat.succ_ne_zero j), mul_zero, zero_div, sub_zero] at h
  linarith

/-- `G_j(z) = (-log z)^{j+1}/(j+1)` for `α = 0`. -/
theorem integral_G_zero_exp (j : ℕ) {z : ℝ} (hz : 0 < z) (hz1 : z ≤ 1) :
    ∫ t in z..1, t ^ ((0 : ℝ) - 1) * (Real.log t - Real.log z) ^ j =
      (-Real.log z) ^ (j + 1) / ((j : ℝ) + 1) := by
  rw [← integral_log_sub_pow_div z hz hz1 j]
  refine integral_congr fun t _ => ?_
  rw [zero_sub, Real.rpow_neg_one]
  ring

/-! ### The representation of `G_j` and of the basis convolution -/

/-- Representation of `z ↦ G_j(z)` for `α ≠ 0`: terms `(1, i, ·)` (i.e. `(-log z)^i`) and one term
`(α+1, 0, ·)` (i.e. `z^α`). -/
noncomputable def gRep (α : ℝ) : ℕ → PowLogRep
  | 0 => [(1, 0, 1 / α), (α + 1, 0, -(1 / α))]
  | j + 1 => (1, j + 1, 1 / α) :: PowLogRep.smul (-(((j : ℝ) + 1) / α)) (gRep α j)

theorem eval_gRep {α : ℝ} (hα : α ≠ 0) (j : ℕ) {z : ℝ} (hz : 0 < z) (hz1 : z ≤ 1) :
    PowLogRep.eval (gRep α j) z = ∫ t in z..1, t ^ (α - 1) * (Real.log t - Real.log z) ^ j := by
  induction j with
  | zero =>
    rw [integral_G_zero hα hz hz1]
    simp only [gRep, PowLogRep.eval_cons, PowLogRep.eval_nil, powLogBasis, sub_self, Real.rpow_zero,
      add_sub_cancel_right, pow_zero]
    ring
  | succ j ih =>
    rw [integral_G_succ hα j hz hz1, ← ih]
    simp only [gRep, PowLogRep.eval_cons, PowLogRep.eval_smul, powLogBasis, sub_self,
      Real.rpow_zero]
    ring

theorem gRep_mem {α : ℝ} (j : ℕ) :
    ∀ t ∈ gRep α j, (t.1 = 1 ∧ t.2.1 ≤ j) ∨ (t.1 = α + 1 ∧ t.2.1 = 0) := by
  induction j with
  | zero =>
    intro t ht
    simp only [gRep, List.mem_cons, List.not_mem_nil, or_false] at ht
    rcases ht with rfl | rfl
    · exact Or.inl ⟨rfl, le_rfl⟩
    · exact Or.inr ⟨rfl, rfl⟩
  | succ j ih =>
    intro t ht
    simp only [gRep, List.mem_cons] at ht
    rcases ht with rfl | ht
    · exact Or.inl ⟨rfl, le_rfl⟩
    · simp only [PowLogRep.smul, List.mem_map] at ht
      obtain ⟨s, hs, rfl⟩ := ht
      rcases ih s hs with ⟨h1, h2⟩ | ⟨h1, h2⟩
      · exact Or.inl ⟨h1, h2.trans (Nat.le_succ j)⟩
      · exact Or.inr ⟨h1, h2⟩

/-- Peeling one coordinate with weight `t^{w-1}`:
`(powLogConv w v)(z) = ∫_{[z,1]} t^{w-1} v(z/t) dt`. -/
noncomputable def powLogConv (w : ℝ) (v : ℝ → ℝ) (z : ℝ) : ℝ :=
  ∫ t in Icc z 1, t ^ (w - 1) * v (z / t)

/-- The convolution of one basis term `c · powLogBasis μ j`, as a representation. -/
noncomputable def PowLogRep.basisConv (w : ℝ) (t : ℝ × ℕ × ℝ) : PowLogRep :=
  if t.1 = w + 1 then [(t.1, t.2.1 + 1, t.2.2 / ((t.2.1 : ℝ) + 1))]
  else PowLogRep.smul t.2.2 (PowLogRep.shift (t.1 - 1) (gRep (w - t.1 + 1) t.2.1))

/-- The convolution of a representation. -/
noncomputable def PowLogRep.conv (w : ℝ) (c : PowLogRep) : PowLogRep :=
  c.flatMap (PowLogRep.basisConv w)

/-- Kernel identity: `t^{w-1} (z/t)^{μ-1} (-log(z/t))^j = z^{μ-1} t^{w-μ} (log t - log z)^j`. -/
theorem kernel_eq (w μ : ℝ) (j : ℕ) {z t : ℝ} (hz : 0 < z) (ht : 0 < t) :
    t ^ (w - 1) * powLogBasis μ j (z / t) =
      z ^ (μ - 1) * (t ^ (w - μ + 1 - 1) * (Real.log t - Real.log z) ^ j) := by
  unfold powLogBasis
  rw [Real.div_rpow hz.le ht.le, Real.log_div hz.ne' ht.ne', neg_sub,
    show w - μ + 1 - 1 = (w - 1) - (μ - 1) by ring, Real.rpow_sub ht (w - 1) (μ - 1)]
  generalize t ^ (w - 1) = A
  generalize t ^ (μ - 1) = B
  generalize z ^ (μ - 1) = C
  ring

/-- **Convolution of a basis term.** -/
theorem eval_basisConv (w : ℝ) (t : ℝ × ℕ × ℝ) {z : ℝ} (hz : 0 < z) (hz1 : z ≤ 1) :
    PowLogRep.eval (PowLogRep.basisConv w t) z =
      powLogConv w (fun τ => t.2.2 * powLogBasis t.1 t.2.1 τ) z := by
  obtain ⟨μ, j, c⟩ := t
  have hconv : powLogConv w (fun τ => c * powLogBasis μ j τ) z =
      c * (z ^ (μ - 1) * ∫ s in z..1, s ^ (w - μ + 1 - 1) * (Real.log s - Real.log z) ^ j) := by
    unfold powLogConv
    rw [integral_of_le hz1, ← integral_Icc_eq_integral_Ioc, ← MeasureTheory.integral_const_mul,
      ← MeasureTheory.integral_const_mul]
    refine setIntegral_congr_fun measurableSet_Icc fun s hs => ?_
    have hs0 : 0 < s := hz.trans_le hs.1
    simp only
    rw [show s ^ (w - 1) * (c * powLogBasis μ j (z / s)) =
        c * (s ^ (w - 1) * powLogBasis μ j (z / s)) by ring,
      kernel_eq w μ j hz hs0]
  rw [hconv]
  simp only [PowLogRep.basisConv]
  split_ifs with hμ
  · -- coincident exponent: α = 0
    have hα : w - μ + 1 = 0 := by linarith
    rw [hα, integral_G_zero_exp j hz hz1]
    simp only [PowLogRep.eval_cons, PowLogRep.eval_nil, powLogBasis, add_zero]
    ring
  · have hα : w - μ + 1 ≠ 0 := fun h => hμ (by linarith)
    rw [PowLogRep.eval_smul, PowLogRep.eval_shift _ _ hz, eval_gRep hα j hz hz1]

theorem integrableOn_kernel_basis (w : ℝ) (t : ℝ × ℕ × ℝ) {z : ℝ} (hz : 0 < z) :
    IntegrableOn (fun s => s ^ (w - 1) * (t.2.2 * powLogBasis t.1 t.2.1 (z / s))) (Icc z 1) := by
  refine ContinuousOn.integrableOn_Icc ?_
  refine ContinuousOn.mul (continuousOn_id.rpow_const fun s hs => Or.inl (hz.trans_le hs.1).ne') ?_
  refine continuousOn_const.mul ?_
  unfold powLogBasis
  have hdiv : ContinuousOn (fun s : ℝ => z / s) (Icc z 1) :=
    continuousOn_const.div continuousOn_id fun s hs => (hz.trans_le hs.1).ne'
  have hpos : ∀ s ∈ Icc z 1, z / s ≠ 0 := fun s hs => (div_pos hz (hz.trans_le hs.1)).ne'
  exact (hdiv.rpow_const fun s hs => Or.inl (hpos s hs)).mul
    ((Real.continuousOn_log.comp hdiv fun s hs => hpos s hs).neg.pow _)

theorem integrableOn_kernel_eval (w : ℝ) (c : PowLogRep) {z : ℝ} (hz : 0 < z) :
    IntegrableOn (fun s => s ^ (w - 1) * PowLogRep.eval c (z / s)) (Icc z 1) := by
  induction c with
  | nil => simp only [PowLogRep.eval_nil, mul_zero]; exact integrableOn_zero
  | cons t c ih =>
    have h := (integrableOn_kernel_basis w t hz).add ih
    refine h.congr_fun (fun s _ => ?_) measurableSet_Icc
    simp only [PowLogRep.eval_cons, Pi.add_apply]
    ring

/-- **Convolution of a representation**: `eval (conv w c) = powLogConv w (eval c)` on `(0,1]`. -/
theorem PowLogRep.eval_conv (w : ℝ) (c : PowLogRep) {z : ℝ} (hz : 0 < z) (hz1 : z ≤ 1) :
    PowLogRep.eval (PowLogRep.conv w c) z = powLogConv w (PowLogRep.eval c) z := by
  induction c with
  | nil =>
    simp only [PowLogRep.conv, List.flatMap_nil, PowLogRep.eval_nil, powLogConv, mul_zero,
      integral_zero]
  | cons t c ih =>
    rw [PowLogRep.conv, List.flatMap_cons, PowLogRep.eval_append, ← PowLogRep.conv, ih,
      eval_basisConv w t hz hz1]
    unfold powLogConv
    rw [← MeasureTheory.integral_add (integrableOn_kernel_basis w t hz)
      (integrableOn_kernel_eval w c hz)]
    refine setIntegral_congr_fun measurableSet_Icc fun s _ => ?_
    simp only [PowLogRep.eval_cons]
    ring

/-! ### Exponent and degree invariants -/

/-- Exponents of `basisConv w t` lie in `{t.1, w+1}`. -/
theorem PowLogRep.basisConv_exponent (w : ℝ) (t u : ℝ × ℕ × ℝ) (hu : u ∈ PowLogRep.basisConv w t) :
    u.1 = t.1 ∨ u.1 = w + 1 := by
  unfold PowLogRep.basisConv at hu
  split_ifs at hu with hμ
  · simp only [List.mem_singleton] at hu
    subst hu
    exact Or.inl rfl
  · simp only [PowLogRep.smul, PowLogRep.shift, List.mem_map] at hu
    obtain ⟨s, ⟨a, ha, rfl⟩, rfl⟩ := hu
    rcases gRep_mem _ a ha with ⟨h1, -⟩ | ⟨h1, -⟩
    · left; simp only; rw [h1]; ring
    · right; simp only; rw [h1]; ring

/-- Degrees: with multiplicity function `r` (number of coordinates of exponent `μ`), if every term
`(μ, j, ·)` of `c` has `j < r μ`, then every term of `conv w c` has degree below
`r μ + (if μ = w + 1 then 1 else 0)`. -/
theorem PowLogRep.basisConv_degree (w : ℝ) (r : ℝ → ℕ) (t : ℝ × ℕ × ℝ) (ht : t.2.1 < r t.1)
    (u : ℝ × ℕ × ℝ) (hu : u ∈ PowLogRep.basisConv w t) :
    u.2.1 < r u.1 + (if u.1 = w + 1 then 1 else 0) := by
  unfold PowLogRep.basisConv at hu
  split_ifs at hu with hμ
  · simp only [List.mem_singleton] at hu
    subst hu
    simp only [if_pos hμ]
    omega
  · simp only [PowLogRep.smul, PowLogRep.shift, List.mem_map] at hu
    obtain ⟨s, ⟨a, ha, rfl⟩, rfl⟩ := hu
    rcases gRep_mem _ a ha with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · simp only
      have : a.1 + (t.1 - 1) = t.1 := by rw [h1]; ring
      rw [this]
      split_ifs
      omega
    · simp only
      have : a.1 + (t.1 - 1) = w + 1 := by rw [h1]; ring
      rw [this, if_pos rfl, h2]
      omega

theorem PowLogRep.conv_exponent_mem (w : ℝ) (c : PowLogRep) (P : Set ℝ)
    (hc : ∀ t ∈ c, t.1 ∈ P) : ∀ u ∈ PowLogRep.conv w c, u.1 ∈ insert (w + 1) P := by
  intro u hu
  simp only [PowLogRep.conv, List.mem_flatMap] at hu
  obtain ⟨t, ht, hu⟩ := hu
  rcases PowLogRep.basisConv_exponent w t u hu with h | h
  · exact Or.inr (h ▸ hc t ht)
  · exact Or.inl h

theorem PowLogRep.conv_degree_lt (w : ℝ) (c : PowLogRep) (r : ℝ → ℕ)
    (hc : ∀ t ∈ c, t.2.1 < r t.1) :
    ∀ u ∈ PowLogRep.conv w c, u.2.1 < r u.1 + (if u.1 = w + 1 then 1 else 0) := by
  intro u hu
  simp only [PowLogRep.conv, List.mem_flatMap] at hu
  obtain ⟨t, ht, hu⟩ := hu
  exact PowLogRep.basisConv_degree w r t (hc t ht) u hu

end Laplace.Grammar
