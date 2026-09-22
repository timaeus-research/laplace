/-
Copyright (c) 2026 Timaeus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Timaeus
-/
import Laplace.Multi.AmbientMoments
import Laplace.Multi.OneLoop
import Laplace.Multi.VarianceOrder3
import Laplace.Sampler.FrobeniusBridge

/-!
# The one-loop covariance of the rotated anharmonic oscillator

E2's oscillator is `L ∘ A` with `A(w) = Qᵀ(w − c)`, `QᵀQ = 1`, `L(u) = ∑ᵢ ℓᵢ(uᵢ)`,
`ℓᵢ(x) = λᵢx²/2 + αᵢx³/6 + γᵢx⁴/24`. Its derivative tensors at the minimum `c` are
`H = Q diag(λ) Qᵀ`, `Tᵢⱼₖ = ∑ₗ αₗ Qᵢₗ Qⱼₗ Qₖₗ` (`rotT`) and
`Q4ᵢⱼₖₘ = ∑ₗ γₗ Qᵢₗ Qⱼₗ Qₖₗ Qₘₗ` (`rotQ`).
This file evaluates the seabed's `oneLoopCov` functional on these tensors in closed form
(`oneLoopCov_rot`):

`oneLoopCov t H T Q4 = Q diag(1/(λᵢt) + (αᵢ²/λᵢ⁴ − γᵢ/(2λᵢ³))/t²) Qᵀ`,

through `contractQ = Q diag(γ/(λt)) Qᵀ` and `bubble = tadpoleLine = Q diag(α²/(λt)²) Qᵀ`. The
key step for every contraction is the eigenframe identity `∑ₖₘ Qₖₚ Sₖₘ Qₘ_q = δₚ_q sₚ` for
`S = Q diag(s) Qᵀ` (`contract_conj_diagonal`), which reduces each multi-index sum to a sum over
the eigen-index.

It then states E7 in the note's matrix form (`frobenius_rel_oneLoop_rotatedAnharmonic`): the
exact covariance matrix of the rotated oscillator has relative squared Frobenius error `≤ K/t⁴`
against `oneLoopCov`, while against the Laplace covariance `(tH)⁻¹` alone it is `Θ(1/t²)` when
`a² ≠ ½` (`frobenius_rel_laplace_lower`).
-/

open Matrix MeasureTheory Filter Topology

namespace Laplace.Multi

variable {d : ℕ}

/-- The rotated cubic tensor `Tᵢⱼₖ = ∑ₗ αₗ Qᵢₗ Qⱼₗ Qₖₗ`. -/
noncomputable def rotT (Q : Matrix (Fin d) (Fin d) ℝ) (alpha : Fin d → ℝ) :
    Fin d → Fin d → Fin d → ℝ :=
  fun i j k => ∑ l, alpha l * Q i l * Q j l * Q k l

/-- The rotated quartic tensor `Q4ᵢⱼₖₘ = ∑ₗ γₗ Qᵢₗ Qⱼₗ Qₖₗ Qₘₗ`. -/
noncomputable def rotQ (Q : Matrix (Fin d) (Fin d) ℝ) (gamma : Fin d → ℝ) :
    Fin d → Fin d → Fin d → Fin d → ℝ :=
  fun i j k m => ∑ l, gamma l * Q i l * Q j l * Q k l * Q m l

/-! ### Sum reorderings -/

theorem sum_comm3 {α β γ M : Type*} [Fintype α] [Fintype β] [Fintype γ] [AddCommMonoid M]
    (f : α → β → γ → M) :
    ∑ a, ∑ b, ∑ c, f a b c = ∑ c, ∑ a, ∑ b, f a b c := by
  calc ∑ a, ∑ b, ∑ c, f a b c = ∑ a, ∑ c, ∑ b, f a b c :=
        Finset.sum_congr rfl fun a _ => Finset.sum_comm
    _ = ∑ c, ∑ a, ∑ b, f a b c := Finset.sum_comm

/-! ### Conjugation by `Q` -/

section Conj

variable {Q : Matrix (Fin d) (Fin d) ℝ}

/-- Columns of an orthogonal matrix are orthonormal. -/
theorem col_orthonormal (hQ : Qᵀ * Q = 1) (p q : Fin d) :
    ∑ k, Q k p * Q k q = if p = q then 1 else 0 := by
  have h := congrFun (congrFun hQ p) q
  rw [Matrix.mul_apply, Matrix.one_apply] at h
  simpa only [transpose_apply] using h

/-- `(Q diag(s) Qᵀ)ᵢⱼ = ∑ₚ sₚ Qᵢₚ Qⱼₚ`. -/
theorem conj_diagonal_apply (Q : Matrix (Fin d) (Fin d) ℝ) (s : Fin d → ℝ) (i j : Fin d) :
    (Q * diagonal s * Qᵀ) i j = ∑ p, s p * Q i p * Q j p := by
  rw [Matrix.mul_apply]
  refine Finset.sum_congr rfl fun p _ => ?_
  rw [Matrix.mul_diagonal, transpose_apply]
  ring

theorem conj_mul_conj (hQ : Qᵀ * Q = 1) (M N : Matrix (Fin d) (Fin d) ℝ) :
    (Q * M * Qᵀ) * (Q * N * Qᵀ) = Q * (M * N) * Qᵀ := by
  simp only [Matrix.mul_assoc]
  rw [← Matrix.mul_assoc Qᵀ Q, hQ, Matrix.one_mul]

theorem conj_add (Q : Matrix (Fin d) (Fin d) ℝ) (a b : Fin d → ℝ) :
    Q * diagonal a * Qᵀ + Q * diagonal b * Qᵀ = Q * diagonal (fun i => a i + b i) * Qᵀ := by
  rw [← diagonal_add, Matrix.mul_add, Matrix.add_mul]

theorem conj_sub (Q : Matrix (Fin d) (Fin d) ℝ) (a b : Fin d → ℝ) :
    Q * diagonal a * Qᵀ - Q * diagonal b * Qᵀ = Q * diagonal (fun i => a i - b i) * Qᵀ := by
  rw [← diagonal_sub, Matrix.mul_sub, Matrix.sub_mul]

theorem conj_smul (Q : Matrix (Fin d) (Fin d) ℝ) (c : ℝ) (a : Fin d → ℝ) :
    c • (Q * diagonal a * Qᵀ) = Q * diagonal (fun i => c * a i) * Qᵀ := by
  rw [← Matrix.smul_mul, ← Matrix.mul_smul, ← diagonal_smul]
  rfl

/-- `Qᵀ (Q diag(s) Qᵀ) Q = diag(s)`. -/
theorem transpose_conj_diagonal (hQ : Qᵀ * Q = 1) (s : Fin d → ℝ) :
    Qᵀ * (Q * diagonal s * Qᵀ) * Q = diagonal s := by
  simp only [← Matrix.mul_assoc]
  rw [hQ, Matrix.one_mul, Matrix.mul_assoc, hQ, Matrix.mul_one]

/-- **The eigenframe contraction**: `∑ₖₘ Qₖₚ Sₖₘ Qₘ_q = δₚ_q sₚ` for `S = Q diag(s) Qᵀ`. -/
theorem contract_conj_diagonal (hQ : Qᵀ * Q = 1) (s : Fin d → ℝ) (p q : Fin d) :
    ∑ k, ∑ m, Q k p * (Q * diagonal s * Qᵀ) k m * Q m q = if p = q then s p else 0 := by
  have h := congrFun (congrFun (transpose_conj_diagonal hQ s) p) q
  set S := Q * diagonal s * Qᵀ with hS
  rw [diagonal_apply] at h
  rw [← h, Matrix.mul_apply]
  simp only [Matrix.mul_apply, transpose_apply, Finset.sum_mul]
  exact Finset.sum_comm

/-- `(t • Q diag(λ) Qᵀ)⁻¹ = Q diag(1/(λt)) Qᵀ`. -/
theorem smul_conj_diagonal_inv (hQ : Qᵀ * Q = 1) {lam : Fin d → ℝ} (hlam : ∀ i, lam i ≠ 0)
    {t : ℝ} (ht : t ≠ 0) :
    (t • (Q * diagonal lam * Qᵀ))⁻¹ = Q * diagonal (fun i => 1 / (lam i * t)) * Qᵀ := by
  apply Matrix.inv_eq_right_inv
  have hUU : Q * Qᵀ = 1 := mul_eq_one_comm.mp hQ
  rw [Matrix.smul_mul, conj_mul_conj hQ, diagonal_mul_diagonal, conj_smul]
  have : (fun i => t * (lam i * (1 / (lam i * t)))) = fun _ => (1 : ℝ) := by
    funext i
    have := hlam i
    field_simp
  rw [this, diagonal_one, Matrix.mul_one, hUU]

end Conj

/-! ### The contractions of the rotated tensors -/

section Contractions

variable {Q : Matrix (Fin d) (Fin d) ℝ}

/-- Contracting the last two slots of `rotT` against any array `M`. -/
theorem rotT_contract (Q : Matrix (Fin d) (Fin d) ℝ) (alpha : Fin d → ℝ) (i : Fin d)
    (M : Fin d → Fin d → ℝ) :
    ∑ k, ∑ l, rotT Q alpha i k l * M k l =
      ∑ p, alpha p * Q i p * ∑ k, ∑ l, Q k p * M k l * Q l p := by
  simp only [rotT, Finset.sum_mul, Finset.mul_sum]
  rw [sum_comm3]
  refine Finset.sum_congr rfl fun p _ => Finset.sum_congr rfl fun k _ =>
    Finset.sum_congr rfl fun l _ => ?_
  ring

/-- Contracting the last slot of `rotT` against a vector `w`. -/
theorem rotT_contract1 (Q : Matrix (Fin d) (Fin d) ℝ) (alpha : Fin d → ℝ) (i j : Fin d)
    (w : Fin d → ℝ) :
    ∑ k, rotT Q alpha i j k * w k = ∑ p, alpha p * Q i p * Q j p * ∑ k, Q k p * w k := by
  simp only [rotT, Finset.sum_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun p _ => Finset.sum_congr rfl fun k _ => ?_
  ring

/-- Contracting the last two slots of `rotQ` against any array `M`. -/
theorem rotQ_contract (Q : Matrix (Fin d) (Fin d) ℝ) (gamma : Fin d → ℝ) (i j : Fin d)
    (M : Fin d → Fin d → ℝ) :
    ∑ k, ∑ l, rotQ Q gamma i j k l * M k l =
      ∑ p, gamma p * Q i p * Q j p * ∑ k, ∑ l, Q k p * M k l * Q l p := by
  simp only [rotQ, Finset.sum_mul, Finset.mul_sum]
  rw [sum_comm3]
  refine Finset.sum_congr rfl fun p _ => Finset.sum_congr rfl fun k _ =>
    Finset.sum_congr rfl fun l _ => ?_
  ring

/-- `(Q4:S) = Q diag(γ s) Qᵀ` for `S = Q diag(s) Qᵀ`. -/
theorem contractQ_rot (hQ : Qᵀ * Q = 1) (gamma s : Fin d → ℝ) :
    contractQ (rotQ Q gamma) (Q * diagonal s * Qᵀ) =
      Q * diagonal (fun i => gamma i * s i) * Qᵀ := by
  ext i j
  rw [contractQ, Matrix.of_apply, conj_diagonal_apply]
  have h := rotQ_contract Q gamma i j (fun k l => (Q * diagonal s * Qᵀ) k l)
  rw [h]
  refine Finset.sum_congr rfl fun p _ => ?_
  rw [contract_conj_diagonal hQ s p p, if_pos rfl]
  ring

/-- `(T:S)ₗ = ∑ₚ αₚ sₚ Qₗₚ` for `S = Q diag(s) Qᵀ`. -/
theorem contractT_rot (hQ : Qᵀ * Q = 1) (alpha s : Fin d → ℝ) (l : Fin d) :
    contractT (rotT Q alpha) (Q * diagonal s * Qᵀ) l = ∑ p, alpha p * s p * Q l p := by
  rw [contractT]
  have h := rotT_contract Q alpha l (fun m n => (Q * diagonal s * Qᵀ) m n)
  rw [h]
  refine Finset.sum_congr rfl fun p _ => ?_
  rw [contract_conj_diagonal hQ s p p, if_pos rfl]
  ring

/-- The square of the eigenframe contraction. -/
theorem contract_conj_diagonal_sq (hQ : Qᵀ * Q = 1) (s : Fin d → ℝ) (p q : Fin d) :
    (∑ k, ∑ m, Q k p * (Q * diagonal s * Qᵀ) k m * Q m q) *
        (∑ k, ∑ m, Q k p * (Q * diagonal s * Qᵀ) k m * Q m q) =
      if p = q then s p ^ 2 else 0 := by
  rw [contract_conj_diagonal hQ s p q]
  split_ifs <;> ring

/-- **The cubic bubble** `TSST = Q diag(α² s²) Qᵀ` for `S = Q diag(s) Qᵀ`. -/
theorem bubble_rot (hQ : Qᵀ * Q = 1) (alpha s : Fin d → ℝ) :
    bubble (rotT Q alpha) (Q * diagonal s * Qᵀ) =
      Q * diagonal (fun i => alpha i ^ 2 * s i ^ 2) * Qᵀ := by
  ext i j
  rw [bubble, Matrix.of_apply, conj_diagonal_apply]
  set S := Q * diagonal s * Qᵀ with hS
  set T := rotT Q alpha with hT
  -- pull the inner double sum into a contraction of `T j`
  have h1 : ∀ k l, ∑ m, ∑ n, T i k l * S k m * S l n * T j m n =
      T i k l * ∑ q, alpha q * Q j q * ((∑ m, S k m * Q m q) * (∑ n, S l n * Q n q)) := by
    intro k l
    have e : ∑ m, ∑ n, T i k l * S k m * S l n * T j m n =
        T i k l * ∑ m, ∑ n, T j m n * (S k m * S l n) := by
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun m _ => ?_
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun n _ => ?_
      ring
    rw [e, hT, rotT_contract]
    congr 1
    refine Finset.sum_congr rfl fun q _ => ?_
    rw [Finset.sum_mul_sum]
    congr 1
    refine Finset.sum_congr rfl fun m _ => Finset.sum_congr rfl fun n _ => ?_
    ring
  simp_rw [h1]
  -- pull `∑ q` outside the `k, l` sums and contract `T i`
  have h2 : ∑ k, ∑ l, T i k l * ∑ q, alpha q * Q j q *
      ((∑ m, S k m * Q m q) * (∑ n, S l n * Q n q)) =
      ∑ q, alpha q * Q j q * ∑ k, ∑ l, T i k l * ((∑ m, S k m * Q m q) * (∑ n, S l n * Q n q)) := by
    have e1 : ∀ k l, T i k l * ∑ q, alpha q * Q j q *
        ((∑ m, S k m * Q m q) * (∑ n, S l n * Q n q)) =
        ∑ q, T i k l * (alpha q * Q j q * ((∑ m, S k m * Q m q) * (∑ n, S l n * Q n q))) :=
      fun k l => by rw [Finset.mul_sum]
    have e2 : ∀ q, alpha q * Q j q *
        ∑ k, ∑ l, T i k l * ((∑ m, S k m * Q m q) * (∑ n, S l n * Q n q)) =
        ∑ k, ∑ l, alpha q * Q j q * (T i k l * ((∑ m, S k m * Q m q) * (∑ n, S l n * Q n q))) :=
      fun q => by
        rw [Finset.mul_sum]
        exact Finset.sum_congr rfl fun k _ => by rw [Finset.mul_sum]
    simp_rw [e1, e2]
    rw [sum_comm3]
    refine Finset.sum_congr rfl fun q _ => Finset.sum_congr rfl fun k _ =>
      Finset.sum_congr rfl fun l _ => ?_
    ring
  rw [h2]
  refine Finset.sum_congr rfl fun q _ => ?_
  rw [hT, rotT_contract]
  -- each inner contraction is `X p q ^ 2`
  have h3 : ∀ p, ∑ k, ∑ l, Q k p * ((∑ m, S k m * Q m q) * (∑ n, S l n * Q n q)) * Q l p =
      (∑ k, ∑ m, Q k p * S k m * Q m q) * (∑ l, ∑ n, Q l p * S l n * Q n q) := by
    intro p
    rw [Finset.sum_mul_sum]
    refine Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun l _ => ?_
    rw [Finset.sum_mul_sum, Finset.sum_mul_sum, Finset.mul_sum, Finset.sum_mul]
    refine Finset.sum_congr rfl fun m _ => ?_
    rw [Finset.mul_sum, Finset.sum_mul]
    refine Finset.sum_congr rfl fun n _ => ?_
    ring
  simp_rw [h3, hS, contract_conj_diagonal_sq hQ s]
  simp only [mul_ite, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, if_true]
  ring

/-- **The cubic tadpole on the line** `T·S·(T:S) = Q diag(α² s²) Qᵀ` for `S = Q diag(s) Qᵀ`. -/
theorem tadpoleLine_rot (hQ : Qᵀ * Q = 1) (alpha s : Fin d → ℝ) :
    tadpoleLine (rotT Q alpha) (Q * diagonal s * Qᵀ) =
      Q * diagonal (fun i => alpha i ^ 2 * s i ^ 2) * Qᵀ := by
  ext i j
  rw [tadpoleLine, Matrix.of_apply, conj_diagonal_apply]
  simp_rw [contractT_rot hQ alpha s]
  set S := Q * diagonal s * Qᵀ with hS
  have h1 : ∑ k, ∑ l, rotT Q alpha i j k * S k l * ∑ q, alpha q * s q * Q l q =
      ∑ k, rotT Q alpha i j k * ∑ q, alpha q * s q * ∑ l, S k l * Q l q := by
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [Finset.mul_sum]
    simp only [Finset.mul_sum]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun q _ => Finset.sum_congr rfl fun l _ => ?_
    ring
  rw [h1, rotT_contract1]
  refine Finset.sum_congr rfl fun p _ => ?_
  have h2 : ∑ k, Q k p * ∑ q, alpha q * s q * ∑ l, S k l * Q l q =
      ∑ q, alpha q * s q * ∑ k, ∑ l, Q k p * S k l * Q l q := by
    simp only [Finset.mul_sum]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun q _ => Finset.sum_congr rfl fun k _ =>
      Finset.sum_congr rfl fun l _ => ?_
    ring
  rw [h2]
  simp_rw [hS, contract_conj_diagonal hQ s]
  simp only [mul_ite, mul_zero, Finset.sum_ite_eq, Finset.mem_univ, if_true]
  ring

/-- **`Π` for the rotated tensors**: `Π = Q diag(t²α²s² − (t/2)γs) Qᵀ` for `S = Q diag(s) Qᵀ`. -/
theorem oneLoopPi_rot (hQ : Qᵀ * Q = 1) (t : ℝ) (alpha gamma s : Fin d → ℝ) :
    oneLoopPi t (rotT Q alpha) (rotQ Q gamma) (Q * diagonal s * Qᵀ) =
      Q * diagonal (fun i => t ^ 2 * alpha i ^ 2 * s i ^ 2 - t / 2 * gamma i * s i) * Qᵀ := by
  rw [oneLoopPi, contractQ_rot hQ, bubble_rot hQ, tadpoleLine_rot hQ, conj_smul, conj_smul,
    conj_add, conj_add]
  have : (fun i => -(t / 2) * (gamma i * s i) + t ^ 2 / 2 * (alpha i ^ 2 * s i ^ 2) +
      t ^ 2 / 2 * (alpha i ^ 2 * s i ^ 2)) =
      fun i => t ^ 2 * alpha i ^ 2 * s i ^ 2 - t / 2 * gamma i * s i := by
    funext i
    ring
  rw [this]

/-- **The one-loop covariance of the rotated oscillator, in closed form**:
`oneLoopCov t (Q diag λ Qᵀ) T Q4 = Q diag(1/(λᵢt) + (αᵢ²/λᵢ⁴ − γᵢ/(2λᵢ³))/t²) Qᵀ`. -/
theorem oneLoopCov_rot (hQ : Qᵀ * Q = 1) {lam : Fin d → ℝ} (hlam : ∀ i, lam i ≠ 0)
    (alpha gamma : Fin d → ℝ) {t : ℝ} (ht : t ≠ 0) :
    oneLoopCov t (Q * diagonal lam * Qᵀ) (rotT Q alpha) (rotQ Q gamma) =
      Q * diagonal (fun i => 1 / (lam i * t) +
        (alpha i ^ 2 / lam i ^ 4 - gamma i / (2 * lam i ^ 3)) / t ^ 2) * Qᵀ := by
  rw [oneLoopCov, smul_conj_diagonal_inv hQ hlam ht, oneLoopPi_rot hQ, conj_mul_conj hQ,
    conj_mul_conj hQ, diagonal_mul_diagonal, diagonal_mul_diagonal, conj_add]
  have : (fun i => 1 / (lam i * t) + 1 / (lam i * t) *
      (t ^ 2 * alpha i ^ 2 * (1 / (lam i * t)) ^ 2 - t / 2 * gamma i * (1 / (lam i * t))) *
        (1 / (lam i * t))) =
      fun i => 1 / (lam i * t) + (alpha i ^ 2 / lam i ^ 4 - gamma i / (2 * lam i ^ 3)) / t ^ 2 := by
    funext i
    have := hlam i
    field_simp
  rw [this]

end Contractions

/-! ### E7 in matrix form -/

section E7

variable [NeZero d] {Q : Matrix (Fin d) (Fin d) ℝ} {lam alpha gamma : Fin d → ℝ}

/-- **E7, matrix form**: the exact covariance matrix of the rotated oscillator has relative squared
Frobenius error `≤ K/t⁴` against the seabed's `oneLoopCov` (normalised by the Laplace covariance
`(tH)⁻¹`), i.e. relative Frobenius error `O(t⁻²)`. -/
theorem frobenius_rel_oneLoop_rotatedAnharmonic (hQ : Qᵀ * Q = 1) (c : Fin d → ℝ)
    (hlam : ∀ i, 0 < lam i) (hgamma : ∀ i, 0 < gamma i)
    (hdisc : ∀ i, alpha i ^ 2 < 3 * lam i * gamma i) :
    ∃ K T : ℝ, 0 ≤ K ∧ 1 ≤ T ∧ ∀ {t : ℝ}, T ≤ t →
      (∑ j, ∑ k, (gibbsCov (rotatedAnharmonic Q c lam alpha gamma) t (fun w => w j) (fun w => w k)
          - oneLoopCov t (Q * diagonal lam * Qᵀ) (rotT Q alpha) (rotQ Q gamma) j k) ^ 2) /
        (∑ j, ∑ k, ((t • (Q * diagonal lam * Qᵀ))⁻¹ j k) ^ 2) ≤ K / t ^ 4 := by
  choose K T hK hT h using fun i => var_anharmonic_order2_rate_sharp (hlam i) (hgamma i) (hdisc i)
  have hD : 0 < ∑ i, (1 / lam i) ^ 2 :=
    Finset.sum_pos (fun i _ => by have := hlam i; positivity) Finset.univ_nonempty
  refine ⟨(∑ i, K i ^ 2) / ∑ i, (1 / lam i) ^ 2, 1 + ∑ i, T i, by positivity,
    le_add_of_nonneg_right (Finset.sum_nonneg fun i _ => zero_le_one.trans (hT i)),
    fun {t} ht => ?_⟩
  have hsum : 0 ≤ ∑ i, T i := Finset.sum_nonneg fun i _ => zero_le_one.trans (hT i)
  have hTi : ∀ i, T i ≤ t := fun i => by
    have := Finset.single_le_sum (f := T) (fun j _ => zero_le_one.trans (hT j)) (Finset.mem_univ i)
    linarith
  have htpos : 0 < t := by linarith
  have hlne : ∀ i, lam i ≠ 0 := fun i => (hlam i).ne'
  have htne : t ≠ 0 := htpos.ne'
  set V : Fin d → ℝ := fun i => gibbsCov (separableAnharmonic lam alpha gamma) t (fun u => u i)
    (fun u => u i) with hV
  -- the matrix difference in the eigenframe
  have hcov := gibbsCovMatrix_rotatedAnharmonic hQ c hlam hgamma hdisc htpos
  have hdiff : ∀ j k, gibbsCov (rotatedAnharmonic Q c lam alpha gamma) t (fun w => w j)
      (fun w => w k) - oneLoopCov t (Q * diagonal lam * Qᵀ) (rotT Q alpha) (rotQ Q gamma) j k =
      (Q * diagonal (fun i => V i - (1 / (lam i * t) +
        (alpha i ^ 2 / lam i ^ 4 - gamma i / (2 * lam i ^ 3)) / t ^ 2)) * Qᵀ :
          Matrix (Fin d) (Fin d) ℝ) j k := fun j k => by
    have := congrFun (congrFun hcov j) k
    rw [Matrix.of_apply] at this
    rw [this, oneLoopCov_rot hQ hlne alpha gamma htne, ← Matrix.sub_apply, conj_sub]
  simp_rw [hdiff, smul_conj_diagonal_inv hQ hlne htne]
  have hUU : Qᵀ * Qᵀᵀ = 1 := by rw [transpose_transpose]; exact hQ
  have hc1 := Laplace.Sampler.sum_sq_conj (diagonal (fun i => V i - (1 / (lam i * t) +
    (alpha i ^ 2 / lam i ^ 4 - gamma i / (2 * lam i ^ 3)) / t ^ 2))) Qᵀ hUU
  have hc2 := Laplace.Sampler.sum_sq_conj (diagonal (fun i => 1 / (lam i * t))) Qᵀ hUU
  rw [transpose_transpose] at hc1 hc2
  rw [hc1, hc2, Laplace.Sampler.sum_sq_diagonal, Laplace.Sampler.sum_sq_diagonal]
  -- per-coordinate bounds from the sharp variance rate
  have hVi : ∀ i, |V i - (1 / (lam i * t) +
      (alpha i ^ 2 / lam i ^ 4 - gamma i / (2 * lam i ^ 3)) / t ^ 2)| ≤ K i / t ^ 3 := fun i => by
    have e := h i (hTi i)
    have hVe : V i = _root_.Laplace.gibbsCov
        (OneD.anharmonicPotential (lam i) (alpha i) (gamma i)) t (fun x => x) (fun x => x) := by
      simp only [hV]
      rw [gibbsCov_separableAnharmonic hlam hgamma hdisc htpos i i, if_pos rfl]
    rw [← hVe] at e
    have key : V i - (1 / (lam i * t) + (alpha i ^ 2 / lam i ^ 4 - gamma i / (2 * lam i ^ 3)) /
        t ^ 2) = (t * V i - 1 / lam i - (alpha i ^ 2 / lam i ^ 4 - gamma i / (2 * lam i ^ 3)) / t) /
        t := by
      have := hlne i
      field_simp
      ring
    rw [key, abs_div, abs_of_pos htpos]
    calc |t * V i - 1 / lam i - (alpha i ^ 2 / lam i ^ 4 - gamma i / (2 * lam i ^ 3)) / t| / t
        ≤ K i / t ^ 2 / t := div_le_div_of_nonneg_right e htpos.le
      _ = K i / t ^ 3 := by ring
  have hnum : ∑ i, (V i - (1 / (lam i * t) +
      (alpha i ^ 2 / lam i ^ 4 - gamma i / (2 * lam i ^ 3)) / t ^ 2)) ^ 2 ≤
      (∑ i, K i ^ 2) / t ^ 6 := by
    rw [Finset.sum_div]
    refine Finset.sum_le_sum fun i _ => ?_
    calc (V i - (1 / (lam i * t) + (alpha i ^ 2 / lam i ^ 4 - gamma i / (2 * lam i ^ 3)) /
          t ^ 2)) ^ 2
        = |V i - (1 / (lam i * t) + (alpha i ^ 2 / lam i ^ 4 - gamma i / (2 * lam i ^ 3)) /
          t ^ 2)| ^ 2 := (sq_abs _).symm
      _ ≤ (K i / t ^ 3) ^ 2 := pow_le_pow_left₀ (abs_nonneg _) (hVi i) 2
      _ = K i ^ 2 / t ^ 6 := by ring
  have hden : ∑ i, (1 / (lam i * t)) ^ 2 = (∑ i, (1 / lam i) ^ 2) / t ^ 2 := by
    rw [Finset.sum_div]
    refine Finset.sum_congr rfl fun i _ => ?_
    have := hlne i
    field_simp
  rw [hden, div_div_eq_mul_div]
  calc (∑ i, (V i - (1 / (lam i * t) + (alpha i ^ 2 / lam i ^ 4 - gamma i / (2 * lam i ^ 3)) /
          t ^ 2)) ^ 2) * t ^ 2 / ∑ i, (1 / lam i) ^ 2
      ≤ (∑ i, K i ^ 2) / t ^ 6 * t ^ 2 / ∑ i, (1 / lam i) ^ 2 := by gcongr
    _ = (∑ i, K i ^ 2) / (∑ i, (1 / lam i) ^ 2) / t ^ 4 := by
        field_simp

omit [NeZero d] in
/-- **In the note's parametrisation** (`γᵢ = λᵢ²`, `αᵢ² = a²λᵢ³`) the one-loop correction is a
scalar: `oneLoopCov = (1 + (a² − ½)/t) (tH)⁻¹`. -/
theorem oneLoopCov_rot_note (hQ : Qᵀ * Q = 1) {a : ℝ} (hlam : ∀ i, 0 < lam i)
    (hgamma : ∀ i, gamma i = lam i ^ 2) (halpha : ∀ i, alpha i ^ 2 = a ^ 2 * lam i ^ 3) {t : ℝ}
    (ht : t ≠ 0) :
    oneLoopCov t (Q * diagonal lam * Qᵀ) (rotT Q alpha) (rotQ Q gamma) =
      (1 + (a ^ 2 - 1 / 2) / t) • (t • (Q * diagonal lam * Qᵀ))⁻¹ := by
  have hlne : ∀ i, lam i ≠ 0 := fun i => (hlam i).ne'
  rw [oneLoopCov_rot hQ hlne alpha gamma ht, smul_conj_diagonal_inv hQ hlne ht, conj_smul]
  have : (fun i => 1 / (lam i * t) +
      (alpha i ^ 2 / lam i ^ 4 - gamma i / (2 * lam i ^ 3)) / t ^ 2) =
      fun i => (1 + (a ^ 2 - 1 / 2) / t) * (1 / (lam i * t)) := by
    funext i
    rw [halpha i, hgamma i]
    have := hlne i
    field_simp
  rw [this]

omit [NeZero d] in
/-- At `a² = ½` the one-loop correction vanishes and `oneLoopCov = (tH)⁻¹`: E7's matrix bound then
says the Laplace covariance itself is accurate to relative `O(t⁻²)`. -/
theorem oneLoopCov_rot_half (hQ : Qᵀ * Q = 1) {a : ℝ} (hlam : ∀ i, 0 < lam i)
    (hgamma : ∀ i, gamma i = lam i ^ 2) (halpha : ∀ i, alpha i ^ 2 = a ^ 2 * lam i ^ 3)
    (ha : a ^ 2 = 1 / 2) {t : ℝ} (ht : t ≠ 0) :
    oneLoopCov t (Q * diagonal lam * Qᵀ) (rotT Q alpha) (rotQ Q gamma) =
      (t • (Q * diagonal lam * Qᵀ))⁻¹ := by
  rw [oneLoopCov_rot_note hQ hlam hgamma halpha ht, ha, sub_self, zero_div, add_zero, one_smul]

/-- **The contrast**: when `a² ≠ ½` the Laplace covariance alone has relative squared Frobenius
error at least `(a² − ½)²/(2t²)` eventually, so the one-loop term improves the relative Frobenius
error from `Θ(1/t)` to `O(1/t²)`. -/
theorem frobenius_rel_laplace_lower (hQ : Qᵀ * Q = 1) (c : Fin d → ℝ) {a : ℝ}
    (hlam : ∀ i, 0 < lam i) (hgamma : ∀ i, gamma i = lam i ^ 2)
    (halpha : ∀ i, alpha i ^ 2 = a ^ 2 * lam i ^ 3) (ha : a ^ 2 < 3) (hb : a ^ 2 ≠ 1 / 2) :
    ∃ cst T : ℝ, 0 < cst ∧ ∀ {t : ℝ}, T ≤ t →
      cst / t ^ 2 ≤
        (∑ j, ∑ k, (gibbsCov (rotatedAnharmonic Q c lam alpha gamma) t (fun w => w j) (fun w => w k)
          - (t • (Q * diagonal lam * Qᵀ))⁻¹ j k) ^ 2) /
        ∑ j, ∑ k, ((t • (Q * diagonal lam * Qᵀ))⁻¹ j k) ^ 2 := by
  have hlim := frobenius_rel_laplace_rotatedAnharmonic hQ c hlam hgamma halpha ha
  have hb' : a ^ 2 - 1 / 2 ≠ 0 := sub_ne_zero.mpr hb
  have hpos : 0 < (a ^ 2 - 1 / 2) ^ 2 := by positivity
  obtain ⟨T, hT⟩ := Filter.eventually_atTop.mp (hlim.eventually (lt_mem_nhds (half_lt_self hpos)))
  refine ⟨(a ^ 2 - 1 / 2) ^ 2 / 2, max T 1, by positivity, fun {t} ht => ?_⟩
  have ht1 : 1 ≤ t := le_trans (le_max_right _ _) ht
  have htpos : 0 < t := by linarith
  have h := hT t (le_trans (le_max_left _ _) ht)
  rw [smul_conj_diagonal_inv hQ (fun i => (hlam i).ne') htpos.ne']
  rw [div_le_iff₀ (by positivity)]
  nlinarith [h]

end E7

end Laplace.Multi
