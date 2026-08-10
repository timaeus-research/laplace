/-
Copyright (c) 2026 Timaeus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib
import Laplace.Multi.GaussAbsorb

/-!
# The q-uniform window majorant

Stage 5c-i of the forward-expansion programme: the single theorem the
dominated-convergence step consumes (the architecture consult's "key
hidden dependency"). On the mesoscopic window, eventually in `q`, the
difference between the true rescaled Boltzmann factor and the graded
polynomial approximation carries `q^N` times a fixed
polynomial-Gaussian envelope. The proof factors the true integrand
through the exponent split (whose critical-point hypothesis is now
the bridge theorem), telescopes the scalar difference into the three
5b pieces (perturbation strip, unrestricted exponential Taylor
remainder, graded polynomial tail), extracts the `q`-power from the
multinomial bound `|A| ≤ q·∑|V_s|`, and absorbs every exponential
factor into the weakened Gaussian of 5c-pre.
-/

open Real Filter Topology Asymptotics

namespace Laplace.Multi

variable {d N : ℕ} {L : EuclidD d → ℝ} {H : Matrix (Fin d) (Fin d) ℝ}

/-- Shift a range sum to an `Icc` sum starting at one. -/
theorem sum_range_shift_eq_sum_Icc (f : ℕ → ℝ) (N : ℕ) :
    ∑ s ∈ Finset.range N, f (s + 1) = ∑ s ∈ Finset.Icc 1 N, f s := by
  induction N with
  | zero => simp
  | succ n ih =>
    rw [Finset.sum_range_succ, ih, Finset.sum_Icc_succ_top (by omega)]

namespace ForwardExpansionDomain

/-- **The q-uniform window majorant**: the single interface consumed
by the dominated-convergence step of the numerator expansion. -/
theorem normalized_window_remainder_bound
    (D : ForwardExpansionDomain N L H) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ᶠ q in 𝓝[>] (0 : ℝ), ∀ z ∈ mesoscopicSet d q,
        |Real.exp (-((L (q • z) - L 0) / q ^ 2)) -
          Real.exp (-taylorHomogeneousTerm 2 L z) *
            ∑ j ∈ Finset.range (N + 1),
              correctionCoeffFn L N j z * q ^ j| ≤
        C * (1 + ‖z‖) ^ ((N + 2) * (N + 1)) * q ^ N *
          Real.exp (-(D.lambda / 4) * ‖z‖ ^ 2) := by
  choose Cc hCc0 hCc using abs_correctionCoeffFn_le L N
  set M : ℝ := ∑ s ∈ Finset.Icc 1 N,
    ((s + 2).factorial : ℝ)⁻¹ * ‖iteratedFDeriv ℝ (s + 2) L 0‖
    with hM_def
  have hM0 : 0 ≤ M := Finset.sum_nonneg fun s _ ↦ by positivity
  set Ctail : ℝ := ∑ j ∈ Finset.Ico (N + 1) (N * N + 1), Cc j
    with hCtail_def
  have hCtail0 : 0 ≤ Ctail := Finset.sum_nonneg fun j _ ↦ hCc0 j
  have hrem0 : 0 ≤ D.remConst := by
    unfold ForwardExpansionDomain.remConst
    exact add_nonneg D.taylorRemainderConst_nonneg (by positivity)
  refine ⟨D.remConst + M ^ (N + 1) / ((N + 1).factorial : ℝ) + Ctail,
    add_nonneg (add_nonneg hrem0 (by positivity)) hCtail0, ?_⟩
  filter_upwards [smul_mem_ball_of_mesoscopic D.taylorRadius_pos,
    D.gaussian_absorb,
    Ioo_mem_nhdsGT (by norm_num : (0 : ℝ) < 1)] with q hball habs hq z hz
  obtain ⟨hq0, hq1⟩ := hq
  have hgabs := habs z hz
  set R : ℝ := q ^ N * D.scaledRem q z with hR_def
  set S : ℝ := ∑ s ∈ Finset.Icc 1 N, exponentTerm s L z * q ^ s
    with hS_def
  set G : Polynomial ℝ :=
    gradedExpPoly (fun s ↦ exponentTerm s L z) N with hG_def
  set E : ℝ := Real.exp (-(D.lambda / 4) * ‖z‖ ^ 2) with hE_def
  set K : ℕ := (N + 2) * (N + 1) with hK_def
  have hbase : (1 : ℝ) ≤ 1 + ‖z‖ := by linarith [norm_nonneg z]
  -- factor the true integrand through the exponent split
  have hsplit := D.exponent_split
    D.taylorHomogeneousTerm_one_eq_zero hq0 z
  have hSr : ∑ s ∈ Finset.range N,
      q ^ (s + 1) * exponentTerm (s + 1) L z = S := by
    rw [hS_def, ← sum_range_shift_eq_sum_Icc
      (fun s ↦ exponentTerm s L z * q ^ s) N]
    refine Finset.sum_congr rfl fun s _ ↦ ?_
    ring
  have hfactor : Real.exp (-((L (q • z) - L 0) / q ^ 2)) =
      Real.exp (-taylorHomogeneousTerm 2 L z) *
        Real.exp (-(S + R)) := by
    rw [hsplit, hSr]
    rw [show -(taylorHomogeneousTerm 2 L z + S + R) =
      -taylorHomogeneousTerm 2 L z + -(S + R) from by ring,
      Real.exp_add]
  -- the absolute-correction facts
  have hSabs : |S| ≤ ∑ s ∈ Finset.Icc 1 N,
      q ^ s * |exponentTerm s L z| := by
    rw [hS_def]
    calc |∑ s ∈ Finset.Icc 1 N, exponentTerm s L z * q ^ s|
        ≤ ∑ s ∈ Finset.Icc 1 N, |exponentTerm s L z * q ^ s| :=
          Finset.abs_sum_le_sum_abs _ _
      _ = ∑ s ∈ Finset.Icc 1 N, q ^ s * |exponentTerm s L z| := by
          refine Finset.sum_congr rfl fun s _ ↦ ?_
          rw [abs_mul, abs_of_pos (pow_pos hq0 s)]
          ring
  have habsorb : Real.exp (-taylorHomogeneousTerm 2 L z) *
      Real.exp (|S| + |R|) ≤ E := by
    refine le_trans ?_ hgabs
    refine mul_le_mul_of_nonneg_left ?_ (Real.exp_pos _).le
    exact Real.exp_le_exp.mpr (add_le_add hSabs le_rfl)
  have habsorb_S : Real.exp (-taylorHomogeneousTerm 2 L z) *
      Real.exp |S| ≤ E := by
    refine le_trans ?_ habsorb
    refine mul_le_mul_of_nonneg_left ?_ (Real.exp_pos _).le
    exact Real.exp_le_exp.mpr (le_add_of_nonneg_right (abs_nonneg R))
  -- growth of the exponent data
  have hVgrow : ∑ s ∈ Finset.Icc 1 N, |exponentTerm s L z| ≤
      M * (1 + ‖z‖) ^ (N + 2) := by
    rw [hM_def, Finset.sum_mul]
    refine Finset.sum_le_sum fun s hs ↦ ?_
    have hs2 : s + 2 ≤ N + 2 := by
      have := (Finset.mem_Icc.mp hs).2
      omega
    calc |exponentTerm s L z| ≤ ((s + 2).factorial : ℝ)⁻¹ *
          ‖iteratedFDeriv ℝ (s + 2) L 0‖ * ‖z‖ ^ (s + 2) :=
          abs_taylorHomogeneousTerm_le (s + 2) L z
      _ ≤ ((s + 2).factorial : ℝ)⁻¹ *
          ‖iteratedFDeriv ℝ (s + 2) L 0‖ * (1 + ‖z‖) ^ (N + 2) := by
          refine mul_le_mul_of_nonneg_left ?_ (by positivity)
          calc ‖z‖ ^ (s + 2) ≤ (1 + ‖z‖) ^ (s + 2) := by
                gcongr
                linarith [norm_nonneg z]
            _ ≤ (1 + ‖z‖) ^ (N + 2) :=
                pow_le_pow_right₀ hbase hs2
  -- piece (i): the perturbation strip
  have hqball : q • z ∈ Metric.ball (0 : EuclidD d) D.taylorRadius := by
    rw [Metric.mem_ball, dist_zero_right]
    exact hball z hz
  have hRbound : |R| ≤ q ^ N * (D.remConst * ‖z‖ ^ (N + 2)) := by
    rw [hR_def, abs_mul, abs_of_pos (pow_pos hq0 N)]
    exact mul_le_mul_of_nonneg_left
      (D.abs_scaledRem_le hq0 hqball) (pow_pos hq0 N).le
  have hpiece1 : Real.exp (-taylorHomogeneousTerm 2 L z) *
      |Real.exp (-(S + R)) - Real.exp (-S)| ≤
      D.remConst * (1 + ‖z‖) ^ K * q ^ N * E := by
    have h1 : |Real.exp (-(S + R)) - Real.exp (-S)| ≤
        |R| * Real.exp (|S| + |R|) :=
      abs_exp_neg_add_sub_exp_neg_le S R
    have hzK : ‖z‖ ^ (N + 2) ≤ (1 + ‖z‖) ^ K := by
      calc ‖z‖ ^ (N + 2) ≤ (1 + ‖z‖) ^ (N + 2) := by
            gcongr
            linarith [norm_nonneg z]
        _ ≤ (1 + ‖z‖) ^ K := by
            refine pow_le_pow_right₀ hbase ?_
            rw [hK_def]
            exact Nat.le_mul_of_pos_right (N + 2) (Nat.succ_pos N)
    calc Real.exp (-taylorHomogeneousTerm 2 L z) *
          |Real.exp (-(S + R)) - Real.exp (-S)|
        ≤ Real.exp (-taylorHomogeneousTerm 2 L z) *
          (|R| * Real.exp (|S| + |R|)) :=
          mul_le_mul_of_nonneg_left h1 (Real.exp_pos _).le
      _ = |R| * (Real.exp (-taylorHomogeneousTerm 2 L z) *
          Real.exp (|S| + |R|)) := by ring
      _ ≤ (q ^ N * (D.remConst * ‖z‖ ^ (N + 2))) * E :=
          mul_le_mul hRbound habsorb (by positivity)
            (mul_nonneg (pow_pos hq0 N).le
              (mul_nonneg hrem0 (by positivity)))
      _ ≤ (q ^ N * (D.remConst * (1 + ‖z‖) ^ K)) * E := by
          have hE0 : 0 ≤ E := (Real.exp_pos _).le
          refine mul_le_mul_of_nonneg_right ?_ hE0
          refine mul_le_mul_of_nonneg_left ?_ (pow_pos hq0 N).le
          exact mul_le_mul_of_nonneg_left hzK hrem0
      _ = D.remConst * (1 + ‖z‖) ^ K * q ^ N * E := by ring
  -- piece (ii): the unrestricted exponential Taylor remainder
  have hpiece2 : Real.exp (-taylorHomogeneousTerm 2 L z) *
      |Real.exp (-S) - G.eval q| ≤
      M ^ (N + 1) / ((N + 1).factorial : ℝ) * (1 + ‖z‖) ^ K *
        q ^ N * E := by
    have hgeval : G.eval q =
        ∑ i ∈ Finset.range (N + 1), (-S) ^ i / (i.factorial : ℝ) := by
      rw [hG_def, gradedExpPoly_eval, hS_def]
    have h1 : |Real.exp (-S) - G.eval q| ≤
        |S| ^ (N + 1) * Real.exp |S| / ((N + 1).factorial : ℝ) := by
      rw [hgeval]
      have := abs_exp_sub_sum_le N (-S)
      rwa [abs_neg] at this
    have hSN : |S| ^ (N + 1) ≤
        M ^ (N + 1) * (1 + ‖z‖) ^ K * q ^ N := by
      have hSMq : |S| ≤ M * (1 + ‖z‖) ^ (N + 2) * q := by
        have hSq : |S| ≤
            (∑ s ∈ Finset.Icc 1 N, |exponentTerm s L z|) * q := by
          rw [hS_def]
          exact abs_exponent_sum_le _ N hq0.le hq1.le
        calc |S| ≤ (∑ s ∈ Finset.Icc 1 N, |exponentTerm s L z|) * q :=
              hSq
          _ ≤ M * (1 + ‖z‖) ^ (N + 2) * q :=
              mul_le_mul_of_nonneg_right hVgrow hq0.le
      calc |S| ^ (N + 1) ≤ (M * (1 + ‖z‖) ^ (N + 2) * q) ^ (N + 1) := by
            gcongr
        _ = M ^ (N + 1) * ((1 + ‖z‖) ^ (N + 2)) ^ (N + 1) *
            q ^ (N + 1) := by
            rw [mul_pow, mul_pow]
        _ = M ^ (N + 1) * (1 + ‖z‖) ^ K * q ^ (N + 1) := by
            rw [← pow_mul, hK_def]
        _ ≤ M ^ (N + 1) * (1 + ‖z‖) ^ K * q ^ N := by
            refine mul_le_mul_of_nonneg_left ?_ (by positivity)
            exact pow_le_pow_of_le_one hq0.le hq1.le (by omega)
    calc Real.exp (-taylorHomogeneousTerm 2 L z) *
          |Real.exp (-S) - G.eval q|
        ≤ Real.exp (-taylorHomogeneousTerm 2 L z) *
          (|S| ^ (N + 1) * Real.exp |S| / ((N + 1).factorial : ℝ)) :=
          mul_le_mul_of_nonneg_left h1 (Real.exp_pos _).le
      _ = |S| ^ (N + 1) / ((N + 1).factorial : ℝ) *
          (Real.exp (-taylorHomogeneousTerm 2 L z) *
            Real.exp |S|) := by ring
      _ ≤ M ^ (N + 1) * (1 + ‖z‖) ^ K * q ^ N /
            ((N + 1).factorial : ℝ) * E := by
          refine mul_le_mul ?_ habsorb_S (by positivity) (by positivity)
          rw [div_eq_mul_inv, div_eq_mul_inv]
          exact mul_le_mul_of_nonneg_right hSN (by positivity)
      _ = M ^ (N + 1) / ((N + 1).factorial : ℝ) * (1 + ‖z‖) ^ K *
          q ^ N * E := by ring
  -- piece (iii): the graded polynomial tail
  have hpiece3 : Real.exp (-taylorHomogeneousTerm 2 L z) *
      |G.eval q - ∑ j ∈ Finset.range (N + 1),
        correctionCoeffFn L N j z * q ^ j| ≤
      Ctail * (1 + ‖z‖) ^ K * q ^ N * E := by
    have htail : |G.eval q - ∑ j ∈ Finset.range (N + 1),
        correctionCoeffFn L N j z * q ^ j| ≤
        q ^ (N + 1) * ∑ j ∈ Finset.Ico (N + 1) (N * N + 1),
          |correctionCoeffFn L N j z| :=
      gradedExpPoly_tail_bound (fun s ↦ exponentTerm s L z) N
        hq0.le hq1.le
    have hsum : ∑ j ∈ Finset.Ico (N + 1) (N * N + 1),
        |correctionCoeffFn L N j z| ≤
        Ctail * (1 + ‖z‖) ^ K := by
      rw [hCtail_def, Finset.sum_mul]
      refine Finset.sum_le_sum fun j hj ↦ ?_
      have hj2 : j + 2 * N ≤ K := by
        have hjm : j < N * N + 1 := (Finset.mem_Ico.mp hj).2
        rw [hK_def]
        nlinarith
      calc |correctionCoeffFn L N j z|
          ≤ Cc j * (1 + ‖z‖) ^ (j + 2 * N) := hCc j z
        _ ≤ Cc j * (1 + ‖z‖) ^ K := by
            refine mul_le_mul_of_nonneg_left ?_ (hCc0 j)
            exact pow_le_pow_right₀ hbase hj2
    have hgauss : Real.exp (-taylorHomogeneousTerm 2 L z) ≤ E := by
      rw [hE_def]
      apply Real.exp_le_exp.mpr
      have h1 := D.t2_lower z
      nlinarith [mul_nonneg D.lambda_pos.le (sq_nonneg ‖z‖)]
    have hq1' : q ^ (N + 1) ≤ q ^ N :=
      pow_le_pow_of_le_one hq0.le hq1.le (by omega)
    calc Real.exp (-taylorHomogeneousTerm 2 L z) *
          |G.eval q - ∑ j ∈ Finset.range (N + 1),
            correctionCoeffFn L N j z * q ^ j|
        ≤ Real.exp (-taylorHomogeneousTerm 2 L z) *
          (q ^ (N + 1) * ∑ j ∈ Finset.Ico (N + 1) (N * N + 1),
            |correctionCoeffFn L N j z|) :=
          mul_le_mul_of_nonneg_left htail (Real.exp_pos _).le
      _ = q ^ (N + 1) *
          (∑ j ∈ Finset.Ico (N + 1) (N * N + 1),
            |correctionCoeffFn L N j z|) *
          Real.exp (-taylorHomogeneousTerm 2 L z) := by ring
      _ ≤ q ^ N * (Ctail * (1 + ‖z‖) ^ K) * E := by
          refine mul_le_mul (mul_le_mul hq1' hsum
            (Finset.sum_nonneg fun j _ ↦ abs_nonneg _)
            (pow_nonneg hq0.le N)) hgauss (Real.exp_pos _).le
            (by positivity)
      _ = Ctail * (1 + ‖z‖) ^ K * q ^ N * E := by ring
  -- assemble the telescope
  rw [hfactor, show Real.exp (-taylorHomogeneousTerm 2 L z) *
      Real.exp (-(S + R)) -
      Real.exp (-taylorHomogeneousTerm 2 L z) *
        ∑ j ∈ Finset.range (N + 1),
          correctionCoeffFn L N j z * q ^ j =
      Real.exp (-taylorHomogeneousTerm 2 L z) *
        (Real.exp (-(S + R)) -
          ∑ j ∈ Finset.range (N + 1),
            correctionCoeffFn L N j z * q ^ j) from by ring,
    abs_mul, abs_of_pos (Real.exp_pos _)]
  have htel : |Real.exp (-(S + R)) -
      ∑ j ∈ Finset.range (N + 1), correctionCoeffFn L N j z * q ^ j| ≤
      |Real.exp (-(S + R)) - Real.exp (-S)| +
        |Real.exp (-S) - G.eval q| +
        |G.eval q - ∑ j ∈ Finset.range (N + 1),
          correctionCoeffFn L N j z * q ^ j| := by
    calc |Real.exp (-(S + R)) -
          ∑ j ∈ Finset.range (N + 1),
            correctionCoeffFn L N j z * q ^ j|
        ≤ |Real.exp (-(S + R)) - G.eval q| +
          |G.eval q - ∑ j ∈ Finset.range (N + 1),
            correctionCoeffFn L N j z * q ^ j| := abs_sub_le _ _ _
      _ ≤ (|Real.exp (-(S + R)) - Real.exp (-S)| +
          |Real.exp (-S) - G.eval q|) +
          |G.eval q - ∑ j ∈ Finset.range (N + 1),
            correctionCoeffFn L N j z * q ^ j| :=
          add_le_add (abs_sub_le _ _ _) le_rfl
  calc Real.exp (-taylorHomogeneousTerm 2 L z) *
        |Real.exp (-(S + R)) -
          ∑ j ∈ Finset.range (N + 1),
            correctionCoeffFn L N j z * q ^ j|
      ≤ Real.exp (-taylorHomogeneousTerm 2 L z) *
        (|Real.exp (-(S + R)) - Real.exp (-S)| +
          |Real.exp (-S) - G.eval q| +
          |G.eval q - ∑ j ∈ Finset.range (N + 1),
            correctionCoeffFn L N j z * q ^ j|) :=
        mul_le_mul_of_nonneg_left htel (Real.exp_pos _).le
    _ = Real.exp (-taylorHomogeneousTerm 2 L z) *
          |Real.exp (-(S + R)) - Real.exp (-S)| +
        Real.exp (-taylorHomogeneousTerm 2 L z) *
          |Real.exp (-S) - G.eval q| +
        Real.exp (-taylorHomogeneousTerm 2 L z) *
          |G.eval q - ∑ j ∈ Finset.range (N + 1),
            correctionCoeffFn L N j z * q ^ j| := by ring
    _ ≤ D.remConst * (1 + ‖z‖) ^ K * q ^ N * E +
        M ^ (N + 1) / ((N + 1).factorial : ℝ) * (1 + ‖z‖) ^ K *
          q ^ N * E +
        Ctail * (1 + ‖z‖) ^ K * q ^ N * E :=
        add_le_add (add_le_add hpiece1 hpiece2) hpiece3
    _ = (D.remConst + M ^ (N + 1) / ((N + 1).factorial : ℝ) + Ctail) *
        (1 + ‖z‖) ^ K * q ^ N * E := by ring

end ForwardExpansionDomain

end Laplace.Multi
