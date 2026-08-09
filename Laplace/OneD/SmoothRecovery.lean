/-
Copyright (c) 2026 Timaeus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib
import Laplace.OneD.TaylorCompare

/-!
# The smooth-loss recovery: Taylor adapter

Stages C4-C5 of the smooth-germ programme, first installment: the
bridge from smoothness to the comparison machinery. Mathlib's
`taylor_isLittleO` is the Peano remainder; here it is converted to
the epsilon-radius jet form the local Taylor comparison consumes
(`taylor_jet_epsilon`), and the admissibility package is shown to
force the first-order facts at the minimum: the derivative vanishes
(`AdmissiblePotential.deriv_zero`) and the second Taylor coefficient
dominates the envelope constant
(`AdmissiblePotential.taylorBase_ge`), so nondegeneracy `λ > 0` is
derived rather than assumed.
-/

open Real MeasureTheory Filter Topology

namespace Laplace.OneD

open Laplace

/-- The quadratic Taylor coefficient (the `λ/2` of the note). -/
noncomputable def taylorBase (L : ℝ → ℝ) : ℝ :=
  iteratedDeriv 2 L 0 / 2

/-- The higher Taylor coefficients in jet indexing: index `i` carries
degree `2 + (i+1)`. -/
noncomputable def taylorCoeff (L : ℝ → ℝ) (D : ℕ) :
    Fin (D - 2) → ℝ :=
  fun i ↦ iteratedDeriv (2 + (i.1 + 1)) L 0 /
    (Nat.factorial (2 + (i.1 + 1)) : ℝ)

/-- **Peano remainder in epsilon-radius form** (from Mathlib's
`taylor_isLittleO`): the jet hypothesis of the local Taylor
comparison, verbatim. -/
theorem taylor_jet_epsilon
    {L : ℝ → ℝ} {D : ℕ} (hL : ContDiff ℝ D L) :
    ∀ ε : ℝ, 0 < ε → ∃ δ' : ℝ, 0 < δ' ∧ ∀ x : ℝ, |x| ≤ δ' →
      |L x - taylorWithinEval L D Set.univ 0 x| ≤ ε * |x| ^ D := by
  intro ε hε
  have h := taylor_isLittleO (convex_univ) (Set.mem_univ (0 : ℝ))
    hL.contDiffOn
  rw [nhdsWithin_univ] at h
  have h2 := (Asymptotics.isLittleO_iff.mp h) hε
  rw [Metric.eventually_nhds_iff] at h2
  obtain ⟨δ₀, hδ₀, hh⟩ := h2
  refine ⟨δ₀ / 2, by positivity, fun x hx ↦ ?_⟩
  have hd : dist x 0 < δ₀ := by
    rw [Real.dist_eq, sub_zero]
    linarith [abs_nonneg x]
  have := hh hd
  rw [Real.norm_eq_abs, Real.norm_eq_abs, sub_zero, abs_pow] at this
  exact this

/-- The derivative of an admissible potential vanishes at the
minimum. -/
theorem AdmissiblePotential.deriv_zero
    {L : ℝ → ℝ} {ρ κ δ : ℝ} (h : AdmissiblePotential L ρ κ δ) :
    deriv L 0 = 0 := by
  have hmin : IsLocalMin L 0 := by
    apply Filter.Eventually.of_forall
    intro x
    have h1 := h.lower x
    rw [h.zero]
    nlinarith [sq_nonneg x, h.rho_pos]
  exact hmin.deriv_eq_zero

/-- The quadratic Taylor coefficient of an admissible potential
dominates the envelope constant; in particular it is positive
(`λ > 0` is derived, not assumed). Uses the degree-2 Peano remainder
against the global lower envelope. -/
theorem AdmissiblePotential.taylorBase_ge
    {L : ℝ → ℝ} {ρ κ δ : ℝ} (h : AdmissiblePotential L ρ κ δ)
    (hL : ContDiff ℝ 2 L) : ρ ≤ taylorBase L := by
  by_contra hlt
  rw [not_le] at hlt
  set ε : ℝ := (ρ - taylorBase L) / 2 with hε_def
  have hε : 0 < ε := by
    rw [hε_def]
    linarith
  obtain ⟨δ', hδ', hjet⟩ := taylor_jet_epsilon hL ε hε
  -- Evaluate at a small positive point.
  set x : ℝ := min δ' (δ / 2) with hx_def
  have hx0 : 0 < x := lt_min hδ' (by linarith [h.delta_pos])
  have hxδ' : |x| ≤ δ' := by
    rw [abs_of_pos hx0]
    exact min_le_left _ _
  have hT : taylorWithinEval L 2 Set.univ 0 x =
      taylorBase L * x ^ 2 := by
    rw [taylor_within_apply]
    have h0 : iteratedDerivWithin 0 L Set.univ 0 = 0 := by
      rw [iteratedDerivWithin_zero]
      exact h.zero
    have h1 : iteratedDerivWithin 1 L Set.univ 0 = 0 := by
      rw [iteratedDerivWithin_one, derivWithin_univ]
      exact h.deriv_zero
    rw [Finset.sum_range_succ, Finset.sum_range_succ,
      Finset.sum_range_one, h0, h1]
    rw [iteratedDerivWithin_univ]
    simp only [smul_eq_mul, sub_zero]
    rw [taylorBase]
    norm_num [Nat.factorial]
    ring
  have hjx := hjet x hxδ'
  rw [hT] at hjx
  have hlow := h.lower x
  rw [abs_of_pos hx0] at hjx
  -- ρ x² ≤ L x ≤ taylorBase·x² + ε·x², contradicting ε = (ρ−base)/2.
  have habs := abs_le.mp hjx
  have hup : L x ≤ taylorBase L * x ^ 2 + ε * x ^ 2 := by
    nlinarith [habs.2]
  have hx2 : 0 < x ^ 2 := by positivity
  nlinarith [hlow, hup]

/-- **The Taylor polynomial in jet shape**: for an admissible `C^D`
potential, the degree-`D` Taylor polynomial at the minimum is exactly
the jet potential with base `taylorBase` and coefficients
`taylorCoeff` (the `k = 0, 1` terms vanish at an admissible
minimum). -/
theorem taylorWithinEval_eq_jet
    {L : ℝ → ℝ} {ρ κ δ : ℝ} {D : ℕ} (hD : 2 ≤ D)
    (h : AdmissiblePotential L ρ κ δ) (x : ℝ) :
    taylorWithinEval L D Set.univ 0 x =
      jetPotential 1 (D - 2) (taylorBase L) 1 (taylorCoeff L D) x := by
  rw [taylor_within_apply]
  simp only [sub_zero, smul_eq_mul, iteratedDerivWithin_univ]
  -- Split off the first three terms.
  have hsplit : (∑ k ∈ Finset.range (D + 1),
      ((Nat.factorial k : ℝ))⁻¹ * x ^ k * iteratedDeriv k L 0) =
      (∑ k ∈ Finset.Ico 0 3,
        ((Nat.factorial k : ℝ))⁻¹ * x ^ k * iteratedDeriv k L 0) +
      ∑ k ∈ Finset.Ico 3 (D + 1),
        ((Nat.factorial k : ℝ))⁻¹ * x ^ k * iteratedDeriv k L 0 := by
    rw [Finset.range_eq_Ico,
      Finset.sum_Ico_consecutive _ (by omega : 0 ≤ 3)
        (by omega : 3 ≤ D + 1)]
  rw [hsplit]
  -- The head: k = 0, 1 vanish; k = 2 is the base term.
  have hhead : (∑ k ∈ Finset.Ico 0 3,
      ((Nat.factorial k : ℝ))⁻¹ * x ^ k * iteratedDeriv k L 0) =
      taylorBase L * x ^ 2 := by
    rw [Finset.sum_Ico_eq_sum_range]
    norm_num [Finset.sum_range_succ, iteratedDeriv_zero, h.zero,
      iteratedDeriv_one, h.deriv_zero, taylorBase, Nat.factorial]
    ring
  rw [hhead]
  -- The tail: reindex to Fin (D - 2).
  have htail : (∑ k ∈ Finset.Ico 3 (D + 1),
      ((Nat.factorial k : ℝ))⁻¹ * x ^ k * iteratedDeriv k L 0) =
      ∑ i : Fin (D - 2), taylorCoeff L D i * 1 ^ (i.1 + 1) *
        x ^ (2 * 1 + (i.1 + 1)) := by
    rw [Finset.sum_Ico_eq_sum_range]
    rw [show D + 1 - 3 = D - 2 by omega]
    rw [← Fin.sum_univ_eq_sum_range (fun i ↦
      ((Nat.factorial (3 + i) : ℝ))⁻¹ * x ^ (3 + i) *
        iteratedDeriv (3 + i) L 0) (D - 2)]
    refine Finset.sum_congr rfl fun i _ ↦ ?_
    rw [taylorCoeff]
    rw [show 2 + (i.1 + 1) = 3 + i.1 by omega]
    rw [one_pow]
    ring
  rw [htail, jetPotential]

/-- Extension of a jet coefficient vector by zeros, with the
stabilizer `d` at the top slot (index `M - 3`, carrying degree
`M`). -/
noncomputable def stabilizedCoeff (R' M : ℕ) (c : Fin R' → ℝ)
    (d : ℝ) : Fin (M - 2) → ℝ :=
  fun i ↦ if h : i.1 < R' then c ⟨i.1, h⟩
    else if i.1 = M - 3 then d else 0

/-- The stabilized jet potential is the original jet plus the top
monomial. -/
theorem stabilized_jet_eq {R' M : ℕ} (hM : R' + 2 < M)
    (a : ℝ) (c : Fin R' → ℝ) (d : ℝ) (x : ℝ) :
    jetPotential 1 (M - 2) a 1 (stabilizedCoeff R' M c d) x =
      jetPotential 1 R' a 1 c x + d * x ^ M := by
  unfold jetPotential
  set g : ℕ → ℝ := fun k ↦
    (if h : k < R' then c ⟨k, h⟩ else if k = M - 3 then d else 0) *
      x ^ (2 * 1 + (k + 1)) with hg_def
  set f : ℕ → ℝ := fun k ↦
    (if h : k < R' then c ⟨k, h⟩ else 0) * x ^ (2 * 1 + (k + 1))
    with hf_def
  have hL : (∑ i : Fin (M - 2), stabilizedCoeff R' M c d i *
      1 ^ (i.1 + 1) * x ^ (2 * 1 + (i.1 + 1))) =
      ∑ k ∈ Finset.range (M - 2), g k := by
    rw [← Fin.sum_univ_eq_sum_range g (M - 2)]
    refine Finset.sum_congr rfl fun i _ ↦ ?_
    simp only [hg_def, stabilizedCoeff, one_pow, mul_one]
  have hR : (∑ i : Fin R', c i * 1 ^ (i.1 + 1) *
      x ^ (2 * 1 + (i.1 + 1))) = ∑ k ∈ Finset.range R', f k := by
    rw [← Fin.sum_univ_eq_sum_range f R']
    refine Finset.sum_congr rfl fun i _ ↦ ?_
    simp only [hf_def, one_pow, mul_one]
    rw [dif_pos i.isLt]
  have hsplit : (∑ k ∈ Finset.range (M - 2), g k) =
      (∑ k ∈ Finset.Ico 0 R', g k) +
        ∑ k ∈ Finset.Ico R' (M - 2), g k := by
    rw [Finset.range_eq_Ico, Finset.sum_Ico_consecutive _
      (by omega : 0 ≤ R') (by omega : R' ≤ M - 2)]
  have hlow : (∑ k ∈ Finset.Ico 0 R', g k) =
      ∑ k ∈ Finset.range R', f k := by
    rw [Finset.range_eq_Ico]
    refine Finset.sum_congr rfl fun k hk ↦ ?_
    have hkR : k < R' := (Finset.mem_Ico.mp hk).2
    rw [hg_def, hf_def]
    simp only [dif_pos hkR]
  have hhigh : (∑ k ∈ Finset.Ico R' (M - 2), g k) = d * x ^ M := by
    have hstep : ∀ k ∈ Finset.Ico R' (M - 2),
        g k = if k = M - 3 then d * x ^ (2 * 1 + (k + 1)) else 0 := by
      intro k hk
      have hkR : ¬ k < R' := by
        have := (Finset.mem_Ico.mp hk).1
        omega
      rw [hg_def]
      simp only [dif_neg hkR]
      by_cases hk3 : k = M - 3
      · simp [hk3]
      · simp [hk3]
    rw [Finset.sum_congr rfl hstep, Finset.sum_ite_eq' _ _ _]
    rw [if_pos (Finset.mem_Ico.mpr ⟨by omega, by omega⟩),
      show 2 * 1 + (M - 3 + 1) = M by omega]
  rw [hL, hR, hsplit, hlow, hhigh]
  ring

/-- The inner-region bound for a jet tail (the stabilizer envelope's
inner case, standalone): below the radius
`ρ = min(1, a/(2(B+1)))` the cubic-and-higher sum is at most half the
quadratic. -/
theorem jet_sum_inner_bound {R' : ℕ} {a : ℝ} (ha : 0 < a)
    (c : Fin R' → ℝ) (x : ℝ)
    (hx : |x| ≤ min 1 (a / (2 * ((∑ i : Fin R', |c i|) + 1)))) :
    |∑ i : Fin R', c i * x ^ (2 + (i.1 + 1))| ≤ a / 2 * x ^ 2 := by
  set B : ℝ := ∑ i : Fin R', |c i| with hB_def
  have hB0 : 0 ≤ B := Finset.sum_nonneg fun i _ ↦ abs_nonneg _
  have hx1 : |x| ≤ 1 := le_trans hx (min_le_left _ _)
  have hxρ : |x| ≤ a / (2 * (B + 1)) :=
    le_trans hx (min_le_right _ _)
  calc |∑ i : Fin R', c i * x ^ (2 + (i.1 + 1))|
      ≤ ∑ i : Fin R', |c i * x ^ (2 + (i.1 + 1))| :=
        Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ i : Fin R', |c i| * (|x| * x ^ 2) := by
        refine Finset.sum_le_sum fun i _ ↦ ?_
        rw [abs_mul, abs_pow]
        apply mul_le_mul_of_nonneg_left _ (abs_nonneg _)
        calc |x| ^ (2 + (i.1 + 1)) ≤ |x| ^ 3 :=
              pow_le_pow_of_le_one (abs_nonneg _) hx1 (by omega)
          _ = |x| * x ^ 2 := by
              rw [pow_succ, sq_abs]
              ring
    _ = B * (|x| * x ^ 2) := by
        rw [hB_def, Finset.sum_mul]
    _ ≤ B * (a / (2 * (B + 1)) * x ^ 2) := by
        apply mul_le_mul_of_nonneg_left _ hB0
        exact mul_le_mul_of_nonneg_right hxρ (sq_nonneg x)
    _ ≤ a / 2 * x ^ 2 := by
        have hcoef : B * (a / (2 * (B + 1))) ≤ a / 2 := by
          rw [← mul_div_assoc,
            div_le_div_iff₀ (by positivity) (by norm_num : (0:ℝ) < 2)]
          nlinarith
        calc B * (a / (2 * (B + 1)) * x ^ 2)
            = B * (a / (2 * (B + 1))) * x ^ 2 := by ring
          _ ≤ a / 2 * x ^ 2 :=
              mul_le_mul_of_nonneg_right hcoef (sq_nonneg x)

/-- **The stabilized Taylor jet is admissible with a positive
profile**: there is `d ≥ 0` making the extension both an
`AdmissiblePotential` (envelope `a/2`, explicit upper constants) and
a `HasPositiveJetProfile` certificate — the two interfaces the
comparison and the recovery theorem respectively consume. -/
theorem stabilized_admissible {R' M : ℕ} (hM_even : Even M)
    (hM : R' + 2 < M) {a : ℝ} (ha : 0 < a) (c : Fin R' → ℝ) :
    ∃ d : ℝ, 0 ≤ d ∧
      AdmissiblePotential
        (fun x ↦ jetPotential 1 (M - 2) a 1
          (stabilizedCoeff R' M c d) x)
        (a / 2) (3 * a / 2 + d)
        (min 1 (a / (2 * ((∑ i : Fin R', |c i|) + 1)))) ∧
      HasPositiveJetProfile (M - 2) a (a / 2)
        (stabilizedCoeff R' M c d) := by
  obtain ⟨d, hd0, henv⟩ := exists_stabilizer_envelope ha c
    hM_even hM
  have henv' : ∀ x : ℝ, a / 2 * x ^ 2 ≤
      jetPotential 1 (M - 2) a 1 (stabilizedCoeff R' M c d) x := by
    intro x
    rw [stabilized_jet_eq hM]
    have h := henv x
    unfold jetPotential
    unfold jetPotential at h
    simp only [one_pow, mul_one] at h ⊢
    calc a / 2 * x ^ 2 ≤ a * x ^ 2 +
          (∑ i : Fin R', c i * x ^ (2 + (i.1 + 1))) + d * x ^ M := h
      _ = a * x ^ (2 * 1) +
          (∑ i : Fin R', c i * x ^ (2 * 1 + (i.1 + 1))) +
          d * x ^ M := by norm_num
  refine ⟨d, hd0, ⟨?_, ?_, henv', ?_, by positivity, by positivity,
    by positivity⟩, ⟨by positivity, ?_⟩⟩
  · exact jetPotential_continuous 1 (M - 2) a 1 _
  · unfold jetPotential
    rw [Finset.sum_eq_zero fun i _ ↦ by
      rw [zero_pow (by omega : 2 * 1 + (i.1 + 1) ≠ 0)]
      ring]
    ring
  · -- The local upper envelope.
    intro x hxδ
    rw [stabilized_jet_eq hM]
    have hx1 : |x| ≤ 1 := le_trans hxδ (min_le_left _ _)
    have hsum := jet_sum_inner_bound ha c x hxδ
    have hxM : d * x ^ M ≤ d * x ^ 2 := by
      apply mul_le_mul_of_nonneg_left _ hd0
      calc x ^ M = |x| ^ M := (hM_even.pow_abs x).symm
        _ ≤ |x| ^ 2 :=
            pow_le_pow_of_le_one (abs_nonneg _) hx1 (by omega)
        _ = x ^ 2 := sq_abs x
    have habs := abs_le.mp hsum
    unfold jetPotential
    simp only [one_pow, mul_one]
    have hexp : ∀ i : Fin R', 2 * 1 + (i.1 + 1) = 2 + (i.1 + 1) :=
      fun i ↦ by omega
    have hsum_eq : (∑ i : Fin R', c i * x ^ (2 * 1 + (i.1 + 1))) =
        ∑ i : Fin R', c i * x ^ (2 + (i.1 + 1)) :=
      Finset.sum_congr rfl fun i _ ↦ by rw [hexp i]
    rw [hsum_eq]
    nlinarith [habs.2]
  · -- The positive jet profile, through the factorization at q = 1.
    intro y
    rcases eq_or_ne y 0 with hy | hy
    · subst hy
      unfold jetProfile
      rw [Finset.sum_eq_zero fun i _ ↦ by
        rw [zero_pow (Nat.succ_ne_zero _)]
        ring]
      linarith
    · have hfac := jetPotential_eq_pow_mul_profile 1 (M - 2) a 1
        (stabilizedCoeff R' M c d) y
      rw [one_mul] at hfac
      have hP := henv' y
      rw [hfac] at hP
      have hyy : y ^ (2 * 1) = y ^ 2 := by norm_num
      rw [hyy] at hP
      have hy2 : (0 : ℝ) < y ^ 2 := by positivity
      by_contra hlt
      rw [not_le] at hlt
      nlinarith [hP, hy2]

/-- The jet difference between an admissible `C^D` loss and its
stabilized Taylor jet, in the epsilon-radius form the comparison
consumes: the Peano remainder supplies order `D`, and the stabilizer
`d·x^M` with `M > D` is absorbed at radius `ε/(2(d+1))`. -/
theorem smooth_stabilized_jet_epsilon
    {L : ℝ → ℝ} {ρ κ δ : ℝ} {D M : ℕ} (hD : 2 ≤ D) (hDM : D < M)
    (h : AdmissiblePotential L ρ κ δ) (hL : ContDiff ℝ D L)
    {d : ℝ} (hd0 : 0 ≤ d) :
    ∀ ε : ℝ, 0 < ε → ∃ δ' : ℝ, 0 < δ' ∧ ∀ x : ℝ, |x| ≤ δ' →
      |L x - jetPotential 1 (M - 2) (taylorBase L) 1
        (stabilizedCoeff (D - 2) M (taylorCoeff L D) d) x| ≤
      ε * |x| ^ D := by
  intro ε hε
  obtain ⟨δ₁, hδ₁, hpeano⟩ := taylor_jet_epsilon hL (ε / 2)
    (by positivity)
  refine ⟨min δ₁ (min 1 (ε / (2 * (d + 1)))), by positivity,
    fun x hx ↦ ?_⟩
  have hx1 : |x| ≤ δ₁ := le_trans hx (min_le_left _ _)
  have hx2 : |x| ≤ 1 :=
    le_trans hx (le_trans (min_le_right _ _) (min_le_left _ _))
  have hx3 : |x| ≤ ε / (2 * (d + 1)) :=
    le_trans hx (le_trans (min_le_right _ _) (min_le_right _ _))
  rw [stabilized_jet_eq (show D - 2 + 2 < M by omega),
    ← taylorWithinEval_eq_jet hD h]
  have hpe := hpeano x hx1
  have hdM : d * |x| ^ M ≤ ε / 2 * |x| ^ D := by
    have hsplit : |x| ^ M = |x| ^ D * |x| ^ (M - D) := by
      rw [← pow_add]
      congr 1
      omega
    have hlast : |x| ^ (M - D) ≤ |x| :=
      calc |x| ^ (M - D) ≤ |x| ^ 1 :=
            pow_le_pow_of_le_one (abs_nonneg _) hx2 (by omega)
        _ = |x| := pow_one _
    calc d * |x| ^ M = d * (|x| ^ D * |x| ^ (M - D)) := by
          rw [hsplit]
      _ ≤ d * (|x| ^ D * |x|) := by
          apply mul_le_mul_of_nonneg_left _ hd0
          exact mul_le_mul_of_nonneg_left hlast (by positivity)
      _ ≤ d * (|x| ^ D * (ε / (2 * (d + 1)))) := by
          apply mul_le_mul_of_nonneg_left _ hd0
          exact mul_le_mul_of_nonneg_left hx3 (by positivity)
      _ ≤ ε / 2 * |x| ^ D := by
          have hcoef : d * (ε / (2 * (d + 1))) ≤ ε / 2 := by
            rw [← mul_div_assoc, div_le_div_iff₀ (by positivity)
              (by norm_num : (0:ℝ) < 2)]
            nlinarith
          calc d * (|x| ^ D * (ε / (2 * (d + 1)))) =
                d * (ε / (2 * (d + 1))) * |x| ^ D := by ring
            _ ≤ ε / 2 * |x| ^ D :=
                mul_le_mul_of_nonneg_right hcoef (by positivity)
  calc |L x - (taylorWithinEval L D Set.univ 0 x + d * x ^ M)|
      = |(L x - taylorWithinEval L D Set.univ 0 x) - d * x ^ M| := by
        congr 1
        ring
    _ ≤ |L x - taylorWithinEval L D Set.univ 0 x| + |d * x ^ M| :=
        abs_sub _ _
    _ ≤ ε / 2 * |x| ^ D + d * |x| ^ M := by
        apply add_le_add hpe
        rw [abs_mul, abs_of_nonneg hd0, abs_pow]
    _ ≤ ε / 2 * |x| ^ D + ε / 2 * |x| ^ D :=
        add_le_add le_rfl hdM
    _ = ε * |x| ^ D := by ring

/-- **Partial stable recovery**: the strong induction of the
weighted-jet programme, truncated at rung `N` — data at rungs below
`N` recovers the base and every coefficient below `N`. (The full jet
of the stabilized polynomial is longer than the data reaches; only
the Taylor part is claimed.) -/
theorem jet_recovery_stable_partial
    {k R' : ℕ} {a₁ a₂ ρc₁ ρc₂ : ℝ} {c₁ c₂ : Fin R' → ℝ} (hk : 1 ≤ k)
    (h1 : HasPositiveJetProfile R' a₁ ρc₁ c₁)
    (h2 : HasPositiveJetProfile R' a₂ ρc₂ c₂)
    (hbase : Tendsto (fun q : ℝ ↦
      normalizedJetMoment k R' 2 a₁ q c₁ -
        normalizedJetMoment k R' 2 a₂ q c₂) (𝓝[>] 0) (𝓝 0))
    {N : ℕ}
    (hdata : ∀ i : Fin R', i.1 < N → Tendsto (fun q : ℝ ↦
      (normalizedJetMoment k R' (2 * k + (i.1 + 1)) a₁ q c₁ -
        normalizedJetMoment k R' (2 * k + (i.1 + 1)) a₂ q c₂) /
        q ^ (i.1 + 1)) (𝓝[>] 0) (𝓝 0)) :
    a₁ = a₂ ∧ ∀ i : Fin R', i.1 < N → c₁ i = c₂ i := by
  have ha := base_recovery_of_tendsto hk h1 h2 hbase
  subst ha
  refine ⟨rfl, ?_⟩
  have key : ∀ n : ℕ, ∀ i : Fin R', i.1 ≤ n → i.1 < N →
      c₁ i = c₂ i := by
    intro n
    induction n using Nat.strong_induction_on with
    | _ n ih =>
      intro i _ hiN
      refine jet_one_rung_recovery hk h1.base_pos i h1 h2 ?_
        (hdata i hiN)
      intro j hj
      have hji : j.1 < i.1 := hj
      rcases Nat.eq_zero_or_pos n with hn | hn
      · omega
      · exact ih j.1 (by omega) j le_rfl (by omega)
  exact fun i hiN ↦ key i.1 i le_rfl hiN

set_option maxHeartbeats 3200000 in
-- The final composition threads five theorem families through one
-- assembly; well past the default heartbeat budget (see CLAUDE.md).
/-- **The finite-order smooth recovery** (germbij Theorem 3.1,
polynomial-to-smooth bridge, stage C5): two admissible `C^(R+2)`
losses whose normalized moments at `x^(2+r)` differ by `o(q^(2+2r))`
for every `r ≤ R` have the same Taylor data through degree `R + 2` —
the base `λ/2` and every higher coefficient. -/
theorem smooth_jet_recovery
    {L₁ L₂ : ℝ → ℝ} {ρ₁ κ₁ δ₁ ρ₂ κ₂ δ₂ : ℝ} {R : ℕ}
    (h1 : AdmissiblePotential L₁ ρ₁ κ₁ δ₁)
    (h2 : AdmissiblePotential L₂ ρ₂ κ₂ δ₂)
    (hs1 : ContDiff ℝ (R + 2) L₁) (hs2 : ContDiff ℝ (R + 2) L₂)
    (hdata : ∀ r : ℕ, r ≤ R → Tendsto (fun q : ℝ ↦
      ((∫ x : ℝ, x ^ (2 + r) * Real.exp (-((q ^ 2)⁻¹ * L₁ x))) /
          (∫ x : ℝ, Real.exp (-((q ^ 2)⁻¹ * L₁ x))) -
        (∫ x : ℝ, x ^ (2 + r) * Real.exp (-((q ^ 2)⁻¹ * L₂ x))) /
          (∫ x : ℝ, Real.exp (-((q ^ 2)⁻¹ * L₂ x)))) /
        q ^ (2 + 2 * r)) (𝓝[>] 0) (𝓝 0)) :
    taylorBase L₁ = taylorBase L₂ ∧
      taylorCoeff L₁ (R + 2) = taylorCoeff L₂ (R + 2) := by
  set D : ℕ := R + 2 with hD_def
  have hD : 2 ≤ D := by omega
  set M : ℕ := 2 * (D / 2 + 1) with hM_def
  have hM_even : Even M := ⟨D / 2 + 1, by rw [hM_def]; ring⟩
  have hDM : D < M := by omega
  have hMR : D - 2 + 2 < M := by omega
  have ha₁pos : 0 < taylorBase L₁ :=
    lt_of_lt_of_le h1.rho_pos (h1.taylorBase_ge
      (hs1.of_le (by exact_mod_cast (by omega : 2 ≤ R + 2))))
  have ha₂pos : 0 < taylorBase L₂ :=
    lt_of_lt_of_le h2.rho_pos (h2.taylorBase_ge
      (hs2.of_le (by exact_mod_cast (by omega : 2 ≤ R + 2))))
  obtain ⟨d₁, hd₁0, hadm₁, hprof₁⟩ := stabilized_admissible
    hM_even hMR ha₁pos (taylorCoeff L₁ D)
  obtain ⟨d₂, hd₂0, hadm₂, hprof₂⟩ := stabilized_admissible
    hM_even hMR ha₂pos (taylorCoeff L₂ D)
  set c₁ := stabilizedCoeff (D - 2) M (taylorCoeff L₁ D) d₁
    with hc₁_def
  set c₂ := stabilizedCoeff (D - 2) M (taylorCoeff L₂ D) d₂
    with hc₂_def
  have hjet₁ := smooth_stabilized_jet_epsilon hD hDM h1 hs1 hd₁0
  have hjet₂ := smooth_stabilized_jet_epsilon hD hDM h2 hs2 hd₂0
  -- C3 quotient comparisons, loss versus stabilized jet.
  have hcomp₁ : ∀ s : ℕ, Tendsto (fun q : ℝ ↦
      ((∫ x : ℝ, x ^ s * Real.exp (-((q ^ 2)⁻¹ * L₁ x))) /
          (∫ x : ℝ, Real.exp (-((q ^ 2)⁻¹ * L₁ x))) -
        (∫ x : ℝ, x ^ s * Real.exp (-((q ^ 2)⁻¹ *
          jetPotential 1 (M - 2) (taylorBase L₁) 1 c₁ x))) /
          (∫ x : ℝ, Real.exp (-((q ^ 2)⁻¹ *
            jetPotential 1 (M - 2) (taylorBase L₁) 1 c₁ x)))) /
        q ^ (s + D - 2)) (𝓝[>] 0) (𝓝 0) :=
    fun s ↦ admissible_normalized_difference_littleO hD h1 hadm₁
      hjet₁ s
  have hcomp₂ : ∀ s : ℕ, Tendsto (fun q : ℝ ↦
      ((∫ x : ℝ, x ^ s * Real.exp (-((q ^ 2)⁻¹ * L₂ x))) /
          (∫ x : ℝ, Real.exp (-((q ^ 2)⁻¹ * L₂ x))) -
        (∫ x : ℝ, x ^ s * Real.exp (-((q ^ 2)⁻¹ *
          jetPotential 1 (M - 2) (taylorBase L₂) 1 c₂ x))) /
          (∫ x : ℝ, Real.exp (-((q ^ 2)⁻¹ *
            jetPotential 1 (M - 2) (taylorBase L₂) 1 c₂ x)))) /
        q ^ (s + D - 2)) (𝓝[>] 0) (𝓝 0) :=
    fun s ↦ admissible_normalized_difference_littleO hD h2 hadm₂
      hjet₂ s
  -- The scaling bridge: x-space normalized moments of the jets are
  -- q^s times the u-space normalized jet moments.
  have hbridge : ∀ (a : ℝ) (c : Fin (M - 2) → ℝ) (ρc : ℝ),
      HasPositiveJetProfile (M - 2) a ρc c →
      ∀ (s : ℕ) (q : ℝ), 0 < q →
      (∫ x : ℝ, x ^ s * Real.exp (-((q ^ 2)⁻¹ *
          jetPotential 1 (M - 2) a 1 c x))) /
        (∫ x : ℝ, Real.exp (-((q ^ 2)⁻¹ *
          jetPotential 1 (M - 2) a 1 c x))) =
      q ^ s * normalizedJetMoment 1 (M - 2) s a q c := by
    intro a c ρc hprof s q hq
    have hqt : ((q ^ 2)⁻¹ : ℝ) * q ^ (2 * 1) = 1 := by
      rw [show (2 * 1 : ℕ) = 2 from rfl]
      exact inv_mul_cancel₀ (by positivity)
    exact normalized_polynomialJet_scale (t := (q ^ 2)⁻¹) s le_rfl
      hprof hq hqt
  -- The jet-level data at every rung r ≤ R, by the three-piece
  -- decomposition.
  have hqpow : ∀ n : ℕ, Tendsto (fun q : ℝ ↦ q ^ n) (𝓝[>] (0 : ℝ))
      (𝓝 ((0 : ℝ) ^ n)) := fun n ↦
    ((continuous_pow n).tendsto 0).mono_left nhdsWithin_le_nhds
  have hjetdata : ∀ r : ℕ, r ≤ R → Tendsto (fun q : ℝ ↦
      (normalizedJetMoment 1 (M - 2) (2 + r) (taylorBase L₁) q c₁ -
        normalizedJetMoment 1 (M - 2) (2 + r) (taylorBase L₂) q c₂) /
        q ^ r) (𝓝[>] 0) (𝓝 0) := by
    intro r hr
    have hlim := (((hcomp₁ (2 + r)).mul (hqpow (D - 2 - r))).neg).add
      ((hdata r hr).add ((hcomp₂ (2 + r)).mul (hqpow (D - 2 - r))))
    rw [show (-(0 * (0 : ℝ) ^ (D - 2 - r)) +
        (0 + 0 * (0 : ℝ) ^ (D - 2 - r))) = 0 by ring] at hlim
    refine hlim.congr' ?_
    filter_upwards [self_mem_nhdsWithin] with q hq
    have hq0 : (0 : ℝ) < q := hq
    rw [hbridge _ _ _ hprof₁ (2 + r) q hq0,
      hbridge _ _ _ hprof₂ (2 + r) q hq0]
    have hpow_split : q ^ (2 + r + D - 2) =
        q ^ (2 + 2 * r) * q ^ (D - 2 - r) := by
      rw [← pow_add]
      congr 1
      omega
    have h2r : (0 : ℝ) < q ^ (2 + 2 * r) := by positivity
    have hDr : (0 : ℝ) < q ^ (D - 2 - r) := by positivity
    have hs2 : (0 : ℝ) < q ^ (2 + r) := by positivity
    have hr0 : (0 : ℝ) < q ^ r := by positivity
    rw [hpow_split]
    field_simp
    ring
  -- Apply the partial recovery.
  have hbase_jet : Tendsto (fun q : ℝ ↦
      normalizedJetMoment 1 (M - 2) 2 (taylorBase L₁) q c₁ -
        normalizedJetMoment 1 (M - 2) 2 (taylorBase L₂) q c₂)
      (𝓝[>] 0) (𝓝 0) := by
    have h := hjetdata 0 (Nat.zero_le R)
    refine h.congr fun q ↦ ?_
    rw [pow_zero, div_one]
  have hrung_jet : ∀ i : Fin (M - 2), i.1 < R → Tendsto (fun q : ℝ ↦
      (normalizedJetMoment 1 (M - 2) (2 * 1 + (i.1 + 1))
          (taylorBase L₁) q c₁ -
        normalizedJetMoment 1 (M - 2) (2 * 1 + (i.1 + 1))
          (taylorBase L₂) q c₂) / q ^ (i.1 + 1)) (𝓝[>] 0) (𝓝 0) := by
    intro i hiR
    have h := hjetdata (i.1 + 1) (by omega)
    refine h.congr fun q ↦ ?_
    rw [show 2 * 1 + (i.1 + 1) = 2 + (i.1 + 1) by omega]
  obtain ⟨ha_eq, hc_eq⟩ := jet_recovery_stable_partial le_rfl
    hprof₁ hprof₂ hbase_jet (N := R) hrung_jet
  refine ⟨ha_eq, ?_⟩
  funext i
  have hiM : i.1 < M - 2 := by omega
  have hiR : i.1 < R := by omega
  have := hc_eq ⟨i.1, hiM⟩ hiR
  rw [hc₁_def, hc₂_def, stabilizedCoeff, stabilizedCoeff] at this
  have hiD : i.1 < D - 2 := by omega
  rw [dif_pos hiD, dif_pos hiD] at this
  convert this using 2

end Laplace.OneD
