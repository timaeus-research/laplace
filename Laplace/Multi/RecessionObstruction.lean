/-
Copyright (c) 2026 Timaeus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Timaeus
-/
import Laplace.Multi.DominantScale

/-!
# A recession direction obstructs the profile certificate

Astra's review (§1.2): a feasible scale has an integrable profile only if it is an isolated
optimum; a recession direction of the polyhedron along which the objective does not increase makes
the profile non-integrable. The coordinate case: if a scaled coordinate `j` is invisible to the
limiting phase (`κ_j ≤ 0`) while its density does not decay (`r_j ≥ −1`), the unweighted profile of
`ProfileIntegrableOf` is not integrable (`not_integrable_of_coordinate_recession`, and
`not_integrable_envelope_of_recession` for the record's envelope and profile under a strict truth
constraint). The proof integrates over the disjoint shells `u_j ∈ [eⁿ, eⁿ⁺¹)` with the other
coordinates in a fixed box: each shell carries at least a fixed positive mass.
-/

open Real MeasureTheory Set Filter Topology Function
open scoped ENNReal

namespace Laplace.Multi

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The shell `u_j ∈ [eⁿ, eⁿ⁺¹)`, other coordinates in `[a_i, b_i]`. -/
def shell (j : ι) (a b : ι → ℝ) (n : ℕ) : Set (ι → ℝ) :=
  Set.pi univ fun i ↦ if i = j then Ico (exp n) (exp (n + 1)) else Icc (a i) (b i)

omit [Fintype ι] in
theorem measurableSet_shell [Countable ι] (j : ι) (a b : ι → ℝ) (n : ℕ) :
    MeasurableSet (shell j a b n) :=
  MeasurableSet.pi countable_univ fun i _ ↦ by
    split_ifs
    · exact measurableSet_Ico
    · exact measurableSet_Icc

omit [Fintype ι] in
theorem shell_disjoint (j : ι) (a b : ι → ℝ) : Pairwise (Disjoint on shell j a b) := by
  intro n m hnm
  refine Set.disjoint_left.2 fun u hn hm ↦ ?_
  have h1 := Set.mem_univ_pi.mp hn j
  have h2 := Set.mem_univ_pi.mp hm j
  simp only [if_true, mem_Ico] at h1 h2
  rcases lt_or_gt_of_ne hnm with h | h
  · have : (n : ℝ) + 1 ≤ m := by exact_mod_cast h
    linarith [Real.exp_le_exp.mpr this]
  · have : (m : ℝ) + 1 ≤ n := by exact_mod_cast h
    linarith [Real.exp_le_exp.mpr this]

theorem volume_shell (j : ι) (a b : ι → ℝ) (n : ℕ) :
    volume (shell j a b n) = ENNReal.ofReal (exp (n + 1) - exp n) *
      ∏ i ∈ Finset.univ.erase j, ENNReal.ofReal (b i - a i) := by
  unfold shell
  rw [volume_pi, Measure.pi_pi, ← Finset.mul_prod_erase Finset.univ _ (Finset.mem_univ j)]
  simp only [if_true, Real.volume_Ico]
  congr 1
  refine Finset.prod_congr rfl fun i hi ↦ ?_
  rw [if_neg (Finset.ne_of_mem_erase hi), Real.volume_Icc]

/-- A power on an interval `[a, b]` with `0 < a` is bounded below by the smaller endpoint value. -/
theorem rpow_ge_min {a b u e : ℝ} (ha : 0 < a) (hu : u ∈ Icc a b) :
    min (a ^ e) (b ^ e) ≤ u ^ e := by
  rcases le_or_gt 0 e with he | he
  · exact (min_le_left _ _).trans (Real.rpow_le_rpow ha.le hu.1 he)
  · exact (min_le_right _ _).trans (Real.rpow_le_rpow_of_nonpos (ha.trans_le hu.1) hu.2 he.le)

theorem rpow_le_max {a b u e : ℝ} (ha : 0 < a) (hu : u ∈ Icc a b) :
    u ^ e ≤ max (a ^ e) (b ^ e) := by
  rcases le_or_gt 0 e with he | he
  · exact (Real.rpow_le_rpow (ha.trans_le hu.1).le hu.2 he).trans (le_max_right _ _)
  · exact (Real.rpow_le_rpow_of_nonpos ha hu.1 he.le).trans (le_max_left _ _)

omit [DecidableEq ι] in
/-- **Coordinate recession obstruction.** If the `j`-th factor of the domain contains `[1, ∞)`,
the other factors contain boxes, the phase is bounded by `K ∏ u^κ` on the box with `κ_j ≤ 0`, and
`r_j ≥ −1`, then `1_L ∏u^r e^{-Φ}` is not integrable. -/
theorem not_integrable_of_coordinate_recession {L : Set (ι → ℝ)} (j : ι) (I : ι → Set ℝ)
    (hsub : Set.pi univ I ⊆ L) (a b : ι → ℝ)
    (hab : ∀ i, i ≠ j → 0 < a i ∧ a i < b i ∧ Icc (a i) (b i) ⊆ I i) (hIj : Ici (1 : ℝ) ⊆ I j)
    {r κ : ι → ℝ} (hrj : -1 ≤ r j) (hκj : κ j ≤ 0) {Φ : (ι → ℝ) → ℝ} {K : ℝ} (hK : 0 ≤ K)
    (hΦ : ∀ u ∈ Set.pi univ I, Φ u ≤ K * ∏ i, u i ^ κ i) :
    ¬ Integrable (fun u ↦ L.indicator (fun u ↦ ∏ i, u i ^ r i) u * exp (-Φ u)) := by
  classical
  intro hint
  -- positivity of points of a shell
  have hpos : ∀ n, ∀ u ∈ shell j a b n, ∀ i, 0 < u i := fun n u hu i ↦ by
    have h := Set.mem_univ_pi.mp hu i
    by_cases hij : i = j
    · subst hij
      rw [if_pos rfl] at h
      exact (exp_pos _).trans_le h.1
    · rw [if_neg hij] at h
      exact (hab i hij).1.trans_le h.1
  have hother : ∀ n, ∀ u ∈ shell j a b n, ∀ i ∈ Finset.univ.erase j, u i ∈ Icc (a i) (b i) :=
    fun n u hu i hi ↦ by
      have h := Set.mem_univ_pi.mp hu i
      rwa [if_neg (Finset.ne_of_mem_erase hi)] at h
  have hshell_sub : ∀ n, shell j a b n ⊆ Set.pi univ I := fun n u hu ↦
    Set.mem_univ_pi.mpr fun i ↦ by
      have h := Set.mem_univ_pi.mp hu i
      by_cases hij : i = j
      · subst hij
        rw [if_pos rfl] at h
        exact hIj ((Real.one_le_exp (Nat.cast_nonneg _)).trans h.1)
      · rw [if_neg hij] at h
        exact (hab i hij).2.2 h
  -- the constants
  set Cr : ℝ := ∏ i ∈ Finset.univ.erase j, min (a i ^ r i) (b i ^ r i) with hCr
  set Cκ : ℝ := ∏ i ∈ Finset.univ.erase j, max (a i ^ κ i) (b i ^ κ i) with hCκ
  have hCr : 0 < Cr := Finset.prod_pos fun i hi ↦
    lt_min (rpow_pos_of_pos (hab i (Finset.ne_of_mem_erase hi)).1 _)
      (rpow_pos_of_pos ((hab i (Finset.ne_of_mem_erase hi)).1.trans
        (hab i (Finset.ne_of_mem_erase hi)).2.1) _)
  set V : ℝ := ∏ i ∈ Finset.univ.erase j, (b i - a i) with hV
  have hVpos : 0 < V := Finset.prod_pos fun i hi ↦
    sub_pos.mpr (hab i (Finset.ne_of_mem_erase hi)).2.1
  have he1 : 0 < exp 1 - 1 := by linarith [Real.add_one_lt_exp (one_ne_zero : (1 : ℝ) ≠ 0)]
  set C₀ : ℝ := Cr * min 1 (exp (r j)) * exp (-(K * Cκ)) with hC₀
  have hC₀pos : 0 < C₀ := mul_pos (mul_pos hCr (lt_min one_pos (exp_pos _))) (exp_pos _)
  -- the pointwise lower bound on a shell
  have hlow : ∀ n, ∀ u ∈ shell j a b n,
      C₀ * ((exp n) ^ r j) ≤ L.indicator (fun u ↦ ∏ i, u i ^ r i) u * exp (-Φ u) := by
    intro n u hu
    have huI := hshell_sub n hu
    rw [Set.indicator_of_mem (hsub huI)]
    have huj := Set.mem_univ_pi.mp hu j
    rw [if_pos rfl] at huj
    have hujpos : 0 < u j := hpos n u hu j
    have huj1 : 1 ≤ u j := (Real.one_le_exp (Nat.cast_nonneg _)).trans huj.1
    have hr : Cr * ((exp n) ^ r j * min 1 (exp (r j))) ≤ ∏ i, u i ^ r i := by
      rw [← Finset.mul_prod_erase Finset.univ _ (Finset.mem_univ j)]
      have hprod : Cr ≤ ∏ i ∈ Finset.univ.erase j, u i ^ r i :=
        Finset.prod_le_prod (fun i hi ↦ (lt_min (rpow_pos_of_pos (hab i
          (Finset.ne_of_mem_erase hi)).1 _) (rpow_pos_of_pos ((hab i
          (Finset.ne_of_mem_erase hi)).1.trans (hab i (Finset.ne_of_mem_erase hi)).2.1) _)).le)
          fun i hi ↦ rpow_ge_min (hab i (Finset.ne_of_mem_erase hi)).1 (hother n u hu i hi)
      have hj : (exp n) ^ r j * min 1 (exp (r j)) ≤ u j ^ r j := by
        rcases le_or_gt 0 (r j) with hr0 | hr0
        · calc (exp n) ^ r j * min 1 (exp (r j)) ≤ (exp n) ^ r j * 1 :=
                mul_le_mul_of_nonneg_left (min_le_left _ _) (rpow_pos_of_pos (exp_pos _) _).le
            _ = (exp n) ^ r j := mul_one _
            _ ≤ u j ^ r j := Real.rpow_le_rpow (exp_pos _).le huj.1 hr0
        · calc (exp n) ^ r j * min 1 (exp (r j)) ≤ (exp n) ^ r j * exp (r j) :=
                mul_le_mul_of_nonneg_left (min_le_right _ _) (rpow_pos_of_pos (exp_pos _) _).le
            _ = (exp (n + 1)) ^ r j := by
                rw [Real.rpow_def_of_pos (exp_pos _), Real.rpow_def_of_pos (exp_pos _),
                  Real.log_exp, Real.log_exp, ← Real.exp_add]
                congr 1
                ring
            _ ≤ u j ^ r j := Real.rpow_le_rpow_of_nonpos hujpos huj.2.le hr0.le
      calc Cr * ((exp n) ^ r j * min 1 (exp (r j)))
          = ((exp n) ^ r j * min 1 (exp (r j))) * Cr := by ring
        _ ≤ u j ^ r j * ∏ i ∈ Finset.univ.erase j, u i ^ r i :=
            mul_le_mul hj hprod hCr.le (rpow_pos_of_pos hujpos _).le
    have hκ : Φ u ≤ K * Cκ := by
      refine (hΦ u huI).trans (mul_le_mul_of_nonneg_left ?_ hK)
      rw [← Finset.mul_prod_erase Finset.univ _ (Finset.mem_univ j)]
      have hprod : ∏ i ∈ Finset.univ.erase j, u i ^ κ i ≤ Cκ :=
        Finset.prod_le_prod (fun i _ ↦ (rpow_pos_of_pos (hpos n u hu i) _).le)
          fun i hi ↦ rpow_le_max (hab i (Finset.ne_of_mem_erase hi)).1 (hother n u hu i hi)
      have hj : u j ^ κ j ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos huj1 hκj
      calc u j ^ κ j * ∏ i ∈ Finset.univ.erase j, u i ^ κ i ≤ 1 * Cκ :=
            mul_le_mul hj hprod (Finset.prod_nonneg fun i _ ↦
              (rpow_pos_of_pos (hpos n u hu i) _).le) zero_le_one
        _ = Cκ := one_mul _
    have hexp : exp (-(K * Cκ)) ≤ exp (-Φ u) := Real.exp_le_exp.mpr (by linarith)
    calc C₀ * (exp n) ^ r j = Cr * ((exp n) ^ r j * min 1 (exp (r j))) * exp (-(K * Cκ)) := by
          rw [hC₀]; ring
      _ ≤ (∏ i, u i ^ r i) * exp (-Φ u) :=
          mul_le_mul hr hexp (exp_pos _).le
            (Finset.prod_nonneg fun i _ ↦ rpow_nonneg (hpos n u hu i).le _)
  -- each shell carries mass at least `C₀ (e − 1) V`
  have hmass : ∀ n, ENNReal.ofReal (C₀ * ((exp 1 - 1) * V)) ≤
      ∫⁻ u in shell j a b n,
        ENNReal.ofReal (L.indicator (fun u ↦ ∏ i, u i ^ r i) u * exp (-Φ u)) := by
    intro n
    have h1 : ∫⁻ u in shell j a b n, ENNReal.ofReal (C₀ * (exp n) ^ r j) ≤
        ∫⁻ u in shell j a b n,
          ENNReal.ofReal (L.indicator (fun u ↦ ∏ i, u i ^ r i) u * exp (-Φ u)) :=
      lintegral_mono_ae ((ae_restrict_iff' (measurableSet_shell j a b n)).2
        (Eventually.of_forall fun u hu ↦ ENNReal.ofReal_le_ofReal (hlow n u hu)))
    refine le_trans ?_ h1
    rw [setLIntegral_const, volume_shell j a b n]
    have hprodV : ∏ i ∈ Finset.univ.erase j, ENNReal.ofReal (b i - a i) = ENNReal.ofReal V := by
      rw [hV, ENNReal.ofReal_prod_of_nonneg fun i hi ↦
        (sub_pos.mpr (hab i (Finset.ne_of_mem_erase hi)).2.1).le]
    rw [hprodV, ← ENNReal.ofReal_mul (sub_nonneg.mpr (Real.exp_le_exp.mpr (by linarith))),
      ← ENNReal.ofReal_mul (mul_nonneg hC₀pos.le (rpow_pos_of_pos (exp_pos _) _).le)]
    refine ENNReal.ofReal_le_ofReal ?_
    have hn : 1 ≤ exp (n * (r j + 1)) :=
      Real.one_le_exp (mul_nonneg (Nat.cast_nonneg _) (by linarith))
    have hpow : (exp n) ^ r j * (exp (n + 1) - exp n) = exp (n * (r j + 1)) * (exp 1 - 1) := by
      rw [Real.rpow_def_of_pos (exp_pos _), Real.log_exp, Real.exp_add]
      have : exp (n * (r j + 1)) = exp (n * r j) * exp n := by
        rw [← Real.exp_add]; congr 1; ring
      rw [this]
      ring
    calc C₀ * ((exp 1 - 1) * V) = C₀ * 1 * ((exp 1 - 1) * V) := by ring
      _ ≤ C₀ * exp (n * (r j + 1)) * ((exp 1 - 1) * V) := by gcongr
      _ = C₀ * (exp n) ^ r j * ((exp (n + 1) - exp n) * V) := by
          linear_combination (-(C₀ * V)) * hpow
  -- summation over the shells
  have hlt := hint.lintegral_lt_top
  have hge : ∫⁻ u in ⋃ n, shell j a b n,
      ENNReal.ofReal (L.indicator (fun u ↦ ∏ i, u i ^ r i) u * exp (-Φ u)) ≤
      ∫⁻ u, ENNReal.ofReal (L.indicator (fun u ↦ ∏ i, u i ^ r i) u * exp (-Φ u)) :=
    lintegral_mono' Measure.restrict_le_self le_rfl
  rw [lintegral_iUnion (measurableSet_shell j a b) (shell_disjoint j a b)] at hge
  have htop : (∑' n : ℕ, ENNReal.ofReal (C₀ * ((exp 1 - 1) * V))) = ⊤ :=
    ENNReal.tsum_const_eq_top_of_ne_zero
      (ENNReal.ofReal_pos.mpr (mul_pos hC₀pos (mul_pos he1 hVpos))).ne'
  have := (ENNReal.tsum_le_tsum hmass).trans hge
  rw [htop] at this
  exact absurd (top_le_iff.mp this) hlt.ne

omit [DecidableEq ι] in
/-- The obstruction for the record's envelope and profile under a strict truth constraint: a
scaled coordinate invisible to the phase (`κ_j ≤ 0`) with non-decaying density (`r_j ≥ −1`)
defeats `ProfileIntegrableOf`. -/
theorem not_integrable_envelope_of_recession {ρ B D γ q δ : ℝ} {Q κ r α : ι → ℝ}
    {a₀ : (ι → ℝ) → ℝ} {amax c : ℝ} (hρ : 0 < ρ) (hstrict : ∑ i, Q i * α i < γ) (j : ι)
    (hαj : α j ≠ 0) (hκj : κ j ≤ 0) (hrj : -1 ≤ r j) (hB : 0 ≤ B) (hc : 0 ≤ c)
    (ha₀ : ∀ u, |a₀ u| ≤ amax) :
    ¬ Integrable fun u ↦ dsEnvelope ρ D γ q Q r α 1 u *
      exp (-(c * dsProfile ρ B D γ q δ Q κ α a₀ u)) := by
  classical
  have e : (fun u ↦ dsEnvelope ρ D γ q Q r α 1 u * exp (-(c * dsProfile ρ B D γ q δ Q κ α a₀ u))) =
      fun u ↦ (limitDomain ρ D γ q Q α).indicator (fun u ↦ ∏ i, u i ^ r i) u *
        exp (-(c * dsProfile ρ B D γ q δ Q κ α a₀ u)) := by
    funext u
    unfold dsEnvelope
    rw [one_mul]
  rw [e]
  have hL : limitDomain ρ D γ q Q α =
      Set.pi univ fun i ↦ if α i = 0 then Ioo (0 : ℝ) ρ else Ioi 0 := by
    unfold limitDomain
    have : {u : ι → ℝ | ∑ i, Q i * α i = γ → D * ∏ i, u i ^ (-(Q i / q)) < ρ} = univ := by
      ext u; simp [hstrict.ne]
    rw [this, inter_univ]
  refine not_integrable_of_coordinate_recession j (fun i ↦ if α i = 0 then Ioo (0 : ℝ) ρ else Ioi 0)
    hL.symm.subset (fun i ↦ if α i = 0 then ρ / 4 else 1) (fun i ↦ if α i = 0 then ρ / 2 else 2)
    (fun i _ ↦ ?_) ?_ hrj hκj (K := c * B * amax) ?_ ?_
  · by_cases h0 : α i = 0
    · simp only [h0, if_true]
      refine ⟨by positivity, by linarith, fun x hx ↦ ⟨by linarith [hx.1], by linarith [hx.2]⟩⟩
    · simp only [h0, if_false]
      exact ⟨one_pos, by norm_num, fun x hx ↦ show (0 : ℝ) < x by linarith [hx.1]⟩
  · rw [if_neg hαj]
    exact fun x hx ↦ show (0 : ℝ) < x from lt_of_lt_of_le one_pos hx
  · have hamax : 0 ≤ amax := (abs_nonneg _).trans (ha₀ 0)
    positivity
  · intro u hu
    have hu' : u ∈ limitDomain ρ D γ q Q α := hL ▸ hu
    have hpos : 0 ≤ ∏ i, u i ^ κ i := Finset.prod_nonneg fun i _ ↦
      rpow_nonneg (limitDomain_pos hu' i).le _
    unfold dsProfile
    rw [if_pos hu']
    split_ifs
    · calc c * (B * a₀ u * ∏ i, u i ^ κ i) ≤ c * (B * amax * ∏ i, u i ^ κ i) := by
            gcongr
            exact (le_abs_self _).trans (ha₀ u)
        _ = c * B * amax * ∏ i, u i ^ κ i := by ring
    · rw [mul_zero]
      have hamax : 0 ≤ amax := (abs_nonneg _).trans (ha₀ 0)
      exact mul_nonneg (mul_nonneg (mul_nonneg hc hB) hamax) hpos

end Laplace.Multi
