/-
Copyright (c) 2026 Timaeus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Laplace.Grammar.BoxBridge

/-!
# The multiplicity-`m` theorem for an arbitrary coordinate order (grammar §4.2)

Relabelling the coordinates of the box by an equivalence `τ : Fin D' ≃ Fin D` leaves the chart
integral invariant when `ξ, η` are transported along the induced measurable equivalence of the box
(`boxIntegralGen_relabel`). Sorting the exponents (`sortPerm`) puts the minimisers last, so the
theorem of unit 80 yields the **hypothesis-light general form**: for any exponents on `Fin D` with
minimal candidate exponent `p` attained `M + 2 ≥ 2` times and jointly continuous `ξ, η` with
`η > 0` on the minimal face,

  `∫_{(0,b]^D} w^H η e^{-βn w^{2K} + β√n w^K ξ} ~ C n^{-p/2} (log n)^{M+1}`,  `C > 0`

(`boxIntegralGen_isEquivalent_general`). Zero `sorry`/`axiom`.
-/

open Real MeasureTheory Set Filter Topology Asymptotics

namespace Laplace.Grammar

/-- Relabelling the coordinates of the box along `τ`. -/
noncomputable def relabel {D D' : ℕ} (τ : Fin D' ≃ Fin D) : (Fin D' → ℝ) ≃ᵐ (Fin D → ℝ) :=
  MeasurableEquiv.piCongrLeft (fun _ : Fin D => ℝ) τ

theorem relabel_apply_apply {D D' : ℕ} (τ : Fin D' ≃ Fin D) (x : Fin D' → ℝ) (i : Fin D') :
    relabel τ x (τ i) = x i := by
  unfold relabel
  exact MeasurableEquiv.piCongrLeft_apply_apply (β := fun _ : Fin D => ℝ) τ x i

theorem relabel_continuous {D D' : ℕ} (τ : Fin D' ≃ Fin D) : Continuous (relabel τ) := by
  refine continuous_pi fun j => ?_
  have : (fun x : Fin D' → ℝ => relabel τ x j) = fun x => x (τ.symm j) := by
    funext x
    conv_lhs => rw [← τ.apply_symm_apply j]
    exact relabel_apply_apply τ x (τ.symm j)
  rw [this]; exact continuous_apply _

/-- **Relabelling invariance** of the chart integral with general `ξ, η`. -/
theorem boxIntegralGen_relabel (β b c : ℝ) {D D' : ℕ} (τ : Fin D' ≃ Fin D) (K H : Fin D → ℕ)
    (ξ η : (Fin D → ℝ) → ℝ) :
    boxIntegralGen β b c (K ∘ τ) (H ∘ τ) (ξ ∘ relabel τ) (η ∘ relabel τ)
      = boxIntegralGen β b c K H ξ η := by
  have hmp := measurePreserving_piCongrLeft
    (fun _ : Fin D => (volume : Measure ℝ).restrict (Ioc 0 b)) τ
  unfold boxIntegralGen boxMeasure
  have key := hmp.integral_comp' (fun w : Fin D → ℝ => (∏ i, w i ^ H i) * η w
    * Real.exp (-β * (c * ∏ i, w i ^ K i) ^ 2 + β * (c * ∏ i, w i ^ K i) * ξ w))
  refine Eq.trans ?_ key
  refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
  have h1 : ∀ g : Fin D → ℕ,
      ∏ i, (MeasurableEquiv.piCongrLeft (fun _ : Fin D => ℝ) τ x) i ^ g i
        = ∏ i, x i ^ g (τ i) := by
    intro g
    refine (Fintype.prod_equiv τ (fun i => x i ^ g (τ i))
      (fun i => (MeasurableEquiv.piCongrLeft (fun _ : Fin D => ℝ) τ x) i ^ g i) fun i => ?_).symm
    rw [MeasurableEquiv.piCongrLeft_apply_apply]
  simp only [Function.comp_apply, relabel]
  rw [h1 H, h1 K]

/-- Positivity of the block coefficient when `η > 0` on the minimal face. -/
theorem blockCoeff_pos (β b p : ℝ) (hβ : 0 < β) (hb : 0 < b) (hp0 : 0 < p) {d₀ d' : ℕ}
    (k : Fin (d₀ + 2) → ℕ) (hk : ∀ j, 0 < k j) (k' h' : Fin d' → ℕ) (hk' : ∀ i, 0 < k' i)
    (hq : ∀ i, p < ((h' i : ℝ) + 1) / k' i) (ξ η : (Fin (d₀ + 2) → ℝ) → (Fin d' → ℝ) → ℝ)
    (hξc : Continuous fun x : (Fin (d₀ + 2) → ℝ) × (Fin d' → ℝ) => ξ x.1 x.2)
    (hηc : Continuous fun x : (Fin (d₀ + 2) → ℝ) × (Fin d' → ℝ) => η x.1 x.2)
    (hηpos : ∀ v : Fin d' → ℝ, (∀ i, 0 < v i ∧ v i ≤ b) → 0 < η 0 v) :
    0 < blockCoeff β b p k k' h' ξ η :=
  integral_blockDivisorDensity_pos β b p hβ hb hp0 (toNatFun k 1) (toNatFun_pos k hk) (d₀ + 1)
    k' h' hk' hq (fun v => ξ 0 v) (fun v => η 0 v)
    (hξc.comp (continuous_const.prodMk continuous_id))
    (hηc.comp (continuous_const.prodMk continuous_id)) hηpos

/-- **The multiplicity theorem for general `ξ, η`, arbitrary coordinate order**: if the minimal
candidate exponent `p` is attained `M + 2` times and `η > 0` on the minimal face
`{wᵢ = 0 for minimisers, wᵢ ∈ (0,b] otherwise}`, then `Z ~ C n^{-p/2} (log n)^{M+1}` with
`C > 0`. -/
theorem boxIntegralGen_isEquivalent_general (β b : ℝ) (hβ : 0 < β) (hb : 0 < b) {D : ℕ}
    (K H : Fin D → ℕ) (hK : ∀ i, 0 < K i) (p : ℝ) (hmin : ∀ i, p ≤ finExp K H i) (M : ℕ)
    (hM : (Finset.univ.filter fun i => finExp K H i = p).card = M + 2)
    (ξ η : (Fin D → ℝ) → ℝ) (hξc : Continuous ξ) (hηc : Continuous η)
    (hηpos : ∀ w : Fin D → ℝ, (∀ i, finExp K H i = p → w i = 0) →
      (∀ i, finExp K H i ≠ p → 0 < w i ∧ w i ≤ b) → 0 < η w) :
    ∃ C : ℝ, 0 < C ∧ (fun n : ℝ => boxIntegralGen β b (Real.sqrt n) K H ξ η) ~[atTop]
      fun n : ℝ => C * (n ^ (-(p / 2)) * Real.log n ^ (M + 1)) := by
  -- sorting
  set σ := sortPerm K H with hσ
  set q : Fin D → ℝ := finExp K H ∘ σ with hq
  have hanti : Antitone q := sortPerm_antitone K H
  set S : Finset (Fin D) := Finset.univ.filter fun j => q j = p with hS
  have hcardS : S.card = M + 2 := by
    rw [← hM]
    refine (Finset.card_equiv σ.symm fun i => ?_).symm
    simp [hS, hq]
  have hSne : S.Nonempty := Finset.card_pos.1 (by omega)
  set i₀ : Fin D := S.min' hSne with hi₀
  have hi₀S : i₀ ∈ S := Finset.min'_mem S hSne
  have hi₀p : q i₀ = p := by simpa [hS] using hi₀S
  have hmin_q : ∀ j, p ≤ q j := fun j => hmin _
  have hge : ∀ j, i₀ ≤ j → q j = p := fun j hj => le_antisymm (hi₀p ▸ hanti hj) (hmin_q j)
  have hlt_p : ∀ j, j < i₀ → p < q j := by
    intro j hj
    refine lt_of_le_of_ne (hmin_q j) fun heq => ?_
    have hjS : j ∈ S := by simp [hS, heq.symm]
    exact absurd (Finset.min'_le S j hjS) (not_le.2 hj)
  have hSIci : S = Finset.Ici i₀ := by
    ext j
    simp only [hS, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_Ici]
    constructor
    · intro hjp
      by_contra hlt
      exact absurd hjp (hlt_p j (not_le.1 hlt)).ne'
    · exact hge j
  have hi₀val : (i₀ : ℕ) = D - (M + 2) := by
    have := hcardS
    rw [hSIci, Fin.card_Ici] at this
    omega
  have hMD : M + 2 ≤ D := by
    have := Finset.card_le_univ S
    rw [hcardS, Fintype.card_fin] at this
    exact this
  set d' : ℕ := D - (M + 2) with hd'
  have hD : d' + (M + 2) = D := by omega
  -- the relabelling
  set τ : Fin (d' + (M + 2)) ≃ Fin D := (finCongr hD).trans σ with hτ
  have hτval : ∀ y : Fin (d' + (M + 2)), finExp K H (τ y) = q (finCongr hD y) := fun y => rfl
  have hcast_val : ∀ y : Fin (d' + (M + 2)), ((finCongr hD y : Fin D) : ℕ) = (y : ℕ) :=
    fun y => rfl
  -- exponents of the relabelled vector
  have hp : ∀ i : Fin (M + 2),
      ((H (τ (Fin.natAdd d' i)) : ℝ) + 1) / K (τ (Fin.natAdd d' i)) = p := by
    intro i
    have : finExp K H (τ (Fin.natAdd d' i)) = p := by
      rw [hτval]
      refine hge _ (Fin.le_def.2 ?_)
      rw [hcast_val, hi₀val]
      simp only [Fin.val_natAdd]
      omega
    simpa [finExp] using this
  have hq' : ∀ j : Fin d', p < ((H (τ (Fin.castAdd (M + 2) j)) : ℝ) + 1)
      / K (τ (Fin.castAdd (M + 2) j)) := by
    intro j
    have : p < finExp K H (τ (Fin.castAdd (M + 2) j)) := by
      rw [hτval]
      refine hlt_p _ (Fin.lt_def.2 ?_)
      rw [hcast_val, hi₀val]
      simp only [Fin.val_castAdd]
      omega
    simpa [finExp] using this
  -- the face condition transports
  have hface : ∀ v : Fin d' → ℝ, (∀ j, 0 < v j ∧ v j ≤ b) →
      0 < (η ∘ relabel τ) (Fin.append v 0) := by
    intro v hv
    refine hηpos _ ?_ ?_
    · intro i hi
      obtain ⟨y, rfl⟩ : ∃ y, τ y = i := ⟨τ.symm i, τ.apply_symm_apply i⟩
      rw [relabel_apply_apply]
      revert hi
      refine Fin.addCases (fun j => ?_) (fun j => ?_) y
      · intro hi
        exfalso
        have := hq' j
        rw [finExp] at hi
        linarith
      · intro _
        rw [Fin.append_right]; rfl
    · intro i hi
      obtain ⟨y, rfl⟩ : ∃ y, τ y = i := ⟨τ.symm i, τ.apply_symm_apply i⟩
      rw [relabel_apply_apply]
      revert hi
      refine Fin.addCases (fun j => ?_) (fun j => ?_) y
      · intro _
        rw [Fin.append_left]; exact hv j
      · intro hi
        exfalso
        have := hp j
        rw [finExp] at hi
        exact hi this
  have hξc' : Continuous (ξ ∘ relabel τ) := hξc.comp (relabel_continuous τ)
  have hηc' : Continuous (η ∘ relabel τ) := hηc.comp (relabel_continuous τ)
  have hE := boxIntegralGen_mult_isEquivalent β b p hβ hb (K ∘ τ) (H ∘ τ) (fun i => hK _)
    hp hq' (ξ ∘ relabel τ) (η ∘ relabel τ) hξc' hηc' hface
  have hp0 : 0 < p := by
    have := hp 0
    rw [← this]
    have := hK (τ (Fin.natAdd d' 0))
    positivity
  refine ⟨_, ?_, hE.congr_left (Filter.Eventually.of_forall fun n => ?_)⟩
  · refine div_pos ?_ (by positivity)
    refine blockCoeff_pos β b p hβ hb hp0 _ (fun j => hK _) _ _ (fun j => hK _) hq' _ _ ?_ ?_ hface
    · exact hξc'.comp ((continuous_append d' (M + 2)).comp (continuous_snd.prodMk continuous_fst))
    · exact hηc'.comp ((continuous_append d' (M + 2)).comp (continuous_snd.prodMk continuous_fst))
  · exact boxIntegralGen_relabel β b (Real.sqrt n) τ K H ξ η

end Laplace.Grammar
