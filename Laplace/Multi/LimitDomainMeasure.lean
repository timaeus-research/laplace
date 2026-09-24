/-
Copyright (c) 2026 Timaeus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Timaeus
-/
import Laplace.Multi.DominantScale

/-!
# The limiting domain is open, and has positive measure when nonempty

Companion to `termConst_pos`: the limiting domain of the rescaling is open (inside the positive
orthant the cutoff function is continuous), so it has positive Lebesgue measure as soon as it is
nonempty (`volume_limitDomain_pos`); when the truth constraint is strict it is a product of
intervals and nonempty (`limitDomain_nonempty_of_strict`).
-/

open Real MeasureTheory Set Filter Topology

namespace Laplace.Multi

variable {ι : Type*} [Fintype ι] {ρ D γ q : ℝ} {Q α : ι → ℝ}

omit [Fintype ι] in
theorem isOpen_pi_scaled [Finite ι] :
    IsOpen (Set.pi univ fun j : ι ↦ if α j = 0 then Ioo (0 : ℝ) ρ else Ioi 0) :=
  isOpen_set_pi finite_univ fun j _ ↦ by
    split_ifs
    · exact isOpen_Ioo
    · exact isOpen_Ioi

omit [Fintype ι] in
theorem pi_scaled_subset_posOrthant :
    (Set.pi univ fun j : ι ↦ if α j = 0 then Ioo (0 : ℝ) ρ else Ioi 0) ⊆
      Set.pi univ fun _ : ι ↦ Ioi (0 : ℝ) := fun u hu ↦ Set.mem_univ_pi.mpr fun j ↦ by
  have h := Set.mem_univ_pi.mp hu j
  split_ifs at h with h0
  · exact h.1
  · exact h

theorem continuousOn_cut :
    ContinuousOn (fun u : ι → ℝ ↦ D * ∏ j, u j ^ (-(Q j / q)))
      (Set.pi univ fun _ : ι ↦ Ioi (0 : ℝ)) :=
  continuousOn_const.mul (continuousOn_finsetProd _ fun j _ ↦
    (continuous_apply j).continuousOn.rpow_const fun _ hu ↦
      Or.inl (Set.mem_univ_pi.mp hu j).ne')

/-- The limiting domain is open. -/
theorem isOpen_limitDomain : IsOpen (limitDomain ρ D γ q Q α) := by
  unfold limitDomain
  by_cases htied : ∑ j, Q j * α j = γ
  · have e : {u : ι → ℝ | ∑ j, Q j * α j = γ → D * ∏ j, u j ^ (-(Q j / q)) < ρ} =
        {u | D * ∏ j, u j ^ (-(Q j / q)) < ρ} := by
      ext u; simp [htied]
    rw [e]
    have e2 : (Set.pi univ fun j : ι ↦ if α j = 0 then Ioo (0 : ℝ) ρ else Ioi 0) ∩
        {u | D * ∏ j, u j ^ (-(Q j / q)) < ρ} =
        (Set.pi univ fun j : ι ↦ if α j = 0 then Ioo (0 : ℝ) ρ else Ioi 0) ∩
        ((Set.pi univ fun _ : ι ↦ Ioi (0 : ℝ)) ∩
          (fun u : ι → ℝ ↦ D * ∏ j, u j ^ (-(Q j / q))) ⁻¹' Iio ρ) := by
      ext u
      simp only [mem_inter_iff, mem_preimage, mem_Iio, mem_ofPred_eq]
      constructor
      · rintro ⟨h1, h2⟩
        exact ⟨h1, pi_scaled_subset_posOrthant h1, h2⟩
      · rintro ⟨h1, -, h2⟩
        exact ⟨h1, h2⟩
    rw [e2]
    exact isOpen_pi_scaled.inter
      (continuousOn_cut.isOpen_inter_preimage (isOpen_set_pi finite_univ fun _ _ ↦ isOpen_Ioi)
        isOpen_Iio)
  · have e : {u : ι → ℝ | ∑ j, Q j * α j = γ → D * ∏ j, u j ^ (-(Q j / q)) < ρ} = univ := by
      ext u; simp [htied]
    rw [e, inter_univ]
    exact isOpen_pi_scaled

/-- A nonempty limiting domain has positive measure. -/
theorem volume_limitDomain_pos (hne : (limitDomain ρ D γ q Q α).Nonempty) :
    0 < volume (limitDomain ρ D γ q Q α) :=
  isOpen_limitDomain.measure_pos volume hne

/-- When the truth constraint is strict, the limiting domain is nonempty. -/
theorem limitDomain_nonempty_of_strict (hρ : 0 < ρ) (hstrict : ∑ j, Q j * α j < γ) :
    (limitDomain ρ D γ q Q α).Nonempty := by
  refine ⟨fun _ ↦ ρ / 2, Set.mem_univ_pi.mpr fun j ↦ ?_, fun h ↦ absurd h hstrict.ne⟩
  split_ifs
  · exact ⟨by positivity, by linarith⟩
  · exact (by positivity : (0 : ℝ) < ρ / 2)

end Laplace.Multi
