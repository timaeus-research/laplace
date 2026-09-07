/-
Copyright (c) 2026 Timaeus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Laplace.Grammar.MonomialPhaseIdentity

/-!
# The exact monomial moment identity with a constant phase (Stage 2b)

Unit 228 (Taylor-tree programme). For a monomial `u^h`, exponents `2k`, phase power `p` and constant
phase `a`, the Taylor-tree term
```
T(N) = ∫_{(0,1]^{n+1}} u^h (√N u^k)^p exp(-βN u^{2k} + β√N u^k a) du
```
equals **exactly**, for every `N > 0`,
```
∏ 1/(2kᵢ) · ∑_{(μ,j,c) ∈ v} c · N^{-μ} ∑_{i ≤ j} C(j,i) (log N)^{j-i}
                                             ∫₀^N t^{μ-1} (-log t)^i g(t) dt,
```
where `v = stateDensityRep n w` is the exact state density of unit 224 (`wᵢ = (hᵢ+1)/(2kᵢ) - 1`,
`μ ∈ {(hᵢ+1)/(2kᵢ)}`, `j < multiplicity`) and `g(t) = (√t)^p e^{-βt+β√t a}` is the phase kernel
(`monomialPhase_eq`, Headline XXIII). This is the paper's substitution of the state-density
expansion into the standard integral, made into a finite exact identity: the only asymptotics left
are the truncated moments `∫₀^N`, whose tails `∫_N^∞` are exponentially small (next unit). No
Mellin inversion, no asymptotic expansion of the density, and no interchange of infinite sums is
involved. Zero `sorry`/`axiom`.
-/

open MeasureTheory Set Real

namespace Laplace.Grammar

theorem integrableOn_powLogBasis_mul_phaseKernel (β a : ℝ) (p : ℕ) {μ : ℝ} (hμ : 0 < μ) (j : ℕ)
    (N : ℝ) : IntegrableOn (fun τ => powLogBasis μ j τ * phaseKernel β a p (N * τ)) (Ioc 0 1) := by
  have hcont : Continuous fun τ : ℝ => phaseKernel β a p (N * τ) :=
    (continuous_phaseKernel β a p).comp (continuous_const.mul continuous_id)
  obtain ⟨C, hC⟩ := (isCompact_Icc (a := (0 : ℝ)) (b := 1)).exists_bound_of_continuousOn
    hcont.continuousOn
  have this : IntegrableOn (fun τ => phaseKernel β a p (N * τ) * powLogBasis μ j τ) (Ioc 0 1) :=
    (integrableOn_powLogBasis μ hμ j).bdd_mul (c := C) hcont.aestronglyMeasurable
      (ae_restrict_of_forall_mem measurableSet_Ioc fun τ hτ => hC τ ⟨hτ.1.le, hτ.2⟩)
  refine this.congr_fun (fun τ _ => ?_) measurableSet_Ioc
  beta_reduce
  ring

/-- Termwise scaling of a representation against the phase kernel. -/
theorem integral_eval_mul_phaseKernel (β a : ℝ) (p : ℕ) {N : ℝ} (hN : 0 < N) :
    ∀ c : PowLogRep, (∀ t ∈ c, 0 < t.1) →
      ∫ τ in Ioc (0 : ℝ) 1, PowLogRep.eval c τ * phaseKernel β a p (N * τ) =
        (c.map fun t => t.2.2 * (N ^ (-t.1) * ∑ i ∈ Finset.range (t.2.1 + 1),
          (t.2.1.choose i : ℝ) * (Real.log N) ^ (t.2.1 - i) * truncMoment β a p t.1 i N)).sum := by
  intro c
  induction c with
  | nil => intro _; simp
  | cons t c ih =>
    intro hc
    have ht := hc t (List.mem_cons_self ..)
    have hrest := ih fun u hu => hc u (List.mem_cons_of_mem t hu)
    have hint1 : IntegrableOn
        (fun τ => t.2.2 * (powLogBasis t.1 t.2.1 τ * phaseKernel β a p (N * τ)))
        (Ioc 0 1) := (integrableOn_powLogBasis_mul_phaseKernel β a p ht t.2.1 N).const_mul _
    have hint2 : IntegrableOn (fun τ => PowLogRep.eval c τ * phaseKernel β a p (N * τ))
        (Ioc 0 1) := by
      clear ih hrest
      induction c with
      | nil => simp only [PowLogRep.eval_nil, zero_mul]; exact integrableOn_zero
      | cons u c ihc =>
        have hu := hc u (List.mem_cons_of_mem t (List.mem_cons_self ..))
        have h1 : IntegrableOn
            (fun τ => u.2.2 * (powLogBasis u.1 u.2.1 τ * phaseKernel β a p (N * τ)))
            (Ioc 0 1) := (integrableOn_powLogBasis_mul_phaseKernel β a p hu u.2.1 N).const_mul _
        have h2 := ihc fun v hv => hc v (by
          rcases List.mem_cons.mp hv with hv | hv
          · exact hv ▸ List.mem_cons_self ..
          · exact List.mem_cons_of_mem t (List.mem_cons_of_mem u hv))
        refine (h1.add h2).congr_fun (fun τ _ => ?_) measurableSet_Ioc
        simp only [PowLogRep.eval_cons, Pi.add_apply]
        ring
    have hsplit : ∫ τ in Ioc (0 : ℝ) 1, PowLogRep.eval (t :: c) τ * phaseKernel β a p (N * τ) =
        ∫ τ in Ioc (0 : ℝ) 1, (t.2.2 * (powLogBasis t.1 t.2.1 τ * phaseKernel β a p (N * τ)) +
          PowLogRep.eval c τ * phaseKernel β a p (N * τ)) :=
      setIntegral_congr_fun measurableSet_Ioc fun τ _ => by simp only [PowLogRep.eval_cons]; ring
    rw [List.map_cons, List.sum_cons, ← hrest, hsplit, integral_add hint1 hint2,
      integral_const_mul, basis_scaling β a p ht t.2.1 hN]

/-- On the box, `(√N ∏uᵢ^{kᵢ})^p exp(-βN ∏uᵢ^{2kᵢ} + β√N ∏uᵢ^{kᵢ} a) = g(N ∏uᵢ^{2kᵢ})`. -/
theorem phaseKernel_box_eq {d : ℕ} (β a : ℝ) (p : ℕ) (k : Fin d → ℕ) {N : ℝ} (hN : 0 ≤ N)
    {u : Fin d → ℝ} (hu : u ∈ unitBox d) :
    (Real.sqrt N * ∏ i, u i ^ k i) ^ p *
        Real.exp (-(β * N * ∏ i, u i ^ (2 * k i)) + β * (Real.sqrt N * ∏ i, u i ^ k i) * a) =
      phaseKernel β a p (N * ∏ i, u i ^ (2 * k i)) := by
  have hP : 0 ≤ ∏ i, u i ^ k i :=
    Finset.prod_nonneg fun i _ => pow_nonneg (hu i (mem_univ i)).1.le _
  have hsq : ∏ i, u i ^ (2 * k i) = (∏ i, u i ^ k i) ^ 2 := by
    rw [← Finset.prod_pow]
    exact Finset.prod_congr rfl fun i _ => by rw [← pow_mul, mul_comm]
  unfold phaseKernel
  rw [hsq, Real.sqrt_mul hN, Real.sqrt_sq hP]
  congr 2
  ring

/-- **Headline XXIII — exact monomial moment identity with a constant phase.** -/
theorem monomialPhase_eq (n : ℕ) (h k : Fin (n + 1) → ℕ) (hk : ∀ i, 0 < k i) (β a : ℝ) (p : ℕ)
    {N : ℝ} (hN : 0 < N) :
    ∫ u in unitBox (n + 1), (∏ i, u i ^ h i) * ((Real.sqrt N * ∏ i, u i ^ k i) ^ p *
        Real.exp (-(β * N * ∏ i, u i ^ (2 * k i)) + β * (Real.sqrt N * ∏ i, u i ^ k i) * a)) =
      (∏ i, 1 / (2 * (k i : ℝ))) *
        ((stateDensityRep n fun i => ((h i : ℝ) + 1) / (2 * (k i : ℝ)) - 1).map fun t =>
          t.2.2 * (N ^ (-t.1) * ∑ i ∈ Finset.range (t.2.1 + 1),
            (t.2.1.choose i : ℝ) * (Real.log N) ^ (t.2.1 - i) *
              truncMoment β a p t.1 i N)).sum := by
  have hbox : ∫ u in unitBox (n + 1), (∏ i, u i ^ h i) * ((Real.sqrt N * ∏ i, u i ^ k i) ^ p *
      Real.exp (-(β * N * ∏ i, u i ^ (2 * k i)) + β * (Real.sqrt N * ∏ i, u i ^ k i) * a)) =
      ∫ u in unitBox (n + 1), (∏ i, u i ^ h i) * phaseKernel β a p (N * ∏ i, u i ^ (2 * k i)) :=
    setIntegral_congr_fun (measurableSet_unitBox _) fun u hu => by
      rw [phaseKernel_box_eq β a p k hN.le hu]
  rw [hbox, integral_unitBox_monomial_eq_stateDensity n h k hk (fun τ => phaseKernel β a p (N * τ))
    ((continuous_phaseKernel β a p).comp (continuous_const.mul continuous_id)).measurable
    (fun τ _ => phaseKernel_nonneg β a p _)]
  congr 1
  refine integral_eval_mul_phaseKernel β a p hN _ fun t ht => ?_
  obtain ⟨i, hi⟩ := stateDensityRep_exponent_mem n _ t ht
  rw [hi]
  have hk' : (0 : ℝ) < k i := by exact_mod_cast hk i
  simp only [sub_add_cancel]
  positivity

end Laplace.Grammar
