You are an independent statement-level fidelity reviewer for a Lean 4 / Mathlib formalisation of Section 4 of a paper on asymptotic expansions of "standard integrals" arising in singular learning theory (the "grammar" paper). You do not run Lean; you review the mathematics of the statements against the paper. Report: overall verdict; per-unit verdicts (u230–u239); a should-fix list (statement or documentation) before Stage 4; sanity checks you performed. Be concrete and sceptical; identify any normalisation, indexing, or scope error.

## Paper statements being formalised (polynomial case)

Definition (standard integral): Z(β,n;ξ,η) = ∫_{[0,b]^d} u^h e^{-βn u^{2k} + β√n u^k ξ(u)} η(u) du, h ∈ ℕ^d, k ∈ ℤ_{>0}^d, β > 0.
Candidate exponent set Λ(h,k) = ∪_i ((h_i+1)/(2k_i) + (1/(2k_i))ℕ).
Theorem (Taylor Tree): for ξ, η real analytic extending holomorphically to a polydisc of radius R > b, there is Λ* ⊆ Λ(h,k) with Z ~ Σ_{μ∈Λ*} n^{-μ} P_μ(β,ξ,η,log n), P_μ a polynomial in log n of degree ≤ d−1 whose coefficients are absolutely convergent series expressed through derivatives of ξ, η and the fluctuation function S_ν(a) = ∫_0^∞ t^{ν-1} e^{-βt+β√t a} dt.
Corollary (Standard Asymptotic Expansion): Z ~ Σ_{μ∈Λ*} Σ_{m=1}^d C_{μ,m} n^{-μ} (log n)^{m-1}.
Proof sketch in the paper: write J = ξ − ξ(0), expand e^{β√n u^k J} = Σ_p (β√n u^k)^p J^p / p!, expand J^p and η in monomials, substitute the state-density expansion of each monomial integral (Stage 1), substitute t = nτ (Stage 2), replace incomplete by complete fluctuation functions (error O(e^{-εn})), truncate the spectrum.

## Scope of the Lean Stage 3 (units 230–239)
b = 1 (unit box (0,1]^{d}), d = n+1 with Lean's `n : ℕ` the dimension index (NOT the sample size); Lean's `N : ℝ` is the paper's sample size n; ξ, η POLYNOMIAL (finite monomial lists `MonoRep (n+1) := List ((Fin (n+1) → ℕ) × ℝ)`, `eval P u = Σ c ∏ u_i^{γ_i}`, `l1 P = Σ|c|`, `fluct P` = list without the constant monomial so `eval (fluct ξ) u = eval ξ u − eval ξ 0`); β > 0; k_i > 0. Stage 1/2 objects: `stateDensityRep n w : List (ℝ × ℕ × ℝ)` (entries (μ, j, c) meaning c τ^{μ-1}(−log τ)^j) is the exact density of ∏ u_i^{w_i} under τ = ∏ u_i; `monoWeights h k i = (h_i+1)/(2k_i) − 1`; `PowLogRep.coeffAt c μ j` = sum of coefficients of entries with exactly (μ, j); `phaseKernel β a p t = (√t)^p exp(−βt + β√t a)`; `truncMoment β a p ν i N = ∫_{(0,N]} t^{ν-1}(−log t)^i phaseKernel`; `fluctMoment β a p ν i = ∫_{(0,∞)} …`; `latticeQ k = 2∏k_i`; `latticeBelow Q L = image (m ↦ m/Q) (range ⌈L·Q⌉₊)`; `PowLogRep.budget Q c = Σ |c| j! Q^j`.

## Lean statements (verbatim, with docstrings; proofs omitted)

### Laplace/Grammar/SpectralLattice.lean
```lean
/-- The lattice denominator `Q = 2 ∏ kᵢ`. -/
def latticeQ {d : ℕ} (k : Fin d → ℕ) : ℕ

theorem latticeQ_pos {d : ℕ} (k : Fin d → ℕ) (hk : ∀ i, 0 < k i) : 0 < latticeQ k

/-- `2kᵢ ∣ Q`. -/
theorem two_mul_dvd_latticeQ {d : ℕ} (k : Fin d → ℕ) (i : Fin d) : 2 * k i ∣ latticeQ k

/-- Every exponent `(e+1)/(2kᵢ)` (`e ∈ ℕ`) is a positive lattice point `m/Q`. -/
theorem ratio_mem_lattice {d : ℕ} (k : Fin d → ℕ) (hk : ∀ i, 0 < k i) (i : Fin d) (e : ℕ) :
    ∃ m : ℕ, 0 < m ∧ ((e : ℝ) + 1) / (2 * (k i : ℝ)) = (m : ℝ) / latticeQ k

/-- Distinct lattice points are at least `1/Q` apart. -/
theorem lattice_sub_ge {Q : ℕ} (hQ : 0 < Q) {m m' : ℕ} (hne : (m : ℝ) / Q ≠ (m' : ℝ) / Q) :
    1 / (Q : ℝ) ≤ |(m : ℝ) / Q - (m' : ℝ) / Q|

/-- The finite set of lattice points below the cutoff `L`. -/
noncomputable def latticeBelow (Q : ℕ) (L : ℝ) : Finset ℝ

theorem mem_latticeBelow {Q : ℕ} (hQ : 0 < Q) {L : ℝ} {m : ℕ} (hm : (m : ℝ) / Q < L) :
    (m : ℝ) / Q ∈ latticeBelow Q L

```

### Laplace/Grammar/DensityBudget.lean
```lean
/-- The weighted budget `∑ |c| · j! · Q^j`. -/
noncomputable def budget (Q : ℝ) (c : PowLogRep) : ℝ

@[simp] theorem budget_nil (Q : ℝ) : budget Q [] = 0

@[simp] theorem budget_cons (Q : ℝ) (t : ℝ × ℕ × ℝ) (c : PowLogRep) :
    budget Q (t :: c) = |t.2.2| * (t.2.1.factorial : ℝ) * Q ^ t.2.1 + budget Q c

theorem budget_append (Q : ℝ) (a b : PowLogRep) : budget Q (a ++ b) = budget Q a + budget Q b

theorem budget_nonneg {Q : ℝ} (hQ : 0 ≤ Q) (c : PowLogRep) : 0 ≤ budget Q c

theorem budget_smul (Q r : ℝ) (c : PowLogRep) : budget Q (smul r c) = |r| * budget Q c

theorem budget_shift (Q a : ℝ) (c : PowLogRep) : budget Q (shift a c) = budget Q c

theorem budget_flatMap (Q : ℝ) (c : PowLogRep) (f : ℝ × ℕ × ℝ → PowLogRep) :
    budget Q (c.flatMap f) = (c.map fun t => budget Q (f t)).sum

/-- Every coefficient is bounded by the budget when `Q ≥ 1`. -/
theorem sum_abs_le_budget {Q : ℝ} (hQ : 1 ≤ Q) (c : PowLogRep) :
    (c.map fun t => |t.2.2|).sum ≤ budget Q c

/-- The aggregated coefficient is bounded by the budget divided by `j! Q^j`. -/
theorem abs_coeffAt_le {Q : ℝ} (hQ : 1 ≤ Q) (c : PowLogRep) (μ : ℝ) (j : ℕ) :
    |coeffAt c μ j| * ((j.factorial : ℝ) * Q ^ j) ≤ budget Q c

/-- `B_Q(gRep α j) ≤ (j+2) · j! · Q^{j+1}` when `|α| ≥ 1/Q`. -/
theorem budget_gRep_le {Q α : ℝ} (hQ : 1 ≤ Q) (hα : 1 / Q ≤ |α|) (j : ℕ) :
    PowLogRep.budget Q (gRep α j) ≤ ((j : ℝ) + 2) * (j.factorial : ℝ) * Q ^ (j + 1)

/-- Budget of the convolution of one basis term on the lattice:
`B_Q(basisConv w (μ,j,c)) ≤ (j+2) Q · |c| j! Q^j` when `w+1-μ` is `0` or at least `1/Q` in size. -/
theorem budget_basisConv_le {Q w : ℝ} (hQ : 1 ≤ Q) (t : ℝ × ℕ × ℝ)
    (hα : t.1 = w + 1 ∨ 1 / Q ≤ |w - t.1 + 1|) :
    PowLogRep.budget Q (PowLogRep.basisConv w t) ≤
      ((t.2.1 : ℝ) + 2) * Q * (|t.2.2| * (t.2.1.factorial : ℝ) * Q ^ t.2.1)

/-- Budget of a convolution: `B_Q(conv w c) ≤ (D+2) Q · B_Q(c)` if every degree in `c` is `≤ D`. -/
theorem budget_conv_le {Q w : ℝ} (hQ : 1 ≤ Q) (c : PowLogRep) (D : ℕ)
    (hdeg : ∀ t ∈ c, t.2.1 ≤ D) (hα : ∀ t ∈ c, t.1 = w + 1 ∨ 1 / Q ≤ |w - t.1 + 1|) :
    PowLogRep.budget Q (PowLogRep.conv w c) ≤ ((D : ℝ) + 2) * Q * PowLogRep.budget Q c

/-- **Uniform budget**: if all `wᵢ + 1` are lattice points `m/Q` (`Q ≥ 1`), then
`B_Q(stateDensityRep n w) ≤ (n+1)! Q^n`. -/
theorem budget_stateDensityRep_le {Q : ℝ} (hQ : 1 ≤ Q) (hQn : ∃ q : ℕ, (q : ℝ) = Q) :
    ∀ (n : ℕ) (w : Fin (n + 1) → ℝ), (∀ i, ∃ m : ℕ, w i + 1 = (m : ℝ) / Q) →
      PowLogRep.budget Q (stateDensityRep n w) ≤ ((n + 1).factorial : ℝ) * Q ^ n

```

### Laplace/Grammar/MonomialRep.lean
```lean
/-- A polynomial in `d` variables as a finite list of monomials `(γ, c)`. -/
abbrev MonoRep (d : ℕ)

/-- The monomial `∏ uᵢ^{γᵢ}`. -/
def mono (γ : Fin d → ℕ) (u : Fin d → ℝ) : ℝ

/-- Evaluation `∑ c · u^γ`. -/
def eval (P : MonoRep d) (u : Fin d → ℝ) : ℝ

@[simp] theorem eval_nil (u : Fin d → ℝ) : eval ([] : MonoRep d) u = 0

@[simp] theorem eval_cons (t : (Fin d → ℕ) × ℝ) (P : MonoRep d) (u : Fin d → ℝ) :
    eval (t :: P) u = t.2 * mono t.1 u + eval P u

theorem eval_append (P Q : MonoRep d) (u : Fin d → ℝ) : eval (P ++ Q) u = eval P u + eval Q u

/-- The coefficient `ℓ¹` norm `∑ |c|`. -/
def l1 (P : MonoRep d) : ℝ

@[simp] theorem l1_nil : l1 ([] : MonoRep d) = 0

@[simp] theorem l1_cons (t : (Fin d → ℕ) × ℝ) (P : MonoRep d) : l1 (t :: P) = |t.2| + l1 P

theorem l1_append (P Q : MonoRep d) : l1 (P ++ Q) = l1 P + l1 Q

theorem l1_nonneg (P : MonoRep d) : 0 ≤ l1 P

theorem continuous_eval (P : MonoRep d) : Continuous (eval P)

theorem measurable_eval (P : MonoRep d) : Measurable (eval P)

theorem mono_nonneg {γ : Fin d → ℕ} {u : Fin d → ℝ} (hu : u ∈ closedCube d) : 0 ≤ mono γ u

theorem mono_le_one {γ : Fin d → ℕ} {u : Fin d → ℝ} (hu : u ∈ closedCube d) : mono γ u ≤ 1

/-- On the closed cube, `|P(u)| ≤ ‖P‖₁`. -/
theorem abs_eval_le_l1 (P : MonoRep d) {u : Fin d → ℝ} (hu : u ∈ closedCube d) :
    |eval P u| ≤ l1 P

/-- Product of representations: all pairwise products. -/
def mul (P Q : MonoRep d) : MonoRep d

theorem mono_add (γ δ : Fin d → ℕ) (u : Fin d → ℝ) : mono (γ + δ) u = mono γ u * mono δ u

theorem eval_map_mul (s : (Fin d → ℕ) × ℝ) (Q : MonoRep d) (u : Fin d → ℝ) :
    eval (Q.map fun t => (s.1 + t.1, s.2 * t.2)) u = s.2 * mono s.1 u * eval Q u

theorem eval_mul (P Q : MonoRep d) (u : Fin d → ℝ) : eval (mul P Q) u = eval P u * eval Q u

theorem l1_map_mul (s : (Fin d → ℕ) × ℝ) (Q : MonoRep d) :
    l1 (Q.map fun t => (s.1 + t.1, s.2 * t.2)) = |s.2| * l1 Q

/-- `‖PQ‖₁ = ‖P‖₁ ‖Q‖₁` for the list product. -/
theorem l1_mul (P Q : MonoRep d) : l1 (mul P Q) = l1 P * l1 Q

/-- Powers by iterated products (`pow P 0 = [(0, 1)]`, the constant `1`). -/
def pow (P : MonoRep d) : ℕ → MonoRep d
  | 0 => [(0, 1)]
  | p + 1 => mul P (pow P p)

theorem eval_pow (P : MonoRep d) (p : ℕ) (u : Fin d → ℝ) : eval (pow P p) u = eval P u ^ p

theorem l1_pow_le (P : MonoRep d) (p : ℕ) : l1 (pow P p) ≤ l1 P ^ p

/-- The fluctuation part `ξ − ξ(0)`: the terms with `γ ≠ 0`. -/
def fluct (P : MonoRep d) : MonoRep d

theorem mono_zero_apply (γ : Fin d → ℕ) : mono γ (0 : Fin d → ℝ) = if γ = 0 then 1 else 0

/-- `eval (fluct P) u = eval P u − eval P 0`. -/
theorem eval_fluct (P : MonoRep d) (u : Fin d → ℝ) : eval (fluct P) u = eval P u - eval P 0

theorem l1_fluct_le (P : MonoRep d) : l1 (fluct P) ≤ l1 P

theorem eval_fluct_zero (P : MonoRep d) : eval (fluct P) 0 = 0

```

### Laplace/Grammar/PhaseMajorant.lean
```lean
/-- The log majorant `t^{ν-1} (1+|log t|)^r (√t)^p e^{-βt+βb√t}`. -/
noncomputable def logMajorant (β b ν : ℝ) (r p : ℕ) (t : ℝ) : ℝ

/-- The positive log moment `∫₀^∞ logMajorant`. -/
noncomputable def phaseLogMoment (β b ν : ℝ) (r p : ℕ) : ℝ

theorem logMajorant_nonneg (β b ν : ℝ) (r p : ℕ) {t : ℝ} (ht : 0 ≤ t) :
    0 ≤ logMajorant β b ν r p t

theorem continuousOn_logMajorant (β b ν : ℝ) (r p : ℕ) :
    ContinuousOn (logMajorant β b ν r p) (Ioi 0)

theorem measurable_logMajorant (β b ν : ℝ) (r p : ℕ) : Measurable (logMajorant β b ν r p)

/-- On `(0,1]`, `(1+|log t|)^r = ∑ C(r,i) (-log t)^i`. -/
theorem one_add_abs_log_pow {t : ℝ} (ht : t ∈ Ioc (0 : ℝ) 1) (r : ℕ) :
    (1 + |Real.log t|) ^ r = ∑ i ∈ Finset.range (r + 1), (r.choose i : ℝ) * (-Real.log t) ^ i

theorem integrableOn_logMajorant_Ioc (β b ν : ℝ) (hν : 0 < ν) (r p : ℕ) :
    IntegrableOn (logMajorant β b ν r p) (Ioc 0 1)

/-- For `t ≥ 1`: `logMajorant ≤ C e^{-βt/4}` with `C = e^{βb²/2} m! (4/β)^m`, `m = ⌈ν⌉ + r + p`. -/
theorem logMajorant_le (β b ν : ℝ) (hβ : 0 < β) (r p : ℕ) {t : ℝ} (ht : 1 ≤ t) :
    logMajorant β b ν r p t ≤ tailConst β b p ν r * Real.exp (-(β * t / 4))

theorem integrableOn_logMajorant_Ioi_one (β b ν : ℝ) (hβ : 0 < β) (r p : ℕ) :
    IntegrableOn (logMajorant β b ν r p) (Ioi 1)

/-- **Integrability of the log majorant on `(0,∞)`** (Gate B: any real `b`, any `r, p`). -/
theorem integrableOn_logMajorant (β b ν : ℝ) (hβ : 0 < β) (hν : 0 < ν) (r p : ℕ) :
    IntegrableOn (logMajorant β b ν r p) (Ioi 0)

theorem phaseLogMoment_nonneg (β b ν : ℝ) (r p : ℕ) : 0 ≤ phaseLogMoment β b ν r p

/-- `∑_p (βB)^p/p! (√t)^p = e^{βB√t}` (the exponential series). -/
theorem tsum_phase_series (β B t : ℝ) :
    ∑' p : ℕ, (β * B) ^ p / (p.factorial : ℝ) * Real.sqrt t ^ p =
      Real.exp (β * B * Real.sqrt t)

theorem summable_phase_series (β B t : ℝ) :
    Summable fun p : ℕ => (β * B) ^ p / (p.factorial : ℝ) * Real.sqrt t ^ p

/-- Pointwise: `∑_p (βB)^p/p! · logMajorant β b ν r p t = logMajorant β (b+B) ν r 0 t`. -/
theorem tsum_logMajorant_series (β b B ν : ℝ) (r : ℕ) (t : ℝ) :
    ∑' p : ℕ, (β * B) ^ p / (p.factorial : ℝ) * logMajorant β b ν r p t =
      logMajorant β (b + B) ν r 0 t

theorem summable_logMajorant_series (β b B ν : ℝ) (r : ℕ) (t : ℝ) :
    Summable fun p : ℕ => (β * B) ^ p / (p.factorial : ℝ) * logMajorant β b ν r p t

/-- Partial sums of the phase series are dominated by the folded majorant (`B ≥ 0`, `t > 0`). -/
theorem sum_range_logMajorant_le (β b B ν : ℝ) (hB : 0 ≤ B) (hβ : 0 ≤ β) (r : ℕ) {t : ℝ}
    (ht : 0 < t) (P : ℕ) :
    ∑ p ∈ Finset.range P, (β * B) ^ p / (p.factorial : ℝ) * logMajorant β b ν r p t ≤
      logMajorant β (b + B) ν r 0 t

/-- Partial sums of the phase series are dominated by the folded majorant (`B ≥ 0`, `t > 0`). -/
theorem sum_range_logMajorant_le (β b B ν : ℝ) (hB : 0 ≤ B) (hβ : 0 ≤ β) (r : ℕ) {t : ℝ}
    (ht : 0 < t) (P : ℕ) :
    ∑ p ∈ Finset.range P, (β * B) ^ p / (p.factorial : ℝ) * logMajorant β b ν r p t ≤
      logMajorant β (b + B) ν r 0 t := by
  rw [← tsum_logMajorant_series β b B ν r t]
  exact (summable_logMajorant_series β b B ν r t).sum_le_tsum _
    (fun p _ => mul_nonneg (by positivity) (logMajorant_nonneg β b ν r p ht.le))

/-! ### The Tonelli majorant: integrate the folded series -/
theorem integrableOn_phase_series_term (β b B ν : ℝ) (hβ : 0 < β) (hν : 0 < ν) (r p : ℕ) :
    IntegrableOn (fun t => (β * B) ^ p / (p.factorial : ℝ) * logMajorant β b ν r p t) (Ioi 0)

/-- Partial sums of the phase-moment series are bounded by the folded log moment. -/
theorem sum_range_phaseLogMoment_le (β b B ν : ℝ) (hβ : 0 < β) (hν : 0 < ν) (hB : 0 ≤ B) (r : ℕ)
    (P : ℕ) :
    ∑ p ∈ Finset.range P, (β * B) ^ p / (p.factorial : ℝ) * phaseLogMoment β b ν r p ≤
      phaseLogMoment β (b + B) ν r 0

/-- **Absolute convergence of the phase-moment series** (Gate B). -/
theorem summable_phaseLogMoment_series (β b B ν : ℝ) (hβ : 0 < β) (hν : 0 < ν) (hB : 0 ≤ B)
    (r : ℕ) :
    Summable fun p : ℕ => (β * B) ^ p / (p.factorial : ℝ) * phaseLogMoment β b ν r p

/-- **Tonelli identity for the phase series**:
`∑_p (βB)^p/p! · M_{ν,r,p}(b) = M_{ν,r,0}(b+B)` for `β > 0`, `ν > 0`, `B ≥ 0`. -/
theorem tsum_phaseLogMoment_series (β b B ν : ℝ) (hβ : 0 < β) (hν : 0 < ν) (hB : 0 ≤ B) (r : ℕ) :
    ∑' p : ℕ, (β * B) ^ p / (p.factorial : ℝ) * phaseLogMoment β b ν r p =
      phaseLogMoment β (b + B) ν r 0

```

### Laplace/Grammar/PhaseTaylorIdentity.lean
```lean
/-- `∑_p x^p/p! = e^x`. -/
theorem tsum_pow_div_factorial (x : ℝ) : ∑' p : ℕ, x ^ p / (p.factorial : ℝ) = Real.exp x

/-- The polynomial phase integral `Z(N)`. -/
noncomputable def polyPhaseIntegral (n : ℕ) (h k : Fin (n + 1) → ℕ) (β N : ℝ)
    (ξ η : MonoRep (n + 1)) : ℝ

/-- The phase-order integral `∫ P(u) u^h phaseKernel β a p (N u^{2k}) du`. -/
noncomputable def phaseOrderIntegral (n : ℕ) (h k : Fin (n + 1) → ℕ) (β a : ℝ) (p : ℕ) (N : ℝ)
    (P : MonoRep (n + 1)) : ℝ

/-- The phase-order integrand. -/
noncomputable def phaseOrderIntegrand (n : ℕ) (h k : Fin (n + 1) → ℕ) (β a : ℝ) (p : ℕ) (N : ℝ)
    (P : MonoRep (n + 1)) (u : Fin (n + 1) → ℝ) : ℝ

theorem continuous_phaseOrderIntegrand (n : ℕ) (h k : Fin (n + 1) → ℕ) (β a : ℝ) (p : ℕ) (N : ℝ)
    (P : MonoRep (n + 1)) : Continuous (phaseOrderIntegrand n h k β a p N P)

theorem integrableOn_phaseOrderIntegrand (n : ℕ) (h k : Fin (n + 1) → ℕ) (β a : ℝ) (p : ℕ) (N : ℝ)
    (P : MonoRep (n + 1)) :
    IntegrableOn (phaseOrderIntegrand n h k β a p N P) (unitBox (n + 1))

theorem volume_unitBox_lt_top (d : ℕ) : (volume : Measure (Fin d → ℝ)) (unitBox d) < ⊤

/-- On the box, the phase-order integrands sum to the full integrand. -/
theorem tsum_phaseOrderIntegrand (n : ℕ) (h k : Fin (n + 1) → ℕ) (β : ℝ) {N : ℝ} (hN : 0 ≤ N)
    (ξ η : MonoRep (n + 1)) {u : Fin (n + 1) → ℝ} (hu : u ∈ unitBox (n + 1)) :
    ∑' p : ℕ, β ^ p / (p.factorial : ℝ) *
        phaseOrderIntegrand n h k β (eval ξ 0) p N (mul η (pow (fluct ξ) p)) u =
      eval η u * (∏ i, u i ^ h i) *
        Real.exp (-(β * N * ∏ i, u i ^ (2 * k i)) +
          β * (Real.sqrt N * ∏ i, u i ^ k i) * eval ξ u)

/-- On `(0,N]`, `phaseKernel β a p t ≤ (√N)^p e^{β√N|a|}` for `β ≥ 0`. -/
theorem phaseKernel_le_const (β a : ℝ) (hβ : 0 ≤ β) (p : ℕ) {N t : ℝ} (ht : 0 ≤ t) (htN : t ≤ N) :
    phaseKernel β a p t ≤ Real.sqrt N ^ p * Real.exp (β * Real.sqrt N * |a|)

theorem prod_pow_mem_Icc {d : ℕ} (e : Fin d → ℕ) {u : Fin d → ℝ} (hu : u ∈ unitBox d) :
    ∏ i, u i ^ e i ∈ Icc (0 : ℝ) 1

/-- The phase-order integrand of order `p` is bounded on the box by
`‖η‖₁ (β ‖J‖₁ √N)^p/p! · e^{β√N|a|}`. -/
theorem abs_phaseOrderIntegrand_le (n : ℕ) (h k : Fin (n + 1) → ℕ) (β : ℝ) (hβ : 0 ≤ β) {N : ℝ}
    (hN : 0 ≤ N) (ξ η : MonoRep (n + 1)) (p : ℕ) {u : Fin (n + 1) → ℝ} (hu : u ∈ unitBox (n + 1)) :
    |β ^ p / (p.factorial : ℝ) *
        phaseOrderIntegrand n h k β (eval ξ 0) p N (mul η (pow (fluct ξ) p)) u| ≤
      l1 η * ((β * l1 (fluct ξ) * Real.sqrt N) ^ p / (p.factorial : ℝ)) *
        Real.exp (β * Real.sqrt N * |eval ξ 0|)

/-- **Integrated phase Taylor identity** (`HasSum` form): the phase-order series
`∑_p β^p/p! ∫ P_p u^h phaseKernel_p(N u^{2k})` converges absolutely to `Z(N)` for every fixed
`N ≥ 0`, `β ≥ 0`. -/
theorem hasSum_phaseOrderIntegral (n : ℕ) (h k : Fin (n + 1) → ℕ) (β : ℝ) (hβ : 0 ≤ β) {N : ℝ}
    (hN : 0 ≤ N) (ξ η : MonoRep (n + 1)) :
    HasSum (fun p : ℕ => β ^ p / (p.factorial : ℝ) *
      phaseOrderIntegral n h k β (eval ξ 0) p N (mul η (pow (fluct ξ) p)))
      (polyPhaseIntegral n h k β N ξ η)

/-- **Integrated phase Taylor identity**: `Z(N) = ∑_p β^p/p! ∫ P_p u^h phaseKernel_p(N u^{2k})`,
an absolutely convergent series for every fixed `N ≥ 0`, `β ≥ 0`. -/
theorem polyPhaseIntegral_eq_tsum (n : ℕ) (h k : Fin (n + 1) → ℕ) (β : ℝ) (hβ : 0 ≤ β) {N : ℝ}
    (hN : 0 ≤ N) (ξ η : MonoRep (n + 1)) :
    polyPhaseIntegral n h k β N ξ η = ∑' p : ℕ, β ^ p / (p.factorial : ℝ) *
      phaseOrderIntegral n h k β (eval ξ 0) p N (mul η (pow (fluct ξ) p))

/-- The right-hand side of Headline XXIII: the truncated state-density sum. -/
noncomputable def monomialTruncSum (n : ℕ) (h k : Fin (n + 1) → ℕ) (β a : ℝ) (p : ℕ) (N : ℝ) :
    ℝ

/-- Headline XXIII in `phaseKernel` form. -/
theorem monomialPhase_eq_truncSum (n : ℕ) (h k : Fin (n + 1) → ℕ) (hk : ∀ i, 0 < k i) (β a : ℝ)
    (p : ℕ) {N : ℝ} (hN : 0 < N) :
    ∫ u in unitBox (n + 1), (∏ i, u i ^ h i) * phaseKernel β a p (N * ∏ i, u i ^ (2 * k i)) =
      monomialTruncSum n h k β a p N

theorem prod_pow_mul_mono {d : ℕ} (h γ : Fin d → ℕ) (u : Fin d → ℝ) :
    (∏ i, u i ^ h i) * mono γ u = ∏ i, u i ^ (h + γ) i

/-- A phase-order integral is the finite sum of its monomial phase integrals. -/
theorem phaseOrderIntegral_eq_sum (n : ℕ) (h k : Fin (n + 1) → ℕ) (β a : ℝ) (p : ℕ) (N : ℝ)
    (P : MonoRep (n + 1)) :
    phaseOrderIntegral n h k β a p N P = (P.map fun s => s.2 *
      ∫ u in unitBox (n + 1), (∏ i, u i ^ (h + s.1) i) *
        phaseKernel β a p (N * ∏ i, u i ^ (2 * k i))).sum

/-- **Headline XXIV — the exact polynomial Taylor tree.** For polynomial phase `ξ` and amplitude
`η`, every `N > 0`, `β ≥ 0`, positive `k`:
`Z(N) = ∑_p β^p/p! ∑_{(γ,c) ∈ η J^p} c · monomialTruncSum (h+γ) k β ξ(0) p N`. -/
theorem polyPhaseIntegral_eq_tsum_truncSum (n : ℕ) (h k : Fin (n + 1) → ℕ) (hk : ∀ i, 0 < k i)
    (β : ℝ) (hβ : 0 ≤ β) {N : ℝ} (hN : 0 < N) (ξ η : MonoRep (n + 1)) :
    polyPhaseIntegral n h k β N ξ η = ∑' p : ℕ, β ^ p / (p.factorial : ℝ) *
      ((mul η (pow (fluct ξ) p)).map fun s =>
        s.2 * monomialTruncSum n (h + s.1) k β (eval ξ 0) p N).sum

/-- Headline XXIV in `HasSum` form. -/
theorem hasSum_truncSum_series (n : ℕ) (h k : Fin (n + 1) → ℕ) (hk : ∀ i, 0 < k i)
    (β : ℝ) (hβ : 0 ≤ β) {N : ℝ} (hN : 0 < N) (ξ η : MonoRep (n + 1)) :
    HasSum (fun p : ℕ => β ^ p / (p.factorial : ℝ) *
      ((mul η (pow (fluct ξ) p)).map fun s =>
        s.2 * monomialTruncSum n (h + s.1) k β (eval ξ 0) p N).sum)
      (polyPhaseIntegral n h k β N ξ η)

```

### Laplace/Grammar/HighSpectrumBound.lean
```lean
/-- One state-density entry's contribution to `monomialTruncSum`. -/
noncomputable def entryTrunc (β a : ℝ) (p : ℕ) (N : ℝ) (t : ℝ × ℕ × ℝ) : ℝ

theorem monomialTruncSum_eq (n : ℕ) (h k : Fin (n + 1) → ℕ) (β a : ℝ) (p : ℕ) (N : ℝ) :
    monomialTruncSum n h k β a p N = (∏ i, 1 / (2 * (k i : ℝ))) *
      ((stateDensityRep n fun i => ((h i : ℝ) + 1) / (2 * (k i : ℝ)) - 1).map
        (entryTrunc β a p N)).sum

/-- An entry is the coefficient times the `τ`-side basis integral. -/
theorem entryTrunc_eq (β a : ℝ) (p : ℕ) {N : ℝ} (hN : 0 < N) {t : ℝ × ℕ × ℝ} (hμ : 0 < t.1) :
    entryTrunc β a p N t =
      t.2.2 * ∫ τ in Ioc (0 : ℝ) 1, powLogBasis t.1 t.2.1 τ * phaseKernel β a p (N * τ)

theorem powLogBasis_nonneg_of_mem (μ : ℝ) (j : ℕ) {τ : ℝ} (hτ : τ ∈ Ioc (0 : ℝ) 1) :
    0 ≤ powLogBasis μ j τ

theorem basis_integral_nonneg (β a : ℝ) (p : ℕ) (μ : ℝ) (j : ℕ) (N : ℝ) :
    0 ≤ ∫ τ in Ioc (0 : ℝ) 1, powLogBasis μ j τ * phaseKernel β a p (N * τ)

/-- Scaling `τ = t/N` on `(0,1]`. -/
theorem integral_Ioc_one_scale (G : ℝ → ℝ) {N : ℝ} (hN : 0 < N) :
    ∫ τ in Ioc (0 : ℝ) 1, G τ = N⁻¹ * ∫ t in Ioc (0 : ℝ) N, G (t / N)

/-- `(log N - log t)^j ≤ (1+log N)^n (1+|log t|)^n` for `N ≥ 1`, `t > 0`, `j ≤ n`. -/
theorem log_diff_pow_le {N t : ℝ} (hN : 1 ≤ N) {j n : ℕ} (hj : j ≤ n) :
    (Real.log N - Real.log t) ^ j ≤ (1 + Real.log N) ^ n * (1 + |Real.log t|) ^ n

/-- Pointwise on `(0,N]`: `τ^{L-1}(-log τ)^j g(t)` at `τ = t/N` is at most
`N^{1-L} (1+log N)^n · logMajorant β a L n p t`. -/
theorem basis_div_mul_le (β a : ℝ) (p : ℕ) (L : ℝ) {j n : ℕ} (hj : j ≤ n) {N t : ℝ} (hN : 1 ≤ N)
    (ht : 0 < t) :
    powLogBasis L j (t / N) * phaseKernel β a p t ≤
      N ^ (1 - L) * (1 + Real.log N) ^ n * logMajorant β a L n p t

/-- **Single-basis high-spectrum bound**: for `L ≤ μ`, `j ≤ n`, `N ≥ 1`,
`∫₀¹ τ^{μ-1}(-log τ)^j g_p(Nτ) dτ ≤ N^{-L} (1+log N)^n M_{L,n,p}(a)`. -/
theorem basis_integral_le (β a : ℝ) (hβ : 0 < β) (p : ℕ) {L μ : ℝ} (hL : 0 < L) (hμ : L ≤ μ)
    {j n : ℕ} (hj : j ≤ n) {N : ℝ} (hN : 1 ≤ N) :
    ∫ τ in Ioc (0 : ℝ) 1, powLogBasis μ j τ * phaseKernel β a p (N * τ) ≤
      N ^ (-L) * (1 + Real.log N) ^ n * phaseLogMoment β a L n p

/-- **High single-entry bound** (`L ≤ μ`, degree `≤ n`, `N ≥ 1`). -/
theorem abs_entryTrunc_le (β a : ℝ) (hβ : 0 < β) (p : ℕ) {L : ℝ} (hL : 0 < L) {n : ℕ} {N : ℝ}
    (hN : 1 ≤ N) {t : ℝ × ℕ × ℝ} (hμ : L ≤ t.1) (hj : t.2.1 ≤ n) :
    |entryTrunc β a p N t| ≤
      |t.2.2| * (N ^ (-L) * (1 + Real.log N) ^ n * phaseLogMoment β a L n p)

/-- The high-spectrum part (`L ≤ μ`) of a density list's truncated sum. -/
noncomputable def highSum (β a : ℝ) (p : ℕ) (N L : ℝ) (c : PowLogRep) : ℝ

/-- The low-spectrum part (`μ < L`). -/
noncomputable def lowSum (β a : ℝ) (p : ℕ) (N L : ℝ) (c : PowLogRep) : ℝ

theorem lowSum_add_highSum (β a : ℝ) (p : ℕ) (N L : ℝ) (c : PowLogRep) :
    lowSum β a p N L c + highSum β a p N L c = (c.map (entryTrunc β a p N)).sum

/-- The high part of a list is bounded by `∑|c|` times the single-entry majorant. -/
theorem abs_highSum_le (β a : ℝ) (hβ : 0 < β) (p : ℕ) {L : ℝ} (hL : 0 < L) {n : ℕ} {N : ℝ}
    (hN : 1 ≤ N) (c : PowLogRep) (hdeg : ∀ t ∈ c, t.2.1 ≤ n) :
    |highSum β a p N L c| ≤ (c.map fun t => |t.2.2|).sum *
      (N ^ (-L) * (1 + Real.log N) ^ n * phaseLogMoment β a L n p)

/-- The high part of a list is bounded by `∑|c|` times the single-entry majorant. -/
theorem abs_highSum_le (β a : ℝ) (hβ : 0 < β) (p : ℕ) {L : ℝ} (hL : 0 < L) {n : ℕ} {N : ℝ}
    (hN : 1 ≤ N) (c : PowLogRep) (hdeg : ∀ t ∈ c, t.2.1 ≤ n) :
    |highSum β a p N L c| ≤ (c.map fun t => |t.2.2|).sum *
      (N ^ (-L) * (1 + Real.log N) ^ n * phaseLogMoment β a L n p) := by
  have hM : 0 ≤ N ^ (-L) * (1 + Real.log N) ^ n * phaseLogMoment β a L n p :=
    mul_nonneg (mul_nonneg (Real.rpow_nonneg (by linarith) _)
      (pow_nonneg (by linarith [Real.log_nonneg hN]) _)) (phaseLogMoment_nonneg β a L n p)
  induction c with
  | nil => simp [highSum]
  | cons t c ih =>
    have ht := hdeg t (List.mem_cons.2 (Or.inl rfl))
    have ih' := ih fun s hs => hdeg s (List.mem_cons.2 (Or.inr hs))
    simp only [highSum, List.map_cons, List.sum_cons] at ih' ⊢
    rw [add_mul]
    refine (abs_add_le _ _).trans (add_le_add ?_ ih')
    split_ifs with h1
    · exact abs_entryTrunc_le β a hβ p hL hN h1 ht
    · rw [abs_zero]
      exact mul_nonneg (abs_nonneg _) hM

/-! ### Uniform bounds for one monomial density -/
theorem stateDensityRep_degree_le (n : ℕ) (w : Fin (n + 1) → ℝ) :
    ∀ t ∈ stateDensityRep n w, t.2.1 ≤ n

/-- The coefficient ℓ¹ norm of a monomial state density is at most `(n+1)! Q^n`, `Q = latticeQ k`,
uniformly in the monomial exponent `h`. -/
theorem sum_abs_stateDensityRep_le (n : ℕ) (h k : Fin (n + 1) → ℕ) (hk : ∀ i, 0 < k i) :
    ((stateDensityRep n fun i => ((h i : ℝ) + 1) / (2 * (k i : ℝ)) - 1).map
      fun t => |t.2.2|).sum ≤ ((n + 1).factorial : ℝ) * (latticeQ k : ℝ) ^ n

/-- The high-spectrum part of `∑_{(γ,c) ∈ P} c · monomialTruncSum (h+γ)`. -/
noncomputable def highPart (n : ℕ) (h k : Fin (n + 1) → ℕ) (β a : ℝ) (p : ℕ) (N L : ℝ)
    (P : MonoRep (n + 1)) : ℝ

/-- The low-spectrum part. -/
noncomputable def lowPart (n : ℕ) (h k : Fin (n + 1) → ℕ) (β a : ℝ) (p : ℕ) (N L : ℝ)
    (P : MonoRep (n + 1)) : ℝ

theorem lowPart_add_highPart (n : ℕ) (h k : Fin (n + 1) → ℕ) (β a : ℝ) (p : ℕ) (N L : ℝ)
    (P : MonoRep (n + 1)) :
    lowPart n h k β a p N L P + highPart n h k β a p N L P =
      (P.map fun s => s.2 * monomialTruncSum n (h + s.1) k β a p N).sum

theorem abs_sum_highSum_le (n : ℕ) (h k : Fin (n + 1) → ℕ) (hk : ∀ i, 0 < k i) (β a : ℝ)
    (hβ : 0 < β) (p : ℕ) {L : ℝ} (hL : 0 < L) {N : ℝ} (hN : 1 ≤ N) (P : MonoRep (n + 1)) :
    |(P.map fun s => s.2 * highSum β a p N L
      (stateDensityRep n fun i => ((((h + s.1) i : ℕ) : ℝ) + 1) / (2 * (k i : ℝ)) - 1)).sum| ≤
      l1 P * ((((n + 1).factorial : ℝ) * (latticeQ k : ℝ) ^ n) *
        (N ^ (-L) * (1 + Real.log N) ^ n * phaseLogMoment β a L n p))

/-- **Uniform high-part bound for one phase order** (Gate C, single order). -/
theorem abs_highPart_le (n : ℕ) (h k : Fin (n + 1) → ℕ) (hk : ∀ i, 0 < k i) (β a : ℝ)
    (hβ : 0 < β) (p : ℕ) {L : ℝ} (hL : 0 < L) {N : ℝ} (hN : 1 ≤ N) (P : MonoRep (n + 1)) :
    |highPart n h k β a p N L P| ≤ (∏ i, 1 / (2 * (k i : ℝ))) * l1 P *
      (((n + 1).factorial : ℝ) * (latticeQ k : ℝ) ^ n) *
      (N ^ (-L) * (1 + Real.log N) ^ n * phaseLogMoment β a L n p)

/-- The high-spectrum remainder `R_high(N) = ∑_p β^p/p! · highPart_p`. -/
noncomputable def highRemainder (n : ℕ) (h k : Fin (n + 1) → ℕ) (β N L : ℝ)
    (ξ η : MonoRep (n + 1)) : ℝ

/-- The low-spectrum series `∑_p β^p/p! · lowPart_p`. -/
noncomputable def lowSeries (n : ℕ) (h k : Fin (n + 1) → ℕ) (β N L : ℝ)
    (ξ η : MonoRep (n + 1)) : ℝ

/-- The `N`-free prefactor of the high-spectrum bound. -/
noncomputable def highConst (n : ℕ) (k : Fin (n + 1) → ℕ) (β L : ℝ) (ξ η : MonoRep (n + 1)) :
    ℝ

theorem highTerm_le (n : ℕ) (h k : Fin (n + 1) → ℕ) (hk : ∀ i, 0 < k i) (β : ℝ) (hβ : 0 < β)
    {L : ℝ} (hL : 0 < L) {N : ℝ} (hN : 1 ≤ N) (ξ η : MonoRep (n + 1)) (p : ℕ) :
    ‖β ^ p / (p.factorial : ℝ) *
        highPart n h k β (eval ξ 0) p N L (mul η (pow (fluct ξ) p))‖ ≤
      ((∏ i, 1 / (2 * (k i : ℝ))) * l1 η * (((n + 1).factorial : ℝ) * (latticeQ k : ℝ) ^ n) *
        (N ^ (-L) * (1 + Real.log N) ^ n)) *
        ((β * l1 (fluct ξ)) ^ p / (p.factorial : ℝ) * phaseLogMoment β (eval ξ 0) L n p)

/-- The majorant series of the high remainder sums to `highConst · N^{-L}(1+log N)^n`. -/
theorem hasSum_highMajorant (n : ℕ) (k : Fin (n + 1) → ℕ) (β : ℝ) (hβ : 0 < β) {L : ℝ}
    (hL : 0 < L) (N : ℝ) (ξ η : MonoRep (n + 1)) :
    HasSum (fun p : ℕ =>
      ((∏ i, 1 / (2 * (k i : ℝ))) * l1 η * (((n + 1).factorial : ℝ) * (latticeQ k : ℝ) ^ n) *
        (N ^ (-L) * (1 + Real.log N) ^ n)) *
        ((β * l1 (fluct ξ)) ^ p / (p.factorial : ℝ) * phaseLogMoment β (eval ξ 0) L n p))
      (highConst n k β L ξ η * (N ^ (-L) * (1 + Real.log N) ^ n))

theorem summable_highRemainder_terms (n : ℕ) (h k : Fin (n + 1) → ℕ) (hk : ∀ i, 0 < k i)
    (β : ℝ) (hβ : 0 < β) {L : ℝ} (hL : 0 < L) {N : ℝ} (hN : 1 ≤ N) (ξ η : MonoRep (n + 1)) :
    Summable fun p : ℕ => β ^ p / (p.factorial : ℝ) *
      highPart n h k β (eval ξ 0) p N L (mul η (pow (fluct ξ) p))

/-- **Gate C — the high-spectrum remainder bound**:
`|R_high(N)| ≤ K_k ‖η‖₁ (n+1)! Q^n M_{L,n}(ξ(0)+‖J‖₁) · N^{-L} (1+log N)^n` for all `N ≥ 1`. -/
theorem abs_highRemainder_le (n : ℕ) (h k : Fin (n + 1) → ℕ) (hk : ∀ i, 0 < k i) (β : ℝ)
    (hβ : 0 < β) {L : ℝ} (hL : 0 < L) {N : ℝ} (hN : 1 ≤ N) (ξ η : MonoRep (n + 1)) :
    |highRemainder n h k β N L ξ η| ≤
      highConst n k β L ξ η * (N ^ (-L) * (1 + Real.log N) ^ n)

theorem truncSum_term_split (n : ℕ) (h k : Fin (n + 1) → ℕ) (β : ℝ) (N L : ℝ)
    (ξ η : MonoRep (n + 1)) (p : ℕ) :
    β ^ p / (p.factorial : ℝ) *
      ((mul η (pow (fluct ξ) p)).map fun s =>
        s.2 * monomialTruncSum n (h + s.1) k β (eval ξ 0) p N).sum =
      β ^ p / (p.factorial : ℝ) * lowPart n h k β (eval ξ 0) p N L (mul η (pow (fluct ξ) p)) +
        β ^ p / (p.factorial : ℝ) *
          highPart n h k β (eval ξ 0) p N L (mul η (pow (fluct ξ) p))

theorem summable_lowSeries_terms (n : ℕ) (h k : Fin (n + 1) → ℕ) (hk : ∀ i, 0 < k i) (β : ℝ)
    (hβ : 0 < β) {L : ℝ} (hL : 0 < L) {N : ℝ} (hN : 1 ≤ N) (ξ η : MonoRep (n + 1)) :
    Summable fun p : ℕ => β ^ p / (p.factorial : ℝ) *
      lowPart n h k β (eval ξ 0) p N L (mul η (pow (fluct ξ) p))

/-- **Decomposition** `Z(N) = lowSeries + highRemainder` for `N ≥ 1`. -/
theorem polyPhaseIntegral_eq_low_add_high (n : ℕ) (h k : Fin (n + 1) → ℕ) (hk : ∀ i, 0 < k i)
    (β : ℝ) (hβ : 0 < β) {L : ℝ} (hL : 0 < L) {N : ℝ} (hN : 1 ≤ N) (ξ η : MonoRep (n + 1)) :
    polyPhaseIntegral n h k β N ξ η =
      lowSeries n h k β N L ξ η + highRemainder n h k β N L ξ η

```

### Laplace/Grammar/SpectralCoefficients.lean
```lean
/-- `|fluctMoment β a p μ i| ≤ M_{μ,n,p}(a)` for `i ≤ n`, `μ > 0`, `β > 0`. -/
theorem abs_fluctMoment_le (β a : ℝ) (hβ : 0 < β) (p : ℕ) {μ : ℝ} (hμ : 0 < μ) {i n : ℕ}
    (hi : i ≤ n) : |fluctMoment β a p μ i| ≤ phaseLogMoment β a μ n p

/-- `|fluctMoment β a p μ i| ≤ M_{μ,n,p}(a)` for `i ≤ n`, `μ > 0`, `β > 0`. -/
theorem abs_fluctMoment_le (β a : ℝ) (hβ : 0 < β) (p : ℕ) {μ : ℝ} (hμ : 0 < μ) {i n : ℕ}
    (hi : i ≤ n) : |fluctMoment β a p μ i| ≤ phaseLogMoment β a μ n p := by
  unfold fluctMoment phaseLogMoment
  refine abs_integral_le_integral_abs.trans ?_
  refine integral_mono_of_nonneg (Eventually.of_forall fun t => abs_nonneg _)
    (integrableOn_logMajorant β a μ hβ hμ n p)
    (ae_restrict_of_forall_mem measurableSet_Ioi fun t ht => ?_)
  have ht0 : 0 < t := mem_Ioi.1 ht
  beta_reduce
  rw [abs_mul, abs_mul, abs_of_nonneg (Real.rpow_nonneg ht0.le _),
    abs_of_nonneg (phaseKernel_nonneg _ _ _ _), abs_pow, abs_neg]
  unfold logMajorant
  refine mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left ?_ (Real.rpow_nonneg ht0.le _))
    (phaseKernel_nonneg _ _ _ _)
  have h0 := abs_nonneg (Real.log t)
  calc |Real.log t| ^ i ≤ (1 + |Real.log t|) ^ i := pow_le_pow_left₀ h0 (by linarith) i
    _ ≤ (1 + |Real.log t|) ^ n := pow_le_pow_right₀ (by linarith) hi

/-! ### The lattice below the cutoff -/
theorem lt_of_mem_latticeBelow {Q : ℕ} (hQ : 0 < Q) {L μ : ℝ} (hμ : μ ∈ latticeBelow Q L) :
    μ < L

theorem sum_sum_ite_coeff (S : Finset ℝ) (R : Finset ℕ) (μ₀ : ℝ) {q₀ : ℕ} (hq : q₀ ∈ R) (x : ℝ)
    (G : ℝ → ℕ → ℝ) :
    ∑ μ ∈ S, ∑ q ∈ R, (if μ₀ = μ ∧ q₀ = q then x else 0) * G μ q =
      if μ₀ ∈ S then x * G μ₀ q₀ else 0

/-- Regrouping a lattice-supported representation by aggregated coefficients: for entries with
exponents in `Q⁻¹ℕ` and degrees `≤ n`,
`∑_{entries, μ < L} c · G μ j = ∑_{μ ∈ Λ_L} ∑_{q ≤ n} coeffAt μ q · G μ q`. -/
theorem sum_map_lt_eq_sum_coeffAt {Q : ℕ} (hQ : 0 < Q) (L : ℝ) (n : ℕ) (G : ℝ → ℕ → ℝ) :
    ∀ c : PowLogRep, (∀ t ∈ c, ∃ m : ℕ, t.1 = (m : ℝ) / Q) → (∀ t ∈ c, t.2.1 < n + 1) →
      (c.map fun t => if t.1 < L then t.2.2 * G t.1 t.2.1 else 0).sum =
        ∑ μ ∈ latticeBelow Q L, ∑ q ∈ Finset.range (n + 1),
          PowLogRep.coeffAt c μ q * G μ q

/-- Regrouping a lattice-supported representation by aggregated coefficients: for entries with
exponents in `Q⁻¹ℕ` and degrees `≤ n`,
`∑_{entries, μ < L} c · G μ j = ∑_{μ ∈ Λ_L} ∑_{q ≤ n} coeffAt μ q · G μ q`. -/
theorem sum_map_lt_eq_sum_coeffAt {Q : ℕ} (hQ : 0 < Q) (L : ℝ) (n : ℕ) (G : ℝ → ℕ → ℝ) :
    ∀ c : PowLogRep, (∀ t ∈ c, ∃ m : ℕ, t.1 = (m : ℝ) / Q) → (∀ t ∈ c, t.2.1 < n + 1) →
      (c.map fun t => if t.1 < L then t.2.2 * G t.1 t.2.1 else 0).sum =
        ∑ μ ∈ latticeBelow Q L, ∑ q ∈ Finset.range (n + 1),
          PowLogRep.coeffAt c μ q * G μ q := by
  intro c
  induction c with
  | nil => simp [PowLogRep.coeffAt_nil]
  | cons t c ih =>
    intro hlat hdeg
    have ih' := ih (fun s hs => hlat s (List.mem_cons_of_mem _ hs))
      (fun s hs => hdeg s (List.mem_cons_of_mem _ hs))
    rw [List.map_cons, List.sum_cons, ih']
    simp only [PowLogRep.coeffAt_cons, add_mul, Finset.sum_add_distrib]
    congr 1
    have hq : t.2.1 ∈ Finset.range (n + 1) :=
      Finset.mem_range.2 (hdeg t (List.mem_cons.2 (Or.inl rfl)))
    rw [sum_sum_ite_coeff (latticeBelow Q L) (Finset.range (n + 1)) t.1 hq t.2.2 G]
    obtain ⟨m, hm⟩ := hlat t (List.mem_cons.2 (Or.inl rfl))
    by_cases hL : t.1 < L
    · rw [if_pos hL, if_pos]
      rw [hm] at hL ⊢
      exact mem_latticeBelow hQ hL
    · rw [if_neg hL, if_neg]
      exact fun hmem => hL (lt_of_mem_latticeBelow hQ hmem)

/-! ### Binomial reflection -/
theorem sum_choose_reflect (q : ℕ) (x : ℝ) (f : ℕ → ℝ) :
    ∑ i ∈ Finset.range (q + 1), (q.choose i : ℝ) * x ^ (q - i) * f i =
      ∑ j ∈ Finset.range (q + 1), (q.choose j : ℝ) * x ^ j * f (q - j)

/-- One density entry with the full fluctuation moments. -/
noncomputable def entryMain (β a : ℝ) (p : ℕ) (N : ℝ) (t : ℝ × ℕ × ℝ) : ℝ

/-- The low-spectrum part with full moments. -/
noncomputable def lowMain (β a : ℝ) (p : ℕ) (N L : ℝ) (c : PowLogRep) : ℝ

/-- The Stage 1 weights of the monomial `u^h` with exponents `2k`. -/
noncomputable def monoWeights {d : ℕ} (h k : Fin d → ℕ) : Fin d → ℝ

theorem monoWeights_lattice {d : ℕ} (h k : Fin d → ℕ) (hk : ∀ i, 0 < k i) (i : Fin d) :
    ∃ m : ℕ, monoWeights h k i + 1 = (m : ℝ) / latticeQ k

theorem stateDensityRep_monoWeights_lattice (n : ℕ) (h k : Fin (n + 1) → ℕ) (hk : ∀ i, 0 < k i) :
    ∀ t ∈ stateDensityRep n (monoWeights h k), ∃ m : ℕ, t.1 = (m : ℝ) / latticeQ k

theorem stateDensityRep_monoWeights_pos (n : ℕ) (h k : Fin (n + 1) → ℕ) (hk : ∀ i, 0 < k i) :
    ∀ t ∈ stateDensityRep n (monoWeights h k), 0 < t.1

/-- The aggregated coefficient of a monomial density is bounded by `(n+1)! Q^n`, uniformly. -/
theorem abs_coeffAt_stateDensityRep_le (n : ℕ) (h k : Fin (n + 1) → ℕ) (hk : ∀ i, 0 < k i)
    (μ : ℝ) (q : ℕ) :
    |PowLogRep.coeffAt (stateDensityRep n (monoWeights h k)) μ q| ≤
      ((n + 1).factorial : ℝ) * (latticeQ k : ℝ) ^ n

/-- `coeffAt` vanishes at an exponent not carried by the list. -/
theorem coeffAt_eq_zero_of_forall_ne (c : PowLogRep) {μ : ℝ} (hc : ∀ t ∈ c, t.1 ≠ μ) (q : ℕ) :
    PowLogRep.coeffAt c μ q = 0

/-- Per phase order: the coefficient of `N^{-μ} (log N)^j` (the paper's `A_{μ,j}` before the
sum over phase orders). -/
noncomputable def coeffTerm (n : ℕ) (h k : Fin (n + 1) → ℕ) (β a : ℝ) (p : ℕ) (μ : ℝ) (j : ℕ)
    (P : MonoRep (n + 1)) : ℝ

/-- The low-spectrum main part of one phase order. -/
noncomputable def mainPart (n : ℕ) (h k : Fin (n + 1) → ℕ) (β a : ℝ) (p : ℕ) (N L : ℝ)
    (P : MonoRep (n + 1)) : ℝ

theorem list_sum_finset_sum_comm {ι κ : Type*} (P : List ι) (S : Finset κ) (f : ι → ℝ)
    (g : ι → κ → ℝ) :
    (P.map fun s => f s * ∑ μ ∈ S, g s μ).sum = ∑ μ ∈ S, (P.map fun s => f s * g s μ).sum

/-- Regrouping one monomial density: `lowMain = ∑_{μ ∈ Λ_L} ∑_{j ≤ n} N^{-μ} (log N)^j T(μ,j)`. -/
theorem lowMain_eq_sum (n : ℕ) (h k : Fin (n + 1) → ℕ) (hk : ∀ i, 0 < k i) (β a : ℝ) (p : ℕ)
    (N L : ℝ) :
    lowMain β a p N L (stateDensityRep n (monoWeights h k)) =
      ∑ μ ∈ latticeBelow (latticeQ k) L, ∑ j ∈ Finset.range (n + 1),
        N ^ (-μ) * (Real.log N) ^ j * ∑ q ∈ Finset.Ico j (n + 1),
          PowLogRep.coeffAt (stateDensityRep n (monoWeights h k)) μ q * (q.choose j : ℝ) *
            fluctMoment β a p μ (q - j)

/-- **Regrouping of the main part** by spectral exponent and log power. -/
theorem mainPart_eq_sum (n : ℕ) (h k : Fin (n + 1) → ℕ) (hk : ∀ i, 0 < k i) (β a : ℝ) (p : ℕ)
    (N L : ℝ) (P : MonoRep (n + 1)) :
    mainPart n h k β a p N L P = ∑ μ ∈ latticeBelow (latticeQ k) L, ∑ j ∈ Finset.range (n + 1),
      N ^ (-μ) * (Real.log N) ^ j * coeffTerm n h k β a p μ j P

/-- Uniform bound on one coefficient term (`μ > 0`). -/
theorem abs_coeffTerm_le (n : ℕ) (h k : Fin (n + 1) → ℕ) (hk : ∀ i, 0 < k i) (β a : ℝ)
    (hβ : 0 < β) (p : ℕ) {μ : ℝ} (hμ : 0 < μ) (j : ℕ) (P : MonoRep (n + 1)) :
    |coeffTerm n h k β a p μ j P| ≤ (∏ i, 1 / (2 * (k i : ℝ))) * l1 P *
      ((n + 1 : ℝ) * (((n + 1).factorial : ℝ) * (latticeQ k : ℝ) ^ n) * 2 ^ n) *
      phaseLogMoment β a μ n p

/-- The `N`-free constant of the coefficient majorant. -/
noncomputable def coeffConst (n : ℕ) (k : Fin (n + 1) → ℕ) (η : MonoRep (n + 1)) : ℝ

theorem coeffTerm_series_le (n : ℕ) (h k : Fin (n + 1) → ℕ) (hk : ∀ i, 0 < k i) (β : ℝ)
    (hβ : 0 < β) {μ : ℝ} (hμ : 0 < μ) (j : ℕ) (ξ η : MonoRep (n + 1)) (p : ℕ) :
    ‖β ^ p / (p.factorial : ℝ) * coeffTerm n h k β (eval ξ 0) p μ j (mul η (pow (fluct ξ) p))‖ ≤
      coeffConst n k η *
        ((β * l1 (fluct ξ)) ^ p / (p.factorial : ℝ) * phaseLogMoment β (eval ξ 0) μ n p)

/-- **Gate D — absolute convergence of the spectral-coefficient series** for every `μ`. -/
theorem summable_coeffTerm_series (n : ℕ) (h k : Fin (n + 1) → ℕ) (hk : ∀ i, 0 < k i) (β : ℝ)
    (hβ : 0 < β) (μ : ℝ) (j : ℕ) (ξ η : MonoRep (n + 1)) :
    Summable fun p : ℕ => β ^ p / (p.factorial : ℝ) *
      coeffTerm n h k β (eval ξ 0) p μ j (mul η (pow (fluct ξ) p))

/-- **The spectral coefficient** `A_{μ,j}` — defined without reference to any cutoff. -/
noncomputable def spectralCoeff (n : ℕ) (h k : Fin (n + 1) → ℕ) (β : ℝ) (ξ η : MonoRep (n + 1))
    (μ : ℝ) (j : ℕ) : ℝ

/-- The main series `∑_p β^p/p! mainPart_p`. -/
noncomputable def mainSeries (n : ℕ) (h k : Fin (n + 1) → ℕ) (β N L : ℝ) (ξ η : MonoRep (n + 1)) :
    ℝ

/-- **Regrouped main series**:
`∑_p β^p/p! mainPart_p = ∑_{μ ∈ Λ_L} N^{-μ} ∑_{j ≤ n} A_{μ,j} (log N)^j`. -/
theorem mainSeries_eq_sum (n : ℕ) (h k : Fin (n + 1) → ℕ) (hk : ∀ i, 0 < k i) (β : ℝ)
    (hβ : 0 < β) (N L : ℝ) (ξ η : MonoRep (n + 1)) :
    mainSeries n h k β N L ξ η = ∑ μ ∈ latticeBelow (latticeQ k) L, N ^ (-μ) *
      ∑ j ∈ Finset.range (n + 1), spectralCoeff n h k β ξ η μ j * (Real.log N) ^ j

```

### Laplace/Grammar/LowSpectrumTail.lean
```lean
/-- `∫_N^∞ logMajorant β a L n p`. -/
noncomputable def logTailMoment (β a L : ℝ) (n p : ℕ) (N : ℝ) : ℝ

theorem logTailMoment_nonneg (β a L : ℝ) (n p : ℕ) {N : ℝ} (hN : 0 ≤ N) :
    0 ≤ logTailMoment β a L n p N

/-- The Tonelli identity of unit 234 on `(N,∞)`, `N ≥ 0`. -/
theorem tsum_logTailMoment_series (β a B L : ℝ) (hβ : 0 < β) (hL : 0 < L) (hB : 0 ≤ B) (n : ℕ)
    {N : ℝ} (hN : 0 ≤ N) :
    ∑' p : ℕ, (β * B) ^ p / (p.factorial : ℝ) * logTailMoment β a L n p N =
      logTailMoment β (a + B) L n 0 N

theorem summable_logTailMoment_series (β a B L : ℝ) (hβ : 0 < β) (hL : 0 < L) (hB : 0 ≤ B) (n : ℕ)
    {N : ℝ} (hN : 0 ≤ N) :
    Summable fun p : ℕ => (β * B) ^ p / (p.factorial : ℝ) * logTailMoment β a L n p N

/-- The tail of the log majorant at phase order `0` decays exponentially. -/
theorem logTailMoment_le (β b L : ℝ) (hβ : 0 < β) (n : ℕ) {N : ℝ} (hN : 1 ≤ N) :
    logTailMoment β b L n 0 N ≤ tailConst β b 0 L n * (4 / β) * Real.exp (-(β * N / 4))

/-- `e^{-βN/4} ≤ ⌈L⌉! (4/β)^{⌈L⌉} N^{-L}` for `N ≥ 1`, `L > 0`. -/
theorem exp_le_rpow_const (β L : ℝ) (hβ : 0 < β) {N : ℝ} (hN : 1 ≤ N) :
    Real.exp (-(β * N / 4)) ≤
      ((⌈L⌉₊.factorial : ℝ) * (4 / β) ^ ⌈L⌉₊) * N ^ (-L)

/-- The tail `∫_N^∞ t^{μ-1}(-log t)^i g_p(t) dt` of a fluctuation moment. -/
noncomputable def momentTail (β a : ℝ) (p : ℕ) (μ : ℝ) (i : ℕ) (N : ℝ) : ℝ

/-- One density entry with the tails of the moments. -/
noncomputable def entryTail (β a : ℝ) (p : ℕ) (N : ℝ) (t : ℝ × ℕ × ℝ) : ℝ

theorem entryTrunc_eq_main_sub_tail (β a : ℝ) (hβ : 0 < β) (p : ℕ) {N : ℝ} (hN : 1 ≤ N)
    {t : ℝ × ℕ × ℝ} (hμ : 0 < t.1) :
    entryTrunc β a p N t = entryMain β a p N t - entryTail β a p N t

/-- `|momentTail| ≤ logTailMoment β a L n p N` for `0 < μ ≤ L`, `i ≤ n`, `N ≥ 1`. -/
theorem abs_momentTail_le (β a : ℝ) (hβ : 0 < β) (p : ℕ) {L μ : ℝ} (hL : 0 < L) (hμ : μ ≤ L)
    {i n : ℕ} (hi : i ≤ n) {N : ℝ} (hN : 1 ≤ N) :
    |momentTail β a p μ i N| ≤ logTailMoment β a L n p N

/-- **Single-entry tail bound**: `|entryTail| ≤ |c| (1+log N)^n logTailMoment`
(`0 < μ ≤ L`, `j ≤ n`). -/
theorem abs_entryTail_le (β a : ℝ) (hβ : 0 < β) (p : ℕ) {L : ℝ} (hL : 0 < L) {n : ℕ} {N : ℝ}
    (hN : 1 ≤ N) {t : ℝ × ℕ × ℝ} (hμ0 : 0 < t.1) (hμ : t.1 ≤ L) (hj : t.2.1 ≤ n) :
    |entryTail β a p N t| ≤ |t.2.2| * ((1 + Real.log N) ^ n * logTailMoment β a L n p N)

/-- The low-spectrum tail part of a density list. -/
noncomputable def lowTail (β a : ℝ) (p : ℕ) (N L : ℝ) (c : PowLogRep) : ℝ

theorem lowSum_add_lowTail (β a : ℝ) (hβ : 0 < β) (p : ℕ) {N : ℝ} (hN : 1 ≤ N) (L : ℝ)
    (c : PowLogRep) (hpos : ∀ t ∈ c, 0 < t.1) :
    lowSum β a p N L c + lowTail β a p N L c = lowMain β a p N L c

theorem lowSum_eq_main_sub_tail (β a : ℝ) (hβ : 0 < β) (p : ℕ) {N : ℝ} (hN : 1 ≤ N) (L : ℝ)
    (c : PowLogRep) (hpos : ∀ t ∈ c, 0 < t.1) :
    lowSum β a p N L c = lowMain β a p N L c - lowTail β a p N L c

theorem abs_lowTail_le (β a : ℝ) (hβ : 0 < β) (p : ℕ) {L : ℝ} (hL : 0 < L) {n : ℕ} {N : ℝ}
    (hN : 1 ≤ N) (c : PowLogRep) (hpos : ∀ t ∈ c, 0 < t.1) (hdeg : ∀ t ∈ c, t.2.1 ≤ n) :
    |lowTail β a p N L c| ≤ (c.map fun t => |t.2.2|).sum *
      ((1 + Real.log N) ^ n * logTailMoment β a L n p N)

/-- The low-spectrum tail part of one phase order. -/
noncomputable def tailPart (n : ℕ) (h k : Fin (n + 1) → ℕ) (β a : ℝ) (p : ℕ) (N L : ℝ)
    (P : MonoRep (n + 1)) : ℝ

theorem lowPart_eq_main_sub_tail (n : ℕ) (h k : Fin (n + 1) → ℕ) (hk : ∀ i, 0 < k i) (β a : ℝ)
    (hβ : 0 < β) (p : ℕ) {N : ℝ} (hN : 1 ≤ N) (L : ℝ) (P : MonoRep (n + 1)) :
    lowPart n h k β a p N L P = mainPart n h k β a p N L P - tailPart n h k β a p N L P

theorem abs_tailPart_le (n : ℕ) (h k : Fin (n + 1) → ℕ) (hk : ∀ i, 0 < k i) (β a : ℝ)
    (hβ : 0 < β) (p : ℕ) {L : ℝ} (hL : 0 < L) {N : ℝ} (hN : 1 ≤ N) (P : MonoRep (n + 1)) :
    |tailPart n h k β a p N L P| ≤ (∏ i, 1 / (2 * (k i : ℝ))) * l1 P *
      (((n + 1).factorial : ℝ) * (latticeQ k : ℝ) ^ n) *
      ((1 + Real.log N) ^ n * logTailMoment β a L n p N)

/-- The tail series `∑_p β^p/p! tailPart_p`. -/
noncomputable def tailSeries (n : ℕ) (h k : Fin (n + 1) → ℕ) (β N L : ℝ) (ξ η : MonoRep (n + 1)) :
    ℝ

theorem tailTerm_le (n : ℕ) (h k : Fin (n + 1) → ℕ) (hk : ∀ i, 0 < k i) (β : ℝ) (hβ : 0 < β)
    {L : ℝ} (hL : 0 < L) {N : ℝ} (hN : 1 ≤ N) (ξ η : MonoRep (n + 1)) (p : ℕ) :
    ‖β ^ p / (p.factorial : ℝ) * tailPart n h k β (eval ξ 0) p N L (mul η (pow (fluct ξ) p))‖ ≤
      ((∏ i, 1 / (2 * (k i : ℝ))) * l1 η * (((n + 1).factorial : ℝ) * (latticeQ k : ℝ) ^ n) *
        (1 + Real.log N) ^ n) *
        ((β * l1 (fluct ξ)) ^ p / (p.factorial : ℝ) * logTailMoment β (eval ξ 0) L n p N)

theorem hasSum_tailMajorant (n : ℕ) (k : Fin (n + 1) → ℕ) (β : ℝ) (hβ : 0 < β) {L : ℝ}
    (hL : 0 < L) {N : ℝ} (hN : 1 ≤ N) (ξ η : MonoRep (n + 1)) :
    HasSum (fun p : ℕ =>
      ((∏ i, 1 / (2 * (k i : ℝ))) * l1 η * (((n + 1).factorial : ℝ) * (latticeQ k : ℝ) ^ n) *
        (1 + Real.log N) ^ n) *
        ((β * l1 (fluct ξ)) ^ p / (p.factorial : ℝ) * logTailMoment β (eval ξ 0) L n p N))
      (((∏ i, 1 / (2 * (k i : ℝ))) * l1 η * (((n + 1).factorial : ℝ) * (latticeQ k : ℝ) ^ n) *
        (1 + Real.log N) ^ n) * logTailMoment β (eval ξ 0 + l1 (fluct ξ)) L n 0 N)

theorem summable_tailSeries_terms (n : ℕ) (h k : Fin (n + 1) → ℕ) (hk : ∀ i, 0 < k i) (β : ℝ)
    (hβ : 0 < β) {L : ℝ} (hL : 0 < L) {N : ℝ} (hN : 1 ≤ N) (ξ η : MonoRep (n + 1)) :
    Summable fun p : ℕ => β ^ p / (p.factorial : ℝ) *
      tailPart n h k β (eval ξ 0) p N L (mul η (pow (fluct ξ) p))

/-- The `N`-free constant of the low-spectrum tail bound. -/
noncomputable def tailSeriesConst (n : ℕ) (k : Fin (n + 1) → ℕ) (β L : ℝ)
    (ξ η : MonoRep (n + 1)) : ℝ

/-- **Summed low-spectrum tail bound**: `|tailSeries| ≤ tailSeriesConst · N^{-L}(1+log N)^n`. -/
theorem abs_tailSeries_le (n : ℕ) (h k : Fin (n + 1) → ℕ) (hk : ∀ i, 0 < k i) (β : ℝ)
    (hβ : 0 < β) {L : ℝ} (hL : 0 < L) {N : ℝ} (hN : 1 ≤ N) (ξ η : MonoRep (n + 1)) :
    |tailSeries n h k β N L ξ η| ≤
      tailSeriesConst n k β L ξ η * (N ^ (-L) * (1 + Real.log N) ^ n)

/-- **Summed low-spectrum tail bound**: `|tailSeries| ≤ tailSeriesConst · N^{-L}(1+log N)^n`. -/
theorem abs_tailSeries_le (n : ℕ) (h k : Fin (n + 1) → ℕ) (hk : ∀ i, 0 < k i) (β : ℝ)
    (hβ : 0 < β) {L : ℝ} (hL : 0 < L) {N : ℝ} (hN : 1 ≤ N) (ξ η : MonoRep (n + 1)) :
    |tailSeries n h k β N L ξ η| ≤
      tailSeriesConst n k β L ξ η * (N ^ (-L) * (1 + Real.log N) ^ n) := by
  have h1 := tsum_of_norm_bounded (hasSum_tailMajorant n k β hβ hL hN ξ η)
    (tailTerm_le n h k hk β hβ hL hN ξ η)
  rw [Real.norm_eq_abs] at h1
  refine h1.trans ?_
  have hK : 0 ≤ ∏ i, 1 / (2 * (k i : ℝ)) := Finset.prod_nonneg fun i _ => by positivity
  have hpre : 0 ≤ (∏ i, 1 / (2 * (k i : ℝ))) * l1 η *
      (((n + 1).factorial : ℝ) * (latticeQ k : ℝ) ^ n) * (1 + Real.log N) ^ n :=
    mul_nonneg (mul_nonneg (mul_nonneg hK (l1_nonneg η)) (by positivity))
      (pow_nonneg (by linarith [Real.log_nonneg hN]) _)
  have hT := (logTailMoment_le β (eval ξ 0 + l1 (fluct ξ)) L hβ n hN).trans
    (mul_le_mul_of_nonneg_left (exp_le_rpow_const β L hβ hN)
      (mul_nonneg (tailConst_nonneg β _ hβ 0 L n) (by positivity)))
  calc _ ≤ ((∏ i, 1 / (2 * (k i : ℝ))) * l1 η *
        (((n + 1).factorial : ℝ) * (latticeQ k : ℝ) ^ n) * (1 + Real.log N) ^ n) *
        (tailConst β (eval ξ 0 + l1 (fluct ξ)) 0 L n * (4 / β) *
          (((⌈L⌉₊.factorial : ℝ) * (4 / β) ^ ⌈L⌉₊) * N ^ (-L))) :=
        mul_le_mul_of_nonneg_left hT hpre
    _ = _ := by unfold tailSeriesConst; ring

/-! ### Assembly: the quantitative cutoff theorem -/
theorem lowSeries_eq_main_sub_tail (n : ℕ) (h k : Fin (n + 1) → ℕ) (hk : ∀ i, 0 < k i) (β : ℝ)
    (hβ : 0 < β) {L : ℝ} (hL : 0 < L) {N : ℝ} (hN : 1 ≤ N) (ξ η : MonoRep (n + 1)) :
    lowSeries n h k β N L ξ η = mainSeries n h k β N L ξ η - tailSeries n h k β N L ξ η

/-- The constant of the cutoff theorem: high-spectrum plus low-spectrum-tail contributions. -/
noncomputable def taylorCutoffConst (n : ℕ) (k : Fin (n + 1) → ℕ) (β L : ℝ)
    (ξ η : MonoRep (n + 1)) : ℝ

/-- **The polynomial Taylor tree, exact form**: `Z(N)` minus the spectral sum below the cutoff is
the high-spectrum remainder minus the low-spectrum tail. -/
theorem polyPhaseIntegral_sub_spectralSum (n : ℕ) (h k : Fin (n + 1) → ℕ) (hk : ∀ i, 0 < k i)
    (β : ℝ) (hβ : 0 < β) {L : ℝ} (hL : 0 < L) {N : ℝ} (hN : 1 ≤ N) (ξ η : MonoRep (n + 1)) :
    polyPhaseIntegral n h k β N ξ η - ∑ μ ∈ latticeBelow (latticeQ k) L, N ^ (-μ) *
        ∑ j ∈ Finset.range (n + 1), spectralCoeff n h k β ξ η μ j * (Real.log N) ^ j =
      highRemainder n h k β N L ξ η - tailSeries n h k β N L ξ η

/-- **Headline XXV — quantitative polynomial Taylor tree.** For polynomial phase `ξ` and
amplitude `η`, `β > 0`, positive `k`, every cutoff `L > 0` and every `N ≥ 1`,
`|Z(N) - ∑_{μ ∈ Λ_L} N^{-μ} ∑_{j ≤ n} A_{μ,j} (log N)^j| ≤ taylorCutoffConst · N^{-L} (1+log N)^n`,
with `A_{μ,j}` independent of `L` and `N`. -/
theorem taylorTree_cutoff_bound (n : ℕ) (h k : Fin (n + 1) → ℕ) (hk : ∀ i, 0 < k i) (β : ℝ)
    (hβ : 0 < β) {L : ℝ} (hL : 0 < L) {N : ℝ} (hN : 1 ≤ N) (ξ η : MonoRep (n + 1)) :
    |polyPhaseIntegral n h k β N ξ η - ∑ μ ∈ latticeBelow (latticeQ k) L, N ^ (-μ) *
        ∑ j ∈ Finset.range (n + 1), spectralCoeff n h k β ξ η μ j * (Real.log N) ^ j| ≤
      taylorCutoffConst n k β L ξ η * (N ^ (-L) * (1 + Real.log N) ^ n)

```

### Laplace/Grammar/TaylorTreeAsymptotic.lean
```lean
/-- The spectral sum below the cutoff `L`: `∑_{μ ∈ Λ_L} N^{-μ} ∑_{j ≤ n} A_{μ,j} (log N)^j`. -/
noncomputable def spectralSum (n : ℕ) (h k : Fin (n + 1) → ℕ) (β L : ℝ) (ξ η : MonoRep (n + 1))
    (N : ℝ) : ℝ

/-- **Headline XXVI — the polynomial Taylor tree, `IsBigO` form.** -/
theorem taylorTree_isBigO (n : ℕ) (h k : Fin (n + 1) → ℕ) (hk : ∀ i, 0 < k i) (β : ℝ)
    (hβ : 0 < β) {L : ℝ} (hL : 0 < L) (ξ η : MonoRep (n + 1)) :
    (fun N : ℝ => polyPhaseIntegral n h k β N ξ η - spectralSum n h k β L ξ η N) =O[atTop]
      fun N : ℝ => N ^ (-L) * (1 + Real.log N) ^ n

/-- `(1 + log N)^n ≤ 2^n (log N)^n` for `N ≥ e`, so the `(1+log N)^n` scale is `O((log N)^n)`. -/
theorem one_add_log_pow_isBigO (n : ℕ) :
    (fun N : ℝ => (1 + Real.log N) ^ n) =O[atTop] fun N : ℝ => (Real.log N) ^ n

/-- **The paper's form**: the remainder is `O(N^{-L} (log N)^{d-1})`. -/
theorem taylorTree_isBigO_log (n : ℕ) (h k : Fin (n + 1) → ℕ) (hk : ∀ i, 0 < k i) (β : ℝ)
    (hβ : 0 < β) {L : ℝ} (hL : 0 < L) (ξ η : MonoRep (n + 1)) :
    (fun N : ℝ => polyPhaseIntegral n h k β N ξ η - spectralSum n h k β L ξ η N) =O[atTop]
      fun N : ℝ => N ^ (-L) * (Real.log N) ^ n

/-- `(1 + log N)^n = o(N^s)` for every `s > 0`. -/
theorem one_add_log_pow_isLittleO (n : ℕ) {s : ℝ} (hs : 0 < s) :
    (fun N : ℝ => (1 + Real.log N) ^ n) =o[atTop] fun N : ℝ => N ^ s

/-- **Asymptotic expansion**: for `L' < L` the remainder is `o(N^{-L'})`. Since `L` is arbitrary,
`∑_μ N^{-μ} P_μ(log N)` is an asymptotic expansion of `Z(N)` in the scale `N^{-μ} (log N)^j`. -/
theorem taylorTree_isLittleO (n : ℕ) (h k : Fin (n + 1) → ℕ) (hk : ∀ i, 0 < k i) (β : ℝ)
    (hβ : 0 < β) {L L' : ℝ} (hL : 0 < L) (hL' : L' < L) (ξ η : MonoRep (n + 1)) :
    (fun N : ℝ => polyPhaseIntegral n h k β N ξ η - spectralSum n h k β L ξ η N) =o[atTop]
      fun N : ℝ => N ^ (-L')

```

## Numerical checks performed by the formaliser
- Headline XXIV (exact identity) in d=1, h=0, k=1, β=1, N=2, ξ = 0.3+0.5u, η = 1+u, 30 phase orders: both sides 1.191350794740, difference 2e-15.
- Headline XXV in d=1 (same data), L = 5/2, Λ_L = {0, 1/2, 1, 3/2, 2}: Z(N) − Σ N^{-μ} A_{μ,0} times N^{5/2} = 0.148, 0.154, 0.148, 0.145 at N = 10, 40, 160, 640.

## Questions
1. Is `polyPhaseIntegral` the paper's standard integral at b = 1 (with Lean's N the paper's n)? Any missing Jacobian/normalisation in `spectralCoeff` relative to the paper's C_{μ,m} (paper m = Lean j + 1)?
2. Is the high-spectrum estimate legitimate as stated (lowering τ^{μ-1} to τ^{L-1} on (0,1], the comparison |log N − log t| ≤ (1+log N)(1+|log t|), the enlargement (0,N] → (0,∞))? Are the constants really independent of N and of the monomial?
3. Is the Tonelli folding Σ_p (βB)^p/p! M_{ν,r,p}(b) = M_{ν,r,0}(b+B) correct with b the constant phase ξ(0) (signed, not |ξ(0)|) and B = ‖J‖₁?
4. Is the regrouping by `coeffAt` over `latticeBelow` sound, in particular the handling of the lattice point μ = 0 and the equivalence "entry exponent < L ⇔ ∈ latticeBelow"?
5. Does Headline XXVI faithfully express the paper's "asymptotic expansion" for polynomial data? What should the documentation say about Λ_L ⊆ Q^{-1}ℕ versus Λ(h,k), about b = 1, and about the derivative dictionary (−∂_μ)^i ∂_a^p S_μ?
6. Should-fix list before a Stage 4 (analytic ξ, η).
