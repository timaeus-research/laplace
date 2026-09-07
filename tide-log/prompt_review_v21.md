You are an independent statement-level fidelity reviewer for a Lean 4 / Mathlib formalisation of Section 4 of a paper on asymptotic expansions of "standard integrals" in singular learning theory. You reviewed Stage 3 (polynomial data) as review v20: qualified pass. This is review v21 of Stage 4 (units 241–247), which extends the polynomial theorem to analytic data given by absolutely summable coefficient families. You do not run Lean; you review the mathematics of the statements against the paper. Report: overall verdict; per-unit verdicts; a should-fix list before author hand-off; sanity checks performed.

## Paper
Z(β,n;ξ,η) = ∫_{[0,b]^d} u^h e^{-βn u^{2k} + β√n u^k ξ(u)} η(u) du. thm:TaylorTree: for ξ, η real analytic on [0,b]^d extending holomorphically to the polydisc D_R = {|z_i| < R}, R > b, there is Λ* ⊆ Λ(h,k) = ∪_i ((h_i+1)/(2k_i) + ℕ/(2k_i)) with Z ~ Σ_{μ∈Λ*} n^{-μ} P_μ(log n), deg P_μ ≤ d−1, coefficients absolutely convergent series in derivatives of ξ, η and the fluctuation function S_ν(a) = ∫₀^∞ t^{ν-1} e^{-βt+β√t a} dt. cor:standardintegralexp: Z ~ Σ_μ Σ_{m=1}^d C_{μ,m} n^{-μ}(log n)^{m-1}.

## Stage 3 (reviewed, v20) recap
Lean `n` = dimension index (d = n+1), Lean `N` = paper's n, b = 1 (unit box (0,1]^d), β > 0, k_i > 0, ξ, η POLYNOMIAL as finite monomial lists `MonoRep (n+1) := List ((Fin (n+1) → ℕ) × ℝ)` with list mass `l1 P = Σ|c|` (uncollected), `fluct P` = list without constant monomials, `eval`. `spectralCoeff n h k β ξ η μ j` = A_{μ,j} (cutoff-free, absolutely convergent), `spectralSum … L … N = Σ_{μ∈latticeBelow Q L} N^{-μ} Σ_{j≤n} A_{μ,j}(log N)^j`, Q = 2∏k_i, `taylorTree_cutoff_bound`: |polyPhaseIntegral − spectralSum| ≤ taylorCutoffConst · N^{-L}(1+log N)^n for N ≥ 1, with taylorCutoffConst = highConst + tailSeriesConst, highConst = K_k ‖η‖₁ (n+1)!Q^n M_{L,n}(ξ(0)+‖J‖₁), tailSeriesConst = K_k ‖η‖₁ (n+1)!Q^n tailConst(β, ξ(0)+‖J‖₁, 0, L, n)(4/β)⌈L⌉!(4/β)^⌈L⌉, where M_{ν,r,p}(b) = phaseLogMoment β b ν r p = ∫₀^∞ t^{ν-1}(1+|log t|)^r (√t)^p e^{-βt+βb√t} dt and tailConst β b p ν i = e^{βb²/2}(⌈ν⌉+i+p)!(4/β)^{⌈ν⌉+i+p}. `candidateExp h k μ` = μ ∈ Λ(h,k). `stabilityPrefactor n k = K_k (n+1)(n+1)!Q^n 2^n`.

## Stage 4 design (Astra #28)
Coefficient families c : (Fin d → ℕ) → ℝ with Σ|c_γ| < ∞ (`AbsSummable`), `mass c = Σ|c_γ|`, `evalF c u = Σ c_γ u^γ`; box truncations `truncList c m` = list of (γ, c_γ) for all γ_i ≤ m; Z for families = `familyPhaseIntegral`; family coefficients = limits of the polynomial coefficients of the truncations (Cauchy via a Lipschitz stability estimate); cutoff bound passes to the limit at fixed N. The claim is that this proves thm:TaylorTree/cor:standardintegralexp at b = 1 under the hypothesis "ξ, η are sums of absolutely summable power series on the closed unit cube" — which is implied by the paper's polydisc hypothesis (R > 1) via Cauchy estimates (that bridge is NOT formalised).

## Lean statements (verbatim, proofs omitted)

### Laplace/Grammar/MonoRepPerm.lean
```lean
theorem l1_perm {P Q : MonoRep d} (h : P.Perm Q) : l1 P = l1 Q

theorem eval_perm {P Q : MonoRep d} (h : P.Perm Q) (u : Fin d → ℝ) : eval P u = eval Q u

theorem mul_append_left (P Q R : MonoRep d) : mul (P ++ Q) R = mul P R ++ mul Q R

theorem mul_append_right_perm (P Q R : MonoRep d) : (mul P (Q ++ R)).Perm (mul P Q ++ mul P R)

theorem mul_perm_left {P P' : MonoRep d} (h : P.Perm P') (Q : MonoRep d) :
    (mul P Q).Perm (mul P' Q)

theorem mul_perm_right (P : MonoRep d) {Q Q' : MonoRep d} (h : Q.Perm Q') :
    (mul P Q).Perm (mul P Q')

theorem pow_perm {P P' : MonoRep d} (h : P.Perm P') : ∀ p : ℕ, (pow P p).Perm (pow P' p)
  | 0 => List.Perm.refl _
  | p + 1 => (mul_perm_left h _).trans (mul_perm_right P' (pow_perm h p))

theorem l1_pow_append_le (J Δ : MonoRep d) (p : ℕ) :
    l1 (pow (J ++ Δ) p) ≤ (l1 J + l1 Δ) ^ p

/-- **Power-difference estimate**: `pow (J ++ Δ) p ~ pow J p ++ R` with
`‖R‖₁ ≤ p ‖Δ‖₁ (‖J‖₁ + ‖Δ‖₁)^{p-1}`. -/
theorem pow_append_perm (J Δ : MonoRep d) :
    ∀ p : ℕ, ∃ R : MonoRep d, (pow (J ++ Δ) p).Perm (pow J p ++ R) ∧
      l1 R ≤ p * l1 Δ * (l1 J + l1 Δ) ^ (p - 1)
  | 0 => ⟨[], by simp [pow], by simp⟩
  | p + 1 => by
    obtain ⟨R, hR, hl⟩

/-- **Power-difference estimate**: `pow (J ++ Δ) p ~ pow J p ++ R` with
`‖R‖₁ ≤ p ‖Δ‖₁ (‖J‖₁ + ‖Δ‖₁)^{p-1}`. -/
theorem pow_append_perm (J Δ : MonoRep d) :
    ∀ p : ℕ, ∃ R : MonoRep d, (pow (J ++ Δ) p).Perm (pow J p ++ R) ∧
      l1 R ≤ p * l1 Δ * (l1 J + l1 Δ) ^ (p - 1)
  | 0 => ⟨[], by simp [pow], by simp⟩
  | p + 1 => by
    obtain ⟨R, hR, hl⟩ := pow_append_perm J Δ p
    have hB : 0 ≤ l1 J := l1_nonneg J
    have hδ : 0 ≤ l1 Δ := l1_nonneg Δ
    refine ⟨mul J R ++ mul Δ (pow (J ++ Δ) p), ?_, ?_⟩
    · calc pow (J ++ Δ) (p + 1) = mul J (pow (J ++ Δ) p) ++ mul Δ (pow (J ++ Δ) p) := by
            rw [pow, mul_append_left]
        _ ~ mul J (pow J p ++ R) ++ mul Δ (pow (J ++ Δ) p) := (mul_perm_right J hR).append_right _
        _ ~ (mul J (pow J p) ++ mul J R) ++ mul Δ (pow (J ++ Δ) p) :=
            (mul_append_right_perm J _ R).append_right _
        _ = pow J (p + 1) ++ (mul J R ++ mul Δ (pow (J ++ Δ) p)) := by
            rw [List.append_assoc]; rfl
    · rw [l1_append, l1_mul, l1_mul]
      have h1 := l1_pow_append_le J Δ p
      have hp : (p : ℝ) * l1 Δ * (l1 J + l1 Δ) ^ (p - 1) * l1 J ≤
          (p : ℝ) * l1 Δ * (l1 J + l1 Δ) ^ p := by
        rcases p with _ | p
        · simp
        · rw [Nat.add_sub_cancel]
          calc ((p + 1 : ℕ) : ℝ) * l1 Δ * (l1 J + l1 Δ) ^ p * l1 J
              ≤ ((p + 1 : ℕ) : ℝ) * l1 Δ * (l1 J + l1 Δ) ^ p * (l1 J + l1 Δ) :=
                mul_le_mul_of_nonneg_left (by linarith) (by positivity)
            _ = _ := by ring
      calc l1 J * l1 R + l1 Δ * l1 (pow (J ++ Δ) p)
          ≤ l1 J * ((p : ℝ) * l1 Δ * (l1 J + l1 Δ) ^ (p - 1)) + l1 Δ * (l1 J + l1 Δ) ^ p :=
            add_le_add (mul_le_mul_of_nonneg_left hl hB) (mul_le_mul_of_nonneg_left h1 hδ)
        _ ≤ (p : ℝ) * l1 Δ * (l1 J + l1 Δ) ^ p + l1 Δ * (l1 J + l1 Δ) ^ p := by
            refine add_le_add ?_ le_rfl
            calc l1 J * ((p : ℝ) * l1 Δ * (l1 J + l1 Δ) ^ (p - 1))
                = (p : ℝ) * l1 Δ * (l1 J + l1 Δ) ^ (p - 1) * l1 J := by ring
              _ ≤ _ := hp
        _ = ((p + 1 : ℕ) : ℝ) * l1 Δ * (l1 J + l1 Δ) ^ (p + 1 - 1) := by
            rw [Nat.add_sub_cancel]; push_cast; ring

end MonoRep

open MonoRep

/-! ### Linearity of the coefficient terms -/
theorem coeffTerm_append (n : ℕ) (h k : Fin (n + 1) → ℕ) (β a : ℝ) (p : ℕ) (μ : ℝ) (j : ℕ)
    (P Q : MonoRep (n + 1)) :
    coeffTerm n h k β a p μ j (P ++ Q) =
      coeffTerm n h k β a p μ j P + coeffTerm n h k β a p μ j Q

theorem coeffTerm_perm (n : ℕ) (h k : Fin (n + 1) → ℕ) (β a : ℝ) (p : ℕ) (μ : ℝ) (j : ℕ)
    {P Q : MonoRep (n + 1)} (hPQ : P.Perm Q) :
    coeffTerm n h k β a p μ j P = coeffTerm n h k β a p μ j Q

```

### Laplace/Grammar/CoeffStability.lean
```lean
theorem logMajorant_succ (β a ν : ℝ) (r p : ℕ) {t : ℝ} (ht : 0 < t) :
    logMajorant β a ν r (p + 1) t = logMajorant β a (ν + 1 / 2) r p t

theorem phaseLogMoment_succ (β a ν : ℝ) (r p : ℕ) :
    phaseLogMoment β a ν r (p + 1) = phaseLogMoment β a (ν + 1 / 2) r p

/-- `∑_p β^p/p! · p · B^{p-1} · M_{ν,n,p}(a) = β · M_{ν+1/2,n}(a+B)`. -/
theorem hasSum_phase_series_shift (β a B ν : ℝ) (hβ : 0 < β) (hν : 0 < ν) (hB : 0 ≤ B) (r : ℕ) :
    HasSum (fun p : ℕ => β ^ p / (p.factorial : ℝ) * ((p : ℝ) * B ^ (p - 1)) *
      phaseLogMoment β a ν r p) (β * phaseLogMoment β (a + B) (ν + 1 / 2) r 0)

/-- `|coeffTerm ((η ++ Δη)(J ++ Δ)^p) − coeffTerm (η J^p)|` is controlled by `‖Δ‖₁`, `‖Δη‖₁`. -/
theorem abs_coeffTerm_pert_le (n : ℕ) (h k : Fin (n + 1) → ℕ) (hk : ∀ i, 0 < k i) (β a : ℝ)
    (hβ : 0 < β) (p : ℕ) {μ : ℝ} (hμ : 0 < μ) (j : ℕ) (η Δη J Δ : MonoRep (n + 1)) {E B : ℝ}
    (hE : l1 η ≤ E) (hB : l1 J + l1 Δ ≤ B) :
    |coeffTerm n h k β a p μ j (mul (η ++ Δη) (pow (J ++ Δ) p)) -
        coeffTerm n h k β a p μ j (mul η (pow J p))| ≤
      (∏ i, 1 / (2 * (k i : ℝ))) * ((n + 1 : ℝ) * (((n + 1).factorial : ℝ) * (latticeQ k : ℝ) ^ n) *
        2 ^ n) * phaseLogMoment β a μ n p *
        (E * ((p : ℝ) * l1 Δ * B ^ (p - 1)) + l1 Δη * B ^ p)

/-- The `N`-free stability constant `K_k D_{n,k}`. -/
noncomputable def stabilityPrefactor (n : ℕ) (k : Fin (n + 1) → ℕ) : ℝ

/-- **Coefficient stability (Stage 4 gate).** For polynomial data with the same constant phase,
`|A_{μ,j}(ξ',η') − A_{μ,j}(ξ,η)| ≤ K_k D (E β M_{μ+1/2,n}(a+B) ‖Δ‖₁ + M_{μ,n}(a+B) ‖Δη‖₁)`. -/
theorem abs_spectralCoeff_sub_le (n : ℕ) (h k : Fin (n + 1) → ℕ) (hk : ∀ i, 0 < k i) (β : ℝ)
    (hβ : 0 < β) {μ : ℝ} (hμ : 0 < μ) (j : ℕ) (ξ ξ' η η' Δη Δ : MonoRep (n + 1))
    (hη : η'.Perm (η ++ Δη)) (hJ : (fluct ξ').Perm (fluct ξ ++ Δ)) (ha : eval ξ' 0 = eval ξ 0)
    {E B : ℝ} (hE : l1 η ≤ E) (hB : l1 (fluct ξ) + l1 Δ ≤ B) :
    |spectralCoeff n h k β ξ' η' μ j - spectralCoeff n h k β ξ η μ j| ≤
      stabilityPrefactor n k *
        (E * β * phaseLogMoment β (eval ξ 0 + B) (μ + 1 / 2) n 0 * l1 Δ +
          phaseLogMoment β (eval ξ 0 + B) μ n 0 * l1 Δη)

```

### Laplace/Grammar/CoeffFamily.lean
```lean
/-- Coefficient families: real coefficients indexed by multi-indices. -/
abbrev CoeffFamily (d : ℕ)

/-- Absolute summability `∑_γ |c_γ| < ∞`. -/
def AbsSummable (c : CoeffFamily d) : Prop

/-- The mass `∑_γ |c_γ|`. -/
noncomputable def mass (c : CoeffFamily d) : ℝ

/-- Evaluation `∑_γ c_γ u^γ`. -/
noncomputable def evalF (c : CoeffFamily d) (u : Fin d → ℝ) : ℝ

theorem mass_nonneg (c : CoeffFamily d) : 0 ≤ mass c

theorem abs_term_le {c : CoeffFamily d} {u : Fin d → ℝ} (hu : u ∈ closedCube d) (γ : Fin d → ℕ) :
    |c γ * mono γ u| ≤ |c γ|

theorem summable_term {c : CoeffFamily d} (hc : AbsSummable c) {u : Fin d → ℝ}
    (hu : u ∈ closedCube d) : Summable fun γ => c γ * mono γ u

theorem summable_abs_term {c : CoeffFamily d} (hc : AbsSummable c) {u : Fin d → ℝ}
    (hu : u ∈ closedCube d) : Summable fun γ => |c γ * mono γ u|

/-- `|eval c u| ≤ mass c` on the closed cube. -/
theorem abs_evalF_le {c : CoeffFamily d} (hc : AbsSummable c) {u : Fin d → ℝ}
    (hu : u ∈ closedCube d) : |evalF c u| ≤ mass c

/-- The box `{γ | ∀ i, γᵢ ≤ m}` of multi-indices. -/
def boxSet (d m : ℕ) : Finset (Fin d → ℕ)

theorem mem_boxSet {m : ℕ} {γ : Fin d → ℕ} : γ ∈ boxSet d m ↔ ∀ i, γ i ≤ m

theorem boxSet_mono {m m' : ℕ} (h : m ≤ m') : boxSet d m ⊆ boxSet d m'

theorem zero_mem_boxSet (m : ℕ) : (0 : Fin d → ℕ) ∈ boxSet d m

/-- The box truncation as a monomial list. -/
noncomputable def truncList (c : CoeffFamily d) (m : ℕ) : MonoRep d

theorem sum_map_toList {α : Type*} (s : Finset α) (f : α → ℝ) :
    (s.toList.map f).sum = ∑ x ∈ s, f x

theorem eval_truncList (c : CoeffFamily d) (m : ℕ) (u : Fin d → ℝ) :
    eval (truncList c m) u = ∑ γ ∈ boxSet d m, c γ * mono γ u

theorem l1_truncList (c : CoeffFamily d) (m : ℕ) :
    l1 (truncList c m) = ∑ γ ∈ boxSet d m, |c γ|

theorem l1_truncList_le_mass {c : CoeffFamily d} (hc : AbsSummable c) (m : ℕ) :
    l1 (truncList c m) ≤ mass c

/-- The truncation keeps the constant term: `eval (truncList c m) 0 = c 0`. -/
theorem eval_truncList_zero (c : CoeffFamily d) (m : ℕ) : eval (truncList c m) 0 = c 0

/-- The tail mass `∑_{γ ∉ box m} |c_γ|` (as a sum with an indicator). -/
noncomputable def tailMass (c : CoeffFamily d) (m : ℕ) : ℝ

theorem tail_term_nonneg (c : CoeffFamily d) (m : ℕ) (γ : Fin d → ℕ) :
    0 ≤ if γ ∈ boxSet d m then 0 else |c γ|

theorem tail_term_le (c : CoeffFamily d) (m : ℕ) (γ : Fin d → ℕ) :
    (if γ ∈ boxSet d m then 0 else |c γ|) ≤ |c γ|

theorem summable_tail_term {c : CoeffFamily d} (hc : AbsSummable c) (m : ℕ) :
    Summable fun γ => if γ ∈ boxSet d m then 0 else |c γ|

theorem tailMass_nonneg (c : CoeffFamily d) (m : ℕ) : 0 ≤ tailMass c m

/-- Every multi-index is eventually in the box. -/
theorem eventually_mem_boxSet (γ : Fin d → ℕ) : ∀ᶠ m in atTop, γ ∈ boxSet d m

/-- **The tail mass tends to zero.** -/
theorem tailMass_tendsto_zero {c : CoeffFamily d} (hc : AbsSummable c) :
    Tendsto (tailMass c) atTop (𝓝 0)

/-- Finite sums outside the box are bounded by the tail mass. -/
theorem sum_abs_le_tailMass {c : CoeffFamily d} (hc : AbsSummable c) (m : ℕ)
    (S : Finset (Fin d → ℕ)) (hS : ∀ γ ∈ S, γ ∉ boxSet d m) :
    ∑ γ ∈ S, |c γ| ≤ tailMass c m

/-- The new monomials between levels `m ≤ m'`. -/
noncomputable def restList (c : CoeffFamily d) (m m' : ℕ) : MonoRep d

theorem l1_restList (c : CoeffFamily d) (m m' : ℕ) :
    l1 (restList c m m') = ∑ γ ∈ (boxSet d m').filter (fun γ => γ ∉ boxSet d m), |c γ|

theorem l1_restList_le_tailMass {c : CoeffFamily d} (hc : AbsSummable c) (m m' : ℕ) :
    l1 (restList c m m') ≤ tailMass c m

/-- `truncList c m' ~ truncList c m ++ restList c m m'` for `m ≤ m'`. -/
theorem truncList_perm (c : CoeffFamily d) {m m' : ℕ} (h : m ≤ m') :
    (truncList c m').Perm (truncList c m ++ restList c m m')

/-- The fluctuation parts of successive truncations differ by an appended list of mass at most
the tail mass. -/
theorem fluct_truncList_perm (c : CoeffFamily d) {m m' : ℕ} (h : m ≤ m') :
    (fluct (truncList c m')).Perm (fluct (truncList c m) ++ fluct (restList c m m'))

/-- `|eval c u − eval (truncList c m) u| ≤ tailMass c m` on the closed cube. -/
theorem abs_evalF_sub_truncList_le {c : CoeffFamily d} (hc : AbsSummable c) (m : ℕ)
    {u : Fin d → ℝ} (hu : u ∈ closedCube d) :
    |evalF c u - eval (truncList c m) u| ≤ tailMass c m

```

### Laplace/Grammar/FamilyPhaseIntegral.lean
```lean
/-- The standard integral for coefficient-family data. -/
noncomputable def familyPhaseIntegral (n : ℕ) (h k : Fin (n + 1) → ℕ) (β N : ℝ)
    (cξ cη : CoeffFamily (n + 1)) : ℝ

/-- Pointwise convergence of the truncations on the closed cube. -/
theorem tendsto_eval_truncList {d : ℕ} {c : CoeffFamily d} (hc : AbsSummable c) {u : Fin d → ℝ}
    (hu : u ∈ closedCube d) :
    Tendsto (fun m => eval (truncList c m) u) atTop (𝓝 (evalF c u))

/-- **The polynomial standard integrals of the truncations converge to the family integral**
(fixed `N ≥ 0`, `β ≥ 0`). -/
theorem tendsto_polyPhaseIntegral_truncList (n : ℕ) (h k : Fin (n + 1) → ℕ) (β : ℝ) (hβ : 0 ≤ β)
    {N : ℝ} (hN : 0 ≤ N) {cξ cη : CoeffFamily (n + 1)} (hξ : AbsSummable cξ) (hη : AbsSummable cη) :
    Tendsto (fun m => polyPhaseIntegral n h k β N (truncList cξ m) (truncList cη m)) atTop
      (𝓝 (familyPhaseIntegral n h k β N cξ cη))

```

### Laplace/Grammar/FamilySpectralCoeff.lean
```lean
theorem boxSet_indicator_le {c : CoeffFamily d} {m m' : ℕ} (h : m ≤ m') (γ : Fin d → ℕ) :
    (if γ ∈ boxSet d m' then 0 else |c γ|) ≤ if γ ∈ boxSet d m then 0 else |c γ|

/-- The tail mass is antitone in the level. -/
theorem tailMass_anti {c : CoeffFamily d} (hc : AbsSummable c) {m m' : ℕ} (h : m ≤ m') :
    tailMass c m' ≤ tailMass c m

/-- The spectral coefficient of the level-`m` truncations. -/
noncomputable def truncCoeff (n : ℕ) (h k : Fin (n + 1) → ℕ) (β : ℝ) (cξ cη : CoeffFamily (n + 1))
    (μ : ℝ) (j : ℕ) (m : ℕ) : ℝ

/-- The stability constants of the truncation sequence. -/
noncomputable def truncStabConst₁ (n : ℕ) (k : Fin (n + 1) → ℕ) (β : ℝ)
    (cξ cη : CoeffFamily (n + 1))
    (μ : ℝ) : ℝ

noncomputable def truncStabConst₂ (n : ℕ) (k : Fin (n + 1) → ℕ) (β : ℝ) (cξ : CoeffFamily (n + 1))
    (μ : ℝ) : ℝ

theorem stabilityPrefactor_nonneg (n : ℕ) (k : Fin (n + 1) → ℕ) : 0 ≤ stabilityPrefactor n k

/-- **Consecutive truncation coefficients are close**: for `m ≤ m'` and `μ > 0`,
`|A(m') − A(m)| ≤ C₁ tailMass cξ m + C₂ tailMass cη m`. -/
theorem abs_truncCoeff_sub_le (n : ℕ) (h k : Fin (n + 1) → ℕ) (hk : ∀ i, 0 < k i) (β : ℝ)
    (hβ : 0 < β) {cξ cη : CoeffFamily (n + 1)} (hξ : AbsSummable cξ) (hη : AbsSummable cη) {μ : ℝ}
    (hμ : 0 < μ) (j : ℕ) {m m' : ℕ} (hmm : m ≤ m') :
    |truncCoeff n h k β cξ cη μ j m' - truncCoeff n h k β cξ cη μ j m| ≤
      truncStabConst₁ n k β cξ cη μ * tailMass cξ m +
        truncStabConst₂ n k β cξ μ * tailMass cη m

/-- The truncation coefficients form a Cauchy sequence. -/
theorem cauchySeq_truncCoeff (n : ℕ) (h k : Fin (n + 1) → ℕ) (hk : ∀ i, 0 < k i) (β : ℝ)
    (hβ : 0 < β) {cξ cη : CoeffFamily (n + 1)} (hξ : AbsSummable cξ) (hη : AbsSummable cη) (μ : ℝ)
    (j : ℕ) : CauchySeq (truncCoeff n h k β cξ cη μ j)

/-- **The family spectral coefficient** `A_{μ,j}(cξ, cη)`: the limit of the truncation
coefficients. -/
noncomputable def familySpectralCoeff (n : ℕ) (h k : Fin (n + 1) → ℕ) (β : ℝ)
    (cξ cη : CoeffFamily (n + 1)) (μ : ℝ) (j : ℕ) : ℝ

/-- **Convergence of the truncation coefficients** to the family coefficient. -/
theorem tendsto_truncCoeff (n : ℕ) (h k : Fin (n + 1) → ℕ) (hk : ∀ i, 0 < k i) (β : ℝ) (hβ : 0 < β)
    {cξ cη : CoeffFamily (n + 1)} (hξ : AbsSummable cξ) (hη : AbsSummable cη) (μ : ℝ) (j : ℕ) :
    Tendsto (truncCoeff n h k β cξ cη μ j) atTop (𝓝 (familySpectralCoeff n h k β cξ cη μ j))

/-- The family coefficients vanish off the paper's candidate set `Λ(h,k)`. -/
theorem familySpectralCoeff_eq_zero_of_not_candidate (n : ℕ) (h k : Fin (n + 1) → ℕ)
    (hk : ∀ i, 0 < k i) (β : ℝ) (hβ : 0 < β) {cξ cη : CoeffFamily (n + 1)} (hξ : AbsSummable cξ)
    (hη : AbsSummable cη) {μ : ℝ} (hμ : ¬ candidateExp h k μ) (j : ℕ) :
    familySpectralCoeff n h k β cξ cη μ j = 0

/-- The spectral sum of coefficient-family data below the cutoff `L`. -/
noncomputable def familySpectralSum (n : ℕ) (h k : Fin (n + 1) → ℕ) (β L : ℝ)
    (cξ cη : CoeffFamily (n + 1)) (N : ℝ) : ℝ

/-- **The spectral sums of the truncations converge** to the family spectral sum. -/
theorem tendsto_spectralSum_truncList (n : ℕ) (h k : Fin (n + 1) → ℕ) (hk : ∀ i, 0 < k i) (β : ℝ)
    (hβ : 0 < β) (L : ℝ) {cξ cη : CoeffFamily (n + 1)} (hξ : AbsSummable cξ) (hη : AbsSummable cη)
    (N : ℝ) :
    Tendsto (fun m => spectralSum n h k β L (truncList cξ m) (truncList cη m) N) atTop
      (𝓝 (familySpectralSum n h k β L cξ cη N))

```

### Laplace/Grammar/UniformCutoffConst.lean
```lean
theorem logMajorant_mono (β : ℝ) (hβ : 0 < β) {b b' : ℝ} (hbb : b ≤ b') (ν : ℝ) (r p : ℕ) {t : ℝ}
    (ht : 0 ≤ t) : logMajorant β b ν r p t ≤ logMajorant β b' ν r p t

/-- `M_{ν,r,p}(b)` is increasing in `b`. -/
theorem phaseLogMoment_mono (β : ℝ) (hβ : 0 < β) {b b' : ℝ} (hbb : b ≤ b') {ν : ℝ} (hν : 0 < ν)
    (r p : ℕ) : phaseLogMoment β b ν r p ≤ phaseLogMoment β b' ν r p

/-- `tailConst β b p ν i` is increasing in `|b|`. -/
theorem tailConst_mono (β : ℝ) (hβ : 0 < β) {b b' : ℝ} (hbb : |b| ≤ |b'|) (p : ℕ) (ν : ℝ)
    (i : ℕ) : tailConst β b p ν i ≤ tailConst β b' p ν i

/-- The uniform cutoff constant: `highConst + tailSeriesConst` with `‖η‖₁ → E` and
`ξ(0) + ‖J‖₁ → |a| + B`. -/
noncomputable def cutoffBound (n : ℕ) (k : Fin (n + 1) → ℕ) (β L a E B : ℝ) : ℝ

/-- The polynomial cutoff constant is at most the uniform bound. -/
theorem taylorCutoffConst_le (n : ℕ) (k : Fin (n + 1) → ℕ) (β : ℝ) (hβ : 0 < β) {L : ℝ}
    (hL : 0 < L) (ξ η : MonoRep (n + 1)) {a E B : ℝ} (ha : eval ξ 0 = a) (hE : l1 η ≤ E)
    (hB : l1 (fluct ξ) ≤ B) :
    taylorCutoffConst n k β L ξ η ≤ cutoffBound n k β L a E B

/-- **Headline XXV with a uniform constant**: for polynomial data with `ξ(0) = a`, `‖η‖₁ ≤ E`,
`‖J‖₁ ≤ B`, the remainder is at most `cutoffBound n k β L a E B · N^{-L}(1+log N)^n`. -/
theorem taylorTree_cutoff_bound_uniform (n : ℕ) (h k : Fin (n + 1) → ℕ) (hk : ∀ i, 0 < k i)
    (β : ℝ) (hβ : 0 < β) {L : ℝ} (hL : 0 < L) {N : ℝ} (hN : 1 ≤ N) (ξ η : MonoRep (n + 1))
    {a E B : ℝ} (ha : eval ξ 0 = a) (hE : l1 η ≤ E) (hB : l1 (fluct ξ) ≤ B) :
    |polyPhaseIntegral n h k β N ξ η - spectralSum n h k β L ξ η N| ≤
      cutoffBound n k β L a E B * (N ^ (-L) * (1 + Real.log N) ^ n)

```

### Laplace/Grammar/FamilyTaylorTree.lean
```lean
/-- **Headline XXVII — the Taylor tree for coefficient-family data, quantitative form.** -/
theorem familyTaylorTree_cutoff_bound (n : ℕ) (h k : Fin (n + 1) → ℕ) (hk : ∀ i, 0 < k i) (β : ℝ)
    (hβ : 0 < β) {L : ℝ} (hL : 0 < L) {N : ℝ} (hN : 1 ≤ N) {cξ cη : CoeffFamily (n + 1)}
    (hξ : AbsSummable cξ) (hη : AbsSummable cη) :
    |familyPhaseIntegral n h k β N cξ cη - familySpectralSum n h k β L cξ cη N| ≤
      cutoffBound n k β L (cξ 0) (mass cη) (mass cξ) * (N ^ (-L) * (1 + Real.log N) ^ n)

/-- **Headline XXVII, `IsBigO` form.** -/
theorem familyTaylorTree_isBigO (n : ℕ) (h k : Fin (n + 1) → ℕ) (hk : ∀ i, 0 < k i) (β : ℝ)
    (hβ : 0 < β) {L : ℝ} (hL : 0 < L) {cξ cη : CoeffFamily (n + 1)} (hξ : AbsSummable cξ)
    (hη : AbsSummable cη) :
    (fun N : ℝ => familyPhaseIntegral n h k β N cξ cη - familySpectralSum n h k β L cξ cη N)
      =O[atTop] fun N : ℝ => N ^ (-L) * (1 + Real.log N) ^ n

/-- The paper's form `O(N^{-L} (log N)^{d-1})`. -/
theorem familyTaylorTree_isBigO_log (n : ℕ) (h k : Fin (n + 1) → ℕ) (hk : ∀ i, 0 < k i) (β : ℝ)
    (hβ : 0 < β) {L : ℝ} (hL : 0 < L) {cξ cη : CoeffFamily (n + 1)} (hξ : AbsSummable cξ)
    (hη : AbsSummable cη) :
    (fun N : ℝ => familyPhaseIntegral n h k β N cξ cη - familySpectralSum n h k β L cξ cη N)
      =O[atTop] fun N : ℝ => N ^ (-L) * (Real.log N) ^ n

/-- `N^{-L}(1+log N)^n = o(N^{-L'})` for `L' < L`. -/
theorem rpow_neg_mul_log_pow_isLittleO (n : ℕ) {L L' : ℝ} (hL' : L' < L) :
    (fun N : ℝ => N ^ (-L) * (1 + Real.log N) ^ n) =o[atTop] fun N : ℝ => N ^ (-L')

/-- **Asymptotic expansion**: the remainder below the cutoff `L` is `o(N^{-L'})` for every
`L' < L`. -/
theorem familyTaylorTree_isLittleO (n : ℕ) (h k : Fin (n + 1) → ℕ) (hk : ∀ i, 0 < k i) (β : ℝ)
    (hβ : 0 < β) {L L' : ℝ} (hL : 0 < L) (hL' : L' < L) {cξ cη : CoeffFamily (n + 1)}
    (hξ : AbsSummable cξ) (hη : AbsSummable cη) :
    (fun N : ℝ => familyPhaseIntegral n h k β N cξ cη - familySpectralSum n h k β L cξ cη N)
      =o[atTop] fun N : ℝ => N ^ (-L')

/-- The family spectral sum restricted to the paper's candidate set `Λ(h,k) ∩ [0,L)`. -/
theorem familySpectralSum_eq_candidate (n : ℕ) (h k : Fin (n + 1) → ℕ) (hk : ∀ i, 0 < k i) (β : ℝ)
    (hβ : 0 < β) (L : ℝ) {cξ cη : CoeffFamily (n + 1)} (hξ : AbsSummable cξ) (hη : AbsSummable cη)
    (N : ℝ) :
    familySpectralSum n h k β L cξ cη N =
      ∑ μ ∈ (latticeBelow (latticeQ k) L).filter (candidateExp h k), N ^ (-μ) *
        ∑ j ∈ Finset.range (n + 1), familySpectralCoeff n h k β cξ cη μ j * (Real.log N) ^ j

/-- **Headline XXVII over the paper's candidate set.** -/
theorem familyTaylorTree_isBigO_candidate (n : ℕ) (h k : Fin (n + 1) → ℕ) (hk : ∀ i, 0 < k i)
    (β : ℝ) (hβ : 0 < β) {L : ℝ} (hL : 0 < L) {cξ cη : CoeffFamily (n + 1)} (hξ : AbsSummable cξ)
    (hη : AbsSummable cη) :
    (fun N : ℝ => familyPhaseIntegral n h k β N cξ cη -
      ∑ μ ∈ (latticeBelow (latticeQ k) L).filter (candidateExp h k), N ^ (-μ) *
        ∑ j ∈ Finset.range (n + 1), familySpectralCoeff n h k β cξ cη μ j * (Real.log N) ^ j)
      =O[atTop] fun N : ℝ => N ^ (-L) * (1 + Real.log N) ^ n

```

## Numerical check performed by the formaliser
d=1, h=0, k=1, β=1, ξ(u) = 0.3 e^{u/2} (c_γ = 0.3/(2^γ γ!)), η(u) = 1/(1−u/3) (c_γ = 3^{-γ}), L = 5/2, coefficients computed from the definition (truncation at degree 24, 40 phase orders): (Z(N) − Σ_{m<5} N^{-m/2} A_{m/2,0}) × N^{5/2} = 0.0598, 0.0574, 0.0542, 0.0527 at N = 10, 40, 160, 640.

## Questions
1. Is the limiting definition `familySpectralCoeff = limUnder atTop (truncCoeff …)` a faithful rendering of the paper's coefficients ("absolutely convergent series" in the Taylor coefficients of ξ, η)? Is anything lost by defining A as a limit rather than an explicit series over monomials? Should an explicit series formula over (p, γ) be added (it would need a convolution of infinite families)?
2. Is the stability estimate (u242) correctly stated, including the shift M_{ν,n,p+1} = M_{ν+1/2,n,p} and the bound with B ≥ ‖J‖₁ + ‖Δ‖₁? Is the hypothesis "same constant phase ξ'(0) = ξ(0)" legitimately satisfied by box truncations?
3. Is passing to the limit at fixed N (le_of_tendsto') with the uniform constant sound, and is `cutoffBound` correctly monotone (M in b, tailConst in |b|; the |a| in |a|+B)?
4. Does the hypothesis `AbsSummable` (Σ|c_γ| < ∞, unweighted, at b = 1) correctly capture the paper's hypothesis at b = 1? State precisely what the Cauchy-estimate bridge would have to prove.
5. Any statement that would mislead the authors; wording for the hand-off (what is and is not proved).
6. Should-fix list.
