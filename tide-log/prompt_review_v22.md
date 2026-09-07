You are an independent statement-level fidelity reviewer for a Lean 4 / Mathlib formalisation of Section 4 of a paper on asymptotic expansions of standard integrals Z(β,n;ξ,η) = ∫_{[0,b]^d} u^h e^{-βn u^{2k} + β√n u^k ξ(u)} η(u) du (thm:TaylorTree / cor:standardintegralexp). You reviewed Stage 3 (v20, polynomial data) and Stage 4 (v21, coefficient families; qualified pass with qualifications: (i) analytic bridge not formalised, (ii) family coefficients only limits, not identified with the paper's explicit series, (iii) derivative dictionary interpretation only). This is review v22 of units 250–254, which address (ii) and half of (iii). You do not run Lean. Report: overall verdict; per-unit verdicts; should-fix list; whether qualification (ii) is now closed and how to word (iii); sanity checks.

## Recap of conventions
Lean `n` = dimension index (d = n+1); Lean `N` = paper's sample size; `CoeffFamily d := (Fin d → ℕ) → ℝ`, `AbsSummable c := Summable (|c ·|)`, `mass c = Σ|c_γ|`, `evalF c u = Σ c_γ u^γ`; `truncList c m` = monomial list of the coefficients with γ_i ≤ m (a `MonoRep`), `truncFamily c m` = c restricted to the box, `fluctFamily c` = c with c_0 removed (the paper's J = ξ − ξ(0)); `spectralCoeff` = Stage-3 polynomial coefficient A_{μ,j}(ξ,η) = Σ_p β^p/p! coeffTerm_p with coeffTerm_p(P) = K_k Σ_{(γ,c)∈P} c Σ_{q=j}^{n} coeffAt(ρ_{h+γ},μ,q) C(q,j) fluctMoment β a p μ (q−j), a = ξ(0), `fluctMoment β a p μ i = ∫₀^∞ t^{μ-1}(−log t)^i (√t)^p e^{-βt+β√t a} dt`; `truncCoeff … m = spectralCoeff (truncList cξ m) (truncList cη m)`; `familySpectralCoeff = limUnder atTop truncCoeff` (Stage 4, u245); `phaseLogMoment β a μ n p = M_{μ,n,p}(a) = ∫₀^∞ t^{μ-1}(1+|log t|)^n(√t)^p e^{-βt+βa√t}`; `kernelBudget n k = D = (n+1)(n+1)!Q^n 2^n`, Q = 2∏k_i.

## The paper's coefficient description (proof of thm:TaylorTree)
ξ(u) = ξ(0) + Σ_{|γ|≥1} (∂^γ ξ(0)/γ!) u^γ; (ξ(u) − ξ(0))^p = Σ_{|n|≥p} ξ_{n,p} u^n with ξ_{n,p} = Σ_{γ^{(1)}+…+γ^{(p)} = n, |γ^{(j)}|≥1} Π ∂^{γ^{(i)}}ξ(0)/γ^{(i)}! (eq:flucttreeterms); η(u) = Σ_m (η_m/m!) u^m; Z = Σ_p Σ_m Σ_{|n|≥p} ξ_{n,p} (η_m/m!) β^p/p! ∫ u^{h+m+n} (√n u^k)^p e^{…}; coefficients "absolutely convergent series expressed as derivatives of ξ, η and the fluctuation function S_ν(a) = ∫₀^∞ t^{ν-1}e^{-βt+β√t a}dt"; the coefficient contains β^p ∫₀^∞ t^{ν+p/2-1}(−log t)^{j-m} e^{-βt+β√t ξ(0)} dt = (−∂_ν)^{j-m} ∂^p S_ν(ξ(0)) = (−∂_ν)^{j-m} S_{ν+p/2}(ξ(0)).

## Lean statements (verbatim, proofs omitted)

### Laplace/Grammar/FluctuationDerivative.lean
```lean
/-- The fluctuation function `S_μ(a) = ∫₀^∞ t^{μ-1} e^{-βt+β√t a} dt`
(`fluctMoment` at `p = i = 0`). -/
noncomputable def fluctuationFn (β μ a : ℝ) : ℝ

theorem phaseKernel_eq_exp (β a : ℝ) (p : ℕ) (t : ℝ) :
    phaseKernel β a p t = Real.sqrt t ^ p * Real.exp (-(β * t) + β * Real.sqrt t * a)

/-- `∂_a phaseKernel β a p t = β √t · phaseKernel β a p t`. -/
theorem hasDerivAt_phaseKernel (β : ℝ) (p : ℕ) (t a : ℝ) :
    HasDerivAt (fun a => phaseKernel β a p t) (β * Real.sqrt t * phaseKernel β a p t) a

/-- The integrand of `fluctMoment` in the phase parameter. -/
noncomputable def fluctIntegrand (β : ℝ) (p : ℕ) (μ : ℝ) (i : ℕ) (a t : ℝ) : ℝ

theorem fluctIntegrand_succ (β : ℝ) (p : ℕ) (μ : ℝ) (i : ℕ) (a t : ℝ) :
    β * Real.sqrt t * fluctIntegrand β p μ i a t = β * fluctIntegrand β (p + 1) μ i a t

/-- Local domination: for `|a' - a| < 1` and `t > 0`,
`|β √t · fluctIntegrand a' t| ≤ β · logMajorant β (|a|+1) μ i (p+1) t`. -/
theorem abs_deriv_fluctIntegrand_le (β : ℝ) (hβ : 0 < β) (p : ℕ) (μ : ℝ) (i : ℕ) {a a' : ℝ}
    (ha : a' ∈ Metric.ball a 1) {t : ℝ} (ht : 0 < t) :
    ‖β * Real.sqrt t * fluctIntegrand β p μ i a' t‖ ≤
      β * logMajorant β (|a| + 1) μ i (p + 1) t

theorem continuous_fluctIntegrand_a (β : ℝ) (p : ℕ) (μ : ℝ) (i : ℕ) (a : ℝ) :
    ContinuousOn (fluctIntegrand β p μ i a) (Ioi 0)

/-- **`∂_a fluctMoment = β · fluctMoment` at the next phase order.** -/
theorem hasDerivAt_fluctMoment (β : ℝ) (hβ : 0 < β) (p : ℕ) {μ : ℝ} (hμ : 0 < μ) (i : ℕ) (a : ℝ) :
    HasDerivAt (fun a => fluctMoment β a p μ i) (β * fluctMoment β a (p + 1) μ i) a

/-- **Iterated derivatives**: `∂_a^p fluctMoment(·, q) = β^p fluctMoment(·, p+q)`. -/
theorem iteratedDeriv_fluctMoment (β : ℝ) (hβ : 0 < β) {μ : ℝ} (hμ : 0 < μ) (i : ℕ) :
    ∀ p q : ℕ, iteratedDeriv p (fun a => fluctMoment β a q μ i) =
      fun a => β ^ p * fluctMoment β a (p + q) μ i
  | 0, q => by simp
  | p + 1, q => by
    rw [iteratedDeriv_succ, iteratedDeriv_fluctMoment β hβ hμ i p q]
    funext a
    have

/-- **The paper's dictionary**: `∂_a^p S_μ(a) = β^p ∫₀^∞ t^{μ-1}(√t)^p e^{-βt+β√t a} dt`, i.e.
`β^p · fluctMoment β a p μ 0 = ∂_a^p S_μ(a)`. -/
theorem iteratedDeriv_fluctuationFn (β : ℝ) (hβ : 0 < β) {μ : ℝ} (hμ : 0 < μ) (p : ℕ) (a : ℝ) :
    iteratedDeriv p (fluctuationFn β μ) a = β ^ p * fluctMoment β a p μ 0

```

### Laplace/Grammar/CoeffConv.lean
```lean
/-- Pairs `(α, δ)` of multi-indices ↔ `⟨γ, α⟩` with `α ≤ γ`, via `γ = α + δ`. -/
def pairEquiv (d : ℕ) :
    (Fin d → ℕ) × (Fin d → ℕ) ≃ Σ γ : Fin d → ℕ, ↥(Finset.Iic γ) where
  toFun p

/-- The Cauchy product `(c * e)_γ = ∑_{α ≤ γ} c_α e_{γ-α}`. -/
noncomputable def conv (c e : CoeffFamily d) : CoeffFamily d

/-- The double series over pairs, regrouped along `γ = α + δ`. -/
theorem hasSum_conv_mono {c e : CoeffFamily d} (hc : AbsSummable c) (he : AbsSummable e)
    {u : Fin d → ℝ} (hu : u ∈ closedCube d) :
    HasSum (fun γ => conv c e γ * mono γ u) (evalF c u * evalF e u)

/-- **`evalF (conv c e) = evalF c · evalF e`** on the closed cube. -/
theorem evalF_conv {c e : CoeffFamily d} (hc : AbsSummable c) (he : AbsSummable e)
    {u : Fin d → ℝ} (hu : u ∈ closedCube d) :
    evalF (conv c e) u = evalF c u * evalF e u

theorem one_mem_closedCube (d : ℕ) : (fun _ => (1 : ℝ)) ∈ closedCube d

theorem mono_one (γ : Fin d → ℕ) : mono γ (fun _ => (1 : ℝ)) = 1

/-- The absolute family `|c|` is absolutely summable with the same mass. -/
theorem absFamily_summable {c : CoeffFamily d} (hc : AbsSummable c) :
    AbsSummable fun γ => |c γ|

theorem evalF_absFamily_one {c : CoeffFamily d} : evalF (fun γ => |c γ|) (fun _ => 1) = mass c

theorem abs_conv_le (c e : CoeffFamily d) (γ : Fin d → ℕ) :
    |conv c e γ| ≤ conv (fun γ => |c γ|) (fun γ => |e γ|) γ

/-- The convolution of absolutely summable families is absolutely summable. -/
theorem AbsSummable.conv {c e : CoeffFamily d} (hc : AbsSummable c) (he : AbsSummable e) :
    AbsSummable (conv c e)

/-- **`mass (conv c e) ≤ mass c · mass e`.** -/
theorem mass_conv_le {c e : CoeffFamily d} (hc : AbsSummable c) (he : AbsSummable e) :
    mass (conv c e) ≤ mass c * mass e

```

### Laplace/Grammar/CoeffFnBridge.lean
```lean
/-- Iterated Cauchy product `c^{*p}` (with `c^{*0} = δ_0`). -/
noncomputable def convPow (c : CoeffFamily d) : ℕ → CoeffFamily d
  | 0 => fun γ => if γ = 0 then 1 else 0
  | p + 1 => conv c (convPow c p)

end CoeffFamily

namespace MonoRep

variable {d : ℕ}

open Classical in
/-- The collected coefficient of `u^γ` in a monomial list. -/
noncomputable def coeffFn (P : MonoRep d) : CoeffFamily d

@[simp] theorem coeffFn_nil (γ : Fin d → ℕ) : coeffFn ([] : MonoRep d) γ = 0

theorem coeffFn_cons (s : (Fin d → ℕ) × ℝ) (P : MonoRep d) (γ : Fin d → ℕ) :
    coeffFn (s :: P) γ = (if s.1 = γ then s.2 else 0) + coeffFn P γ

theorem coeffFn_append (P Q : MonoRep d) (γ : Fin d → ℕ) :
    coeffFn (P ++ Q) γ = coeffFn P γ + coeffFn Q γ

theorem coeffFn_perm {P Q : MonoRep d} (h : P.Perm Q) (γ : Fin d → ℕ) :
    coeffFn P γ = coeffFn Q γ

/-- The exponents occurring in a list. -/
def exps (P : MonoRep d) : Finset (Fin d → ℕ)

theorem coeffFn_eq_zero_of_notMem (P : MonoRep d) {γ : Fin d → ℕ} (hγ : γ ∉ exps P) :
    coeffFn P γ = 0

/-- A finite-support family is absolutely summable; the collected family in particular. -/
theorem summable_of_support_subset {c : CoeffFamily d} {S : Finset (Fin d → ℕ)}
    (hS : ∀ γ, γ ∉ S → c γ = 0) : Summable fun γ => |c γ|

theorem tsum_eq_sum_of_support_subset {c : CoeffFamily d} {S : Finset (Fin d → ℕ)}
    (hS : ∀ γ, γ ∉ S → c γ = 0) (f : (Fin d → ℕ) → ℝ) :
    ∑' γ, c γ * f γ = ∑ γ ∈ S, c γ * f γ

theorem absSummable_coeffFn (P : MonoRep d) : AbsSummable (coeffFn P)

/-- Any list sum `∑_{(γ,c) ∈ P} c · f γ` is the sum of the collected family against `f`. -/
theorem sum_map_eq_tsum_coeffFn (P : MonoRep d) (f : (Fin d → ℕ) → ℝ) :
    (P.map fun s => s.2 * f s.1).sum = ∑' γ, coeffFn P γ * f γ

theorem evalF_coeffFn (P : MonoRep d) (u : Fin d → ℝ) : evalF (coeffFn P) u = eval P u

theorem mass_coeffFn_le (P : MonoRep d) : mass (coeffFn P) ≤ l1 P

/-- The shifted copy of `Q` collects to `s.2 · coeffFn Q (γ - s.1)` when `s.1 ≤ γ`. -/
theorem coeffFn_map_shift (s : (Fin d → ℕ) × ℝ) (Q : MonoRep d) (γ : Fin d → ℕ) :
    coeffFn (Q.map fun t => (s.1 + t.1, s.2 * t.2)) γ =
      if s.1 ≤ γ then s.2 * coeffFn Q (γ - s.1) else 0

/-- The list product collects to the Cauchy product. -/
theorem coeffFn_mul (P Q : MonoRep d) (γ : Fin d → ℕ) :
    coeffFn (mul P Q) γ = CoeffFamily.conv (coeffFn P) (coeffFn Q) γ

theorem coeffFn_pow (P : MonoRep d) : ∀ p : ℕ, coeffFn (pow P p) = CoeffFamily.convPow (coeffFn P) p
  | 0 => by
    funext γ
    simp only [pow, CoeffFamily.convPow, coeffFn_cons, coeffFn_nil, add_zero]
    by_cases h : γ = 0
    · subst h; simp
    · rw [if_neg (Ne.symm h), if_neg h]
  | p + 1 => by
    funext γ
    rw [pow, coeffFn_mul, coeffFn_pow P p]
    rfl

end MonoRep

end Laplace.Grammar


```

### Laplace/Grammar/CoeffKernel.lean
```lean
/-- The monomial kernel
`S_p(μ,j;γ) = ∑_{q=j}^{n} coeffAt(ρ_{h+γ},μ,q) C(q,j) fluctMoment_p(μ,q-j)`. -/
noncomputable def kernelS (n : ℕ) (h k : Fin (n + 1) → ℕ) (β a : ℝ) (p : ℕ) (μ : ℝ) (j : ℕ)
    (γ : Fin (n + 1) → ℕ) : ℝ

/-- The uniform budget `D_{n,k} = (n+1)(n+1)! Q^n 2^n`. -/
noncomputable def kernelBudget (n : ℕ) (k : Fin (n + 1) → ℕ) : ℝ

theorem kernelBudget_nonneg (n : ℕ) (k : Fin (n + 1) → ℕ) : 0 ≤ kernelBudget n k

/-- `|S_p(μ,j;γ)| ≤ D M_{μ,n,p}(a)`, uniformly in the monomial `γ`. -/
theorem abs_kernelS_le (n : ℕ) (h k : Fin (n + 1) → ℕ) (hk : ∀ i, 0 < k i) (β a : ℝ) (hβ : 0 < β)
    (p : ℕ) {μ : ℝ} (hμ : 0 < μ) (j : ℕ) (γ : Fin (n + 1) → ℕ) :
    |kernelS n h k β a p μ j γ| ≤ kernelBudget n k * phaseLogMoment β a μ n p

/-- `T_p(f) = K_k ∑_γ f_γ S_p(μ,j;γ)`. -/
noncomputable def kernelFunctional (n : ℕ) (h k : Fin (n + 1) → ℕ) (β a : ℝ) (p : ℕ) (μ : ℝ)
    (j : ℕ) (f : CoeffFamily (n + 1)) : ℝ

/-- The Stage 3 coefficient term is the kernel functional of the collected coefficients. -/
theorem coeffTerm_eq_kernelFunctional (n : ℕ) (h k : Fin (n + 1) → ℕ) (β a : ℝ) (p : ℕ) (μ : ℝ)
    (j : ℕ) (P : MonoRep (n + 1)) :
    coeffTerm n h k β a p μ j P = kernelFunctional n h k β a p μ j (coeffFn P)

theorem summable_kernel_term (n : ℕ) (h k : Fin (n + 1) → ℕ) (hk : ∀ i, 0 < k i) (β a : ℝ)
    (hβ : 0 < β) (p : ℕ) {μ : ℝ} (hμ : 0 < μ) (j : ℕ) {f : CoeffFamily (n + 1)}
    (hf : AbsSummable f) :
    Summable fun γ => |f γ * kernelS n h k β a p μ j γ|

/-- **`ℓ¹`-continuity of the kernel functional**: `|T_p f| ≤ K_k D M_{μ,n,p}(a) mass f`. -/
theorem abs_kernelFunctional_le (n : ℕ) (h k : Fin (n + 1) → ℕ) (hk : ∀ i, 0 < k i) (β a : ℝ)
    (hβ : 0 < β) (p : ℕ) {μ : ℝ} (hμ : 0 < μ) (j : ℕ) {f : CoeffFamily (n + 1)}
    (hf : AbsSummable f) :
    |kernelFunctional n h k β a p μ j f| ≤
      (∏ i, 1 / (2 * (k i : ℝ))) * kernelBudget n k * phaseLogMoment β a μ n p * mass f

/-- Linearity of the kernel functional in the family (difference form). -/
theorem kernelFunctional_sub (n : ℕ) (h k : Fin (n + 1) → ℕ) (hk : ∀ i, 0 < k i) (β a : ℝ)
    (hβ : 0 < β) (p : ℕ) {μ : ℝ} (hμ : 0 < μ) (j : ℕ) {f g : CoeffFamily (n + 1)}
    (hf : AbsSummable f) (hg : AbsSummable g) :
    kernelFunctional n h k β a p μ j f - kernelFunctional n h k β a p μ j g =
      kernelFunctional n h k β a p μ j (f - g)

/-- The constant-free part `J` of a family. -/
noncomputable def fluctFamily (c : CoeffFamily d) : CoeffFamily d

/-- The family restricted to the box `{γ | γᵢ ≤ m}`. -/
noncomputable def truncFamily (c : CoeffFamily d) (m : ℕ) : CoeffFamily d

theorem abs_fluctFamily_le (c : CoeffFamily d) (γ : Fin d → ℕ) : |fluctFamily c γ| ≤ |c γ|

theorem AbsSummable.fluctFamily {c : CoeffFamily d} (hc : AbsSummable c) :
    AbsSummable (fluctFamily c)

theorem mass_fluctFamily_le {c : CoeffFamily d} (hc : AbsSummable c) :
    mass (fluctFamily c) ≤ mass c

theorem abs_truncFamily_le (c : CoeffFamily d) (m : ℕ) (γ : Fin d → ℕ) :
    |truncFamily c m γ| ≤ |c γ|

theorem AbsSummable.truncFamily {c : CoeffFamily d} (hc : AbsSummable c) (m : ℕ) :
    AbsSummable (truncFamily c m)

theorem mass_truncFamily_le {c : CoeffFamily d} (hc : AbsSummable c) (m : ℕ) :
    mass (truncFamily c m) ≤ mass c

/-- `mass (c − truncFamily c m) = tailMass c m`. -/
theorem mass_sub_truncFamily {c : CoeffFamily d} (m : ℕ) :
    mass (c - truncFamily c m) = tailMass c m

theorem fluctFamily_truncFamily (c : CoeffFamily d) (m : ℕ) :
    fluctFamily (truncFamily c m) = truncFamily (fluctFamily c) m

theorem coeffFn_fluct (P : MonoRep d) : coeffFn (fluct P) = fluctFamily (coeffFn P)

theorem coeffFn_truncList (c : CoeffFamily d) (m : ℕ) :
    coeffFn (truncList c m) = truncFamily c m

```

### Laplace/Grammar/FamilyCoeffSeries.lean
```lean
theorem AbsSummable.add {f g : CoeffFamily d} (hf : AbsSummable f) (hg : AbsSummable g) :
    AbsSummable (f + g)

theorem AbsSummable.neg {f : CoeffFamily d} (hf : AbsSummable f) : AbsSummable (-f)

theorem AbsSummable.sub {f g : CoeffFamily d} (hf : AbsSummable f) (hg : AbsSummable g) :
    AbsSummable (f - g)

theorem mass_add_le {f g : CoeffFamily d} (hf : AbsSummable f) (hg : AbsSummable g) :
    mass (f + g) ≤ mass f + mass g

/-- `δ_0 = convPow c 0` is absolutely summable with mass `1`. -/
theorem absSummable_convPow_zero (c : CoeffFamily d) : AbsSummable (convPow c 0)

theorem mass_convPow_zero (c : CoeffFamily d) : mass (convPow c 0) = 1

theorem AbsSummable.convPow {c : CoeffFamily d} (hc : AbsSummable c) :
    ∀ p, AbsSummable (convPow c p)
  | 0 => absSummable_convPow_zero c
  | p + 1 => hc.conv (hc.convPow p)

theorem mass_convPow_le {c : CoeffFamily d} (hc : AbsSummable c) {B : ℝ} (hB : mass c ≤ B) :
    ∀ p, mass (convPow c p) ≤ B ^ p
  | 0 => by rw [mass_convPow_zero, pow_zero]
  | p + 1 => by
    have hB0 : 0 ≤ B

theorem conv_sub_left (f f' g : CoeffFamily d) : conv (f - f') g = conv f g - conv f' g

theorem conv_sub_right (f g g' : CoeffFamily d) : conv f (g - g') = conv f g - conv f g'

/-- **Power-difference estimate for families**:
`mass (c^{*p} − c'^{*p}) ≤ p B^{p-1} mass (c − c')` when both masses are `≤ B`. -/
theorem mass_convPow_sub_le {c c' : CoeffFamily d} (hc : AbsSummable c) (hc' : AbsSummable c')
    {B : ℝ} (hB : mass c ≤ B) (hB' : mass c' ≤ B) :
    ∀ p, mass (convPow c p - convPow c' p) ≤ p * B ^ (p - 1) * mass (c - c')
  | 0 => by simp [convPow, mass]
  | p + 1 => by
    have hB0 : 0 ≤ B

theorem tailMass_fluctFamily_le {c : CoeffFamily d} (hc : AbsSummable c) (m : ℕ) :
    tailMass (fluctFamily c) m ≤ tailMass c m

theorem fluctFamily_sub_truncFamily (c : CoeffFamily d) (m : ℕ) :
    fluctFamily c - fluctFamily (truncFamily c m) = fluctFamily c - truncFamily (fluctFamily c) m


/-- The `p`-th term of the coefficient series of family data. -/
noncomputable def familyCoeffTerm (n : ℕ) (h k : Fin (n + 1) → ℕ) (β : ℝ)
    (cξ cη : CoeffFamily (n + 1)) (μ : ℝ) (j p : ℕ) : ℝ

/-- **The paper's coefficient series** `A_{μ,j} = ∑_p β^p/p! T_p(cη * J^{*p})`. -/
noncomputable def familyCoeffSeries (n : ℕ) (h k : Fin (n + 1) → ℕ) (β : ℝ)
    (cξ cη : CoeffFamily (n + 1)) (μ : ℝ) (j : ℕ) : ℝ

/-- The truncation coefficients are the same series for the truncated families. -/
theorem truncCoeff_eq_series (n : ℕ) (h k : Fin (n + 1) → ℕ) (β : ℝ) (cξ cη : CoeffFamily (n + 1))
    (μ : ℝ) (j m : ℕ) :
    truncCoeff n h k β cξ cη μ j m =
      ∑' p : ℕ, β ^ p / (p.factorial : ℝ) * kernelFunctional n h k β (cξ 0) p μ j
        (CoeffFamily.conv (truncFamily cη m) (CoeffFamily.convPow (fluctFamily (truncFamily cξ
            m)) p))

/-- Uniform bound on the series terms, for any families with masses at most `E`, `B`. -/
theorem abs_kernel_conv_le (n : ℕ) (h k : Fin (n + 1) → ℕ) (hk : ∀ i, 0 < k i) (β a : ℝ)
    (hβ : 0 < β) (p : ℕ) {μ : ℝ} (hμ : 0 < μ) (j : ℕ) {f g : CoeffFamily (n + 1)}
    (hf : AbsSummable f) (hg : AbsSummable g) {E B : ℝ} (hE : mass f ≤ E) (hB : mass g ≤ B) :
    |kernelFunctional n h k β a p μ j (CoeffFamily.conv f (CoeffFamily.convPow g p))| ≤
      (∏ i, 1 / (2 * (k i : ℝ))) * kernelBudget n k * phaseLogMoment β a μ n p * (E * B ^ p)

/-- The Tonelli majorant of the series. -/
theorem summable_series_bound (n : ℕ) (k : Fin (n + 1) → ℕ) (β a : ℝ) (hβ : 0 < β) {μ : ℝ}
    (hμ : 0 < μ) {E B : ℝ} (hB : 0 ≤ B) :
    Summable fun p : ℕ => β ^ p / (p.factorial : ℝ) *
      ((∏ i, 1 / (2 * (k i : ℝ))) * kernelBudget n k * phaseLogMoment β a μ n p * (E * B ^ p))

/-- **Absolute convergence of the coefficient series.** -/
theorem summable_familyCoeffSeries_terms (n : ℕ) (h k : Fin (n + 1) → ℕ) (hk : ∀ i, 0 < k i) (β : ℝ)
    (hβ : 0 < β) {cξ cη : CoeffFamily (n + 1)} (hξ : AbsSummable cξ) (hη : AbsSummable cη) {μ : ℝ}
    (hμ : 0 < μ) (j : ℕ) :
    Summable fun p => |familyCoeffTerm n h k β cξ cη μ j p|

/-- Termwise convergence of the truncated series terms. -/
theorem tendsto_trunc_term (n : ℕ) (h k : Fin (n + 1) → ℕ) (hk : ∀ i, 0 < k i) (β : ℝ)
    (hβ : 0 < β) {cξ cη : CoeffFamily (n + 1)} (hξ : AbsSummable cξ) (hη : AbsSummable cη) {μ : ℝ}
    (hμ : 0 < μ) (j p : ℕ) :
    Tendsto (fun m => kernelFunctional n h k β (cξ 0) p μ j
      (CoeffFamily.conv (truncFamily cη m) (CoeffFamily.convPow (fluctFamily (truncFamily cξ m))
          p))) atTop
      (𝓝 (kernelFunctional n h k β (cξ 0) p μ j (CoeffFamily.conv cη (CoeffFamily.convPow
          (fluctFamily cξ) p))))

/-- **The truncation coefficients converge to the explicit series.** -/
theorem tendsto_truncCoeff_series (n : ℕ) (h k : Fin (n + 1) → ℕ) (hk : ∀ i, 0 < k i) (β : ℝ)
    (hβ : 0 < β) {cξ cη : CoeffFamily (n + 1)} (hξ : AbsSummable cξ) (hη : AbsSummable cη) {μ : ℝ}
    (hμ : 0 < μ) (j : ℕ) :
    Tendsto (truncCoeff n h k β cξ cη μ j) atTop (𝓝 (familyCoeffSeries n h k β cξ cη μ j))

/-- **Identification**: the limit-defined family coefficient is the paper's absolutely convergent
series, `A_{μ,j}(cξ, cη) = ∑_p β^p/p! T_p(cη * J^{*p})`, for `μ > 0`. -/
theorem familySpectralCoeff_eq_series (n : ℕ) (h k : Fin (n + 1) → ℕ) (hk : ∀ i, 0 < k i) (β : ℝ)
    (hβ : 0 < β) {cξ cη : CoeffFamily (n + 1)} (hξ : AbsSummable cξ) (hη : AbsSummable cη) {μ : ℝ}
    (hμ : 0 < μ) (j : ℕ) :
    familySpectralCoeff n h k β cξ cη μ j = familyCoeffSeries n h k β cξ cη μ j

```

## Questions
1. Is `familyCoeffSeries` the paper's coefficient series? Check: the Cauchy product `conv cη (convPow (fluctFamily cξ) p)` at γ equals Σ_{m + n = γ} (η_m/m!)·ξ_{n,p} with the paper's ξ_{n,p} (given c_γ = ∂^γ f(0)/γ!), including the p = 0 term (convPow c 0 = δ_0) and the exclusion of the constant term in J. Any normalisation slip (β^p/p!, K_k, binomials)?
2. Is the identification theorem (`familySpectralCoeff_eq_series`, μ > 0) a correct closure of qualification (ii)? Is the dominated-convergence argument (ℓ¹ continuity of T_p, power-difference estimate, tail masses, Tonelli majorant) sound as stated? What about μ ≤ 0 (both sides vanish; is a statement needed)?
3. u250: is `iteratedDeriv_fluctuationFn` the correct `∂_a^p S_μ(a) = β^p ∫ t^{μ-1}(√t)^p e^{…}` = β^p S_{μ+p/2}(a)? Any issue with `iteratedDeriv` (global derivative) vs the paper's derivative at a point? How should the remaining `(−∂_μ)^i` half be stated so that `fluctMoment β a p μ i = (−∂_μ)^i S_{μ+p/2}(a)` matches the sign convention `(−log t)^i`?
4. Should-fix list and hand-off wording for the coefficient description after these units.
