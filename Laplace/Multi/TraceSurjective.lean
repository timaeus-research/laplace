/-
Copyright (c) 2026 Timaeus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib
import Laplace.Multi.TraceKernelMain

/-!
# The trace map is onto: the visible dimension of a monomial design

`TraceKernelMain` identifies what the degree-`≤ m` monomial design sees of a smooth homogeneous
`Q` of degree `k = s + 2r` (with `s ≤ m ≤ s + 1` of the parity of `k`): exactly the trace
`Δ^r Q`, a smooth homogeneous function of degree `s`, in the sense that the design annihilates
`Q` iff `Δ^r Q = 0`. This file supplies the other half of the rank statement: **every** smooth
homogeneous `g` of degree `s` is `Δ^r Q` for some smooth homogeneous `Q` of degree `s + 2r`
(`SmoothHomog.exists_iterate_lap_eq`), for `d ≥ 1`. So the trace map `H_{s+2r} → H_s` is onto,
the design data of degree-`k` jets fill out all of `H_s`, and the visible dimension is
`dim H_s = binom(d + s - 1, s)` (the dimension count itself is not formalised).

The proof is the classical one via the identity, for `g` smooth homogeneous of degree `s`,
`Δ(|x|^{2(m+1)} g) = 2(m+1)(d + 2m + 2s) |x|^{2m} g + |x|^{2(m+1)} Δg`
(`lap_nsq_pow_mul`), which follows from the product rule for `Δ`,
`Δ|x|^{2(m+1)} = 2(m+1)(d+2m)|x|^{2m}` and Euler's identity `∑ xᵢ ∂ᵢ g = s g`. Strong
induction on `s`, with the exponent `m` carried along (`SmoothHomog.exists_lap_eq_nsq_pow_mul`),
then produces the preimage: `Δg` has degree `s - 2`, so by induction `|x|^{2(m+1)} Δg = ΔQ'`,
and `Q = (|x|^{2(m+1)} g - Q') / (2(m+1)(d+2m+2s))` does the job; for `s ≤ 1`, `Δg = 0` and the
correction is absent.
-/

open Real MeasureTheory Filter Topology
open scoped ContDiff

namespace Laplace.Multi

variable {d : ℕ}

/-! ### Linearity of `pd` and `lap` -/

theorem pd_add' {u v : EuclidD d → ℝ} (hu : Differentiable ℝ u) (hv : Differentiable ℝ v)
    (i : Fin d) : pd i (fun x ↦ u x + v x) = fun x ↦ pd i u x + pd i v x := by
  funext x
  unfold pd
  have hd : HasFDerivAt (fun x ↦ u x + v x) (fderiv ℝ u x + fderiv ℝ v x) x :=
    (hu x).hasFDerivAt.add (hv x).hasFDerivAt
  rw [hd.fderiv, add_apply]

theorem pd_const_mul' (c : ℝ) {u : EuclidD d → ℝ} (hu : Differentiable ℝ u) (i : Fin d) :
    pd i (fun x ↦ c * u x) = fun x ↦ c * pd i u x := by
  funext x
  unfold pd
  rw [fderiv_const_mul (hu x), smul_apply, smul_eq_mul]

theorem lap_add' {u v : EuclidD d → ℝ} (hu : ContDiff ℝ ∞ u) (hv : ContDiff ℝ ∞ v) :
    lap (fun x ↦ u x + v x) = fun x ↦ lap u x + lap v x := by
  funext x
  unfold lap
  have hu' : Differentiable ℝ u := hu.differentiable (by simp)
  have hv' : Differentiable ℝ v := hv.differentiable (by simp)
  simp only [pd_add' hu' hv']
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  rw [pd_add' ((pd_smooth hu i).differentiable (by simp))
    ((pd_smooth hv i).differentiable (by simp))]

theorem lap_const_mul' (c : ℝ) {u : EuclidD d → ℝ} (hu : ContDiff ℝ ∞ u) :
    lap (fun x ↦ c * u x) = fun x ↦ c * lap u x := by
  funext x
  unfold lap
  have hu' : Differentiable ℝ u := hu.differentiable (by simp)
  simp only [pd_const_mul' c hu']
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  rw [pd_const_mul' c ((pd_smooth hu i).differentiable (by simp))]

theorem pd_coord (i j : Fin d) :
    pd i (fun x : EuclidD d ↦ x j) = fun _ ↦ if j = i then (1 : ℝ) else 0 := by
  funext x
  unfold pd
  have hd : HasFDerivAt (fun x : EuclidD d ↦ x j) (EuclideanSpace.proj (𝕜 := ℝ) j) x :=
    (EuclideanSpace.proj (𝕜 := ℝ) j).hasFDerivAt
  rw [hd.fderiv]
  change (EuclideanSpace.single i (1 : ℝ)) j = _
  simp [PiLp.single_apply]

/-! ### Sums and the squared norm -/

theorem SmoothHomog.sum {ι : Type*} (s : Finset ι) {n : ℕ} {g : ι → EuclidD d → ℝ}
    (hg : ∀ k ∈ s, SmoothHomog n (g k)) : SmoothHomog n fun x ↦ ∑ k ∈ s, g k x := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using SmoothHomog.zero_fun (d := d) n
  | insert a s ha ih =>
    simp only [Finset.sum_insert ha]
    exact (hg a (Finset.mem_insert_self _ _)).add
      (ih fun k hk ↦ hg k (Finset.mem_insert_of_mem hk))

/-- The squared Euclidean norm as a polynomial. -/
def nsq (x : EuclidD d) : ℝ := ∑ i, x i * x i

theorem nsq_eq_norm_sq (x : EuclidD d) : nsq x = ‖x‖ ^ 2 := by
  rw [EuclideanSpace.norm_eq, Real.sq_sqrt (Finset.sum_nonneg fun i _ ↦ by positivity)]
  simp [nsq, sq]

theorem smoothHomog_nsq : SmoothHomog 2 (nsq (d := d)) :=
  SmoothHomog.sum Finset.univ fun i _ ↦ (SmoothHomog.coord i).mul (SmoothHomog.coord i)

theorem smoothHomog_nsq_pow : ∀ m : ℕ, SmoothHomog (2 * m) fun x : EuclidD d ↦ nsq x ^ m
  | 0 => by simpa using SmoothHomog.one (d := d)
  | m + 1 => by
    rw [show 2 * (m + 1) = 2 * m + 2 by ring]
    simp only [pow_succ]
    exact (smoothHomog_nsq_pow m).mul smoothHomog_nsq

theorem pd_nsq (i : Fin d) : pd i nsq = fun x ↦ 2 * x i := by
  have h := pd_sum (Finset.univ) (g := fun j (x : EuclidD d) ↦ x j * x j)
    (fun j ↦ ((SmoothHomog.coord j).mul (SmoothHomog.coord j)).smooth) i
  have hnsq : nsq = fun x : EuclidD d ↦ ∑ j, x j * x j := rfl
  rw [hnsq, h]
  funext x
  simp only [pd_mul (SmoothHomog.coord _) (SmoothHomog.coord _) i, pd_coord]
  simp [Finset.sum_add_distrib, ite_mul, mul_ite]
  ring

theorem pd_nsq_pow (i : Fin d) :
    ∀ m : ℕ, pd i (fun x : EuclidD d ↦ nsq x ^ (m + 1)) = fun x ↦ 2 * (m + 1) * x i * nsq x ^ m
  | 0 => by
    have h1 : (fun x : EuclidD d ↦ nsq x ^ (0 + 1)) = nsq := by
      funext x
      simp
    rw [h1, pd_nsq]
    funext x
    simp
  | m + 1 => by
    have h1 : (fun x : EuclidD d ↦ nsq x ^ (m + 1 + 1)) =
        fun x ↦ nsq x ^ (m + 1) * nsq x := by
      funext x
      ring
    rw [h1, pd_mul (smoothHomog_nsq_pow (m + 1)) smoothHomog_nsq, pd_nsq_pow i m, pd_nsq]
    funext x
    push_cast
    ring

/-! ### The Laplacian of `|x|^{2(m+1)} g` -/

theorem lap_mul {a b : ℕ} {f g : EuclidD d → ℝ} (hf : SmoothHomog a f) (hg : SmoothHomog b g) :
    lap (fun x ↦ f x * g x) =
      fun x ↦ lap f x * g x + 2 * ∑ i, pd i f x * pd i g x + f x * lap g x := by
  funext x
  unfold lap
  simp only [pd_mul hf hg]
  have hstep : ∀ i : Fin d, pd i (fun x ↦ pd i f x * g x + f x * pd i g x) x =
      pd i (pd i f) x * g x + pd i f x * pd i g x +
        (pd i f x * pd i g x + f x * pd i (pd i g) x) := by
    intro i
    rw [pd_add' (((hf.deriv i).mul hg).differentiable) ((hf.mul (hg.deriv i)).differentiable),
      pd_mul (hf.deriv i) hg, pd_mul hf (hg.deriv i)]
  simp only [hstep, Finset.sum_add_distrib, ← Finset.sum_mul, ← Finset.mul_sum]
  ring

theorem lap_nsq_pow (m : ℕ) :
    lap (fun x : EuclidD d ↦ nsq x ^ (m + 1)) = fun x ↦ 2 * (m + 1) * (d + 2 * m) * nsq x ^ m := by
  funext x
  unfold lap
  simp only [pd_nsq_pow]
  have hstep : ∀ i : Fin d, pd i (fun x ↦ 2 * (m + 1) * x i * nsq x ^ m) x =
      2 * (m + 1) * (nsq x ^ m + x i * pd i (fun x ↦ nsq x ^ m) x) := by
    intro i
    have h1 : (fun x : EuclidD d ↦ 2 * (m + 1) * x i * nsq x ^ m) =
        fun x ↦ 2 * (m + 1) * (x i * nsq x ^ m) := by
      funext x
      ring
    rw [h1, pd_const_mul' _ ((SmoothHomog.coord i).mul (smoothHomog_nsq_pow m)).differentiable,
      pd_mul (SmoothHomog.coord i) (smoothHomog_nsq_pow m), pd_coord]
    simp
  simp only [hstep]
  rw [← Finset.mul_sum, Finset.sum_add_distrib, ← (smoothHomog_nsq_pow (d := d) m).euler x]
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  push_cast
  ring

theorem sum_pd_nsq_pow_mul_pd {s : ℕ} {g : EuclidD d → ℝ} (hg : SmoothHomog s g) (m : ℕ)
    (x : EuclidD d) :
    ∑ i, pd i (fun x : EuclidD d ↦ nsq x ^ (m + 1)) x * pd i g x =
      2 * (m + 1) * s * nsq x ^ m * g x := by
  simp only [pd_nsq_pow]
  have h : ∀ i : Fin d, 2 * ((m : ℝ) + 1) * x i * nsq x ^ m * pd i g x =
      2 * (m + 1) * nsq x ^ m * (x i * pd i g x) := fun i ↦ by ring
  simp only [h]
  rw [← Finset.mul_sum, ← hg.euler x]
  ring

/-- **The key identity**: `Δ(|x|^{2(m+1)} g) = 2(m+1)(d + 2m + 2s) |x|^{2m} g + |x|^{2(m+1)} Δg`. -/
theorem lap_nsq_pow_mul {s : ℕ} {g : EuclidD d → ℝ} (hg : SmoothHomog s g) (m : ℕ) :
    lap (fun x : EuclidD d ↦ nsq x ^ (m + 1) * g x) =
      fun x ↦ 2 * (m + 1) * (d + 2 * m + 2 * s) * (nsq x ^ m * g x) +
        nsq x ^ (m + 1) * lap g x := by
  rw [lap_mul (smoothHomog_nsq_pow (m + 1)) hg]
  funext x
  rw [sum_pd_nsq_pow_mul_pd hg m x]
  have h := congrFun (lap_nsq_pow (d := d) m) x
  rw [h]
  ring

/-! ### `Δg = 0` in degree `≤ 1` -/

theorem SmoothHomog.lap_eq_zero_of_le_one {s : ℕ} {g : EuclidD d → ℝ} (hg : SmoothHomog s g)
    (hs : s ≤ 1) : lap g = fun _ ↦ 0 := by
  funext x
  unfold lap
  refine Finset.sum_eq_zero fun i _ ↦ ?_
  have h0 : SmoothHomog 0 (pd i g) := by
    have := hg.deriv i
    rwa [show s - 1 = 0 by omega] at this
  rw [h0.pd_zero i]

/-! ### Surjectivity -/

/-- Strong induction on the degree, carrying the exponent of `|x|^2`: for `d ≥ 1`, every
`|x|^{2m} g` with `g` smooth homogeneous of degree `s` is the Laplacian of a smooth homogeneous
function of degree `s + 2m + 2`. -/
theorem SmoothHomog.exists_lap_eq_nsq_pow_mul (hd : 0 < d) :
    ∀ (s : ℕ) (g : EuclidD d → ℝ), SmoothHomog s g → ∀ m : ℕ,
      ∃ Q, SmoothHomog (s + 2 * m + 2) Q ∧ lap Q = fun x ↦ nsq x ^ m * g x := by
  intro s
  induction s using Nat.strong_induction_on with
  | _ s ih =>
  intro g hg m
  have hdpos : (0 : ℝ) < d := by exact_mod_cast hd
  set a : ℝ := 2 * (m + 1) * (d + 2 * m + 2 * s) with ha
  have hapos : 0 < a := by positivity
  have hkey := lap_nsq_pow_mul hg m
  rcases Nat.lt_or_ge s 2 with hlt | hge
  · -- `Δg = 0`: the correction is absent.
    refine ⟨fun x ↦ a⁻¹ * (nsq x ^ (m + 1) * g x), ?_, ?_⟩
    · have := ((smoothHomog_nsq_pow (d := d) (m + 1)).mul hg).const_mul a⁻¹
      rwa [show 2 * (m + 1) + s = s + 2 * m + 2 by ring] at this
    · rw [lap_const_mul' _ ((smoothHomog_nsq_pow (d := d) (m + 1)).mul hg).smooth, hkey,
        hg.lap_eq_zero_of_le_one (by omega)]
      funext x
      simp only [mul_zero, add_zero]
      rw [← ha]
      field_simp
  · -- `s = s' + 2`: correct by the inductive preimage of `|x|^{2(m+1)} Δg`.
    obtain ⟨s', rfl⟩ : ∃ s', s = s' + 2 := ⟨s - 2, by omega⟩
    have hlap : SmoothHomog s' (lap g) := by
      have := hg.laplacian
      rwa [show s' + 2 - 2 = s' by omega] at this
    obtain ⟨Q', hQ', hlapQ'⟩ := ih s' (by omega) (lap g) hlap (m + 1)
    refine ⟨fun x ↦ a⁻¹ * (nsq x ^ (m + 1) * g x + (-1) * Q' x), ?_, ?_⟩
    · have h1 := (smoothHomog_nsq_pow (d := d) (m + 1)).mul hg
      have h2 := hQ'.const_mul (-1)
      rw [show 2 * (m + 1) + (s' + 2) = s' + 2 * (m + 1) + 2 by ring] at h1
      have := (h1.add h2).const_mul a⁻¹
      rwa [show s' + 2 * (m + 1) + 2 = s' + 2 + 2 * m + 2 by ring] at this
    · have hsm : ContDiff ℝ ∞ fun x : EuclidD d ↦ nsq x ^ (m + 1) * g x :=
        ((smoothHomog_nsq_pow (d := d) (m + 1)).mul hg).smooth
      have hQ'' : ContDiff ℝ ∞ fun x ↦ (-1 : ℝ) * Q' x := contDiff_const.mul hQ'.smooth
      rw [lap_const_mul' _ (hsm.add hQ''), lap_add' hsm hQ'', lap_const_mul' _ hQ'.smooth, hkey,
        hlapQ']
      funext x
      simp only
      rw [← ha]
      field_simp
      ring

/-- **`Δ : H_{s+2} → H_s` is onto** (`d ≥ 1`). -/
theorem SmoothHomog.exists_lap_eq (hd : 0 < d) {s : ℕ} {g : EuclidD d → ℝ}
    (hg : SmoothHomog s g) : ∃ Q, SmoothHomog (s + 2) Q ∧ lap Q = g := by
  obtain ⟨Q, hQ, hlap⟩ := SmoothHomog.exists_lap_eq_nsq_pow_mul hd s g hg 0
  refine ⟨Q, by simpa using hQ, ?_⟩
  rw [hlap]
  funext x
  simp

/-- **`Δ^r : H_{s+2r} → H_s` is onto** (`d ≥ 1`). -/
theorem SmoothHomog.exists_iterate_lap_eq (hd : 0 < d) {s : ℕ} {g : EuclidD d → ℝ}
    (hg : SmoothHomog s g) : ∀ r : ℕ, ∃ Q, SmoothHomog (s + 2 * r) Q ∧ lap^[r] Q = g
  | 0 => ⟨g, by simpa using hg, rfl⟩
  | r + 1 => by
    obtain ⟨Q, hQ, hlap⟩ := SmoothHomog.exists_iterate_lap_eq hd hg r
    obtain ⟨Q₁, hQ₁, hlap₁⟩ := SmoothHomog.exists_lap_eq hd hQ
    refine ⟨Q₁, ?_, ?_⟩
    · rwa [show s + 2 * (r + 1) = s + 2 * r + 2 by ring]
    · rw [Function.iterate_succ_apply, hlap₁, hlap]

/-! ### Headline: kernel and image of the trace map -/

/-- **What the degree-`≤ m` design sees of the degree-`k` jet, with `k = s + 2r`, `1 ≤ s ≤ m ≤ s+1`,
`d ≥ 1`.** The design annihilates a smooth homogeneous `Q` of degree `k` iff its trace `Δ^r Q`
vanishes (`TraceKernelMain`), and every smooth homogeneous `g` of degree `s` is the trace of some
such `Q`. So the design's view of `H_k` is the surjection `Δ^r : H_k → H_s`: it sees exactly
`dim H_s = binom(d+s-1, s)` dimensions of the degree-`k` jet. -/
theorem trace_data_complete (hd : 0 < d) {m s r : ℕ} (hs : 1 ≤ s) (hsm : s ≤ m)
    (hms : m ≤ s + 1) :
    (∀ Q : EuclidD d → ℝ, SmoothHomog (s + 2 * r) Q → (CovWords m Q ↔ lap^[r] Q = 0)) ∧
    (∀ g : EuclidD d → ℝ, SmoothHomog s g →
      ∃ Q, SmoothHomog (s + 2 * r) Q ∧ lap^[r] Q = g) :=
  ⟨fun _ hQ ↦ hQ.trace_kernel_iff hs rfl hsm hms,
    fun _ hg ↦ hg.exists_iterate_lap_eq hd r⟩

end Laplace.Multi
