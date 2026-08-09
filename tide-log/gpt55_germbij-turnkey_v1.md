Let

```lean
let S : Set ℝ := Set.Ioc 0 1
let T : Set ℝ := tsupport φ
let μ : Measure (ℝ × ℝ) := (volume.restrict S).prod volume
let f : ℝ × ℝ → ℝ := Function.uncurry F
```

Assume `hT : IsCompact T` and `hout : ∀ s w, w ∉ T → F s w = 0`.

### 1. Relevant lemmas

#### Continuity and measurability

Usually prove joint continuity directly:

```lean
have hf : Continuous f := by
  dsimp [f, F]
  fun_prop
```

Then:

```lean
have hfm : AEStronglyMeasurable f μ :=
  hf.aestronglyMeasurable
```

Do not prove only separate continuity: separate continuity is insufficient for joint continuity. `fun_prop` handles `fst`, `snd`, multiplication, `Real.exp`, etc. There is no generally useful `Continuous.uncurry` turning separate continuity into joint continuity.

#### Compactness and uniform bound

```lean
have hK : IsCompact (Set.Icc (0 : ℝ) 1 ×ˢ T) :=
  isCompact_Icc.prod hT
```

Apply the compact-bound lemma to the norm:

```lean
obtain ⟨B, hB⟩ :=
  hK.exists_bound_of_continuousOn hf.norm.continuousOn
-- hB : ∀ p ∈ Set.Icc 0 1 ×ˢ T, ‖f p‖ ≤ B
```

It is convenient to replace `B` by `max B 0`, so that the majorant has norm exactly that constant.

#### Product/restriction identity

For measurable `S`, the relevant identity is:

```lean
Measure.restrict_prod
```

with shape

```lean
(volume.restrict S).prod volume
  = (volume.prod volume).restrict (S ×ˢ Set.univ)
```

possibly in the opposite rewrite orientation. Thus, after rewriting, membership in the restricted set is available via:

```lean
ae_restrict_mem (hS.prod measurableSet_univ)
```

where `hS : MeasurableSet S`.

You can also avoid using this identity: prove the bound by `Measure.prod_ae`/Fubini from the fact that `x ∈ S` almost everywhere for `volume.restrict S`. The restriction identity is usually shorter.

#### Finite measure of the cylinder

For measurable rectangles:

```lean
Measure.prod_apply
```

has the shape

```lean
(μ.prod ν) (A ×ˢ B) = μ A * ν B
```

given `MeasurableSet A` and `MeasurableSet B`.

Compact sets have finite measure under a locally finite measure:

```lean
hT.measure_lt_top
isCompact_Icc.measure_lt_top
```

Hence:

```lean
have hSfinite : (volume.restrict S) Set.univ < ∞ := by
  have hle : volume S ≤ volume (Set.Icc (0 : ℝ) 1) :=
    measure_mono Set.Ioc_subset_Icc_self
  simpa [Measure.restrict_apply, hS] using
    lt_of_le_of_lt hle isCompact_Icc.measure_lt_top
```

and, for `C := Set.univ ×ˢ T`,

```lean
have hCfinite : μ C < ∞ := by
  rw [Measure.prod_apply measurableSet_univ hT.isClosed.measurableSet]
  exact ENNReal.mul_lt_top hSfinite hT.measure_lt_top
```

#### Indicator majorant

Since

```lean
IntegrableOn g C μ
```

is definitionally integrability of `C.indicator g`, use:

```lean
integrableOn_const
```

Typically:

```lean
have hmaj : Integrable (C.indicator fun _ => (B' : ℝ)) μ := by
  change IntegrableOn (fun _ : ℝ × ℝ => B') C μ
  exact integrableOn_const.2 (ne_of_lt hCfinite)
```

The exact RHS of `integrableOn_const` is finite measure, generally expressed as `μ C ≠ ∞`; `ne_of_lt hCfinite` supplies it.

#### Domination

The final lemma is:

```lean
Integrable.mono'
```

used as:

```lean
exact hmaj.mono' hfm hae_bound
```

where

```lean
hae_bound :
  ∀ᵐ p ∂μ, ‖f p‖ ≤ ‖C.indicator (fun _ => B') p‖
```

Notice that `mono'` compares norms.

---

### 2. Shorter alternatives

There is a general compact-set route via the compact integrability theorem, exposed around:

```lean
ContinuousOn.integrableOn_compact
```

Conceptually:

```lean
have : IntegrableOn f (Set.Icc 0 1 ×ˢ T) (volume.prod volume) := ...
```

Then use `S ⊆ Icc 0 1` and the fact that `f = 0` outside `T`. In practice, transferring this to `(volume.restrict S).prod volume` can require as much measure-restriction bookkeeping as the explicit majorant.

`Continuous.integrable_of_hasCompactSupport` is not directly applicable to `f`, since `f` need not have compact support in the `s` variable. Multiplying by a continuous compactly supported cutoff equal to `1` on `[0,1]` makes it applicable, but constructing and proving the cutoff properties is usually longer.

---

### 3. Recommended skeleton

```lean
let S : Set ℝ := Set.Ioc 0 1
let T : Set ℝ := tsupport φ
let μ : Measure (ℝ × ℝ) := (volume.restrict S).prod volume
let f : ℝ × ℝ → ℝ := Function.uncurry F

have hS : MeasurableSet S := measurableSet_Ioc
have hTm : MeasurableSet T := hT.isClosed.measurableSet

have hf : Continuous f := by
  dsimp [f, F]
  fun_prop

have hK : IsCompact (Set.Icc (0 : ℝ) 1 ×ˢ T) :=
  isCompact_Icc.prod hT

obtain ⟨B, hB⟩ :=
  hK.exists_bound_of_continuousOn hf.norm.continuousOn

let B' : ℝ := max B 0
have hB' : 0 ≤ B' := le_max_right _ _

let C : Set (ℝ × ℝ) := Set.univ ×ˢ T
let maj : ℝ × ℝ → ℝ := C.indicator (fun _ => B')

have hSfinite : (volume.restrict S) Set.univ < ∞ := by
  have hle : volume S ≤ volume (Set.Icc (0 : ℝ) 1) :=
    measure_mono Set.Ioc_subset_Icc_self
  simpa [S, Measure.restrict_apply, hS] using
    lt_of_le_of_lt hle isCompact_Icc.measure_lt_top

have hCfinite : μ C < ∞ := by
  dsimp [μ, C]
  rw [Measure.prod_apply measurableSet_univ hTm]
  exact ENNReal.mul_lt_top hSfinite hT.measure_lt_top

have hmaj : Integrable maj μ := by
  change IntegrableOn (fun _ : ℝ × ℝ => B') C μ
  exact integrableOn_const.2 (ne_of_lt hCfinite)

have hae_bound : ∀ᵐ p ∂μ, ‖f p‖ ≤ ‖maj p‖ := by
  -- Rewrite μ using Measure.restrict_prod, then use
  -- ae_restrict_mem (hS.prod measurableSet_univ).
  -- For p.2 ∈ T, apply hB since S ⊆ Icc 0 1.
  -- For p.2 ∉ T, use hout, so both sides are zero.
  rw [Measure.restrict_prod hS]
  filter_upwards [ae_restrict_mem (hS.prod measurableSet_univ)] with p hp
  rcases hp with ⟨hpS, -⟩
  by_cases hpT : p.2 ∈ T
  · have hpK : p ∈ Set.Icc (0 : ℝ) 1 ×ˢ T :=
      ⟨Set.Ioc_subset_Icc_self hpS, hpT⟩
    have := hB p hpK
    simp [maj, C, hpT, B', hB', le_max_of_le_left this]
  · have hz : f p = 0 := hout p.1 p.2 hpT
    simp [maj, C, hpT, hz]

exact hmaj.mono' hf.aestronglyMeasurable hae_bound
```

The only part likely to need minor syntactic adjustment across Mathlib versions is the rewrite orientation/application syntax of `Measure.restrict_prod`; the domination and `Integrable.mono'` structure is the robust route.