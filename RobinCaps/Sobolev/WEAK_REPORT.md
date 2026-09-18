# U-SOB-ND report — `RobinCaps/Sobolev/Weak.lean`

Status: **741 lines, compiles with `lake env lean RobinCaps/Sobolev/Weak.lean`, exit code 0, no
errors, no warnings, no `sorry` / `admit` / `axiom`.** Every substantive theorem depends only on
`[propext, Classical.choice, Quot.sound]`.

Throughout, `E` abbreviates `EuclideanSpace ℝ (Fin n)` (a `local notation` in the file) and the
namespace is `RobinCaps.Sobolev.Weak`.

---

## (a) What the file defines and proves

### A.1 The weak gradient

```lean
def HasWeakGrad (D : Set E) (u : E → ℝ) (g : E → E) : Prop :=
  ∀ φ : E → ℝ, ContDiff ℝ ∞ φ → HasCompactSupport φ → tsupport φ ⊆ D →
    ∀ i : Fin n, ∫ x in D, u x * fderiv ℝ φ x (EuclideanSpace.single i 1)
      = - ∫ x in D, g x i * φ x
```

This is the coordinatewise distributional identity `∫_D u ∂ᵢφ = -∫_D gᵢ φ`. Test functions are
`C^∞`, compactly supported, with `tsupport φ ⊆ D` — so no boundary term is ever implicitly
discarded. `∂ᵢφ x` is spelled `fderiv ℝ φ x (EuclideanSpace.single i 1)` and `gᵢ x` is `g x i`
(the `PiLp` coercion), i.e. everything is in Euclidean coordinates, never as an abstract
`fderiv` norm.

Auxiliary integrability layer (for a measure `μ` with `[IsFiniteMeasureOnCompacts μ]`), all
resting on the locally declared instance `instHolderTripleTwoTwoOne : ENNReal.HolderTriple 2 2 1`
(mathlib does not register `2⁻¹ + 2⁻¹ = 1⁻¹` globally), which is what makes `L²·L² ⊆ L¹`
available through `MemLp.integrable_mul`:

| name | statement |
|---|---|
| `memLp_two_of_test` | `ContDiff ℝ ∞ φ → HasCompactSupport φ → MemLp φ 2 μ` |
| `memLp_two_pderiv` | same hypotheses ⟹ `MemLp (fun x => fderiv ℝ φ x (EuclideanSpace.single i 1)) 2 μ` |
| `integrable_mul_pderiv` | `MemLp u 2 μ` ⟹ `Integrable (fun x => u x * ∂ᵢφ x) μ` |
| `memLp_two_comp` | `MemLp g 2 μ → MemLp (fun x => g x i) 2 μ` (via `EuclideanSpace.proj i`) |
| `integrable_comp_mul` | `MemLp g 2 μ` ⟹ `Integrable (fun x => g x i * φ x) μ` |

Algebra of weak gradients (namespace `HasWeakGrad`):

* `zero : HasWeakGrad D (fun _ => (0:ℝ)) (fun _ => (0:E))`
* `add` — needs the four `MemLp … 2 (volume.restrict D)` hypotheses on `u, v, g, h` (they are
  used to split the integrals); concludes `HasWeakGrad D (u + v) (g + h)`.
* `smul (c : ℝ)` — `HasWeakGrad D u g → HasWeakGrad D (c • u) (c • g)`; no integrability needed.
* `congr_ae` — `u =ᵐ[volume.restrict D] u' → g =ᵐ[volume.restrict D] g' → HasWeakGrad D u g →
  HasWeakGrad D u' g'`.
* **(added in this session)** `setIntegral_mul_pderiv_eq_integral`,
  `setIntegral_comp_mul_eq_integral` — for `tsupport φ ⊆ S`, the integral over `S` of `u·∂ᵢφ`
  (resp. `gᵢ·φ`) equals the integral over the whole space.
* **(added in this session)** `mono {D D'} (hsub : D' ⊆ D) : HasWeakGrad D u g → HasWeakGrad D' u g`
  — **locality of weak gradients**. Both sides of the defining identity are unchanged when the
  domain of integration shrinks from `D` to `D'`, because the integrands vanish off `tsupport φ`.

### A.2 Uniqueness of the weak gradient (deliverable 1(i) — already present)

```lean
theorem HasWeakGrad.ae_eq {D : Set E} (hD : IsOpen D) {u : E → ℝ} {g g' : E → E}
    (hg : MemLp g 2 (volume.restrict D)) (hg' : MemLp g' 2 (volume.restrict D))
    (h : HasWeakGrad D u g) (h' : HasWeakGrad D u g') :
    g =ᵐ[volume.restrict D] g'
```

Proof: coordinatewise, `x ↦ g x i - g' x i` is `LocallyIntegrableOn … D` (from `MemLp … 2`
via `MemLp.locallyIntegrable` with `1 ≤ 2`), and pairs to zero against every test function;
mathlib's fundamental lemma of the calculus of variations
`IsOpen.ae_eq_zero_of_integral_contDiff_smul_eq_zero` gives a.e. vanishing on `D`;
`ae_all_iff` collects the `n` coordinates and `PiLp.ext` reassembles the vectors.
**This is exactly the mathlib lemma the task names** (see §(b) below for the signature) — the
`IsOpen` variant, which is the right one because the conclusion is only claimed on `D`.

### A.3 The space `H1 D`

```lean
structure H1 (D : Set E) where
  toFun : E → ℝ
  grad : E → E
  memL2 : MemLp toFun 2 (volume.restrict D)
  grad_memL2 : MemLp grad 2 (volume.restrict D)
  hasWeakGrad : HasWeakGrad D toFun grad
```

Elements carry **representatives**: `H1.ext` is pointwise equality of the pair, not a.e.
equality. The file supplies `H1.toPair`, `toPair_injective`, `zero`, `add`, `smul`, the `simp`
lemmas `zero_toFun … smul_grad`, and then, by `Function.Injective.addCommMonoid` /
`Function.Injective.module` along `toPair`:

```lean
instance instAddCommMonoid : AddCommMonoid (H1 D)
instance instModule       : Module ℝ (H1 D)
instance instAddCommGroup : AddCommGroup (H1 D)   -- via Module.addCommMonoidToAddCommGroup
```

So `H1 D` is a real vector space — precisely the input type required by the abstract form
engine `RobinCaps.Spectrum.minmax : (H → ℝ) → (H → ℝ) → ℕ → ℝ`, which only assumes
`[AddCommGroup H] [Module ℝ H]`. **The interface between U-SOB-ND and U-SPEC is therefore
already type-correct.**

### A.4 The forms (deliverable 1(iii) — already present)

```lean
def dirichlet {D : Set E} (u : H1 D) : ℝ := ∫ x in D, ‖u.grad x‖ ^ 2
def mass      {D : Set E} (u : H1 D) : ℝ := ∫ x in D, u.toFun x ^ 2
def robinForm {D : Set E} (σ : Measure E) (T : H1 D → (E → ℝ)) (α : ℝ) (u : H1 D) : ℝ :=
  dirichlet u + α * ∫ x, (T u x) ^ 2 ∂σ
```

The boundary measure `σ` and the trace `T` are **explicit parameters**. Neither exists in
mathlib v4.26.0; carrying them as parameters means nothing about the boundary is invented and
there is no hidden axiom. `robinForm` is literally `eq:robin-form`, `mass` is literally `N_D`.

Proved about them:

| name | statement |
|---|---|
| `dirichlet_nonneg` | `0 ≤ dirichlet u` |
| `mass_nonneg` | `0 ≤ mass u` |
| `robinForm_nonneg` | `0 ≤ α → 0 ≤ robinForm σ T α u` |
| `mass_congr_ae` | `u.toFun =ᵐ[volume.restrict D] v.toFun → mass u = mass v` |
| `dirichlet_congr_ae` | `u.grad =ᵐ[volume.restrict D] v.grad → dirichlet u = dirichlet v` |
| `dirichlet_eq_of_toFun_eq` | `IsOpen D → u.toFun = v.toFun → dirichlet u = dirichlet v` |
| `mass_smul` | `mass (c • u) = c ^ 2 * mass u` |
| `dirichlet_smul` | `dirichlet (c • u) = c ^ 2 * dirichlet u` |

**Added in this session** (this is the statement that actually justifies the module docstring's
claim that "nothing is lost at the level of the forms"):

```lean
theorem H1.grad_ae_eq {D : Set E} (hD : IsOpen D) {u v : H1 D}
    (h : u.toFun =ᵐ[volume.restrict D] v.toFun) : u.grad =ᵐ[volume.restrict D] v.grad

theorem dirichlet_eq_of_toFun_ae_eq {D : Set E} (hD : IsOpen D) {u v : H1 D}
    (h : u.toFun =ᵐ[volume.restrict D] v.toFun) : dirichlet u = dirichlet v
```

Together with `mass_congr_ae` these say: on an open `D`, **both forms descend to the quotient of
`H1 D` by a.e. equality of `toFun`**, so the representative-carrying model costs nothing
variationally. (The previous `dirichlet_eq_of_toFun_eq` required literal function equality,
which is too strong to be usable.)

### A.5 Integration by parts and classical gradients (deliverable 1(ii) — already present)

```lean
theorem integral_fderiv_single_eq_zero_pi {m : ℕ} (G : (Fin (m + 1) → ℝ) → ℝ)
    (hG : ContDiff ℝ 1 G) (hGc : HasCompactSupport G) (i : Fin (m + 1)) :
    ∫ y, fderiv ℝ G y (Pi.single i 1) = 0
```

Proof method (≈100 lines, the technical core of the file): pick `R` with
`tsupport G ⊆ closedBall 0 r`, `R = max r 0 + 1`; set the box `a = fun _ => -R`,
`b = fun _ => R`; take the vector field `f j = if j = i then G else 0` with derivative
`f' j = if j = i then fderiv ℝ G else 0`, so that `∑ j, f' j y (Pi.single j 1) = ∂ᵢG y`; all
`2(m+1)` face integrals vanish since every face point has sup-norm `≥ R`
(`Fin.insertNth_apply_same` + `norm_le_pi_norm`); apply
`MeasureTheory.integral_divergence_of_hasFDerivAt_off_countable'` with the countable exceptional
set `∅`; finally `setIntegral_eq_integral_of_forall_compl_eq_zero` upgrades `∫ over Icc a b` to
`∫ over univ` because `fderiv ℝ G x = 0` outside the box.

```lean
theorem integral_fderiv_single_eq_zero (F : E → ℝ) (hF : ContDiff ℝ 1 F)
    (hFc : HasCompactSupport F) (i : Fin n) :
    ∫ x, fderiv ℝ F x (EuclideanSpace.single i 1) = 0
```
transports the above from `Fin n → ℝ` to `EuclideanSpace ℝ (Fin n)` along
`(EuclideanSpace.equiv (Fin (m+1)) ℝ).symm`, using
`PiLp.volume_preserving_toLp (Fin (m+1))` (`MeasurePreserving (WithLp.toLp 2) volume volume`)
and `ContinuousLinearEquiv.comp_right_fderiv`. The `n = 0` case is `Fin.elim0`.

```lean
theorem integral_mul_fderiv_eq_neg (u φ : E → ℝ) (hu : ContDiff ℝ 1 u)
    (hφ : ContDiff ℝ 1 φ) (hφc : HasCompactSupport φ) (i : Fin n) :
    ∫ x, u x * fderiv ℝ φ x (EuclideanSpace.single i 1)
      = - ∫ x, fderiv ℝ u x (EuclideanSpace.single i 1) * φ x
```
(Leibniz on `u * φ`, which is `C¹` with compact support, then the previous theorem. Note `u`
needs **no** decay.)

```lean
def classicalGrad (u : E → ℝ) (x : E) : E :=
  WithLp.toLp 2 fun i => fderiv ℝ u x (EuclideanSpace.single i 1)
@[simp] theorem classicalGrad_apply : classicalGrad u x i = fderiv ℝ u x (EuclideanSpace.single i 1)

theorem hasWeakGrad_classicalGrad (D : Set E) (u : E → ℝ) (hu : ContDiff ℝ 1 u) :
    HasWeakGrad D u (classicalGrad u)
```

This is deliverable 1(ii) and is in fact **stronger** than asked: no compact support on `u` and
no hypothesis on `D` at all (the test function's support does the localisation). Supporting
lemmas `continuous_classicalGrad`, `hasCompactSupport_classicalGrad`, and then

```lean
def H1.ofCompactSupport (D : Set E) (u : E → ℝ) (hu : ContDiff ℝ 1 u)
    (huc : HasCompactSupport u) : H1 D
```
with `@[simp]` lemmas `ofCompactSupport_toFun`, `ofCompactSupport_grad`. So `H1 D` provably
contains every compactly supported `C¹` function — the space is nonempty in a nontrivial way,
which is the sanity check that the definition is not vacuous.

### A.6 Targets (statements only, added this session)

Four `Prop`-valued `def`s at the end of the file, in the project's established style
(`RobinCaps.Sobolev.VariationBridge`). **None is used as a hypothesis anywhere above; nothing in
the file depends on them.**

```lean
def IsBoundaryMeasure (D : Set E) (σ : Measure E) : Prop :=
  σ = (Measure.hausdorffMeasure ((n : ℝ) - 1)).restrict (frontier D)

def TraceExists (D : Set E) (σ : Measure E) : Prop :=
  ∃ T : H1 D → (E → ℝ),
    (∀ u v : H1 D, T (u + v) = T u + T v) ∧
    (∀ (c : ℝ) (u : H1 D), T (c • u) = c • T u) ∧
    (∀ (u : E → ℝ) (hu : ContDiff ℝ 1 u) (huc : HasCompactSupport u),
      T (H1.ofCompactSupport D u hu huc) =ᵐ[σ] u) ∧
    ∃ C : ℝ, 0 ≤ C ∧ ∀ u : H1 D, ∫ x, (T u x) ^ 2 ∂σ ≤ C * (dirichlet u + mass u)

def TraceInequality (D : Set E) (σ : Measure E) (T : H1 D → (E → ℝ)) : Prop :=
  ∃ C : ℝ, 0 ≤ C ∧ ∀ u : H1 D, ∫ x, (T u x) ^ 2 ∂σ ≤ C * (dirichlet u + mass u)

def RellichEmbedding (D : Set E) : Prop :=
  ∀ u : ℕ → H1 D, (∃ C : ℝ, ∀ k, dirichlet (u k) + mass (u k) ≤ C) →
    ∃ (ν : ℕ → ℕ) (v : E → ℝ), StrictMono ν ∧
      Tendsto (fun k => ∫ x in D, ((u (ν k)).toFun x - v x) ^ 2) atTop (nhds 0)

def RobinCoercive (D : Set E) (σ : Measure E) (T : H1 D → (E → ℝ)) (α : ℝ) : Prop :=
  ∃ C : ℝ, 0 ≤ C ∧ ∀ u : H1 D, -(C * mass u) ≤ robinForm σ T α u
```

The third conjunct of `TraceExists` is what makes the trace *the* trace and not an arbitrary
bounded linear map: on `C¹` compactly supported functions it must be restriction.

### A.7 Deliverable 1 — verdict

All three requested items were **already present** in the prototype; the module docstring was
stale (it still announced `ClassicalGradIsWeakGrad` as an unproven `Prop`-target although
`hasWeakGrad_classicalGrad` is a proved theorem). The docstring has been corrected and now
documents the actual proof route. The cheap extensions actually added are: `HasWeakGrad.mono`
plus its two `setIntegral` helpers, `H1.grad_ae_eq`, `dirichlet_eq_of_toFun_ae_eq`, and the five
target `def`s. `RobinCaps.lean` does **not** import `RobinCaps/Sobolev/Weak.lean` or
`RobinCaps/Sobolev/Quotient.lean` — the coordinator should add both imports (not done here: the
brief forbids touching other files).

---

## (b) mathlib v4.26.0 capability table

Every signature below was checked by `#check` / by reading the source under
`.lake/packages/mathlib/Mathlib`.

### 1. Fundamental lemma of the calculus of variations — **PRESENT**

`Mathlib/Analysis/Distribution/AEEqOfIntegralContDiff.lean`, lines 188 / 202 / 207.

```lean
theorem MeasureTheory.ae_eq_zero_of_integral_contDiff_smul_eq_zero
    (hf : LocallyIntegrable f μ)
    (h : ∀ g : E → ℝ, ContDiff ℝ ∞ g → HasCompactSupport g → ∫ x, g x • f x ∂μ = 0) :
    ∀ᵐ x ∂μ, f x = 0

theorem MeasureTheory.ae_eq_of_integral_contDiff_smul_eq
    (hf : LocallyIntegrable f μ) (hf' : LocallyIntegrable f' μ)
    (h : ∀ g : E → ℝ, ContDiff ℝ ∞ g → HasCompactSupport g →
      ∫ x, g x • f x ∂μ = ∫ x, g x • f' x ∂μ) :
    ∀ᵐ x ∂μ, f x = f' x

theorem IsOpen.ae_eq_zero_of_integral_contDiff_smul_eq_zero {U : Set E} (hU : IsOpen U)
    (hf : LocallyIntegrableOn f U μ)
    (h : ∀ g : E → ℝ, ContDiff ℝ ∞ g → HasCompactSupport g → tsupport g ⊆ U →
      ∫ x, g x • f x ∂μ = 0) :
    ∀ᵐ x ∂μ, x ∈ U → f x = 0
```
Context: `[NormedAddCommGroup F] [NormedSpace ℝ F] [MeasurableSpace E] [BorelSpace E]`,
`f f' : E → F`, `μ : Measure E`, `E` a finite-dimensional real normed space.
**Used** in `Weak.lean` (`HasWeakGrad.ae_eq`), the `IsOpen` variant.

### 2. `Lp` completeness — **PRESENT**

`Mathlib/MeasureTheory/Function/LpSpace/Complete.lean:394`
```lean
instance MeasureTheory.Lp.instCompleteSpace
    {α} {m : MeasurableSpace α} {p : ℝ≥0∞} {μ : Measure α} {E}
    [NormedAddCommGroup E] [CompleteSpace E] [hp : Fact (1 ≤ p)] : CompleteSpace (Lp E p μ)
```
Note `Weak.lean`'s `H1 D` is built on raw functions plus `MemLp`, *not* on `Lp`, so this
instance is not inherited. Completeness of `H1 D` in the graph norm is **not** available and is
not needed for the min–max architecture (the form engine is purely algebraic/order-theoretic).

### 3. Rellich–Kondrachov compact embedding — **ABSENT**

No `Rellich`, `Kondrachov`, `CompactEmbedding`, `compactEmbedding` anywhere under `Mathlib/`.
What exists is only the *inequality* side, in
`Mathlib/Analysis/FunctionalSpaces/SobolevInequality.lean` (Gagliardo–Nirenberg–Sobolev):
```lean
theorem MeasureTheory.eLpNorm_le_eLpNorm_fderiv [FiniteDimensional ℝ F]
    (μ : Measure E) [μ.IsAddHaarMeasure] {u : E → F} {s : Set E}
    (hu : ContDiff ℝ 1 u) (h2u : Function.support u ⊆ s)
    {p : ℝ≥0} (hp : 1 ≤ p) (h2p : p < Module.finrank ℝ E) (hs : Bornology.IsBounded s) :
    eLpNorm u p μ ≤ eLpNormLESNormFDerivOfLeConst F μ s p p * eLpNorm (fderiv ℝ u) p μ
```
(siblings: `eLpNorm_le_eLpNorm_fderiv_one`, `…_of_eq_inner`, `…_of_eq`, `…_of_le`,
`lintegral_pow_le_pow_lintegral_fderiv`). Note it is stated with `fderiv` and an abstract `E`;
on a product with the sup norm it is therefore *not* directly the Euclidean statement (see (c)).
No compactness. Recorded as the target `RellichEmbedding`.

### 4. Trace inequality / trace operator — **ABSENT**

No `boundaryTrace`, `traceOperator`, `TraceOperator`, `traceInequality` anywhere.
(`Mathlib/Analysis/InnerProductSpace/Trace.lean` is the *operator* trace — unrelated.)
The only trace inequality in the whole ecosystem relevant here is the project's own
one-dimensional one, `RobinCaps/Sobolev/Interval.lean`:
```lean
theorem RobinCaps.Sobolev.H1.trace_ineq (u : H1 ℓ) (hℓ : 0 < ℓ) :
    u.toFun 0 ^ 2 + u.toFun ℓ ^ 2 ≤ max (4 / ℓ) (4 * ℓ) * (mass ℓ u + dirichlet ℓ u)
theorem …trace_ineq_abs  -- same with |·|
theorem …trace_ineq_uniform (L : ℝ) (hL : 0 < L) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ ℓ, L / 2 ≤ ℓ → ℓ ≤ L → ∀ u : H1 ℓ,
      |u.toFun 0| ^ 2 + |u.toFun ℓ| ^ 2 ≤ C * (mass ℓ u + dirichlet ℓ u)
```
with the explicit constant `max (8/L) (4L)`. **This is the seed for the multi-dimensional trace
inequality** (see (c)).

### 5. Surface measure on a sphere — **PARTIALLY PRESENT** (`Measure.toSphere`)

`Mathlib/MeasureTheory/Constructions/HaarToSphere.lean`:
```lean
def MeasureTheory.Measure.toSphere {E} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [MeasurableSpace E] (μ : Measure E) : Measure ↥(Metric.sphere (0 : E) 1) :=
  dim E • ((μ.comap (Subtype.val ∘ (homeomorphUnitSphereProd E).symm)).restrict
    (univ ×ˢ Iio ⟨1, _⟩)).fst

theorem Measure.toSphere_apply' (hs : MeasurableSet s) :
    μ.toSphere s = dim E * μ (Ioo (0:ℝ) 1 • ((↑) '' s))
theorem Measure.toSphere_apply_univ  : μ.toSphere univ = dim E * μ (ball 0 1)
theorem Measure.toSphere_real_apply_univ : μ.toSphere.real univ = dim E * μ.real (ball 0 1)
theorem Measure.measurePreserving_homeomorphUnitSphereProd :
    MeasurePreserving (homeomorphUnitSphereProd E) (μ.comap (↑))
      (μ.toSphere.prod (volumeIoiPow (dim E - 1)))
lemma MeasureTheory.integral_fun_norm_addHaar (f : ℝ → F) :
    ∫ x, f ‖x‖ ∂μ = dim E • μ.real (ball 0 1) • ∫ y in Ioi (0:ℝ), y ^ (dim E - 1) • f y
lemma MeasureTheory.integrable_fun_norm_addHaar :
    Integrable (f ‖·‖) μ ↔ IntegrableOn (fun y : ℝ => y ^ (dim E - 1) • f y) (Ioi 0)
```
Caveats, all load-bearing for us:
* it is a measure on the **unit** sphere `sphere (0:E) 1` only — no `sphere c r`;
* it is **not** identified with `μH[dim E - 1]`: there is no lemma relating `toSphere` to
  `Measure.hausdorffMeasure` anywhere in mathlib (grep for `hausdorffMeasure.*sphere` is empty);
* the polar-coordinate integral formula `integral_fun_norm_addHaar` is only for **radial**
  integrands `f ‖x‖`. There is **no** general `∫_E f = ∫_0^∞ ∫_{S} f(rω) r^{d-1} dω dr`.
  That general slicing must be derived from `measurePreserving_homeomorphUnitSphereProd`.

### 6. Surface measure on a general boundary — **ABSENT**

No `surfaceMeasure`, `boundaryMeasure`, `Measure.toBoundary` (confirms coordinator AUDIT §10.1).
Only the raw Hausdorff measure exists:
```lean
def MeasureTheory.Measure.hausdorffMeasure {X} [EMetricSpace X] [MeasurableSpace X]
    [BorelSpace X] (d : ℝ) : Measure X          -- notation μH[d]
```
(`Mathlib/MeasureTheory/Measure/Hausdorff.lean`). There is `hausdorffMeasure_pi_real`
(`μH[n]` = Lebesgue on `ι → ℝ`) but **no** theorem computing `μH[d-1]` of a parametrised
hypersurface from its Jacobian. This is the single largest missing brick.

### 7. Divergence theorem beyond boxes — **ABSENT**

`Mathlib/MeasureTheory/Integral/DivergenceTheorem.lean` contains exactly:
```lean
theorem MeasureTheory.integral_divergence_of_hasFDerivAt_off_countable (hle : a ≤ b) …
theorem MeasureTheory.integral_divergence_of_hasFDerivAt_off_countable' (hle : a ≤ b)
    (f : Fin (n+1) → ℝⁿ⁺¹ → E) (f' : Fin (n+1) → ℝⁿ⁺¹ → ℝⁿ⁺¹ →L[ℝ] E) (s : Set ℝⁿ⁺¹)
    (hs : s.Countable) (Hc : ∀ i, ContinuousOn (f i) (Icc a b))
    (Hd : ∀ x ∈ (pi univ fun i => Ioo (a i) (b i)) \ s, ∀ i, HasFDerivAt (f i) (f' i x) x)
    (Hi : IntegrableOn (fun x => ∑ i, f' i x (e i)) (Icc a b)) :
    (∫ x in Icc a b, ∑ i, f' i x (e i)) =
      ∑ i, ((∫ x in face i, f i (frontFace i x)) - ∫ x in face i, f i (backFace i x))
theorem MeasureTheory.integral_divergence_of_hasFDerivAt_off_countable_of_equiv
    (eL : F ≃L[ℝ] Fin (n+1) → ℝ) (h_order : ∀ x y, eL x ≤ eL y ↔ x ≤ y)
    (hmp : MeasurePreserving eL volume volume) … (a b : F) (hab : a ≤ b) … 
```
plus the 1-D (`integral_eq_of_hasDerivAt_off_countable`) and 2-D-rectangle
(`integral_divergence_prod_Icc_of_hasFDerivAt_off_countable_of_le`,
`integral2_divergence_prod_of_hasFDerivAt_off_countable`) corollaries.
**All are boxes.** `_of_equiv` only moves the box through an order- and measure-preserving
linear equivalence; the region is still `Icc a b`. `Analysis/BoxIntegral/DivergenceTheorem.lean`
likewise. No `stokes`, no `green`, no curved boundary, no outward normal.
`Weak.lean` uses the `'` version on `[-R,R]ⁿ` — that is the maximum one can currently extract.

### 8. Integration by parts on a ball — **ABSENT**

Follows from 7: there is no divergence theorem on a ball, hence no Green identity
`∫_B ∇u·∇v = -∫_B Δu v + ∫_{∂B} ∂_ν u v`. The only integration by parts in mathlib is
one-dimensional:
```lean
theorem intervalIntegral.integral_mul_deriv_eq_deriv_mul
    (hu : ∀ x ∈ [[a,b]], HasDerivAt u (u' x) x) (hv : ∀ x ∈ [[a,b]], HasDerivAt v (v' x) x)
    (hu' : IntervalIntegrable u' volume a b) (hv' : IntervalIntegrable v' volume a b) :
    ∫ x in a..b, u x * v' x = u b * v b - u a * v a - ∫ x in a..b, u' x * v x
```
(`Mathlib/MeasureTheory/Integral/IntervalIntegral/IntegrationByParts.lean:142`; improper-integral
variant at `MeasureTheory/Integral/IntegralEqImproper.lean:1223`).
**Consequence for the architecture:** integration by parts on the transverse ball
`B_m(R)` must be obtained by *radial* reduction — polar coordinates
(`measurePreserving_homeomorphUnitSphereProd`) plus the 1-D result above — not from a
multi-dimensional divergence theorem. See (c).

### 9. Smooth cutoffs / mollifiers (`ContDiffBump`) — **PRESENT**

`Mathlib/Analysis/Calculus/BumpFunction/Basic.lean:70`
```lean
structure ContDiffBump {E} [NormedAddCommGroup E] [NormedSpace ℝ E] (c : E) where
  (rIn rOut : ℝ)
  rIn_pos : 0 < rIn
  rIn_lt_rOut : rIn < rOut
class HasContDiffBump (E) [NormedAddCommGroup E] [NormedSpace ℝ E] : Prop
```
with `CoeFun` when `[HasContDiffBump E]`; `f = 1` on `closedBall c f.rIn`,
`support f = ball c f.rOut`, `0 ≤ f ≤ 1`, `ContDiff ℝ ∞ f`. Normalisation/mollification:
`Mathlib/Analysis/Calculus/BumpFunction/Normed.lean`
```lean
protected def ContDiffBump.normed (μ : Measure E) : E → ℝ := fun x => f x / ∫ x, f x ∂μ
theorem ContDiffBump.integral_normed [BorelSpace E] [FiniteDimensional ℝ E]
    [IsLocallyFiniteMeasure μ] [μ.IsOpenPosMeasure] : ∫ x, f.normed μ x ∂μ = 1
```
plus `ContDiffBump.convolution_tendsto_right` etc. in `BumpFunction/Convolution.lean`.
`EuclideanSpace ℝ (Fin n)` and `ℝ × EuclideanSpace ℝ (Fin m)` both have `HasContDiffBump`
(finite-dimensional real normed spaces). **This is enough to build every cutoff and every
partition of unity needed below; it is not a gap.**

### Summary table

| capability | v4.26.0 | name |
|---|---|---|
| fundamental lemma of calc. of variations | **present** | `(IsOpen.)ae_eq_zero_of_integral_contDiff_smul_eq_zero` |
| `Lp` completeness | **present** | `MeasureTheory.Lp.instCompleteSpace` |
| Rellich compact embedding | **absent** | — (only GNS `eLpNorm_le_eLpNorm_fderiv`) |
| trace inequality / trace operator | **absent** | — (1-D own: `Sobolev.H1.trace_ineq`) |
| surface measure on a sphere | **partial** | `Measure.toSphere`, `integral_fun_norm_addHaar` |
| surface measure on a general boundary | **absent** | — (only `Measure.hausdorffMeasure`) |
| divergence theorem beyond boxes | **absent** | box-only `integral_divergence_of_hasFDerivAt_off_countable('/_of_equiv)` |
| integration by parts on a ball | **absent** | 1-D only: `intervalIntegral.integral_mul_deriv_eq_deriv_mul` |
| smooth cutoffs / mollifiers | **present** | `ContDiffBump`, `ContDiffBump.normed` |
| Poincaré inequality | **absent** | — |

---

## (c) Architecture proposal for `thm:main`

### C.0 The ambient type — already fixed by the repo

`RobinCaps/Cap/Basic.lean:37` already declares

```lean
abbrev CapSpace (m : ℕ) : Type := ℝ × EuclideanSpace ℝ (Fin m)
```

and `Cap m`, `Cap.body`, `Cap.Sigma`, `Cap.Gamma` all live there. **The thin domain must use
`CapSpace m`** — reusing it costs nothing and immediately makes the cap layer (`RobinCaps.Cap.*`,
already complete: `Sharp`, `SharpComplete`, `Sphere`, …) usable without transport.

Two facts I verified by `#check`:

1. `MeasureTheory.Measure.volume_eq_prod (α β) : (volume : Measure (α × β)) = volume.prod volume`
   is proved by **`rfl`** (`MeasureTheory/Measure/Prod.lean:179`, instance `prod.measureSpace`).
   So on `CapSpace m` the `volume` used by `∫ p in Ω, …` *is* the product measure and the whole
   Fubini API (`MeasureTheory.integral_integral_swap`, `Measure.prod_restrict`,
   `Measure.restrict_prod_eq_prod_univ`, `MeasureTheory.integral_prod`) applies with no glue.
2. `Prod.norm_def (x : E × F) : ‖x‖ = max ‖x.1‖ ‖x.2‖`. The product carries the **sup norm**.

**Therefore (the NOTE in the brief, made precise):** on `CapSpace m` the number
`‖fderiv ℝ u p‖` is the operator norm of `fderiv ℝ u p : (ℝ × EuclideanSpace ℝ (Fin m)) →L[ℝ] ℝ`
with respect to the sup norm, which is the *dual* ℓ¹-type norm
`|∂ₓ u| + ‖∇_z u‖`, **not** `√(|∂ₓu|² + ‖∇_zu‖²)`. Writing the Dirichlet energy as
`∫ ‖fderiv ℝ u p‖^2` on `CapSpace m` would formalise the **wrong functional**. The Dirichlet
integrand must be spelled out:

```lean
/-- The axial and transverse partial derivatives on `CapSpace m`. -/
def dx (u : CapSpace m → ℝ) (p : CapSpace m) : ℝ := fderiv ℝ u p (1, 0)
def gradZ (u : CapSpace m → ℝ) (p : CapSpace m) : EuclideanSpace ℝ (Fin m) :=
  WithLp.toLp 2 fun i => fderiv ℝ u p (0, EuclideanSpace.single i 1)

/-- `|∇u|² = (∂ₓu)² + ‖∇_z u‖²` — written out, never as `‖fderiv‖²`. -/
def dirichletDensity (u g : …) (p : CapSpace m) : ℝ := (dxComp p) ^ 2 + ‖gradZComp p‖ ^ 2
```

Consequently the ND weak-gradient layer for the thin domain should **not** be
`Weak.HasWeakGrad` verbatim, but a product-adapted twin (see C.1).

There is an inconsistency in the repo that the coordinator must resolve first:
`RobinCaps/Domain/Capsule.lean` defines `capsule m L R : Set (EuclideanSpace ℝ (Fin (m+1)))`
using `axis m = EuclideanSpace.single 0 1` and `Metric.infDist`, i.e. the **Euclidean** ambient
model, whereas `Cap` uses the **product** model. The two are related by the linear homeomorphism
`EuclideanSpace ℝ (Fin (m+1)) ≃ ℝ × EuclideanSpace ℝ (Fin m)` which is measure-preserving but
**not** an isometry. Recommendation: declare `CapSpace m` the official ambient type for the thin
domain and its forms, and prove once a `MeasurePreserving` + "Dirichlet-energy-transport" bridge
to the `Capsule.lean` model (needed anyway for `capsule_counterexample`).

### C.1 The `H¹` layer on the thin domain

```lean
namespace RobinCaps.ThinDomain
/-- `g = (gₓ, g_z)` is a weak gradient of `u` on `Ω ⊆ CapSpace m`. -/
def HasWeakGradP (Ω : Set (CapSpace m)) (u : CapSpace m → ℝ)
    (gx : CapSpace m → ℝ) (gz : CapSpace m → EuclideanSpace ℝ (Fin m)) : Prop :=
  (∀ φ, ContDiff ℝ ∞ φ → HasCompactSupport φ → tsupport φ ⊆ Ω →
     ∫ p in Ω, u p * fderiv ℝ φ p (1, 0) = - ∫ p in Ω, gx p * φ p) ∧
  (∀ φ, ContDiff ℝ ∞ φ → HasCompactSupport φ → tsupport φ ⊆ Ω → ∀ i : Fin m,
     ∫ p in Ω, u p * fderiv ℝ φ p (0, EuclideanSpace.single i 1)
       = - ∫ p in Ω, gz p i * φ p)

structure H1P (Ω : Set (CapSpace m)) where
  toFun : CapSpace m → ℝ
  gx : CapSpace m → ℝ
  gz : CapSpace m → EuclideanSpace ℝ (Fin m)
  memL2 : MemLp toFun 2 (volume.restrict Ω)
  gx_memL2 : MemLp gx 2 (volume.restrict Ω)
  gz_memL2 : MemLp gz 2 (volume.restrict Ω)
  hasWeakGrad : HasWeakGradP Ω toFun gx gz

def dirichletP (u : H1P Ω) : ℝ := ∫ p in Ω, (u.gx p ^ 2 + ‖u.gz p‖ ^ 2)
def massP (u : H1P Ω) : ℝ := ∫ p in Ω, u.toFun p ^ 2
```

**Every proof in `Weak.lean` ports verbatim**, because `Weak.lean` never used the Euclidean norm
of `fderiv` — it is entirely written in terms of `fderiv ℝ φ x (EuclideanSpace.single i 1)`, and
`(1,0)`/`(0, single i 1)` play the same role. In particular:
`HasWeakGradP.{zero,add,smul,congr_ae,mono}`, the `AddCommGroup`/`Module ℝ` instances on
`H1P Ω`, the uniqueness `HasWeakGradP.ae_eq` (the fundamental lemma applies to any
finite-dimensional real normed `E`, so `CapSpace m` is fine), and
`hasWeakGradP_classicalGrad` (the box divergence theorem applies to
`Fin (m+1) → ℝ` and `CapSpace m ≃L[ℝ] (Fin (m+1) → ℝ)` is order- and measure-preserving,
so `integral_divergence_of_hasFDerivAt_off_countable_of_equiv` can be used directly instead of
the hand transport in `Weak.lean`). **Size: ≈700 lines, essentially a mechanical port
(1–2 sessions).**

### C.2 The domain and its boundary, slice-wise

```lean
/-- The thin domain `Ω_R`: bulk cylinder `I_R × B_m(R)` glued to two rescaled caps. -/
def radius (T : ThinData m α L) (R x : ℝ) : ℝ :=   -- the profile, as a function of the axis
  if x ≤ x₋ then R * T.Cm.θ ((x - a) / R - T.Cm.K) else
  if x < x₊ then R else R * T.Cp.θ ((x - b) / R)

def Omega (T : ThinData m α L) (R : ℝ) : Set (CapSpace m) :=
  {p | a < p.1 ∧ p.1 < b ∧ ‖p.2‖ < radius T R p.1}
```

i.e. `Ω_R` is a **domain of revolution described by a radial profile `ρ : ℝ → ℝ`**, and all its
slices are Euclidean balls `B_m(ρ x)`. Everything below is organised around this.

The Robin boundary term is written **slice-wise**, never via a general surface measure — this is
the key move that lets us bypass the absent `μH^{d-1}` machinery:

```lean
/-- Lateral boundary of revolution, parametrised by the profile: for a.e. axial `x`,
the sphere of radius `ρ x` with the area element `ρ(x)^{m-1} √(1 + ρ'(x)²)`. -/
def lateralIntegral (T) (R) (f : CapSpace m → ℝ) : ℝ :=
  ∫ x in a..b, (radius T R x) ^ (m - 1) * Real.sqrt (1 + deriv (radius T R) x ^ 2) *
    ∫ ω, f (x, (radius T R x) • (ω : EuclideanSpace ℝ (Fin m)))
      ∂((volume : Measure (EuclideanSpace ℝ (Fin m))).toSphere)

/-- End-disk integral (only in the flat-end / single-cap case). -/
def endDiskIntegral (T) (R) (x : ℝ) (f) : ℝ := ∫ z in Metric.ball 0 (radius T R x), f (x, z)

def robinFormP (T) (R α) (u : H1P (Omega T R)) : ℝ :=
  dirichletP u + α * (lateralIntegral T R (fun p => (traceP u p) ^ 2) + …end disks…)
```

This is **definitionally** the classical surface integral of revolution, and it is exactly the
formula already used, and already justified, by `RobinCaps/Cap/Basic.lean:94`
(`lateralArea = m ω_m ∫ θ^{m-1} √(1+θ'²)`) and `terminalArea`. **Consistency requirement:** a
target `lateralIntegral_const_one` proving `lateralIntegral T R 1 = Cap.lateralArea …`-shaped
identity, so the two layers are provably the same boundary.

Honest statement to record: this *defines* the boundary measure by the revolution formula
instead of deriving it from `μH^{m}`. The derivation is target `IsBoundaryMeasure` above; until
it is proved, the main theorem is a theorem about the revolution-parametrised Robin form, and
that must be said in the theorem's docstring.

### C.3 What must be built from scratch, in dependency order

**(1) Transverse ball: polar coordinates and the 1-D radial reduction.** ≈400–600 lines.
From `Measure.measurePreserving_homeomorphUnitSphereProd` and `Measure.volumeIoiPow`, prove the
*non-radial* polar formula
```lean
theorem integral_ball_polar (f : EuclideanSpace ℝ (Fin m) → ℝ) (hf : IntegrableOn f (ball 0 R)) :
    ∫ z in Metric.ball (0:EuclideanSpace ℝ (Fin m)) R, f z
      = ∫ r in Ioo (0:ℝ) R, r ^ (m-1) • ∫ ω, f (r • (ω:_)) ∂(volume.toSphere)
```
This is the single most reusable brick: it gives the Dirichlet energy, the mass and the lateral
boundary integral all in the form `∫ᵣ r^{m-1} (∫_{S^{m-1}} …)`.

**(2) Trace inequality on the cylinder via the 1-D trace in the transverse radial variable.**
≈500–800 lines. *This is the deliverable the brief names and it is genuinely within reach.*
Method: for fixed `ω ∈ S^{m-1}` and fixed axial `x`, the function `r ↦ u (x, r•ω)` is an element
of `RobinCaps.Sobolev.H1 R` (the 1-D model of `Interval.lean`) with
`deriv = ⟪∇_z u, ω⟫`; `Sobolev.H1.trace_ineq` gives
`|u(x,R ω)|² ≤ max (4/R) (4R) · (∫₀^R |u|² + ∫₀^R |∂_r u|²)`.
Multiply by `R^{m-1}`, integrate `dω` and `dx`, and use (1) to recognise the right-hand side as
`C(R) (massP u + dirichletP u)` with `C(R) = max (4/R) (4R) · R^{m-1}/…`. Two real
difficulties: (i) the 1-D `H1` model of `Interval.lean` carries the `ftc` field, so this needs a
lemma "a weak-`H¹` function is a.e.-slice-wise absolutely continuous" (an ACL characterisation)
— **budget this separately, ≈400 lines**, or, much cheaper, only prove the trace inequality for
`u` in a dense class (`C¹` up to the boundary, via `H1P.ofCompactSupport`) and carry the
extension to all of `H1P` as an explicit hypothesis/target; (ii) the boundary of `Ω_R` is not a
cylinder in the caps, but the caps are handled by the cap estimates, not by this inequality.
Recommendation: state it on the **bulk cylinder** `I_R × B_m(R)` only. That is all
`eq:global-mass-upper` needs (the `CR·D[F]` term comes from the *1-D* `trace_ineq_uniform`,
which is already proved).

**(3) Transverse ground state on `B_m(R)` and its spectral gap.** *The hardest item; do not
build it from scratch.* A genuine construction of `ψ_R` needs existence of a minimiser of the
Rayleigh quotient, i.e. Rellich (absent), i.e. realistically **1500–3000 lines**. Strong
recommendation: **make `ψ_R` data, not a theorem**:
```lean
/-- A transverse Robin ground state on `B_m(R)`, as explicit data: an `L²`-normalized positive
weak eigenfunction with eigenvalue `ν`, together with the spectral gap `eq:transverse-gap`. -/
structure TransverseGroundState (m : ℕ) (α R : ℝ) where
  psi : EuclideanSpace ℝ (Fin m) → ℝ
  nu : ℝ
  radial : ∀ z, psi z = psiR ‖z‖          -- reduces everything to 1-D
  pos : ∀ z ∈ Metric.ball 0 R, 0 < psi z
  normalized : ∫ z in Metric.ball 0 R, psi z ^ 2 = 1
  weak_eq : ∀ v : H1Ball m R, ∫ z in ball 0 R, ⟪gradOf psi z, v.grad z⟫
              + α * sphereIntegral R (psi * v) = nu * ∫ z in ball 0 R, psi z * v.toFun z
  gap : ∃ c > 0, ∀ v : H1Ball m R,
          (∫ z in ball 0 R, psi z * v.toFun z) = 0 →
            c * R⁻¹^2 * (∫ z in ball 0 R, v.toFun z ^ 2)
              ≤ (dirichletBall v + α * sphereIntegral R (v.toFun ^ 2) - nu * massBall v)
```
Cost: ≈200 lines for the structure + its basic consequences. A *later* unit can construct an
instance: because the ground state is **radial**, `psi` solves a 1-D singular ODE
`-(r^{m-1}ψ')' = ν r^{m-1} ψ` on `(0,R)` with `ψ'(R) = -αψ(R)`, i.e. a Bessel-type equation, and
the project already has a 1-D phase-function machinery (`RobinCaps/Interval/Phase.lean`,
`RobinCaps.Interval.mu`). Constructing `ψ_R` by the radial phase method is the realistic route
and is itself a ≈1000–1500 line unit, **independent of Rellich**. The `O(R)` expansions
`eq:nu-expansion`, `eq:Psi-H1`, `eq:d-R` are then 1-D asymptotics (≈600 lines).

**(4) The exact bulk decomposition `eq:exact-separation`.** ≈800–1200 lines. Given (1) and (3),
this is Fubini plus orthogonality, *not* analysis:
```lean
def F (u : H1P (bulk T R)) (x : ℝ) : ℝ := ∫ z in ball 0 R, u.toFun (x,z) * gs.psi z
def w (u) (p : CapSpace m) : ℝ := u.toFun p - F u p.1 * gs.psi p.2
theorem bulk_mass_split : massP u = ∫ x in I_R, F u x ^ 2 + ∫ p in bulk, w u p ^ 2
theorem bulk_energy_split :
    dirichletP u + α * lateralIntegral … - gs.nu * massP u
      = (∫ x in I_R, deriv (F u) x ^ 2) + T_R (w u)
theorem T_R_lower : c * R⁻¹^2 * ‖w u‖² ≤ T_R (w u)
```
The two cross terms: the axial one vanishes because `⟪∂ₓw, ψ_R⟫ = ∂ₓ⟪w,ψ_R⟫ = 0` (needs
differentiation under the integral sign — `MeasureTheory.hasDerivAt_integral_of_dominated_loc_of_deriv_le`,
**present** in mathlib); the transverse + lateral one cancels by `gs.weak_eq` tested against
`w(x,·)`. `T_R_lower` is `gs.gap`. `F u ∈ Sobolev.H1 ℓ_R` needs the `ftc` field — again
Cauchy–Schwarz plus FTC under the integral sign.

**(5) Cap estimates (`sec:cap-lemma`) and the trial extension `eq:trial-extension`.**
≈700–1000 lines. Rescaling `U(s,z) = R^{m/2} u(b+Rs, Rz)` is a measure-preserving dilation
(`Measure.addHaar_smul`, present); the gluing of the three pieces of `𝒯_R F` into one `H1P`
element needs a "weak gradient glues across a slice of measure zero" lemma — provable from
`HasWeakGradP.mono` plus a cutoff argument with `ContDiffBump`, ≈250 lines.

**(6) Assembly.** ≈300–500 lines, and **the abstract engine is already done**:
`RobinCaps/Spectrum/MainAbstract.lean` provides exactly the two steps needed,
```lean
def BulkComparison (E N : H → ℝ) (a b : V → ℝ) (Z : H → ℝ) (π : H →ₗ[ℝ] V) (h : ℝ) : Prop :=
  (∀ u, a (π u) + h * Z u ≤ E u) ∧ (∀ u, N u ≤ b (π u) + Z u)
theorem minmax_lower_of_bulk_codim … : ρ ≤ minmax E N j
theorem minmax_upper_of_bulk_trial … : minmax E N j ≤ η + δ * γ
```
with `H := H1P (Omega T R)`, `V := Sobolev.H1Q ℓ_R` (the quotient space of
`RobinCaps/Sobolev/Quotient.lean`, which is where `massQ_pos` lives — positive definiteness of
the mass is a hypothesis of `minmax_lower_of_bulk_codim`), `π u := ⟦F u⟧`,
`Z u := ‖w u‖² + C₀R Σ ‖∇g_σ‖²` (`eq:Z-definition`), `h := c₀R⁻²`,
`a := a_R` (`eq:a-R`), `b := b̂_R` (`eq:D-less-a`). The interval inputs
`ℓ_j(R) = μ_j(β₋-CR, β₊-CR; ℓ_R)` and `η_j(R)` come from `RobinCaps.Interval.mu` and
`Quotient.robinMinmaxQ_le_mu` / `mu_le_robinMinmaxQ_of_picone`, both already proved.

### C.4 Rough total

| unit | lines | risk |
|---|---|---|
| (0) `CapSpace` vs `EuclideanSpace` bridge | 250–400 | low |
| (1) `H1P` port of `Weak.lean` to the product | ≈700 | low (mechanical) |
| (2) polar coordinates / radial reduction on the ball | 400–600 | medium |
| (3) cylinder trace inequality from the 1-D trace | 500–800 (+400 for ACL) | medium-high |
| (4) `TransverseGroundState` as a structure | ≈200 | low |
| (4') constructing an instance by the radial phase method | 1000–1500 | high |
| (5) transverse `O(R)` expansions | ≈600 | medium |
| (6) exact bulk decomposition | 800–1200 | medium |
| (7) cap rescaling + gluing + trial extension | 700–1000 | medium-high |
| (8) assembly onto `MainAbstract` | 300–500 | low |
| **total to `thm:main` modulo (4')** | **≈4500–6000** | |
| **total including (4')** | **≈6000–7500** | |

Rellich, a general surface measure, a curved divergence theorem and a general trace operator are
**not** on the critical path under this architecture, and should *not* be attempted: the
revolution parametrisation (C.2), the radial reduction (C.3.1–2) and the ground state as data
(C.3.3) route around all four. That is the main architectural claim of this report.

---

## (d) Recommended `def`-targets to dispatch next

Ordered; each is a one-line precise statement. The first five are already compiled into
`Weak.lean`; the rest are proposed for the new `RobinCaps/ThinDomain/` files.

1. **`RobinCaps.Sobolev.Weak.RellichEmbedding D`** — an `H¹`-bounded sequence in `H1 D` has an
   `L²(D)`-convergent subsequence. *(low priority: not on the critical path.)*
2. **`RobinCaps.Sobolev.Weak.TraceExists D σ`** — there is a linear `T : H1 D → (E → ℝ)`
   agreeing `σ`-a.e. with restriction on `C¹` compactly supported functions and satisfying
   `∫ (Tu)² dσ ≤ C (dirichlet u + mass u)`.
3. **`RobinCaps.Sobolev.Weak.TraceInequality D σ T`** — the boundedness half of 2 for a given `T`.
4. **`RobinCaps.Sobolev.Weak.IsBoundaryMeasure D σ`** — `σ = μH[(n:ℝ)-1] restricted to frontier D`.
5. **`RobinCaps.Sobolev.Weak.RobinCoercive D σ T α`** — `∃ C ≥ 0, ∀ u, -(C * mass u) ≤ robinForm σ T α u`.
6. **`ThinDomain.PolarBall m R`** — `∀ f, IntegrableOn f (ball 0 R) → ∫ z in ball 0 R, f z = ∫ r in Ioo 0 R, r^(m-1) • ∫ ω, f (r • ω) ∂volume.toSphere`.
7. **`ThinDomain.LateralIsHausdorff T R`** — the revolution formula `lateralIntegral` equals
   `∫ over the lateral boundary against μH[m]`; equivalently `lateralIntegral T R 1 = Cap.lateralArea`-style consistency.
8. **`ThinDomain.SliceACL Ω u`** — for `u : H1P Ω`, for a.e. `(x, ω)` the radial slice
   `r ↦ u (x, r•ω)` is an element of `RobinCaps.Sobolev.H1 (radius T R x)` with
   `deriv = ⟪u.gz, ω⟫`. *(the bridge that unlocks target 9.)*
9. **`ThinDomain.CylinderTrace m α R`** — `∃ C ≥ 0, ∀ u : H1P (I_R ×ˢ ball 0 R)`,
   `lateralIntegral … (Tu)² ≤ C * (dirichletP u + massP u)`; the multi-dimensional
   `eq:interval-trace`.
10. **`ThinDomain.HasTransverseGroundState m α R`** — `Nonempty (TransverseGroundState m α R)`,
    i.e. existence of a positive `L²`-normalized radial Robin ground state on `B_m(R)` with
    eigenvalue `ν_R` and gap `λ₂ - ν_R ≥ cR⁻²` (`eq:transverse-gap`).
11. **`ThinDomain.TransverseExpansion m α`** — `R²ν_R = mαR + O(R²)`,
    `‖Ψ_R - ω_m^{-1/2}‖_{H¹(B_m(1))} ≤ CR`, `d_R = √ω_m + O(R²)` (`lem:transverse`).
12. **`ThinDomain.BulkSeparation T R gs`** — `eq:exact-separation` + `eq:bulk-mass` + `eq:T-bound`
    as a single conjunction for `u : H1P (bulk T R)`.
13. **`ThinDomain.CapEstimates T R gs`** — `eq:cap-lower`, `eq:cap-mass-bound`, `lem:cap-upper`
    for the rescaled cap functions.
14. **`ThinDomain.GlueH1 T R`** — three `H1P` pieces with matching entrance traces glue to one
    `H1P (Omega T R)` element (needed for `eq:trial-extension`).
15. **`ThinDomain.GlobalComparison T R gs`** — `RobinCaps.Spectrum.BulkComparison E_R N_R a_R b̂_R Z_R π (c₀R⁻²)`,
    i.e. `eq:global-energy-lower` ∧ `eq:global-mass-upper`. **This is the single target that,
    combined with the already-proved `minmax_lower_of_bulk_codim` /
    `minmax_upper_of_bulk_trial` and the already-proved interval layer, yields `thm:main`.**

Dispatch order: 6 → 8 → 9 in one track (analysis on the ball), 10 → 11 in a second track
(1-D radial ODE, reuses `Interval/Phase.lean`), 12 → 13 → 14 → 15 in a third once 6 and 10 land.
Targets 1–5 and 7 are independent and can be left dormant; the architecture in (c) does not
depend on them.
