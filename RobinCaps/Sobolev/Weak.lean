import Mathlib

/-!
# U-SOB-ND: the multi-dimensional weak-`H¹` layer (definitional foundation)

This file lays the *definitional* foundation of the multi-dimensional Sobolev layer needed by
the main theorem of the Robin end-cap project (`eq:robin-form`, `eq:minmax` of
`reference/robin_endcaps_corrected_en.tex`, lines 118–140):

`q_D[u] = ∫_D |∇u|² + α ∫_{∂D} |Tr u|² dℋ^{d-1}`, `N_D[u] = ∫_D |u|²`, `u ∈ H¹(D)`.

mathlib `v4.26.0` has no Sobolev spaces, no weak derivatives and no trace operator, so we
build the layer ourselves, in the most explicit form possible.

## Contents

* `HasWeakGrad D u g`: `g : E → E` is a weak gradient of `u : E → ℝ` on the open set `D`, i.e.
  `∫_D u ∂ᵢφ = -∫_D gᵢ φ` for every test function `φ` (smooth, compactly supported, with
  `tsupport φ ⊆ D`) and every coordinate `i`.  Here `E = EuclideanSpace ℝ (Fin n)` and
  `∂ᵢφ x = fderiv ℝ φ x (EuclideanSpace.single i 1)`.
* `H1 D`: a function `u` together with a chosen weak gradient `g`, both in `L²(D)`.
* The vector-space structure on `H1 D` (`AddCommGroup`, `Module ℝ`), obtained by pulling back
  along the injective map `u ↦ (u.toFun, u.grad)`.
* `HasWeakGrad.ae_eq`: **uniqueness of the weak gradient** almost everywhere on `D`.  This is
  the one substantive theorem of the file; it is deduced from mathlib's fundamental lemma of the
  calculus of variations `IsOpen.ae_eq_zero_of_integral_contDiff_smul_eq_zero`.
* The forms `dirichlet`, `mass` (nonnegative, a.e.-invariant) and `robinForm σ T α`, where the
  boundary measure `σ` and the trace map `T` are explicit *parameters* to be supplied by later
  work; nothing about the boundary is invented here.
* `hasWeakGrad_classicalGrad`: a `C¹` function has its classical gradient (`classicalGrad`,
  the vector of the partial derivatives `∂ᵢu`) as a weak gradient on every set `D`.  This is
  proved by integration by parts, which is obtained from mathlib's box divergence theorem
  `MeasureTheory.integral_divergence_of_hasFDerivAt_off_countable'` applied to a box
  `[-R,R]ⁿ` containing `tsupport φ` (all face terms vanish), transported from
  `Fin n → ℝ` to `EuclideanSpace ℝ (Fin n)` along `PiLp.volume_preserving_toLp`.
  Consequently `H1.ofCompactSupport` exhibits every compactly supported `C¹` function as an
  element of `H1 D`, so the space is nonempty in a nontrivial way.
* `HasWeakGrad.mono`: weak gradients localize along `D' ⊆ D`.
* A final section of `Prop`-valued **targets** (`RellichEmbedding`, `TraceInequality`,
  `RobinCoercive`, `TraceExists`) — statements only, for the coordinator to dispatch; none of
  them is used as a hypothesis anywhere above.

## Honest modelling remarks

* Elements of `H1 D` carry *representatives*: equality in `H1 D` is pointwise equality of the
  pair `(toFun, grad)`, not a.e. equality.  The quotient by a.e. equality can be taken later;
  the form values `dirichlet`, `mass` below are shown to be a.e.-invariant, and the weak gradient
  is a.e. unique (`HasWeakGrad.ae_eq`), so nothing is lost at the level of the forms.
* The test-function integrals are Bochner integrals over `D` (i.e. against `volume.restrict D`).
  The integrability of `u ∂ᵢφ` and `gᵢ φ` needed for the algebra is proved from
  `L² × (continuous, compactly supported) ⊆ L¹` (Hölder with exponents `2, 2`).

Everything below is proved without `sorry`, `axiom` or `admit`.
-/

open MeasureTheory Set Filter

open scoped ContDiff ENNReal Topology

namespace RobinCaps.Sobolev.Weak

noncomputable section

variable {n : ℕ}

/-- The ambient Euclidean space `ℝⁿ`. -/
local notation "E" => EuclideanSpace ℝ (Fin n)

/-- The Hölder triple `(2, 2, 1)`: `2⁻¹ + 2⁻¹ = 1⁻¹`.  mathlib does not register this as a
global instance; it is what makes `L² · L² ⊆ L¹` available through `MemLp.integrable_mul`. -/
instance instHolderTripleTwoTwoOne : ENNReal.HolderTriple 2 2 1 :=
  ⟨by rw [inv_one]; exact ENNReal.inv_two_add_inv_two⟩

/-! ### Test functions and the weak gradient -/

/-- **Weak gradient.**  `g : E → E` is a weak gradient of `u : E → ℝ` on `D` if for every
test function `φ` (smooth, compactly supported, with `tsupport φ ⊆ D`) and every coordinate `i`,

`∫_D u · ∂ᵢφ = - ∫_D gᵢ · φ`,

where `∂ᵢφ x = fderiv ℝ φ x (EuclideanSpace.single i 1)` and `gᵢ x = g x i`. -/
def HasWeakGrad (D : Set E) (u : E → ℝ) (g : E → E) : Prop :=
  ∀ φ : E → ℝ, ContDiff ℝ ∞ φ → HasCompactSupport φ → tsupport φ ⊆ D →
    ∀ i : Fin n, ∫ x in D, u x * fderiv ℝ φ x (EuclideanSpace.single i 1)
      = - ∫ x in D, g x i * φ x

/-! ### Integrability of the pairings -/

section Integrability

variable {μ : Measure (EuclideanSpace ℝ (Fin n))} [IsFiniteMeasureOnCompacts μ]

/-- A smooth compactly supported function is in `L²(μ)`. -/
theorem memLp_two_of_test {φ : E → ℝ} (hφ : ContDiff ℝ ∞ φ) (hφc : HasCompactSupport φ) :
    MemLp φ 2 μ :=
  hφ.continuous.memLp_of_hasCompactSupport hφc

/-- The partial derivative `∂ᵢφ` of a smooth compactly supported function is in `L²(μ)`. -/
theorem memLp_two_pderiv {φ : E → ℝ} (hφ : ContDiff ℝ ∞ φ) (hφc : HasCompactSupport φ)
    (i : Fin n) :
    MemLp (fun x => fderiv ℝ φ x (EuclideanSpace.single i 1)) 2 μ := by
  have hc : Continuous fun x => fderiv ℝ φ x (EuclideanSpace.single i 1) :=
    (hφ.continuous_fderiv (by simp)).clm_apply continuous_const
  have hs : HasCompactSupport fun x => fderiv ℝ φ x (EuclideanSpace.single i 1) :=
    hφc.fderiv_apply ℝ (EuclideanSpace.single i 1)
  exact hc.memLp_of_hasCompactSupport hs

/-- `u ∈ L²` times `∂ᵢφ` is integrable. -/
theorem integrable_mul_pderiv {u : E → ℝ} (hu : MemLp u 2 μ) {φ : E → ℝ}
    (hφ : ContDiff ℝ ∞ φ) (hφc : HasCompactSupport φ) (i : Fin n) :
    Integrable (fun x => u x * fderiv ℝ φ x (EuclideanSpace.single i 1)) μ :=
  hu.integrable_mul (memLp_two_pderiv hφ hφc i)

omit [IsFiniteMeasureOnCompacts μ] in
/-- The `i`-th component of a vector field in `L²` is in `L²`. -/
theorem memLp_two_comp {g : E → E} (hg : MemLp g 2 μ) (i : Fin n) :
    MemLp (fun x => g x i) 2 μ := by
  have h := (EuclideanSpace.proj i : E →L[ℝ] ℝ).comp_memLp' hg
  simpa [Function.comp_def] using h

/-- `gᵢ ∈ L²` times a test function `φ` is integrable. -/
theorem integrable_comp_mul {g : E → E} (hg : MemLp g 2 μ) {φ : E → ℝ}
    (hφ : ContDiff ℝ ∞ φ) (hφc : HasCompactSupport φ) (i : Fin n) :
    Integrable (fun x => g x i * φ x) μ :=
  (memLp_two_comp hg i).integrable_mul (memLp_two_of_test hφ hφc)

end Integrability

/-! ### Algebra of weak gradients -/

namespace HasWeakGrad

variable {D : Set (EuclideanSpace ℝ (Fin n))}

/-- The zero function has weak gradient `0`. -/
theorem zero : HasWeakGrad D (fun _ => (0 : ℝ)) (fun _ => (0 : E)) := by
  intro φ _ _ _ i
  simp

/-- Weak gradients add. -/
theorem add {u v : E → ℝ} {g h : E → E}
    (hu : MemLp u 2 (volume.restrict D)) (hv : MemLp v 2 (volume.restrict D))
    (hg : MemLp g 2 (volume.restrict D)) (hh : MemLp h 2 (volume.restrict D))
    (hug : HasWeakGrad D u g) (hvh : HasWeakGrad D v h) :
    HasWeakGrad D (u + v) (g + h) := by
  intro φ hφ hφc hφs i
  have h1 := hug φ hφ hφc hφs i
  have h2 := hvh φ hφ hφc hφs i
  have hL : (∫ x in D, (u + v) x * fderiv ℝ φ x (EuclideanSpace.single i 1))
      = (∫ x in D, u x * fderiv ℝ φ x (EuclideanSpace.single i 1))
        + ∫ x in D, v x * fderiv ℝ φ x (EuclideanSpace.single i 1) := by
    rw [← integral_add (integrable_mul_pderiv hu hφ hφc i) (integrable_mul_pderiv hv hφ hφc i)]
    congr 1
    funext x
    simp only [Pi.add_apply]
    ring
  have hR : (∫ x in D, (g + h) x i * φ x)
      = (∫ x in D, g x i * φ x) + ∫ x in D, h x i * φ x := by
    rw [← integral_add (integrable_comp_mul hg hφ hφc i) (integrable_comp_mul hh hφ hφc i)]
    congr 1
    funext x
    simp only [Pi.add_apply, PiLp.add_apply]
    ring
  rw [hL, hR, h1, h2]
  ring

/-- Weak gradients are compatible with real scalar multiplication. -/
theorem smul (c : ℝ) {u : E → ℝ} {g : E → E} (hug : HasWeakGrad D u g) :
    HasWeakGrad D (c • u) (c • g) := by
  intro φ hφ hφc hφs i
  have h1 := hug φ hφ hφc hφs i
  have hL : (∫ x in D, (c • u) x * fderiv ℝ φ x (EuclideanSpace.single i 1))
      = c * ∫ x in D, u x * fderiv ℝ φ x (EuclideanSpace.single i 1) := by
    rw [← integral_const_mul]
    congr 1
    funext x
    simp only [Pi.smul_apply, smul_eq_mul]
    ring
  have hR : (∫ x in D, (c • g) x i * φ x) = c * ∫ x in D, g x i * φ x := by
    rw [← integral_const_mul]
    congr 1
    funext x
    simp only [Pi.smul_apply, PiLp.smul_apply, smul_eq_mul]
    ring
  rw [hL, hR, h1]
  ring

/-- The weak-gradient relation only depends on the a.e.-classes of `u` and `g` on `D`. -/
theorem congr_ae {u u' : E → ℝ} {g g' : E → E}
    (hu : u =ᵐ[volume.restrict D] u') (hg : g =ᵐ[volume.restrict D] g')
    (h : HasWeakGrad D u g) : HasWeakGrad D u' g' := by
  intro φ hφ hφc hφs i
  have h1 := h φ hφ hφc hφs i
  have hL : (∫ x in D, u' x * fderiv ℝ φ x (EuclideanSpace.single i 1))
      = ∫ x in D, u x * fderiv ℝ φ x (EuclideanSpace.single i 1) := by
    apply integral_congr_ae
    filter_upwards [hu] with x hx
    rw [hx]
  have hR : (∫ x in D, g' x i * φ x) = ∫ x in D, g x i * φ x := by
    apply integral_congr_ae
    filter_upwards [hg] with x hx
    rw [hx]
  rw [hL, hR, h1]

/-- A test function supported in `S` only sees `S`: for `tsupport φ ⊆ S` the integral of
`u · ∂ᵢφ` over `S` is the integral over the whole space. -/
theorem setIntegral_mul_pderiv_eq_integral {u : E → ℝ} {φ : E → ℝ} (i : Fin n) {S : Set E}
    (hS : tsupport φ ⊆ S) :
    (∫ x in S, u x * fderiv ℝ φ x (EuclideanSpace.single i 1))
      = ∫ x, u x * fderiv ℝ φ x (EuclideanSpace.single i 1) := by
  apply setIntegral_eq_integral_of_forall_compl_eq_zero
  intro x hx
  have hxs : x ∉ tsupport φ := fun h => hx (hS h)
  have hd : fderiv ℝ φ x = 0 :=
    Function.notMem_support.1 fun h => hxs (support_fderiv_subset ℝ h)
  rw [hd]
  simp

/-- The companion statement for the right-hand pairing `gᵢ · φ`. -/
theorem setIntegral_comp_mul_eq_integral {g : E → E} {φ : E → ℝ} (i : Fin n) {S : Set E}
    (hS : tsupport φ ⊆ S) :
    (∫ x in S, g x i * φ x) = ∫ x, g x i * φ x := by
  apply setIntegral_eq_integral_of_forall_compl_eq_zero
  intro x hx
  rw [image_eq_zero_of_notMem_tsupport fun h => hx (hS h)]
  simp

/-- **Locality of weak gradients.**  If `D' ⊆ D` and `g` is a weak gradient of `u` on `D`, then
`g` is a weak gradient of `u` on `D'`: a test function supported in `D'` is a test function
supported in `D`, and both sides of the defining identity are unchanged when the domain of
integration is shrunk from `D` to `D'`. -/
theorem mono {D D' : Set E} (hsub : D' ⊆ D) {u : E → ℝ} {g : E → E}
    (h : HasWeakGrad D u g) : HasWeakGrad D' u g := by
  intro φ hφ hφc hφs i
  have hφsD : tsupport φ ⊆ D := hφs.trans hsub
  rw [setIntegral_mul_pderiv_eq_integral (u := u) i hφs,
    setIntegral_comp_mul_eq_integral (g := g) i hφs,
    ← setIntegral_mul_pderiv_eq_integral (u := u) i hφsD,
    ← setIntegral_comp_mul_eq_integral (g := g) i hφsD]
  exact h φ hφ hφc hφsD i

end HasWeakGrad

/-! ### Uniqueness of the weak gradient (fundamental lemma of the calculus of variations) -/

/-- **Uniqueness of the weak gradient.**  Two `L²` weak gradients of the same function on an
open set `D` agree almost everywhere on `D`.  Proved from mathlib's fundamental lemma of the
calculus of variations `IsOpen.ae_eq_zero_of_integral_contDiff_smul_eq_zero`, applied
coordinatewise to `g - g'`. -/
theorem HasWeakGrad.ae_eq {D : Set E} (hD : IsOpen D) {u : E → ℝ} {g g' : E → E}
    (hg : MemLp g 2 (volume.restrict D)) (hg' : MemLp g' 2 (volume.restrict D))
    (h : HasWeakGrad D u g) (h' : HasWeakGrad D u g') :
    g =ᵐ[volume.restrict D] g' := by
  -- coordinatewise vanishing of `g - g'` in the sense of distributions
  have hcoord : ∀ i : Fin n, ∀ᵐ x ∂(volume.restrict D), x ∈ D → g x i - g' x i = 0 := by
    intro i
    have hloc : LocallyIntegrableOn (fun x => g x i - g' x i) D (volume.restrict D) := by
      have hmem : MemLp (fun x => g x i - g' x i) 2 (volume.restrict D) :=
        (memLp_two_comp hg i).sub (memLp_two_comp hg' i)
      exact (hmem.locallyIntegrable (by norm_num)).locallyIntegrableOn D
    refine hD.ae_eq_zero_of_integral_contDiff_smul_eq_zero hloc ?_
    intro φ hφ hφc hφs
    have h1 := h φ hφ hφc hφs i
    have h2 := h' φ hφ hφc hφs i
    have hsplit : (∫ x, φ x • (g x i - g' x i) ∂(volume.restrict D))
        = (∫ x in D, g x i * φ x) - ∫ x in D, g' x i * φ x := by
      rw [← integral_sub (integrable_comp_mul hg hφ hφc i) (integrable_comp_mul hg' hφ hφc i)]
      congr 1
      funext x
      simp only [smul_eq_mul]
      ring
    rw [hsplit]
    linarith [h1, h2]
  have hall : ∀ᵐ x ∂(volume.restrict D), ∀ i : Fin n, x ∈ D → g x i - g' x i = 0 :=
    ae_all_iff.2 hcoord
  filter_upwards [hall, ae_restrict_mem hD.measurableSet] with x hx hxD
  ext i
  exact sub_eq_zero.1 (hx i hxD)

/-! ### The weak Sobolev space `H¹(D)` -/

/-- **The multi-dimensional weak Sobolev layer `H¹(D)`.**

An element is a function `toFun : E → ℝ` together with a chosen weak gradient `grad : E → E`,
both square integrable on `D`.  Equality of elements is equality of the pair of representatives
(see the module docstring). -/
structure H1 (D : Set E) where
  /-- The underlying function. -/
  toFun : E → ℝ
  /-- The chosen weak gradient. -/
  grad : E → E
  /-- `toFun ∈ L²(D)`. -/
  memL2 : MemLp toFun 2 (volume.restrict D)
  /-- `grad ∈ L²(D; ℝⁿ)`. -/
  grad_memL2 : MemLp grad 2 (volume.restrict D)
  /-- `grad` is a weak gradient of `toFun` on `D`. -/
  hasWeakGrad : HasWeakGrad D toFun grad

namespace H1

variable {D : Set (EuclideanSpace ℝ (Fin n))}

/-- The pair of representatives `(u, ∇u)`. -/
def toPair (u : H1 D) : (E → ℝ) × (E → E) := (u.toFun, u.grad)

@[ext]
theorem ext {u v : H1 D} (h₁ : u.toFun = v.toFun) (h₂ : u.grad = v.grad) : u = v := by
  cases u
  cases v
  simp_all

theorem toPair_injective : Function.Injective (toPair : H1 D → (E → ℝ) × (E → E)) := by
  intro u v h
  exact H1.ext (congrArg Prod.fst h) (congrArg Prod.snd h)

/-- The zero element. -/
def zero : H1 D where
  toFun := fun _ => 0
  grad := fun _ => 0
  memL2 := MemLp.zero
  grad_memL2 := MemLp.zero
  hasWeakGrad := HasWeakGrad.zero

/-- Pointwise sum. -/
def add (u v : H1 D) : H1 D where
  toFun := u.toFun + v.toFun
  grad := u.grad + v.grad
  memL2 := u.memL2.add v.memL2
  grad_memL2 := u.grad_memL2.add v.grad_memL2
  hasWeakGrad :=
    HasWeakGrad.add u.memL2 v.memL2 u.grad_memL2 v.grad_memL2 u.hasWeakGrad v.hasWeakGrad

/-- Real scalar multiple. -/
def smul (c : ℝ) (u : H1 D) : H1 D where
  toFun := c • u.toFun
  grad := c • u.grad
  memL2 := u.memL2.const_smul c
  grad_memL2 := u.grad_memL2.const_smul c
  hasWeakGrad := HasWeakGrad.smul c u.hasWeakGrad

instance instZero : Zero (H1 D) := ⟨H1.zero⟩
instance instAdd : Add (H1 D) := ⟨H1.add⟩
instance instSMul : SMul ℝ (H1 D) := ⟨H1.smul⟩
instance instSMulNat : SMul ℕ (H1 D) := ⟨fun k u => (k : ℝ) • u⟩

@[simp] theorem zero_toFun : (0 : H1 D).toFun = fun _ => (0 : ℝ) := rfl
@[simp] theorem zero_grad : (0 : H1 D).grad = fun _ => (0 : E) := rfl
@[simp] theorem add_toFun (u v : H1 D) : (u + v).toFun = u.toFun + v.toFun := rfl
@[simp] theorem add_grad (u v : H1 D) : (u + v).grad = u.grad + v.grad := rfl
@[simp] theorem smul_toFun (c : ℝ) (u : H1 D) : (c • u).toFun = c • u.toFun := rfl
@[simp] theorem smul_grad (c : ℝ) (u : H1 D) : (c • u).grad = c • u.grad := rfl

theorem toPair_zero : toPair (0 : H1 D) = 0 := rfl
theorem toPair_add (u v : H1 D) : toPair (u + v) = toPair u + toPair v := rfl
theorem toPair_smul (c : ℝ) (u : H1 D) : toPair (c • u) = c • toPair u := rfl

theorem toPair_nsmul (u : H1 D) (k : ℕ) : toPair (k • u) = k • toPair u := by
  change toPair ((k : ℝ) • u) = k • toPair u
  rw [toPair_smul, Nat.cast_smul_eq_nsmul]

instance instAddCommMonoid : AddCommMonoid (H1 D) :=
  Function.Injective.addCommMonoid (toPair : H1 D → (E → ℝ) × (E → E)) toPair_injective
    toPair_zero toPair_add toPair_nsmul

instance instModule : Module ℝ (H1 D) :=
  Function.Injective.module ℝ
    { toFun := toPair, map_zero' := toPair_zero, map_add' := toPair_add }
    toPair_injective toPair_smul

instance instAddCommGroup : AddCommGroup (H1 D) :=
  Module.addCommMonoidToAddCommGroup ℝ

end H1

/-! ### The forms -/

/-- The Dirichlet energy `∫_D |∇u|²`. -/
def dirichlet {D : Set E} (u : H1 D) : ℝ := ∫ x in D, ‖u.grad x‖ ^ 2

/-- The `L²` mass `N_D[u] = ∫_D |u|²` (`eq:robin-form`). -/
def mass {D : Set E} (u : H1 D) : ℝ := ∫ x in D, u.toFun x ^ 2

/-- **The Robin form** `q_D[u] = ∫_D |∇u|² + α ∫ |T u|² dσ` (`eq:robin-form`), with the boundary
measure `σ` (intended: `ℋ^{n-1}` on `∂D`) and the trace map `T` (intended: the boundary trace
`H¹(D) → L²(∂D)`) supplied as explicit parameters.  Neither exists in mathlib `v4.26.0`; they
are inputs of later work, not hidden assumptions. -/
def robinForm {D : Set E} (σ : Measure E) (T : H1 D → (E → ℝ)) (α : ℝ) (u : H1 D) : ℝ :=
  dirichlet u + α * ∫ x, (T u x) ^ 2 ∂σ

theorem dirichlet_nonneg {D : Set E} (u : H1 D) : 0 ≤ dirichlet u :=
  integral_nonneg fun _ => by positivity

theorem mass_nonneg {D : Set E} (u : H1 D) : 0 ≤ mass u :=
  integral_nonneg fun _ => sq_nonneg _

/-- The Robin form is nonnegative for `α ≥ 0`. -/
theorem robinForm_nonneg {D : Set E} (σ : Measure E) (T : H1 D → (E → ℝ)) {α : ℝ}
    (hα : 0 ≤ α) (u : H1 D) : 0 ≤ robinForm σ T α u :=
  add_nonneg (dirichlet_nonneg u)
    (mul_nonneg hα (integral_nonneg fun _ => sq_nonneg _))

/-- The mass only depends on the a.e.-class of the representative on `D`. -/
theorem mass_congr_ae {D : Set E} {u v : H1 D} (h : u.toFun =ᵐ[volume.restrict D] v.toFun) :
    mass u = mass v := by
  unfold mass
  apply integral_congr_ae
  filter_upwards [h] with x hx
  rw [hx]

/-- The Dirichlet energy only depends on the a.e.-class of the gradient on `D`. -/
theorem dirichlet_congr_ae {D : Set E} {u v : H1 D} (h : u.grad =ᵐ[volume.restrict D] v.grad) :
    dirichlet u = dirichlet v := by
  unfold dirichlet
  apply integral_congr_ae
  filter_upwards [h] with x hx
  rw [hx]

/-- On an open set the Dirichlet energy of `u` does not depend on the *choice* of the weak
gradient: any two elements of `H1 D` with the same underlying function have the same energy. -/
theorem dirichlet_eq_of_toFun_eq {D : Set E} (hD : IsOpen D) {u v : H1 D}
    (h : u.toFun = v.toFun) : dirichlet u = dirichlet v :=
  dirichlet_congr_ae (HasWeakGrad.ae_eq hD u.grad_memL2 v.grad_memL2 u.hasWeakGrad
    (h ▸ v.hasWeakGrad))

/-- On an open set the *chosen* weak gradient is determined a.e. by the a.e.-class of the
underlying function: if `u.toFun = v.toFun` a.e. on `D`, then `u.grad = v.grad` a.e. on `D`. -/
theorem H1.grad_ae_eq {D : Set E} (hD : IsOpen D) {u v : H1 D}
    (h : u.toFun =ᵐ[volume.restrict D] v.toFun) : u.grad =ᵐ[volume.restrict D] v.grad :=
  HasWeakGrad.ae_eq hD u.grad_memL2 v.grad_memL2 u.hasWeakGrad
    (HasWeakGrad.congr_ae h.symm (Filter.EventuallyEq.refl _ _) v.hasWeakGrad)

/-- **Both forms descend to a.e.-classes.**  On an open set, two elements of `H1 D` whose
underlying functions agree a.e. on `D` have the same mass and the same Dirichlet energy.  This
is what makes `dirichlet`, `mass` (and hence `robinForm`) well defined on the quotient of
`H1 D` by a.e. equality, even though `H1 D` itself carries representatives. -/
theorem dirichlet_eq_of_toFun_ae_eq {D : Set E} (hD : IsOpen D) {u v : H1 D}
    (h : u.toFun =ᵐ[volume.restrict D] v.toFun) : dirichlet u = dirichlet v :=
  dirichlet_congr_ae (H1.grad_ae_eq hD h)

/-- Mass and Dirichlet energy are compatible with scaling: `N[c u] = c² N[u]`. -/
theorem mass_smul {D : Set E} (c : ℝ) (u : H1 D) : mass (c • u) = c ^ 2 * mass u := by
  unfold mass
  rw [← integral_const_mul]
  congr 1
  funext x
  simp only [H1.smul_toFun, Pi.smul_apply, smul_eq_mul]
  ring

/-- `dirichlet (c • u) = c² dirichlet u`. -/
theorem dirichlet_smul {D : Set E} (c : ℝ) (u : H1 D) :
    dirichlet (c • u) = c ^ 2 * dirichlet u := by
  unfold dirichlet
  rw [← integral_const_mul]
  congr 1
  funext x
  simp only [H1.smul_grad, Pi.smul_apply, norm_smul, Real.norm_eq_abs, mul_pow, sq_abs]

/-! ### Integration by parts on `ℝⁿ` and classical gradients

mathlib's divergence theorem `MeasureTheory.integral_divergence_of_hasFDerivAt_off_countable'`
is stated on boxes `Icc a b ⊆ Fin (m+1) → ℝ`.  For a `C¹` function with compact support we
choose a box containing the support; the face terms vanish, and the box integral equals the
integral over the whole space.  We then transport to `EuclideanSpace ℝ (Fin n)` along the
volume-preserving equivalence `WithLp.toLp 2`. -/

/-- On the box model `Fin (m+1) → ℝ`, the integral of a partial derivative of a `C¹` function
with compact support vanishes. -/
theorem integral_fderiv_single_eq_zero_pi {m : ℕ} (G : (Fin (m + 1) → ℝ) → ℝ)
    (hG : ContDiff ℝ 1 G) (hGc : HasCompactSupport G) (i : Fin (m + 1)) :
    ∫ y, fderiv ℝ G y (Pi.single i 1) = 0 := by
  classical
  -- a radius beyond which `G` vanishes
  obtain ⟨r, hr⟩ := (Metric.isBounded_iff_subset_closedBall (0 : Fin (m + 1) → ℝ)).1
    hGc.isBounded
  set R : ℝ := max r 0 + 1 with hRdef
  have hrR : r < R := by
    have : r ≤ max r 0 := le_max_left _ _
    linarith
  have hR0 : 0 < R := by
    have : (0 : ℝ) ≤ max r 0 := le_max_right _ _
    linarith
  have hnot : ∀ y : Fin (m + 1) → ℝ, R ≤ ‖y‖ → y ∉ tsupport G := by
    intro y hy hmem
    have h1 : ‖y‖ ≤ r := by simpa [mem_closedBall_zero_iff] using hr hmem
    linarith
  have hG0 : ∀ y : Fin (m + 1) → ℝ, R ≤ ‖y‖ → G y = 0 := fun y hy =>
    image_eq_zero_of_notMem_tsupport (hnot y hy)
  have hDG0 : ∀ y : Fin (m + 1) → ℝ, R ≤ ‖y‖ → fderiv ℝ G y = 0 := fun y hy =>
    Function.notMem_support.1 fun h => hnot y hy (support_fderiv_subset ℝ h)
  -- the box `[-R, R]ᵐ⁺¹`
  set a : Fin (m + 1) → ℝ := fun _ => -R with ha
  set b : Fin (m + 1) → ℝ := fun _ => R with hb
  have hab : a ≤ b := fun _ => by simp [ha, hb]; linarith
  -- the field `f = G eᵢ`
  set f : Fin (m + 1) → (Fin (m + 1) → ℝ) → ℝ := fun j y => if j = i then G y else 0 with hf
  set f' : Fin (m + 1) → (Fin (m + 1) → ℝ) → (Fin (m + 1) → ℝ) →L[ℝ] ℝ :=
    fun j y => if j = i then fderiv ℝ G y else 0 with hf'
  have hsum : ∀ y, (∑ j, f' j y (Pi.single j 1)) = fderiv ℝ G y (Pi.single i 1) := by
    intro y
    rw [Finset.sum_eq_single i]
    · simp [hf']
    · intro j _ hj
      simp [hf', hj]
    · intro h
      exact absurd (Finset.mem_univ i) h
  have hf0 : ∀ j y, R ≤ ‖y‖ → f j y = 0 := by
    intro j y hy
    simp only [hf]
    split_ifs
    · exact hG0 y hy
    · rfl
  have hface : ∀ (j : Fin (m + 1)) (c : ℝ), |c| = R → ∀ x : Fin m → ℝ,
      R ≤ ‖Fin.insertNth (α := fun _ => ℝ) j c x‖ := by
    intro j c hc x
    calc R = |c| := hc.symm
      _ = ‖(Fin.insertNth (α := fun _ => ℝ) j c x) j‖ := by
        rw [Fin.insertNth_apply_same, Real.norm_eq_abs]
      _ ≤ ‖Fin.insertNth (α := fun _ => ℝ) j c x‖ := norm_le_pi_norm _ j
  have hfront : ∀ (j : Fin (m + 1)) (x : Fin m → ℝ),
      f j (Fin.insertNth (α := fun _ => ℝ) j (b j) x) = 0 :=
    fun j x => hf0 j _ (hface j (b j) (by simp [hb, abs_of_pos hR0]) x)
  have hback : ∀ (j : Fin (m + 1)) (x : Fin m → ℝ),
      f j (Fin.insertNth (α := fun _ => ℝ) j (a j) x) = 0 :=
    fun j x => hf0 j _ (hface j (a j) (by simp [ha, abs_of_pos hR0]) x)
  have Hc : ∀ j, ContinuousOn (f j) (Icc a b) := by
    intro j
    by_cases hj : j = i
    · simp only [hf, hj, if_true]
      exact hG.continuous.continuousOn
    · simp only [hf, hj, if_false]
      exact continuousOn_const
  have Hd : ∀ x ∈ (Set.pi univ fun j => Ioo (a j) (b j)) \ (∅ : Set (Fin (m + 1) → ℝ)),
      ∀ j, HasFDerivAt (f j) (f' j x) x := by
    intro x _ j
    by_cases hj : j = i
    · simp only [hf, hf', hj, if_true]
      exact (hG.differentiable le_rfl x).hasFDerivAt
    · simp only [hf, hf', hj, if_false]
      exact hasFDerivAt_const 0 x
  have Hi : IntegrableOn (fun x => ∑ j, f' j x (Pi.single j 1)) (Icc a b) := by
    simp only [hsum]
    exact ((hG.continuous_fderiv le_rfl).clm_apply continuous_const).integrableOn_Icc
  have key := integral_divergence_of_hasFDerivAt_off_countable' a b hab f f' ∅ countable_empty
    Hc Hd Hi
  simp only [hsum, hfront, hback, integral_zero, sub_zero, Finset.sum_const_zero] at key
  -- the integral over the box is the integral over the whole space
  have hbox : (∫ x in Icc a b, fderiv ℝ G x (Pi.single i 1))
      = ∫ x, fderiv ℝ G x (Pi.single i 1) := by
    apply setIntegral_eq_integral_of_forall_compl_eq_zero
    intro x hx
    have hRx : R ≤ ‖x‖ := by
      by_contra hlt
      push_neg at hlt
      have hcoord : ∀ j, -R < x j ∧ x j < R := by
        intro j
        have h1 : ‖x j‖ < R := lt_of_le_of_lt (norm_le_pi_norm x j) hlt
        rw [Real.norm_eq_abs] at h1
        exact abs_lt.1 h1
      refine hx ⟨fun j => ?_, fun j => ?_⟩
      · simp only [ha]
        linarith [(hcoord j).1]
      · simp only [hb]
        linarith [(hcoord j).2]
    rw [hDG0 x hRx]
    rfl
  rw [← hbox]
  exact key

/-- On `ℝⁿ = EuclideanSpace ℝ (Fin n)`, the integral of a partial derivative of a `C¹` function
with compact support vanishes: `∫ ∂ᵢF = 0`. -/
theorem integral_fderiv_single_eq_zero (F : E → ℝ)
    (hF : ContDiff ℝ 1 F) (hFc : HasCompactSupport F) (i : Fin n) :
    ∫ x, fderiv ℝ F x (EuclideanSpace.single i 1) = 0 := by
  cases n with
  | zero => exact i.elim0
  | succ m =>
    set L : (Fin (m + 1) → ℝ) ≃L[ℝ] EuclideanSpace ℝ (Fin (m + 1)) :=
      (EuclideanSpace.equiv (Fin (m + 1)) ℝ).symm with hL
    set G : (Fin (m + 1) → ℝ) → ℝ := F ∘ L with hGdef
    have hG : ContDiff ℝ 1 G := hF.comp L.contDiff
    have hGc : HasCompactSupport G := hFc.comp_homeomorph L.toHomeomorph
    have hDG : ∀ y, fderiv ℝ G y (Pi.single i 1)
        = fderiv ℝ F (WithLp.toLp 2 y) (EuclideanSpace.single i 1) := by
      intro y
      rw [hGdef, L.comp_right_fderiv]
      rfl
    have hmp : MeasurePreserving (MeasurableEquiv.toLp 2 (Fin (m + 1) → ℝ)) volume volume :=
      PiLp.volume_preserving_toLp (Fin (m + 1))
    have htrans := hmp.integral_comp' (fun x => fderiv ℝ F x (EuclideanSpace.single i 1))
    rw [← htrans]
    have h0 := integral_fderiv_single_eq_zero_pi G hG hGc i
    simp only [hDG] at h0
    exact h0

/-- **Integration by parts on `ℝⁿ`** against a compactly supported `C¹` function `φ`:
`∫ u ∂ᵢφ = - ∫ ∂ᵢu φ` for every `C¹` function `u` (no decay of `u` is needed). -/
theorem integral_mul_fderiv_eq_neg (u φ : E → ℝ) (hu : ContDiff ℝ 1 u)
    (hφ : ContDiff ℝ 1 φ) (hφc : HasCompactSupport φ) (i : Fin n) :
    ∫ x, u x * fderiv ℝ φ x (EuclideanSpace.single i 1)
      = - ∫ x, fderiv ℝ u x (EuclideanSpace.single i 1) * φ x := by
  have hF : ContDiff ℝ 1 (u * φ) := hu.mul hφ
  have hFc : HasCompactSupport (u * φ) := hφc.mul_left
  have h0 := integral_fderiv_single_eq_zero (u * φ) hF hFc i
  have hprod : ∀ x, fderiv ℝ (u * φ) x (EuclideanSpace.single i 1)
      = u x * fderiv ℝ φ x (EuclideanSpace.single i 1)
        + fderiv ℝ u x (EuclideanSpace.single i 1) * φ x := by
    intro x
    rw [fderiv_mul (hu.differentiable le_rfl x) (hφ.differentiable le_rfl x)]
    simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply, smul_eq_mul]
    ring
  have h1 : Integrable (fun x => u x * fderiv ℝ φ x (EuclideanSpace.single i 1)) :=
    (hu.continuous.mul ((hφ.continuous_fderiv le_rfl).clm_apply continuous_const))
      |>.integrable_of_hasCompactSupport (hφc.fderiv_apply ℝ _).mul_left
  have h2 : Integrable (fun x => fderiv ℝ u x (EuclideanSpace.single i 1) * φ x) :=
    (((hu.continuous_fderiv le_rfl).clm_apply continuous_const).mul hφ.continuous)
      |>.integrable_of_hasCompactSupport hφc.mul_left
  simp only [hprod] at h0
  rw [integral_add h1 h2] at h0
  linarith [h0]

/-- The classical gradient of `u` at `x`: the vector with components `∂ᵢu x`. -/
def classicalGrad (u : E → ℝ) (x : E) : E :=
  WithLp.toLp 2 fun i => fderiv ℝ u x (EuclideanSpace.single i 1)

@[simp] theorem classicalGrad_apply (u : E → ℝ) (x : E) (i : Fin n) :
    classicalGrad u x i = fderiv ℝ u x (EuclideanSpace.single i 1) := rfl

/-- **Sanity check: classical gradients are weak gradients.**  For every `C¹` function `u` and
every set `D`, the classical gradient is a weak gradient of `u` on `D`. -/
theorem hasWeakGrad_classicalGrad (D : Set E) (u : E → ℝ) (hu : ContDiff ℝ 1 u) :
    HasWeakGrad D u (classicalGrad u) := by
  intro φ hφ hφc hφs i
  have hφ1 : ContDiff ℝ 1 φ := hφ.of_le (by simp)
  have hL : (∫ x in D, u x * fderiv ℝ φ x (EuclideanSpace.single i 1))
      = ∫ x, u x * fderiv ℝ φ x (EuclideanSpace.single i 1) := by
    apply setIntegral_eq_integral_of_forall_compl_eq_zero
    intro x hx
    have hxs : x ∉ tsupport φ := fun h => hx (hφs h)
    have hd : fderiv ℝ φ x = 0 :=
      Function.notMem_support.1 fun h => hxs (support_fderiv_subset ℝ h)
    rw [hd]
    simp
  have hR : (∫ x in D, classicalGrad u x i * φ x)
      = ∫ x, fderiv ℝ u x (EuclideanSpace.single i 1) * φ x := by
    simp only [classicalGrad_apply]
    apply setIntegral_eq_integral_of_forall_compl_eq_zero
    intro x hx
    rw [image_eq_zero_of_notMem_tsupport fun h => hx (hφs h)]
    simp
  rw [hL, hR]
  exact integral_mul_fderiv_eq_neg u φ hu hφ1 hφc i

/-- The classical gradient of a `C¹` function is continuous. -/
theorem continuous_classicalGrad (u : E → ℝ) (hu : ContDiff ℝ 1 u) :
    Continuous (classicalGrad u) := by
  have hL : Continuous (WithLp.toLp 2 : (Fin n → ℝ) → E) :=
    (EuclideanSpace.equiv (Fin n) ℝ).symm.continuous
  exact hL.comp (continuous_pi fun i =>
    (hu.continuous_fderiv le_rfl).clm_apply continuous_const)

/-- The classical gradient of a compactly supported function has compact support. -/
theorem hasCompactSupport_classicalGrad (u : E → ℝ) (huc : HasCompactSupport u) :
    HasCompactSupport (classicalGrad u) := by
  have h := (huc.fderiv ℝ).comp_left
    (g := fun L : E →L[ℝ] ℝ => (WithLp.toLp 2 fun i => L (EuclideanSpace.single i 1) : E))
    (by ext i; simp)
  exact h

/-- **A `C¹` function with compact support is an element of `H1 D`**, with its classical
gradient as weak gradient (for any set `D`). -/
def H1.ofCompactSupport (D : Set E) (u : E → ℝ) (hu : ContDiff ℝ 1 u)
    (huc : HasCompactSupport u) : H1 D where
  toFun := u
  grad := classicalGrad u
  memL2 := hu.continuous.memLp_of_hasCompactSupport huc
  grad_memL2 :=
    (continuous_classicalGrad u hu).memLp_of_hasCompactSupport
      (hasCompactSupport_classicalGrad u huc)
  hasWeakGrad := hasWeakGrad_classicalGrad D u hu

@[simp] theorem H1.ofCompactSupport_toFun (D : Set E) (u : E → ℝ) (hu : ContDiff ℝ 1 u)
    (huc : HasCompactSupport u) : (H1.ofCompactSupport D u hu huc).toFun = u := rfl

@[simp] theorem H1.ofCompactSupport_grad (D : Set E) (u : E → ℝ) (hu : ContDiff ℝ 1 u)
    (huc : HasCompactSupport u) : (H1.ofCompactSupport D u hu huc).grad = classicalGrad u := rfl

/-! ### Targets

The following are **statements only** (`Prop`-valued `def`s), recorded so that the coordinator
can dispatch them as self-contained units.  None of them is proved here and none of them is
used as a hypothesis anywhere above; nothing in this file depends on them.  They are the four
capabilities that mathlib `v4.26.0` does not provide and that the Robin main theorem needs
(see `WEAK_REPORT.md`). -/

/-- **Target (boundary measure).**  `σ` is *the* boundary measure of `D`, i.e. the
`(n-1)`-dimensional Hausdorff measure restricted to the topological frontier of `D`.  This is
the measure `dℋ^{d-1}` of `eq:robin-form`; mathlib has `Measure.hausdorffMeasure` but no
surface measure on the boundary of a domain, and in particular no theorem computing it from a
parametrisation of the boundary. -/
def IsBoundaryMeasure (D : Set E) (σ : Measure E) : Prop :=
  σ = (Measure.hausdorffMeasure ((n : ℝ) - 1)).restrict (frontier D)

/-- **Target (trace operator).**  There is a linear boundary trace `T : H1 D → (E → ℝ)` which
(a) extends restriction to the boundary for functions that are `C¹` up to the boundary, and
(b) is bounded from the `H¹` norm to `L²(σ)`.  Part (b) is the trace inequality
`∫_{∂D} |Tu|² dσ ≤ C (∫_D |∇u|² + ∫_D |u|²)`; it is the multi-dimensional analogue of the
one-dimensional `eq:interval-trace` proved in `RobinCaps/Sobolev/Interval.lean`.  Nothing of
the kind exists in mathlib. -/
def TraceExists (D : Set E) (σ : Measure E) : Prop :=
  ∃ T : H1 D → (E → ℝ),
    (∀ u v : H1 D, T (u + v) = T u + T v) ∧
    (∀ (c : ℝ) (u : H1 D), T (c • u) = c • T u) ∧
    (∀ (u : E → ℝ) (hu : ContDiff ℝ 1 u) (huc : HasCompactSupport u),
      T (H1.ofCompactSupport D u hu huc) =ᵐ[σ] u) ∧
    ∃ C : ℝ, 0 ≤ C ∧ ∀ u : H1 D, ∫ x, (T u x) ^ 2 ∂σ ≤ C * (dirichlet u + mass u)

/-- **Target (trace inequality for a given trace).**  The boundedness half of `TraceExists`,
isolated for a trace map `T` that has already been constructed. -/
def TraceInequality (D : Set E) (σ : Measure E) (T : H1 D → (E → ℝ)) : Prop :=
  ∃ C : ℝ, 0 ≤ C ∧ ∀ u : H1 D, ∫ x, (T u x) ^ 2 ∂σ ≤ C * (dirichlet u + mass u)

/-- **Target (Rellich–Kondrachov).**  On a bounded domain, a sequence with bounded `H¹` energy
`dirichlet + mass` has a subsequence converging in `L²(D)`.  This is what turns the min–max
values `eq:minmax` into an actual discrete spectrum; mathlib has no compact Sobolev embedding
(it has the Gagliardo–Nirenberg–Sobolev *inequality*
`MeasureTheory.eLpNorm_le_eLpNorm_fderiv*`, but no compactness). -/
def RellichEmbedding (D : Set E) : Prop :=
  ∀ u : ℕ → H1 D, (∃ C : ℝ, ∀ k, dirichlet (u k) + mass (u k) ≤ C) →
    ∃ (ν : ℕ → ℕ) (v : E → ℝ), StrictMono ν ∧
      Tendsto (fun k => ∫ x in D, ((u (ν k)).toFun x - v x) ^ 2) atTop (nhds 0)

/-- **Target (coercivity of the Robin form).**  For `α ≥ 0` the Robin form is nonnegative
(`robinForm_nonneg`, proved above); for `α < 0` — the case that is *not* needed for the
manuscript, where `α > 0` — one needs the lower bound `-C · N_D[u] ≤ q_D[u]`, which follows
from the trace inequality.  Recorded for completeness of the variational setting. -/
def RobinCoercive (D : Set E) (σ : Measure E) (T : H1 D → (E → ℝ)) (α : ℝ) : Prop :=
  ∃ C : ℝ, 0 ≤ C ∧ ∀ u : H1 D, -(C * mass u) ≤ robinForm σ T α u

end

end RobinCaps.Sobolev.Weak
