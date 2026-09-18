import RobinCaps.Sobolev.Weak
import RobinCaps.Sobolev.Quotient

set_option linter.style.longLine false

/-!
# U-SOB-ND-Q: the multi-dimensional weak space modulo a.e. equality

`RobinCaps/Sobolev/Weak.lean` builds the weak-`H¹` layer `H1 D` out of **pointwise
representatives**: an element is a pair `(u, ∇u)` of honest functions, and equality in `H1 D`
is equality of the pair.  Consequently the mass `N_D[u] = ∫_D u²` is *not* positive definite on
`H1 D` — every function which is a.e. zero on `D` (for instance any nonzero function supported
off `D`) is a nonzero element of zero mass.  The variational values `λ_j(D;α)` of the manuscript
(`eq:minmax`, lines 118–140) are therefore not defined on `H1 D` itself: the abstract form engine
`RobinCaps.Spectrum.minmax` needs `b u > 0` for `u ≠ 0`.

This file removes the obstruction exactly as `RobinCaps/Sobolev/Quotient.lean` does in one
dimension, but with the null space of the *multi-dimensional* model, which is a.e. vanishing
on `D` rather than pointwise vanishing on an interval.

## Contents

* `nullAE D` — the subspace `{u | u.toFun =ᵐ[volume.restrict D] 0}` of `H1 D`, and the quotient
  `H1Q D := H1 D ⧸ nullAE D`.
* `massBilin D`, `dirichletBilin D : H1 D →ₗ[ℝ] H1 D →ₗ[ℝ] ℝ` — the bilinear packaging of the
  two forms of `Weak.lean`, `∫_D u v` and `∫_D ⟪∇u, ∇v⟫`, with `mass u = massBilin D u u`
  (`mass_eq_massBilin`) and `dirichlet u = dirichletBilin D u u` (`dirichlet_eq_dirichletBilin`).
  Integrability of the two pairings comes from Hölder `L² · L² ⊆ L¹`
  (`MeasureTheory.MemLp.integrable_mul` through the triple instance
  `RobinCaps.Sobolev.Weak.instHolderTripleTwoTwoOne` of `Weak.lean`), the gradient pairing being
  expanded coordinatewise (`inner_eq_sum`).
* Both forms vanish as soon as one argument lies in `nullAE D`; for the Dirichlet form this uses
  the a.e. uniqueness of the weak gradient on an **open** `D` (`H1.grad_ae_eq`).  Hence they
  descend through `RobinCaps.Sobolev.descendBilin` to `massBilinQ D`, `dirichletBilinQ hD`, and
  so do the quadratic forms `massQ D`, `dirichletQ hD`.
* An abstract boundary form `bd : H1 D →ₗ[ℝ] H1 D →ₗ[ℝ] ℝ` which vanishes on `nullAE D`
  (`VanishesOnNullAE`) descends likewise (`bdQ`), giving the **Robin form on the quotient**
  `robinFormQ hD bd hbd α = dirichletQ + α · bdQ` (`eq:robin-form`) and the manuscript's
  variational eigenvalues `lambdaQ hD bd hbd α j` (`eq:minmax`).
* `massQ_pos` — the mass **is** positive definite on `H1Q D`: if `∫_D u² = 0` with `u² ≥ 0`
  then `u =ᵐ 0`, i.e. `u ∈ nullAE D`.
* `bddBelowRatio_robinFormQ` and the two engine wrappers `lambdaQ_le_of_trial`,
  `le_lambdaQ_of_codim`, specialisations of `RobinCaps.Spectrum.minmax_le_of_trial'` and
  `RobinCaps.Spectrum.le_minmax_of_codim'` (the latter fed by
  `RobinCaps.Spectrum.bddAbove_ratio_of_bilinear` applied to
  `Q := dirichletBilinQ hD + α • bdQ bd hbd` and `B := massBilinQ D`).

The boundary form `bd` is a *parameter*: mathlib `v4.26.0` has no trace operator, and `Weak.lean`
records `TraceExists` as a target.  Once a trace `T` and a boundary measure `σ` are available,
`bd u v := ∫ (T u) (T v) dσ` is the intended instantiation and `lambdaQ` is `λ_j(D;α)`.

Everything below is proved without `sorry`, `axiom`, `admit` or `native_decide`.
-/

noncomputable section

set_option linter.unusedSectionVars false

open MeasureTheory Set Filter

namespace RobinCaps.Sobolev.Weak

variable {n : ℕ}

/-- The ambient Euclidean space `ℝⁿ`. -/
local notation "E" => EuclideanSpace ℝ (Fin n)

variable {D : Set (EuclideanSpace ℝ (Fin n))}

/-! ### The null subspace of a.e.-vanishing elements, and the quotient -/

/-- **The subspace of `H1 D` of elements whose representative vanishes a.e. on `D`.**  This is
the kernel of every form of the model: `mass`, `dirichlet` (for open `D`) and any boundary form
that is well defined on a.e.-classes.  Quotienting by it is what makes the mass positive
definite, hence what makes the min–max values `eq:minmax` meaningful. -/
def nullAE (D : Set E) : Submodule ℝ (H1 D) where
  carrier := {u : H1 D | u.toFun =ᵐ[volume.restrict D] 0}
  zero_mem' := by
    show (0 : H1 D).toFun =ᵐ[volume.restrict D] 0
    filter_upwards with x
    simp
  add_mem' := by
    intro u v hu hv
    have hu' : u.toFun =ᵐ[volume.restrict D] 0 := hu
    have hv' : v.toFun =ᵐ[volume.restrict D] 0 := hv
    show (u + v).toFun =ᵐ[volume.restrict D] 0
    filter_upwards [hu', hv'] with x hx hy
    simp only [Pi.zero_apply] at hx hy ⊢
    simp [hx, hy]
  smul_mem' := by
    intro c u hu
    have hu' : u.toFun =ᵐ[volume.restrict D] 0 := hu
    show (c • u).toFun =ᵐ[volume.restrict D] 0
    filter_upwards [hu'] with x hx
    simp only [Pi.zero_apply] at hx ⊢
    simp [hx]

theorem mem_nullAE {u : H1 D} : u ∈ nullAE D ↔ u.toFun =ᵐ[volume.restrict D] 0 := Iff.rfl

/-- **The quotient of the weak model by a.e. equality**, `H1Q D = H1 D ⧸ nullAE D`.  Two
elements of `H1 D` have the same class iff their representatives agree a.e. on `D`. -/
abbrev H1Q (D : Set E) := H1 D ⧸ nullAE D

theorem H1.neg_toFun (u : H1 D) : (-u).toFun = -u.toFun := by
  have h : -u = (-1 : ℝ) • u := (neg_one_smul ℝ u).symm
  rw [h, H1.smul_toFun]
  funext x
  simp

theorem H1.sub_toFun (u v : H1 D) : (u - v).toFun = u.toFun - v.toFun := by
  rw [sub_eq_add_neg, H1.add_toFun, H1.neg_toFun, ← sub_eq_add_neg]

/-- Two elements of `H1 D` have the same class in `H1Q D` iff their representatives agree
a.e. on `D`: the quotient really is the quotient by a.e. equality. -/
theorem H1Q_eq_iff {u v : H1 D} :
    (Submodule.Quotient.mk u : H1Q D) = Submodule.Quotient.mk v ↔
      u.toFun =ᵐ[volume.restrict D] v.toFun := by
  rw [Submodule.Quotient.eq]
  constructor
  · intro h
    have h' : (u - v).toFun =ᵐ[volume.restrict D] 0 := h
    filter_upwards [h'] with x hx
    rw [H1.sub_toFun] at hx
    simp only [Pi.sub_apply, Pi.zero_apply] at hx
    linarith
  · intro h
    show (u - v).toFun =ᵐ[volume.restrict D] 0
    filter_upwards [h] with x hx
    rw [H1.sub_toFun]
    simp [hx]

/-! ### The two pairings and their integrability -/

/-- The real inner product of `EuclideanSpace ℝ (Fin n)` is the coordinate sum. -/
theorem inner_eq_sum (a b : E) : inner ℝ a b = ∑ i, a i * b i := by
  rw [PiLp.inner_apply]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [RCLike.inner_apply]
  simp [mul_comm]

/-- The `L²(D)` pairing `∫_D u v` of two elements of `H1 D`. -/
def massPairing (u v : H1 D) : ℝ := ∫ x in D, u.toFun x * v.toFun x

/-- The Dirichlet pairing `∫_D ⟪∇u, ∇v⟫` of two elements of `H1 D`. -/
def dirichletPairing (u v : H1 D) : ℝ := ∫ x in D, inner ℝ (u.grad x) (v.grad x)

/-- `u v` is integrable on `D` for `u, v ∈ H1 D` (Hölder `L² · L² ⊆ L¹`). -/
theorem integrable_massPairing (u v : H1 D) :
    Integrable (fun x => u.toFun x * v.toFun x) (volume.restrict D) :=
  u.memL2.integrable_mul v.memL2

/-- `⟪∇u, ∇v⟫` is integrable on `D` for `u, v ∈ H1 D`: expand coordinatewise and apply
Hölder `L² · L² ⊆ L¹` to each of the `n` products. -/
theorem integrable_dirichletPairing (u v : H1 D) :
    Integrable (fun x => inner ℝ (u.grad x) (v.grad x)) (volume.restrict D) := by
  have hfun : (fun x => (inner ℝ (u.grad x) (v.grad x) : ℝ))
      = fun x => ∑ i, u.grad x i * v.grad x i := by
    funext x
    exact inner_eq_sum _ _
  rw [hfun]
  refine integrable_finset_sum _ fun i _ => ?_
  exact (memLp_two_comp u.grad_memL2 i).integrable_mul (memLp_two_comp v.grad_memL2 i)

/-! ### Bilinearity -/

theorem massPairing_add_left (u v w : H1 D) :
    massPairing (u + v) w = massPairing u w + massPairing v w := by
  unfold massPairing
  rw [← integral_add (integrable_massPairing u w) (integrable_massPairing v w)]
  refine integral_congr_ae (Eventually.of_forall fun x => ?_)
  simp only [H1.add_toFun, Pi.add_apply]
  ring

theorem massPairing_smul_left (c : ℝ) (u v : H1 D) :
    massPairing (c • u) v = c * massPairing u v := by
  unfold massPairing
  rw [← integral_const_mul]
  refine integral_congr_ae (Eventually.of_forall fun x => ?_)
  simp only [H1.smul_toFun, Pi.smul_apply, smul_eq_mul]
  ring

theorem massPairing_comm (u v : H1 D) : massPairing u v = massPairing v u := by
  unfold massPairing
  refine integral_congr_ae (Eventually.of_forall fun x => ?_)
  ring

theorem massPairing_add_right (u v w : H1 D) :
    massPairing u (v + w) = massPairing u v + massPairing u w := by
  rw [massPairing_comm, massPairing_add_left, massPairing_comm v u, massPairing_comm w u]

theorem massPairing_smul_right (c : ℝ) (u v : H1 D) :
    massPairing u (c • v) = c * massPairing u v := by
  rw [massPairing_comm, massPairing_smul_left, massPairing_comm v u]

theorem dirichletPairing_add_left (u v w : H1 D) :
    dirichletPairing (u + v) w = dirichletPairing u w + dirichletPairing v w := by
  unfold dirichletPairing
  rw [← integral_add (integrable_dirichletPairing u w) (integrable_dirichletPairing v w)]
  refine integral_congr_ae (Eventually.of_forall fun x => ?_)
  simp only [H1.add_grad, Pi.add_apply]
  rw [inner_add_left]

theorem dirichletPairing_smul_left (c : ℝ) (u v : H1 D) :
    dirichletPairing (c • u) v = c * dirichletPairing u v := by
  unfold dirichletPairing
  rw [← integral_const_mul]
  refine integral_congr_ae (Eventually.of_forall fun x => ?_)
  simp only [H1.smul_grad, Pi.smul_apply]
  rw [real_inner_smul_left]

theorem dirichletPairing_comm (u v : H1 D) : dirichletPairing u v = dirichletPairing v u := by
  unfold dirichletPairing
  refine integral_congr_ae (Eventually.of_forall fun x => ?_)
  exact real_inner_comm _ _

theorem dirichletPairing_add_right (u v w : H1 D) :
    dirichletPairing u (v + w) = dirichletPairing u v + dirichletPairing u w := by
  rw [dirichletPairing_comm, dirichletPairing_add_left, dirichletPairing_comm v u,
    dirichletPairing_comm w u]

theorem dirichletPairing_smul_right (c : ℝ) (u v : H1 D) :
    dirichletPairing u (c • v) = c * dirichletPairing u v := by
  rw [dirichletPairing_comm, dirichletPairing_smul_left, dirichletPairing_comm v u]

/-! ### The bundled bilinear forms -/

/-- **The mass bilinear form** `(u, v) ↦ ∫_D u v` on `H1 D`, bundled. -/
def massBilin (D : Set E) : H1 D →ₗ[ℝ] H1 D →ₗ[ℝ] ℝ :=
  LinearMap.mk₂ ℝ massPairing massPairing_add_left
    (fun c u v => (massPairing_smul_left c u v).trans (smul_eq_mul c _).symm)
    massPairing_add_right
    (fun c u v => (massPairing_smul_right c u v).trans (smul_eq_mul c _).symm)

@[simp] theorem massBilin_apply (u v : H1 D) :
    massBilin D u v = ∫ x in D, u.toFun x * v.toFun x := rfl

/-- **The Dirichlet bilinear form** `(u, v) ↦ ∫_D ⟪∇u, ∇v⟫` on `H1 D`, bundled. -/
def dirichletBilin (D : Set E) : H1 D →ₗ[ℝ] H1 D →ₗ[ℝ] ℝ :=
  LinearMap.mk₂ ℝ dirichletPairing dirichletPairing_add_left
    (fun c u v => (dirichletPairing_smul_left c u v).trans (smul_eq_mul c _).symm)
    dirichletPairing_add_right
    (fun c u v => (dirichletPairing_smul_right c u v).trans (smul_eq_mul c _).symm)

@[simp] theorem dirichletBilin_apply (u v : H1 D) :
    dirichletBilin D u v = ∫ x in D, inner ℝ (u.grad x) (v.grad x) := rfl

/-- The mass is the diagonal of `massBilin`. -/
theorem mass_eq_massBilin (u : H1 D) : mass u = massBilin D u u := by
  rw [massBilin_apply]
  unfold mass
  refine integral_congr_ae (Eventually.of_forall fun x => ?_)
  ring

/-- The Dirichlet energy is the diagonal of `dirichletBilin`. -/
theorem dirichlet_eq_dirichletBilin (u : H1 D) : dirichlet u = dirichletBilin D u u := by
  rw [dirichletBilin_apply]
  unfold dirichlet
  refine integral_congr_ae (Eventually.of_forall fun x => ?_)
  show ‖u.grad x‖ ^ 2 = inner ℝ (u.grad x) (u.grad x)
  rw [real_inner_self_eq_norm_sq]

/-! ### Vanishing on `nullAE D` -/

theorem massBilin_eq_zero_left {u : H1 D} (hu : u ∈ nullAE D) (v : H1 D) :
    massBilin D u v = 0 := by
  have hu' : u.toFun =ᵐ[volume.restrict D] 0 := hu
  rw [massBilin_apply]
  have h : (fun x => u.toFun x * v.toFun x) =ᵐ[volume.restrict D] fun _ => (0 : ℝ) := by
    filter_upwards [hu'] with x hx
    simp only [Pi.zero_apply] at hx
    simp [hx]
  rw [integral_congr_ae h, integral_zero]

theorem massBilin_eq_zero_right (u : H1 D) {v : H1 D} (hv : v ∈ nullAE D) :
    massBilin D u v = 0 := by
  rw [massBilin_apply, ← massPairing, massPairing_comm]
  exact massBilin_eq_zero_left hv u

/-- An element of `nullAE D` has an a.e.-vanishing weak gradient on the **open** set `D`: this
is the a.e. uniqueness of the weak gradient (`H1.grad_ae_eq`) applied to `u` and `0`. -/
theorem grad_ae_zero_of_mem_nullAE (hD : IsOpen D) {u : H1 D} (hu : u ∈ nullAE D) :
    u.grad =ᵐ[volume.restrict D] fun _ => (0 : E) := by
  have hu' : u.toFun =ᵐ[volume.restrict D] 0 := hu
  have h0 : u.toFun =ᵐ[volume.restrict D] (0 : H1 D).toFun := by
    filter_upwards [hu'] with x hx
    simpa using hx
  have hg := H1.grad_ae_eq hD h0
  filter_upwards [hg] with x hx
  simpa using hx

theorem dirichletBilin_eq_zero_left (hD : IsOpen D) {u : H1 D} (hu : u ∈ nullAE D) (v : H1 D) :
    dirichletBilin D u v = 0 := by
  have hg := grad_ae_zero_of_mem_nullAE hD hu
  rw [dirichletBilin_apply]
  have h : (fun x => (inner ℝ (u.grad x) (v.grad x) : ℝ))
      =ᵐ[volume.restrict D] fun _ => (0 : ℝ) := by
    filter_upwards [hg] with x hx
    rw [hx, inner_zero_left]
  rw [integral_congr_ae h, integral_zero]

theorem dirichletBilin_eq_zero_right (hD : IsOpen D) (u : H1 D) {v : H1 D}
    (hv : v ∈ nullAE D) : dirichletBilin D u v = 0 := by
  rw [dirichletBilin_apply, ← dirichletPairing, dirichletPairing_comm]
  exact dirichletBilin_eq_zero_left hD hv u

/-- **A boundary form vanishing on `nullAE D`.**  This is the hypothesis under which an abstract
boundary pairing (intended: `bd u v = ∫_{∂D} (T u) (T v) dσ` for a trace `T`, which mathlib
`v4.26.0` does not provide) descends to the quotient. -/
def VanishesOnNullAE (D : Set E) (bd : H1 D →ₗ[ℝ] H1 D →ₗ[ℝ] ℝ) : Prop :=
  (∀ u ∈ nullAE D, ∀ v, bd u v = 0) ∧ (∀ u, ∀ v ∈ nullAE D, bd u v = 0)

/-! ### The descended forms -/

/-- **The mass bilinear form on the quotient `H1Q D`.** -/
def massBilinQ (D : Set E) : H1Q D →ₗ[ℝ] H1Q D →ₗ[ℝ] ℝ :=
  descendBilin (nullAE D) (massBilin D) (fun _ hu v => massBilin_eq_zero_left hu v)
    (fun u _ hv => massBilin_eq_zero_right u hv)

@[simp] theorem massBilinQ_mk (u v : H1 D) :
    massBilinQ D (Submodule.Quotient.mk u) (Submodule.Quotient.mk v) = massBilin D u v := rfl

/-- **The Dirichlet bilinear form on the quotient `H1Q D`** (for open `D`). -/
def dirichletBilinQ (hD : IsOpen D) : H1Q D →ₗ[ℝ] H1Q D →ₗ[ℝ] ℝ :=
  descendBilin (nullAE D) (dirichletBilin D)
    (fun _ hu v => dirichletBilin_eq_zero_left hD hu v)
    (fun u _ hv => dirichletBilin_eq_zero_right hD u hv)

@[simp] theorem dirichletBilinQ_mk (hD : IsOpen D) (u v : H1 D) :
    dirichletBilinQ hD (Submodule.Quotient.mk u) (Submodule.Quotient.mk v)
      = dirichletBilin D u v := rfl

/-- **A boundary form on the quotient `H1Q D`.** -/
def bdQ (bd : H1 D →ₗ[ℝ] H1 D →ₗ[ℝ] ℝ) (hbd : VanishesOnNullAE D bd) :
    H1Q D →ₗ[ℝ] H1Q D →ₗ[ℝ] ℝ :=
  descendBilin (nullAE D) bd hbd.1 hbd.2

@[simp] theorem bdQ_mk (bd : H1 D →ₗ[ℝ] H1 D →ₗ[ℝ] ℝ) (hbd : VanishesOnNullAE D bd)
    (u v : H1 D) :
    bdQ bd hbd (Submodule.Quotient.mk u) (Submodule.Quotient.mk v) = bd u v := rfl

/-- **The mass on the quotient**, `N_D` of `eq:robin-form`. -/
def massQ (D : Set E) (w : H1Q D) : ℝ := massBilinQ D w w

/-- **The Dirichlet energy on the quotient**, `∫_D |∇u|²` of `eq:robin-form`. -/
def dirichletQ (hD : IsOpen D) (w : H1Q D) : ℝ := dirichletBilinQ hD w w

@[simp] theorem massQ_mk (u : H1 D) : massQ D (Submodule.Quotient.mk u) = mass u := by
  rw [massQ, massBilinQ_mk, ← mass_eq_massBilin]

@[simp] theorem dirichletQ_mk (hD : IsOpen D) (u : H1 D) :
    dirichletQ hD (Submodule.Quotient.mk u) = dirichlet u := by
  rw [dirichletQ, dirichletBilinQ_mk, ← dirichlet_eq_dirichletBilin]

/-- **The Robin form on the quotient** `q_D[u] = ∫_D |∇u|² + α · bd[u]` (`eq:robin-form`),
with the boundary pairing `bd` as a parameter. -/
def robinFormQ (hD : IsOpen D) (bd : H1 D →ₗ[ℝ] H1 D →ₗ[ℝ] ℝ) (hbd : VanishesOnNullAE D bd)
    (α : ℝ) (w : H1Q D) : ℝ :=
  dirichletQ hD w + α * bdQ bd hbd w w

@[simp] theorem robinFormQ_mk (hD : IsOpen D) (bd : H1 D →ₗ[ℝ] H1 D →ₗ[ℝ] ℝ)
    (hbd : VanishesOnNullAE D bd) (α : ℝ) (u : H1 D) :
    robinFormQ hD bd hbd α (Submodule.Quotient.mk u) = dirichlet u + α * bd u u := by
  rw [robinFormQ, dirichletQ_mk, bdQ_mk]

/-- The Robin form on the quotient is the diagonal of the bilinear form
`dirichletBilinQ hD + α • bdQ bd hbd`.  This is the shape required by
`RobinCaps.Spectrum.bddAbove_ratio_of_bilinear`. -/
theorem robinFormQ_eq_bilin (hD : IsOpen D) (bd : H1 D →ₗ[ℝ] H1 D →ₗ[ℝ] ℝ)
    (hbd : VanishesOnNullAE D bd) (α : ℝ) (w : H1Q D) :
    robinFormQ hD bd hbd α w = (dirichletBilinQ hD + α • bdQ bd hbd) w w := by
  simp only [LinearMap.add_apply, LinearMap.smul_apply, smul_eq_mul, robinFormQ, dirichletQ]

/-! ### Positive definiteness of the mass on the quotient -/

/-- **An element of zero mass is a.e. zero**, i.e. lies in `nullAE D`.  The integrand `u²` is
nonnegative and integrable (`MemLp` with exponent `2`), so a vanishing integral forces `u² = 0`
a.e. -/
theorem mem_nullAE_of_mass_eq_zero {u : H1 D} (hm : mass u = 0) : u ∈ nullAE D := by
  have hint : Integrable (fun x => u.toFun x ^ 2) (volume.restrict D) := by
    have h : Integrable (fun x => u.toFun x * u.toFun x) (volume.restrict D) :=
      integrable_massPairing u u
    simpa [pow_two] using h
  have hnn : 0 ≤ᵐ[volume.restrict D] fun x => u.toFun x ^ 2 :=
    Eventually.of_forall fun x => sq_nonneg _
  have hm' : (∫ x in D, u.toFun x ^ 2) = 0 := hm
  have hz := (integral_eq_zero_iff_of_nonneg_ae hnn hint).mp hm'
  show u.toFun =ᵐ[volume.restrict D] 0
  filter_upwards [hz] with x hx
  simp only [Pi.zero_apply] at hx ⊢
  exact (pow_eq_zero_iff two_ne_zero).mp hx

theorem massQ_nonneg (w : H1Q D) : 0 ≤ massQ D w := by
  obtain ⟨u, rfl⟩ := Submodule.Quotient.mk_surjective (nullAE D) w
  rw [massQ_mk]
  exact mass_nonneg u

set_option linter.unusedVariables false in
/-- **The mass is positive definite on the quotient `H1Q D`.**  This is the property that fails
on `H1 D` itself and that the quotient is built for; it is the hypothesis `b u > 0` of the
abstract form engine, hence what makes `lambdaQ` (`eq:minmax`) meaningful.

(The openness hypothesis `hD` is kept for uniformity with the other statements of this file —
positivity of the mass itself only uses the underlying function, not the weak gradient.) -/
theorem massQ_pos (hD : IsOpen D) (w : H1Q D) (hw : w ≠ 0) : 0 < massQ D w := by
  obtain ⟨u, rfl⟩ := Submodule.Quotient.mk_surjective (nullAE D) w
  rw [massQ_mk]
  rcases (mass_nonneg u).lt_or_eq with h | h
  · exact h
  · exact absurd ((Submodule.Quotient.mk_eq_zero (nullAE D)).mpr
      (mem_nullAE_of_mass_eq_zero h.symm)) hw

/-! ### The variational eigenvalues `λ_j(D;α)` -/

/-- **The variational eigenvalues of the manuscript** (`eq:minmax`):
`λ_j(D;α) = min_{V, dim V = j} max_{0 ≠ u ∈ V} q_D[u] / N_D[u]`, computed on the quotient
`H1Q D`, where the mass is positive definite.  With `bd` the boundary trace pairing this is
`λ_j(D;α)`. -/
def lambdaQ (hD : IsOpen D) (bd : H1 D →ₗ[ℝ] H1 D →ₗ[ℝ] ℝ) (hbd : VanishesOnNullAE D bd)
    (α : ℝ) (j : ℕ) : ℝ :=
  Spectrum.minmax (robinFormQ hD bd hbd α) (massQ D) j

theorem dirichletQ_nonneg (hD : IsOpen D) (w : H1Q D) : 0 ≤ dirichletQ hD w := by
  obtain ⟨u, rfl⟩ := Submodule.Quotient.mk_surjective (nullAE D) w
  rw [dirichletQ_mk]
  exact dirichlet_nonneg u

theorem robinFormQ_nonneg (hD : IsOpen D) (bd : H1 D →ₗ[ℝ] H1 D →ₗ[ℝ] ℝ)
    (hbd : VanishesOnNullAE D bd) {α : ℝ} (hα : 0 ≤ α) (hbd0 : ∀ v : H1 D, 0 ≤ bd v v)
    (w : H1Q D) : 0 ≤ robinFormQ hD bd hbd α w := by
  obtain ⟨u, rfl⟩ := Submodule.Quotient.mk_surjective (nullAE D) w
  rw [robinFormQ_mk]
  exact add_nonneg (dirichlet_nonneg u) (mul_nonneg hα (hbd0 u))

/-- The lower ratio bound of the abstract engine, with constant `0`: for `α ≥ 0` and a
nonnegative boundary form the Robin quotient is nonnegative. -/
theorem bddBelowRatio_robinFormQ (hD : IsOpen D) (bd : H1 D →ₗ[ℝ] H1 D →ₗ[ℝ] ℝ)
    (hbd : VanishesOnNullAE D bd) {α : ℝ} (hα : 0 ≤ α) (hbd0 : ∀ v : H1 D, 0 ≤ bd v v) :
    Spectrum.BddBelowRatio (robinFormQ hD bd hbd α) (massQ D) :=
  ⟨0, le_rfl, fun w _ =>
    div_nonneg (robinFormQ_nonneg hD bd hbd hα hbd0 w) (massQ_nonneg w)⟩

/-- **Trial-space upper bound for `λ_j(D;α)`** (`RobinCaps.Spectrum.minmax_le_of_trial'`):
a `j`-dimensional subspace of `H1Q D` on which `q_D ≤ t · N_D` bounds `λ_j` by `t`. -/
theorem lambdaQ_le_of_trial (hD : IsOpen D) (bd : H1 D →ₗ[ℝ] H1 D →ₗ[ℝ] ℝ)
    (hbd : VanishesOnNullAE D bd) {α : ℝ} (hα : 0 ≤ α) (hbd0 : ∀ v : H1 D, 0 ≤ bd v v)
    (j : ℕ) (hj : 0 < j) (W : Submodule ℝ (H1Q D)) (hW : Module.finrank ℝ W = j) (t : ℝ)
    (h : ∀ w ∈ W, w ≠ 0 → robinFormQ hD bd hbd α w ≤ t * massQ D w) :
    lambdaQ hD bd hbd α j ≤ t :=
  Spectrum.minmax_le_of_trial' (robinFormQ hD bd hbd α) (massQ D) j hj (massQ_pos hD)
    (bddBelowRatio_robinFormQ hD bd hbd hα hbd0) W hW t h

/-- **Finite-codimension lower bound for `λ_j(D;α)`** (`RobinCaps.Spectrum.le_minmax_of_codim'`):
if `t · N_D ≤ q_D` on the kernel of a `(j-1)`-dimensional constraint `φ`, then `t ≤ λ_j`.  The
per-subspace boundedness of the Rayleigh quotient required by the engine is supplied by
`RobinCaps.Spectrum.bddAbove_ratio_of_bilinear` with
`Q = dirichletBilinQ hD + α • bdQ bd hbd` and `B = massBilinQ D`. -/
theorem le_lambdaQ_of_codim (hD : IsOpen D) (bd : H1 D →ₗ[ℝ] H1 D →ₗ[ℝ] ℝ)
    (hbd : VanishesOnNullAE D bd) (α : ℝ) (j : ℕ) (hj : 1 ≤ j)
    (φ : H1Q D →ₗ[ℝ] (Fin (j - 1) → ℝ))
    (hφ : Module.finrank ℝ (LinearMap.range φ) = j - 1) (t : ℝ)
    (h : ∀ w : H1Q D, w ≠ 0 → φ w = 0 → t * massQ D w ≤ robinFormQ hD bd hbd α w)
    (hex : ∃ V : Submodule ℝ (H1Q D), Module.finrank ℝ V = j) :
    t ≤ lambdaQ hD bd hbd α j := by
  refine Spectrum.le_minmax_of_codim' (robinFormQ hD bd hbd α) (massQ D) j hj (massQ_pos hD)
    ?_ φ hφ t h hex
  intro V hV
  haveI : FiniteDimensional ℝ V := FiniteDimensional.of_finrank_pos (by omega)
  have hfun : (fun u : {u : V // u ≠ 0} =>
        robinFormQ hD bd hbd α ((u : V) : H1Q D) / massQ D ((u : V) : H1Q D))
      = fun u : {u : V // u ≠ 0} =>
        (dirichletBilinQ hD + α • bdQ bd hbd) ((u : V) : H1Q D) ((u : V) : H1Q D)
          / massBilinQ D ((u : V) : H1Q D) ((u : V) : H1Q D) := by
    funext u
    rw [robinFormQ_eq_bilin]
    rfl
  rw [hfun]
  exact Spectrum.bddAbove_ratio_of_bilinear (dirichletBilinQ hD + α • bdQ bd hbd)
    (massBilinQ D) (massQ_pos hD) V

end RobinCaps.Sobolev.Weak

end
