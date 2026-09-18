import RobinCaps.ThinDomain.H1P
import RobinCaps.Sobolev.Quotient

set_option linter.style.longLine false

/-!
# U-SOB-P-Q: the product weak space `H1P Ω` modulo a.e. equality, and `λ_j(Ω;α)`

`RobinCaps/ThinDomain/H1P.lean` builds the weak-`H¹` layer `H1P Ω` on the product ambient
space `CapSpace m = ℝ × EuclideanSpace ℝ (Fin m)` out of **pointwise representatives**: an
element is a triple `(u, ∂ₓu, ∇_z u)` of honest functions, and equality in `H1P Ω` is equality
of the triple.  Consequently the mass `N_Ω[u] = ∫_Ω u²` is *not* positive definite on `H1P Ω`
— every function vanishing a.e. on `Ω` (for instance any nonzero function supported off `Ω`)
is a nonzero element of zero mass.  The variational values `λ_j(Ω;α)` of the manuscript
(`eq:minmax`, lines 118–140) are therefore not defined on `H1P Ω` itself: the abstract form
engine `RobinCaps.Spectrum.minmax` needs `b u > 0` for `u ≠ 0`.

This file removes the obstruction for the *product* model exactly as
`RobinCaps/Sobolev/WeakQuotient.lean` does for `EuclideanSpace ℝ (Fin n)`.

## Contents

* `nullAEP Ω` — the subspace `{u | u.toFun =ᵐ[volume.restrict Ω] 0}` of `H1P Ω`, and the
  quotient `H1PQ Ω := H1P Ω ⧸ nullAEP Ω`; `H1PQ_eq_iff` says that the quotient really is the
  quotient by a.e. equality.
* Both bundled forms `massBilinPₗ`, `dirichletBilinPₗ` of `H1P.lean` vanish as soon as one
  argument lies in `nullAEP Ω`.  For the mass this is immediate; for the Dirichlet form it uses
  the a.e. uniqueness of the weak gradient on an **open** `Ω`, i.e. `H1P.gx_ae_eq` and
  `H1P.gz_ae_eq`.  Hence they descend through `RobinCaps.Sobolev.descendBilin` to
  `massBilinPQ`, `dirichletBilinPQ hΩ`, and so do the quadratic forms `massPQ`, `dirichletPQ`.
* An abstract boundary form `bd : H1P Ω →ₗ[ℝ] H1P Ω →ₗ[ℝ] ℝ` which vanishes on `nullAEP Ω`
  (`VanishesOnNullAEP`) descends likewise (`bdQ`), giving the **Robin form on the quotient**
  `robinFormPQ hΩ bd hbd α = dirichletPQ + α · bdQ` (`eq:robin-form`) and the manuscript's
  variational eigenvalues `lambdaPQ hΩ bd hbd α j` (`eq:minmax`).
* `massPQ_pos` — the mass **is** positive definite on `H1PQ Ω`: if `∫_Ω u² = 0` with `u² ≥ 0`
  and `u² ` integrable (`MemLp _ 2`), then `u =ᵐ 0`, i.e. `u ∈ nullAEP Ω`.
* `bddBelowRatio_robinFormPQ` and the two engine wrappers `lambdaPQ_le_of_trial`,
  `le_lambdaPQ_of_codim`, specialisations of `RobinCaps.Spectrum.minmax_le_of_trial'` and
  `RobinCaps.Spectrum.le_minmax_of_codim'` (the latter fed by
  `RobinCaps.Spectrum.bddAbove_ratio_of_bilinear` applied to
  `Q := dirichletBilinPQ hΩ + α • bdQ bd hbd` and `B := massBilinPQ`).
* `RobinCaps.Spectrum.minmax_mono'` — a variant of `RobinCaps.Spectrum.minmax_mono` in which
  the **global** upper ratio bound `BddAboveRatio q₂ b` (which is false for Robin forms: the
  Robin spectrum is unbounded above) is replaced by boundedness of the ratio on each
  `j`-dimensional subspace, exactly as in `RobinCaps.Spectrum.le_minmax_of_codim'`.  This is
  what makes the monotonicity statements `lambdaPQ_mono_bd` (monotonicity in the boundary form)
  and `lambdaPQ_mono_alpha` (monotonicity in the Robin parameter `α`) unconditional for
  `j ≥ 1`.

The boundary form `bd` is a *parameter*: mathlib `v4.26.0` has no trace operator on the product
space.  Once a trace `T` and a boundary measure `σ` are available, `bd u v := ∫ (T u) (T v) dσ`
is the intended instantiation and `lambdaPQ` is the manuscript's `λ_j(Ω;α)`.

Everything below is proved without `sorry`, `axiom`, `admit` or `native_decide`.
-/

noncomputable section

set_option linter.unusedSectionVars false

open MeasureTheory Set Filter

/-! ## Part A: a monotonicity lemma for the abstract min–max engine -/

namespace RobinCaps.Spectrum

variable {H : Type*} [AddCommGroup H] [Module ℝ H]

/-- **Monotonicity of the min–max values in the form, with per-subspace ratio bounds.**

`RobinCaps.Spectrum.minmax_mono` asks for the *global* bound `BddAboveRatio q₂ b`, which fails
for Robin forms (their spectrum is unbounded above).  As in
`RobinCaps.Spectrum.le_minmax_of_codim'`, it is enough that the ratio `q₂ / b` be bounded above
on every `j`-dimensional subspace — a condition supplied for quadratic forms coming from
bilinear maps by `RobinCaps.Spectrum.bddAbove_ratio_of_bilinear`.  Only the lower bound
`BddBelowRatio q₁ b` for the smaller form is needed on the other side. -/
theorem minmax_mono' {q₁ q₂ b : H → ℝ} (h : ∀ u, q₁ u ≤ q₂ u)
    (hb : ∀ u, u ≠ 0 → 0 < b u) (hB : BddBelowRatio q₁ b) (j : ℕ)
    (hA : ∀ V : Submodule ℝ H, Module.finrank ℝ V = j →
      BddAbove (Set.range fun u : {u : V // u ≠ 0} => q₂ ((u : V) : H) / b ((u : V) : H))) :
    minmax q₁ b j ≤ minmax q₂ b j := by
  unfold minmax
  refine ciInf_mono (bddBelow_range_minmaxFamily' q₁ b hB j) ?_
  intro V
  refine ciSup_mono (hA V.1 V.2) ?_
  intro u
  exact div_le_div_of_nonneg_right (h _)
    (le_of_lt (hb _ (fun hh => u.2 (Subtype.ext hh))))

end RobinCaps.Spectrum

/-! ## Part B: the quotient of the product weak space -/

namespace RobinCaps.ThinDomain

variable {m : ℕ} {Ω : Set (CapSpace m)}

/-! ### The null subspace of a.e.-vanishing elements, and the quotient -/

/-- **The subspace of `H1P Ω` of elements whose representative vanishes a.e. on `Ω`.**  This is
the kernel of every form of the model: `massP`, `dirichletP` (for open `Ω`) and any boundary
form that is well defined on a.e.-classes.  Quotienting by it is what makes the mass positive
definite, hence what makes the min–max values `eq:minmax` meaningful. -/
def nullAEP (Ω : Set (CapSpace m)) : Submodule ℝ (H1P Ω) where
  carrier := {u : H1P Ω | u.toFun =ᵐ[volume.restrict Ω] 0}
  zero_mem' := by
    show (0 : H1P Ω).toFun =ᵐ[volume.restrict Ω] 0
    filter_upwards with p
    simp
  add_mem' := by
    intro u v hu hv
    have hu' : u.toFun =ᵐ[volume.restrict Ω] 0 := hu
    have hv' : v.toFun =ᵐ[volume.restrict Ω] 0 := hv
    show (u + v).toFun =ᵐ[volume.restrict Ω] 0
    filter_upwards [hu', hv'] with p hp hq
    simp only [Pi.zero_apply] at hp hq ⊢
    simp [hp, hq]
  smul_mem' := by
    intro c u hu
    have hu' : u.toFun =ᵐ[volume.restrict Ω] 0 := hu
    show (c • u).toFun =ᵐ[volume.restrict Ω] 0
    filter_upwards [hu'] with p hp
    simp only [Pi.zero_apply] at hp ⊢
    simp [hp]

theorem mem_nullAEP {u : H1P Ω} : u ∈ nullAEP Ω ↔ u.toFun =ᵐ[volume.restrict Ω] 0 := Iff.rfl

/-- **The quotient of the product weak model by a.e. equality**, `H1PQ Ω = H1P Ω ⧸ nullAEP Ω`. -/
abbrev H1PQ (Ω : Set (CapSpace m)) := H1P Ω ⧸ nullAEP Ω

theorem H1P.neg_toFun (u : H1P Ω) : (-u).toFun = -u.toFun := by
  have h : -u = (-1 : ℝ) • u := (neg_one_smul ℝ u).symm
  rw [h, H1P.smul_toFun]
  funext p
  simp

theorem H1P.sub_toFun (u v : H1P Ω) : (u - v).toFun = u.toFun - v.toFun := by
  rw [sub_eq_add_neg, H1P.add_toFun, H1P.neg_toFun, ← sub_eq_add_neg]

/-- Two elements of `H1P Ω` have the same class in `H1PQ Ω` iff their representatives agree
a.e. on `Ω`: the quotient really is the quotient by a.e. equality. -/
theorem H1PQ_eq_iff {u v : H1P Ω} :
    (Submodule.Quotient.mk u : H1PQ Ω) = Submodule.Quotient.mk v ↔
      u.toFun =ᵐ[volume.restrict Ω] v.toFun := by
  rw [Submodule.Quotient.eq]
  constructor
  · intro h
    have h' : (u - v).toFun =ᵐ[volume.restrict Ω] 0 := h
    filter_upwards [h'] with p hp
    rw [H1P.sub_toFun] at hp
    simp only [Pi.sub_apply, Pi.zero_apply] at hp
    linarith
  · intro h
    show (u - v).toFun =ᵐ[volume.restrict Ω] 0
    filter_upwards [h] with p hp
    rw [H1P.sub_toFun]
    simp [hp]

/-! ### Vanishing of the two forms on `nullAEP Ω` -/

theorem massBilinP_eq_zero_left {u : H1P Ω} (hu : u ∈ nullAEP Ω) (v : H1P Ω) :
    massBilinP u v = 0 := by
  have hu' : u.toFun =ᵐ[volume.restrict Ω] 0 := hu
  unfold massBilinP
  have h : (fun p => u.toFun p * v.toFun p) =ᵐ[volume.restrict Ω] fun _ => (0 : ℝ) := by
    filter_upwards [hu'] with p hp
    simp only [Pi.zero_apply] at hp
    simp [hp]
  rw [integral_congr_ae h, integral_zero]

theorem massBilinP_eq_zero_right (u : H1P Ω) {v : H1P Ω} (hv : v ∈ nullAEP Ω) :
    massBilinP u v = 0 := by
  rw [massBilinP_comm]
  exact massBilinP_eq_zero_left hv u

/-- An element of `nullAEP Ω` has an a.e.-vanishing axial weak derivative on the **open** set
`Ω`: this is a.e. uniqueness of the weak gradient (`H1P.gx_ae_eq`) applied to `u` and `0`. -/
theorem gx_ae_zero_of_mem_nullAEP (hΩ : IsOpen Ω) {u : H1P Ω} (hu : u ∈ nullAEP Ω) :
    u.gx =ᵐ[volume.restrict Ω] fun _ => (0 : ℝ) := by
  have hu' : u.toFun =ᵐ[volume.restrict Ω] 0 := hu
  have h0 : u.toFun =ᵐ[volume.restrict Ω] (0 : H1P Ω).toFun := by
    filter_upwards [hu'] with p hp
    simpa using hp
  have hg := H1P.gx_ae_eq hΩ h0
  filter_upwards [hg] with p hp
  simpa using hp

/-- The transverse counterpart of `gx_ae_zero_of_mem_nullAEP`, from `H1P.gz_ae_eq`. -/
theorem gz_ae_zero_of_mem_nullAEP (hΩ : IsOpen Ω) {u : H1P Ω} (hu : u ∈ nullAEP Ω) :
    u.gz =ᵐ[volume.restrict Ω] fun _ => (0 : EuclideanSpace ℝ (Fin m)) := by
  have hu' : u.toFun =ᵐ[volume.restrict Ω] 0 := hu
  have h0 : u.toFun =ᵐ[volume.restrict Ω] (0 : H1P Ω).toFun := by
    filter_upwards [hu'] with p hp
    simpa using hp
  have hg := H1P.gz_ae_eq hΩ h0
  filter_upwards [hg] with p hp
  simpa using hp

theorem dirichletBilinP_eq_zero_left (hΩ : IsOpen Ω) {u : H1P Ω} (hu : u ∈ nullAEP Ω)
    (v : H1P Ω) : dirichletBilinP u v = 0 := by
  have hx := gx_ae_zero_of_mem_nullAEP hΩ hu
  have hz := gz_ae_zero_of_mem_nullAEP hΩ hu
  unfold dirichletBilinP
  have h : (fun p => u.gx p * v.gx p + ∑ i, u.gz p i * v.gz p i)
      =ᵐ[volume.restrict Ω] fun _ => (0 : ℝ) := by
    filter_upwards [hx, hz] with p hpx hpz
    simp [hpx, hpz]
  rw [integral_congr_ae h, integral_zero]

theorem dirichletBilinP_eq_zero_right (hΩ : IsOpen Ω) (u : H1P Ω) {v : H1P Ω}
    (hv : v ∈ nullAEP Ω) : dirichletBilinP u v = 0 := by
  rw [dirichletBilinP_comm]
  exact dirichletBilinP_eq_zero_left hΩ hv u

/-- **A boundary form vanishing on `nullAEP Ω`.**  This is the hypothesis under which an
abstract boundary pairing (intended: `bd u v = ∫_{∂Ω} (T u) (T v) dσ` for a trace `T`, which
mathlib `v4.26.0` does not provide) descends to the quotient. -/
def VanishesOnNullAEP (Ω : Set (CapSpace m)) (bd : H1P Ω →ₗ[ℝ] H1P Ω →ₗ[ℝ] ℝ) : Prop :=
  (∀ u ∈ nullAEP Ω, ∀ v, bd u v = 0) ∧ (∀ u, ∀ v ∈ nullAEP Ω, bd u v = 0)

/-! ### The descended forms -/

/-- **The mass bilinear form on the quotient `H1PQ Ω`.** -/
def massBilinPQ : H1PQ Ω →ₗ[ℝ] H1PQ Ω →ₗ[ℝ] ℝ :=
  RobinCaps.Sobolev.descendBilin (nullAEP Ω) massBilinPₗ
    (fun _ hu v => massBilinP_eq_zero_left hu v)
    (fun u _ hv => massBilinP_eq_zero_right u hv)

@[simp] theorem massBilinPQ_mk (u v : H1P Ω) :
    massBilinPQ (Submodule.Quotient.mk u) (Submodule.Quotient.mk v) = massBilinP u v := rfl

/-- **The Dirichlet bilinear form on the quotient `H1PQ Ω`** (for open `Ω`). -/
def dirichletBilinPQ (hΩ : IsOpen Ω) : H1PQ Ω →ₗ[ℝ] H1PQ Ω →ₗ[ℝ] ℝ :=
  RobinCaps.Sobolev.descendBilin (nullAEP Ω) dirichletBilinPₗ
    (fun _ hu v => dirichletBilinP_eq_zero_left hΩ hu v)
    (fun u _ hv => dirichletBilinP_eq_zero_right hΩ u hv)

@[simp] theorem dirichletBilinPQ_mk (hΩ : IsOpen Ω) (u v : H1P Ω) :
    dirichletBilinPQ hΩ (Submodule.Quotient.mk u) (Submodule.Quotient.mk v)
      = dirichletBilinP u v := rfl

/-- **A boundary form on the quotient `H1PQ Ω`.** -/
def bdQ (bd : H1P Ω →ₗ[ℝ] H1P Ω →ₗ[ℝ] ℝ) (hbd : VanishesOnNullAEP Ω bd) :
    H1PQ Ω →ₗ[ℝ] H1PQ Ω →ₗ[ℝ] ℝ :=
  RobinCaps.Sobolev.descendBilin (nullAEP Ω) bd hbd.1 hbd.2

@[simp] theorem bdQ_mk (bd : H1P Ω →ₗ[ℝ] H1P Ω →ₗ[ℝ] ℝ) (hbd : VanishesOnNullAEP Ω bd)
    (u v : H1P Ω) :
    bdQ bd hbd (Submodule.Quotient.mk u) (Submodule.Quotient.mk v) = bd u v := rfl

/-- **The mass on the quotient**, `N_Ω` of `eq:robin-form`. -/
def massPQ (w : H1PQ Ω) : ℝ := massBilinPQ w w

/-- **The Dirichlet energy on the quotient**, `∫_Ω ((∂ₓu)² + ‖∇_z u‖²)` of `eq:robin-form`. -/
def dirichletPQ (hΩ : IsOpen Ω) (w : H1PQ Ω) : ℝ := dirichletBilinPQ hΩ w w

@[simp] theorem massPQ_mk (u : H1P Ω) : massPQ (Submodule.Quotient.mk u) = massP u := by
  rw [massPQ, massBilinPQ_mk, massBilinP_self]

@[simp] theorem dirichletPQ_mk (hΩ : IsOpen Ω) (u : H1P Ω) :
    dirichletPQ hΩ (Submodule.Quotient.mk u) = dirichletP u := by
  rw [dirichletPQ, dirichletBilinPQ_mk, dirichletBilinP_self]

/-- **The Robin form on the quotient** `q_Ω[u] = ∫_Ω ((∂ₓu)² + ‖∇_z u‖²) + α · bd[u]`
(`eq:robin-form`), with the boundary pairing `bd` as a parameter. -/
def robinFormPQ (hΩ : IsOpen Ω) (bd : H1P Ω →ₗ[ℝ] H1P Ω →ₗ[ℝ] ℝ)
    (hbd : VanishesOnNullAEP Ω bd) (α : ℝ) (w : H1PQ Ω) : ℝ :=
  dirichletPQ hΩ w + α * bdQ bd hbd w w

@[simp] theorem robinFormPQ_mk (hΩ : IsOpen Ω) (bd : H1P Ω →ₗ[ℝ] H1P Ω →ₗ[ℝ] ℝ)
    (hbd : VanishesOnNullAEP Ω bd) (α : ℝ) (u : H1P Ω) :
    robinFormPQ hΩ bd hbd α (Submodule.Quotient.mk u) = dirichletP u + α * bd u u := by
  rw [robinFormPQ, dirichletPQ_mk, bdQ_mk]

/-- The Robin form on the quotient is the diagonal of the bilinear form
`dirichletBilinPQ hΩ + α • bdQ bd hbd`.  This is the shape required by
`RobinCaps.Spectrum.bddAbove_ratio_of_bilinear`. -/
theorem robinFormPQ_eq_bilin (hΩ : IsOpen Ω) (bd : H1P Ω →ₗ[ℝ] H1P Ω →ₗ[ℝ] ℝ)
    (hbd : VanishesOnNullAEP Ω bd) (α : ℝ) (w : H1PQ Ω) :
    robinFormPQ hΩ bd hbd α w = (dirichletBilinPQ hΩ + α • bdQ bd hbd) w w := by
  simp only [LinearMap.add_apply, LinearMap.smul_apply, smul_eq_mul, robinFormPQ, dirichletPQ]

/-! ### Positive definiteness of the mass on the quotient -/

/-- **An element of zero mass is a.e. zero**, i.e. lies in `nullAEP Ω`.  The integrand `u²` is
nonnegative and integrable (`MemLp` with exponent `2`), so a vanishing integral forces `u² = 0`
a.e. -/
theorem mem_nullAEP_of_massP_eq_zero {u : H1P Ω} (hm : massP u = 0) : u ∈ nullAEP Ω := by
  have hint : Integrable (fun p => u.toFun p ^ 2) (volume.restrict Ω) := u.memL2.integrable_sq
  have hnn : 0 ≤ᵐ[volume.restrict Ω] fun p => u.toFun p ^ 2 :=
    Eventually.of_forall fun _ => sq_nonneg _
  have hm' : (∫ p in Ω, u.toFun p ^ 2) = 0 := hm
  have hz := (integral_eq_zero_iff_of_nonneg_ae hnn hint).mp hm'
  show u.toFun =ᵐ[volume.restrict Ω] 0
  filter_upwards [hz] with p hp
  simp only [Pi.zero_apply] at hp ⊢
  exact (pow_eq_zero_iff two_ne_zero).mp hp

theorem massPQ_nonneg (w : H1PQ Ω) : 0 ≤ massPQ w := by
  obtain ⟨u, rfl⟩ := Submodule.Quotient.mk_surjective (nullAEP Ω) w
  rw [massPQ_mk]
  exact massP_nonneg u

/-- **The mass is positive definite on the quotient `H1PQ Ω`.**  This is the property that fails
on `H1P Ω` itself and that the quotient is built for; it is the hypothesis `b u > 0` of the
abstract form engine, hence what makes `lambdaPQ` (`eq:minmax`) meaningful. -/
theorem massPQ_pos (w : H1PQ Ω) (hw : w ≠ 0) : 0 < massPQ w := by
  obtain ⟨u, rfl⟩ := Submodule.Quotient.mk_surjective (nullAEP Ω) w
  rw [massPQ_mk]
  rcases (massP_nonneg u).lt_or_eq with h | h
  · exact h
  · exact absurd ((Submodule.Quotient.mk_eq_zero (nullAEP Ω)).mpr
      (mem_nullAEP_of_massP_eq_zero h.symm)) hw

/-! ### Nonnegativity and the lower ratio bound -/

theorem dirichletPQ_nonneg (hΩ : IsOpen Ω) (w : H1PQ Ω) : 0 ≤ dirichletPQ hΩ w := by
  obtain ⟨u, rfl⟩ := Submodule.Quotient.mk_surjective (nullAEP Ω) w
  rw [dirichletPQ_mk]
  exact dirichletP_nonneg u

theorem robinFormPQ_nonneg (hΩ : IsOpen Ω) (bd : H1P Ω →ₗ[ℝ] H1P Ω →ₗ[ℝ] ℝ)
    (hbd : VanishesOnNullAEP Ω bd) {α : ℝ} (hα : 0 ≤ α) (hbd0 : ∀ v : H1P Ω, 0 ≤ bd v v)
    (w : H1PQ Ω) : 0 ≤ robinFormPQ hΩ bd hbd α w := by
  obtain ⟨u, rfl⟩ := Submodule.Quotient.mk_surjective (nullAEP Ω) w
  rw [robinFormPQ_mk]
  exact add_nonneg (dirichletP_nonneg u) (mul_nonneg hα (hbd0 u))

/-- The lower ratio bound of the abstract engine, with constant `0`: for `α ≥ 0` and a
nonnegative boundary form the Robin quotient is nonnegative. -/
theorem bddBelowRatio_robinFormPQ (hΩ : IsOpen Ω) (bd : H1P Ω →ₗ[ℝ] H1P Ω →ₗ[ℝ] ℝ)
    (hbd : VanishesOnNullAEP Ω bd) {α : ℝ} (hα : 0 ≤ α) (hbd0 : ∀ v : H1P Ω, 0 ≤ bd v v) :
    Spectrum.BddBelowRatio (robinFormPQ hΩ bd hbd α) (massPQ (Ω := Ω)) :=
  ⟨0, le_rfl, fun w _ =>
    div_nonneg (robinFormPQ_nonneg hΩ bd hbd hα hbd0 w) (massPQ_nonneg w)⟩

/-- The Rayleigh ratio of the Robin form is bounded above on every finite-dimensional subspace
of the quotient: both forms are diagonals of bilinear maps and the mass is positive definite
(`RobinCaps.Spectrum.bddAbove_ratio_of_bilinear`). -/
theorem bddAboveRatio_robinFormPQ_on (hΩ : IsOpen Ω) (bd : H1P Ω →ₗ[ℝ] H1P Ω →ₗ[ℝ] ℝ)
    (hbd : VanishesOnNullAEP Ω bd) (α : ℝ) (V : Submodule ℝ (H1PQ Ω))
    [FiniteDimensional ℝ V] :
    BddAbove (Set.range fun w : {w : V // w ≠ 0} =>
      robinFormPQ hΩ bd hbd α ((w : V) : H1PQ Ω) / massPQ ((w : V) : H1PQ Ω)) := by
  have hfun : (fun w : {w : V // w ≠ 0} =>
        robinFormPQ hΩ bd hbd α ((w : V) : H1PQ Ω) / massPQ ((w : V) : H1PQ Ω))
      = fun w : {w : V // w ≠ 0} =>
        (dirichletBilinPQ hΩ + α • bdQ bd hbd) ((w : V) : H1PQ Ω) ((w : V) : H1PQ Ω)
          / massBilinPQ ((w : V) : H1PQ Ω) ((w : V) : H1PQ Ω) := by
    funext w
    rw [robinFormPQ_eq_bilin]
    rfl
  rw [hfun]
  exact Spectrum.bddAbove_ratio_of_bilinear (dirichletBilinPQ hΩ + α • bdQ bd hbd)
    massBilinPQ massPQ_pos V

/-! ### The variational eigenvalues `λ_j(Ω;α)` -/

/-- **The variational eigenvalues of the manuscript** (`eq:minmax`):
`λ_j(Ω;α) = min_{V, dim V = j} max_{0 ≠ u ∈ V} q_Ω[u] / N_Ω[u]`, computed on the quotient
`H1PQ Ω`, where the mass is positive definite.  With `bd` the boundary trace pairing this is
`λ_j(Ω;α)` of the thin-domain Robin problem. -/
def lambdaPQ (hΩ : IsOpen Ω) (bd : H1P Ω →ₗ[ℝ] H1P Ω →ₗ[ℝ] ℝ)
    (hbd : VanishesOnNullAEP Ω bd) (α : ℝ) (j : ℕ) : ℝ :=
  Spectrum.minmax (robinFormPQ hΩ bd hbd α) (massPQ (Ω := Ω)) j

/-- **Trial-space upper bound for `λ_j(Ω;α)`** (`RobinCaps.Spectrum.minmax_le_of_trial'`):
a `j`-dimensional subspace of `H1PQ Ω` on which `q_Ω ≤ t · N_Ω` bounds `λ_j` by `t`. -/
theorem lambdaPQ_le_of_trial (hΩ : IsOpen Ω) (bd : H1P Ω →ₗ[ℝ] H1P Ω →ₗ[ℝ] ℝ)
    (hbd : VanishesOnNullAEP Ω bd) {α : ℝ} (hα : 0 ≤ α) (hbd0 : ∀ v : H1P Ω, 0 ≤ bd v v)
    (j : ℕ) (hj : 0 < j) (W : Submodule ℝ (H1PQ Ω)) (hW : Module.finrank ℝ W = j) (t : ℝ)
    (h : ∀ w ∈ W, w ≠ 0 → robinFormPQ hΩ bd hbd α w ≤ t * massPQ w) :
    lambdaPQ hΩ bd hbd α j ≤ t :=
  Spectrum.minmax_le_of_trial' (robinFormPQ hΩ bd hbd α) (massPQ (Ω := Ω)) j hj massPQ_pos
    (bddBelowRatio_robinFormPQ hΩ bd hbd hα hbd0) W hW t h

/-- **Finite-codimension lower bound for `λ_j(Ω;α)`**
(`RobinCaps.Spectrum.le_minmax_of_codim'`): if `t · N_Ω ≤ q_Ω` on the kernel of a
`(j-1)`-dimensional constraint `φ`, then `t ≤ λ_j`.  The per-subspace boundedness of the
Rayleigh quotient required by the engine is supplied by
`RobinCaps.Spectrum.bddAbove_ratio_of_bilinear` with
`Q = dirichletBilinPQ hΩ + α • bdQ bd hbd` and `B = massBilinPQ`. -/
theorem le_lambdaPQ_of_codim (hΩ : IsOpen Ω) (bd : H1P Ω →ₗ[ℝ] H1P Ω →ₗ[ℝ] ℝ)
    (hbd : VanishesOnNullAEP Ω bd) (α : ℝ) (j : ℕ) (hj : 1 ≤ j)
    (φ : H1PQ Ω →ₗ[ℝ] (Fin (j - 1) → ℝ))
    (hφ : Module.finrank ℝ (LinearMap.range φ) = j - 1) (t : ℝ)
    (h : ∀ w : H1PQ Ω, w ≠ 0 → φ w = 0 → t * massPQ w ≤ robinFormPQ hΩ bd hbd α w)
    (hex : ∃ V : Submodule ℝ (H1PQ Ω), Module.finrank ℝ V = j) :
    t ≤ lambdaPQ hΩ bd hbd α j := by
  refine Spectrum.le_minmax_of_codim' (robinFormPQ hΩ bd hbd α) (massPQ (Ω := Ω)) j hj
    massPQ_pos ?_ φ hφ t h hex
  intro V hV
  haveI : FiniteDimensional ℝ V := FiniteDimensional.of_finrank_pos (by omega)
  exact bddAboveRatio_robinFormPQ_on hΩ bd hbd α V

/-! ### Monotonicity of `λ_j(Ω;α)` -/

/-- **Monotonicity in the boundary form.**  If `bd₁ v v ≤ bd₂ v v` for every `v ∈ H1P Ω` and
`α ≥ 0`, then `λ_j` computed with `bd₁` is at most `λ_j` computed with `bd₂` (for `j ≥ 1`).

The engine's `RobinCaps.Spectrum.minmax_mono` would require the global upper ratio bound
`BddAboveRatio` for the larger form, which is false for Robin forms; we use the variant
`RobinCaps.Spectrum.minmax_mono'` with per-subspace bounds instead, which is why `1 ≤ j` is
assumed (it makes every competitor subspace finite dimensional). -/
theorem lambdaPQ_mono_bd (hΩ : IsOpen Ω) (bd₁ bd₂ : H1P Ω →ₗ[ℝ] H1P Ω →ₗ[ℝ] ℝ)
    (hbd₁ : VanishesOnNullAEP Ω bd₁) (hbd₂ : VanishesOnNullAEP Ω bd₂)
    {α : ℝ} (hα : 0 ≤ α) (hbd0 : ∀ v : H1P Ω, 0 ≤ bd₁ v v)
    (hle : ∀ v : H1P Ω, bd₁ v v ≤ bd₂ v v) (j : ℕ) (hj : 1 ≤ j) :
    lambdaPQ hΩ bd₁ hbd₁ α j ≤ lambdaPQ hΩ bd₂ hbd₂ α j := by
  refine Spectrum.minmax_mono' ?_ massPQ_pos
    (bddBelowRatio_robinFormPQ hΩ bd₁ hbd₁ hα hbd0) j ?_
  · intro w
    obtain ⟨u, rfl⟩ := Submodule.Quotient.mk_surjective (nullAEP Ω) w
    rw [robinFormPQ_mk, robinFormPQ_mk]
    have := mul_le_mul_of_nonneg_left (hle u) hα
    linarith
  · intro V hV
    haveI : FiniteDimensional ℝ V := FiniteDimensional.of_finrank_pos (by omega)
    exact bddAboveRatio_robinFormPQ_on hΩ bd₂ hbd₂ α V

/-- **Monotonicity in the Robin parameter `α`.**  For a nonnegative boundary form and
`0 ≤ α₁ ≤ α₂`, the variational eigenvalues increase with `α` (for `j ≥ 1`). -/
theorem lambdaPQ_mono_alpha (hΩ : IsOpen Ω) (bd : H1P Ω →ₗ[ℝ] H1P Ω →ₗ[ℝ] ℝ)
    (hbd : VanishesOnNullAEP Ω bd) (hbd0 : ∀ v : H1P Ω, 0 ≤ bd v v)
    {α₁ α₂ : ℝ} (hα₁ : 0 ≤ α₁) (hα : α₁ ≤ α₂) (j : ℕ) (hj : 1 ≤ j) :
    lambdaPQ hΩ bd hbd α₁ j ≤ lambdaPQ hΩ bd hbd α₂ j := by
  refine Spectrum.minmax_mono' ?_ massPQ_pos
    (bddBelowRatio_robinFormPQ hΩ bd hbd hα₁ hbd0) j ?_
  · intro w
    obtain ⟨u, rfl⟩ := Submodule.Quotient.mk_surjective (nullAEP Ω) w
    rw [robinFormPQ_mk, robinFormPQ_mk]
    have := mul_le_mul_of_nonneg_right hα (hbd0 u)
    linarith
  · intro V hV
    haveI : FiniteDimensional ℝ V := FiniteDimensional.of_finrank_pos (by omega)
    exact bddAboveRatio_robinFormPQ_on hΩ bd hbd α₂ V

end RobinCaps.ThinDomain

end
