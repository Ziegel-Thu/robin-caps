import Mathlib
import RobinCaps.Sobolev.Weak
import RobinCaps.Spectrum.FormEngine
import RobinCaps.Spectrum.MainAbstract

/-!
# The transverse Robin ground state on `B_m(R)`, as data

This file formalizes `sec:transverse` / `lem:transverse` of the manuscript
`reference/robin_endcaps_corrected_en.tex` (lines 428–560) in the only honest way available
inside mathlib `v4.26.0`: the transverse ground state `ψ_R` of the Robin Laplacian on the ball
`B_m(R)` is packaged as **explicit data** (`TransverseGroundState`) carrying its defining
properties, and all the *algebraic* consequences that the bulk decomposition
`eq:exact-separation` (line 535) needs are proved from that data.

**Nothing here proves existence of `ψ_R`.**  Existence is a genuine analytic theorem (a Rayleigh
minimiser on `H¹(B_m(R))`, i.e. Rellich–Kondrachov compactness, which mathlib does not have; see
`RellichEmbedding` in `RobinCaps/Sobolev/Weak.lean`).  It is isolated as the target
`HasTransverseGroundState`, and the quantitative expansions of `lem:transverse` are isolated as
the targets in the final section.  This keeps the missing brick visible instead of hiding it in
a `sorry`.

## The setting

Everything happens on `E = EuclideanSpace ℝ (Fin m)`, on the ball `B = transverseBall m R`,
in the weak Sobolev space `TransH1 m R = Weak.H1 B` of `RobinCaps/Sobolev/Weak.lean`.

The boundary (Robin) term is a **parameter**: a bilinear form
`bd : TransH1 m R →ₗ[ℝ] TransH1 m R →ₗ[ℝ] ℝ`, which is intended to be
`bd u v = ∫_{∂B} (Tr u)(Tr v) dℋ^{m-1}`.  No trace operator is defined here — mathlib has none,
and inventing one would be dishonest.  Symmetry and nonnegativity of `bd` are recorded as
fields `bdSymm`, `bdNonneg` of `TransverseGroundState`, since the weak eigenvalue equation is
only meaningful for a symmetric form.

The two forms are

* `qB α bd v = Weak.dirichlet v + α * bd v v`  (`q_{B_m(R)}[v]`, `eq:robin-form`);
* `NB v = Weak.mass v = ∫_B |v|²`             (`N_{B_m(R)}[v]`),

together with their polarizations `qBilin α bd`, `NBilin`, which are genuine `ℝ`-bilinear maps
(`qBilinₗ`, `NBilinₗ`).  Building these bilinear forms on `Weak.H1` (mathlib only provides the
quadratic forms `Weak.dirichlet`, `Weak.mass`) is the first half of the file; the `L²`-pairings
are integrable by Cauchy–Schwarz, via the Hölder triple `(2,2,1)` instance of `Weak.lean`.

## The algebraic consequences (§2 of the brief)

For a ground state `gs : TransverseGroundState m α R bd` and any `v`:

* `nu_eq_rayleigh`     : `gs.nu = qB α bd gs.psi`;
* `proj`               : `gs.proj v = v - (NBilin gs.psi v) • gs.psi`;
* `NBilin_psi_proj`    : `NBilin gs.psi (gs.proj v) = 0`;
* `mass_split`         : `NB v = (NBilin gs.psi v)^2 + NB (gs.proj v)`   (`eq:bulk-mass`, 539);
* `energy_split`       : `qB α bd v - gs.nu * NB v = qB α bd (gs.proj v) - gs.nu * NB (gs.proj v)`
                         (the cross terms cancel by the weak eigenvalue equation — this is the
                         sentence at lines 543–545 of the manuscript);
* `energy_lower`       : `gs.gapConst * R⁻¹^2 * NB (gs.proj v) ≤ qB α bd v - gs.nu * NB v`
                         (the transverse half of `eq:exact-separation` / `eq:T-bound`, 535–536);
* `nu_mul_mass_le`     : `gs.nu * NB v ≤ qB α bd v` for **every** `v`;
* `qB_psi_eq_nu`       : `qB α bd gs.psi = gs.nu` with `NB gs.psi = 1` (the trial bound);
* `bulkComparison`     : the data feeds `Spectrum.BulkComparison` of
                         `RobinCaps/Spectrum/MainAbstract.lean` with the remainder
                         `Z v = NB (gs.proj v) ≥ 0` in exactly the required shape.

### Why not `gs.nu ≤ Spectrum.minmax (qB α bd) NB 1`?

`Spectrum.minmax` is only meaningful when the mass is positive on nonzero vectors, and both
`Spectrum.minmax_le_of_trial` and `Spectrum.le_minmax_of_codim` take `∀ u ≠ 0, 0 < b u` as a
hypothesis.  On the *un-quotiented* `Weak.H1 B` this is false: a nonzero element of `Weak.H1 B`
can have `toFun = 0` a.e. on `B` (nothing forces the representative to be supported in `B`), and
then `NB v = 0`.  Rather than build the quotient by a.e. equality here (a separate unit; the
1-D analogue is `RobinCaps/Sobolev/Quotient.lean`), we give the two *pointwise* statements that
carry all the spectral content and survive passage to any quotient:

* `nu_mul_mass_le : ∀ v, gs.nu * NB v ≤ qB α bd v` — the Rayleigh quotient is `≥ gs.nu`
  wherever it is defined, i.e. `gs.nu ≤ λ₁`;
* `qB_psi_eq_nu` together with `normalized : NB gs.psi = 1` — the trial function `gs.psi`
  realizes the value `gs.nu`, i.e. `λ₁ ≤ gs.nu`.

Together they say `gs.nu = λ₁(B_m(R); α)` in any setting where `minmax` is well defined.  Both
halves are also recorded formally, as `minmax_le_nu` and `nu_le_minmax`, with the positivity of
`NB` on nonzero vectors (and the ratio bounds of `Spectrum.FormEngine`) taken as explicit
hypotheses, so that they become unconditional as soon as the quotient is built.

No `sorry`, `admit`, `axiom` or `native_decide` occurs in this file.
-/

noncomputable section

namespace RobinCaps.ThinDomain

open MeasureTheory RobinCaps.Sobolev

open scoped InnerProductSpace ENNReal

/-! ## Part 1. Bilinear forms on the multi-dimensional weak Sobolev space

`RobinCaps/Sobolev/Weak.lean` provides the quadratic forms `Weak.dirichlet` and `Weak.mass`
only.  Their polarizations are built here, mirroring `robinBilin`/`massBilin` of
`RobinCaps/Sobolev/VariationBridge.lean` (which are the one-dimensional analogues) and packaged
as honest `LinearMap`s through `LinearMap.mk₂`, as in `RobinCaps/Sobolev/Quotient.lean`. -/

section Bilinear

variable {n : ℕ} {D : Set (EuclideanSpace ℝ (Fin n))}

/-! ### Integrability of the pairings -/

/-- The `L²` pairing of two elements of `H¹(D)` is integrable (Cauchy–Schwarz, through the
Hölder triple `(2,2,1)` registered in `RobinCaps/Sobolev/Weak.lean`). -/
theorem integrable_toFun_mul (u v : Weak.H1 D) :
    Integrable (fun x => u.toFun x * v.toFun x) (volume.restrict D) :=
  u.memL2.integrable_mul v.memL2

/-- The pointwise inner product of the two weak gradients is integrable. -/
theorem integrable_inner_grad (u v : Weak.H1 D) :
    Integrable (fun x => ⟪u.grad x, v.grad x⟫_ℝ) (volume.restrict D) := by
  have hmul : Integrable (fun x => ‖u.grad x‖ * ‖v.grad x‖) (volume.restrict D) :=
    u.grad_memL2.norm.integrable_mul v.grad_memL2.norm
  refine hmul.mono'
    (u.grad_memL2.aestronglyMeasurable.inner v.grad_memL2.aestronglyMeasurable) ?_
  filter_upwards with x
  simpa only [Real.norm_eq_abs] using abs_real_inner_le_norm (u.grad x) (v.grad x)

/-! ### The two bilinear forms -/

/-- The `L²(D)` inner product `⟪u, v⟫_{L²(D)} = ∫_D u v`; its diagonal is `Weak.mass`. -/
def massBilin (u v : Weak.H1 D) : ℝ := ∫ x in D, u.toFun x * v.toFun x

/-- The Dirichlet bilinear form `∫_D ⟪∇u, ∇v⟫`; its diagonal is `Weak.dirichlet`. -/
def dirichletBilin (u v : Weak.H1 D) : ℝ := ∫ x in D, ⟪u.grad x, v.grad x⟫_ℝ

@[simp] theorem massBilin_self (u : Weak.H1 D) : massBilin u u = Weak.mass u := by
  simp only [massBilin, Weak.mass, pow_two]

@[simp] theorem dirichletBilin_self (u : Weak.H1 D) : dirichletBilin u u = Weak.dirichlet u := by
  simp only [dirichletBilin, Weak.dirichlet, real_inner_self_eq_norm_sq]

theorem massBilin_comm (u v : Weak.H1 D) : massBilin u v = massBilin v u :=
  integral_congr_ae (Filter.Eventually.of_forall fun _ => mul_comm _ _)

theorem dirichletBilin_comm (u v : Weak.H1 D) : dirichletBilin u v = dirichletBilin v u :=
  integral_congr_ae (Filter.Eventually.of_forall fun _ => real_inner_comm _ _)

theorem massBilin_add_left (u v w : Weak.H1 D) :
    massBilin (u + v) w = massBilin u w + massBilin v w := by
  have h : ∀ x, (u + v).toFun x * w.toFun x
      = u.toFun x * w.toFun x + v.toFun x * w.toFun x := by
    intro x
    simp only [Weak.H1.add_toFun, Pi.add_apply]
    ring
  simp only [massBilin, h]
  exact integral_add (integrable_toFun_mul u w) (integrable_toFun_mul v w)

theorem massBilin_smul_left (c : ℝ) (u v : Weak.H1 D) :
    massBilin (c • u) v = c * massBilin u v := by
  simp only [massBilin]
  rw [← integral_const_mul]
  refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
  simp only [Weak.H1.smul_toFun, Pi.smul_apply, smul_eq_mul]
  ring

theorem massBilin_add_right (u v w : Weak.H1 D) :
    massBilin u (v + w) = massBilin u v + massBilin u w := by
  rw [massBilin_comm u (v + w), massBilin_add_left v w u, massBilin_comm v u,
    massBilin_comm w u]

theorem massBilin_smul_right (c : ℝ) (u v : Weak.H1 D) :
    massBilin u (c • v) = c * massBilin u v := by
  rw [massBilin_comm u (c • v), massBilin_smul_left c v u, massBilin_comm v u]

theorem dirichletBilin_add_left (u v w : Weak.H1 D) :
    dirichletBilin (u + v) w = dirichletBilin u w + dirichletBilin v w := by
  have h : ∀ x, ⟪(u + v).grad x, w.grad x⟫_ℝ
      = ⟪u.grad x, w.grad x⟫_ℝ + ⟪v.grad x, w.grad x⟫_ℝ := by
    intro x
    simp only [Weak.H1.add_grad, Pi.add_apply]
    exact inner_add_left _ _ _
  simp only [dirichletBilin, h]
  exact integral_add (integrable_inner_grad u w) (integrable_inner_grad v w)

theorem dirichletBilin_smul_left (c : ℝ) (u v : Weak.H1 D) :
    dirichletBilin (c • u) v = c * dirichletBilin u v := by
  simp only [dirichletBilin]
  rw [← integral_const_mul]
  refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
  simp only [Weak.H1.smul_grad, Pi.smul_apply]
  exact real_inner_smul_left _ _ _

theorem dirichletBilin_add_right (u v w : Weak.H1 D) :
    dirichletBilin u (v + w) = dirichletBilin u v + dirichletBilin u w := by
  rw [dirichletBilin_comm u (v + w), dirichletBilin_add_left v w u, dirichletBilin_comm v u,
    dirichletBilin_comm w u]

theorem dirichletBilin_smul_right (c : ℝ) (u v : Weak.H1 D) :
    dirichletBilin u (c • v) = c * dirichletBilin u v := by
  rw [dirichletBilin_comm u (c • v), dirichletBilin_smul_left c v u, dirichletBilin_comm v u]

/-! ### Packaging as `LinearMap`s -/

/-- The `L²(D)` inner product as an honest bilinear map. -/
def massBilinₗ (D : Set (EuclideanSpace ℝ (Fin n))) : Weak.H1 D →ₗ[ℝ] Weak.H1 D →ₗ[ℝ] ℝ :=
  LinearMap.mk₂ ℝ massBilin massBilin_add_left
    (fun c u v => (massBilin_smul_left c u v).trans (smul_eq_mul c _).symm)
    massBilin_add_right
    (fun c u v => (massBilin_smul_right c u v).trans (smul_eq_mul c _).symm)

@[simp] theorem massBilinₗ_apply (D : Set (EuclideanSpace ℝ (Fin n))) (u v : Weak.H1 D) :
    massBilinₗ D u v = massBilin u v := rfl

/-- The Dirichlet form as an honest bilinear map. -/
def dirichletBilinₗ (D : Set (EuclideanSpace ℝ (Fin n))) : Weak.H1 D →ₗ[ℝ] Weak.H1 D →ₗ[ℝ] ℝ :=
  LinearMap.mk₂ ℝ dirichletBilin dirichletBilin_add_left
    (fun c u v => (dirichletBilin_smul_left c u v).trans (smul_eq_mul c _).symm)
    dirichletBilin_add_right
    (fun c u v => (dirichletBilin_smul_right c u v).trans (smul_eq_mul c _).symm)

@[simp] theorem dirichletBilinₗ_apply (D : Set (EuclideanSpace ℝ (Fin n))) (u v : Weak.H1 D) :
    dirichletBilinₗ D u v = dirichletBilin u v := rfl

end Bilinear

/-! ### An abstract polarization identity

The only piece of algebra used below: for a symmetric bilinear form `B`,
`B (v - c•p) (v - c•p) = B v v - 2 c B p v + c² B p p`. -/

/-- Expansion of the diagonal of a symmetric bilinear form along `v ↦ v - c • p`. -/
theorem bilin_sub_smul_self {W : Type*} [AddCommGroup W] [Module ℝ W]
    (B : W →ₗ[ℝ] W →ₗ[ℝ] ℝ) (hB : ∀ x y : W, B x y = B y x) (p v : W) (c : ℝ) :
    B (v - c • p) (v - c • p) = B v v - 2 * c * B p v + c ^ 2 * B p p := by
  simp only [map_sub, map_smul, LinearMap.sub_apply, LinearMap.smul_apply, smul_eq_mul]
  rw [hB v p]
  ring

/-! ## Part 2. The transverse ball and its two forms -/

/-- The transverse ball `B_m(R) = {z ∈ ℝ^m : |z| < R}` (`sec:transverse`). -/
def transverseBall (m : ℕ) (R : ℝ) : Set (EuclideanSpace ℝ (Fin m)) := Metric.ball 0 R

/-- The weak Sobolev space `H¹(B_m(R))` in which the transverse ground state lives. -/
abbrev TransH1 (m : ℕ) (R : ℝ) : Type := Weak.H1 (transverseBall m R)

variable {m : ℕ} {α R : ℝ}

/-- The transverse mass `N_{B_m(R)}[v] = ∫_{B_m(R)} |v|²` (`eq:robin-form`). -/
def NB (v : TransH1 m R) : ℝ := Weak.mass v

/-- The transverse mass as a bilinear form (the `L²(B_m(R))` inner product). -/
def NBilinₗ (m : ℕ) (R : ℝ) : TransH1 m R →ₗ[ℝ] TransH1 m R →ₗ[ℝ] ℝ :=
  massBilinₗ (transverseBall m R)

/-- The `L²(B_m(R))` inner product, `NBilin u v = ∫_{B_m(R)} u v`. -/
def NBilin (u v : TransH1 m R) : ℝ := NBilinₗ m R u v

/-- The transverse Robin form `q_{B_m(R)}[v] = ∫_{B_m(R)} |∇v|² + α · bd v v`, where the
boundary term `bd` is a parameter (intended: `∫_{∂B_m(R)} |Tr v|² dℋ^{m-1}`). -/
def qB (α : ℝ) (bd : TransH1 m R →ₗ[ℝ] TransH1 m R →ₗ[ℝ] ℝ) (v : TransH1 m R) : ℝ :=
  Weak.dirichlet v + α * bd v v

/-- The transverse Robin form as a bilinear map, `dirichletBilin + α • bd`. -/
def qBilinₗ (α : ℝ) (bd : TransH1 m R →ₗ[ℝ] TransH1 m R →ₗ[ℝ] ℝ) :
    TransH1 m R →ₗ[ℝ] TransH1 m R →ₗ[ℝ] ℝ :=
  dirichletBilinₗ (transverseBall m R) + α • bd

/-- The polarization of `qB`. -/
def qBilin (α : ℝ) (bd : TransH1 m R →ₗ[ℝ] TransH1 m R →ₗ[ℝ] ℝ) (u v : TransH1 m R) : ℝ :=
  qBilinₗ α bd u v

theorem NBilinₗ_apply (u v : TransH1 m R) : NBilinₗ m R u v = NBilin u v := rfl

theorem qBilinₗ_apply (α : ℝ) (bd : TransH1 m R →ₗ[ℝ] TransH1 m R →ₗ[ℝ] ℝ)
    (u v : TransH1 m R) : qBilinₗ α bd u v = qBilin α bd u v := rfl

theorem NBilin_eq_massBilin (u v : TransH1 m R) : NBilin u v = massBilin u v := rfl

theorem qBilin_eq (α : ℝ) (bd : TransH1 m R →ₗ[ℝ] TransH1 m R →ₗ[ℝ] ℝ)
    (u v : TransH1 m R) : qBilin α bd u v = dirichletBilin u v + α * bd u v := by
  show qBilinₗ α bd u v = _
  simp only [qBilinₗ, LinearMap.add_apply, LinearMap.smul_apply, smul_eq_mul,
    dirichletBilinₗ_apply]

theorem NBilin_self (v : TransH1 m R) : NBilin v v = NB v :=
  massBilin_self (D := transverseBall m R) v

theorem qBilin_self (α : ℝ) (bd : TransH1 m R →ₗ[ℝ] TransH1 m R →ₗ[ℝ] ℝ)
    (v : TransH1 m R) : qBilin α bd v v = qB α bd v := by
  rw [qBilin_eq, dirichletBilin_self, qB]

theorem NBilin_comm (u v : TransH1 m R) : NBilin u v = NBilin v u :=
  massBilin_comm (D := transverseBall m R) u v

theorem NB_nonneg (v : TransH1 m R) : 0 ≤ NB v := Weak.mass_nonneg v

/-! ## Part 3. The transverse ground state as data -/

/-- **The transverse Robin ground state of `B_m(R)`, as explicit data** (`sec:transverse`,
`lem:transverse`, manuscript lines 428–490).

The fields are exactly the defining properties of `ψ_R` and `ν_R = λ₁(B_m(R); α)` used by the
bulk decomposition `eq:exact-separation` (line 535):

* `psi` — the ground state `ψ_R ∈ H¹(B_m(R))`;
* `nu` — the ground state energy `ν_R`;
* `normalized` — `‖ψ_R‖_{L²(B_m(R))} = 1`;
* `weak_eq` — the **weak eigenvalue equation**: `q_B(ψ_R, v) = ν_R ⟪ψ_R, v⟫` for all `v`;
* `gapConst`, `gapConst_pos`, `gap` — the **transverse spectral gap** `eq:transverse-gap`
  (line 444) in its variational form: on the `L²`-orthogonal complement of `ψ_R`,
  `q_B[v] - ν_R N[v] ≥ c R⁻² N[v]`.  This is `eq:T-bound` (line 536) in the transverse
  variable.

`bdSymm` and `bdNonneg` record that the boundary form parameter `bd` is symmetric and
nonnegative; symmetry is what makes `weak_eq` an eigenvalue equation rather than a one-sided
condition, and it is used in `energy_split`.

**No instance of this structure is constructed in this file**, see `HasTransverseGroundState`.
Radiality and positivity of `ψ_R` (which the manuscript also asserts) are deliberately omitted:
they are not used by any consequence proved below. -/
structure TransverseGroundState (m : ℕ) (α R : ℝ)
    (bd : TransH1 m R →ₗ[ℝ] TransH1 m R →ₗ[ℝ] ℝ) where
  /-- The boundary form is symmetric. -/
  bdSymm : ∀ u v : TransH1 m R, bd u v = bd v u
  /-- The boundary form is nonnegative on the diagonal. -/
  bdNonneg : ∀ v : TransH1 m R, 0 ≤ bd v v
  /-- The ground state `ψ_R`. -/
  psi : TransH1 m R
  /-- The ground state energy `ν_R = λ₁(B_m(R); α)`. -/
  nu : ℝ
  /-- `ψ_R` is `L²`-normalized. -/
  normalized : NB psi = 1
  /-- The weak eigenvalue equation for `ψ_R`. -/
  weak_eq : ∀ v : TransH1 m R, qBilin α bd psi v = nu * NBilin psi v
  /-- The constant `c > 0` of the transverse gap `eq:transverse-gap`. -/
  gapConst : ℝ
  /-- The gap constant is positive. -/
  gapConst_pos : 0 < gapConst
  /-- **The transverse gap** `eq:transverse-gap` in variational form. -/
  gap : ∀ v : TransH1 m R, NBilin psi v = 0 →
    gapConst * R⁻¹ ^ 2 * NB v ≤ qB α bd v - nu * NB v

namespace TransverseGroundState

variable {bd : TransH1 m R →ₗ[ℝ] TransH1 m R →ₗ[ℝ] ℝ} (gs : TransverseGroundState m α R bd)

include gs in
/-- The Robin form `qBilin` is symmetric (the Dirichlet part always is; the boundary part is by
`gs.bdSymm`). -/
theorem qBilin_symm (u v : TransH1 m R) : qBilin α bd u v = qBilin α bd v u := by
  rw [qBilin_eq, qBilin_eq, dirichletBilin_comm, gs.bdSymm]

theorem NBilin_psi_psi : NBilin gs.psi gs.psi = 1 := by
  rw [NBilin_self]; exact gs.normalized

/-! ### The Rayleigh value of the ground state -/

/-- **`ν_R` is the Rayleigh quotient of `ψ_R`**: testing the weak equation against `ψ_R` itself
and using the normalization. -/
theorem nu_eq_rayleigh : gs.nu = qB α bd gs.psi := by
  have h := gs.weak_eq gs.psi
  rw [qBilin_self, gs.NBilin_psi_psi, mul_one] at h
  exact h.symm

/-- The trial bound: `ψ_R` has energy exactly `ν_R` and mass exactly `1`. -/
theorem qB_psi_eq_nu : qB α bd gs.psi = gs.nu := gs.nu_eq_rayleigh.symm

/-! ### The `L²`-orthogonal projection off `ψ_R` -/

/-- The transverse remainder `v ↦ v - ⟪v, ψ_R⟫ ψ_R` — the `w` of `eq:bulk-projection`
(manuscript line 528), in the transverse variable only. -/
def proj (v : TransH1 m R) : TransH1 m R := v - (NBilin gs.psi v) • gs.psi

/-- The remainder is `L²`-orthogonal to `ψ_R` (`eq:bulk-projection`, line 529). -/
theorem NBilin_psi_proj (v : TransH1 m R) : NBilin gs.psi (gs.proj v) = 0 := by
  have h : NBilin gs.psi (gs.proj v)
      = NBilin gs.psi v - (NBilin gs.psi v) * NBilin gs.psi gs.psi := by
    show NBilinₗ m R gs.psi (v - (NBilin gs.psi v) • gs.psi) = _
    simp only [map_sub, map_smul, smul_eq_mul, NBilinₗ_apply]
  rw [h, gs.NBilin_psi_psi, mul_one, sub_self]

/-! ### The exact splitting of mass and energy -/

/-- **Exact mass splitting** (`eq:bulk-mass`, manuscript line 539, transverse variable):
`N[v] = ⟪v, ψ_R⟫² + N[v - ⟪v, ψ_R⟫ ψ_R]`. -/
theorem NBilin_proj_proj (v : TransH1 m R) :
    NBilin (gs.proj v) (gs.proj v) = NB v - (NBilin gs.psi v) ^ 2 := by
  have h := bilin_sub_smul_self (NBilinₗ m R) NBilin_comm gs.psi v (NBilin gs.psi v)
  simp only [NBilinₗ_apply] at h
  rw [show gs.proj v = v - (NBilin gs.psi v) • gs.psi from rfl, h, NBilin_self,
    gs.NBilin_psi_psi]
  ring

/-- **Exact mass splitting** (`eq:bulk-mass`, manuscript line 539, transverse variable):
`N[v] = ⟪v, ψ_R⟫² + N[v - ⟪v, ψ_R⟫ ψ_R]`. -/
theorem mass_split (v : TransH1 m R) : NB v = (NBilin gs.psi v) ^ 2 + NB (gs.proj v) := by
  have h := gs.NBilin_proj_proj v
  rw [NBilin_self] at h
  linarith

/-- **Exact energy splitting** (the identity behind `eq:exact-separation`, manuscript
lines 535 and 543–545): the renormalized energy of `v` equals that of its transverse remainder.
The cross terms cancel by the weak eigenvalue equation for `ψ_R`. -/
theorem qB_proj (v : TransH1 m R) :
    qB α bd (gs.proj v) = qB α bd v - gs.nu * (NBilin gs.psi v) ^ 2 := by
  have h := bilin_sub_smul_self (qBilinₗ α bd) gs.qBilin_symm gs.psi v (NBilin gs.psi v)
  simp only [qBilinₗ_apply] at h
  rw [show gs.proj v = v - (NBilin gs.psi v) • gs.psi from rfl, ← qBilin_self, h,
    qBilin_self, gs.weak_eq v, gs.weak_eq gs.psi, gs.NBilin_psi_psi]
  ring

/-- **Exact energy splitting** (the identity behind `eq:exact-separation`, manuscript
lines 535 and 543–545): the renormalized energy of `v` equals that of its transverse remainder.
The cross terms cancel by the weak eigenvalue equation for `ψ_R`. -/
theorem energy_split (v : TransH1 m R) :
    qB α bd v - gs.nu * NB v = qB α bd (gs.proj v) - gs.nu * NB (gs.proj v) := by
  rw [gs.qB_proj v, gs.mass_split v]
  ring

/-- **The transverse half of `eq:exact-separation` / `eq:T-bound`** (manuscript lines 535–536):
the renormalized transverse energy controls the mass of the remainder, with the gap constant. -/
theorem energy_lower (v : TransH1 m R) :
    gs.gapConst * R⁻¹ ^ 2 * NB (gs.proj v) ≤ qB α bd v - gs.nu * NB v := by
  rw [gs.energy_split v]
  exact gs.gap _ (gs.NBilin_psi_proj v)

/-- The remainder term of `energy_lower` is nonnegative. -/
theorem gap_term_nonneg (v : TransH1 m R) : 0 ≤ gs.gapConst * R⁻¹ ^ 2 * NB (gs.proj v) :=
  mul_nonneg (mul_nonneg gs.gapConst_pos.le (sq_nonneg _)) (NB_nonneg _)

/-- **`ν_R` is a lower bound for the Rayleigh quotient**: `ν_R N[v] ≤ q_B[v]` for *every*
`v ∈ H¹(B_m(R))`.  Together with `qB_psi_eq_nu` and `normalized` this says
`ν_R = λ₁(B_m(R); α)` in any formulation of `λ₁` as an infimum of Rayleigh quotients. -/
theorem nu_mul_mass_le (v : TransH1 m R) : gs.nu * NB v ≤ qB α bd v := by
  have h := gs.energy_lower v
  have h0 := gs.gap_term_nonneg v
  linarith

/-- The remainder has no more mass than `v` itself. -/
theorem mass_proj_le (v : TransH1 m R) : NB (gs.proj v) ≤ NB v := by
  rw [gs.mass_split v]
  nlinarith [sq_nonneg (NBilin gs.psi v)]

/-- For a nonnegative Robin parameter the ground state energy is nonnegative. -/
theorem nu_nonneg (hα : 0 ≤ α) : 0 ≤ gs.nu := by
  rw [gs.nu_eq_rayleigh, qB]
  exact add_nonneg (Weak.dirichlet_nonneg _) (mul_nonneg hα (gs.bdNonneg _))

/-! ### Feeding the abstract bulk comparison

`RobinCaps/Spectrum/MainAbstract.lean` runs the two min–max comparison steps from a
`Spectrum.BulkComparison E N a b Z π h`.  In the transverse variable the decomposition of
`eq:bulk-projection` supplies it with `π = ⟪·, ψ_R⟫` (a genuine linear functional),
`Z v = N[v - ⟪v,ψ_R⟫ψ_R] ≥ 0`, bulk forms `a F = ν_R F²`, `b F = F²`, and energy weight
`h = c R⁻²`.  The mass comparison is an equality (`mass_split`) and the energy comparison is
`energy_lower`. -/

/-- The linear functional `v ↦ ⟪v, ψ_R⟫_{L²(B_m(R))}` — the transverse bulk projection `π`. -/
def pi : TransH1 m R →ₗ[ℝ] ℝ := NBilinₗ m R gs.psi

@[simp] theorem pi_apply (v : TransH1 m R) : gs.pi v = NBilin gs.psi v := rfl

/-- The remainder `Z` of the bulk decomposition is nonnegative. -/
theorem proj_mass_nonneg (v : TransH1 m R) : 0 ≤ NB (gs.proj v) := NB_nonneg _

/-- **The ground state data supplies a `Spectrum.BulkComparison` of exactly the shape used by
`RobinCaps/Spectrum/MainAbstract.lean`.** -/
theorem bulkComparison (hnu : 0 ≤ gs.nu) :
    Spectrum.BulkComparison (qB α bd) NB (fun F : ℝ => gs.nu * F ^ 2) (fun F : ℝ => F ^ 2)
      (fun v => NB (gs.proj v)) gs.pi (gs.gapConst * R⁻¹ ^ 2) := by
  constructor
  · intro v
    have h := gs.energy_lower v
    have hm := gs.mass_split v
    have hz : 0 ≤ gs.nu * NB (gs.proj v) := mul_nonneg hnu (NB_nonneg _)
    simp only [pi_apply]
    nlinarith
  · intro v
    exact le_of_eq (gs.mass_split v)

/-! ### The trial half of the min–max statement

`Spectrum.minmax` needs `0 < NB v` for `v ≠ 0`, which fails on the un-quotiented `Weak.H1`
(see the module docstring).  The trial bound is therefore stated with that positivity — and the
nondegeneracy of `ψ_R` — as explicit hypotheses, so that it becomes available verbatim once the
quotient by a.e. equality is built. -/

/-- **`λ₁ ≤ ν_R`**: the line `ℝ ∙ ψ_R` is a one-dimensional trial space on which
`q_B = ν_R N`, so `minmax (qB α bd) NB 1 ≤ ν_R` as soon as `NB` is positive on nonzero
vectors and `ψ_R ≠ 0`. -/
theorem minmax_le_nu (hpos : ∀ v : TransH1 m R, v ≠ 0 → 0 < NB v)
    (hA : Spectrum.BddAboveRatio (qB α bd) NB) (hB : Spectrum.BddBelowRatio (qB α bd) NB)
    (hpsi : gs.psi ≠ 0) :
    Spectrum.minmax (qB α bd) NB 1 ≤ gs.nu := by
  refine Spectrum.minmax_le_of_trial (qB α bd) NB 1 Nat.one_pos hpos hA hB
    (Submodule.span ℝ {gs.psi}) ?_ gs.nu ?_
  · rw [finrank_span_singleton hpsi]
  · intro u hu _
    rw [Submodule.mem_span_singleton] at hu
    obtain ⟨t, rfl⟩ := hu
    have hq : qB α bd (t • gs.psi) = t ^ 2 * qB α bd gs.psi := by
      rw [← qBilin_self, ← qBilin_self]
      show qBilinₗ α bd (t • gs.psi) (t • gs.psi) = t ^ 2 * qBilinₗ α bd gs.psi gs.psi
      simp only [map_smul, LinearMap.smul_apply, smul_eq_mul]
      ring
    have hn : NB (t • gs.psi) = t ^ 2 * NB gs.psi := by
      rw [← NBilin_self, ← NBilin_self]
      show NBilinₗ m R (t • gs.psi) (t • gs.psi) = t ^ 2 * NBilinₗ m R gs.psi gs.psi
      simp only [map_smul, LinearMap.smul_apply, smul_eq_mul]
      ring
    rw [hq, hn, gs.qB_psi_eq_nu, gs.normalized]
    apply le_of_eq
    ring

/-- **`ν_R ≤ λ₁`**, from `nu_mul_mass_le`: the pointwise inequality `ν_R N ≤ q_B` is exactly the
hypothesis of `Spectrum.le_minmax_of_codim` at `j = 1` (empty constraint). -/
theorem nu_le_minmax (hpos : ∀ v : TransH1 m R, v ≠ 0 → 0 < NB v)
    (hA : Spectrum.BddAboveRatio (qB α bd) NB)
    (hex : ∃ V : Submodule ℝ (TransH1 m R), Module.finrank ℝ V = 1) :
    gs.nu ≤ Spectrum.minmax (qB α bd) NB 1 := by
  refine Spectrum.le_minmax_of_codim (qB α bd) NB 1 le_rfl hpos hA 0 ?_ gs.nu ?_ hex
  · simp
  · exact fun v _ _ => gs.nu_mul_mass_le v

end TransverseGroundState

/-! ## Part 4. Targets

Everything below is a `Prop`-valued definition, originally recorded as a target.  None of them is
used above.  `HasTransverseGroundState` has since been proved for the Rellich boundary form and
small `R` (`Compact.hasTransverseGroundState_bdR`, `Compact/GroundStateExists.lean`). -/

/-- **TARGET (existence of the transverse ground state).**

`HasTransverseGroundState m α R bd` asserts that the data of `TransverseGroundState` exists for
the ball `B_m(R)` with Robin parameter `α` and boundary form `bd`.

**Status:** proved for `bd = bdR m R` and small `R` in `Compact/GroundStateExists.lean`
(`hasTransverseGroundState_bdR`), by route 1 below.  The original analysis of what an instance
requires follows:

1. *(direct method)* existence of a minimiser of the Rayleigh quotient
   `v ↦ q_B[v] / N[v]` on `H¹(B_m(R)) \ {0}`.  This needs the **Rellich–Kondrachov compact
   embedding** `H¹(B) ↪↪ L²(B)` together with a boundary trace operator and the trace
   inequality; mathlib `v4.26.0` has *none* of the three (see `Weak.RellichEmbedding`,
   `Weak.TraceExists`, `Weak.TraceInequality` in `RobinCaps/Sobolev/Weak.lean`).  The gap field
   then additionally needs the existence of the second eigenvalue `λ₂(B_m(R); α)` and the
   spectral theorem for the associated compact resolvent.
2. *(radial ODE route, Rellich-free)* the ground state is radial, so `ψ_R(z) = f(‖z‖)` with
   `-(r^{m-1} f')' = ν r^{m-1} f` on `(0,R)`, `f'(R) = -α f(R)` — a Bessel-type singular
   Sturm–Liouville problem.  The project already has one-dimensional phase-function machinery
   (`RobinCaps/Interval/Phase.lean`, `RobinCaps.Interval.mu`) that could be adapted.  This also
   requires the polar-coordinates reduction of integrals on the ball, which is itself not yet
   formalized here.

Both routes are large separate units.  Isolating them in this definition is the point of the
file: every theorem in Part 3 is unconditional *given* the data. -/
def HasTransverseGroundState (m : ℕ) (α R : ℝ)
    (bd : TransH1 m R →ₗ[ℝ] TransH1 m R →ₗ[ℝ] ℝ) : Prop :=
  Nonempty (TransverseGroundState m α R bd)

/-- **TARGET `eq:nu-expansion`** (manuscript line 442):
`R² ν_R = m α R + O(R²)` as `R ↓ 0`.

Here `nu : ℝ → ℝ` is intended to be `R ↦ ν_R = λ₁(B_m(R); α)`.  Unproved: it is a consequence of
the `H¹` estimate `eq:Psi-H1` plus the trace inequality on the unit ball (manuscript
lines 477–483), none of which is formalized. -/
def NuExpansionTarget (m : ℕ) (α : ℝ) (nu : ℝ → ℝ) : Prop :=
  ∃ C : ℝ, 0 < C ∧ ∃ R₀ : ℝ, 0 < R₀ ∧ ∀ R : ℝ, 0 < R → R < R₀ →
    |R ^ 2 * nu R - (m : ℝ) * α * R| ≤ C * R ^ 2

/-- **TARGET `eq:Psi-H1`** (manuscript line 443):
`‖Ψ_R - ω_m^{-1/2}‖_{H¹(B_m(1))} ≤ C R` as `R ↓ 0`, where
`Ψ_R(z) = R^{m/2} ψ_R(R z)` is the rescaled ground state (`eq:scaled-groundstate`, line 433) and
`ω_m = |B_m(1)|`.

`Psi R` is intended to be `Ψ_R ∈ H¹(B_m(1))` and `cst` the constant function `ω_m^{-1/2}`; the
squared `H¹` norm is `Weak.mass + Weak.dirichlet`.  Unproved: the manuscript's proof
(lines 462–476) uses the Poincaré and trace inequalities on the unit ball, neither of which is
formalized. -/
def PsiH1Target (m : ℕ) (Psi : ℝ → TransH1 m 1) (cst : TransH1 m 1) : Prop :=
  ∃ C : ℝ, 0 < C ∧ ∃ R₀ : ℝ, 0 < R₀ ∧ ∀ R : ℝ, 0 < R → R < R₀ →
    Weak.mass (Psi R - cst) + Weak.dirichlet (Psi R - cst) ≤ C ^ 2 * R ^ 2

/-- **TARGET `eq:d-R`** (manuscript lines 447–450):
`d_R = ∫_{B_m(1)} Ψ_R = √ω_m + O(R²)` and `d_R ≥ √ω_m / 2` for small `R`.

`omega` is intended to be `ω_m = |B_m(1)|`.  Unproved, for the same reason as `PsiH1Target`. -/
def DRTarget (m : ℕ) (Psi : ℝ → TransH1 m 1) (omega : ℝ) : Prop :=
  ∃ C : ℝ, 0 < C ∧ ∃ R₀ : ℝ, 0 < R₀ ∧ ∀ R : ℝ, 0 < R → R < R₀ →
    |(∫ z in transverseBall m 1, (Psi R).toFun z) - Real.sqrt omega| ≤ C * R ^ 2 ∧
      Real.sqrt omega / 2 ≤ ∫ z in transverseBall m 1, (Psi R).toFun z

/-- **TARGET `eq:transverse-gap`** (manuscript line 444):
`λ₂(B_m(R); α) - ν_R ≥ c R⁻²` for small `R`.

`lam2` and `nu` are intended to be `R ↦ λ₂(B_m(R); α)` and `R ↦ ν_R` for a fixed `α`.  This is the statement
whose *variational consequence* is taken as the field `TransverseGroundState.gap`; proving it
needs the existence of `λ₂` (hence the spectral theorem for the Robin Laplacian on the ball) and
the Neumann eigenvalue bound of manuscript lines 485–489.  Unproved. -/
def TransverseGapTarget (lam2 nu : ℝ → ℝ) : Prop :=
  ∃ c : ℝ, 0 < c ∧ ∃ R₀ : ℝ, 0 < R₀ ∧ ∀ R : ℝ, 0 < R → R < R₀ →
    c * R⁻¹ ^ 2 ≤ lam2 R - nu R

/-- **TARGET: `lem:transverse` in full** (manuscript lines 439–451).

The conjunction of the four statements of the lemma: the eigenvalue expansion
`eq:nu-expansion`, the `H¹` estimate `eq:Psi-H1`, the transverse gap `eq:transverse-gap` and
the mean-value estimate `eq:d-R`.  **Unproved.** -/
def TransverseExpansion (m : ℕ) (α : ℝ) (nu lam2 : ℝ → ℝ) (Psi : ℝ → TransH1 m 1)
    (cst : TransH1 m 1) (omega : ℝ) : Prop :=
  NuExpansionTarget m α nu ∧ PsiH1Target m Psi cst ∧ TransverseGapTarget lam2 nu ∧
    DRTarget m Psi omega

end RobinCaps.ThinDomain


