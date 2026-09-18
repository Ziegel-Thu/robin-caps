import RobinCaps.ThinDomain.Slice
import RobinCaps.ThinDomain.BulkMass
import RobinCaps.ThinDomain.Tensor

/-!
# The exact bulk separation of the thin-domain energy

This file formalizes `eq:exact-separation`, `eq:T-bound` and `eq:bulk-mass` of `sec:transverse`
in the manuscript `reference/robin_endcaps_corrected_en.tex` (lines 526-556), on the **bulk
cylinder** `Ω = I × B` with `I = (a,b)` and `B = B_m(R)`, i.e. on `bulkCyl a b m R`.

## The setting

* `u : H1P (bulkCyl a b m R)` is the product-space weak-`H¹` model of
  `RobinCaps/ThinDomain/H1P.lean` (axial and transverse derivatives kept separate, because
  `CapSpace m` carries the sup norm);
* `gs : TransverseGroundState m α R bd` is the transverse ground state *as data*
  (`RobinCaps/ThinDomain/GroundState.lean`): the eigenvalue `gs.nu`, the weak eigen-identity
  `gs.weak_eq`, and the spectral gap `gs.gap`, together with the abstract lateral boundary form
  `bd` (intended: `bd v w = ∫_{∂B_m(R)} (Tr v)(Tr w)`);
* the lateral Robin term of the bulk energy is built **slice-wise** from `bd`:
  `bdCyl bd u v = ∫_I bd (u(x,·)) (v(x,·)) dx`, and
  `EB α bd u = dirichletP u + α * bdCyl bd u u`.

## Contents

1. `IsGoodSlice`, `slice`, `ae_isGoodSlice` — the transverse slice `u(x,·)` as an element of
   `TransH1 m R = H¹(B_m(R))`, defined for a.e. `x` (`sliceACL_transverse` of `Slice.lean`).
2. `massP_eq_integral_NB_slice`, `dirichletP_eq_axial_add_slice` — Fubini: the bulk mass and the
   transverse part of the bulk Dirichlet energy are the axial integrals of the corresponding
   slice forms.
3. `bdCyl`, `EB`, `BdSliceable`, `abs_bilin_le_sqrt_mul_sqrt` — the lateral boundary form and
   the bulk energy.
4. `hasWeakGradP_tensorACW`, `H1P.tensorACW` — the rank-one tensor `F ⊗ ψ` for an axial factor `F`
   that is only `H¹(I)` (a weak derivative, not `C¹` as in `RobinCaps/ThinDomain/Tensor.lean`).
5. `hasWeakDeriv_axialCoeff_slice` — `F(x) = ⟪u(x,·),ψ⟫` has `G(x) = ⟪∂ₓu(x,·),ψ⟫` as a
   one-dimensional weak derivative.
6. `axialProfile`, `axialProfileDeriv`, `bulkTensor`, `bulkRemainder`, `bulk_mass_split`,
   `axialDirichletP_bulk_split`, `ae_slice_bulkRemainder` — the decomposition
   `u = F ⊗ ψ_R + w` of `eq:bulk-projection`.
7. `bulk_exact_separation` (`eq:exact-separation`), `bulk_gap_bound` (`eq:T-bound`),
   `bulk_mass_split` (`eq:bulk-mass`), `bulk_separation` (the bulk restriction of
   `eq:global-energy-lower`), `exists_h1_axialProfile` (`F ∈ H¹(I_R)`).

## What is assumed and what is proved

Everything is **proved**, with the single exception of `BdSliceable`: for an *abstract* bilinear
form `bd` there is no reason for `x ↦ bd (slice u x) (slice v x)` to be measurable, let alone
integrable, so this is recorded as an explicit hypothesis structure and is threaded through the
main theorems.  For the concrete trace-based `bd` it is a Fubini statement about the surface
measure of the lateral boundary and must be verified separately (see
`RobinCaps/ThinDomain/Boundary.lean` for the boundary measure).  The Cauchy-Schwarz bound
`|bd u v| ≤ √(bd u u)·√(bd v v)` is *not* assumed: it is proved from symmetry and nonnegativity
(`abs_bilin_le_sqrt_mul_sqrt`).

No `sorry`, `admit`, `axiom` or `native_decide` occurs in this file.

## A remark on imports

`RobinCaps/ThinDomain/Slice.lean` and `RobinCaps/ThinDomain/AxialCoeff.lean` both declare
`RobinCaps.ThinDomain.prodTest` and therefore cannot be imported together.  This file needs
`sliceACL_transverse` (only in `Slice.lean`), so `AxialCoeff.lean` is not available; its
`hasWeakDeriv_axialCoeff` is reproved here as `hasWeakDeriv_axialCoeff_slice`, by a shorter
route (Fubini plus the *axial* ACL property `sliceACL_axial`).
-/
noncomputable section

namespace RobinCaps.ThinDomain

open MeasureTheory Set RobinCaps.Sobolev

open scoped ENNReal InnerProductSpace ContDiff

variable {m : ℕ} {a b R α : ℝ}

/-! ## Part 0. Subtraction in the two Sobolev models -/

theorem H1P.sub_eq {Ω : Set (CapSpace m)} (u v : H1P Ω) : u - v = u + (-1 : ℝ) • v := by
  rw [neg_one_smul, ← sub_eq_add_neg]

theorem H1P.sub_toFun_be {Ω : Set (CapSpace m)} (u v : H1P Ω) :
    (u - v).toFun = fun p => u.toFun p - v.toFun p := by
  rw [H1P.sub_eq]; funext p
  simp only [H1P.add_toFun, H1P.smul_toFun, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  ring

theorem H1P.sub_gx {Ω : Set (CapSpace m)} (u v : H1P Ω) :
    (u - v).gx = fun p => u.gx p - v.gx p := by
  rw [H1P.sub_eq]; funext p
  simp only [H1P.add_gx, H1P.smul_gx, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  ring

theorem H1P.sub_gz {Ω : Set (CapSpace m)} (u v : H1P Ω) :
    (u - v).gz = fun p => u.gz p - v.gz p := by
  rw [H1P.sub_eq, H1P.add_gz, H1P.smul_gz]
  funext p
  simp only [Pi.add_apply, neg_smul, one_smul, Pi.neg_apply]
  abel

theorem weakH1_sub_eq {n : ℕ} {D : Set (EuclideanSpace ℝ (Fin n))} (u v : Weak.H1 D) :
    u - v = u + (-1 : ℝ) • v := by
  rw [neg_one_smul, ← sub_eq_add_neg]

theorem weakH1_sub_toFun {n : ℕ} {D : Set (EuclideanSpace ℝ (Fin n))} (u v : Weak.H1 D) :
    (u - v).toFun = fun z => u.toFun z - v.toFun z := by
  rw [weakH1_sub_eq]; funext z
  simp only [Weak.H1.add_toFun, Weak.H1.smul_toFun, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  ring

theorem weakH1_sub_grad {n : ℕ} {D : Set (EuclideanSpace ℝ (Fin n))} (u v : Weak.H1 D) :
    (u - v).grad = fun z => u.grad z - v.grad z := by
  rw [weakH1_sub_eq, Weak.H1.add_grad, Weak.H1.smul_grad]
  funext z
  simp only [Pi.add_apply, neg_smul, one_smul, Pi.neg_apply]
  abel

/-! ## Part 1. Transverse slices as elements of `TransH1 m R` -/

/-- The **good set** of axial coordinates: those `x` for which the transverse slice of `u`
is a genuine element of `H¹(B_m(R))`, with the slice of `∇_z u` as its weak gradient. -/
def IsGoodSlice (u : H1P (bulkCyl a b m R)) (x : ℝ) : Prop :=
  Weak.HasWeakGrad (transverseBall m R) (fun z => u.toFun (x, z)) (fun z => u.gz (x, z)) ∧
    MemLp (fun z => u.toFun (x, z)) 2 (volume.restrict (transverseBall m R)) ∧
    MemLp (fun z => u.gz (x, z)) 2 (volume.restrict (transverseBall m R))

open Classical in
/-- **The transverse slice of `u` at `x`**, as an element of `TransH1 m R = H¹(B_m(R))`.
Off the good set (a null set, `ae_isGoodSlice`) the slice is defined to be `0`. -/
def slice (u : H1P (bulkCyl a b m R)) (x : ℝ) : TransH1 m R :=
  if h : IsGoodSlice u x then
    { toFun := fun z => u.toFun (x, z)
      grad := fun z => u.gz (x, z)
      memL2 := h.2.1
      grad_memL2 := h.2.2
      hasWeakGrad := h.1 }
  else 0

theorem slice_toFun {u : H1P (bulkCyl a b m R)} {x : ℝ} (h : IsGoodSlice u x) :
    (slice u x).toFun = fun z => u.toFun (x, z) := by
  simp only [slice, dif_pos h]

theorem slice_grad {u : H1P (bulkCyl a b m R)} {x : ℝ} (h : IsGoodSlice u x) :
    (slice u x).grad = fun z => u.gz (x, z) := by
  simp only [slice, dif_pos h]

/-- The vector-valued analogue of `ae_memLp_transverseSlice`. -/
theorem ae_memLp_transverseSlice_vec {B : Set (EuclideanSpace ℝ (Fin m))}
    {f : CapSpace m → EuclideanSpace ℝ (Fin m)}
    (hf : MemLp f 2 (volume.restrict (Ioo a b ×ˢ B))) :
    ∀ᵐ x ∂(volume.restrict (Ioo a b)), MemLp (fun z => f (x, z)) 2 (volume.restrict B) := by
  have hsq : Integrable (fun p => ‖f p‖ ^ 2) (volume.restrict (Ioo a b ×ˢ B)) :=
    (memLp_two_iff_integrable_sq_norm hf.aestronglyMeasurable).1 hf
  have hmeas : AEStronglyMeasurable f (volume.restrict (Ioo a b ×ˢ B)) := hf.aestronglyMeasurable
  rw [restrict_prodDomain] at hsq hmeas
  filter_upwards [hsq.prod_right_ae, hmeas.prodMk_left] with x h1 h2
  exact (memLp_two_iff_integrable_sq_norm h2).2 h1

/-- **Almost every axial coordinate is good**: `sliceACL_transverse` (the ACL property in the
transverse direction) together with a.e. slice square integrability. -/
theorem ae_isGoodSlice (u : H1P (bulkCyl a b m R)) :
    ∀ᵐ x ∂(volume.restrict (Ioo a b)), IsGoodSlice u x := by
  have h1 : SliceACLTransverse a b (transverseBall m R) u := sliceACL_transverse u
  have h2 := ae_memLp_transverseSlice (a := a) (b := b) (B := transverseBall m R) u.memL2
  have h3 := ae_memLp_transverseSlice_vec (a := a) (b := b) (B := transverseBall m R) u.gz_memL2
  filter_upwards [h1, h2, h3] with x hx1 hx2 hx3
  exact ⟨hx1, hx2, hx3⟩


/-! ## Part 2. Fubini: the bulk forms as axial integrals of the slice forms -/

/-- Fubini on the bulk cylinder. -/
theorem integral_bulk_eq {f : CapSpace m → ℝ}
    (hf : Integrable f (volume.restrict (bulkCyl a b m R))) :
    ∫ p in bulkCyl a b m R, f p
      = ∫ x in Ioo a b, ∫ z in transverseBall m R, f (x, z) := by
  rw [volume_restrict_bulkCyl] at hf ⊢
  exact integral_prod f hf

/-- The inner (transverse) integral is integrable in the axial variable. -/
theorem integrableOn_inner_bulk {f : CapSpace m → ℝ}
    (hf : Integrable f (volume.restrict (bulkCyl a b m R))) :
    IntegrableOn (fun x => ∫ z in transverseBall m R, f (x, z)) (Ioo a b) := by
  rw [volume_restrict_bulkCyl] at hf
  exact hf.integral_prod_left

theorem integrable_sq_toFun (u : H1P (bulkCyl a b m R)) :
    Integrable (fun p => u.toFun p ^ 2) (volume.restrict (bulkCyl a b m R)) :=
  u.memL2.integrable_sq

theorem integrable_sq_gx (u : H1P (bulkCyl a b m R)) :
    Integrable (fun p => u.gx p ^ 2) (volume.restrict (bulkCyl a b m R)) :=
  u.gx_memL2.integrable_sq

theorem integrable_normSq_gz (u : H1P (bulkCyl a b m R)) :
    Integrable (fun p => ‖u.gz p‖ ^ 2) (volume.restrict (bulkCyl a b m R)) :=
  (memLp_two_iff_integrable_sq_norm u.gz_memL2.aestronglyMeasurable).1 u.gz_memL2

/-- The transverse mass of the slice is the inner integral of `u²`. -/
theorem ae_NB_slice (u : H1P (bulkCyl a b m R)) :
    (fun x => NB (slice u x)) =ᵐ[volume.restrict (Ioo a b)]
      fun x => ∫ z in transverseBall m R, u.toFun (x, z) ^ 2 := by
  filter_upwards [ae_isGoodSlice u] with x hx
  simp only [NB, Weak.mass, slice_toFun hx]

/-- The transverse Dirichlet energy of the slice is the inner integral of `‖∇_z u‖²`. -/
theorem ae_dirichlet_slice (u : H1P (bulkCyl a b m R)) :
    (fun x => Weak.dirichlet (slice u x)) =ᵐ[volume.restrict (Ioo a b)]
      fun x => ∫ z in transverseBall m R, ‖u.gz (x, z)‖ ^ 2 := by
  filter_upwards [ae_isGoodSlice u] with x hx
  simp only [Weak.dirichlet, slice_grad hx]

theorem integrableOn_NB_slice (u : H1P (bulkCyl a b m R)) :
    IntegrableOn (fun x => NB (slice u x)) (Ioo a b) :=
  (integrableOn_inner_bulk (integrable_sq_toFun u)).congr_fun_ae (ae_NB_slice u).symm

theorem integrableOn_dirichlet_slice (u : H1P (bulkCyl a b m R)) :
    IntegrableOn (fun x => Weak.dirichlet (slice u x)) (Ioo a b) :=
  (integrableOn_inner_bulk (integrable_normSq_gz u)).congr_fun_ae (ae_dirichlet_slice u).symm

/-- **The mass is the axial integral of the slice masses.** -/
theorem massP_eq_integral_NB_slice (u : H1P (bulkCyl a b m R)) :
    massP u = ∫ x in Ioo a b, NB (slice u x) := by
  rw [massP, integral_bulk_eq (integrable_sq_toFun u)]
  exact (integral_congr_ae (ae_NB_slice u)).symm

/-- **The transverse Dirichlet energy is the axial integral of the slice Dirichlet energies.** -/
theorem integral_normSq_gz_eq_integral_dirichlet_slice (u : H1P (bulkCyl a b m R)) :
    ∫ p in bulkCyl a b m R, ‖u.gz p‖ ^ 2
      = ∫ x in Ioo a b, Weak.dirichlet (slice u x) := by
  rw [integral_bulk_eq (integrable_normSq_gz u)]
  exact (integral_congr_ae (ae_dirichlet_slice u)).symm

/-- The **axial** part of the bulk Dirichlet energy, `∫_Ω (∂ₓu)²`. -/
def axialDirichletP (u : H1P (bulkCyl a b m R)) : ℝ := ∫ p in bulkCyl a b m R, u.gx p ^ 2

theorem axialDirichletP_nonneg (u : H1P (bulkCyl a b m R)) : 0 ≤ axialDirichletP u :=
  integral_nonneg fun _ => sq_nonneg _

/-- **The splitting of the bulk Dirichlet energy into axial and transverse parts.** -/
theorem dirichletP_eq_axial_add_slice (u : H1P (bulkCyl a b m R)) :
    dirichletP u = axialDirichletP u + ∫ x in Ioo a b, Weak.dirichlet (slice u x) := by
  rw [dirichletP, integral_add (integrable_sq_gx u) (integrable_normSq_gz u),
    ← integral_normSq_gz_eq_integral_dirichlet_slice u, axialDirichletP]


/-! ## Part 3. The lateral boundary form and the bulk energy

The lateral Robin term `α ∫_{I × ∂B_m(R)} |u|²` of `E_bulk` (manuscript line 531) is defined
**slice-wise** from the transverse boundary form `bd` of `RobinCaps/ThinDomain/GroundState.lean`
(which is a parameter there, intended to be `bd v w = ∫_{∂B_m(R)} (Tr v)(Tr w) dℋ^{m-1}`):

`bdCyl bd u v = ∫_I bd (u(x,·)) (v(x,·)) dx`.

For an *abstract* `bd` nothing forces `x ↦ bd (slice u x) (slice v x)` to be measurable, let
alone integrable; this is recorded as the hypothesis structure `BdSliceable`.  For the concrete
trace-based `bd` it has to be verified separately (it is a Fubini statement for the surface
measure of the lateral boundary; see `RobinCaps/ThinDomain/Boundary.lean`). -/

/-- **The lateral boundary form of the bulk cylinder**, defined slice-wise. -/
def bdCyl (bd : TransH1 m R →ₗ[ℝ] TransH1 m R →ₗ[ℝ] ℝ)
    (u v : H1P (bulkCyl a b m R)) : ℝ :=
  ∫ x in Ioo a b, bd (slice u x) (slice v x)

/-- **The bulk energy** `E_bulk[u] = ∫_Ω ((∂ₓu)² + ‖∇_z u‖²) + α ∫_{lat} |u|²`
(manuscript `eq:exact-separation`, line 531). -/
def EB (α : ℝ) (bd : TransH1 m R →ₗ[ℝ] TransH1 m R →ₗ[ℝ] ℝ)
    (u : H1P (bulkCyl a b m R)) : ℝ :=
  dirichletP u + α * bdCyl bd u u

/-- **Sliceability of the boundary form**: the only analytic input about `bd` that the bulk
separation needs.  It is *not* automatic for an abstract bilinear form and is therefore taken
as a hypothesis; for the concrete trace form it must be proved separately. -/
structure BdSliceable (a b : ℝ) (bd : TransH1 m R →ₗ[ℝ] TransH1 m R →ₗ[ℝ] ℝ) : Prop where
  /-- The slice-wise boundary pairing of any two bulk elements is integrable on `I`. -/
  integrableOn : ∀ u v : H1P (bulkCyl a b m R),
    IntegrableOn (fun x => bd (slice u x) (slice v x)) (Ioo a b)

/-! ### Cauchy–Schwarz for a symmetric nonnegative bilinear form

This is the estimate announced for `bd`; it follows from symmetry and nonnegativity alone,
so it is *not* a field of `BdSliceable`. -/

/-- **Cauchy–Schwarz** for a symmetric positive semidefinite bilinear form. -/
theorem abs_bilin_le_sqrt_mul_sqrt {W : Type*} [AddCommGroup W] [Module ℝ W]
    (Bf : W →ₗ[ℝ] W →ₗ[ℝ] ℝ) (hsymm : ∀ x y : W, Bf x y = Bf y x)
    (hnn : ∀ x : W, 0 ≤ Bf x x) (u v : W) :
    |Bf u v| ≤ Real.sqrt (Bf u u) * Real.sqrt (Bf v v) := by
  have key : ∀ t : ℝ, 0 ≤ Bf u u + 2 * t * Bf u v + t ^ 2 * Bf v v := by
    intro t
    have h := hnn (u + t • v)
    have e : Bf (u + t • v) (u + t • v) = Bf u u + 2 * t * Bf u v + t ^ 2 * Bf v v := by
      simp only [map_add, map_smul, LinearMap.add_apply, LinearMap.smul_apply, smul_eq_mul]
      rw [hsymm v u]; ring
    rw [e] at h
    exact h
  have hsq : Bf u v ^ 2 ≤ Bf u u * Bf v v := by
    rcases eq_or_lt_of_le (hnn v) with hv | hv
    · have hzero : Bf u v = 0 := by
        by_contra hne
        have h1 := key (-(Bf u u + 1) / (2 * Bf u v))
        have h2 : 2 * (-(Bf u u + 1) / (2 * Bf u v)) * Bf u v = -(Bf u u + 1) := by
          field_simp
        rw [← hv, h2] at h1
        nlinarith [h1]
      rw [hzero, ← hv]
      simp
    · have hne : Bf v v ≠ 0 := ne_of_gt hv
      have h1 := key (-(Bf u v) / Bf v v)
      have h3 : 0 ≤ (Bf u u + 2 * (-(Bf u v) / Bf v v) * Bf u v
          + (-(Bf u v) / Bf v v) ^ 2 * Bf v v) * Bf v v := mul_nonneg h1 hv.le
      have h4 : (Bf u u + 2 * (-(Bf u v) / Bf v v) * Bf u v
          + (-(Bf u v) / Bf v v) ^ 2 * Bf v v) * Bf v v
            = Bf u u * Bf v v - Bf u v ^ 2 := by
        field_simp; ring
      rw [h4] at h3
      linarith
  calc |Bf u v| = Real.sqrt (Bf u v ^ 2) := (Real.sqrt_sq_eq_abs _).symm
    _ ≤ Real.sqrt (Bf u u * Bf v v) := Real.sqrt_le_sqrt hsq
    _ = Real.sqrt (Bf u u) * Real.sqrt (Bf v v) := Real.sqrt_mul (hnn u) _


/-! ## Part 4. The rank-one tensor `F ⊗ ψ` for a merely `H¹` axial factor

`RobinCaps/ThinDomain/Tensor.lean` builds `F ⊗ ψ ∈ H¹(Ω)` for `F` of class `C¹`.  The axial
coefficient `F(x) = ⟪u(x,·), ψ⟫` of an arbitrary `u ∈ H¹(Ω)` is *not* `C¹`; it is only `H¹(I)`.
The construction below therefore takes as input a pair `(F, G)` with `G` a **weak** derivative
of `F` on `(a,b)`, in the sense of `RobinCaps/Sobolev/DuBoisReymond.lean`. -/

/-- `L²(Ω)` for a scalar tensor product with an `L²(I)` axial factor. -/
theorem memLp_two_tensorL2 {f : ℝ → ℝ} (hf : MemLp f 2 (volume.restrict (Ioo a b)))
    {w : EuclideanSpace ℝ (Fin m) → ℝ}
    (hw : MemLp w 2 (volume.restrict (transverseBall m R))) :
    MemLp (fun p : CapSpace m => f p.1 * w p.2) 2 (volume.restrict (bulkCyl a b m R)) := by
  rw [volume_restrict_bulkCyl]
  have hm : AEStronglyMeasurable (fun p : CapSpace m => f p.1 * w p.2)
      (((volume : Measure ℝ).restrict (Ioo a b)).prod
        ((volume : Measure (EuclideanSpace ℝ (Fin m))).restrict (transverseBall m R))) :=
    (hf.aestronglyMeasurable.comp_fst).mul (hw.aestronglyMeasurable.comp_snd)
  rw [memLp_two_iff_integrable_sq hm]
  have hprod := hf.integrable_sq.mul_prod hw.integrable_sq
  refine hprod.congr (Filter.Eventually.of_forall fun p => ?_)
  simp [mul_pow]

/-- `L²(Ω;ℝᵐ)` for a vector tensor product with an `L²(I)` axial factor. -/
theorem memLp_two_tensorL2_vec {f : ℝ → ℝ} (hf : MemLp f 2 (volume.restrict (Ioo a b)))
    {w : EuclideanSpace ℝ (Fin m) → EuclideanSpace ℝ (Fin m)}
    (hw : MemLp w 2 (volume.restrict (transverseBall m R))) :
    MemLp (fun p : CapSpace m => f p.1 • w p.2) 2 (volume.restrict (bulkCyl a b m R)) := by
  rw [volume_restrict_bulkCyl]
  have hm : AEStronglyMeasurable (fun p : CapSpace m => f p.1 • w p.2)
      (((volume : Measure ℝ).restrict (Ioo a b)).prod
        ((volume : Measure (EuclideanSpace ℝ (Fin m))).restrict (transverseBall m R))) :=
    (hf.aestronglyMeasurable.comp_fst).smul (hw.aestronglyMeasurable.comp_snd)
  rw [memLp_two_iff_integrable_sq_norm hm]
  have hwn : Integrable (fun z => ‖w z‖ ^ 2)
      (volume.restrict (transverseBall m R)) :=
    (memLp_two_iff_integrable_sq_norm hw.aestronglyMeasurable).1 hw
  have hprod := hf.integrable_sq.mul_prod hwn
  refine hprod.congr (Filter.Eventually.of_forall fun p => ?_)
  simp only [norm_smul, mul_pow, Real.norm_eq_abs, sq_abs]

/-- **The weak gradient of `F ⊗ ψ` when `F` has only a weak derivative.**

`∂ₓ(F ⊗ ψ) = G ⊗ ψ` and `∇_z(F ⊗ ψ) = F ⊗ ∇ψ`, where `G` is a weak derivative of `F` on
`(a,b)`.  The proof is the one of `hasWeakGradP_tensor` with the classical one-dimensional
integration by parts replaced by the definition of `HasWeakDeriv`. -/
theorem hasWeakGradP_tensorACW {F G : ℝ → ℝ}
    (hF : MemLp F 2 (volume.restrict (Ioo a b)))
    (hG : MemLp G 2 (volume.restrict (Ioo a b)))
    (hFG : Sobolev.HasWeakDeriv a b F G) (ψ : TransH1 m R) :
    HasWeakGradP (bulkCyl a b m R) (tensorFun F ψ)
      (fun p => G p.1 * ψ.toFun p.2) (fun p => F p.1 • ψ.grad p.2) := by
  have hmeas := volume_restrict_bulkCyl (a := a) (b := b) (m := m) (R := R)
  have hu : MemLp (tensorFun F ψ) 2 (volume.restrict (bulkCyl a b m R)) :=
    memLp_two_tensorL2 hF ψ.memL2
  have hgx : MemLp (fun p : CapSpace m => G p.1 * ψ.toFun p.2) 2
      (volume.restrict (bulkCyl a b m R)) := memLp_two_tensorL2 hG ψ.memL2
  have hgz : MemLp (fun p : CapSpace m => F p.1 • ψ.grad p.2) 2
      (volume.restrict (bulkCyl a b m R)) := memLp_two_tensorL2_vec hF ψ.grad_memL2
  intro φ hφ hφc hφs
  have hφ1 : ContDiff ℝ 1 φ := hφ.of_le (by simp)
  constructor
  · -- axial identity
    have hintL : Integrable (fun p : CapSpace m => tensorFun F ψ p *
        fderiv ℝ φ p ((1 : ℝ), (0 : EuclideanSpace ℝ (Fin m))))
        (volume.restrict (bulkCyl a b m R)) :=
      integrable_mul_dirDeriv hu hφ hφc _
    have hintR : Integrable
        (fun p : CapSpace m => (G p.1 * ψ.toFun p.2) * φ p)
        (volume.restrict (bulkCyl a b m R)) :=
      integrable_gx_mul hgx hφ hφc
    rw [hmeas] at hintL hintR
    have key : ∀ z : EuclideanSpace ℝ (Fin m),
        (∫ x in Ioo a b, tensorFun F ψ (x, z) *
            fderiv ℝ φ (x, z) ((1 : ℝ), (0 : EuclideanSpace ℝ (Fin m))))
          = -∫ x in Ioo a b, (G x * ψ.toFun z) * φ (x, z) := by
      intro z
      have hgC : ContDiff ℝ ∞ fun t : ℝ => φ (t, z) :=
        hφ.comp (contDiff_id.prodMk contDiff_const)
      have hgc : HasCompactSupport fun t : ℝ => φ (t, z) := hasCompactSupport_sliceFst hφc z
      have hgs : tsupport (fun t : ℝ => φ (t, z)) ⊆ Ioo a b :=
        tsupport_sliceFst_subset_interval hφs z
      have h1 : (∫ x in Ioo a b, tensorFun F ψ (x, z) *
            fderiv ℝ φ (x, z) ((1 : ℝ), (0 : EuclideanSpace ℝ (Fin m))))
          = ψ.toFun z * ∫ x in Ioo a b, F x * deriv (fun t : ℝ => φ (t, z)) x := by
        rw [← integral_const_mul]
        refine integral_congr_ae (.of_forall fun x => ?_)
        simp only [tensorFun_apply, deriv_sliceFst hφ1 x z]
        ring
      have h2 : (∫ x in Ioo a b, (G x * ψ.toFun z) * φ (x, z))
          = ψ.toFun z * ∫ x in Ioo a b, G x * φ (x, z) := by
        rw [← integral_const_mul]
        refine integral_congr_ae (.of_forall fun x => ?_)
        ring
      have hibp : (∫ x in Ioo a b, F x * deriv (fun t : ℝ => φ (t, z)) x)
          = -∫ x in Ioo a b, G x * φ (x, z) :=
        hFG (fun t : ℝ => φ (t, z)) hgC hgc hgs
      rw [h1, h2, hibp]
      ring
    calc (∫ p in bulkCyl a b m R, tensorFun F ψ p *
            fderiv ℝ φ p ((1 : ℝ), (0 : EuclideanSpace ℝ (Fin m))))
        = ∫ z in transverseBall m R, ∫ x in Ioo a b, tensorFun F ψ (x, z) *
            fderiv ℝ φ (x, z) ((1 : ℝ), (0 : EuclideanSpace ℝ (Fin m))) := by
          rw [hmeas]; exact integral_prod_symm _ hintL
      _ = ∫ z in transverseBall m R,
            -∫ x in Ioo a b, (G x * ψ.toFun z) * φ (x, z) :=
          integral_congr_ae (.of_forall key)
      _ = -∫ z in transverseBall m R, ∫ x in Ioo a b,
            (G x * ψ.toFun z) * φ (x, z) := integral_neg _
      _ = -∫ p in bulkCyl a b m R, (G p.1 * ψ.toFun p.2) * φ p := by
          rw [hmeas, integral_prod_symm _ hintR]
  · -- transverse identities
    intro i
    have hintL : Integrable (fun p : CapSpace m => tensorFun F ψ p *
        fderiv ℝ φ p ((0 : ℝ), EuclideanSpace.single i (1 : ℝ)))
        (volume.restrict (bulkCyl a b m R)) :=
      integrable_mul_dirDeriv hu hφ hφc _
    have hintR : Integrable
        (fun p : CapSpace m => (F p.1 • ψ.grad p.2) i * φ p)
        (volume.restrict (bulkCyl a b m R)) :=
      integrable_compP_mul hgz hφ hφc i
    rw [hmeas] at hintL hintR
    have key : ∀ x : ℝ,
        (∫ z in transverseBall m R, tensorFun F ψ (x, z) *
            fderiv ℝ φ (x, z) ((0 : ℝ), EuclideanSpace.single i (1 : ℝ)))
          = -∫ z in transverseBall m R, (F x • ψ.grad z) i * φ (x, z) := by
      intro x
      have hgC : ContDiff ℝ ∞ fun w : EuclideanSpace ℝ (Fin m) => φ (x, w) :=
        hφ.comp (contDiff_const.prodMk contDiff_id)
      have hgc : HasCompactSupport fun w : EuclideanSpace ℝ (Fin m) => φ (x, w) :=
        hasCompactSupport_sliceSnd hφc x
      have hgs : tsupport (fun w : EuclideanSpace ℝ (Fin m) => φ (x, w)) ⊆ transverseBall m R :=
        tsupport_sliceSnd_subset_ball hφs x
      have hw : (∫ z in transverseBall m R, ψ.toFun z *
            fderiv ℝ (fun w : EuclideanSpace ℝ (Fin m) => φ (x, w)) z
              (EuclideanSpace.single i 1))
          = -∫ z in transverseBall m R, ψ.grad z i * φ (x, z) :=
        ψ.hasWeakGrad (fun w : EuclideanSpace ℝ (Fin m) => φ (x, w)) hgC hgc hgs i
      have h1 : (∫ z in transverseBall m R, tensorFun F ψ (x, z) *
            fderiv ℝ φ (x, z) ((0 : ℝ), EuclideanSpace.single i (1 : ℝ)))
          = F x * ∫ z in transverseBall m R, ψ.toFun z *
              fderiv ℝ (fun w : EuclideanSpace ℝ (Fin m) => φ (x, w)) z
                (EuclideanSpace.single i 1) := by
        rw [← integral_const_mul]
        refine integral_congr_ae (.of_forall fun z => ?_)
        simp only [tensorFun_apply, fderiv_sliceSnd hφ1 x z]
        ring
      have h2 : (∫ z in transverseBall m R, (F x • ψ.grad z) i * φ (x, z))
          = F x * ∫ z in transverseBall m R, ψ.grad z i * φ (x, z) := by
        rw [← integral_const_mul]
        refine integral_congr_ae (.of_forall fun z => ?_)
        simp only [PiLp.smul_apply, smul_eq_mul]
        ring
      rw [h1, h2, hw, mul_neg]
    calc (∫ p in bulkCyl a b m R, tensorFun F ψ p *
            fderiv ℝ φ p ((0 : ℝ), EuclideanSpace.single i (1 : ℝ)))
        = ∫ x in Ioo a b, ∫ z in transverseBall m R, tensorFun F ψ (x, z) *
            fderiv ℝ φ (x, z) ((0 : ℝ), EuclideanSpace.single i (1 : ℝ)) := by
          rw [hmeas]; exact integral_prod _ hintL
      _ = ∫ x in Ioo a b,
            -∫ z in transverseBall m R, (F x • ψ.grad z) i * φ (x, z) :=
          integral_congr_ae (.of_forall key)
      _ = -∫ x in Ioo a b, ∫ z in transverseBall m R,
            (F x • ψ.grad z) i * φ (x, z) := integral_neg _
      _ = -∫ p in bulkCyl a b m R, (F p.1 • ψ.grad p.2) i * φ p := by
          rw [hmeas, integral_prod _ hintR]

/-- **The rank-one tensor `F ⊗ ψ` as an element of `H¹(Ω)`**, for `F ∈ H¹(I)` in the weak sense. -/
def H1P.tensorACW {F G : ℝ → ℝ} (hF : MemLp F 2 (volume.restrict (Ioo a b)))
    (hG : MemLp G 2 (volume.restrict (Ioo a b)))
    (hFG : Sobolev.HasWeakDeriv a b F G) (ψ : TransH1 m R) : H1P (bulkCyl a b m R) where
  toFun := tensorFun F ψ
  gx := fun p => G p.1 * ψ.toFun p.2
  gz := fun p => F p.1 • ψ.grad p.2
  memL2 := memLp_two_tensorL2 hF ψ.memL2
  gx_memL2 := memLp_two_tensorL2 hG ψ.memL2
  gz_memL2 := memLp_two_tensorL2_vec hF ψ.grad_memL2
  hasWeakGrad := hasWeakGradP_tensorACW hF hG hFG ψ

@[simp] theorem H1P.tensorACW_toFun {F G : ℝ → ℝ} (hF : MemLp F 2 (volume.restrict (Ioo a b)))
    (hG : MemLp G 2 (volume.restrict (Ioo a b)))
    (hFG : Sobolev.HasWeakDeriv a b F G) (ψ : TransH1 m R) :
    (H1P.tensorACW hF hG hFG ψ).toFun = fun p => F p.1 * ψ.toFun p.2 := rfl

@[simp] theorem H1P.tensorAC_gx {F G : ℝ → ℝ} (hF : MemLp F 2 (volume.restrict (Ioo a b)))
    (hG : MemLp G 2 (volume.restrict (Ioo a b)))
    (hFG : Sobolev.HasWeakDeriv a b F G) (ψ : TransH1 m R) :
    (H1P.tensorACW hF hG hFG ψ).gx = fun p => G p.1 * ψ.toFun p.2 := rfl

@[simp] theorem H1P.tensorAC_gz {F G : ℝ → ℝ} (hF : MemLp F 2 (volume.restrict (Ioo a b)))
    (hG : MemLp G 2 (volume.restrict (Ioo a b)))
    (hFG : Sobolev.HasWeakDeriv a b F G) (ψ : TransH1 m R) :
    (H1P.tensorACW hF hG hFG ψ).gz = fun p => F p.1 • ψ.grad p.2 := rfl


/-! ## Part 5. The axial coefficient and its weak derivative

`F(x) = ⟪u(x,·), ψ⟫_{L²(B)}` (manuscript `eq:bulk-projection`, line 528) has
`G(x) = ⟪∂ₓu(x,·), ψ⟫_{L²(B)}` as a one-dimensional weak derivative.  (The same statement is
proved by a different route in `RobinCaps/ThinDomain/AxialCoeff.lean`, which unfortunately
cannot be imported here at the same time as `RobinCaps/ThinDomain/Slice.lean`: the two files
both declare `RobinCaps.ThinDomain.prodTest`.  The proof below uses the axial ACL property
`sliceACL_axial` of `Slice.lean` and is short.) -/

theorem isOpen_transverseBall_be : IsOpen (transverseBall m R) := Metric.isOpen_ball

/-- Fubini for the pairing of the axial coefficient against a continuous axial weight. -/
theorem integral_axialCoeff_mul_continuous {v : CapSpace m → ℝ}
    (hv : MemLp v 2 (volume.restrict (bulkCyl a b m R)))
    {ψ : EuclideanSpace ℝ (Fin m) → ℝ}
    (hψ : MemLp ψ 2 (volume.restrict (transverseBall m R)))
    {c : ℝ → ℝ} (hc : Continuous c) :
    ∫ x in Ioo a b, axialCoeff (transverseBall m R) v ψ x * c x
      = ∫ z in transverseBall m R, ψ z * ∫ x in Ioo a b, v (x, z) * c x := by
  have hk : Integrable (fun p : CapSpace m => v p * (c p.1 * ψ p.2))
      (volume.restrict (bulkCyl a b m R)) :=
    hv.integrable_mul (memLp_two_tensor hc hψ)
  have hstep1 : ∫ x in Ioo a b, axialCoeff (transverseBall m R) v ψ x * c x
      = ∫ x in Ioo a b, ∫ z in transverseBall m R, v (x, z) * (c x * ψ z) := by
    refine integral_congr_ae (.of_forall fun x => ?_)
    simp only [axialCoeff]
    rw [← integral_mul_const]
    exact integral_congr_ae (.of_forall fun z => by ring)
  have hstep2 : ∫ x in Ioo a b, ∫ z in transverseBall m R, v (x, z) * (c x * ψ z)
      = ∫ p in bulkCyl a b m R, v p * (c p.1 * ψ p.2) :=
    (integral_bulk_eq hk).symm
  have hstep3 : ∫ p in bulkCyl a b m R, v p * (c p.1 * ψ p.2)
      = ∫ z in transverseBall m R, ∫ x in Ioo a b, v (x, z) * (c x * ψ z) := by
    rw [volume_restrict_bulkCyl] at hk ⊢
    exact integral_prod_symm _ hk
  have hstep4 : ∫ z in transverseBall m R, ∫ x in Ioo a b, v (x, z) * (c x * ψ z)
      = ∫ z in transverseBall m R, ψ z * ∫ x in Ioo a b, v (x, z) * c x := by
    refine integral_congr_ae (.of_forall fun z => ?_)
    show (∫ x in Ioo a b, v (x, z) * (c x * ψ z))
        = ψ z * ∫ x in Ioo a b, v (x, z) * c x
    rw [← integral_const_mul]
    exact integral_congr_ae (.of_forall fun x => by ring)
  rw [hstep1, hstep2, hstep3, hstep4]

/-- **The axial coefficient has the axial coefficient of `∂ₓu` as a weak derivative.** -/
theorem hasWeakDeriv_axialCoeff_slice (hab : a < b) (u : H1P (bulkCyl a b m R))
    {ψ : EuclideanSpace ℝ (Fin m) → ℝ}
    (hψ : MemLp ψ 2 (volume.restrict (transverseBall m R))) :
    Sobolev.HasWeakDeriv a b (axialCoeff (transverseBall m R) u.toFun ψ)
      (axialCoeff (transverseBall m R) u.gx ψ) := by
  intro φ hφ hφc hφs
  have hφ'cont : Continuous (deriv φ) := ((contDiff_infty_iff_deriv.1 hφ).2).continuous
  have h1 := integral_axialCoeff_mul_continuous u.memL2 hψ hφ'cont
  have h2 := integral_axialCoeff_mul_continuous u.gx_memL2 hψ hφ.continuous
  have hslice : ∀ᵐ z ∂(volume.restrict (transverseBall m R)),
      ψ z * (∫ x in Ioo a b, u.toFun (x, z) * deriv φ x)
        = -(ψ z * ∫ x in Ioo a b, u.gx (x, z) * φ x) := by
    filter_upwards [sliceACL_axial hab isOpen_transverseBall_be u] with z hz
    rw [hz φ hφ hφc hφs]
    ring
  rw [h1, h2, integral_congr_ae hslice, integral_neg]


/-! ## Part 6. The exact bulk decomposition `u = F ⊗ ψ + w` -/

section Decomposition

variable {bd : TransH1 m R →ₗ[ℝ] TransH1 m R →ₗ[ℝ] ℝ}

theorem volume_Ioo_ne_top' (a b : ℝ) : (volume : Measure ℝ) (Ioo a b) ≠ ⊤ := by
  rw [Real.volume_Ioo]; exact ENNReal.ofReal_ne_top

theorem psi_normalized_integral (gs : TransverseGroundState m α R bd) :
    ∫ z in transverseBall m R, gs.psi.toFun z ^ 2 = 1 := gs.normalized

/-- **The axial profile** `F(x) = ⟪u(x,·), ψ_R⟫_{L²(B_m(R))}` (`eq:bulk-projection`). -/
def axialProfile (gs : TransverseGroundState m α R bd) (u : H1P (bulkCyl a b m R)) : ℝ → ℝ :=
  axialCoeff (transverseBall m R) u.toFun gs.psi.toFun

/-- **The weak derivative of the axial profile**, `F'(x) = ⟪∂ₓu(x,·), ψ_R⟫`. -/
def axialProfileDeriv (gs : TransverseGroundState m α R bd)
    (u : H1P (bulkCyl a b m R)) : ℝ → ℝ :=
  axialCoeff (transverseBall m R) u.gx gs.psi.toFun

theorem memLp_axialProfile (gs : TransverseGroundState m α R bd)
    (u : H1P (bulkCyl a b m R)) :
    MemLp (axialProfile gs u) 2 (volume.restrict (Ioo a b)) :=
  axialCoeff_memL2 (I := Ioo a b) (volume_Ioo_ne_top' a b) u.memL2 gs.psi.memL2
    (psi_normalized_integral gs)

theorem memLp_axialProfileDeriv (gs : TransverseGroundState m α R bd)
    (u : H1P (bulkCyl a b m R)) :
    MemLp (axialProfileDeriv gs u) 2 (volume.restrict (Ioo a b)) :=
  axialCoeff_memL2 (I := Ioo a b) (volume_Ioo_ne_top' a b) u.gx_memL2 gs.psi.memL2
    (psi_normalized_integral gs)

theorem hasWeakDeriv_axialProfile (hab : a < b) (gs : TransverseGroundState m α R bd)
    (u : H1P (bulkCyl a b m R)) :
    Sobolev.HasWeakDeriv a b (axialProfile gs u) (axialProfileDeriv gs u) :=
  hasWeakDeriv_axialCoeff_slice hab u gs.psi.memL2

/-- **The rank-one part `F ⊗ ψ_R`** of the bulk decomposition `eq:bulk-projection`. -/
def bulkTensor (hab : a < b) (gs : TransverseGroundState m α R bd)
    (u : H1P (bulkCyl a b m R)) : H1P (bulkCyl a b m R) :=
  H1P.tensorACW (memLp_axialProfile gs u) (memLp_axialProfileDeriv gs u)
    (hasWeakDeriv_axialProfile hab gs u) gs.psi

/-- **The bulk remainder `w = u - F ⊗ ψ_R`** (`eq:bulk-projection`, manuscript line 528). -/
def bulkRemainder (hab : a < b) (gs : TransverseGroundState m α R bd)
    (u : H1P (bulkCyl a b m R)) : H1P (bulkCyl a b m R) :=
  u - bulkTensor hab gs u

variable {hab : a < b} {gs : TransverseGroundState m α R bd} {u : H1P (bulkCyl a b m R)}

theorem bulkRemainder_toFun :
    (bulkRemainder hab gs u).toFun = remainder (transverseBall m R) u.toFun gs.psi.toFun := by
  rw [bulkRemainder, H1P.sub_toFun_be]
  rfl

theorem bulkRemainder_gx :
    (bulkRemainder hab gs u).gx = remainder (transverseBall m R) u.gx gs.psi.toFun := by
  rw [bulkRemainder, H1P.sub_gx]
  rfl

theorem bulkRemainder_gz :
    (bulkRemainder hab gs u).gz
      = fun p => u.gz p - axialProfile gs u p.1 • gs.psi.grad p.2 := by
  rw [bulkRemainder, H1P.sub_gz]
  rfl

/-! ### Exact mass splitting (`eq:bulk-mass`) -/

theorem massP_bulkRemainder :
    massP (bulkRemainder hab gs u)
      = ∫ p in bulkCyl a b m R, remainder (transverseBall m R) u.toFun gs.psi.toFun p ^ 2 := by
  rw [massP, bulkRemainder_toFun]

/-- **Exact mass splitting** `∫_Ω |u|² = ∫_I |F|² + ‖w‖²` (`eq:bulk-mass`, manuscript 539). -/
theorem massP_bulk_split :
    massP u = (∫ x in Ioo a b, axialProfile gs u x ^ 2) + massP (bulkRemainder hab gs u) := by
  rw [massP_bulkRemainder]
  exact massP_split (I := Ioo a b) (volume_Ioo_ne_top' a b) u gs.psi.memL2
    (psi_normalized_integral gs)

/-! ### Exact splitting of the axial Dirichlet energy -/

theorem axialDirichletP_bulkRemainder :
    axialDirichletP (bulkRemainder hab gs u)
      = ∫ p in bulkCyl a b m R, remainder (transverseBall m R) u.gx gs.psi.toFun p ^ 2 := by
  rw [axialDirichletP, bulkRemainder_gx]

/-- **Exact splitting of the axial Dirichlet energy** `∫_Ω (∂ₓu)² = ∫_I |F'|² + ∫_Ω (∂ₓw)²`.
This is the vanishing of the axial cross term of `eq:exact-separation`: it holds because `F'` is
by construction the `L²(B)`-projection of `∂ₓu` on `ψ_R`. -/
theorem axialDirichletP_bulk_split :
    axialDirichletP u
      = (∫ x in Ioo a b, axialProfileDeriv gs u x ^ 2)
        + axialDirichletP (bulkRemainder hab gs u) := by
  rw [axialDirichletP_bulkRemainder]
  exact mass_split (I := Ioo a b) (volume_Ioo_ne_top' a b) u.gx_memL2 gs.psi.memL2
    (psi_normalized_integral gs)

/-! ### The slice of the remainder is the transverse projection of the slice -/

theorem NBilin_psi_slice {x : ℝ} (hx : IsGoodSlice u x) :
    NBilin gs.psi (slice u x) = axialProfile gs u x := by
  show (∫ z in transverseBall m R, gs.psi.toFun z * (slice u x).toFun z)
    = ∫ z in transverseBall m R, u.toFun (x, z) * gs.psi.toFun z
  rw [slice_toFun hx]
  exact integral_congr_ae (.of_forall fun z => mul_comm _ _)

/-- **The transverse slice of `w` is the transverse `ψ_R`-projection of the slice of `u`.** -/
theorem ae_slice_bulkRemainder :
    ∀ᵐ x ∂(volume.restrict (Ioo a b)),
      slice (bulkRemainder hab gs u) x = gs.proj (slice u x) := by
  filter_upwards [ae_isGoodSlice u, ae_isGoodSlice (bulkRemainder hab gs u)] with x hxu hxw
  have hproj : gs.proj (slice u x) = slice u x - (axialProfile gs u x) • gs.psi := by
    rw [TransverseGroundState.proj, NBilin_psi_slice hxu]
  rw [hproj]
  refine Weak.H1.ext ?_ ?_
  · rw [slice_toFun hxw, weakH1_sub_toFun, slice_toFun hxu, Weak.H1.smul_toFun]
    funext z
    simp only [Pi.smul_apply, smul_eq_mul, bulkRemainder_toFun, remainder]
    rfl
  · rw [slice_grad hxw, weakH1_sub_grad, slice_grad hxu, Weak.H1.smul_grad]
    funext z
    simp only [Pi.smul_apply, bulkRemainder_gz]

/-- The slice of the remainder is `L²(B)`-orthogonal to `ψ_R`, for a.e. `x`. -/
theorem ae_NBilin_psi_slice_bulkRemainder :
    ∀ᵐ x ∂(volume.restrict (Ioo a b)),
      NBilin gs.psi (slice (bulkRemainder hab gs u) x) = 0 := by
  filter_upwards [ae_slice_bulkRemainder (hab := hab) (gs := gs) (u := u)] with x hx
  rw [hx]
  exact gs.NBilin_psi_proj _

end Decomposition


/-! ## Part 7. The exact separation and the gap bound

`eq:exact-separation` (line 535), `eq:T-bound` (line 536) and `eq:bulk-mass` (line 539) of the
manuscript, on the bulk cylinder. -/

section Separation

variable {bd : TransH1 m R →ₗ[ℝ] TransH1 m R →ₗ[ℝ] ℝ}

/-- The slice-wise renormalized transverse energy is integrable on `I`. -/
theorem integrableOn_slice_energy (gs : TransverseGroundState m α R bd)
    (hsl : BdSliceable a b bd) (v : H1P (bulkCyl a b m R)) :
    IntegrableOn (fun x => qB α bd (slice v x) - gs.nu * NB (slice v x)) (Ioo a b) := by
  have hd := integrableOn_dirichlet_slice v
  have hb := hsl.integrableOn v v
  have hn := integrableOn_NB_slice v
  have hdb : IntegrableOn
      (fun x => Weak.dirichlet (slice v x) + α * bd (slice v x) (slice v x)) (Ioo a b) :=
    hd.add (hb.const_mul α)
  have hnn : IntegrableOn (fun x => gs.nu * NB (slice v x)) (Ioo a b) := hn.const_mul gs.nu
  simp only [qB]
  exact hdb.sub hnn

/-- **The renormalized bulk energy splits into its axial part and the axial integral of the
renormalized transverse slice energies.**  This is the Fubini form of `E_bulk - ν N`. -/
theorem EB_sub_nu_massP (gs : TransverseGroundState m α R bd) (hsl : BdSliceable a b bd)
    (v : H1P (bulkCyl a b m R)) :
    EB α bd v - gs.nu * massP v
      = axialDirichletP v
        + ∫ x in Ioo a b, (qB α bd (slice v x) - gs.nu * NB (slice v x)) := by
  have hd := integrableOn_dirichlet_slice v
  have hb := hsl.integrableOn v v
  have hn := integrableOn_NB_slice v
  have key : ∫ x in Ioo a b, (qB α bd (slice v x) - gs.nu * NB (slice v x))
      = (∫ x in Ioo a b, Weak.dirichlet (slice v x))
        + α * (∫ x in Ioo a b, bd (slice v x) (slice v x))
        - gs.nu * ∫ x in Ioo a b, NB (slice v x) := by
    have hdb : IntegrableOn
        (fun x => Weak.dirichlet (slice v x) + α * bd (slice v x) (slice v x)) (Ioo a b) :=
      hd.add (hb.const_mul α)
    have hnn : IntegrableOn (fun x => gs.nu * NB (slice v x)) (Ioo a b) := hn.const_mul gs.nu
    simp only [qB]
    rw [integral_sub hdb hnn, integral_add hd (hb.const_mul α), integral_const_mul,
      integral_const_mul]
  rw [key, EB, dirichletP_eq_axial_add_slice, massP_eq_integral_NB_slice, bdCyl]
  ring

/-- **The transverse cross terms cancel** (manuscript lines 543-545): slice-wise, the
renormalized transverse energy of `u` equals that of the remainder `w`, by the weak eigenvalue
equation for `ψ_R`. -/
theorem ae_slice_energy_eq (hab : a < b) (gs : TransverseGroundState m α R bd)
    (u : H1P (bulkCyl a b m R)) :
    (fun x => qB α bd (slice u x) - gs.nu * NB (slice u x))
      =ᵐ[volume.restrict (Ioo a b)]
      fun x => qB α bd (slice (bulkRemainder hab gs u) x)
        - gs.nu * NB (slice (bulkRemainder hab gs u) x) := by
  filter_upwards [ae_slice_bulkRemainder (hab := hab) (gs := gs) (u := u)] with x hx
  rw [hx]
  exact gs.energy_split (slice u x)

/-- **`eq:exact-separation`** (manuscript line 535), on the bulk cylinder:
`E_bulk[u] - ν_R N[u] = ∫_I |F'|² + (E_bulk[w] - ν_R N[w])`.
This is an **identity**, not an asymptotic approximation. -/
theorem bulk_exact_separation (hab : a < b) (gs : TransverseGroundState m α R bd)
    (hsl : BdSliceable a b bd) (u : H1P (bulkCyl a b m R)) :
    EB α bd u - gs.nu * massP u
      = (∫ x in Ioo a b, axialProfileDeriv gs u x ^ 2)
        + (EB α bd (bulkRemainder hab gs u) - gs.nu * massP (bulkRemainder hab gs u)) := by
  rw [EB_sub_nu_massP gs hsl u, EB_sub_nu_massP gs hsl (bulkRemainder hab gs u),
    integral_congr_ae (ae_slice_energy_eq hab gs u),
    axialDirichletP_bulk_split (hab := hab) (gs := gs) (u := u)]
  ring

/-- **`eq:T-bound`** (manuscript line 536), on the bulk cylinder:
`T_R[w] = E_bulk[w] - ν_R N[w] ≥ c R⁻² ‖w‖²_{L²}`.
The axial Dirichlet energy of `w` is nonnegative and is dropped; the transverse part is the
spectral gap `gs.gap` applied slice-wise to the `L²(B)`-orthogonal slices of `w`. -/
theorem bulk_gap_bound (hab : a < b) (gs : TransverseGroundState m α R bd)
    (hsl : BdSliceable a b bd) (u : H1P (bulkCyl a b m R)) :
    gs.gapConst * R⁻¹ ^ 2 * massP (bulkRemainder hab gs u)
      ≤ EB α bd (bulkRemainder hab gs u) - gs.nu * massP (bulkRemainder hab gs u) := by
  set w := bulkRemainder hab gs u with hwdef
  rw [EB_sub_nu_massP gs hsl w]
  have hmono : (∫ x in Ioo a b, gs.gapConst * R⁻¹ ^ 2 * NB (slice w x))
      ≤ ∫ x in Ioo a b, (qB α bd (slice w x) - gs.nu * NB (slice w x)) := by
    refine integral_mono_ae ((integrableOn_NB_slice w).const_mul _)
      (integrableOn_slice_energy gs hsl w) ?_
    filter_upwards [ae_NBilin_psi_slice_bulkRemainder (hab := hab) (gs := gs) (u := u)] with x hx
    exact gs.gap _ hx
  have hmass : (∫ x in Ioo a b, gs.gapConst * R⁻¹ ^ 2 * NB (slice w x))
      = gs.gapConst * R⁻¹ ^ 2 * massP w := by
    rw [integral_const_mul, massP_eq_integral_NB_slice]
  have hax : 0 ≤ axialDirichletP w := axialDirichletP_nonneg w
  linarith

/-- **`eq:bulk-mass`** (manuscript line 539): the mass separates exactly,
`∫_Ω |u|² = ∫_I |F|² + ‖w‖²_{L²(Ω)}`. -/
theorem bulk_mass_split (hab : a < b) (gs : TransverseGroundState m α R bd)
    (u : H1P (bulkCyl a b m R)) :
    massP u = (∫ x in Ioo a b, axialProfile gs u x ^ 2) + massP (bulkRemainder hab gs u) :=
  massP_bulk_split

/-- **The bulk restriction of `eq:global-energy-lower`** (manuscript line 700), with
`Z = ‖w‖²_{L²(Ω)}`:
`E_bulk[u] - ν_R N[u] ≥ ∫_I |F'|² + c R⁻² Z`. -/
theorem bulk_separation (hab : a < b) (gs : TransverseGroundState m α R bd)
    (hsl : BdSliceable a b bd) (u : H1P (bulkCyl a b m R)) :
    (∫ x in Ioo a b, axialProfileDeriv gs u x ^ 2)
        + gs.gapConst * R⁻¹ ^ 2 * massP (bulkRemainder hab gs u)
      ≤ EB α bd u - gs.nu * massP u := by
  rw [bulk_exact_separation hab gs hsl u]
  linarith [bulk_gap_bound hab gs hsl u]

/-- **`F ∈ H¹(I)`** (manuscript line 530): on `I = (0,ℓ)` the axial profile has an absolutely
continuous representative in the concrete one-dimensional model `RobinCaps.Sobolev.H1 ℓ`, whose
classical derivative is `F'` a.e. and whose Dirichlet energy `D[F]` is the `∫_I |F'|²` appearing
in `bulk_exact_separation`. -/
theorem exists_h1_axialProfile {ℓ : ℝ} (hℓ : 0 < ℓ) (gs : TransverseGroundState m α R bd)
    (u : H1P (bulkCyl 0 ℓ m R)) :
    ∃ W : Sobolev.H1 ℓ,
      W.toFun =ᵐ[volume.restrict (Ioo 0 ℓ)] axialProfile gs u ∧
      deriv W.toFun =ᵐ[volume.restrict (Ioo 0 ℓ)] axialProfileDeriv gs u ∧
      Sobolev.dirichlet ℓ W = ∫ x in Ioo 0 ℓ, axialProfileDeriv gs u x ^ 2 := by
  have hF := memLp_axialProfile (a := 0) (b := ℓ) gs u
  have hG := memLp_axialProfileDeriv (a := 0) (b := ℓ) gs u
  obtain ⟨W, hW1, hW2⟩ := Sobolev.exists_h1_of_hasWeakDeriv hℓ (hF.integrable one_le_two)
    (hG.integrable one_le_two) hG.integrable_sq (hasWeakDeriv_axialProfile hℓ gs u)
  refine ⟨W, hW1, hW2, ?_⟩
  rw [Sobolev.dirichlet, Sobolev.intervalIntegral_eq_setIntegral_Ioo hℓ.le]
  refine integral_congr_ae ?_
  filter_upwards [hW2] with x hx
  rw [hx]

end Separation

end RobinCaps.ThinDomain

end


