import RobinCaps.ThinDomain.AxialCoeff
import RobinCaps.ThinDomain.H1PQuotient
import RobinCaps.ThinDomain.Tensor
import RobinCaps.Domain.Thin

/-!
# The bulk projection `π : u ↦ F_u` as a surjective linear map on the a.e. quotients

This file packages the **bulk projection** of the manuscript (`eq:bulk-projection`, `sec:proof`)

`F_u (x) = ∫_{B} u (x, z) ψ (z) dz`

as a *linear map* from the a.e.-quotient `H1PQ Ω` of the product weak space on the bulk cylinder
`Ω = (0,ℓ) ×ˢ B` to the a.e.-quotient `Sobolev.H1Q ℓ` of the one-dimensional Sobolev model, and
proves that this map is **surjective**.  It is the map `π` required by the abstract two-step
comparison of `RobinCaps/Spectrum/MainAbstract.lean` (`BulkComparison`,
`minmax_lower_of_bulk_codim`, whose hypothesis is `Function.Surjective π`).

## Contents

* `bulkRep` — a chosen absolutely continuous representative of `axialCoeff B u.toFun ψ` in the
  concrete model `RobinCaps.Sobolev.H1 ℓ`, obtained from
  `RobinCaps.ThinDomain.exists_h1_axialCoeff`, with `bulkRep_ae`, `bulkRep_deriv_ae` and
  `bulkRep_dirichlet_le`.
* `rep_eqOn_of_ae` — **uniqueness on `[0,ℓ]`**: two elements of `Sobolev.H1 ℓ` which agree a.e.
  on `(0,ℓ)` agree *everywhere* on `[0,ℓ]` (both are continuous there, by
  `AbsolutelyContinuousOnInterval.continuousOn`, and `(0,ℓ)` has full measure in `[0,ℓ]`), hence
  define the same class in `Sobolev.H1Q ℓ = H1 ℓ ⧸ nullOff ℓ`.
* `bulkRepₗ`, `bulkProj` — the linear map `H1P Ω →ₗ[ℝ] Sobolev.H1Q ℓ` and its descent
  `H1PQ Ω →ₗ[ℝ] Sobolev.H1Q ℓ` through `Submodule.liftQ`.
* `massQ_bulkProj_mk`, `massQ_bulkProj_le`, `bulkRep_dirichlet_le`,
  `dirichlet_bulkRep_le_dirichletPQ` — compatibility of the projection with the mass
  (`BulkMass.massP_split`) and with the Dirichlet energy.
* `H1P.tensorAC` — the tensor product `W ⊗ ψ` of an **absolutely continuous** axial factor
  `W : Sobolev.H1 ℓ` (only weakly differentiable!) with a transverse factor `ψ ∈ H¹(B)`, as an
  element of `H1P Ω`.  The axial half of the weak-gradient identity uses the one-dimensional
  *weak* integration by parts `hasWeakDeriv_h1` (from `W.ftc` and
  `RobinCaps.Sobolev.hasWeakDeriv_primitive`) instead of the classical one used in
  `RobinCaps.ThinDomain.hasWeakGradP_tensor`.
* `bulkProj_tensorAC`, `bulkProj_surjective` — **surjectivity of the bulk projection**.
* `restrictBulkP`, `restrictBulkPQ`, `bulkProjT`, `bulkProjThin` — the restriction of the thin
  domain `Ω_R` to its bulk cylinder and the composite projection
  `H1PQ (thinDomain …) →ₗ[ℝ] Sobolev.H1Q (bulkLength …)`, together with the **target**
  `BulkProjThinSurjective` (see its docstring: surjectivity from the thin domain needs the trial
  extension `eq:trial-extension`, which lives in `RobinCaps/ThinDomain/Trial.lean`).

Everything is proved without `sorry`, `axiom`, `admit` or `native_decide`.
-/

-- Several statements carry hypotheses (finiteness of `volume B`, positivity of the interval)
-- for uniformity even when the particular proof does not use them.
set_option linter.unusedVariables false

open MeasureTheory Set Filter

open scoped ContDiff ENNReal Topology

namespace RobinCaps.ThinDomain

noncomputable section

variable {m : ℕ}

/-! ## Item 1: the absolutely continuous representative of the axial coefficient -/

section Rep

variable {ℓ : ℝ}

/-- An element of the concrete one-dimensional model is continuous on `[0,ℓ]`. -/
theorem h1_continuousOn (hℓ : 0 ≤ ℓ) (w : Sobolev.H1 ℓ) : ContinuousOn w.toFun (Icc 0 ℓ) := by
  have h := w.ac.continuousOn
  rwa [uIcc_of_le hℓ] at h

/-- **Uniqueness of the representative on `[0,ℓ]`.**  Two elements of `Sobolev.H1 ℓ` that agree
almost everywhere on `(0,ℓ)` agree at *every* point of `[0,ℓ]`: both are continuous there and
`(0,ℓ)` is dense with full measure in `[0,ℓ]`. -/
theorem rep_eqOn_of_ae (hℓ : 0 < ℓ) {w₁ w₂ : Sobolev.H1 ℓ}
    (h : w₁.toFun =ᵐ[volume.restrict (Ioo 0 ℓ)] w₂.toFun) :
    EqOn w₁.toFun w₂.toFun (Icc 0 ℓ) := by
  have hIcc : w₁.toFun =ᵐ[volume.restrict (Icc (0 : ℝ) ℓ)] w₂.toFun := by
    rwa [Measure.restrict_congr_set Ioo_ae_eq_Icc] at h
  exact Measure.eqOn_Icc_of_ae_eq volume (ne_of_lt hℓ) hIcc
    (h1_continuousOn hℓ.le w₁) (h1_continuousOn hℓ.le w₂)

/-- The underlying function of a difference in `Sobolev.H1 ℓ`. -/
theorem h1_sub_toFun (w₁ w₂ : Sobolev.H1 ℓ) :
    (w₁ - w₂).toFun = fun x => w₁.toFun x - w₂.toFun x := by
  have h : w₁ - w₂ = w₁ + (-1 : ℝ) • w₂ := by
    rw [neg_one_smul]
    exact sub_eq_add_neg w₁ w₂
  rw [h]
  funext x
  show w₁.toFun x + (-1 : ℝ) * w₂.toFun x = w₁.toFun x - w₂.toFun x
  ring

/-- Two elements of `Sobolev.H1 ℓ` agreeing on `[0,ℓ]` define the same class in the quotient
`Sobolev.H1Q ℓ = H1 ℓ ⧸ nullOff ℓ` (the null subspace is the set of functions vanishing on
`[[0,ℓ]] = [0,ℓ]`). -/
theorem h1Q_mk_eq_of_eqOn (hℓ : 0 ≤ ℓ) {w₁ w₂ : Sobolev.H1 ℓ}
    (h : EqOn w₁.toFun w₂.toFun (Icc 0 ℓ)) :
    (Submodule.Quotient.mk w₁ : Sobolev.H1Q ℓ) = Submodule.Quotient.mk w₂ := by
  rw [Submodule.Quotient.eq]
  refine Sobolev.mem_nullOff.2 fun x hx => ?_
  rw [uIcc_of_le hℓ] at hx
  rw [h1_sub_toFun]
  simp [h hx]

/-- The class of an element of `Sobolev.H1 ℓ` vanishing on `[0,ℓ]` is zero. -/
theorem h1Q_mk_eq_zero_of_eqOn (hℓ : 0 ≤ ℓ) {w : Sobolev.H1 ℓ}
    (h : ∀ x ∈ Icc (0 : ℝ) ℓ, w.toFun x = 0) :
    (Submodule.Quotient.mk w : Sobolev.H1Q ℓ) = 0 := by
  rw [Submodule.Quotient.mk_eq_zero]
  refine Sobolev.mem_nullOff.2 fun x hx => ?_
  rw [uIcc_of_le hℓ] at hx
  exact h x hx

end Rep

section BulkProj

variable {ℓ : ℝ} {B : Set (EuclideanSpace ℝ (Fin m))} {ψ : EuclideanSpace ℝ (Fin m) → ℝ}

/-- **The bulk representative.**  A chosen absolutely continuous representative, in the concrete
one-dimensional model `RobinCaps.Sobolev.H1 ℓ`, of the bulk projection
`F_u (x) = ∫_B u (x, z) ψ z dz` (`eq:bulk-projection`). -/
def bulkRep (hℓ : 0 < ℓ) (hBo : IsOpen B) (hB : volume B ≠ ⊤)
    (hψ : MemLp ψ 2 (volume.restrict B)) (hψ1 : ∫ z in B, ψ z ^ 2 = 1)
    (u : H1P (Ioo 0 ℓ ×ˢ B)) : Sobolev.H1 ℓ :=
  Classical.choose (exists_h1_axialCoeff hℓ hBo hB u hψ hψ1)

/-- The bulk representative represents the axial coefficient. -/
theorem bulkRep_ae (hℓ : 0 < ℓ) (hBo : IsOpen B) (hB : volume B ≠ ⊤)
    (hψ : MemLp ψ 2 (volume.restrict B)) (hψ1 : ∫ z in B, ψ z ^ 2 = 1)
    (u : H1P (Ioo 0 ℓ ×ˢ B)) :
    (bulkRep hℓ hBo hB hψ hψ1 u).toFun
      =ᵐ[volume.restrict (Ioo 0 ℓ)] axialCoeff B u.toFun ψ :=
  (Classical.choose_spec (exists_h1_axialCoeff hℓ hBo hB u hψ hψ1)).1

/-- The derivative of the bulk representative is the axial coefficient of `∂ₓu`. -/
theorem bulkRep_deriv_ae (hℓ : 0 < ℓ) (hBo : IsOpen B) (hB : volume B ≠ ⊤)
    (hψ : MemLp ψ 2 (volume.restrict B)) (hψ1 : ∫ z in B, ψ z ^ 2 = 1)
    (u : H1P (Ioo 0 ℓ ×ˢ B)) :
    deriv (bulkRep hℓ hBo hB hψ hψ1 u).toFun
      =ᵐ[volume.restrict (Ioo 0 ℓ)] axialCoeff B u.gx ψ :=
  (Classical.choose_spec (exists_h1_axialCoeff hℓ hBo hB u hψ hψ1)).2.1

/-- **The Dirichlet energy does not increase under the bulk projection** (the axial term of
`eq:exact-separation`). -/
theorem bulkRep_dirichlet_le (hℓ : 0 < ℓ) (hBo : IsOpen B) (hB : volume B ≠ ⊤)
    (hψ : MemLp ψ 2 (volume.restrict B)) (hψ1 : ∫ z in B, ψ z ^ 2 = 1)
    (u : H1P (Ioo 0 ℓ ×ˢ B)) :
    Sobolev.dirichlet ℓ (bulkRep hℓ hBo hB hψ hψ1 u) ≤ dirichletP u :=
  (Classical.choose_spec (exists_h1_axialCoeff hℓ hBo hB u hψ hψ1)).2.2

/-! ### Additivity and homogeneity of the axial coefficient -/

/-- The axial coefficient is additive in the function (a.e. on the interval: the slices are
integrable only for a.e. `x`). -/
theorem ae_axialCoeff_add {I : Set ℝ} (hI : volume I ≠ ⊤)
    (hψ : MemLp ψ 2 (volume.restrict B)) (u v : H1P (I ×ˢ B)) :
    ∀ᵐ x ∂(volume.restrict I),
      axialCoeff B (u + v).toFun ψ x
        = axialCoeff B u.toFun ψ x + axialCoeff B v.toFun ψ x := by
  filter_upwards [ae_integrable_slice_mul hI u.memL2 hψ,
    ae_integrable_slice_mul hI v.memL2 hψ] with x hu hv
  show (∫ z in B, (u + v).toFun (x, z) * ψ z)
      = (∫ z in B, u.toFun (x, z) * ψ z) + ∫ z in B, v.toFun (x, z) * ψ z
  rw [← integral_add hu hv]
  refine integral_congr_ae (.of_forall fun z => ?_)
  show (u.toFun (x, z) + v.toFun (x, z)) * ψ z = _
  ring

/-- The axial coefficient is homogeneous in the function. -/
theorem axialCoeff_smul_h1p {I : Set ℝ} (c : ℝ) (u : H1P (I ×ˢ B)) (x : ℝ) :
    axialCoeff B (c • u).toFun ψ x = c * axialCoeff B u.toFun ψ x := by
  show (∫ z in B, (c • u).toFun (x, z) * ψ z) = c * ∫ z in B, u.toFun (x, z) * ψ z
  rw [← integral_const_mul]
  refine integral_congr_ae (.of_forall fun z => ?_)
  show c * u.toFun (x, z) * ψ z = c * (u.toFun (x, z) * ψ z)
  ring

/-! ### Item 2: the linear map and its descent to the quotient -/

/-- **The bulk projection on `H1P Ω`**, as a linear map to the quotient one-dimensional model.
Linearity holds *after* passing to `Sobolev.H1Q ℓ`: the chosen representatives are only
determined up to their values on `[0,ℓ]`. -/
def bulkRepₗ (hℓ : 0 < ℓ) (hBo : IsOpen B) (hB : volume B ≠ ⊤)
    (hψ : MemLp ψ 2 (volume.restrict B)) (hψ1 : ∫ z in B, ψ z ^ 2 = 1) :
    H1P (Ioo 0 ℓ ×ˢ B) →ₗ[ℝ] Sobolev.H1Q ℓ where
  toFun u := Submodule.Quotient.mk (bulkRep hℓ hBo hB hψ hψ1 u)
  map_add' u v := by
    have hsum : (Submodule.Quotient.mk (bulkRep hℓ hBo hB hψ hψ1 u)
          + Submodule.Quotient.mk (bulkRep hℓ hBo hB hψ hψ1 v) : Sobolev.H1Q ℓ)
        = Submodule.Quotient.mk
            (bulkRep hℓ hBo hB hψ hψ1 u + bulkRep hℓ hBo hB hψ hψ1 v) := rfl
    rw [hsum]
    refine h1Q_mk_eq_of_eqOn hℓ.le (rep_eqOn_of_ae hℓ ?_)
    filter_upwards [bulkRep_ae hℓ hBo hB hψ hψ1 (u + v), bulkRep_ae hℓ hBo hB hψ hψ1 u,
      bulkRep_ae hℓ hBo hB hψ hψ1 v, ae_axialCoeff_add (volume_Ioo_ne_top 0 ℓ) hψ u v] with x h0 h1 h2 h3
    show (bulkRep hℓ hBo hB hψ hψ1 (u + v)).toFun x
        = (bulkRep hℓ hBo hB hψ hψ1 u).toFun x + (bulkRep hℓ hBo hB hψ hψ1 v).toFun x
    rw [h0, h1, h2, h3]
  map_smul' c u := by
    have hsmul : (c • Submodule.Quotient.mk (bulkRep hℓ hBo hB hψ hψ1 u) : Sobolev.H1Q ℓ)
        = Submodule.Quotient.mk (c • bulkRep hℓ hBo hB hψ hψ1 u) := rfl
    show Submodule.Quotient.mk (bulkRep hℓ hBo hB hψ hψ1 (c • u))
        = (RingHom.id ℝ) c • Submodule.Quotient.mk (bulkRep hℓ hBo hB hψ hψ1 u)
    rw [RingHom.id_apply, hsmul]
    refine h1Q_mk_eq_of_eqOn hℓ.le (rep_eqOn_of_ae hℓ ?_)
    filter_upwards [bulkRep_ae hℓ hBo hB hψ hψ1 (c • u), bulkRep_ae hℓ hBo hB hψ hψ1 u]
      with x h0 h1
    show (bulkRep hℓ hBo hB hψ hψ1 (c • u)).toFun x
        = c * (bulkRep hℓ hBo hB hψ hψ1 u).toFun x
    rw [h0, h1, axialCoeff_smul_h1p c u x]

@[simp] theorem bulkRepₗ_apply (hℓ : 0 < ℓ) (hBo : IsOpen B) (hB : volume B ≠ ⊤)
    (hψ : MemLp ψ 2 (volume.restrict B)) (hψ1 : ∫ z in B, ψ z ^ 2 = 1)
    (u : H1P (Ioo 0 ℓ ×ˢ B)) :
    bulkRepₗ hℓ hBo hB hψ hψ1 u = Submodule.Quotient.mk (bulkRep hℓ hBo hB hψ hψ1 u) := rfl

/-- An a.e.-vanishing element of `H1P Ω` has vanishing axial coefficient a.e. on the interval. -/
theorem ae_axialCoeff_eq_zero_of_mem_nullAEP {I : Set ℝ} (hB : volume B ≠ ⊤)
    {u : H1P (I ×ˢ B)} (hu : u ∈ nullAEP (I ×ˢ B)) :
    ∀ᵐ x ∂(volume.restrict I), axialCoeff B u.toFun ψ x = 0 := by
  haveI := isFiniteMeasure_restrict hB
  have hu' : u.toFun =ᵐ[volume.restrict (I ×ˢ B)] 0 := hu
  rw [← volume_restrict_prod I B] at hu'
  have hslice := Measure.ae_ae_of_ae_prod hu'
  filter_upwards [hslice] with x hx
  show (∫ z in B, u.toFun (x, z) * ψ z) = 0
  rw [integral_congr_ae (g := fun _ : EuclideanSpace ℝ (Fin m) => (0 : ℝ)) ?_, integral_zero]
  filter_upwards [hx] with z hz
  show u.toFun (x, z) * ψ z = 0
  simp only [Pi.zero_apply] at hz
  rw [hz, zero_mul]

/-- **The bulk projection on the a.e. quotient** (`π` of the abstract two-step comparison).  It
is well defined because the axial coefficient only depends on the a.e. class of `u` on `Ω`. -/
def bulkProj (hℓ : 0 < ℓ) (hBo : IsOpen B) (hB : volume B ≠ ⊤)
    (hψ : MemLp ψ 2 (volume.restrict B)) (hψ1 : ∫ z in B, ψ z ^ 2 = 1) :
    H1PQ (Ioo 0 ℓ ×ˢ B) →ₗ[ℝ] Sobolev.H1Q ℓ := by
  refine Submodule.liftQ _ (bulkRepₗ hℓ hBo hB hψ hψ1) ?_
  intro u hu
  show bulkRepₗ hℓ hBo hB hψ hψ1 u = 0
  rw [bulkRepₗ_apply]
  refine h1Q_mk_eq_zero_of_eqOn hℓ.le ?_
  have hz : (bulkRep hℓ hBo hB hψ hψ1 u).toFun
      =ᵐ[volume.restrict (Ioo 0 ℓ)] (0 : Sobolev.H1 ℓ).toFun := by
    filter_upwards [bulkRep_ae hℓ hBo hB hψ hψ1 u,
      ae_axialCoeff_eq_zero_of_mem_nullAEP (ψ := ψ) hB hu] with x h1 h2
    rw [h1, h2]
    rfl
  intro x hx
  simpa using rep_eqOn_of_ae hℓ hz hx

@[simp] theorem bulkProj_mk (hℓ : 0 < ℓ) (hBo : IsOpen B) (hB : volume B ≠ ⊤)
    (hψ : MemLp ψ 2 (volume.restrict B)) (hψ1 : ∫ z in B, ψ z ^ 2 = 1)
    (u : H1P (Ioo 0 ℓ ×ˢ B)) :
    bulkProj hℓ hBo hB hψ hψ1 (Submodule.Quotient.mk u)
      = Submodule.Quotient.mk (bulkRep hℓ hBo hB hψ hψ1 u) := rfl

/-! ### Item 3: compatibility with the mass and the Dirichlet energy -/

/-- **The mass of the projection is the `L²` norm of the axial coefficient.** -/
theorem massQ_bulkProj_mk (hℓ : 0 < ℓ) (hBo : IsOpen B) (hB : volume B ≠ ⊤)
    (hψ : MemLp ψ 2 (volume.restrict B)) (hψ1 : ∫ z in B, ψ z ^ 2 = 1)
    (u : H1P (Ioo 0 ℓ ×ˢ B)) :
    Sobolev.massQ ℓ (bulkProj hℓ hBo hB hψ hψ1 (Submodule.Quotient.mk u))
      = ∫ x in Ioo 0 ℓ, axialCoeff B u.toFun ψ x ^ 2 := by
  rw [bulkProj_mk, Sobolev.massQ_mk, Sobolev.mass,
    Sobolev.intervalIntegral_eq_setIntegral_Ioo hℓ.le]
  refine integral_congr_ae ?_
  filter_upwards [bulkRep_ae hℓ hBo hB hψ hψ1 u] with x hx
  rw [hx]

/-- **The bulk projection does not increase the mass** (`BulkMass.massP_split`:
`N_Ω[u] = ∫_I F_u² + ∫_Ω w²` with `w = u - F_u ⊗ ψ`). -/
theorem massQ_bulkProj_le (hℓ : 0 < ℓ) (hBo : IsOpen B) (hB : volume B ≠ ⊤)
    (hψ : MemLp ψ 2 (volume.restrict B)) (hψ1 : ∫ z in B, ψ z ^ 2 = 1)
    (w : H1PQ (Ioo 0 ℓ ×ˢ B)) :
    Sobolev.massQ ℓ (bulkProj hℓ hBo hB hψ hψ1 w) ≤ massPQ w := by
  obtain ⟨u, rfl⟩ := Submodule.Quotient.mk_surjective (nullAEP (Ioo 0 ℓ ×ˢ B)) w
  rw [massQ_bulkProj_mk, massPQ_mk]
  exact integral_axialCoeff_sq_le_massP (volume_Ioo_ne_top 0 ℓ) u hψ hψ1

/-- **The bulk projection does not increase the Dirichlet energy**, in the quotient form. -/
theorem dirichlet_bulkRep_le_dirichletPQ (hℓ : 0 < ℓ) (hBo : IsOpen B) (hB : volume B ≠ ⊤)
    (hψ : MemLp ψ 2 (volume.restrict B)) (hψ1 : ∫ z in B, ψ z ^ 2 = 1)
    (hΩ : IsOpen (Ioo 0 ℓ ×ˢ B)) (u : H1P (Ioo 0 ℓ ×ˢ B)) :
    Sobolev.dirichlet ℓ (bulkRep hℓ hBo hB hψ hψ1 u)
      ≤ dirichletPQ hΩ (Submodule.Quotient.mk u) := by
  rw [dirichletPQ_mk]
  exact bulkRep_dirichlet_le hℓ hBo hB hψ hψ1 u

/-! ## Item 4: surjectivity via tensor products with an absolutely continuous axial factor -/

/-! ### The one-dimensional weak derivative of an element of the concrete model -/

/-- The integral of the derivative of a test function over `(a,b)` vanishes. -/
theorem setIntegral_deriv_test_zero {a b : ℝ} {φ : ℝ → ℝ} (hφ : ContDiff ℝ ∞ φ)
    (hφc : HasCompactSupport φ) (hφs : tsupport φ ⊆ Ioo a b) :
    ∫ x in Ioo a b, deriv φ x = 0 := by
  have hφ' : ContDiff ℝ ∞ (deriv φ) := (contDiff_infty_iff_deriv.1 hφ).2
  have hdsupp : tsupport (deriv φ) ⊆ Ioo a b :=
    (closure_minimal support_deriv_subset isClosed_closure).trans hφs
  rw [Sobolev.setIntegral_test_eq_integral hdsupp]
  exact integral_deriv_eq_zero_of_compactSupport
    (fun x => (hφ.differentiable (by simp) x).hasDerivAt) hφ'.continuous hφc

/-- **The concrete model has the expected weak derivative.**  An element `W` of
`RobinCaps.Sobolev.H1 ℓ` is, by its `ftc` field, the constant `W 0` plus the primitive of
`deriv W`, so `deriv W` is a one-dimensional *weak* derivative of `W` on `(0,ℓ)`
(`RobinCaps.Sobolev.hasWeakDeriv_primitive`).  This replaces the classical integration by parts
of `hasWeakGradP_tensor`, which is unavailable for a merely absolutely continuous factor. -/
theorem hasWeakDeriv_h1 (hℓ : 0 < ℓ) (W : Sobolev.H1 ℓ) :
    Sobolev.HasWeakDeriv 0 ℓ W.toFun (deriv W.toFun) := by
  have hg : IntegrableOn (deriv W.toFun) (Ioo 0 ℓ) :=
    (intervalIntegrable_iff_integrableOn_Ioo_of_le hℓ.le).1 W.deriv_int
  have hprim : Sobolev.HasWeakDeriv 0 ℓ
      (fun x => ∫ t in (0 : ℝ)..x, deriv W.toFun t) (deriv W.toFun) :=
    Sobolev.hasWeakDeriv_primitive hℓ hg ⟨le_rfl, hℓ.le⟩
  have hWeq : EqOn W.toFun (fun x => W.toFun 0 + ∫ t in (0 : ℝ)..x, deriv W.toFun t)
      (Ioo 0 ℓ) := fun x hx => W.ftc x (Ioo_subset_Icc_self hx)
  have hWint : IntegrableOn W.toFun (Ioo 0 ℓ) :=
    ((h1_continuousOn hℓ.le W).integrableOn_Icc).mono_set Ioo_subset_Icc_self
  have hPint : IntegrableOn (fun x => ∫ t in (0 : ℝ)..x, deriv W.toFun t) (Ioo 0 ℓ) := by
    refine IntegrableOn.congr_fun (hWint.sub (integrable_const (W.toFun 0))) ?_
      measurableSet_Ioo
    intro x hx
    show W.toFun x - W.toFun 0 = _
    rw [hWeq hx]
    ring
  intro φ hφ hφc hφs
  have hφ' : ContDiff ℝ ∞ (deriv φ) := (contDiff_infty_iff_deriv.1 hφ).2
  have h1 : IntegrableOn (fun x => (∫ t in (0 : ℝ)..x, deriv W.toFun t) * deriv φ x)
      (Ioo 0 ℓ) := Sobolev.integrableOn_mul_test hPint hφ'.continuous hφc.deriv
  have h2 : IntegrableOn (fun x => W.toFun 0 * deriv φ x) (Ioo 0 ℓ) := by
    refine Integrable.const_mul ?_ (W.toFun 0)
    exact (hφ'.continuous.integrableOn_Icc (a := 0) (b := ℓ)).mono_set Ioo_subset_Icc_self
  have hstep : (∫ x in Ioo 0 ℓ, W.toFun x * deriv φ x)
      = (∫ x in Ioo 0 ℓ, W.toFun 0 * deriv φ x)
        + ∫ x in Ioo 0 ℓ, (∫ t in (0 : ℝ)..x, deriv W.toFun t) * deriv φ x := by
    rw [← integral_add h2 h1]
    refine setIntegral_congr_fun measurableSet_Ioo fun x hx => ?_
    rw [hWeq hx]
    ring
  rw [hstep, integral_const_mul, setIntegral_deriv_test_zero hφ hφc hφs, mul_zero, zero_add]
  exact hprim φ hφ hφc hφs

/-! ### `L²` membership of the factors and of the tensor product -/

/-- An element of the concrete model is square integrable on `(0,ℓ)` (it is continuous on the
compact interval `[0,ℓ]`). -/
theorem memLp_two_h1_toFun (hℓ : 0 < ℓ) (W : Sobolev.H1 ℓ) :
    MemLp W.toFun 2 (volume.restrict (Ioo 0 ℓ)) := by
  have hc : ContinuousOn W.toFun (Icc 0 ℓ) := h1_continuousOn hℓ.le W
  have hm : AEStronglyMeasurable W.toFun (volume.restrict (Ioo 0 ℓ)) :=
    (hc.mono Ioo_subset_Icc_self).aestronglyMeasurable measurableSet_Ioo
  refine (memLp_two_iff_integrable_sq hm).2 ?_
  exact ((hc.pow 2).integrableOn_Icc).mono_set Ioo_subset_Icc_self

/-- The derivative of an element of the concrete model is square integrable on `(0,ℓ)` (this is
the `H¹` condition `deriv_sq_int`). -/
theorem memLp_two_h1_deriv (hℓ : 0 < ℓ) (W : Sobolev.H1 ℓ) :
    MemLp (deriv W.toFun) 2 (volume.restrict (Ioo 0 ℓ)) := by
  have hm : AEStronglyMeasurable (deriv W.toFun) (volume.restrict (Ioo 0 ℓ)) :=
    (measurable_deriv W.toFun).aestronglyMeasurable
  refine (memLp_two_iff_integrable_sq hm).2 ?_
  exact (intervalIntegrable_iff_integrableOn_Ioo_of_le hℓ.le).1 W.deriv_sq_int

/-- **`L²` of a scalar tensor product** on a product set: `f ∈ L²(I)` and `w ∈ L²(B)` give
`(x,z) ↦ f x · w z ∈ L²(I ×ˢ B)`.  Unlike `memLp_two_tensor` no continuity of `f` is
assumed. -/
theorem memLp_two_prodMul {I : Set ℝ} {f : ℝ → ℝ} {w : EuclideanSpace ℝ (Fin m) → ℝ}
    (hf : MemLp f 2 (volume.restrict I)) (hw : MemLp w 2 (volume.restrict B)) :
    MemLp (fun p : CapSpace m => f p.1 * w p.2) 2 (volume.restrict (I ×ˢ B)) := by
  rw [← volume_restrict_prod I B]
  have hm : AEStronglyMeasurable (fun p : CapSpace m => f p.1 * w p.2)
      (((volume : Measure ℝ).restrict I).prod
        ((volume : Measure (EuclideanSpace ℝ (Fin m))).restrict B)) :=
    (hf.aestronglyMeasurable.comp_fst).mul (hw.aestronglyMeasurable.comp_snd)
  rw [memLp_two_iff_integrable_sq hm]
  refine (hf.integrable_sq.mul_prod hw.integrable_sq).congr (.of_forall fun p => ?_)
  simp [mul_pow]

/-- **`L²` of a vector tensor product** on a product set. -/
theorem memLp_two_prodSmul {I : Set ℝ} {f : ℝ → ℝ}
    {w : EuclideanSpace ℝ (Fin m) → EuclideanSpace ℝ (Fin m)}
    (hf : MemLp f 2 (volume.restrict I)) (hw : MemLp w 2 (volume.restrict B)) :
    MemLp (fun p : CapSpace m => f p.1 • w p.2) 2 (volume.restrict (I ×ˢ B)) := by
  rw [← volume_restrict_prod I B]
  have hm : AEStronglyMeasurable (fun p : CapSpace m => f p.1 • w p.2)
      (((volume : Measure ℝ).restrict I).prod
        ((volume : Measure (EuclideanSpace ℝ (Fin m))).restrict B)) :=
    (hf.aestronglyMeasurable.comp_fst).smul (hw.aestronglyMeasurable.comp_snd)
  rw [memLp_two_iff_integrable_sq_norm hm]
  have hwn : Integrable (fun z => ‖w z‖ ^ 2) (volume.restrict B) :=
    (memLp_two_iff_integrable_sq_norm hw.aestronglyMeasurable).1 hw
  refine (hf.integrable_sq.mul_prod hwn).congr (.of_forall fun p => ?_)
  simp only [norm_smul, mul_pow, Real.norm_eq_abs, sq_abs]

/-! ### The tensor product with an absolutely continuous axial factor -/

/-- **The separated function `W ⊗ ψ`** with an absolutely continuous axial factor
`W ∈ RobinCaps.Sobolev.H1 ℓ`. -/
def tensorACFun (W : Sobolev.H1 ℓ) (Ψ : Sobolev.Weak.H1 B) (p : CapSpace m) : ℝ :=
  W.toFun p.1 * Ψ.toFun p.2

@[simp] theorem tensorACFun_apply (W : Sobolev.H1 ℓ) (Ψ : Sobolev.Weak.H1 B) (p : CapSpace m) :
    tensorACFun W Ψ p = W.toFun p.1 * Ψ.toFun p.2 := rfl

/-- **The weak gradient of `W ⊗ ψ`** for a merely absolutely continuous axial factor.  The
proof is the one of `hasWeakGradP_tensor` with the classical one-dimensional integration by
parts replaced by the weak one (`hasWeakDeriv_h1`). -/
theorem hasWeakGradP_tensorAC (hℓ : 0 < ℓ) (W : Sobolev.H1 ℓ) (Ψ : Sobolev.Weak.H1 B) :
    HasWeakGradP (Ioo 0 ℓ ×ˢ B) (tensorACFun W Ψ)
      (fun p => deriv W.toFun p.1 * Ψ.toFun p.2) (fun p => W.toFun p.1 • Ψ.grad p.2) := by
  have hmeas := volume_restrict_prod (Ioo (0 : ℝ) ℓ) B
  have hu : MemLp (tensorACFun W Ψ) 2 (volume.restrict (Ioo 0 ℓ ×ˢ B)) :=
    memLp_two_prodMul (memLp_two_h1_toFun hℓ W) Ψ.memL2
  have hgx : MemLp (fun p : CapSpace m => deriv W.toFun p.1 * Ψ.toFun p.2) 2
      (volume.restrict (Ioo 0 ℓ ×ˢ B)) :=
    memLp_two_prodMul (memLp_two_h1_deriv hℓ W) Ψ.memL2
  have hgz : MemLp (fun p : CapSpace m => W.toFun p.1 • Ψ.grad p.2) 2
      (volume.restrict (Ioo 0 ℓ ×ˢ B)) :=
    memLp_two_prodSmul (memLp_two_h1_toFun hℓ W) Ψ.grad_memL2
  intro φ hφ hφc hφs
  have hφ1 : ContDiff ℝ 1 φ := hφ.of_le (by simp)
  constructor
  · -- axial identity
    have hintL : Integrable (fun p : CapSpace m => tensorACFun W Ψ p *
        fderiv ℝ φ p ((1 : ℝ), (0 : EuclideanSpace ℝ (Fin m))))
        (volume.restrict (Ioo 0 ℓ ×ˢ B)) :=
      integrable_mul_dirDeriv hu hφ hφc _
    have hintR : Integrable
        (fun p : CapSpace m => (deriv W.toFun p.1 * Ψ.toFun p.2) * φ p)
        (volume.restrict (Ioo 0 ℓ ×ˢ B)) :=
      integrable_gx_mul hgx hφ hφc
    rw [← hmeas] at hintL hintR
    have key : ∀ z : EuclideanSpace ℝ (Fin m),
        (∫ x in Ioo 0 ℓ, tensorACFun W Ψ (x, z) *
            fderiv ℝ φ (x, z) ((1 : ℝ), (0 : EuclideanSpace ℝ (Fin m))))
          = -∫ x in Ioo 0 ℓ, (deriv W.toFun x * Ψ.toFun z) * φ (x, z) := by
      intro z
      have hgC : ContDiff ℝ ∞ fun t : ℝ => φ (t, z) :=
        hφ.comp (contDiff_id.prodMk contDiff_const)
      have hgc : HasCompactSupport fun t : ℝ => φ (t, z) := hasCompactSupport_sliceFst hφc z
      have hgs : tsupport (fun t : ℝ => φ (t, z)) ⊆ Ioo 0 ℓ :=
        (tsupport_sliceFst_subset φ z).trans fun _ hx => (hφs hx).1
      have h1 : (∫ x in Ioo 0 ℓ, tensorACFun W Ψ (x, z) *
            fderiv ℝ φ (x, z) ((1 : ℝ), (0 : EuclideanSpace ℝ (Fin m))))
          = Ψ.toFun z * ∫ x in Ioo 0 ℓ, W.toFun x * deriv (fun t : ℝ => φ (t, z)) x := by
        rw [← integral_const_mul]
        refine integral_congr_ae (.of_forall fun x => ?_)
        simp only [tensorACFun_apply, deriv_sliceFst hφ1 x z]
        ring
      have h2 : (∫ x in Ioo 0 ℓ, (deriv W.toFun x * Ψ.toFun z) * φ (x, z))
          = Ψ.toFun z * ∫ x in Ioo 0 ℓ, deriv W.toFun x * φ (x, z) := by
        rw [← integral_const_mul]
        refine integral_congr_ae (.of_forall fun x => ?_)
        ring
      have hibp : (∫ x in Ioo 0 ℓ, W.toFun x * deriv (fun t : ℝ => φ (t, z)) x)
          = -∫ x in Ioo 0 ℓ, deriv W.toFun x * φ (x, z) :=
        hasWeakDeriv_h1 hℓ W (fun t : ℝ => φ (t, z)) hgC hgc hgs
      rw [h1, h2, hibp]
      ring
    calc (∫ p in Ioo 0 ℓ ×ˢ B, tensorACFun W Ψ p *
            fderiv ℝ φ p ((1 : ℝ), (0 : EuclideanSpace ℝ (Fin m))))
        = ∫ z in B, ∫ x in Ioo 0 ℓ, tensorACFun W Ψ (x, z) *
            fderiv ℝ φ (x, z) ((1 : ℝ), (0 : EuclideanSpace ℝ (Fin m))) := by
          rw [← hmeas]; exact integral_prod_symm _ hintL
      _ = ∫ z in B, -∫ x in Ioo 0 ℓ, (deriv W.toFun x * Ψ.toFun z) * φ (x, z) :=
          integral_congr_ae (.of_forall key)
      _ = -∫ z in B, ∫ x in Ioo 0 ℓ, (deriv W.toFun x * Ψ.toFun z) * φ (x, z) := integral_neg _
      _ = -∫ p in Ioo 0 ℓ ×ˢ B, (deriv W.toFun p.1 * Ψ.toFun p.2) * φ p := by
          rw [← hmeas, integral_prod_symm _ hintR]
  · -- transverse identities
    intro i
    have hintL : Integrable (fun p : CapSpace m => tensorACFun W Ψ p *
        fderiv ℝ φ p ((0 : ℝ), EuclideanSpace.single i (1 : ℝ)))
        (volume.restrict (Ioo 0 ℓ ×ˢ B)) :=
      integrable_mul_dirDeriv hu hφ hφc _
    have hintR : Integrable
        (fun p : CapSpace m => (W.toFun p.1 • Ψ.grad p.2) i * φ p)
        (volume.restrict (Ioo 0 ℓ ×ˢ B)) :=
      integrable_compP_mul hgz hφ hφc i
    rw [← hmeas] at hintL hintR
    have key : ∀ x : ℝ,
        (∫ z in B, tensorACFun W Ψ (x, z) *
            fderiv ℝ φ (x, z) ((0 : ℝ), EuclideanSpace.single i (1 : ℝ)))
          = -∫ z in B, (W.toFun x • Ψ.grad z) i * φ (x, z) := by
      intro x
      have hgC : ContDiff ℝ ∞ fun w : EuclideanSpace ℝ (Fin m) => φ (x, w) :=
        hφ.comp (contDiff_const.prodMk contDiff_id)
      have hgc : HasCompactSupport fun w : EuclideanSpace ℝ (Fin m) => φ (x, w) :=
        hasCompactSupport_sliceSnd hφc x
      have hgs : tsupport (fun w : EuclideanSpace ℝ (Fin m) => φ (x, w)) ⊆ B :=
        (tsupport_sliceSnd_subset φ x).trans fun _ hz => (hφs hz).2
      have hw : (∫ z in B, Ψ.toFun z *
            fderiv ℝ (fun w : EuclideanSpace ℝ (Fin m) => φ (x, w)) z
              (EuclideanSpace.single i 1))
          = -∫ z in B, Ψ.grad z i * φ (x, z) :=
        Ψ.hasWeakGrad (fun w : EuclideanSpace ℝ (Fin m) => φ (x, w)) hgC hgc hgs i
      have h1 : (∫ z in B, tensorACFun W Ψ (x, z) *
            fderiv ℝ φ (x, z) ((0 : ℝ), EuclideanSpace.single i (1 : ℝ)))
          = W.toFun x * ∫ z in B, Ψ.toFun z *
              fderiv ℝ (fun w : EuclideanSpace ℝ (Fin m) => φ (x, w)) z
                (EuclideanSpace.single i 1) := by
        rw [← integral_const_mul]
        refine integral_congr_ae (.of_forall fun z => ?_)
        simp only [tensorACFun_apply, fderiv_sliceSnd hφ1 x z]
        ring
      have h2 : (∫ z in B, (W.toFun x • Ψ.grad z) i * φ (x, z))
          = W.toFun x * ∫ z in B, Ψ.grad z i * φ (x, z) := by
        rw [← integral_const_mul]
        refine integral_congr_ae (.of_forall fun z => ?_)
        simp only [PiLp.smul_apply, smul_eq_mul]
        ring
      rw [h1, h2, hw, mul_neg]
    calc (∫ p in Ioo 0 ℓ ×ˢ B, tensorACFun W Ψ p *
            fderiv ℝ φ p ((0 : ℝ), EuclideanSpace.single i (1 : ℝ)))
        = ∫ x in Ioo 0 ℓ, ∫ z in B, tensorACFun W Ψ (x, z) *
            fderiv ℝ φ (x, z) ((0 : ℝ), EuclideanSpace.single i (1 : ℝ)) := by
          rw [← hmeas]; exact integral_prod _ hintL
      _ = ∫ x in Ioo 0 ℓ, -∫ z in B, (W.toFun x • Ψ.grad z) i * φ (x, z) :=
          integral_congr_ae (.of_forall key)
      _ = -∫ x in Ioo 0 ℓ, ∫ z in B, (W.toFun x • Ψ.grad z) i * φ (x, z) := integral_neg _
      _ = -∫ p in Ioo 0 ℓ ×ˢ B, (W.toFun p.1 • Ψ.grad p.2) i * φ p := by
          rw [← hmeas, integral_prod _ hintR]

/-- **The tensor product `W ⊗ ψ` as an element of `H1P Ω`** for an absolutely continuous axial
factor `W ∈ RobinCaps.Sobolev.H1 ℓ` and a transverse factor `ψ ∈ H¹(B)`. -/
def H1P.tensorAC (hℓ : 0 < ℓ) (W : Sobolev.H1 ℓ) (Ψ : Sobolev.Weak.H1 B) :
    H1P (Ioo 0 ℓ ×ˢ B) where
  toFun := tensorACFun W Ψ
  gx := fun p => deriv W.toFun p.1 * Ψ.toFun p.2
  gz := fun p => W.toFun p.1 • Ψ.grad p.2
  memL2 := memLp_two_prodMul (memLp_two_h1_toFun hℓ W) Ψ.memL2
  gx_memL2 := memLp_two_prodMul (memLp_two_h1_deriv hℓ W) Ψ.memL2
  gz_memL2 := memLp_two_prodSmul (memLp_two_h1_toFun hℓ W) Ψ.grad_memL2
  hasWeakGrad := hasWeakGradP_tensorAC hℓ W Ψ

@[simp] theorem H1P.tensorAC_toFun (hℓ : 0 < ℓ) (W : Sobolev.H1 ℓ) (Ψ : Sobolev.Weak.H1 B) :
    (H1P.tensorAC hℓ W Ψ).toFun = tensorACFun W Ψ := rfl

/-- **The bulk projection of a tensor product is its axial factor**: with a normalised
transverse profile, `∫_B (W ⊗ ψ) (x, z) ψ z dz = W x`. -/
theorem axialCoeff_tensorAC (hℓ : 0 < ℓ) (W : Sobolev.H1 ℓ) (Ψ : Sobolev.Weak.H1 B)
    (hψ1 : ∫ z in B, Ψ.toFun z ^ 2 = 1) (x : ℝ) :
    axialCoeff B (H1P.tensorAC hℓ W Ψ).toFun Ψ.toFun x = W.toFun x := by
  show (∫ z in B, W.toFun x * Ψ.toFun z * Ψ.toFun z) = W.toFun x
  have h : (∫ z in B, W.toFun x * Ψ.toFun z * Ψ.toFun z)
      = W.toFun x * ∫ z in B, Ψ.toFun z ^ 2 := by
    rw [← integral_const_mul]
    refine integral_congr_ae (.of_forall fun z => ?_)
    ring
  rw [h, hψ1, mul_one]

/-- The bulk projection sends the class of `W ⊗ ψ` to the class of `W`. -/
theorem bulkProj_tensorAC (hℓ : 0 < ℓ) (hBo : IsOpen B) (hB : volume B ≠ ⊤)
    (Ψ : Sobolev.Weak.H1 B) (hψ1 : ∫ z in B, Ψ.toFun z ^ 2 = 1) (W : Sobolev.H1 ℓ) :
    bulkProj hℓ hBo hB Ψ.memL2 hψ1
        (Submodule.Quotient.mk (H1P.tensorAC hℓ W Ψ)) = Submodule.Quotient.mk W := by
  rw [bulkProj_mk]
  refine h1Q_mk_eq_of_eqOn hℓ.le (rep_eqOn_of_ae hℓ ?_)
  filter_upwards [bulkRep_ae hℓ hBo hB Ψ.memL2 hψ1 (H1P.tensorAC hℓ W Ψ)] with x hx
  rw [hx, axialCoeff_tensorAC hℓ W Ψ hψ1 x]

/-- **Surjectivity of the bulk projection** (`π` of `RobinCaps/Spectrum/MainAbstract.lean`):
every class in the one-dimensional quotient model is the bulk projection of a tensor trial
function `W ⊗ ψ`. -/
theorem bulkProj_surjective (hℓ : 0 < ℓ) (hBo : IsOpen B) (hB : volume B ≠ ⊤)
    (Ψ : Sobolev.Weak.H1 B) (hψ1 : ∫ z in B, Ψ.toFun z ^ 2 = 1) :
    Function.Surjective (bulkProj hℓ hBo hB Ψ.memL2 hψ1) := by
  intro q
  obtain ⟨W, rfl⟩ := Submodule.Quotient.mk_surjective (Sobolev.nullOff ℓ) q
  exact ⟨Submodule.Quotient.mk (H1P.tensorAC hℓ W Ψ), bulkProj_tensorAC hℓ hBo hB Ψ hψ1 W⟩

end BulkProj

/-! ## Item 5: restriction from the thin domain, and the composite projection -/

/-! ### The bulk projection on a general axial interval `(a,b)` -/

section Translate

variable {a b : ℝ} {B : Set (EuclideanSpace ℝ (Fin m))} {ψ : EuclideanSpace ℝ (Fin m) → ℝ}

/-- **Uniqueness of the translated representative on `[0,b-a]`.**  Two elements of
`Sobolev.H1 (b-a)` whose translates `x ↦ w (x-a)` agree a.e. on `(a,b)` agree everywhere on
`[0,b-a]`. -/
theorem repT_eqOn_of_ae (hab : a < b) {w₁ w₂ : Sobolev.H1 (b - a)}
    (h : (fun x => w₁.toFun (x - a)) =ᵐ[volume.restrict (Ioo a b)] fun x => w₂.toFun (x - a)) :
    EqOn w₁.toFun w₂.toFun (Icc 0 (b - a)) := by
  have hmaps : MapsTo (fun x : ℝ => x - a) (Icc a b) (Icc 0 (b - a)) := by
    intro x hx
    exact ⟨by linarith [hx.1], by linarith [hx.2]⟩
  have hcont : ∀ w : Sobolev.H1 (b - a),
      ContinuousOn (fun x : ℝ => w.toFun (x - a)) (Icc a b) := by
    intro w
    have h1 : ContinuousOn w.toFun (Icc 0 (b - a)) :=
      h1_continuousOn (by linarith) w
    exact h1.comp ((continuous_id.sub continuous_const).continuousOn) hmaps
  have hIcc : (fun x => w₁.toFun (x - a))
      =ᵐ[volume.restrict (Icc a b)] fun x => w₂.toFun (x - a) := by
    rwa [Measure.restrict_congr_set Ioo_ae_eq_Icc] at h
  have heq := Measure.eqOn_Icc_of_ae_eq volume (ne_of_lt hab) hIcc (hcont w₁) (hcont w₂)
  intro y hy
  have hya : y + a ∈ Icc a b := ⟨by linarith [hy.1], by linarith [hy.2]⟩
  simpa using heq hya

/-- **The translated bulk representative.**  For a cylinder over the general interval `(a,b)`,
the bulk projection is represented, after the translation `x ↦ x - a`, by an element of
`RobinCaps.Sobolev.H1 (b-a)` (`exists_h1_axialCoeff_translate`). -/
def bulkRepT (hab : a < b) (hBo : IsOpen B) (hB : volume B ≠ ⊤)
    (hψ : MemLp ψ 2 (volume.restrict B)) (hψ1 : ∫ z in B, ψ z ^ 2 = 1)
    (u : H1P (Ioo a b ×ˢ B)) : Sobolev.H1 (b - a) :=
  Classical.choose (exists_h1_axialCoeff_translate hab hBo hB u hψ hψ1)

theorem bulkRepT_ae (hab : a < b) (hBo : IsOpen B) (hB : volume B ≠ ⊤)
    (hψ : MemLp ψ 2 (volume.restrict B)) (hψ1 : ∫ z in B, ψ z ^ 2 = 1)
    (u : H1P (Ioo a b ×ˢ B)) :
    (fun x => (bulkRepT hab hBo hB hψ hψ1 u).toFun (x - a))
      =ᵐ[volume.restrict (Ioo a b)] axialCoeff B u.toFun ψ :=
  (Classical.choose_spec (exists_h1_axialCoeff_translate hab hBo hB u hψ hψ1)).1

theorem bulkRepT_deriv_ae (hab : a < b) (hBo : IsOpen B) (hB : volume B ≠ ⊤)
    (hψ : MemLp ψ 2 (volume.restrict B)) (hψ1 : ∫ z in B, ψ z ^ 2 = 1)
    (u : H1P (Ioo a b ×ˢ B)) :
    (fun x => deriv (bulkRepT hab hBo hB hψ hψ1 u).toFun (x - a))
      =ᵐ[volume.restrict (Ioo a b)] axialCoeff B u.gx ψ :=
  (Classical.choose_spec (exists_h1_axialCoeff_translate hab hBo hB u hψ hψ1)).2.1

theorem bulkRepT_dirichlet_le (hab : a < b) (hBo : IsOpen B) (hB : volume B ≠ ⊤)
    (hψ : MemLp ψ 2 (volume.restrict B)) (hψ1 : ∫ z in B, ψ z ^ 2 = 1)
    (u : H1P (Ioo a b ×ˢ B)) :
    Sobolev.dirichlet (b - a) (bulkRepT hab hBo hB hψ hψ1 u) ≤ dirichletP u :=
  (Classical.choose_spec (exists_h1_axialCoeff_translate hab hBo hB u hψ hψ1)).2.2

/-- The translated bulk projection as a linear map on `H1P (Ioo a b ×ˢ B)`. -/
def bulkRepTₗ (hab : a < b) (hBo : IsOpen B) (hB : volume B ≠ ⊤)
    (hψ : MemLp ψ 2 (volume.restrict B)) (hψ1 : ∫ z in B, ψ z ^ 2 = 1) :
    H1P (Ioo a b ×ˢ B) →ₗ[ℝ] Sobolev.H1Q (b - a) where
  toFun u := Submodule.Quotient.mk (bulkRepT hab hBo hB hψ hψ1 u)
  map_add' u v := by
    have hsum : (Submodule.Quotient.mk (bulkRepT hab hBo hB hψ hψ1 u)
          + Submodule.Quotient.mk (bulkRepT hab hBo hB hψ hψ1 v) : Sobolev.H1Q (b - a))
        = Submodule.Quotient.mk
            (bulkRepT hab hBo hB hψ hψ1 u + bulkRepT hab hBo hB hψ hψ1 v) := rfl
    rw [hsum]
    refine h1Q_mk_eq_of_eqOn (by linarith) (repT_eqOn_of_ae hab ?_)
    filter_upwards [bulkRepT_ae hab hBo hB hψ hψ1 (u + v), bulkRepT_ae hab hBo hB hψ hψ1 u,
      bulkRepT_ae hab hBo hB hψ hψ1 v,
      ae_axialCoeff_add (volume_Ioo_ne_top a b) hψ u v] with x h0 h1 h2 h3
    show (bulkRepT hab hBo hB hψ hψ1 (u + v)).toFun (x - a)
        = (bulkRepT hab hBo hB hψ hψ1 u).toFun (x - a)
          + (bulkRepT hab hBo hB hψ hψ1 v).toFun (x - a)
    rw [h0, h1, h2, h3]
  map_smul' c u := by
    have hsmul : (c • Submodule.Quotient.mk (bulkRepT hab hBo hB hψ hψ1 u) :
          Sobolev.H1Q (b - a))
        = Submodule.Quotient.mk (c • bulkRepT hab hBo hB hψ hψ1 u) := rfl
    show Submodule.Quotient.mk (bulkRepT hab hBo hB hψ hψ1 (c • u))
        = (RingHom.id ℝ) c • Submodule.Quotient.mk (bulkRepT hab hBo hB hψ hψ1 u)
    rw [RingHom.id_apply, hsmul]
    refine h1Q_mk_eq_of_eqOn (by linarith) (repT_eqOn_of_ae hab ?_)
    filter_upwards [bulkRepT_ae hab hBo hB hψ hψ1 (c • u), bulkRepT_ae hab hBo hB hψ hψ1 u]
      with x h0 h1
    show (bulkRepT hab hBo hB hψ hψ1 (c • u)).toFun (x - a)
        = c * (bulkRepT hab hBo hB hψ hψ1 u).toFun (x - a)
    rw [h0, h1, axialCoeff_smul_h1p c u x]

@[simp] theorem bulkRepTₗ_apply (hab : a < b) (hBo : IsOpen B) (hB : volume B ≠ ⊤)
    (hψ : MemLp ψ 2 (volume.restrict B)) (hψ1 : ∫ z in B, ψ z ^ 2 = 1)
    (u : H1P (Ioo a b ×ˢ B)) :
    bulkRepTₗ hab hBo hB hψ hψ1 u = Submodule.Quotient.mk (bulkRepT hab hBo hB hψ hψ1 u) :=
  rfl

/-- **The bulk projection on a general axial interval**, on the a.e. quotient. -/
def bulkProjT (hab : a < b) (hBo : IsOpen B) (hB : volume B ≠ ⊤)
    (hψ : MemLp ψ 2 (volume.restrict B)) (hψ1 : ∫ z in B, ψ z ^ 2 = 1) :
    H1PQ (Ioo a b ×ˢ B) →ₗ[ℝ] Sobolev.H1Q (b - a) := by
  refine Submodule.liftQ _ (bulkRepTₗ hab hBo hB hψ hψ1) ?_
  intro u hu
  show bulkRepTₗ hab hBo hB hψ hψ1 u = 0
  rw [bulkRepTₗ_apply]
  refine h1Q_mk_eq_zero_of_eqOn (by linarith) ?_
  have hz : (fun x => (bulkRepT hab hBo hB hψ hψ1 u).toFun (x - a))
      =ᵐ[volume.restrict (Ioo a b)] fun x => (0 : Sobolev.H1 (b - a)).toFun (x - a) := by
    filter_upwards [bulkRepT_ae hab hBo hB hψ hψ1 u,
      ae_axialCoeff_eq_zero_of_mem_nullAEP (ψ := ψ) hB hu] with x h1 h2
    show (bulkRepT hab hBo hB hψ hψ1 u).toFun (x - a) = 0
    rw [h1, h2]
  intro x hx
  simpa using repT_eqOn_of_ae hab hz hx

@[simp] theorem bulkProjT_mk (hab : a < b) (hBo : IsOpen B) (hB : volume B ≠ ⊤)
    (hψ : MemLp ψ 2 (volume.restrict B)) (hψ1 : ∫ z in B, ψ z ^ 2 = 1)
    (u : H1P (Ioo a b ×ˢ B)) :
    bulkProjT hab hBo hB hψ hψ1 (Submodule.Quotient.mk u)
      = Submodule.Quotient.mk (bulkRepT hab hBo hB hψ hψ1 u) := rfl

end Translate

/-! ### Restriction from the thin domain to the bulk cylinder -/

section Thin

variable {Cm Cp : RobinCaps.Cap m} {L R : ℝ}

/-- The transverse ball is open. -/
theorem isOpen_transverseBall : IsOpen (transverseBall m R) := Metric.isOpen_ball

/-- The transverse ball has finite volume. -/
theorem volume_transverseBall_ne_top : volume (transverseBall m R) ≠ ⊤ :=
  (measure_ball_lt_top).ne

/-- **The open bulk cylinder sits inside the thin domain**: on the bulk interval the radial
profile is constant equal to `R` (`RobinCaps.Domain.profile_bulk`). -/
theorem bulkCyl_subset_thinDomain (hR : 0 < R) :
    Ioo (-L/2 + Cm.K * R) (L/2 - Cp.K * R) ×ˢ transverseBall m R
      ⊆ Domain.thinDomain Cm Cp L R := by
  rintro ⟨x, z⟩ ⟨hx, hz⟩
  have hKm : 0 < Cm.K * R := mul_pos Cm.hK hR
  have hKp : 0 < Cp.K * R := mul_pos Cp.hK hR
  have hzR : ‖z‖ < R := by
    have : z ∈ Metric.ball (0 : EuclideanSpace ℝ (Fin m)) R := hz
    simpa [Metric.mem_ball, dist_zero_right] using this
  refine ⟨by simp only []; linarith [hx.1], by simp only []; linarith [hx.2], ?_⟩
  show ‖z‖ < Domain.profile Cm Cp L R x
  rw [Domain.profile_bulk (le_of_lt hx.1) (le_of_lt hx.2)]
  exact hzR

/-- **Restriction of an element of `H1P (Ω_R)` to the bulk cylinder** (`HasWeakGradP.mono`). -/
def restrictBulkP (hR : 0 < R) :
    H1P (Domain.thinDomain Cm Cp L R) →ₗ[ℝ]
      H1P (Ioo (-L/2 + Cm.K * R) (L/2 - Cp.K * R) ×ˢ transverseBall m R) where
  toFun u :=
    { toFun := u.toFun
      gx := u.gx
      gz := u.gz
      memL2 := u.memL2.mono_measure
        (Measure.restrict_mono (bulkCyl_subset_thinDomain hR) le_rfl)
      gx_memL2 := u.gx_memL2.mono_measure
        (Measure.restrict_mono (bulkCyl_subset_thinDomain hR) le_rfl)
      gz_memL2 := u.gz_memL2.mono_measure
        (Measure.restrict_mono (bulkCyl_subset_thinDomain hR) le_rfl)
      hasWeakGrad := u.hasWeakGrad.mono (bulkCyl_subset_thinDomain hR) }
  map_add' u v := H1P.ext rfl rfl rfl
  map_smul' c u := H1P.ext rfl rfl rfl

@[simp] theorem restrictBulkP_toFun (hR : 0 < R) (u : H1P (Domain.thinDomain Cm Cp L R)) :
    (restrictBulkP (Cm := Cm) (Cp := Cp) (L := L) hR u).toFun = u.toFun := rfl

/-- **The restriction descends to the a.e. quotients.** -/
def restrictBulkPQ (hR : 0 < R) :
    H1PQ (Domain.thinDomain Cm Cp L R) →ₗ[ℝ]
      H1PQ (Ioo (-L/2 + Cm.K * R) (L/2 - Cp.K * R) ×ˢ transverseBall m R) := by
  refine Submodule.liftQ _
    ((nullAEP (Ioo (-L/2 + Cm.K * R) (L/2 - Cp.K * R) ×ˢ transverseBall m R)).mkQ.comp
      (restrictBulkP hR)) ?_
  intro u hu
  have hu' : u.toFun =ᵐ[volume.restrict (Domain.thinDomain Cm Cp L R)] 0 := hu
  show Submodule.Quotient.mk (restrictBulkP hR u) = 0
  rw [Submodule.Quotient.mk_eq_zero]
  show (restrictBulkP hR u).toFun
      =ᵐ[volume.restrict (Ioo (-L/2 + Cm.K * R) (L/2 - Cp.K * R) ×ˢ transverseBall m R)] 0
  exact ae_restrict_of_ae_restrict_of_subset (bulkCyl_subset_thinDomain hR) hu'

@[simp] theorem restrictBulkPQ_mk (hR : 0 < R) (u : H1P (Domain.thinDomain Cm Cp L R)) :
    restrictBulkPQ (Cm := Cm) (Cp := Cp) (L := L) hR (Submodule.Quotient.mk u)
      = Submodule.Quotient.mk (restrictBulkP hR u) := rfl

/-- The bulk length `ℓ_R = L - (K₋ + K₊) R` is the length of the bulk interval. -/
theorem bulkLength_eq_sub :
    Domain.bulkLength Cm Cp L R = L/2 - Cp.K * R - (-L/2 + Cm.K * R) := by
  simp only [Domain.bulkLength]
  ring

/-- **The bulk projection from the thin domain** `Ω_R`: restrict to the bulk cylinder, then
project onto the axial profile.  The target is the quotient one-dimensional model on the bulk
interval of length `ℓ_R = bulkLength Cm Cp L R`. -/
def bulkProjThin {ψ : EuclideanSpace ℝ (Fin m) → ℝ} (hR : 0 < R)
    (hL : (Cm.K + Cp.K) * R < L)
    (hψ : MemLp ψ 2 (volume.restrict (transverseBall m R)))
    (hψ1 : ∫ z in transverseBall m R, ψ z ^ 2 = 1) :
    H1PQ (Domain.thinDomain Cm Cp L R) →ₗ[ℝ]
      Sobolev.H1Q (Domain.bulkLength Cm Cp L R) := by
  rw [bulkLength_eq_sub]
  exact (bulkProjT (Domain.interface_lt hR hL) isOpen_transverseBall
    volume_transverseBall_ne_top hψ hψ1).comp (restrictBulkPQ hR)

/-- **Target (`eq:trial-extension`).**  Surjectivity of the bulk projection *from the thin
domain*.  Unlike `bulkProj_surjective`, this cannot be obtained from a tensor product alone: a
one-dimensional profile `W` has to be extended from the bulk interval to the whole thin domain
by the **trial extension** of the manuscript (`eq:trial-extension`, constant continuation on the
two caps), which is being formalized in `RobinCaps/ThinDomain/Trial.lean`.  Given such an
extension `𝒯_R W ∈ H1P (Ω_R)` with `restrictBulkP (𝒯_R W) = (W ∘ (· - a)) ⊗ ψ` on the bulk
cylinder, this statement follows exactly as `bulkProj_surjective` does.  What *is* proved here
is the reduction `surjective_bulkProjT_comp`. -/
def BulkProjThinSurjective {ψ : EuclideanSpace ℝ (Fin m) → ℝ} (hR : 0 < R)
    (hL : (Cm.K + Cp.K) * R < L)
    (hψ : MemLp ψ 2 (volume.restrict (transverseBall m R)))
    (hψ1 : ∫ z in transverseBall m R, ψ z ^ 2 = 1) : Prop :=
  Function.Surjective (bulkProjThin hR hL hψ hψ1)

/-- **The reduction of item 5 to the trial extension.**  The composite of the restriction and of
the bulk projection on the bulk cylinder is surjective as soon as both factors are; the second
factor is the analogue on `(x₋,x₊)` of `bulkProj_surjective`, and the first one is exactly what
the trial extension provides. -/
theorem surjective_bulkProjT_comp {ψ : EuclideanSpace ℝ (Fin m) → ℝ} (hR : 0 < R)
    (hL : (Cm.K + Cp.K) * R < L)
    (hψ : MemLp ψ 2 (volume.restrict (transverseBall m R)))
    (hψ1 : ∫ z in transverseBall m R, ψ z ^ 2 = 1)
    (hrestr : Function.Surjective (restrictBulkPQ (Cm := Cm) (Cp := Cp) (L := L) hR))
    (hproj : Function.Surjective (bulkProjT (Domain.interface_lt hR hL) isOpen_transverseBall
      volume_transverseBall_ne_top hψ hψ1)) :
    Function.Surjective
      (((bulkProjT (Domain.interface_lt hR hL) isOpen_transverseBall
        volume_transverseBall_ne_top hψ hψ1).comp (restrictBulkPQ hR) :
          H1PQ (Domain.thinDomain Cm Cp L R) →ₗ[ℝ] _)) :=
  hproj.comp hrestr

end Thin


end

end RobinCaps.ThinDomain
