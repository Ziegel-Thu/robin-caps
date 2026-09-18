import RobinCaps.ThinDomain.InterfaceTrace
import RobinCaps.ThinDomain.TrialAC

/-!
# The endpoint values of the axial profile (`eq:interval-trace`)

For `u ∈ H¹(Ω_R)` (the weak product model `H1P`) and a normalised transverse profile `ψ ∈
L²(B_m(R))` the manuscript's **axial profile** is

`F (x) = ∫_B u (x, z) ψ (z) dz`,

an absolutely continuous function on the bulk interval `[x₋, x₊]` whose concrete representative
in `RobinCaps.Sobolev.H1 ℓ_R` is the one produced by `RobinCaps.ThinDomain.bulkRepT` (and used
by `RobinCaps.ThinDomain.bulkProjThin`); here it is named `profileRep_pe`.  This file proves
the manuscript's `eq:interval-trace`: the two **endpoint values** of `F` are the pairings of the
interface traces `ifaceL u`, `ifaceR u` of `RobinCaps/ThinDomain/InterfaceTrace.lean` with `ψ`,

`F (x₋) = ∫_B ifaceL u · ψ`,     `F (x₊) = ∫_B ifaceR u · ψ`.

## Contents

1. `integral_slicePrim0_mul_pe` — the Fubini interchange `∫_B (∫_{x₋}^{x} ∂ₓu (t,z) dt) ψ (z) dz
   = ∫_{x₋}^{x} (∫_B ∂ₓu (t,z) ψ (z) dz) dt`, from the integrability of `(t,z) ↦ ∂ₓu (t,z) ψ (z)`
   on the finite-measure cylinder `(x₋,x) ×ˢ B` (`integrable_mul_psi_snd`).
2. `profileRep_pe`, `profileRep_ae_pe`, `profileRep_deriv_ae_pe`, `profileRep_ftc_pe` — the
   profile representative and its fundamental theorem of calculus, written on `[x₋, x₊]`.
3. `ifaceDefect_pe`, `ae_ae_ifaceDefect_pe`, `ae_ae_ifaceDefect_swap_pe` — the interface
   reconstruction `u (x,z) = ifaceL u z + ∫_{x₋}^{x} ∂ₓu (t,z) dt` of
   `RobinCaps.ThinDomain.ifaceL_spec`, transported to the globally measurable representatives
   `repFunT` / `slicePrim0` so that the two almost-everywhere quantifiers may be exchanged
   (`MeasureTheory.Measure.ae_ae_comm`).
4. `profileEndpoint_left_pe`, `profileEndpoint_right_pe` — **the two endpoint identities**.
   The constant is identified by evaluating the reconstruction at one good abscissa `x` of the
   bulk interval, where both the profile's own reconstruction (item 2) and the interface
   reconstruction (item 3) hold; the right endpoint then follows from
   `RobinCaps.ThinDomain.ifaceR_eq_ifaceL_add_it`.
5. `profile_eq_integral_iface_pe` — the explicit almost-everywhere form of the profile.
6. `bulkProjThin_mk_eq_pe`, `bulkProjThin_endpoint_left_pe`, `bulkProjThin_endpoint_right_pe`
   — the same statements for *any* representative `W ∈ Sobolev.H1 ℓ_R` of the quotient-level
   bulk projection `bulkProjThin ⟦u⟧` (representatives of one class agree everywhere on
   `[0, ℓ_R]`, since `nullOff ℓ` consists of the functions vanishing on `[0,ℓ]`).
7. `sq_integral_ifaceL_mul_le_pe`, `profileEndpoint_left_sq_le_pe` (and the right analogues)
   — the Cauchy–Schwarz consequence `F (x₋)² ≤ ∫_B |ifaceL u|²` for a normalised `ψ`.

No `sorry`, `admit`, `axiom` or `native_decide` occurs in this file.

## A remark on imports

`RobinCaps/ThinDomain/InterfaceTrace.lean` (which imports through `Slice.lean`) and
`RobinCaps/ThinDomain/TrialAC.lean` (which imports through `AxialCoeff.lean` and `BulkProj.lean`)
are imported together; the `prodTest` name clash mentioned in `BulkEnergy.lean` no longer
occurs, `Slice.lean` using the name `prodTestS`.
-/

open MeasureTheory Set Filter Metric

open scoped ENNReal Topology

namespace RobinCaps.ThinDomain

open RobinCaps.Domain RobinCaps.Sobolev

noncomputable section

variable {m : ℕ} {Cm Cp : RobinCaps.Cap m} {L R : ℝ}
variable {ψ : EuclideanSpace ℝ (Fin m) → ℝ}

/-! ## 0.  Elementary reformulations -/

theorem transverseBall_eq_ball_pe :
    transverseBall m R = ball (0 : EuclideanSpace ℝ (Fin m)) R := rfl

theorem interfaceL_eq_pe : interfaceL Cm L R = -L / 2 + Cm.K * R := rfl

theorem interfaceR_eq_pe : interfaceR Cp L R = L / 2 - Cp.K * R := rfl

/-- A sub-cylinder of the bulk cylinder sits inside the thin domain. -/
theorem cyl_subset_thin_pe (hR : 0 < R) {a b : ℝ} (ha : interfaceL Cm L R ≤ a)
    (hb : b ≤ interfaceR Cp L R) :
    Ioo a b ×ˢ transverseBall m R ⊆ thinDomain Cm Cp L R :=
  (Set.prod_mono (Ioo_subset_Ioo ha hb) (subset_refl _)).trans
    (bulkCyl_subset_thinDomain (Cm := Cm) (Cp := Cp) (L := L) hR)

variable (u : H1P (thinDomain Cm Cp L R))

theorem memLp_repFunT_pe (hR : 0 < R) {a b : ℝ} (ha : interfaceL Cm L R ≤ a)
    (hb : b ≤ interfaceR Cp L R) :
    MemLp (repFunT u) 2 (volume.restrict (Ioo a b ×ˢ transverseBall m R)) :=
  (MemLp.ae_eq u.memL2.aestronglyMeasurable.ae_eq_mk u.memL2).mono_measure
    (Measure.restrict_mono (cyl_subset_thin_pe hR ha hb) le_rfl)

theorem memLp_repGxT_pe (hR : 0 < R) {a b : ℝ} (ha : interfaceL Cm L R ≤ a)
    (hb : b ≤ interfaceR Cp L R) :
    MemLp (repGxT u) 2 (volume.restrict (Ioo a b ×ˢ transverseBall m R)) :=
  (MemLp.ae_eq u.gx_memL2.aestronglyMeasurable.ae_eq_mk u.gx_memL2).mono_measure
    (Measure.restrict_mono (cyl_subset_thin_pe hR ha hb) le_rfl)

/-- Almost-everywhere statements on `Ioo a b` transfer to `Ioc a c` for `c ≤ b`. -/
theorem ae_restrict_Ioc_of_Ioo_pe {a b c : ℝ} (hc : c ≤ b) {P : ℝ → Prop}
    (h : ∀ᵐ t ∂(volume.restrict (Ioo a b)), P t) :
    ∀ᵐ t ∂(volume.restrict (Ioc a c)), P t := by
  have h1 : ∀ᵐ t ∂(volume.restrict (Ioc a b)), P t := by
    rwa [Measure.restrict_congr_set Ioo_ae_eq_Ioc] at h
  exact ae_restrict_of_ae_restrict_of_subset (Ioc_subset_Ioc le_rfl hc) h1

/-! ## 1.  The transverse pairing of the axial primitive -/

/-- **Fubini for the axial primitive.**  Pairing the axial primitive
`(x,z) ↦ ∫_{x₋}^{x} ∂ₓu (t,z) dt` with `ψ` in the transverse variable is the same as pairing
`∂ₓu` with `ψ` first and integrating in `t` afterwards. -/
theorem integral_slicePrim0_mul_pe (hR : 0 < R)
    (hψ : MemLp ψ 2 (volume.restrict (transverseBall m R)))
    {x : ℝ} (hx₁ : interfaceL Cm L R ≤ x) (hx₂ : x ≤ interfaceR Cp L R) :
    (∫ z in transverseBall m R, slicePrim0 (interfaceL Cm L R) u (x, z) * ψ z)
      = ∫ t in (interfaceL Cm L R)..x,
          ∫ z in transverseBall m R, repGxT u (t, z) * ψ z := by
  have hint : Integrable (fun p : CapSpace m => repGxT u p * ψ p.2)
      (volume.restrict (Ioo (interfaceL Cm L R) x ×ˢ transverseBall m R)) :=
    integrable_mul_psi_snd (volume_Ioo_ne_top _ _) (memLp_repGxT_pe u hR le_rfl hx₂) hψ
  rw [← volume_restrict_prod] at hint
  have hswap := MeasureTheory.integral_integral_swap
    (f := fun (t : ℝ) (z : EuclideanSpace ℝ (Fin m)) => repGxT u (t, z) * ψ z) hint
  rw [Sobolev.intervalIntegral_eq_setIntegral_Ioo hx₁, hswap]
  refine integral_congr_ae (Eventually.of_forall fun z => ?_)
  show slicePrim0 (interfaceL Cm L R) u (x, z) * ψ z
      = ∫ t in Ioo (interfaceL Cm L R) x, repGxT u (t, z) * ψ z
  rw [integral_mul_const, slicePrim0_eq_it,
    Sobolev.intervalIntegral_eq_setIntegral_Ioo hx₁]

/-- For almost every `t` the transverse pairing of the measurable representative of `∂ₓu` is
the axial coefficient of `∂ₓu`. -/
theorem ae_integral_repGxT_mul_pe (hR : 0 < R) (ψ : EuclideanSpace ℝ (Fin m) → ℝ) :
    ∀ᵐ t ∂(volume.restrict (Ioo (interfaceL Cm L R) (interfaceR Cp L R))),
      (∫ z in transverseBall m R, repGxT u (t, z) * ψ z)
        = axialCoeff (transverseBall m R) u.gx ψ t := by
  have hae : repGxT u
      =ᵐ[volume.restrict (Ioo (interfaceL Cm L R) (interfaceR Cp L R)
          ×ˢ transverseBall m R)] u.gx :=
    ae_restrict_of_ae_restrict_of_subset (cyl_subset_thin_pe hR le_rfl le_rfl)
      u.gx_memL2.aestronglyMeasurable.ae_eq_mk.symm
  rw [← volume_restrict_prod] at hae
  filter_upwards [Measure.ae_ae_of_ae_prod hae] with t ht
  refine integral_congr_ae ?_
  filter_upwards [ht] with z hz
  rw [hz]

/-! ## 2.  The axial profile representative and its reconstruction identity -/

/-- **The axial profile representative.**  This is the element of the concrete one-dimensional
model `RobinCaps.Sobolev.H1 ℓ_R` produced by `RobinCaps.ThinDomain.bulkRepT` out of the
restriction of `u` to the bulk cylinder: the (absolutely continuous representative of the)
axial profile `F (x) = ∫_B u (x,z) ψ (z) dz`, read on `[0, ℓ_R]` through the translation
`x ↦ x - x₋`.  It is the representative underlying `RobinCaps.ThinDomain.bulkProjThin`. -/
def profileRep_pe (hR : 0 < R) (hL : (Cm.K + Cp.K) * R < L)
    (hψ : MemLp ψ 2 (volume.restrict (transverseBall m R)))
    (hψ1 : ∫ z in transverseBall m R, ψ z ^ 2 = 1) :
    Sobolev.H1 (interfaceR Cp L R - interfaceL Cm L R) :=
  bulkRepT (Domain.interface_lt hR hL) isOpen_transverseBall volume_transverseBall_ne_top
    hψ hψ1 (restrictBulkP hR u)

variable (hR : 0 < R) (hL : (Cm.K + Cp.K) * R < L)
    (hψ : MemLp ψ 2 (volume.restrict (transverseBall m R)))
    (hψ1 : ∫ z in transverseBall m R, ψ z ^ 2 = 1)

/-- The profile representative represents the axial profile. -/
theorem profileRep_ae_pe :
    (fun x => (profileRep_pe u hR hL hψ hψ1).toFun (x - interfaceL Cm L R))
      =ᵐ[volume.restrict (Ioo (interfaceL Cm L R) (interfaceR Cp L R))]
        axialCoeff (transverseBall m R) u.toFun ψ :=
  bulkRepT_ae (Domain.interface_lt hR hL) isOpen_transverseBall volume_transverseBall_ne_top
    hψ hψ1 (restrictBulkP hR u)

/-- The derivative of the profile representative is the axial profile of `∂ₓu`. -/
theorem profileRep_deriv_ae_pe :
    (fun x => deriv (profileRep_pe u hR hL hψ hψ1).toFun (x - interfaceL Cm L R))
      =ᵐ[volume.restrict (Ioo (interfaceL Cm L R) (interfaceR Cp L R))]
        axialCoeff (transverseBall m R) u.gx ψ :=
  bulkRepT_deriv_ae (Domain.interface_lt hR hL) isOpen_transverseBall
    volume_transverseBall_ne_top hψ hψ1 (restrictBulkP hR u)

/-- **The profile representative is reconstructed from its derivative on the bulk interval.**
This is the one-dimensional fundamental theorem of calculus of `RobinCaps.Sobolev.H1`, written
back on the untranslated bulk interval `[x₋, x₊]`. -/
theorem profileRep_ftc_pe {x : ℝ} (hx1 : interfaceL Cm L R ≤ x)
    (hx2 : x ≤ interfaceR Cp L R) :
    (profileRep_pe u hR hL hψ hψ1).toFun (x - interfaceL Cm L R)
      = (profileRep_pe u hR hL hψ hψ1).toFun 0
        + ∫ t in (interfaceL Cm L R)..x, axialCoeff (transverseBall m R) u.gx ψ t := by
  have hftc := (profileRep_pe u hR hL hψ hψ1).ftc (x - interfaceL Cm L R)
    ⟨by linarith, by linarith⟩
  have hcomp : (∫ t in (interfaceL Cm L R)..x,
        deriv (profileRep_pe u hR hL hψ hψ1).toFun (t - interfaceL Cm L R))
      = ∫ s in (0 : ℝ)..(x - interfaceL Cm L R),
          deriv (profileRep_pe u hR hL hψ hψ1).toFun s := by
    simp
  have hcongr : (∫ t in (interfaceL Cm L R)..x,
        deriv (profileRep_pe u hR hL hψ hψ1).toFun (t - interfaceL Cm L R))
      = ∫ t in (interfaceL Cm L R)..x, axialCoeff (transverseBall m R) u.gx ψ t := by
    refine intervalIntegral.integral_congr_ae ?_
    rw [← ae_restrict_iff' measurableSet_uIoc, uIoc_of_le hx1]
    exact ae_restrict_Ioc_of_Ioo_pe hx2 (profileRep_deriv_ae_pe u hR hL hψ hψ1)
  rw [hftc, ← hcomp, hcongr]

/-- **Deliverable 1.**  For almost every `x` in the bulk interval the axial profile is the
pairing of the left interface trace with `ψ` plus the integral of the axial profile of
`∂ₓu`. -/
theorem axialCoeff_eq_add_integral_pe :
    ∀ᵐ x ∂(volume.restrict (Ioo (interfaceL Cm L R) (interfaceR Cp L R))),
      axialCoeff (transverseBall m R) u.toFun ψ x
        = (profileRep_pe u hR hL hψ hψ1).toFun 0
          + ∫ t in (interfaceL Cm L R)..x, axialCoeff (transverseBall m R) u.gx ψ t := by
  filter_upwards [profileRep_ae_pe u hR hL hψ hψ1, ae_restrict_mem measurableSet_Ioo]
    with x hx hxmem
  have hx' : (profileRep_pe u hR hL hψ hψ1).toFun (x - interfaceL Cm L R)
      = axialCoeff (transverseBall m R) u.toFun ψ x := hx
  rw [← hx', profileRep_ftc_pe u hR hL hψ hψ1 hxmem.1.le hxmem.2.le]

/-! ## 3.  The interface reconstruction, almost everywhere on the bulk cylinder -/

/-- The defect of the interface reconstruction `u (x,z) = ifaceL u z + ∫_{x₋}^x ∂ₓu (t,z) dt`,
written with the globally strongly measurable representatives of `RobinCaps.ThinDomain.repFunT`
and `RobinCaps.ThinDomain.slicePrim0` so as to be measurable on the product. -/
def ifaceDefect_pe (p : CapSpace m) : ℝ :=
  repFunT u p - slicePrim0 (interfaceL Cm L R) u p - ifaceL u p.2

theorem stronglyMeasurable_ifaceDefect_pe : StronglyMeasurable (ifaceDefect_pe u) :=
  ((stronglyMeasurable_repFunT u).sub (stronglyMeasurable_slicePrim0_it _ u)).sub
    ((measurable_ifaceL u).stronglyMeasurable.comp_measurable measurable_snd)

include hR hL in
/-- **The defect vanishes on almost every axial line of the bulk** — this is
`RobinCaps.ThinDomain.ifaceL_spec` transported to the measurable representatives. -/
theorem ae_ae_ifaceDefect_pe :
    ∀ᵐ z ∂(volume.restrict (ball (0 : EuclideanSpace ℝ (Fin m)) R)),
      ∀ᵐ x ∂(volume.restrict (Ioo (interfaceL Cm L R) (interfaceR Cp L R))),
        ifaceDefect_pe u (x, z) = 0 := by
  filter_upwards [ifaceL_spec hR hL u,
    ae_restrict_of_ae (ae_slice_repFunT_it hR hL u),
    ae_restrict_of_ae (ae_slice_repGxT_it hR hL u),
    ae_restrict_mem measurableSet_ball] with z hspec hrf hrg hzb
  have hznorm : ‖z‖ < R := mem_ball_zero_iff.1 hzb
  have hmemthin : ∀ x : ℝ, x ∈ Ioo (interfaceL Cm L R) (interfaceR Cp L R) →
      (x, z) ∈ thinDomain Cm Cp L R := fun x hx =>
    bulkOpen_subset_thinDomain hR hL ((mem_bulkOpen_iff (p := (x, z))).2 ⟨⟨hx.1, hx.2⟩, hznorm⟩)
  have hprim : ∀ x ∈ Ioo (interfaceL Cm L R) (interfaceR Cp L R),
      slicePrim0 (interfaceL Cm L R) u (x, z)
        = ∫ t in (interfaceL Cm L R)..x, u.gx (t, z) := by
    intro x hx
    rw [slicePrim0_eq_it]
    refine intervalIntegral.integral_congr_ae ?_
    filter_upwards [hrg, ae_ne_pair_it (interfaceL Cm L R) (interfaceR Cp L R)]
      with t ht htne htmem
    have htIcc : t ∈ Icc (interfaceL Cm L R) (interfaceR Cp L R) := by
      rw [Set.mem_uIoc] at htmem
      rcases htmem with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;>
        exact ⟨by linarith [hx.1, hx.2], by linarith [hx.1, hx.2]⟩
    exact ht (hmemthin t ⟨lt_of_le_of_ne htIcc.1 (Ne.symm htne.1),
      lt_of_le_of_ne htIcc.2 htne.2⟩)
  have hsub : Ioo (interfaceL Cm L R) (interfaceR Cp L R)
      ⊆ Ioo (aZ Cm Cp L R z) (bZ Cm Cp L R z) :=
    Ioo_interface_subset_axialSlice_it hR hL hznorm
  filter_upwards [hspec.filter_mono (ae_mono (Measure.restrict_mono hsub le_rfl)),
    ae_restrict_of_ae hrf, ae_restrict_mem measurableSet_Ioo] with x hx1 hx2 hx3
  show repFunT u (x, z) - slicePrim0 (interfaceL Cm L R) u (x, z) - ifaceL u z = 0
  rw [hx2 (hmemthin x hx3), hprim x hx3, hx1]
  ring

include hR hL in
/-- **The same statement with the two almost-everywhere quantifiers exchanged**
(`MeasureTheory.Measure.ae_ae_comm`, legitimate because the defect is measurable). -/
theorem ae_ae_ifaceDefect_swap_pe :
    ∀ᵐ x ∂(volume.restrict (Ioo (interfaceL Cm L R) (interfaceR Cp L R))),
      ∀ᵐ z ∂(volume.restrict (ball (0 : EuclideanSpace ℝ (Fin m)) R)),
        ifaceDefect_pe u (x, z) = 0 := by
  have hm : Measurable fun q : ℝ × EuclideanSpace ℝ (Fin m) => ifaceDefect_pe u (q.1, q.2) :=
    (stronglyMeasurable_ifaceDefect_pe u).measurable
  exact (Measure.ae_ae_comm (p := fun (x : ℝ) (z : EuclideanSpace ℝ (Fin m)) =>
    ifaceDefect_pe u (x, z) = 0) (hm (measurableSet_singleton 0))).2
      (ae_ae_ifaceDefect_pe u hR hL)

/-! ## 4.  The left endpoint value of the profile -/

theorem ae_transverseBall_iff_pe {P : EuclideanSpace ℝ (Fin m) → Prop} :
    (∀ᵐ z ∂(volume.restrict (transverseBall m R)), P z)
      ↔ ∀ᵐ z ∂(volume.restrict (ball (0 : EuclideanSpace ℝ (Fin m)) R)), P z := Iff.rfl

theorem ae_ae_repFunT_pe (hR : 0 < R) :
    ∀ᵐ x ∂(volume.restrict (Ioo (interfaceL Cm L R) (interfaceR Cp L R))),
      ∀ᵐ z ∂(volume.restrict (transverseBall m R)), repFunT u (x, z) = u.toFun (x, z) := by
  have hae : repFunT u
      =ᵐ[volume.restrict (Ioo (interfaceL Cm L R) (interfaceR Cp L R)
          ×ˢ transverseBall m R)] u.toFun :=
    ae_restrict_of_ae_restrict_of_subset (cyl_subset_thin_pe hR le_rfl le_rfl)
      u.memL2.aestronglyMeasurable.ae_eq_mk.symm
  rw [← volume_restrict_prod] at hae
  exact Measure.ae_ae_of_ae_prod hae

include hR hL hψ in
/-- The pairing of the left interface trace with `ψ` is integrable. -/
theorem integrable_ifaceL_mul_pe :
    Integrable (fun z => ifaceL u z * ψ z) (volume.restrict (transverseBall m R)) := by
  have hL2 : MemLp (ifaceL u) 2
      (volume.restrict (ball (0 : EuclideanSpace ℝ (Fin m)) R)) :=
    (memLp_two_iff_integrable_sq (measurable_ifaceL u).aestronglyMeasurable).2
      (integrableOn_ifaceL_sq hR hL u)
  simpa using hL2.integrable_mul hψ

include hR hL hψ hψ1 in
/-- **The left endpoint value of the axial profile is the pairing of the left interface trace
with `ψ`** (`eq:interval-trace`). -/
theorem profileEndpoint_left_pe :
    (profileRep_pe u hR hL hψ hψ1).toFun 0
      = ∫ z in transverseBall m R, ifaceL u z * ψ z := by
  have hab : interfaceL Cm L R < interfaceR Cp L R := interfaceL_lt_interfaceR_it hR hL
  have hifaceInt := integrable_ifaceL_mul_pe u hR hL hψ
  have hslice := ae_integrable_slice_mul (I := Ioo (interfaceL Cm L R) (interfaceR Cp L R))
    (volume_Ioo_ne_top _ _) (memLp_repFunT_pe u hR le_rfl le_rfl) hψ
  have hne : (volume.restrict (Ioo (interfaceL Cm L R) (interfaceR Cp L R))) ≠ 0 := by
    intro h
    have h0 : (volume.restrict (Ioo (interfaceL Cm L R) (interfaceR Cp L R)))
        (univ : Set ℝ) = 0 := by rw [h]; rfl
    rw [Measure.restrict_apply_univ, Real.volume_Ioo, ENNReal.ofReal_eq_zero] at h0
    linarith
  haveI : (ae (volume.restrict (Ioo (interfaceL Cm L R) (interfaceR Cp L R)))).NeBot :=
    ae_neBot.2 hne
  obtain ⟨x, hxF, hxD, hxR, hxS, hxmem⟩ :=
    ((axialCoeff_eq_add_integral_pe u hR hL hψ hψ1).and
      ((ae_ae_ifaceDefect_swap_pe u hR hL).and
        ((ae_ae_repFunT_pe u hR).and
          (hslice.and (ae_restrict_mem measurableSet_Ioo))))).exists
  have hx1 : interfaceL Cm L R ≤ x := hxmem.1.le
  have hx2 : x ≤ interfaceR Cp L R := hxmem.2.le
  have hxD' : ∀ᵐ z ∂(volume.restrict (transverseBall m R)),
      repFunT u (x, z) - slicePrim0 (interfaceL Cm L R) u (x, z) - ifaceL u z = 0 :=
    ae_transverseBall_iff_pe.2 hxD
  have hprimInt : Integrable (fun z => slicePrim0 (interfaceL Cm L R) u (x, z) * ψ z)
      (volume.restrict (transverseBall m R)) := by
    refine (hxS.sub hifaceInt).congr ?_
    filter_upwards [hxD'] with z hz
    have h4 : repFunT u (x, z) - ifaceL u z
        = slicePrim0 (interfaceL Cm L R) u (x, z) := by linarith
    show repFunT u (x, z) * ψ z - ifaceL u z * ψ z
        = slicePrim0 (interfaceL Cm L R) u (x, z) * ψ z
    rw [← sub_mul, h4]
  have key : axialCoeff (transverseBall m R) u.toFun ψ x
      = (∫ z in transverseBall m R, ifaceL u z * ψ z)
        + ∫ z in transverseBall m R, slicePrim0 (interfaceL Cm L R) u (x, z) * ψ z := by
    have hz : ∀ᵐ z ∂(volume.restrict (transverseBall m R)),
        u.toFun (x, z) * ψ z
          = ifaceL u z * ψ z + slicePrim0 (interfaceL Cm L R) u (x, z) * ψ z := by
      filter_upwards [hxD', hxR] with z hz1 hz2
      have h3 : u.toFun (x, z)
          = ifaceL u z + slicePrim0 (interfaceL Cm L R) u (x, z) := by
        rw [← hz2]; linarith
      rw [h3]; ring
    simp only [axialCoeff]
    rw [integral_congr_ae hz, integral_add hifaceInt hprimInt]
  rw [integral_slicePrim0_mul_pe u hR hψ hx1 hx2] at key
  have hgx : (∫ t in (interfaceL Cm L R)..x,
        ∫ z in transverseBall m R, repGxT u (t, z) * ψ z)
      = ∫ t in (interfaceL Cm L R)..x, axialCoeff (transverseBall m R) u.gx ψ t := by
    refine intervalIntegral.integral_congr_ae ?_
    rw [← ae_restrict_iff' measurableSet_uIoc, uIoc_of_le hx1]
    exact ae_restrict_Ioc_of_Ioo_pe hx2 (ae_integral_repGxT_mul_pe u hR ψ)
  rw [hgx, hxF] at key
  linarith

/-! ## 5.  The right endpoint value of the profile -/

include hR hL in
/-- For almost every `z` in the transverse ball the axial primitive of `RobinCaps.ThinDomain`
is the interval integral of `∂ₓu` along the axial line. -/
theorem ae_slicePrim0_eq_pe {x : ℝ} (hx1 : interfaceL Cm L R ≤ x)
    (hx2 : x ≤ interfaceR Cp L R) :
    ∀ᵐ z ∂(volume.restrict (ball (0 : EuclideanSpace ℝ (Fin m)) R)),
      slicePrim0 (interfaceL Cm L R) u (x, z)
        = ∫ t in (interfaceL Cm L R)..x, u.gx (t, z) := by
  filter_upwards [ae_restrict_of_ae (ae_slice_repGxT_it hR hL u),
    ae_restrict_mem measurableSet_ball] with z hrg hzb
  have hznorm : ‖z‖ < R := mem_ball_zero_iff.1 hzb
  have hmemthin : ∀ t : ℝ, t ∈ Ioo (interfaceL Cm L R) (interfaceR Cp L R) →
      (t, z) ∈ thinDomain Cm Cp L R := fun t ht =>
    bulkOpen_subset_thinDomain hR hL ((mem_bulkOpen_iff (p := (t, z))).2 ⟨⟨ht.1, ht.2⟩, hznorm⟩)
  rw [slicePrim0_eq_it]
  refine intervalIntegral.integral_congr_ae ?_
  filter_upwards [hrg, ae_ne_pair_it (interfaceL Cm L R) (interfaceR Cp L R)]
    with t ht htne htmem
  have htIcc : t ∈ Icc (interfaceL Cm L R) (interfaceR Cp L R) := by
    rw [Set.mem_uIoc] at htmem
    rcases htmem with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> exact ⟨by linarith, by linarith⟩
  exact ht (hmemthin t ⟨lt_of_le_of_ne htIcc.1 (Ne.symm htne.1),
    lt_of_le_of_ne htIcc.2 htne.2⟩)

include hR hL hψ in
/-- The pairing of the right interface trace with `ψ` is integrable. -/
theorem integrable_ifaceR_mul_pe :
    Integrable (fun z => ifaceR u z * ψ z) (volume.restrict (transverseBall m R)) := by
  have hL2 : MemLp (ifaceR u) 2
      (volume.restrict (ball (0 : EuclideanSpace ℝ (Fin m)) R)) :=
    (memLp_two_iff_integrable_sq (measurable_ifaceR u).aestronglyMeasurable).2
      (integrableOn_ifaceR_sq hR hL u)
  simpa using hL2.integrable_mul hψ

include hR hL hψ hψ1 in
/-- **The right endpoint value of the axial profile is the pairing of the right interface trace
with `ψ`** (`eq:interval-trace`). -/
theorem profileEndpoint_right_pe :
    (profileRep_pe u hR hL hψ hψ1).toFun (interfaceR Cp L R - interfaceL Cm L R)
      = ∫ z in transverseBall m R, ifaceR u z * ψ z := by
  have hab : interfaceL Cm L R < interfaceR Cp L R := interfaceL_lt_interfaceR_it hR hL
  have hifaceInt := integrable_ifaceL_mul_pe u hR hL hψ
  have hifaceRInt := integrable_ifaceR_mul_pe u hR hL hψ
  have hdiff : ∀ᵐ z ∂(volume.restrict (transverseBall m R)),
      ifaceR u z * ψ z - ifaceL u z * ψ z
        = slicePrim0 (interfaceL Cm L R) u (interfaceR Cp L R, z) * ψ z := by
    filter_upwards [ae_transverseBall_iff_pe.2 (ifaceR_eq_ifaceL_add_it hR hL u),
      ae_transverseBall_iff_pe.2 (ae_slicePrim0_eq_pe u hR hL hab.le le_rfl)] with z h1 h2
    rw [h1, h2]; ring
  have hprimInt : Integrable
      (fun z => slicePrim0 (interfaceL Cm L R) u (interfaceR Cp L R, z) * ψ z)
      (volume.restrict (transverseBall m R)) := by
    refine (hifaceRInt.sub hifaceInt).congr ?_
    filter_upwards [hdiff] with z hz
    show ifaceR u z * ψ z - ifaceL u z * ψ z
        = slicePrim0 (interfaceL Cm L R) u (interfaceR Cp L R, z) * ψ z
    exact hz
  have hsplit : (∫ z in transverseBall m R, ifaceR u z * ψ z)
      = (∫ z in transverseBall m R, ifaceL u z * ψ z)
        + ∫ z in transverseBall m R,
            slicePrim0 (interfaceL Cm L R) u (interfaceR Cp L R, z) * ψ z := by
    rw [← integral_add hifaceInt hprimInt]
    refine integral_congr_ae ?_
    filter_upwards [hdiff] with z hz
    show ifaceR u z * ψ z
        = ifaceL u z * ψ z + slicePrim0 (interfaceL Cm L R) u (interfaceR Cp L R, z) * ψ z
    linarith
  have hgx : (∫ t in (interfaceL Cm L R)..(interfaceR Cp L R),
        ∫ z in transverseBall m R, repGxT u (t, z) * ψ z)
      = ∫ t in (interfaceL Cm L R)..(interfaceR Cp L R),
          axialCoeff (transverseBall m R) u.gx ψ t := by
    refine intervalIntegral.integral_congr_ae ?_
    rw [← ae_restrict_iff' measurableSet_uIoc, uIoc_of_le hab.le]
    exact ae_restrict_Ioc_of_Ioo_pe le_rfl (ae_integral_repGxT_mul_pe u hR ψ)
  rw [hsplit, integral_slicePrim0_mul_pe u hR hψ hab.le le_rfl, hgx,
    profileRep_ftc_pe u hR hL hψ hψ1 hab.le le_rfl, profileEndpoint_left_pe u hR hL hψ hψ1]

/-! ## 6.  Deliverable 1 in explicit form -/

include hR hL hψ hψ1 in
/-- **The manuscript's `eq:interval-trace`, first half.**  For almost every `x` in the bulk
interval the axial profile `F (x) = ∫_B u (x,z) ψ (z) dz` is the pairing of the *left interface
trace* with `ψ` plus the flux integral. -/
theorem profile_eq_integral_iface_pe :
    ∀ᵐ x ∂(volume.restrict (Ioo (interfaceL Cm L R) (interfaceR Cp L R))),
      (∫ z in ball (0 : EuclideanSpace ℝ (Fin m)) R, u.toFun (x, z) * ψ z)
        = (∫ z in ball (0 : EuclideanSpace ℝ (Fin m)) R, ifaceL u z * ψ z)
          + ∫ t in (interfaceL Cm L R)..x,
              ∫ z in ball (0 : EuclideanSpace ℝ (Fin m)) R, u.gx (t, z) * ψ z := by
  filter_upwards [axialCoeff_eq_add_integral_pe u hR hL hψ hψ1] with x hx
  rw [← transverseBall_eq_ball_pe (m := m) (R := R),
    ← profileEndpoint_left_pe u hR hL hψ hψ1]
  exact hx

/-! ## 7.  The endpoint values of any representative of `bulkProjThin` -/

/-- Two elements of `Sobolev.H1 ℓ` with the same class in `Sobolev.H1Q ℓ` agree on `[0,ℓ]`. -/
theorem h1Q_eqOn_of_mk_eq_pe {ℓ : ℝ} (hℓ : 0 ≤ ℓ) {W V : Sobolev.H1 ℓ}
    (h : (Submodule.Quotient.mk W : Sobolev.H1Q ℓ) = Submodule.Quotient.mk V) :
    EqOn W.toFun V.toFun (Icc 0 ℓ) := by
  rw [Submodule.Quotient.eq] at h
  intro x hx
  have hx' := Sobolev.mem_nullOff.1 h x (by rwa [uIcc_of_le hℓ])
  rw [h1_sub_toFun] at hx'
  have hx'' : W.toFun x - V.toFun x = 0 := hx'
  linarith

theorem h1QCongr_symm_mk_pe {ℓ ℓ' : ℝ} (e : ℓ = ℓ') (W : Sobolev.H1 ℓ') :
    (h1QCongr e).symm (Submodule.Quotient.mk W)
      = (Submodule.Quotient.mk ((h1Congr e).symm W) : Sobolev.H1Q ℓ) := by
  subst e; rfl

theorem h1Congr_symm_toFun_pe {ℓ ℓ' : ℝ} (e : ℓ = ℓ') (W : Sobolev.H1 ℓ') :
    ((h1Congr e).symm W).toFun = W.toFun := by subst e; rfl

include hR hL hψ hψ1 in
/-- **The class of the profile representative is the bulk projection.** -/
theorem bulkProjThin_mk_eq_pe :
    bulkProjThin hR hL hψ hψ1 (Submodule.Quotient.mk u)
      = Submodule.Quotient.mk
          ((h1Congr (bulkLength_eq_sub (Cm := Cm) (Cp := Cp) (L := L) (R := R))).symm
            (profileRep_pe u hR hL hψ hψ1)) := by
  rw [bulkProjThin_eq hR hL hψ hψ1]
  simp only [LinearMap.comp_apply, restrictBulkPQ_mk, bulkProjT_mk, LinearEquiv.coe_coe]
  rw [h1QCongr_symm_mk_pe]
  rfl

include hR hL hψ hψ1 in
/-- **`eq:interval-trace`, left endpoint, at the level of the quotient bulk projection.**
*Every* representative `W` of `bulkProjThin ⟦u⟧` takes at `0` the value
`∫_B ifaceL u · ψ`. -/
theorem bulkProjThin_endpoint_left_pe {W : Sobolev.H1 (bulkLength Cm Cp L R)}
    (hW : (Submodule.Quotient.mk W : Sobolev.H1Q (bulkLength Cm Cp L R))
      = bulkProjThin hR hL hψ hψ1 (Submodule.Quotient.mk u)) :
    W.toFun 0 = ∫ z in transverseBall m R, ifaceL u z * ψ z := by
  have hℓ : 0 < bulkLength Cm Cp L R := bulkLength_pos_it hR hL
  rw [bulkProjThin_mk_eq_pe u hR hL hψ hψ1] at hW
  have h0 := h1Q_eqOn_of_mk_eq_pe hℓ.le hW (left_mem_Icc.2 hℓ.le)
  rw [h0, h1Congr_symm_toFun_pe]
  exact profileEndpoint_left_pe u hR hL hψ hψ1

include hR hL hψ hψ1 in
/-- **`eq:interval-trace`, right endpoint, at the level of the quotient bulk projection.** -/
theorem bulkProjThin_endpoint_right_pe {W : Sobolev.H1 (bulkLength Cm Cp L R)}
    (hW : (Submodule.Quotient.mk W : Sobolev.H1Q (bulkLength Cm Cp L R))
      = bulkProjThin hR hL hψ hψ1 (Submodule.Quotient.mk u)) :
    W.toFun (bulkLength Cm Cp L R) = ∫ z in transverseBall m R, ifaceR u z * ψ z := by
  have hℓ : 0 < bulkLength Cm Cp L R := bulkLength_pos_it hR hL
  rw [bulkProjThin_mk_eq_pe u hR hL hψ hψ1] at hW
  have h0 := h1Q_eqOn_of_mk_eq_pe hℓ.le hW (right_mem_Icc.2 hℓ.le)
  rw [h0, h1Congr_symm_toFun_pe, bulkLength_eq_sub_it]
  exact profileEndpoint_right_pe u hR hL hψ hψ1

/-! ## 8.  The Cauchy–Schwarz consequence -/

include hR hL hψ in
/-- **Cauchy–Schwarz for the interface pairing.** -/
theorem sq_integral_ifaceL_mul_le_pe :
    (∫ z in transverseBall m R, ifaceL u z * ψ z) ^ 2
      ≤ (∫ z in transverseBall m R, ifaceL u z ^ 2)
        * ∫ z in transverseBall m R, ψ z ^ 2 :=
  sq_integral_mul_le_mul (integrableOn_ifaceL_sq hR hL u)
    (integrable_ifaceL_mul_pe u hR hL hψ) (integrable_psi_sq hψ)

include hR hL hψ hψ1 in
/-- **The endpoint bound `F (x₋)² ≤ ∫_B |ifaceL u|²`** for a normalised transverse profile. -/
theorem profileEndpoint_left_sq_le_pe :
    ((profileRep_pe u hR hL hψ hψ1).toFun 0) ^ 2
      ≤ ∫ z in transverseBall m R, ifaceL u z ^ 2 := by
  rw [profileEndpoint_left_pe u hR hL hψ hψ1]
  have h := sq_integral_ifaceL_mul_le_pe u hR hL hψ
  rwa [hψ1, mul_one] at h

include hR hL hψ in
/-- **Cauchy–Schwarz for the interface pairing** (right interface). -/
theorem sq_integral_ifaceR_mul_le_pe :
    (∫ z in transverseBall m R, ifaceR u z * ψ z) ^ 2
      ≤ (∫ z in transverseBall m R, ifaceR u z ^ 2)
        * ∫ z in transverseBall m R, ψ z ^ 2 :=
  sq_integral_mul_le_mul (integrableOn_ifaceR_sq hR hL u)
    (integrable_ifaceR_mul_pe u hR hL hψ) (integrable_psi_sq hψ)

include hR hL hψ hψ1 in
/-- **The endpoint bound `F (x₊)² ≤ ∫_B |ifaceR u|²`** for a normalised transverse profile. -/
theorem profileEndpoint_right_sq_le_pe :
    ((profileRep_pe u hR hL hψ hψ1).toFun
        (interfaceR Cp L R - interfaceL Cm L R)) ^ 2
      ≤ ∫ z in transverseBall m R, ifaceR u z ^ 2 := by
  rw [profileEndpoint_right_pe u hR hL hψ hψ1]
  have h := sq_integral_ifaceR_mul_le_pe u hR hL hψ
  rwa [hψ1, mul_one] at h

end

end RobinCaps.ThinDomain
