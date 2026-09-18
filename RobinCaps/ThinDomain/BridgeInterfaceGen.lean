import RobinCaps.ThinDomain.AssemblyOne
import RobinCaps.ThinDomain.InterfaceTrace
import RobinCaps.ThinDomain.ProfileEndpoint

/-!
# Discharging the interface-trace input, general transverse dimension `m`

This file is the general-`m` analogue of `RobinCaps/ThinDomain/BridgeInterfaceOne.lean`: it
assembles the interface-trace data of `eq:interval-trace` / `eq:cap-rescale` for an *abstract*
transverse ground state `gs : RobinCaps.ThinDomain.TransverseGroundState m α R bd` (in place of
the concrete `m = 1` ground state `psiOne_a1` used by `AssemblyOne.lean`), out of

* `RobinCaps/ThinDomain/InterfaceTrace.lean` — the interface traces `ifaceL`, `ifaceR` (already
  stated for general `m`), their measurability and their `L²(B_m(R))` bound
  `integral_ifaceL_sq_le` / `integral_ifaceR_sq_le` with the explicit constants `2/ℓ_R`, `2 ℓ_R`
  of the one-dimensional trace inequality on the bulk interval;
* `RobinCaps/ThinDomain/ProfileEndpoint.lean` — `eq:interval-trace`, the identification of the
  two endpoint values of *any* representative of `bulkProjThin ⟦u⟧` with the pairings
  `⟨ifaceL u, ψ⟩`, `⟨ifaceR u, ψ⟩` (`bulkProjThin_endpoint_left_pe` / `_right_pe`), applied to
  the representative `axialRep_big` built from an arbitrary normalised `ψ = gs.psi`
  (`bulkProjThin_mk_big`, via `bulkProjThin_mk_eq_pe`).

As in the `m = 1` bridge, the only new content beyond the two imported files is the
**uniformity in `R`**: restricting to `R < R₀ = L / (2 (K₋+K₊))` forces
`ℓ_R = L - (K₋+K₊) R ∈ (L/2, L]`, hence `2/ℓ_R ≤ 4/L` and `2 ℓ_R ≤ 2 L`, so the single constant
`C_if = max (4/L) (2L)` works for every admissible radius and every abstract ground state.

No `sorry`, `admit`, `axiom` or `native_decide` occurs in this file.
-/

open MeasureTheory Set Filter Metric

open scoped ENNReal Topology

noncomputable section

namespace RobinCaps.ThinDomain

open RobinCaps.Domain RobinCaps.Sobolev RobinCaps.Transverse

variable {m : ℕ} {Cm Cp : Cap m} {L R α : ℝ}
variable {bd : TransH1 m R →ₗ[ℝ] TransH1 m R →ₗ[ℝ] ℝ}

/-! ## 1.  The bulk mass and axial Dirichlet energy as cylinder integrals -/

/-- `N_bulk[u]` is the integral of `|u|²` over the (closed) bulk cylinder.  General-`m` analogue
of `massP_restrictBulkP_eq_bi`; the underlying lemma `setIntegral_bulkCylinder_it` is already
stated for general `m`. -/
theorem massP_restrictBulkP_eq_big (hR : 0 < R) (u : H1P (thinDomain Cm Cp L R)) :
    massP (restrictBulkP (Cm := Cm) (Cp := Cp) (L := L) hR u)
      = ∫ p in bulkCylinder Cm Cp L R, u.toFun p ^ 2 := by
  have h : massP (restrictBulkP (Cm := Cm) (Cp := Cp) (L := L) hR u)
      = ∫ p in bulkOpen Cm Cp L R, u.toFun p ^ 2 := rfl
  rw [h, ← setIntegral_bulkCylinder_it]

/-- `∫_bulk |∂ₓ u|²` is the integral of `|∂ₓ u|²` over the (closed) bulk cylinder.  General-`m`
analogue of `axialDirichletP_restrictBulkP_eq_bi`. -/
theorem axialDirichletP_restrictBulkP_eq_big (hR : 0 < R) (u : H1P (thinDomain Cm Cp L R)) :
    axialDirichletP (restrictBulkP (Cm := Cm) (Cp := Cp) (L := L) hR u)
      = ∫ p in bulkCylinder Cm Cp L R, u.gx p ^ 2 := by
  have h : axialDirichletP (restrictBulkP (Cm := Cm) (Cp := Cp) (L := L) hR u)
      = ∫ p in bulkOpen Cm Cp L R, u.gx p ^ 2 := rfl
  rw [h, ← setIntegral_bulkCylinder_it]

/-! ## 2.  The two interface traces are square integrable -/

theorem memLp_ifaceL_big (hR : 0 < R) (hL : (Cm.K + Cp.K) * R < L)
    (u : H1P (thinDomain Cm Cp L R)) :
    MemLp (ifaceL u) 2 (volume.restrict (transverseBall m R)) :=
  (memLp_two_iff_integrable_sq (measurable_ifaceL u).aestronglyMeasurable).2
    (integrableOn_ifaceL_sq hR hL u)

theorem memLp_ifaceR_big (hR : 0 < R) (hL : (Cm.K + Cp.K) * R < L)
    (u : H1P (thinDomain Cm Cp L R)) :
    MemLp (ifaceR u) 2 (volume.restrict (transverseBall m R)) :=
  (memLp_two_iff_integrable_sq (measurable_ifaceR u).aestronglyMeasurable).2
    (integrableOn_ifaceR_sq hR hL u)

/-! ## 3.  The abstract ground state: normalisation and the axial profile representative -/

/-- **`gs.psi` is `L²`-normalized as an honest integral.**  This is exactly the field
`gs.normalized : NB gs.psi = 1` (`NB = Weak.mass`), unfolded to the integral form that
`bulkRepT` / `profileRep_pe` expect — the general-`m` analogue of `psiOne_normalized_a1`. -/
theorem gs_normalized_big (gs : TransverseGroundState m α R bd) :
    ∫ z in transverseBall m R, gs.psi.toFun z ^ 2 = 1 :=
  psi_normalized_integral gs

/-- **The absolutely continuous representative of the axial profile `F`** built out of an
*abstract* transverse ground state `gs`, as an element of the concrete one-dimensional model on
the bulk interval `I_R` of length `ℓ_R = bulkLength Cm Cp L R`.  This is the representative of
`bulkProjThin u` (`bulkProjThin_mk_big`), so `F(x_∓)` are its endpoint values.  General-`m`
analogue of `axialRepOne_a1`. -/
def axialRep_big (hR : 0 < R) (hL : (Cm.K + Cp.K) * R < L) (gs : TransverseGroundState m α R bd)
    (u : H1P (thinDomain Cm Cp L R)) : Sobolev.H1 (bulkLength Cm Cp L R) :=
  (h1Congr (bulkLength_eq_sub (Cm := Cm) (Cp := Cp) (L := L) (R := R))).symm
    (profileRep_pe u hR hL gs.psi.memL2 (gs_normalized_big gs))

/-- **The bulk projection `π` of `RobinCaps/ThinDomain/BulkProj.lean`, computed for `gs.psi`.**
General-`m` analogue of `bulkProjThin_mk_a1`; it is exactly `bulkProjThin_mk_eq_pe` unfolded
along the definition of `axialRep_big`. -/
theorem bulkProjThin_mk_big (hR : 0 < R) (hL : (Cm.K + Cp.K) * R < L)
    (gs : TransverseGroundState m α R bd) (u : H1P (thinDomain Cm Cp L R)) :
    bulkProjThin hR hL gs.psi.memL2 (gs_normalized_big gs) (Submodule.Quotient.mk u)
      = Submodule.Quotient.mk (axialRep_big hR hL gs u) :=
  bulkProjThin_mk_eq_pe u hR hL gs.psi.memL2 (gs_normalized_big gs)

/-- **`eq:interval-trace`, left endpoint, for the abstract representative `axialRep_big`.** -/
theorem axialRep_endpoint_left_big (hR : 0 < R) (hL : (Cm.K + Cp.K) * R < L)
    (gs : TransverseGroundState m α R bd) (u : H1P (thinDomain Cm Cp L R)) :
    (axialRep_big hR hL gs u).toFun 0
      = ∫ z in transverseBall m R, ifaceL u z * gs.psi.toFun z :=
  bulkProjThin_endpoint_left_pe u hR hL gs.psi.memL2 (gs_normalized_big gs)
    (bulkProjThin_mk_big hR hL gs u).symm

/-- **`eq:interval-trace`, right endpoint, for the abstract representative `axialRep_big`.** -/
theorem axialRep_endpoint_right_big (hR : 0 < R) (hL : (Cm.K + Cp.K) * R < L)
    (gs : TransverseGroundState m α R bd) (u : H1P (thinDomain Cm Cp L R)) :
    (axialRep_big hR hL gs u).toFun (bulkLength Cm Cp L R)
      = ∫ z in transverseBall m R, ifaceR u z * gs.psi.toFun z :=
  bulkProjThin_endpoint_right_pe u hR hL gs.psi.memL2 (gs_normalized_big gs)
    (bulkProjThin_mk_big hR hL gs u).symm

/-! ### The `TransverseGroundStateReg` variant

`TransverseGroundStateReg` (`RobinCaps/ThinDomain/Trial.lean`) is a `TransverseGroundState`
together with extra regularity data, exposed through the field `toTransverseGroundState`.  Since
none of the above uses anything but the ground-state data proper, the regularised statements are
immediate corollaries. -/

theorem gsr_normalized_big (gsr : TransverseGroundStateReg m α R bd) :
    ∫ z in transverseBall m R, gsr.psi.toFun z ^ 2 = 1 :=
  gs_normalized_big gsr.toTransverseGroundState

/-- `axialRep_big` specialised to a regularised ground state. -/
def axialRepReg_big (hR : 0 < R) (hL : (Cm.K + Cp.K) * R < L)
    (gsr : TransverseGroundStateReg m α R bd) (u : H1P (thinDomain Cm Cp L R)) :
    Sobolev.H1 (bulkLength Cm Cp L R) :=
  axialRep_big hR hL gsr.toTransverseGroundState u

theorem axialRepReg_endpoint_left_big (hR : 0 < R) (hL : (Cm.K + Cp.K) * R < L)
    (gsr : TransverseGroundStateReg m α R bd) (u : H1P (thinDomain Cm Cp L R)) :
    (axialRepReg_big hR hL gsr u).toFun 0
      = ∫ z in transverseBall m R, ifaceL u z * gsr.psi.toFun z :=
  axialRep_endpoint_left_big hR hL gsr.toTransverseGroundState u

theorem axialRepReg_endpoint_right_big (hR : 0 < R) (hL : (Cm.K + Cp.K) * R < L)
    (gsr : TransverseGroundStateReg m α R bd) (u : H1P (thinDomain Cm Cp L R)) :
    (axialRepReg_big hR hL gsr u).toFun (bulkLength Cm Cp L R)
      = ∫ z in transverseBall m R, ifaceR u z * gsr.psi.toFun z :=
  axialRep_endpoint_right_big hR hL gsr.toTransverseGroundState u

/-! ## 4.  The `L²` bound with an arbitrary admissible constant -/

theorem integral_ifaceL_sq_le_const_big (hR : 0 < R) (hL : (Cm.K + Cp.K) * R < L)
    (u : H1P (thinDomain Cm Cp L R)) {Cif : ℝ}
    (h1 : 2 / bulkLength Cm Cp L R ≤ Cif) (h2 : 2 * bulkLength Cm Cp L R ≤ Cif) :
    (∫ z in transverseBall m R, ifaceL u z ^ 2)
      ≤ Cif * (massP (restrictBulkP hR u) + axialDirichletP (restrictBulkP hR u)) := by
  have hM : (0 : ℝ) ≤ ∫ p in bulkCylinder Cm Cp L R, u.toFun p ^ 2 :=
    integral_nonneg fun _ => sq_nonneg _
  have hG : (0 : ℝ) ≤ ∫ p in bulkCylinder Cm Cp L R, u.gx p ^ 2 :=
    integral_nonneg fun _ => sq_nonneg _
  have h := integral_ifaceL_sq_le hR hL u
  rw [massP_restrictBulkP_eq_big hR u, axialDirichletP_restrictBulkP_eq_big hR u,
    show transverseBall m R = ball (0 : EuclideanSpace ℝ (Fin m)) R from rfl]
  have e1 := mul_le_mul_of_nonneg_right h1 hM
  have e2 := mul_le_mul_of_nonneg_right h2 hG
  linarith

theorem integral_ifaceR_sq_le_const_big (hR : 0 < R) (hL : (Cm.K + Cp.K) * R < L)
    (u : H1P (thinDomain Cm Cp L R)) {Cif : ℝ}
    (h1 : 2 / bulkLength Cm Cp L R ≤ Cif) (h2 : 2 * bulkLength Cm Cp L R ≤ Cif) :
    (∫ z in transverseBall m R, ifaceR u z ^ 2)
      ≤ Cif * (massP (restrictBulkP hR u) + axialDirichletP (restrictBulkP hR u)) := by
  have hM : (0 : ℝ) ≤ ∫ p in bulkCylinder Cm Cp L R, u.toFun p ^ 2 :=
    integral_nonneg fun _ => sq_nonneg _
  have hG : (0 : ℝ) ≤ ∫ p in bulkCylinder Cm Cp L R, u.gx p ^ 2 :=
    integral_nonneg fun _ => sq_nonneg _
  have h := integral_ifaceR_sq_le hR hL u
  rw [massP_restrictBulkP_eq_big hR u, axialDirichletP_restrictBulkP_eq_big hR u,
    show transverseBall m R = ball (0 : EuclideanSpace ℝ (Fin m)) R from rfl]
  have e1 := mul_le_mul_of_nonneg_right h1 hM
  have e2 := mul_le_mul_of_nonneg_right h2 hG
  linarith

/-! ## 5.  The witness at a single radius, for an abstract ground state -/

/-- **The interface-trace data at one admissible radius, for an abstract transverse ground
state `gs`.**  General-`m` analogue of `exists_iface_bi`. -/
theorem exists_iface_big (hR : 0 < R) (hL : (Cm.K + Cp.K) * R < L)
    (gs : TransverseGroundState m α R bd) (u : H1P (thinDomain Cm Cp L R)) {Cif : ℝ}
    (h1 : 2 / bulkLength Cm Cp L R ≤ Cif) (h2 : 2 * bulkLength Cm Cp L R ≤ Cif) :
    ∃ fm fp : EuclideanSpace ℝ (Fin m) → ℝ,
      MemLp fm 2 (volume.restrict (transverseBall m R)) ∧
      MemLp fp 2 (volume.restrict (transverseBall m R)) ∧
      (axialRep_big hR hL gs u).toFun 0
        = ∫ z in transverseBall m R, fm z * gs.psi.toFun z ∧
      (axialRep_big hR hL gs u).toFun (bulkLength Cm Cp L R)
        = ∫ z in transverseBall m R, fp z * gs.psi.toFun z ∧
      (∫ z in transverseBall m R, fm z ^ 2)
        ≤ Cif * (massP (restrictBulkP hR u) + axialDirichletP (restrictBulkP hR u)) ∧
      (∫ z in transverseBall m R, fp z ^ 2)
        ≤ Cif * (massP (restrictBulkP hR u) + axialDirichletP (restrictBulkP hR u)) :=
  ⟨ifaceL u, ifaceR u, memLp_ifaceL_big hR hL u, memLp_ifaceR_big hR hL u,
    axialRep_endpoint_left_big hR hL gs u, axialRep_endpoint_right_big hR hL gs u,
    integral_ifaceL_sq_le_const_big hR hL u h1 h2,
    integral_ifaceR_sq_le_const_big hR hL u h1 h2⟩

/-! ## 6.  The general-`m` interface-trace interface, monotonicity, and the final statement -/

/-- **`eq:interval-trace` / `eq:cap-rescale`, general transverse dimension `m`: the entrance
pairing is the endpoint value of the axial profile, for *every* abstract transverse ground
state `gs`.**

This mirrors `RobinCaps.ThinDomain.InterfaceTraceInput_a1` (the `m = 1` interface consumed by
`RobinCaps/ThinDomain/AssemblyOne.lean`), generalised to arbitrary `m`, arbitrary boundary form
`bd` and arbitrary transverse ground state `gs`. -/
structure InterfaceTraceInput_big (m : ℕ) (Cm Cp : Cap m) (L α : ℝ) (hα : 0 < α)
    (Cif R₀ : ℝ) : Prop where
  /-- The two interface values and their two properties, for every admissible radius, every
  boundary form `bd` and every transverse ground state `gs` for that `bd`. -/
  iface : ∀ (R : ℝ) (hR : 0 < R), R < R₀ → ∀ (hL : (Cm.K + Cp.K) * R < L)
      (bd : TransH1 m R →ₗ[ℝ] TransH1 m R →ₗ[ℝ] ℝ) (gs : TransverseGroundState m α R bd)
      (u : H1P (thinDomain Cm Cp L R)),
    ∃ fm fp : EuclideanSpace ℝ (Fin m) → ℝ,
      MemLp fm 2 (volume.restrict (transverseBall m R)) ∧
      MemLp fp 2 (volume.restrict (transverseBall m R)) ∧
      (axialRep_big hR hL gs u).toFun 0
        = ∫ z in transverseBall m R, fm z * gs.psi.toFun z ∧
      (axialRep_big hR hL gs u).toFun (bulkLength Cm Cp L R)
        = ∫ z in transverseBall m R, fp z * gs.psi.toFun z ∧
      (∫ z in transverseBall m R, fm z ^ 2)
        ≤ Cif * (massP (restrictBulkP hR u) + axialDirichletP (restrictBulkP hR u)) ∧
      (∫ z in transverseBall m R, fp z ^ 2)
        ≤ Cif * (massP (restrictBulkP hR u) + axialDirichletP (restrictBulkP hR u))

/-- **`InterfaceTraceInput_big` is monotone in the radius threshold.** -/
theorem interfaceTraceInput_le_big {hα : 0 < α} {Cif R₀ R₀' : ℝ}
    (h : InterfaceTraceInput_big m Cm Cp L α hα Cif R₀) (hle : R₀' ≤ R₀) :
    InterfaceTraceInput_big m Cm Cp L α hα Cif R₀' :=
  ⟨fun R hR hR0 hL bd gs u => h.iface R hR (lt_of_lt_of_le hR0 hle) hL bd gs u⟩

/-- **`InterfaceTraceInput_big` holds, with `C_if = max (4/L) (2L)` and
`R₀ = L / (2 (K₋ + K₊))`, uniformly in the transverse dimension `m`, the boundary form `bd` and
the transverse ground state `gs`.**

Same proof as `interfaceTraceInput_one_bi`: for `0 < R < R₀` the bulk length
`ℓ_R = L - (K₋+K₊) R` lies in `(L/2, L]`, so the two explicit constants `2/ℓ_R`, `2 ℓ_R` of the
one-dimensional trace inequality (`RobinCaps.ThinDomain.integral_ifaceL_sq_le`) are bounded by
`4/L` and `2L` uniformly in the radius. -/
theorem interfaceTraceInput_gen_big (m : ℕ) (Cm Cp : Cap m) (L α : ℝ) (hα : 0 < α)
    (hL0 : 0 < L) :
    ∃ Cif R₀ : ℝ, 0 ≤ Cif ∧ 0 < R₀ ∧ InterfaceTraceInput_big m Cm Cp L α hα Cif R₀ := by
  have hK : (0 : ℝ) < Cm.K + Cp.K := add_pos Cm.hK Cp.hK
  refine ⟨max (4 / L) (2 * L), L / (2 * (Cm.K + Cp.K)),
    le_max_of_le_right (by linarith), div_pos hL0 (by linarith),
    ⟨fun R hR hR0 hL bd gs u => ?_⟩⟩
  have hbl : bulkLength Cm Cp L R = L - (Cm.K + Cp.K) * R := rfl
  have hKR : (Cm.K + Cp.K) * R < L / 2 := by
    have hlt := mul_lt_mul_of_pos_left hR0 hK
    have heq : (Cm.K + Cp.K) * (L / (2 * (Cm.K + Cp.K))) = L / 2 := by
      field_simp
    rwa [heq] at hlt
  have hℓ : 0 < bulkLength Cm Cp L R := by rw [hbl]; linarith
  have hℓub : bulkLength Cm Cp L R ≤ L := by
    rw [hbl]; nlinarith [mul_pos hK hR]
  have h1 : 2 / bulkLength Cm Cp L R ≤ max (4 / L) (2 * L) := by
    refine le_max_of_le_left ?_
    rw [div_le_div_iff₀ hℓ hL0, hbl]
    linarith
  have h2 : 2 * bulkLength Cm Cp L R ≤ max (4 / L) (2 * L) :=
    le_max_of_le_right (by linarith)
  exact exists_iface_big hR hL gs u h1 h2

/-! ## 7.  Consistency with the `m = 1` bridge `BridgeInterfaceOne.lean` -/

/-- **`interfaceTraceInput_gen_big`, specialised to `m = 1`, `bd := bdTr R`,
`gs := groundStateOne α R hα hR`, recovers the body of `InterfaceTraceInput_a1.iface` at one
radius verbatim** — `axialRep_big hR hL (groundStateOne α R hα hR) u` unfolds definitionally to
`axialRepOne_a1 hR hL hα u` (both are `(h1Congr bulkLength_eq_sub).symm` applied to the same
`bulkRepT` term, since `psiOne_a1 α R hα hR = (groundStateOne α R hα hR).psi` by definition and
`gs_normalized_big` / `psiOne_normalized_a1` are two proofs of the same proposition, hence equal
by proof irrelevance), and likewise `gs.psi.toFun = (psiOne_a1 α R hα hR).toFun`.  So this
instance is a **direct (definitional) instantiation** of `exists_iface_big`, not merely a
provable consequence. -/
theorem exists_iface_one_of_big (Cm Cp : Cap 1) (hR : 0 < R) (hL : (Cm.K + Cp.K) * R < L)
    (hα : 0 < α) (u : H1P (thinDomain Cm Cp L R)) {Cif : ℝ}
    (h1 : 2 / bulkLength Cm Cp L R ≤ Cif) (h2 : 2 * bulkLength Cm Cp L R ≤ Cif) :
    ∃ fm fp : EuclideanSpace ℝ (Fin 1) → ℝ,
      MemLp fm 2 (volume.restrict (transverseBall 1 R)) ∧
      MemLp fp 2 (volume.restrict (transverseBall 1 R)) ∧
      (axialRepOne_a1 hR hL hα u).toFun 0
        = ∫ z in transverseBall 1 R, fm z * (psiOne_a1 α R hα hR).toFun z ∧
      (axialRepOne_a1 hR hL hα u).toFun (bulkLength Cm Cp L R)
        = ∫ z in transverseBall 1 R, fp z * (psiOne_a1 α R hα hR).toFun z ∧
      (∫ z in transverseBall 1 R, fm z ^ 2)
        ≤ Cif * (massP (restrictBulkP hR u) + axialDirichletP (restrictBulkP hR u)) ∧
      (∫ z in transverseBall 1 R, fp z ^ 2)
        ≤ Cif * (massP (restrictBulkP hR u) + axialDirichletP (restrictBulkP hR u)) :=
  exists_iface_big hR hL (groundStateOne α R hα hR) u h1 h2

/-- **`InterfaceTraceInput_a1` is a direct instance of `InterfaceTraceInput_big` at `m = 1`.** -/
theorem interfaceTraceInput_one_of_big (Cm Cp : Cap 1) {L α Cif R₀ : ℝ} {hα : 0 < α}
    (h : InterfaceTraceInput_big 1 Cm Cp L α hα Cif R₀) :
    InterfaceTraceInput_a1 Cm Cp L α hα Cif R₀ :=
  ⟨fun R hR hR0 hL u => h.iface R hR hR0 hL (bdTr R) (groundStateOne α R hα hR) u⟩

/-- **`interfaceTraceInput_one_bi`, re-derived from `interfaceTraceInput_gen_big`.** -/
theorem interfaceTraceInput_one_of_gen_big (Cm Cp : Cap 1) (L α : ℝ) (hα : 0 < α)
    (hL0 : 0 < L) :
    ∃ Cif R₀ : ℝ, 0 ≤ Cif ∧ 0 < R₀ ∧ InterfaceTraceInput_a1 Cm Cp L α hα Cif R₀ := by
  obtain ⟨Cif, R₀, hCif, hR₀, h⟩ := interfaceTraceInput_gen_big 1 Cm Cp L α hα hL0
  exact ⟨Cif, R₀, hCif, hR₀, interfaceTraceInput_one_of_big Cm Cp h⟩

end RobinCaps.ThinDomain

end
