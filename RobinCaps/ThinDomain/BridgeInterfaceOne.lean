import RobinCaps.ThinDomain.AssemblyOne
import RobinCaps.ThinDomain.InterfaceTrace
import RobinCaps.ThinDomain.ProfileEndpoint

/-!
# Discharging `InterfaceTraceInput_a1`

This file is a pure bridge: it assembles the interface-trace interface
`RobinCaps.ThinDomain.InterfaceTraceInput_a1` of
`RobinCaps/ThinDomain/AssemblyOne.lean` out of

* `RobinCaps/ThinDomain/InterfaceTrace.lean` — the interface traces `ifaceL`, `ifaceR`, their
  measurability and their `L²(B_1(R))` bound `integral_ifaceL_sq_le` with the explicit
  constants `2/ℓ_R`, `2 ℓ_R` of the one-dimensional trace inequality on the bulk interval;
* `RobinCaps/ThinDomain/ProfileEndpoint.lean` — `eq:interval-trace`, the identification of the
  two endpoint values of *any* representative of `bulkProjThin ⟦u⟧` with the pairings
  `⟨ifaceL u, ψ⟩`, `⟨ifaceR u, ψ⟩` (`bulkProjThin_endpoint_left_pe` / `_right_pe`), applied to
  the representative `axialRepOne_a1` through `bulkProjThin_mk_a1`.

The only new content is the **uniformity in `R`**: restricting to `R < R₀ = L / (2 (K₋+K₊))`
forces `ℓ_R = L - (K₋+K₊) R ∈ (L/2, L]`, hence `2/ℓ_R ≤ 4/L` and `2 ℓ_R ≤ 2 L`, so the single
constant `C_if = max (4/L) (2L)` works for every admissible radius.

No `sorry`, `admit`, `axiom` or `native_decide` occurs in this file.
-/

open MeasureTheory Set Filter Metric

open scoped ENNReal Topology

noncomputable section

namespace RobinCaps.ThinDomain

open RobinCaps.Domain RobinCaps.Sobolev

variable {Cm Cp : Cap 1} {L R α : ℝ}

/-! ## 1.  The bulk mass and axial Dirichlet energy as cylinder integrals -/

/-- `N_bulk[u]` is the integral of `|u|²` over the (closed) bulk cylinder. -/
theorem massP_restrictBulkP_eq_bi (hR : 0 < R) (u : H1P (thinDomain Cm Cp L R)) :
    massP (restrictBulkP (Cm := Cm) (Cp := Cp) (L := L) hR u)
      = ∫ p in bulkCylinder Cm Cp L R, u.toFun p ^ 2 := by
  have h : massP (restrictBulkP (Cm := Cm) (Cp := Cp) (L := L) hR u)
      = ∫ p in bulkOpen Cm Cp L R, u.toFun p ^ 2 := rfl
  rw [h, ← setIntegral_bulkCylinder_it]

/-- `∫_bulk |∂ₓ u|²` is the integral of `|∂ₓ u|²` over the (closed) bulk cylinder. -/
theorem axialDirichletP_restrictBulkP_eq_bi (hR : 0 < R) (u : H1P (thinDomain Cm Cp L R)) :
    axialDirichletP (restrictBulkP (Cm := Cm) (Cp := Cp) (L := L) hR u)
      = ∫ p in bulkCylinder Cm Cp L R, u.gx p ^ 2 := by
  have h : axialDirichletP (restrictBulkP (Cm := Cm) (Cp := Cp) (L := L) hR u)
      = ∫ p in bulkOpen Cm Cp L R, u.gx p ^ 2 := rfl
  rw [h, ← setIntegral_bulkCylinder_it]

/-! ## 2.  The two interface traces are square integrable -/

theorem memLp_ifaceL_bi (hR : 0 < R) (hL : (Cm.K + Cp.K) * R < L)
    (u : H1P (thinDomain Cm Cp L R)) :
    MemLp (ifaceL u) 2 (volume.restrict (transverseBall 1 R)) :=
  (memLp_two_iff_integrable_sq (measurable_ifaceL u).aestronglyMeasurable).2
    (integrableOn_ifaceL_sq hR hL u)

theorem memLp_ifaceR_bi (hR : 0 < R) (hL : (Cm.K + Cp.K) * R < L)
    (u : H1P (thinDomain Cm Cp L R)) :
    MemLp (ifaceR u) 2 (volume.restrict (transverseBall 1 R)) :=
  (memLp_two_iff_integrable_sq (measurable_ifaceR u).aestronglyMeasurable).2
    (integrableOn_ifaceR_sq hR hL u)

/-! ## 3.  The endpoint values of `axialRepOne_a1` -/

/-- **`eq:interval-trace`, left endpoint, for the representative used by `AssemblyOne`.** -/
theorem axialRepOne_endpoint_left_bi (hR : 0 < R) (hL : (Cm.K + Cp.K) * R < L) (hα : 0 < α)
    (u : H1P (thinDomain Cm Cp L R)) :
    (axialRepOne_a1 hR hL hα u).toFun 0
      = ∫ z in transverseBall 1 R, ifaceL u z * (psiOne_a1 α R hα hR).toFun z :=
  bulkProjThin_endpoint_left_pe u hR hL (psiOne_a1 α R hα hR).memL2
    (psiOne_normalized_a1 hα hR) (bulkProjThin_mk_a1 hR hL hα u).symm

/-- **`eq:interval-trace`, right endpoint, for the representative used by `AssemblyOne`.** -/
theorem axialRepOne_endpoint_right_bi (hR : 0 < R) (hL : (Cm.K + Cp.K) * R < L) (hα : 0 < α)
    (u : H1P (thinDomain Cm Cp L R)) :
    (axialRepOne_a1 hR hL hα u).toFun (bulkLength Cm Cp L R)
      = ∫ z in transverseBall 1 R, ifaceR u z * (psiOne_a1 α R hα hR).toFun z :=
  bulkProjThin_endpoint_right_pe u hR hL (psiOne_a1 α R hα hR).memL2
    (psiOne_normalized_a1 hα hR) (bulkProjThin_mk_a1 hR hL hα u).symm

/-! ## 4.  The `L²` bound with an arbitrary admissible constant -/

theorem integral_ifaceL_sq_le_const_bi (hR : 0 < R) (hL : (Cm.K + Cp.K) * R < L)
    (u : H1P (thinDomain Cm Cp L R)) {Cif : ℝ}
    (h1 : 2 / bulkLength Cm Cp L R ≤ Cif) (h2 : 2 * bulkLength Cm Cp L R ≤ Cif) :
    (∫ z in transverseBall 1 R, ifaceL u z ^ 2)
      ≤ Cif * (massP (restrictBulkP hR u) + axialDirichletP (restrictBulkP hR u)) := by
  have hM : (0 : ℝ) ≤ ∫ p in bulkCylinder Cm Cp L R, u.toFun p ^ 2 :=
    integral_nonneg fun _ => sq_nonneg _
  have hG : (0 : ℝ) ≤ ∫ p in bulkCylinder Cm Cp L R, u.gx p ^ 2 :=
    integral_nonneg fun _ => sq_nonneg _
  have h := integral_ifaceL_sq_le hR hL u
  rw [massP_restrictBulkP_eq_bi hR u, axialDirichletP_restrictBulkP_eq_bi hR u,
    show transverseBall 1 R = ball (0 : EuclideanSpace ℝ (Fin 1)) R from rfl]
  have e1 := mul_le_mul_of_nonneg_right h1 hM
  have e2 := mul_le_mul_of_nonneg_right h2 hG
  linarith

theorem integral_ifaceR_sq_le_const_bi (hR : 0 < R) (hL : (Cm.K + Cp.K) * R < L)
    (u : H1P (thinDomain Cm Cp L R)) {Cif : ℝ}
    (h1 : 2 / bulkLength Cm Cp L R ≤ Cif) (h2 : 2 * bulkLength Cm Cp L R ≤ Cif) :
    (∫ z in transverseBall 1 R, ifaceR u z ^ 2)
      ≤ Cif * (massP (restrictBulkP hR u) + axialDirichletP (restrictBulkP hR u)) := by
  have hM : (0 : ℝ) ≤ ∫ p in bulkCylinder Cm Cp L R, u.toFun p ^ 2 :=
    integral_nonneg fun _ => sq_nonneg _
  have hG : (0 : ℝ) ≤ ∫ p in bulkCylinder Cm Cp L R, u.gx p ^ 2 :=
    integral_nonneg fun _ => sq_nonneg _
  have h := integral_ifaceR_sq_le hR hL u
  rw [massP_restrictBulkP_eq_bi hR u, axialDirichletP_restrictBulkP_eq_bi hR u,
    show transverseBall 1 R = ball (0 : EuclideanSpace ℝ (Fin 1)) R from rfl]
  have e1 := mul_le_mul_of_nonneg_right h1 hM
  have e2 := mul_le_mul_of_nonneg_right h2 hG
  linarith

/-! ## 5.  The witness at a single radius -/

/-- **The interface-trace data at one admissible radius.**  This is the body of the field
`InterfaceTraceInput_a1.iface`. -/
theorem exists_iface_bi (hR : 0 < R) (hL : (Cm.K + Cp.K) * R < L) (hα : 0 < α)
    (u : H1P (thinDomain Cm Cp L R)) {Cif : ℝ}
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
  ⟨ifaceL u, ifaceR u, memLp_ifaceL_bi hR hL u, memLp_ifaceR_bi hR hL u,
    axialRepOne_endpoint_left_bi hR hL hα u, axialRepOne_endpoint_right_bi hR hL hα u,
    integral_ifaceL_sq_le_const_bi hR hL u h1 h2,
    integral_ifaceR_sq_le_const_bi hR hL u h1 h2⟩

/-! ## 6.  Monotonicity in the radius threshold and the final statement -/

/-- **`InterfaceTraceInput_a1` is monotone in the radius threshold.** -/
theorem interfaceTraceInput_le_bi {hα : 0 < α} {Cif R₀ R₀' : ℝ}
    (h : InterfaceTraceInput_a1 Cm Cp L α hα Cif R₀) (hle : R₀' ≤ R₀) :
    InterfaceTraceInput_a1 Cm Cp L α hα Cif R₀' :=
  ⟨fun R hR hR0 hL u => h.iface R hR (lt_of_lt_of_le hR0 hle) hL u⟩

/-- **`InterfaceTraceInput_a1` holds, with `C_if = max (4/L) (2L)` and
`R₀ = L / (2 (K₋ + K₊))`.**

For `0 < R < R₀` the bulk length `ℓ_R = L - (K₋+K₊) R` lies in `(L/2, L]`, so the two explicit
constants `2/ℓ_R`, `2 ℓ_R` of the one-dimensional trace inequality
(`RobinCaps.ThinDomain.integral_ifaceL_sq_le`) are bounded by `4/L` and `2L` uniformly in the
radius. -/
theorem interfaceTraceInput_one_bi (Cm Cp : Cap 1) (L α : ℝ) (hα : 0 < α) (hL0 : 0 < L) :
    ∃ Cif R₀ : ℝ, 0 ≤ Cif ∧ 0 < R₀ ∧ InterfaceTraceInput_a1 Cm Cp L α hα Cif R₀ := by
  have hK : (0 : ℝ) < Cm.K + Cp.K := add_pos Cm.hK Cp.hK
  refine ⟨max (4 / L) (2 * L), L / (2 * (Cm.K + Cp.K)),
    le_max_of_le_right (by linarith), div_pos hL0 (by linarith), ⟨fun R hR hR0 hL u => ?_⟩⟩
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
  exact exists_iface_bi hR hL hα u h1 h2

end RobinCaps.ThinDomain

end

