import RobinCaps.ThinDomain.TrialAC
import RobinCaps.ThinDomain.TrialAssemblyOne
import RobinCaps.ThinDomain.TrialAssemblyGen
import RobinCaps.ThinDomain.TrialBound
import RobinCaps.ThinDomain.Restrict
import RobinCaps.ThinDomain.BulkEnergy
import RobinCaps.ThinDomain.H1PQuotient
import RobinCaps.ThinDomain.Boundary
import RobinCaps.ThinDomain.AssemblyOneGen
import RobinCaps.Compact.BoundaryForm
import RobinCaps.Cap.TraceDataHemi

/-!
# The trial side of the global comparison, for a **weak** transverse ground state

`RobinCaps/ThinDomain/TrialAssemblyGen.lean` proves the `trial_energy` field of
`RobinCaps.ThinDomain.GlobalComparisonData` for a *regular* transverse ground state
(`TransverseGroundStateReg`), whose extra continuity field `psiC1` lets `bd_trialAC_tg` identify
an abstract trace datum's boundary form `td.bd` with the honest surface integral
`boundaryEnergy` through `td.tr_continuous` (the trial extension is continuous up to `∂Ω_R`
*only when the transverse factor itself is continuous*).

For a merely **weak** transverse ground state (`TransverseGroundState`, no continuity of `ψ_R`)
the trial extension `𝒯_R W` is *not* continuous, so `tr_continuous` cannot be invoked. This file
computes `td.bd (𝒯_R W) (𝒯_R W)` instead through the *structure* of the trace datum, taken as the
hypothesis `TraceSplitW_taw`: the bulk part is the abstract lateral form `bdCyl (bdR m R)` of
`RobinCaps/ThinDomain/BulkEnergy.lean` applied to the bulk-cylinder restriction of the tensor, and
the two cap parts are the unit-cap `Γ`-form `bdΓ` of `RobinCaps.Cap.TraceDataHemi` applied to the
rescaled cap restrictions `capLeft`/`capRight` of `RobinCaps/ThinDomain/Restrict.lean`.

## Contents

1. `TraceSplitW_taw` — the trace-split interface for the two hemispherical caps, general `m`.
2. `capLiftW`, `capEnergyTermW_taw` — the transverse lift of the weak ground state (taken as a
   parameter with its three defining properties) and the renormalized cap energy term built from
   it through `bdΓ` instead of the concrete surface integral `capJForm`.
3. `bdΓ_capLeft_taw`/`bdΓ_capRight_taw` — the cap component of the tensor's boundary form: only
   the *values* of the trial function's axial factor at the two endpoints survive, established
   through `vanishes_ae` (the trace only sees the a.e. class) rather than continuity.
4. `massP_leftCap_taw`/`dirichletP_leftCap_taw` (and their right twins) — the bulk part of the
   tensor: the physical cap masses/energies of `TrialAC.lean`'s `massP_trialAC`/`dirichletP_trialAC`
   in terms of `capLiftW`, by the same change-of-variables computation as
   `massP_capTrialLeft_eq`/`dirichletP_capTrialLeft_eq`.
5. `bdCyl_bulk_taw` — the bulk part of the tensor's boundary form: `bdCyl (bdR m R)` of the
   restricted tensor is the axial mass of `W` times `bdR m R gs.psi gs.psi`.
6. `bd_trialAC_taw` — the trace split of the trial extension, assembling 3 and 5.
7. `renormEnergy_trialAC_taw` — the exact `eq:trial-energy` splitting for the weak ground state.
8. `trial_energy_field_taw` — the `trial_energy` field of `GlobalComparisonData`.

No `sorry`, `admit`, `axiom` or `native_decide` occurs in this file.
-/

open MeasureTheory Set Metric Filter

open scoped ENNReal Topology InnerProductSpace

namespace RobinCaps.ThinDomain

open RobinCaps.Sobolev RobinCaps.Domain RobinCaps.Cap RobinCaps.Compact

noncomputable section

variable {m : ℕ} {α R L : ℝ}

/-! ## 1. The trace-split interface for the two hemispherical caps -/

/-- **Interface (`TraceGen.lean`).** The trace split of a general trace datum `td` on the two
hemispherical caps, for general transverse dimension `m`: the bulk part of the tensor is the
abstract lateral form `bdCyl (bdR m R)` of the bulk-cylinder restriction, and the two cap parts
are the unit-cap `Γ`-form `bdΓ` of the rescaled cap restrictions `capLeft`/`capRight`, at the
manuscript amplitude `c = R^{m/2}` (so that `c² = R^m` and the recorded scaling factor
`R^m · c⁻²`, matching `BoundaryPieces.lateralIntegral_leftCap_eq`'s `R^m` against the amplitude
`c` of `capLeft`, is exactly `1` for `R > 0`; it is kept explicit here to match the source). -/
def TraceSplitW_taw (hm : 1 ≤ m) (hR : 0 < R)
    (hL : ((hemisphere m).K + (hemisphere m).K) * R < L)
    (td : TraceData (hemisphere m) (hemisphere m) L R) : Prop :=
  ∀ u : H1P (thinDomain (hemisphere m) (hemisphere m) L R),
    td.bd u u
      = R ^ m * (R ^ ((m : ℝ) / 2))⁻¹ ^ 2 *
          (capTraceDataHemi_th m hm).bdΓ (capLeft hR hL (R ^ ((m : ℝ) / 2)) u)
              (capLeft hR hL (R ^ ((m : ℝ) / 2)) u)
        + bdCyl (bdR m R) (restrictBulkP hR u) (restrictBulkP hR u)
        + R ^ m * (R ^ ((m : ℝ) / 2))⁻¹ ^ 2 *
          (capTraceDataHemi_th m hm).bdΓ (capRight hR hL (R ^ ((m : ℝ) / 2)) u)
              (capRight hR hL (R ^ ((m : ℝ) / 2)) u)

/-- The scaling factor `R^m · (R^{m/2})⁻²` of `TraceSplitW_taw` is exactly `1` for `R > 0`
(`c² = R^m` at the manuscript normalisation `c = R^{m/2}`, `RobinCaps.ThinDomain.sq_rpow_half`). -/
theorem capScale_taw (m : ℕ) (hR : 0 < R) :
    R ^ m * (R ^ ((m : ℝ) / 2))⁻¹ ^ 2 = 1 := by
  rw [inv_pow, sq_rpow_half m hR, mul_inv_cancel₀ (pow_ne_zero m hR.ne')]

/-! ## 2. The transverse lift of the weak ground state, and the cap energy term -/

/-- **Interface (`TrialBoundW.lean`).** The renormalized cap energy term for a **weak**
transverse ground state, built from the trace form `bdΓ` of the unit hemispherical cap instead
of the concrete surface integral `capJForm` (which needs continuity of `ψ_R` to identify with the
abstract trace). `capLiftW` is the transverse lift `p ↦ R^{m/2} ψ_R(Rp.2)` of `TrialBound.lean`'s
`transLift`, as an element of `H1P (hemisphere m).body`; it is taken here as a parameter with its
three defining properties (`toFun`, `gx = 0`, `gz`), since its construction (`TrialBoundW.lean`)
is not yet available. -/
def capEnergyTermW_taw (m : ℕ) (hm : 1 ≤ m) (α R : ℝ)
    {bd : TransH1 m R →ₗ[ℝ] TransH1 m R →ₗ[ℝ] ℝ} (gs : TransverseGroundState m α R bd)
    (capLiftW : H1P (hemisphere m).body) : ℝ :=
  R⁻¹ * (∫ p in (hemisphere m).body, ‖capLiftW.gz p‖ ^ 2)
    + (α * (capTraceDataHemi_th m hm).bdΓ capLiftW capLiftW - (m : ℝ) * α * massP capLiftW)
    - (R * gs.nu - (m : ℝ) * α) * massP capLiftW

/-! ## 3. The cap component of the tensor -/

/-- **The left-cap value of the trial extension, in cap coordinates.**  On the whole cap body
(not merely a.e.) the rescaled restriction of `𝒯_R W` to the left cap is the constant `W(0)`
times the transverse lift `transLift m R ψ`. -/
theorem toFun_capLeft_trialAC_taw (hR : 0 < R)
    (hL : ((hemisphere m).K + (hemisphere m).K) * R < L)
    (W : Sobolev.H1 (bulkLength (hemisphere m) (hemisphere m) L R)) (ψ : TransH1 m R)
    {p : CapSpace m} (hp : p ∈ (hemisphere m).body) :
    (capLeft hR hL (R ^ ((m : ℝ) / 2)) (trialAC hR hL W ψ)).toFun p
      = W.toFun 0 * transLift m R ψ p.2 := by
  have hle : (-L / 2 + (-1 : ℝ) * R * p.1 : ℝ) ≤ -L / 2 + (hemisphere m).K * R := by
    have h1 : -(hemisphere m).K < p.1 := hp.1
    nlinarith [mul_pos hR (show (0:ℝ) < p.1 + (hemisphere m).K by linarith)]
  rw [capLeft, H1P.rescaleLeft, H1P.cast_toFun, H1P.rescaleP_toFun, restrictLeft_toFun,
    trialAC_toFun]
  show (R ^ ((m : ℝ) / 2)) * trialACFun (hemisphere m) (hemisphere m) L R W ψ
      (affP (-L / 2) (-1) R p) = _
  show (R ^ ((m : ℝ) / 2)) *
      (trialACProfile (-L / 2 + (hemisphere m).K * R) W (-L / 2 + (-1 : ℝ) * R * p.1)
        * ψ.toFun (R • p.2)) = _
  rw [trialACProfile_of_le (trialAC_bulkLength_pos hL).le W hle]
  simp only [transLift]
  ring

/-- **The right-cap value of the trial extension, in cap coordinates.** -/
theorem toFun_capRight_trialAC_taw (hR : 0 < R)
    (hL : ((hemisphere m).K + (hemisphere m).K) * R < L)
    (W : Sobolev.H1 (bulkLength (hemisphere m) (hemisphere m) L R)) (ψ : TransH1 m R)
    {p : CapSpace m} (hp : p ∈ (hemisphere m).body) :
    (capRight hR hL (R ^ ((m : ℝ) / 2)) (trialAC hR hL W ψ)).toFun p
      = W.toFun (bulkLength (hemisphere m) (hemisphere m) L R) * transLift m R ψ p.2 := by
  have hge : L / 2 - (hemisphere m).K * R ≤ L / 2 + (1 : ℝ) * R * p.1 := by
    have h1 : -(hemisphere m).K < p.1 := hp.1
    nlinarith [mul_pos hR (show (0:ℝ) < p.1 + (hemisphere m).K by linarith)]
  rw [capRight, H1P.rescaleRight, H1P.cast_toFun, H1P.rescaleP_toFun, restrictRight_toFun,
    trialAC_toFun]
  show (R ^ ((m : ℝ) / 2)) * trialACFun (hemisphere m) (hemisphere m) L R W ψ
      (affP (L / 2) 1 R p) = _
  show (R ^ ((m : ℝ) / 2)) *
      (trialACProfile (-L / 2 + (hemisphere m).K * R) W (L / 2 + (1 : ℝ) * R * p.1)
        * ψ.toFun (R • p.2)) = _
  have hge' : (-L / 2 + (hemisphere m).K * R)
      + bulkLength (hemisphere m) (hemisphere m) L R ≤ L / 2 + (1 : ℝ) * R * p.1 := by
    rw [trialAC_interface_add]; exact hge
  rw [trialACProfile_of_ge (trialAC_bulkLength_pos hL).le W hge']
  simp only [transLift]
  ring

/-- **`bdΓ` only sees the a.e. class of `toFun`.**  The bilinear consequence of
`CapTraceData.vanishes_ae`. -/
theorem bdΓ_congr_ae_taw (hm : 1 ≤ m) {u v : H1P (hemisphere m).body}
    (h : u.toFun =ᵐ[volume.restrict (hemisphere m).body] v.toFun)
    (w : H1P (hemisphere m).body) :
    (capTraceDataHemi_th m hm).bdΓ u w = (capTraceDataHemi_th m hm).bdΓ v w := by
  have hsub : (u - v).toFun =ᵐ[volume.restrict (hemisphere m).body] 0 := by
    rw [H1P.sub_toFun_be]
    filter_upwards [h] with p hp
    simp [hp]
  have h0 := (capTraceDataHemi_th m hm).vanishes_ae (u - v) hsub w
  rw [map_sub, LinearMap.sub_apply] at h0
  linarith

/-- **The cap component of the tensor's boundary form, general `p`.**  Given any
`Φ : H1P (hemisphere m).body` whose representative is the transverse lift `transLift m R ψ`, the
left-cap `Γ`-form of the trial extension is `W(0)²` times `bdΓ Φ Φ`. -/
theorem bdΓ_capLeft_taw (hm : 1 ≤ m) (hR : 0 < R)
    (hL : ((hemisphere m).K + (hemisphere m).K) * R < L)
    (W : Sobolev.H1 (bulkLength (hemisphere m) (hemisphere m) L R)) (ψ : TransH1 m R)
    (Φ : H1P (hemisphere m).body) (hΦ : Φ.toFun = fun p => transLift m R ψ p.2) :
    (capTraceDataHemi_th m hm).bdΓ (capLeft hR hL (R ^ ((m : ℝ) / 2)) (trialAC hR hL W ψ))
        (capLeft hR hL (R ^ ((m : ℝ) / 2)) (trialAC hR hL W ψ))
      = W.toFun 0 ^ 2 * (capTraceDataHemi_th m hm).bdΓ Φ Φ := by
  set u := capLeft hR hL (R ^ ((m : ℝ) / 2)) (trialAC hR hL W ψ) with hu
  set v := W.toFun 0 • Φ with hv
  have htoeq : u.toFun =ᵐ[volume.restrict (hemisphere m).body] v.toFun := by
    refine (ae_restrict_iff' (measurableSet_capBody (hemisphere m))).2
      (Filter.Eventually.of_forall fun p hp => ?_)
    rw [hu, hv, H1P.smul_toFun]
    show (capLeft hR hL (R ^ ((m : ℝ) / 2)) (trialAC hR hL W ψ)).toFun p
        = W.toFun 0 * Φ.toFun p
    rw [toFun_capLeft_trialAC_taw hR hL W ψ hp, hΦ]
  have h1 := bdΓ_congr_ae_taw hm htoeq u
  have h2 := (capTraceDataHemi_th m hm).bdΓ_symm v u
  have h3 := bdΓ_congr_ae_taw hm htoeq v
  rw [h1, h2, h3, hv]
  simp only [map_smul, LinearMap.smul_apply, smul_eq_mul]
  ring

/-- **The cap component of the tensor's boundary form, right cap.** -/
theorem bdΓ_capRight_taw (hm : 1 ≤ m) (hR : 0 < R)
    (hL : ((hemisphere m).K + (hemisphere m).K) * R < L)
    (W : Sobolev.H1 (bulkLength (hemisphere m) (hemisphere m) L R)) (ψ : TransH1 m R)
    (Φ : H1P (hemisphere m).body) (hΦ : Φ.toFun = fun p => transLift m R ψ p.2) :
    (capTraceDataHemi_th m hm).bdΓ (capRight hR hL (R ^ ((m : ℝ) / 2)) (trialAC hR hL W ψ))
        (capRight hR hL (R ^ ((m : ℝ) / 2)) (trialAC hR hL W ψ))
      = W.toFun (bulkLength (hemisphere m) (hemisphere m) L R) ^ 2
        * (capTraceDataHemi_th m hm).bdΓ Φ Φ := by
  set u := capRight hR hL (R ^ ((m : ℝ) / 2)) (trialAC hR hL W ψ) with hu
  set v := W.toFun (bulkLength (hemisphere m) (hemisphere m) L R) • Φ with hv
  have htoeq : u.toFun =ᵐ[volume.restrict (hemisphere m).body] v.toFun := by
    refine (ae_restrict_iff' (measurableSet_capBody (hemisphere m))).2
      (Filter.Eventually.of_forall fun p hp => ?_)
    rw [hu, hv, H1P.smul_toFun]
    show (capRight hR hL (R ^ ((m : ℝ) / 2)) (trialAC hR hL W ψ)).toFun p
        = W.toFun (bulkLength (hemisphere m) (hemisphere m) L R) * Φ.toFun p
    rw [toFun_capRight_trialAC_taw hR hL W ψ hp, hΦ]
  have h1 := bdΓ_congr_ae_taw hm htoeq u
  have h2 := (capTraceDataHemi_th m hm).bdΓ_symm v u
  have h3 := bdΓ_congr_ae_taw hm htoeq v
  rw [h1, h2, h3, hv]
  simp only [map_smul, LinearMap.smul_apply, smul_eq_mul]
  ring

/-! ## 4. The two physical cap terms, in terms of `capLiftW` -/

/-- **The left-cap mass of the trial extension, in terms of `capLiftW`.** -/
theorem massP_leftCap_taw (hR : 0 < R) (hL : ((hemisphere m).K + (hemisphere m).K) * R < L)
    (W : Sobolev.H1 (bulkLength (hemisphere m) (hemisphere m) L R)) (ψ : TransH1 m R)
    (Φ : H1P (hemisphere m).body) (hΦ : Φ.toFun = fun p => transLift m R ψ p.2) :
    (∫ p in leftCap (hemisphere m) L R, (W.toFun 0 * ψ.toFun p.2) ^ 2)
      = R * (W.toFun 0 ^ 2 * massP Φ) := by
  have hbody := measurableSet_capBody (hemisphere m)
  have hcov := setIntegral_image_affP (m := m) (-L / 2) (ε := -1) hR (by norm_num) hbody
    (fun q : CapSpace m => (W.toFun 0 * ψ.toFun q.2) ^ 2)
  have h0 : (∫ p in leftCap (hemisphere m) L R, (W.toFun 0 * ψ.toFun p.2) ^ 2)
      = ∫ q in affP (-L / 2) (-1) R '' (hemisphere m).body, (W.toFun 0 * ψ.toFun q.2) ^ 2 := by
    rw [← leftCap_eq_image]
  have hpt : ∀ p : CapSpace m,
      (W.toFun 0 * ψ.toFun ((affP (-L / 2) (-1) R p).2)) ^ 2
        = (R ^ m)⁻¹ * (W.toFun 0 ^ 2 * Φ.toFun p ^ 2) := by
    intro p
    rw [show (affP (-L / 2) (-1) R p).2 = R • p.2 from rfl, hΦ]
    show (W.toFun 0 * ψ.toFun (R • p.2)) ^ 2
        = (R ^ m)⁻¹ * (W.toFun 0 ^ 2 * transLift m R ψ p.2 ^ 2)
    rw [transLift_sq m hR ψ p.2]
    have hRm : (R ^ m : ℝ) ≠ 0 := pow_ne_zero m hR.ne'
    field_simp
  have key : (∫ p in (hemisphere m).body,
        (W.toFun 0 * ψ.toFun ((affP (-L / 2) (-1) R p).2)) ^ 2)
      = (R ^ m)⁻¹ * (W.toFun 0 ^ 2 * massP Φ) := by
    rw [integral_congr_ae (.of_forall hpt), integral_const_mul, integral_const_mul]
    rfl
  rw [h0, hcov, key, pow_succ]
  have hRm : (R ^ m : ℝ) ≠ 0 := pow_ne_zero m hR.ne'
  field_simp

/-- **The right-cap mass of the trial extension, in terms of `capLiftW`.** -/
theorem massP_rightCap_taw (hR : 0 < R) (hL : ((hemisphere m).K + (hemisphere m).K) * R < L)
    (W : Sobolev.H1 (bulkLength (hemisphere m) (hemisphere m) L R)) (ψ : TransH1 m R)
    (Φ : H1P (hemisphere m).body) (hΦ : Φ.toFun = fun p => transLift m R ψ p.2) :
    (∫ p in rightCap (hemisphere m) L R,
        (W.toFun (bulkLength (hemisphere m) (hemisphere m) L R) * ψ.toFun p.2) ^ 2)
      = R * (W.toFun (bulkLength (hemisphere m) (hemisphere m) L R) ^ 2 * massP Φ) := by
  have hbody := measurableSet_capBody (hemisphere m)
  have hcov := setIntegral_image_affP (m := m) (L / 2) (ε := 1) hR (by norm_num) hbody
    (fun q : CapSpace m =>
      (W.toFun (bulkLength (hemisphere m) (hemisphere m) L R) * ψ.toFun q.2) ^ 2)
  have h0 : (∫ p in rightCap (hemisphere m) L R,
        (W.toFun (bulkLength (hemisphere m) (hemisphere m) L R) * ψ.toFun p.2) ^ 2)
      = ∫ q in affP (L / 2) 1 R '' (hemisphere m).body,
          (W.toFun (bulkLength (hemisphere m) (hemisphere m) L R) * ψ.toFun q.2) ^ 2 := by
    rw [← rightCap_eq_image]
  have hpt : ∀ p : CapSpace m,
      (W.toFun (bulkLength (hemisphere m) (hemisphere m) L R)
          * ψ.toFun ((affP (L / 2) 1 R p).2)) ^ 2
        = (R ^ m)⁻¹ *
          (W.toFun (bulkLength (hemisphere m) (hemisphere m) L R) ^ 2 * Φ.toFun p ^ 2) := by
    intro p
    rw [show (affP (L / 2) 1 R p).2 = R • p.2 from rfl, hΦ]
    show (W.toFun (bulkLength (hemisphere m) (hemisphere m) L R) * ψ.toFun (R • p.2)) ^ 2
        = (R ^ m)⁻¹ *
          (W.toFun (bulkLength (hemisphere m) (hemisphere m) L R) ^ 2 * transLift m R ψ p.2 ^ 2)
    rw [transLift_sq m hR ψ p.2]
    have hRm : (R ^ m : ℝ) ≠ 0 := pow_ne_zero m hR.ne'
    field_simp
  have key : (∫ p in (hemisphere m).body,
        (W.toFun (bulkLength (hemisphere m) (hemisphere m) L R)
            * ψ.toFun ((affP (L / 2) 1 R p).2)) ^ 2)
      = (R ^ m)⁻¹ *
        (W.toFun (bulkLength (hemisphere m) (hemisphere m) L R) ^ 2 * massP Φ) := by
    rw [integral_congr_ae (.of_forall hpt), integral_const_mul, integral_const_mul]
    rfl
  rw [h0, hcov, key, pow_succ]
  have hRm : (R ^ m : ℝ) ≠ 0 := pow_ne_zero m hR.ne'
  field_simp

/-- **The left-cap Dirichlet energy of the trial extension, in terms of `capLiftW`.** -/
theorem dirichletP_leftCap_taw (hR : 0 < R) (hL : ((hemisphere m).K + (hemisphere m).K) * R < L)
    (W : Sobolev.H1 (bulkLength (hemisphere m) (hemisphere m) L R)) (ψ : TransH1 m R)
    (Φ : H1P (hemisphere m).body)
    (hgz : Φ.gz = fun p => (R ^ ((m : ℝ) / 2) * R) • ψ.grad (R • p.2)) :
    (∫ p in leftCap (hemisphere m) L R, ‖W.toFun 0 • ψ.grad p.2‖ ^ 2)
      = R⁻¹ * (W.toFun 0 ^ 2 * ∫ p in (hemisphere m).body, ‖Φ.gz p‖ ^ 2) := by
  have hbody := measurableSet_capBody (hemisphere m)
  have hcov := setIntegral_image_affP (m := m) (-L / 2) (ε := -1) hR (by norm_num) hbody
    (fun q : CapSpace m => ‖W.toFun 0 • ψ.grad q.2‖ ^ 2)
  have h0 : (∫ p in leftCap (hemisphere m) L R, ‖W.toFun 0 • ψ.grad p.2‖ ^ 2)
      = ∫ q in affP (-L / 2) (-1) R '' (hemisphere m).body, ‖W.toFun 0 • ψ.grad q.2‖ ^ 2 := by
    rw [← leftCap_eq_image]
  have hR2m : (0 : ℝ) < R ^ (m + 2) := by positivity
  have hpt : ∀ p : CapSpace m,
      ‖W.toFun 0 • ψ.grad ((affP (-L / 2) (-1) R p).2)‖ ^ 2
        = (R ^ (m + 2))⁻¹ * (W.toFun 0 ^ 2 * ‖Φ.gz p‖ ^ 2) := by
    intro p
    rw [show (affP (-L / 2) (-1) R p).2 = R • p.2 from rfl, hgz]
    show ‖W.toFun 0 • ψ.grad (R • p.2)‖ ^ 2
        = (R ^ (m + 2))⁻¹ * (W.toFun 0 ^ 2 * ‖(R ^ ((m : ℝ) / 2) * R) • ψ.grad (R • p.2)‖ ^ 2)
    rw [norm_smul, norm_smul, Real.norm_eq_abs, Real.norm_eq_abs, mul_pow, mul_pow, sq_abs,
      sq_abs, mul_pow, sq_rpow_half m hR]
    have hRm2 : (R ^ (m + 2) : ℝ) ≠ 0 := hR2m.ne'
    field_simp
    ring
  have key : (∫ p in (hemisphere m).body,
        ‖W.toFun 0 • ψ.grad ((affP (-L / 2) (-1) R p).2)‖ ^ 2)
      = (R ^ (m + 2))⁻¹ * (W.toFun 0 ^ 2 * ∫ p in (hemisphere m).body, ‖Φ.gz p‖ ^ 2) := by
    rw [integral_congr_ae (.of_forall hpt), integral_const_mul, integral_const_mul]
  rw [h0, hcov, key]
  have hRm2 : (R ^ (m + 2) : ℝ) ≠ 0 := hR2m.ne'
  have hR0 : (R : ℝ) ≠ 0 := hR.ne'
  field_simp
  rw [pow_succ, pow_succ]
  ring

/-- **The right-cap Dirichlet energy of the trial extension, in terms of `capLiftW`.** -/
theorem dirichletP_rightCap_taw (hR : 0 < R) (hL : ((hemisphere m).K + (hemisphere m).K) * R < L)
    (W : Sobolev.H1 (bulkLength (hemisphere m) (hemisphere m) L R)) (ψ : TransH1 m R)
    (Φ : H1P (hemisphere m).body)
    (hgz : Φ.gz = fun p => (R ^ ((m : ℝ) / 2) * R) • ψ.grad (R • p.2)) :
    (∫ p in rightCap (hemisphere m) L R,
        ‖W.toFun (bulkLength (hemisphere m) (hemisphere m) L R) • ψ.grad p.2‖ ^ 2)
      = R⁻¹ * (W.toFun (bulkLength (hemisphere m) (hemisphere m) L R) ^ 2
          * ∫ p in (hemisphere m).body, ‖Φ.gz p‖ ^ 2) := by
  have hbody := measurableSet_capBody (hemisphere m)
  have hcov := setIntegral_image_affP (m := m) (L / 2) (ε := 1) hR (by norm_num) hbody
    (fun q : CapSpace m =>
      ‖W.toFun (bulkLength (hemisphere m) (hemisphere m) L R) • ψ.grad q.2‖ ^ 2)
  have h0 : (∫ p in rightCap (hemisphere m) L R,
        ‖W.toFun (bulkLength (hemisphere m) (hemisphere m) L R) • ψ.grad p.2‖ ^ 2)
      = ∫ q in affP (L / 2) 1 R '' (hemisphere m).body,
          ‖W.toFun (bulkLength (hemisphere m) (hemisphere m) L R) • ψ.grad q.2‖ ^ 2 := by
    rw [← rightCap_eq_image]
  have hR2m : (0 : ℝ) < R ^ (m + 2) := by positivity
  have hpt : ∀ p : CapSpace m,
      ‖W.toFun (bulkLength (hemisphere m) (hemisphere m) L R)
          • ψ.grad ((affP (L / 2) 1 R p).2)‖ ^ 2
        = (R ^ (m + 2))⁻¹ *
          (W.toFun (bulkLength (hemisphere m) (hemisphere m) L R) ^ 2 * ‖Φ.gz p‖ ^ 2) := by
    intro p
    rw [show (affP (L / 2) 1 R p).2 = R • p.2 from rfl, hgz]
    show ‖W.toFun (bulkLength (hemisphere m) (hemisphere m) L R) • ψ.grad (R • p.2)‖ ^ 2
        = (R ^ (m + 2))⁻¹ *
          (W.toFun (bulkLength (hemisphere m) (hemisphere m) L R) ^ 2
            * ‖(R ^ ((m : ℝ) / 2) * R) • ψ.grad (R • p.2)‖ ^ 2)
    rw [norm_smul, norm_smul, Real.norm_eq_abs, Real.norm_eq_abs, mul_pow, mul_pow, sq_abs,
      sq_abs, mul_pow, sq_rpow_half m hR]
    have hRm2 : (R ^ (m + 2) : ℝ) ≠ 0 := hR2m.ne'
    field_simp
    ring
  have key : (∫ p in (hemisphere m).body,
        ‖W.toFun (bulkLength (hemisphere m) (hemisphere m) L R)
            • ψ.grad ((affP (L / 2) 1 R p).2)‖ ^ 2)
      = (R ^ (m + 2))⁻¹ *
        (W.toFun (bulkLength (hemisphere m) (hemisphere m) L R) ^ 2
          * ∫ p in (hemisphere m).body, ‖Φ.gz p‖ ^ 2) := by
    rw [integral_congr_ae (.of_forall hpt), integral_const_mul, integral_const_mul]
  rw [h0, hcov, key]
  have hRm2 : (R ^ (m + 2) : ℝ) ≠ 0 := hR2m.ne'
  have hR0 : (R : ℝ) ≠ 0 := hR.ne'
  field_simp
  rw [pow_succ, pow_succ]
  ring

/-! ## 5. The bulk part of the tensor's boundary form -/

/-- **The bulk part of the tensor's boundary form.**  On the bulk cylinder the tensor's slice
at `x` is `W(x - a) • ψ`, so `bdCyl (bdR m R)` is the axial mass of `W` times `bdR m R ψ ψ`. -/
theorem bdCyl_bulk_taw (hR : 0 < R) (hL : ((hemisphere m).K + (hemisphere m).K) * R < L)
    (W : Sobolev.H1 (bulkLength (hemisphere m) (hemisphere m) L R)) (ψ : TransH1 m R) :
    bdCyl (bdR m R) (restrictBulkP hR (trialAC hR hL W ψ))
        (restrictBulkP hR (trialAC hR hL W ψ))
      = Sobolev.mass (bulkLength (hemisphere m) (hemisphere m) L R) W * bdR m R ψ ψ := by
  have hab : (-L / 2 + (hemisphere m).K * R) + bulkLength (hemisphere m) (hemisphere m) L R
      = L / 2 - (hemisphere m).K * R := trialAC_interface_add
  have hℓ0 : (0 : ℝ) ≤ bulkLength (hemisphere m) (hemisphere m) L R :=
    (trialAC_bulkLength_pos hL).le
  have hslice : ∀ x ∈ Ioo (-L / 2 + (hemisphere m).K * R) (L / 2 - (hemisphere m).K * R),
      slice (restrictBulkP hR (trialAC hR hL W ψ)) x
        = W.toFun (x - (-L / 2 + (hemisphere m).K * R)) • ψ := by
    intro x hx
    have hmem1 : (-L / 2 + (hemisphere m).K * R) ≤ x := hx.1.le
    have hmem2 : x ≤ (-L / 2 + (hemisphere m).K * R) + bulkLength (hemisphere m) (hemisphere m) L R
        := by rw [hab]; exact hx.2.le
    have heq1 : (fun z => (restrictBulkP hR (trialAC hR hL W ψ)).toFun (x, z))
        = (W.toFun (x - (-L / 2 + (hemisphere m).K * R)) • ψ).toFun := by
      funext z
      rw [restrictBulkP_toFun, trialAC_toFun, Weak.H1.smul_toFun]
      show trialACFun (hemisphere m) (hemisphere m) L R W ψ (x, z)
          = (W.toFun (x - (-L / 2 + (hemisphere m).K * R)) • ψ.toFun) z
      show trialACProfile (-L / 2 + (hemisphere m).K * R) W x * ψ.toFun z = _
      rw [trialACProfile_of_mem W hmem1 hmem2, Pi.smul_apply, smul_eq_mul]
    have heq2 : (fun z => (restrictBulkP hR (trialAC hR hL W ψ)).gz (x, z))
        = (W.toFun (x - (-L / 2 + (hemisphere m).K * R)) • ψ).grad := by
      funext z
      show (trialAC hR hL W ψ).gz (x, z) = _
      rw [trialAC_gz, Weak.H1.smul_grad]
      show trialACGz (hemisphere m) (hemisphere m) L R W ψ (x, z)
          = (W.toFun (x - (-L / 2 + (hemisphere m).K * R)) • ψ.grad) z
      show trialACProfile (-L / 2 + (hemisphere m).K * R) W x • ψ.grad z = _
      rw [trialACProfile_of_mem W hmem1 hmem2, Pi.smul_apply]
    have hg1 : Weak.HasWeakGrad (transverseBall m R)
        (fun z => (restrictBulkP hR (trialAC hR hL W ψ)).toFun (x, z))
        (fun z => (restrictBulkP hR (trialAC hR hL W ψ)).gz (x, z)) := by
      rw [heq1, heq2]
      exact (W.toFun (x - (-L / 2 + (hemisphere m).K * R)) • ψ).hasWeakGrad
    have hg2 : MemLp (fun z => (restrictBulkP hR (trialAC hR hL W ψ)).toFun (x, z)) 2
        (volume.restrict (transverseBall m R)) := by
      rw [heq1]; exact (W.toFun (x - (-L / 2 + (hemisphere m).K * R)) • ψ).memL2
    have hg3 : MemLp (fun z => (restrictBulkP hR (trialAC hR hL W ψ)).gz (x, z)) 2
        (volume.restrict (transverseBall m R)) := by
      rw [heq2]; exact (W.toFun (x - (-L / 2 + (hemisphere m).K * R)) • ψ).grad_memL2
    have hgood : IsGoodSlice (restrictBulkP hR (trialAC hR hL W ψ)) x := ⟨hg1, hg2, hg3⟩
    refine Weak.H1.ext ?_ ?_
    · rw [slice_toFun hgood]; exact heq1
    · rw [slice_grad hgood]; exact heq2
  have hbd : ∀ x ∈ Ioo (-L / 2 + (hemisphere m).K * R) (L / 2 - (hemisphere m).K * R),
      bdR m R (slice (restrictBulkP hR (trialAC hR hL W ψ)) x)
          (slice (restrictBulkP hR (trialAC hR hL W ψ)) x)
        = W.toFun (x - (-L / 2 + (hemisphere m).K * R)) ^ 2 * bdR m R ψ ψ := by
    intro x hx
    rw [hslice x hx]
    simp only [map_smul, LinearMap.smul_apply, smul_eq_mul]
    ring
  calc bdCyl (bdR m R) (restrictBulkP hR (trialAC hR hL W ψ))
        (restrictBulkP hR (trialAC hR hL W ψ))
      = ∫ x in Ioo (-L / 2 + (hemisphere m).K * R) (L / 2 - (hemisphere m).K * R),
          W.toFun (x - (-L / 2 + (hemisphere m).K * R)) ^ 2 * bdR m R ψ ψ := by
        rw [bdCyl]; exact setIntegral_congr_fun measurableSet_Ioo hbd
    _ = (∫ x in Ioo (-L / 2 + (hemisphere m).K * R) (L / 2 - (hemisphere m).K * R),
          W.toFun (x - (-L / 2 + (hemisphere m).K * R)) ^ 2) * bdR m R ψ ψ :=
        integral_mul_const _ _
    _ = Sobolev.mass (bulkLength (hemisphere m) (hemisphere m) L R) W * bdR m R ψ ψ := by
        rw [← hab, setIntegral_trialACProfile_sq hℓ0 W]

/-! ## 6. The trace split of the trial extension -/

/-- **`bd_trialAC_taw`: the trace split of the trial extension, for a weak transverse ground
state.**  The bulk part cancels via `bdCyl_bulk_taw`; the two cap parts are `W`'s endpoint values
squared times `bdΓ Φ Φ`, via `TraceSplitW_taw` and the cap identities of §3, with the scaling
factor of `TraceSplitW_taw` collapsing to `1` (`capScale_taw`). -/
theorem bd_trialAC_taw (hm : 1 ≤ m) (hR : 0 < R)
    (hL : ((hemisphere m).K + (hemisphere m).K) * R < L)
    (W : Sobolev.H1 (bulkLength (hemisphere m) (hemisphere m) L R))
    {bd : TransH1 m R →ₗ[ℝ] TransH1 m R →ₗ[ℝ] ℝ} (gs : TransverseGroundState m α R bd)
    (td : TraceData (hemisphere m) (hemisphere m) L R) (hsplit : TraceSplitW_taw hm hR hL td)
    (Φ : H1P (hemisphere m).body) (hΦ : Φ.toFun = fun p => transLift m R gs.psi p.2) :
    td.bd (trialAC hR hL W gs.psi) (trialAC hR hL W gs.psi)
      = W.toFun 0 ^ 2 * (capTraceDataHemi_th m hm).bdΓ Φ Φ
        + Sobolev.mass (bulkLength (hemisphere m) (hemisphere m) L R) W * bdR m R gs.psi gs.psi
        + W.toFun (bulkLength (hemisphere m) (hemisphere m) L R) ^ 2
            * (capTraceDataHemi_th m hm).bdΓ Φ Φ := by
  rw [hsplit (trialAC hR hL W gs.psi), capScale_taw m hR,
    bdΓ_capLeft_taw hm hR hL W gs.psi Φ hΦ, bdCyl_bulk_taw hR hL W gs.psi,
    bdΓ_capRight_taw hm hR hL W gs.psi Φ hΦ]
  ring

/-! ## 7. The exact renormalized-energy splitting -/

/-- **`renormEnergy_trialAC_taw`: `eq:trial-energy`, exact form, for a weak transverse ground
state.** -/
theorem renormEnergy_trialAC_taw (hm : 1 ≤ m) (hR : 0 < R)
    (hL : ((hemisphere m).K + (hemisphere m).K) * R < L)
    (W : Sobolev.H1 (bulkLength (hemisphere m) (hemisphere m) L R))
    (gs : TransverseGroundState m α R (bdR m R))
    (td : TraceData (hemisphere m) (hemisphere m) L R) (hsplit : TraceSplitW_taw hm hR hL td)
    (Φ : H1P (hemisphere m).body) (hΦtoFun : Φ.toFun = fun p => transLift m R gs.psi p.2)
    (hΦgz : Φ.gz = fun p => (R ^ ((m : ℝ) / 2) * R) • gs.psi.grad (R • p.2)) :
    dirichletP (trialAC hR hL W gs.psi)
        + α * td.bd (trialAC hR hL W gs.psi) (trialAC hR hL W gs.psi)
        - gs.nu * massP (trialAC hR hL W gs.psi)
      = Sobolev.dirichlet (bulkLength (hemisphere m) (hemisphere m) L R) W
        + W.toFun 0 ^ 2 * capEnergyTermW_taw m hm α R gs Φ
        + W.toFun (bulkLength (hemisphere m) (hemisphere m) L R) ^ 2
            * capEnergyTermW_taw m hm α R gs Φ := by
  have hbulk : Weak.dirichlet gs.psi + α * bdR m R gs.psi gs.psi = gs.nu := by
    have h := gs.weak_eq gs.psi
    rw [qBilin_self, NBilin_self, gs.normalized, mul_one, qB] at h
    exact h
  rw [dirichletP_trialAC, massP_trialAC,
    bd_trialAC_taw hm hR hL W gs td hsplit Φ hΦtoFun,
    massP_leftCap_taw hR hL W gs.psi Φ hΦtoFun, massP_rightCap_taw hR hL W gs.psi Φ hΦtoFun,
    dirichletP_leftCap_taw hR hL W gs.psi Φ hΦgz, dirichletP_rightCap_taw hR hL W gs.psi Φ hΦgz,
    gs.normalized]
  simp only [capEnergyTermW_taw]
  linear_combination (Sobolev.mass (bulkLength (hemisphere m) (hemisphere m) L R) W) * hbulk

/-! ## 8. The `trial_energy` field -/

/-- **`trial_energy_field_taw`: the `trial_energy` field of `GlobalComparisonData`, for a weak
transverse ground state.**  The constant `Ctr` depends only on the uniform bound `A` of the
hypothesis `hcapR` — in particular not on `R`, `gs`, `td`, `Φ` nor the trial vector `v`. -/
theorem trial_energy_field_taw (hm : 1 ≤ m) (α : ℝ) (hα : 0 < α) (L A : ℝ) :
    ∃ Ctr : ℝ, 0 ≤ Ctr ∧ ∀ (R : ℝ) (hR : 0 < R), R ≤ 1 →
      ∀ (hL : ((hemisphere m).K + (hemisphere m).K) * R < L)
        (gs : TransverseGroundState m α R (bdR m R))
        (td : TraceData (hemisphere m) (hemisphere m) L R) (hsplit : TraceSplitW_taw hm hR hL td)
        (Φ : H1P (hemisphere m).body) (hΦtoFun : Φ.toFun = fun p => transLift m R gs.psi p.2)
        (hΦgz : Φ.gz = fun p => (R ^ ((m : ℝ) / 2) * R) • gs.psi.grad (R • p.2))
        (hcapR : |capEnergyTermW_taw m hm α R gs Φ - (hemisphere m).beta α| ≤ Ctr * R)
        (v : Sobolev.H1Q (bulkLength (hemisphere m) (hemisphere m) L R)),
        robinFormPQ (isOpen_thinDomain hR hL) td.bd td.vanishesOnNullAEP α
            (liftQ hR hL gs.psi v)
          - gs.nu * massPQ (liftQ hR hL gs.psi v)
        ≤ Sobolev.robinFormQ ((hemisphere m).beta α + Ctr * R) ((hemisphere m).beta α + Ctr * R)
            (bulkLength (hemisphere m) (hemisphere m) L R) v := by
  refine ⟨|A|, abs_nonneg A, ?_⟩
  intro R hR hR1 hL gs td hsplit Φ hΦtoFun hΦgz hcapR v
  obtain ⟨W, rfl⟩ := Submodule.Quotient.mk_surjective (Sobolev.nullOff _) v
  rw [liftQ_mk, robinFormPQ_mk, massPQ_mk, Sobolev.robinFormQ_mk,
    renormEnergy_trialAC_taw hm hR hL W gs td hsplit Φ hΦtoFun hΦgz, Sobolev.robinForm]
  have hb0 : capEnergyTermW_taw m hm α R gs Φ ≤ (hemisphere m).beta α + |A| * R := by
    have := (abs_le.1 hcapR).2
    linarith
  have h1 : W.toFun 0 ^ 2 * capEnergyTermW_taw m hm α R gs Φ
      ≤ ((hemisphere m).beta α + |A| * R) * W.toFun 0 ^ 2 := by
    nlinarith [sq_nonneg (W.toFun 0), hb0]
  have h2 : W.toFun (bulkLength (hemisphere m) (hemisphere m) L R) ^ 2
        * capEnergyTermW_taw m hm α R gs Φ
      ≤ ((hemisphere m).beta α + |A| * R)
          * W.toFun (bulkLength (hemisphere m) (hemisphere m) L R) ^ 2 := by
    nlinarith [sq_nonneg (W.toFun (bulkLength (hemisphere m) (hemisphere m) L R)), hb0]
  linarith

end

end RobinCaps.ThinDomain

