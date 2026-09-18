import RobinCaps.ThinDomain.TrialAssemblyW

/-!
# The trial side of the global comparison, mixed flat/hemisphere caps, weak ground state

`RobinCaps/ThinDomain/TrialAssemblyW.lean` proves the `trial_energy` field of
`RobinCaps.ThinDomain.GlobalComparisonData` for a **weak** transverse ground state, for the thin
domain with two hemispherical caps `thinDomain (hemisphere m) (hemisphere m) L R`.

This file redoes the same computation for the **mixed** thin domain
`thinDomain (Cap.flat m K hK) (Cap.hemisphere m) L R`: a flat left cap (a straight cylinder
segment `Ioo (-K) 0 ×ˢ ball 0 1` with a flat terminal disk, `Cap.flat` of
`RobinCaps/Cap/Sharp.lean`) and a hemispherical right cap, with the flat cap's trace datum an
*abstract* parameter `tdF : CapTraceData (Cap.flat m K hK)`.

Every underlying lemma of `TrialAssemblyW.lean` used here (`toFun_capLeft_trialAC_taw`,
`bdΓ_capLeft_taw`, `massP_leftCap_taw`, `dirichletP_leftCap_taw`, `bdCyl_bulk_taw`) is in fact
already stated, in `RobinCaps/ThinDomain/TrialAC.lean` and `RobinCaps/ThinDomain/Restrict.lean`,
for an *arbitrary* pair of caps `Cm Cp : Cap m` — the hemisphere never enters those proofs beyond
being *some* admissible cap. So §3–5 below simply restate those lemmas for a generic pair
`Cm Cp : Cap m` (with an abstract `CapTraceData` on each side), and §1–2, §6–8 specialise them at
`Cm := Cap.flat m K hK` (trace datum `tdF`) and `Cp := Cap.hemisphere m`
(trace datum `capTraceDataHemi_th m hm`, from `RobinCaps.Cap.TraceDataHemi`).

The right-cap energy term is *literally* `capEnergyTermW_taw m hm α R gs ΦR`: that definition is
already independent of the thin domain, stated only in terms of `H1P (hemisphere m).body`.

## Contents

1. `TraceSplitMixed_tam` — the trace-split interface for the mixed cap pair.
2. `capEnergyTermL_tam` — the renormalized cap energy term for the flat left cap (mirrors
   `capEnergyTermW_taw`, with `tdF.bdΓ` replacing `(capTraceDataHemi_th m hm).bdΓ`); the right cap
   term reuses `capEnergyTermW_taw` unchanged.
3. `toFun_capLeft_trialAC_tam`/`toFun_capRight_trialAC_tam` — the cap values of the trial
   extension, general `Cm Cp`.
4. `bdΓ_congr_ae_tam`, `bdΓ_capLeft_tam`/`bdΓ_capRight_tam` — the cap component of the tensor's
   boundary form, general `Cm Cp` and an abstract `CapTraceData` on the relevant side.
5. `massP_leftCap_tam`/`massP_rightCap_tam`, `dirichletP_leftCap_tam`/`dirichletP_rightCap_tam` —
   the two physical cap terms, general `Cm Cp`.
6. `bdCyl_bulk_tam` — the bulk part of the tensor's boundary form, general `Cm Cp`.
7. `bd_trialAC_tam`, `renormEnergy_trialAC_tam` — assembled at `Cm := Cap.flat m K hK`,
   `Cp := Cap.hemisphere m`.
8. `trial_energy_field_tam` — the `trial_energy` field of `GlobalComparisonData` for the mixed
   pair.

No `sorry`, `admit`, `axiom` or `native_decide` occurs in this file.
-/

open MeasureTheory Set Metric Filter

open scoped ENNReal Topology InnerProductSpace

namespace RobinCaps.ThinDomain

open RobinCaps.Sobolev RobinCaps.Domain RobinCaps.Cap RobinCaps.Compact

noncomputable section

variable {m : ℕ} {α R L : ℝ}

/-! ## 1. The trace-split interface for the mixed cap pair -/

/-- **Interface (`TraceGen.lean`).** The trace split of a general trace datum `td` on the mixed
cap pair (flat left, hemispherical right): same shape as `TraceSplitW_taw`, with `tdF.bdΓ`
replacing `(capTraceDataHemi_th m hm).bdΓ` on the left. -/
def TraceSplitMixed_tam (hm : 1 ≤ m) (K : ℝ) (hK : 0 < K)
    (tdF : CapTraceData (Cap.flat m K hK)) (hR : 0 < R)
    (hL : ((Cap.flat m K hK).K + (Cap.hemisphere m).K) * R < L)
    (td : TraceData (Cap.flat m K hK) (Cap.hemisphere m) L R) : Prop :=
  ∀ u : H1P (thinDomain (Cap.flat m K hK) (Cap.hemisphere m) L R),
    td.bd u u
      = R ^ m * (R ^ ((m : ℝ) / 2))⁻¹ ^ 2 *
          tdF.bdΓ (capLeft hR hL (R ^ ((m : ℝ) / 2)) u) (capLeft hR hL (R ^ ((m : ℝ) / 2)) u)
        + bdCyl (bdR m R) (restrictBulkP hR u) (restrictBulkP hR u)
        + R ^ m * (R ^ ((m : ℝ) / 2))⁻¹ ^ 2 *
          (capTraceDataHemi_th m hm).bdΓ (capRight hR hL (R ^ ((m : ℝ) / 2)) u)
              (capRight hR hL (R ^ ((m : ℝ) / 2)) u)

/-! ## 2. The two cap energy terms -/

/-- **The renormalized cap energy term for the flat left cap.**  Same shape as
`capEnergyTermW_taw`, with `tdF.bdΓ` in place of `(capTraceDataHemi_th m hm).bdΓ`. -/
def capEnergyTermL_tam (m : ℕ) (K : ℝ) (hK : 0 < K) (tdF : CapTraceData (Cap.flat m K hK))
    (α R : ℝ) {bd : TransH1 m R →ₗ[ℝ] TransH1 m R →ₗ[ℝ] ℝ} (gs : TransverseGroundState m α R bd)
    (ΦL : H1P (Cap.flat m K hK).body) : ℝ :=
  R⁻¹ * (∫ p in (Cap.flat m K hK).body, ‖ΦL.gz p‖ ^ 2)
    + (α * tdF.bdΓ ΦL ΦL - (m : ℝ) * α * massP ΦL)
    - (R * gs.nu - (m : ℝ) * α) * massP ΦL

/-! ## 3. The cap values of the trial extension, general `Cm Cp` -/

section GenericCaps

variable {Cm Cp : Cap m}

/-- **The left-cap value of the trial extension, in cap coordinates**, general `Cm Cp`. -/
theorem toFun_capLeft_trialAC_tam (hR : 0 < R) (hL : (Cm.K + Cp.K) * R < L)
    (W : Sobolev.H1 (bulkLength Cm Cp L R)) (ψ : TransH1 m R)
    {p : CapSpace m} (hp : p ∈ Cm.body) :
    (capLeft hR hL (R ^ ((m : ℝ) / 2)) (trialAC hR hL W ψ)).toFun p
      = W.toFun 0 * transLift m R ψ p.2 := by
  have hle : (-L / 2 + (-1 : ℝ) * R * p.1 : ℝ) ≤ -L / 2 + Cm.K * R := by
    have h1 : -Cm.K < p.1 := hp.1
    nlinarith [mul_pos hR (show (0:ℝ) < p.1 + Cm.K by linarith)]
  rw [capLeft, H1P.rescaleLeft, H1P.cast_toFun, H1P.rescaleP_toFun, restrictLeft_toFun,
    trialAC_toFun]
  show (R ^ ((m : ℝ) / 2)) * trialACFun Cm Cp L R W ψ
      (affP (-L / 2) (-1) R p) = _
  show (R ^ ((m : ℝ) / 2)) *
      (trialACProfile (-L / 2 + Cm.K * R) W (-L / 2 + (-1 : ℝ) * R * p.1)
        * ψ.toFun (R • p.2)) = _
  rw [trialACProfile_of_le (trialAC_bulkLength_pos hL).le W hle]
  simp only [transLift]
  ring

/-- **The right-cap value of the trial extension, in cap coordinates**, general `Cm Cp`. -/
theorem toFun_capRight_trialAC_tam (hR : 0 < R) (hL : (Cm.K + Cp.K) * R < L)
    (W : Sobolev.H1 (bulkLength Cm Cp L R)) (ψ : TransH1 m R)
    {p : CapSpace m} (hp : p ∈ Cp.body) :
    (capRight hR hL (R ^ ((m : ℝ) / 2)) (trialAC hR hL W ψ)).toFun p
      = W.toFun (bulkLength Cm Cp L R) * transLift m R ψ p.2 := by
  have hge : L / 2 - Cp.K * R ≤ L / 2 + (1 : ℝ) * R * p.1 := by
    have h1 : -Cp.K < p.1 := hp.1
    nlinarith [mul_pos hR (show (0:ℝ) < p.1 + Cp.K by linarith)]
  rw [capRight, H1P.rescaleRight, H1P.cast_toFun, H1P.rescaleP_toFun, restrictRight_toFun,
    trialAC_toFun]
  show (R ^ ((m : ℝ) / 2)) * trialACFun Cm Cp L R W ψ
      (affP (L / 2) 1 R p) = _
  show (R ^ ((m : ℝ) / 2)) *
      (trialACProfile (-L / 2 + Cm.K * R) W (L / 2 + (1 : ℝ) * R * p.1)
        * ψ.toFun (R • p.2)) = _
  have hge' : (-L / 2 + Cm.K * R) + bulkLength Cm Cp L R ≤ L / 2 + (1 : ℝ) * R * p.1 := by
    rw [trialAC_interface_add]; exact hge
  rw [trialACProfile_of_ge (trialAC_bulkLength_pos hL).le W hge']
  simp only [transLift]
  ring

/-! ## 4. The cap component of the tensor's boundary form, general `Cm Cp` -/

/-- **`bdΓ` only sees the a.e. class of `toFun`**, for an arbitrary `CapTraceData`. -/
theorem bdΓ_congr_ae_tam {C : Cap m} (td : CapTraceData C) {u v : H1P C.body}
    (h : u.toFun =ᵐ[volume.restrict C.body] v.toFun) (w : H1P C.body) :
    td.bdΓ u w = td.bdΓ v w := by
  have hsub : (u - v).toFun =ᵐ[volume.restrict C.body] 0 := by
    rw [H1P.sub_toFun_be]
    filter_upwards [h] with p hp
    simp [hp]
  have h0 := td.vanishes_ae (u - v) hsub w
  rw [map_sub, LinearMap.sub_apply] at h0
  linarith

/-- **The cap component of the tensor's boundary form, left cap, general `Cm Cp`.** -/
theorem bdΓ_capLeft_tam (tdM : CapTraceData Cm) (hR : 0 < R) (hL : (Cm.K + Cp.K) * R < L)
    (W : Sobolev.H1 (bulkLength Cm Cp L R)) (ψ : TransH1 m R)
    (Φ : H1P Cm.body) (hΦ : Φ.toFun = fun p => transLift m R ψ p.2) :
    tdM.bdΓ (capLeft hR hL (R ^ ((m : ℝ) / 2)) (trialAC hR hL W ψ))
        (capLeft hR hL (R ^ ((m : ℝ) / 2)) (trialAC hR hL W ψ))
      = W.toFun 0 ^ 2 * tdM.bdΓ Φ Φ := by
  set u := capLeft hR hL (R ^ ((m : ℝ) / 2)) (trialAC hR hL W ψ) with hu
  set v := W.toFun 0 • Φ with hv
  have htoeq : u.toFun =ᵐ[volume.restrict Cm.body] v.toFun := by
    refine (ae_restrict_iff' (measurableSet_capBody Cm)).2
      (Filter.Eventually.of_forall fun p hp => ?_)
    rw [hu, hv, H1P.smul_toFun]
    show (capLeft hR hL (R ^ ((m : ℝ) / 2)) (trialAC hR hL W ψ)).toFun p
        = W.toFun 0 * Φ.toFun p
    rw [toFun_capLeft_trialAC_tam hR hL W ψ hp, hΦ]
  have h1 := bdΓ_congr_ae_tam tdM htoeq u
  have h2 := tdM.bdΓ_symm v u
  have h3 := bdΓ_congr_ae_tam tdM htoeq v
  rw [h1, h2, h3, hv]
  simp only [map_smul, LinearMap.smul_apply, smul_eq_mul]
  ring

/-- **The cap component of the tensor's boundary form, right cap, general `Cm Cp`.** -/
theorem bdΓ_capRight_tam (tdP : CapTraceData Cp) (hR : 0 < R) (hL : (Cm.K + Cp.K) * R < L)
    (W : Sobolev.H1 (bulkLength Cm Cp L R)) (ψ : TransH1 m R)
    (Φ : H1P Cp.body) (hΦ : Φ.toFun = fun p => transLift m R ψ p.2) :
    tdP.bdΓ (capRight hR hL (R ^ ((m : ℝ) / 2)) (trialAC hR hL W ψ))
        (capRight hR hL (R ^ ((m : ℝ) / 2)) (trialAC hR hL W ψ))
      = W.toFun (bulkLength Cm Cp L R) ^ 2 * tdP.bdΓ Φ Φ := by
  set u := capRight hR hL (R ^ ((m : ℝ) / 2)) (trialAC hR hL W ψ) with hu
  set v := W.toFun (bulkLength Cm Cp L R) • Φ with hv
  have htoeq : u.toFun =ᵐ[volume.restrict Cp.body] v.toFun := by
    refine (ae_restrict_iff' (measurableSet_capBody Cp)).2
      (Filter.Eventually.of_forall fun p hp => ?_)
    rw [hu, hv, H1P.smul_toFun]
    show (capRight hR hL (R ^ ((m : ℝ) / 2)) (trialAC hR hL W ψ)).toFun p
        = W.toFun (bulkLength Cm Cp L R) * Φ.toFun p
    rw [toFun_capRight_trialAC_tam hR hL W ψ hp, hΦ]
  have h1 := bdΓ_congr_ae_tam tdP htoeq u
  have h2 := tdP.bdΓ_symm v u
  have h3 := bdΓ_congr_ae_tam tdP htoeq v
  rw [h1, h2, h3, hv]
  simp only [map_smul, LinearMap.smul_apply, smul_eq_mul]
  ring

/-! ## 5. The two physical cap terms, general `Cm Cp` -/

/-- **The left-cap mass of the trial extension, in terms of `capLiftW`**, general `Cm Cp`. -/
theorem massP_leftCap_tam (hR : 0 < R) (hL : (Cm.K + Cp.K) * R < L)
    (W : Sobolev.H1 (bulkLength Cm Cp L R)) (ψ : TransH1 m R)
    (Φ : H1P Cm.body) (hΦ : Φ.toFun = fun p => transLift m R ψ p.2) :
    (∫ p in leftCap Cm L R, (W.toFun 0 * ψ.toFun p.2) ^ 2)
      = R * (W.toFun 0 ^ 2 * massP Φ) := by
  have hbody := measurableSet_capBody Cm
  have hcov := setIntegral_image_affP (m := m) (-L / 2) (ε := -1) hR (by norm_num) hbody
    (fun q : CapSpace m => (W.toFun 0 * ψ.toFun q.2) ^ 2)
  have h0 : (∫ p in leftCap Cm L R, (W.toFun 0 * ψ.toFun p.2) ^ 2)
      = ∫ q in affP (-L / 2) (-1) R '' Cm.body, (W.toFun 0 * ψ.toFun q.2) ^ 2 := by
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
  have key : (∫ p in Cm.body,
        (W.toFun 0 * ψ.toFun ((affP (-L / 2) (-1) R p).2)) ^ 2)
      = (R ^ m)⁻¹ * (W.toFun 0 ^ 2 * massP Φ) := by
    rw [integral_congr_ae (.of_forall hpt), integral_const_mul, integral_const_mul]
    rfl
  rw [h0, hcov, key, pow_succ]
  have hRm : (R ^ m : ℝ) ≠ 0 := pow_ne_zero m hR.ne'
  field_simp

/-- **The right-cap mass of the trial extension, in terms of `capLiftW`**, general `Cm Cp`. -/
theorem massP_rightCap_tam (hR : 0 < R) (hL : (Cm.K + Cp.K) * R < L)
    (W : Sobolev.H1 (bulkLength Cm Cp L R)) (ψ : TransH1 m R)
    (Φ : H1P Cp.body) (hΦ : Φ.toFun = fun p => transLift m R ψ p.2) :
    (∫ p in rightCap Cp L R, (W.toFun (bulkLength Cm Cp L R) * ψ.toFun p.2) ^ 2)
      = R * (W.toFun (bulkLength Cm Cp L R) ^ 2 * massP Φ) := by
  have hbody := measurableSet_capBody Cp
  have hcov := setIntegral_image_affP (m := m) (L / 2) (ε := 1) hR (by norm_num) hbody
    (fun q : CapSpace m => (W.toFun (bulkLength Cm Cp L R) * ψ.toFun q.2) ^ 2)
  have h0 : (∫ p in rightCap Cp L R, (W.toFun (bulkLength Cm Cp L R) * ψ.toFun p.2) ^ 2)
      = ∫ q in affP (L / 2) 1 R '' Cp.body,
          (W.toFun (bulkLength Cm Cp L R) * ψ.toFun q.2) ^ 2 := by
    rw [← rightCap_eq_image]
  have hpt : ∀ p : CapSpace m,
      (W.toFun (bulkLength Cm Cp L R) * ψ.toFun ((affP (L / 2) 1 R p).2)) ^ 2
        = (R ^ m)⁻¹ * (W.toFun (bulkLength Cm Cp L R) ^ 2 * Φ.toFun p ^ 2) := by
    intro p
    rw [show (affP (L / 2) 1 R p).2 = R • p.2 from rfl, hΦ]
    show (W.toFun (bulkLength Cm Cp L R) * ψ.toFun (R • p.2)) ^ 2
        = (R ^ m)⁻¹ * (W.toFun (bulkLength Cm Cp L R) ^ 2 * transLift m R ψ p.2 ^ 2)
    rw [transLift_sq m hR ψ p.2]
    have hRm : (R ^ m : ℝ) ≠ 0 := pow_ne_zero m hR.ne'
    field_simp
  have key : (∫ p in Cp.body,
        (W.toFun (bulkLength Cm Cp L R) * ψ.toFun ((affP (L / 2) 1 R p).2)) ^ 2)
      = (R ^ m)⁻¹ * (W.toFun (bulkLength Cm Cp L R) ^ 2 * massP Φ) := by
    rw [integral_congr_ae (.of_forall hpt), integral_const_mul, integral_const_mul]
    rfl
  rw [h0, hcov, key, pow_succ]
  have hRm : (R ^ m : ℝ) ≠ 0 := pow_ne_zero m hR.ne'
  field_simp

/-- **The left-cap Dirichlet energy of the trial extension, in terms of `capLiftW`**, general
`Cm Cp`. -/
theorem dirichletP_leftCap_tam (hR : 0 < R) (hL : (Cm.K + Cp.K) * R < L)
    (W : Sobolev.H1 (bulkLength Cm Cp L R)) (ψ : TransH1 m R)
    (Φ : H1P Cm.body)
    (hgz : Φ.gz = fun p => (R ^ ((m : ℝ) / 2) * R) • ψ.grad (R • p.2)) :
    (∫ p in leftCap Cm L R, ‖W.toFun 0 • ψ.grad p.2‖ ^ 2)
      = R⁻¹ * (W.toFun 0 ^ 2 * ∫ p in Cm.body, ‖Φ.gz p‖ ^ 2) := by
  have hbody := measurableSet_capBody Cm
  have hcov := setIntegral_image_affP (m := m) (-L / 2) (ε := -1) hR (by norm_num) hbody
    (fun q : CapSpace m => ‖W.toFun 0 • ψ.grad q.2‖ ^ 2)
  have h0 : (∫ p in leftCap Cm L R, ‖W.toFun 0 • ψ.grad p.2‖ ^ 2)
      = ∫ q in affP (-L / 2) (-1) R '' Cm.body, ‖W.toFun 0 • ψ.grad q.2‖ ^ 2 := by
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
  have key : (∫ p in Cm.body,
        ‖W.toFun 0 • ψ.grad ((affP (-L / 2) (-1) R p).2)‖ ^ 2)
      = (R ^ (m + 2))⁻¹ * (W.toFun 0 ^ 2 * ∫ p in Cm.body, ‖Φ.gz p‖ ^ 2) := by
    rw [integral_congr_ae (.of_forall hpt), integral_const_mul, integral_const_mul]
  rw [h0, hcov, key]
  have hRm2 : (R ^ (m + 2) : ℝ) ≠ 0 := hR2m.ne'
  have hR0 : (R : ℝ) ≠ 0 := hR.ne'
  field_simp
  rw [pow_succ, pow_succ]
  ring

/-- **The right-cap Dirichlet energy of the trial extension, in terms of `capLiftW`**, general
`Cm Cp`. -/
theorem dirichletP_rightCap_tam (hR : 0 < R) (hL : (Cm.K + Cp.K) * R < L)
    (W : Sobolev.H1 (bulkLength Cm Cp L R)) (ψ : TransH1 m R)
    (Φ : H1P Cp.body)
    (hgz : Φ.gz = fun p => (R ^ ((m : ℝ) / 2) * R) • ψ.grad (R • p.2)) :
    (∫ p in rightCap Cp L R, ‖W.toFun (bulkLength Cm Cp L R) • ψ.grad p.2‖ ^ 2)
      = R⁻¹ * (W.toFun (bulkLength Cm Cp L R) ^ 2
          * ∫ p in Cp.body, ‖Φ.gz p‖ ^ 2) := by
  have hbody := measurableSet_capBody Cp
  have hcov := setIntegral_image_affP (m := m) (L / 2) (ε := 1) hR (by norm_num) hbody
    (fun q : CapSpace m =>
      ‖W.toFun (bulkLength Cm Cp L R) • ψ.grad q.2‖ ^ 2)
  have h0 : (∫ p in rightCap Cp L R,
        ‖W.toFun (bulkLength Cm Cp L R) • ψ.grad p.2‖ ^ 2)
      = ∫ q in affP (L / 2) 1 R '' Cp.body,
          ‖W.toFun (bulkLength Cm Cp L R) • ψ.grad q.2‖ ^ 2 := by
    rw [← rightCap_eq_image]
  have hR2m : (0 : ℝ) < R ^ (m + 2) := by positivity
  have hpt : ∀ p : CapSpace m,
      ‖W.toFun (bulkLength Cm Cp L R)
          • ψ.grad ((affP (L / 2) 1 R p).2)‖ ^ 2
        = (R ^ (m + 2))⁻¹ *
          (W.toFun (bulkLength Cm Cp L R) ^ 2 * ‖Φ.gz p‖ ^ 2) := by
    intro p
    rw [show (affP (L / 2) 1 R p).2 = R • p.2 from rfl, hgz]
    show ‖W.toFun (bulkLength Cm Cp L R) • ψ.grad (R • p.2)‖ ^ 2
        = (R ^ (m + 2))⁻¹ *
          (W.toFun (bulkLength Cm Cp L R) ^ 2
            * ‖(R ^ ((m : ℝ) / 2) * R) • ψ.grad (R • p.2)‖ ^ 2)
    rw [norm_smul, norm_smul, Real.norm_eq_abs, Real.norm_eq_abs, mul_pow, mul_pow, sq_abs,
      sq_abs, mul_pow, sq_rpow_half m hR]
    have hRm2 : (R ^ (m + 2) : ℝ) ≠ 0 := hR2m.ne'
    field_simp
    ring
  have key : (∫ p in Cp.body,
        ‖W.toFun (bulkLength Cm Cp L R)
            • ψ.grad ((affP (L / 2) 1 R p).2)‖ ^ 2)
      = (R ^ (m + 2))⁻¹ *
        (W.toFun (bulkLength Cm Cp L R) ^ 2
          * ∫ p in Cp.body, ‖Φ.gz p‖ ^ 2) := by
    rw [integral_congr_ae (.of_forall hpt), integral_const_mul, integral_const_mul]
  rw [h0, hcov, key]
  have hRm2 : (R ^ (m + 2) : ℝ) ≠ 0 := hR2m.ne'
  have hR0 : (R : ℝ) ≠ 0 := hR.ne'
  field_simp
  rw [pow_succ, pow_succ]
  ring

/-! ## 6. The bulk part of the tensor's boundary form, general `Cm Cp` -/

/-- **The bulk part of the tensor's boundary form**, general `Cm Cp`. -/
theorem bdCyl_bulk_tam (hR : 0 < R) (hL : (Cm.K + Cp.K) * R < L)
    (W : Sobolev.H1 (bulkLength Cm Cp L R)) (ψ : TransH1 m R) :
    bdCyl (bdR m R) (restrictBulkP hR (trialAC hR hL W ψ))
        (restrictBulkP hR (trialAC hR hL W ψ))
      = Sobolev.mass (bulkLength Cm Cp L R) W * bdR m R ψ ψ := by
  have hab : (-L / 2 + Cm.K * R) + bulkLength Cm Cp L R
      = L / 2 - Cp.K * R := trialAC_interface_add
  have hℓ0 : (0 : ℝ) ≤ bulkLength Cm Cp L R := (trialAC_bulkLength_pos hL).le
  have hslice : ∀ x ∈ Ioo (-L / 2 + Cm.K * R) (L / 2 - Cp.K * R),
      slice (restrictBulkP hR (trialAC hR hL W ψ)) x
        = W.toFun (x - (-L / 2 + Cm.K * R)) • ψ := by
    intro x hx
    have hmem1 : (-L / 2 + Cm.K * R) ≤ x := hx.1.le
    have hmem2 : x ≤ (-L / 2 + Cm.K * R) + bulkLength Cm Cp L R
        := by rw [hab]; exact hx.2.le
    have heq1 : (fun z => (restrictBulkP hR (trialAC hR hL W ψ)).toFun (x, z))
        = (W.toFun (x - (-L / 2 + Cm.K * R)) • ψ).toFun := by
      funext z
      rw [restrictBulkP_toFun, trialAC_toFun, Weak.H1.smul_toFun]
      show trialACFun Cm Cp L R W ψ (x, z)
          = (W.toFun (x - (-L / 2 + Cm.K * R)) • ψ.toFun) z
      show trialACProfile (-L / 2 + Cm.K * R) W x * ψ.toFun z = _
      rw [trialACProfile_of_mem W hmem1 hmem2, Pi.smul_apply, smul_eq_mul]
    have heq2 : (fun z => (restrictBulkP hR (trialAC hR hL W ψ)).gz (x, z))
        = (W.toFun (x - (-L / 2 + Cm.K * R)) • ψ).grad := by
      funext z
      show (trialAC hR hL W ψ).gz (x, z) = _
      rw [trialAC_gz, Weak.H1.smul_grad]
      show trialACGz Cm Cp L R W ψ (x, z)
          = (W.toFun (x - (-L / 2 + Cm.K * R)) • ψ.grad) z
      show trialACProfile (-L / 2 + Cm.K * R) W x • ψ.grad z = _
      rw [trialACProfile_of_mem W hmem1 hmem2, Pi.smul_apply]
    have hg1 : Weak.HasWeakGrad (transverseBall m R)
        (fun z => (restrictBulkP hR (trialAC hR hL W ψ)).toFun (x, z))
        (fun z => (restrictBulkP hR (trialAC hR hL W ψ)).gz (x, z)) := by
      rw [heq1, heq2]
      exact (W.toFun (x - (-L / 2 + Cm.K * R)) • ψ).hasWeakGrad
    have hg2 : MemLp (fun z => (restrictBulkP hR (trialAC hR hL W ψ)).toFun (x, z)) 2
        (volume.restrict (transverseBall m R)) := by
      rw [heq1]; exact (W.toFun (x - (-L / 2 + Cm.K * R)) • ψ).memL2
    have hg3 : MemLp (fun z => (restrictBulkP hR (trialAC hR hL W ψ)).gz (x, z)) 2
        (volume.restrict (transverseBall m R)) := by
      rw [heq2]; exact (W.toFun (x - (-L / 2 + Cm.K * R)) • ψ).grad_memL2
    have hgood : IsGoodSlice (restrictBulkP hR (trialAC hR hL W ψ)) x := ⟨hg1, hg2, hg3⟩
    refine Weak.H1.ext ?_ ?_
    · rw [slice_toFun hgood]; exact heq1
    · rw [slice_grad hgood]; exact heq2
  have hbd : ∀ x ∈ Ioo (-L / 2 + Cm.K * R) (L / 2 - Cp.K * R),
      bdR m R (slice (restrictBulkP hR (trialAC hR hL W ψ)) x)
          (slice (restrictBulkP hR (trialAC hR hL W ψ)) x)
        = W.toFun (x - (-L / 2 + Cm.K * R)) ^ 2 * bdR m R ψ ψ := by
    intro x hx
    rw [hslice x hx]
    simp only [map_smul, LinearMap.smul_apply, smul_eq_mul]
    ring
  calc bdCyl (bdR m R) (restrictBulkP hR (trialAC hR hL W ψ))
        (restrictBulkP hR (trialAC hR hL W ψ))
      = ∫ x in Ioo (-L / 2 + Cm.K * R) (L / 2 - Cp.K * R),
          W.toFun (x - (-L / 2 + Cm.K * R)) ^ 2 * bdR m R ψ ψ := by
        rw [bdCyl]; exact setIntegral_congr_fun measurableSet_Ioo hbd
    _ = (∫ x in Ioo (-L / 2 + Cm.K * R) (L / 2 - Cp.K * R),
          W.toFun (x - (-L / 2 + Cm.K * R)) ^ 2) * bdR m R ψ ψ :=
        integral_mul_const _ _
    _ = Sobolev.mass (bulkLength Cm Cp L R) W * bdR m R ψ ψ := by
        rw [← hab, setIntegral_trialACProfile_sq hℓ0 W]

end GenericCaps

/-! ## 7. The trace split of the trial extension, at the mixed cap pair -/

/-- **`bd_trialAC_tam`: the trace split of the trial extension, for a weak transverse ground
state, at the mixed flat/hemisphere cap pair.** -/
theorem bd_trialAC_tam (hm : 1 ≤ m) (K : ℝ) (hK : 0 < K) (tdF : CapTraceData (Cap.flat m K hK))
    (hR : 0 < R) (hL : ((Cap.flat m K hK).K + (Cap.hemisphere m).K) * R < L)
    (W : Sobolev.H1 (bulkLength (Cap.flat m K hK) (Cap.hemisphere m) L R))
    {bd : TransH1 m R →ₗ[ℝ] TransH1 m R →ₗ[ℝ] ℝ} (gs : TransverseGroundState m α R bd)
    (td : TraceData (Cap.flat m K hK) (Cap.hemisphere m) L R)
    (hsplit : TraceSplitMixed_tam hm K hK tdF hR hL td)
    (ΦL : H1P (Cap.flat m K hK).body) (hΦL : ΦL.toFun = fun p => transLift m R gs.psi p.2)
    (ΦR : H1P (Cap.hemisphere m).body) (hΦR : ΦR.toFun = fun p => transLift m R gs.psi p.2) :
    td.bd (trialAC hR hL W gs.psi) (trialAC hR hL W gs.psi)
      = W.toFun 0 ^ 2 * tdF.bdΓ ΦL ΦL
        + Sobolev.mass (bulkLength (Cap.flat m K hK) (Cap.hemisphere m) L R) W
            * bdR m R gs.psi gs.psi
        + W.toFun (bulkLength (Cap.flat m K hK) (Cap.hemisphere m) L R) ^ 2
            * (capTraceDataHemi_th m hm).bdΓ ΦR ΦR := by
  rw [hsplit (trialAC hR hL W gs.psi), capScale_taw m hR,
    bdΓ_capLeft_tam tdF hR hL W gs.psi ΦL hΦL, bdCyl_bulk_tam hR hL W gs.psi,
    bdΓ_capRight_tam (capTraceDataHemi_th m hm) hR hL W gs.psi ΦR hΦR]
  ring

/-- **`renormEnergy_trialAC_tam`: `eq:trial-energy`, exact form, for a weak transverse ground
state, at the mixed flat/hemisphere cap pair.** -/
theorem renormEnergy_trialAC_tam (hm : 1 ≤ m) (K : ℝ) (hK : 0 < K)
    (tdF : CapTraceData (Cap.flat m K hK)) (hR : 0 < R)
    (hL : ((Cap.flat m K hK).K + (Cap.hemisphere m).K) * R < L)
    (W : Sobolev.H1 (bulkLength (Cap.flat m K hK) (Cap.hemisphere m) L R))
    (gs : TransverseGroundState m α R (bdR m R))
    (td : TraceData (Cap.flat m K hK) (Cap.hemisphere m) L R)
    (hsplit : TraceSplitMixed_tam hm K hK tdF hR hL td)
    (ΦL : H1P (Cap.flat m K hK).body) (hΦLtoFun : ΦL.toFun = fun p => transLift m R gs.psi p.2)
    (hΦLgz : ΦL.gz = fun p => (R ^ ((m : ℝ) / 2) * R) • gs.psi.grad (R • p.2))
    (ΦR : H1P (Cap.hemisphere m).body) (hΦRtoFun : ΦR.toFun = fun p => transLift m R gs.psi p.2)
    (hΦRgz : ΦR.gz = fun p => (R ^ ((m : ℝ) / 2) * R) • gs.psi.grad (R • p.2)) :
    dirichletP (trialAC hR hL W gs.psi)
        + α * td.bd (trialAC hR hL W gs.psi) (trialAC hR hL W gs.psi)
        - gs.nu * massP (trialAC hR hL W gs.psi)
      = Sobolev.dirichlet (bulkLength (Cap.flat m K hK) (Cap.hemisphere m) L R) W
        + W.toFun 0 ^ 2 * capEnergyTermL_tam m K hK tdF α R gs ΦL
        + W.toFun (bulkLength (Cap.flat m K hK) (Cap.hemisphere m) L R) ^ 2
            * capEnergyTermW_taw m hm α R gs ΦR := by
  have hbulk : Weak.dirichlet gs.psi + α * bdR m R gs.psi gs.psi = gs.nu := by
    have h := gs.weak_eq gs.psi
    rw [qBilin_self, NBilin_self, gs.normalized, mul_one, qB] at h
    exact h
  rw [dirichletP_trialAC, massP_trialAC,
    bd_trialAC_tam hm K hK tdF hR hL W gs td hsplit ΦL hΦLtoFun ΦR hΦRtoFun,
    massP_leftCap_tam hR hL W gs.psi ΦL hΦLtoFun, massP_rightCap_tam hR hL W gs.psi ΦR hΦRtoFun,
    dirichletP_leftCap_tam hR hL W gs.psi ΦL hΦLgz, dirichletP_rightCap_tam hR hL W gs.psi ΦR hΦRgz,
    gs.normalized]
  simp only [capEnergyTermL_tam, capEnergyTermW_taw]
  linear_combination
    (Sobolev.mass (bulkLength (Cap.flat m K hK) (Cap.hemisphere m) L R) W) * hbulk

/-! ## 8. The `trial_energy` field, mixed cap pair -/

/-- **`trial_energy_field_tam`: the `trial_energy` field of `GlobalComparisonData`, for a weak
transverse ground state, at the mixed flat/hemisphere cap pair.**  The constant `Ctr` is the
maximum of the two (uniform, `R`-independent) cap bound constants, taken here as the single
hypothesis-level constant `A` (as in `trial_energy_field_taw`), used for both caps. -/
theorem trial_energy_field_tam (hm : 1 ≤ m) (K : ℝ) (hK : 0 < K)
    (tdF : CapTraceData (Cap.flat m K hK)) (α : ℝ) (hα : 0 < α) (L A : ℝ) :
    ∃ Ctr : ℝ, 0 ≤ Ctr ∧ ∀ (R : ℝ) (hR : 0 < R), R ≤ 1 →
      ∀ (hL : ((Cap.flat m K hK).K + (Cap.hemisphere m).K) * R < L)
        (gs : TransverseGroundState m α R (bdR m R))
        (td : TraceData (Cap.flat m K hK) (Cap.hemisphere m) L R)
        (hsplit : TraceSplitMixed_tam hm K hK tdF hR hL td)
        (ΦL : H1P (Cap.flat m K hK).body) (hΦLtoFun : ΦL.toFun = fun p => transLift m R gs.psi p.2)
        (hΦLgz : ΦL.gz = fun p => (R ^ ((m : ℝ) / 2) * R) • gs.psi.grad (R • p.2))
        (ΦR : H1P (Cap.hemisphere m).body)
        (hΦRtoFun : ΦR.toFun = fun p => transLift m R gs.psi p.2)
        (hΦRgz : ΦR.gz = fun p => (R ^ ((m : ℝ) / 2) * R) • gs.psi.grad (R • p.2))
        (hcapL : |capEnergyTermL_tam m K hK tdF α R gs ΦL - (Cap.flat m K hK).beta α|
          ≤ Ctr * R)
        (hcapR : |capEnergyTermW_taw m hm α R gs ΦR - (Cap.hemisphere m).beta α| ≤ Ctr * R)
        (v : Sobolev.H1Q (bulkLength (Cap.flat m K hK) (Cap.hemisphere m) L R)),
        robinFormPQ (isOpen_thinDomain hR hL) td.bd td.vanishesOnNullAEP α
            (liftQ hR hL gs.psi v)
          - gs.nu * massPQ (liftQ hR hL gs.psi v)
        ≤ Sobolev.robinFormQ ((Cap.flat m K hK).beta α + Ctr * R)
            ((Cap.hemisphere m).beta α + Ctr * R)
            (bulkLength (Cap.flat m K hK) (Cap.hemisphere m) L R) v := by
  refine ⟨|A|, abs_nonneg A, ?_⟩
  intro R hR hR1 hL gs td hsplit ΦL hΦLtoFun hΦLgz ΦR hΦRtoFun hΦRgz hcapL hcapR v
  obtain ⟨W, rfl⟩ := Submodule.Quotient.mk_surjective (Sobolev.nullOff _) v
  rw [liftQ_mk, robinFormPQ_mk, massPQ_mk, Sobolev.robinFormQ_mk,
    renormEnergy_trialAC_tam hm K hK tdF hR hL W gs td hsplit ΦL hΦLtoFun hΦLgz ΦR hΦRtoFun hΦRgz,
    Sobolev.robinForm]
  have hb0L : capEnergyTermL_tam m K hK tdF α R gs ΦL ≤ (Cap.flat m K hK).beta α + |A| * R := by
    have := (abs_le.1 hcapL).2
    linarith
  have hb0R : capEnergyTermW_taw m hm α R gs ΦR ≤ (Cap.hemisphere m).beta α + |A| * R := by
    have := (abs_le.1 hcapR).2
    linarith
  have h1 : W.toFun 0 ^ 2 * capEnergyTermL_tam m K hK tdF α R gs ΦL
      ≤ ((Cap.flat m K hK).beta α + |A| * R) * W.toFun 0 ^ 2 := by
    nlinarith [sq_nonneg (W.toFun 0), hb0L]
  have h2 : W.toFun (bulkLength (Cap.flat m K hK) (Cap.hemisphere m) L R) ^ 2
        * capEnergyTermW_taw m hm α R gs ΦR
      ≤ ((Cap.hemisphere m).beta α + |A| * R)
          * W.toFun (bulkLength (Cap.flat m K hK) (Cap.hemisphere m) L R) ^ 2 := by
    nlinarith [sq_nonneg (W.toFun (bulkLength (Cap.flat m K hK) (Cap.hemisphere m) L R)), hb0R]
  linarith

end

end RobinCaps.ThinDomain
