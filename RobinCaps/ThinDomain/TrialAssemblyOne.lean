import RobinCaps.ThinDomain.TrialAC
import RobinCaps.ThinDomain.TrialBound
import RobinCaps.ThinDomain.TraceOne
import RobinCaps.ThinDomain.Assembly

/-!
# The trial side of the `m = 1` global comparison

This file assembles, for transverse dimension `m = 1`, the **`trial_energy` field** of
`RobinCaps.ThinDomain.GlobalComparisonData` out of

* the absolutely-continuous trial extension `trialAC` / `liftQ` of
  `RobinCaps/ThinDomain/TrialAC.lean` (the exact mass and Dirichlet splittings
  `massP_trialAC`, `dirichletP_trialAC`),
* the cap estimates `cap_upper_gradient`, `cap_upper_J`, `cap_mass_le` of
  `RobinCaps/ThinDomain/TrialBound.lean` (packaged in `capEnergyTerm_sub_beta`), and
* the planar trace datum `traceDataOne` of `RobinCaps/ThinDomain/TraceOne.lean`, whose
  consistency field `tr_continuous` identifies the abstract boundary form with the honest
  surface integral `boundaryEnergy` on functions continuous up to `∂Ω_R`.

The transverse expansions (`lem:transverse`) are taken as a hypothesis, exactly as in
`TrialBound.lean`, through `TransverseExpansionData`.

## Contents

1. `continuous_trialACFun_ta`, `boundaryEnergy_trialAC_ta` — the analogue of
   `boundaryEnergy_trialExt` for the merely absolutely continuous axial factor.
2. `bd_trialAC_ta`, `robinFormPQ_liftQ_ta`, `massPQ_liftQ_ta` — the quotient Robin form of
   the trial lift through the concrete pieces.
3. `renormEnergy_trialAC_ta` — the exact renormalized-energy splitting `eq:trial-energy`
   for `trialAC`.
4. `trialAC_energy_le_ta`, `trial_energy_field_one` — the `trial_energy` field.
5. `trial_mass_field_one` — the `trial_mass` field in the same shape.

No `sorry`, `admit`, `axiom` or `native_decide` occurs in this file.
-/

open MeasureTheory Set Metric Filter

open scoped ENNReal Topology InnerProductSpace

namespace RobinCaps.ThinDomain

open RobinCaps.Sobolev RobinCaps.Domain

noncomputable section

variable {m : ℕ} {α R : ℝ} {bd : TransH1 m R →ₗ[ℝ] TransH1 m R →ₗ[ℝ] ℝ}

/-! ## 1. The boundary energy of the absolutely continuous trial extension -/

section Boundary

variable {Cm Cp : Cap m} {L : ℝ}

/-- The trial extension `𝒯_R W` is continuous on **all** of `CapSpace m` as soon as the
transverse profile is continuous: the clamped axial profile is continuous by
`continuous_trialACProfile`. -/
theorem continuous_trialACFun_ta (hL : (Cm.K + Cp.K) * R < L)
    (W : Sobolev.H1 (bulkLength Cm Cp L R)) {ψ : TransH1 m R}
    (hψ : Continuous fun z => ψ.toFun z) :
    Continuous (trialACFun Cm Cp L R W ψ) :=
  ((continuous_trialACProfile (trialAC_bulkLength_pos hL).le W).comp continuous_fst).mul
    (hψ.comp continuous_snd)

/-- In particular the trial extension is continuous up to the boundary of `Ω_R`, which is the
hypothesis of the `tr_continuous` field of `TraceData`. -/
theorem continuousOn_trialACFun_ta (hR : 0 < R) (hL : (Cm.K + Cp.K) * R < L)
    (W : Sobolev.H1 (bulkLength Cm Cp L R)) {ψ : TransH1 m R}
    (hψ : Continuous fun z => ψ.toFun z) :
    ContinuousOn (trialAC hR hL W ψ).toFun (closure (thinDomain Cm Cp L R)) :=
  (continuous_trialACFun_ta hL W hψ).continuousOn

/-- The `L²` norm of the clamped profile over the bulk interval is the interval mass of `W`. -/
theorem setIntegral_trialACProfile_sq_bulk_ta (hL : (Cm.K + Cp.K) * R < L)
    (W : Sobolev.H1 (bulkLength Cm Cp L R)) :
    (∫ x in Ioo (-L/2 + Cm.K * R) (L/2 - Cp.K * R),
        trialACProfile (-L/2 + Cm.K * R) W x ^ 2)
      = Sobolev.mass (bulkLength Cm Cp L R) W := by
  have hℓ : (0:ℝ) ≤ bulkLength Cm Cp L R := (trialAC_bulkLength_pos hL).le
  rw [← trialAC_interface_add (Cm := Cm) (Cp := Cp) (L := L) (R := R)]
  have h : (∫ x in Ioo (-L/2 + Cm.K * R)
        ((-L/2 + Cm.K * R) + bulkLength Cm Cp L R),
          trialACProfile (-L/2 + Cm.K * R) W x ^ 2)
      = ∫ x in Ioo (-L/2 + Cm.K * R) ((-L/2 + Cm.K * R) + bulkLength Cm Cp L R),
          W.toFun (x - (-L/2 + Cm.K * R)) ^ 2 :=
    setIntegral_congr_fun measurableSet_Ioo fun x hx => by
      rw [trialACProfile_of_mem W hx.1.le hx.2.le]
  rw [h, setIntegral_trialACProfile_sq hℓ W]

/-- **The boundary energy of the absolutely continuous trial extension.**  This is the exact
analogue of `boundaryEnergy_trialExt`: only the *values* of the axial factor enter, so the
bulk lateral part is `M[W] · ∫_{∂B_m(R)} ψ_R²` and the two caps contribute
`W(0)² J[Ψ_R]` and `W(ℓ_R)² J[Ψ_R]`. -/
theorem boundaryEnergy_trialAC_ta (hm : 1 ≤ m) (Cm Cp : Cap m) (L : ℝ) (hR : 0 < R)
    (hL : (Cm.K + Cp.K) * R < L) (W : Sobolev.H1 (bulkLength Cm Cp L R))
    (gsr : TransverseGroundStateReg m α R bd) :
    boundaryEnergy Cm Cp L R (trialACFun Cm Cp L R W gsr.psi)
      = Sobolev.mass (bulkLength Cm Cp L R) W
            * sphereIntegral m R (fun z => gsr.psi.toFun z ^ 2)
        + W.toFun 0 ^ 2 * capJterm Cm (transLift m R gsr.psi)
        + W.toFun (bulkLength Cm Cp L R) ^ 2 * capJterm Cp (transLift m R gsr.psi) := by
  have hab := interface_lt (Cm := Cm) (Cp := Cp) hR hL
  have hℓ : (0:ℝ) ≤ bulkLength Cm Cp L R := (trialAC_bulkLength_pos hL).le
  have hKmR : (0:ℝ) < Cm.K * R := mul_pos Cm.hK hR
  have hKpR : (0:ℝ) < Cp.K * R := mul_pos Cp.hK hR
  have hcont : Continuous (trialACFun Cm Cp L R W gsr.psi) :=
    continuous_trialACFun_ta hL W gsr.psiC1.continuous
  have hsplit := boundaryEnergy_tensor_split_of_continuous' (Cm := Cm) (Cp := Cp) (L := L)
    (R := R) hm hR hL (trialACFun Cm Cp L R W gsr.psi)
    (trialACProfile (-L/2 + Cm.K * R) W) (fun z => gsr.psi.toFun z) hcont
    (fun _ _ _ => rfl)
  rw [hsplit, integral_Icc_eq_integral_Ioo, setIntegral_trialACProfile_sq_bulk_ta hL W]
  -- the left cap
  have hlatL : capLateralIntegral Cm (fun p => trialACFun Cm Cp L R W gsr.psi
        (-L/2 - R * p.1, R • p.2) ^ 2)
      = capLateralIntegral Cm (fun p => W.toFun 0 ^ 2
          * gsr.psi.toFun (R • p.2) ^ 2) := by
    refine capLateralIntegral_congr Cm fun s hs ω => ?_
    have hlt : (-L/2 - R * s : ℝ) ≤ -L/2 + Cm.K * R := by nlinarith [hs.1, hR]
    show (trialACProfile (-L/2 + Cm.K * R) W (-L/2 - R * s) * _) ^ 2 = _
    rw [trialACProfile_of_le hℓ W hlt]
    ring
  have hdiskL : (∫ z in ball (0 : EuclideanSpace ℝ (Fin m)) (Cm.θ 0),
        trialACFun Cm Cp L R W gsr.psi (-L/2, R • z) ^ 2)
      = W.toFun 0 ^ 2
        * ∫ z in ball (0 : EuclideanSpace ℝ (Fin m)) (Cm.θ 0), gsr.psi.toFun (R • z) ^ 2 := by
    rw [← integral_const_mul]
    refine setIntegral_congr_fun measurableSet_ball fun z _ => ?_
    show (trialACProfile (-L/2 + Cm.K * R) W (-L/2) * _) ^ 2 = _
    rw [trialACProfile_of_le hℓ W (by linarith)]
    ring
  -- the right cap
  have hlatR : capLateralIntegral Cp (fun p => trialACFun Cm Cp L R W gsr.psi
        (L/2 + R * p.1, R • p.2) ^ 2)
      = capLateralIntegral Cp (fun p => W.toFun (bulkLength Cm Cp L R) ^ 2
          * gsr.psi.toFun (R • p.2) ^ 2) := by
    refine capLateralIntegral_congr Cp fun s hs ω => ?_
    have hgt : (-L/2 + Cm.K * R) + bulkLength Cm Cp L R ≤ (L/2 + R * s : ℝ) := by
      rw [trialAC_interface_add]; nlinarith [hs.1, hR]
    show (trialACProfile (-L/2 + Cm.K * R) W (L/2 + R * s) * _) ^ 2 = _
    rw [trialACProfile_of_ge hℓ W hgt]
    ring
  have hdiskR : (∫ z in ball (0 : EuclideanSpace ℝ (Fin m)) (Cp.θ 0),
        trialACFun Cm Cp L R W gsr.psi (L/2, R • z) ^ 2)
      = W.toFun (bulkLength Cm Cp L R) ^ 2
        * ∫ z in ball (0 : EuclideanSpace ℝ (Fin m)) (Cp.θ 0), gsr.psi.toFun (R • z) ^ 2 := by
    rw [← integral_const_mul]
    refine setIntegral_congr_fun measurableSet_ball fun z _ => ?_
    have hge : (-L/2 + Cm.K * R) + bulkLength Cm Cp L R ≤ (L/2 : ℝ) := by
      rw [trialAC_interface_add]; linarith
    show (trialACProfile (-L/2 + Cm.K * R) W (L/2) * _) ^ 2 = _
    rw [trialACProfile_of_ge hℓ W hge]
    ring
  rw [hlatL, capLateralIntegral_const_mul, hdiskL, hlatR, capLateralIntegral_const_mul, hdiskR,
    capJterm_transLift hR Cm gsr.psi, capJterm_transLift hR Cp gsr.psi]
  ring

end Boundary

/-! ## 2. The two cap contributions in cap coordinates -/

section Caps

variable {Cm Cp : Cap m} {L : ℝ}

/-- The left cap mass of the trial extension, in cap coordinates. -/
theorem setIntegral_leftCap_sq_ta (Cm Cp : Cap m) (L : ℝ) (hR : 0 < R)
    (hL : (Cm.K + Cp.K) * R < L) (c : ℝ) (gsr : TransverseGroundStateReg m α R bd) :
    (∫ p in leftCap Cm L R, (c * gsr.psi.toFun p.2) ^ 2)
      = c ^ 2 * (R ^ (m + 1) * ∫ p in Cm.body, gsr.psi.toFun (R • p.2) ^ 2) :=
  massP_capTrialLeft_eq Cm Cp L hR hL (fun _ => c) gsr

/-- The right cap mass of the trial extension, in cap coordinates. -/
theorem setIntegral_rightCap_sq_ta (Cm Cp : Cap m) (L : ℝ) (hR : 0 < R)
    (hL : (Cm.K + Cp.K) * R < L) (c : ℝ) (gsr : TransverseGroundStateReg m α R bd) :
    (∫ p in rightCap Cp L R, (c * gsr.psi.toFun p.2) ^ 2)
      = c ^ 2 * (R ^ (m + 1) * ∫ p in Cp.body, gsr.psi.toFun (R • p.2) ^ 2) :=
  massP_capTrialRight_eq Cm Cp L hR hL (fun _ => c) gsr

/-- On the left cap the chosen weak gradient of `ψ_R` is its classical gradient. -/
theorem grad_eq_on_leftCap_ta (hR : 0 < R) (hL : (Cm.K + Cp.K) * R < L)
    (gsr : TransverseGroundStateReg m α R bd) {p : CapSpace m} (hp : p ∈ leftCap Cm L R) :
    gsr.psi.grad p.2 = Weak.classicalGrad (fun z => gsr.psi.toFun z) p.2 :=
  gsr.grad_eq p.2 (mem_ball_zero_iff.2
    (mem_thinDomain_norm_lt hR hL (leftCap_subset (Cp := Cp) hR hL hp)))

/-- On the right cap the chosen weak gradient of `ψ_R` is its classical gradient. -/
theorem grad_eq_on_rightCap_ta (hR : 0 < R) (hL : (Cm.K + Cp.K) * R < L)
    (gsr : TransverseGroundStateReg m α R bd) {p : CapSpace m} (hp : p ∈ rightCap Cp L R) :
    gsr.psi.grad p.2 = Weak.classicalGrad (fun z => gsr.psi.toFun z) p.2 :=
  gsr.grad_eq p.2 (mem_ball_zero_iff.2
    (mem_thinDomain_norm_lt hR hL (rightCap_subset (Cm := Cm) hR hL hp)))

/-- The left cap energy of the trial extension, in cap coordinates. -/
theorem setIntegral_leftCap_grad_sq_ta (Cm Cp : Cap m) (L : ℝ) (hR : 0 < R)
    (hL : (Cm.K + Cp.K) * R < L) (c : ℝ) (gsr : TransverseGroundStateReg m α R bd) :
    (∫ p in leftCap Cm L R, ‖c • gsr.psi.grad p.2‖ ^ 2)
      = c ^ 2 * (R ^ (m + 1) *
          ∫ p in Cm.body, ‖Weak.classicalGrad (fun z => gsr.psi.toFun z) (R • p.2)‖ ^ 2) := by
  have hd : dirichletP (capTrialLeft Cm Cp L hR hL (fun _ => c) gsr)
      = ∫ p in leftCap Cm L R,
          (dxP (constTensor c gsr.psi) p ^ 2 + ‖gradZP (constTensor c gsr.psi) p‖ ^ 2) := rfl
  have key : (∫ p in leftCap Cm L R, ‖c • gsr.psi.grad p.2‖ ^ 2)
      = ∫ p in leftCap Cm L R,
          (dxP (constTensor c gsr.psi) p ^ 2 + ‖gradZP (constTensor c gsr.psi) p‖ ^ 2) := by
    refine setIntegral_congr_fun (measurableSet_leftCap' hR) fun p hp => ?_
    rw [dirichlet_integrand_constTensor c gsr p, grad_eq_on_leftCap_ta (Cp := Cp) hR hL gsr hp,
      norm_smul, Real.norm_eq_abs, mul_pow, sq_abs]
  rw [key, ← hd, dirichletP_capTrialLeft_eq Cm Cp L hR hL (fun _ => c) gsr]

/-- The right cap energy of the trial extension, in cap coordinates. -/
theorem setIntegral_rightCap_grad_sq_ta (Cm Cp : Cap m) (L : ℝ) (hR : 0 < R)
    (hL : (Cm.K + Cp.K) * R < L) (c : ℝ) (gsr : TransverseGroundStateReg m α R bd) :
    (∫ p in rightCap Cp L R, ‖c • gsr.psi.grad p.2‖ ^ 2)
      = c ^ 2 * (R ^ (m + 1) *
          ∫ p in Cp.body, ‖Weak.classicalGrad (fun z => gsr.psi.toFun z) (R • p.2)‖ ^ 2) := by
  have hd : dirichletP (capTrialRight Cm Cp L hR hL (fun _ => c) gsr)
      = ∫ p in rightCap Cp L R,
          (dxP (constTensor c gsr.psi) p ^ 2 + ‖gradZP (constTensor c gsr.psi) p‖ ^ 2) := rfl
  have key : (∫ p in rightCap Cp L R, ‖c • gsr.psi.grad p.2‖ ^ 2)
      = ∫ p in rightCap Cp L R,
          (dxP (constTensor c gsr.psi) p ^ 2 + ‖gradZP (constTensor c gsr.psi) p‖ ^ 2) := by
    refine setIntegral_congr_fun (measurableSet_rightCap' hR) fun p hp => ?_
    rw [dirichlet_integrand_constTensor c gsr p, grad_eq_on_rightCap_ta (Cm := Cm) hR hL gsr hp,
      norm_smul, Real.norm_eq_abs, mul_pow, sq_abs]
  rw [key, ← hd, dirichletP_capTrialRight_eq Cm Cp L hR hL (fun _ => c) gsr]

end Caps

/-! ## 3. The exact renormalized-energy splitting of the trial extension -/

section Renorm

variable {Cm Cp : Cap m} {L : ℝ}

/-- **`eq:trial-energy`, exact form, for a merely absolutely continuous axial factor.**

The renormalized energy `E_R[𝒯_R W] = D[𝒯_RW] + α ∫_{∂Ω_R} (𝒯_RW)² − ν_R N[𝒯_RW]` of the
trial extension is the axial Dirichlet energy of `W` plus the two cap terms; the bulk
transverse contribution cancels exactly by the weak eigenvalue equation for `ψ_R`.  This is
the exact analogue of `renormEnergy_trialH1P`. -/
theorem renormEnergy_trialAC_ta (hm : 1 ≤ m) (Cm Cp : Cap m) (L : ℝ) (hR : 0 < R)
    (hL : (Cm.K + Cp.K) * R < L) (W : Sobolev.H1 (bulkLength Cm Cp L R))
    (gsr : TransverseGroundStateReg m α R bd)
    (hbd : bd gsr.psi gsr.psi = sphereIntegral m R (fun z => gsr.psi.toFun z ^ 2)) :
    dirichletP (trialAC hR hL W gsr.psi)
        + α * boundaryEnergy Cm Cp L R (trialACFun Cm Cp L R W gsr.psi)
        - gsr.nu * massP (trialAC hR hL W gsr.psi)
      = Sobolev.dirichlet (bulkLength Cm Cp L R) W
        + W.toFun 0 ^ 2 * capEnergyTerm m α R Cm gsr
        + W.toFun (bulkLength Cm Cp L R) ^ 2 * capEnergyTerm m α R Cp gsr := by
  have hRne : R ≠ 0 := hR.ne'
  have hmassCap : ∀ C : Cap m, (R ^ (m + 1) * ∫ p in C.body, gsr.psi.toFun (R • p.2) ^ 2)
      = R * ∫ p in C.body, capGroundLift m R gsr.psi p ^ 2 := by
    intro C
    have h : (∫ p in C.body, capGroundLift m R gsr.psi p ^ 2)
        = R ^ m * ∫ p in C.body, gsr.psi.toFun (R • p.2) ^ 2 := by
      rw [← integral_const_mul]
      exact setIntegral_congr_fun (measurableSet_capBody C)
        fun p _ => transLift_sq m hR gsr.psi p.2
    rw [h, pow_succ]
    ring
  have hdirCap : ∀ C : Cap m, (R ^ (m + 1) *
        ∫ p in C.body, ‖Weak.classicalGrad (fun z => gsr.psi.toFun z) (R • p.2)‖ ^ 2)
      = R⁻¹ * ∫ p in C.body, ‖gradZP (capGroundLift m R gsr.psi) p‖ ^ 2 := by
    intro C
    have h : (∫ p in C.body, ‖gradZP (capGroundLift m R gsr.psi) p‖ ^ 2)
        = R ^ m * R ^ 2 *
          ∫ p in C.body, ‖Weak.classicalGrad (fun z => gsr.psi.toFun z) (R • p.2)‖ ^ 2 := by
      rw [← integral_const_mul]
      refine setIntegral_congr_fun (measurableSet_capBody C) fun p _ => ?_
      rw [gradZP_capGroundLift gsr.psiC1, norm_classicalGrad_transLift_sq hR gsr.psiC1]
    rw [h]
    field_simp
    ring
  have hray : Weak.dirichlet gsr.psi
      + α * sphereIntegral m R (fun z => gsr.psi.toFun z ^ 2) = gsr.nu := by
    have h := gsr.toTransverseGroundState.nu_eq_rayleigh
    rw [qB] at h
    rw [← hbd]
    exact h.symm
  rw [dirichletP_trialAC, massP_trialAC, boundaryEnergy_trialAC_ta hm Cm Cp L hR hL W gsr,
    setIntegral_leftCap_sq_ta Cm Cp L hR hL _ gsr,
    setIntegral_rightCap_sq_ta Cm Cp L hR hL _ gsr,
    setIntegral_leftCap_grad_sq_ta Cm Cp L hR hL _ gsr,
    setIntegral_rightCap_grad_sq_ta Cm Cp L hR hL _ gsr,
    hmassCap Cm, hmassCap Cp, hdirCap Cm, hdirCap Cp, gsr.normalized,
    capEnergyTerm, capEnergyTerm, capJForm_capGroundLift, capJForm_capGroundLift,
    capJterm_transLift hR Cm gsr.psi, capJterm_transLift hR Cp gsr.psi, ← hray]
  ring

end Renorm

/-! ## 4. The quotient Robin form of the trial lift -/

section Quotient

/-- The mass of the trial lift on the quotient is the mass of the concrete trial extension. -/
theorem massPQ_liftQ_ta {Cm Cp : Cap m} {L : ℝ} (hR : 0 < R) (hL : (Cm.K + Cp.K) * R < L)
    (W : Sobolev.H1 (bulkLength Cm Cp L R)) (ψ : TransH1 m R) :
    massPQ (liftQ hR hL ψ (Submodule.Quotient.mk W)) = massP (trialAC hR hL W ψ) := by
  rw [liftQ_mk, massPQ_mk]

variable {Cm Cp : Cap 1} {L : ℝ}

/-- For `m = 1` the abstract boundary form of `traceDataOne` evaluated on the trial extension
**is** the honest surface integral, because the trial extension is continuous up to
`∂Ω_R` (`tr_continuous`). -/
theorem bd_trialAC_ta (hR : 0 < R) (hL : (Cm.K + Cp.K) * R < L) (hm0 : Cm.θ 0 = 0)
    (hp0 : Cp.θ 0 = 0) (hti : TraceIneqOne Cm Cp L R)
    (W : Sobolev.H1 (bulkLength Cm Cp L R)) {ψ : TransH1 1 R}
    (hψ : Continuous fun z => ψ.toFun z) :
    (traceDataOne hR hL hm0 hp0 hti).bd (trialAC hR hL W ψ) (trialAC hR hL W ψ)
      = boundaryEnergy Cm Cp L R (trialACFun Cm Cp L R W ψ) :=
  (traceDataOne hR hL hm0 hp0 hti).tr_continuous _ (continuousOn_trialACFun_ta hR hL W hψ)

/-- **The quotient Robin form of the trial lift, through the concrete pieces.** -/
theorem robinFormPQ_liftQ_ta (hR : 0 < R) (hL : (Cm.K + Cp.K) * R < L) (hm0 : Cm.θ 0 = 0)
    (hp0 : Cp.θ 0 = 0) (hti : TraceIneqOne Cm Cp L R) (α : ℝ)
    (W : Sobolev.H1 (bulkLength Cm Cp L R)) {ψ : TransH1 1 R}
    (hψ : Continuous fun z => ψ.toFun z) :
    robinFormPQ (isOpen_thinDomain hR hL) (traceDataOne hR hL hm0 hp0 hti).bd
        (traceDataOne hR hL hm0 hp0 hti).vanishesOnNullAEP α
        (liftQ hR hL ψ (Submodule.Quotient.mk W))
      = dirichletP (trialAC hR hL W ψ)
        + α * boundaryEnergy Cm Cp L R (trialACFun Cm Cp L R W ψ) := by
  rw [liftQ_mk, robinFormPQ_mk, bd_trialAC_ta hR hL hm0 hp0 hti W hψ]

end Quotient

/-! ## 5. The `trial_energy` field -/

section Field

/-- The explicit constant of `capEnergyTerm_sub_beta` for one cap. -/
def capEnergyConst_ta (m : ℕ) (α : ℝ) (C : Cap m) (Cexp : ℝ) : ℝ :=
  C.K * Cexp ^ 2 + (|α| * capBdryConst m C Cexp
    + (m : ℝ) * |α| * capMassConst m C Cexp + Cexp * C.K)

/-- The constant `C` of `eq:trial-energy`: the larger of the two cap constants (truncated
below at `0` so that it is manifestly nonnegative).  It depends only on `m, α, 𝒞±` and the
expansion constant `Cexp` — **not** on `R` nor on the axial factor. -/
def trialEnergyConst_ta (m : ℕ) (α : ℝ) (Cm Cp : Cap m) (Cexp : ℝ) : ℝ :=
  max (max (capEnergyConst_ta m α Cm Cexp) (capEnergyConst_ta m α Cp Cexp)) 0

theorem trialEnergyConst_ta_nonneg (m : ℕ) (α : ℝ) (Cm Cp : Cap m) (Cexp : ℝ) :
    0 ≤ trialEnergyConst_ta m α Cm Cp Cexp := le_max_right _ _

/-- **`eq:trial-energy` for the absolutely continuous trial extension**, in the shape of the
`trial_energy` field: the renormalized energy of `𝒯_R W` is at most the one-dimensional Robin
form with the two endpoint coefficients shifted by `C R`. -/
theorem trialAC_energy_le_ta (hm : 1 ≤ m) (Cm Cp : Cap m) (L : ℝ)
    (hθ0m : 0 ≤ Cm.θ 0) (hθ1m : Cm.θ 0 ≤ 1) (hθ0p : 0 ≤ Cp.θ 0) (hθ1p : Cp.θ 0 ≤ 1)
    (hR : 0 < R) (hR1 : R ≤ 1) (hL : (Cm.K + Cp.K) * R < L)
    {gsr : TransverseGroundStateReg m α R bd} {Cexp : ℝ}
    (hexp : TransverseExpansionData m α R gsr Cexp)
    (W : Sobolev.H1 (bulkLength Cm Cp L R)) :
    dirichletP (trialAC hR hL W gsr.psi)
        + α * boundaryEnergy Cm Cp L R (trialACFun Cm Cp L R W gsr.psi)
        - gsr.nu * massP (trialAC hR hL W gsr.psi)
      ≤ Sobolev.robinForm (Cm.beta α + trialEnergyConst_ta m α Cm Cp Cexp * R)
          (Cp.beta α + trialEnergyConst_ta m α Cm Cp Cexp * R) (bulkLength Cm Cp L R) W := by
  have hEm := capEnergyTerm_sub_beta hm hR hR1 Cm hθ0m hθ1m hexp
  have hEp := capEnergyTerm_sub_beta hm hR hR1 Cp hθ0p hθ1p hexp
  have hAm : capEnergyConst_ta m α Cm Cexp ≤ trialEnergyConst_ta m α Cm Cp Cexp :=
    le_trans (le_max_left _ _) (le_max_left _ _)
  have hAp : capEnergyConst_ta m α Cp Cexp ≤ trialEnergyConst_ta m α Cm Cp Cexp :=
    le_trans (le_max_right _ _) (le_max_left _ _)
  have hbm : capEnergyTerm m α R Cm gsr - Cap.beta Cm α
      ≤ trialEnergyConst_ta m α Cm Cp Cexp * R :=
    le_trans (le_trans (le_abs_self _) hEm) (mul_le_mul_of_nonneg_right hAm hR.le)
  have hbp : capEnergyTerm m α R Cp gsr - Cap.beta Cp α
      ≤ trialEnergyConst_ta m α Cm Cp Cexp * R :=
    le_trans (le_trans (le_abs_self _) hEp) (mul_le_mul_of_nonneg_right hAp hR.le)
  have h1 : W.toFun 0 ^ 2 * capEnergyTerm m α R Cm gsr
      ≤ (Cap.beta Cm α + trialEnergyConst_ta m α Cm Cp Cexp * R) * W.toFun 0 ^ 2 := by
    nlinarith [sq_nonneg (W.toFun 0), hbm]
  have h2 : W.toFun (bulkLength Cm Cp L R) ^ 2 * capEnergyTerm m α R Cp gsr
      ≤ (Cap.beta Cp α + trialEnergyConst_ta m α Cm Cp Cexp * R)
          * W.toFun (bulkLength Cm Cp L R) ^ 2 := by
    nlinarith [sq_nonneg (W.toFun (bulkLength Cm Cp L R)), hbp]
  rw [renormEnergy_trialAC_ta hm Cm Cp L hR hL W gsr hexp.bdSphere, Sobolev.robinForm]
  linarith

end Field

/-! ## 6. The `trial_energy` and `trial_mass` fields for `m = 1` -/

section One

variable {Cm Cp : Cap 1} {L : ℝ}

/-- **The `trial_energy` field of `GlobalComparisonData`, for `m = 1`.**

The constant `A` is uniform: it depends only on `α`, the two caps and the expansion constant
`Cexp` of `TransverseExpansionData`, and in particular not on `R`, on `v`, nor on the trace
datum. -/
theorem trial_energy_field_one (α : ℝ) (hα : 0 < α) (Cm Cp : Cap 1) (L Cexp : ℝ)
    (hm0 : Cm.θ 0 = 0) (hp0 : Cp.θ 0 = 0) :
    ∃ A : ℝ, 0 ≤ A ∧ ∀ (R : ℝ) (hR : 0 < R), R ≤ 1 →
      ∀ hL : (Cm.K + Cp.K) * R < L, ∀ hti : TraceIneqOne Cm Cp L R,
        TransverseExpansionData 1 α R (Transverse.groundStateOneReg α R hα hR) Cexp →
        ∀ v : Sobolev.H1Q (bulkLength Cm Cp L R),
          robinFormPQ (isOpen_thinDomain hR hL) (traceDataOne hR hL hm0 hp0 hti).bd
              (traceDataOne hR hL hm0 hp0 hti).vanishesOnNullAEP α
              (liftQ hR hL (Transverse.groundStateOneReg α R hα hR).psi v)
            - (Transverse.groundStateOneReg α R hα hR).nu
                * massPQ (liftQ hR hL (Transverse.groundStateOneReg α R hα hR).psi v)
          ≤ Sobolev.robinFormQ (Cm.beta α + A * R) (Cp.beta α + A * R)
              (bulkLength Cm Cp L R) v := by
  refine ⟨trialEnergyConst_ta 1 α Cm Cp Cexp, trialEnergyConst_ta_nonneg 1 α Cm Cp Cexp, ?_⟩
  intro R hR hR1 hL hti hexp v
  obtain ⟨W, rfl⟩ := Submodule.Quotient.mk_surjective (Sobolev.nullOff _) v
  rw [robinFormPQ_liftQ_ta hR hL hm0 hp0 hti α W
      (Transverse.groundStateOneReg α R hα hR).psiC1.continuous,
    massPQ_liftQ_ta hR hL W (Transverse.groundStateOneReg α R hα hR).psi,
    Sobolev.robinFormQ_mk]
  exact trialAC_energy_le_ta le_rfl Cm Cp L hm0.ge (by rw [hm0]; norm_num) hp0.ge
    (by rw [hp0]; norm_num) hR hR1 hL hexp W

/-- **The `trial_mass` field of `GlobalComparisonData`, for `m = 1`** (this is
`massQ_le_massPQ_liftQ` with the normalisation of the ground state discharged). -/
theorem trial_mass_field_one (α : ℝ) (hα : 0 < α) {R : ℝ} (hR : 0 < R)
    (hL : (Cm.K + Cp.K) * R < L) (v : Sobolev.H1Q (bulkLength Cm Cp L R)) :
    Sobolev.massQ (bulkLength Cm Cp L R) v
      ≤ massPQ (liftQ hR hL (Transverse.groundStateOneReg α R hα hR).psi v) :=
  massQ_le_massPQ_liftQ hR hL (Transverse.groundStateOneReg α R hα hR).psi
    (Transverse.groundStateOneReg α R hα hR).normalized v

end One

end

end RobinCaps.ThinDomain

