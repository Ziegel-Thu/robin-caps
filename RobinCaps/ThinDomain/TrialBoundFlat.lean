import RobinCaps.ThinDomain.TrialBoundW
import RobinCaps.Cap.LowerWeak
import RobinCaps.Cap.Sharp
import RobinCaps.Cap.PoincareFlat
import RobinCaps.Compact.GroundStateGap
import RobinCaps.Compact.BoundaryNonneg

/-!
# U-TRIALBOUND-FLAT: `lem:cap-upper` for the flat cap, weak transverse ground state

This file proves the manuscript's `lem:cap-upper` for the **flat cap** `C = Cap.flat m K hK`
(`RobinCaps/Cap/Sharp.lean`, profile `θ ≡ 1`, body the literal cylinder `(-K,0) × B_m(1)`),
mirroring `RobinCaps/ThinDomain/TrialBoundW.lean`'s treatment of the hemisphere but replacing the
hemisphere's trace datum `Cap.capTraceDataHemi_th` by an **abstract** trace datum
`tdF : CapTraceData (Cap.flat m K hK)` together with the interface hypothesis `FlatLiftBd_tbf`
describing the trace form of the transverse lift on the flat cap: the lateral wall contributes
`K` times the unit-ball Rellich boundary form `bdR m 1` of the transverse profile, and the
terminal disc contributes its plain `L²` mass.

Since the flat cap's body is the *literal* product `(-K,0) × B_m(1)` (not merely contained in the
unit cylinder, as for a general cap), the bulk integrals (`massP`, the gradient term) are **exact**
multiples of `K` (`setIntegral_flatBody_snd_eq_tbf`), with no `O(R)` error: this is the main
simplification over the hemisphere's `cap_mass_expansion_tw`.  The only genuine expansion needed is
that of `bdR m 1 Ψ Ψ` itself, `bdR_flat_expansion_tbf`, obtained by writing `Ψ = d + (Ψ - d)`
(`d = ω_m^{-1/2}`) exactly as `TrialBoundW.cap_boundary_expansion_tw` does for `bdΓ`, using
`RobinCaps.Compact.bdR_oneB` for the constant term and `RobinCaps.Compact.abs_bdR_le` /
`abs_bdR_le₂` (rather than an abstract trace inequality) for the remainder and cross terms.

## Contents

* `FlatLiftBd_tbf` — the interface: the flat cap's trace form on the transverse lift, to be
  discharged by `RobinCaps/Cap/TraceDataFlat.lean`;
* `setIntegral_flatBody_snd_eq_tbf` — the exact Fubini identity `∫_{C.body} f(z) = K ∫_{B_1} f`
  for the flat cap;
* `massP_capLiftW_flat_eq_tbf`, `gradIntegral_capLiftW_flat_eq_tbf` — the exact bulk identities;
* `bdR_flat_expansion_tbf` — `bdR m 1 Ψ Ψ = m + O(R)`;
* `capEnergyTermFlat_tbf`, `capEnergyTermFlat_sub_beta_tbf` — the assembled cap-level energy
  correction and its convergence to `β(𝒞) = α` at rate `O(R)`.

No `sorry`, `admit`, `axiom` or `native_decide` occurs in this file.
-/

open MeasureTheory Set Metric Filter

open scoped ENNReal Topology InnerProductSpace ContDiff

namespace RobinCaps.ThinDomain

open RobinCaps.Sobolev.Weak

noncomputable section

variable {m : ℕ} {R : ℝ}

/-! ## 0. A triangle-inequality helper -/

private theorem abs_add_sub_le_tbf (x y z : ℝ) : |x + y - z| ≤ |x| + |y| + |z| := by
  have h1 : |x + y - z| ≤ |x + y| + |z| := by
    rw [sub_eq_add_neg]
    calc |x + y + -z| ≤ |x + y| + |-z| := abs_add_le _ _
      _ = |x + y| + |z| := by rw [abs_neg]
  have h2 : |x + y| ≤ |x| + |y| := abs_add_le _ _
  linarith

/-! ## 1. The trace interface for the flat cap's lift -/

/-- The flat cap's trace form on the transverse lift: lateral wall `(-K,0) × S^{m-1}` contributes
`K` times the unit-ball Rellich form of `Ψ`, the terminal disc contributes `∫_{B_1} Ψ²`. -/
structure FlatLiftBd_tbf (m : ℕ) (K : ℝ) (hK : 0 < K)
    (tdF : Cap.CapTraceData (Cap.flat m K hK)) : Prop where
  bdΓ_lift : ∀ (R : ℝ) (hR : 0 < R) (ψ : TransH1 m R),
    tdF.bdΓ (capLiftW_tw (Cap.flat m K hK) hR ψ) (capLiftW_tw (Cap.flat m K hK) hR ψ)
      = K * RobinCaps.Compact.bdR m 1 (transLiftH1_tw hR ψ) (transLiftH1_tw hR ψ)
        + ∫ y in ball (0 : EuclideanSpace ℝ (Fin m)) 1, transLift m R ψ y ^ 2

/-! ## 2. Exact Fubini identities on the flat cap's body -/

/-- **The flat cap's body is the literal unit cylinder**: `∫_{C.body} f(z) = K ∫_{B_1} f`,
with no inequality needed (unlike the general `setIntegral_body_le_tw`). -/
theorem setIntegral_flatBody_snd_eq_tbf (m : ℕ) (K : ℝ) (hK : 0 < K)
    (f : EuclideanSpace ℝ (Fin m) → ℝ) :
    (∫ p in (Cap.flat m K hK).body, f p.2)
      = K * ∫ y in ball (0 : EuclideanSpace ℝ (Fin m)) 1, f y := by
  rw [Cap.flat_body_eq_pf m K hK]
  exact setIntegral_cyl_snd (Cap.flat m K hK) f

variable {α : ℝ} {bd : TransH1 m R →ₗ[ℝ] TransH1 m R →ₗ[ℝ] ℝ}

/-- **The exact mass identity on the flat cap**: `∫_{C.body} Ψ² = K` (no `O(R)` error, since
`∫_{B_1} Ψ² = 1` exactly by the normalisation `NB ψ = 1`). -/
theorem massP_capLiftW_flat_eq_tbf (K : ℝ) (hK : 0 < K) (hR : 0 < R)
    (gs : TransverseGroundState m α R bd) :
    massP (capLiftW_tw (Cap.flat m K hK) hR gs.psi) = K := by
  have h1 : massP (capLiftW_tw (Cap.flat m K hK) hR gs.psi)
      = ∫ p in (Cap.flat m K hK).body, transLift m R gs.psi p.2 ^ 2 := rfl
  have h2 := setIntegral_flatBody_snd_eq_tbf m K hK (fun z => transLift m R gs.psi z ^ 2)
  rw [h1, h2, integral_transLift_sq_tw hR gs, mul_one]

/-- **The exact gradient identity on the flat cap**: `∫_{C.body} |∇_zΨ|² = K ∫_{B_1} |∇Ψ|²`. -/
theorem gradIntegral_capLiftW_flat_eq_tbf (K : ℝ) (hK : 0 < K) (hR : 0 < R) (ψ : TransH1 m R) :
    (∫ p in (Cap.flat m K hK).body, ‖(capLiftW_tw (Cap.flat m K hK) hR ψ).gz p‖ ^ 2)
      = K * ∫ y in ball (0 : EuclideanSpace ℝ (Fin m)) 1, ‖transLiftGrad_tw m R ψ y‖ ^ 2 := by
  have h1 : (∫ p in (Cap.flat m K hK).body, ‖(capLiftW_tw (Cap.flat m K hK) hR ψ).gz p‖ ^ 2)
      = ∫ p in (Cap.flat m K hK).body, ‖transLiftGrad_tw m R ψ p.2‖ ^ 2 := rfl
  have h2 := setIntegral_flatBody_snd_eq_tbf m K hK (fun z => ‖transLiftGrad_tw m R ψ z‖ ^ 2)
  rw [h1, h2]

/-! ## 3. The expansion of the boundary form `bdR m 1 Ψ Ψ` -/

variable {gs : TransverseGroundState m α R bd} {Cexp : ℝ}

/-- **The boundary-form expansion**: `bdR m 1 Ψ Ψ = m + O(R)`, the flat-cap analogue of
`cap_boundary_expansion_tw`. -/
theorem bdR_flat_expansion_tbf (hm : 1 ≤ m) (hR : 0 < R) (hR1 : R ≤ 1)
    (hexp : ExpW_tw m α R gs Cexp) :
    |RobinCaps.Compact.bdR m 1 (transLiftH1_tw hR gs.psi) (transLiftH1_tw hR gs.psi) - (m : ℝ)|
      ≤ (((m : ℝ) + 2) * Cexp ^ 2 + 2 * ((m : ℝ) + 1) * Real.sqrt 2 * |Cexp|) * R := by
  have h1 : (0 : ℝ) < 1 := one_pos
  set c : ℝ := (Real.sqrt (omega m))⁻¹ with hcdef
  have hω : 0 < omega m := Cap.omega_pos m
  have hsqω : 0 < Real.sqrt (omega m) := Real.sqrt_pos.2 hω
  have hc0 : 0 ≤ c := le_of_lt (inv_pos.2 hsqω)
  have hcsq : c * Real.sqrt (omega m) = 1 := inv_mul_cancel₀ hsqω.ne'
  set U : H1 (ball (0 : EuclideanSpace ℝ (Fin m)) 1) := transLiftH1_tw hR gs.psi with hUdef
  set G : H1 (ball (0 : EuclideanSpace ℝ (Fin m)) 1) := U - c • RobinCaps.Compact.oneB m 1
    with hGdef
  have hUeq : U = G + c • RobinCaps.Compact.oneB m 1 := by rw [hGdef]; abel
  -- value of `bdR` on the constant function
  have hOneOne : RobinCaps.Compact.bdR m 1 (RobinCaps.Compact.oneB m 1)
      (RobinCaps.Compact.oneB m 1) = (m : ℝ) * omega m := by
    have h := RobinCaps.Compact.bdR_oneB hm h1
    rwa [one_pow, mul_one] at h
  have hOneOneNonneg : 0 ≤ (m : ℝ) * omega m := by positivity
  -- mass / dirichlet bounds for `G`
  have hMG : mass G ≤ Cexp ^ 2 * R ^ 2 := by
    have heq : mass G = ∫ y in ball (0 : EuclideanSpace ℝ (Fin m)) 1,
        (transLift m R gs.psi y - c) ^ 2 := by
      rw [hGdef, RobinCaps.Compact.mass_sub]
      refine integral_congr_ae (Eventually.of_forall fun x => ?_)
      have hone : (c • RobinCaps.Compact.oneB m 1).toFun x = c := by
        simp [H1.smul_toFun, RobinCaps.Compact.oneB_toFun]
      simp only [hone, hUdef, transLiftH1_tw_toFun]
    rw [heq]
    have hle := hexp.l2_le
    rwa [← hcdef] at hle
  have hDU : dirichlet U ≤ Cexp ^ 2 * R ^ 2 := by
    have heq : dirichlet U = ∫ y in ball (0 : EuclideanSpace ℝ (Fin m)) 1,
        ‖transLiftGrad_tw m R gs.psi y‖ ^ 2 := by
      unfold dirichlet
      rw [hUdef, transLiftH1_tw_grad]
    rw [heq]; exact hexp.grad_le
  have hDGeq : dirichlet G = dirichlet U := by
    have hcgrad : (c • RobinCaps.Compact.oneB m 1).grad
        = (0 : EuclideanSpace ℝ (Fin m) → EuclideanSpace ℝ (Fin m)) := by
      funext x; simp [H1.smul_grad, RobinCaps.Compact.oneB_grad]
    have hGgrad : G.grad = U.grad := by
      rw [hGdef, RobinCaps.Compact.H1.sub_grad, hcgrad, sub_zero]
    unfold dirichlet; rw [hGgrad]
  have hDG : dirichlet G ≤ Cexp ^ 2 * R ^ 2 := hDGeq ▸ hDU
  have hmassGnn : 0 ≤ mass G := mass_nonneg G
  have hdirGnn : 0 ≤ dirichlet G := dirichlet_nonneg G
  -- the diagonal bound `bdR(G,G) ≤ (m+2) Cexp² R²`
  have hGGabs : |RobinCaps.Compact.bdR m 1 G G| ≤ ((m : ℝ) / 1 + 1) * mass G + dirichlet G :=
    RobinCaps.Compact.abs_bdR_le h1 G
  have hGG0 : 0 ≤ RobinCaps.Compact.bdR m 1 G G := RobinCaps.Compact.bdR_nonneg hm h1 G
  have hGG : RobinCaps.Compact.bdR m 1 G G ≤ ((m : ℝ) + 2) * Cexp ^ 2 * R ^ 2 := by
    rw [abs_of_nonneg hGG0, div_one] at hGGabs
    nlinarith only [hGGabs, hMG, hDG]
  -- the cross-term bound
  have hOneMass : mass (RobinCaps.Compact.oneB m 1) = omega m := by
    rw [RobinCaps.Compact.mass_oneB, RobinCaps.Compact.volume_ball_toReal_eq h1, one_pow, mul_one]
  have hOneDir : dirichlet (RobinCaps.Compact.oneB m 1) = 0 := RobinCaps.Compact.dirichlet_oneB
  have hCS := RobinCaps.Compact.abs_bdR_le₂ h1 (RobinCaps.Compact.oneB m 1) G
  have hsqrtOne : Real.sqrt (mass (RobinCaps.Compact.oneB m 1)
      + dirichlet (RobinCaps.Compact.oneB m 1)) = Real.sqrt (omega m) := by
    rw [hOneMass, hOneDir, add_zero]
  have hsqrtG : Real.sqrt (mass G + dirichlet G) ≤ Real.sqrt 2 * |Cexp| * R := by
    have hsum2 : mass G + dirichlet G ≤ 2 * (Cexp ^ 2 * R ^ 2) := by linarith only [hMG, hDG]
    have hbound : Real.sqrt (mass G + dirichlet G) ≤ Real.sqrt (2 * (Cexp ^ 2 * R ^ 2)) :=
      Real.sqrt_le_sqrt hsum2
    have heq2 : Real.sqrt (2 * (Cexp ^ 2 * R ^ 2)) = Real.sqrt 2 * |Cexp| * R := by
      rw [show (2 : ℝ) * (Cexp ^ 2 * R ^ 2) = 2 * (Cexp * R) ^ 2 from by ring,
        Real.sqrt_mul (by norm_num), Real.sqrt_sq_eq_abs, abs_mul, abs_of_nonneg hR.le, mul_assoc]
    rwa [heq2] at hbound
  have hCSabs : |RobinCaps.Compact.bdR m 1 (RobinCaps.Compact.oneB m 1) G|
      ≤ ((m : ℝ) + 1) * Real.sqrt (omega m) * (Real.sqrt 2 * |Cexp| * R) := by
    have hnn : 0 ≤ ((m : ℝ) + 1) * Real.sqrt (omega m) := by positivity
    calc |RobinCaps.Compact.bdR m 1 (RobinCaps.Compact.oneB m 1) G|
        ≤ ((m : ℝ) / 1 + 1) * Real.sqrt (mass (RobinCaps.Compact.oneB m 1)
              + dirichlet (RobinCaps.Compact.oneB m 1))
            * Real.sqrt (mass G + dirichlet G) := hCS
      _ = ((m : ℝ) + 1) * Real.sqrt (omega m) * Real.sqrt (mass G + dirichlet G) := by
          rw [hsqrtOne, div_one]
      _ ≤ ((m : ℝ) + 1) * Real.sqrt (omega m) * (Real.sqrt 2 * |Cexp| * R) :=
          mul_le_mul_of_nonneg_left hsqrtG hnn
  -- assemble via bilinearity
  have hexpand := RobinCaps.Compact.bilin_add_smul_smul
      (Q := RobinCaps.Compact.bdR m 1)
      (fun u v => RobinCaps.Compact.bdR_symm u v) G (RobinCaps.Compact.oneB m 1) c
  have hsym : RobinCaps.Compact.bdR m 1 G (RobinCaps.Compact.oneB m 1)
      = RobinCaps.Compact.bdR m 1 (RobinCaps.Compact.oneB m 1) G :=
    RobinCaps.Compact.bdR_symm G (RobinCaps.Compact.oneB m 1)
  have hc2 : c ^ 2 = (omega m)⁻¹ := by rw [hcdef, inv_pow, Real.sq_sqrt hω.le]
  have hmeq : (omega m)⁻¹ * ((m : ℝ) * omega m) = (m : ℝ) := by
    rw [mul_comm (m : ℝ) (omega m), ← mul_assoc, inv_mul_cancel₀ hω.ne', one_mul]
  have key : RobinCaps.Compact.bdR m 1 U U - (m : ℝ)
      = RobinCaps.Compact.bdR m 1 G G
        + 2 * c * RobinCaps.Compact.bdR m 1 (RobinCaps.Compact.oneB m 1) G := by
    rw [hUeq, hexpand, hOneOne, hsym, hc2, hmeq]
    ring
  have habs : |RobinCaps.Compact.bdR m 1 U U - (m : ℝ)|
      ≤ RobinCaps.Compact.bdR m 1 G G
        + 2 * c * |RobinCaps.Compact.bdR m 1 (RobinCaps.Compact.oneB m 1) G| := by
    rw [key]
    calc |RobinCaps.Compact.bdR m 1 G G
          + 2 * c * RobinCaps.Compact.bdR m 1 (RobinCaps.Compact.oneB m 1) G|
        ≤ |RobinCaps.Compact.bdR m 1 G G|
          + |2 * c * RobinCaps.Compact.bdR m 1 (RobinCaps.Compact.oneB m 1) G| := abs_add_le _ _
      _ = RobinCaps.Compact.bdR m 1 G G
          + 2 * c * |RobinCaps.Compact.bdR m 1 (RobinCaps.Compact.oneB m 1) G| := by
          rw [abs_of_nonneg hGG0, abs_mul, abs_mul, abs_of_nonneg (by norm_num : (0:ℝ) ≤ 2),
            abs_of_nonneg hc0]
  have hstep : RobinCaps.Compact.bdR m 1 G G
      + 2 * c * |RobinCaps.Compact.bdR m 1 (RobinCaps.Compact.oneB m 1) G|
      ≤ ((m : ℝ) + 2) * Cexp ^ 2 * R ^ 2
        + 2 * c * (((m : ℝ) + 1) * Real.sqrt (omega m) * (Real.sqrt 2 * |Cexp| * R)) := by
    have h2 := mul_le_mul_of_nonneg_left hCSabs (by positivity : (0:ℝ) ≤ 2 * c)
    linarith only [hGG, h2]
  have hcollapse : 2 * c * (((m : ℝ) + 1) * Real.sqrt (omega m) * (Real.sqrt 2 * |Cexp| * R))
      = 2 * ((m : ℝ) + 1) * Real.sqrt 2 * |Cexp| * R := by
    calc 2 * c * (((m : ℝ) + 1) * Real.sqrt (omega m) * (Real.sqrt 2 * |Cexp| * R))
        = 2 * ((m : ℝ) + 1) * (c * Real.sqrt (omega m)) * (Real.sqrt 2 * |Cexp| * R) := by ring
      _ = 2 * ((m : ℝ) + 1) * 1 * (Real.sqrt 2 * |Cexp| * R) := by rw [hcsq]
      _ = 2 * ((m : ℝ) + 1) * Real.sqrt 2 * |Cexp| * R := by ring
  have hR2 : R ^ 2 ≤ R := by nlinarith only [hR.le, hR1]
  have hcoef0 : (0 : ℝ) ≤ ((m : ℝ) + 2) * Cexp ^ 2 := by positivity
  calc |RobinCaps.Compact.bdR m 1 U U - (m : ℝ)|
      ≤ RobinCaps.Compact.bdR m 1 G G
        + 2 * c * |RobinCaps.Compact.bdR m 1 (RobinCaps.Compact.oneB m 1) G| := habs
    _ ≤ ((m : ℝ) + 2) * Cexp ^ 2 * R ^ 2
        + 2 * c * (((m : ℝ) + 1) * Real.sqrt (omega m) * (Real.sqrt 2 * |Cexp| * R)) := hstep
    _ = ((m : ℝ) + 2) * Cexp ^ 2 * R ^ 2 + 2 * ((m : ℝ) + 1) * Real.sqrt 2 * |Cexp| * R := by
        rw [hcollapse]
    _ ≤ ((m : ℝ) + 2) * Cexp ^ 2 * R + 2 * ((m : ℝ) + 1) * Real.sqrt 2 * |Cexp| * R := by
        nlinarith only [mul_le_mul_of_nonneg_left hR2 hcoef0]
    _ = (((m : ℝ) + 2) * Cexp ^ 2 + 2 * ((m : ℝ) + 1) * Real.sqrt 2 * |Cexp|) * R := by ring

/-! ## 4. The cap-level energy correction for the flat cap -/

/-- **The cap-level energy term of `eq:trial-energy`, flat-cap version.** -/
noncomputable def capEnergyTermFlat_tbf (hm : 1 ≤ m) (K : ℝ) (hK : 0 < K) (α : ℝ) (hR : 0 < R)
    (tdF : Cap.CapTraceData (Cap.flat m K hK)) (gs : TransverseGroundState m α R bd) : ℝ :=
  R⁻¹ * (∫ p in (Cap.flat m K hK).body,
      ‖(capLiftW_tw (Cap.flat m K hK) hR gs.psi).gz p‖ ^ 2)
    + (α * tdF.bdΓ (capLiftW_tw (Cap.flat m K hK) hR gs.psi)
          (capLiftW_tw (Cap.flat m K hK) hR gs.psi)
        - (m : ℝ) * α * massP (capLiftW_tw (Cap.flat m K hK) hR gs.psi))
    - (R * gs.nu - (m : ℝ) * α) * massP (capLiftW_tw (Cap.flat m K hK) hR gs.psi)

/-- **`lem:cap-upper` for the flat cap, weak transverse ground state.**  `capEnergyTermFlat_tbf`
converges to `β(𝒞) = α` at rate `O(R)`. -/
theorem capEnergyTermFlat_sub_beta_tbf (m : ℕ) (hm : 1 ≤ m) (K : ℝ) (hK : 0 < K) (α : ℝ)
    (hα : 0 < α) (tdF : Cap.CapTraceData (Cap.flat m K hK)) (hlift : FlatLiftBd_tbf m K hK tdF)
    (Cexp : ℝ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (R : ℝ) (hR : 0 < R), R ≤ 1 →
      ∀ {bd} (gs : TransverseGroundState m α R bd), ExpW_tw m α R gs Cexp →
        |capEnergyTermFlat_tbf hm K hK α hR tdF gs - (Cap.flat m K hK).beta α| ≤ C * R := by
  refine ⟨K * Cexp ^ 2
      + α * K * (((m : ℝ) + 2) * Cexp ^ 2 + 2 * ((m : ℝ) + 1) * Real.sqrt 2 * |Cexp|)
      + K * |Cexp|, by positivity, ?_⟩
  intro R hR hR1 bd gs hexp
  have hmass : massP (capLiftW_tw (Cap.flat m K hK) hR gs.psi) = K :=
    massP_capLiftW_flat_eq_tbf K hK hR gs
  have hgradInt : (∫ p in (Cap.flat m K hK).body,
      ‖(capLiftW_tw (Cap.flat m K hK) hR gs.psi).gz p‖ ^ 2)
      = K * ∫ y in ball (0 : EuclideanSpace ℝ (Fin m)) 1, ‖transLiftGrad_tw m R gs.psi y‖ ^ 2 :=
    gradIntegral_capLiftW_flat_eq_tbf K hK hR gs.psi
  have hPsiOne : (∫ y in ball (0 : EuclideanSpace ℝ (Fin m)) 1, transLift m R gs.psi y ^ 2) = 1 :=
    integral_transLift_sq_tw hR gs
  have hbdΓeq : tdF.bdΓ (capLiftW_tw (Cap.flat m K hK) hR gs.psi)
      (capLiftW_tw (Cap.flat m K hK) hR gs.psi)
      = K * RobinCaps.Compact.bdR m 1 (transLiftH1_tw hR gs.psi) (transLiftH1_tw hR gs.psi)
        + 1 := by
    rw [hlift.bdΓ_lift R hR gs.psi, hPsiOne]
  have hbdRexp := bdR_flat_expansion_tbf hm hR hR1 hexp
  have hbeta : (Cap.flat m K hK).beta α = α :=
    Cap.flat_beta_eq_alpha m K hK (Cap.omega_ne_zero m)
  have hdelta := abs_delta_le_tw hR hexp
  have hgradNonneg : (0 : ℝ) ≤ ∫ y in ball (0 : EuclideanSpace ℝ (Fin m)) 1,
      ‖transLiftGrad_tw m R gs.psi y‖ ^ 2 :=
    setIntegral_nonneg measurableSet_ball fun _ _ => by positivity
  have hsplit : capEnergyTermFlat_tbf hm K hK α hR tdF gs - (Cap.flat m K hK).beta α
      = R⁻¹ * (K * (∫ y in ball (0 : EuclideanSpace ℝ (Fin m)) 1,
            ‖transLiftGrad_tw m R gs.psi y‖ ^ 2))
        + α * K * (RobinCaps.Compact.bdR m 1 (transLiftH1_tw hR gs.psi)
              (transLiftH1_tw hR gs.psi) - (m : ℝ))
        - (R * gs.nu - (m : ℝ) * α) * K := by
    unfold capEnergyTermFlat_tbf
    rw [hbeta, hmass, hgradInt, hbdΓeq]
    ring
  rw [hsplit]
  have t1 : |R⁻¹ * (K * (∫ y in ball (0 : EuclideanSpace ℝ (Fin m)) 1,
        ‖transLiftGrad_tw m R gs.psi y‖ ^ 2))| ≤ K * Cexp ^ 2 * R := by
    rw [abs_of_nonneg (by positivity)]
    have hle : R⁻¹ * (K * (∫ y in ball (0 : EuclideanSpace ℝ (Fin m)) 1,
          ‖transLiftGrad_tw m R gs.psi y‖ ^ 2))
        ≤ R⁻¹ * (K * (Cexp ^ 2 * R ^ 2)) :=
      mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hexp.grad_le hK.le) (by positivity)
    have hRR : R⁻¹ * R ^ 2 = R := by
      rw [sq, ← mul_assoc, inv_mul_cancel₀ hR.ne', one_mul]
    have heq : R⁻¹ * (K * (Cexp ^ 2 * R ^ 2)) = K * Cexp ^ 2 * R := by
      calc R⁻¹ * (K * (Cexp ^ 2 * R ^ 2)) = K * Cexp ^ 2 * (R⁻¹ * R ^ 2) := by ring
        _ = K * Cexp ^ 2 * R := by rw [hRR]
    linarith only [hle, heq.le, heq.ge]
  have t2 : |α * K * (RobinCaps.Compact.bdR m 1 (transLiftH1_tw hR gs.psi)
        (transLiftH1_tw hR gs.psi) - (m : ℝ))|
      ≤ α * K * (((m : ℝ) + 2) * Cexp ^ 2 + 2 * ((m : ℝ) + 1) * Real.sqrt 2 * |Cexp|) * R := by
    rw [abs_mul, abs_mul, abs_of_pos hα, abs_of_nonneg hK.le]
    have h0 : (0 : ℝ) ≤ α * K := by positivity
    calc α * K * |RobinCaps.Compact.bdR m 1 (transLiftH1_tw hR gs.psi)
          (transLiftH1_tw hR gs.psi) - (m : ℝ)|
        ≤ α * K * ((((m : ℝ) + 2) * Cexp ^ 2 + 2 * ((m : ℝ) + 1) * Real.sqrt 2 * |Cexp|) * R) :=
          mul_le_mul_of_nonneg_left hbdRexp h0
      _ = α * K * (((m : ℝ) + 2) * Cexp ^ 2 + 2 * ((m : ℝ) + 1) * Real.sqrt 2 * |Cexp|) * R := by
          ring
  have t3 : |(R * gs.nu - (m : ℝ) * α) * K| ≤ K * |Cexp| * R := by
    rw [abs_mul, abs_of_nonneg hK.le]
    have h1 : |R * gs.nu - (m : ℝ) * α| ≤ Cexp * R := hdelta
    have h2 : Cexp * R ≤ |Cexp| * R := mul_le_mul_of_nonneg_right (le_abs_self Cexp) hR.le
    calc |R * gs.nu - (m : ℝ) * α| * K ≤ (Cexp * R) * K :=
          mul_le_mul_of_nonneg_right h1 hK.le
      _ ≤ (|Cexp| * R) * K := mul_le_mul_of_nonneg_right h2 hK.le
      _ = K * |Cexp| * R := by ring
  calc |R⁻¹ * (K * (∫ y in ball (0 : EuclideanSpace ℝ (Fin m)) 1,
          ‖transLiftGrad_tw m R gs.psi y‖ ^ 2))
        + α * K * (RobinCaps.Compact.bdR m 1 (transLiftH1_tw hR gs.psi)
              (transLiftH1_tw hR gs.psi) - (m : ℝ))
        - (R * gs.nu - (m : ℝ) * α) * K|
      ≤ |R⁻¹ * (K * (∫ y in ball (0 : EuclideanSpace ℝ (Fin m)) 1,
            ‖transLiftGrad_tw m R gs.psi y‖ ^ 2))|
        + |α * K * (RobinCaps.Compact.bdR m 1 (transLiftH1_tw hR gs.psi)
              (transLiftH1_tw hR gs.psi) - (m : ℝ))|
        + |(R * gs.nu - (m : ℝ) * α) * K| :=
        abs_add_sub_le_tbf _ _ _
    _ ≤ K * Cexp ^ 2 * R
        + α * K * (((m : ℝ) + 2) * Cexp ^ 2 + 2 * ((m : ℝ) + 1) * Real.sqrt 2 * |Cexp|) * R
        + K * |Cexp| * R := by linarith only [t1, t2, t3]
    _ = (K * Cexp ^ 2
          + α * K * (((m : ℝ) + 2) * Cexp ^ 2 + 2 * ((m : ℝ) + 1) * Real.sqrt 2 * |Cexp|)
          + K * |Cexp|) * R := by ring

end
end RobinCaps.ThinDomain
