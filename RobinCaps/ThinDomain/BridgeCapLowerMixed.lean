import RobinCaps.ThinDomain.BridgeCapLowerW
import RobinCaps.ThinDomain.Eigen

/-!
# `lem:cap` for the single-cap thin domain: flat left cap, hemispherical right cap

This file assembles the manuscript's `lem:cap` input `CapLowerInput_gm`
(`RobinCaps/ThinDomain/AssemblyGen.lean`) for the **single-cap** thin domain of `eq:single-cap`,

`thinDomain (Cap.flat m K hK) (Cap.hemisphere m) L R`,

a flat left end (`Cap.flat m K hK`, `RobinCaps/Cap/Sharp.lean`, profile `θ ≡ 1`) and a
hemispherical right cap, for a weak transverse ground state
`gs : TransverseGroundState m α R bd`.

The whole argument mirrors `RobinCaps/ThinDomain/BridgeCapLowerW.lean`'s two-hemisphere weak
assembly `capLowerInput_gen_bcw`: the right (hemisphere) side is *literally* the same argument,
with `Cap.hemisphere m` playing both the left- and right-cap role there; the left (flat) side is
the same argument with `capTraceDataHemi_th m hm` replaced by an **abstract** trace datum
`tdF : CapTraceData (Cap.flat m K hK)` (supplied by the caller, not built here), `CapEntranceL2`/
`CapPoincare` replaced by the corresponding flat-cap hypotheses `henF`/`hPF`, and
`(Cap.hemisphere m).beta α` replaced by `(Cap.flat m K hK).beta α` (kept in that form, *not*
simplified to `α`, so that the statement matches `CapLowerInput_gm`'s generic shape
`Cm.beta α`/`Cp.beta α`).

## The one genuinely new ingredient

`RobinCaps/ThinDomain/BridgeCapLowerGen.lean`'s bookkeeping constant `capLowerConst_bcg` is
hard-coded to `Cm = Cp = Cap.hemisphere m` (its definition literally reads off
`(Cap.hemisphere m).revolutionVolume`), so it cannot serve both caps of the mixed domain at once.
This file's `capLowerConstGen_bcm` is the same bookkeeping constant, generalised to an
**arbitrary** cap `C : Cap m`; instantiating it once at `C = Cap.flat m K hK` and once at
`C = Cap.hemisphere m` and taking the `max` of the two produces a single constant `Ccap` that
dominates both per-cap constants, exactly as `capLowerInput_gen_bcw`'s single hemisphere-only
`capLowerConst_bcg` did in the two-hemisphere case. The per-cap `lem:cap` lemmas below
(`cap_lower_left_flat_bcm`, `cap_lower_right_hemi_bcm`, `cap_mass_left_flat_bcm`,
`cap_mass_right_hemi_bcm`) are therefore stated against an *external* `Ccap` together with the
hypothesis that the relevant per-cap constant is `≤ Ccap`, rather than being pinned to one
specific bookkeeping constant as in `BridgeCapLowerGen.lean`/`BridgeCapLowerW.lean`.

## Remaining hypotheses

Exactly the hypotheses of `capLowerInput_gen_bcw`, doubled across the two caps:

* `tdF : CapTraceData (Cap.flat m K hK)` — the flat cap's `Γ`-trace interface, abstract (there is
  no analogue of `capTraceDataHemi_th` for the flat cap in this project, so it is taken as an
  input, as the task specifies);
* `hPF : CapPoincare (Cap.flat m K hK) CP`, `henF : CapEntranceL2 (Cap.flat m K hK) C₁` — the
  flat-cap Poincaré and entrance-trace interfaces (the hemisphere side's analogues,
  `capPoincare_hemi_phg m` and `henH`, are as in `BridgeCapLowerGen.lean`/`BridgeCapLowerW.lean`);
* `hCexp : 0 ≤ Cexp` — as in `capLowerInput_gen_bcw`, not eliminable in general dimension (there
  is no canonical transverse ground-state family to bootstrap its sign from a single radius).

No `sorry`, `admit`, `axiom` or `native_decide` occurs in this file.
-/

open MeasureTheory Set Filter Metric

open scoped ENNReal Topology

noncomputable section

namespace RobinCaps.ThinDomain

open RobinCaps.Domain RobinCaps.Sobolev RobinCaps.Transverse RobinCaps.Cap

set_option linter.style.longLine false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

/-! ## 0. The flat cap: nonnegativity of `θ 0` -/

/-- The flat cap has `θ ≡ 1`, in particular `θ 0 = 1 ≥ 0`. -/
theorem flat_theta_zero_nonneg_bcm (m : ℕ) (K : ℝ) (hK : 0 < K) :
    0 ≤ (Cap.flat m K hK).θ 0 := by
  have h : (Cap.flat m K hK).θ 0 = 1 := rfl
  rw [h]; norm_num

/-! ## 1. The bookkeeping constant of `lem:cap`, generalised to an arbitrary cap

The general-cap analogue of `RobinCaps.ThinDomain.capLowerConst_bcg`
(`RobinCaps/ThinDomain/BridgeCapLowerGen.lean`), which hard-codes `Cm = Cp = Cap.hemisphere m`.
Every ingredient it is built from (`capLowerConstW`, `capPoincareConstW`, `Cap.revolutionVolume`)
is already stated for a general `Cap m` in `RobinCaps/Cap/LowerWeak.lean`, so the generalisation is
a direct copy. -/

/-- The bookkeeping constant `C` dominating the three constants produced by `cap_lower_weak_p`
and `cap_mass_bound_weak_p`, for an arbitrary cap `C`. -/
def capLowerConstGen_bcm {m : ℕ} (C : Cap m) (α : ℝ) (td : CapTraceData C) (CP C₁ Cexp : ℝ) :
    ℝ :=
  max (max (capLowerConstW C α td CP C₁ Cexp / omega m) (8 * C.revolutionVolume / omega m))
    (2 * capPoincareConstW C CP C₁)

theorem capLowerConstGen_nonneg_bcm {m : ℕ} (C : Cap m) (α : ℝ) (td : CapTraceData C)
    (CP C₁ Cexp : ℝ) : 0 ≤ capLowerConstGen_bcm C α td CP C₁ Cexp := by
  refine le_trans (le_trans ?_ (le_max_right _ _)) (le_max_left _ _)
  have h8 : (0 : ℝ) ≤ 8 * C.revolutionVolume :=
    mul_nonneg (by norm_num) (revolutionVolume_nonneg_lw C)
  exact div_nonneg h8 (omega_pos m).le

theorem capLowerConstW_div_le_gen_bcm {m : ℕ} (C : Cap m) (α : ℝ) (td : CapTraceData C)
    (CP C₁ Cexp : ℝ) :
    capLowerConstW C α td CP C₁ Cexp / omega m ≤ capLowerConstGen_bcm C α td CP C₁ Cexp :=
  le_trans (le_max_left _ _) (le_max_left _ _)

theorem revolutionVolume_div_le_gen_bcm {m : ℕ} (C : Cap m) (α : ℝ) (td : CapTraceData C)
    (CP C₁ Cexp : ℝ) :
    8 * C.revolutionVolume / omega m ≤ capLowerConstGen_bcm C α td CP C₁ Cexp :=
  le_trans (le_max_right _ _) (le_max_left _ _)

theorem poincareConstW_le_gen_bcm {m : ℕ} (C : Cap m) (α : ℝ) (td : CapTraceData C)
    (CP C₁ Cexp : ℝ) :
    2 * capPoincareConstW C CP C₁ ≤ capLowerConstGen_bcm C α td CP C₁ Cexp :=
  le_max_right _ _

/-- `capLowerConstW ≥ 0`, for an arbitrary cap. The general-cap copy of
`capLowerConstW_nonneg_bcg`. -/
theorem capLowerConstW_nonneg_gen_bcm {m : ℕ} {C : Cap m} {α : ℝ} (hα : 0 ≤ α)
    (td : CapTraceData C) {CP C₁ Cexp : ℝ} (hCP : 0 ≤ CP) (hC₁ : 0 ≤ C₁) (hCexp : 0 ≤ Cexp) :
    0 ≤ capLowerConstW C α td CP C₁ Cexp := by
  have hA0 := (capConstW_ge C hα td hCP hC₁ hCexp).1
  rw [capLowerConstW]
  nlinarith [sq_nonneg (capConstW C α td CP C₁ Cexp),
    sq_nonneg (capConstW C α td CP C₁ Cexp + capConstW C α td CP C₁ Cexp ^ 2)]

/-! ## 2. The two cap pieces of the mixed domain's boundary form -/

/-- **The left-cap piece**, flat cap: the rescaled unit-cap `Γ`-trace form, at `c = R^{m/2}`,
against the abstract trace datum `tdF`. -/
def bdCapLFlat_bcm {m : ℕ} (hm : 1 ≤ m) (K : ℝ) (hK : 0 < K)
    (tdF : CapTraceData (Cap.flat m K hK)) (L R : ℝ) (hR : 0 < R)
    (hL : ((Cap.flat m K hK).K + (Cap.hemisphere m).K) * R < L)
    (u : H1P (thinDomain (Cap.flat m K hK) (Cap.hemisphere m) L R)) : ℝ :=
  R ^ m * (R ^ ((m : ℝ) / 2))⁻¹ ^ 2
    * tdF.bdΓ (capLeft hR hL (R ^ ((m : ℝ) / 2)) u) (capLeft hR hL (R ^ ((m : ℝ) / 2)) u)

/-- **The right-cap piece**, hemisphere: the rescaled unit-cap `Γ`-trace form, against the
concrete hemisphere trace datum `capTraceDataHemi_th m hm`. -/
def bdCapRHemi_bcm {m : ℕ} (hm : 1 ≤ m) (K : ℝ) (hK : 0 < K) (L R : ℝ) (hR : 0 < R)
    (hL : ((Cap.flat m K hK).K + (Cap.hemisphere m).K) * R < L)
    (u : H1P (thinDomain (Cap.flat m K hK) (Cap.hemisphere m) L R)) : ℝ :=
  R ^ m * (R ^ ((m : ℝ) / 2))⁻¹ ^ 2
    * (capTraceDataHemi_th m hm).bdΓ (capRight hR hL (R ^ ((m : ℝ) / 2)) u)
        (capRight hR hL (R ^ ((m : ℝ) / 2)) u)

/-- **The unit-cap energy of the left (flat) cap component is the thin-domain left-cap energy.**
The scaling factor `R^m · (R^{m/2})⁻¹²` is exactly `1` at `c = R^{m/2}` (`sq_rpow_half`), so this
needs no matching hypothesis, exactly as `capEnergyW_capLeft_bcg`. -/
theorem capEnergyW_capLeftFlat_bcm {m : ℕ} (hm : 1 ≤ m) (K : ℝ) (hK : 0 < K) {α L R : ℝ}
    (tdF : CapTraceData (Cap.flat m K hK)) (hR : 0 < R)
    (hL : ((Cap.flat m K hK).K + (Cap.hemisphere m).K) * R < L) (ν : ℝ)
    (u : H1P (thinDomain (Cap.flat m K hK) (Cap.hemisphere m) L R)) :
    capEnergyW (Cap.flat m K hK) α tdF R (R * ν - (m : ℝ) * α)
        (capLeft hR hL (R ^ ((m : ℝ) / 2)) u)
      = capEnergyL_gm α ν hR hL (bdCapLFlat_bcm hm K hK tdF L R hR hL) u := by
  have hc : (R ^ ((m : ℝ) / 2)) ^ 2 = R ^ m := sq_rpow_half m hR
  have hRne : R ≠ 0 := hR.ne'
  have hRmne : (R : ℝ) ^ m ≠ 0 := (pow_pos hR m).ne'
  rw [capEnergyW, capJW, capEnergyL_gm, bdCapLFlat_bcm, inv_pow, hc,
    dirichletP_capLeft_of_sq_eq hR hL hc u, massP_capLeft_of_sq_eq hR hL hc u]
  field_simp
  ring

/-- **The unit-cap energy of the right (hemisphere) cap component is the thin-domain right-cap
energy.** -/
theorem capEnergyW_capRightHemi_bcm {m : ℕ} (hm : 1 ≤ m) (K : ℝ) (hK : 0 < K) {α L R : ℝ}
    (hR : 0 < R) (hL : ((Cap.flat m K hK).K + (Cap.hemisphere m).K) * R < L) (ν : ℝ)
    (u : H1P (thinDomain (Cap.flat m K hK) (Cap.hemisphere m) L R)) :
    capEnergyW (Cap.hemisphere m) α (capTraceDataHemi_th m hm) R (R * ν - (m : ℝ) * α)
        (capRight hR hL (R ^ ((m : ℝ) / 2)) u)
      = capEnergyR_gm α ν hR hL (bdCapRHemi_bcm hm K hK L R hR hL) u := by
  have hc : (R ^ ((m : ℝ) / 2)) ^ 2 = R ^ m := sq_rpow_half m hR
  have hRne : R ≠ 0 := hR.ne'
  have hRmne : (R : ℝ) ^ m ≠ 0 := (pow_pos hR m).ne'
  rw [capEnergyW, capJW, capEnergyR_gm, bdCapRHemi_bcm, inv_pow, hc,
    dirichletP_capRight_of_sq_eq hR hL hc u, massP_capRight_of_sq_eq hR hL hc u]
  field_simp
  ring

/-! ## 3. `lem:cap` at a single admissible radius, flat left cap / hemisphere right cap

The mixed-domain copies of `cap_lower_left_gm_bcw`/`cap_lower_right_gm_bcw`/
`cap_mass_left_gm_bcw`/`cap_mass_right_gm_bcw` (`BridgeCapLowerW.lean`), each stated against an
*external* bookkeeping constant `Ccap` (rather than a fixed `capLowerConst_bcg`), together with
the hypothesis that the relevant per-cap constant `capLowerConstGen_bcm` is `≤ Ccap`. This lets
`capLowerInput_mixed_bcm` below instantiate `Ccap` as the `max` of the flat- and hemisphere-side
bookkeeping constants. -/

theorem cap_lower_left_flat_bcm {m : ℕ} (hm : 1 ≤ m) (K : ℝ) (hK : 0 < K) {α L R : ℝ}
    (hα : 0 < α) (tdF : CapTraceData (Cap.flat m K hK)) {CP C₁ Cexp Ccap : ℝ}
    (hP : CapPoincare (Cap.flat m K hK) CP) (hen : CapEntranceL2 (Cap.flat m K hK) C₁)
    (hR : 0 < R) {bd : TransH1 m R →ₗ[ℝ] TransH1 m R →ₗ[ℝ] ℝ}
    (gs : TransverseGroundState m α R bd) (hCexp : 0 ≤ Cexp)
    (hdR : Real.sqrt (omega m) / 2
      ≤ ∫ y in ball (0 : EuclideanSpace ℝ (Fin m)) 1, transLift m R gs.psi y)
    (hδ : |R * gs.nu - (m : ℝ) * α| ≤ Cexp * R)
    (hRc : R < capR0W (Cap.flat m K hK) α tdF CP C₁ Cexp)
    (hBR : capLowerConstW (Cap.flat m K hK) α tdF CP C₁ Cexp * R
      ≤ omega m * (Cap.flat m K hK).beta α)
    (hCcap : capLowerConstGen_bcm (Cap.flat m K hK) α tdF CP C₁ Cexp ≤ Ccap)
    (hL : ((Cap.flat m K hK).K + (Cap.hemisphere m).K) * R < L)
    (u : H1P (thinDomain (Cap.flat m K hK) (Cap.hemisphere m) L R)) :
    ((Cap.flat m K hK).beta α - Ccap * R) * (axialRep_gm hR hL gs u).toFun 0 ^ 2
        + (2 * R)⁻¹ * dirichletP (gPartW (Cap.flat m K hK) (transLift m R gs.psi)
            (∫ y in ball (0 : EuclideanSpace ℝ (Fin m)) 1, transLift m R gs.psi y)
            (capLeft hR hL (R ^ ((m : ℝ) / 2)) u))
      ≤ capEnergyL_gm α gs.nu hR hL (bdCapLFlat_bcm hm K hK tdF L R hR hL) u := by
  have hkey := cap_lower_weak_p (Cap.flat m K hK) hm (flat_theta_zero_nonneg_bcm m K hK)
    tdF hP hen hCexp hα.le (flat_beta_pos m K hK hα).le
    (memLp_transLift_gm_bcw hR gs) (integral_transLift_sq_gm_bcw hR gs) rfl
    hdR hR hRc hδ hBR (capLeft hR hL (R ^ ((m : ℝ) / 2)) u)
  rw [capEnergyW_capLeftFlat_bcm hm K hK tdF hR hL gs.nu u,
    pCoefW_capLeft_gen_gm_bcw hR hL gs u] at hkey
  have hle : capLowerConstW (Cap.flat m K hK) α tdF CP C₁ Cexp / omega m ≤ Ccap :=
    le_trans (capLowerConstW_div_le_gen_bcm (Cap.flat m K hK) α tdF CP C₁ Cexp) hCcap
  have hcoef : (Cap.flat m K hK).beta α - Ccap * R
      ≤ (Cap.flat m K hK).beta α
        - capLowerConstW (Cap.flat m K hK) α tdF CP C₁ Cexp / omega m * R := by
    have := mul_le_mul_of_nonneg_right hle hR.le
    linarith
  have hstep := mul_le_mul_of_nonneg_right hcoef (sq_nonneg ((axialRep_gm hR hL gs u).toFun 0))
  have hdiv : (2 * R)⁻¹ * dirichletP (gPartW (Cap.flat m K hK) (transLift m R gs.psi)
      (∫ y in ball (0 : EuclideanSpace ℝ (Fin m)) 1, transLift m R gs.psi y)
      (capLeft hR hL (R ^ ((m : ℝ) / 2)) u))
      = dirichletP (gPartW (Cap.flat m K hK) (transLift m R gs.psi)
          (∫ y in ball (0 : EuclideanSpace ℝ (Fin m)) 1, transLift m R gs.psi y)
          (capLeft hR hL (R ^ ((m : ℝ) / 2)) u)) / (2 * R) := by ring
  rw [hdiv]
  linarith

theorem cap_lower_right_hemi_bcm {m : ℕ} (hm : 1 ≤ m) (K : ℝ) (hK : 0 < K) {α L R : ℝ}
    (hα : 0 < α) {CP C₁ Cexp Ccap : ℝ}
    (hP : CapPoincare (Cap.hemisphere m) CP) (hen : CapEntranceL2 (Cap.hemisphere m) C₁)
    (hR : 0 < R) {bd : TransH1 m R →ₗ[ℝ] TransH1 m R →ₗ[ℝ] ℝ}
    (gs : TransverseGroundState m α R bd) (hCexp : 0 ≤ Cexp)
    (hdR : Real.sqrt (omega m) / 2
      ≤ ∫ y in ball (0 : EuclideanSpace ℝ (Fin m)) 1, transLift m R gs.psi y)
    (hδ : |R * gs.nu - (m : ℝ) * α| ≤ Cexp * R)
    (hRc : R < capR0W (Cap.hemisphere m) α (capTraceDataHemi_th m hm) CP C₁ Cexp)
    (hBR : capLowerConstW (Cap.hemisphere m) α (capTraceDataHemi_th m hm) CP C₁ Cexp * R
      ≤ omega m * (Cap.hemisphere m).beta α)
    (hCcap : capLowerConstGen_bcm (Cap.hemisphere m) α (capTraceDataHemi_th m hm) CP C₁ Cexp
      ≤ Ccap)
    (hL : ((Cap.flat m K hK).K + (Cap.hemisphere m).K) * R < L)
    (u : H1P (thinDomain (Cap.flat m K hK) (Cap.hemisphere m) L R)) :
    ((Cap.hemisphere m).beta α - Ccap * R)
          * (axialRep_gm hR hL gs u).toFun
              (bulkLength (Cap.flat m K hK) (Cap.hemisphere m) L R) ^ 2
        + (2 * R)⁻¹ * dirichletP (gPartW (Cap.hemisphere m) (transLift m R gs.psi)
            (∫ y in ball (0 : EuclideanSpace ℝ (Fin m)) 1, transLift m R gs.psi y)
            (capRight hR hL (R ^ ((m : ℝ) / 2)) u))
      ≤ capEnergyR_gm α gs.nu hR hL (bdCapRHemi_bcm hm K hK L R hR hL) u := by
  have hkey := cap_lower_weak_p (Cap.hemisphere m) hm hemisphere_theta_zero_nonneg_bcg
    (capTraceDataHemi_th m hm) hP hen hCexp hα.le (hemisphere_beta_pos m hm hα).le
    (memLp_transLift_gm_bcw hR gs) (integral_transLift_sq_gm_bcw hR gs) rfl
    hdR hR hRc hδ hBR (capRight hR hL (R ^ ((m : ℝ) / 2)) u)
  rw [capEnergyW_capRightHemi_bcm hm K hK hR hL gs.nu u,
    pCoefW_capRight_gen_gm_bcw hR hL gs u] at hkey
  have hle : capLowerConstW (Cap.hemisphere m) α (capTraceDataHemi_th m hm) CP C₁ Cexp / omega m
      ≤ Ccap :=
    le_trans
      (capLowerConstW_div_le_gen_bcm (Cap.hemisphere m) α (capTraceDataHemi_th m hm) CP C₁ Cexp)
      hCcap
  have hcoef : (Cap.hemisphere m).beta α - Ccap * R
      ≤ (Cap.hemisphere m).beta α
        - capLowerConstW (Cap.hemisphere m) α (capTraceDataHemi_th m hm) CP C₁ Cexp / omega m
          * R := by
    have := mul_le_mul_of_nonneg_right hle hR.le
    linarith
  have hstep := mul_le_mul_of_nonneg_right hcoef
    (sq_nonneg ((axialRep_gm hR hL gs u).toFun
      (bulkLength (Cap.flat m K hK) (Cap.hemisphere m) L R)))
  have hdiv : (2 * R)⁻¹ * dirichletP (gPartW (Cap.hemisphere m) (transLift m R gs.psi)
      (∫ y in ball (0 : EuclideanSpace ℝ (Fin m)) 1, transLift m R gs.psi y)
      (capRight hR hL (R ^ ((m : ℝ) / 2)) u))
      = dirichletP (gPartW (Cap.hemisphere m) (transLift m R gs.psi)
          (∫ y in ball (0 : EuclideanSpace ℝ (Fin m)) 1, transLift m R gs.psi y)
          (capRight hR hL (R ^ ((m : ℝ) / 2)) u)) / (2 * R) := by ring
  rw [hdiv]
  linarith

theorem cap_mass_left_flat_bcm {m : ℕ} (hm : 1 ≤ m) (K : ℝ) (hK : 0 < K) {α L R : ℝ}
    (tdF : CapTraceData (Cap.flat m K hK)) {CP C₁ Cexp Ccap : ℝ}
    (hP : CapPoincare (Cap.flat m K hK) CP) (hen : CapEntranceL2 (Cap.flat m K hK) C₁)
    (hR : 0 < R) {bd : TransH1 m R →ₗ[ℝ] TransH1 m R →ₗ[ℝ] ℝ}
    (gs : TransverseGroundState m α R bd)
    (hdR : Real.sqrt (omega m) / 2
      ≤ ∫ y in ball (0 : EuclideanSpace ℝ (Fin m)) 1, transLift m R gs.psi y)
    (hCcap : capLowerConstGen_bcm (Cap.flat m K hK) α tdF CP C₁ Cexp ≤ Ccap)
    (hL : ((Cap.flat m K hK).K + (Cap.hemisphere m).K) * R < L)
    (u : H1P (thinDomain (Cap.flat m K hK) (Cap.hemisphere m) L R)) :
    massP (restrictLeft hR hL u)
      ≤ Ccap * R * (axialRep_gm hR hL gs u).toFun 0 ^ 2
        + Ccap * R * dirichletP (gPartW (Cap.flat m K hK) (transLift m R gs.psi)
              (∫ y in ball (0 : EuclideanSpace ℝ (Fin m)) 1, transLift m R gs.psi y)
              (capLeft hR hL (R ^ ((m : ℝ) / 2)) u)) := by
  have hkey := cap_mass_bound_weak_p (Cap.flat m K hK) hP hen (memLp_transLift_gm_bcw hR gs)
    (integral_transLift_sq_gm_bcw hR gs) rfl hdR hR.le (capLeft hR hL (R ^ ((m : ℝ) / 2)) u)
  rw [capMassScaledW_capLeft_gen_bcg hR hL (sq_rpow_half m hR) u,
    pCoefW_capLeft_gen_gm_bcw hR hL gs u] at hkey
  have hleV : 8 * (Cap.flat m K hK).revolutionVolume / omega m ≤ Ccap :=
    le_trans (revolutionVolume_div_le_gen_bcm (Cap.flat m K hK) α tdF CP C₁ Cexp) hCcap
  have hleP : 2 * capPoincareConstW (Cap.flat m K hK) CP C₁ ≤ Ccap :=
    le_trans (poincareConstW_le_gen_bcm (Cap.flat m K hK) α tdF CP C₁ Cexp) hCcap
  have e1 := mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_right hleV hR.le) (sq_nonneg ((axialRep_gm hR hL gs u).toFun 0))
  have e2 := mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_right hleP hR.le)
    (dirichletP_nonneg (gPartW (Cap.flat m K hK) (transLift m R gs.psi)
      (∫ y in ball (0 : EuclideanSpace ℝ (Fin m)) 1, transLift m R gs.psi y)
      (capLeft hR hL (R ^ ((m : ℝ) / 2)) u)))
  linarith

theorem cap_mass_right_hemi_bcm {m : ℕ} (hm : 1 ≤ m) (K : ℝ) (hK : 0 < K) {α L R : ℝ}
    {CP C₁ Cexp Ccap : ℝ}
    (hP : CapPoincare (Cap.hemisphere m) CP) (hen : CapEntranceL2 (Cap.hemisphere m) C₁)
    (hR : 0 < R) {bd : TransH1 m R →ₗ[ℝ] TransH1 m R →ₗ[ℝ] ℝ}
    (gs : TransverseGroundState m α R bd)
    (hdR : Real.sqrt (omega m) / 2
      ≤ ∫ y in ball (0 : EuclideanSpace ℝ (Fin m)) 1, transLift m R gs.psi y)
    (hCcap : capLowerConstGen_bcm (Cap.hemisphere m) α (capTraceDataHemi_th m hm) CP C₁ Cexp
      ≤ Ccap)
    (hL : ((Cap.flat m K hK).K + (Cap.hemisphere m).K) * R < L)
    (u : H1P (thinDomain (Cap.flat m K hK) (Cap.hemisphere m) L R)) :
    massP (restrictRight hR hL u)
      ≤ Ccap * R * (axialRep_gm hR hL gs u).toFun
              (bulkLength (Cap.flat m K hK) (Cap.hemisphere m) L R) ^ 2
        + Ccap * R * dirichletP (gPartW (Cap.hemisphere m) (transLift m R gs.psi)
              (∫ y in ball (0 : EuclideanSpace ℝ (Fin m)) 1, transLift m R gs.psi y)
              (capRight hR hL (R ^ ((m : ℝ) / 2)) u)) := by
  have hkey := cap_mass_bound_weak_p (Cap.hemisphere m) hP hen (memLp_transLift_gm_bcw hR gs)
    (integral_transLift_sq_gm_bcw hR gs) rfl hdR hR.le (capRight hR hL (R ^ ((m : ℝ) / 2)) u)
  rw [capMassScaledW_capRight_gen_bcg hR hL (sq_rpow_half m hR) u,
    pCoefW_capRight_gen_gm_bcw hR hL gs u] at hkey
  have hleV : 8 * (Cap.hemisphere m).revolutionVolume / omega m ≤ Ccap :=
    le_trans
      (revolutionVolume_div_le_gen_bcm (Cap.hemisphere m) α (capTraceDataHemi_th m hm) CP C₁
        Cexp) hCcap
  have hleP : 2 * capPoincareConstW (Cap.hemisphere m) CP C₁ ≤ Ccap :=
    le_trans (poincareConstW_le_gen_bcm (Cap.hemisphere m) α (capTraceDataHemi_th m hm) CP C₁
      Cexp) hCcap
  have e1 := mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_right hleV hR.le) (sq_nonneg ((axialRep_gm hR hL gs u).toFun
      (bulkLength (Cap.flat m K hK) (Cap.hemisphere m) L R)))
  have e2 := mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_right hleP hR.le)
    (dirichletP_nonneg (gPartW (Cap.hemisphere m) (transLift m R gs.psi)
      (∫ y in ball (0 : EuclideanSpace ℝ (Fin m)) 1, transLift m R gs.psi y)
      (capRight hR hL (R ^ ((m : ℝ) / 2)) u)))
  linarith

/-! ## 4. `CapLowerInput_gm` for the mixed domain: flat left cap, hemisphere right cap -/

set_option linter.unusedVariables false in
/-- **`lem:cap` in thin-domain scaling for the single-cap thin domain** `eq:single-cap`: a flat
left end `Cap.flat m K hK` and a hemispherical right cap `Cap.hemisphere m`, for a weak transverse
ground state. The mixed-domain analogue of `capLowerInput_gen_bcw`. -/
theorem capLowerInput_mixed_bcm (m : ℕ) (hm : 1 ≤ m) (K : ℝ) (hK : 0 < K) (α : ℝ) (hα : 0 < α)
    (L : ℝ) (hL0 : 0 < L) (tdF : CapTraceData (Cap.flat m K hK))
    {C₁ C₁' CP Cexp : ℝ} (hCexp : 0 ≤ Cexp)
    (henF : CapEntranceL2 (Cap.flat m K hK) C₁) (hPF : CapPoincare (Cap.flat m K hK) CP)
    (henH : CapEntranceL2 (Cap.hemisphere m) C₁') :
    ∃ Ccap R₀ : ℝ, 0 ≤ Ccap ∧ 0 < R₀ ∧
      ∀ (R : ℝ) (hR : 0 < R), R < R₀ →
        ∀ (hL : ((Cap.flat m K hK).K + (Cap.hemisphere m).K) * R < L)
          {bd : TransH1 m R →ₗ[ℝ] TransH1 m R →ₗ[ℝ] ℝ} (gs : TransverseGroundState m α R bd),
          Real.sqrt (omega m) / 2
              ≤ (∫ y in ball (0 : EuclideanSpace ℝ (Fin m)) 1, transLift m R gs.psi y) →
          |R * gs.nu - (m : ℝ) * α| ≤ Cexp * R →
          CapLowerInput_gm gs Ccap hR hL (bdCapLFlat_bcm hm K hK tdF L R hR hL)
            (bdCapRHemi_bcm hm K hK L R hR hL) := by
  obtain ⟨CPH, hPH⟩ := capPoincare_hemi_phg m
  have hβF := flat_beta_pos m K hK hα
  have hβH := hemisphere_beta_pos m hm hα
  have hCcapF0 : 0 ≤ capLowerConstGen_bcm (Cap.flat m K hK) α tdF CP C₁ Cexp :=
    capLowerConstGen_nonneg_bcm (Cap.flat m K hK) α tdF CP C₁ Cexp
  have hCcapH0 : 0 ≤ capLowerConstGen_bcm (Cap.hemisphere m) α (capTraceDataHemi_th m hm) CPH C₁'
      Cexp :=
    capLowerConstGen_nonneg_bcm (Cap.hemisphere m) α (capTraceDataHemi_th m hm) CPH C₁' Cexp
  have hB0F : 0 ≤ capLowerConstW (Cap.flat m K hK) α tdF CP C₁ Cexp :=
    capLowerConstW_nonneg_gen_bcm hα.le tdF hPF.nonneg henF.nonneg hCexp
  have hB0H : 0 ≤ capLowerConstW (Cap.hemisphere m) α (capTraceDataHemi_th m hm) CPH C₁' Cexp :=
    capLowerConstW_nonneg_gen_bcm hα.le (capTraceDataHemi_th m hm) hPH.nonneg henH.nonneg hCexp
  have hdenF : (0 : ℝ) < capLowerConstW (Cap.flat m K hK) α tdF CP C₁ Cexp + 1 := by linarith
  have hdenH : (0 : ℝ) < capLowerConstW (Cap.hemisphere m) α (capTraceDataHemi_th m hm) CPH C₁'
      Cexp + 1 := by linarith
  refine ⟨max (capLowerConstGen_bcm (Cap.flat m K hK) α tdF CP C₁ Cexp)
      (capLowerConstGen_bcm (Cap.hemisphere m) α (capTraceDataHemi_th m hm) CPH C₁' Cexp),
    min (min (capR0W (Cap.flat m K hK) α tdF CP C₁ Cexp)
          (capR0W (Cap.hemisphere m) α (capTraceDataHemi_th m hm) CPH C₁' Cexp))
      (min (omega m * (Cap.flat m K hK).beta α
              / (capLowerConstW (Cap.flat m K hK) α tdF CP C₁ Cexp + 1))
        (omega m * (Cap.hemisphere m).beta α
              / (capLowerConstW (Cap.hemisphere m) α (capTraceDataHemi_th m hm) CPH C₁' Cexp
                  + 1))),
    le_trans hCcapF0 (le_max_left _ _),
    lt_min
      (lt_min (capR0W_pos (Cap.flat m K hK) hα.le tdF hPF.nonneg henF.nonneg hCexp)
        (capR0W_pos (Cap.hemisphere m) hα.le (capTraceDataHemi_th m hm) hPH.nonneg henH.nonneg
          hCexp))
      (lt_min (div_pos (mul_pos (omega_pos m) hβF) hdenF)
        (div_pos (mul_pos (omega_pos m) hβH) hdenH)),
    fun R hR hR0 hL bd gs hdR hδ => ?_⟩
  have hRcF : R < capR0W (Cap.flat m K hK) α tdF CP C₁ Cexp :=
    lt_of_lt_of_le hR0 (le_trans (min_le_left _ _) (min_le_left _ _))
  have hRcH : R < capR0W (Cap.hemisphere m) α (capTraceDataHemi_th m hm) CPH C₁' Cexp :=
    lt_of_lt_of_le hR0 (le_trans (min_le_left _ _) (min_le_right _ _))
  have hRbF : R < omega m * (Cap.flat m K hK).beta α
      / (capLowerConstW (Cap.flat m K hK) α tdF CP C₁ Cexp + 1) :=
    lt_of_lt_of_le hR0 (le_trans (min_le_right _ _) (min_le_left _ _))
  have hRbH : R < omega m * (Cap.hemisphere m).beta α
      / (capLowerConstW (Cap.hemisphere m) α (capTraceDataHemi_th m hm) CPH C₁' Cexp + 1) :=
    lt_of_lt_of_le hR0 (le_trans (min_le_right _ _) (min_le_right _ _))
  have hBRF : capLowerConstW (Cap.flat m K hK) α tdF CP C₁ Cexp * R
      ≤ omega m * (Cap.flat m K hK).beta α := by
    have h := (lt_div_iff₀ hdenF).1 hRbF
    nlinarith [hR.le, hB0F]
  have hBRH : capLowerConstW (Cap.hemisphere m) α (capTraceDataHemi_th m hm) CPH C₁' Cexp * R
      ≤ omega m * (Cap.hemisphere m).beta α := by
    have h := (lt_div_iff₀ hdenH).1 hRbH
    nlinarith [hR.le, hB0H]
  have hCcapFle : capLowerConstGen_bcm (Cap.flat m K hK) α tdF CP C₁ Cexp
      ≤ max (capLowerConstGen_bcm (Cap.flat m K hK) α tdF CP C₁ Cexp)
          (capLowerConstGen_bcm (Cap.hemisphere m) α (capTraceDataHemi_th m hm) CPH C₁' Cexp) :=
    le_max_left _ _
  have hCcapHle : capLowerConstGen_bcm (Cap.hemisphere m) α (capTraceDataHemi_th m hm) CPH C₁'
      Cexp
      ≤ max (capLowerConstGen_bcm (Cap.flat m K hK) α tdF CP C₁ Cexp)
          (capLowerConstGen_bcm (Cap.hemisphere m) α (capTraceDataHemi_th m hm) CPH C₁' Cexp) :=
    le_max_right _ _
  have hCcap0 : (0 : ℝ) ≤ max (capLowerConstGen_bcm (Cap.flat m K hK) α tdF CP C₁ Cexp)
      (capLowerConstGen_bcm (Cap.hemisphere m) α (capTraceDataHemi_th m hm) CPH C₁' Cexp) :=
    le_trans hCcapF0 (le_max_left _ _)
  exact ⟨fun u => dirichletP (gPartW (Cap.flat m K hK) (transLift m R gs.psi)
        (∫ y in ball (0 : EuclideanSpace ℝ (Fin m)) 1, transLift m R gs.psi y)
        (capLeft hR hL (R ^ ((m : ℝ) / 2)) u)),
    fun u => dirichletP (gPartW (Cap.hemisphere m) (transLift m R gs.psi)
        (∫ y in ball (0 : EuclideanSpace ℝ (Fin m)) 1, transLift m R gs.psi y)
        (capRight hR hL (R ^ ((m : ℝ) / 2)) u)),
    fun u => dirichletP_nonneg _, fun u => dirichletP_nonneg _,
    fun u => cap_lower_left_flat_bcm hm K hK hα tdF hPF henF hR gs hCexp hdR hδ hRcF hBRF
      hCcapFle hL u,
    fun u => cap_lower_right_hemi_bcm hm K hK hα hPH henH hR gs hCexp hdR hδ hRcH hBRH
      hCcapHle hL u,
    fun u => cap_mass_left_flat_bcm hm K hK tdF hPF henF hR gs hdR hCcapFle hL u,
    fun u => cap_mass_right_hemi_bcm hm K hK hPH henH hR gs hdR hCcapHle hL u⟩

end RobinCaps.ThinDomain

end
