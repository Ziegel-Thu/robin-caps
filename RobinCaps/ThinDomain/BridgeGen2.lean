import RobinCaps.ThinDomain.BridgeCapLowerGen2
import RobinCaps.ThinDomain.TrialAssemblyGen2
import RobinCaps.ThinDomain.TrialBoundGen
import RobinCaps.ThinDomain.BridgeInterfaceGen
import RobinCaps.ThinDomain.BridgeGen
import RobinCaps.ThinDomain.AssemblyGen

/-!
# Assembling `TraceSplitFamilyInput_gm`, `InterfaceTraceInput_gm`, `TrialEnergyInput_gm`,
an arbitrary pair of caps

This file redoes `RobinCaps/ThinDomain/BridgeMixed.lean`'s assembly of the three `Prop` inputs of
`AssemblyGen.lean`'s `mainTheorem_gm` for an **arbitrary** pair of admissible caps `Cm Cp : Cap m`
with **abstract** cap trace data `tdM : CapTraceData Cm`, `tdP : CapTraceData Cp`, from the
per-radius bricks of `RobinCaps/ThinDomain/BridgeCapLowerGen2.lean` (`capLowerInput_gen2_bg2`,
`bdCapL_bg2`, `bdCapR_bg2`), `RobinCaps/ThinDomain/TrialAssemblyGen2.lean` (`TraceSplitGen2_ag2`,
`capEnergyTermGen_ag2`, `renormEnergy_trialAC_ag2`) and `RobinCaps/ThinDomain/TrialBoundGen.lean`
(`capEnergyTermGen_tbg`, `capTrialConstGen_tbg`, `capEnergyTermGen_sub_beta_tbg'`), for an
arbitrary ground-state family `gsf : GroundStateFamily_gm m α R₀` whose boundary form `gsf.bd R`
is only *propositionally* `bdR m R` (`hbd`), exactly mirroring `BridgeMixed.lean`'s treatment of
the mixed flat/hemisphere pair.

The transport lemma `transportBd_bg` and the interface specialisation
`interfaceTraceInput_gen_big` are already stated for arbitrary caps, so §1 and §2 below simply
reuse them at an arbitrary pair `(Cm, Cp)`. §3 assembles `TrialEnergyInput_gm` from the *two*
per-cap upper bounds, both instances of the *same* lemma `capEnergyTermGen_sub_beta_tbg'`
(applied at `Cm, tdM` and at `Cp, tdP`), taking the uniform constant `A` to be the `max` of the
two per-cap constants `capTrialConstGen_tbg Cm tdM α Cexp`/`capTrialConstGen_tbg Cp tdP α Cexp` —
simpler than `BridgeMixed.lean`, which had to juggle two different lemmas (one for the flat cap,
one for the hemisphere). §4 packages the whole assembly as the `Prop` `BridgeGen2_bg3` and proves
it in `mainTheorem_gen2_bridged_bg3`.

No `sorry`, `admit`, `axiom` or `native_decide` occurs in this file.
-/

open MeasureTheory Set Filter Metric

open scoped ENNReal Topology InnerProductSpace

noncomputable section

namespace RobinCaps.ThinDomain

open RobinCaps.Domain RobinCaps.Sobolev RobinCaps.Transverse RobinCaps.Cap RobinCaps.Compact

set_option linter.style.longLine false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

variable {m : ℕ}

/-! ## 1. `TraceSplitFamilyInput_gm`, an arbitrary pair of caps -/

/-- **`TraceSplitFamilyInput_gm` from the general-cap trace split (`TraceSplitGen2_ag2`) and the
weak `lem:cap` lower bound (`capLowerInput_gen2_bg2`).** The radius threshold `R₁` and the
constant `Ccap` come from `capLowerInput_gen2_bg2`; every family radius `R₀ ≤ R₁` inherits the
bound. The general-cap analogue of `BridgeMixed.traceSplitFamilyInput_bm`. -/
theorem traceSplitFamilyInput_bg3 (hm : 1 ≤ m) (Cm Cp : Cap m) (α : ℝ) (hα : 0 < α)
    (L : ℝ) (hL0 : 0 < L) (tdM : CapTraceData Cm) (tdP : CapTraceData Cp)
    {C₁ C₁' CPm CPp Cexp : ℝ} (hCexp : 0 ≤ Cexp)
    (henM : CapEntranceL2 Cm C₁) (hPM : CapPoincare Cm CPm)
    (henP : CapEntranceL2 Cp C₁') (hPP : CapPoincare Cp CPp) :
    ∃ Ccap R₁ : ℝ, 0 ≤ Ccap ∧ 0 < R₁ ∧
      ∀ (R₀ : ℝ) (hR₀ : R₀ ≤ R₁) (gsf : GroundStateFamily_gm m α R₀)
        (hbd : ∀ R, gsf.bd R = bdR m R)
        (tdf : TraceFamily Cm Cp L R₀)
        (hsplit : ∀ R hR hR₀', ∀ hL, TraceSplitGen2_ag2 Cm Cp tdM tdP hR hL (tdf R hR hR₀'))
        (hexp : ∀ R hR hR₀', ExpW_tw m α R (gsf.gs R hR hR₀') Cexp),
        TraceSplitFamilyInput_gm Cm Cp L α Ccap R₀ gsf tdf := by
  obtain ⟨Ccap, R₁, hCcap, hR₁, hmain⟩ :=
    capLowerInput_gen2_bg2 m hm Cm Cp α hα L hL0 tdM tdP hCexp henM hPM henP hPP
  refine ⟨Ccap, R₁, hCcap, hR₁, ?_⟩
  intro R₀ hR₀ gsf hbd tdf hsplit hexp
  refine ⟨fun R hR hR₀' hL =>
    ⟨bdCapL_bg2 Cm Cp tdM L R hR hL, bdCapR_bg2 Cm Cp tdP L R hR hL, ?_, ?_⟩⟩
  · -- `TraceSplitInput_gm hR (tdf R hR hR₀') (gsf.bd R) bdCapL_bg2 bdCapR_bg2`
    refine ⟨fun u => ?_, fun u => ?_, fun u => ?_⟩
    · have hfac : (0 : ℝ) ≤ R ^ m * (R ^ ((m : ℝ) / 2))⁻¹ ^ 2 := by positivity
      exact mul_nonneg hfac (tdM.bdΓ_nonneg _)
    · have hfac : (0 : ℝ) ≤ R ^ m * (R ^ ((m : ℝ) / 2))⁻¹ ^ 2 := by positivity
      exact mul_nonneg hfac (tdP.bdΓ_nonneg _)
    · have hs := hsplit R hR hR₀' hL u
      rw [hs, hbd R, bdCapL_bg2, bdCapR_bg2]
  · -- `CapLowerInput_gm (gsf.gs R hR hR₀') Ccap hR hL bdCapL_bg2 bdCapR_bg2`
    have hRR₁ : R < R₁ := lt_of_lt_of_le hR₀' hR₀
    have hexpR := hexp R hR hR₀'
    have hδ : |R * (gsf.gs R hR hR₀').nu - (m : ℝ) * α| ≤ Cexp * R := by
      have hnu := hexpR.nuExp
      rw [abs_le] at hnu ⊢
      obtain ⟨hnu1, hnu2⟩ := hnu
      constructor
      · nlinarith [hnu1, hnu2, hR]
      · nlinarith [hnu1, hnu2, hR]
    exact hmain R hR hRR₁ hL (gsf.gs R hR hR₀') hexpR.dR_ge hδ

/-! ## 2. `InterfaceTraceInput_gm`, an arbitrary pair of caps -/

/-- **`InterfaceTraceInput_gm` from the general-`m`, arbitrary-`bd`/`gs` interface trace bound
`interfaceTraceInput_gen_big`**, specialised to an arbitrary cap pair `(Cm, Cp)` and to the
family's own `gsf.bd R`/`gsf.gs R hR hR₀`. `axialRep_big_eq_gm_bcw` (already stated for arbitrary
caps) identifies the two axial-profile representatives definitionally. The general-cap analogue of
`BridgeMixed.interfaceTraceInput_bm`. -/
theorem interfaceTraceInput_bg3 (m : ℕ) (Cm Cp : Cap m) (α : ℝ) (hα : 0 < α) (L : ℝ)
    (hL0 : 0 < L) :
    ∃ Cif R₁ : ℝ, 0 ≤ Cif ∧ 0 < R₁ ∧
      ∀ (R₀ : ℝ) (hR₀ : R₀ ≤ R₁) (gsf : GroundStateFamily_gm m α R₀),
        InterfaceTraceInput_gm Cm Cp L α Cif R₀ gsf := by
  obtain ⟨Cif, R₁, hCif, hR₁, hbig⟩ :=
    interfaceTraceInput_gen_big m Cm Cp L α hα hL0
  refine ⟨Cif, R₁, hCif, hR₁, ?_⟩
  intro R₀ hR₀ gsf
  refine ⟨fun R hR hR₀' hL u => ?_⟩
  have hb := (interfaceTraceInput_le_big hbig hR₀).iface R hR hR₀' hL (gsf.bd R) (gsf.gs R hR hR₀') u
  rwa [axialRep_big_eq_gm_bcw] at hb

/-! ## 3. `TrialEnergyInput_gm`, an arbitrary pair of caps -/

/-- **`capEnergyTermGen_tbg` agrees with `capEnergyTermGen_ag2`, at any cap, abstract trace
datum, ground state and test function.** Both unfold to the identical expression
`R⁻¹ · ∫_𝒞 |∇_zΦ|² + (α · td.bdΓ(Φ,Φ) − mα‖Φ‖²) − (Rν − mα)‖Φ‖²`, so this holds by `rfl`. -/
theorem capEnergyTermGen_tbg_eq_ag2_bg3 (C : Cap m) (td : CapTraceData C) {α R : ℝ}
    {bd : TransH1 m R →ₗ[ℝ] TransH1 m R →ₗ[ℝ] ℝ} (gs : TransverseGroundState m α R bd)
    (Φ : H1P C.body) :
    capEnergyTermGen_tbg C td α R gs Φ = capEnergyTermGen_ag2 C td α R gs Φ := rfl

/-- **`TrialEnergyInput_gm` from `trial_energy_field_ag2`/`renormEnergy_trialAC_ag2` and the
*single* upper-bound lemma `capEnergyTermGen_sub_beta_tbg'`, applied once at each cap.** The
constant `Ctr` is uniform in `R`: it is `|A|` for `A := max CM CP`, the `max` of the two
(uniform, `R`-independent) per-cap constants `CM := capTrialConstGen_tbg Cm tdM α Cexp` and
`CP := capTrialConstGen_tbg Cp tdP α Cexp` — the general-cap analogue of
`BridgeMixed.trialEnergyInput_bm`, simplified since both sides now come from the same lemma. -/
theorem trialEnergyInput_bg3 (hm : 1 ≤ m) (Cm Cp : Cap m) (α : ℝ) (hα : 0 < α) (L : ℝ)
    (hL0 : 0 < L) (tdM : CapTraceData Cm) (tdP : CapTraceData Cp) {Cexp : ℝ}
    (R₀ : ℝ) (hR₀1 : R₀ ≤ 1) (gsf : GroundStateFamily_gm m α R₀)
    (hbd : ∀ R, gsf.bd R = bdR m R)
    (tdf : TraceFamily Cm Cp L R₀)
    (hsplit : ∀ R hR hR₀', ∀ hL, TraceSplitGen2_ag2 Cm Cp tdM tdP hR hL (tdf R hR hR₀'))
    (hexp : ∀ R hR hR₀', ExpW_tw m α R (gsf.gs R hR hR₀') Cexp) :
    ∃ Ctr : ℝ, 0 ≤ Ctr ∧
      TrialEnergyInput_gm Cm Cp L α Ctr R₀ gsf tdf := by
  set A : ℝ := max (capTrialConstGen_tbg Cm tdM α Cexp) (capTrialConstGen_tbg Cp tdP α Cexp)
    with hAdef
  refine ⟨|A|, abs_nonneg A, ⟨fun R hR hR₀' hL v => ?_⟩⟩
  have hR1 : R ≤ 1 := le_trans hR₀'.le hR₀1
  set gs : TransverseGroundState m α R (bdR m R) := transportBd_bg (hbd R) (gsf.gs R hR hR₀')
    with hgsdef
  have hgspsi : gs.psi = (gsf.gs R hR hR₀').psi := transportBd_bg_psi (hbd R) (gsf.gs R hR hR₀')
  have hgsnu : gs.nu = (gsf.gs R hR hR₀').nu := transportBd_bg_nu (hbd R) (gsf.gs R hR hR₀')
  rw [← hgspsi, ← hgsnu]
  set ΦL : H1P Cm.body := capLiftW_tw Cm hR gs.psi with hΦLdef
  set ΦR : H1P Cp.body := capLiftW_tw Cp hR gs.psi with hΦRdef
  have hΦLtoFun : ΦL.toFun = fun p => transLift m R gs.psi p.2 :=
    funext fun p => capLiftW_tw_toFun Cm hR gs.psi p
  have hΦLgz : ΦL.gz = fun p => (R ^ ((m : ℝ) / 2) * R) • gs.psi.grad (R • p.2) :=
    funext fun p => capLiftW_tw_gz Cm hR gs.psi p
  have hΦRtoFun : ΦR.toFun = fun p => transLift m R gs.psi p.2 :=
    funext fun p => capLiftW_tw_toFun Cp hR gs.psi p
  have hΦRgz : ΦR.gz = fun p => (R ^ ((m : ℝ) / 2) * R) • gs.psi.grad (R • p.2) :=
    funext fun p => capLiftW_tw_gz Cp hR gs.psi p
  have he := hexp R hR hR₀'
  have hexpR : ExpW_tw m α R gs Cexp :=
    { psiH1 := by rw [hgspsi]; exact he.psiH1
      dR_close := by rw [hgspsi]; exact he.dR_close
      dR_ge := by rw [hgspsi]; exact he.dR_ge
      nuExp := by rw [hgsnu]; exact he.nuExp }
  have hcapLeq : capEnergyTermGen_tbg Cm tdM α R gs ΦL = capEnergyTermGen_ag2 Cm tdM α R gs ΦL :=
    capEnergyTermGen_tbg_eq_ag2_bg3 Cm tdM gs ΦL
  have hbL : |capEnergyTermGen_tbg Cm tdM α R gs ΦL - Cm.beta α|
      ≤ capTrialConstGen_tbg Cm tdM α Cexp * R :=
    capEnergyTermGen_sub_beta_tbg' Cm hm tdM hR hR1 hexpR
  have hcapL : |capEnergyTermGen_ag2 Cm tdM α R gs ΦL - Cm.beta α| ≤ |A| * R := by
    rw [← hcapLeq]
    have hCMA : capTrialConstGen_tbg Cm tdM α Cexp ≤ |A| :=
      le_trans (le_max_left _ _) (le_abs_self A)
    exact hbL.trans (mul_le_mul_of_nonneg_right hCMA hR.le)
  have hcapReq : capEnergyTermGen_tbg Cp tdP α R gs ΦR = capEnergyTermGen_ag2 Cp tdP α R gs ΦR :=
    capEnergyTermGen_tbg_eq_ag2_bg3 Cp tdP gs ΦR
  have hbR : |capEnergyTermGen_tbg Cp tdP α R gs ΦR - Cp.beta α|
      ≤ capTrialConstGen_tbg Cp tdP α Cexp * R :=
    capEnergyTermGen_sub_beta_tbg' Cp hm tdP hR hR1 hexpR
  have hcapR : |capEnergyTermGen_ag2 Cp tdP α R gs ΦR - Cp.beta α| ≤ |A| * R := by
    rw [← hcapReq]
    have hCPA : capTrialConstGen_tbg Cp tdP α Cexp ≤ |A| :=
      le_trans (le_max_right _ _) (le_abs_self A)
    exact hbR.trans (mul_le_mul_of_nonneg_right hCPA hR.le)
  have hsplitR : TraceSplitGen2_ag2 Cm Cp tdM tdP hR hL (tdf R hR hR₀') := hsplit R hR hR₀' hL
  obtain ⟨W, rfl⟩ := Submodule.Quotient.mk_surjective (Sobolev.nullOff _) v
  rw [liftQ_mk, robinFormPQ_mk, massPQ_mk, Sobolev.robinFormQ_mk,
    renormEnergy_trialAC_ag2 hR hL tdM tdP W gs (tdf R hR hR₀') hsplitR ΦL hΦLtoFun hΦLgz ΦR
      hΦRtoFun hΦRgz,
    Sobolev.robinForm]
  have hb0L : capEnergyTermGen_ag2 Cm tdM α R gs ΦL ≤ Cm.beta α + |A| * R := by
    have := (abs_le.1 hcapL).2
    linarith
  have hb0R : capEnergyTermGen_ag2 Cp tdP α R gs ΦR ≤ Cp.beta α + |A| * R := by
    have := (abs_le.1 hcapR).2
    linarith
  have h1 : W.toFun 0 ^ 2 * capEnergyTermGen_ag2 Cm tdM α R gs ΦL
      ≤ (Cm.beta α + |A| * R) * W.toFun 0 ^ 2 := by
    nlinarith [sq_nonneg (W.toFun 0), hb0L]
  have h2 : W.toFun (bulkLength Cm Cp L R) ^ 2 * capEnergyTermGen_ag2 Cp tdP α R gs ΦR
      ≤ (Cp.beta α + |A| * R) * W.toFun (bulkLength Cm Cp L R) ^ 2 := by
    nlinarith [sq_nonneg (W.toFun (bulkLength Cm Cp L R)), hb0R]
  linarith

/-! ## 4. The final combination, an arbitrary pair of caps -/

/-- The conclusion of this file, packaged so that `RobinCaps/ThinDomain/MainGeneral.lean` can be
written against it in parallel. -/
def BridgeGen2_bg3 (m : ℕ) (Cm Cp : Cap m) (L α : ℝ) (hL0 : 0 < L)
    (tdM : CapTraceData Cm) (tdP : CapTraceData Cp) (Cexp : ℝ)
    (hβm : 0 < Cm.beta α) (hβp : 0 < Cp.beta α) : Prop :=
  ∃ R₁ : ℝ, 0 < R₁ ∧ ∀ (R₀ : ℝ) (hR₀ : 0 < R₀) (hR₀1 : R₀ ≤ R₁)
      (gsf : GroundStateFamily_gm m α R₀) (hbd : ∀ R, gsf.bd R = bdR m R)
      (tdf : TraceFamily Cm Cp L R₀)
      (hsplit : ∀ R hR hR₀', ∀ hL, TraceSplitGen2_ag2 Cm Cp tdM tdP hR hL (tdf R hR hR₀'))
      (hexp : ∀ R hR hR₀', ExpW_tw m α R (gsf.gs R hR hR₀') Cexp),
    MainTheorem m Cm Cp L α hL0 hβm hβp gsf.nu' R₀ tdf

/-- **`thm:main`, fully assembled from the per-radius bricks**, for an **arbitrary** pair of
admissible caps `Cm Cp : Cap m` with abstract cap trace data, and an arbitrary ground-state family
whose boundary form is only propositionally `bdR m R`. The threshold `R₁` is the minimum of the
radii of `traceSplitFamilyInput_bg3`, `interfaceTraceInput_bg3` and the radius `1` needed by
`trialEnergyInput_bg3`. The general-cap analogue of `BridgeMixed.mainTheorem_mixed_bridged_bm`. -/
theorem mainTheorem_gen2_bridged_bg3 (m : ℕ) (hm : 1 ≤ m) (Cm Cp : Cap m) (L α : ℝ)
    (hL0 : 0 < L) (hα : 0 < α) (tdM : CapTraceData Cm) (tdP : CapTraceData Cp)
    {C₁ C₁' CPm CPp Cexp : ℝ} (hCexp : 0 ≤ Cexp)
    (henM : CapEntranceL2 Cm C₁) (hPM : CapPoincare Cm CPm)
    (henP : CapEntranceL2 Cp C₁') (hPP : CapPoincare Cp CPp) :
    BridgeGen2_bg3 m Cm Cp L α hL0 tdM tdP Cexp
      (cap_beta_pos_bg2 m hm Cm hα) (cap_beta_pos_bg2 m hm Cp hα) := by
  obtain ⟨Ccap, R₁split, hCcap, hR₁split, hsplitmain⟩ :=
    traceSplitFamilyInput_bg3 hm Cm Cp α hα L hL0 tdM tdP hCexp henM hPM henP hPP
  obtain ⟨Cif, R₁iface, hCif, hR₁iface, hifacemain⟩ :=
    interfaceTraceInput_bg3 m Cm Cp α hα L hL0
  refine ⟨min (min R₁split R₁iface) 1, lt_min (lt_min hR₁split hR₁iface) one_pos, ?_⟩
  intro R₀ hR₀ hR₀1 gsf hbd tdf hsplit hexp
  have hR₀split : R₀ ≤ R₁split := hR₀1.trans (le_trans (min_le_left _ _) (min_le_left _ _))
  have hR₀iface : R₀ ≤ R₁iface := hR₀1.trans (le_trans (min_le_left _ _) (min_le_right _ _))
  have hR₀one : R₀ ≤ 1 := hR₀1.trans (min_le_right _ _)
  have hsplit_gm := hsplitmain R₀ hR₀split gsf hbd tdf hsplit hexp
  have hif_gm := hifacemain R₀ hR₀iface gsf
  obtain ⟨Ctr, hCtr0, htr_gm⟩ :=
    trialEnergyInput_bg3 hm Cm Cp α hα L hL0 tdM tdP R₀ hR₀one gsf hbd tdf hsplit hexp
  exact mainTheorem_gm Cm Cp L α hL0 hα (cap_beta_pos_bg2 m hm Cm hα) (cap_beta_pos_bg2 m hm Cp hα)
    R₀ hR₀ gsf tdf hCcap hsplit_gm hif_gm htr_gm

end RobinCaps.ThinDomain

end
