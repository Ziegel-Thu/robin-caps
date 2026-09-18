import RobinCaps.ThinDomain.BridgeCapLowerMixed
import RobinCaps.ThinDomain.TrialAssemblyMixed
import RobinCaps.ThinDomain.TrialBoundFlat
import RobinCaps.ThinDomain.BridgeInterfaceGen
import RobinCaps.ThinDomain.BridgeGen
import RobinCaps.ThinDomain.AssemblyGen

/-!
# Assembling `TraceSplitFamilyInput_gm`, `InterfaceTraceInput_gm`, `TrialEnergyInput_gm`,
mixed flat/hemisphere caps

This file redoes `RobinCaps/ThinDomain/BridgeGen.lean`'s assembly of the three `Prop` inputs of
`AssemblyGen.lean`'s `mainTheorem_gm` for the **single-cap** thin domain of `eq:single-cap`,

`thinDomain (Cap.flat m K hK) (Cap.hemisphere m) L R`,

a flat left cap `Cap.flat m K hK` (`RobinCaps/Cap/Sharp.lean`, profile `θ ≡ 1`) and a
hemispherical right cap `Cap.hemisphere m`, from the per-radius bricks of
`RobinCaps/ThinDomain/BridgeCapLowerMixed.lean` (`capLowerInput_mixed_bcm`),
`RobinCaps/ThinDomain/TrialAssemblyMixed.lean` (`TraceSplitMixed_tam`, `trial_energy_field_tam`)
and `RobinCaps/ThinDomain/TrialBoundFlat.lean`/`RobinCaps/ThinDomain/TrialBoundW.lean`
(`FlatLiftBd_tbf`, `capEnergyTermFlat_sub_beta_tbf`, `ExpW_tw`, `capLiftW_tw`,
`capEnergyTermW_sub_beta_tw`), for an arbitrary ground-state family
`gsf : GroundStateFamily_gm m α R₀` whose boundary form `gsf.bd R` is only *propositionally*
`bdR m R` (`hbd`), exactly mirroring `BridgeGen.lean`'s treatment of the two-hemisphere domain.

The transport lemma `transportBd_bg` and the interface specialisation
`interfaceTraceInput_gen_big` are already stated for arbitrary caps, so §1 and §2 below simply
reuse them at `(Cm, Cp) := (Cap.flat m K hK, Cap.hemisphere m)`. §3 assembles
`TrialEnergyInput_gm` from the *two* per-cap upper bounds (`capEnergyTermFlat_sub_beta_tbf` for
the flat left cap, `capEnergyTermW_sub_beta_tw` for the hemispherical right cap), taking the
uniform constant `A` to be the `max` of the two per-cap constants, mirroring how
`BridgeGen.trialEnergyInput_bg` picks the single hemisphere constant `A`. §4 assembles
`mainTheorem_gm` into `mainTheorem_mixed_bridged_bm`, and §5 records the flat cap's
`β(𝒞) = α` identity, both as a standalone remark (`flat_beta_eq_alpha_bm`) and as a restatement
of `mainTheorem_mixed_bridged_bm` with `(Cap.flat m K hK).beta α` rewritten to `α` throughout.

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

/-! ## 1. `TraceSplitFamilyInput_gm`, mixed flat/hemisphere caps -/

/-- **`TraceSplitFamilyInput_gm` from the mixed-cap trace split (`TraceSplitMixed_tam`) and the
weak `lem:cap` lower bound (`capLowerInput_mixed_bcm`).**  The radius threshold `R₁` and the
constant `Ccap` come from `capLowerInput_mixed_bcm`; every family radius `R₀ ≤ R₁` inherits the
bound.  The mixed-domain analogue of `BridgeGen.traceSplitFamilyInput_bg`. -/
theorem traceSplitFamilyInput_bm (hm : 1 ≤ m) (K : ℝ) (hK : 0 < K) (α : ℝ) (hα : 0 < α)
    (L : ℝ) (hL0 : 0 < L) (tdF : CapTraceData (Cap.flat m K hK))
    {C₁ C₁' CP Cexp : ℝ} (hCexp : 0 ≤ Cexp)
    (henF : CapEntranceL2 (Cap.flat m K hK) C₁) (hPF : CapPoincare (Cap.flat m K hK) CP)
    (henH : CapEntranceL2 (Cap.hemisphere m) C₁') :
    ∃ Ccap R₁ : ℝ, 0 ≤ Ccap ∧ 0 < R₁ ∧
      ∀ (R₀ : ℝ) (hR₀ : R₀ ≤ R₁) (gsf : GroundStateFamily_gm m α R₀)
        (hbd : ∀ R, gsf.bd R = bdR m R)
        (tdf : TraceFamily (Cap.flat m K hK) (Cap.hemisphere m) L R₀)
        (hsplit : ∀ R hR hR₀', ∀ hL, TraceSplitMixed_tam hm K hK tdF hR hL (tdf R hR hR₀'))
        (hexp : ∀ R hR hR₀', ExpW_tw m α R (gsf.gs R hR hR₀') Cexp),
        TraceSplitFamilyInput_gm (Cap.flat m K hK) (Cap.hemisphere m) L α Ccap R₀ gsf tdf := by
  obtain ⟨Ccap, R₁, hCcap, hR₁, hmain⟩ :=
    capLowerInput_mixed_bcm m hm K hK α hα L hL0 tdF hCexp henF hPF henH
  refine ⟨Ccap, R₁, hCcap, hR₁, ?_⟩
  intro R₀ hR₀ gsf hbd tdf hsplit hexp
  refine ⟨fun R hR hR₀' hL =>
    ⟨bdCapLFlat_bcm hm K hK tdF L R hR hL, bdCapRHemi_bcm hm K hK L R hR hL, ?_, ?_⟩⟩
  · -- `TraceSplitInput_gm hR (tdf R hR hR₀') (gsf.bd R) bdCapLFlat_bcm bdCapRHemi_bcm`
    refine ⟨fun u => ?_, fun u => ?_, fun u => ?_⟩
    · have hfac : (0 : ℝ) ≤ R ^ m * (R ^ ((m : ℝ) / 2))⁻¹ ^ 2 := by positivity
      exact mul_nonneg hfac (tdF.bdΓ_nonneg _)
    · have hfac : (0 : ℝ) ≤ R ^ m * (R ^ ((m : ℝ) / 2))⁻¹ ^ 2 := by positivity
      exact mul_nonneg hfac ((capTraceDataHemi_th m hm).bdΓ_nonneg _)
    · have hs := hsplit R hR hR₀' hL u
      rw [hs, hbd R, bdCapLFlat_bcm, bdCapRHemi_bcm]
  · -- `CapLowerInput_gm (gsf.gs R hR hR₀') Ccap hR hL bdCapLFlat_bcm bdCapRHemi_bcm`
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

/-! ## 2. `InterfaceTraceInput_gm`, mixed flat/hemisphere caps -/

/-- **`InterfaceTraceInput_gm` from the general-`m`, arbitrary-`bd`/`gs` interface trace bound
`interfaceTraceInput_gen_big`**, specialised to the mixed cap pair
`(Cap.flat m K hK, Cap.hemisphere m)` and to the family's own `gsf.bd R`/`gsf.gs R hR hR₀`.
`axialRep_big_eq_gm_bcw` (already stated for arbitrary caps) identifies the two axial-profile
representatives definitionally.  The mixed-domain analogue of `BridgeGen.interfaceTraceInput_bg`.
-/
theorem interfaceTraceInput_bm (m : ℕ) (K : ℝ) (hK : 0 < K) (α : ℝ) (hα : 0 < α) (L : ℝ)
    (hL0 : 0 < L) :
    ∃ Cif R₁ : ℝ, 0 ≤ Cif ∧ 0 < R₁ ∧
      ∀ (R₀ : ℝ) (hR₀ : R₀ ≤ R₁) (gsf : GroundStateFamily_gm m α R₀),
        InterfaceTraceInput_gm (Cap.flat m K hK) (Cap.hemisphere m) L α Cif R₀ gsf := by
  obtain ⟨Cif, R₁, hCif, hR₁, hbig⟩ :=
    interfaceTraceInput_gen_big m (Cap.flat m K hK) (Cap.hemisphere m) L α hα hL0
  refine ⟨Cif, R₁, hCif, hR₁, ?_⟩
  intro R₀ hR₀ gsf
  refine ⟨fun R hR hR₀' hL u => ?_⟩
  have hb := (interfaceTraceInput_le_big hbig hR₀).iface R hR hR₀' hL (gsf.bd R) (gsf.gs R hR hR₀') u
  rwa [axialRep_big_eq_gm_bcw] at hb

/-! ## 3. `TrialEnergyInput_gm`, mixed flat/hemisphere caps -/

/-- **`capEnergyTermL_tam` at `ΦL := capLiftW_tw (Cap.flat m K hK) hR gs.psi` agrees with
`capEnergyTermFlat_tbf`.**  Both unfold to the identical expression
`R⁻¹ · ∫_𝒞 |∇_zΨ_R|² + (α · tdF.bdΓ(Ψ_R,Ψ_R) − mα‖Ψ_R‖²) − (Rν − mα)‖Ψ_R‖²`, so this holds by
`rfl`. -/
theorem capEnergyTermL_tam_eq_tbf_bm (hm : 1 ≤ m) (K : ℝ) (hK : 0 < K)
    (tdF : CapTraceData (Cap.flat m K hK)) {α R : ℝ} (hR : 0 < R)
    {bd : TransH1 m R →ₗ[ℝ] TransH1 m R →ₗ[ℝ] ℝ} (gs : TransverseGroundState m α R bd) :
    capEnergyTermL_tam m K hK tdF α R gs (capLiftW_tw (Cap.flat m K hK) hR gs.psi)
      = capEnergyTermFlat_tbf hm K hK α hR tdF gs := rfl

/-- **`TrialEnergyInput_gm` from `trial_energy_field_tam`, `capEnergyTermFlat_sub_beta_tbf` (flat
left cap) and `capEnergyTermW_sub_beta_tw` (hemispherical right cap).**  The constant `Ctr` is
uniform in `R`: it is `|A|` for `A := max CF CH`, the `max` of the (uniform, `R`-independent)
flat-cap constant `CF` (from `capEnergyTermFlat_sub_beta_tbf`) and the hemisphere-cap constant
`CH` (the explicit constant of `capEnergyTermW_sub_beta_tw`) — the mixed-domain analogue of
`BridgeGen.trialEnergyInput_bg`. -/
theorem trialEnergyInput_bm (hm : 1 ≤ m) (K : ℝ) (hK : 0 < K) (α : ℝ) (hα : 0 < α) (L : ℝ)
    (hL0 : 0 < L) (tdF : CapTraceData (Cap.flat m K hK)) (hlift : FlatLiftBd_tbf m K hK tdF)
    {C₁ C₁' CP Cexp : ℝ} (hCexp : 0 ≤ Cexp)
    (henF : CapEntranceL2 (Cap.flat m K hK) C₁) (hPF : CapPoincare (Cap.flat m K hK) CP)
    (henH : CapEntranceL2 (Cap.hemisphere m) C₁')
    (R₀ : ℝ) (hR₀1 : R₀ ≤ 1) (gsf : GroundStateFamily_gm m α R₀)
    (hbd : ∀ R, gsf.bd R = bdR m R)
    (tdf : TraceFamily (Cap.flat m K hK) (Cap.hemisphere m) L R₀)
    (hsplit : ∀ R hR hR₀', ∀ hL, TraceSplitMixed_tam hm K hK tdF hR hL (tdf R hR hR₀'))
    (hexp : ∀ R hR hR₀', ExpW_tw m α R (gsf.gs R hR hR₀') Cexp) :
    ∃ Ctr : ℝ, 0 ≤ Ctr ∧
      TrialEnergyInput_gm (Cap.flat m K hK) (Cap.hemisphere m) L α Ctr R₀ gsf tdf := by
  obtain ⟨CF, hCF0, hCFmain⟩ := capEnergyTermFlat_sub_beta_tbf m hm K hK α hα tdF hlift Cexp
  set CH : ℝ := (Cap.hemisphere m).K * Cexp ^ 2
    + (|α| * capBdryConstW_tw m hm Cexp + (m : ℝ) * |α| * capMassConstW_tw m Cexp
        + Cexp * (Cap.hemisphere m).K) with hCHdef
  set A : ℝ := max CF CH with hAdef
  refine ⟨|A|, abs_nonneg A, ⟨fun R hR hR₀' hL v => ?_⟩⟩
  have hR1 : R ≤ 1 := le_trans hR₀'.le hR₀1
  set gs : TransverseGroundState m α R (bdR m R) := transportBd_bg (hbd R) (gsf.gs R hR hR₀')
    with hgsdef
  have hgspsi : gs.psi = (gsf.gs R hR hR₀').psi := transportBd_bg_psi (hbd R) (gsf.gs R hR hR₀')
  have hgsnu : gs.nu = (gsf.gs R hR hR₀').nu := transportBd_bg_nu (hbd R) (gsf.gs R hR hR₀')
  rw [← hgspsi, ← hgsnu]
  set ΦL : H1P (Cap.flat m K hK).body := capLiftW_tw (Cap.flat m K hK) hR gs.psi with hΦLdef
  set ΦR : H1P (Cap.hemisphere m).body := capLiftW_tw (Cap.hemisphere m) hR gs.psi with hΦRdef
  have hΦLtoFun : ΦL.toFun = fun p => transLift m R gs.psi p.2 :=
    funext fun p => capLiftW_tw_toFun (Cap.flat m K hK) hR gs.psi p
  have hΦLgz : ΦL.gz = fun p => (R ^ ((m : ℝ) / 2) * R) • gs.psi.grad (R • p.2) :=
    funext fun p => capLiftW_tw_gz (Cap.flat m K hK) hR gs.psi p
  have hΦRtoFun : ΦR.toFun = fun p => transLift m R gs.psi p.2 :=
    funext fun p => capLiftW_tw_toFun (Cap.hemisphere m) hR gs.psi p
  have hΦRgz : ΦR.gz = fun p => (R ^ ((m : ℝ) / 2) * R) • gs.psi.grad (R • p.2) :=
    funext fun p => capLiftW_tw_gz (Cap.hemisphere m) hR gs.psi p
  have he := hexp R hR hR₀'
  have hexpR : ExpW_tw m α R gs Cexp :=
    { psiH1 := by rw [hgspsi]; exact he.psiH1
      dR_close := by rw [hgspsi]; exact he.dR_close
      dR_ge := by rw [hgspsi]; exact he.dR_ge
      nuExp := by rw [hgsnu]; exact he.nuExp }
  have hcapLeq : capEnergyTermL_tam m K hK tdF α R gs ΦL
      = capEnergyTermFlat_tbf hm K hK α hR tdF gs :=
    capEnergyTermL_tam_eq_tbf_bm hm K hK tdF hR gs
  have hcapL : |capEnergyTermL_tam m K hK tdF α R gs ΦL - (Cap.flat m K hK).beta α| ≤ |A| * R := by
    rw [hcapLeq]
    have hb := hCFmain R hR hR1 gs hexpR
    have hCFA : CF ≤ |A| := le_trans (le_max_left CF CH) (le_abs_self A)
    exact hb.trans (mul_le_mul_of_nonneg_right hCFA hR.le)
  have hcapReq : capEnergyTermW_taw m hm α R gs ΦR = capEnergyTermW_tw hm α hR gs :=
    capEnergyTermW_taw_eq_tw_bg hm α R hR gs
  have hcapR : |capEnergyTermW_taw m hm α R gs ΦR - (Cap.hemisphere m).beta α| ≤ |A| * R := by
    rw [hcapReq]
    have hb := capEnergyTermW_sub_beta_tw hm hR hR1 hexpR
    have hCHA : CH ≤ |A| := le_trans (le_max_right CF CH) (le_abs_self A)
    exact hb.trans (mul_le_mul_of_nonneg_right hCHA hR.le)
  have hsplitR : TraceSplitMixed_tam hm K hK tdF hR hL (tdf R hR hR₀') := hsplit R hR hR₀' hL
  obtain ⟨W, rfl⟩ := Submodule.Quotient.mk_surjective (Sobolev.nullOff _) v
  rw [liftQ_mk, robinFormPQ_mk, massPQ_mk, Sobolev.robinFormQ_mk,
    renormEnergy_trialAC_tam hm K hK tdF hR hL W gs (tdf R hR hR₀') hsplitR ΦL hΦLtoFun hΦLgz ΦR
      hΦRtoFun hΦRgz,
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

/-! ## 4. The final combination, mixed flat/hemisphere caps -/

/-- **`thm:main`, fully assembled from the per-radius bricks**, for the single-cap thin domain
with a flat left cap `Cap.flat m K hK` and a hemispherical right cap `Cap.hemisphere m`, and an
arbitrary ground-state family whose boundary form is only propositionally `bdR m R`.  The
threshold `R₁` is the minimum of the radii of `traceSplitFamilyInput_bm`, `interfaceTraceInput_bm`
and the radius `1` needed by `trialEnergyInput_bm`.  The mixed-domain analogue of
`BridgeGen.mainTheorem_bridged_bg`. -/
theorem mainTheorem_mixed_bridged_bm (hm : 1 ≤ m) (K : ℝ) (hK : 0 < K) (L α : ℝ) (hL0 : 0 < L)
    (hα : 0 < α) (tdF : CapTraceData (Cap.flat m K hK)) (hlift : FlatLiftBd_tbf m K hK tdF)
    {C₁ C₁' CP Cexp : ℝ} (hCexp : 0 ≤ Cexp) (henF : CapEntranceL2 (Cap.flat m K hK) C₁)
    (hPF : CapPoincare (Cap.flat m K hK) CP) (henH : CapEntranceL2 (Cap.hemisphere m) C₁') :
    ∃ R₁ : ℝ, 0 < R₁ ∧ ∀ (R₀ : ℝ) (hR₀ : 0 < R₀) (hR₀1 : R₀ ≤ R₁)
        (gsf : GroundStateFamily_gm m α R₀) (hbd : ∀ R, gsf.bd R = bdR m R)
        (tdf : TraceFamily (Cap.flat m K hK) (Cap.hemisphere m) L R₀)
        (hsplit : ∀ R hR hR₀', ∀ hL, TraceSplitMixed_tam hm K hK tdF hR hL (tdf R hR hR₀'))
        (hexp : ∀ R hR hR₀', ExpW_tw m α R (gsf.gs R hR hR₀') Cexp),
      MainTheorem m (Cap.flat m K hK) (Cap.hemisphere m) L α hL0 (flat_beta_pos m K hK hα)
        (hemisphere_beta_pos m hm hα) gsf.nu' R₀ tdf := by
  obtain ⟨Ccap, R₁split, hCcap, hR₁split, hsplitmain⟩ :=
    traceSplitFamilyInput_bm hm K hK α hα L hL0 tdF hCexp henF hPF henH
  obtain ⟨Cif, R₁iface, hCif, hR₁iface, hifacemain⟩ :=
    interfaceTraceInput_bm m K hK α hα L hL0
  refine ⟨min (min R₁split R₁iface) 1, lt_min (lt_min hR₁split hR₁iface) one_pos, ?_⟩
  intro R₀ hR₀ hR₀1 gsf hbd tdf hsplit hexp
  have hR₀split : R₀ ≤ R₁split := hR₀1.trans (le_trans (min_le_left _ _) (min_le_left _ _))
  have hR₀iface : R₀ ≤ R₁iface := hR₀1.trans (le_trans (min_le_left _ _) (min_le_right _ _))
  have hR₀one : R₀ ≤ 1 := hR₀1.trans (min_le_right _ _)
  have hsplit_gm := hsplitmain R₀ hR₀split gsf hbd tdf hsplit hexp
  have hif_gm := hifacemain R₀ hR₀iface gsf
  obtain ⟨Ctr, hCtr0, htr_gm⟩ :=
    trialEnergyInput_bm hm K hK α hα L hL0 tdF hlift hCexp henF hPF henH R₀ hR₀one gsf hbd tdf
      hsplit hexp
  exact mainTheorem_gm (Cap.flat m K hK) (Cap.hemisphere m) L α hL0 hα (flat_beta_pos m K hK hα)
    (hemisphere_beta_pos m hm hα) R₀ hR₀ gsf tdf hCcap hsplit_gm hif_gm htr_gm

/-! ## 5. The flat cap's `β(𝒞) = α` identity -/

/-- **`Interval.mu` only sees the *values* of its first two arguments**, not the specific proofs
of positivity supplied: if `p = p'` then `Interval.mu p q ℓ j hp hq hℓ hj = Interval.mu p' q ℓ j
hp' hq hℓ hj` for *any* proofs `hp : 0 < p`, `hp' : 0 < p'`.  Proved by `subst` + Lean's
definitional proof irrelevance for `Prop`, so that a plain `rw` can later replace a whole
`Interval.mu` application at once without running into the "motive is not type correct" issue
that a direct `rw` at `(Cap.flat m K hK).beta α` would hit (the positivity proof `hp` occurs in
the term being rewritten with a type that itself mentions `p`). -/
theorem interval_mu_congr_left_bm (p p' q ℓ : ℝ) (j : ℕ) (hp : 0 < p) (hp' : 0 < p') (hq : 0 < q)
    (hℓ : 0 < ℓ) (hj : 1 ≤ j) (hpp' : p = p') :
    Interval.mu p q ℓ j hp hq hℓ hj = Interval.mu p' q ℓ j hp' hq hℓ hj := by
  subst hpp'
  rfl

/-- **The flat cap's coefficient `β(𝒞)` is exactly the Robin parameter `α`**
(`Cap.flat_beta_eq_alpha`, recorded here at the `_bm` naming for this file's remark-level use):
`mainTheorem_mixed_bridged_bm`'s hypothesis `0 < (Cap.flat m K hK).beta α` may then be read as the
manuscript's `0 < β₋ = α`, and its conclusion's `μ_j(β₋,β₊;L)` as `μ_j(α,β₊;L)`. -/
theorem flat_beta_eq_alpha_bm (m : ℕ) (K : ℝ) (hK : 0 < K) (hm : 1 ≤ m) (α : ℝ) :
    (Cap.flat m K hK).beta α = α :=
  Cap.flat_beta_eq_alpha m K hK (Cap.omega_ne_zero m)

/-- **`mainTheorem_mixed_bridged_bm`, restated with `(Cap.flat m K hK).beta α` rewritten to `α`
throughout**, so that the conclusion reads exactly as the manuscript's `thm:main` with
`β₋ = α`: `|λ_j(Ω_R;α) − ν_R − μ_j(α,β₊;L)| ≤ C_J R`. -/
theorem mainTheorem_mixed_bridged_alpha_bm (hm : 1 ≤ m) (K : ℝ) (hK : 0 < K) (L α : ℝ)
    (hL0 : 0 < L) (hα : 0 < α) (tdF : CapTraceData (Cap.flat m K hK))
    (hlift : FlatLiftBd_tbf m K hK tdF) {C₁ C₁' CP Cexp : ℝ} (hCexp : 0 ≤ Cexp)
    (henF : CapEntranceL2 (Cap.flat m K hK) C₁) (hPF : CapPoincare (Cap.flat m K hK) CP)
    (henH : CapEntranceL2 (Cap.hemisphere m) C₁') :
    ∃ R₁ : ℝ, 0 < R₁ ∧ ∀ (R₀ : ℝ) (hR₀ : 0 < R₀) (hR₀1 : R₀ ≤ R₁)
        (gsf : GroundStateFamily_gm m α R₀) (hbd : ∀ R, gsf.bd R = bdR m R)
        (tdf : TraceFamily (Cap.flat m K hK) (Cap.hemisphere m) L R₀)
        (hsplit : ∀ R hR hR₀', ∀ hL, TraceSplitMixed_tam hm K hK tdF hR hL (tdf R hR hR₀'))
        (hexp : ∀ R hR hR₀', ExpW_tw m α R (gsf.gs R hR hR₀') Cexp),
      ∀ J : ℕ, ∃ C R₁' : ℝ, 0 ≤ C ∧ 0 < R₁' ∧ R₁' ≤ R₀ ∧
        ∀ (R : ℝ) (hR : 0 < R) (hRR₀ : R < R₀) (_hR₁ : R < R₁')
          (hLR : ((Cap.flat m K hK).K + (Cap.hemisphere m).K) * R < L) (j : ℕ) (hj : 1 ≤ j),
          j ≤ J →
          |lambdaThin hR hLR (tdf R hR hRR₀) α j - gsf.nu' R
              - Interval.mu α ((Cap.hemisphere m).beta α) L j hα (hemisphere_beta_pos m hm hα)
                  hL0 hj| ≤ C * R := by
  obtain ⟨R₁, hR₁pos, hmain⟩ :=
    mainTheorem_mixed_bridged_bm hm K hK L α hL0 hα tdF hlift hCexp henF hPF henH
  refine ⟨R₁, hR₁pos, ?_⟩
  intro R₀ hR₀ hR₀1 gsf hbd tdf hsplit hexp J
  obtain ⟨C, R₁', hC, hR₁'pos, hR₁'le, hbound⟩ :=
    hmain R₀ hR₀ hR₀1 gsf hbd tdf hsplit hexp J
  refine ⟨C, R₁', hC, hR₁'pos, hR₁'le, ?_⟩
  intro R hR hRR₀ hR₁ hLR j hj hjJ
  have hb := hbound R hR hRR₀ hR₁ hLR j hj hjJ
  have hmueq := interval_mu_congr_left_bm ((Cap.flat m K hK).beta α) α
    ((Cap.hemisphere m).beta α) L j (flat_beta_pos m K hK hα) hα (hemisphere_beta_pos m hm hα) hL0
    hj (flat_beta_eq_alpha_bm m K hK hm α)
  rwa [hmueq] at hb

end RobinCaps.ThinDomain

end
