import RobinCaps.ThinDomain.NuBall
import RobinCaps.ThinDomain.TraceGenAbs
import RobinCaps.ThinDomain.TraceGenIntegrable
import RobinCaps.ThinDomain.BridgeBulkTrace
import RobinCaps.ThinDomain.TrialAssemblyGen2
import RobinCaps.ThinDomain.BridgeCapLowerGen2

/-!
# `thm:main` for an arbitrary pair of admissible caps, general `m ≥ 1`

This file generalises `RobinCaps/ThinDomain/MainSingle.lean` (flat left cap, hemispherical right
cap) and `RobinCaps/ThinDomain/NuBall.lean` (both caps hemispherical) to an **arbitrary** pair of
admissible caps `Cm Cp : Cap m`, `m ≥ 1`, modulo three per-cap analytic inputs supplied by the
caller — `CapTraceData`, `CapEntranceL2`, `CapPoincare` — bundled here as the derived hypotheses
`CapTraceIntegrableAbs_tga Cm tdM` / `CapTraceIntegrableAbs_tga Cp tdP` (`hciM`/`hciP`) together
with an interface hypothesis `BridgeGen2Input_mgl`, restated verbatim from the (parallel, not
imported) companion file `RobinCaps/ThinDomain/BridgeGen2.lean`, whose `mainTheorem_gen2_bridged_bg3`
is expected to discharge it from `CapEntranceL2`/`CapPoincare`/`FlatLiftBd_tbf`-style per-cap data,
exactly as `RobinCaps/ThinDomain/BridgeMixed.lean`'s `mainTheorem_mixed_bridged_bm` discharges the
single-cap (flat/hemisphere) case.

## Contents

1. `continuousBoundaryIntegrableAbs_gen_mgl` — the general continuous-boundary integrability fact
   `ContinuousBoundaryIntegrableAbs_tga`, for an arbitrary cap pair. The proof is verbatim that of
   `RobinCaps.ThinDomain.continuousBoundaryIntegrableAbs_mixed_mi`
   (`RobinCaps/ThinDomain/MixedIntegrable.lean`), which is already general in both caps.
2. `hL_of_lt_R₀_mgl`, `traceFamilyGen2_mgl`, `traceFamilyGen2_mgl_eq`,
   `traceSplitGen2_traceFamilyGen2_mgl` — the concrete trace family built from `traceDataAbs_tga`
   (`RobinCaps/ThinDomain/TraceGenAbs.lean`), for an arbitrary cap pair with abstract trace data
   `tdM tdP`, and its `TraceSplitGen2_ag2` normalisation
   (`RobinCaps/ThinDomain/TrialAssemblyGen2.lean`).
3. `BridgeGen2Input_mgl` — the restated conclusion of the (parallel) bridge file, taken as an
   interface hypothesis.
4. `mainTheorem_general_exists_mgl`, `mainTheorem_general_nb_mgl` — `thm:main` for an arbitrary
   admissible cap pair, with `ν_R = nuBall m α R = λ₁(B_m(R);α)` explicit
   (`RobinCaps/ThinDomain/NuBall.lean`), first for one concrete trace family and then for every
   recorded trace family (`RobinCaps/ThinDomain/TraceUniqueFinal.lean`).

The counterexample corollary (`cor:counterexample`) is **not** produced here:
`RobinCaps.ThinDomain.counterexample_of_mainTheorem'` (`RobinCaps/ThinDomain/Eigen.lean`) is
hard-wired to two copies of `Cap.hemisphere m` (it uses `hemisphere_hL : 2 * R < L → …` and
`hemisphere_beta_pos` for *both* sides), so it does not typecheck against an arbitrary pair
`Cm Cp : Cap m` with the general admissibility hypothesis `(Cm.K + Cp.K) * R < L`. Producing a
counterexample corollary for a general cap pair would need a genuinely general replacement for
`counterexample_of_mainTheorem'`, which is out of scope here; this is flagged as an open interface
rather than attempted.

No `sorry`, `admit`, `axiom` or `native_decide` occurs in this file.
-/

open MeasureTheory Set Filter Metric

open scoped ENNReal Topology

noncomputable section

namespace RobinCaps.ThinDomain

open RobinCaps.Domain RobinCaps.Sobolev RobinCaps.Transverse RobinCaps.Cap RobinCaps.Compact

set_option linter.style.longLine false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

/-! ## 1. The general continuous-boundary integrability -/

/-- **`ContinuousBoundaryIntegrableAbs_tga`, discharged for an arbitrary pair of admissible caps**
`Cm Cp : Cap m`. Verbatim the proof of `RobinCaps.ThinDomain.continuousBoundaryIntegrableAbs_mixed_mi`
(`RobinCaps/ThinDomain/MixedIntegrable.lean`), whose underlying lemma
`integrableOn_lateralDensity_of_continuousOn_closure_tgi`
(`RobinCaps/ThinDomain/TraceGenIntegrable.lean`) is already general in both caps. -/
theorem continuousBoundaryIntegrableAbs_gen_mgl (m : ℕ) (Cm Cp : Cap m) (L R : ℝ) (hR : 0 < R)
    (hL : (Cm.K + Cp.K) * R < L) :
    ContinuousBoundaryIntegrableAbs_tga m Cm Cp L R hR hL where
  integrableOn u hc :=
    integrableOn_lateralDensity_of_continuousOn_closure_tgi hR hL (hc.pow 2)

/-! ## 2. The concrete trace family, for an arbitrary cap pair -/

/-- The admissibility hypothesis, specialised to a radius below a threshold
`(Cm.K + Cp.K) * R₀ ≤ L`, for an arbitrary pair of admissible caps `Cm Cp : Cap m`. The general-cap
analogue of `hL_of_lt_R₀_ms` (`RobinCaps/ThinDomain/MainSingle.lean`): `Cm.K + Cp.K > 0` now comes
from `Cm.hK`/`Cp.hK` rather than from a single flat-cap hypothesis `hK`. -/
theorem hL_of_lt_R₀_mgl {m : ℕ} {Cm Cp : Cap m} {L R₀ : ℝ} (hR₀L : (Cm.K + Cp.K) * R₀ ≤ L)
    {R : ℝ} (hR₀' : R < R₀) :
    (Cm.K + Cp.K) * R < L := by
  have hKpos : (0 : ℝ) < Cm.K + Cp.K := by linarith [Cm.hK, Cp.hK]
  exact lt_of_lt_of_le (mul_lt_mul_of_pos_left hR₀' hKpos) hR₀L

/-- **The trace family on the thin domain built from an arbitrary pair of admissible caps**, at
threshold `(Cm.K + Cp.K) * R₀ ≤ L`, from the trace datum `traceDataAbs_tga`
(`RobinCaps/ThinDomain/TraceGenAbs.lean`), the bulk-trace interface `bulkTraceInput_bbt`
(`RobinCaps/ThinDomain/BridgeBulkTrace.lean`, already general in both caps), the two abstract
cap-trace-integrability hypotheses `hciM`/`hciP`, and `continuousBoundaryIntegrableAbs_gen_mgl`.
The general-cap analogue of `traceFamilySingle_ms`. -/
def traceFamilyGen2_mgl (m : ℕ) (hm : 1 ≤ m) (Cm Cp : Cap m) (L R₀ : ℝ)
    (hR₀L : (Cm.K + Cp.K) * R₀ ≤ L) (tdM : CapTraceData Cm) (tdP : CapTraceData Cp)
    (hciM : CapTraceIntegrableAbs_tga Cm tdM) (hciP : CapTraceIntegrableAbs_tga Cp tdP) :
    TraceFamily Cm Cp L R₀ :=
  fun R hR hR₀' =>
    traceDataAbs_tga hm hR (hL_of_lt_R₀_mgl hR₀L hR₀') tdM tdP
      (bulkTraceInput_bbt m hm hR (hL_of_lt_R₀_mgl hR₀L hR₀'))
      hciM hciP
      (continuousBoundaryIntegrableAbs_gen_mgl m Cm Cp L R hR (hL_of_lt_R₀_mgl hR₀L hR₀'))

/-- **`traceFamilyGen2_mgl`, unfolded at an arbitrary proof of the admissibility hypothesis**
(any two proofs of `(Cm.K + Cp.K) * R < L` are definitionally equal, by proof irrelevance). The
general-cap analogue of `traceFamilySingle_ms_eq`. -/
theorem traceFamilyGen2_mgl_eq (m : ℕ) (hm : 1 ≤ m) (Cm Cp : Cap m) (L R₀ : ℝ)
    (hR₀L : (Cm.K + Cp.K) * R₀ ≤ L) (tdM : CapTraceData Cm) (tdP : CapTraceData Cp)
    (hciM : CapTraceIntegrableAbs_tga Cm tdM) (hciP : CapTraceIntegrableAbs_tga Cp tdP)
    (R : ℝ) (hR : 0 < R) (hR₀' : R < R₀) (hL : (Cm.K + Cp.K) * R < L) :
    traceFamilyGen2_mgl m hm Cm Cp L R₀ hR₀L tdM tdP hciM hciP R hR hR₀'
      = traceDataAbs_tga hm hR hL tdM tdP (bulkTraceInput_bbt m hm hR hL) hciM hciP
          (continuousBoundaryIntegrableAbs_gen_mgl m Cm Cp L R hR hL) := rfl

/-- **`traceFamilyGen2_mgl` satisfies `TraceSplitGen2_ag2`** (`RobinCaps/ThinDomain/TrialAssemblyGen2.lean`),
at every admissible radius and every admissibility proof. As in `traceSplitMixed_traceFamilySingle_ms`,
`bdCapL_tga`/`bdCapR_tga` unfold to exactly `TraceSplitGen2_ag2`'s right-hand side (`capC_tga m R`
is *literally* `R ^ ((m : ℝ) / 2)`, definitionally), so `traceSplit_tga` applies directly, with no
separate normalisation lemma needed. -/
theorem traceSplitGen2_traceFamilyGen2_mgl (m : ℕ) (hm : 1 ≤ m) (Cm Cp : Cap m) (L R₀ : ℝ)
    (hR₀L : (Cm.K + Cp.K) * R₀ ≤ L) (tdM : CapTraceData Cm) (tdP : CapTraceData Cp)
    (hciM : CapTraceIntegrableAbs_tga Cm tdM) (hciP : CapTraceIntegrableAbs_tga Cp tdP)
    (R : ℝ) (hR : 0 < R) (hR₀' : R < R₀) (hL : (Cm.K + Cp.K) * R < L) :
    TraceSplitGen2_ag2 Cm Cp tdM tdP hR hL
      (traceFamilyGen2_mgl m hm Cm Cp L R₀ hR₀L tdM tdP hciM hciP R hR hR₀') := by
  rw [traceFamilyGen2_mgl_eq m hm Cm Cp L R₀ hR₀L tdM tdP hciM hciP R hR hR₀' hL]
  intro u
  exact traceSplit_tga hm hR hL tdM tdP (bulkTraceInput_bbt m hm hR hL) hciM hciP
    (continuousBoundaryIntegrableAbs_gen_mgl m Cm Cp L R hR hL) u

/-! ## 3. The bridge interface, restated verbatim from `RobinCaps/ThinDomain/BridgeGen2.lean` -/

/-- The conclusion of `RobinCaps/ThinDomain/BridgeGen2.lean`'s `mainTheorem_gen2_bridged_bg3`,
restated here so that the two files can be written in parallel; the coordinator bridges them. -/
def BridgeGen2Input_mgl (m : ℕ) (Cm Cp : Cap m) (L α : ℝ) (hL0 : 0 < L)
    (tdM : CapTraceData Cm) (tdP : CapTraceData Cp) (Cexp : ℝ)
    (hβm : 0 < Cm.beta α) (hβp : 0 < Cp.beta α) : Prop :=
  ∃ R₁ : ℝ, 0 < R₁ ∧ ∀ (R₀ : ℝ) (hR₀ : 0 < R₀) (hR₀1 : R₀ ≤ R₁)
      (gsf : GroundStateFamily_gm m α R₀) (hbd : ∀ R, gsf.bd R = bdR m R)
      (tdf : TraceFamily Cm Cp L R₀)
      (hsplit : ∀ R hR hR₀', ∀ hL, TraceSplitGen2_ag2 Cm Cp tdM tdP hR hL (tdf R hR hR₀'))
      (hexp : ∀ R hR hR₀', ExpW_tw m α R (gsf.gs R hR hR₀') Cexp),
    MainTheorem m Cm Cp L α hL0 hβm hβp gsf.nu' R₀ tdf

/-! ## 4. `thm:main` for an arbitrary pair of admissible caps, general `m ≥ 1` -/

/-- **`thm:main` for an arbitrary pair of admissible caps, general `m ≥ 1`**, with
`ν_R = nuBall m α R = λ₁(B_m(R);α)` explicit, modulo `BridgeGen2Input_mgl` (the companion bridge
file's conclusion, restated), for one concrete trace family.

The radius threshold `R₀` is the minimum of the thresholds produced by
`exists_groundStateFamily_bdR_gsf` (ground-state family on the ball), `expW_sharp_xs` (the sharp
`O(R²)` transverse expansion), the bridge's own `R₁`, and the general admissibility threshold
`L / (Cm.K + Cp.K)`. -/
theorem mainTheorem_general_exists_mgl (m : ℕ) (hm : 1 ≤ m) (Cm Cp : Cap m) (L α : ℝ)
    (hL0 : 0 < L) (hα : 0 < α) (tdM : CapTraceData Cm) (tdP : CapTraceData Cp)
    (hciM : CapTraceIntegrableAbs_tga Cm tdM) (hciP : CapTraceIntegrableAbs_tga Cp tdP)
    (hbridge : ∀ Cexp : ℝ, 0 ≤ Cexp →
      BridgeGen2Input_mgl m Cm Cp L α hL0 tdM tdP Cexp
        (cap_beta_pos_bg2 m hm Cm hα) (cap_beta_pos_bg2 m hm Cp hα)) :
    ∃ R₀ : ℝ, ∃ hR₀ : 0 < R₀, ∃ hR₀L : (Cm.K + Cp.K) * R₀ ≤ L,
      ∃ tdf : TraceFamily Cm Cp L R₀,
      MainTheorem m Cm Cp L α hL0 (cap_beta_pos_bg2 m hm Cm hα) (cap_beta_pos_bg2 m hm Cp hα)
        (nuBall m α) R₀ tdf := by
  obtain ⟨R₀g, hR₀gpos, gsf0, hbd0, hsign0⟩ := exists_groundStateFamily_bdR_gsf m hm α hα
  obtain ⟨Cexp, R₀e, hCexp0, hR₀epos, hR₀ele1, hexpsharp⟩ := expW_sharp_xs m hm α hα
  obtain ⟨R₁, hR₁pos, hbridge'⟩ := hbridge Cexp hCexp0
  have hKpos : (0 : ℝ) < Cm.K + Cp.K := by linarith [Cm.hK, Cp.hK]
  set R₀ : ℝ := min (min R₀g R₀e) (min R₁ (L / (Cm.K + Cp.K))) with hR₀def
  have hR₀pos : 0 < R₀ :=
    lt_min (lt_min hR₀gpos hR₀epos) (lt_min hR₁pos (div_pos hL0 hKpos))
  have hR₀g_le : R₀ ≤ R₀g := le_trans (min_le_left _ _) (min_le_left _ _)
  have hR₀e_le : R₀ ≤ R₀e := le_trans (min_le_left _ _) (min_le_right _ _)
  have hR₁_le : R₀ ≤ R₁ := le_trans (min_le_right _ _) (min_le_left _ _)
  have hR₀_le_div : R₀ ≤ L / (Cm.K + Cp.K) := le_trans (min_le_right _ _) (min_le_right _ _)
  have hR₀L : (Cm.K + Cp.K) * R₀ ≤ L := by
    rw [mul_comm]
    exact (le_div_iff₀ hKpos).1 hR₀_le_div
  set gsf : GroundStateFamily_gm m α R₀ := restrict_mg gsf0 hR₀g_le with hgsfdef
  have hbd : ∀ R, gsf.bd R = bdR m R := hbd0
  set tdf : TraceFamily Cm Cp L R₀ :=
    traceFamilyGen2_mgl m hm Cm Cp L R₀ hR₀L tdM tdP hciM hciP with htdfdef
  have hsplit : ∀ (R : ℝ) (hR : 0 < R) (hR₀' : R < R₀),
      ∀ hL, TraceSplitGen2_ag2 Cm Cp tdM tdP hR hL (tdf R hR hR₀') :=
    fun R hR hR₀' hL =>
      traceSplitGen2_traceFamilyGen2_mgl m hm Cm Cp L R₀ hR₀L tdM tdP hciM hciP R hR hR₀' hL
  have hexp : ∀ (R : ℝ) (hR : 0 < R) (hR₀' : R < R₀), ExpW_tw m α R (gsf.gs R hR hR₀') Cexp := by
    intro R hR hR₀'
    have hRe : R < R₀e := lt_of_lt_of_le hR₀' hR₀e_le
    have hRg : R < R₀g := lt_of_lt_of_le hR₀' hR₀g_le
    have hbdR : gsf.bd R = bdR m R := hbd R
    set gs' : TransverseGroundState m α R (bdR m R) := transportBd_bg hbdR (gsf.gs R hR hR₀')
      with hgs'def
    have hgspsi : gs'.psi = (gsf.gs R hR hR₀').psi := transportBd_bg_psi hbdR (gsf.gs R hR hR₀')
    have hsign : 0 ≤ ∫ z in ball (0 : EuclideanSpace ℝ (Fin m)) R, gs'.psi.toFun z := by
      rw [hgspsi]; exact hsign0 R hR hRg
    exact expW_tw_of_transportBd_mg hbdR (gsf.gs R hR hR₀') (hexpsharp R hR hRe gs' hsign)
  exact ⟨R₀, hR₀pos, hR₀L, tdf,
    mainTheorem_congr_nu_nb (fun R hR hR₀' => gsf.nu'_eq_lam1_nb hbd R hR hR₀')
      (hbridge' R₀ hR₀pos hR₁_le gsf hbd tdf hsplit hexp)⟩

/-- **`thm:main` for an arbitrary pair of admissible caps, general `m ≥ 1`**, with
`ν_R = λ₁(B_m(R);α)` explicit: trace families exist, and the asymptotics hold for **every**
trace family. Uses `mainTheorem_of_any_traceFamily_tu` together with `c1Dense_tuf`
(`RobinCaps/ThinDomain/TraceUniqueFinal.lean`), exactly as `mainTheorem_single_nb` does. -/
theorem mainTheorem_general_nb_mgl (m : ℕ) (hm : 1 ≤ m) (Cm Cp : Cap m) (L α : ℝ)
    (hL0 : 0 < L) (hα : 0 < α) (tdM : CapTraceData Cm) (tdP : CapTraceData Cp)
    (hciM : CapTraceIntegrableAbs_tga Cm tdM) (hciP : CapTraceIntegrableAbs_tga Cp tdP)
    (hbridge : ∀ Cexp : ℝ, 0 ≤ Cexp →
      BridgeGen2Input_mgl m Cm Cp L α hL0 tdM tdP Cexp
        (cap_beta_pos_bg2 m hm Cm hα) (cap_beta_pos_bg2 m hm Cp hα)) :
    ∃ R₀ : ℝ, ∃ hR₀ : 0 < R₀, ∃ hR₀L : (Cm.K + Cp.K) * R₀ ≤ L,
      Nonempty (TraceFamily Cm Cp L R₀) ∧
      ∀ tdf : TraceFamily Cm Cp L R₀,
        MainTheorem m Cm Cp L α hL0 (cap_beta_pos_bg2 m hm Cm hα) (cap_beta_pos_bg2 m hm Cp hα)
          (nuBall m α) R₀ tdf := by
  obtain ⟨R₀, hR₀, hR₀L, tdf₀, hmain⟩ :=
    mainTheorem_general_exists_mgl m hm Cm Cp L α hL0 hα tdM tdP hciM hciP hbridge
  exact ⟨R₀, hR₀, hR₀L, ⟨tdf₀⟩, fun tdf =>
    mainTheorem_of_any_traceFamily_tu (fun R hR hL => c1Dense_tuf hR hL) tdf₀ tdf hmain⟩

end RobinCaps.ThinDomain

end
