import RobinCaps.Cap.PoincareGen
import RobinCaps.Cap.CapDensity
import RobinCaps.Cap.EntranceL2Gen
import RobinCaps.ThinDomain.BridgeGen2
import RobinCaps.ThinDomain.MainGeneral
import RobinCaps.ThinDomain.MixedIntegrable
import RobinCaps.Cap.TraceDataFlatDerived

/-!
# The fully general `thm:main`, unconditional on the per-cap analytic inputs

This file removes the last three "interface" hypotheses left open by
`RobinCaps/ThinDomain/MainGeneral.lean` (`BridgeGen2Input_mgl`) and
`RobinCaps/ThinDomain/BridgeGen2.lean` (which itself needs `CapEntranceL2`/`CapPoincare` for both
caps): every admissible cap `C : Cap m`, `m ≥ 1`, satisfies both `CapEntranceL2` and `CapPoincare`
unconditionally, by `RobinCaps.Cap.capEntranceL2_gen_eg2`/`RobinCaps.Cap.exists_c1_h1_close_cap_cdn`
(density) and `RobinCaps.Cap.capPoincare_gen_pgn`.  Combining these with
`RobinCaps.ThinDomain.mainTheorem_gen2_bridged_bg3` discharges `BridgeGen2Input_mgl` for *every*
`Cexp ≥ 0`, closing the last hypothesis of `RobinCaps.ThinDomain.mainTheorem_general_nb_mgl`.

## Contents

* `capEntranceL2_gen_mgc` — `CapEntranceL2` for an arbitrary admissible cap, unconditional: plugs
  the density theorem `exists_c1_h1_close_cap_cdn` (`RobinCaps/Cap/CapDensity.lean`) into
  `capEntranceL2_gen_eg2` (`RobinCaps/Cap/EntranceL2Gen.lean`).
* `bridgeGen2Input_mgc` — `BridgeGen2Input_mgl`, for an arbitrary pair of admissible caps and every
  `Cexp ≥ 0`, from `mainTheorem_gen2_bridged_bg3` (`RobinCaps/ThinDomain/BridgeGen2.lean`), fed by
  `capEntranceL2_gen_mgc` and `capPoincare_gen_pgn` (`RobinCaps/Cap/PoincareGen.lean`) for both
  caps.  `BridgeGen2Input_mgl` and the conclusion `BridgeGen2_bg3` of `mainTheorem_gen2_bridged_bg3`
  are *verbatim* the same `Prop` (both `def`s unfold to the identical statement), so no bridging
  beyond `exact` is needed.
* `mainTheorem_general_of_traceData_mgc` — `thm:main` for an arbitrary pair of admissible caps,
  general `m ≥ 1`, with the per-cap trace data `tdM`/`tdP` (and their integrability) as the *only*
  hypotheses: `mainTheorem_general_nb_mgl` (`RobinCaps/ThinDomain/MainGeneral.lean`) fed by
  `bridgeGen2Input_mgc`.
* Two consistency corollaries, instantiating `mainTheorem_general_of_traceData_mgc` at concrete
  cap pairs (both hemispheres; flat/hemisphere) with their recorded trace data.

No `sorry`, `admit`, `axiom` or `native_decide` occurs in this file.
-/

namespace RobinCaps.ThinDomain

open RobinCaps.Cap RobinCaps.ThinDomain

/-! ## 1. `CapEntranceL2`, unconditional -/

/-- **`CapEntranceL2` for an arbitrary admissible cap, unconditional.**  The density hypothesis
`hdense` of `RobinCaps.Cap.capEntranceL2_gen_eg2` is exactly
`RobinCaps.Cap.exists_c1_h1_close_cap_cdn` (`RobinCaps/Cap/CapDensity.lean`, where `η` is
implicit). -/
theorem capEntranceL2_gen_mgc (m : ℕ) (hm : 1 ≤ m) (C : Cap m) : ∃ C₁ : ℝ, CapEntranceL2 C C₁ :=
  RobinCaps.Cap.capEntranceL2_gen_eg2 m hm C
    (fun u η hη => RobinCaps.Sobolev.exists_c1_h1_close_cap_cdn C u hη)

/-! ## 2. `BridgeGen2Input_mgl`, unconditional -/

/-- **`BridgeGen2Input_mgl`, for an arbitrary pair of admissible caps and every `Cexp ≥ 0`,
unconditional.**  Feeds `capEntranceL2_gen_mgc` and `capPoincare_gen_pgn`
(`RobinCaps/Cap/PoincareGen.lean`), for both caps, into `mainTheorem_gen2_bridged_bg3`
(`RobinCaps/ThinDomain/BridgeGen2.lean`).  `BridgeGen2Input_mgl`
(`RobinCaps/ThinDomain/MainGeneral.lean`) and `BridgeGen2_bg3`
(`RobinCaps/ThinDomain/BridgeGen2.lean`, the conclusion of `mainTheorem_gen2_bridged_bg3`) are
verbatim the same `Prop` up to the name of the `def`, so `exact` unfolds both without any further
bridging. -/
theorem bridgeGen2Input_mgc (m : ℕ) (hm : 1 ≤ m) (Cm Cp : Cap m) (L α : ℝ) (hL0 : 0 < L)
    (hα : 0 < α) (tdM : CapTraceData Cm) (tdP : CapTraceData Cp) (Cexp : ℝ) (hCexp : 0 ≤ Cexp) :
    BridgeGen2Input_mgl m Cm Cp L α hL0 tdM tdP Cexp
      (cap_beta_pos_bg2 m hm Cm hα) (cap_beta_pos_bg2 m hm Cp hα) := by
  obtain ⟨C₁, henM⟩ := capEntranceL2_gen_mgc m hm Cm
  obtain ⟨CPm, hPM⟩ := RobinCaps.Cap.capPoincare_gen_pgn m hm Cm
  obtain ⟨C₁', henP⟩ := capEntranceL2_gen_mgc m hm Cp
  obtain ⟨CPp, hPP⟩ := RobinCaps.Cap.capPoincare_gen_pgn m hm Cp
  exact mainTheorem_gen2_bridged_bg3 m hm Cm Cp L α hL0 hα tdM tdP hCexp henM hPM henP hPP

/-! ## 3. `thm:main` for an arbitrary pair of admissible caps, unconditional on `BridgeGen2Input_mgl` -/

/-- **`thm:main` for an arbitrary pair of admissible caps, general `m ≥ 1`, with only the per-cap
trace data as hypotheses.**  Everything else (`CapEntranceL2`, `CapPoincare` for both caps, hence
`BridgeGen2Input_mgl` for every `Cexp ≥ 0`) is now unconditional, by `bridgeGen2Input_mgc`. -/
theorem mainTheorem_general_of_traceData_mgc (m : ℕ) (hm : 1 ≤ m) (Cm Cp : Cap m) (L α : ℝ)
    (hL0 : 0 < L) (hα : 0 < α) (tdM : CapTraceData Cm) (tdP : CapTraceData Cp)
    (hciM : CapTraceIntegrableAbs_tga Cm tdM) (hciP : CapTraceIntegrableAbs_tga Cp tdP) :
    ∃ R₀ : ℝ, ∃ hR₀ : 0 < R₀, ∃ hR₀L : (Cm.K + Cp.K) * R₀ ≤ L,
      Nonempty (TraceFamily Cm Cp L R₀) ∧
      ∀ tdf : TraceFamily Cm Cp L R₀,
        MainTheorem m Cm Cp L α hL0 (cap_beta_pos_bg2 m hm Cm hα) (cap_beta_pos_bg2 m hm Cp hα)
          (nuBall m α) R₀ tdf :=
  mainTheorem_general_nb_mgl m hm Cm Cp L α hL0 hα tdM tdP hciM hciP
    (fun Cexp hCexp => bridgeGen2Input_mgc m hm Cm Cp L α hL0 hα tdM tdP Cexp hCexp)

/-! ## 4. Consistency corollaries -/

/-- **Sanity check 1**: `mainTheorem_general_of_traceData_mgc` at two hemispherical caps,
with the recorded hemisphere trace data (`RobinCaps/Cap/TraceDataHemi.lean`) and its integrability
(`RobinCaps/ThinDomain/MixedIntegrable.lean`). -/
theorem mainTheorem_general_hemi_hemi_mgc (m : ℕ) (hm : 1 ≤ m) (L α : ℝ) (hL0 : 0 < L)
    (hα : 0 < α) :
    ∃ R₀ : ℝ, ∃ hR₀ : 0 < R₀,
      ∃ hR₀L : ((Cap.hemisphere m).K + (Cap.hemisphere m).K) * R₀ ≤ L,
      Nonempty (TraceFamily (Cap.hemisphere m) (Cap.hemisphere m) L R₀) ∧
      ∀ tdf : TraceFamily (Cap.hemisphere m) (Cap.hemisphere m) L R₀,
        MainTheorem m (Cap.hemisphere m) (Cap.hemisphere m) L α hL0
          (cap_beta_pos_bg2 m hm (Cap.hemisphere m) hα) (cap_beta_pos_bg2 m hm (Cap.hemisphere m) hα)
          (nuBall m α) R₀ tdf :=
  mainTheorem_general_of_traceData_mgc m hm (Cap.hemisphere m) (Cap.hemisphere m) L α hL0 hα
    (capTraceDataHemi_th m hm) (capTraceDataHemi_th m hm)
    (capTraceIntegrableAbs_hemi_mi m hm) (capTraceIntegrableAbs_hemi_mi m hm)

/-- **Sanity check 2**: `mainTheorem_general_of_traceData_mgc` at a flat/hemisphere pair,
with the recorded flat-cap trace data (`RobinCaps/Cap/TraceDataFlat.lean`) and its integrability
(`RobinCaps/Cap/TraceDataFlatDerived.lean`), and the recorded hemisphere trace data. -/
theorem mainTheorem_general_flat_hemi_mgc (m : ℕ) (hm : 1 ≤ m) (K : ℝ) (hK : 0 < K) (L α : ℝ)
    (hL0 : 0 < L) (hα : 0 < α) :
    ∃ R₀ : ℝ, ∃ hR₀ : 0 < R₀,
      ∃ hR₀L : ((Cap.flat m K hK).K + (Cap.hemisphere m).K) * R₀ ≤ L,
      Nonempty (TraceFamily (Cap.flat m K hK) (Cap.hemisphere m) L R₀) ∧
      ∀ tdf : TraceFamily (Cap.flat m K hK) (Cap.hemisphere m) L R₀,
        MainTheorem m (Cap.flat m K hK) (Cap.hemisphere m) L α hL0
          (cap_beta_pos_bg2 m hm (Cap.flat m K hK) hα) (cap_beta_pos_bg2 m hm (Cap.hemisphere m) hα)
          (nuBall m α) R₀ tdf :=
  mainTheorem_general_of_traceData_mgc m hm (Cap.flat m K hK) (Cap.hemisphere m) L α hL0 hα
    (capTraceDataFlat_tf m hm K hK) (capTraceDataHemi_th m hm)
    (capTraceIntegrableAbs_flat_tfd m hm K hK) (capTraceIntegrableAbs_hemi_mi m hm)

end RobinCaps.ThinDomain
