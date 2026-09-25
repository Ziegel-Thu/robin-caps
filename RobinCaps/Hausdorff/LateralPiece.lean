import RobinCaps.Hausdorff.LateralChart
import RobinCaps.Hausdorff.GramMeasurable
import RobinCaps.Hausdorff.AreaLintegral
import RobinCaps.Hausdorff.LinearImage

/-!
# The lateral-piece integral area formula (wave 12, Hausdorff)

This file proves the integral area formula for a "piece" of the lateral chart
`latChart_lch n r : ℝ^{n+1} → ℝ^{n+2}` of `RobinCaps.Hausdorff.LateralChart`, over a parameter
set `S = latPieceSet_lpc n J A = {w | w 0 ∈ J ∧ tailE_lch n w ∈ A}` cut out by an axial-coordinate
constraint `w 0 ∈ J` and a transverse constraint `tailE_lch n w ∈ A`.

The main theorem, `latPiece_lintegral_lpc`, states that for `r : ℝ → ℝ` positive and
differentiable on `J`, `A ⊆ ball 0 1` measurable, and `h : ℝ^{n+2} → ℝ≥0∞` measurable,

`∫⁻ y in latChart_lch n r '' S, h y ∂μH[n+1]`
`  = hConst (n+1) * ∫⁻ x in J, ofReal (√(1 + (r'x)²) * (r x)^n) *`
`      ∫⁻ ω in {ω ∈ sphere 0 1 | ω ∈ hemi n '' A}, h (toEuclid (n+1) (x, r x • ω)) ∂volume.toSphere`

(the outer `∫⁻ x in J` against Lebesgue measure on `ℝ`), given the hemisphere-chart interface
fact `HemiToSphereProp n`.

## Architecture

* `latPieceSet_lpc` — the parameter set `S`, and `latPieceSet_eq_image_lpc` identifies it as
  `toEuclid n '' (J ×ˢ A)` under the identification `toEuclid n : CapSpace n ≃ ℝ^{n+1}` of
  `RobinCaps.Domain.CapsuleThin` (which is exactly `consE_lch n`, by
  `consE_lch_eq_toEuclid_lch`), so `measurableSet_latPieceSet_lpc` is immediate from the
  continuity of the coordinate maps `w ↦ w 0` and `tailE_lch n`.
* `continuous_toEuclid_lpc` — `toEuclid m` is (jointly) continuous, via
  `consE_eq_add_lch`/`eZero_lch`/`iotaSucc_lch` (already continuous linear maps in
  `LateralChart.lean`).
* `hemiDensity_continuousOn_lpc` — `hemiDensity n` is continuous on `A ⊆ ball 0 1` (a local
  transcription of the corresponding `have` inside `AreaLintegral.hemiToSphereLintegral_alt`,
  needed again here for a.e.-measurability in the Tonelli step below).
* `latDeriv_props_lpc` — packages `latChart_hasFDerivAt_lch` (Fréchet derivative, Gram
  determinant, injectivity) at every point of `S`, using `hJ` to supply `0 < r (w 0)` and the
  derivative of `r` at `w 0`, and `A ⊆ ball 0 1` to supply `‖tailE_lch n w‖ < 1`.
* `sqrt_latGramDet_lpc` — the algebraic identity
  `ofReal (√((1+r'²) ρ^{2n} / (1-‖z‖²))) = ofReal (√(1+r'²) ρ^n) * hemiDensity n z`
  splitting the area-formula density into the "axial" factor of the final statement and
  `hemiDensity n z` (literally, by the *definition* of `hemiDensity`), via `Real.sqrt_div'`,
  `Real.sqrt_mul`, `Real.sqrt_sq` and `ENNReal.ofReal_mul`.
* `latPiece_lintegral_lpc` — the main theorem. The proof chains:
  1. `areaLintegralInj_gam (n+1) (n+2)` (the unconditional area formula, integral form) applied
     to `S`, `latChart_lch n r`, and the derivative field of `latDeriv_props_lpc`, turning the
     goal into an integral over `S` against `μH[n+1]`;
  2. `hausdorffVolume_hlin (n+1)` (`μH[n+1] = hConst (n+1) • volume`) pulls out the constant
     `hConst (n+1)`, turning the remaining integral into one against Lebesgue measure on
     `ℝ^{n+1}`;
  3. `measurePreserving_toEuclid n` (already proved in `RobinCaps.Domain.CapsuleThin` for
     exactly this coordinate splitting) together with `latPieceSet_eq_image_lpc` transports the
     integral over `S ⊆ ℝ^{n+1}` to one over `J ×ˢ A ⊆ ℝ × ℝ^n` against the product measure
     `volume.prod volume` (`Measure.volume_eq_prod`, an equality of measures that holds *by
     definition*), via `MeasurePreserving.setLIntegral_comp_emb`;
  4. the *density* factor `√(gramDet)` is rewritten pointwise on `J ×ˢ A`
     (`setLIntegral_congr_fun`, no measurability needed) via `latDeriv_props_lpc` and
     `sqrt_latGramDet_lpc` into the explicit axial-times-`hemiDensity` product, leaving the
     `h`-factor as `h (latChart_lch n r (toEuclid n p))` (not yet unfolded — this keeps the
     a.e.-measurability argument of step 5 as simple as possible);
  5. Tonelli (`MeasureTheory.setLIntegral_prod`) splits the product integral into iterated
     integrals, using a.e.-measurability of the three factors: continuity of
     `latChart_lch n r ∘ toEuclid n` on `J ×ˢ A` (from the `HasFDerivWithinAt` of step 1),
     measurability of `deriv r` (`measurable_deriv`) and continuity of `r` on `J` (from `hJ`),
     and `hemiDensity_continuousOn_lpc`;
  6. for each fixed `x ∈ J`, the axial factor is pulled out of the inner (`z`) integral
     (`lintegral_const_mul''`), and `h (latChart_lch n r (toEuclid n (x, z)))` is unfolded to
     `h (toEuclid (n+1) (x, r x • hemi n z))` via `latChart_mem_lch`;
  7. `hemiToSphereLintegral_alt n hV` converts the remaining `z`-integral against
     `hemiDensity n` into the sphere integral against `volume.toSphere` of the main statement.

No `sorry`. The only nontrivial *hypothesis* used is `hV : HemiToSphereProp n`
(step 7 above), exactly as anticipated by the task.
-/

noncomputable section

open MeasureTheory Set Metric Function
open scoped ENNReal

namespace RobinCaps.Hausdorff

open RobinCaps.Domain

variable {n : ℕ}

/-! ## The parameter set `S` -/

/-- The parameter set of the lateral-piece chart: axial coordinate in `J`, transverse
coordinate (after `tailE_lch`) in `A`. -/
def latPieceSet_lpc (n : ℕ) (J : Set ℝ) (A : Set (Esp_lch n)) : Set (Esp_lch (n + 1)) :=
  {w : Esp_lch (n + 1) | w 0 ∈ J ∧ tailE_lch n w ∈ A}

theorem mem_latPieceSet_lpc {n : ℕ} {J : Set ℝ} {A : Set (Esp_lch n)} {w : Esp_lch (n + 1)} :
    w ∈ latPieceSet_lpc n J A ↔ w 0 ∈ J ∧ tailE_lch n w ∈ A := Iff.rfl

/-- `toEuclid m` (from `RobinCaps.Domain.CapsuleThin`) is (jointly) continuous: it equals
`consE_lch m p.1 p.2 = eZero_lch m p.1 + iotaSucc_lch m p.2`, a sum of two continuous linear
maps precomposed with the continuous projections. -/
theorem continuous_toEuclid_lpc (m : ℕ) : Continuous (toEuclid m) := by
  have heq : toEuclid m = fun p : CapSpace m => eZero_lch m p.1 + iotaSucc_lch m p.2 := by
    funext p
    rw [← consE_lch_eq_toEuclid_lch, consE_eq_add_lch]
  rw [heq]
  exact ((eZero_lch m).continuous.comp continuous_fst).add
    ((iotaSucc_lch m).continuous.comp continuous_snd)

/-- **`S` is exactly the image of `J ×ˢ A` under `toEuclid n`.** -/
theorem latPieceSet_eq_image_lpc (n : ℕ) (J : Set ℝ) (A : Set (Esp_lch n)) :
    latPieceSet_lpc n J A = toEuclid n '' (J ×ˢ A) := by
  ext w
  constructor
  · rintro ⟨hw0, hwtail⟩
    exact ⟨(w 0, tailE_lch n w), ⟨hw0, hwtail⟩, by
      rw [← consE_lch_eq_toEuclid_lch]; exact consE_tailE_lch n w⟩
  · rintro ⟨⟨x, z⟩, ⟨hx, hz⟩, rfl⟩
    refine ⟨?_, ?_⟩
    · rw [← consE_lch_eq_toEuclid_lch, consE_apply_zero_lch]; exact hx
    · rw [← consE_lch_eq_toEuclid_lch, tailE_consE_lch]; exact hz

/-- **`S` is measurable**, given `J` and `A` measurable. -/
theorem measurableSet_latPieceSet_lpc {n : ℕ} {J : Set ℝ} {A : Set (Esp_lch n)}
    (hJm : MeasurableSet J) (hAm : MeasurableSet A) :
    MeasurableSet (latPieceSet_lpc n J A) := by
  have h0 : Measurable (fun w : Esp_lch (n + 1) => w 0) := by
    have heq : (fun w : Esp_lch (n + 1) => w 0) = ⇑(proj0CLM_lch n) :=
      funext fun w => (proj0_apply_lch n w).symm
    rw [heq]; exact (proj0CLM_lch n).continuous.measurable
  have h1 : Measurable (tailE_lch n) := by
    have heq : tailE_lch n = ⇑(tailCLM_lch n) := funext fun w => (tailCLM_eq_tailE_lch n w).symm
    rw [heq]; exact (tailCLM_lch n).continuous.measurable
  exact (h0 hJm).inter (h1 hAm)

/-! ## `hemiDensity` is continuous on `A ⊆ ball 0 1` -/

/-- The chart density `hemiDensity n` is continuous on any `A ⊆ ball 0 1`. -/
theorem hemiDensity_continuousOn_lpc {n : ℕ} {A : Set (Esp_lch n)} (hAsub : A ⊆ ball 0 1) :
    ContinuousOn (hemiDensity n) A := by
  have h1 : ContinuousOn (fun z : Esp_lch n => (1 : ℝ) - ‖z‖ ^ 2) A :=
    (continuous_const.sub (continuous_norm.pow 2)).continuousOn
  have h2 : ContinuousOn (fun z : Esp_lch n => Real.sqrt (1 - ‖z‖ ^ 2)) A :=
    Real.continuous_sqrt.comp_continuousOn h1
  have h3 : ∀ z ∈ A, Real.sqrt (1 - ‖z‖ ^ 2) ≠ 0 := by
    intro z hz
    have hz1 : ‖z‖ < 1 := mem_ball_zero_iff.mp (hAsub hz)
    exact (Real.sqrt_pos.mpr (by nlinarith [norm_nonneg z])).ne'
  have h4 : ContinuousOn (fun z : Esp_lch n => 1 / Real.sqrt (1 - ‖z‖ ^ 2)) A :=
    continuousOn_const.div h2 h3
  exact ENNReal.continuous_ofReal.comp_continuousOn h4

/-! ## The derivative field of the chart, on `S` -/

/-- At every `w ∈ S`, the lateral chart has a Fréchet derivative within `S`, with the stated
Gram determinant, injective. -/
theorem latDeriv_props_lpc {n : ℕ} {r : ℝ → ℝ} {J : Set ℝ} {A : Set (Esp_lch n)}
    (hJ : ∀ x ∈ J, 0 < r x ∧ HasDerivAt r (deriv r x) x) (hAsub : A ⊆ ball 0 1)
    {w : Esp_lch (n + 1)} (hw : w ∈ latPieceSet_lpc n J A) :
    HasFDerivWithinAt (latChart_lch n r) (latDeriv_lch n (deriv r (w 0)) r w)
        (latPieceSet_lpc n J A) w ∧
      gramDet (latDeriv_lch n (deriv r (w 0)) r w)
          = (1 + deriv r (w 0) ^ 2) * r (w 0) ^ (2 * n) / (1 - ‖tailE_lch n w‖ ^ 2) ∧
      Function.Injective (latDeriv_lch n (deriv r (w 0)) r w) := by
  obtain ⟨hw0, hwA⟩ := hw
  have hr0 : 0 < r (w 0) := (hJ (w 0) hw0).1
  have hrD : HasDerivAt r (deriv r (w 0)) (w 0) := (hJ (w 0) hw0).2
  have hz : ‖tailE_lch n w‖ < 1 := mem_ball_zero_iff.mp (hAsub hwA)
  refine ⟨(hasFDerivAt_latChart_lch hrD hz).hasFDerivWithinAt, ?_, ?_⟩
  · rw [latDeriv_eq_Dlat_lch]; exact gramDet_Dlat_lch hz
  · rw [latDeriv_eq_Dlat_lch]; exact injective_Dlat_lch hr0

/-! ## Algebraic simplification of `√(gramDet)` -/

/-- **The area-formula density of the lateral chart splits** into the axial factor
`√(1+r'²) ρ^n` of the final theorem, and `hemiDensity n z` (literally, by definition of
`hemiDensity`). -/
theorem sqrt_latGramDet_lpc {n : ℕ} {r' ρ : ℝ} {z : Esp_lch n} (hρ : 0 ≤ ρ) (hz : ‖z‖ < 1) :
    ENNReal.ofReal (Real.sqrt ((1 + r' ^ 2) * ρ ^ (2 * n) / (1 - ‖z‖ ^ 2)))
      = ENNReal.ofReal (Real.sqrt (1 + r' ^ 2) * ρ ^ n) * hemiDensity n z := by
  have hy : (0 : ℝ) ≤ 1 - ‖z‖ ^ 2 := by nlinarith [norm_nonneg z]
  have hx : (0 : ℝ) ≤ 1 + r' ^ 2 := by positivity
  have hpow : ρ ^ (2 * n) = (ρ ^ n) ^ 2 := by rw [two_mul, pow_add, sq]
  have hρn : (0 : ℝ) ≤ ρ ^ n := pow_nonneg hρ n
  have hstep : Real.sqrt ((1 + r' ^ 2) * ρ ^ (2 * n) / (1 - ‖z‖ ^ 2))
      = Real.sqrt (1 + r' ^ 2) * ρ ^ n * (1 / Real.sqrt (1 - ‖z‖ ^ 2)) := by
    rw [Real.sqrt_div' _ hy, Real.sqrt_mul hx, hpow, Real.sqrt_sq hρn, div_eq_mul_one_div]
  rw [hstep, ENNReal.ofReal_mul (by positivity)]
  rfl

/-! ## The main theorem -/

/-- **The integral area formula for a lateral-chart piece.** -/
theorem latPiece_lintegral_lpc {n : ℕ} (r : ℝ → ℝ) {J : Set ℝ} (hJm : MeasurableSet J)
    {A : Set (Esp_lch n)} (hAm : MeasurableSet A) (hAsub : A ⊆ ball 0 1)
    (hJ : ∀ x ∈ J, 0 < r x ∧ HasDerivAt r (deriv r x) x) (hV : HemiToSphereProp n)
    (h : Esp_lch (n + 2) → ℝ≥0∞) (hMeasurable : Measurable h) :
    ∫⁻ y in latChart_lch n r '' latPieceSet_lpc n J A, h y
        ∂(Measure.hausdorffMeasure ((n : ℝ) + 1) : Measure (Esp_lch (n + 2)))
      = hConst (n + 1) * ∫⁻ x in J, ENNReal.ofReal (Real.sqrt (1 + deriv r x ^ 2) * r x ^ n) *
          ∫⁻ ω in {ω : sphere (0 : Esp_lch (n + 1)) 1 | (ω : Esp_lch (n + 1)) ∈ hemi n '' A},
            h (toEuclid (n + 1) (x, r x • (ω : Esp_lch (n + 1)))) ∂(volume.toSphere) := by
  classical
  set S := latPieceSet_lpc n J A with hS_def
  have hSmeas : MeasurableSet S := measurableSet_latPieceSet_lpc hJm hAm
  -- The derivative field on `S`.
  set F' : Esp_lch (n + 1) → Esp_lch (n + 1) →L[ℝ] Esp_lch (n + 2) :=
    fun w => latDeriv_lch n (deriv r (w 0)) r w with hF'_def
  have hF'props : ∀ w ∈ S, HasFDerivWithinAt (latChart_lch n r) (F' w) S w ∧
      gramDet (F' w) = (1 + deriv r (w 0) ^ 2) * r (w 0) ^ (2 * n) / (1 - ‖tailE_lch n w‖ ^ 2) ∧
      Function.Injective (F' w) :=
    fun w hw => latDeriv_props_lpc hJ hAsub hw
  have hSsub : S ⊆ {w : Esp_lch (n + 1) | 0 < r (w 0) ∧ ‖tailE_lch n w‖ < 1} := by
    rintro w ⟨hw0, hwA⟩
    exact ⟨(hJ (w 0) hw0).1, mem_ball_zero_iff.mp (hAsub hwA)⟩
  have hFinj : Set.InjOn (latChart_lch n r) S := latChart_injOn_lch.mono hSsub
  -- Step 1: the unconditional integral area formula.
  have key1 : ∫⁻ y in latChart_lch n r '' S, h y
        ∂(Measure.hausdorffMeasure ((n : ℝ) + 1) : Measure (Esp_lch (n + 2)))
      = ∫⁻ w in S, h (latChart_lch n r w) * ENNReal.ofReal (Real.sqrt (gramDet (F' w)))
          ∂(Measure.hausdorffMeasure ((n : ℝ) + 1) : Measure (Esp_lch (n + 1))) := by
    have hcast : ((n : ℝ) + 1) = ((n + 1 : ℕ) : ℝ) := by push_cast; ring
    rw [hcast]
    exact areaLintegralInj_gam (n + 1) (n + 2) S (latChart_lch n r) F' hSmeas
      (fun w hw => (hF'props w hw).1) hFinj (fun w hw => (hF'props w hw).2.2) h hMeasurable
  -- Step 2: `μH[n+1] = hConst (n+1) • volume`.
  obtain ⟨heqvol, -, -⟩ := hausdorffVolume_hlin (n + 1)
  have key2 : ∫⁻ w in S, h (latChart_lch n r w) * ENNReal.ofReal (Real.sqrt (gramDet (F' w)))
        ∂(Measure.hausdorffMeasure ((n : ℝ) + 1) : Measure (Esp_lch (n + 1)))
      = hConst (n + 1) *
        ∫⁻ w in S, h (latChart_lch n r w) * ENNReal.ofReal (Real.sqrt (gramDet (F' w)))
          ∂(volume : Measure (Esp_lch (n + 1))) := by
    have hcast : ((n : ℝ) + 1) = ((n + 1 : ℕ) : ℝ) := by push_cast; ring
    rw [hcast, heqvol, MeasureTheory.setLIntegral_smul_measure, smul_eq_mul]
  -- Step 3: transport along `toEuclid n`, from `S` to `J ×ˢ A`.
  have hMapsTo : Set.MapsTo (toEuclid n) (J ×ˢ A) S := by
    rintro ⟨x, z⟩ ⟨hx, hz⟩
    rw [hS_def, latPieceSet_eq_image_lpc]
    exact ⟨(x, z), ⟨hx, hz⟩, rfl⟩
  have hEmb : MeasurableEmbedding (toEuclid n) :=
    (capSpaceMeasurableEquiv n).measurableEmbedding
  have hMP : MeasurePreserving (toEuclid n)
      (volume : Measure (CapSpace n)) (volume : Measure (Esp_lch (n + 1))) :=
    measurePreserving_toEuclid n
  have key3 : ∫⁻ w in S, h (latChart_lch n r w) * ENNReal.ofReal (Real.sqrt (gramDet (F' w)))
        ∂(volume : Measure (Esp_lch (n + 1)))
      = ∫⁻ p in J ×ˢ A,
          h (latChart_lch n r (toEuclid n p)) *
            ENNReal.ofReal (Real.sqrt (gramDet (F' (toEuclid n p))))
        ∂(volume : Measure (CapSpace n)) := by
    have himg : toEuclid n '' (J ×ˢ A) = S := (latPieceSet_eq_image_lpc n J A).symm
    rw [← himg]
    exact (hMP.setLIntegral_comp_emb hEmb
      (fun w => h (latChart_lch n r w) * ENNReal.ofReal (Real.sqrt (gramDet (F' w))))
      (J ×ˢ A)).symm
  -- Step 4: rewrite the *density* factor pointwise on `J ×ˢ A`.
  have hpointwise : ∀ p ∈ J ×ˢ A,
      h (latChart_lch n r (toEuclid n p)) *
          ENNReal.ofReal (Real.sqrt (gramDet (F' (toEuclid n p))))
        = h (latChart_lch n r (toEuclid n p)) *
            ENNReal.ofReal (Real.sqrt (1 + deriv r p.1 ^ 2) * r p.1 ^ n) * hemiDensity n p.2 := by
    rintro ⟨x, z⟩ ⟨hx, hz⟩
    have hz1 : ‖z‖ < 1 := mem_ball_zero_iff.mp (hAsub hz)
    have hwmemS : toEuclid n (x, z) ∈ S := hMapsTo ⟨hx, hz⟩
    have hw0 : (toEuclid n (x, z)) 0 = x := by
      rw [← consE_lch_eq_toEuclid_lch]; exact consE_apply_zero_lch n x z
    have hwtail : tailE_lch n (toEuclid n (x, z)) = z := by
      rw [← consE_lch_eq_toEuclid_lch]; exact tailE_consE_lch n x z
    have hgram : gramDet (F' (toEuclid n (x, z)))
        = (1 + deriv r x ^ 2) * r x ^ (2 * n) / (1 - ‖z‖ ^ 2) := by
      have hthis := (hF'props (toEuclid n (x, z)) hwmemS).2.1
      rwa [hw0, hwtail] at hthis
    rw [hgram, sqrt_latGramDet_lpc (hJ x hx).1.le hz1]
    ring
  have key4 : ∫⁻ p in J ×ˢ A,
        h (latChart_lch n r (toEuclid n p)) *
          ENNReal.ofReal (Real.sqrt (gramDet (F' (toEuclid n p))))
        ∂(volume : Measure (CapSpace n))
      = ∫⁻ p in J ×ˢ A,
          h (latChart_lch n r (toEuclid n p)) *
              ENNReal.ofReal (Real.sqrt (1 + deriv r p.1 ^ 2) * r p.1 ^ n) * hemiDensity n p.2
        ∂(volume : Measure (CapSpace n)) :=
    setLIntegral_congr_fun (hJm.prod hAm) hpointwise
  -- Step 5: Tonelli, splitting the product integral.
  have hrContOn : ContinuousOn r J := fun x hx => ((hJ x hx).2.continuousAt).continuousWithinAt
  have hSContOn : ContinuousOn (latChart_lch n r) S :=
    fun w hw => (hF'props w hw).1.continuousWithinAt
  have hΨcont : ContinuousOn (fun p : CapSpace n => latChart_lch n r (toEuclid n p)) (J ×ˢ A) :=
    hSContOn.comp (continuous_toEuclid_lpc n).continuousOn hMapsTo
  have hAE_hΨ : AEMeasurable (fun p : CapSpace n => h (latChart_lch n r (toEuclid n p)))
      ((volume : Measure (CapSpace n)).restrict (J ×ˢ A)) :=
    Measurable.comp_aemeasurable hMeasurable (hΨcont.aemeasurable (hJm.prod hAm))
  have hCae : AEMeasurable (fun x : ℝ => ENNReal.ofReal (Real.sqrt (1 + deriv r x ^ 2) * r x ^ n))
      (volume.restrict J) := by
    have h1 : AEMeasurable (deriv r) (volume.restrict J) := (measurable_deriv r).aemeasurable
    have h2 : AEMeasurable r (volume.restrict J) := hrContOn.aemeasurable hJm
    have h3 : AEMeasurable (fun x => Real.sqrt (1 + deriv r x ^ 2)) (volume.restrict J) :=
      Measurable.comp_aemeasurable Real.continuous_sqrt.measurable
        (aemeasurable_const.add (h1.pow_const 2))
    exact ENNReal.measurable_ofReal.comp_aemeasurable (h3.mul (h2.pow_const n))
  have hDae : AEMeasurable (hemiDensity n) (volume.restrict A) :=
    (hemiDensity_continuousOn_lpc hAsub).aemeasurable hAm
  have hCae' : AEMeasurable (fun p : CapSpace n =>
      ENNReal.ofReal (Real.sqrt (1 + deriv r p.1 ^ 2) * r p.1 ^ n))
      ((volume.restrict J).prod (volume.restrict A)) := hCae.comp_fst
  have hDae' : AEMeasurable (fun p : CapSpace n => hemiDensity n p.2)
      ((volume.restrict J).prod (volume.restrict A)) := hDae.comp_snd
  have hAEfull : AEMeasurable
      (fun p : CapSpace n =>
        h (latChart_lch n r (toEuclid n p)) *
            ENNReal.ofReal (Real.sqrt (1 + deriv r p.1 ^ 2) * r p.1 ^ n) * hemiDensity n p.2)
      ((volume : Measure (CapSpace n)).restrict (J ×ˢ A)) := by
    have hmeq : (volume : Measure (CapSpace n)).restrict (J ×ˢ A)
        = (volume.restrict J).prod (volume.restrict A) := by
      rw [Measure.prod_restrict, ← MeasureTheory.Measure.volume_eq_prod]
    have hAE_hΨ' : AEMeasurable (fun p : CapSpace n => h (latChart_lch n r (toEuclid n p)))
        ((volume.restrict J).prod (volume.restrict A)) := by
      rw [← hmeq]; exact hAE_hΨ
    rw [hmeq]
    exact (hAE_hΨ'.mul hCae').mul hDae'
  have key5 : ∫⁻ p in J ×ˢ A,
        h (latChart_lch n r (toEuclid n p)) *
            ENNReal.ofReal (Real.sqrt (1 + deriv r p.1 ^ 2) * r p.1 ^ n) * hemiDensity n p.2
        ∂(volume : Measure (CapSpace n))
      = ∫⁻ x in J, ∫⁻ z in A,
          h (latChart_lch n r (toEuclid n (x, z))) *
              ENNReal.ofReal (Real.sqrt (1 + deriv r x ^ 2) * r x ^ n) * hemiDensity n z
          ∂volume ∂volume := by
    rw [MeasureTheory.Measure.volume_eq_prod]
    exact MeasureTheory.setLIntegral_prod _ (by rwa [← MeasureTheory.Measure.volume_eq_prod])
  -- Step 6: pull the axial factor out of the inner integral, and unfold the chart value.
  have key6 : ∀ x ∈ J, (∫⁻ z in A,
        h (latChart_lch n r (toEuclid n (x, z))) *
            ENNReal.ofReal (Real.sqrt (1 + deriv r x ^ 2) * r x ^ n) * hemiDensity n z ∂volume)
      = ENNReal.ofReal (Real.sqrt (1 + deriv r x ^ 2) * r x ^ n) *
          ∫⁻ z in A, h (toEuclid (n + 1) (x, r x • hemi n z)) * hemiDensity n z ∂volume := by
    intro x hx
    have hchartval : ∀ z ∈ A, h (latChart_lch n r (toEuclid n (x, z)))
        = h (toEuclid (n + 1) (x, r x • hemi n z)) := by
      intro z hz
      have hz1 : ‖z‖ < 1 := mem_ball_zero_iff.mp (hAsub hz)
      have hw0 : (toEuclid n (x, z)) 0 = x := by
        rw [← consE_lch_eq_toEuclid_lch]; exact consE_apply_zero_lch n x z
      have hwtail : tailE_lch n (toEuclid n (x, z)) = z := by
        rw [← consE_lch_eq_toEuclid_lch]; exact tailE_consE_lch n x z
      have hchart := (latChart_mem_lch r (w := toEuclid n (x, z)) (by rw [hwtail]; exact hz1)).1
      rw [hw0, hwtail] at hchart
      exact congrArg h hchart
    have hstep1 : (∫⁻ z in A,
          h (latChart_lch n r (toEuclid n (x, z))) *
              ENNReal.ofReal (Real.sqrt (1 + deriv r x ^ 2) * r x ^ n) * hemiDensity n z ∂volume)
        = ∫⁻ z in A, ENNReal.ofReal (Real.sqrt (1 + deriv r x ^ 2) * r x ^ n) *
            (h (toEuclid (n + 1) (x, r x • hemi n z)) * hemiDensity n z) ∂volume := by
      apply setLIntegral_congr_fun hAm
      intro z hz
      dsimp only
      rw [hchartval z hz]; ring
    have hcont : Continuous (fun z : Esp_lch n => toEuclid (n + 1) (x, r x • hemi n z)) :=
      (continuous_toEuclid_lpc (n + 1)).comp
        (Continuous.prodMk continuous_const (continuous_const.smul (hemiContinuous_alt n)))
    have hfz : AEMeasurable (fun z : Esp_lch n =>
        h (toEuclid (n + 1) (x, r x • hemi n z)) * hemiDensity n z) (volume.restrict A) :=
      (hMeasurable.comp hcont.measurable).aemeasurable.mul hDae
    rw [hstep1, lintegral_const_mul'' _ hfz]
  -- Step 7: convert the `z`-integral against `hemiDensity n` into the sphere integral.
  have key7 : ∀ x ∈ J,
      (∫⁻ z in A, h (toEuclid (n + 1) (x, r x • hemi n z)) * hemiDensity n z ∂volume)
        = ∫⁻ ω in {ω : sphere (0 : Esp_lch (n + 1)) 1 | (ω : Esp_lch (n + 1)) ∈ hemi n '' A},
            h (toEuclid (n + 1) (x, r x • (ω : Esp_lch (n + 1)))) ∂(volume.toSphere) := by
    intro x _
    have hgcont : Continuous (fun p : Esp_lch (n + 1) => toEuclid (n + 1) (x, r x • p)) :=
      (continuous_toEuclid_lpc (n + 1)).comp
        (Continuous.prodMk continuous_const (continuous_id.const_smul (r x)))
    have hgmeas : Measurable (fun p : Esp_lch (n + 1) => h (toEuclid (n + 1) (x, r x • p))) :=
      hMeasurable.comp hgcont.measurable
    exact (hemiToSphereLintegral_alt n hV A hAsub hAm
      (fun p => h (toEuclid (n + 1) (x, r x • p))) hgmeas).symm
  -- Final assembly.
  calc ∫⁻ y in latChart_lch n r '' S, h y
        ∂(Measure.hausdorffMeasure ((n : ℝ) + 1) : Measure (Esp_lch (n + 2)))
      = ∫⁻ w in S, h (latChart_lch n r w) * ENNReal.ofReal (Real.sqrt (gramDet (F' w)))
          ∂(Measure.hausdorffMeasure ((n : ℝ) + 1) : Measure (Esp_lch (n + 1))) := key1
    _ = hConst (n + 1) *
          ∫⁻ w in S, h (latChart_lch n r w) * ENNReal.ofReal (Real.sqrt (gramDet (F' w)))
            ∂(volume : Measure (Esp_lch (n + 1))) := key2
    _ = hConst (n + 1) * ∫⁻ p in J ×ˢ A,
          h (latChart_lch n r (toEuclid n p)) *
            ENNReal.ofReal (Real.sqrt (gramDet (F' (toEuclid n p))))
          ∂(volume : Measure (CapSpace n)) := by rw [key3]
    _ = hConst (n + 1) * ∫⁻ p in J ×ˢ A,
          h (latChart_lch n r (toEuclid n p)) *
              ENNReal.ofReal (Real.sqrt (1 + deriv r p.1 ^ 2) * r p.1 ^ n) * hemiDensity n p.2
          ∂(volume : Measure (CapSpace n)) := by rw [key4]
    _ = hConst (n + 1) * ∫⁻ x in J, ∫⁻ z in A,
          h (latChart_lch n r (toEuclid n (x, z))) *
              ENNReal.ofReal (Real.sqrt (1 + deriv r x ^ 2) * r x ^ n) * hemiDensity n z
          ∂volume ∂volume := by rw [key5]
    _ = hConst (n + 1) * ∫⁻ x in J, ENNReal.ofReal (Real.sqrt (1 + deriv r x ^ 2) * r x ^ n) *
          ∫⁻ ω in {ω : sphere (0 : Esp_lch (n + 1)) 1 | (ω : Esp_lch (n + 1)) ∈ hemi n '' A},
            h (toEuclid (n + 1) (x, r x • (ω : Esp_lch (n + 1)))) ∂(volume.toSphere) ∂volume := by
        congr 1
        refine setLIntegral_congr_fun hJm (fun x hx => ?_)
        exact (key6 x hx).trans (congrArg
          (fun t => ENNReal.ofReal (Real.sqrt (1 + deriv r x ^ 2) * r x ^ n) * t) (key7 x hx))
