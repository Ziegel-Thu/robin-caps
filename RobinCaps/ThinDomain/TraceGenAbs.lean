import RobinCaps.ThinDomain.TraceGen

/-!
# The trace datum of the thin domain in general transverse dimension, for two abstract caps

This file generalises `RobinCaps/ThinDomain/TraceGen.lean` from the two hemispherical caps
`Cap.hemisphere m` (with the concrete trace datum `capTraceDataHemi_th`) to **two arbitrary
admissible caps** `Cm Cp : Cap m` equipped with **abstract** trace data `tdm : CapTraceData Cm`,
`tdp : CapTraceData Cp`.

The bulk interface `RobinCaps.ThinDomain.BulkTraceInput_tgn` and the whole apparatus of
`RobinCaps/ThinDomain/TraceGen.lean` sections 0–4 (transport along `affP`, additivity/homogeneity
of `capLeft`/`capRight`, bilinearity of `bdCyl`, the bulk trace interface and its linearisation)
are already stated for general `Cm Cp : Cap m` there, so they are reused verbatim.

**Normalisation.** Unlike `RobinCaps.ThinDomain.capC_tgn m R = √(R^m)`, this file uses
`c = R ^ ((m : ℝ) / 2)` (the real-power normalisation of `RobinCaps.ThinDomain.TrialBound`'s
`sq_rpow_half`), matching the consumers `RobinCaps.ThinDomain.TrialAssemblyW.TraceSplitW_taw` and
`RobinCaps.ThinDomain.BridgeCapLowerGen.bdCapL_bcg`.

**The terminal disc.**  `RobinCaps.Cap.capGammaPair C f g` (hence `CapTraceData.bdΓ`, via
`bdΓ_eq`) is the *lateral* revolution integral **plus** the terminal-disc integral
`∫_{ball 0 (C.θ 0)} f(0,z) g(0,z)`.  For the hemisphere `(Cap.hemisphere m).θ 0 = 0` and this disc
degenerates to a point, so `RobinCaps/ThinDomain/TraceGen.lean` could kill it outright.  For a
general cap — in particular the flat cap, whose terminal disc has full radius `θ 0 = 1` — it does
not vanish.  Reassuringly, `RobinCaps.ThinDomain.boundaryIntegral_split`
(`RobinCaps/ThinDomain/BoundaryPieces.lean`) already carries the **same** terminal-disc term in
its cap pieces (`R ^ m * (capLateralIntegral Cm (…) + ∫ z in ball 0 (Cm.θ 0), g (-L/2, R • z))`),
so the two sides of `bd_eq` / `tr_continuous` match *exactly*, term for term, once both are
unfolded — no extra hypothesis about the disc is needed, and in particular no
`CapPieceWithDisc_tga`-style axiom is introduced.  The price is that the cap-piece identities of
this file are stated with the lateral integral **and** the disc integral kept together (matching
`boundaryIntegral_split`'s own grouping), rather than as a pure lateral identity the way
`RobinCaps/ThinDomain/TraceGen.lean` could afford to for the hemisphere.

No `sorry`, `admit`, `axiom` or `native_decide` occurs in this file.
-/

open MeasureTheory Set Metric Filter
open scoped ENNReal Topology InnerProductSpace

noncomputable section

namespace RobinCaps.ThinDomain

open RobinCaps.Domain RobinCaps.Cap RobinCaps.Sobolev RobinCaps.Compact

/-! ## 0. The normalisation constant `c = R^{m/2}` -/

/-- The manuscript's normalisation constant `c = R^{m/2}`, realised through the real power
`Real.rpow` (rather than `Real.sqrt (R^m)` as `RobinCaps.ThinDomain.capC_tgn`), to match the
normalisation used by `RobinCaps.ThinDomain.TrialAssemblyW` / `RobinCaps.ThinDomain.BridgeCapLowerGen`. -/
def capC_tga (m : ℕ) (R : ℝ) : ℝ := R ^ ((m : ℝ) / 2)

theorem capC_sq_tga (m : ℕ) {R : ℝ} (hR : 0 < R) : capC_tga m R ^ 2 = R ^ m :=
  sq_rpow_half m hR

theorem capC_pos_tga (m : ℕ) {R : ℝ} (hR : 0 < R) : 0 < capC_tga m R :=
  Real.rpow_pos_of_pos hR _

theorem capC_pow_inv_sq_tga (m : ℕ) {R : ℝ} (hR : 0 < R) :
    R ^ m * (capC_tga m R)⁻¹ ^ 2 = 1 := by
  rw [← capC_sq_tga m hR, ← mul_pow, mul_inv_cancel₀ (ne_of_gt (capC_pos_tga m hR)), one_pow]

/-- The algebraic cancellation needed to turn the `capC²`-rescaled lateral-plus-disc sum back into
the unrescaled one: `R^m c⁻² (c² a + c² b) = R^m (a+b)`. -/
theorem capC_cancel_add_tga (m : ℕ) {R : ℝ} (hR : 0 < R) (a b : ℝ) :
    R ^ m * (capC_tga m R)⁻¹ ^ 2 * (capC_tga m R ^ 2 * a + capC_tga m R ^ 2 * b)
      = R ^ m * (a + b) := by
  have hcc : (capC_tga m R)⁻¹ ^ 2 * capC_tga m R ^ 2 = 1 := by
    rw [inv_pow, inv_mul_cancel₀ (pow_ne_zero 2 (capC_pos_tga m hR).ne')]
  calc R ^ m * (capC_tga m R)⁻¹ ^ 2 * (capC_tga m R ^ 2 * a + capC_tga m R ^ 2 * b)
      = R ^ m * ((capC_tga m R)⁻¹ ^ 2 * capC_tga m R ^ 2) * (a + b) := by ring
    _ = R ^ m * 1 * (a + b) := by rw [hcc]
    _ = R ^ m * (a + b) := by ring

/-- **For optional reuse of `RobinCaps.ThinDomain.TraceGen`'s lemmas verbatim**: the two
normalisations of `c` agree for `R > 0`. -/
theorem rpow_half_eq_sqrt_tga (m : ℕ) {R : ℝ} (hR : 0 < R) :
    capC_tga m R = Real.sqrt (R ^ m) := by
  have hnn : (0:ℝ) ≤ R := hR.le
  rw [capC_tga, Real.sqrt_eq_rpow, div_eq_mul_inv, Real.rpow_mul hnn, Real.rpow_natCast, one_div]

/-! ## 1. The cap traces `capTraceL_tga` / `capTraceR_tga`, for abstract cap trace data -/

variable {m : ℕ} {Cm Cp : Cap m} {L R : ℝ}

/-- **The left-cap trace**: `tdm`'s `Γ`-trace of the rescaled left-cap component, transported to
`Ω_R`'s coordinates through the inverse of `(s, z) ↦ (-L/2 - R s, R z)`. -/
def capTraceL_tga (hR : 0 < R) (hL : (Cm.K + Cp.K) * R < L) (tdm : CapTraceData Cm)
    (u : H1P (thinDomain Cm Cp L R)) (p : CapSpace m) : ℝ :=
  (capC_tga m R)⁻¹ * tdm.trΓ (capLeft hR hL (capC_tga m R) u) ((-L / 2 - p.1) / R, R⁻¹ • p.2)

/-- **The right-cap trace**: transported through the inverse of `(s, z) ↦ (L/2 + R s, R z)`. -/
def capTraceR_tga (hR : 0 < R) (hL : (Cm.K + Cp.K) * R < L) (tdp : CapTraceData Cp)
    (u : H1P (thinDomain Cm Cp L R)) (p : CapSpace m) : ℝ :=
  (capC_tga m R)⁻¹ * tdp.trΓ (capRight hR hL (capC_tga m R) u) ((p.1 - L / 2) / R, R⁻¹ • p.2)

variable (hR : 0 < R) (hL : (Cm.K + Cp.K) * R < L)

theorem capTraceL_add_tga (tdm : CapTraceData Cm) (u v : H1P (thinDomain Cm Cp L R)) :
    capTraceL_tga hR hL tdm (u + v) = capTraceL_tga hR hL tdm u + capTraceL_tga hR hL tdm v := by
  funext p
  show capTraceL_tga hR hL tdm (u + v) p
      = capTraceL_tga hR hL tdm u p + capTraceL_tga hR hL tdm v p
  unfold capTraceL_tga
  rw [capLeft_add_tgn, tdm.trΓ_add]
  simp only [Pi.add_apply]
  ring

theorem capTraceL_smul_tga (tdm : CapTraceData Cm) (k : ℝ) (u : H1P (thinDomain Cm Cp L R)) :
    capTraceL_tga hR hL tdm (k • u) = k • capTraceL_tga hR hL tdm u := by
  funext p
  show capTraceL_tga hR hL tdm (k • u) p = k * capTraceL_tga hR hL tdm u p
  unfold capTraceL_tga
  rw [capLeft_smul_tgn, tdm.trΓ_smul]
  simp only [Pi.smul_apply, smul_eq_mul]
  ring

theorem capTraceR_add_tga (tdp : CapTraceData Cp) (u v : H1P (thinDomain Cm Cp L R)) :
    capTraceR_tga hR hL tdp (u + v) = capTraceR_tga hR hL tdp u + capTraceR_tga hR hL tdp v := by
  funext p
  show capTraceR_tga hR hL tdp (u + v) p
      = capTraceR_tga hR hL tdp u p + capTraceR_tga hR hL tdp v p
  unfold capTraceR_tga
  rw [capRight_add_tgn, tdp.trΓ_add]
  simp only [Pi.add_apply]
  ring

theorem capTraceR_smul_tga (tdp : CapTraceData Cp) (k : ℝ) (u : H1P (thinDomain Cm Cp L R)) :
    capTraceR_tga hR hL tdp (k • u) = k • capTraceR_tga hR hL tdp u := by
  funext p
  show capTraceR_tga hR hL tdp (k • u) p = k * capTraceR_tga hR hL tdp u p
  unfold capTraceR_tga
  rw [capRight_smul_tgn, tdp.trΓ_smul]
  simp only [Pi.smul_apply, smul_eq_mul]
  ring

/-- **The left-cap trace, evaluated at an image point of the left-cap affine chart.** -/
theorem capTraceL_affineL_tga (tdm : CapTraceData Cm) (u : H1P (thinDomain Cm Cp L R))
    (q : CapSpace m) :
    capTraceL_tga hR hL tdm u (-L / 2 - R * q.1, R • q.2)
      = (capC_tga m R)⁻¹ * tdm.trΓ (capLeft hR hL (capC_tga m R) u) q := by
  have e1 : (-L / 2 - (-L / 2 - R * q.1)) / R = q.1 := by field_simp; ring
  have e2 : R⁻¹ • (R • q.2) = q.2 := by rw [smul_smul, inv_mul_cancel₀ hR.ne', one_smul]
  show (capC_tga m R)⁻¹ * tdm.trΓ (capLeft hR hL (capC_tga m R) u)
      ((-L / 2 - (-L / 2 - R * q.1)) / R, R⁻¹ • (R • q.2)) = _
  rw [e1, e2]

/-- **The right-cap trace, evaluated at an image point of the right-cap affine chart.** -/
theorem capTraceR_affineR_tga (tdp : CapTraceData Cp) (u : H1P (thinDomain Cm Cp L R))
    (q : CapSpace m) :
    capTraceR_tga hR hL tdp u (L / 2 + R * q.1, R • q.2)
      = (capC_tga m R)⁻¹ * tdp.trΓ (capRight hR hL (capC_tga m R) u) q := by
  have e1 : (L / 2 + R * q.1 - L / 2) / R = q.1 := by field_simp; ring
  have e2 : R⁻¹ • (R • q.2) = q.2 := by rw [smul_smul, inv_mul_cancel₀ hR.ne', one_smul]
  show (capC_tga m R)⁻¹ * tdp.trΓ (capRight hR hL (capC_tga m R) u)
      ((L / 2 + R * q.1 - L / 2) / R, R⁻¹ • (R • q.2)) = _
  rw [e1, e2]

/-! ## 2. The two cap pieces `bdCapL_tga` / `bdCapR_tga` of the boundary form -/

/-- **The left-cap piece of the boundary form.** -/
def bdCapL_tga (tdm : CapTraceData Cm) (u v : H1P (thinDomain Cm Cp L R)) : ℝ :=
  R ^ m * (capC_tga m R)⁻¹ ^ 2 * tdm.bdΓ
    (capLeft hR hL (capC_tga m R) u) (capLeft hR hL (capC_tga m R) v)

/-- **The right-cap piece of the boundary form.** -/
def bdCapR_tga (tdp : CapTraceData Cp) (u v : H1P (thinDomain Cm Cp L R)) : ℝ :=
  R ^ m * (capC_tga m R)⁻¹ ^ 2 * tdp.bdΓ
    (capRight hR hL (capC_tga m R) u) (capRight hR hL (capC_tga m R) v)

theorem bdCapL_eq_bdΓ_tga (tdm : CapTraceData Cm) (u v : H1P (thinDomain Cm Cp L R)) :
    bdCapL_tga hR hL tdm u v = tdm.bdΓ
      (capLeft hR hL (capC_tga m R) u) (capLeft hR hL (capC_tga m R) v) := by
  simp only [bdCapL_tga, capC_pow_inv_sq_tga m hR, one_mul]

theorem bdCapR_eq_bdΓ_tga (tdp : CapTraceData Cp) (u v : H1P (thinDomain Cm Cp L R)) :
    bdCapR_tga hR hL tdp u v = tdp.bdΓ
      (capRight hR hL (capC_tga m R) u) (capRight hR hL (capC_tga m R) v) := by
  simp only [bdCapR_tga, capC_pow_inv_sq_tga m hR, one_mul]

theorem bdCapL_add_left_tga (tdm : CapTraceData Cm) (u u' v : H1P (thinDomain Cm Cp L R)) :
    bdCapL_tga hR hL tdm (u + u') v = bdCapL_tga hR hL tdm u v + bdCapL_tga hR hL tdm u' v := by
  simp only [bdCapL_tga, capLeft_add_tgn, map_add, LinearMap.add_apply]
  ring

theorem bdCapL_smul_left_tga (tdm : CapTraceData Cm) (k : ℝ) (u v : H1P (thinDomain Cm Cp L R)) :
    bdCapL_tga hR hL tdm (k • u) v = k * bdCapL_tga hR hL tdm u v := by
  simp only [bdCapL_tga, capLeft_smul_tgn, map_smul, LinearMap.smul_apply, smul_eq_mul]
  ring

theorem bdCapL_symm_tga (tdm : CapTraceData Cm) (u v : H1P (thinDomain Cm Cp L R)) :
    bdCapL_tga hR hL tdm u v = bdCapL_tga hR hL tdm v u := by
  simp only [bdCapL_tga, tdm.bdΓ_symm]

theorem bdCapL_add_right_tga (tdm : CapTraceData Cm) (u v v' : H1P (thinDomain Cm Cp L R)) :
    bdCapL_tga hR hL tdm u (v + v') = bdCapL_tga hR hL tdm u v + bdCapL_tga hR hL tdm u v' := by
  rw [bdCapL_symm_tga hR hL tdm u (v + v'), bdCapL_add_left_tga hR hL tdm v v' u,
    bdCapL_symm_tga hR hL tdm v u, bdCapL_symm_tga hR hL tdm v' u]

theorem bdCapL_smul_right_tga (tdm : CapTraceData Cm) (k : ℝ) (u v : H1P (thinDomain Cm Cp L R)) :
    bdCapL_tga hR hL tdm u (k • v) = k * bdCapL_tga hR hL tdm u v := by
  rw [bdCapL_symm_tga hR hL tdm u (k • v), bdCapL_smul_left_tga hR hL tdm k v u,
    bdCapL_symm_tga hR hL tdm v u]

theorem bdCapL_nonneg_tga (tdm : CapTraceData Cm) (u : H1P (thinDomain Cm Cp L R)) :
    0 ≤ bdCapL_tga hR hL tdm u u := by
  rw [bdCapL_eq_bdΓ_tga]
  exact tdm.bdΓ_nonneg _

theorem bdCapR_add_left_tga (tdp : CapTraceData Cp) (u u' v : H1P (thinDomain Cm Cp L R)) :
    bdCapR_tga hR hL tdp (u + u') v = bdCapR_tga hR hL tdp u v + bdCapR_tga hR hL tdp u' v := by
  simp only [bdCapR_tga, capRight_add_tgn, map_add, LinearMap.add_apply]
  ring

theorem bdCapR_smul_left_tga (tdp : CapTraceData Cp) (k : ℝ) (u v : H1P (thinDomain Cm Cp L R)) :
    bdCapR_tga hR hL tdp (k • u) v = k * bdCapR_tga hR hL tdp u v := by
  simp only [bdCapR_tga, capRight_smul_tgn, map_smul, LinearMap.smul_apply, smul_eq_mul]
  ring

theorem bdCapR_symm_tga (tdp : CapTraceData Cp) (u v : H1P (thinDomain Cm Cp L R)) :
    bdCapR_tga hR hL tdp u v = bdCapR_tga hR hL tdp v u := by
  simp only [bdCapR_tga, tdp.bdΓ_symm]

theorem bdCapR_add_right_tga (tdp : CapTraceData Cp) (u v v' : H1P (thinDomain Cm Cp L R)) :
    bdCapR_tga hR hL tdp u (v + v') = bdCapR_tga hR hL tdp u v + bdCapR_tga hR hL tdp u v' := by
  rw [bdCapR_symm_tga hR hL tdp u (v + v'), bdCapR_add_left_tga hR hL tdp v v' u,
    bdCapR_symm_tga hR hL tdp v u, bdCapR_symm_tga hR hL tdp v' u]

theorem bdCapR_smul_right_tga (tdp : CapTraceData Cp) (k : ℝ) (u v : H1P (thinDomain Cm Cp L R)) :
    bdCapR_tga hR hL tdp u (k • v) = k * bdCapR_tga hR hL tdp u v := by
  rw [bdCapR_symm_tga hR hL tdp u (k • v), bdCapR_smul_left_tga hR hL tdp k v u,
    bdCapR_symm_tga hR hL tdp v u]

theorem bdCapR_nonneg_tga (tdp : CapTraceData Cp) (u : H1P (thinDomain Cm Cp L R)) :
    0 ≤ bdCapR_tga hR hL tdp u u := by
  rw [bdCapR_eq_bdΓ_tga]
  exact tdp.bdΓ_nonneg _

/-! ## 3. The combined trace `trAbs_tga` -/

/-- **The combined trace of the thin domain, for two abstract caps**: the bulk trace
`bulkTraceL_tgn` on the closed bulk interval, and the cap traces `capTraceL_tga` / `capTraceR_tga`
on the two caps. -/
def trAbs_tga (tdm : CapTraceData Cm) (tdp : CapTraceData Cp)
    (hb : BulkTraceInput_tgn m Cm Cp L R hR hL) (u : H1P (thinDomain Cm Cp L R)) :
    CapSpace m → ℝ :=
  fun p =>
    if p.1 < interfaceL Cm L R then capTraceL_tga hR hL tdm u p
    else if interfaceR Cp L R < p.1 then capTraceR_tga hR hL tdp u p
    else bulkTraceL_tgn hb u p

theorem trAbs_eq_capTraceL_of_lt_tga (tdm : CapTraceData Cm) (tdp : CapTraceData Cp)
    (hb : BulkTraceInput_tgn m Cm Cp L R hR hL) (u : H1P (thinDomain Cm Cp L R)) {p : CapSpace m}
    (hp : p.1 < interfaceL Cm L R) :
    trAbs_tga hR hL tdm tdp hb u p = capTraceL_tga hR hL tdm u p := by
  simp only [trAbs_tga, if_pos hp]

theorem trAbs_eq_capTraceR_of_gt_tga (tdm : CapTraceData Cm) (tdp : CapTraceData Cp)
    (hb : BulkTraceInput_tgn m Cm Cp L R hR hL) (u : H1P (thinDomain Cm Cp L R)) {p : CapSpace m}
    (hp1 : ¬ p.1 < interfaceL Cm L R) (hp2 : interfaceR Cp L R < p.1) :
    trAbs_tga hR hL tdm tdp hb u p = capTraceR_tga hR hL tdp u p := by
  simp only [trAbs_tga, if_neg hp1, if_pos hp2]

theorem trAbs_eq_bulkTraceL_tga (tdm : CapTraceData Cm) (tdp : CapTraceData Cp)
    (hb : BulkTraceInput_tgn m Cm Cp L R hR hL) (u : H1P (thinDomain Cm Cp L R)) {p : CapSpace m}
    (hp1 : ¬ p.1 < interfaceL Cm L R) (hp2 : ¬ interfaceR Cp L R < p.1) :
    trAbs_tga hR hL tdm tdp hb u p = bulkTraceL_tgn hb u p := by
  simp only [trAbs_tga, if_neg hp1, if_neg hp2]

theorem trAbs_add_tga (tdm : CapTraceData Cm) (tdp : CapTraceData Cp)
    (hb : BulkTraceInput_tgn m Cm Cp L R hR hL) (u v : H1P (thinDomain Cm Cp L R)) :
    trAbs_tga hR hL tdm tdp hb (u + v) = trAbs_tga hR hL tdm tdp hb u + trAbs_tga hR hL tdm tdp hb v := by
  funext p
  show trAbs_tga hR hL tdm tdp hb (u + v) p
      = trAbs_tga hR hL tdm tdp hb u p + trAbs_tga hR hL tdm tdp hb v p
  unfold trAbs_tga
  split_ifs with h1 h2
  · exact congrFun (capTraceL_add_tga hR hL tdm u v) p
  · exact congrFun (capTraceR_add_tga hR hL tdp u v) p
  · exact congrFun (bulkTraceL_add_tgn hb u v) p

theorem trAbs_smul_tga (tdm : CapTraceData Cm) (tdp : CapTraceData Cp)
    (hb : BulkTraceInput_tgn m Cm Cp L R hR hL) (k : ℝ) (u : H1P (thinDomain Cm Cp L R)) :
    trAbs_tga hR hL tdm tdp hb (k • u) = k • trAbs_tga hR hL tdm tdp hb u := by
  funext p
  show trAbs_tga hR hL tdm tdp hb (k • u) p = k * trAbs_tga hR hL tdm tdp hb u p
  unfold trAbs_tga
  split_ifs with h1 h2
  · exact congrFun (capTraceL_smul_tga hR hL tdm k u) p
  · exact congrFun (capTraceR_smul_tga hR hL tdp k u) p
  · exact congrFun (bulkTraceL_smul_tgn hb k u) p

/-! ## 4. The bilinear boundary form `bdAbs_tga` -/

/-- **The bilinear boundary form**, the sum of the two cap pieces and the bulk cylinder form of
`bdR m R`. -/
def bdAbs_tga (tdm : CapTraceData Cm) (tdp : CapTraceData Cp)
    (hb : BulkTraceInput_tgn m Cm Cp L R hR hL) :
    H1P (thinDomain Cm Cp L R) →ₗ[ℝ] H1P (thinDomain Cm Cp L R) →ₗ[ℝ] ℝ :=
  LinearMap.mk₂ ℝ (fun u v => bdCapL_tga hR hL tdm u v
      + bdCyl (bdR m R) (restrictBulkP hR u) (restrictBulkP hR v) + bdCapR_tga hR hL tdp u v)
    (fun u u' v => by
      dsimp only
      rw [bdCapL_add_left_tga, bdCapR_add_left_tga, map_add,
        bdCyl_add_left_tgn (bdSliceable_bdR_bsg hR _ _)]
      ring)
    (fun k u v => by
      dsimp only
      simp only [smul_eq_mul]
      rw [bdCapL_smul_left_tga, bdCapR_smul_left_tga, map_smul, bdCyl_smul_left_tgn]
      ring)
    (fun u v v' => by
      dsimp only
      rw [bdCapL_add_right_tga, bdCapR_add_right_tga, map_add,
        bdCyl_add_right_tgn (bdSliceable_bdR_bsg hR _ _) (fun x y => bdR_symm x y)]
      ring)
    (fun k u v => by
      dsimp only
      simp only [smul_eq_mul]
      rw [bdCapL_smul_right_tga, bdCapR_smul_right_tga, map_smul,
        bdCyl_smul_right_tgn (bdR m R) (fun x y => bdR_symm x y)]
      ring)

theorem bdAbs_apply_tga (tdm : CapTraceData Cm) (tdp : CapTraceData Cp)
    (hb : BulkTraceInput_tgn m Cm Cp L R hR hL) (u v : H1P (thinDomain Cm Cp L R)) :
    bdAbs_tga hR hL tdm tdp hb u v = bdCapL_tga hR hL tdm u v
      + bdCyl (bdR m R) (restrictBulkP hR u) (restrictBulkP hR v) + bdCapR_tga hR hL tdp u v :=
  rfl

theorem bdAbs_symm_tga (tdm : CapTraceData Cm) (tdp : CapTraceData Cp)
    (hb : BulkTraceInput_tgn m Cm Cp L R hR hL) (u v : H1P (thinDomain Cm Cp L R)) :
    bdAbs_tga hR hL tdm tdp hb u v = bdAbs_tga hR hL tdm tdp hb v u := by
  rw [bdAbs_apply_tga, bdAbs_apply_tga, bdCapL_symm_tga, bdCapR_symm_tga,
    bdCyl_symm_tgn (bdR m R) (fun x y => bdR_symm x y)]

theorem bdAbs_nonneg_tga (hm : 1 ≤ m) (tdm : CapTraceData Cm) (tdp : CapTraceData Cp)
    (hb : BulkTraceInput_tgn m Cm Cp L R hR hL) (u : H1P (thinDomain Cm Cp L R)) :
    0 ≤ bdAbs_tga hR hL tdm tdp hb u u := by
  rw [bdAbs_apply_tga]
  have h1 := bdCapL_nonneg_tga hR hL tdm u
  have h2 := bdCapR_nonneg_tga hR hL tdp u
  have h3 : 0 ≤ bdCyl (bdR m R) (restrictBulkP hR u) (restrictBulkP hR u) :=
    bdCyl_nonneg_tgn (fun x => bdR_nonneg hm hR x) _
  linarith

/-- **`vanishes_ae`.**  If `u.toFun` vanishes a.e. on the thin domain, `bdAbs` vanishes against
every `v`. -/
theorem bdAbs_vanishes_ae_tga (tdm : CapTraceData Cm) (tdp : CapTraceData Cp)
    (hb : BulkTraceInput_tgn m Cm Cp L R hR hL) (u : H1P (thinDomain Cm Cp L R))
    (hu : u.toFun =ᵐ[volume.restrict (thinDomain Cm Cp L R)] 0)
    (v : H1P (thinDomain Cm Cp L R)) :
    bdAbs_tga hR hL tdm tdp hb u v = 0 := by
  rw [bdAbs_apply_tga]
  have h1 : bdCapL_tga hR hL tdm u v = 0 := by
    rw [bdCapL_eq_bdΓ_tga,
      tdm.vanishes_ae (capLeft hR hL (capC_tga m R) u)
        (capLeft_toFun_ae_zero_tgn hR hL (capC_tga m R) hu) (capLeft hR hL (capC_tga m R) v)]
  have h3 : bdCapR_tga hR hL tdp u v = 0 := by
    rw [bdCapR_eq_bdΓ_tga,
      tdp.vanishes_ae (capRight hR hL (capC_tga m R) u)
        (capRight_toFun_ae_zero_tgn hR hL (capC_tga m R) hu) (capRight hR hL (capC_tga m R) v)]
  have h2 : bdCyl (bdR m R) (restrictBulkP hR u) (restrictBulkP hR v) = 0 := by
    refine bdCyl_eq_zero_of_toFun_ae_zero_tgn ?_ _
    show (restrictBulkP hR u).toFun
        =ᵐ[volume.restrict (bulkCyl (interfaceL Cm L R) (interfaceR Cp L R) m R)] 0
    rw [restrictBulkP_toFun]
    exact ae_restrict_of_ae_restrict_of_subset (bulkCyl_subset_thinDomain hR) hu
  rw [h1, h2, h3]
  ring

/-! ## 5. Continuity transport through the cap rescaling -/

theorem capLeft_continuousOn_tga {u : H1P (thinDomain Cm Cp L R)}
    (hc : ContinuousOn u.toFun (closure (thinDomain Cm Cp L R))) :
    ContinuousOn (capLeft hR hL (capC_tga m R) u).toFun (closure Cm.body) := by
  have hcont : Continuous (affP (-L / 2) (-1) R : CapSpace m → CapSpace m) :=
    (affHomeoP (m := m) (-L / 2) (by norm_num : (-1 : ℝ) ≠ 0) hR.ne').continuous
  have himg : affP (-L / 2) (-1) R '' closure Cm.body = closure (leftCap Cm L R) := by
    have h := Homeomorph.image_closure
      (affHomeoP (m := m) (-L / 2) (by norm_num : (-1 : ℝ) ≠ 0) hR.ne') Cm.body
    rwa [coe_affHomeoP, ← leftCap_eq_image] at h
  have hmaps : MapsTo (affP (-L / 2) (-1) R) (closure Cm.body)
      (closure (thinDomain Cm Cp L R)) := by
    intro p hp
    have hp' : affP (-L / 2) (-1) R p ∈ closure (leftCap Cm L R) := himg ▸ ⟨p, hp, rfl⟩
    exact closure_mono (leftCap_subset_thinDomain hR hL) hp'
  have hcomp : ContinuousOn (fun p => u.toFun (affP (-L / 2) (-1) R p)) (closure Cm.body) :=
    hc.comp hcont.continuousOn hmaps
  have heq : (capLeft hR hL (capC_tga m R) u).toFun
      = fun p => capC_tga m R * u.toFun (affP (-L / 2) (-1) R p) := by
    show (H1P.rescaleLeft Cm L (capC_tga m R) hR (Cap.Concave.continuousOn_Ioo Cm)
        (restrictLeft hR hL u)).toFun = _
    unfold H1P.rescaleLeft
    rw [H1P.cast_toFun, H1P.rescaleP_toFun, restrictLeft_toFun]
  rw [heq]
  exact continuousOn_const.mul hcomp

theorem capRight_continuousOn_tga {u : H1P (thinDomain Cm Cp L R)}
    (hc : ContinuousOn u.toFun (closure (thinDomain Cm Cp L R))) :
    ContinuousOn (capRight hR hL (capC_tga m R) u).toFun (closure Cp.body) := by
  have hcont : Continuous (affP (L / 2) 1 R : CapSpace m → CapSpace m) :=
    (affHomeoP (m := m) (L / 2) (by norm_num : (1 : ℝ) ≠ 0) hR.ne').continuous
  have himg : affP (L / 2) 1 R '' closure Cp.body = closure (rightCap Cp L R) := by
    have h := Homeomorph.image_closure
      (affHomeoP (m := m) (L / 2) (by norm_num : (1 : ℝ) ≠ 0) hR.ne') Cp.body
    rwa [coe_affHomeoP, ← rightCap_eq_image] at h
  have hmaps : MapsTo (affP (L / 2) 1 R) (closure Cp.body)
      (closure (thinDomain Cm Cp L R)) := by
    intro p hp
    have hp' : affP (L / 2) 1 R p ∈ closure (rightCap Cp L R) := himg ▸ ⟨p, hp, rfl⟩
    exact closure_mono (rightCap_subset_thinDomain hR hL) hp'
  have hcomp : ContinuousOn (fun p => u.toFun (affP (L / 2) 1 R p)) (closure Cp.body) :=
    hc.comp hcont.continuousOn hmaps
  have heq : (capRight hR hL (capC_tga m R) u).toFun
      = fun p => capC_tga m R * u.toFun (affP (L / 2) 1 R p) := by
    show (H1P.rescaleRight Cp L (capC_tga m R) hR (Cap.Concave.continuousOn_Ioo Cp)
        (restrictRight hR hL u)).toFun = _
    unfold H1P.rescaleRight
    rw [H1P.cast_toFun, H1P.rescaleP_toFun, restrictRight_toFun]
  rw [heq]
  exact continuousOn_const.mul hcomp

theorem capLeft_toFun_eq_tga (u : H1P (thinDomain Cm Cp L R)) (q : CapSpace m) :
    (capLeft hR hL (capC_tga m R) u).toFun q
      = capC_tga m R * u.toFun (-L / 2 - R * q.1, R • q.2) := by
  show (H1P.rescaleLeft Cm L (capC_tga m R) hR (Cap.Concave.continuousOn_Ioo Cm)
      (restrictLeft hR hL u)).toFun q = _
  unfold H1P.rescaleLeft
  rw [H1P.cast_toFun, H1P.rescaleP_toFun, restrictLeft_toFun]
  show capC_tga m R * u.toFun (affP (-L / 2) (-1) R q) = _
  have haff : affP (-L / 2) (-1) R q = (-L / 2 - R * q.1, R • q.2) := by
    show (-L / 2 + (-1) * R * q.1, R • q.2) = (-L / 2 - R * q.1, R • q.2)
    congr 1
    ring
  rw [haff]

theorem capRight_toFun_eq_tga (u : H1P (thinDomain Cm Cp L R)) (q : CapSpace m) :
    (capRight hR hL (capC_tga m R) u).toFun q
      = capC_tga m R * u.toFun (L / 2 + R * q.1, R • q.2) := by
  show (H1P.rescaleRight Cp L (capC_tga m R) hR (Cap.Concave.continuousOn_Ioo Cp)
      (restrictRight hR hL u)).toFun q = _
  unfold H1P.rescaleRight
  rw [H1P.cast_toFun, H1P.rescaleP_toFun, restrictRight_toFun]
  show capC_tga m R * u.toFun (affP (L / 2) 1 R q) = _
  have haff : affP (L / 2) 1 R q = (L / 2 + R * q.1, R • q.2) := by
    show (L / 2 + 1 * R * q.1, R • q.2) = (L / 2 + R * q.1, R • q.2)
    congr 1
    ring
  rw [haff]

/-! ## 5b. The one remaining hypothesis, per cap: integrability of the trace-product density -/

/-- **The one remaining hypothesis of this file, per cap.**  `RobinCaps.Cap.CapTraceData` bundles
a boundary representative `trΓ`, its induced bilinear form `bdΓ` and the value identity `bdΓ_eq`,
but not that the revolution-coordinate lateral density `capLateralDensity C (fun p => trΓ u p *
trΓ v p)` is literally Bochner-integrable on `Ioo (-C.K) 0` — only that its integral computes the
right value. This is exactly the gap `RobinCaps.ThinDomain.TraceGen.CapTraceIntegrable_tgn`
isolates for the hemisphere; here it is stated once per abstract cap so that it can be discharged
independently for `Cm` and for `Cp` (e.g. by the hemisphere's own witness, or by a future flat-cap
one). -/
structure CapTraceIntegrableAbs_tga {m : ℕ} (C : Cap m) (td : CapTraceData C) : Prop where
  integrableOn : ∀ a b : H1P C.body,
    IntegrableOn (capLateralDensity C (fun p => td.trΓ a p * td.trΓ b p)) (Ioo (-C.K) 0)

/-! ## 6. The trace inequality -/

theorem massP_dirichletP_restrictLeft_le_tga (u : H1P (thinDomain Cm Cp L R)) :
    massP (restrictLeft hR hL u) + dirichletP (restrictLeft hR hL u) ≤ massP u + dirichletP u := by
  have hm1 := massP_eq_sum hR hL u
  have hd1 := dirichletP_eq_sum hR hL u
  have hmb := massP_nonneg (restrictBulk hR hL u)
  have hmr := massP_nonneg (restrictRight hR hL u)
  have hdb := dirichletP_nonneg (restrictBulk hR hL u)
  have hdr := dirichletP_nonneg (restrictRight hR hL u)
  linarith

theorem massP_dirichletP_restrictRight_le_tga (u : H1P (thinDomain Cm Cp L R)) :
    massP (restrictRight hR hL u) + dirichletP (restrictRight hR hL u)
      ≤ massP u + dirichletP u := by
  have hm1 := massP_eq_sum hR hL u
  have hd1 := dirichletP_eq_sum hR hL u
  have hml := massP_nonneg (restrictLeft hR hL u)
  have hmb := massP_nonneg (restrictBulk hR hL u)
  have hdl := dirichletP_nonneg (restrictLeft hR hL u)
  have hdb := dirichletP_nonneg (restrictBulk hR hL u)
  linarith

theorem massP_dirichletP_restrictBulk_le_tga (u : H1P (thinDomain Cm Cp L R)) :
    massP (restrictBulk hR hL u) + dirichletP (restrictBulk hR hL u)
      ≤ massP u + dirichletP u := by
  have hm1 := massP_eq_sum hR hL u
  have hd1 := dirichletP_eq_sum hR hL u
  have hml := massP_nonneg (restrictLeft hR hL u)
  have hmr := massP_nonneg (restrictRight hR hL u)
  have hdl := dirichletP_nonneg (restrictLeft hR hL u)
  have hdr := dirichletP_nonneg (restrictRight hR hL u)
  linarith

/-- **`trace_ineq`.**  The boundary energy `bdAbs u u` is controlled by the `H¹` energy
`dirichletP u + massP u`, with a constant built from the two cap trace constants of `tdm`, `tdp`,
the manuscript rescaling `R, R⁻¹`, and the bulk constant `m/R + 1`. -/
theorem bdAbs_trace_ineq_tga (tdm : CapTraceData Cm) (tdp : CapTraceData Cp)
    (hb : BulkTraceInput_tgn m Cm Cp L R hR hL) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ u : H1P (thinDomain Cm Cp L R),
      bdAbs_tga hR hL tdm tdp hb u u ≤ C * (dirichletP u + massP u) := by
  set Ccapm := tdm.traceConst * max R R⁻¹ with hCcapm_def
  set Ccapp := tdp.traceConst * max R R⁻¹ with hCcapp_def
  set Cbulk := max ((m : ℝ) / R + 1) 1 with hCbulk_def
  have hCcapm_nonneg : 0 ≤ Ccapm :=
    mul_nonneg tdm.traceConst_nonneg (le_trans (le_of_lt hR) (le_max_left R R⁻¹))
  have hCcapp_nonneg : 0 ≤ Ccapp :=
    mul_nonneg tdp.traceConst_nonneg (le_trans (le_of_lt hR) (le_max_left R R⁻¹))
  have hCbulk_nonneg : 0 ≤ Cbulk := le_trans zero_le_one (le_max_right _ _)
  refine ⟨Ccapm + Cbulk + Ccapp, by linarith, fun u => ?_⟩
  rw [bdAbs_apply_tga]
  have h1 : bdCapL_tga hR hL tdm u u ≤ Ccapm * (dirichletP u + massP u) := by
    rw [bdCapL_eq_bdΓ_tga]
    have hb1 := tdm.trace_ineq (capLeft hR hL (capC_tga m R) u)
    have hdc := dirichletP_capLeft_of_sq_eq hR hL (capC_sq_tga m hR) u
    have hmc := massP_capLeft_of_sq_eq hR hL (capC_sq_tga m hR) u
    have hdnn := dirichletP_nonneg (restrictLeft hR hL u)
    have hmnn := massP_nonneg (restrictLeft hR hL u)
    have hR' : R ≤ max R R⁻¹ := le_max_left _ _
    have hRi : R⁻¹ ≤ max R R⁻¹ := le_max_right _ _
    have hsum := massP_dirichletP_restrictLeft_le_tga hR hL u
    have hstep : dirichletP (capLeft hR hL (capC_tga m R) u) + massP (capLeft hR hL (capC_tga m R) u)
        ≤ max R R⁻¹ * (dirichletP (restrictLeft hR hL u) + massP (restrictLeft hR hL u)) := by
      rw [hdc, hmc]
      nlinarith [mul_le_mul_of_nonneg_right hR' hdnn, mul_le_mul_of_nonneg_right hRi hmnn]
    have hfin := tdm.traceConst_nonneg
    nlinarith [mul_le_mul_of_nonneg_left hstep hfin, hb1, hsum]
  have h3 : bdCapR_tga hR hL tdp u u ≤ Ccapp * (dirichletP u + massP u) := by
    rw [bdCapR_eq_bdΓ_tga]
    have hb1 := tdp.trace_ineq (capRight hR hL (capC_tga m R) u)
    have hdc := dirichletP_capRight_of_sq_eq hR hL (capC_sq_tga m hR) u
    have hmc := massP_capRight_of_sq_eq hR hL (capC_sq_tga m hR) u
    have hdnn := dirichletP_nonneg (restrictRight hR hL u)
    have hmnn := massP_nonneg (restrictRight hR hL u)
    have hR' : R ≤ max R R⁻¹ := le_max_left _ _
    have hRi : R⁻¹ ≤ max R R⁻¹ := le_max_right _ _
    have hsum := massP_dirichletP_restrictRight_le_tga hR hL u
    have hstep : dirichletP (capRight hR hL (capC_tga m R) u)
        + massP (capRight hR hL (capC_tga m R) u)
        ≤ max R R⁻¹ * (dirichletP (restrictRight hR hL u) + massP (restrictRight hR hL u)) := by
      rw [hdc, hmc]
      nlinarith [mul_le_mul_of_nonneg_right hR' hdnn, mul_le_mul_of_nonneg_right hRi hmnn]
    have hfin := tdp.traceConst_nonneg
    nlinarith [mul_le_mul_of_nonneg_left hstep hfin, hb1, hsum]
  have h2 : bdCyl (bdR m R) (restrictBulkP hR u) (restrictBulkP hR u)
      ≤ Cbulk * (dirichletP u + massP u) := by
    have hle := bdCyl_bdR_le_tgn hR (restrictBulkP hR u)
    have hsum : massP (restrictBulkP hR u) + dirichletP (restrictBulkP hR u)
        ≤ massP u + dirichletP u := massP_dirichletP_restrictBulk_le_tga hR hL u
    have hmnn := massP_nonneg (restrictBulkP hR u)
    have hdnn := dirichletP_nonneg (restrictBulkP hR u)
    have hR1 : (m : ℝ) / R + 1 ≤ Cbulk := le_max_left _ _
    have hR2 : (1 : ℝ) ≤ Cbulk := le_max_right _ _
    nlinarith [mul_le_mul_of_nonneg_right hR1 hmnn, mul_le_mul_of_nonneg_right hR2 hdnn]
  linarith

/-! ## 7. `bd_eq`: the lateral and terminal-disc density identities -/

theorem capLateralDensity_left_eq_tga (tdm : CapTraceData Cm) (tdp : CapTraceData Cp)
    (hb : BulkTraceInput_tgn m Cm Cp L R hR hL) (u v : H1P (thinDomain Cm Cp L R)) (s : ℝ)
    (hs : s ∈ Ioo (-Cm.K) 0) :
    capLateralDensity Cm
        (fun p => trAbs_tga hR hL tdm tdp hb u (-L / 2 - R * p.1, R • p.2)
          * trAbs_tga hR hL tdm tdp hb v (-L / 2 - R * p.1, R • p.2)) s
      = (capC_tga m R)⁻¹ ^ 2 * capLateralDensity Cm
          (fun p => tdm.trΓ (capLeft hR hL (capC_tga m R) u) p
            * tdm.trΓ (capLeft hR hL (capC_tga m R) v) p) s := by
  have hlt : -L / 2 - R * s < interfaceL Cm L R := by
    show -L / 2 - R * s < -L / 2 + Cm.K * R
    nlinarith [mul_lt_mul_of_pos_left hs.1 hR]
  rw [← capLateralDensity_const_mul_tgn]
  simp only [capLateralDensity]
  congr 1
  refine integral_congr_ae (Filter.Eventually.of_forall fun ω => ?_)
  show trAbs_tga hR hL tdm tdp hb u
        (-L / 2 - R * s, R • Cm.θ s • (ω : EuclideanSpace ℝ (Fin m)))
      * trAbs_tga hR hL tdm tdp hb v
        (-L / 2 - R * s, R • Cm.θ s • (ω : EuclideanSpace ℝ (Fin m)))
      = (capC_tga m R)⁻¹ ^ 2 * (tdm.trΓ (capLeft hR hL (capC_tga m R) u)
          (s, Cm.θ s • (ω : EuclideanSpace ℝ (Fin m)))
        * tdm.trΓ (capLeft hR hL (capC_tga m R) v)
          (s, Cm.θ s • (ω : EuclideanSpace ℝ (Fin m))))
  rw [trAbs_eq_capTraceL_of_lt_tga hR hL tdm tdp hb u hlt,
    trAbs_eq_capTraceL_of_lt_tga hR hL tdm tdp hb v hlt,
    capTraceL_affineL_tga hR hL tdm u (s, Cm.θ s • (ω : EuclideanSpace ℝ (Fin m))),
    capTraceL_affineL_tga hR hL tdm v (s, Cm.θ s • (ω : EuclideanSpace ℝ (Fin m)))]
  ring

theorem capLateralDensity_right_eq_tga (tdm : CapTraceData Cm) (tdp : CapTraceData Cp)
    (hb : BulkTraceInput_tgn m Cm Cp L R hR hL) (u v : H1P (thinDomain Cm Cp L R)) (s : ℝ)
    (hs : s ∈ Ioo (-Cp.K) 0) :
    capLateralDensity Cp
        (fun p => trAbs_tga hR hL tdm tdp hb u (L / 2 + R * p.1, R • p.2)
          * trAbs_tga hR hL tdm tdp hb v (L / 2 + R * p.1, R • p.2)) s
      = (capC_tga m R)⁻¹ ^ 2 * capLateralDensity Cp
          (fun p => tdp.trΓ (capRight hR hL (capC_tga m R) u) p
            * tdp.trΓ (capRight hR hL (capC_tga m R) v) p) s := by
  have hgt : interfaceR Cp L R < L / 2 + R * s := by
    show L / 2 - Cp.K * R < L / 2 + R * s
    nlinarith [mul_lt_mul_of_pos_left hs.1 hR]
  have hnlt : ¬ L / 2 + R * s < interfaceL Cm L R := by
    have hmid : interfaceL Cm L R < interfaceR Cp L R := interface_lt (Cm := Cm) (Cp := Cp) hR hL
    exact not_lt.2 (le_of_lt (lt_trans hmid hgt))
  rw [← capLateralDensity_const_mul_tgn]
  simp only [capLateralDensity]
  congr 1
  refine integral_congr_ae (Filter.Eventually.of_forall fun ω => ?_)
  show trAbs_tga hR hL tdm tdp hb u
        (L / 2 + R * s, R • Cp.θ s • (ω : EuclideanSpace ℝ (Fin m)))
      * trAbs_tga hR hL tdm tdp hb v
        (L / 2 + R * s, R • Cp.θ s • (ω : EuclideanSpace ℝ (Fin m)))
      = (capC_tga m R)⁻¹ ^ 2 * (tdp.trΓ (capRight hR hL (capC_tga m R) u)
          (s, Cp.θ s • (ω : EuclideanSpace ℝ (Fin m)))
        * tdp.trΓ (capRight hR hL (capC_tga m R) v)
          (s, Cp.θ s • (ω : EuclideanSpace ℝ (Fin m))))
  rw [trAbs_eq_capTraceR_of_gt_tga hR hL tdm tdp hb u hnlt hgt,
    trAbs_eq_capTraceR_of_gt_tga hR hL tdm tdp hb v hnlt hgt,
    capTraceR_affineR_tga hR hL tdp u (s, Cp.θ s • (ω : EuclideanSpace ℝ (Fin m))),
    capTraceR_affineR_tga hR hL tdp v (s, Cp.θ s • (ω : EuclideanSpace ℝ (Fin m)))]
  ring

/-- **The left terminal-disc density identity**, the disc analogue of
`capLateralDensity_left_eq_tga` at the tip point `x = -L/2` (i.e. `s = 0`). -/
theorem capTraceL_disc_eq_tga (tdm : CapTraceData Cm) (tdp : CapTraceData Cp)
    (hb : BulkTraceInput_tgn m Cm Cp L R hR hL) (u v : H1P (thinDomain Cm Cp L R)) :
    (∫ z in ball (0 : EuclideanSpace ℝ (Fin m)) (Cm.θ 0),
        trAbs_tga hR hL tdm tdp hb u (-L / 2, R • z)
          * trAbs_tga hR hL tdm tdp hb v (-L / 2, R • z))
      = (capC_tga m R)⁻¹ ^ 2 * ∫ z in ball (0 : EuclideanSpace ℝ (Fin m)) (Cm.θ 0),
          tdm.trΓ (capLeft hR hL (capC_tga m R) u) (0, z)
            * tdm.trΓ (capLeft hR hL (capC_tga m R) v) (0, z) := by
  have hlt : (-L / 2 : ℝ) < interfaceL Cm L R := left_lt_interface (Cm := Cm) (L := L) hR
  have hpt : ∀ z : EuclideanSpace ℝ (Fin m),
      trAbs_tga hR hL tdm tdp hb u (-L / 2, R • z) * trAbs_tga hR hL tdm tdp hb v (-L / 2, R • z)
        = (capC_tga m R)⁻¹ ^ 2 * (tdm.trΓ (capLeft hR hL (capC_tga m R) u) (0, z)
            * tdm.trΓ (capLeft hR hL (capC_tga m R) v) (0, z)) := by
    intro z
    rw [trAbs_eq_capTraceL_of_lt_tga hR hL tdm tdp hb u hlt,
      trAbs_eq_capTraceL_of_lt_tga hR hL tdm tdp hb v hlt]
    have e1 := capTraceL_affineL_tga hR hL tdm u (0, z)
    have e2 := capTraceL_affineL_tga hR hL tdm v (0, z)
    simp only [mul_zero, sub_zero] at e1 e2
    rw [e1, e2]
    ring
  rw [setIntegral_congr_fun measurableSet_ball (fun z _ => hpt z), integral_const_mul]

/-- **The right terminal-disc density identity**, at the tip point `x = L/2`. -/
theorem capTraceR_disc_eq_tga (tdm : CapTraceData Cm) (tdp : CapTraceData Cp)
    (hb : BulkTraceInput_tgn m Cm Cp L R hR hL) (u v : H1P (thinDomain Cm Cp L R)) :
    (∫ z in ball (0 : EuclideanSpace ℝ (Fin m)) (Cp.θ 0),
        trAbs_tga hR hL tdm tdp hb u (L / 2, R • z)
          * trAbs_tga hR hL tdm tdp hb v (L / 2, R • z))
      = (capC_tga m R)⁻¹ ^ 2 * ∫ z in ball (0 : EuclideanSpace ℝ (Fin m)) (Cp.θ 0),
          tdp.trΓ (capRight hR hL (capC_tga m R) u) (0, z)
            * tdp.trΓ (capRight hR hL (capC_tga m R) v) (0, z) := by
  have hgt : interfaceR Cp L R < (L / 2 : ℝ) := interface_lt_right (Cp := Cp) (L := L) hR
  have hpt : ∀ z : EuclideanSpace ℝ (Fin m),
      trAbs_tga hR hL tdm tdp hb u (L / 2, R • z) * trAbs_tga hR hL tdm tdp hb v (L / 2, R • z)
        = (capC_tga m R)⁻¹ ^ 2 * (tdp.trΓ (capRight hR hL (capC_tga m R) u) (0, z)
            * tdp.trΓ (capRight hR hL (capC_tga m R) v) (0, z)) := by
    intro z
    have hnlt : ¬ (L / 2 : ℝ) < interfaceL Cm L R := by
      have hmid : interfaceL Cm L R < interfaceR Cp L R := interface_lt (Cm := Cm) (Cp := Cp) hR hL
      exact not_lt.2 (le_of_lt (lt_trans hmid hgt))
    rw [trAbs_eq_capTraceR_of_gt_tga hR hL tdm tdp hb u hnlt hgt,
      trAbs_eq_capTraceR_of_gt_tga hR hL tdm tdp hb v hnlt hgt]
    have e1 := capTraceR_affineR_tga hR hL tdp u (0, z)
    have e2 := capTraceR_affineR_tga hR hL tdp v (0, z)
    simp only [mul_zero, add_zero] at e1 e2
    rw [e1, e2]
    ring
  rw [setIntegral_congr_fun measurableSet_ball (fun z _ => hpt z), integral_const_mul]

theorem intervalIntegrable_lateralDensity_left_tga (tdm : CapTraceData Cm) (tdp : CapTraceData Cp)
    (hb : BulkTraceInput_tgn m Cm Cp L R hR hL) (hcim : CapTraceIntegrableAbs_tga Cm tdm)
    (u v : H1P (thinDomain Cm Cp L R)) :
    IntervalIntegrable (lateralDensity Cm Cp L R
        (fun p => trAbs_tga hR hL tdm tdp hb u p * trAbs_tga hR hL tdm tdp hb v p)) volume
      (-L / 2) (-L / 2 + Cm.K * R) := by
  have hl := left_lt_interface (Cm := Cm) (L := L) hR
  have hF : IntervalIntegrable (capLateralDensity Cm
      (fun p => trAbs_tga hR hL tdm tdp hb u (-L / 2 - R * p.1, R • p.2)
        * trAbs_tga hR hL tdm tdp hb v (-L / 2 - R * p.1, R • p.2))) volume (-Cm.K) 0 := by
    rw [intervalIntegrable_iff_integrableOn_Ioo_of_le (by linarith [Cm.hK] : (-Cm.K : ℝ) ≤ 0)]
    refine IntegrableOn.congr_fun ((hcim.integrableOn (capLeft hR hL (capC_tga m R) u)
      (capLeft hR hL (capC_tga m R) v)).const_mul ((capC_tga m R)⁻¹ ^ 2)) ?_ measurableSet_Ioo
    intro s hs
    exact (capLateralDensity_left_eq_tga hR hL tdm tdp hb u v s hs).symm
  have h4 := (intervalIntegrable_comp_left Cm.K R L hR hF).const_mul (R ^ (m - 1))
  rw [intervalIntegrable_iff_integrableOn_Ioo_of_le hl.le] at h4 ⊢
  refine IntegrableOn.congr_fun h4 (fun x hx => ?_) measurableSet_Ioo
  exact (lateralDensity_left_eq (Cp := Cp) hR
    (fun p => trAbs_tga hR hL tdm tdp hb u p * trAbs_tga hR hL tdm tdp hb v p) hx.2).symm

theorem intervalIntegrable_lateralDensity_right_tga (tdm : CapTraceData Cm) (tdp : CapTraceData Cp)
    (hb : BulkTraceInput_tgn m Cm Cp L R hR hL) (hcip : CapTraceIntegrableAbs_tga Cp tdp)
    (u v : H1P (thinDomain Cm Cp L R)) :
    IntervalIntegrable (lateralDensity Cm Cp L R
        (fun p => trAbs_tga hR hL tdm tdp hb u p * trAbs_tga hR hL tdm tdp hb v p)) volume
      (L / 2 - Cp.K * R) (L / 2) := by
  have hr := interface_lt_right (Cp := Cp) (L := L) hR
  have hF : IntervalIntegrable (capLateralDensity Cp
      (fun p => trAbs_tga hR hL tdm tdp hb u (L / 2 + R * p.1, R • p.2)
        * trAbs_tga hR hL tdm tdp hb v (L / 2 + R * p.1, R • p.2))) volume (-Cp.K) 0 := by
    rw [intervalIntegrable_iff_integrableOn_Ioo_of_le (by linarith [Cp.hK] : (-Cp.K : ℝ) ≤ 0)]
    refine IntegrableOn.congr_fun ((hcip.integrableOn (capRight hR hL (capC_tga m R) u)
      (capRight hR hL (capC_tga m R) v)).const_mul ((capC_tga m R)⁻¹ ^ 2)) ?_ measurableSet_Ioo
    intro s hs
    exact (capLateralDensity_right_eq_tga hR hL tdm tdp hb u v s hs).symm
  have h4 := (intervalIntegrable_comp_right Cp.K R L hR hF).const_mul (R ^ (m - 1))
  rw [intervalIntegrable_iff_integrableOn_Ioo_of_le hr.le] at h4 ⊢
  refine IntegrableOn.congr_fun h4 (fun x hx => ?_) measurableSet_Ioo
  exact (lateralDensity_right_eq (Cm := Cm) hR hL
    (fun p => trAbs_tga hR hL tdm tdp hb u p * trAbs_tga hR hL tdm tdp hb v p) hx.1).symm

/-- **The bulk lateral density of `trAbs`'s product is a.e. the bulk lateral density of the raw
bulk trace's product.** -/
theorem ae_lateralDensity_bulk_eq_tga (tdm : CapTraceData Cm) (tdp : CapTraceData Cp)
    (hb : BulkTraceInput_tgn m Cm Cp L R hR hL) (u v : H1P (thinDomain Cm Cp L R)) :
    ∀ᵐ x ∂(volume.restrict (Ioo (interfaceL Cm L R) (interfaceR Cp L R))),
      lateralDensity Cm Cp L R
          (fun p => trAbs_tga hR hL tdm tdp hb u p * trAbs_tga hR hL tdm tdp hb v p) x
        = lateralDensity Cm Cp L R (fun p => bulkTrace_tgn hb u p * bulkTrace_tgn hb v p) x := by
  have hau := bulkTraceL_ae_tgn hb u
  have hav := bulkTraceL_ae_tgn hb v
  have hprod : ∀ᵐ p : ℝ × sphere (0 : EuclideanSpace ℝ (Fin m)) 1
      ∂((volume.restrict (Ioo (interfaceL Cm L R) (interfaceR Cp L R))).prod (sphereMeasure m)),
      bulkTraceL_tgn hb u (p.1, R • (p.2 : EuclideanSpace ℝ (Fin m)))
          * bulkTraceL_tgn hb v (p.1, R • (p.2 : EuclideanSpace ℝ (Fin m)))
        = bulkTrace_tgn hb u (p.1, R • (p.2 : EuclideanSpace ℝ (Fin m)))
          * bulkTrace_tgn hb v (p.1, R • (p.2 : EuclideanSpace ℝ (Fin m))) := by
    filter_upwards [hau, hav] with p h1 h2
    rw [h1, h2]
  have hae_x := Measure.ae_ae_of_ae_prod hprod
  filter_upwards [hae_x, ae_restrict_mem measurableSet_Ioo] with x hx hxI
  rw [lateralDensity_bulk _ hxI.1 hxI.2, lateralDensity_bulk _ hxI.1 hxI.2]
  congr 1
  refine integral_congr_ae ?_
  filter_upwards [hx] with ω hω
  have hp1 : ¬ x < interfaceL Cm L R := not_lt.2 hxI.1.le
  have hp2 : ¬ interfaceR Cp L R < x := not_lt.2 hxI.2.le
  rw [trAbs_eq_bulkTraceL_tga hR hL tdm tdp hb u hp1 hp2,
    trAbs_eq_bulkTraceL_tga hR hL tdm tdp hb v hp1 hp2]
  exact hω

theorem intervalIntegrable_lateralDensity_bulk_tga (tdm : CapTraceData Cm) (tdp : CapTraceData Cp)
    (hb : BulkTraceInput_tgn m Cm Cp L R hR hL) (u v : H1P (thinDomain Cm Cp L R)) :
    IntervalIntegrable (lateralDensity Cm Cp L R
        (fun p => trAbs_tga hR hL tdm tdp hb u p * trAbs_tga hR hL tdm tdp hb v p)) volume
      (interfaceL Cm L R) (interfaceR Cp L R) := by
  have hmid := interface_lt (Cm := Cm) (Cp := Cp) hR hL
  show IntervalIntegrable (lateralDensity Cm Cp L R
      (fun p => trAbs_tga hR hL tdm tdp hb u p * trAbs_tga hR hL tdm tdp hb v p)) volume
    (-L / 2 + Cm.K * R) (L / 2 - Cp.K * R)
  rw [intervalIntegrable_iff_integrableOn_Ioo_of_le hmid.le]
  exact (bulkTrace_integrableOn_tgn hb u v).congr
    ((ae_lateralDensity_bulk_eq_tga hR hL tdm tdp hb u v).mono fun _ h => h.symm)

/-- **Deliverable.  `bd_eq`.**  The bilinear boundary form `bdAbs` is the concrete revolution
boundary integral of the product of the boundary representatives `trAbs`. -/
theorem bd_eq_tga (hm : 1 ≤ m) (tdm : CapTraceData Cm) (tdp : CapTraceData Cp)
    (hb : BulkTraceInput_tgn m Cm Cp L R hR hL) (hcim : CapTraceIntegrableAbs_tga Cm tdm)
    (hcip : CapTraceIntegrableAbs_tga Cp tdp) (u v : H1P (thinDomain Cm Cp L R)) :
    bdAbs_tga hR hL tdm tdp hb u v
      = boundaryIntegral Cm Cp L R
          (fun p => trAbs_tga hR hL tdm tdp hb u p * trAbs_tga hR hL tdm tdp hb v p) := by
  have h1 : IntegrableOn (lateralDensity Cm Cp L R
        (fun p => trAbs_tga hR hL tdm tdp hb u p * trAbs_tga hR hL tdm tdp hb v p))
      (Ioo (-L / 2) (-L / 2 + Cm.K * R)) :=
    (intervalIntegrable_iff_integrableOn_Ioo_of_le
      (left_lt_interface (Cm := Cm) (L := L) hR).le).1
      (intervalIntegrable_lateralDensity_left_tga hR hL tdm tdp hb hcim u v)
  have h2 : IntegrableOn (lateralDensity Cm Cp L R
        (fun p => trAbs_tga hR hL tdm tdp hb u p * trAbs_tga hR hL tdm tdp hb v p))
      (Ioo (-L / 2 + Cm.K * R) (L / 2 - Cp.K * R)) :=
    (intervalIntegrable_iff_integrableOn_Ioo_of_le
      (interface_lt (Cm := Cm) (Cp := Cp) hR hL).le).1
      (intervalIntegrable_lateralDensity_bulk_tga hR hL tdm tdp hb u v)
  have h3 : IntegrableOn (lateralDensity Cm Cp L R
        (fun p => trAbs_tga hR hL tdm tdp hb u p * trAbs_tga hR hL tdm tdp hb v p))
      (Ioo (L / 2 - Cp.K * R) (L / 2)) :=
    (intervalIntegrable_iff_integrableOn_Ioo_of_le
      (interface_lt_right (Cp := Cp) (L := L) hR).le).1
      (intervalIntegrable_lateralDensity_right_tga hR hL tdm tdp hb hcip u v)
  rw [bdAbs_apply_tga, boundaryIntegral_split hm hR hL _ h1 h2 h3]
  have hleft : R ^ m * (capLateralIntegral Cm
        (fun p => trAbs_tga hR hL tdm tdp hb u (-L / 2 - R * p.1, R • p.2)
          * trAbs_tga hR hL tdm tdp hb v (-L / 2 - R * p.1, R • p.2))
      + ∫ z in ball (0 : EuclideanSpace ℝ (Fin m)) (Cm.θ 0),
          trAbs_tga hR hL tdm tdp hb u (-L / 2, R • z)
            * trAbs_tga hR hL tdm tdp hb v (-L / 2, R • z))
      = bdCapL_tga hR hL tdm u v := by
    have hlat : capLateralIntegral Cm
        (fun p => trAbs_tga hR hL tdm tdp hb u (-L / 2 - R * p.1, R • p.2)
          * trAbs_tga hR hL tdm tdp hb v (-L / 2 - R * p.1, R • p.2))
        = (capC_tga m R)⁻¹ ^ 2 * capLateralIntegral Cm
            (fun p => tdm.trΓ (capLeft hR hL (capC_tga m R) u) p
              * tdm.trΓ (capLeft hR hL (capC_tga m R) v) p) := by
      rw [capLateralIntegral,
        setIntegral_congr_fun measurableSet_Ioo
          (fun s hs => capLateralDensity_left_eq_tga hR hL tdm tdp hb u v s hs),
        integral_const_mul, ← capLateralIntegral]
    rw [hlat, capTraceL_disc_eq_tga hR hL tdm tdp hb u v, bdCapL_tga, tdm.bdΓ_eq, capGammaPair]
    ring
  have hright : R ^ m * (capLateralIntegral Cp
        (fun p => trAbs_tga hR hL tdm tdp hb u (L / 2 + R * p.1, R • p.2)
          * trAbs_tga hR hL tdm tdp hb v (L / 2 + R * p.1, R • p.2))
      + ∫ z in ball (0 : EuclideanSpace ℝ (Fin m)) (Cp.θ 0),
          trAbs_tga hR hL tdm tdp hb u (L / 2, R • z)
            * trAbs_tga hR hL tdm tdp hb v (L / 2, R • z))
      = bdCapR_tga hR hL tdp u v := by
    have hlat : capLateralIntegral Cp
        (fun p => trAbs_tga hR hL tdm tdp hb u (L / 2 + R * p.1, R • p.2)
          * trAbs_tga hR hL tdm tdp hb v (L / 2 + R * p.1, R • p.2))
        = (capC_tga m R)⁻¹ ^ 2 * capLateralIntegral Cp
            (fun p => tdp.trΓ (capRight hR hL (capC_tga m R) u) p
              * tdp.trΓ (capRight hR hL (capC_tga m R) v) p) := by
      rw [capLateralIntegral,
        setIntegral_congr_fun measurableSet_Ioo
          (fun s hs => capLateralDensity_right_eq_tga hR hL tdm tdp hb u v s hs),
        integral_const_mul, ← capLateralIntegral]
    rw [hlat, capTraceR_disc_eq_tga hR hL tdm tdp hb u v, bdCapR_tga, tdp.bdΓ_eq, capGammaPair]
    ring
  rw [hleft, hright]
  have hbulk : (∫ x in Icc (-L / 2 + Cm.K * R) (L / 2 - Cp.K * R),
      lateralDensity Cm Cp L R
        (fun p => trAbs_tga hR hL tdm tdp hb u p * trAbs_tga hR hL tdm tdp hb v p) x)
      = bdCyl (bdR m R) (restrictBulkP hR u) (restrictBulkP hR v) := by
    rw [integral_Icc_eq_integral_Ioo]
    show (∫ x in Ioo (interfaceL Cm L R) (interfaceR Cp L R),
        lateralDensity Cm Cp L R
          (fun p => trAbs_tga hR hL tdm tdp hb u p * trAbs_tga hR hL tdm tdp hb v p) x)
        = bdCyl (bdR m R) (restrictBulkP hR u) (restrictBulkP hR v)
    rw [integral_congr_ae (ae_lateralDensity_bulk_eq_tga hR hL tdm tdp hb u v),
      bulkTrace_eq_bdCyl_tgn hb]
  rw [hbulk]
  ring

/-! ## 8. `tr_continuous` -/

/-- The left-cap piece of `bdAbs`'s diagonal is the left-cap piece of the honest boundary energy
of `u.toFun`, for a representative continuous up to the boundary — **lateral surface plus
terminal disc**, matching `RobinCaps.ThinDomain.boundaryIntegral_split`'s own grouping of the cap
piece exactly. -/
theorem bdCapL_eq_left_lateral_disc_tga (tdm : CapTraceData Cm) (u : H1P (thinDomain Cm Cp L R))
    (hc : ContinuousOn u.toFun (closure (thinDomain Cm Cp L R))) :
    bdCapL_tga hR hL tdm u u = R ^ m * (capLateralIntegral Cm
        (fun p => u.toFun (-L / 2 - R * p.1, R • p.2) ^ 2)
      + ∫ z in ball (0 : EuclideanSpace ℝ (Fin m)) (Cm.θ 0), u.toFun (-L / 2, R • z) ^ 2) := by
  rw [bdCapL_tga, tdm.trΓ_continuous _ (capLeft_continuousOn_tga hR hL hc), capBoundary]
  have hpt : (fun p : CapSpace m => (capLeft hR hL (capC_tga m R) u).toFun p ^ 2)
      = fun p => capC_tga m R ^ 2 * u.toFun (-L / 2 - R * p.1, R • p.2) ^ 2 := by
    funext p
    rw [capLeft_toFun_eq_tga]
    ring
  rw [hpt, capLateralIntegral_const_mul_tgn]
  have hdisc : (∫ z in ball (0 : EuclideanSpace ℝ (Fin m)) (Cm.θ 0),
      (capLeft hR hL (capC_tga m R) u).toFun (0, z) ^ 2)
      = capC_tga m R ^ 2 * ∫ z in ball (0 : EuclideanSpace ℝ (Fin m)) (Cm.θ 0),
          u.toFun (-L / 2, R • z) ^ 2 := by
    have hpt2 : ∀ z : EuclideanSpace ℝ (Fin m),
        (capLeft hR hL (capC_tga m R) u).toFun (0, z) ^ 2
          = capC_tga m R ^ 2 * u.toFun (-L / 2, R • z) ^ 2 := by
      intro z
      have e := capLeft_toFun_eq_tga hR hL u (0, z)
      simp only [mul_zero, sub_zero] at e
      rw [e]
      ring
    rw [setIntegral_congr_fun measurableSet_ball (fun z _ => hpt2 z), integral_const_mul]
  rw [hdisc]
  exact capC_cancel_add_tga m hR _ _

/-- The right-cap piece, mirrored. -/
theorem bdCapR_eq_right_lateral_disc_tga (tdp : CapTraceData Cp) (u : H1P (thinDomain Cm Cp L R))
    (hc : ContinuousOn u.toFun (closure (thinDomain Cm Cp L R))) :
    bdCapR_tga hR hL tdp u u = R ^ m * (capLateralIntegral Cp
        (fun p => u.toFun (L / 2 + R * p.1, R • p.2) ^ 2)
      + ∫ z in ball (0 : EuclideanSpace ℝ (Fin m)) (Cp.θ 0), u.toFun (L / 2, R • z) ^ 2) := by
  rw [bdCapR_tga, tdp.trΓ_continuous _ (capRight_continuousOn_tga hR hL hc), capBoundary]
  have hpt : (fun p : CapSpace m => (capRight hR hL (capC_tga m R) u).toFun p ^ 2)
      = fun p => capC_tga m R ^ 2 * u.toFun (L / 2 + R * p.1, R • p.2) ^ 2 := by
    funext p
    rw [capRight_toFun_eq_tga]
    ring
  rw [hpt, capLateralIntegral_const_mul_tgn]
  have hdisc : (∫ z in ball (0 : EuclideanSpace ℝ (Fin m)) (Cp.θ 0),
      (capRight hR hL (capC_tga m R) u).toFun (0, z) ^ 2)
      = capC_tga m R ^ 2 * ∫ z in ball (0 : EuclideanSpace ℝ (Fin m)) (Cp.θ 0),
          u.toFun (L / 2, R • z) ^ 2 := by
    have hpt2 : ∀ z : EuclideanSpace ℝ (Fin m),
        (capRight hR hL (capC_tga m R) u).toFun (0, z) ^ 2
          = capC_tga m R ^ 2 * u.toFun (L / 2, R • z) ^ 2 := by
      intro z
      have e := capRight_toFun_eq_tga hR hL u (0, z)
      simp only [mul_zero, add_zero] at e
      rw [e]
      ring
    rw [setIntegral_congr_fun measurableSet_ball (fun z _ => hpt2 z), integral_const_mul]
  rw [hdisc]
  exact capC_cancel_add_tga m hR _ _

/-- The bulk piece of `bdAbs`'s diagonal is the bulk piece of the honest boundary energy, for a
representative continuous up to the boundary. -/
theorem bdCyl_eq_bulk_lateral_tga (tdm : CapTraceData Cm) (tdp : CapTraceData Cp)
    (hb : BulkTraceInput_tgn m Cm Cp L R hR hL) (u : H1P (thinDomain Cm Cp L R))
    (hc : ContinuousOn u.toFun (closure (thinDomain Cm Cp L R))) :
    bdCyl (bdR m R) (restrictBulkP hR u) (restrictBulkP hR u)
      = ∫ x in Icc (-L / 2 + Cm.K * R) (L / 2 - Cp.K * R),
          lateralDensity Cm Cp L R (fun p => u.toFun p ^ 2) x := by
  rw [← bulkTrace_eq_bdCyl_tgn hb u u, integral_Icc_eq_integral_Ioo]
  show (∫ x in Ioo (interfaceL Cm L R) (interfaceR Cp L R),
      lateralDensity Cm Cp L R
        (fun p => bulkTrace_tgn hb u p * bulkTrace_tgn hb u p) x)
      = ∫ x in Ioo (interfaceL Cm L R) (interfaceR Cp L R),
          lateralDensity Cm Cp L R (fun p => u.toFun p ^ 2) x
  refine integral_congr_ae ?_
  have hcont := bulkTrace_continuous_ae_tgn hb u hc
  have hprod : ∀ᵐ p : ℝ × sphere (0 : EuclideanSpace ℝ (Fin m)) 1
      ∂((volume.restrict (Ioo (interfaceL Cm L R) (interfaceR Cp L R))).prod (sphereMeasure m)),
      bulkTrace_tgn hb u (p.1, R • (p.2 : EuclideanSpace ℝ (Fin m)))
          * bulkTrace_tgn hb u (p.1, R • (p.2 : EuclideanSpace ℝ (Fin m)))
        = u.toFun (p.1, R • (p.2 : EuclideanSpace ℝ (Fin m))) ^ 2 := by
    filter_upwards [hcont] with p h1
    rw [h1]; ring
  have hae_x := Measure.ae_ae_of_ae_prod hprod
  filter_upwards [hae_x, ae_restrict_mem measurableSet_Ioo] with x hx hxI
  rw [lateralDensity_bulk _ hxI.1 hxI.2, lateralDensity_bulk _ hxI.1 hxI.2]
  congr 1
  exact integral_congr_ae hx

/-- **`tr_continuous`.**  On functions continuous up to the boundary, `bdAbs u u` is the honest
surface energy `boundaryEnergy (...) u.toFun`. -/
theorem tr_continuous_tga (hm : 1 ≤ m) (tdm : CapTraceData Cm) (tdp : CapTraceData Cp)
    (hb : BulkTraceInput_tgn m Cm Cp L R hR hL) (u : H1P (thinDomain Cm Cp L R))
    (hc : ContinuousOn u.toFun (closure (thinDomain Cm Cp L R)))
    (hi : IntegrableOn (lateralDensity Cm Cp L R (fun p => u.toFun p ^ 2))
        (Ioo (-L / 2) (-L / 2 + Cm.K * R)) ∧
      IntegrableOn (lateralDensity Cm Cp L R (fun p => u.toFun p ^ 2))
        (Ioo (-L / 2 + Cm.K * R) (L / 2 - Cp.K * R)) ∧
      IntegrableOn (lateralDensity Cm Cp L R (fun p => u.toFun p ^ 2))
        (Ioo (L / 2 - Cp.K * R) (L / 2))) :
    bdAbs_tga hR hL tdm tdp hb u u = boundaryEnergy Cm Cp L R u.toFun := by
  rw [bdAbs_apply_tga, bdCapL_eq_left_lateral_disc_tga hR hL tdm u hc,
    bdCyl_eq_bulk_lateral_tga hR hL tdm tdp hb u hc, bdCapR_eq_right_lateral_disc_tga hR hL tdp u hc]
  rw [boundaryEnergy, boundaryIntegral_split hm hR hL _ hi.1 hi.2.1 hi.2.2]
  ring

/-! ## 9. Assembly: the trace datum -/

/-- **A second, narrowly-scoped remaining hypothesis**, needed only for `tr_continuous`: for a
representative continuous up to the boundary, the lateral density of its own square `u.toFun ^ 2`
is genuinely Bochner-integrable on each of the three axial pieces. Mirrors
`RobinCaps.ThinDomain.TraceGen.ContinuousBoundaryIntegrable_tgn`, generalised to two abstract
caps. -/
structure ContinuousBoundaryIntegrableAbs_tga (m : ℕ) (Cm Cp : Cap m) (L R : ℝ) (hR : 0 < R)
    (hL : (Cm.K + Cp.K) * R < L) : Prop where
  integrableOn : ∀ u : H1P (thinDomain Cm Cp L R),
    ContinuousOn u.toFun (closure (thinDomain Cm Cp L R)) →
    IntegrableOn (lateralDensity Cm Cp L R (fun p => u.toFun p ^ 2))
        (Ioo (-L / 2) (-L / 2 + Cm.K * R)) ∧
    IntegrableOn (lateralDensity Cm Cp L R (fun p => u.toFun p ^ 2))
      (Ioo (-L / 2 + Cm.K * R) (L / 2 - Cp.K * R)) ∧
    IntegrableOn (lateralDensity Cm Cp L R (fun p => u.toFun p ^ 2))
        (Ioo (L / 2 - Cp.K * R) (L / 2))

/-- **Deliverable.  The trace datum of the thin domain, for two abstract admissible caps.**
Assembled from the cap `Γ`-traces of `tdm` / `tdp` (transported to `Ω_R` via `capLeft` /
`capRight`), the bulk trace interface `hb`, and the two remaining Fubini/polar-coordinates facts
`CapTraceIntegrableAbs_tga` / `ContinuousBoundaryIntegrableAbs_tga`. -/
def traceDataAbs_tga (hm : 1 ≤ m) (hR : 0 < R) (hL : (Cm.K + Cp.K) * R < L)
    (tdm : CapTraceData Cm) (tdp : CapTraceData Cp)
    (hb : BulkTraceInput_tgn m Cm Cp L R hR hL)
    (hcim : CapTraceIntegrableAbs_tga Cm tdm) (hcip : CapTraceIntegrableAbs_tga Cp tdp)
    (hcbi : ContinuousBoundaryIntegrableAbs_tga m Cm Cp L R hR hL) : TraceData Cm Cp L R where
  tr := trAbs_tga hR hL tdm tdp hb
  tr_add := trAbs_add_tga hR hL tdm tdp hb
  tr_smul := trAbs_smul_tga hR hL tdm tdp hb
  bd := bdAbs_tga hR hL tdm tdp hb
  bd_eq := bd_eq_tga hR hL hm tdm tdp hb hcim hcip
  bd_symm := bdAbs_symm_tga hR hL tdm tdp hb
  bd_nonneg := bdAbs_nonneg_tga hR hL hm tdm tdp hb
  tr_continuous := fun u hc => tr_continuous_tga hR hL hm tdm tdp hb u hc (hcbi.integrableOn u hc)
  trace_ineq := bdAbs_trace_ineq_tga hR hL tdm tdp hb
  vanishes_ae := bdAbs_vanishes_ae_tga hR hL tdm tdp hb

/-- **Deliverable.  The trace split.**  The boundary form splits into the left-cap piece, the bulk
cylinder form `bdCyl (bdR m R)` of the bulk restriction, and the right-cap piece — definitional
from the construction of `bdAbs_tga`. -/
theorem traceSplit_tga (hm : 1 ≤ m) (hR : 0 < R) (hL : (Cm.K + Cp.K) * R < L)
    (tdm : CapTraceData Cm) (tdp : CapTraceData Cp) (hb : BulkTraceInput_tgn m Cm Cp L R hR hL)
    (hcim : CapTraceIntegrableAbs_tga Cm tdm) (hcip : CapTraceIntegrableAbs_tga Cp tdp)
    (hcbi : ContinuousBoundaryIntegrableAbs_tga m Cm Cp L R hR hL)
    (u : H1P (thinDomain Cm Cp L R)) :
    (traceDataAbs_tga hm hR hL tdm tdp hb hcim hcip hcbi).bd u u
      = bdCapL_tga hR hL tdm u u + bdCyl (bdR m R) (restrictBulkP hR u) (restrictBulkP hR u)
        + bdCapR_tga hR hL tdp u u :=
  bdAbs_apply_tga hR hL tdm tdp hb u u

/-- The two cap pieces of the trace split are individually nonnegative. -/
theorem traceSplit_capL_nonneg_tga (tdm : CapTraceData Cm) (u : H1P (thinDomain Cm Cp L R)) :
    0 ≤ bdCapL_tga hR hL tdm u u := bdCapL_nonneg_tga hR hL tdm u

theorem traceSplit_capR_nonneg_tga (tdp : CapTraceData Cp) (u : H1P (thinDomain Cm Cp L R)) :
    0 ≤ bdCapR_tga hR hL tdp u u := bdCapR_nonneg_tga hR hL tdp u

/-- The bulk piece of the trace split is also nonnegative. -/
theorem traceSplit_bulk_nonneg_tga (hm : 1 ≤ m) (u : H1P (thinDomain Cm Cp L R)) :
    0 ≤ bdCyl (bdR m R) (restrictBulkP hR u) (restrictBulkP hR u) :=
  bdCyl_nonneg_tgn (fun x => bdR_nonneg hm hR x) _

/-- **The trace exists for the thin domain, for two abstract admissible caps**, granted the bulk
trace interface and the two Fubini/polar-coordinates facts. -/
theorem hasTraceData_abs_tga (hm : 1 ≤ m) (hR : 0 < R) (hL : (Cm.K + Cp.K) * R < L)
    (tdm : CapTraceData Cm) (tdp : CapTraceData Cp) (hb : BulkTraceInput_tgn m Cm Cp L R hR hL)
    (hcim : CapTraceIntegrableAbs_tga Cm tdm) (hcip : CapTraceIntegrableAbs_tga Cp tdp)
    (hcbi : ContinuousBoundaryIntegrableAbs_tga m Cm Cp L R hR hL) : HasTraceData Cm Cp L R :=
  ⟨traceDataAbs_tga hm hR hL tdm tdp hb hcim hcip hcbi⟩

/-! ## 10. Optional consistency check with `RobinCaps.ThinDomain.TraceGen` at the hemisphere -/

theorem capC_tga_eq_capC_tgn (m : ℕ) {R : ℝ} (hR : 0 < R) : capC_tga m R = capC_tgn m R := by
  rw [capC_tgn]
  exact rpow_half_eq_sqrt_tga m hR

theorem bdCapL_eq_tgn_tga (hm : 1 ≤ m) (hR : 0 < R)
    (hL : ((Cap.hemisphere m).K + (Cap.hemisphere m).K) * R < L)
    (u v : H1P (thinDomain (Cap.hemisphere m) (Cap.hemisphere m) L R)) :
    bdCapL_tga hR hL (capTraceDataHemi_th m hm) u v = bdCapL_tgn hm hR hL u v := by
  rw [bdCapL_tga, bdCapL_tgn, capC_tga_eq_capC_tgn m hR]

theorem bdCapR_eq_tgn_tga (hm : 1 ≤ m) (hR : 0 < R)
    (hL : ((Cap.hemisphere m).K + (Cap.hemisphere m).K) * R < L)
    (u v : H1P (thinDomain (Cap.hemisphere m) (Cap.hemisphere m) L R)) :
    bdCapR_tga hR hL (capTraceDataHemi_th m hm) u v = bdCapR_tgn hm hR hL u v := by
  rw [bdCapR_tga, bdCapR_tgn, capC_tga_eq_capC_tgn m hR]

/-- **Consistency.**  At `Cm = Cp = Cap.hemisphere m` with `tdm = tdp = capTraceDataHemi_th m hm`,
`bdAbs_tga` agrees with `RobinCaps.ThinDomain.TraceGen.bdGen_tgn` — hence `traceDataAbs_tga` and
`RobinCaps.ThinDomain.TraceGen.traceDataGen_tgn` have the same boundary form, and in particular
the same trace split. -/
theorem bdAbs_eq_bdGen_tgn_tga (hm : 1 ≤ m) (hR : 0 < R)
    (hL : ((Cap.hemisphere m).K + (Cap.hemisphere m).K) * R < L)
    (hb : BulkTraceInput_tgn m (Cap.hemisphere m) (Cap.hemisphere m) L R hR hL)
    (u v : H1P (thinDomain (Cap.hemisphere m) (Cap.hemisphere m) L R)) :
    bdAbs_tga hR hL (capTraceDataHemi_th m hm) (capTraceDataHemi_th m hm) hb u v
      = bdGen_tgn hm hR hL hb u v := by
  rw [bdAbs_apply_tga, bdGen_apply_tgn, bdCapL_eq_tgn_tga hm hR hL, bdCapR_eq_tgn_tga hm hR hL]

/-- **Consistency, at the level of `TraceData.bd`.**  `traceDataAbs_tga`, specialised to two
hemispherical caps with `capTraceDataHemi_th` on both sides, reproduces the boundary form of
`RobinCaps.ThinDomain.TraceGen.traceDataGen_tgn`. -/
theorem bd_eq_tgn_tga (hm : 1 ≤ m) (hR : 0 < R)
    (hL : ((Cap.hemisphere m).K + (Cap.hemisphere m).K) * R < L)
    (hb : BulkTraceInput_tgn m (Cap.hemisphere m) (Cap.hemisphere m) L R hR hL)
    (hcim : CapTraceIntegrableAbs_tga (Cap.hemisphere m) (capTraceDataHemi_th m hm))
    (hcip : CapTraceIntegrableAbs_tga (Cap.hemisphere m) (capTraceDataHemi_th m hm))
    (hcbi : ContinuousBoundaryIntegrableAbs_tga m (Cap.hemisphere m) (Cap.hemisphere m) L R hR hL)
    (hci : CapTraceIntegrable_tgn m hm) (hcbi' : ContinuousBoundaryIntegrable_tgn m L R hR hL)
    (u v : H1P (thinDomain (Cap.hemisphere m) (Cap.hemisphere m) L R)) :
    (traceDataAbs_tga hm hR hL (capTraceDataHemi_th m hm) (capTraceDataHemi_th m hm) hb hcim hcip
        hcbi).bd u v
      = (traceDataGen_tgn hm hR hL hb hci hcbi').bd u v := by
  show bdAbs_tga hR hL (capTraceDataHemi_th m hm) (capTraceDataHemi_th m hm) hb u v
      = bdGen_tgn hm hR hL hb u v
  exact bdAbs_eq_bdGen_tgn_tga hm hR hL hb u v

end RobinCaps.ThinDomain

