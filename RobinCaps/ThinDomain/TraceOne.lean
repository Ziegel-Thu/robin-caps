import RobinCaps.ThinDomain.SliceThin
import RobinCaps.ThinDomain.BoundaryIntegrable
import RobinCaps.Transverse.GroundStateOneReg

/-!
# The trace of the planar thin domain (`m = 1`), from the slice-wise absolute continuity

This file **constructs** a `RobinCaps.ThinDomain.TraceData Cm Cp L R` for transverse dimension
`m = 1` out of the slice-wise ACL property already proved in
`RobinCaps/ThinDomain/SliceThin.lean`, taking **one** analytic fact as an explicit hypothesis:
the slice-wise trace inequality, packaged as `TraceIneqOne`.

Everything else — the boundary representative, its linearity, the bilinear boundary form, its
identification with the concrete revolution boundary integral, symmetry, nonnegativity, the
consistency with the honest surface integral for continuous functions, and the a.e.-invariance
— is proved here.

## The construction

For `m = 1` the transverse slice of `Ω_R` at the axial coordinate `x` is the interval
`(−r(x), r(x)) ⊂ EuclideanSpace ℝ (Fin 1)`, `r = RobinCaps.Domain.profile Cm Cp L R`.  It is
identified with `(0, 2 r(x))` by the affine map `eptSh (r x) : t ↦ ept (t − r x)` of
`RobinCaps/Transverse/GroundStateOneFull.lean`.

* `hasWeakDeriv_of_hasWeakGrad_ball` transports a weak gradient on the ball to a
  one-dimensional weak derivative on `(0, 2ρ)` (this is `Transverse.hasWeakDeriv_slice`, with the
  `TransH1` packaging removed).
* `SliceGood u x` collects the five facts making the slice at `x` a genuine one-dimensional
  `H¹` function; `ae_sliceGood` proves that a.e. `x ∈ (−L/2, L/2)` is good, combining
  `sliceACL_transverse_thin` with Fubini for the three integrability statements.
* `sliceRep u x : Sobolev.H1 (2 r x)` is the **absolutely continuous representative** of the
  slice (`Sobolev.exists_h1_of_hasWeakDeriv`), `0` on the bad set; `trPlus u x`, `trMinus u x`
  are its values at the two endpoints, i.e. the boundary values at `(x, ±r(x))`.
* `trPlus` is only *a.e.* additive, while the field `TraceData.tr_add` asks for a pointwise
  identity.  The gap is closed once and for all by `slSection`, a linear section of the
  quotient of `ℝ → ℝ` by the subspace `slNull` of functions vanishing a.e. on `(−L/2, L/2)`
  and at the two endpoints `±L/2` (every surjection of vector spaces splits:
  `LinearMap.exists_rightInverse_of_surjective`).  The resulting `trPlusL`, `trMinusL` are
  **honestly linear** and a.e. equal to `trPlus`, `trMinus`; `trOne` glues them into a boundary
  representative on `CapSpace 1`.
* Since `∫_{S⁰_ρ} g = g(ept ρ) + g(ept (−ρ))` (`Transverse.sphereIntegral_one_eq`), the lateral
  boundary integral of `tr u · tr v` is
  `∫_{-L/2}^{L/2} A(x) (trPlus u · trPlus v + trMinus u · trMinus v) dx`, with
  `A = areaElement = √(1 + r'²)` the area element (`traceForm_eq`); the two **end disks**
  contribute nothing, because `trOne u` vanishes identically on them (the slices at `x = ∓L/2`
  are not good, `SliceGood` requiring `x ∈ (−L/2, L/2)`).

## The single remaining hypothesis

`TraceIneqOne Cm Cp L R` asks for

* a.e. measurability of `x ↦ trPlus u x` and `x ↦ trMinus u x`,
* integrability of `x ↦ A(x) (trPlus u x ² + trMinus u x ²)` on `(−L/2, L/2)`,
* a constant `C` with `∫ A (trPlus u ² + trMinus u ²) ≤ C (D[u] + N[u])` for every `u`.

This is exactly the planar trace inequality.  It cannot be obtained from the vertical slices
alone: on a vertical segment `{x} × (−r(x), r(x))` the one-dimensional trace inequality of
`RobinCaps/Sobolev/Interval.lean` costs a factor `r(x)⁻¹`, which is *not* integrable against the
area element near the tips of the caps, where `r(x) → 0`.  A genuine proof needs a Poincaré /
trace argument adapted to the caps (e.g. slicing along the normal to the lateral boundary, or a
Lipschitz extension), which is the analytic brick this file isolates.

No `sorry`, `admit`, `axiom` or `native_decide` occurs in this file.
-/

open MeasureTheory Set Metric Filter

open scoped ContDiff ENNReal Topology

noncomputable section

namespace RobinCaps.ThinDomain

open RobinCaps.Domain RobinCaps.Sobolev RobinCaps.Transverse

variable {Cm Cp : Cap 1} {L R : ℝ}

/-! ## 0. The area element in transverse dimension one -/

/-- For `m = 1` the area element is `√(1 + r'²)`: the weight `r^{m-1}` is `r^0 = 1`. -/
theorem areaElement_one_eq (x : ℝ) :
    areaElement Cm Cp L R x = Real.sqrt (1 + deriv (profile Cm Cp L R) x ^ 2) := by
  simp [areaElement]

theorem areaElement_nonneg (x : ℝ) : 0 ≤ areaElement Cm Cp L R x := by
  rw [areaElement_one_eq]; exact Real.sqrt_nonneg _

theorem measurable_areaElement : Measurable (areaElement Cm Cp L R) := by
  have h : (areaElement Cm Cp L R) = fun x => Real.sqrt (1 + deriv (profile Cm Cp L R) x ^ 2) :=
    funext areaElement_one_eq
  rw [h]
  exact Real.continuous_sqrt.measurable.comp
    (measurable_const.add ((measurable_deriv (profile Cm Cp L R)).pow_const 2))

/-! ## 1. From a weak gradient on the transverse ball to a one-dimensional weak derivative -/

/-- **The slice transport.**  If `g` is a weak gradient of `f` on the ball `B_1(ρ)`, then the
coordinate `t ↦ g (eptSh ρ t) 0` is a one-dimensional weak derivative of `t ↦ f (eptSh ρ t)` on
`(0, 2ρ)`.  This is `RobinCaps.Transverse.hasWeakDeriv_slice` with the `TransH1` packaging
removed, so that it applies to the slices of an `H1P` element of the thin domain. -/
theorem hasWeakDeriv_of_hasWeakGrad_ball {ρ : ℝ} (hρ : 0 < ρ)
    {f : EuclideanSpace ℝ (Fin 1) → ℝ} {g : EuclideanSpace ℝ (Fin 1) → EuclideanSpace ℝ (Fin 1)}
    (h : Weak.HasWeakGrad (ball (0 : EuclideanSpace ℝ (Fin 1)) ρ) f g) :
    HasWeakDeriv 0 (2 * ρ) (fun t => f (eptSh ρ t)) (fun t => g (eptSh ρ t) 0) := by
  intro φ hφ hφc hφs
  have h2ρ : (0 : ℝ) ≤ 2 * ρ := by linarith
  have hwg := h (liftTest ρ φ) (contDiff_liftTest ρ hφ) (hasCompactSupport_liftTest hφc)
    (tsupport_liftTest_subset_ball hφs) 0
  have hL : (∫ z in ball (0 : EuclideanSpace ℝ (Fin 1)) ρ,
        f z * fderiv ℝ (liftTest ρ φ) z (EuclideanSpace.single (0 : Fin 1) 1))
      = ∫ t in Ioo (0 : ℝ) (2 * ρ), f (eptSh ρ t) * deriv φ t := by
    simp only [fderiv_liftTest_single ρ hφ]
    rw [integral_ball_shift hρ.le (fun z => f z * deriv φ (z 0 + ρ)),
      ← Sobolev.intervalIntegral_eq_setIntegral_Ioo h2ρ]
    simp
  have hR' : (∫ z in ball (0 : EuclideanSpace ℝ (Fin 1)) ρ, g z 0 * liftTest ρ φ z)
      = ∫ t in Ioo (0 : ℝ) (2 * ρ), g (eptSh ρ t) 0 * φ t := by
    rw [integral_ball_shift hρ.le (fun z => g z 0 * liftTest ρ φ z),
      ← Sobolev.intervalIntegral_eq_setIntegral_Ioo h2ρ]
    simp
  rw [← hL, ← hR']
  exact hwg

/-! ## 2. Slice-wise integrability on the thin domain -/

/-- Almost every transverse slice of an `L²(Ω_R)` function is in `L²` of the corresponding
transverse ball.  The thin domain is not a product, so the statement is obtained by extending
by zero to the enclosing cylinder `(−L/2, L/2) × B_1(R)`. -/
theorem ae_memLp_slice (hR : 0 < R) (hL : (Cm.K + Cp.K) * R < L) {f : CapSpace 1 → ℝ}
    (hf : MemLp f 2 (volume.restrict (thinDomain Cm Cp L R))) :
    ∀ᵐ x ∂(volume.restrict (Ioo (-L / 2) (L / 2))),
      MemLp (fun z => f (x, z)) 2
        (volume.restrict (ball (0 : EuclideanSpace ℝ (Fin 1)) (profile Cm Cp L R x))) := by
  have hΩ : MeasurableSet (thinDomain Cm Cp L R) := measurableSet_thinDomain hR hL
  have hind : MemLp ((thinDomain Cm Cp L R).indicator f) 2 (volume : Measure (CapSpace 1)) :=
    (memLp_indicator_iff_restrict hΩ).2 hf
  have h2 : MemLp ((thinDomain Cm Cp L R).indicator f) 2
      (volume.restrict (Ioo (-L / 2) (L / 2) ×ˢ ball (0 : EuclideanSpace ℝ (Fin 1)) R)) :=
    hind.restrict _
  filter_upwards [ae_memLp_transverseSlice h2, ae_restrict_mem measurableSet_Ioo] with x hx hxI
  have hsub : ball (0 : EuclideanSpace ℝ (Fin 1)) (profile Cm Cp L R x)
      ⊆ ball (0 : EuclideanSpace ℝ (Fin 1)) R := ball_subset_ball (profile_le_R hR hL hxI)
  have hres : ((volume : Measure (EuclideanSpace ℝ (Fin 1))).restrict
        (ball (0 : EuclideanSpace ℝ (Fin 1)) R)).restrict
        (ball (0 : EuclideanSpace ℝ (Fin 1)) (profile Cm Cp L R x))
      = (volume : Measure (EuclideanSpace ℝ (Fin 1))).restrict
        (ball (0 : EuclideanSpace ℝ (Fin 1)) (profile Cm Cp L R x)) :=
    Measure.restrict_restrict_of_subset hsub
  have hx' := hx.restrict (ball (0 : EuclideanSpace ℝ (Fin 1)) (profile Cm Cp L R x))
  rw [hres] at hx'
  refine (memLp_congr_ae ?_).1 hx'
  refine (ae_restrict_iff' measurableSet_ball).2 (Eventually.of_forall fun z hz => ?_)
  have hmem : ((x, z) : CapSpace 1) ∈ thinDomain Cm Cp L R :=
    ⟨hxI.1, hxI.2, mem_ball_zero_iff.1 hz⟩
  exact Set.indicator_of_mem hmem f

/-- An `L²` slice gives the three integrability statements on `(0, 2ρ)` needed by the du
Bois-Reymond bridge. -/
theorem integrableOn_shift_of_memLp {ρ : ℝ} {F : EuclideanSpace ℝ (Fin 1) → ℝ}
    (hF : MemLp F 2 (volume.restrict (ball (0 : EuclideanSpace ℝ (Fin 1)) ρ))) :
    IntegrableOn (fun t => F (eptSh ρ t)) (Ioo 0 (2 * ρ)) volume ∧
      IntegrableOn (fun t => F (eptSh ρ t) ^ 2) (Ioo 0 (2 * ρ)) volume := by
  haveI : IsFiniteMeasure
      ((volume : Measure (EuclideanSpace ℝ (Fin 1))).restrict
        (ball (0 : EuclideanSpace ℝ (Fin 1)) ρ)) := isFiniteMeasure_ball ρ
  constructor
  · exact (integrableOn_comp_eptSh F).2 (hF.integrable one_le_two)
  · exact (integrableOn_comp_eptSh (fun z => F z ^ 2)).2
      ((memLp_two_iff_integrable_sq hF.aestronglyMeasurable).1 hF)

/-! ## 3. The good slices and the absolutely continuous slice representative -/

/-- **A good axial coordinate**: the transverse slice at `x` is a genuine one-dimensional
Sobolev function on `(0, 2 r(x))` after the affine identification `eptSh (r x)`.  All five
conditions hold for almost every `x ∈ (−L/2, L/2)` (`ae_sliceGood`). -/
structure SliceGood {Cm Cp : Cap 1} {L R : ℝ} (u : H1P (thinDomain Cm Cp L R)) (x : ℝ) :
    Prop where
  /-- The axial coordinate lies in the open axial interval. -/
  mem : x ∈ Ioo (-L / 2) (L / 2)
  /-- The transverse slice is a nondegenerate interval. -/
  pos : 0 < profile Cm Cp L R x
  /-- The slice is integrable. -/
  int_fun : IntegrableOn (fun t => u.toFun (x, eptSh (profile Cm Cp L R x) t))
    (Ioo 0 (2 * profile Cm Cp L R x)) volume
  /-- The slice of the transverse gradient is integrable. -/
  int_grad : IntegrableOn (fun t => u.gz (x, eptSh (profile Cm Cp L R x) t) 0)
    (Ioo 0 (2 * profile Cm Cp L R x)) volume
  /-- The slice of the transverse gradient is square integrable. -/
  int_grad_sq : IntegrableOn (fun t => u.gz (x, eptSh (profile Cm Cp L R x) t) 0 ^ 2)
    (Ioo 0 (2 * profile Cm Cp L R x)) volume
  /-- The slice of the transverse gradient is a weak derivative of the slice. -/
  weakDeriv : HasWeakDeriv 0 (2 * profile Cm Cp L R x)
    (fun t => u.toFun (x, eptSh (profile Cm Cp L R x) t))
    (fun t => u.gz (x, eptSh (profile Cm Cp L R x) t) 0)

theorem SliceGood.len_pos {u : H1P (thinDomain Cm Cp L R)} {x : ℝ} (h : SliceGood u x) :
    (0 : ℝ) < 2 * profile Cm Cp L R x := by linarith [h.pos]

/-- **Deliverable 1 (a).**  For almost every `x ∈ (−L/2, L/2)` the transverse slice at `x` is
good: this combines `sliceACL_transverse_thin` (the weak gradient), the slice transport
`hasWeakDeriv_of_hasWeakGrad_ball` and Fubini (`ae_memLp_slice`) for the integrability. -/
theorem ae_sliceGood (hR : 0 < R) (hL : (Cm.K + Cp.K) * R < L)
    (u : H1P (thinDomain Cm Cp L R)) :
    ∀ᵐ x ∂(volume.restrict (Ioo (-L / 2) (L / 2))), SliceGood u x := by
  have hgz : MemLp (fun p : CapSpace 1 => u.gz p 0) 2
      (volume.restrict (thinDomain Cm Cp L R)) := memLp_two_compP u.gz_memL2 0
  filter_upwards [ae_restrict_mem measurableSet_Ioo, sliceACL_transverse_thin hR hL u,
    ae_memLp_slice hR hL u.memL2, ae_memLp_slice hR hL hgz] with x hxI hwg hf hg
  have hpos := profile_pos hR hL hxI
  exact
    { mem := hxI
      pos := hpos
      int_fun := (integrableOn_shift_of_memLp hf).1
      int_grad := (integrableOn_shift_of_memLp hg).1
      int_grad_sq := (integrableOn_shift_of_memLp hg).2
      weakDeriv := hasWeakDeriv_of_hasWeakGrad_ball hpos hwg }

open Classical in
/-- **Deliverable 1 (b).  The absolutely continuous representative of the transverse slice**,
an element of the concrete one-dimensional Sobolev layer `H¹(0, 2 r(x))`; `0` on the (null) set
of bad axial coordinates. -/
def sliceRep (u : H1P (thinDomain Cm Cp L R)) (x : ℝ) : H1 (2 * profile Cm Cp L R x) :=
  if h : SliceGood u x then
    Classical.choose (exists_h1_of_hasWeakDeriv h.len_pos h.int_fun h.int_grad h.int_grad_sq
      h.weakDeriv)
  else 0

theorem sliceRep_ae {u : H1P (thinDomain Cm Cp L R)} {x : ℝ} (h : SliceGood u x) :
    (sliceRep u x).toFun =ᵐ[volume.restrict (Ioo 0 (2 * profile Cm Cp L R x))]
      fun t => u.toFun (x, eptSh (profile Cm Cp L R x) t) := by
  rw [sliceRep, dif_pos h]
  exact (Classical.choose_spec (exists_h1_of_hasWeakDeriv h.len_pos h.int_fun h.int_grad
    h.int_grad_sq h.weakDeriv)).1

theorem sliceRep_of_not {u : H1P (thinDomain Cm Cp L R)} {x : ℝ} (h : ¬ SliceGood u x) :
    (sliceRep u x).toFun = fun _ => 0 := by
  rw [sliceRep, dif_neg h]; rfl

/-- **Uniqueness of the slice representative on the closed interval.**  Any continuous function
a.e. equal to the slice agrees with `sliceRep u x` on all of `[0, 2 r(x)]`, endpoints
included. -/
theorem sliceRep_eqOn {u : H1P (thinDomain Cm Cp L R)} {x : ℝ} (hg : SliceGood u x)
    {w : ℝ → ℝ} (hwc : ContinuousOn w (Icc 0 (2 * profile Cm Cp L R x)))
    (hw : w =ᵐ[volume.restrict (Ioo 0 (2 * profile Cm Cp L R x))]
      fun t => u.toFun (x, eptSh (profile Cm Cp L R x) t)) :
    EqOn w (sliceRep u x).toFun (Icc 0 (2 * profile Cm Cp L R x)) :=
  eqOn_Icc_of_ae_eq_of_continuousOn hg.len_pos hwc
    (H1_continuousOn hg.len_pos (sliceRep u x)) (hw.trans (sliceRep_ae hg).symm)

/-! ### The two endpoint traces -/

/-- **The boundary value at the upper endpoint** `(x, r(x))` of the transverse slice. -/
def trPlus (u : H1P (thinDomain Cm Cp L R)) (x : ℝ) : ℝ :=
  (sliceRep u x).toFun (2 * profile Cm Cp L R x)

/-- **The boundary value at the lower endpoint** `(x, −r(x))` of the transverse slice. -/
def trMinus (u : H1P (thinDomain Cm Cp L R)) (x : ℝ) : ℝ := (sliceRep u x).toFun 0

theorem trPlus_of_not {u : H1P (thinDomain Cm Cp L R)} {x : ℝ} (h : ¬ SliceGood u x) :
    trPlus u x = 0 := by rw [trPlus, sliceRep_of_not h]

theorem trMinus_of_not {u : H1P (thinDomain Cm Cp L R)} {x : ℝ} (h : ¬ SliceGood u x) :
    trMinus u x = 0 := by rw [trMinus, sliceRep_of_not h]

theorem sliceGood_mem {u : H1P (thinDomain Cm Cp L R)} {x : ℝ} (h : SliceGood u x) :
    x ∈ Ioo (-L / 2) (L / 2) := h.mem

theorem not_sliceGood_left (u : H1P (thinDomain Cm Cp L R)) : ¬ SliceGood u (-L / 2) :=
  fun h => absurd h.mem.1 (lt_irrefl _)

theorem not_sliceGood_right (u : H1P (thinDomain Cm Cp L R)) : ¬ SliceGood u (L / 2) :=
  fun h => absurd h.mem.2 (lt_irrefl _)

theorem trPlus_left (u : H1P (thinDomain Cm Cp L R)) : trPlus u (-L / 2) = 0 :=
  trPlus_of_not (not_sliceGood_left u)

theorem trPlus_right (u : H1P (thinDomain Cm Cp L R)) : trPlus u (L / 2) = 0 :=
  trPlus_of_not (not_sliceGood_right u)

theorem trMinus_left (u : H1P (thinDomain Cm Cp L R)) : trMinus u (-L / 2) = 0 :=
  trMinus_of_not (not_sliceGood_left u)

theorem trMinus_right (u : H1P (thinDomain Cm Cp L R)) : trMinus u (L / 2) = 0 :=
  trMinus_of_not (not_sliceGood_right u)


/-! ### Linearity of the endpoint traces, almost everywhere -/

theorem mem_Icc_zero {u : H1P (thinDomain Cm Cp L R)} {x : ℝ} (h : SliceGood u x) :
    (0 : ℝ) ∈ Icc (0 : ℝ) (2 * profile Cm Cp L R x) := ⟨le_rfl, h.len_pos.le⟩

theorem mem_Icc_end {u : H1P (thinDomain Cm Cp L R)} {x : ℝ} (h : SliceGood u x) :
    (2 * profile Cm Cp L R x) ∈ Icc (0 : ℝ) (2 * profile Cm Cp L R x) := ⟨h.len_pos.le, le_rfl⟩

/-- **Additivity of the endpoint traces on the good set.** -/
theorem trPlus_add_of {u v : H1P (thinDomain Cm Cp L R)} {x : ℝ}
    (hu : SliceGood u x) (hv : SliceGood v x) (huv : SliceGood (u + v) x) :
    trPlus (u + v) x = trPlus u x + trPlus v x ∧
      trMinus (u + v) x = trMinus u x + trMinus v x := by
  have hcont : ContinuousOn (sliceRep u x + sliceRep v x).toFun
      (Icc 0 (2 * profile Cm Cp L R x)) := by
    rw [H1.add_toFun]
    exact (H1_continuousOn hu.len_pos _).add (H1_continuousOn hv.len_pos _)
  have hw : (sliceRep u x + sliceRep v x).toFun
      =ᵐ[volume.restrict (Ioo 0 (2 * profile Cm Cp L R x))]
        fun t => (u + v).toFun (x, eptSh (profile Cm Cp L R x) t) := by
    filter_upwards [sliceRep_ae hu, sliceRep_ae hv] with t h1 h2
    simp only [H1.add_toFun, Pi.add_apply, H1P.add_toFun, h1, h2]
  have heq := sliceRep_eqOn huv hcont hw
  constructor
  · have h := heq (mem_Icc_end huv)
    simpa only [trPlus, H1.add_toFun, Pi.add_apply] using h.symm
  · have h := heq (mem_Icc_zero huv)
    simpa only [trMinus, H1.add_toFun, Pi.add_apply] using h.symm

/-- **Homogeneity of the endpoint traces on the good set.** -/
theorem trPlus_smul_of (c : ℝ) {u : H1P (thinDomain Cm Cp L R)} {x : ℝ}
    (hu : SliceGood u x) (hcu : SliceGood (c • u) x) :
    trPlus (c • u) x = c * trPlus u x ∧ trMinus (c • u) x = c * trMinus u x := by
  have hcont : ContinuousOn (c • sliceRep u x).toFun (Icc 0 (2 * profile Cm Cp L R x)) := by
    rw [H1.smul_toFun]
    exact continuousOn_const.mul (H1_continuousOn hu.len_pos _)
  have hw : (c • sliceRep u x).toFun =ᵐ[volume.restrict (Ioo 0 (2 * profile Cm Cp L R x))]
      fun t => (c • u).toFun (x, eptSh (profile Cm Cp L R x) t) := by
    filter_upwards [sliceRep_ae hu] with t h1
    simp only [H1.smul_toFun, H1P.smul_toFun, Pi.smul_apply, smul_eq_mul, h1]
  have heq := sliceRep_eqOn hcu hcont hw
  constructor
  · have h := heq (mem_Icc_end hcu)
    simpa only [trPlus, H1.smul_toFun] using h.symm
  · have h := heq (mem_Icc_zero hcu)
    simpa only [trMinus, H1.smul_toFun] using h.symm

/-- **Deliverable 1 (c).  `trPlus` and `trMinus` are additive almost everywhere.** -/
theorem ae_trPlus_add (hR : 0 < R) (hL : (Cm.K + Cp.K) * R < L)
    (u v : H1P (thinDomain Cm Cp L R)) :
    ∀ᵐ x ∂(volume.restrict (Ioo (-L / 2) (L / 2))),
      trPlus (u + v) x = trPlus u x + trPlus v x ∧
        trMinus (u + v) x = trMinus u x + trMinus v x := by
  filter_upwards [ae_sliceGood hR hL u, ae_sliceGood hR hL v, ae_sliceGood hR hL (u + v)]
    with x h1 h2 h3
  exact trPlus_add_of h1 h2 h3

/-- **Deliverable 1 (d).  `trPlus` and `trMinus` are homogeneous almost everywhere.** -/
theorem ae_trPlus_smul (hR : 0 < R) (hL : (Cm.K + Cp.K) * R < L) (c : ℝ)
    (u : H1P (thinDomain Cm Cp L R)) :
    ∀ᵐ x ∂(volume.restrict (Ioo (-L / 2) (L / 2))),
      trPlus (c • u) x = c * trPlus u x ∧ trMinus (c • u) x = c * trMinus u x := by
  filter_upwards [ae_sliceGood hR hL u, ae_sliceGood hR hL (c • u)] with x h1 h2
  exact trPlus_smul_of c h1 h2

/-! ## 4. From the a.e.-linear traces to an honestly linear boundary representative

The field `TraceData.tr_add` is a *pointwise* identity, while `trPlus` is only additive almost
everywhere.  The two are reconciled by a linear section of the quotient of `ℝ → ℝ` by the
subspace of functions vanishing a.e. on the axial interval and at its two endpoints: a
surjection of vector spaces always splits. -/

/-- Functions vanishing a.e. on `(−L/2, L/2)` and at the two endpoints `±L/2`. -/
def slNull (L : ℝ) : Submodule ℝ (ℝ → ℝ) where
  carrier := {f | f =ᵐ[volume.restrict (Ioo (-L / 2) (L / 2))] 0 ∧ f (-L / 2) = 0 ∧ f (L / 2) = 0}
  zero_mem' := ⟨Filter.EventuallyEq.rfl, rfl, rfl⟩
  add_mem' := by
    rintro a b ⟨ha, ha1, ha2⟩ ⟨hb, hb1, hb2⟩
    refine ⟨?_, by simp [ha1, hb1], by simp [ha2, hb2]⟩
    filter_upwards [ha, hb] with t h1 h2
    simp only [Pi.add_apply, Pi.zero_apply] at *
    rw [h1, h2, add_zero]
  smul_mem' := by
    rintro c a ⟨ha, ha1, ha2⟩
    refine ⟨?_, by simp [ha1], by simp [ha2]⟩
    filter_upwards [ha] with t h1
    simp only [Pi.smul_apply, Pi.zero_apply, smul_eq_mul] at *
    rw [h1, mul_zero]

theorem mem_slNull {L : ℝ} {f : ℝ → ℝ}
    (h1 : f =ᵐ[volume.restrict (Ioo (-L / 2) (L / 2))] 0) (h2 : f (-L / 2) = 0)
    (h3 : f (L / 2) = 0) : f ∈ slNull L := ⟨h1, h2, h3⟩

theorem slNull_ae {L : ℝ} {f : ℝ → ℝ} (h : f ∈ slNull L) :
    f =ᵐ[volume.restrict (Ioo (-L / 2) (L / 2))] 0 := h.1

theorem slNull_left {L : ℝ} {f : ℝ → ℝ} (h : f ∈ slNull L) : f (-L / 2) = 0 := h.2.1

theorem slNull_right {L : ℝ} {f : ℝ → ℝ} (h : f ∈ slNull L) : f (L / 2) = 0 := h.2.2

theorem exists_slSection (L : ℝ) :
    ∃ s : ((ℝ → ℝ) ⧸ slNull L) →ₗ[ℝ] (ℝ → ℝ), (slNull L).mkQ.comp s = LinearMap.id :=
  LinearMap.exists_rightInverse_of_surjective _ (Submodule.range_mkQ _)

/-- **A linear section** of the quotient map `(ℝ → ℝ) → (ℝ → ℝ) ⧸ slNull L`. -/
def slSection (L : ℝ) : ((ℝ → ℝ) ⧸ slNull L) →ₗ[ℝ] (ℝ → ℝ) :=
  Classical.choose (exists_slSection L)

theorem slSection_spec (L : ℝ) (q : (ℝ → ℝ) ⧸ slNull L) :
    (Submodule.Quotient.mk (slSection L q) : (ℝ → ℝ) ⧸ slNull L) = q := by
  have h := congrArg (fun F : ((ℝ → ℝ) ⧸ slNull L) →ₗ[ℝ] ((ℝ → ℝ) ⧸ slNull L) => F q)
    (Classical.choose_spec (exists_slSection L))
  simpa only [LinearMap.coe_comp, Function.comp_apply, Submodule.mkQ_apply,
    LinearMap.id_coe, id_eq] using h

theorem slSection_sub_mem (L : ℝ) (f : ℝ → ℝ) :
    slSection L (Submodule.Quotient.mk f) - f ∈ slNull L :=
  (Submodule.Quotient.eq (slNull L)).1 (slSection_spec L _)

/-! ### The linearised endpoint traces -/

/-- The class of `trPlus u` in the quotient, as a linear map. -/
def trPlusQ (hR : 0 < R) (hL : (Cm.K + Cp.K) * R < L) :
    H1P (thinDomain Cm Cp L R) →ₗ[ℝ] ((ℝ → ℝ) ⧸ slNull L) where
  toFun u := Submodule.Quotient.mk (trPlus u)
  map_add' u v := by
    rw [← Submodule.Quotient.mk_add]
    refine (Submodule.Quotient.eq (slNull L)).2 (mem_slNull ?_ ?_ ?_)
    · filter_upwards [ae_trPlus_add hR hL u v] with x hx
      simp only [Pi.sub_apply, Pi.add_apply, Pi.zero_apply, hx.1, sub_self]
    · simp only [Pi.sub_apply, Pi.add_apply, trPlus_left, sub_self, add_zero]
    · simp only [Pi.sub_apply, Pi.add_apply, trPlus_right, sub_self, add_zero]
  map_smul' c u := by
    rw [RingHom.id_apply, ← Submodule.Quotient.mk_smul]
    refine (Submodule.Quotient.eq (slNull L)).2 (mem_slNull ?_ ?_ ?_)
    · filter_upwards [ae_trPlus_smul hR hL c u] with x hx
      simp only [Pi.sub_apply, Pi.smul_apply, Pi.zero_apply, smul_eq_mul, hx.1, sub_self]
    · simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul, trPlus_left, mul_zero, sub_self]
    · simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul, trPlus_right, mul_zero, sub_self]

/-- The class of `trMinus u` in the quotient, as a linear map. -/
def trMinusQ (hR : 0 < R) (hL : (Cm.K + Cp.K) * R < L) :
    H1P (thinDomain Cm Cp L R) →ₗ[ℝ] ((ℝ → ℝ) ⧸ slNull L) where
  toFun u := Submodule.Quotient.mk (trMinus u)
  map_add' u v := by
    rw [← Submodule.Quotient.mk_add]
    refine (Submodule.Quotient.eq (slNull L)).2 (mem_slNull ?_ ?_ ?_)
    · filter_upwards [ae_trPlus_add hR hL u v] with x hx
      simp only [Pi.sub_apply, Pi.add_apply, Pi.zero_apply, hx.2, sub_self]
    · simp only [Pi.sub_apply, Pi.add_apply, trMinus_left, sub_self, add_zero]
    · simp only [Pi.sub_apply, Pi.add_apply, trMinus_right, sub_self, add_zero]
  map_smul' c u := by
    rw [RingHom.id_apply, ← Submodule.Quotient.mk_smul]
    refine (Submodule.Quotient.eq (slNull L)).2 (mem_slNull ?_ ?_ ?_)
    · filter_upwards [ae_trPlus_smul hR hL c u] with x hx
      simp only [Pi.sub_apply, Pi.smul_apply, Pi.zero_apply, smul_eq_mul, hx.2, sub_self]
    · simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul, trMinus_left, mul_zero, sub_self]
    · simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul, trMinus_right, mul_zero, sub_self]

/-- **The linearised upper endpoint trace**: honestly linear in `u`, and a.e. equal to
`trPlus u` (`trPlusL_ae`). -/
def trPlusL (hR : 0 < R) (hL : (Cm.K + Cp.K) * R < L) :
    H1P (thinDomain Cm Cp L R) →ₗ[ℝ] (ℝ → ℝ) := (slSection L).comp (trPlusQ hR hL)

/-- **The linearised lower endpoint trace.** -/
def trMinusL (hR : 0 < R) (hL : (Cm.K + Cp.K) * R < L) :
    H1P (thinDomain Cm Cp L R) →ₗ[ℝ] (ℝ → ℝ) := (slSection L).comp (trMinusQ hR hL)

theorem trPlusL_sub_mem (hR : 0 < R) (hL : (Cm.K + Cp.K) * R < L)
    (u : H1P (thinDomain Cm Cp L R)) : trPlusL hR hL u - trPlus u ∈ slNull L :=
  slSection_sub_mem L (trPlus u)

theorem trMinusL_sub_mem (hR : 0 < R) (hL : (Cm.K + Cp.K) * R < L)
    (u : H1P (thinDomain Cm Cp L R)) : trMinusL hR hL u - trMinus u ∈ slNull L :=
  slSection_sub_mem L (trMinus u)

theorem trPlusL_ae (hR : 0 < R) (hL : (Cm.K + Cp.K) * R < L)
    (u : H1P (thinDomain Cm Cp L R)) :
    trPlusL hR hL u =ᵐ[volume.restrict (Ioo (-L / 2) (L / 2))] trPlus u := by
  filter_upwards [slNull_ae (trPlusL_sub_mem hR hL u)] with x hx
  simpa only [Pi.sub_apply, Pi.zero_apply, sub_eq_zero] using hx

theorem trMinusL_ae (hR : 0 < R) (hL : (Cm.K + Cp.K) * R < L)
    (u : H1P (thinDomain Cm Cp L R)) :
    trMinusL hR hL u =ᵐ[volume.restrict (Ioo (-L / 2) (L / 2))] trMinus u := by
  filter_upwards [slNull_ae (trMinusL_sub_mem hR hL u)] with x hx
  simpa only [Pi.sub_apply, Pi.zero_apply, sub_eq_zero] using hx

theorem trPlusL_left (hR : 0 < R) (hL : (Cm.K + Cp.K) * R < L)
    (u : H1P (thinDomain Cm Cp L R)) : trPlusL hR hL u (-L / 2) = 0 := by
  have h := slNull_left (trPlusL_sub_mem hR hL u)
  simp only [Pi.sub_apply, sub_eq_zero] at h
  rw [h, trPlus_left]

theorem trPlusL_right (hR : 0 < R) (hL : (Cm.K + Cp.K) * R < L)
    (u : H1P (thinDomain Cm Cp L R)) : trPlusL hR hL u (L / 2) = 0 := by
  have h := slNull_right (trPlusL_sub_mem hR hL u)
  simp only [Pi.sub_apply, sub_eq_zero] at h
  rw [h, trPlus_right]

theorem trMinusL_left (hR : 0 < R) (hL : (Cm.K + Cp.K) * R < L)
    (u : H1P (thinDomain Cm Cp L R)) : trMinusL hR hL u (-L / 2) = 0 := by
  have h := slNull_left (trMinusL_sub_mem hR hL u)
  simp only [Pi.sub_apply, sub_eq_zero] at h
  rw [h, trMinus_left]

theorem trMinusL_right (hR : 0 < R) (hL : (Cm.K + Cp.K) * R < L)
    (u : H1P (thinDomain Cm Cp L R)) : trMinusL hR hL u (L / 2) = 0 := by
  have h := slNull_right (trMinusL_sub_mem hR hL u)
  simp only [Pi.sub_apply, sub_eq_zero] at h
  rw [h, trMinus_right]

/-! ## 5. The boundary representative on `CapSpace 1` -/

/-- **The boundary representative of the manuscript's trace, for `m = 1`**: the two linearised
endpoint traces, glued according to the sign of the transverse coordinate.  Only its values at
the lateral boundary points `(x, ±r(x))` matter for the boundary integral. -/
def trOne (hR : 0 < R) (hL : (Cm.K + Cp.K) * R < L) (u : H1P (thinDomain Cm Cp L R)) :
    CapSpace 1 → ℝ :=
  fun p => if 0 < p.2 0 then trPlusL hR hL u p.1 else trMinusL hR hL u p.1

theorem trOne_add (hR : 0 < R) (hL : (Cm.K + Cp.K) * R < L)
    (u v : H1P (thinDomain Cm Cp L R)) :
    trOne hR hL (u + v) = trOne hR hL u + trOne hR hL v := by
  funext p
  by_cases h : 0 < p.2 0 <;>
    simp [trOne, h, map_add]

theorem trOne_smul (hR : 0 < R) (hL : (Cm.K + Cp.K) * R < L) (c : ℝ)
    (u : H1P (thinDomain Cm Cp L R)) : trOne hR hL (c • u) = c • trOne hR hL u := by
  funext p
  by_cases h : 0 < p.2 0 <;>
    simp [trOne, h, map_smul]

theorem trOne_plus (hR : 0 < R) (hL : (Cm.K + Cp.K) * R < L) (u : H1P (thinDomain Cm Cp L R))
    {x : ℝ} (hx : 0 < profile Cm Cp L R x) :
    trOne hR hL u (x, ept (profile Cm Cp L R x)) = trPlusL hR hL u x := by
  simp [trOne, hx]

theorem trOne_minus (hR : 0 < R) (hL : (Cm.K + Cp.K) * R < L) (u : H1P (thinDomain Cm Cp L R))
    {x : ℝ} (hx : 0 < profile Cm Cp L R x) :
    trOne hR hL u (x, ept (-(profile Cm Cp L R x))) = trMinusL hR hL u x := by
  have h : ¬ (0 : ℝ) < -(profile Cm Cp L R x) := by simp only [not_lt]; linarith
  simp [trOne, h]

theorem trOne_end_left (hR : 0 < R) (hL : (Cm.K + Cp.K) * R < L)
    (u : H1P (thinDomain Cm Cp L R)) (z : EuclideanSpace ℝ (Fin 1)) :
    trOne hR hL u (-L / 2, z) = 0 := by
  by_cases h : 0 < z 0
  · simp [trOne, h, trPlusL_left]
  · simp [trOne, h, trMinusL_left]

theorem trOne_end_right (hR : 0 < R) (hL : (Cm.K + Cp.K) * R < L)
    (u : H1P (thinDomain Cm Cp L R)) (z : EuclideanSpace ℝ (Fin 1)) :
    trOne hR hL u (L / 2, z) = 0 := by
  by_cases h : 0 < z 0
  · simp [trOne, h, trPlusL_right]
  · simp [trOne, h, trMinusL_right]

/-! ## 6. The boundary integral in transverse dimension one -/

/-- For `m = 1` the lateral density is the area element times the sum of the two boundary
values, because `S⁰_ρ = {±ρ}`. -/
theorem lateralDensity_one_eq (g : CapSpace 1 → ℝ) (x : ℝ) :
    lateralDensity Cm Cp L R g x
      = areaElement Cm Cp L R x *
        (g (x, ept (profile Cm Cp L R x)) + g (x, ept (-(profile Cm Cp L R x)))) := by
  rw [lateralDensity_eq_sphereIntegral, sphereIntegral_one_eq, areaElement_one_eq]

/-- **The boundary integral for `m = 1`, for an integrand vanishing on the two end disks.** -/
theorem boundaryIntegral_one_eq (g : CapSpace 1 → ℝ)
    (hgl : ∀ z : EuclideanSpace ℝ (Fin 1), g (-L / 2, z) = 0)
    (hgr : ∀ z : EuclideanSpace ℝ (Fin 1), g (L / 2, z) = 0) :
    boundaryIntegral Cm Cp L R g
      = ∫ x in Ioo (-L / 2) (L / 2), areaElement Cm Cp L R x *
          (g (x, ept (profile Cm Cp L R x)) + g (x, ept (-(profile Cm Cp L R x)))) := by
  rw [boundaryIntegral, endDiskIntegralLeft, endDiskIntegralRight]
  simp only [hgl, hgr, integral_zero, add_zero]
  rw [lateralIntegral]
  exact setIntegral_congr_fun measurableSet_Ioo fun x _ => lateralDensity_one_eq g x

/-- **Deliverable 2.  The trace form**: the boundary integral of the product of two boundary
representatives. -/
def traceForm (hR : 0 < R) (hL : (Cm.K + Cp.K) * R < L)
    (u v : H1P (thinDomain Cm Cp L R)) : ℝ :=
  boundaryIntegral Cm Cp L R (fun p => trOne hR hL u p * trOne hR hL v p)

/-- **Deliverable 2 (identification).**  The trace form is the axial integral of the area
element against the two endpoint traces; the two end disks contribute nothing, because the
boundary representative vanishes on them. -/
theorem traceForm_eq (hR : 0 < R) (hL : (Cm.K + Cp.K) * R < L)
    (u v : H1P (thinDomain Cm Cp L R)) :
    traceForm hR hL u v = ∫ x in Ioo (-L / 2) (L / 2), areaElement Cm Cp L R x *
        (trPlus u x * trPlus v x + trMinus u x * trMinus v x) := by
  rw [traceForm, boundaryIntegral_one_eq _
    (fun z => by rw [trOne_end_left hR hL u z, zero_mul])
    (fun z => by rw [trOne_end_right hR hL u z, zero_mul])]
  refine integral_congr_ae ?_
  filter_upwards [trPlusL_ae hR hL u, trPlusL_ae hR hL v, trMinusL_ae hR hL u,
    trMinusL_ae hR hL v, ae_restrict_mem measurableSet_Ioo] with x h1 h2 h3 h4 hxI
  have hpos := profile_pos hR hL hxI
  rw [trOne_plus hR hL u hpos, trOne_plus hR hL v hpos, trOne_minus hR hL u hpos,
    trOne_minus hR hL v hpos, h1, h2, h3, h4]


/-! ## 7. Consistency for functions continuous up to the boundary -/

/-- The lateral boundary points `(x, ept t)` with `|t| ≤ r(x)` lie in `closure Ω_R`. -/
theorem mem_closure_ept (hR : 0 < R) (hL : (Cm.K + Cp.K) * R < L) {x : ℝ}
    (hx : x ∈ Ioo (-L / 2) (L / 2)) {t : ℝ} (ht : |t| ≤ profile Cm Cp L R x) :
    ((x, ept t) : CapSpace 1) ∈ closure (thinDomain Cm Cp L R) := by
  have hpos := profile_pos hR hL hx
  rcases lt_or_eq_of_le ht with h | h
  · exact subset_closure ⟨hx.1, hx.2, by rw [ept_norm]; exact h⟩
  · rcases (abs_eq hpos.le).1 h with h1 | h1
    · have e : ept t = profile Cm Cp L R x • ((spPlus : Metric.sphere
          (0 : EuclideanSpace ℝ (Fin 1)) 1) : EuclideanSpace ℝ (Fin 1)) := by
        rw [h1]; exact ept_eq_smul _
      rw [e]
      exact mem_closure_thinDomain_lateral hR hL hx spPlus
    · have e : ept t = profile Cm Cp L R x • ((spMinus : Metric.sphere
          (0 : EuclideanSpace ℝ (Fin 1)) 1) : EuclideanSpace ℝ (Fin 1)) := by
        rw [h1]
        show ept (-(profile Cm Cp L R x)) = profile Cm Cp L R x • ept (-1 : ℝ)
        rw [ept_eq_smul (-1 : ℝ), ept_eq_smul (-(profile Cm Cp L R x)), smul_smul]
        norm_num
      rw [e]
      exact mem_closure_thinDomain_lateral hR hL hx spMinus

theorem eptSh_end (ρ : ℝ) : eptSh ρ (2 * ρ) = ept ρ := by
  show ept (2 * ρ - ρ) = ept ρ
  congr 1; ring

theorem eptSh_zero (ρ : ℝ) : eptSh ρ 0 = ept (-ρ) := by
  show ept (0 - ρ) = ept (-ρ)
  congr 1; ring

/-- **Deliverable 1 (e).  Consistency of the endpoint traces.**  For a representative which is
continuous up to the boundary, the endpoint traces are the boundary values of `u` itself. -/
theorem trPlus_eq_of_continuous (hR : 0 < R) (hL : (Cm.K + Cp.K) * R < L)
    {u : H1P (thinDomain Cm Cp L R)}
    (hc : ContinuousOn u.toFun (closure (thinDomain Cm Cp L R))) {x : ℝ} (hg : SliceGood u x) :
    trPlus u x = u.toFun (x, ept (profile Cm Cp L R x)) ∧
      trMinus u x = u.toFun (x, ept (-(profile Cm Cp L R x))) := by
  have hmaps : MapsTo (fun t => ((x, eptSh (profile Cm Cp L R x) t) : CapSpace 1))
      (Icc 0 (2 * profile Cm Cp L R x)) (closure (thinDomain Cm Cp L R)) := by
    intro t ht
    show ((x, ept (t - profile Cm Cp L R x)) : CapSpace 1) ∈ _
    refine mem_closure_ept hR hL hg.mem ?_
    rw [abs_le]
    exact ⟨by linarith [ht.1], by linarith [ht.2]⟩
  have hcont : ContinuousOn (fun t => u.toFun (x, eptSh (profile Cm Cp L R x) t))
      (Icc 0 (2 * profile Cm Cp L R x)) :=
    hc.comp (continuous_const.prodMk (continuous_eptSh _)).continuousOn hmaps
  have heq := sliceRep_eqOn hg hcont Filter.EventuallyEq.rfl
  constructor
  · have h := (heq (mem_Icc_end hg)).symm
    rw [trPlus, h]
    simp only [eptSh_end]
  · have h := (heq (mem_Icc_zero hg)).symm
    rw [trMinus, h]
    simp only [eptSh_zero]

/-! ## 8. The a.e.-invariance -/

/-- Transport of an a.e. statement on the transverse ball to the interval `(0, 2ρ)`. -/
theorem ae_comp_eptSh {ρ : ℝ} {P : EuclideanSpace ℝ (Fin 1) → Prop}
    (h : ∀ᵐ z ∂(volume.restrict (ball (0 : EuclideanSpace ℝ (Fin 1)) ρ)), P z) :
    ∀ᵐ t ∂(volume.restrict (Ioo (0 : ℝ) (2 * ρ))), P (eptSh ρ t) := by
  have hmp : MeasurePreserving (eptSh ρ) (volume.restrict (Ioo (0 : ℝ) (2 * ρ)))
      (volume.restrict (ball (0 : EuclideanSpace ℝ (Fin 1)) ρ)) := by
    have h0 := (measurePreserving_eptSh ρ).restrict_preimage
      (measurableSet_ball (x := (0 : EuclideanSpace ℝ (Fin 1))) (ε := ρ))
    rwa [eptSh_preimage_ball ρ] at h0
  exact hmp.quasiMeasurePreserving.ae h

/-- If a function vanishes a.e. on `Ω_R`, then a.e. transverse slice vanishes a.e. -/
theorem ae_slice_ae_zero (hR : 0 < R) (hL : (Cm.K + Cp.K) * R < L) {f : CapSpace 1 → ℝ}
    (h : f =ᵐ[volume.restrict (thinDomain Cm Cp L R)] 0) :
    ∀ᵐ x ∂(volume.restrict (Ioo (-L / 2) (L / 2))),
      ∀ᵐ t ∂(volume.restrict (Ioo (0 : ℝ) (2 * profile Cm Cp L R x))),
        f (x, eptSh (profile Cm Cp L R x) t) = 0 := by
  have hΩ : MeasurableSet (thinDomain Cm Cp L R) := measurableSet_thinDomain hR hL
  have h1 : ∀ᵐ p ∂(volume : Measure (CapSpace 1)), p ∈ thinDomain Cm Cp L R → f p = 0 := by
    filter_upwards [(ae_restrict_iff' hΩ).1 h] with p hp hmem
    simpa using hp hmem
  rw [Measure.volume_eq_prod] at h1
  have h2 := Measure.ae_ae_of_ae_prod h1
  filter_upwards [ae_restrict_of_ae h2, ae_restrict_mem measurableSet_Ioo] with x hx hxI
  refine ae_comp_eptSh (P := fun z => f (x, z) = 0) ?_
  filter_upwards [ae_restrict_of_ae hx, ae_restrict_mem measurableSet_ball] with z hz hzb
  exact hz ⟨hxI.1, hxI.2, mem_ball_zero_iff.1 hzb⟩

/-- **Deliverable 1 (f).  The endpoint traces only see the a.e. class.** -/
theorem trPlus_eq_zero_of_ae_zero (hR : 0 < R) (hL : (Cm.K + Cp.K) * R < L)
    {u : H1P (thinDomain Cm Cp L R)}
    (h : u.toFun =ᵐ[volume.restrict (thinDomain Cm Cp L R)] 0) :
    ∀ᵐ x ∂(volume.restrict (Ioo (-L / 2) (L / 2))), trPlus u x = 0 ∧ trMinus u x = 0 := by
  filter_upwards [ae_sliceGood hR hL u, ae_slice_ae_zero hR hL h] with x hg hz
  have hw : (fun _ : ℝ => (0 : ℝ)) =ᵐ[volume.restrict (Ioo 0 (2 * profile Cm Cp L R x))]
      fun t => u.toFun (x, eptSh (profile Cm Cp L R x) t) := by
    filter_upwards [hz] with t ht
    rw [ht]
  have heq := sliceRep_eqOn hg continuousOn_const hw
  exact ⟨(heq (mem_Icc_end hg)).symm, (heq (mem_Icc_zero hg)).symm⟩

/-! ## 9. Deliverable 3: the remaining analytic hypothesis -/

/-- **The slice-wise trace inequality for the planar thin domain**, the single analytic fact
that this file does *not* prove.

It asks that the two endpoint traces be measurable in the axial variable, that the trace
density `A(x) (trPlus u x² + trMinus u x²)` be integrable on the axial interval, and that its
integral be controlled by the `H¹` energy `D[u] + N[u]`, uniformly in `u`.

**Why this is the remaining brick.**  The vertical slices used throughout this file *cannot*
give it.  On the segment `{x} × (−r(x), r(x))` the one-dimensional trace inequality
(`RobinCaps.Sobolev.trace_ineq`) reads
`|f(±r(x))|² ≤ C (r(x)⁻¹ ∫ |f|² + ∫ |f'|²)`, and the weight `r(x)⁻¹` blows up at the tips of
the two caps, where `r(x) → 0`, while the area element `A = √(1 + r'²)` stays bounded away from
zero there.  The vertical slicing is therefore off by a non-integrable factor near the tips.  A
genuine proof needs a Poincaré/trace argument adapted to the cap geometry — for instance
slicing along the inward normal of the lateral surface, or extending `u` across the lateral
boundary — which is exactly the analytic input that mathlib `v4.26.0` does not provide (no
Sobolev extension theorem for Lipschitz domains, no surface measure). -/
structure TraceIneqOne (Cm Cp : Cap 1) (L R : ℝ) : Prop where
  /-- The upper endpoint trace is a.e. measurable in the axial variable. -/
  aesm_trPlus : ∀ u : H1P (thinDomain Cm Cp L R),
    AEStronglyMeasurable (trPlus u) (volume.restrict (Ioo (-L / 2) (L / 2)))
  /-- The lower endpoint trace is a.e. measurable in the axial variable. -/
  aesm_trMinus : ∀ u : H1P (thinDomain Cm Cp L R),
    AEStronglyMeasurable (trMinus u) (volume.restrict (Ioo (-L / 2) (L / 2)))
  /-- The trace density is integrable along the axis. -/
  integrable : ∀ u : H1P (thinDomain Cm Cp L R),
    IntegrableOn (fun x => areaElement Cm Cp L R x * (trPlus u x ^ 2 + trMinus u x ^ 2))
      (Ioo (-L / 2) (L / 2)) volume
  /-- The trace inequality itself. -/
  bound : ∃ C : ℝ, ∀ u : H1P (thinDomain Cm Cp L R),
    (∫ x in Ioo (-L / 2) (L / 2),
        areaElement Cm Cp L R x * (trPlus u x ^ 2 + trMinus u x ^ 2))
      ≤ C * (dirichletP u + massP u)

/-! ## 10. The bilinear boundary form -/

theorem aesm_trPlusL (hR : 0 < R) (hL : (Cm.K + Cp.K) * R < L) (hti : TraceIneqOne Cm Cp L R)
    (u : H1P (thinDomain Cm Cp L R)) :
    AEStronglyMeasurable (trPlusL hR hL u) (volume.restrict (Ioo (-L / 2) (L / 2))) :=
  (hti.aesm_trPlus u).congr (trPlusL_ae hR hL u).symm

theorem aesm_trMinusL (hR : 0 < R) (hL : (Cm.K + Cp.K) * R < L) (hti : TraceIneqOne Cm Cp L R)
    (u : H1P (thinDomain Cm Cp L R)) :
    AEStronglyMeasurable (trMinusL hR hL u) (volume.restrict (Ioo (-L / 2) (L / 2))) :=
  (hti.aesm_trMinus u).congr (trMinusL_ae hR hL u).symm

theorem integrableOn_traceSqL (hR : 0 < R) (hL : (Cm.K + Cp.K) * R < L)
    (hti : TraceIneqOne Cm Cp L R) (u : H1P (thinDomain Cm Cp L R)) :
    IntegrableOn (fun x => areaElement Cm Cp L R x *
      (trPlusL hR hL u x ^ 2 + trMinusL hR hL u x ^ 2)) (Ioo (-L / 2) (L / 2)) volume := by
  refine (hti.integrable u).congr ?_
  filter_upwards [trPlusL_ae hR hL u, trMinusL_ae hR hL u] with x h1 h2
  rw [h1, h2]

/-- The elementary Cauchy-Schwarz bound behind the integrability of the mixed trace density. -/
theorem abs_mul_add_mul_le (A a b c d : ℝ) (hA : 0 ≤ A) :
    |A * (a * b + c * d)| ≤ 1 / 2 * (A * (a ^ 2 + c ^ 2) + A * (b ^ 2 + d ^ 2)) := by
  rw [abs_mul, abs_of_nonneg hA]
  have key : |a * b + c * d| ≤ 1 / 2 * ((a ^ 2 + c ^ 2) + (b ^ 2 + d ^ 2)) := by
    rw [abs_le]
    constructor <;>
      nlinarith [sq_nonneg (a + b), sq_nonneg (c + d), sq_nonneg (a - b), sq_nonneg (c - d)]
  nlinarith [key, hA, abs_nonneg (a * b + c * d)]

theorem integrableOn_traceProd (hR : 0 < R) (hL : (Cm.K + Cp.K) * R < L)
    (hti : TraceIneqOne Cm Cp L R) (u v : H1P (thinDomain Cm Cp L R)) :
    IntegrableOn (fun x => areaElement Cm Cp L R x *
      (trPlusL hR hL u x * trPlusL hR hL v x + trMinusL hR hL u x * trMinusL hR hL v x))
      (Ioo (-L / 2) (L / 2)) volume := by
  have hg : IntegrableOn (fun x => 1 / 2 *
      (areaElement Cm Cp L R x * (trPlusL hR hL u x ^ 2 + trMinusL hR hL u x ^ 2)
        + areaElement Cm Cp L R x * (trPlusL hR hL v x ^ 2 + trMinusL hR hL v x ^ 2)))
      (Ioo (-L / 2) (L / 2)) volume :=
    ((integrableOn_traceSqL hR hL hti u).add (integrableOn_traceSqL hR hL hti v)).const_mul _
  refine Integrable.mono' hg ?_ ?_
  · exact measurable_areaElement.aestronglyMeasurable.mul
      (((aesm_trPlusL hR hL hti u).mul (aesm_trPlusL hR hL hti v)).add
        ((aesm_trMinusL hR hL hti u).mul (aesm_trMinusL hR hL hti v)))
  · filter_upwards with x
    simpa only [Real.norm_eq_abs] using
      abs_mul_add_mul_le (areaElement Cm Cp L R x) (trPlusL hR hL u x) (trPlusL hR hL v x)
        (trMinusL hR hL u x) (trMinusL hR hL v x) (areaElement_nonneg x)

/-- The trace form, written with the linearised endpoint traces. -/
theorem traceForm_eqL (hR : 0 < R) (hL : (Cm.K + Cp.K) * R < L)
    (u v : H1P (thinDomain Cm Cp L R)) :
    traceForm hR hL u v = ∫ x in Ioo (-L / 2) (L / 2), areaElement Cm Cp L R x *
      (trPlusL hR hL u x * trPlusL hR hL v x + trMinusL hR hL u x * trMinusL hR hL v x) := by
  rw [traceForm_eq]
  refine integral_congr_ae ?_
  filter_upwards [trPlusL_ae hR hL u, trPlusL_ae hR hL v, trMinusL_ae hR hL u,
    trMinusL_ae hR hL v] with x h1 h2 h3 h4
  rw [h1, h2, h3, h4]

theorem traceForm_add_left (hR : 0 < R) (hL : (Cm.K + Cp.K) * R < L)
    (hti : TraceIneqOne Cm Cp L R) (u u' v : H1P (thinDomain Cm Cp L R)) :
    traceForm hR hL (u + u') v = traceForm hR hL u v + traceForm hR hL u' v := by
  rw [traceForm_eqL, traceForm_eqL, traceForm_eqL,
    ← integral_add (integrableOn_traceProd hR hL hti u v)
      (integrableOn_traceProd hR hL hti u' v)]
  refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
  simp only [map_add, Pi.add_apply]
  ring

theorem traceForm_smul_left (hR : 0 < R) (hL : (Cm.K + Cp.K) * R < L) (c : ℝ)
    (u v : H1P (thinDomain Cm Cp L R)) :
    traceForm hR hL (c • u) v = c * traceForm hR hL u v := by
  rw [traceForm_eqL, traceForm_eqL, ← integral_const_mul]
  refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
  simp only [map_smul, Pi.smul_apply, smul_eq_mul]
  ring

theorem traceForm_symm (hR : 0 < R) (hL : (Cm.K + Cp.K) * R < L)
    (u v : H1P (thinDomain Cm Cp L R)) : traceForm hR hL u v = traceForm hR hL v u := by
  rw [traceForm_eqL, traceForm_eqL]
  refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
  ring

/-- **The bilinear boundary form of the planar thin domain.** -/
def bdOne (hR : 0 < R) (hL : (Cm.K + Cp.K) * R < L) (hti : TraceIneqOne Cm Cp L R) :
    H1P (thinDomain Cm Cp L R) →ₗ[ℝ] H1P (thinDomain Cm Cp L R) →ₗ[ℝ] ℝ :=
  LinearMap.mk₂ ℝ (traceForm hR hL)
    (fun u u' v => traceForm_add_left hR hL hti u u' v)
    (fun c u v => by simpa only [smul_eq_mul] using traceForm_smul_left hR hL c u v)
    (fun u v v' => by
      rw [traceForm_symm hR hL u (v + v'), traceForm_add_left hR hL hti v v' u,
        traceForm_symm hR hL v u, traceForm_symm hR hL v' u])
    (fun c u v => by
      rw [traceForm_symm hR hL u (c • v), traceForm_smul_left hR hL c v u,
        traceForm_symm hR hL v u, smul_eq_mul])

@[simp] theorem bdOne_apply (hR : 0 < R) (hL : (Cm.K + Cp.K) * R < L)
    (hti : TraceIneqOne Cm Cp L R) (u v : H1P (thinDomain Cm Cp L R)) :
    bdOne hR hL hti u v = traceForm hR hL u v := rfl

theorem traceForm_self_eq (hR : 0 < R) (hL : (Cm.K + Cp.K) * R < L)
    (u : H1P (thinDomain Cm Cp L R)) :
    traceForm hR hL u u = ∫ x in Ioo (-L / 2) (L / 2),
      areaElement Cm Cp L R x * (trPlus u x ^ 2 + trMinus u x ^ 2) := by
  rw [traceForm_eq]
  refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
  ring

theorem traceForm_self_nonneg (hR : 0 < R) (hL : (Cm.K + Cp.K) * R < L)
    (u : H1P (thinDomain Cm Cp L R)) : 0 ≤ traceForm hR hL u u := by
  rw [traceForm_self_eq]
  refine setIntegral_nonneg measurableSet_Ioo fun x _ => ?_
  have := areaElement_nonneg (Cm := Cm) (Cp := Cp) (L := L) (R := R) x
  positivity

/-! ## 11. Deliverable 4: the trace data of the planar thin domain -/

/-- The boundary integral for `m = 1` when the two terminal radii vanish (hemispherical caps),
so that the end disks are degenerate. -/
theorem boundaryIntegral_one_eq' (hm0 : Cm.θ 0 = 0) (hp0 : Cp.θ 0 = 0) (g : CapSpace 1 → ℝ) :
    boundaryIntegral Cm Cp L R g
      = ∫ x in Ioo (-L / 2) (L / 2), areaElement Cm Cp L R x *
          (g (x, ept (profile Cm Cp L R x)) + g (x, ept (-(profile Cm Cp L R x)))) := by
  rw [boundaryIntegral, endDiskIntegralLeft, endDiskIntegralRight, hm0, hp0]
  simp only [mul_zero, ball_zero, Measure.restrict_empty, integral_zero_measure, add_zero]
  rw [lateralIntegral]
  exact setIntegral_congr_fun measurableSet_Ioo fun x _ => lateralDensity_one_eq g x

/-- **Deliverable 4.  The trace data of the planar thin domain**, constructed from the
slice-wise absolute continuity, with the trace inequality `hti` as the single hypothesis.

The two conditions `Cm.θ 0 = 0`, `Cp.θ 0 = 0` say that the caps *close up* (as the
hemispherical caps of the manuscript's counterexample do), so that the two end disks of
`∂Ω_R` are degenerate.  They are used only for the consistency field `tr_continuous`, which
compares the boundary form with the honest surface integral over the *whole* boundary. -/
def traceDataOne (hR : 0 < R) (hL : (Cm.K + Cp.K) * R < L) (hm0 : Cm.θ 0 = 0)
    (hp0 : Cp.θ 0 = 0) (hti : TraceIneqOne Cm Cp L R) : TraceData Cm Cp L R where
  tr := trOne hR hL
  tr_add := trOne_add hR hL
  tr_smul := trOne_smul hR hL
  bd := bdOne hR hL hti
  bd_eq := fun _ _ => rfl
  bd_symm := fun u v => traceForm_symm hR hL u v
  bd_nonneg := fun u => traceForm_self_nonneg hR hL u
  tr_continuous := by
    intro u hc
    show traceForm hR hL u u = boundaryEnergy Cm Cp L R u.toFun
    rw [traceForm_eq, boundaryEnergy, boundaryIntegral_one_eq' hm0 hp0]
    refine integral_congr_ae ?_
    filter_upwards [ae_sliceGood hR hL u] with x hg
    obtain ⟨e1, e2⟩ := trPlus_eq_of_continuous hR hL hc hg
    rw [e1, e2]
    ring
  trace_ineq := by
    obtain ⟨C, hC⟩ := hti.bound
    refine ⟨max C 0, le_max_right _ _, fun u => ?_⟩
    have hDN : 0 ≤ dirichletP u + massP u := add_nonneg (dirichletP_nonneg u) (massP_nonneg u)
    have h1 : traceForm hR hL u u ≤ C * (dirichletP u + massP u) := by
      rw [traceForm_self_eq]; exact hC u
    have h2 : C * (dirichletP u + massP u) ≤ max C 0 * (dirichletP u + massP u) :=
      mul_le_mul_of_nonneg_right (le_max_left _ _) hDN
    exact le_trans h1 h2
  vanishes_ae := by
    intro u h v
    show traceForm hR hL u v = 0
    rw [traceForm_eq]
    have : (∫ x in Ioo (-L / 2) (L / 2), areaElement Cm Cp L R x *
        (trPlus u x * trPlus v x + trMinus u x * trMinus v x))
        = ∫ _x in Ioo (-L / 2) (L / 2), (0 : ℝ) := by
      refine integral_congr_ae ?_
      filter_upwards [trPlus_eq_zero_of_ae_zero hR hL h] with x hx
      rw [hx.1, hx.2]
      ring
    rw [this, integral_zero]

/-- **The trace exists for the planar thin domain**, granted the trace inequality. -/
theorem hasTraceData_one (hR : 0 < R) (hL : (Cm.K + Cp.K) * R < L) (hm0 : Cm.θ 0 = 0)
    (hp0 : Cp.θ 0 = 0) (hti : TraceIneqOne Cm Cp L R) : HasTraceData Cm Cp L R :=
  ⟨traceDataOne hR hL hm0 hp0 hti⟩

/-! ## 12. Deliverable 5: compatibility with the transverse trace on the bulk -/

/-- **Compatibility with `RobinCaps.Transverse.bdTr`.**  If the transverse slice of `u` at an
axial coordinate `x` where the profile equals `R` is represented by an element `v` of the
transverse space `TransH1 1 R`, then the two endpoint traces of this file are the endpoint
traces `trEnd`, `trZero` used to build the transverse boundary form `bdTr R`. -/
theorem trPlus_eq_trEnd (hR : 0 < R) (_hL : (Cm.K + Cp.K) * R < L)
    {u : H1P (thinDomain Cm Cp L R)} {x : ℝ} (hg : SliceGood u x)
    (hx : profile Cm Cp L R x = R) (v : TransH1 1 R)
    (hv : v.toFun =ᵐ[volume.restrict (ball (0 : EuclideanSpace ℝ (Fin 1)) R)]
      fun z => u.toFun (x, z)) :
    trPlus u x = trEnd hR v ∧ trMinus u x = trZero hR v := by
  have hwc : ContinuousOn (rep hR v).toFun (Icc 0 (2 * profile Cm Cp L R x)) := by
    rw [hx]
    exact H1_continuousOn (by linarith) (rep hR v)
  have hw : (rep hR v).toFun =ᵐ[volume.restrict (Ioo 0 (2 * profile Cm Cp L R x))]
      fun t => u.toFun (x, eptSh (profile Cm Cp L R x) t) := by
    rw [hx]
    filter_upwards [rep_ae hR v, ae_comp_eptSh (P := fun z => v.toFun z = u.toFun (x, z)) hv]
      with t h1 h2
    rw [h1, h2]
  have heq := sliceRep_eqOn hg hwc hw
  refine ⟨?_, ?_⟩
  · have h := (heq (mem_Icc_end hg)).symm
    rw [trPlus, h, trEnd, hx]
  · have h := (heq (mem_Icc_zero hg)).symm
    rw [trMinus, h, trZero]

/-- **The trace density of this file is the transverse boundary form `bdTr R`, on the bulk.**
On the bulk interval the area element is `1` and the profile is `R`, so the integrand of
`traceForm u u` at `x` is exactly `bdTr R v v` for a transverse representative `v` of the
slice. -/
theorem traceDensity_bulk_eq (hR : 0 < R) (_hL : (Cm.K + Cp.K) * R < L)
    {u : H1P (thinDomain Cm Cp L R)} {x : ℝ}
    (hxb : x ∈ Ioo (-L / 2 + Cm.K * R) (L / 2 - Cp.K * R)) (hg : SliceGood u x)
    (v : TransH1 1 R)
    (hv : v.toFun =ᵐ[volume.restrict (ball (0 : EuclideanSpace ℝ (Fin 1)) R)]
      fun z => u.toFun (x, z)) :
    areaElement Cm Cp L R x * (trPlus u x * trPlus u x + trMinus u x * trMinus u x)
      = bdTr R v v := by
  have hprof : profile Cm Cp L R x = R := profile_bulk hxb.1.le hxb.2.le
  obtain ⟨e1, e2⟩ := trPlus_eq_trEnd hR _hL hg hprof v hv
  have hpow : (R : ℝ) ^ (1 - 1 : ℕ) = 1 := by norm_num
  rw [areaElement_bulk hxb.1 hxb.2, e1, e2, bdTr_apply hR, hpow, one_mul]
  ring

end RobinCaps.ThinDomain

end
