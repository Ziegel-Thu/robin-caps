import RobinCaps.Domain.Thin
import RobinCaps.ThinDomain.Polar
import RobinCaps.ThinDomain.H1P

/-!
# The boundary integral of the thin domain `Ω_R`, and the trace as data

This file defines the Robin boundary term

`α ∫_{∂Ω_R} |Tr u|² dℋ^{n-1}`  (manuscript `eq:robin-form`, with `n = m+1`, so `ℋ^m`)

**concretely**, through the revolution parametrisation of `∂Ω_R`, and packages the trace
operator as explicit **data** (`TraceData`).

## Why a concrete definition

Mathlib `v4.26.0` has no surface measure: `μH[d]` carries no normalisation constant, and on the
product type `CapSpace m = ℝ × EuclideanSpace ℝ (Fin m)` (which carries the *sup* norm) it is not
even proportional to the Euclidean surface measure — this is the reason recorded in the docstring
of `RobinCaps.Cap.F`.  The cap chapter therefore already *defines* `ℋ^m` of a boundary of
revolution by the classical area formula
(`Cap.lateralArea = m ω_m ∫_{-K}^0 θ^{m-1}√(1+θ'²)`, `Cap.terminalArea = ω_m θ(0)^m`), and this
file does exactly the same for the thin domain, so that the two layers are provably the same
boundary (`boundaryIntegral_one`).

## The boundary of `Ω_R` (manuscript, lines 180–222)

`Ω_R = {(x,z) : -L/2 < x < L/2, ‖z‖ < r_R(x)}` is a domain of revolution around the axis, with
radial profile `r_R = profile Cm Cp L R`.  Its boundary consists of

* the **lateral surface of revolution** `Γ_lat = {(x, r_R(x) ω) : -L/2 < x < L/2, ω ∈ S^{m-1}}`,
  whose area element in the coordinates `(x, ω) ↦ (x, r_R(x) ω)` is
  `r_R(x)^{m-1} √(1 + r_R'(x)²) dx dσ(ω)`  (`lateralIntegral`);
* the two **end disks** `{∓L/2} × B_m(R θ∓(0))`, which are non-degenerate exactly when the
  terminal radii `θ∓(0)` are positive (`endDiskIntegralLeft`, `endDiskIntegralRight`).

The two *interface* disks carry no boundary contribution — they lie inside `Ω_R` (manuscript,
line 207) — and indeed they are interior points of the axial interval, of measure zero for the
axial integral.

## Main definitions

* `lateralDensity`, `lateralIntegral`, `endDiskIntegralLeft/Right`, `boundaryIntegral`,
  `boundaryEnergy` — the boundary integral `∫_{∂Ω_R} g dℋ^m` of a **pointwise** function `g`;
* `TraceData Cm Cp L R` — the trace operator of the manuscript, as data: a boundary
  representative `tr`, the induced bilinear boundary form `bd`, and the recorded assumptions
  (`bd_eq`, `bd_symm`, `bd_nonneg`, `tr_continuous`, `trace_ineq`, `vanishes_ae`);
* `robinFormP td α u = dirichletP u + α * bd u u` — the Robin form `q_{Ω_R}` of `eq:robin-form`;
* `HasTraceData` — the target asserting that such data exists.

## Main results

* `boundaryIntegral_one` — the **normalisation check**:
  `ℋ^m(∂Ω_R) = R^m (|Γ₋| + |Γ₊|) + m ω_m R^{m-1} ℓ_R`, with `|Γ∓|` the cap areas of
  `RobinCaps/Cap/Basic.lean`.  This is what pins the definition to the manuscript's
  normalisation and to the cap chapter;
* `lateralDensity_bulk`, `lateralIntegral_bulk` — on the bulk the density is
  `R^{m-1} ∫_{S^{m-1}} g(x, Rω) dσ`, i.e. the cylindrical surface integral;
* `boundaryIntegral_nonneg`, `boundaryIntegral_add`, `boundaryIntegral_const_mul`,
  `boundaryEnergy_nonneg`.

No `sorry`, `admit`, `axiom` or `native_decide` occurs in this file.  The only unproven facts are
the **fields** of `TraceData` (documented there) and the `Prop`-valued target `HasTraceData`.
-/

open MeasureTheory Set Metric Filter
open scoped ENNReal Topology

noncomputable section

namespace RobinCaps.ThinDomain

open RobinCaps.Domain

/-! ## 0. Two substitution lemmas for interval integrability

The analogues, for `IntervalIntegrable`, of `RobinCaps.Domain.integral_comp_left` and
`integral_comp_right`. -/

/-- Integrability transfers along the left-cap substitution `x = -L/2 - R s`. -/
theorem intervalIntegrable_comp_left {f : ℝ → ℝ} (K R L : ℝ) (hR : 0 < R)
    (hf : IntervalIntegrable f volume (-K) 0) :
    IntervalIntegrable (fun x => f ((-L/2 - x) / R)) volume (-L/2) (-L/2 + K * R) := by
  have h1 : IntervalIntegrable (fun t => f (R⁻¹ * t)) volume ((-K) / R⁻¹) ((0 : ℝ) / R⁻¹) :=
    hf.comp_mul_left
  have e1 : (-K) / R⁻¹ = -(K * R) := by field_simp
  have e2 : (0 : ℝ) / R⁻¹ = 0 := by simp
  rw [e1, e2] at h1
  have h2 := h1.comp_sub_left (-L/2)
  have e3 : -L/2 - -(K * R) = -L/2 + K * R := by ring
  have e4 : -L/2 - (0 : ℝ) = -L/2 := by ring
  rw [e3, e4] at h2
  have h3 : IntervalIntegrable (fun x : ℝ => f (R⁻¹ * (-L/2 - x))) volume
      (-L/2 + K * R) (-L/2) := h2
  have hfe : (fun x : ℝ => f (R⁻¹ * (-L/2 - x))) = fun x : ℝ => f ((-L/2 - x) / R) := by
    funext x; congr 1; ring
  rw [hfe] at h3
  exact h3.symm

/-- Integrability transfers along the right-cap substitution `x = L/2 + R s`. -/
theorem intervalIntegrable_comp_right {f : ℝ → ℝ} (K R L : ℝ) (hR : 0 < R)
    (hf : IntervalIntegrable f volume (-K) 0) :
    IntervalIntegrable (fun x => f ((x - L/2) / R)) volume (L/2 - K * R) (L/2) := by
  have h1 : IntervalIntegrable (fun t => f (R⁻¹ * t)) volume ((-K) / R⁻¹) ((0 : ℝ) / R⁻¹) :=
    hf.comp_mul_left
  have e1 : (-K) / R⁻¹ = -(K * R) := by field_simp
  have e2 : (0 : ℝ) / R⁻¹ = 0 := by simp
  rw [e1, e2] at h1
  have h2 := h1.comp_sub_right (L/2)
  have e3 : -(K * R) + L/2 = L/2 - K * R := by ring
  have e4 : (0 : ℝ) + L/2 = L/2 := by ring
  rw [e3, e4] at h2
  have h3 : IntervalIntegrable (fun x : ℝ => f (R⁻¹ * (x - L/2))) volume
      (L/2 - K * R) (L/2) := h2
  have hfe : (fun x : ℝ => f (R⁻¹ * (x - L/2))) = fun x : ℝ => f ((x - L/2) / R) := by
    funext x; congr 1; ring
  rwa [hfe] at h3

variable {m : ℕ} {Cm Cp : Cap m} {L R : ℝ}

/-! ## 1. The area element -/

/-- The area element `θ^{m-1} √(1 + θ'²)` of a cap profile — the integrand of
`RobinCaps.Cap.lateralArea`. -/
def capAreaElement (C : Cap m) (s : ℝ) : ℝ :=
  C.θ s ^ (m - 1) * Real.sqrt (1 + deriv C.θ s ^ 2)

theorem lateralArea_eq (C : Cap m) :
    C.lateralArea = (m : ℝ) * omega m * ∫ s in (-C.K)..0, capAreaElement C s := rfl

/-- The area element `r_R^{m-1} √(1 + r_R'²)` of the lateral surface of revolution of `Ω_R`. -/
def areaElement (Cm Cp : Cap m) (L R : ℝ) (x : ℝ) : ℝ :=
  profile Cm Cp L R x ^ (m - 1) *
    Real.sqrt (1 + deriv (profile Cm Cp L R) x ^ 2)

/-! ### The derivative of the profile on the three branches -/

/-- On the left cap the profile has derivative `-θ₋'((-L/2-x)/R)` (chain rule through the
rescaling `x ↦ (-L/2-x)/R`).  No differentiability hypothesis is needed: mathlib's junk value
`0` propagates through an affine substitution. -/
theorem deriv_profile_left (hR : 0 < R) {x : ℝ} (hx : x < -L/2 + Cm.K * R) :
    deriv (profile Cm Cp L R) x = -deriv Cm.θ ((-L/2 - x) / R) := by
  have hEv : profile Cm Cp L R =ᶠ[𝓝 x] fun y => R * (Cm.θ <| R⁻¹ * ·) (-L/2 - y) := by
    refine Filter.eventuallyEq_of_mem (Iio_mem_nhds hx) fun y hy => ?_
    rw [profile_left hy]
    simp only [div_eq_inv_mul]
  have h2 := deriv_comp_const_sub (Cm.θ <| R⁻¹ * ·) (-L/2) x
  have h3 := deriv_comp_mul_left R⁻¹ Cm.θ (-L/2 - x)
  rw [hEv.deriv_eq, deriv_const_mul_field, h2, h3, smul_eq_mul, mul_neg, ← mul_assoc,
    mul_inv_cancel₀ hR.ne', one_mul, ← div_eq_inv_mul]

/-- On the right cap the profile has derivative `θ₊'((x-L/2)/R)`. -/
theorem deriv_profile_right (hR : 0 < R) (hL : (Cm.K + Cp.K) * R < L) {x : ℝ}
    (hx : L/2 - Cp.K * R < x) :
    deriv (profile Cm Cp L R) x = deriv Cp.θ ((x - L/2) / R) := by
  have hmid := interface_lt (Cm := Cm) (Cp := Cp) hR hL
  have hEv : profile Cm Cp L R =ᶠ[𝓝 x] fun y => R * (Cp.θ <| R⁻¹ * ·) (y - L/2) := by
    refine Filter.eventuallyEq_of_mem (Ioi_mem_nhds hx) fun y hy => ?_
    rw [profile_right (le_of_lt (lt_trans hmid hy)) hy]
    simp only [div_eq_inv_mul]
  have h2 := deriv_comp_sub_const (Cp.θ <| R⁻¹ * ·) (L/2) x
  have h3 := deriv_comp_mul_left R⁻¹ Cp.θ (x - L/2)
  rw [hEv.deriv_eq, deriv_const_mul_field, h2, h3, smul_eq_mul, ← mul_assoc,
    mul_inv_cancel₀ hR.ne', one_mul, ← div_eq_inv_mul]

/-- On the (open) bulk the profile is constant, hence has vanishing derivative. -/
theorem deriv_profile_bulk {x : ℝ} (h1 : -L/2 + Cm.K * R < x) (h2 : x < L/2 - Cp.K * R) :
    deriv (profile Cm Cp L R) x = 0 := by
  have hEv : profile Cm Cp L R =ᶠ[𝓝 x] fun _ => R :=
    Filter.eventuallyEq_of_mem (Ioo_mem_nhds h1 h2) fun y hy => profile_bulk hy.1.le hy.2.le
  rw [hEv.deriv_eq, deriv_const]

theorem areaElement_left (hR : 0 < R) {x : ℝ} (hx : x < -L/2 + Cm.K * R) :
    areaElement Cm Cp L R x = R ^ (m - 1) * capAreaElement Cm ((-L/2 - x) / R) := by
  rw [areaElement, capAreaElement, profile_left hx, deriv_profile_left hR hx, mul_pow, neg_pow_two]
  ring

theorem areaElement_right (hR : 0 < R) (hL : (Cm.K + Cp.K) * R < L) {x : ℝ}
    (hx : L/2 - Cp.K * R < x) :
    areaElement Cm Cp L R x = R ^ (m - 1) * capAreaElement Cp ((x - L/2) / R) := by
  have hmid := interface_lt (Cm := Cm) (Cp := Cp) hR hL
  rw [areaElement, capAreaElement, profile_right (le_of_lt (lt_trans hmid hx)) hx,
    deriv_profile_right hR hL hx, mul_pow]
  ring

theorem areaElement_bulk {x : ℝ} (h1 : -L/2 + Cm.K * R < x) (h2 : x < L/2 - Cp.K * R) :
    areaElement Cm Cp L R x = R ^ (m - 1) := by
  rw [areaElement, profile_bulk h1.le h2.le, deriv_profile_bulk h1 h2]
  simp

/-! ## 2. The boundary integral -/

/-- The integrand of `lateralIntegral`: the area element times the spherical average of `g`
over the transverse sphere of radius `r_R(x)`. -/
def lateralDensity (Cm Cp : Cap m) (L R : ℝ) (g : CapSpace m → ℝ) (x : ℝ) : ℝ :=
  profile Cm Cp L R x ^ (m - 1) *
      Real.sqrt (1 + deriv (profile Cm Cp L R) x ^ 2) *
    ∫ ω : sphere (0 : EuclideanSpace ℝ (Fin m)) 1,
      g (x, profile Cm Cp L R x • (ω : EuclideanSpace ℝ (Fin m))) ∂(sphereMeasure m)

/-- **The lateral boundary integral** `∫_{Γ_lat} g dℋ^m`, written in the revolution coordinates
`(x, ω) ↦ (x, r_R(x) ω)` with the classical area element `r^{m-1}√(1+r'²)`. -/
def lateralIntegral (Cm Cp : Cap m) (L R : ℝ) (g : CapSpace m → ℝ) : ℝ :=
  ∫ x in Ioo (-L/2) (L/2), lateralDensity Cm Cp L R g x

theorem lateralIntegral_eq (g : CapSpace m → ℝ) :
    lateralIntegral Cm Cp L R g
      = ∫ x in Ioo (-L/2) (L/2), profile Cm Cp L R x ^ (m - 1) *
          Real.sqrt (1 + deriv (profile Cm Cp L R) x ^ 2) *
          ∫ ω : sphere (0 : EuclideanSpace ℝ (Fin m)) 1,
            g (x, profile Cm Cp L R x • (ω : EuclideanSpace ℝ (Fin m))) ∂(sphereMeasure m) := rfl

theorem lateralDensity_eq_sphereIntegral (g : CapSpace m → ℝ) (x : ℝ) :
    lateralDensity Cm Cp L R g x
      = Real.sqrt (1 + deriv (profile Cm Cp L R) x ^ 2) *
          sphereIntegral m (profile Cm Cp L R x) (fun z => g (x, z)) := by
  rw [lateralDensity, sphereIntegral]; ring

/-- **On the bulk the lateral density is the cylindrical one**: `R^{m-1} ∫_{S^{m-1}} g(x,Rω)`. -/
theorem lateralDensity_bulk (g : CapSpace m → ℝ) {x : ℝ} (h1 : -L/2 + Cm.K * R < x)
    (h2 : x < L/2 - Cp.K * R) :
    lateralDensity Cm Cp L R g x
      = R ^ (m - 1) * ∫ ω : sphere (0 : EuclideanSpace ℝ (Fin m)) 1,
          g (x, R • (ω : EuclideanSpace ℝ (Fin m))) ∂(sphereMeasure m) := by
  rw [lateralDensity, profile_bulk h1.le h2.le, deriv_profile_bulk h1 h2]
  simp

/-- **The bulk part of the lateral integral is the cylindrical one**: over the bulk interval
`I_R = (x₋, x₊)` the lateral integral is `R^{m-1} ∫_{I_R} ∫_{S^{m-1}} g(x, Rω) dσ(ω) dx`, i.e.
the surface integral over the cylinder `I_R × ∂B_m(R)`. -/
theorem lateralIntegral_bulk (g : CapSpace m → ℝ) :
    ∫ x in Ioo (-L/2 + Cm.K * R) (L/2 - Cp.K * R), lateralDensity Cm Cp L R g x
      = R ^ (m - 1) * ∫ x in Ioo (-L/2 + Cm.K * R) (L/2 - Cp.K * R),
          ∫ ω : sphere (0 : EuclideanSpace ℝ (Fin m)) 1,
            g (x, R • (ω : EuclideanSpace ℝ (Fin m))) ∂(sphereMeasure m) := by
  rw [setIntegral_congr_fun measurableSet_Ioo (fun x hx => lateralDensity_bulk g hx.1 hx.2),
    integral_const_mul]

/-- The left **end disk** `{-L/2} × B_m(R θ₋(0))`: it is a genuine part of `∂Ω_R` exactly when
the terminal radius `θ₋(0)` is positive (`Cap.Gamma` of the cap chapter contains the terminal
disk for the same reason). -/
def endDiskIntegralLeft (Cm : Cap m) (L R : ℝ) (g : CapSpace m → ℝ) : ℝ :=
  ∫ z in ball (0 : EuclideanSpace ℝ (Fin m)) (R * Cm.θ 0), g (-L/2, z)

/-- The right **end disk** `{L/2} × B_m(R θ₊(0))`. -/
def endDiskIntegralRight (Cp : Cap m) (L R : ℝ) (g : CapSpace m → ℝ) : ℝ :=
  ∫ z in ball (0 : EuclideanSpace ℝ (Fin m)) (R * Cp.θ 0), g (L/2, z)

/-- **The boundary integral** `∫_{∂Ω_R} g dℋ^m`: lateral surface plus the two end disks. -/
def boundaryIntegral (Cm Cp : Cap m) (L R : ℝ) (g : CapSpace m → ℝ) : ℝ :=
  lateralIntegral Cm Cp L R g + endDiskIntegralLeft Cm L R g + endDiskIntegralRight Cp L R g

/-- The **boundary energy** `∫_{∂Ω_R} u² dℋ^m` of a pointwise function `u`; this is the
quantity multiplied by `α` in `eq:robin-form`, for `u` a boundary representative. -/
def boundaryEnergy (Cm Cp : Cap m) (L R : ℝ) (u : CapSpace m → ℝ) : ℝ :=
  boundaryIntegral Cm Cp L R (fun p => u p ^ 2)

theorem boundaryIntegral_sq (u : CapSpace m → ℝ) :
    boundaryEnergy Cm Cp L R u = boundaryIntegral Cm Cp L R (fun p => u p ^ 2) := rfl

/-! ## 3. The normalisation check: the total surface area -/

/-- `|B_m(r)| = r^m ω_m` as a real number, for `r ≥ 0` and `m ≥ 1`. -/
theorem volume_ball_toReal (m : ℕ) (hm : 1 ≤ m) {r : ℝ} (hr : 0 ≤ r) :
    (volume (ball (0 : EuclideanSpace ℝ (Fin m)) r)).toReal = r ^ m * omega m := by
  rcases eq_or_lt_of_le hr with h | h
  · have hb : ball (0 : EuclideanSpace ℝ (Fin m)) r = ∅ := by
      rw [← h]; exact ball_zero
    rw [hb, measure_empty, ENNReal.toReal_zero, ← h, zero_pow (by omega), zero_mul]
  · rw [Cap.volume_ball_eq_pow_mul m h, ENNReal.toReal_mul,
      ENNReal.toReal_ofReal (by positivity)]
    rfl

theorem integral_sphere_one (m : ℕ) (hm : 1 ≤ m) :
    ∫ _ω : sphere (0 : EuclideanSpace ℝ (Fin m)) 1, (1 : ℝ) ∂(sphereMeasure m)
      = (m : ℝ) * omega m := by
  rw [integral_const, measureReal_def, sphere_measure_univ m hm, smul_eq_mul, mul_one]

theorem lateralDensity_one (hm : 1 ≤ m) (x : ℝ) :
    lateralDensity Cm Cp L R (fun _ => 1) x
      = (m : ℝ) * omega m * areaElement Cm Cp L R x := by
  rw [lateralDensity, areaElement, integral_sphere_one m hm]; ring

/-! ### Interval integrability of the area element on the three pieces -/

theorem intervalIntegrable_areaElement_left (hR : 0 < R) :
    IntervalIntegrable (areaElement Cm Cp L R) volume (-L/2) (-L/2 + Cm.K * R) := by
  have hl := left_lt_interface (Cm := Cm) (L := L) hR
  have hF : IntervalIntegrable (capAreaElement Cm) volume (-Cm.K) 0 :=
    Cap.Concave.areaElement_intervalIntegrable Cm
  have h4 : IntervalIntegrable (fun x => R ^ (m - 1) * capAreaElement Cm ((-L/2 - x) / R))
      volume (-L/2) (-L/2 + Cm.K * R) :=
    (intervalIntegrable_comp_left Cm.K R L hR hF).const_mul _
  rw [intervalIntegrable_iff_integrableOn_Ioo_of_le hl.le] at h4 ⊢
  exact h4.congr_fun (fun x hx => (areaElement_left hR hx.2).symm) measurableSet_Ioo

theorem intervalIntegrable_areaElement_right (hR : 0 < R) (hL : (Cm.K + Cp.K) * R < L) :
    IntervalIntegrable (areaElement Cm Cp L R) volume (L/2 - Cp.K * R) (L/2) := by
  have hr := interface_lt_right (Cp := Cp) (L := L) hR
  have hF : IntervalIntegrable (capAreaElement Cp) volume (-Cp.K) 0 :=
    Cap.Concave.areaElement_intervalIntegrable Cp
  have h4 : IntervalIntegrable (fun x => R ^ (m - 1) * capAreaElement Cp ((x - L/2) / R))
      volume (L/2 - Cp.K * R) (L/2) :=
    (intervalIntegrable_comp_right Cp.K R L hR hF).const_mul _
  rw [intervalIntegrable_iff_integrableOn_Ioo_of_le hr.le] at h4 ⊢
  exact h4.congr_fun (fun x hx => (areaElement_right hR hL hx.1).symm) measurableSet_Ioo

theorem intervalIntegrable_areaElement_bulk (hR : 0 < R) (hL : (Cm.K + Cp.K) * R < L) :
    IntervalIntegrable (areaElement Cm Cp L R) volume (-L/2 + Cm.K * R) (L/2 - Cp.K * R) := by
  have hmid := interface_lt (Cm := Cm) (Cp := Cp) hR hL
  have h4 : IntervalIntegrable (fun _ : ℝ => R ^ (m - 1)) volume
      (-L/2 + Cm.K * R) (L/2 - Cp.K * R) := intervalIntegrable_const
  rw [intervalIntegrable_iff_integrableOn_Ioo_of_le hmid.le] at h4 ⊢
  exact h4.congr_fun (fun x hx => (areaElement_bulk hx.1 hx.2).symm) measurableSet_Ioo

/-! ### The three-piece splitting of the axial integral -/

theorem integral_areaElement_left (hR : 0 < R) :
    ∫ x in (-L/2)..(-L/2 + Cm.K * R), areaElement Cm Cp L R x
      = R ^ (m - 1) * R * ∫ s in (-Cm.K)..0, capAreaElement Cm s := by
  have hl := left_lt_interface (Cm := Cm) (L := L) hR
  have hEq : EqOn (areaElement Cm Cp L R)
      (fun x => R ^ (m - 1) * capAreaElement Cm ((-L/2 - x) / R))
      (Ioo (-L/2) (-L/2 + Cm.K * R)) := fun x hx => areaElement_left hR hx.2
  rw [integral_congr_Ioo hl.le hEq, intervalIntegral.integral_const_mul,
    integral_comp_left Cm.K R L hR.ne' (capAreaElement Cm), mul_assoc]

theorem integral_areaElement_right (hR : 0 < R) (hL : (Cm.K + Cp.K) * R < L) :
    ∫ x in (L/2 - Cp.K * R)..(L/2), areaElement Cm Cp L R x
      = R ^ (m - 1) * R * ∫ s in (-Cp.K)..0, capAreaElement Cp s := by
  have hr := interface_lt_right (Cp := Cp) (L := L) hR
  have hEq : EqOn (areaElement Cm Cp L R)
      (fun x => R ^ (m - 1) * capAreaElement Cp ((x - L/2) / R))
      (Ioo (L/2 - Cp.K * R) (L/2)) := fun x hx => areaElement_right hR hL hx.1
  rw [integral_congr_Ioo hr.le hEq, intervalIntegral.integral_const_mul,
    integral_comp_right Cp.K R L hR.ne' (capAreaElement Cp), mul_assoc]

theorem integral_areaElement_bulk (hR : 0 < R) (hL : (Cm.K + Cp.K) * R < L) :
    ∫ x in (-L/2 + Cm.K * R)..(L/2 - Cp.K * R), areaElement Cm Cp L R x
      = R ^ (m - 1) * bulkLength Cm Cp L R := by
  have hmid := interface_lt (Cm := Cm) (Cp := Cp) hR hL
  have hEq : EqOn (areaElement Cm Cp L R) (fun _ => R ^ (m - 1))
      (Ioo (-L/2 + Cm.K * R) (L/2 - Cp.K * R)) := fun x hx => areaElement_bulk hx.1 hx.2
  rw [integral_congr_Ioo hmid.le hEq, intervalIntegral.integral_const, smul_eq_mul, bulkLength]
  ring

/-- **The axial integral of the area element**, split into the two caps and the bulk. -/
theorem integral_areaElement (hR : 0 < R) (hL : (Cm.K + Cp.K) * R < L) :
    ∫ x in Ioo (-L/2) (L/2), areaElement Cm Cp L R x
      = R ^ (m - 1) * R * ((∫ s in (-Cm.K)..0, capAreaElement Cm s)
          + ∫ s in (-Cp.K)..0, capAreaElement Cp s)
        + R ^ (m - 1) * bulkLength Cm Cp L R := by
  have hL0 : 0 < L := span_pos (Cm := Cm) (Cp := Cp) hR hL
  have i1 := intervalIntegrable_areaElement_left (Cm := Cm) (Cp := Cp) (L := L) hR
  have i2 := intervalIntegrable_areaElement_bulk (Cm := Cm) (Cp := Cp) hR hL
  have i3 := intervalIntegrable_areaElement_right (Cm := Cm) (Cp := Cp) hR hL
  have hIoo : ∫ x in Ioo (-L/2) (L/2), areaElement Cm Cp L R x
      = ∫ x in (-L/2)..(L/2), areaElement Cm Cp L R x := by
    rw [intervalIntegral.integral_of_le (by linarith), integral_Ioc_eq_integral_Ioo]
  rw [hIoo, ← intervalIntegral.integral_add_adjacent_intervals (i1.trans i2) i3,
    ← intervalIntegral.integral_add_adjacent_intervals i1 i2,
    integral_areaElement_left hR, integral_areaElement_bulk hR hL,
    integral_areaElement_right hR hL]
  ring

theorem lateralIntegral_one (hm : 1 ≤ m) (hR : 0 < R) (hL : (Cm.K + Cp.K) * R < L) :
    lateralIntegral Cm Cp L R (fun _ => 1)
      = R ^ m * (Cm.lateralArea + Cp.lateralArea)
        + (m : ℝ) * omega m * R ^ (m - 1) * bulkLength Cm Cp L R := by
  have hpow : R ^ (m - 1) * R = R ^ m := by
    rw [← pow_succ]; congr 1; omega
  rw [lateralIntegral, setIntegral_congr_fun measurableSet_Ioo
      (fun x _ => lateralDensity_one hm x), integral_const_mul, integral_areaElement hR hL,
    lateralArea_eq, lateralArea_eq, hpow]
  ring

theorem endDiskIntegralLeft_one (hm : 1 ≤ m) (hR : 0 < R) (hθ : 0 ≤ Cm.θ 0) :
    endDiskIntegralLeft Cm L R (fun _ => 1) = R ^ m * Cm.terminalArea := by
  rw [endDiskIntegralLeft, setIntegral_const, measureReal_def,
    volume_ball_toReal m hm (by positivity), smul_eq_mul, mul_one, Cap.terminalArea, mul_pow]
  ring

theorem endDiskIntegralRight_one (hm : 1 ≤ m) (hR : 0 < R) (hθ : 0 ≤ Cp.θ 0) :
    endDiskIntegralRight Cp L R (fun _ => 1) = R ^ m * Cp.terminalArea := by
  rw [endDiskIntegralRight, setIntegral_const, measureReal_def,
    volume_ball_toReal m hm (by positivity), smul_eq_mul, mul_one, Cap.terminalArea, mul_pow]
  ring

/-- **The total surface area of `∂Ω_R`** (the normalisation check).

`ℋ^m(∂Ω_R) = R^m (|Γ₋| + |Γ₊|) + m ω_m R^{m-1} ℓ_R`, where `|Γ∓| = lateralArea + terminalArea`
are the cap areas of `RobinCaps/Cap/Basic.lean` and `ℓ_R = L - (K₋+K₊)R` is the bulk length.
This is the statement that the revolution definition of `boundaryIntegral` carries exactly the
manuscript's normalisation, and that it is the *same* boundary as the one used by the cap
chapter.

The two hypotheses `0 ≤ Cm.θ 0`, `0 ≤ Cp.θ 0` say that the terminal radii are nonnegative;
the `Cap` structure constrains `θ` only on `(-K,0)`, so `θ 0` is otherwise unconstrained, while
`Cap.terminalArea` uses the value `θ 0`.  (For a left-continuous profile they hold automatically,
since `θ > 0` on `(-K,0)`.) -/
theorem boundaryIntegral_one (hm : 1 ≤ m) (hR : 0 < R) (hL : (Cm.K + Cp.K) * R < L)
    (hm0 : 0 ≤ Cm.θ 0) (hp0 : 0 ≤ Cp.θ 0) :
    boundaryIntegral Cm Cp L R (fun _ => 1)
      = R ^ m * (Cm.lateralArea + Cm.terminalArea + Cp.lateralArea + Cp.terminalArea)
        + (m : ℝ) * omega m * R ^ (m - 1) * bulkLength Cm Cp L R := by
  rw [boundaryIntegral, lateralIntegral_one hm hR hL, endDiskIntegralLeft_one hm hR hm0,
    endDiskIntegralRight_one hm hR hp0]
  ring

/-- The same, in terms of `Cap.revolutionArea = lateralArea + terminalArea`. -/
theorem boundaryIntegral_one' (hm : 1 ≤ m) (hR : 0 < R) (hL : (Cm.K + Cp.K) * R < L)
    (hm0 : 0 ≤ Cm.θ 0) (hp0 : 0 ≤ Cp.θ 0) :
    boundaryIntegral Cm Cp L R (fun _ => 1)
      = R ^ m * (Cm.revolutionArea + Cp.revolutionArea)
        + (m : ℝ) * omega m * R ^ (m - 1) * bulkLength Cm Cp L R := by
  rw [boundaryIntegral_one hm hR hL hm0 hp0, Cap.revolutionArea, Cap.revolutionArea]
  ring

/-! ## 4. Positivity and linearity -/

theorem lateralIntegral_nonneg (hR : 0 < R) (hL : (Cm.K + Cp.K) * R < L)
    {g : CapSpace m → ℝ} (hg : ∀ p, 0 ≤ g p) : 0 ≤ lateralIntegral Cm Cp L R g := by
  refine setIntegral_nonneg measurableSet_Ioo fun x hx => ?_
  have hp : 0 ≤ profile Cm Cp L R x := (profile_pos hR hL hx).le
  have h1 : 0 ≤ ∫ ω : sphere (0 : EuclideanSpace ℝ (Fin m)) 1,
      g (x, profile Cm Cp L R x • (ω : EuclideanSpace ℝ (Fin m))) ∂(sphereMeasure m) :=
    integral_nonneg fun _ => hg _
  have h2 : (0:ℝ) ≤ Real.sqrt (1 + deriv (profile Cm Cp L R) x ^ 2) := Real.sqrt_nonneg _
  have h3 : (0:ℝ) ≤ profile Cm Cp L R x ^ (m - 1) := pow_nonneg hp _
  exact mul_nonneg (mul_nonneg h3 h2) h1

theorem endDiskIntegralLeft_nonneg {g : CapSpace m → ℝ} (hg : ∀ p, 0 ≤ g p) :
    0 ≤ endDiskIntegralLeft Cm L R g :=
  setIntegral_nonneg measurableSet_ball fun _ _ => hg _

theorem endDiskIntegralRight_nonneg {g : CapSpace m → ℝ} (hg : ∀ p, 0 ≤ g p) :
    0 ≤ endDiskIntegralRight Cp L R g :=
  setIntegral_nonneg measurableSet_ball fun _ _ => hg _

/-- **Monotone positivity**: the boundary integral of a nonnegative function is nonnegative. -/
theorem boundaryIntegral_nonneg (hR : 0 < R) (hL : (Cm.K + Cp.K) * R < L)
    {g : CapSpace m → ℝ} (hg : ∀ p, 0 ≤ g p) : 0 ≤ boundaryIntegral Cm Cp L R g := by
  have h1 := lateralIntegral_nonneg hR hL hg
  have h2 := endDiskIntegralLeft_nonneg (Cm := Cm) (L := L) (R := R) hg
  have h3 := endDiskIntegralRight_nonneg (Cp := Cp) (L := L) (R := R) hg
  simp only [boundaryIntegral]
  linarith

/-- The boundary energy `∫_{∂Ω} u²` is nonnegative. -/
theorem boundaryEnergy_nonneg (hR : 0 < R) (hL : (Cm.K + Cp.K) * R < L) (u : CapSpace m → ℝ) :
    0 ≤ boundaryEnergy Cm Cp L R u :=
  boundaryIntegral_nonneg hR hL fun _ => sq_nonneg _

/-! ### Linearity -/

theorem lateralDensity_const_mul (c : ℝ) (g : CapSpace m → ℝ) (x : ℝ) :
    lateralDensity Cm Cp L R (fun p => c * g p) x = c * lateralDensity Cm Cp L R g x := by
  simp only [lateralDensity, integral_const_mul]; ring

theorem lateralIntegral_const_mul (c : ℝ) (g : CapSpace m → ℝ) :
    lateralIntegral Cm Cp L R (fun p => c * g p) = c * lateralIntegral Cm Cp L R g := by
  simp only [lateralIntegral, lateralDensity_const_mul, integral_const_mul]

theorem endDiskIntegralLeft_const_mul (c : ℝ) (g : CapSpace m → ℝ) :
    endDiskIntegralLeft Cm L R (fun p => c * g p) = c * endDiskIntegralLeft Cm L R g := by
  simp only [endDiskIntegralLeft, integral_const_mul]

theorem endDiskIntegralRight_const_mul (c : ℝ) (g : CapSpace m → ℝ) :
    endDiskIntegralRight Cp L R (fun p => c * g p) = c * endDiskIntegralRight Cp L R g := by
  simp only [endDiskIntegralRight, integral_const_mul]

/-- **Homogeneity** of the boundary integral (no integrability hypothesis is needed). -/
theorem boundaryIntegral_const_mul (c : ℝ) (g : CapSpace m → ℝ) :
    boundaryIntegral Cm Cp L R (fun p => c * g p) = c * boundaryIntegral Cm Cp L R g := by
  simp only [boundaryIntegral, lateralIntegral_const_mul, endDiskIntegralLeft_const_mul,
    endDiskIntegralRight_const_mul]
  ring

/-- The spherical integrability hypothesis needed to split the lateral density of a sum. -/
def SphereIntegrableOn (Cm Cp : Cap m) (L R : ℝ) (g : CapSpace m → ℝ) : Prop :=
  ∀ x ∈ Ioo (-L/2) (L/2), Integrable (fun ω : sphere (0 : EuclideanSpace ℝ (Fin m)) 1 =>
    g (x, profile Cm Cp L R x • (ω : EuclideanSpace ℝ (Fin m)))) (sphereMeasure m)

theorem lateralDensity_add {g₁ g₂ : CapSpace m → ℝ} {x : ℝ}
    (h₁ : Integrable (fun ω : sphere (0 : EuclideanSpace ℝ (Fin m)) 1 =>
      g₁ (x, profile Cm Cp L R x • (ω : EuclideanSpace ℝ (Fin m)))) (sphereMeasure m))
    (h₂ : Integrable (fun ω : sphere (0 : EuclideanSpace ℝ (Fin m)) 1 =>
      g₂ (x, profile Cm Cp L R x • (ω : EuclideanSpace ℝ (Fin m)))) (sphereMeasure m)) :
    lateralDensity Cm Cp L R (fun p => g₁ p + g₂ p) x
      = lateralDensity Cm Cp L R g₁ x + lateralDensity Cm Cp L R g₂ x := by
  simp only [lateralDensity]
  rw [integral_add h₁ h₂]
  ring

theorem lateralIntegral_add {g₁ g₂ : CapSpace m → ℝ}
    (hs₁ : SphereIntegrableOn Cm Cp L R g₁) (hs₂ : SphereIntegrableOn Cm Cp L R g₂)
    (h₁ : IntegrableOn (lateralDensity Cm Cp L R g₁) (Ioo (-L/2) (L/2)))
    (h₂ : IntegrableOn (lateralDensity Cm Cp L R g₂) (Ioo (-L/2) (L/2))) :
    lateralIntegral Cm Cp L R (fun p => g₁ p + g₂ p)
      = lateralIntegral Cm Cp L R g₁ + lateralIntegral Cm Cp L R g₂ := by
  rw [lateralIntegral, setIntegral_congr_fun measurableSet_Ioo
    (fun x hx => lateralDensity_add (hs₁ x hx) (hs₂ x hx)), integral_add h₁ h₂]
  rfl

theorem endDiskIntegralLeft_add {g₁ g₂ : CapSpace m → ℝ}
    (h₁ : IntegrableOn (fun z => g₁ (-L/2, z)) (ball (0 : EuclideanSpace ℝ (Fin m)) (R * Cm.θ 0)))
    (h₂ : IntegrableOn (fun z => g₂ (-L/2, z))
      (ball (0 : EuclideanSpace ℝ (Fin m)) (R * Cm.θ 0))) :
    endDiskIntegralLeft Cm L R (fun p => g₁ p + g₂ p)
      = endDiskIntegralLeft Cm L R g₁ + endDiskIntegralLeft Cm L R g₂ := by
  simp only [endDiskIntegralLeft]
  exact integral_add h₁ h₂

theorem endDiskIntegralRight_add {g₁ g₂ : CapSpace m → ℝ}
    (h₁ : IntegrableOn (fun z => g₁ (L/2, z)) (ball (0 : EuclideanSpace ℝ (Fin m)) (R * Cp.θ 0)))
    (h₂ : IntegrableOn (fun z => g₂ (L/2, z))
      (ball (0 : EuclideanSpace ℝ (Fin m)) (R * Cp.θ 0))) :
    endDiskIntegralRight Cp L R (fun p => g₁ p + g₂ p)
      = endDiskIntegralRight Cp L R g₁ + endDiskIntegralRight Cp L R g₂ := by
  simp only [endDiskIntegralRight]
  exact integral_add h₁ h₂

/-- **Additivity** of the boundary integral, under the integrability hypotheses that make each
of the three pieces additive. -/
theorem boundaryIntegral_add {g₁ g₂ : CapSpace m → ℝ}
    (hs₁ : SphereIntegrableOn Cm Cp L R g₁) (hs₂ : SphereIntegrableOn Cm Cp L R g₂)
    (h₁ : IntegrableOn (lateralDensity Cm Cp L R g₁) (Ioo (-L/2) (L/2)))
    (h₂ : IntegrableOn (lateralDensity Cm Cp L R g₂) (Ioo (-L/2) (L/2)))
    (d₁ : IntegrableOn (fun z => g₁ (-L/2, z)) (ball (0 : EuclideanSpace ℝ (Fin m)) (R * Cm.θ 0)))
    (d₂ : IntegrableOn (fun z => g₂ (-L/2, z)) (ball (0 : EuclideanSpace ℝ (Fin m)) (R * Cm.θ 0)))
    (e₁ : IntegrableOn (fun z => g₁ (L/2, z)) (ball (0 : EuclideanSpace ℝ (Fin m)) (R * Cp.θ 0)))
    (e₂ : IntegrableOn (fun z => g₂ (L/2, z))
      (ball (0 : EuclideanSpace ℝ (Fin m)) (R * Cp.θ 0))) :
    boundaryIntegral Cm Cp L R (fun p => g₁ p + g₂ p)
      = boundaryIntegral Cm Cp L R g₁ + boundaryIntegral Cm Cp L R g₂ := by
  simp only [boundaryIntegral, lateralIntegral_add hs₁ hs₂ h₁ h₂,
    endDiskIntegralLeft_add d₁ d₂, endDiskIntegralRight_add e₁ e₂]
  ring

/-! ## 5. The trace operator, as data -/

/-- **The trace operator of the manuscript, as explicit data.**

`eq:robin-form` uses the trace `Tr : H¹(Ω_R) → L²(∂Ω_R)` of a bounded Lipschitz domain.  The
thin domain `Ω_R` *is* bounded, Lipschitz and (manuscript, line 205) convex, so the trace exists
and is bounded by the standard theory — but **mathlib `v4.26.0` has no trace theorem** (it has
neither a surface measure nor the Sobolev extension/compactness machinery; see the targets
`RobinCaps.Sobolev.Weak.TraceExists`, `TraceInequality`, `RellichEmbedding`).  Rather than
pretend, the trace is taken here as *data* and everything downstream is stated for a given
`TraceData`.  This is the same device as `RobinCaps.ThinDomain.TransverseGroundState` in
`RobinCaps/ThinDomain/GroundState.lean` (where the boundary form `bd` was likewise a parameter).

The fields are:

* `tr u` — a **boundary representative** of `u`, i.e. a pointwise function on `CapSpace m` whose
  values on the revolution parametrisation of `∂Ω_R` are the boundary values of `u`;
* `tr_add`, `tr_smul` — linearity of the representative;
* `bd` — the induced **boundary bilinear form**, bundled as a genuine `ℝ`-bilinear map (this is
  the formulation that lets `bd` feed the abstract spectral engine of
  `RobinCaps/Spectrum/*`, which expects `LinearMap`s);
* `bd_eq` — `bd u v` **is** the concrete revolution boundary integral of `(tr u)(tr v)`; this is
  the link between the analytic assumption and the explicit geometry of this file;
* `bd_symm`, `bd_nonneg` — symmetry and nonnegativity of the boundary form (they follow from
  `bd_eq` and `boundaryIntegral_nonneg` for representatives, but are recorded so that the form
  may also be given abstractly);
* `tr_continuous` — **consistency**: on functions continuous up to the boundary the trace is the
  restriction, i.e. the boundary energy is the honest `∫_{∂Ω_R} u² dℋ^m`;
* `trace_ineq` — the **trace inequality** `∫_{∂Ω} |Tr u|² ≤ C (D[u] + N[u])`, which is what makes
  the Robin form closed and bounded below (the target
  `RobinCaps.Sobolev.Weak.TraceInequality`, transported to `H1P`);
* `vanishes_ae` — the trace kills elements whose representative vanishes a.e. on `Ω_R`, which is
  what lets the Robin form descend to the a.e. quotient (as in
  `RobinCaps/Sobolev/Quotient.lean`).

**Nothing in this file constructs a `TraceData`.** -/
structure TraceData (Cm Cp : Cap m) (L R : ℝ) where
  /-- The boundary representative of an `H¹` element. -/
  tr : H1P (thinDomain Cm Cp L R) → (CapSpace m → ℝ)
  /-- The representative is additive. -/
  tr_add : ∀ u v, tr (u + v) = tr u + tr v
  /-- The representative is homogeneous. -/
  tr_smul : ∀ (c : ℝ) (u), tr (c • u) = c • tr u
  /-- The boundary bilinear form `(u,v) ↦ ∫_{∂Ω_R} (Tr u)(Tr v) dℋ^m`. -/
  bd : H1P (thinDomain Cm Cp L R) →ₗ[ℝ] H1P (thinDomain Cm Cp L R) →ₗ[ℝ] ℝ
  /-- The bilinear form is the concrete revolution boundary integral. -/
  bd_eq : ∀ u v, bd u v = boundaryIntegral Cm Cp L R (fun p => tr u p * tr v p)
  /-- The boundary form is symmetric. -/
  bd_symm : ∀ u v, bd u v = bd v u
  /-- The boundary form is nonnegative on the diagonal. -/
  bd_nonneg : ∀ u, 0 ≤ bd u u
  /-- On functions continuous up to the boundary the trace is the restriction. -/
  tr_continuous : ∀ u : H1P (thinDomain Cm Cp L R),
    ContinuousOn u.toFun (closure (thinDomain Cm Cp L R)) →
      bd u u = boundaryEnergy Cm Cp L R u.toFun
  /-- The trace inequality: the boundary energy is controlled by the `H¹` energy. -/
  trace_ineq : ∃ C : ℝ, 0 ≤ C ∧ ∀ u, bd u u ≤ C * (dirichletP u + massP u)
  /-- The boundary form only sees the a.e. class of the representative. -/
  vanishes_ae : ∀ u, u.toFun =ᵐ[volume.restrict (thinDomain Cm Cp L R)] 0 → ∀ v, bd u v = 0

namespace TraceData

variable {Cm Cp : Cap m} {L R : ℝ}

theorem bd_sq (td : TraceData Cm Cp L R) (u : H1P (thinDomain Cm Cp L R)) :
    td.bd u u = boundaryEnergy Cm Cp L R (td.tr u) := by
  rw [td.bd_eq u u, boundaryEnergy]
  simp only [sq]

theorem bd_add_left (td : TraceData Cm Cp L R) (u v w : H1P (thinDomain Cm Cp L R)) :
    td.bd (u + v) w = td.bd u w + td.bd v w := by
  rw [map_add]; rfl

theorem bd_smul_left (td : TraceData Cm Cp L R) (c : ℝ) (u v : H1P (thinDomain Cm Cp L R)) :
    td.bd (c • u) v = c * td.bd u v := by
  rw [map_smul]; rfl

theorem bd_add_right (td : TraceData Cm Cp L R) (u v w : H1P (thinDomain Cm Cp L R)) :
    td.bd u (v + w) = td.bd u v + td.bd u w := map_add _ _ _

theorem bd_smul_right (td : TraceData Cm Cp L R) (c : ℝ) (u v : H1P (thinDomain Cm Cp L R)) :
    td.bd u (c • v) = c * td.bd u v := map_smul _ _ _

/-- The boundary form only depends on the a.e. class (both variables), by bilinearity. -/
theorem bd_congr_ae_left (td : TraceData Cm Cp L R) {u u' : H1P (thinDomain Cm Cp L R)}
    (h : (u - u').toFun =ᵐ[volume.restrict (thinDomain Cm Cp L R)] 0)
    (v : H1P (thinDomain Cm Cp L R)) : td.bd u v = td.bd u' v := by
  have h0 : td.bd (u - u') v = 0 := td.vanishes_ae _ h v
  rw [map_sub] at h0
  have : td.bd u v - td.bd u' v = 0 := h0
  linarith

end TraceData

/-- **The Robin quadratic form of the thin domain** (manuscript `eq:robin-form`):
`q_{Ω_R}[u] = ∫_{Ω_R} |∇u|² + α ∫_{∂Ω_R} |Tr u|² dℋ^m`, for a given trace datum. -/
def robinFormP (td : TraceData Cm Cp L R) (α : ℝ) (u : H1P (thinDomain Cm Cp L R)) : ℝ :=
  dirichletP u + α * td.bd u u

theorem robinFormP_eq (td : TraceData Cm Cp L R) (α : ℝ) (u : H1P (thinDomain Cm Cp L R)) :
    robinFormP td α u
      = dirichletP u + α * boundaryIntegral Cm Cp L R (fun p => td.tr u p * td.tr u p) := by
  rw [robinFormP, td.bd_eq]

/-- For `α ≥ 0` — the case of the manuscript — the Robin form is nonnegative. -/
theorem robinFormP_nonneg (td : TraceData Cm Cp L R) {α : ℝ} (hα : 0 ≤ α)
    (u : H1P (thinDomain Cm Cp L R)) : 0 ≤ robinFormP td α u := by
  have h1 := dirichletP_nonneg u
  have h2 := td.bd_nonneg u
  have : 0 ≤ α * td.bd u u := mul_nonneg hα h2
  simp only [robinFormP]
  linarith

/-- For `α ≥ 0` the Robin form dominates the Dirichlet energy. -/
theorem dirichletP_le_robinFormP (td : TraceData Cm Cp L R) {α : ℝ} (hα : 0 ≤ α)
    (u : H1P (thinDomain Cm Cp L R)) : dirichletP u ≤ robinFormP td α u := by
  have : 0 ≤ α * td.bd u u := mul_nonneg hα (td.bd_nonneg u)
  simp only [robinFormP]
  linarith

/-- The Robin form is bounded above by a multiple of the `H¹` energy (from `trace_ineq`). -/
theorem robinFormP_le (td : TraceData Cm Cp L R) {α : ℝ} (hα : 0 ≤ α) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ u : H1P (thinDomain Cm Cp L R),
      robinFormP td α u ≤ (1 + α * C) * (dirichletP u + massP u) := by
  obtain ⟨C, hC0, hC⟩ := td.trace_ineq
  refine ⟨C, hC0, fun u => ?_⟩
  have h1 := dirichletP_nonneg u
  have h2 := massP_nonneg u
  have h3 : α * td.bd u u ≤ α * (C * (dirichletP u + massP u)) :=
    mul_le_mul_of_nonneg_left (hC u) hα
  simp only [robinFormP]
  nlinarith

/-- **Target: existence of the trace operator on the thin domain.**

A construction needs, in the order of `RobinCaps/Sobolev/WEAK_REPORT.md` §C.3(2):

1. the slice-wise ACL property in the radial variable — for a.e. axial `x` and a.e. direction
   `ω ∈ S^{m-1}`, the map `r ↦ u(x, r ω)` is an element of the one-dimensional weak space
   `RobinCaps.Sobolev.H1` with derivative `⟪∇_z u, ω⟫`; the statement of the transverse half is
   already recorded as `RobinCaps.ThinDomain.SliceACL` in `RobinCaps/ThinDomain/H1P.lean`;
2. the one-dimensional trace inequality `RobinCaps.Sobolev.trace_ineq` (already **proved**, in
   `RobinCaps/Sobolev/Interval.lean`), applied on each radial segment and multiplied by the area
   element `r^{m-1}√(1+r'²)`, then integrated `dσ(ω) dx` — the polar formula
   `RobinCaps.ThinDomain.integral_ball_polar` of `RobinCaps/ThinDomain/Polar.lean` recognises the
   right-hand side as `C(R) (massP u + dirichletP u)`;
3. the density of `C¹(closure Ω_R)` in `H1P (thinDomain Cm Cp L R)` (mathlib has no Sobolev
   extension theorem for Lipschitz domains), which is what upgrades the inequality from the
   smooth class `H1P.ofCompactSupport` to all of `H1P` and gives `tr_continuous`.

Steps 1 and 3 are the missing analytic bricks. -/
def HasTraceData (Cm Cp : Cap m) (L R : ℝ) : Prop := Nonempty (TraceData Cm Cp L R)

end RobinCaps.ThinDomain
