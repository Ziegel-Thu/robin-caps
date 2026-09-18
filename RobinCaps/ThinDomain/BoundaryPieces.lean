import RobinCaps.ThinDomain.Boundary
import RobinCaps.ThinDomain.Rescale

/-!
# The three axial pieces of the boundary integral of `Ω_R`

This file computes the pieces of the boundary term of the trial-function upper bound
(manuscript `eq:trial-extension`, and the boundary integrals of `sec:proof` / `sec:cap-lemma`):

* the **lateral integral splits** into the two cap pieces and the bulk piece
  (`lateralIntegral_split`);
* on the **bulk** the lateral integral of a tensor-type function `F(x) h(z)` factorises as
  `(∫_{I_R} F) · ∫_{∂B_m(R)} h` (`lateralIntegral_bulk_tensor`), and for `(F ⊗ h)²` with a
  radial `h` this is `(∫ F²) · m ω_m R^{m-1} h_r(R)²`;
* on the **caps** the lateral integral is `R^m` times the *unit cap's* own lateral boundary
  integral of the rescaled function (`lateralIntegral_leftCap_eq`,
  `lateralIntegral_rightCap_eq`), and the end disks are `R^m` times the unit cap's terminal disk
  integrals (`endDiskIntegralLeft_eq`, `endDiskIntegralRight_eq`);
* consistency with the cap chapter: `capLateralIntegral C 1 = C.lateralArea`
  (`capLateralIntegral_one`), so that the splitting with `g = 1` reproduces
  `RobinCaps.ThinDomain.boundaryIntegral_one`.

Everything is assembled in `boundaryIntegral_split` and `boundaryEnergy_tensor_split`.

No `sorry`, `admit`, `axiom` or `native_decide` occurs in this file.
-/

open MeasureTheory Set Metric Filter

noncomputable section

namespace RobinCaps.ThinDomain

open RobinCaps.Domain

variable {m : ℕ} {Cm Cp : Cap m} {L R : ℝ}

/-! ## 0. Two elementary rewriting lemmas -/

/-- An interval integral over `[a,b]` with `a ≤ b` is the set integral over `Ioo a b`. -/
theorem intervalIntegral_eq_integral_Ioo {a b : ℝ} (hab : a ≤ b) (f : ℝ → ℝ) :
    ∫ x in a..b, f x = ∫ x in Ioo a b, f x := by
  rw [intervalIntegral.integral_of_le hab, integral_Ioc_eq_integral_Ioo]

/-- The lateral density is the area element times the spherical average — a restatement of the
definition that isolates `areaElement`. -/
theorem lateralDensity_eq_areaElement (g : CapSpace m → ℝ) (x : ℝ) :
    lateralDensity Cm Cp L R g x
      = areaElement Cm Cp L R x *
          ∫ ω : sphere (0 : EuclideanSpace ℝ (Fin m)) 1,
            g (x, profile Cm Cp L R x • (ω : EuclideanSpace ℝ (Fin m))) ∂(sphereMeasure m) := rfl

/-! ## 1. The three-piece splitting of the lateral integral -/

/-- **Splitting of the lateral integral** into the left cap piece, the bulk piece and the right
cap piece, for a general integrand `g`, under interval integrability of the density on the three
pieces.  The bulk piece is written over the *closed* interval `[x₋, x₊]` (the two interface
circles are Lebesgue-null for the axial integral), matching `bulkCylinder`. -/
theorem lateralIntegral_split (hR : 0 < R) (hL : (Cm.K + Cp.K) * R < L) (g : CapSpace m → ℝ)
    (h₁ : IntegrableOn (lateralDensity Cm Cp L R g) (Ioo (-L/2) (-L/2 + Cm.K * R)))
    (h₂ : IntegrableOn (lateralDensity Cm Cp L R g)
      (Ioo (-L/2 + Cm.K * R) (L/2 - Cp.K * R)))
    (h₃ : IntegrableOn (lateralDensity Cm Cp L R g) (Ioo (L/2 - Cp.K * R) (L/2))) :
    lateralIntegral Cm Cp L R g
      = (∫ x in Ioo (-L/2) (-L/2 + Cm.K * R), lateralDensity Cm Cp L R g x)
        + (∫ x in Icc (-L/2 + Cm.K * R) (L/2 - Cp.K * R), lateralDensity Cm Cp L R g x)
        + (∫ x in Ioo (L/2 - Cp.K * R) (L/2), lateralDensity Cm Cp L R g x) := by
  have hl := left_lt_interface (Cm := Cm) (L := L) hR
  have hmid := interface_lt (Cm := Cm) (Cp := Cp) hR hL
  have hr := interface_lt_right (Cp := Cp) (L := L) hR
  have i₁ : IntervalIntegrable (lateralDensity Cm Cp L R g) volume (-L/2) (-L/2 + Cm.K * R) := by
    rw [intervalIntegrable_iff_integrableOn_Ioo_of_le hl.le]; exact h₁
  have i₂ : IntervalIntegrable (lateralDensity Cm Cp L R g) volume
      (-L/2 + Cm.K * R) (L/2 - Cp.K * R) := by
    rw [intervalIntegrable_iff_integrableOn_Ioo_of_le hmid.le]; exact h₂
  have i₃ : IntervalIntegrable (lateralDensity Cm Cp L R g) volume (L/2 - Cp.K * R) (L/2) := by
    rw [intervalIntegrable_iff_integrableOn_Ioo_of_le hr.le]; exact h₃
  rw [lateralIntegral, ← intervalIntegral_eq_integral_Ioo (by linarith : (-L/2 : ℝ) ≤ L/2),
    ← intervalIntegral.integral_add_adjacent_intervals (i₁.trans i₂) i₃,
    ← intervalIntegral.integral_add_adjacent_intervals i₁ i₂,
    intervalIntegral_eq_integral_Ioo hl.le, intervalIntegral_eq_integral_Ioo hmid.le,
    intervalIntegral_eq_integral_Ioo hr.le, integral_Icc_eq_integral_Ioo]

/-! ## 2. The bulk piece for tensor-type functions -/

/-- On the bulk, the lateral density of a **tensor function** `g(x,z) = F(x) h(z)` factorises:
it is `F(x)` times the spherical integral of `h` over `∂B_m(R)`. -/
theorem lateralDensity_bulk_tensor (F : ℝ → ℝ) (h : EuclideanSpace ℝ (Fin m) → ℝ) {x : ℝ}
    (h1 : -L/2 + Cm.K * R < x) (h2 : x < L/2 - Cp.K * R) :
    lateralDensity Cm Cp L R (fun p => F p.1 * h p.2) x = F x * sphereIntegral m R h := by
  rw [lateralDensity_bulk (Cm := Cm) (Cp := Cp) _ h1 h2, sphereIntegral]
  simp only []
  rw [integral_const_mul]
  ring

/-- **The bulk piece of the lateral integral of a tensor function**:
`∫_{I_R} ∫_{∂B_m(R)} F(x) h(z) = (∫_{I_R} F) · (∫_{∂B_m(R)} h)`. -/
theorem lateralIntegral_bulk_tensor (F : ℝ → ℝ) (h : EuclideanSpace ℝ (Fin m) → ℝ) :
    (∫ x in Icc (-L/2 + Cm.K * R) (L/2 - Cp.K * R),
        lateralDensity Cm Cp L R (fun p => F p.1 * h p.2) x)
      = (∫ x in Icc (-L/2 + Cm.K * R) (L/2 - Cp.K * R), F x) * sphereIntegral m R h := by
  rw [integral_Icc_eq_integral_Ioo, integral_Icc_eq_integral_Ioo,
    setIntegral_congr_fun measurableSet_Ioo
      (fun x hx => lateralDensity_bulk_tensor (Cm := Cm) (Cp := Cp) F h hx.1 hx.2),
    integral_mul_const]

/-- The same for the **squared** tensor function `(F ⊗ h)²`, which is the shape of the boundary
energy of the manuscript's trial function on the bulk. -/
theorem lateralIntegral_bulk_tensor_sq (F : ℝ → ℝ) (h : EuclideanSpace ℝ (Fin m) → ℝ) :
    (∫ x in Icc (-L/2 + Cm.K * R) (L/2 - Cp.K * R),
        lateralDensity Cm Cp L R (fun p => (F p.1 * h p.2) ^ 2) x)
      = (∫ x in Icc (-L/2 + Cm.K * R) (L/2 - Cp.K * R), F x ^ 2)
          * sphereIntegral m R (fun z => h z ^ 2) := by
  have hsq : (fun p : CapSpace m => (F p.1 * h p.2) ^ 2)
      = fun p : CapSpace m => (fun x => F x ^ 2) p.1 * (fun z => h z ^ 2) p.2 := by
    funext p; exact mul_pow _ _ _
  rw [hsq]
  exact lateralIntegral_bulk_tensor (Cm := Cm) (Cp := Cp) (fun x => F x ^ 2) (fun z => h z ^ 2)

/-- For a **radial** transverse factor `h(z) = h_r(‖z‖)` the transverse boundary integral is
explicit: `∫_{∂B_m(R)} h² = m ω_m R^{m-1} h_r(R)²`. -/
theorem sphereIntegral_radial_sq (hm : 1 ≤ m) (hR : 0 < R) (hr : ℝ → ℝ) :
    sphereIntegral m R (fun z => hr ‖z‖ ^ 2)
      = (m : ℝ) * omega m * R ^ (m - 1) * hr R ^ 2 :=
  sphereIntegral_radial m hm hR (fun r => hr r ^ 2)

/-- The bulk piece for a squared tensor function with a **radial** transverse factor, fully
explicit. -/
theorem lateralIntegral_bulk_tensor_sq_radial (hm : 1 ≤ m) (hR : 0 < R) (F : ℝ → ℝ)
    (hr : ℝ → ℝ) :
    (∫ x in Icc (-L/2 + Cm.K * R) (L/2 - Cp.K * R),
        lateralDensity Cm Cp L R (fun p => (F p.1 * hr ‖p.2‖) ^ 2) x)
      = (∫ x in Icc (-L/2 + Cm.K * R) (L/2 - Cp.K * R), F x ^ 2)
          * ((m : ℝ) * omega m * R ^ (m - 1) * hr R ^ 2) := by
  rw [lateralIntegral_bulk_tensor_sq (Cm := Cm) (Cp := Cp) F (fun z => hr ‖z‖),
    sphereIntegral_radial_sq hm hR hr]

/-! ## 3. The cap pieces, by rescaling -/

/-- The lateral boundary density of the **unit cap**: the area element `θ^{m-1}√(1+θ'²)` times
the spherical average of `G` over the transverse sphere of radius `θ(s)`. -/
def capLateralDensity (C : Cap m) (G : CapSpace m → ℝ) (s : ℝ) : ℝ :=
  capAreaElement C s *
    ∫ ω : sphere (0 : EuclideanSpace ℝ (Fin m)) 1,
      G (s, C.θ s • (ω : EuclideanSpace ℝ (Fin m))) ∂(sphereMeasure m)

/-- **The lateral boundary integral `∫_{Γ_lat} G dℋ^m` of the unit cap** `C`, in the revolution
coordinates `(s, ω) ↦ (s, θ(s) ω)`.  For `G = 1` this is `Cap.lateralArea`
(`capLateralIntegral_one`). -/
def capLateralIntegral (C : Cap m) (G : CapSpace m → ℝ) : ℝ :=
  ∫ s in Ioo (-C.K) 0, capLateralDensity C G s

/-- **Consistency with the cap chapter**: the unit cap's lateral boundary integral of the
constant `1` is `Cap.lateralArea`. -/
theorem capLateralIntegral_one (C : Cap m) (hm : 1 ≤ m) :
    capLateralIntegral C (fun _ => 1) = C.lateralArea := by
  have h0 : (-C.K : ℝ) ≤ 0 := by linarith [C.hK]
  have hpt : ∀ s : ℝ, capLateralDensity C (fun _ => (1 : ℝ)) s
      = (m : ℝ) * omega m * capAreaElement C s := by
    intro s
    rw [capLateralDensity]
    simp only []
    rw [integral_sphere_one m hm]
    ring
  rw [capLateralIntegral, setIntegral_congr_fun measurableSet_Ioo (fun s _ => hpt s),
    integral_const_mul, lateralArea_eq, intervalIntegral_eq_integral_Ioo h0]

/-- On the **left cap** the lateral density of `g` is `R^{m-1}` times the unit cap's lateral
density of the rescaled function `G(s,z) = g(-L/2 - R s, R z)`, evaluated at `s = (-L/2-x)/R`. -/
theorem lateralDensity_left_eq (hR : 0 < R) (g : CapSpace m → ℝ) {x : ℝ}
    (hx : x < -L/2 + Cm.K * R) :
    lateralDensity Cm Cp L R g x
      = R ^ (m - 1) *
          capLateralDensity Cm (fun p => g (-L/2 - R * p.1, R • p.2)) ((-L/2 - x) / R) := by
  have hsval : -L/2 - R * ((-L/2 - x) / R) = x := by field_simp; ring
  have hpt : ∀ ω : sphere (0 : EuclideanSpace ℝ (Fin m)) 1,
      g (-L/2 - R * ((-L/2 - x) / R),
          R • (Cm.θ ((-L/2 - x) / R) • (ω : EuclideanSpace ℝ (Fin m))))
        = g (x, profile Cm Cp L R x • (ω : EuclideanSpace ℝ (Fin m))) := by
    intro ω
    rw [hsval, smul_smul, profile_left (Cp := Cp) hx]
  rw [capLateralDensity]
  simp only [hpt]
  rw [lateralDensity_eq_areaElement, areaElement_left (Cp := Cp) hR hx]
  ring

/-- On the **right cap** the lateral density of `g` is `R^{m-1}` times the unit cap's lateral
density of `G(s,z) = g(L/2 + R s, R z)`, evaluated at `s = (x-L/2)/R`. -/
theorem lateralDensity_right_eq (hR : 0 < R) (hL : (Cm.K + Cp.K) * R < L) (g : CapSpace m → ℝ)
    {x : ℝ} (hx : L/2 - Cp.K * R < x) :
    lateralDensity Cm Cp L R g x
      = R ^ (m - 1) *
          capLateralDensity Cp (fun p => g (L/2 + R * p.1, R • p.2)) ((x - L/2) / R) := by
  have hmid := interface_lt (Cm := Cm) (Cp := Cp) hR hL
  have hsval : L/2 + R * ((x - L/2) / R) = x := by field_simp; ring
  have hpt : ∀ ω : sphere (0 : EuclideanSpace ℝ (Fin m)) 1,
      g (L/2 + R * ((x - L/2) / R),
          R • (Cp.θ ((x - L/2) / R) • (ω : EuclideanSpace ℝ (Fin m))))
        = g (x, profile Cm Cp L R x • (ω : EuclideanSpace ℝ (Fin m))) := by
    intro ω
    rw [hsval, smul_smul, profile_right (le_of_lt (lt_trans hmid hx)) hx]
  rw [capLateralDensity]
  simp only [hpt]
  rw [lateralDensity_eq_areaElement, areaElement_right hR hL hx]
  ring

/-- **The left cap piece of the lateral integral**: it is `R^m` times the *unit* cap's lateral
boundary integral of the rescaled function `G(s,z) = g(-L/2 - R s, R z)`.

This is the boundary half of the rescaling `affP (-L/2) (-1) R` of
`RobinCaps/ThinDomain/Rescale.lean`, which maps the unit cap body onto `leftCap Cm L R`. -/
theorem lateralIntegral_leftCap_eq (hm : 1 ≤ m) (hR : 0 < R) (g : CapSpace m → ℝ) :
    (∫ x in Ioo (-L/2) (-L/2 + Cm.K * R), lateralDensity Cm Cp L R g x)
      = R ^ m * capLateralIntegral Cm (fun p => g (-L/2 - R * p.1, R • p.2)) := by
  have hl := left_lt_interface (Cm := Cm) (L := L) hR
  have h0 : (-Cm.K : ℝ) ≤ 0 := by linarith [Cm.hK]
  have hpow : R ^ (m - 1) * R = R ^ m := by rw [← pow_succ]; congr 1; omega
  rw [← intervalIntegral_eq_integral_Ioo hl.le,
    integral_congr_Ioo hl.le
      (fun x hx => lateralDensity_left_eq (Cp := Cp) hR g hx.2),
    intervalIntegral.integral_const_mul,
    integral_comp_left Cm.K R L hR.ne'
      (capLateralDensity Cm (fun p => g (-L/2 - R * p.1, R • p.2))),
    capLateralIntegral, ← intervalIntegral_eq_integral_Ioo h0, ← hpow]
  ring

/-- **The right cap piece of the lateral integral**: `R^m` times the unit cap's lateral boundary
integral of `G(s,z) = g(L/2 + R s, R z)`. -/
theorem lateralIntegral_rightCap_eq (hm : 1 ≤ m) (hR : 0 < R) (hL : (Cm.K + Cp.K) * R < L)
    (g : CapSpace m → ℝ) :
    (∫ x in Ioo (L/2 - Cp.K * R) (L/2), lateralDensity Cm Cp L R g x)
      = R ^ m * capLateralIntegral Cp (fun p => g (L/2 + R * p.1, R • p.2)) := by
  have hr := interface_lt_right (Cp := Cp) (L := L) hR
  have h0 : (-Cp.K : ℝ) ≤ 0 := by linarith [Cp.hK]
  have hpow : R ^ (m - 1) * R = R ^ m := by rw [← pow_succ]; congr 1; omega
  rw [← intervalIntegral_eq_integral_Ioo hr.le,
    integral_congr_Ioo hr.le
      (fun x hx => lateralDensity_right_eq (Cm := Cm) hR hL g hx.1),
    intervalIntegral.integral_const_mul,
    integral_comp_right Cp.K R L hR.ne'
      (capLateralDensity Cp (fun p => g (L/2 + R * p.1, R • p.2))),
    capLateralIntegral, ← intervalIntegral_eq_integral_Ioo h0, ← hpow]
  ring

/-! ### The end disks -/

/-- Scaling of a ball integral: `∫_{B(0,Rρ)} f = R^m ∫_{B(0,ρ)} f(R ·)`. -/
theorem integral_ball_smul_radius (m : ℕ) {R ρ : ℝ} (hR : 0 < R)
    (f : EuclideanSpace ℝ (Fin m) → ℝ) :
    ∫ z in ball (0 : EuclideanSpace ℝ (Fin m)) (R * ρ), f z
      = R ^ m * ∫ z in ball (0 : EuclideanSpace ℝ (Fin m)) ρ, f (R • z) := by
  rcases le_or_gt ρ 0 with hρ | hρ
  · rw [ball_eq_empty.2 hρ, ball_eq_empty.2 (by nlinarith : R * ρ ≤ 0)]
    simp
  · have hsm : ∀ z : EuclideanSpace ℝ (Fin m), (R * ρ) • z = R • (ρ • z) := fun z =>
      (smul_smul R ρ z).symm
    rw [integral_ball_smul m (by positivity) f,
      integral_ball_smul m hρ (fun z => f (R • z))]
    simp only [hsm]
    rw [mul_pow]
    ring

/-- **The left end disk after rescaling**: `∫_{ {-L/2} × B_m(Rθ₋(0)) } g = R^m ∫_{B_m(θ₋(0))}
g(-L/2, R z)`. -/
theorem endDiskIntegralLeft_eq (hR : 0 < R) (g : CapSpace m → ℝ) :
    endDiskIntegralLeft Cm L R g
      = R ^ m * ∫ z in ball (0 : EuclideanSpace ℝ (Fin m)) (Cm.θ 0), g (-L/2, R • z) :=
  integral_ball_smul_radius m hR (fun z => g (-L/2, z))

/-- **The right end disk after rescaling**. -/
theorem endDiskIntegralRight_eq (hR : 0 < R) (g : CapSpace m → ℝ) :
    endDiskIntegralRight Cp L R g
      = R ^ m * ∫ z in ball (0 : EuclideanSpace ℝ (Fin m)) (Cp.θ 0), g (L/2, R • z) :=
  integral_ball_smul_radius m hR (fun z => g (L/2, z))

/-! ### Consistency: the splitting with `g = 1` -/

/-- The left cap contribution to `boundaryIntegral Cm Cp L R 1` is `R^m |Γ₋|`, reproducing the
cap part of `boundaryIntegral_one`. -/
theorem lateralIntegral_leftCap_one (hm : 1 ≤ m) (hR : 0 < R) :
    (∫ x in Ioo (-L/2) (-L/2 + Cm.K * R), lateralDensity Cm Cp L R (fun _ => 1) x)
      = R ^ m * Cm.lateralArea := by
  rw [lateralIntegral_leftCap_eq (Cp := Cp) hm hR (fun _ => 1), capLateralIntegral_one Cm hm]

/-- The right cap contribution to `boundaryIntegral Cm Cp L R 1` is `R^m |Γ₊|`. -/
theorem lateralIntegral_rightCap_one (hm : 1 ≤ m) (hR : 0 < R)
    (hL : (Cm.K + Cp.K) * R < L) :
    (∫ x in Ioo (L/2 - Cp.K * R) (L/2), lateralDensity Cm Cp L R (fun _ => 1) x)
      = R ^ m * Cp.lateralArea := by
  rw [lateralIntegral_rightCap_eq (Cm := Cm) hm hR hL (fun _ => 1), capLateralIntegral_one Cp hm]

/-- The bulk piece of `boundaryIntegral Cm Cp L R 1` is `m ω_m R^{m-1} ℓ_R`. -/
theorem lateralIntegral_bulk_one (hm : 1 ≤ m) (hR : 0 < R) (hL : (Cm.K + Cp.K) * R < L) :
    (∫ x in Icc (-L/2 + Cm.K * R) (L/2 - Cp.K * R), lateralDensity Cm Cp L R (fun _ => 1) x)
      = (m : ℝ) * omega m * R ^ (m - 1) * bulkLength Cm Cp L R := by
  have hmid := interface_lt (Cm := Cm) (Cp := Cp) hR hL
  have hEq : EqOn (lateralDensity Cm Cp L R (fun _ => 1))
      (fun _ => (m : ℝ) * omega m * R ^ (m - 1))
      (Ioo (-L/2 + Cm.K * R) (L/2 - Cp.K * R)) := by
    intro x hx
    rw [lateralDensity_one hm x, areaElement_bulk hx.1 hx.2]
  rw [integral_Icc_eq_integral_Ioo, setIntegral_congr_fun measurableSet_Ioo hEq,
    setIntegral_const, measureReal_def, Real.volume_Ioo,
    ENNReal.toReal_ofReal (by linarith), smul_eq_mul, bulkLength]
  ring

/-- The lateral density of the constant `1` is integrable on each of the three axial pieces. -/
theorem integrableOn_lateralDensity_one_left (hm : 1 ≤ m) (hR : 0 < R) :
    IntegrableOn (lateralDensity Cm Cp L R (fun _ => 1)) (Ioo (-L/2) (-L/2 + Cm.K * R)) := by
  have hl := left_lt_interface (Cm := Cm) (L := L) hR
  have h := (intervalIntegrable_areaElement_left (Cm := Cm) (Cp := Cp) (L := L) hR).const_mul
    ((m : ℝ) * omega m)
  rw [intervalIntegrable_iff_integrableOn_Ioo_of_le hl.le] at h
  exact h.congr_fun (fun x _ => (lateralDensity_one hm x).symm) measurableSet_Ioo

theorem integrableOn_lateralDensity_one_bulk (hm : 1 ≤ m) (hR : 0 < R)
    (hL : (Cm.K + Cp.K) * R < L) :
    IntegrableOn (lateralDensity Cm Cp L R (fun _ => 1))
      (Ioo (-L/2 + Cm.K * R) (L/2 - Cp.K * R)) := by
  have hmid := interface_lt (Cm := Cm) (Cp := Cp) hR hL
  have h := (intervalIntegrable_areaElement_bulk (Cm := Cm) (Cp := Cp) hR hL).const_mul
    ((m : ℝ) * omega m)
  rw [intervalIntegrable_iff_integrableOn_Ioo_of_le hmid.le] at h
  exact h.congr_fun (fun x _ => (lateralDensity_one hm x).symm) measurableSet_Ioo

theorem integrableOn_lateralDensity_one_right (hm : 1 ≤ m) (hR : 0 < R)
    (hL : (Cm.K + Cp.K) * R < L) :
    IntegrableOn (lateralDensity Cm Cp L R (fun _ => 1)) (Ioo (L/2 - Cp.K * R) (L/2)) := by
  have hr := interface_lt_right (Cp := Cp) (L := L) hR
  have h := (intervalIntegrable_areaElement_right (Cm := Cm) (Cp := Cp) hR hL).const_mul
    ((m : ℝ) * omega m)
  rw [intervalIntegrable_iff_integrableOn_Ioo_of_le hr.le] at h
  exact h.congr_fun (fun x _ => (lateralDensity_one hm x).symm) measurableSet_Ioo

/-! ## 4. Assembly -/

/-- **The boundary integral of `Ω_R`, split into its three axial pieces**, with the two cap
pieces rescaled to the unit caps.  The bulk piece is left as it stands; for tensor-type
integrands it is computed by `lateralIntegral_bulk_tensor`. -/
theorem boundaryIntegral_split (hm : 1 ≤ m) (hR : 0 < R) (hL : (Cm.K + Cp.K) * R < L)
    (g : CapSpace m → ℝ)
    (h₁ : IntegrableOn (lateralDensity Cm Cp L R g) (Ioo (-L/2) (-L/2 + Cm.K * R)))
    (h₂ : IntegrableOn (lateralDensity Cm Cp L R g)
      (Ioo (-L/2 + Cm.K * R) (L/2 - Cp.K * R)))
    (h₃ : IntegrableOn (lateralDensity Cm Cp L R g) (Ioo (L/2 - Cp.K * R) (L/2))) :
    boundaryIntegral Cm Cp L R g
      = (∫ x in Icc (-L/2 + Cm.K * R) (L/2 - Cp.K * R), lateralDensity Cm Cp L R g x)
        + R ^ m * (capLateralIntegral Cm (fun p => g (-L/2 - R * p.1, R • p.2))
            + ∫ z in ball (0 : EuclideanSpace ℝ (Fin m)) (Cm.θ 0), g (-L/2, R • z))
        + R ^ m * (capLateralIntegral Cp (fun p => g (L/2 + R * p.1, R • p.2))
            + ∫ z in ball (0 : EuclideanSpace ℝ (Fin m)) (Cp.θ 0), g (L/2, R • z)) := by
  rw [boundaryIntegral, lateralIntegral_split hR hL g h₁ h₂ h₃,
    lateralIntegral_leftCap_eq (Cp := Cp) hm hR g,
    lateralIntegral_rightCap_eq (Cm := Cm) hm hR hL g,
    endDiskIntegralLeft_eq hR g, endDiskIntegralRight_eq hR g]
  ring

/-- Two integrands that agree on the **bulk lateral surface** `I_R × ∂B_m(R)` have the same bulk
piece. -/
theorem lateralIntegral_bulk_congr {g₁ g₂ : CapSpace m → ℝ}
    (hcong : ∀ x ∈ Ioo (-L/2 + Cm.K * R) (L/2 - Cp.K * R),
      ∀ ω : sphere (0 : EuclideanSpace ℝ (Fin m)) 1,
        g₁ (x, R • (ω : EuclideanSpace ℝ (Fin m))) = g₂ (x, R • (ω : EuclideanSpace ℝ (Fin m)))) :
    (∫ x in Icc (-L/2 + Cm.K * R) (L/2 - Cp.K * R), lateralDensity Cm Cp L R g₁ x)
      = ∫ x in Icc (-L/2 + Cm.K * R) (L/2 - Cp.K * R), lateralDensity Cm Cp L R g₂ x := by
  rw [integral_Icc_eq_integral_Ioo, integral_Icc_eq_integral_Ioo]
  refine setIntegral_congr_fun measurableSet_Ioo fun x hx => ?_
  rw [lateralDensity_bulk (Cm := Cm) (Cp := Cp) g₁ hx.1 hx.2,
    lateralDensity_bulk (Cm := Cm) (Cp := Cp) g₂ hx.1 hx.2]
  congr 1
  exact integral_congr_ae (Filter.Eventually.of_forall fun ω => hcong x hx ω)

/-- **The boundary energy of a trial function of the manuscript's shape**
(`eq:trial-extension`): a function `u` which on the bulk lateral surface is the tensor product
`F(x) h(z)` and is arbitrary on the two caps.  The boundary energy splits into

* the **bulk** term `(∫_{I_R} F²) · ∫_{∂B_m(R)} h²`,
* `R^m` times the **left cap**'s own boundary energy (lateral surface plus terminal disk) of the
  rescaled function `u(-L/2 - R s, R z)`,
* `R^m` times the same for the **right cap**.
-/
theorem boundaryEnergy_tensor_split (hm : 1 ≤ m) (hR : 0 < R) (hL : (Cm.K + Cp.K) * R < L)
    (u : CapSpace m → ℝ) (F : ℝ → ℝ) (h : EuclideanSpace ℝ (Fin m) → ℝ)
    (hbulk : ∀ x ∈ Ioo (-L/2 + Cm.K * R) (L/2 - Cp.K * R),
      ∀ ω : sphere (0 : EuclideanSpace ℝ (Fin m)) 1,
        u (x, R • (ω : EuclideanSpace ℝ (Fin m)))
          = F x * h (R • (ω : EuclideanSpace ℝ (Fin m))))
    (h₁ : IntegrableOn (lateralDensity Cm Cp L R (fun p => u p ^ 2))
      (Ioo (-L/2) (-L/2 + Cm.K * R)))
    (h₂ : IntegrableOn (lateralDensity Cm Cp L R (fun p => u p ^ 2))
      (Ioo (-L/2 + Cm.K * R) (L/2 - Cp.K * R)))
    (h₃ : IntegrableOn (lateralDensity Cm Cp L R (fun p => u p ^ 2))
      (Ioo (L/2 - Cp.K * R) (L/2))) :
    boundaryEnergy Cm Cp L R u
      = (∫ x in Icc (-L/2 + Cm.K * R) (L/2 - Cp.K * R), F x ^ 2)
            * sphereIntegral m R (fun z => h z ^ 2)
        + R ^ m * (capLateralIntegral Cm (fun p => u (-L/2 - R * p.1, R • p.2) ^ 2)
            + ∫ z in ball (0 : EuclideanSpace ℝ (Fin m)) (Cm.θ 0), u (-L/2, R • z) ^ 2)
        + R ^ m * (capLateralIntegral Cp (fun p => u (L/2 + R * p.1, R • p.2) ^ 2)
            + ∫ z in ball (0 : EuclideanSpace ℝ (Fin m)) (Cp.θ 0), u (L/2, R • z) ^ 2) := by
  have hcong : ∀ x ∈ Ioo (-L/2 + Cm.K * R) (L/2 - Cp.K * R),
      ∀ ω : sphere (0 : EuclideanSpace ℝ (Fin m)) 1,
        u (x, R • (ω : EuclideanSpace ℝ (Fin m))) ^ 2
          = (F x * h (R • (ω : EuclideanSpace ℝ (Fin m)))) ^ 2 := by
    intro x hx ω
    rw [hbulk x hx ω]
  rw [boundaryEnergy, boundaryIntegral_split hm hR hL _ h₁ h₂ h₃,
    lateralIntegral_bulk_congr (Cm := Cm) (Cp := Cp) (g₁ := fun p : CapSpace m => u p ^ 2)
      (g₂ := fun p : CapSpace m => (F p.1 * h p.2) ^ 2) hcong,
    lateralIntegral_bulk_tensor_sq (Cm := Cm) (Cp := Cp) F h]

/-- **Consistency check**: the three-piece splitting, applied to `g = 1`, reproduces
`RobinCaps.ThinDomain.boundaryIntegral_one` — the cap pieces give `R^m (|Γ₋| + |Γ₊|)` (lateral
plus terminal areas of the *unit* caps) and the bulk piece gives `m ω_m R^{m-1} ℓ_R`.  This
re-proves `boundaryIntegral_one` from `boundaryIntegral_split`. -/
theorem boundaryIntegral_split_one (hm : 1 ≤ m) (hR : 0 < R) (hL : (Cm.K + Cp.K) * R < L)
    (hm0 : 0 ≤ Cm.θ 0) (hp0 : 0 ≤ Cp.θ 0) :
    boundaryIntegral Cm Cp L R (fun _ => 1)
      = R ^ m * (Cm.lateralArea + Cm.terminalArea + Cp.lateralArea + Cp.terminalArea)
        + (m : ℝ) * omega m * R ^ (m - 1) * bulkLength Cm Cp L R := by
  have hdm : (∫ _z in ball (0 : EuclideanSpace ℝ (Fin m)) (Cm.θ 0), (1 : ℝ))
      = Cm.terminalArea := by
    rw [setIntegral_const, measureReal_def, volume_ball_toReal m hm hm0, smul_eq_mul, mul_one,
      Cap.terminalArea]
    ring
  have hdp : (∫ _z in ball (0 : EuclideanSpace ℝ (Fin m)) (Cp.θ 0), (1 : ℝ))
      = Cp.terminalArea := by
    rw [setIntegral_const, measureReal_def, volume_ball_toReal m hm hp0, smul_eq_mul, mul_one,
      Cap.terminalArea]
    ring
  rw [boundaryIntegral_split hm hR hL (fun _ => 1)
      (integrableOn_lateralDensity_one_left hm hR)
      (integrableOn_lateralDensity_one_bulk hm hR hL)
      (integrableOn_lateralDensity_one_right hm hR hL),
    lateralIntegral_bulk_one hm hR hL, capLateralIntegral_one Cm hm,
    capLateralIntegral_one Cp hm, hdm, hdp]
  ring

end RobinCaps.ThinDomain

end
