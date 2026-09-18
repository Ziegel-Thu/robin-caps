import RobinCaps.Cap.EntranceL2HemiGen
import RobinCaps.Cap.Sharp

/-!
# The entrance trace of a weak `H¹` function on the flat cap body is square integrable

This file discharges the interface `RobinCaps.Cap.CapEntranceL2` of `RobinCaps/Cap/LowerWeak.lean`
for the **flat cap** `Cap.flat m K hK` (profile `θ ≡ 1`), i.e. for the straight cylinder segment

`C = {(s,z) | -K < s < 0, ‖z‖ < 1} ⊆ ℝ × EuclideanSpace ℝ (Fin m)`,

in every transverse dimension `m` and for every axial length `K > 0`.

## The argument

This is the easy case of the general entrance-trace bound: because the profile is constant,
**every** axial slice through a point `z` of the entrance ball `B_m(1)` is the full interval
`(-K,0)`, of the *same* length `K`, so the one-dimensional trace inequality
(`RobinCaps.Cap.ae_entranceVal_sq_le_el`, already stated for a general cap `C : Cap m`)
specialises, uniformly in `z`, to

`entranceVal(z)² ≤ (2/K) · axMass(z) + 2K · axEnergy(z)`.

Integrating over `z ∈ B_m(1)` and using the general-`m` identities
`RobinCaps.Cap.massP_eq_rep_el`/`RobinCaps.Cap.dirichletP_eq_rep_el` (already available from
`RobinCaps.Cap.EntranceL2Hemi`) gives the bound with `C₁ = max (2/K) (2K)`. Unlike the
hemispherical cap, no singular weight and no polar-coordinate integrability argument is needed,
since the axial slice length never degenerates.

No `sorry`, `admit`, `axiom` or `native_decide` occurs in this file.
-/

open MeasureTheory Set Filter Metric
open scoped ContDiff ENNReal Topology

namespace RobinCaps
namespace Cap

open RobinCaps.ThinDomain RobinCaps.Sobolev RobinCaps.Transverse

noncomputable section

variable {m : ℕ}

/-! ## 1. The geometry of the flat cap: every axial slice through the entrance ball is `(-K,0)` -/

@[simp] theorem flat_K_elf (m : ℕ) (K : ℝ) (hK : 0 < K) : (flat m K hK).K = K := rfl

theorem flat_theta_elf (m : ℕ) (K : ℝ) (hK : 0 < K) (s : ℝ) : (flat m K hK).θ s = 1 := rfl

/-- **The axial slice of the flat cap body is the full interval `(-K,0)`**, for every transverse
point of the entrance ball. -/
theorem axialSlice_flat_elf (m : ℕ) (K : ℝ) (hK : 0 < K) {z : EuclideanSpace ℝ (Fin m)}
    (hz : ‖z‖ < 1) : axialSlice (flat m K hK) z = Ioo (-K) 0 := by
  ext s
  simp only [axialSlice, mem_setOf_eq, body, flat_theta_elf, flat_K_elf, mem_Ioo]
  constructor
  · rintro ⟨h1, h2, -⟩
    exact ⟨h1, h2⟩
  · rintro ⟨h1, h2⟩
    exact ⟨h1, h2, hz⟩

/-- **The exit time of the flat cap is `0`** at every transverse point of the entrance ball:
the axial line always reaches the terminal disk. -/
theorem exitTime_flat_elf (m : ℕ) (K : ℝ) (hK : 0 < K) {z : EuclideanSpace ℝ (Fin m)}
    (hz : ‖z‖ < 1) : exitTime (flat m K hK) z = 0 := by
  have h1 : axialSlice (flat m K hK) z
      = Ioo (-(flat m K hK).K) (exitTime (flat m K hK) z) := axialSlice_eq _ _
  have h2 : axialSlice (flat m K hK) z = Ioo (-K) (0 : ℝ) := axialSlice_flat_elf m K hK hz
  rw [flat_K_elf] at h1
  have heq : Ioo (-K) (exitTime (flat m K hK) z) = Ioo (-K) (0 : ℝ) := h1 ▸ h2
  have hb : (-K : ℝ) < exitTime (flat m K hK) z :=
    (exitTime_mem (flat m K hK) hz).1
  have hc : (-K : ℝ) < 0 := by linarith
  exact Ioo_right_eq_el hb hc heq

/-- **The uniform axial slice length**: `exitTime + K = K` for every transverse point of the
entrance ball. -/
theorem axialLen_flat_elf (m : ℕ) (K : ℝ) (hK : 0 < K) {z : EuclideanSpace ℝ (Fin m)}
    (hz : ‖z‖ < 1) : exitTime (flat m K hK) z + (flat m K hK).K = K := by
  rw [exitTime_flat_elf m K hK hz, flat_K_elf, zero_add]

/-! ## 2. The pointwise majorant and the assembly -/

/-- The pointwise majorant of the squared entrance trace on the entrance ball, for the flat
cap: a constant multiple of the axial mass and energy. -/
def majFun_elf (m : ℕ) (K : ℝ) (hK : 0 < K) (u : H1P (flat m K hK).body)
    (z : EuclideanSpace ℝ (Fin m)) : ℝ :=
  (2 / K) * axMass_el (flat m K hK) u z + (2 * K) * axEnergy_el (flat m K hK) u z

theorem majFun_nonneg_elf (m : ℕ) (K : ℝ) (hK : 0 < K) (u : H1P (flat m K hK).body)
    (z : EuclideanSpace ℝ (Fin m)) : 0 ≤ majFun_elf m K hK u z := by
  have h1 := axMass_nonneg_el (flat m K hK) u z
  have h2 := axEnergy_nonneg_el (flat m K hK) u z
  have h3 : (0 : ℝ) ≤ 2 / K := by positivity
  have h4 : (0 : ℝ) ≤ 2 * K := by positivity
  rw [majFun_elf]; positivity

/-- **The pointwise bound on the entrance ball**, for the flat cap: the general trace bound
`ae_entranceVal_sq_le_el`, specialised via the uniform slice length `axialLen_flat_elf`. -/
theorem ae_entranceVal_sq_le_maj_elf (m : ℕ) (K : ℝ) (hK : 0 < K) (u : H1P (flat m K hK).body) :
    ∀ᵐ z ∂(volume.restrict (ball (0 : EuclideanSpace ℝ (Fin m)) 1)),
      entranceVal (flat m K hK) u z ^ 2 ≤ majFun_elf m K hK u z := by
  filter_upwards [ae_entranceVal_sq_le_el (flat m K hK) u, ae_restrict_mem measurableSet_ball]
    with z h1 hzb
  have hz : ‖z‖ < 1 := mem_ball_zero_iff.1 hzb
  rw [axialLen_flat_elf m K hK hz] at h1
  exact h1

theorem integrableOn_majFun_elf (m : ℕ) (K : ℝ) (hK : 0 < K) (u : H1P (flat m K hK).body) :
    IntegrableOn (majFun_elf m K hK u) (ball (0 : EuclideanSpace ℝ (Fin m)) 1) volume := by
  refine Integrable.add ?_ ?_
  · exact (integrable_axMass_el (flat m K hK) u).integrableOn.const_mul _
  · exact (integrable_axEnergy_el (flat m K hK) u).integrableOn.const_mul _

/-- **The trace bound** for the flat cap. -/
theorem integral_majFun_le_elf (m : ℕ) (K : ℝ) (hK : 0 < K) (u : H1P (flat m K hK).body) :
    (∫ z in ball (0 : EuclideanSpace ℝ (Fin m)) 1, majFun_elf m K hK u z)
      ≤ max (2 / K) (2 * K) * (massP u + dirichletP u) := by
  set M : ℝ := ∫ p in (flat m K hK).body, repFun (flat m K hK) u p ^ 2 with hM
  set A : ℝ := ∫ p in (flat m K hK).body, repGx (flat m K hK) u p ^ 2 with hA
  set B : ℝ := ∫ p in (flat m K hK).body, ‖repGz_el (flat m K hK) u p‖ ^ 2 with hB
  have hM0 : 0 ≤ M := setIntegral_nonneg (measurableSet_body' _) fun p _ => sq_nonneg _
  have hA0 : 0 ≤ A := setIntegral_nonneg (measurableSet_body' _) fun p _ => sq_nonneg _
  have hB0 : 0 ≤ B := setIntegral_nonneg (measurableSet_body' _) fun p _ => by positivity
  have hmass : massP u = M := massP_eq_rep_el _ u
  have hdir : dirichletP u = A + B := dirichletP_eq_rep_el _ u
  have hax : (∫ z in ball (0 : EuclideanSpace ℝ (Fin m)) 1, axMass_el (flat m K hK) u z) ≤ M := by
    rw [hM, ← integral_axMass_el (flat m K hK) u]
    exact setIntegral_le_integral (integrable_axMass_el _ u)
      (Eventually.of_forall fun z => axMass_nonneg_el _ _ _)
  have hae : (∫ z in ball (0 : EuclideanSpace ℝ (Fin m)) 1, axEnergy_el (flat m K hK) u z) ≤ A := by
    rw [hA, ← integral_axEnergy_el (flat m K hK) u]
    exact setIntegral_le_integral (integrable_axEnergy_el _ u)
      (Eventually.of_forall fun z => axEnergy_nonneg_el _ _ _)
  have hI1 : IntegrableOn (fun z => (2 / K) * axMass_el (flat m K hK) u z)
      (ball (0 : EuclideanSpace ℝ (Fin m)) 1) volume :=
    (integrable_axMass_el (flat m K hK) u).integrableOn.const_mul _
  have hI2 : IntegrableOn (fun z => (2 * K) * axEnergy_el (flat m K hK) u z)
      (ball (0 : EuclideanSpace ℝ (Fin m)) 1) volume :=
    (integrable_axEnergy_el (flat m K hK) u).integrableOn.const_mul _
  have hsplit : (∫ z in ball (0 : EuclideanSpace ℝ (Fin m)) 1, majFun_elf m K hK u z)
      = (2 / K) * (∫ z in ball (0 : EuclideanSpace ℝ (Fin m)) 1, axMass_el (flat m K hK) u z)
        + (2 * K) * (∫ z in ball (0 : EuclideanSpace ℝ (Fin m)) 1, axEnergy_el (flat m K hK) u z) := by
    simp only [majFun_elf]
    rw [integral_add hI1 hI2, integral_const_mul, integral_const_mul]
  rw [hsplit, hmass, hdir]
  have hKinv_nonneg : (0 : ℝ) ≤ 2 / K := by positivity
  have hK2_nonneg : (0 : ℝ) ≤ 2 * K := by positivity
  have hterm1 : (2 / K) * (∫ z in ball (0 : EuclideanSpace ℝ (Fin m)) 1,
      axMass_el (flat m K hK) u z) ≤ max (2 / K) (2 * K) * M :=
    (mul_le_mul_of_nonneg_left hax hKinv_nonneg).trans
      (mul_le_mul_of_nonneg_right (le_max_left _ _) hM0)
  have hterm2 : (2 * K) * (∫ z in ball (0 : EuclideanSpace ℝ (Fin m)) 1,
      axEnergy_el (flat m K hK) u z) ≤ max (2 / K) (2 * K) * A :=
    (mul_le_mul_of_nonneg_left hae hK2_nonneg).trans
      (mul_le_mul_of_nonneg_right (le_max_right _ _) hA0)
  have hmax0 : (0 : ℝ) ≤ max (2 / K) (2 * K) := le_trans hKinv_nonneg (le_max_left _ _)
  have hexpand : max (2 / K) (2 * K) * (M + (A + B))
      = max (2 / K) (2 * K) * M + max (2 / K) (2 * K) * A + max (2 / K) (2 * K) * B := by ring
  rw [hexpand]
  have hBnn : 0 ≤ max (2 / K) (2 * K) * B := mul_nonneg hmax0 hB0
  linarith [hterm1, hterm2, hBnn]

/-! ## 3. The main theorem -/

/-- **The entrance trace of a weak `H¹` function on the flat cap body is square integrable**,
in every transverse dimension `m` and for every axial length `K > 0`. This discharges the
interface `RobinCaps.Cap.CapEntranceL2` for `Cap.flat m K hK`. -/
theorem capEntranceL2_flat_elf (m : ℕ) (K : ℝ) (hK : 0 < K) :
    ∃ C₁ : ℝ, CapEntranceL2 (Cap.flat m K hK) C₁ := by
  have hKinv_nonneg : (0 : ℝ) ≤ 2 / K := by positivity
  have hK2_nonneg : (0 : ℝ) ≤ 2 * K := by positivity
  have hmax0 : (0 : ℝ) ≤ max (2 / K) (2 * K) := le_trans hKinv_nonneg (le_max_left _ _)
  refine ⟨max (2 / K) (2 * K), ⟨hmax0, fun u => ?_, fun u => ?_⟩⟩
  · have hmeas : AEStronglyMeasurable (entranceVal (flat m K hK) u)
        (volume.restrict (ball (0 : EuclideanSpace ℝ (Fin m)) 1)) :=
      (measurable_entranceVal (flat m K hK) u).aestronglyMeasurable
    refine (memLp_two_iff_integrable_sq hmeas).2 ?_
    refine Integrable.mono' (integrableOn_majFun_elf m K hK u) (hmeas.pow 2) ?_
    filter_upwards [ae_entranceVal_sq_le_maj_elf m K hK u] with z hz
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
    exact hz
  · have hmeas : AEStronglyMeasurable (entranceVal (flat m K hK) u)
        (volume.restrict (ball (0 : EuclideanSpace ℝ (Fin m)) 1)) :=
      (measurable_entranceVal (flat m K hK) u).aestronglyMeasurable
    have hint : IntegrableOn (fun z => entranceVal (flat m K hK) u z ^ 2)
        (ball (0 : EuclideanSpace ℝ (Fin m)) 1) volume := by
      refine Integrable.mono' (integrableOn_majFun_elf m K hK u) (hmeas.pow 2) ?_
      filter_upwards [ae_entranceVal_sq_le_maj_elf m K hK u] with z hz
      rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
      exact hz
    have hstep : (∫ z in ball (0 : EuclideanSpace ℝ (Fin m)) 1,
        entranceVal (flat m K hK) u z ^ 2)
        ≤ ∫ z in ball (0 : EuclideanSpace ℝ (Fin m)) 1, majFun_elf m K hK u z :=
      integral_mono_ae hint (integrableOn_majFun_elf m K hK u) (ae_entranceVal_sq_le_maj_elf m K hK u)
    exact hstep.trans (integral_majFun_le_elf m K hK u)

end

end Cap
end RobinCaps
