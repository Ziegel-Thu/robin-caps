import Mathlib
import RobinCaps.Cap.Basic
import RobinCaps.Cap.Regular
import RobinCaps.Cap.Checks

/-!
# Volume of an end cap: Lebesgue measure equals the volume-of-revolution integral

For a cap `C` of transverse dimension `m` whose profile `θ` is continuous on
the open axial interval `(-K,0)`, the genuine Lebesgue volume of the body
`C.body = {(s,z) | -K < s < 0, ‖z‖ < θ s}` equals the classical
volume-of-revolution formula `ω_m ∫_{-K}^0 θ^m`, i.e.

`volume C.body = ENNReal.ofReal C.revolutionVolume`.

The proof is Fubini for the product measure on `ℝ × ℝ^m`: the slice of the
body at axial position `s ∈ (-K,0)` is the ball of radius `θ s`, whose
measure is `θ(s)^m` times the unit-ball volume; all other slices are empty.
-/

open MeasureTheory Set Filter Metric
open scoped Topology ENNReal

namespace RobinCaps
namespace Cap

noncomputable section

variable {m : ℕ}

/-- Volume of a ball of positive radius in `ℝ^m`, as a multiple of the
unit-ball volume.  Valid also for `m = 0`, where every ball of positive radius
is the whole (one-point) space. -/
theorem volume_ball_eq_pow_mul (m : ℕ) {r : ℝ} (hr : 0 < r) :
    volume (ball (0 : EuclideanSpace ℝ (Fin m)) r)
      = ENNReal.ofReal (r ^ m) * volume (ball (0 : EuclideanSpace ℝ (Fin m)) 1) := by
  cases m with
  | zero =>
    have hnorm : ∀ z : EuclideanSpace ℝ (Fin 0), ‖z‖ = 0 := by
      intro z
      rw [EuclideanSpace.norm_eq]
      simp
    have hball : ∀ s : ℝ, 0 < s → ball (0 : EuclideanSpace ℝ (Fin 0)) s = univ := by
      intro s hs
      ext z
      simp [hnorm z, hs]
    rw [hball r hr, hball 1 one_pos]
    simp
  | succ n =>
    rw [Measure.addHaar_ball volume 0 hr.le, finrank_euclideanSpace_fin]

/-- The axial slice of the body at `x`: the ball of radius `θ x` for
`x ∈ (-K,0)`, empty otherwise. -/
theorem body_slice (C : Cap m) (x : ℝ) :
    Prod.mk x ⁻¹' C.body =
      if x ∈ Ioo (-C.K) 0 then ball (0 : EuclideanSpace ℝ (Fin m)) (C.θ x) else ∅ := by
  ext z
  simp only [body, mem_preimage, mem_setOf_eq, mem_Ioo]
  split_ifs with hx
  · simp [hx.1, hx.2]
  · simp only [mem_empty_iff_false, iff_false]
    intro h
    exact hx ⟨h.1, h.2.1⟩

/-- The body is open when the profile is continuous on the open interval. -/
theorem isOpen_body (C : Cap m) (hθ : ContinuousOn C.θ (Ioo (-C.K) 0)) :
    IsOpen C.body := by
  have hU : IsOpen (Ioo (-C.K) 0 ×ˢ (univ : Set (EuclideanSpace ℝ (Fin m)))) :=
    isOpen_Ioo.prod isOpen_univ
  have hF : ContinuousOn (fun p : CapSpace m => (‖p.2‖, C.θ p.1))
      (Ioo (-C.K) 0 ×ˢ (univ : Set (EuclideanSpace ℝ (Fin m)))) := by
    refine ContinuousOn.prodMk continuous_snd.norm.continuousOn ?_
    exact hθ.comp continuous_fst.continuousOn (fun p hp => hp.1)
  have ht : IsOpen {q : ℝ × ℝ | q.1 < q.2} := isOpen_lt continuous_fst continuous_snd
  have h := hF.isOpen_inter_preimage hU ht
  convert h using 1
  ext p
  simp [body, and_assoc]

/-- The body is measurable. -/
theorem measurableSet_body (C : Cap m) (hθ : ContinuousOn C.θ (Ioo (-C.K) 0)) :
    MeasurableSet C.body :=
  (C.isOpen_body hθ).measurableSet

/-- `θ^m` is integrable on `(-K,0)`: it is continuous there and bounded by `1`. -/
theorem integrableOn_pow (C : Cap m) (hθ : ContinuousOn C.θ (Ioo (-C.K) 0)) :
    IntegrableOn (fun s => C.θ s ^ m) (Ioo (-C.K) 0) := by
  have hmeas : AEStronglyMeasurable (fun s => C.θ s ^ m) (volume.restrict (Ioo (-C.K) 0)) :=
    (hθ.pow m).aestronglyMeasurable measurableSet_Ioo
  refine Integrable.mono' (integrableOn_const (C := (1 : ℝ)) measure_Ioo_lt_top.ne) hmeas ?_
  refine ae_restrict_of_forall_mem measurableSet_Ioo (fun s hs => ?_)
  rw [Real.norm_eq_abs, abs_of_nonneg (pow_nonneg (C.θ_pos s hs).le m)]
  exact pow_le_one₀ (C.θ_pos s hs).le (C.θ_le_one s hs)

/-- The volume-of-revolution integral is nonnegative. -/
theorem revolutionVolume_nonneg (m : ℕ) (C : Cap m) : 0 ≤ C.revolutionVolume := by
  rw [revolutionVolume]
  refine mul_nonneg (omega_pos m).le ?_
  rw [intervalIntegral.integral_of_le (by linarith [C.hK]), integral_Ioc_eq_integral_Ioo]
  exact setIntegral_nonneg measurableSet_Ioo (fun s hs => pow_nonneg (C.θ_pos s hs).le m)

/-- **Volume of the body.**  The Lebesgue measure of the cap body equals the
volume-of-revolution integral `ω_m ∫_{-K}^0 θ^m`. -/
theorem volume_body_eq (m : ℕ) (C : Cap m) (hθ : ContinuousOn C.θ (Ioo (-C.K) 0)) :
    volume C.body = ENNReal.ofReal C.revolutionVolume := by
  have hBfin : volume (ball (0 : EuclideanSpace ℝ (Fin m)) 1) ≠ ∞ := measure_ball_lt_top.ne
  have hmeas : MeasurableSet C.body := C.measurableSet_body hθ
  have hprod : volume C.body = ∫⁻ x, volume (Prod.mk x ⁻¹' C.body) :=
    Measure.prod_apply hmeas
  have hslice : ∀ x : ℝ, volume (Prod.mk x ⁻¹' C.body)
      = (Ioo (-C.K) 0).indicator
          (fun x => ENNReal.ofReal (C.θ x ^ m)
            * volume (ball (0 : EuclideanSpace ℝ (Fin m)) 1)) x := by
    intro x
    rw [body_slice]
    by_cases hx : x ∈ Ioo (-C.K) 0
    · rw [if_pos hx, indicator_of_mem hx, volume_ball_eq_pow_mul m (C.θ_pos x hx)]
    · rw [if_neg hx, indicator_of_notMem hx, measure_empty]
  have hnn : 0 ≤ᵐ[volume.restrict (Ioo (-C.K) 0)] fun s => C.θ s ^ m :=
    ae_restrict_of_forall_mem measurableSet_Ioo (fun s hs => pow_nonneg (C.θ_pos s hs).le m)
  rw [hprod, lintegral_congr hslice, lintegral_indicator measurableSet_Ioo,
    lintegral_mul_const' _ _ hBfin,
    ← ofReal_integral_eq_lintegral_ofReal (C.integrableOn_pow hθ).integrable hnn]
  have hom : volume (ball (0 : EuclideanSpace ℝ (Fin m)) 1) = ENNReal.ofReal (omega m) := by
    rw [omega, ENNReal.ofReal_toReal hBfin]
  rw [hom, ← ENNReal.ofReal_mul
      (setIntegral_nonneg measurableSet_Ioo (fun s hs => pow_nonneg (C.θ_pos s hs).le m)),
    revolutionVolume, intervalIntegral.integral_of_le (by linarith [C.hK]),
    integral_Ioc_eq_integral_Ioo, mul_comm]

/-- The real-valued volume of the body equals the volume-of-revolution integral. -/
theorem volume_body_toReal (m : ℕ) (C : Cap m) (hθ : ContinuousOn C.θ (Ioo (-C.K) 0)) :
    (volume C.body).toReal = C.revolutionVolume := by
  rw [volume_body_eq m C hθ, ENNReal.toReal_ofReal (revolutionVolume_nonneg m C)]

end

end Cap
end RobinCaps
