import Mathlib
import RobinCaps.Domain.Thin
import RobinCaps.Domain.Capsule

/-!
# Identification of the product model with Euclidean space

The thin domain `Ω_R` of `RobinCaps.Domain.Thin` lives in the *product* model
`CapSpace m = ℝ × EuclideanSpace ℝ (Fin m)`, whereas the capsule of
`RobinCaps.Domain.Capsule` lives in `EuclideanSpace ℝ (Fin (m+1))`.  The product
model carries the *sup* metric, not the Euclidean one, so the two spaces are
*not* isometric as metric spaces and the identification has to be made explicit.

This file provides the linear identification

`toEuclid m (t, z) = (t, z₀, …, z_{m-1})`

(which is an `Equiv`, a `MeasurableEquiv` and volume preserving), computes the
Euclidean norm and distance through it, and proves the two statements the audit
asked for:

* `toEuclid_thinDomain_hemisphere`: the image of the hemispherical thin domain
  is exactly the capsule;
* `euclidDiam_thinDomain_hemisphere`: consequently the *Euclidean* diameter of
  the thin domain is `L`, so `diam Ω_R = L` genuinely refers to the domain of
  `thm:main`;
* `volume_capsule_eq_volume_thinDomain`: the volumes agree, so
  `volume_thinDomain` transports to the capsule.
-/

open MeasureTheory Set Metric
open scoped Topology ENNReal RealInnerProductSpace

namespace RobinCaps
namespace Domain

open RobinCaps.Cap

noncomputable section

variable {m : ℕ}

/-! ## The identification `ℝ × ℝ^m ≃ ℝ^{m+1}` -/

/-- The identification of the product model `CapSpace m = ℝ × EuclideanSpace ℝ (Fin m)`
with `EuclideanSpace ℝ (Fin (m+1))`: the axial coordinate becomes the `0`-th
coordinate and the transverse coordinates are shifted by one. -/
def toEuclid (m : ℕ) (p : CapSpace m) : EuclideanSpace ℝ (Fin (m + 1)) :=
  WithLp.toLp 2 (Fin.cons p.1 (fun i => p.2 i))

/-- The inverse of `toEuclid`. -/
def ofEuclid (m : ℕ) (x : EuclideanSpace ℝ (Fin (m + 1))) : CapSpace m :=
  (x 0, WithLp.toLp 2 fun i : Fin m => x i.succ)

@[simp] theorem toEuclid_apply_zero (p : CapSpace m) : toEuclid m p 0 = p.1 := rfl

@[simp] theorem toEuclid_apply_succ (p : CapSpace m) (i : Fin m) :
    toEuclid m p i.succ = p.2 i := rfl

@[simp] theorem ofEuclid_fst (x : EuclideanSpace ℝ (Fin (m + 1))) : (ofEuclid m x).1 = x 0 := rfl

@[simp] theorem ofEuclid_snd_apply (x : EuclideanSpace ℝ (Fin (m + 1))) (i : Fin m) :
    (ofEuclid m x).2 i = x i.succ := rfl

theorem toEuclid_ofEuclid (x : EuclideanSpace ℝ (Fin (m + 1))) :
    toEuclid m (ofEuclid m x) = x := by
  refine PiLp.ext fun j => ?_
  refine Fin.cases ?_ ?_ j
  · rfl
  · intro i; rfl

theorem ofEuclid_toEuclid (p : CapSpace m) : ofEuclid m (toEuclid m p) = p := by
  obtain ⟨t, z⟩ := p
  refine Prod.ext rfl ?_
  exact PiLp.ext fun i => rfl

theorem toEuclid_injective : Function.Injective (toEuclid m) :=
  Function.LeftInverse.injective ofEuclid_toEuclid

theorem toEuclid_surjective : Function.Surjective (toEuclid m) :=
  Function.RightInverse.surjective toEuclid_ofEuclid

theorem toEuclid_bijective : Function.Bijective (toEuclid m) :=
  ⟨toEuclid_injective, toEuclid_surjective⟩

/-- `toEuclid` packaged as an `Equiv`. -/
def capSpaceEquiv (m : ℕ) : CapSpace m ≃ EuclideanSpace ℝ (Fin (m + 1)) where
  toFun := toEuclid m
  invFun := ofEuclid m
  left_inv := ofEuclid_toEuclid
  right_inv := toEuclid_ofEuclid

@[simp] theorem capSpaceEquiv_apply (p : CapSpace m) : capSpaceEquiv m p = toEuclid m p := rfl

@[simp] theorem capSpaceEquiv_symm_apply (x : EuclideanSpace ℝ (Fin (m + 1))) :
    (capSpaceEquiv m).symm x = ofEuclid m x := rfl

/-! ## Euclidean norm and distance through the identification -/

/-- The identification computes the Euclidean norm: `‖(t,z)‖² = t² + ‖z‖²`. -/
theorem norm_toEuclid_sq (p : CapSpace m) : ‖toEuclid m p‖ ^ 2 = p.1 ^ 2 + ‖p.2‖ ^ 2 := by
  rw [EuclideanSpace.norm_sq_eq, Fin.sum_univ_succ, EuclideanSpace.norm_sq_eq]
  simp [Real.norm_eq_abs, sq_abs]

/-- The identification computes the Euclidean distance:
`dist ((t,z),(s,w))² = (t-s)² + ‖z-w‖²`. -/
theorem dist_toEuclid_sq (p q : CapSpace m) :
    dist (toEuclid m p) (toEuclid m q) ^ 2 = (p.1 - q.1) ^ 2 + ‖p.2 - q.2‖ ^ 2 := by
  rw [EuclideanSpace.dist_sq_eq, Fin.sum_univ_succ]
  congr 1
  · simp [Real.dist_eq, sq_abs]
  · simp only [toEuclid_apply_succ]
    rw [← EuclideanSpace.dist_sq_eq, dist_eq_norm]

/-- The axis vector is the image of `(1,0)`. -/
theorem axis_eq_toEuclid : axis m = toEuclid m (1, 0) := by
  refine PiLp.ext fun j => ?_
  refine Fin.cases ?_ ?_ j
  · simp [axis, EuclideanSpace.single_apply]
  · intro i
    simp [axis, EuclideanSpace.single_apply, Fin.succ_ne_zero]

/-- Points of the axis are images of `(t,0)`. -/
theorem smul_axis_eq_toEuclid (t : ℝ) : t • axis m = toEuclid m (t, 0) := by
  refine PiLp.ext fun j => ?_
  refine Fin.cases ?_ ?_ j
  · simp [axis, EuclideanSpace.single_apply]
  · intro i
    simp [axis, EuclideanSpace.single_apply, Fin.succ_ne_zero]

/-- The Euclidean distance from `toEuclid p` to the axial point `t • e`. -/
theorem dist_toEuclid_smul_axis_sq (p : CapSpace m) (t : ℝ) :
    dist (toEuclid m p) (t • axis m) ^ 2 = (p.1 - t) ^ 2 + ‖p.2‖ ^ 2 := by
  rw [smul_axis_eq_toEuclid, dist_toEuclid_sq]
  simp

/-! ## The identification is measurable and volume preserving -/

theorem toEuclid_eq_comp :
    toEuclid m = (WithLp.toLp 2 : (Fin (m + 1) → ℝ) → EuclideanSpace ℝ (Fin (m + 1))) ∘
      ((MeasurableEquiv.piFinSuccAbove (fun _ : Fin (m + 1) => ℝ) 0).symm) ∘
      (Prod.map (id : ℝ → ℝ)
        (WithLp.ofLp : EuclideanSpace ℝ (Fin m) → (Fin m → ℝ))) := by
  funext p
  refine PiLp.ext fun j => ?_
  simp only [Function.comp_apply, MeasurableEquiv.piFinSuccAbove_symm_apply]
  refine Fin.cases ?_ ?_ j
  · simp [toEuclid]
  · intro i
    simp [toEuclid]

/-- **`toEuclid` is volume preserving.** -/
theorem measurePreserving_toEuclid (m : ℕ) :
    MeasurePreserving (toEuclid m) volume volume := by
  have h1 : MeasurePreserving
      (Prod.map (id : ℝ → ℝ)
        (WithLp.ofLp : EuclideanSpace ℝ (Fin m) → (Fin m → ℝ)))
      volume volume :=
    (MeasurePreserving.id (volume : Measure ℝ)).prod (PiLp.volume_preserving_ofLp (Fin m))
  have h2 : MeasurePreserving
      ((MeasurableEquiv.piFinSuccAbove (fun _ : Fin (m + 1) => ℝ) 0).symm) volume volume :=
    (volume_preserving_piFinSuccAbove (fun _ : Fin (m + 1) => ℝ) 0).symm _
  have h3 : MeasurePreserving
      (WithLp.toLp 2 : (Fin (m + 1) → ℝ) → EuclideanSpace ℝ (Fin (m + 1))) volume volume :=
    PiLp.volume_preserving_toLp (Fin (m + 1))
  rw [toEuclid_eq_comp]
  exact h3.comp (h2.comp h1)

theorem measurable_toEuclid (m : ℕ) : Measurable (toEuclid m) :=
  (measurePreserving_toEuclid m).measurable

theorem measurable_ofEuclid (m : ℕ) : Measurable (ofEuclid m) :=
  Measurable.prodMk
    ((measurable_pi_apply (0 : Fin (m + 1))).comp (WithLp.measurable_ofLp 2 _))
    ((WithLp.measurable_toLp 2 _).comp
      (measurable_pi_iff.mpr fun i =>
        (measurable_pi_apply i.succ).comp (WithLp.measurable_ofLp 2 _)))

/-- `toEuclid` packaged as a `MeasurableEquiv`. -/
def capSpaceMeasurableEquiv (m : ℕ) : CapSpace m ≃ᵐ EuclideanSpace ℝ (Fin (m + 1)) where
  toEquiv := capSpaceEquiv m
  measurable_toFun := measurable_toEuclid m
  measurable_invFun := measurable_ofEuclid m

theorem measurePreserving_ofEuclid (m : ℕ) :
    MeasurePreserving (ofEuclid m) volume volume :=
  (measurePreserving_toEuclid m).symm (capSpaceMeasurableEquiv m)

/-- The image under `toEuclid` is the preimage under `ofEuclid`. -/
theorem toEuclid_image_eq_ofEuclid_preimage (S : Set (CapSpace m)) :
    toEuclid m '' S = ofEuclid m ⁻¹' S := by
  ext x
  constructor
  · rintro ⟨p, hp, rfl⟩
    simpa [mem_preimage, ofEuclid_toEuclid] using hp
  · intro hx
    exact ⟨ofEuclid m x, hx, toEuclid_ofEuclid x⟩

theorem volume_toEuclid_image {S : Set (CapSpace m)} (hS : NullMeasurableSet S volume) :
    volume (toEuclid m '' S) = volume S := by
  rw [toEuclid_image_eq_ofEuclid_preimage]
  exact (measurePreserving_ofEuclid m).measure_preimage hS

/-! ## The hemispherical thin domain is the capsule -/

variable {L R : ℝ}

/-- The admissibility hypothesis of `Thin.lean` for two hemispherical caps. -/
theorem hemisphere_hL (hL : 2 * R < L) :
    ((hemisphere m).K + (hemisphere m).K) * R < L := by
  show ((1 : ℝ) + 1) * R < L
  linarith

/-- **The thin domain with two hemispherical caps is the capsule.**  This is the
identification the audit asked for: `Ω_R ⊆ ℝ × ℝ^m` and the capsule
`{x ∈ ℝ^{m+1} : dist(x, S_R) < R}` correspond under `toEuclid`. -/
theorem toEuclid_thinDomain_hemisphere (hR : 0 < R) (hL : 2 * R < L) :
    toEuclid m '' thinDomain (hemisphere m) (hemisphere m) L R = capsule m L R := by
  ext x
  constructor
  · rintro ⟨p, hp, rfl⟩
    obtain ⟨t, ht, hlt⟩ := (mem_thinDomain_hemisphere_iff hR hL).mp hp
    refine mem_capsule_iff.mpr ⟨t • axis m, ?_, ?_⟩
    · exact smul_axis_mem_axisSegment hL.le (abs_le.mpr ⟨ht.1, ht.2⟩)
    · have hsq := dist_toEuclid_smul_axis_sq p t
      have hd : dist (toEuclid m p) (t • axis m) ^ 2 < R ^ 2 := by rw [hsq]; exact hlt
      nlinarith [dist_nonneg (x := toEuclid m p) (y := t • axis m)]
  · intro hx
    obtain ⟨q, hq, hd⟩ := mem_capsule_iff.mp hx
    obtain ⟨t, ht, rfl⟩ := (mem_axisSegment_iff hL.le).mp hq
    refine ⟨ofEuclid m x, ?_, toEuclid_ofEuclid x⟩
    refine (mem_thinDomain_hemisphere_iff hR hL).mpr ⟨t, ?_, ?_⟩
    · exact mem_Icc.mpr ⟨neg_le_of_abs_le ht, le_of_abs_le ht⟩
    · have hx' : dist (toEuclid m (ofEuclid m x)) (t • axis m) < R := by
        rw [toEuclid_ofEuclid]; exact hd
      have hsq := dist_toEuclid_smul_axis_sq (ofEuclid m x) t
      nlinarith [dist_nonneg (x := toEuclid m (ofEuclid m x)) (y := t • axis m)]

/-- The reverse form of `toEuclid_thinDomain_hemisphere`. -/
theorem ofEuclid_capsule_hemisphere (hR : 0 < R) (hL : 2 * R < L) :
    ofEuclid m '' capsule m L R = thinDomain (hemisphere m) (hemisphere m) L R := by
  rw [← toEuclid_thinDomain_hemisphere (m := m) hR hL, ← image_comp]
  refine (image_congr (fun p _ => ?_)).trans (image_id _)
  simp [Function.comp_apply, ofEuclid_toEuclid]

/-! ## The Euclidean diameter of the thin domain -/

/-- The **Euclidean** diameter of a subset of the product model `CapSpace m`
(the ambient metric on `CapSpace m` itself is the sup metric, which is *not*
the one used in the manuscript). -/
def euclidDiam (S : Set (CapSpace m)) : ℝ := Metric.diam (toEuclid m '' S)

/-- **The Euclidean diameter of the thin domain is exactly `L`**
(manuscript `eq:exact-diameter`, for the domain of `thm:main`). -/
theorem euclidDiam_thinDomain_hemisphere (hR : 0 < R) (hL : 2 * R < L) :
    euclidDiam (thinDomain (hemisphere m) (hemisphere m) L R) = L := by
  rw [euclidDiam, toEuclid_thinDomain_hemisphere hR hL, diam_capsule hR hL]

/-! ## Transport of the volume -/

/-- The capsule and the hemispherical thin domain have the same volume. -/
theorem volume_capsule_eq_volume_thinDomain (hR : 0 < R) (hL : 2 * R < L) :
    volume (capsule m L R) = volume (thinDomain (hemisphere m) (hemisphere m) L R) := by
  rw [← toEuclid_thinDomain_hemisphere hR hL]
  exact volume_toEuclid_image
    ((measurableSet_thinDomain hR (hemisphere_hL hL)).nullMeasurableSet)

/-- The explicit volume of the capsule, transported from `volume_thinDomain`. -/
theorem volume_capsule (hR : 0 < R) (hL : 2 * R < L) :
    volume (capsule m L R)
      = ENNReal.ofReal (omega m * R ^ m * bulkLength (hemisphere m) (hemisphere m) L R
          + R ^ (m + 1) * ((hemisphere m).revolutionVolume
            + (hemisphere m).revolutionVolume)) := by
  rw [volume_capsule_eq_volume_thinDomain hR hL, volume_thinDomain hR (hemisphere_hL hL)]

end

end Domain
end RobinCaps

